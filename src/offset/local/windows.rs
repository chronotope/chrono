// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::convert::TryFrom;
use std::mem::MaybeUninit;
use std::ptr;

use super::win_bindings::{GetTimeZoneInformationForYear, SYSTEMTIME, TIME_ZONE_INFORMATION};

use super::{FixedOffset, TzInfo};
use crate::{Datelike, LocalResult, NaiveDate, NaiveDateTime, NaiveTime, Weekday};

// We don't use `SystemTimeToTzSpecificLocalTime` because it doesn't support the same range of dates
// as Chrono. Also it really isn't that difficult to work out the correct offset from the provided
// DST rules.
#[allow(clippy::collapsible_else_if)]
pub(super) fn offset_from_utc_datetime(utc: &NaiveDateTime) -> LocalResult<FixedOffset> {
    // Using a `TzInfo` based on the year of an UTC datetime is technically wrong, we should be
    // using the rules for the year of the corresponding local time. But this matches what
    //`SystemTimeToTzSpecificLocalTime` is documented to do.
    let tz_info = match tz_info_for_year(utc.year()) {
        Some(tz_info) => tz_info,
        None => return LocalResult::None,
    };
    LocalResult::Single(match (tz_info.std_transition, tz_info.dst_transition) {
        (Some(std_transition), Some(dst_transition)) => {
            let std_transition_utc = std_transition - tz_info.dst_offset;
            let dst_transition_utc = dst_transition - tz_info.std_offset;
            if dst_transition_utc < std_transition_utc {
                if utc >= &dst_transition_utc && utc < &std_transition_utc {
                    tz_info.dst_offset
                } else {
                    tz_info.std_offset
                }
            } else {
                if utc >= &std_transition_utc && utc < &dst_transition_utc {
                    tz_info.std_offset
                } else {
                    tz_info.dst_offset
                }
            }
        }
        _ => tz_info.std_offset,
    })
}

// We don't use `TzSpecificLocalTimeToSystemTime` because it doesn't let us choose how to handle
// ambiguous cases (during a DST transition). Instead we get the timezone information for the
// current year and compute it ourselves, like we do on Unix.
pub(super) fn offset_from_local_datetime(local: &NaiveDateTime) -> LocalResult<FixedOffset> {
    let tz_info = match tz_info_for_year(local.year()) {
        Some(tz_info) => tz_info,
        None => return LocalResult::None,
    };
    match (tz_info.std_transition, tz_info.dst_transition) {
        (Some(_), Some(_)) => tz_info.lookup_with_dst_transitions(*local),
        _ => LocalResult::Single(tz_info.std_offset),
    }
}

// The basis for Windows timezone and DST support has been in place since Windows 2000. It does not
// allow for complex rules like the IANA timezone database:
// - A timezone has the same base offset the whole year.
// - There are either zero or two DST transitions.
// - As of Vista(?) only years from 2004 until a few years into the future are supported.
// - All other years get the base settings, which seem to be that of the current year.
fn tz_info_for_year(year: i32) -> Option<TzInfo> {
    // The API limits years to 1601..=30827.
    // Working with timezones and daylight saving time this far into the past or future makes
    // little sense. But whatever is extrapolated for 1601 or 30827 is what can be extrapolated
    // for years beyond.
    let ref_year = year.clamp(1601, 30827) as u16;
    let tz_info = unsafe {
        let mut tz_info = MaybeUninit::<TIME_ZONE_INFORMATION>::uninit();
        if GetTimeZoneInformationForYear(ref_year, ptr::null_mut(), tz_info.as_mut_ptr()) == 0 {
            return None;
        }
        tz_info.assume_init()
    };
    Some(TzInfo {
        std_offset: FixedOffset::west_opt((tz_info.Bias + tz_info.StandardBias) * 60)?,
        dst_offset: FixedOffset::west_opt((tz_info.Bias + tz_info.DaylightBias) * 60)?,
        std_transition: systemtime_to_naive_dt(tz_info.StandardDate, year),
        dst_transition: systemtime_to_naive_dt(tz_info.DaylightDate, year),
    })
}

fn systemtime_to_naive_dt(st: SYSTEMTIME, year: i32) -> Option<NaiveDateTime> {
    if st.wYear == 0 && st.wMonth == 0 {
        return None; // No DST transitions for this year in this timezone.
    }
    let time = NaiveTime::from_hms_milli_opt(
        st.wHour as u32,
        st.wMinute as u32,
        st.wSecond as u32,
        st.wMilliseconds as u32,
    )?;
    let day_of_week = Weekday::try_from(u8::try_from(st.wDayOfWeek).ok()?).ok()?.pred();
    let date = if st.wYear == 0 {
        if let Some(date) =
            NaiveDate::from_weekday_of_month_opt(year, st.wMonth as u32, day_of_week, st.wDay as u8)
        {
            date
        } else if st.wDay == 5 {
            NaiveDate::from_weekday_of_month_opt(year, st.wMonth as u32, day_of_week, 4)?
        } else {
            return None;
        }
    } else {
        NaiveDate::from_ymd_opt(st.wYear as i32, st.wMonth as u32, st.wDay as u32)?
    };
    Some(date.and_time(time))
}

#[cfg(test)]
mod tests {
    use crate::offset::local::win_bindings::{
        SystemTimeToFileTime, TzSpecificLocalTimeToSystemTime, FILETIME, SYSTEMTIME,
    };
    use crate::{DateTime, Duration, FixedOffset, Local, NaiveDate, NaiveDateTime};
    use crate::{Datelike, TimeZone, Timelike};
    use std::mem::MaybeUninit;
    use std::ptr;

    #[test]
    fn verify_against_tz_specific_local_time_to_system_time() {
        // The implementation in Windows itself is the source of truth on how to work with the OS
        // timezone information. This test compares for every hour over a period of 125 years our
        // implementation to `TzSpecificLocalTimeToSystemTime`.
        //
        // This uses parts of a previous Windows `Local` implementation in chrono.
        fn from_local_time(dt: &NaiveDateTime) -> DateTime<Local> {
            let st = system_time_from_naive_date_time(dt);
            let utc_time = local_to_utc_time(&st);
            let utc_secs = system_time_as_unix_seconds(&utc_time);
            let local_secs = system_time_as_unix_seconds(&st);
            let offset = (local_secs - utc_secs) as i32;
            let offset = FixedOffset::east_opt(offset).unwrap();
            DateTime::from_naive_utc_and_offset(*dt - offset, offset)
        }
        fn system_time_from_naive_date_time(dt: &NaiveDateTime) -> SYSTEMTIME {
            SYSTEMTIME {
                // Valid values: 1601-30827
                wYear: dt.year() as u16,
                // Valid values:1-12
                wMonth: dt.month() as u16,
                // Valid values: 0-6, starting Sunday.
                // NOTE: enum returns 1-7, starting Monday, so we are
                // off here, but this is not currently used in local.
                wDayOfWeek: dt.weekday() as u16,
                // Valid values: 1-31
                wDay: dt.day() as u16,
                // Valid values: 0-23
                wHour: dt.hour() as u16,
                // Valid values: 0-59
                wMinute: dt.minute() as u16,
                // Valid values: 0-59
                wSecond: dt.second() as u16,
                // Valid values: 0-999
                wMilliseconds: 0,
            }
        }
        fn local_to_utc_time(local: &SYSTEMTIME) -> SYSTEMTIME {
            let mut sys_time = MaybeUninit::<SYSTEMTIME>::uninit();
            unsafe { TzSpecificLocalTimeToSystemTime(ptr::null(), local, sys_time.as_mut_ptr()) };
            // SAFETY: TzSpecificLocalTimeToSystemTime must have succeeded at this point, so we can
            // assume the value is initialized.
            unsafe { sys_time.assume_init() }
        }
        const HECTONANOSECS_IN_SEC: i64 = 10_000_000;
        const HECTONANOSEC_TO_UNIX_EPOCH: i64 = 11_644_473_600 * HECTONANOSECS_IN_SEC;
        fn system_time_as_unix_seconds(st: &SYSTEMTIME) -> i64 {
            let mut init = MaybeUninit::<FILETIME>::uninit();
            unsafe {
                SystemTimeToFileTime(st, init.as_mut_ptr());
            }
            // SystemTimeToFileTime must have succeeded at this point, so we can assume the value is
            // initalized.
            let filetime = unsafe { init.assume_init() };
            let bit_shift =
                ((filetime.dwHighDateTime as u64) << 32) | (filetime.dwLowDateTime as u64);
            (bit_shift as i64 - HECTONANOSEC_TO_UNIX_EPOCH) / HECTONANOSECS_IN_SEC
        }

        let mut date = NaiveDate::from_ymd_opt(1975, 1, 1).unwrap().and_hms_opt(0, 30, 0).unwrap();

        while date.year() < 2078 {
            // Windows doesn't handle non-existing dates, it just treats it as valid.
            if let Some(our_result) = Local.from_local_datetime(&date).earliest() {
                assert_eq!(from_local_time(&date), our_result);
            }
            date += Duration::hours(1);
        }
    }
}
