// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::io;
use std::mem;
use std::time::{SystemTime, UNIX_EPOCH};

use winapi::shared::minwindef::*;
use winapi::um::minwinbase::SYSTEMTIME;
use winapi::um::timezoneapi::*;

use super::{FixedOffset, Local};
use crate::error::{ChronoError, ChronoErrorKind};
use crate::offset::LocalResult;
use crate::{DateTime, Datelike, NaiveDate, NaiveDateTime, NaiveTime, Timelike};

pub(super) fn now() -> Result<DateTime<Local>, ChronoError> {
    tm_to_datetime(Timespec::now()?.local()?)
}

/// Converts a local `NaiveDateTime` to the `time::Timespec`.
pub(super) fn naive_to_local(
    d: &NaiveDateTime,
    local: bool,
) -> Result<LocalResult<DateTime<Local>>, ChronoError> {
    let tm = Tm {
        tm_sec: d.second() as i32,
        tm_min: d.minute() as i32,
        tm_hour: d.hour() as i32,
        tm_mday: d.day() as i32,
        tm_mon: d.month0() as i32, // yes, C is that strange...
        tm_year: d.year() - 1900,  // this doesn't underflow, we know that d is `NaiveDateTime`.
        tm_wday: 0,                // to_local ignores this
        tm_yday: 0,                // and this
        tm_isdst: -1,
        // This seems pretty fake?
        tm_utcoff: if local { 1 } else { 0 },
        // do not set this, OS APIs are heavily inconsistent in terms of leap second handling
        tm_nsec: 0,
    };

    let spec = Timespec {
        sec: match local {
            false => utc_tm_to_time(&tm)?,
            true => local_tm_to_time(&tm)?,
        },
        nsec: tm.tm_nsec,
    };

    // Adjust for leap seconds
    let mut tm = spec.local()?;
    assert_eq!(tm.tm_nsec, 0);
    tm.tm_nsec = d.nanosecond() as i32;

    // #TODO - there should be ambiguous cases, investigate?
    Ok(LocalResult::Single(tm_to_datetime(tm)?))
}

/// Converts a `time::Tm` struct into the timezone-aware `DateTime`.
fn tm_to_datetime(mut tm: Tm) -> Result<DateTime<Local>, ChronoError> {
    if tm.tm_sec >= 60 {
        tm.tm_nsec += (tm.tm_sec - 59) * 1_000_000_000;
        tm.tm_sec = 59;
    }

    let date = NaiveDate::from_ymd(tm.tm_year + 1900, tm.tm_mon as u32 + 1, tm.tm_mday as u32)?;
    let time = NaiveTime::from_hms_nano(
        tm.tm_hour as u32,
        tm.tm_min as u32,
        tm.tm_sec as u32,
        tm.tm_nsec as u32,
    )?;

    let offset = FixedOffset::east(tm.tm_utcoff)?;
    Ok(DateTime::from_utc(date.and_time(time) - offset, offset))
}

/// A record specifying a time value in seconds and nanoseconds, where
/// nanoseconds represent the offset from the given second.
///
/// For example a timespec of 1.2 seconds after the beginning of the epoch would
/// be represented as {sec: 1, nsec: 200000000}.
struct Timespec {
    sec: i64,
    nsec: i32,
}

impl Timespec {
    /// Constructs a timespec representing the current time in UTC.
    fn now() -> Result<Timespec, ChronoError> {
        let st = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| ChronoErrorKind::SystemTimeBeforeEpoch)?;
        Ok(Timespec { sec: st.as_secs() as i64, nsec: st.subsec_nanos() as i32 })
    }

    /// Converts this timespec into the system's local time.
    fn local(self) -> Result<Tm, ChronoError> {
        let mut tm = Tm {
            tm_sec: 0,
            tm_min: 0,
            tm_hour: 0,
            tm_mday: 0,
            tm_mon: 0,
            tm_year: 0,
            tm_wday: 0,
            tm_yday: 0,
            tm_isdst: 0,
            tm_utcoff: 0,
            tm_nsec: 0,
        };
        time_to_local_tm(self.sec, &mut tm)?;
        tm.tm_nsec = self.nsec;
        Ok(tm)
    }
}

/// Holds a calendar date and time broken down into its components (year, month,
/// day, and so on), also called a broken-down time value.
// FIXME: use c_int instead of i32?
#[repr(C)]
struct Tm {
    /// Seconds after the minute - [0, 60]
    tm_sec: i32,

    /// Minutes after the hour - [0, 59]
    tm_min: i32,

    /// Hours after midnight - [0, 23]
    tm_hour: i32,

    /// Day of the month - [1, 31]
    tm_mday: i32,

    /// Months since January - [0, 11]
    tm_mon: i32,

    /// Years since 1900
    tm_year: i32,

    /// Days since Sunday - [0, 6]. 0 = Sunday, 1 = Monday, ..., 6 = Saturday.
    tm_wday: i32,

    /// Days since January 1 - [0, 365]
    tm_yday: i32,

    /// Daylight Saving Time flag.
    ///
    /// This value is positive if Daylight Saving Time is in effect, zero if
    /// Daylight Saving Time is not in effect, and negative if this information
    /// is not available.
    tm_isdst: i32,

    /// Identifies the time zone that was used to compute this broken-down time
    /// value, including any adjustment for Daylight Saving Time. This is the
    /// number of seconds east of UTC. For example, for U.S. Pacific Daylight
    /// Time, the value is `-7*60*60 = -25200`.
    tm_utcoff: i32,

    /// Nanoseconds after the second - [0, 10<sup>9</sup> - 1]
    tm_nsec: i32,
}

const HECTONANOSECS_IN_SEC: i64 = 10_000_000;
const HECTONANOSEC_TO_UNIX_EPOCH: i64 = 11_644_473_600 * HECTONANOSECS_IN_SEC;

fn time_to_file_time(sec: i64) -> FILETIME {
    let t = ((sec * HECTONANOSECS_IN_SEC) + HECTONANOSEC_TO_UNIX_EPOCH) as u64;
    FILETIME { dwLowDateTime: t as DWORD, dwHighDateTime: (t >> 32) as DWORD }
}

fn file_time_as_u64(ft: &FILETIME) -> u64 {
    ((ft.dwHighDateTime as u64) << 32) | (ft.dwLowDateTime as u64)
}

fn file_time_to_unix_seconds(ft: &FILETIME) -> i64 {
    let t = file_time_as_u64(ft) as i64;
    ((t - HECTONANOSEC_TO_UNIX_EPOCH) / HECTONANOSECS_IN_SEC) as i64
}

fn system_time_to_file_time(sys: &SYSTEMTIME) -> FILETIME {
    unsafe {
        let mut ft = mem::zeroed();
        SystemTimeToFileTime(sys, &mut ft);
        ft
    }
}

fn tm_to_system_time(tm: &Tm) -> SYSTEMTIME {
    let mut sys: SYSTEMTIME = unsafe { mem::zeroed() };
    sys.wSecond = tm.tm_sec as WORD;
    sys.wMinute = tm.tm_min as WORD;
    sys.wHour = tm.tm_hour as WORD;
    sys.wDay = tm.tm_mday as WORD;
    sys.wDayOfWeek = tm.tm_wday as WORD;
    sys.wMonth = (tm.tm_mon + 1) as WORD;
    sys.wYear = (tm.tm_year + 1900) as WORD;
    sys
}

fn system_time_to_tm(sys: &SYSTEMTIME, tm: &mut Tm) {
    tm.tm_sec = sys.wSecond as i32;
    tm.tm_min = sys.wMinute as i32;
    tm.tm_hour = sys.wHour as i32;
    tm.tm_mday = sys.wDay as i32;
    tm.tm_wday = sys.wDayOfWeek as i32;
    tm.tm_mon = (sys.wMonth - 1) as i32;
    tm.tm_year = (sys.wYear - 1900) as i32;
    tm.tm_yday = yday(tm.tm_year, tm.tm_mon + 1, tm.tm_mday);

    fn yday(year: i32, month: i32, day: i32) -> i32 {
        let leap = if month > 2 {
            if year % 4 == 0 {
                1
            } else {
                2
            }
        } else {
            0
        };
        let july = if month > 7 { 1 } else { 0 };

        (month - 1) * 30 + month / 2 + (day - 1) - leap + july
    }
}

macro_rules! call {
    ($name:ident($($arg:expr),*)) => {
        if $name($($arg),*) == 0 {
            return Err(ChronoError::new(ChronoErrorKind::SystemError(io::Error::last_os_error())))
        }
    }
}

fn time_to_local_tm(sec: i64, tm: &mut Tm) -> Result<(), ChronoError> {
    let ft = time_to_file_time(sec);
    unsafe {
        let mut utc = mem::zeroed();
        let mut local = mem::zeroed();
        call!(FileTimeToSystemTime(&ft, &mut utc));
        call!(SystemTimeToTzSpecificLocalTime(0 as *const _, &mut utc, &mut local));
        system_time_to_tm(&local, tm);

        let local = system_time_to_file_time(&local);
        let local_sec = file_time_to_unix_seconds(&local);

        let mut tz = mem::zeroed();
        GetTimeZoneInformation(&mut tz);

        // SystemTimeToTzSpecificLocalTime already applied the biases so
        // check if it non standard
        tm.tm_utcoff = (local_sec - sec) as i32;
        tm.tm_isdst = if tm.tm_utcoff == -60 * (tz.Bias + tz.StandardBias) { 0 } else { 1 };
        Ok(())
    }
}

fn utc_tm_to_time(tm: &Tm) -> Result<i64, ChronoError> {
    unsafe {
        let mut ft = mem::zeroed();
        let sys_time = tm_to_system_time(tm);
        call!(SystemTimeToFileTime(&sys_time, &mut ft));
        Ok(file_time_to_unix_seconds(&ft))
    }
}

fn local_tm_to_time(tm: &Tm) -> Result<i64, ChronoError> {
    unsafe {
        let mut ft = mem::zeroed();
        let mut utc = mem::zeroed();
        let mut sys_time = tm_to_system_time(tm);
        call!(TzSpecificLocalTimeToSystemTime(0 as *mut _, &mut sys_time, &mut utc));
        call!(SystemTimeToFileTime(&utc, &mut ft));
        Ok(file_time_to_unix_seconds(&ft))
    }
}
