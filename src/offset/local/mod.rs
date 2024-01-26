// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The local (system) time zone.

#[cfg(any(unix, windows))]
use std::{cmp, cmp::Ordering};

#[cfg(any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"))]
use rkyv::{Archive, Deserialize, Serialize};

use super::fixed::FixedOffset;
use super::{LocalResult, TimeZone};
use crate::naive::{NaiveDate, NaiveDateTime, NaiveTime};
#[allow(deprecated)]
use crate::Date;
use crate::{DateTime, Utc};

#[cfg(unix)]
#[path = "unix.rs"]
mod inner;

#[cfg(windows)]
#[path = "windows.rs"]
mod inner;

#[cfg(all(windows, feature = "clock"))]
#[allow(unreachable_pub)]
mod win_bindings;

#[cfg(all(
    not(unix),
    not(windows),
    not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))
))]
mod inner {
    use crate::{FixedOffset, LocalResult, NaiveDateTime};

    pub(super) fn offset_from_utc_datetime(_utc_time: &NaiveDateTime) -> LocalResult<FixedOffset> {
        LocalResult::Single(FixedOffset::east_opt(0).unwrap())
    }

    pub(super) fn offset_from_local_datetime(
        _local_time: &NaiveDateTime,
    ) -> LocalResult<FixedOffset> {
        LocalResult::Single(FixedOffset::east_opt(0).unwrap())
    }
}

#[cfg(all(
    target_arch = "wasm32",
    feature = "wasmbind",
    not(any(target_os = "emscripten", target_os = "wasi"))
))]
mod inner {
    use crate::{Datelike, FixedOffset, LocalResult, NaiveDateTime, Timelike};

    pub(super) fn offset_from_utc_datetime(utc: &NaiveDateTime) -> LocalResult<FixedOffset> {
        let offset = js_sys::Date::from(utc.and_utc()).get_timezone_offset();
        LocalResult::Single(FixedOffset::west_opt((offset as i32) * 60).unwrap())
    }

    pub(super) fn offset_from_local_datetime(local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        let mut year = local.year();
        if year < 100 {
            // The API in `js_sys` does not let us create a `Date` with negative years.
            // And values for years from `0` to `99` map to the years `1900` to `1999`.
            // Shift the value by a multiple of 400 years until it is `>= 100`.
            let shift_cycles = (year - 100).div_euclid(400);
            year -= shift_cycles * 400;
        }
        let js_date = js_sys::Date::new_with_year_month_day_hr_min_sec(
            year as u32,
            local.month0() as i32,
            local.day() as i32,
            local.hour() as i32,
            local.minute() as i32,
            local.second() as i32,
            // ignore milliseconds, our representation of leap seconds may be problematic
        );
        let offset = js_date.get_timezone_offset();
        // We always get a result, even if this time does not exist or is ambiguous.
        LocalResult::Single(FixedOffset::west_opt((offset as i32) * 60).unwrap())
    }
}

#[cfg(unix)]
mod tz_info;

/// The local timescale.
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on the Local struct is the preferred way to construct `DateTime<Local>`
/// instances.
///
/// # Example
///
/// ```
/// use chrono::{Local, DateTime, TimeZone};
///
/// let dt1: DateTime<Local> = Local::now();
/// let dt2: DateTime<Local> = Local.timestamp_opt(0, 0).unwrap();
/// assert!(dt1 >= dt2);
/// ```
#[derive(Copy, Clone, Debug)]
#[cfg_attr(
    any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"),
    derive(Archive, Deserialize, Serialize),
    archive(compare(PartialEq)),
    archive_attr(derive(Clone, Copy, Debug))
)]
#[cfg_attr(feature = "rkyv-validation", archive(check_bytes))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Local;

impl Local {
    /// Returns a `Date` which corresponds to the current date.
    #[deprecated(since = "0.4.23", note = "use `Local::now()` instead")]
    #[allow(deprecated)]
    #[must_use]
    pub fn today() -> Date<Local> {
        Local::now().date()
    }

    /// Returns a `DateTime<Local>` which corresponds to the current date, time and offset from
    /// UTC.
    ///
    /// See also the similar [`Utc::now()`] which returns `DateTime<Utc>`, i.e. without the local
    /// offset.
    ///
    /// # Example
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// # use chrono::{DateTime, FixedOffset, Local};
    /// // Current local time
    /// let now = Local::now();
    ///
    /// // Current local date
    /// let today = now.date_naive();
    ///
    /// // Current local time, converted to `DateTime<FixedOffset>`
    /// let now_fixed_offset = Local::now().fixed_offset();
    /// // or
    /// let now_fixed_offset: DateTime<FixedOffset> = Local::now().into();
    ///
    /// // Current time in some timezone (let's use +05:00)
    /// // Note that it is usually more efficient to use `Utc::now` for this use case.
    /// let offset = FixedOffset::east_opt(5 * 60 * 60).unwrap();
    /// let now_with_offset = Local::now().with_timezone(&offset);
    /// ```
    pub fn now() -> DateTime<Local> {
        Utc::now().with_timezone(&Local)
    }
}

impl TimeZone for Local {
    type Offset = FixedOffset;

    fn from_offset(_offset: &FixedOffset) -> Local {
        Local
    }

    #[allow(deprecated)]
    fn offset_from_local_date(&self, local: &NaiveDate) -> LocalResult<FixedOffset> {
        // Get the offset at local midnight.
        self.offset_from_local_datetime(&local.and_time(NaiveTime::MIN))
    }

    fn offset_from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        inner::offset_from_local_datetime(local)
    }

    #[allow(deprecated)]
    fn offset_from_utc_date(&self, utc: &NaiveDate) -> FixedOffset {
        // Get the offset at midnight.
        self.offset_from_utc_datetime(&utc.and_time(NaiveTime::MIN))
    }

    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> FixedOffset {
        inner::offset_from_utc_datetime(utc).unwrap()
    }
}

#[cfg(any(unix, windows))]
pub(crate) struct TzInfo {
    // Offset from UTC during standard time.
    std_offset: FixedOffset,
    // Offset from UTC during daylight saving time.
    dst_offset: FixedOffset,
    // Transition from standard time to daylight saving time, given in local standard time.
    std_transition: Option<NaiveDateTime>,
    // Transition from daylight saving time to standard time, given in local daylight saving time.
    dst_transition: Option<NaiveDateTime>,
}

#[cfg(any(unix, windows))]
impl TzInfo {
    // Calculate the time in UTC fiven a local time, DST offsets and transition dates.
    // The transition dates are expected to be in the same year as `dt`.
    //
    // Notes on the implementation:
    //
    // If the first transition is to DST, the year starts in STD, transitions to DST, and ends with
    // STD. If the first transition is to STD, the opposite.
    //
    // For every transition we take in local time the earliest clock value, and latest clock value
    // (`transition_min` and `transition_max`).
    // - If the transition crates a gap, all times exclusive do not exist.
    //   => Open interval (*_transition_min..*_transition_max).
    // - If the transition crates an overlap, all times inclusive are ambiguous.
    //   => Closed interval [*_transition_min..*_transition_max]`
    // - The interval in between the transitions should have the remaining comparison operator
    //   (i.e. `>` if the transition uses `<=`).
    //
    // The result to return in `LocalResult::Single` is straightforward, `dst_offset` or
    // `std_offset` as appropriate.
    //
    // The correct order in `LocalResult::Ambiguous` is the offset right before the transition, then
    // the offset right after.
    fn lookup_with_dst_transitions(&self, dt: NaiveDateTime) -> LocalResult<FixedOffset> {
        let std_offset = self.std_offset;
        let dst_offset = self.dst_offset;
        let std_transition_after = self.std_transition.unwrap() + std_offset - dst_offset;
        let dst_transition_after = self.dst_transition.unwrap() + dst_offset - std_offset;

        // Depending on the dst and std offsets, *_transition_after can have a local time that is
        // before or after *_transition. To remain sane we define *_min and *_max values that have
        // the times in order.
        let std_transition_min = cmp::min(self.std_transition.unwrap(), std_transition_after);
        let std_transition_max = cmp::max(self.std_transition.unwrap(), std_transition_after);
        let dst_transition_min = cmp::min(self.dst_transition.unwrap(), dst_transition_after);
        let dst_transition_max = cmp::max(self.dst_transition.unwrap(), dst_transition_after);

        match std_offset.local_minus_utc().cmp(&dst_offset.local_minus_utc()) {
            Ordering::Equal => LocalResult::Single(std_offset),
            Ordering::Less => {
                if dst_transition_min < std_transition_min {
                    // Northern hemisphere DST.
                    // - The transition to DST happens at an earlier date than that to STD.
                    // - At DST start the local time is adjusted forwards (creating a gap), at DST
                    //   end the local time is adjusted backwards (creating ambiguous datetimes).
                    if dt > dst_transition_min && dt < dst_transition_max {
                        LocalResult::None
                    } else if dt >= dst_transition_max && dt < std_transition_min {
                        LocalResult::Single(dst_offset)
                    } else if dt >= std_transition_min && dt <= std_transition_max {
                        LocalResult::Ambiguous(dst_offset, std_offset)
                    } else {
                        LocalResult::Single(std_offset)
                    }
                } else {
                    // Southern hemisphere DST.
                    // - The transition to STD happens at a earlier date than that to DST.
                    // - At DST start the local time is adjusted forwards (creating a gap), at DST
                    //   end the local time is adjusted backwards (creating ambiguous datetimes).
                    if dt >= std_transition_min && dt <= std_transition_max {
                        LocalResult::Ambiguous(dst_offset, std_offset)
                    } else if dt > std_transition_max && dt <= dst_transition_min {
                        LocalResult::Single(std_offset)
                    } else if dt > dst_transition_min && dt < dst_transition_max {
                        LocalResult::None
                    } else {
                        LocalResult::Single(dst_offset)
                    }
                }
            }
            Ordering::Greater => {
                if dst_transition_min < std_transition_min {
                    // Southern hemisphere reverse DST.
                    // - The transition to DST happens at an earlier date than that to STD.
                    // - At DST start the local time is adjusted backwards (creating ambiguous
                    //   datetimes), at DST end the local time is adjusted forwards (creating a gap)
                    if dt >= dst_transition_min && dt <= dst_transition_max {
                        LocalResult::Ambiguous(std_offset, dst_offset)
                    } else if dt > dst_transition_max && dt <= std_transition_min {
                        LocalResult::Single(dst_offset)
                    } else if dt > std_transition_min && dt < std_transition_max {
                        LocalResult::None
                    } else {
                        LocalResult::Single(std_offset)
                    }
                } else {
                    // Northern hemisphere reverse DST.
                    // - The transition to STD happens at a earlier date than that to DST.
                    // - At DST start the local time is adjusted backwards (creating ambiguous
                    //   datetimes), at DST end the local time is adjusted forwards (creating a gap)
                    if dt > std_transition_min && dt < std_transition_max {
                        LocalResult::None
                    } else if dt >= std_transition_max && dt < dst_transition_min {
                        LocalResult::Single(std_offset)
                    } else if dt >= dst_transition_min && dt <= dst_transition_max {
                        LocalResult::Ambiguous(std_offset, dst_offset)
                    } else {
                        LocalResult::Single(dst_offset)
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Local;
    #[cfg(any(unix, windows))]
    use crate::offset::local::TzInfo;
    use crate::offset::TimeZone;
    use crate::{Datelike, Duration, Utc};
    #[cfg(any(unix, windows))]
    use crate::{FixedOffset, LocalResult, NaiveDate};

    #[test]
    fn verify_correct_offsets() {
        let now = Local::now();
        let from_local = Local.from_local_datetime(&now.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&now.naive_utc());

        assert_eq!(now.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(now.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(now, from_local);
        assert_eq!(now, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_past() {
        // let distant_past = Local::now() - Duration::days(365 * 100);
        let distant_past = Local::now() - Duration::days(250 * 31);
        let from_local = Local.from_local_datetime(&distant_past.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&distant_past.naive_utc());

        assert_eq!(distant_past.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(distant_past.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(distant_past, from_local);
        assert_eq!(distant_past, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_future() {
        let distant_future = Local::now() + Duration::days(250 * 31);
        let from_local = Local.from_local_datetime(&distant_future.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&distant_future.naive_utc());

        assert_eq!(
            distant_future.offset().local_minus_utc(),
            from_local.offset().local_minus_utc()
        );
        assert_eq!(distant_future.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(distant_future, from_local);
        assert_eq!(distant_future, from_utc);
    }

    #[test]
    fn test_local_date_sanity_check() {
        // issue #27
        assert_eq!(Local.with_ymd_and_hms(2999, 12, 28, 0, 0, 0).unwrap().day(), 28);
    }

    #[test]
    fn test_leap_second() {
        // issue #123
        let today = Utc::now().date_naive();

        if let Some(dt) = today.and_hms_milli_opt(15, 2, 59, 1000) {
            let timestr = dt.time().to_string();
            // the OS API may or may not support the leap second,
            // but there are only two sensible options.
            assert!(
                timestr == "15:02:60" || timestr == "15:03:00",
                "unexpected timestr {:?}",
                timestr
            );
        }

        if let Some(dt) = today.and_hms_milli_opt(15, 2, 3, 1234) {
            let timestr = dt.time().to_string();
            assert!(
                timestr == "15:02:03.234" || timestr == "15:02:04.234",
                "unexpected timestr {:?}",
                timestr
            );
        }
    }

    #[test]
    #[cfg(any(unix, windows))]
    fn test_lookup_with_dst_transitions() {
        #[track_caller]
        #[allow(clippy::too_many_arguments)]
        fn compare_lookup(
            tz_info: &TzInfo,
            y: i32,
            m: u32,
            d: u32,
            h: u32,
            n: u32,
            s: u32,
            result: LocalResult<FixedOffset>,
        ) {
            let dt = NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap();
            assert_eq!(tz_info.lookup_with_dst_transitions(dt), result);
        }

        // dst transition before std transition
        // dst offset > std offset
        let std = FixedOffset::east_opt(3 * 60 * 60).unwrap();
        let dst = FixedOffset::east_opt(4 * 60 * 60).unwrap();
        let tz_info = TzInfo {
            std_offset: std,
            dst_offset: dst,
            std_transition: Some(
                NaiveDate::from_ymd_opt(2023, 10, 29).unwrap().and_hms_opt(3, 0, 0).unwrap(),
            ),
            dst_transition: Some(
                NaiveDate::from_ymd_opt(2023, 3, 26).unwrap().and_hms_opt(2, 0, 0).unwrap(),
            ),
        };
        compare_lookup(&tz_info, 2023, 3, 26, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&tz_info, 2023, 3, 26, 2, 0, 0, LocalResult::Single(std));
        compare_lookup(&tz_info, 2023, 3, 26, 2, 30, 0, LocalResult::None);
        compare_lookup(&tz_info, 2023, 3, 26, 3, 0, 0, LocalResult::Single(dst));
        compare_lookup(&tz_info, 2023, 3, 26, 4, 0, 0, LocalResult::Single(dst));

        compare_lookup(&tz_info, 2023, 10, 29, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&tz_info, 2023, 10, 29, 2, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&tz_info, 2023, 10, 29, 2, 30, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&tz_info, 2023, 10, 29, 3, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&tz_info, 2023, 10, 29, 4, 0, 0, LocalResult::Single(std));

        // std transition before dst transition
        // dst offset > std offset
        let std = FixedOffset::east_opt(-5 * 60 * 60).unwrap();
        let dst = FixedOffset::east_opt(-4 * 60 * 60).unwrap();
        let tz_info = TzInfo {
            std_offset: std,
            dst_offset: dst,
            std_transition: Some(
                NaiveDate::from_ymd_opt(2023, 3, 24).unwrap().and_hms_opt(3, 0, 0).unwrap(),
            ),
            dst_transition: Some(
                NaiveDate::from_ymd_opt(2023, 10, 27).unwrap().and_hms_opt(2, 0, 0).unwrap(),
            ),
        };
        compare_lookup(&tz_info, 2023, 3, 24, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&tz_info, 2023, 3, 24, 2, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&tz_info, 2023, 3, 24, 2, 30, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&tz_info, 2023, 3, 24, 3, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&tz_info, 2023, 3, 24, 4, 0, 0, LocalResult::Single(std));

        compare_lookup(&tz_info, 2023, 10, 27, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&tz_info, 2023, 10, 27, 2, 0, 0, LocalResult::Single(std));
        compare_lookup(&tz_info, 2023, 10, 27, 2, 30, 0, LocalResult::None);
        compare_lookup(&tz_info, 2023, 10, 27, 3, 0, 0, LocalResult::Single(dst));
        compare_lookup(&tz_info, 2023, 10, 27, 4, 0, 0, LocalResult::Single(dst));

        // dst transition before std transition
        // dst offset < std offset
        let std = FixedOffset::east_opt(3 * 60 * 60).unwrap();
        let dst = FixedOffset::east_opt((2 * 60 + 30) * 60).unwrap();
        let tz_info = TzInfo {
            std_offset: std,
            dst_offset: dst,
            std_transition: Some(
                NaiveDate::from_ymd_opt(2023, 10, 29).unwrap().and_hms_opt(2, 0, 0).unwrap(),
            ),
            dst_transition: Some(
                NaiveDate::from_ymd_opt(2023, 3, 26).unwrap().and_hms_opt(2, 30, 0).unwrap(),
            ),
        };
        compare_lookup(&tz_info, 2023, 3, 26, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&tz_info, 2023, 3, 26, 2, 0, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&tz_info, 2023, 3, 26, 2, 15, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&tz_info, 2023, 3, 26, 2, 30, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&tz_info, 2023, 3, 26, 3, 0, 0, LocalResult::Single(dst));

        compare_lookup(&tz_info, 2023, 10, 29, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&tz_info, 2023, 10, 29, 2, 0, 0, LocalResult::Single(dst));
        compare_lookup(&tz_info, 2023, 10, 29, 2, 15, 0, LocalResult::None);
        compare_lookup(&tz_info, 2023, 10, 29, 2, 30, 0, LocalResult::Single(std));
        compare_lookup(&tz_info, 2023, 10, 29, 3, 0, 0, LocalResult::Single(std));

        // std transition before dst transition
        // dst offset < std offset
        let std = FixedOffset::east_opt(-(4 * 60 + 30) * 60).unwrap();
        let dst = FixedOffset::east_opt(-5 * 60 * 60).unwrap();
        let tz_info = TzInfo {
            std_offset: std,
            dst_offset: dst,
            std_transition: Some(
                NaiveDate::from_ymd_opt(2023, 3, 24).unwrap().and_hms_opt(2, 0, 0).unwrap(),
            ),
            dst_transition: Some(
                NaiveDate::from_ymd_opt(2023, 10, 27).unwrap().and_hms_opt(2, 30, 0).unwrap(),
            ),
        };
        compare_lookup(&tz_info, 2023, 3, 24, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&tz_info, 2023, 3, 24, 2, 0, 0, LocalResult::Single(dst));
        compare_lookup(&tz_info, 2023, 3, 24, 2, 15, 0, LocalResult::None);
        compare_lookup(&tz_info, 2023, 3, 24, 2, 30, 0, LocalResult::Single(std));
        compare_lookup(&tz_info, 2023, 3, 24, 3, 0, 0, LocalResult::Single(std));

        compare_lookup(&tz_info, 2023, 10, 27, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&tz_info, 2023, 10, 27, 2, 0, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&tz_info, 2023, 10, 27, 2, 15, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&tz_info, 2023, 10, 27, 2, 30, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&tz_info, 2023, 10, 27, 3, 0, 0, LocalResult::Single(dst));
    }

    #[test]
    #[cfg(feature = "rkyv-validation")]
    fn test_rkyv_validation() {
        let local = Local;
        // Local is a ZST and serializes to 0 bytes
        let bytes = rkyv::to_bytes::<_, 0>(&local).unwrap();
        assert_eq!(bytes.len(), 0);

        // but is deserialized to an archived variant without a
        // wrapping object
        assert_eq!(rkyv::from_bytes::<Local>(&bytes).unwrap(), super::ArchivedLocal);
    }
}
