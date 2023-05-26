// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The local (system) time zone.

#[cfg(feature = "rkyv")]
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
    use crate::{FixedOffset, LocalResult, NaiveDateTime};

    pub(super) fn offset_from_utc_datetime(_utc: &NaiveDateTime) -> LocalResult<FixedOffset> {
        let offset = js_sys::Date::new_0().get_timezone_offset();
        LocalResult::Single(FixedOffset::west_opt((offset as i32) * 60).unwrap())
    }

    pub(super) fn offset_from_local_datetime(local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        offset_from_utc_datetime(local)
    }
}

#[cfg(unix)]
mod tz_info;

/// The local timescale. This is implemented via the standard `time` crate.
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
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
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

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))]
    #[must_use]
    pub fn now() -> DateTime<Local> {
        Utc::now().with_timezone(&Local)
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))]
    #[must_use]
    pub fn now() -> DateTime<Local> {
        use super::Utc;
        let now: DateTime<Utc> = super::Utc::now();

        // Workaround missing timezone logic in `time` crate
        let offset =
            FixedOffset::west_opt((js_sys::Date::new_0().get_timezone_offset() as i32) * 60)
                .unwrap();
        DateTime::from_utc(now.naive_utc(), offset)
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

#[cfg(test)]
mod tests {
    use super::Local;
    use crate::offset::TimeZone;
    use crate::{Datelike, Duration, Utc};

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

    /// Test Issue #866
    #[test]
    fn test_issue_866() {
        #[allow(deprecated)]
        let local_20221106 = Local.ymd(2022, 11, 6);
        let _dt_20221106 = local_20221106.and_hms_milli_opt(1, 2, 59, 1000).unwrap();
    }
}
