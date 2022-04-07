// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The local (system) time zone.

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use super::fixed::FixedOffset;
use super::{LocalResult, TimeZone};
use crate::naive::{NaiveDate, NaiveDateTime};
use crate::{Date, DateTime};

#[cfg(all(not(unix), not(windows)))]
#[path = "sys/stub.rs"]
mod inner;

#[cfg(unix)]
#[path = "sys/unix.rs"]
mod inner;

#[cfg(windows)]
#[path = "sys/windows.rs"]
mod inner;

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
/// let dt: DateTime<Local> = Local::now();
/// let dt: DateTime<Local> = Local.timestamp(0, 0);
/// ```
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct Local;

impl Local {
    /// Returns a `Date` which corresponds to the current date.
    pub fn today() -> Date<Local> {
        Local::now().date()
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
    pub fn now() -> DateTime<Local> {
        inner::now()
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind"))]
    pub fn now() -> DateTime<Local> {
        use super::Utc;
        let now: DateTime<Utc> = super::Utc::now();

        // Workaround missing timezone logic in `time` crate
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        DateTime::from_utc(now.naive_utc(), offset)
    }
}

impl TimeZone for Local {
    type Offset = FixedOffset;

    fn from_offset(_offset: &FixedOffset) -> Local {
        Local
    }

    // they are easier to define in terms of the finished date and time unlike other offsets
    fn offset_from_local_date(&self, local: &NaiveDate) -> LocalResult<FixedOffset> {
        self.from_local_date(local).map(|date| *date.offset())
    }

    fn offset_from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        self.from_local_datetime(local).map(|datetime| *datetime.offset())
    }

    fn offset_from_utc_date(&self, utc: &NaiveDate) -> FixedOffset {
        *self.from_utc_date(utc).offset()
    }

    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> FixedOffset {
        *self.from_utc_datetime(utc).offset()
    }

    // override them for avoiding redundant works
    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<Local>> {
        // this sounds very strange, but required for keeping `TimeZone::ymd` sane.
        // in the other words, we use the offset at the local midnight
        // but keep the actual date unaltered (much like `FixedOffset`).
        let midnight = self.from_local_datetime(&local.and_hms(0, 0, 0));
        midnight.map(|datetime| Date::from_utc(*local, *datetime.offset()))
    }

    #[cfg(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind"))]
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Local>> {
        let mut local = local.clone();
        // Get the offset from the js runtime
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        local -= crate::Duration::seconds(offset.local_minus_utc() as i64);
        LocalResult::Single(DateTime::from_utc(local, offset))
    }

    #[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Local>> {
        LocalResult::Single(inner::naive_to_local(local, true))
    }

    fn from_utc_date(&self, utc: &NaiveDate) -> Date<Local> {
        let midnight = self.from_utc_datetime(&utc.and_hms(0, 0, 0));
        Date::from_utc(*utc, *midnight.offset())
    }

    #[cfg(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind"))]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Local> {
        // Get the offset from the js runtime
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        DateTime::from_utc(*utc, offset)
    }

    #[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Local> {
        inner::naive_to_local(utc, false)
    }
}

#[cfg(test)]
mod tests {
    use super::Local;
    use crate::offset::TimeZone;
    use crate::Datelike;

    #[test]
    fn test_local_date_sanity_check() {
        // issue #27
        assert_eq!(Local.ymd(2999, 12, 28).day(), 28);
    }

    #[test]
    fn test_leap_second() {
        // issue #123
        let today = Local::today();

        let dt = today.and_hms_milli(1, 2, 59, 1000);
        let timestr = dt.time().to_string();
        // the OS API may or may not support the leap second,
        // but there are only two sensible options.
        assert!(timestr == "01:02:60" || timestr == "01:03:00", "unexpected timestr {:?}", timestr);

        let dt = today.and_hms_milli(1, 2, 3, 1234);
        let timestr = dt.time().to_string();
        assert!(
            timestr == "01:02:03.234" || timestr == "01:02:04.234",
            "unexpected timestr {:?}",
            timestr
        );
    }
}
