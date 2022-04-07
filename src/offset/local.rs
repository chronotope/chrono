// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The local (system) time zone.

use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use super::fixed::FixedOffset;
use super::{LocalResult, TimeZone};
#[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
use crate::naive::NaiveTime;
use crate::naive::{NaiveDate, NaiveDateTime};
use crate::{Date, DateTime};
#[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
use crate::{Datelike, Timelike};

#[cfg(all(not(unix), not(windows)))]
#[path = "sys/stub.rs"]
mod inner;

#[cfg(unix)]
#[path = "sys/unix.rs"]
mod inner;

#[cfg(windows)]
#[path = "sys/windows.rs"]
mod inner;

use inner::{local_tm_to_time, time_to_local_tm, utc_tm_to_time};

/// Converts a `time::Tm` struct into the timezone-aware `DateTime`.
/// This assumes that `time` is working correctly, i.e. any error is fatal.
#[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
fn tm_to_datetime(mut tm: Tm) -> DateTime<Local> {
    if tm.tm_sec >= 60 {
        tm.tm_nsec += (tm.tm_sec - 59) * 1_000_000_000;
        tm.tm_sec = 59;
    }

    #[cfg(not(windows))]
    fn tm_to_naive_date(tm: &Tm) -> NaiveDate {
        // from_yo is more efficient than from_ymd (since it's the internal representation).
        NaiveDate::from_yo(tm.tm_year + 1900, tm.tm_yday as u32 + 1)
    }

    #[cfg(windows)]
    fn tm_to_naive_date(tm: &Tm) -> NaiveDate {
        // ...but tm_yday is broken in Windows (issue #85)
        NaiveDate::from_ymd(tm.tm_year + 1900, tm.tm_mon as u32 + 1, tm.tm_mday as u32)
    }

    let date = tm_to_naive_date(&tm);
    let time = NaiveTime::from_hms_nano(
        tm.tm_hour as u32,
        tm.tm_min as u32,
        tm.tm_sec as u32,
        tm.tm_nsec as u32,
    );
    let offset = FixedOffset::east(tm.tm_utcoff);
    DateTime::from_utc(date.and_time(time) - offset, offset)
}

/// Converts a local `NaiveDateTime` to the `time::Timespec`.
#[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
fn datetime_to_timespec(d: &NaiveDateTime, local: bool) -> Timespec {
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

    Timespec {
        sec: match local {
            false => utc_tm_to_time(&tm),
            true => local_tm_to_time(&tm),
        },
        nsec: tm.tm_nsec,
    }
}

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
        tm_to_datetime(Timespec::now().local())
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
        let timespec = datetime_to_timespec(local, true);

        // datetime_to_timespec completely ignores leap seconds, so we need to adjust for them
        let mut tm = timespec.local();
        assert_eq!(tm.tm_nsec, 0);
        tm.tm_nsec = local.nanosecond() as i32;

        LocalResult::Single(tm_to_datetime(tm))
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
        let timespec = datetime_to_timespec(utc, false);

        // datetime_to_timespec completely ignores leap seconds, so we need to adjust for them
        let mut tm = timespec.local();
        assert_eq!(tm.tm_nsec, 0);
        tm.tm_nsec = utc.nanosecond() as i32;

        tm_to_datetime(tm)
    }
}

/// A record specifying a time value in seconds and nanoseconds, where
/// nanoseconds represent the offset from the given second.
///
/// For example a timespec of 1.2 seconds after the beginning of the epoch would
/// be represented as {sec: 1, nsec: 200000000}.
pub(super) struct Timespec {
    sec: i64,
    nsec: i32,
}

impl Timespec {
    /// Constructs a timespec representing the current time in UTC.
    pub(super) fn now() -> Timespec {
        let st =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
        Timespec { sec: st.as_secs() as i64, nsec: st.subsec_nanos() as i32 }
    }

    /// Converts this timespec into the system's local time.
    pub(super) fn local(self) -> Tm {
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
        time_to_local_tm(self.sec, &mut tm);
        tm.tm_nsec = self.nsec;
        tm
    }
}

/// Holds a calendar date and time broken down into its components (year, month,
/// day, and so on), also called a broken-down time value.
// FIXME: use c_int instead of i32?
#[cfg(feature = "clock")]
#[repr(C)]
pub(crate) struct Tm {
    /// Seconds after the minute - [0, 60]
    pub(crate) tm_sec: i32,

    /// Minutes after the hour - [0, 59]
    pub(crate) tm_min: i32,

    /// Hours after midnight - [0, 23]
    pub(crate) tm_hour: i32,

    /// Day of the month - [1, 31]
    pub(crate) tm_mday: i32,

    /// Months since January - [0, 11]
    pub(crate) tm_mon: i32,

    /// Years since 1900
    pub(crate) tm_year: i32,

    /// Days since Sunday - [0, 6]. 0 = Sunday, 1 = Monday, ..., 6 = Saturday.
    pub(crate) tm_wday: i32,

    /// Days since January 1 - [0, 365]
    pub(crate) tm_yday: i32,

    /// Daylight Saving Time flag.
    ///
    /// This value is positive if Daylight Saving Time is in effect, zero if
    /// Daylight Saving Time is not in effect, and negative if this information
    /// is not available.
    pub(crate) tm_isdst: i32,

    /// Identifies the time zone that was used to compute this broken-down time
    /// value, including any adjustment for Daylight Saving Time. This is the
    /// number of seconds east of UTC. For example, for U.S. Pacific Daylight
    /// Time, the value is `-7*60*60 = -25200`.
    pub(crate) tm_utcoff: i32,

    /// Nanoseconds after the second - [0, 10<sup>9</sup> - 1]
    pub(crate) tm_nsec: i32,
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
