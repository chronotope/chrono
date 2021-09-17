// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The UTC (Coordinated Universal Time) time zone.

use core::fmt;

use super::{FixedOffset, LocalResult, Offset, TimeZone};
use naive::{NaiveDate, NaiveDateTime};
#[cfg(all(
    feature = "clock",
    not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind"))
))]
use std::time::{SystemTime, UNIX_EPOCH};
#[cfg(feature = "clock")]
use {Date, DateTime};

/// The UTC time zone. This is the most efficient time zone when you don't need the local time.
/// It is also used as an offset (which is also a dummy type).
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on the UTC struct is the preferred way to construct `DateTime<Utc>`
/// instances.
///
/// # Example
///
/// ```
/// use chrono::{DateTime, TimeZone, NaiveDateTime, Utc};
///
/// let dt = DateTime::<Utc>::from_utc(NaiveDateTime::from_timestamp(61, 0), Utc);
///
/// assert_eq!(Utc.timestamp(61, 0), dt);
/// assert_eq!(Utc.ymd(1970, 1, 1).and_hms(0, 1, 1), dt);
/// ```
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Utc;

#[cfg(feature = "clock")]
impl Utc {
    /// Returns a `Date` which corresponds to the current date.
    pub fn today() -> Date<Utc> {
        Utc::now().date()
    }

    /// Returns a `DateTime` which corresponds to the current date.
    #[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
    pub fn now() -> DateTime<Utc> {
        #[cfg(feature = "test-override")]
        {
            if let Some(t) = Self::test_get_override() {
                return t;
            }
        }

        let now =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
        let naive = NaiveDateTime::from_timestamp(now.as_secs() as i64, now.subsec_nanos() as u32);
        DateTime::from_utc(naive, Utc)
    }

    /// Returns a `DateTime` which corresponds to the current date.
    #[cfg(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind"))]
    pub fn now() -> DateTime<Utc> {
        #[cfg(feature = "test-override")]
        {
            if let Some(t) = Self::test_get_override() {
                return t;
            }
        }

        let now = js_sys::Date::new_0();
        DateTime::<Utc>::from(now)
    }
}

impl TimeZone for Utc {
    type Offset = Utc;

    fn from_offset(_state: &Utc) -> Utc {
        Utc
    }

    fn offset_from_local_date(&self, _local: &NaiveDate) -> LocalResult<Utc> {
        LocalResult::Single(Utc)
    }
    fn offset_from_local_datetime(&self, _local: &NaiveDateTime) -> LocalResult<Utc> {
        LocalResult::Single(Utc)
    }

    fn offset_from_utc_date(&self, _utc: &NaiveDate) -> Utc {
        Utc
    }
    fn offset_from_utc_datetime(&self, _utc: &NaiveDateTime) -> Utc {
        Utc
    }
}

impl Offset for Utc {
    fn fix(&self) -> FixedOffset {
        FixedOffset::east(0)
    }
}

impl fmt::Debug for Utc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Z")
    }
}

impl fmt::Display for Utc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "UTC")
    }
}

#[cfg(all(feature = "clock", feature = "test-override"))]
thread_local!(static OVERRIDE: std::cell::RefCell<Option<DateTime<Utc>>> = std::cell::RefCell::new(None));

#[cfg(all(feature = "clock", feature = "test-override"))]
impl Utc {
    #[cfg_attr(docsrs, doc(cfg(feature = "test-override")))]
    /// Override the value that will be returned by `Utc::now()`, for use in local tests.
    ///
    /// ```
    /// use chrono::{Utc, TimeZone, Datelike};
    /// fn is_today_leap_day() -> bool {
    ///     let today = Utc::today();
    ///     today.month() == 2 && today.day() == 29
    /// }
    ///
    /// Utc::test_override_now(Utc.ymd(2020, 2, 29).and_hms(0, 0, 0));
    /// assert!(is_today_leap_day());
    /// Utc::test_clear_override();
    /// ```
    pub fn test_override_now(datetime: DateTime<Utc>) {
        OVERRIDE.with(|o| {
            *o.borrow_mut() = Some(datetime);
        });
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "test-override")))]
    /// Clear an override created by `Utc::test_override_now()`.
    pub fn test_clear_override() {
        OVERRIDE.with(|o| {
            *o.borrow_mut() = None;
        });
    }

    /// Get the overriden time to return for `Utc::now()`.
    #[inline]
    fn test_get_override() -> Option<DateTime<Utc>> {
        OVERRIDE.with(|o| *o.borrow())
    }
}

#[cfg(test)]
mod tests {
    use super::Utc;
    use offset::TimeZone;

    #[cfg(feature = "test-override")]
    #[test]
    fn test_override() {
        assert!(Utc::now() > Utc.ymd(2021, 8, 7).and_hms(13, 0, 0));

        Utc::test_override_now(Utc.ymd(2020, 2, 29).and_hms(0, 0, 0));
        assert_eq!(Utc::now(), Utc.ymd(2020, 2, 29).and_hms(0, 0, 0));

        Utc::test_clear_override();
        assert!(Utc::now() > Utc.ymd(2021, 8, 7).and_hms(13, 0, 0));
    }

    #[cfg(feature = "test-override")]
    #[test]
    fn test_override_multiple_threads() {
        // stub
        use std::sync::{Arc, Barrier};
        use std::thread::spawn;

        let barrier = Arc::new(Barrier::new(3));

        let barrier_1 = barrier.clone();
        let thread_1 = spawn(move || {
            Utc::test_override_now(Utc.ymd(2020, 2, 29).and_hms(12, 0, 0));
            barrier_1.wait();

            assert_eq!(Utc::now(), Utc.ymd(2020, 2, 29).and_hms(12, 0, 0));
        });

        let barrier_2 = barrier.clone();
        let thread_2 = spawn(move || {
            Utc::test_override_now(Utc.ymd(2016, 2, 29).and_hms(12, 0, 0));
            barrier_2.wait();

            assert_eq!(Utc::now(), Utc.ymd(2016, 2, 29).and_hms(12, 0, 0));
        });

        let barrier_3 = barrier;
        let thread_3 = spawn(move || {
            barrier_3.wait();

            assert!(Utc::now() > Utc.ymd(2021, 8, 7).and_hms(13, 0, 0));
        });

        thread_1.join().expect("Thread 1 should succeed");
        thread_2.join().expect("Thread 2 should succeed");
        thread_3.join().expect("Thread 3 should succeed");
    }
}
