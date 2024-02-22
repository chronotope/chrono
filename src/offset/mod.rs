// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The time zone, which calculates offsets from the local time to UTC.
//!
//! There are four operations provided by the `TimeZone` trait:
//!
//! 1. Converting the local `NaiveDateTime` to `DateTime<Tz>`
//! 2. Converting the UTC `NaiveDateTime` to `DateTime<Tz>`
//! 3. Converting `DateTime<Tz>` to the local `NaiveDateTime`
//! 4. Constructing `DateTime<Tz>` objects from various offsets
//!
//! 1 is used for constructors. 2 is used for the `with_timezone` method of date and time types.
//! 3 is used for other methods, e.g. `year()` or `format()`, and provided by an associated type
//! which implements `Offset` (which then passed to `TimeZone` for actual implementations).
//! Technically speaking `TimeZone` has a total knowledge about given timescale,
//! but `Offset` is used as a cache to avoid the repeated conversion
//! and provides implementations for 1 and 3.
//! An `TimeZone` instance can be reconstructed from the corresponding `Offset` instance.

use core::fmt;

use crate::naive::{NaiveDate, NaiveDateTime};
use crate::{DateTime, Error};

pub(crate) mod fixed;
pub use self::fixed::FixedOffset;

#[cfg(feature = "clock")]
pub(crate) mod local;
#[cfg(feature = "clock")]
pub use self::local::Local;

pub(crate) mod utc;
pub use self::utc::Utc;

/// The conversion result from the local time to the timezone-aware datetime types.
#[derive(Clone, PartialEq, Debug, Copy, Eq, Hash)]
pub enum LocalResult<T> {
    /// Given local time representation is invalid.
    /// This can occur when, for example, the positive timezone transition.
    None,
    /// Given local time representation has a single unique result.
    Single(T),
    /// Given local time representation has multiple results and thus ambiguous.
    /// This can occur when, for example, the negative timezone transition.
    Ambiguous(T /* min */, T /* max */),
}

impl<T> LocalResult<T> {
    /// Returns `Some` only when the conversion result is unique, or `None` otherwise.
    #[must_use]
    pub fn single(self) -> Option<T> {
        match self {
            LocalResult::Single(t) => Some(t),
            _ => None,
        }
    }

    /// Returns `Some` for the earliest possible conversion result, or `None` if none.
    #[must_use]
    pub fn earliest(self) -> Option<T> {
        match self {
            LocalResult::Single(t) | LocalResult::Ambiguous(t, _) => Some(t),
            _ => None,
        }
    }

    /// Returns `Some` for the latest possible conversion result, or `None` if none.
    #[must_use]
    pub fn latest(self) -> Option<T> {
        match self {
            LocalResult::Single(t) | LocalResult::Ambiguous(_, t) => Some(t),
            _ => None,
        }
    }

    /// Maps a `LocalResult<T>` into `LocalResult<U>` with given function.
    #[must_use]
    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> LocalResult<U> {
        match self {
            LocalResult::None => LocalResult::None,
            LocalResult::Single(v) => LocalResult::Single(f(v)),
            LocalResult::Ambiguous(min, max) => LocalResult::Ambiguous(f(min), f(max)),
        }
    }
}

impl<T: fmt::Debug> LocalResult<T> {
    /// Returns the single unique conversion result, or panics accordingly.
    #[must_use]
    #[track_caller]
    pub fn unwrap(self) -> T {
        match self {
            LocalResult::None => panic!("No such local time"),
            LocalResult::Single(t) => t,
            LocalResult::Ambiguous(t1, t2) => {
                panic!("Ambiguous local time, ranging from {:?} to {:?}", t1, t2)
            }
        }
    }
}

/// The offset from the local time to UTC.
pub trait Offset: Sized + Clone + fmt::Debug {
    /// Returns the fixed offset from UTC to the local time stored.
    fn fix(&self) -> FixedOffset;
}

/// The time zone.
///
/// The methods here are the primary constructors for the [`DateTime`] type.
pub trait TimeZone: Sized + Clone {
    /// An associated offset type.
    /// This type is used to store the actual offset in date and time types.
    /// The original `TimeZone` value can be recovered via `TimeZone::from_offset`.
    type Offset: Offset;

    /// Make a new `DateTime` from year, month, day, time components and current time zone.
    ///
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// Returns `LocalResult::None` on invalid input data.
    fn with_ymd_and_hms(
        &self,
        year: i32,
        month: u32,
        day: u32,
        hour: u32,
        min: u32,
        sec: u32,
    ) -> LocalResult<DateTime<Self>> {
        match NaiveDate::from_ymd(year, month, day).and_then(|d| d.and_hms(hour, min, sec)) {
            Ok(dt) => self.from_local_datetime(&dt),
            Err(_) => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the number of non-leap seconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp")
    /// and the number of nanoseconds since the last whole non-leap second.
    ///
    /// The nanosecond part can exceed 1,000,000,000 in order to represent a
    /// [leap second](crate::NaiveTime#leap-second-handling), but only when `secs % 60 == 59`.
    /// (The true "UNIX timestamp" cannot represent a leap second unambiguously.)
    ///
    /// # Errors
    ///
    /// Returns `LocalResult::None` on out-of-range number of seconds and/or
    /// invalid nanosecond, otherwise always returns `LocalResult::Single`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeZone, Utc};
    ///
    /// assert_eq!(Utc.timestamp(1431648000, 0).unwrap().to_string(), "2015-05-15 00:00:00 UTC");
    /// ```
    fn timestamp(&self, secs: i64, nsecs: u32) -> LocalResult<DateTime<Self>> {
        match NaiveDateTime::from_timestamp(secs, nsecs) {
            Some(dt) => LocalResult::Single(self.from_utc_datetime(&dt)),
            None => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the number of non-leap milliseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    ///
    /// Returns `LocalResult::None` on out-of-range number of milliseconds
    /// and/or invalid nanosecond, otherwise always returns
    /// `LocalResult::Single`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{LocalResult, TimeZone, Utc};
    /// match Utc.timestamp_millis(1431648000) {
    ///     LocalResult::Single(dt) => assert_eq!(dt.timestamp(), 1431648),
    ///     _ => panic!("Incorrect timestamp_millis"),
    /// };
    /// ```
    fn timestamp_millis(&self, millis: i64) -> LocalResult<DateTime<Self>> {
        match NaiveDateTime::from_timestamp_millis(millis) {
            Some(dt) => LocalResult::Single(self.from_utc_datetime(&dt)),
            None => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the number of non-leap nanoseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    /// Unlike [`timestamp_millis`](#method.timestamp_millis), this never fails.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeZone, Utc};
    ///
    /// assert_eq!(Utc.timestamp_nanos(1431648000000000).timestamp(), 1431648);
    /// ```
    fn timestamp_nanos(&self, nanos: i64) -> DateTime<Self> {
        let (mut secs, mut nanos) = (nanos / 1_000_000_000, nanos % 1_000_000_000);
        if nanos < 0 {
            secs -= 1;
            nanos += 1_000_000_000;
        }
        self.timestamp(secs, nanos as u32).unwrap()
    }

    /// Makes a new `DateTime` from the number of non-leap microseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeZone, Utc};
    ///
    /// assert_eq!(Utc.timestamp_micros(1431648000000).unwrap().timestamp(), 1431648);
    /// ```
    fn timestamp_micros(&self, micros: i64) -> LocalResult<DateTime<Self>> {
        match NaiveDateTime::from_timestamp_micros(micros) {
            Some(dt) => LocalResult::Single(self.from_utc_datetime(&dt)),
            None => LocalResult::None,
        }
    }

    /// Reconstructs the time zone from the offset.
    fn from_offset(offset: &Self::Offset) -> Self;

    /// Creates the offset(s) for given local `NaiveDateTime` if possible.
    fn offset_from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<Self::Offset>;

    /// Converts the local `NaiveDateTime` to the timezone-aware `DateTime` if possible.
    #[allow(clippy::wrong_self_convention)]
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Self>> {
        // Return `LocalResult::None` when the offset pushes a value out of range, instead of
        // panicking.
        match self.offset_from_local_datetime(local) {
            LocalResult::None => LocalResult::None,
            LocalResult::Single(offset) => match local.checked_sub_offset(offset.fix()) {
                Some(dt) => LocalResult::Single(DateTime::from_naive_utc_and_offset(dt, offset)),
                None => LocalResult::None,
            },
            LocalResult::Ambiguous(o1, o2) => {
                match (local.checked_sub_offset(o1.fix()), local.checked_sub_offset(o2.fix())) {
                    (Some(d1), Some(d2)) => LocalResult::Ambiguous(
                        DateTime::from_naive_utc_and_offset(d1, o1),
                        DateTime::from_naive_utc_and_offset(d2, o2),
                    ),
                    _ => LocalResult::None,
                }
            }
        }
    }

    /// Creates the offset for given UTC `NaiveDateTime`. This cannot fail.
    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> Self::Offset;

    /// Converts the UTC `NaiveDateTime` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    #[allow(clippy::wrong_self_convention)]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Self> {
        DateTime::from_naive_utc_and_offset(*utc, self.offset_from_utc_datetime(utc))
    }
}


/// Error type for time zone lookups.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TzLookupError {
    /// Unable to determine the local time zone of the os/platform.
    TimeZoneUnknown,

    /// Error returned by a platform API.
    OsError(i32),

    /// `TZ` environment variable set to an invalid value.
    InvalidTzString,

    /// Unable to locate an IANA time zone database.
    NoTzdb,

    /// The specified time zone is not found (in the database).
    TimeZoneNotFound,

    /// There is an error when reading/validating the time zone data.
    InvalidTimeZoneData,

    /// The result would be out of range.
    OutOfRange,
}

impl fmt::Display for TzLookupError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TzLookupError::TimeZoneUnknown => write!(f, "unable to determine the local time zone"),
            TzLookupError::OsError(code) => {
                let io_error = std::io::Error::from_raw_os_error(*code);
                fmt::Display::fmt(&io_error, f)
            }
            TzLookupError::InvalidTzString => write!(f, "`TZ` environment variable set to an invalid value"),
            TzLookupError::NoTzdb => write!(f, "unable to locate an IANA time zone database"),
            TzLookupError::TimeZoneNotFound => write!(f, "the specified time zone is not found"),
            TzLookupError::InvalidTimeZoneData => write!(f, "error when reading/validating the time zone data"),
            TzLookupError::OutOfRange => write!(f, "date or offset outside of the supported range"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TzLookupError {}

impl From<TzLookupError> for Error {
    fn from(error: TzLookupError) -> Self {
        Error::TzLookupFailure(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fixed_offset_min_max_dates() {
        for offset_hour in -23..=23 {
            dbg!(offset_hour);
            let offset = FixedOffset::east(offset_hour * 60 * 60).unwrap();

            let local_max = offset.from_utc_datetime(&NaiveDateTime::MAX);
            assert_eq!(local_max.naive_utc(), NaiveDateTime::MAX);
            let local_min = offset.from_utc_datetime(&NaiveDateTime::MIN);
            assert_eq!(local_min.naive_utc(), NaiveDateTime::MIN);

            let local_max = offset.from_local_datetime(&NaiveDateTime::MAX);
            if offset_hour >= 0 {
                assert_eq!(local_max.unwrap().naive_local(), NaiveDateTime::MAX);
            } else {
                assert_eq!(local_max, LocalResult::None);
            }
            let local_min = offset.from_local_datetime(&NaiveDateTime::MIN);
            if offset_hour <= 0 {
                assert_eq!(local_min.unwrap().naive_local(), NaiveDateTime::MIN);
            } else {
                assert_eq!(local_min, LocalResult::None);
            }
        }
    }

    #[test]
    fn test_negative_millis() {
        let dt = Utc.timestamp_millis(-1000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59 UTC");
        let dt = Utc.timestamp_millis(-7000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:53 UTC");
        let dt = Utc.timestamp_millis(-7001).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:52.999 UTC");
        let dt = Utc.timestamp_millis(-7003).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:52.997 UTC");
        let dt = Utc.timestamp_millis(-999).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.001 UTC");
        let dt = Utc.timestamp_millis(-1).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.999 UTC");
        let dt = Utc.timestamp_millis(-60000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:00 UTC");
        let dt = Utc.timestamp_millis(-3600000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:00:00 UTC");

        for (millis, expected) in &[
            (-7000, "1969-12-31 23:59:53 UTC"),
            (-7001, "1969-12-31 23:59:52.999 UTC"),
            (-7003, "1969-12-31 23:59:52.997 UTC"),
        ] {
            match Utc.timestamp_millis(*millis) {
                LocalResult::Single(dt) => {
                    assert_eq!(dt.to_string(), *expected);
                }
                e => panic!("Got {:?} instead of an okay answer", e),
            }
        }
    }

    #[test]
    fn test_negative_nanos() {
        let dt = Utc.timestamp_nanos(-1_000_000_000);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59 UTC");
        let dt = Utc.timestamp_nanos(-999_999_999);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.000000001 UTC");
        let dt = Utc.timestamp_nanos(-1);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.999999999 UTC");
        let dt = Utc.timestamp_nanos(-60_000_000_000);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:00 UTC");
        let dt = Utc.timestamp_nanos(-3_600_000_000_000);
        assert_eq!(dt.to_string(), "1969-12-31 23:00:00 UTC");
    }

    #[test]
    fn test_nanos_never_panics() {
        Utc.timestamp_nanos(i64::max_value());
        Utc.timestamp_nanos(i64::default());
        Utc.timestamp_nanos(i64::min_value());
    }

    #[test]
    fn test_negative_micros() {
        let dt = Utc.timestamp_micros(-1_000_000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59 UTC");
        let dt = Utc.timestamp_micros(-999_999).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.000001 UTC");
        let dt = Utc.timestamp_micros(-1).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.999999 UTC");
        let dt = Utc.timestamp_micros(-60_000_000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:00 UTC");
        let dt = Utc.timestamp_micros(-3_600_000_000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:00:00 UTC");
    }
}
