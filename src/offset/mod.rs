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

/// The result of mapping a local time to a concrete instant in a given time zone.
///
/// The calculation to go from a local time (wall clock time) to an instant in UTC can end up in
/// three cases:
/// * A single, simple result.
/// * An ambiguous result when the clock is turned backwards during a transition due to for example
///   DST.
/// * No result when the clock is turned forwards during a transition due to for example DST.
///
/// When the clock is turned backwards it creates a _fold_ in local time, during which the local
/// time is _ambiguous_. When the clock is turned forwards it creates a _gap_ in local time, during
/// which the local time is _missing_, or does not exist.
///
/// Chrono does not return a default choice or invalid data during time zone transitions, but has
/// the `MappedLocalTime` type to help deal with the result correctly.
///
/// The type of `T` is usually a [`DateTime`] but may also be only an offset.
#[derive(Clone, PartialEq, Debug, Copy, Eq, Hash)]
pub enum MappedLocalTime<T> {
    /// The local time maps to a single unique result.
    Single(T),

    /// The local time is _ambiguous_ because there is a _fold_ in the local time.
    ///
    /// This variant contains the two possible results, in the order `(earliest, latest)`.
    Ambiguous(T, T),

    /// The local time does not exist because there is a _gap_ in the local time.
    ///
    /// This variant may also be returned if there was an error while resolving the local time,
    /// caused by for example missing time zone data files, an error in an OS API, or overflow.
    None,
}

impl<T> MappedLocalTime<T> {
    /// Returns `Some` if the time zone mapping has a single result.
    ///
    /// # Errors
    ///
    /// Returns `None` if local time falls in a _fold_ or _gap_ in the local time, or if there was
    /// an error.
    #[must_use]
    pub fn single(self) -> Option<T> {
        match self {
            MappedLocalTime::Single(t) => Some(t),
            _ => None,
        }
    }

    /// Returns the earliest possible result of a the time zone mapping.
    ///
    /// # Errors
    ///
    /// Returns `None` if local time falls in a _gap_ in the local time, or if there was an error.
    #[must_use]
    pub fn earliest(self) -> Option<T> {
        match self {
            MappedLocalTime::Single(t) | MappedLocalTime::Ambiguous(t, _) => Some(t),
            _ => None,
        }
    }

    /// Returns the latest possible result of a the time zone mapping.
    ///
    /// # Errors
    ///
    /// Returns `None` if local time falls in a _gap_ in the local time, or if there was an error.
    #[must_use]
    pub fn latest(self) -> Option<T> {
        match self {
            MappedLocalTime::Single(t) | MappedLocalTime::Ambiguous(_, t) => Some(t),
            _ => None,
        }
    }

    /// Maps a `MappedLocalTime<T>` into `MappedLocalTime<U>` with given function.
    #[must_use]
    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> MappedLocalTime<U> {
        match self {
            MappedLocalTime::None => MappedLocalTime::None,
            MappedLocalTime::Single(v) => MappedLocalTime::Single(f(v)),
            MappedLocalTime::Ambiguous(min, max) => MappedLocalTime::Ambiguous(f(min), f(max)),
        }
    }

    /// Maps a `MappedLocalTime<T>` into `MappedLocalTime<U>` with given function.
    ///
    /// Returns `MappedLocalTime::None` if the function returns `Err`.
    #[must_use]
    pub(crate) fn and_then<U, F: FnMut(T) -> Result<U, Error>>(
        self,
        mut f: F,
    ) -> MappedLocalTime<U> {
        match self {
            MappedLocalTime::None => MappedLocalTime::None,
            MappedLocalTime::Single(v) => match f(v) {
                Ok(new) => MappedLocalTime::Single(new),
                Err(_) => MappedLocalTime::None,
            },
            MappedLocalTime::Ambiguous(min, max) => match (f(min), f(max)) {
                (Ok(min), Ok(max)) => MappedLocalTime::Ambiguous(min, max),
                _ => MappedLocalTime::None,
            },
        }
    }
}

impl<T: fmt::Debug> MappedLocalTime<T> {
    /// Returns a single unique conversion result or panics.
    ///
    /// `unwrap()` is best combined with time zone types where the mapping can never fail like
    /// [`Utc`] and [`FixedOffset`]. Note that for [`FixedOffset`] there is a rare case where a
    /// resulting [`DateTime`] can be out of range.
    ///
    /// # Panics
    ///
    /// Panics if the local time falls within a _fold_ or a _gap_ in the local time, and on any
    /// error that may have been returned by the type implementing [`TimeZone`].
    #[must_use]
    #[track_caller]
    pub fn unwrap(self) -> T {
        match self {
            MappedLocalTime::None => panic!("No such local time"),
            MappedLocalTime::Single(t) => t,
            MappedLocalTime::Ambiguous(t1, t2) => {
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
    /// Returns `MappedLocalTime::None` on invalid input data.
    fn at_ymd_and_hms(
        &self,
        year: i32,
        month: u32,
        day: u32,
        hour: u32,
        min: u32,
        sec: u32,
    ) -> MappedLocalTime<DateTime<Self>> {
        match NaiveDate::from_ymd(year, month, day).and_then(|d| d.at_hms(hour, min, sec)) {
            Ok(dt) => self.from_local_datetime(dt),
            Err(_) => MappedLocalTime::None,
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
    /// Returns `MappedLocalTime::None` on out-of-range number of seconds and/or
    /// invalid nanosecond, otherwise always returns `MappedLocalTime::Single`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeZone, Utc};
    ///
    /// assert_eq!(Utc.at_timestamp(1431648000, 0).unwrap().to_string(), "2015-05-15 00:00:00 UTC");
    /// ```
    fn at_timestamp(&self, secs: i64, nsecs: u32) -> MappedLocalTime<DateTime<Self>> {
        match DateTime::from_timestamp(secs, nsecs) {
            Ok(dt) => MappedLocalTime::Single(self.from_utc_datetime(dt.naive_utc())),
            Err(_) => MappedLocalTime::None,
        }
    }

    /// Makes a new `DateTime` from the number of non-leap milliseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    ///
    /// Returns `MappedLocalTime::None` on out-of-range number of milliseconds
    /// and/or invalid nanosecond, otherwise always returns
    /// `MappedLocalTime::Single`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{MappedLocalTime, TimeZone, Utc};
    /// match Utc.at_timestamp_millis(1431648000) {
    ///     MappedLocalTime::Single(dt) => assert_eq!(dt.timestamp(), 1431648),
    ///     _ => panic!("Incorrect timestamp_millis"),
    /// };
    /// ```
    fn at_timestamp_millis(&self, millis: i64) -> MappedLocalTime<DateTime<Self>> {
        match DateTime::from_timestamp_millis(millis) {
            Ok(dt) => MappedLocalTime::Single(self.from_utc_datetime(dt.naive_utc())),
            Err(_) => MappedLocalTime::None,
        }
    }

    /// Makes a new `DateTime` from the number of non-leap nanoseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    /// Unlike [`at_timestamp_millis`](#method.at_timestamp_millis), this never fails.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeZone, Utc};
    ///
    /// assert_eq!(Utc.at_timestamp_nanos(1431648000000000).timestamp(), 1431648);
    /// ```
    fn at_timestamp_nanos(self, nanos: i64) -> DateTime<Self> {
        self.from_utc_datetime(DateTime::from_timestamp_nanos(nanos).naive_utc())
    }

    /// Makes a new `DateTime` from the number of non-leap microseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeZone, Utc};
    ///
    /// assert_eq!(Utc.at_timestamp_micros(1431648000000).unwrap().timestamp(), 1431648);
    /// ```
    fn at_timestamp_micros(&self, micros: i64) -> MappedLocalTime<DateTime<Self>> {
        match DateTime::from_timestamp_micros(micros) {
            Ok(dt) => MappedLocalTime::Single(self.from_utc_datetime(dt.naive_utc())),
            Err(_) => MappedLocalTime::None,
        }
    }

    /// Reconstructs the time zone from the offset.
    fn from_offset(offset: &Self::Offset) -> Self;

    /// Creates the offset(s) for given local `NaiveDateTime` if possible.
    fn offset_from_local_datetime(&self, local: NaiveDateTime) -> MappedLocalTime<Self::Offset>;

    /// Converts the local `NaiveDateTime` to the timezone-aware `DateTime` if possible.
    #[allow(clippy::wrong_self_convention)]
    fn from_local_datetime(&self, local: NaiveDateTime) -> MappedLocalTime<DateTime<Self>> {
        self.offset_from_local_datetime(local).and_then(|off| {
            local
                .checked_sub_offset(off.fix())
                .map(|dt| DateTime::from_naive_utc_and_offset(dt, off))
        })
    }

    /// Creates the offset for given UTC `NaiveDateTime`. This cannot fail.
    fn offset_from_utc_datetime(&self, utc: NaiveDateTime) -> Self::Offset;

    /// Converts the UTC `NaiveDateTime` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    #[allow(clippy::wrong_self_convention)]
    fn from_utc_datetime(&self, utc: NaiveDateTime) -> DateTime<Self> {
        DateTime::from_naive_utc_and_offset(utc, self.offset_from_utc_datetime(utc))
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

            let local_max = offset.from_utc_datetime(NaiveDateTime::MAX);
            assert_eq!(local_max.naive_utc(), NaiveDateTime::MAX);
            let local_min = offset.from_utc_datetime(NaiveDateTime::MIN);
            assert_eq!(local_min.naive_utc(), NaiveDateTime::MIN);

            let local_max = offset.from_local_datetime(NaiveDateTime::MAX);
            if offset_hour >= 0 {
                assert_eq!(local_max.unwrap().naive_local(), NaiveDateTime::MAX);
            } else {
                assert_eq!(local_max, MappedLocalTime::None);
            }
            let local_min = offset.from_local_datetime(NaiveDateTime::MIN);
            if offset_hour <= 0 {
                assert_eq!(local_min.unwrap().naive_local(), NaiveDateTime::MIN);
            } else {
                assert_eq!(local_min, MappedLocalTime::None);
            }
        }
    }

    #[test]
    fn test_negative_millis() {
        let dt = Utc.at_timestamp_millis(-1000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59 UTC");
        let dt = Utc.at_timestamp_millis(-7000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:53 UTC");
        let dt = Utc.at_timestamp_millis(-7001).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:52.999 UTC");
        let dt = Utc.at_timestamp_millis(-7003).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:52.997 UTC");
        let dt = Utc.at_timestamp_millis(-999).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.001 UTC");
        let dt = Utc.at_timestamp_millis(-1).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.999 UTC");
        let dt = Utc.at_timestamp_millis(-60000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:00 UTC");
        let dt = Utc.at_timestamp_millis(-3600000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:00:00 UTC");

        for (millis, expected) in &[
            (-7000, "1969-12-31 23:59:53 UTC"),
            (-7001, "1969-12-31 23:59:52.999 UTC"),
            (-7003, "1969-12-31 23:59:52.997 UTC"),
        ] {
            match Utc.at_timestamp_millis(*millis) {
                MappedLocalTime::Single(dt) => {
                    assert_eq!(dt.to_string(), *expected);
                }
                e => panic!("Got {:?} instead of an okay answer", e),
            }
        }
    }

    #[test]
    fn test_negative_nanos() {
        let dt = Utc.at_timestamp_nanos(-1_000_000_000);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59 UTC");
        let dt = Utc.at_timestamp_nanos(-999_999_999);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.000000001 UTC");
        let dt = Utc.at_timestamp_nanos(-1);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.999999999 UTC");
        let dt = Utc.at_timestamp_nanos(-60_000_000_000);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:00 UTC");
        let dt = Utc.at_timestamp_nanos(-3_600_000_000_000);
        assert_eq!(dt.to_string(), "1969-12-31 23:00:00 UTC");
    }

    #[test]
    fn test_nanos_never_panics() {
        Utc.at_timestamp_nanos(i64::max_value());
        Utc.at_timestamp_nanos(i64::default());
        Utc.at_timestamp_nanos(i64::min_value());
    }

    #[test]
    fn test_negative_micros() {
        let dt = Utc.at_timestamp_micros(-1_000_000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59 UTC");
        let dt = Utc.at_timestamp_micros(-999_999).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.000001 UTC");
        let dt = Utc.at_timestamp_micros(-1).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.999999 UTC");
        let dt = Utc.at_timestamp_micros(-60_000_000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:00 UTC");
        let dt = Utc.at_timestamp_micros(-3_600_000_000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:00:00 UTC");
    }
}
