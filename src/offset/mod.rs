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

use crate::format::{parse, Parsed, StrftimeItems};
use crate::naive::{NaiveDate, NaiveDateTime, NaiveTime};
#[allow(deprecated)]
use crate::Date;
use crate::{DateTime, Error};

mod fixed;
pub use self::fixed::FixedOffset;

#[cfg(feature = "clock")]
mod local;
#[cfg(feature = "clock")]
pub use self::local::Local;

mod utc;
pub use self::utc::Utc;

/// The conversion result from the local time to the timezone-aware datetime types.
#[derive(Clone, PartialEq, Debug, Copy, Eq, Hash)]
pub enum LocalResult<T> {
    /// Given local time representation has a single unique result.
    Single(T),
    /// Given local time representation has multiple results and thus ambiguous.
    /// This can occur when, for example, the negative timezone transition.
    Ambiguous(T /*min*/, T /*max*/),
}

impl<T> LocalResult<T> {
    /// Returns the single value that this local result corresponds to or
    /// `Err(chrono::Error)` if the result is ambiguous.
    /// [LocalResult::Single].
    pub fn single(self) -> Result<T, Error> {
        match self {
            LocalResult::Single(value) => Ok(value),
            _ => Err(Error::AmbiguousDate),
        }
    }

    /// Returns the date corresponding to the earliest date in the local result.
    pub fn earliest(self) -> T {
        match self {
            LocalResult::Single(t) | LocalResult::Ambiguous(t, _) => t,
        }
    }

    /// Returns the date corresponding to the latest date in the local result.
    pub fn latest(self) -> T {
        match self {
            LocalResult::Single(t) | LocalResult::Ambiguous(_, t) => t,
        }
    }

    /// Maps a `LocalResult<T>` into `LocalResult<U>` with given function.
    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> LocalResult<U> {
        match self {
            LocalResult::Single(v) => LocalResult::Single(f(v)),
            LocalResult::Ambiguous(min, max) => LocalResult::Ambiguous(f(min), f(max)),
        }
    }

    /// Maps a `LocalResult<T>` into `LocalResult<U>` fallibly with given
    /// function.
    pub fn try_map<U, E, F: FnMut(T) -> Result<U, E>>(self, mut f: F) -> Result<LocalResult<U>, E> {
        match self {
            LocalResult::Single(v) => Ok(LocalResult::Single(f(v)?)),
            LocalResult::Ambiguous(min, max) => Ok(LocalResult::Ambiguous(f(min)?, f(max)?)),
        }
    }
}

#[allow(deprecated)]
impl<Tz: TimeZone> LocalResult<Date<Tz>> {
    /// Makes a new `DateTime` from the current date and given `NaiveTime`.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    pub fn and_time(self, time: NaiveTime) -> Result<DateTime<Tz>, Error> {
        self.single()?.and_time(time)
    }

    /// Makes a new `DateTime` from the current date, hour, minute and second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    pub fn and_hms(self, hour: u32, min: u32, sec: u32) -> Result<DateTime<Tz>, Error> {
        self.single()?.and_hms(hour, min, sec)
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Errors on ambiguous results.
    #[inline]
    pub fn and_hms_milli(
        self,
        hour: u32,
        min: u32,
        sec: u32,
        milli: u32,
    ) -> Result<DateTime<Tz>, Error> {
        self.single()?.and_hms_milli(hour, min, sec, milli)
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Errors on ambiguous results.
    #[inline]
    pub fn and_hms_micro(
        self,
        hour: u32,
        min: u32,
        sec: u32,
        micro: u32,
    ) -> Result<DateTime<Tz>, Error> {
        self.single()?.and_hms_micro(hour, min, sec, micro)
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Errors on ambiguous results.
    #[inline]
    pub fn and_hms_nano(
        self,
        hour: u32,
        min: u32,
        sec: u32,
        nano: u32,
    ) -> Result<DateTime<Tz>, Error> {
        self.single()?.and_hms_nano(hour, min, sec, nano)
    }
}

#[cfg(test)]
impl<T> LocalResult<T> {
    /// Returns the single unique conversion result, or panics accordingly.
    pub fn unwrap(self) -> T {
        self.single().unwrap()
    }
}

/// The offset from the local time to UTC.
pub trait Offset: Sized + Clone + fmt::Debug {
    /// Returns the fixed offset from UTC to the local time stored.
    fn fix(&self) -> FixedOffset;
}

/// The time zone.
///
/// The methods here are the primarily constructors for [`Date`](../struct.Date.html) and
/// [`DateTime`](../struct.DateTime.html) types.
pub trait TimeZone: Sized + Clone {
    /// An associated offset type.
    /// This type is used to store the actual offset in date and time types.
    /// The original `TimeZone` value can be recovered via `TimeZone::from_offset`.
    type Offset: Offset;

    /// Make a new `DateTime` from year, month, day, time components and current time zone.
    ///
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// Returns `Err(chrono::Error)` on invalid input data.
    fn with_ymd_and_hms(
        &self,
        year: i32,
        month: u32,
        day: u32,
        hour: u32,
        min: u32,
        sec: u32,
    ) -> Result<LocalResult<DateTime<Self>>, Error> {
        self.from_local_datetime(&NaiveDate::from_ymd(year, month, day)?.and_hms(hour, min, sec)?)
    }

    /// Makes a new `DateTime` from the number of non-leap seconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp")
    /// and the number of nanoseconds since the last whole non-leap second.
    ///
    /// Returns `Err(chrono::Error)` on out-of-range number of seconds and/or
    /// invalid nanosecond, otherwise always returns `Ok(LocalResult::Single)`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Utc, TimeZone};
    ///
    /// assert_eq!(Utc.timestamp(1431648000, 0).unwrap().to_string(), "2015-05-15 00:00:00 UTC");
    /// ```
    fn timestamp(&self, secs: i64, nsecs: u32) -> Result<DateTime<Self>, Error> {
        self.from_utc_datetime(&NaiveDateTime::from_timestamp(secs, nsecs)?)
    }

    /// Makes a new `DateTime` from the number of non-leap milliseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    ///
    /// Returns `Err(chrono::Error)` on out-of-range number of milliseconds
    /// and/or invalid nanosecond
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Utc, TimeZone, LocalResult};
    /// match Utc.timestamp_millis(1431648000) {
    ///     Ok(dt) => assert_eq!(dt.timestamp(), 1431648),
    ///     Err(_) => panic!("Incorrect timestamp_millis"),
    /// };
    /// ```
    fn timestamp_millis(&self, millis: i64) -> Result<DateTime<Self>, Error> {
        let (mut secs, mut millis) = (millis / 1000, millis % 1000);
        if millis < 0 {
            secs -= 1;
            millis += 1000;
        }
        self.timestamp(secs, millis as u32 * 1_000_000)
    }

    /// Makes a new `DateTime` from the number of non-leap nanoseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    /// Just like [`timestamp_millis`](#method.timestamp_millis), this
    /// returns `Err(chrono::Error)` in case of failure.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Utc, TimeZone};
    ///
    /// assert_eq!(Utc.timestamp_nanos(1431648000000000)?.timestamp(), 1431648);
    /// Ok::<(), chrono::Error>(())
    /// ```
    fn timestamp_nanos(&self, nanos: i64) -> Result<DateTime<Self>, Error> {
        let (mut secs, mut nanos) = (nanos / 1_000_000_000, nanos % 1_000_000_000);
        if nanos < 0 {
            secs -= 1;
            nanos += 1_000_000_000;
        }
        self.timestamp(secs, nanos as u32)
    }

    /// Parses a string with the specified format string and returns a
    /// `DateTime` with the current offset.
    ///
    /// See the [`crate::format::strftime`] module on the
    /// supported escape sequences.
    ///
    /// If the to-be-parsed string includes an offset, it *must* match the
    /// offset of the TimeZone, otherwise an error will be returned.
    ///
    /// See also [`DateTime::parse_from_str`] which gives a [`DateTime`] with
    /// parsed [`FixedOffset`].
    fn datetime_from_str(&self, s: &str, fmt: &str) -> Result<DateTime<Self>, Error> {
        let mut parsed = Parsed::new();
        parse(&mut parsed, s, StrftimeItems::new(fmt))?;
        parsed.to_datetime_with_timezone(self)
    }

    /// Reconstructs the time zone from the offset.
    fn from_offset(offset: &Self::Offset) -> Self;

    /// Creates the offset(s) for given local `NaiveDate` if possible.
    fn offset_from_local_date(&self, local: &NaiveDate)
        -> Result<LocalResult<Self::Offset>, Error>;

    /// Creates the offset(s) for given local `NaiveDateTime` if possible.
    fn offset_from_local_datetime(
        &self,
        local: &NaiveDateTime,
    ) -> Result<LocalResult<Self::Offset>, Error>;

    /// Converts the local `NaiveDate` to the timezone-aware `Date` if possible.
    #[allow(clippy::wrong_self_convention)]
    #[allow(deprecated)]
    fn from_local_date(&self, local: &NaiveDate) -> Result<LocalResult<Date<Self>>, Error> {
        // TODO: This might be total nonsense, but the functionality is required at quite a few places
        // Is the default time of a day midnight or noon?
        Ok(self
            .offset_from_local_date(local)?
            .map(|offset| Date::from_utc((local.and_midnight() - offset.fix()).date(), offset)))
    }

    /// Converts the local `NaiveDateTime` to the timezone-aware `DateTime` if possible.
    #[allow(clippy::wrong_self_convention)]
    fn from_local_datetime(
        &self,
        local: &NaiveDateTime,
    ) -> Result<LocalResult<DateTime<Self>>, Error> {
        Ok(self
            .offset_from_local_datetime(local)?
            .map(|offset| DateTime::from_utc(*local - offset.fix(), offset)))
    }

    /// Creates the offset for given UTC `NaiveDate`.
    fn offset_from_utc_date(&self, utc: &NaiveDate) -> Result<Self::Offset, Error>;

    /// Creates the offset for given UTC `NaiveDateTime`.
    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> Result<Self::Offset, Error>;

    /// Converts the UTC `NaiveDate` to the local date.
    #[allow(deprecated)]
    #[allow(clippy::wrong_self_convention)]
    fn from_utc_date(&self, utc: &NaiveDate) -> Result<Date<Self>, Error> {
        Ok(Date::from_utc(*utc, self.offset_from_utc_date(utc)?))
    }

    /// Converts the UTC `NaiveDateTime` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    // TODO: At least one implementation of this function can fail.
    #[allow(clippy::wrong_self_convention)]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> Result<DateTime<Self>, Error> {
        Ok(DateTime::from_utc(*utc, self.offset_from_utc_datetime(utc)?))
    }
}

/// A time zone that is fixed. It is distinguished from [TimeZone] by allowing
/// for infallible operations since there is no need to access system
/// information to figure out which timezone is being used.
pub(crate) trait FixedTimeZone: TimeZone {
    /// Creates the offset for given UTC `NaiveDate`. This cannot fail.
    fn offset_from_utc_date_fixed(&self, utc: &NaiveDate) -> Self::Offset;

    /// Creates the offset for given UTC `NaiveDateTime`. This cannot fail.
    fn offset_from_utc_datetime_fixed(&self, utc: &NaiveDateTime) -> Self::Offset;

    /// Converts the UTC `NaiveDate` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    #[allow(clippy::wrong_self_convention)]
    #[allow(deprecated)]
    fn from_utc_date_fixed(&self, utc: &NaiveDate) -> Date<Self> {
        Date::from_utc(*utc, self.offset_from_utc_date_fixed(utc))
    }

    /// Converts the UTC `NaiveDateTime` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    #[allow(clippy::wrong_self_convention)]
    fn from_utc_datetime_fixed(&self, utc: &NaiveDateTime) -> DateTime<Self> {
        DateTime::from_utc(*utc, self.offset_from_utc_datetime_fixed(utc))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
            let dt = Utc.timestamp_millis(*millis).unwrap();
            assert_eq!(dt.to_string(), *expected);
        }
    }

    #[test]
    fn test_negative_nanos() {
        let dt = Utc.timestamp_nanos(-1_000_000_000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59 UTC");
        let dt = Utc.timestamp_nanos(-999_999_999).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.000000001 UTC");
        let dt = Utc.timestamp_nanos(-1).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.999999999 UTC");
        let dt = Utc.timestamp_nanos(-60_000_000_000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:00 UTC");
        let dt = Utc.timestamp_nanos(-3_600_000_000_000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:00:00 UTC");
    }

    #[test]
    fn test_nanos_never_panics() {
        Utc.timestamp_nanos(i64::max_value()).unwrap();
        Utc.timestamp_nanos(i64::default()).unwrap();
        Utc.timestamp_nanos(i64::min_value()).unwrap();
    }
}
