// This is a part of Chrono.
// See README.md and LICENSE.txt for details.
#![allow(dead_code)]

//! ISO 8601 date and time without timezone.

#[cfg(any(feature = "alloc", feature = "std", test))]
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::convert::TryFrom;
use core::fmt::Write;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use core::{fmt, str};

use num_integer::div_mod_floor;
#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

#[cfg(any(feature = "alloc", feature = "std", test))]
use crate::format::DelayedFormat;
use crate::format::{parse, Parsed, StrftimeItems};
use crate::format::{Fixed, Item, Numeric, Pad};
use crate::naive::{Days, IsoWeek, NaiveDate, NaiveTime};
use crate::{DateTime, Datelike, Error, Months, TimeDelta, TimeZone, Timelike, Weekday};

/// Tools to help serializing/deserializing `NaiveDateTime`s
#[cfg(feature = "serde")]
pub(crate) mod serde;

#[cfg(test)]
mod tests;

/// The tight upper bound guarantees that a duration with `|TimeDelta| >= 2^MAX_SECS_BITS`
/// will always overflow the addition with any date and time type.
///
/// So why is this needed? `TimeDelta::seconds(rhs)` may overflow, and we don't have
/// an alternative returning `Option` or `Result`. Thus we need some early bound to avoid
/// touching that call when we are already sure that it WILL overflow...
const MAX_SECS_BITS: usize = 44;

/// Number of nanoseconds in a millisecond
const NANOS_IN_MILLISECOND: u32 = 1_000_000;
/// Number of nanoseconds in a second
const NANOS_IN_SECOND: u32 = 1000 * NANOS_IN_MILLISECOND;

/// The minimum possible `NaiveDateTime`.
#[deprecated(since = "0.4.20", note = "Use NaiveDateTime::MIN instead")]
pub const MIN_DATETIME: NaiveDateTime = NaiveDateTime::MIN;
/// The maximum possible `NaiveDateTime`.
#[deprecated(since = "0.4.20", note = "Use NaiveDateTime::MAX instead")]
pub const MAX_DATETIME: NaiveDateTime = NaiveDateTime::MAX;

/// ISO 8601 combined date and time without timezone.
///
/// # Example
///
/// `NaiveDateTime` is commonly created from [`NaiveDate`](./struct.NaiveDate.html).
///
/// ```
/// use chrono::{NaiveDate, NaiveDateTime};
///
/// let dt: NaiveDateTime = NaiveDate::from_ymd(2016, 7, 8)?.and_hms(9, 10, 11)?;
/// # let _ = dt;
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// You can use typical [date-like](../trait.Datelike.html) and
/// [time-like](../trait.Timelike.html) methods,
/// provided that relevant traits are in the scope.
///
/// ```
/// # use chrono::{NaiveDate, NaiveDateTime};
/// # let dt: NaiveDateTime = NaiveDate::from_ymd(2016, 7, 8)?.and_hms(9, 10, 11)?;
/// use chrono::{Datelike, Timelike, Weekday};
///
/// assert_eq!(dt.weekday(), Weekday::Fri);
/// assert_eq!(dt.num_seconds_from_midnight(), 33011);
/// # Ok::<_, chrono::Error>(())
/// ```
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct NaiveDateTime {
    date: NaiveDate,
    time: NaiveTime,
}

/// The unit of a timestamp expressed in fractions of a second.
/// Currently either milliseconds or microseconds.
///
/// This is a private type, used in the implementation of
/// [NaiveDateTime::from_timestamp_millis] and [NaiveDateTime::from_timestamp_micros].
#[derive(Clone, Copy, Debug)]
enum TimestampUnit {
    Millis,
    Micros,
}

impl TimestampUnit {
    fn per_second(self) -> u32 {
        match self {
            TimestampUnit::Millis => 1_000,
            TimestampUnit::Micros => 1_000_000,
        }
    }
    fn nanos_per(self) -> u32 {
        match self {
            TimestampUnit::Millis => 1_000_000,
            TimestampUnit::Micros => 1_000,
        }
    }
}

impl NaiveDateTime {
    pub(crate) const UNIX_EPOCH: NaiveDateTime =
        NaiveDateTime { date: NaiveDate::MIN, time: NaiveTime::MIDNIGHT };

    /// Makes a new `NaiveDateTime` from date and time components.
    /// Equivalent to [`date.and_time(time)`](./struct.NaiveDate.html#method.and_time)
    /// and many other helper constructors on `NaiveDate`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveTime, NaiveDateTime};
    ///
    /// let d = NaiveDate::from_ymd(2015, 6, 3)?;
    /// let t = NaiveTime::from_hms_milli(12, 34, 56, 789)?;
    ///
    /// let dt = NaiveDateTime::new(d, t);
    /// assert_eq!(dt.date(), d);
    /// assert_eq!(dt.time(), t);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub const fn new(date: NaiveDate, time: NaiveTime) -> NaiveDateTime {
        NaiveDateTime { date, time }
    }

    /// Creates a new [NaiveDateTime] from milliseconds since the UNIX epoch.
    ///
    /// The UNIX epoch starts on midnight, January 1, 1970, UTC.
    ///
    /// Returns `Err(Error)` on an out-of-range number of milliseconds.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDateTime;
    /// let timestamp_millis: i64 = 1662921288000; //Sunday, September 11, 2022 6:34:48 PM
    /// let naive_datetime = NaiveDateTime::from_timestamp_millis(timestamp_millis);
    /// assert_eq!(timestamp_millis, naive_datetime?.timestamp_millis());
    ///
    /// // Negative timestamps (before the UNIX epoch) are supported as well.
    /// let timestamp_millis: i64 = -2208936075000; //Mon Jan 01 1900 14:38:45 GMT+0000
    /// let naive_datetime = NaiveDateTime::from_timestamp_millis(timestamp_millis);
    /// assert_eq!(timestamp_millis, naive_datetime?.timestamp_millis());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn from_timestamp_millis(millis: i64) -> Result<NaiveDateTime, Error> {
        Self::from_timestamp_unit(millis, TimestampUnit::Millis)
    }

    /// Creates a new [NaiveDateTime] from microseconds since the UNIX epoch.
    ///
    /// The UNIX epoch starts on midnight, January 1, 1970, UTC.
    ///
    /// Returns `Err(Error)` on an out-of-range number of microseconds.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDateTime;
    /// let timestamp_micros: i64 = 1662921288000000; //Sunday, September 11, 2022 6:34:48 PM
    /// let naive_datetime = NaiveDateTime::from_timestamp_micros(timestamp_micros);
    /// assert_eq!(timestamp_micros, naive_datetime?.timestamp_micros());
    ///
    /// // Negative timestamps (before the UNIX epoch) are supported as well.
    /// let timestamp_micros: i64 = -2208936075000000; //Mon Jan 01 1900 14:38:45 GMT+0000
    /// let naive_datetime = NaiveDateTime::from_timestamp_micros(timestamp_micros);
    /// assert_eq!(timestamp_micros, naive_datetime?.timestamp_micros());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn from_timestamp_micros(micros: i64) -> Result<NaiveDateTime, Error> {
        Self::from_timestamp_unit(micros, TimestampUnit::Micros)
    }

    /// Makes a new `NaiveDateTime` corresponding to a UTC date and time, from
    /// the number of non-leap seconds since the midnight UTC on January 1, 1970
    /// (aka "UNIX timestamp") and the number of nanoseconds since the last
    /// whole non-leap second.
    ///
    /// For a non-naive version of this function see
    /// [`TimeZone::timestamp`](../offset/trait.TimeZone.html#method.timestamp).
    ///
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the
    /// [leap second](./struct.NaiveTime.html#leap-second-handling). (The true
    /// "UNIX timestamp" cannot represent a leap second unambiguously.)
    ///
    /// Returns `Err(Error)` on the out-of-range number of seconds and/or
    /// invalid nanosecond.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDateTime, NaiveDate};
    /// use std::i64;
    ///
    /// let dt = NaiveDateTime::from_timestamp(0, 42_000_000)?;
    /// assert_eq!(dt, NaiveDate::from_ymd(1970, 1, 1)?.and_hms_milli(0, 0, 0, 42)?);
    ///
    /// let dt = NaiveDateTime::from_timestamp(1_000_000_000, 0)?;
    /// assert_eq!(dt, NaiveDate::from_ymd(2001, 9, 9)?.and_hms(1, 46, 40)?);
    ///
    /// let from_timestamp = NaiveDateTime::from_timestamp;
    ///
    /// assert!(from_timestamp(0, 0).is_ok());
    /// assert!(from_timestamp(0, 999_999_999).is_ok());
    /// assert!(from_timestamp(0, 1_500_000_000).is_ok()); // leap second
    /// assert!(from_timestamp(0, 2_000_000_000).is_err());
    /// assert!(from_timestamp(i64::MAX, 0).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn from_timestamp(secs: i64, nsecs: u32) -> Result<NaiveDateTime, Error> {
        let (days, secs) = div_mod_floor(secs, 86_400);
        let date = i32::try_from(days)
            .ok()
            .and_then(|days| days.checked_add(719_163))
            .ok_or_else(|| Error::InvalidDateTime)
            .and_then(NaiveDate::from_num_days_from_ce)?;

        let time = NaiveTime::from_num_seconds_from_midnight(secs as u32, nsecs)?;
        Ok(NaiveDateTime { date, time })
    }

    /// Parses a string with the specified format string and returns a new `NaiveDateTime`.
    /// See the [`format::strftime` module](../format/strftime/index.html)
    /// on the supported escape sequences.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDateTime, NaiveDate};
    ///
    /// let parse_from_str = NaiveDateTime::parse_from_str;
    ///
    /// assert_eq!(parse_from_str("2015-09-05 23:56:04", "%Y-%m-%d %H:%M:%S"),
    ///            Ok(NaiveDate::from_ymd(2015, 9, 5)?.and_hms(23, 56, 4)?));
    /// assert_eq!(parse_from_str("5sep2015pm012345.6789", "%d%b%Y%p%I%M%S%.f"),
    ///            Ok(NaiveDate::from_ymd(2015, 9, 5)?.and_hms_micro(13, 23, 45, 678_900)?));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// Offset is ignored for the purpose of parsing.
    ///
    /// ```
    /// # use chrono::{NaiveDateTime, NaiveDate};
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// assert_eq!(parse_from_str("2014-5-17T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
    ///            Ok(NaiveDate::from_ymd(2014, 5, 17)?.and_hms(12, 34, 56)?));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// [Leap seconds](./struct.NaiveTime.html#leap-second-handling) are correctly handled by
    /// treating any time of the form `hh:mm:60` as a leap second.
    /// (This equally applies to the formatting, so the round trip is possible.)
    ///
    /// ```
    /// # use chrono::{NaiveDateTime, NaiveDate};
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// assert_eq!(parse_from_str("2015-07-01 08:59:60.123", "%Y-%m-%d %H:%M:%S%.f"),
    ///            Ok(NaiveDate::from_ymd(2015, 7, 1)?.and_hms_milli(8, 59, 59, 1_123)?));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// Missing seconds are assumed to be zero,
    /// but out-of-bound times or insufficient fields are errors otherwise.
    ///
    /// ```
    /// # use chrono::{NaiveDateTime, NaiveDate};
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// assert_eq!(parse_from_str("94/9/4 7:15", "%y/%m/%d %H:%M"),
    ///            Ok(NaiveDate::from_ymd(1994, 9, 4)?.and_hms(7, 15, 0)?));
    ///
    /// assert!(parse_from_str("04m33s", "%Mm%Ss").is_err());
    /// assert!(parse_from_str("94/9/4 12", "%y/%m/%d %H").is_err());
    /// assert!(parse_from_str("94/9/4 17:60", "%y/%m/%d %H:%M").is_err());
    /// assert!(parse_from_str("94/9/4 24:00:00", "%y/%m/%d %H:%M:%S").is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// All parsed fields should be consistent to each other, otherwise it's an error.
    ///
    /// ```
    /// # use chrono::NaiveDateTime;
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// let fmt = "%Y-%m-%d %H:%M:%S = UNIX timestamp %s";
    /// assert!(parse_from_str("2001-09-09 01:46:39 = UNIX timestamp 999999999", fmt).is_ok());
    /// assert!(parse_from_str("1970-01-01 00:00:00 = UNIX timestamp 1", fmt).is_err());
    /// ```
    ///
    /// Years before 1 BCE or after 9999 CE, require an initial sign
    ///
    ///```
    /// # use chrono::{NaiveDate, NaiveDateTime};
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// let fmt = "%Y-%m-%d %H:%M:%S";
    /// assert!(parse_from_str("10000-09-09 01:46:39", fmt).is_err());
    /// assert!(parse_from_str("+10000-09-09 01:46:39", fmt).is_ok());
    ///```     
    pub fn parse_from_str(s: &str, fmt: &str) -> Result<NaiveDateTime, Error> {
        let mut parsed = Parsed::new();
        parse(&mut parsed, s, StrftimeItems::new(fmt))?;
        parsed.to_naive_datetime_with_offset(0) // no offset adjustment
    }

    /// Retrieves a date component.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd(2016, 7, 8)?.and_hms(9, 10, 11)?;
    /// assert_eq!(dt.date(), NaiveDate::from_ymd(2016, 7, 8)?);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub const fn date(&self) -> NaiveDate {
        self.date
    }

    /// Retrieves a time component.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveTime};
    ///
    /// let dt = NaiveDate::from_ymd(2016, 7, 8)?.and_hms(9, 10, 11)?;
    /// assert_eq!(dt.time(), NaiveTime::from_hms(9, 10, 11)?);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub const fn time(&self) -> NaiveTime {
        self.time
    }

    /// Returns the number of non-leap seconds since the midnight on January 1, 1970.
    ///
    /// Note that this does *not* account for the timezone!
    /// The true "UNIX timestamp" would count seconds since the midnight *UTC* on the epoch.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd(1970, 1, 1)?.and_hms_milli(0, 0, 1, 980)?;
    /// assert_eq!(dt.timestamp(), 1);
    ///
    /// let dt = NaiveDate::from_ymd(2001, 9, 9)?.and_hms(1, 46, 40)?;
    /// assert_eq!(dt.timestamp(), 1_000_000_000);
    ///
    /// let dt = NaiveDate::from_ymd(1969, 12, 31)?.and_hms(23, 59, 59)?;
    /// assert_eq!(dt.timestamp(), -1);
    ///
    /// let dt = NaiveDate::from_ymd(-1, 1, 1)?.and_hms(0, 0, 0)?;
    /// assert_eq!(dt.timestamp(), -62198755200);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn timestamp(&self) -> i64 {
        const UNIX_EPOCH_DAY: i64 = 719_163;
        let gregorian_day = i64::from(self.date.num_days_from_ce());
        let seconds_from_midnight = i64::from(self.time.num_seconds_from_midnight());
        (gregorian_day - UNIX_EPOCH_DAY) * 86_400 + seconds_from_midnight
    }

    /// Returns the number of non-leap *milliseconds* since midnight on January 1, 1970.
    ///
    /// Note that this does *not* account for the timezone!
    /// The true "UNIX timestamp" would count seconds since the midnight *UTC* on the epoch.
    ///
    /// Note also that this does reduce the number of years that can be
    /// represented from ~584 Billion to ~584 Million. (If this is a problem,
    /// please file an issue to let me know what domain needs millisecond
    /// precision over billions of years, I'm curious.)
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd(1970, 1, 1)?.and_hms_milli(0, 0, 1, 444)?;
    /// assert_eq!(dt.timestamp_millis(), 1_444);
    ///
    /// let dt = NaiveDate::from_ymd(2001, 9, 9)?.and_hms_milli(1, 46, 40, 555)?;
    /// assert_eq!(dt.timestamp_millis(), 1_000_000_000_555);
    ///
    /// let dt = NaiveDate::from_ymd(1969, 12, 31)?.and_hms_milli(23, 59, 59, 100)?;
    /// assert_eq!(dt.timestamp_millis(), -900);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn timestamp_millis(&self) -> i64 {
        let as_ms = self.timestamp() * 1000;
        as_ms + i64::from(self.timestamp_subsec_millis())
    }

    /// Returns the number of non-leap *microseconds* since midnight on January 1, 1970.
    ///
    /// Note that this does *not* account for the timezone!
    /// The true "UNIX timestamp" would count seconds since the midnight *UTC* on the epoch.
    ///
    /// Note also that this does reduce the number of years that can be
    /// represented from ~584 Billion to ~584 Thousand. (If this is a problem,
    /// please file an issue to let me know what domain needs microsecond
    /// precision over millennia, I'm curious.)
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd(1970, 1, 1)?.and_hms_micro(0, 0, 1, 444)?;
    /// assert_eq!(dt.timestamp_micros(), 1_000_444);
    ///
    /// let dt = NaiveDate::from_ymd(2001, 9, 9)?.and_hms_micro(1, 46, 40, 555)?;
    /// assert_eq!(dt.timestamp_micros(), 1_000_000_000_000_555);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn timestamp_micros(&self) -> i64 {
        let as_us = self.timestamp() * 1_000_000;
        as_us + i64::from(self.timestamp_subsec_micros())
    }

    /// Returns the number of non-leap *nanoseconds* since midnight on January 1, 1970.
    ///
    /// Note that this does *not* account for the timezone!
    /// The true "UNIX timestamp" would count seconds since the midnight *UTC* on the epoch.
    ///
    /// # Panics
    ///
    /// Note also that this does reduce the number of years that can be
    /// represented from ~584 Billion to ~584 years. The dates that can be
    /// represented as nanoseconds are between 1677-09-21T00:12:44.0 and
    /// 2262-04-11T23:47:16.854775804.
    ///
    /// (If this is a problem, please file an issue to let me know what domain
    /// needs nanosecond precision over millennia, I'm curious.)
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime};
    ///
    /// let dt = NaiveDate::from_ymd(1970, 1, 1)?.and_hms_nano(0, 0, 1, 444)?;
    /// assert_eq!(dt.timestamp_nanos(), 1_000_000_444);
    ///
    /// let dt = NaiveDate::from_ymd(2001, 9, 9)?.and_hms_nano(1, 46, 40, 555)?;
    ///
    /// const A_BILLION: i64 = 1_000_000_000;
    /// let nanos = dt.timestamp_nanos();
    /// assert_eq!(nanos, 1_000_000_000_000_000_555);
    /// assert_eq!(
    ///     dt,
    ///     NaiveDateTime::from_timestamp(nanos / A_BILLION, (nanos % A_BILLION) as u32)?
    /// );
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn timestamp_nanos(&self) -> i64 {
        let as_ns = self.timestamp() * 1_000_000_000;
        as_ns + i64::from(self.timestamp_subsec_nanos())
    }

    /// Returns the number of milliseconds since the last whole non-leap second.
    ///
    /// The return value ranges from 0 to 999,
    /// or for [leap seconds](./struct.NaiveTime.html#leap-second-handling), to 1,999.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd(2016, 7, 8)?.and_hms_nano(9, 10, 11, 123_456_789)?;
    /// assert_eq!(dt.timestamp_subsec_millis(), 123);
    ///
    /// let dt = NaiveDate::from_ymd(2015, 7, 1)?.and_hms_nano(8, 59, 59, 1_234_567_890)?;
    /// assert_eq!(dt.timestamp_subsec_millis(), 1_234);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn timestamp_subsec_millis(&self) -> u32 {
        self.timestamp_subsec_nanos() / 1_000_000
    }

    /// Returns the number of microseconds since the last whole non-leap second.
    ///
    /// The return value ranges from 0 to 999,999,
    /// or for [leap seconds](./struct.NaiveTime.html#leap-second-handling), to 1,999,999.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd(2016, 7, 8)?.and_hms_nano(9, 10, 11, 123_456_789)?;
    /// assert_eq!(dt.timestamp_subsec_micros(), 123_456);
    ///
    /// let dt = NaiveDate::from_ymd(2015, 7, 1)?.and_hms_nano(8, 59, 59, 1_234_567_890)?;
    /// assert_eq!(dt.timestamp_subsec_micros(), 1_234_567);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn timestamp_subsec_micros(&self) -> u32 {
        self.timestamp_subsec_nanos() / 1_000
    }

    /// Returns the number of nanoseconds since the last whole non-leap second.
    ///
    /// The return value ranges from 0 to 999,999,999,
    /// or for [leap seconds](./struct.NaiveTime.html#leap-second-handling), to 1,999,999,999.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd(2016, 7, 8)?.and_hms_nano(9, 10, 11, 123_456_789)?;
    /// assert_eq!(dt.timestamp_subsec_nanos(), 123_456_789);
    ///
    /// let dt = NaiveDate::from_ymd(2015, 7, 1)?.and_hms_nano(8, 59, 59, 1_234_567_890)?;
    /// assert_eq!(dt.timestamp_subsec_nanos(), 1_234_567_890);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn timestamp_subsec_nanos(&self) -> u32 {
        self.time.nanosecond()
    }

    /// Adds given `TimeDelta` to the current date and time.
    ///
    /// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
    /// the addition assumes that **there is no leap second ever**,
    /// except when the `NaiveDateTime` itself represents a leap second
    /// in which case the assumption becomes that **there is exactly a single leap second ever**.
    ///
    /// Returns `Err(Error)` when it will result in overflow.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeDelta, NaiveDate};
    ///
    /// let d = NaiveDate::from_ymd(2016, 7, 8)?;
    ///
    /// let hms = |h, m, s| d.and_hms(h, m, s);
    /// assert_eq!(hms(3, 5, 7)?.checked_add_signed(TimeDelta::zero()),
    ///            Ok(hms(3, 5, 7)?));
    /// assert_eq!(hms(3, 5, 7)?.checked_add_signed(TimeDelta::seconds(1)),
    ///            Ok(hms(3, 5, 8)?));
    /// assert_eq!(hms(3, 5, 7)?.checked_add_signed(TimeDelta::seconds(-1)),
    ///            Ok(hms(3, 5, 6)?));
    /// assert_eq!(hms(3, 5, 7)?.checked_add_signed(TimeDelta::seconds(3600 + 60)),
    ///            Ok(hms(4, 6, 7)?));
    /// assert_eq!(hms(3, 5, 7)?.checked_add_signed(TimeDelta::seconds(86_400)),
    ///            Ok(NaiveDate::from_ymd(2016, 7, 9)?.and_hms(3, 5, 7)?));
    ///
    /// let hmsm = |h, m, s, milli| d.and_hms_milli(h, m, s, milli);
    /// assert_eq!(hmsm(3, 5, 7, 980)?.checked_add_signed(TimeDelta::milliseconds(450)),
    ///            Ok(hmsm(3, 5, 8, 430)?));
    ///
    /// assert!(NaiveDate::from_ymd(2016, 7, 8)?.and_hms(3, 5, 7)?.checked_add_signed(TimeDelta::days(1_000_000_000)).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// Leap seconds are handled,
    /// but the addition assumes that it is the only leap second happened.
    ///
    /// ```
    /// # use chrono::{TimeDelta, NaiveDate};
    /// # let from_ymd = NaiveDate::from_ymd;
    /// # let hmsm = |h, m, s, milli| Ok::<_, chrono::Error>(from_ymd(2016, 7, 8)?.and_hms_milli(h, m, s, milli)?);
    /// let leap = hmsm(3, 5, 59, 1_300)?;
    /// assert_eq!(leap.checked_add_signed(TimeDelta::zero()),
    ///            Ok(hmsm(3, 5, 59, 1_300)?));
    /// assert_eq!(leap.checked_add_signed(TimeDelta::milliseconds(-500)),
    ///            Ok(hmsm(3, 5, 59, 800)?));
    /// assert_eq!(leap.checked_add_signed(TimeDelta::milliseconds(500)),
    ///            Ok(hmsm(3, 5, 59, 1_800)?));
    /// assert_eq!(leap.checked_add_signed(TimeDelta::milliseconds(800)),
    ///            Ok(hmsm(3, 6, 0, 100)?));
    /// assert_eq!(leap.checked_add_signed(TimeDelta::seconds(10)),
    ///            Ok(hmsm(3, 6, 9, 300)?));
    /// assert_eq!(leap.checked_add_signed(TimeDelta::seconds(-10)),
    ///            Ok(hmsm(3, 5, 50, 300)?));
    /// assert_eq!(leap.checked_add_signed(TimeDelta::days(1)),
    ///            Ok(from_ymd(2016, 7, 9)?.and_hms_milli(3, 5, 59, 300)?));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    pub fn checked_add_signed(self, rhs: TimeDelta) -> Result<Self, Error> {
        let (time, rhs) = self.time.overflowing_add_signed(rhs);

        // early checking to avoid overflow in OldTimeDelta::seconds
        if rhs <= (-1 << MAX_SECS_BITS) || rhs >= (1 << MAX_SECS_BITS) {
            return Err(Error::ParsingOutOfRange);
        }

        let date = self.date.checked_add_signed(TimeDelta::seconds(rhs))?;
        Ok(Self { date, time })
    }

    /// Adds given `Months` to the current date and time.
    ///
    /// Returns `Err(Error)` when it will result in overflow.
    ///
    /// # Example
    ///
    /// ```
    /// use std::str::FromStr;
    /// use chrono::{Months, NaiveDate, NaiveDateTime};
    ///
    /// assert_eq!(
    ///     NaiveDate::from_ymd(2014, 1, 1)?.and_hms(1, 0, 0)?
    ///         .checked_add_months(Months::new(1)),
    ///     Ok(NaiveDate::from_ymd(2014, 2, 1)?.and_hms(1, 0, 0)?)
    /// );
    ///
    /// assert!(
    ///     NaiveDate::from_ymd(2014, 1, 1)?.and_hms(1, 0, 0)?
    ///         .checked_add_months(Months::new(core::i32::MAX as u32 + 1))
    ///         .is_err()
    /// );
    /// # Ok::<_, chrono::Error>(())
    /// ```
    pub fn checked_add_months(self, rhs: Months) -> Result<Self, Error> {
        Ok(Self { date: self.date.checked_add_months(rhs)?, time: self.time })
    }

    /// Subtracts given `TimeDelta` from the current date and time.
    ///
    /// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
    /// the subtraction assumes that **there is no leap second ever**,
    /// except when the `NaiveDateTime` itself represents a leap second
    /// in which case the assumption becomes that **there is exactly a single leap second ever**.
    ///
    /// Returns `Err(Error)` when it will result in overflow.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeDelta, NaiveDate};
    ///
    /// let d = NaiveDate::from_ymd(2016, 7, 8)?;
    ///
    /// assert_eq!(d.and_hms(3, 5, 7)?.checked_sub_signed(TimeDelta::zero()),
    ///            Ok(d.and_hms(3, 5, 7)?));
    /// assert_eq!(d.and_hms(3, 5, 7)?.checked_sub_signed(TimeDelta::seconds(1)),
    ///            Ok(d.and_hms(3, 5, 6)?));
    /// assert_eq!(d.and_hms(3, 5, 7)?.checked_sub_signed(TimeDelta::seconds(-1)),
    ///            Ok(d.and_hms(3, 5, 8)?));
    /// assert_eq!(d.and_hms(3, 5, 7)?.checked_sub_signed(TimeDelta::seconds(3600 + 60)),
    ///            Ok(d.and_hms(2, 4, 7)?));
    /// assert_eq!(d.and_hms(3, 5, 7)?.checked_sub_signed(TimeDelta::seconds(86_400)),
    ///            Ok(NaiveDate::from_ymd(2016, 7, 7)?.and_hms(3, 5, 7)?));
    ///
    /// assert_eq!(d.and_hms_milli(3, 5, 7, 450)?.checked_sub_signed(TimeDelta::milliseconds(670)),
    ///            Ok(d.and_hms_milli(3, 5, 6, 780)?));
    ///
    /// let dt = NaiveDate::from_ymd(2016, 7, 8)?.and_hms(3, 5, 7)?;
    /// assert!(dt.checked_sub_signed(TimeDelta::days(1_000_000_000)).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// Leap seconds are handled, but the subtraction assumes that it is the
    /// only leap second happened.
    ///
    /// ```
    /// # use chrono::{TimeDelta, NaiveDate};
    /// # let from_ymd = NaiveDate::from_ymd;
    /// # let hmsm = |h, m, s, milli| Ok::<_, chrono::Error>(from_ymd(2016, 7, 8)?.and_hms_milli(h, m, s, milli)?);
    /// let leap = hmsm(3, 5, 59, 1_300)?;
    /// assert_eq!(leap.checked_sub_signed(TimeDelta::zero()),
    ///            Ok(hmsm(3, 5, 59, 1_300)?));
    /// assert_eq!(leap.checked_sub_signed(TimeDelta::milliseconds(200)),
    ///            Ok(hmsm(3, 5, 59, 1_100)?));
    /// assert_eq!(leap.checked_sub_signed(TimeDelta::milliseconds(500)),
    ///            Ok(hmsm(3, 5, 59, 800)?));
    /// assert_eq!(leap.checked_sub_signed(TimeDelta::seconds(60)),
    ///            Ok(hmsm(3, 5, 0, 300)?));
    /// assert_eq!(leap.checked_sub_signed(TimeDelta::days(1)),
    ///            Ok(from_ymd(2016, 7, 7)?.and_hms_milli(3, 6, 0, 300)?));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    pub fn checked_sub_signed(self, rhs: TimeDelta) -> Result<Self, Error> {
        let (time, rhs) = self.time.overflowing_sub_signed(rhs);

        // early checking to avoid overflow in OldTimeDelta::seconds
        if rhs <= (-1 << MAX_SECS_BITS) || rhs >= (1 << MAX_SECS_BITS) {
            return Err(Error::ParsingOutOfRange);
        }

        let date = self.date.checked_sub_signed(TimeDelta::seconds(rhs))?;
        Ok(Self { date, time })
    }

    /// Subtracts given `Months` from the current date and time.
    ///
    /// Returns `Err(Error)` when it will result in overflow.
    ///
    /// # Example
    ///
    /// ```
    /// use std::str::FromStr;
    /// use chrono::{Months, NaiveDate, NaiveDateTime};
    ///
    /// assert_eq!(
    ///     NaiveDate::from_ymd(2014, 1, 1)?.and_hms(1, 0, 0)?.checked_sub_months(Months::new(1)),
    ///     Ok(NaiveDate::from_ymd(2013, 12, 1)?.and_hms(1, 0, 0)?)
    /// );
    ///
    /// assert!(
    ///     NaiveDate::from_ymd(2014, 1, 1)?.and_hms(1, 0, 0)?
    ///         .checked_sub_months(Months::new(core::i32::MAX as u32 + 1))
    ///         .is_err()
    /// );
    /// # Ok::<_, chrono::Error>(())
    /// ```
    pub fn checked_sub_months(self, rhs: Months) -> Result<Self, Error> {
        Ok(Self { date: self.date.checked_sub_months(rhs)?, time: self.time })
    }

    /// Add a duration in [`Days`] to the date part of the `NaiveDateTime`
    ///
    /// Returns `Err(Error)` if the resulting date would be out of range.
    pub fn checked_add_days(self, days: Days) -> Result<Self, Error> {
        Ok(Self { date: self.date.checked_add_days(days)?, ..self })
    }

    /// Subtract a duration in [`Days`] from the date part of the `NaiveDateTime`
    ///
    /// Returns `Err(Error)` if the resulting date would be out of range.
    pub fn checked_sub_days(self, days: Days) -> Result<Self, Error> {
        Ok(Self { date: self.date.checked_sub_days(days)?, ..self })
    }

    /// Subtracts another `NaiveDateTime` from the current date and time.
    /// This does not overflow or underflow at all.
    ///
    /// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
    /// the subtraction assumes that **there is no leap second ever**,
    /// except when any of the `NaiveDateTime`s themselves represents a leap second
    /// in which case the assumption becomes that
    /// **there are exactly one (or two) leap second(s) ever**.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeDelta, NaiveDate};
    ///
    /// let from_ymd = NaiveDate::from_ymd;
    ///
    /// let d = from_ymd(2016, 7, 8)?;
    /// assert_eq!(d.and_hms(3, 5, 7)?.signed_duration_since(d.and_hms(2, 4, 6)?),
    ///            TimeDelta::seconds(3600 + 60 + 1));
    ///
    /// // July 8 is 190th day in the year 2016
    /// let d0 = from_ymd(2016, 1, 1)?;
    /// assert_eq!(d.and_hms_milli(0, 7, 6, 500)?.signed_duration_since(d0.and_hms(0, 0, 0)?),
    ///            TimeDelta::seconds(189 * 86_400 + 7 * 60 + 6) + TimeDelta::milliseconds(500));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// Leap seconds are handled, but the subtraction assumes that
    /// there were no other leap seconds happened.
    ///
    /// ```
    /// # use chrono::{TimeDelta, NaiveDate};
    /// # let from_ymd = NaiveDate::from_ymd;
    /// let leap = from_ymd(2015, 6, 30)?.and_hms_milli(23, 59, 59, 1_500)?;
    /// assert_eq!(leap.signed_duration_since(from_ymd(2015, 6, 30)?.and_hms(23, 0, 0)?),
    ///            TimeDelta::seconds(3600) + TimeDelta::milliseconds(500));
    /// assert_eq!(from_ymd(2015, 7, 1)?.and_hms(1, 0, 0)?.signed_duration_since(leap),
    ///            TimeDelta::seconds(3600) - TimeDelta::milliseconds(500));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    pub fn signed_duration_since(self, rhs: NaiveDateTime) -> TimeDelta {
        self.date.signed_duration_since(rhs.date) + self.time.signed_duration_since(rhs.time)
    }

    /// Formats the combined date and time with the specified formatting items.
    /// Otherwise it is the same as the ordinary [`format`](#method.format) method.
    ///
    /// The `Iterator` of items should be `Clone`able,
    /// since the resulting `DelayedFormat` value may be formatted multiple times.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    /// use chrono::format::strftime::StrftimeItems;
    ///
    /// let fmt = StrftimeItems::new("%Y-%m-%d %H:%M:%S");
    /// let dt = NaiveDate::from_ymd(2015, 9, 5)?.and_hms(23, 56, 4)?;
    /// assert_eq!(dt.format_with_items(fmt.clone()).to_string(), "2015-09-05 23:56:04");
    /// assert_eq!(dt.format("%Y-%m-%d %H:%M:%S").to_string(),    "2015-09-05 23:56:04");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// The resulting `DelayedFormat` can be formatted directly via the `Display` trait.
    ///
    /// ```
    /// # use chrono::NaiveDate;
    /// # use chrono::format::strftime::StrftimeItems;
    /// # let fmt = StrftimeItems::new("%Y-%m-%d %H:%M:%S").clone();
    /// # let dt = NaiveDate::from_ymd(2015, 9, 5)?.and_hms(23, 56, 4)?;
    /// assert_eq!(format!("{}", dt.format_with_items(fmt)), "2015-09-05 23:56:04");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    pub fn format_with_items<'a, I, B>(&self, items: I) -> DelayedFormat<I>
    where
        I: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        DelayedFormat::new(Some(self.date), Some(self.time), items)
    }

    /// Formats the combined date and time with the specified format string.
    /// See the [`format::strftime` module](../format/strftime/index.html)
    /// on the supported escape sequences.
    ///
    /// This returns a `DelayedFormat`,
    /// which gets converted to a string only when actual formatting happens.
    /// You may use the `to_string` method to get a `String`,
    /// or just feed it into `print!` and other formatting macros.
    /// (In this way it avoids the redundant memory allocation.)
    ///
    /// A wrong format string does *not* issue an error immediately.
    /// Rather, converting or formatting the `DelayedFormat` fails.
    /// You are recommended to immediately use `DelayedFormat` for this reason.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd(2015, 9, 5)?.and_hms(23, 56, 4)?;
    /// assert_eq!(dt.format("%Y-%m-%d %H:%M:%S").to_string(), "2015-09-05 23:56:04");
    /// assert_eq!(dt.format("around %l %p on %b %-d").to_string(), "around 11 PM on Sep 5");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// The resulting `DelayedFormat` can be formatted directly via the `Display` trait.
    ///
    /// ```
    /// # use chrono::NaiveDate;
    /// # let dt = NaiveDate::from_ymd(2015, 9, 5)?.and_hms(23, 56, 4)?;
    /// assert_eq!(format!("{}", dt.format("%Y-%m-%d %H:%M:%S")), "2015-09-05 23:56:04");
    /// assert_eq!(format!("{}", dt.format("around %l %p on %b %-d")), "around 11 PM on Sep 5");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_with_items(StrftimeItems::new(fmt))
    }

    /// Converts the `NaiveDateTime` into the timezone-aware `DateTime<Tz>`
    /// with the provided timezone, if possible.
    ///
    /// This can fail in cases where the local time represented by the `NaiveDateTime`
    /// is not a valid local timestamp in the target timezone due to an offset transition
    /// for example if the target timezone had a change from +00:00 to +01:00
    /// occuring at 2015-09-05 22:59:59, then a local time of 2015-09-05 23:56:04
    /// could never occur. Similarly, if the offset transitioned in the opposite direction
    /// then there would be two local times of 2015-09-05 23:56:04, one at +00:00 and one
    /// at +01:00.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, Utc};
    /// let dt = NaiveDate::from_ymd(2015, 9, 5)?.and_hms(23, 56, 4)?.and_local_timezone(Utc)?;
    /// assert_eq!(dt.timezone(), Utc);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    pub fn and_local_timezone<Tz: TimeZone>(&self, tz: Tz) -> Result<DateTime<Tz>, Error> {
        tz.from_local_datetime(self)?.single()
    }

    /// The minimum possible `NaiveDateTime`.
    pub const MIN: Self = Self { date: NaiveDate::MIN, time: NaiveTime::MIN };
    /// The maximum possible `NaiveDateTime`.
    pub const MAX: Self = Self { date: NaiveDate::MAX, time: NaiveTime::MAX };

    /// Creates a new [NaiveDateTime] from milliseconds or microseconds since the UNIX epoch.
    ///
    /// This is a private function used by [from_timestamp_millis] and [from_timestamp_micros].
    #[inline]
    fn from_timestamp_unit(value: i64, unit: TimestampUnit) -> Result<NaiveDateTime, Error> {
        let (secs, subsecs) =
            (value / i64::from(unit.per_second()), value % i64::from(unit.per_second()));

        match subsecs.cmp(&0) {
            Ordering::Less => {
                // in the case where our subsec part is negative, then we are actually in the earlier second
                // hence we subtract one from the seconds part, and we then add a whole second worth of nanos
                // to our nanos part. Due to the use of u32 datatype, it is more convenient to subtract
                // the absolute value of the subsec nanos from a whole second worth of nanos
                let nsecs = u32::try_from(subsecs.abs())? * unit.nanos_per();
                NaiveDateTime::from_timestamp(
                    match secs.checked_sub(1) {
                        None => return Err(Error::ParsingOutOfRange),
                        Some(secs) => secs,
                    },
                    match NANOS_IN_SECOND.checked_sub(nsecs) {
                        None => return Err(Error::ParsingOutOfRange),
                        Some(nsecs) => nsecs,
                    },
                )
            }
            Ordering::Equal => NaiveDateTime::from_timestamp(secs, 0),
            Ordering::Greater => {
                // convert the subsec millis into nanosecond scale so they can be supplied
                // as the nanoseconds parameter
                let nsecs = u32::try_from(subsecs)? * unit.nanos_per();
                NaiveDateTime::from_timestamp(secs, nsecs)
            }
        }
    }
}

impl Datelike for NaiveDateTime {
    /// Returns the year number in the [calendar date](./index.html#calendar-date).
    ///
    /// See also the [`NaiveDate::year`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 25)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.year(), 2015);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn year(&self) -> i32 {
        self.date.year()
    }

    /// Returns the month number starting from 1.
    ///
    /// The return value ranges from 1 to 12.
    ///
    /// See also the [`NaiveDate::month`](./struct.NaiveDate.html#method.month) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 25)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.month(), 9);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn month(&self) -> u32 {
        self.date.month()
    }

    /// Returns the month number starting from 0.
    ///
    /// The return value ranges from 0 to 11.
    ///
    /// See also the [`NaiveDate::month0`](./struct.NaiveDate.html#method.month0) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 25)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.month0(), 8);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn month0(&self) -> u32 {
        self.date.month0()
    }

    /// Returns the day of month starting from 1.
    ///
    /// The return value ranges from 1 to 31. (The last day of month differs by months.)
    ///
    /// See also the [`NaiveDate::day`](./struct.NaiveDate.html#method.day) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 25)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.day(), 25);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn day(&self) -> u32 {
        self.date.day()
    }

    /// Returns the day of month starting from 0.
    ///
    /// The return value ranges from 0 to 30. (The last day of month differs by months.)
    ///
    /// See also the [`NaiveDate::day0`](./struct.NaiveDate.html#method.day0) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 25)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.day0(), 24);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn day0(&self) -> u32 {
        self.date.day0()
    }

    /// Returns the day of year starting from 1.
    ///
    /// The return value ranges from 1 to 366. (The last day of year differs by years.)
    ///
    /// See also the [`NaiveDate::ordinal`](./struct.NaiveDate.html#method.ordinal) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 25)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.ordinal(), 268);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn ordinal(&self) -> u32 {
        self.date.ordinal()
    }

    /// Returns the day of year starting from 0.
    ///
    /// The return value ranges from 0 to 365. (The last day of year differs by years.)
    ///
    /// See also the [`NaiveDate::ordinal0`](./struct.NaiveDate.html#method.ordinal0) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 25)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.ordinal0(), 267);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn ordinal0(&self) -> u32 {
        self.date.ordinal0()
    }

    /// Returns the day of week.
    ///
    /// See also the [`NaiveDate::weekday`](./struct.NaiveDate.html#method.weekday) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike, Weekday};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 25)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.weekday(), Weekday::Fri);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn weekday(&self) -> Weekday {
        self.date.weekday()
    }

    #[inline]
    fn iso_week(&self) -> IsoWeek {
        self.date.iso_week()
    }

    /// Makes a new `NaiveDateTime` with the year number changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 25)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.with_year(2016)?, NaiveDate::from_ymd(2016, 9, 25)?.and_hms(12, 34, 56)?);
    /// assert_eq!(dt.with_year(-308)?, NaiveDate::from_ymd(-308, 9, 25)?.and_hms(12, 34, 56)?);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_year(&self, year: i32) -> Result<NaiveDateTime, Error> {
        let d = self.date.with_year(year)?;
        Ok(NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the month number (starting from 1) changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 30)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.with_month(10)?, NaiveDate::from_ymd(2015, 10, 30)?.and_hms(12, 34, 56)?);
    /// assert!(dt.with_month(13).is_err()); // no month 13
    /// assert!(dt.with_month(2).is_err()); // no February 30
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_month(&self, month: u32) -> Result<NaiveDateTime, Error> {
        let d = self.date.with_month(month)?;
        Ok(NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the month number (starting from 0) changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 30)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.with_month0(9)?, NaiveDate::from_ymd(2015, 10, 30)?.and_hms(12, 34, 56)?);
    /// assert!(dt.with_month0(12).is_err()); // no month 13
    /// assert!(dt.with_month0(1).is_err()); // no February 30
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_month0(&self, month0: u32) -> Result<NaiveDateTime, Error> {
        let d = self.date.with_month0(month0)?;
        Ok(NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the day of month (starting from 1) changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 8)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.with_day(30)?, NaiveDate::from_ymd(2015, 9, 30)?.and_hms(12, 34, 56)?);
    /// assert!(dt.with_day(31).is_err()); // no September 31
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_day(&self, day: u32) -> Result<NaiveDateTime, Error> {
        let d = self.date.with_day(day)?;
        Ok(NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the day of month (starting from 0) changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt = NaiveDate::from_ymd(2015, 9, 8)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.with_day0(29)?, NaiveDate::from_ymd(2015, 9, 30)?.and_hms(12, 34, 56)?);
    /// assert!(dt.with_day0(30).is_err()); // no September 31
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_day0(&self, day0: u32) -> Result<NaiveDateTime, Error> {
        let d = self.date.with_day0(day0)?;
        Ok(NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the day of year (starting from 1) changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt = NaiveDate::from_ymd(2015, 9, 8)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.with_ordinal(60)?,
    ///            NaiveDate::from_ymd(2015, 3, 1)?.and_hms(12, 34, 56)?);
    /// assert!(dt.with_ordinal(366).is_err()); // 2015 had only 365 days
    ///
    /// let dt = NaiveDate::from_ymd(2016, 9, 8)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.with_ordinal(60)?,
    ///            NaiveDate::from_ymd(2016, 2, 29)?.and_hms(12, 34, 56)?);
    /// assert_eq!(dt.with_ordinal(366)?,
    ///            NaiveDate::from_ymd(2016, 12, 31)?.and_hms(12, 34, 56)?);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Result<NaiveDateTime, Error> {
        let d = self.date.with_ordinal(ordinal)?;
        Ok(NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the day of year (starting from 0) changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt = NaiveDate::from_ymd(2015, 9, 8)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.with_ordinal0(59)?,
    ///            NaiveDate::from_ymd(2015, 3, 1)?.and_hms(12, 34, 56)?);
    /// assert!(dt.with_ordinal0(365).is_err()); // 2015 had only 365 days
    ///
    /// let dt = NaiveDate::from_ymd(2016, 9, 8)?.and_hms(12, 34, 56)?;
    /// assert_eq!(dt.with_ordinal0(59)?,
    ///            NaiveDate::from_ymd(2016, 2, 29)?.and_hms(12, 34, 56)?);
    /// assert_eq!(dt.with_ordinal0(365)?,
    ///            NaiveDate::from_ymd(2016, 12, 31)?.and_hms(12, 34, 56)?);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Result<NaiveDateTime, Error> {
        let d = self.date.with_ordinal0(ordinal0)?;
        Ok(NaiveDateTime { date: d, ..*self })
    }
}

impl Timelike for NaiveDateTime {
    /// Returns the hour number from 0 to 23.
    ///
    /// See also the [`NaiveTime::hour`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 34, 56, 789)?;
    /// assert_eq!(dt.hour(), 12);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn hour(&self) -> u32 {
        self.time.hour()
    }

    /// Returns the minute number from 0 to 59.
    ///
    /// See also the [`NaiveTime::minute`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 34, 56, 789)?;
    /// assert_eq!(dt.minute(), 34);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn minute(&self) -> u32 {
        self.time.minute()
    }

    /// Returns the second number from 0 to 59.
    ///
    /// See also the [`NaiveTime::second`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 34, 56, 789)?;
    /// assert_eq!(dt.second(), 56);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn second(&self) -> u32 {
        self.time.second()
    }

    /// Returns the number of nanoseconds since the whole non-leap second.
    /// The range from 1,000,000,000 to 1,999,999,999 represents
    /// the [leap second](./struct.NaiveTime.html#leap-second-handling).
    ///
    /// See also the [`NaiveTime::nanosecond`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 34, 56, 789)?;
    /// assert_eq!(dt.nanosecond(), 789_000_000);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn nanosecond(&self) -> u32 {
        self.time.nanosecond()
    }

    /// Makes a new `NaiveDateTime` with the hour number changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the [`NaiveTime::with_hour`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 34, 56, 789)?;
    /// assert_eq!(dt.with_hour(7)?,
    ///            NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(7, 34, 56, 789)?);
    /// assert!(dt.with_hour(24).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_hour(&self, hour: u32) -> Result<NaiveDateTime, Error> {
        let t = self.time.with_hour(hour)?;
        Ok(NaiveDateTime { time: t, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the minute number changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the
    /// [`NaiveTime::with_minute`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 34, 56, 789)?;
    /// assert_eq!(dt.with_minute(45)?,
    ///            NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 45, 56, 789)?);
    /// assert!(dt.with_minute(60).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_minute(&self, min: u32) -> Result<NaiveDateTime, Error> {
        let t = self.time.with_minute(min)?;
        Ok(NaiveDateTime { time: t, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the second number changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    /// As with the [`NaiveDateTime::second`] method, the input range
    /// is restricted to 0 through 59.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt = NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 34, 56, 789)?;
    /// assert_eq!(dt.with_second(17)?,
    ///            NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 34, 17, 789)?);
    /// assert!(dt.with_second(60).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_second(&self, sec: u32) -> Result<NaiveDateTime, Error> {
        let t = self.time.with_second(sec)?;
        Ok(NaiveDateTime { time: t, ..*self })
    }

    /// Makes a new `NaiveDateTime` with nanoseconds since the whole non-leap second changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveDateTime` would be invalid.
    /// As with the [`NaiveDateTime::nanosecond`] method,
    /// the input range can exceed 1,000,000,000 for leap seconds.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd(2015, 9, 8)?.and_hms_milli(12, 34, 56, 789)?;
    /// assert_eq!(dt.with_nanosecond(333_333_333)?,
    ///            NaiveDate::from_ymd(2015, 9, 8)?.and_hms_nano(12, 34, 56, 333_333_333)?);
    /// assert_eq!(dt.with_nanosecond(1_333_333_333)?, // leap second
    ///            NaiveDate::from_ymd(2015, 9, 8)?.and_hms_nano(12, 34, 56, 1_333_333_333)?);
    /// assert!(dt.with_nanosecond(2_000_000_000).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Result<NaiveDateTime, Error> {
        let t = self.time.with_nanosecond(nano)?;
        Ok(NaiveDateTime { time: t, ..*self })
    }
}

/// An addition of `TimeDelta` to `NaiveDateTime` yields another `NaiveDateTime`.
///
/// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
/// the addition assumes that **there is no leap second ever**,
/// except when the `NaiveDateTime` itself represents a leap second
/// in which case the assumption becomes that **there is exactly a single leap second ever**.
///
/// Panics on underflow or overflow. Use [`NaiveDateTime::checked_add_signed`]
/// to detect that.
///
/// # Example
///
/// ```
/// use chrono::{TimeDelta, NaiveDate};
///
/// let d = NaiveDate::from_ymd(2016, 7, 8)?;
/// let hms = |h, m, s| d.and_hms(h, m, s);
/// assert_eq!(hms(3, 5, 7)? + TimeDelta::zero(), hms(3, 5, 7)?);
/// assert_eq!(hms(3, 5, 7)? + TimeDelta::seconds(1), hms(3, 5, 8)?);
/// assert_eq!(hms(3, 5, 7)? + TimeDelta::seconds(-1), hms(3, 5, 6)?);
/// assert_eq!(hms(3, 5, 7)? + TimeDelta::seconds(3600 + 60), hms(4, 6, 7)?);
/// assert_eq!(hms(3, 5, 7)? + TimeDelta::seconds(86_400),
///            NaiveDate::from_ymd(2016, 7, 9)?.and_hms(3, 5, 7)?);
/// assert_eq!(hms(3, 5, 7)? + TimeDelta::days(365),
///            NaiveDate::from_ymd(2017, 7, 8)?.and_hms(3, 5, 7)?);
///
/// let hmsm = |h, m, s, milli| d.and_hms_milli(h, m, s, milli);
/// assert_eq!(hmsm(3, 5, 7, 980)? + TimeDelta::milliseconds(450), hmsm(3, 5, 8, 430)?);
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds are handled,
/// but the addition assumes that it is the only leap second happened.
///
/// ```
/// # use chrono::{TimeDelta, NaiveDate};
/// # let from_ymd = NaiveDate::from_ymd;
/// # let hmsm = |h, m, s, milli| from_ymd(2016, 7, 8)?.and_hms_milli(h, m, s, milli);
/// let leap = hmsm(3, 5, 59, 1_300)?;
/// assert_eq!(leap + TimeDelta::zero(), hmsm(3, 5, 59, 1_300)?);
/// assert_eq!(leap + TimeDelta::milliseconds(-500), hmsm(3, 5, 59, 800)?);
/// assert_eq!(leap + TimeDelta::milliseconds(500), hmsm(3, 5, 59, 1_800)?);
/// assert_eq!(leap + TimeDelta::milliseconds(800), hmsm(3, 6, 0, 100)?);
/// assert_eq!(leap + TimeDelta::seconds(10), hmsm(3, 6, 9, 300)?);
/// assert_eq!(leap + TimeDelta::seconds(-10), hmsm(3, 5, 50, 300)?);
/// assert_eq!(leap + TimeDelta::days(1),
///            from_ymd(2016, 7, 9)?.and_hms_milli(3, 5, 59, 300)?);
/// # Ok::<_, chrono::Error>(())
/// ```
impl Add<TimeDelta> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn add(self, rhs: TimeDelta) -> NaiveDateTime {
        self.checked_add_signed(rhs).expect("`NaiveDateTime + TimeDelta` overflowed")
    }
}

impl AddAssign<TimeDelta> for NaiveDateTime {
    #[inline]
    fn add_assign(&mut self, rhs: TimeDelta) {
        *self = self.add(rhs);
    }
}

impl Add<Months> for NaiveDateTime {
    type Output = NaiveDateTime;

    /// An addition of months to `NaiveDateTime` clamped to valid days in resulting month.
    ///
    /// # Panics
    ///
    /// Panics if the resulting date would be out of range.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeDelta, NaiveDateTime, Months, NaiveDate};
    /// use std::str::FromStr;
    ///
    /// assert_eq!(
    ///     NaiveDate::from_ymd(2014, 1, 1)?.and_hms(1, 0, 0)? + Months::new(1),
    ///     NaiveDate::from_ymd(2014, 2, 1)?.and_hms(1, 0, 0)?
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd(2014, 1, 1)?.and_hms(0, 2, 0)? + Months::new(11),
    ///     NaiveDate::from_ymd(2014, 12, 1)?.and_hms(0, 2, 0)?
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd(2014, 1, 1)?.and_hms(0, 0, 3)? + Months::new(12),
    ///     NaiveDate::from_ymd(2015, 1, 1)?.and_hms(0, 0, 3)?
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd(2014, 1, 1)?.and_hms(0, 0, 4)? + Months::new(13),
    ///     NaiveDate::from_ymd(2015, 2, 1)?.and_hms(0, 0, 4)?
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd(2014, 1, 31)?.and_hms(0, 5, 0)? + Months::new(1),
    ///     NaiveDate::from_ymd(2014, 2, 28)?.and_hms(0, 5, 0)?
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd(2020, 1, 31)?.and_hms(6, 0, 0)? + Months::new(1),
    ///     NaiveDate::from_ymd(2020, 2, 29)?.and_hms(6, 0, 0)?
    /// );
    /// # Ok::<_, chrono::Error>(())
    /// ```
    fn add(self, rhs: Months) -> Self::Output {
        Self { date: self.date.checked_add_months(rhs).unwrap(), time: self.time }
    }
}

/// A subtraction of `TimeDelta` from `NaiveDateTime` yields another `NaiveDateTime`.
/// It is the same as the addition with a negated `TimeDelta`.
///
/// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
/// the addition assumes that **there is no leap second ever**,
/// except when the `NaiveDateTime` itself represents a leap second
/// in which case the assumption becomes that **there is exactly a single leap second ever**.
///
/// Panics on underflow or overflow. Use [`NaiveDateTime::checked_sub_signed`]
/// to detect that.
///
/// # Example
///
/// ```
/// use chrono::{TimeDelta, NaiveDate};
///
/// let from_ymd = NaiveDate::from_ymd;
///
/// let d = from_ymd(2016, 7, 8)?;
/// let hms = |h, m, s| d.and_hms(h, m, s);
/// assert_eq!(hms(3, 5, 7)? - TimeDelta::zero(), hms(3, 5, 7)?);
/// assert_eq!(hms(3, 5, 7)? - TimeDelta::seconds(1), hms(3, 5, 6)?);
/// assert_eq!(hms(3, 5, 7)? - TimeDelta::seconds(-1), hms(3, 5, 8)?);
/// assert_eq!(hms(3, 5, 7)? - TimeDelta::seconds(3600 + 60), hms(2, 4, 7)?);
/// assert_eq!(hms(3, 5, 7)? - TimeDelta::seconds(86_400),
///            from_ymd(2016, 7, 7)?.and_hms(3, 5, 7)?);
/// assert_eq!(hms(3, 5, 7)? - TimeDelta::days(365),
///            from_ymd(2015, 7, 9)?.and_hms(3, 5, 7)?);
///
/// let hmsm = |h, m, s, milli| d.and_hms_milli(h, m, s, milli);
/// assert_eq!(hmsm(3, 5, 7, 450)? - TimeDelta::milliseconds(670), hmsm(3, 5, 6, 780)?);
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds are handled,
/// but the subtraction assumes that it is the only leap second happened.
///
/// ```
/// # use chrono::{TimeDelta, NaiveDate};
/// # let from_ymd = NaiveDate::from_ymd;
/// # let hmsm = |h, m, s, milli| Ok::<_, chrono::Error>(from_ymd(2016, 7, 8)?.and_hms_milli(h, m, s, milli)?);
/// let leap = hmsm(3, 5, 59, 1_300)?;
/// assert_eq!(leap - TimeDelta::zero(), hmsm(3, 5, 59, 1_300)?);
/// assert_eq!(leap - TimeDelta::milliseconds(200), hmsm(3, 5, 59, 1_100)?);
/// assert_eq!(leap - TimeDelta::milliseconds(500), hmsm(3, 5, 59, 800)?);
/// assert_eq!(leap - TimeDelta::seconds(60), hmsm(3, 5, 0, 300)?);
/// assert_eq!(leap - TimeDelta::days(1),
///            from_ymd(2016, 7, 7)?.and_hms_milli(3, 6, 0, 300)?);
/// # Ok::<_, chrono::Error>(())
/// ```
impl Sub<TimeDelta> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn sub(self, rhs: TimeDelta) -> NaiveDateTime {
        self.checked_sub_signed(rhs).expect("`NaiveDateTime - TimeDelta` overflowed")
    }
}

impl SubAssign<TimeDelta> for NaiveDateTime {
    #[inline]
    fn sub_assign(&mut self, rhs: TimeDelta) {
        *self = self.sub(rhs);
    }
}

/// A subtraction of Months from `NaiveDateTime` clamped to valid days in resulting month.
///
/// # Panics
///
/// Panics if the resulting date would be out of range.
///
/// # Example
///
/// ```
/// use chrono::{TimeDelta, NaiveDateTime, Months, NaiveDate};
/// use std::str::FromStr;
///
/// assert_eq!(
///     NaiveDate::from_ymd(2014, 01, 01)?.and_hms(01, 00, 00)? - Months::new(11),
///     NaiveDate::from_ymd(2013, 02, 01)?.and_hms(01, 00, 00)?
/// );
/// assert_eq!(
///     NaiveDate::from_ymd(2014, 01, 01)?.and_hms(00, 02, 00)? - Months::new(12),
///     NaiveDate::from_ymd(2013, 01, 01)?.and_hms(00, 02, 00)?
/// );
/// assert_eq!(
///     NaiveDate::from_ymd(2014, 01, 01)?.and_hms(00, 00, 03)? - Months::new(13),
///     NaiveDate::from_ymd(2012, 12, 01)?.and_hms(00, 00, 03)?
/// );
/// # Ok::<_, chrono::Error>(())
/// ```
impl Sub<Months> for NaiveDateTime {
    type Output = NaiveDateTime;

    fn sub(self, rhs: Months) -> Self::Output {
        Self { date: self.date.checked_sub_months(rhs).unwrap(), time: self.time }
    }
}

/// Subtracts another `NaiveDateTime` from the current date and time.
/// This does not overflow or underflow at all.
///
/// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
/// the subtraction assumes that **there is no leap second ever**,
/// except when any of the `NaiveDateTime`s themselves represents a leap second
/// in which case the assumption becomes that
/// **there are exactly one (or two) leap second(s) ever**.
///
/// The implementation is a wrapper around [`NaiveDateTime::signed_duration_since`].
///
/// # Example
///
/// ```
/// use chrono::{TimeDelta, NaiveDate};
///
/// let d = NaiveDate::from_ymd(2016, 7, 8)?;
/// assert_eq!(d.and_hms(3, 5, 7)? - d.and_hms(2, 4, 6)?, TimeDelta::seconds(3600 + 60 + 1));
///
/// // July 8 is 190th day in the year 2016
/// let d0 = NaiveDate::from_ymd(2016, 1, 1)?;
/// assert_eq!(d.and_hms_milli(0, 7, 6, 500)? - d0.and_hms(0, 0, 0)?,
///            TimeDelta::seconds(189 * 86_400 + 7 * 60 + 6) + TimeDelta::milliseconds(500));
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds are handled, but the subtraction assumes that no other leap
/// seconds happened.
///
/// ```
/// # use chrono::{TimeDelta, NaiveDate};
/// let leap = NaiveDate::from_ymd(2015, 6, 30)?.and_hms_milli(23, 59, 59, 1_500)?;
///
/// assert_eq!(leap - NaiveDate::from_ymd(2015, 6, 30)?.and_hms(23, 0, 0)?,
///            TimeDelta::seconds(3600) + TimeDelta::milliseconds(500));
///
/// assert_eq!(NaiveDate::from_ymd(2015, 7, 1)?.and_hms(1, 0, 0)? - leap,
///            TimeDelta::seconds(3600) - TimeDelta::milliseconds(500));
/// # Ok::<_, chrono::Error>(())
/// ```
impl Sub<NaiveDateTime> for NaiveDateTime {
    type Output = TimeDelta;

    #[inline]
    fn sub(self, rhs: NaiveDateTime) -> TimeDelta {
        self.signed_duration_since(rhs)
    }
}

impl Add<Days> for NaiveDateTime {
    type Output = NaiveDateTime;

    fn add(self, days: Days) -> Self::Output {
        self.checked_add_days(days).unwrap()
    }
}

impl Sub<Days> for NaiveDateTime {
    type Output = NaiveDateTime;

    fn sub(self, days: Days) -> Self::Output {
        self.checked_sub_days(days).unwrap()
    }
}

/// The `Debug` output of the naive date and time `dt` is the same as
/// [`dt.format("%Y-%m-%dT%H:%M:%S%.f")`](crate::format::strftime).
///
/// The string printed can be readily parsed via the `parse` method on `str`.
///
/// It should be noted that, for leap seconds not on the minute boundary,
/// it may print a representation not distinguishable from non-leap seconds.
/// This doesn't matter in practice, since such leap seconds never happened.
/// (By the time of the first leap second on 1972-06-30,
/// every time zone offset around the world has standardized to the 5-minute alignment.)
///
/// # Example
///
/// ```
/// use chrono::NaiveDate;
///
/// let dt = NaiveDate::from_ymd(2016, 11, 15)?.and_hms(7, 39, 24)?;
/// assert_eq!(format!("{:?}", dt), "2016-11-15T07:39:24");
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds may also be used.
///
/// ```
/// # use chrono::NaiveDate;
/// let dt = NaiveDate::from_ymd(2015, 6, 30)?.and_hms_milli(23, 59, 59, 1_500)?;
/// assert_eq!(format!("{:?}", dt), "2015-06-30T23:59:60.500");
/// # Ok::<_, chrono::Error>(())
/// ```
impl fmt::Debug for NaiveDateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.date.fmt(f)?;
        f.write_char('T')?;
        self.time.fmt(f)
    }
}

/// The `Display` output of the naive date and time `dt` is the same as
/// [`dt.format("%Y-%m-%d %H:%M:%S%.f")`](crate::format::strftime).
///
/// It should be noted that, for leap seconds not on the minute boundary,
/// it may print a representation not distinguishable from non-leap seconds.
/// This doesn't matter in practice, since such leap seconds never happened.
/// (By the time of the first leap second on 1972-06-30,
/// every time zone offset around the world has standardized to the 5-minute alignment.)
///
/// # Example
///
/// ```
/// use chrono::NaiveDate;
///
/// let dt = NaiveDate::from_ymd(2016, 11, 15)?.and_hms(7, 39, 24)?;
/// assert_eq!(format!("{}", dt), "2016-11-15 07:39:24");
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds may also be used.
///
/// ```
/// # use chrono::NaiveDate;
/// let dt = NaiveDate::from_ymd(2015, 6, 30)?.and_hms_milli(23, 59, 59, 1_500)?;
/// assert_eq!(format!("{}", dt), "2015-06-30 23:59:60.500");
/// # Ok::<_, chrono::Error>(())
/// ```
impl fmt::Display for NaiveDateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.date.fmt(f)?;
        f.write_char(' ')?;
        self.time.fmt(f)
    }
}

/// Parsing a `str` into a `NaiveDateTime` uses the same format,
/// [`%Y-%m-%dT%H:%M:%S%.f`](crate::format::strftime), as in `Debug`.
///
/// # Example
///
/// ```
/// use chrono::{NaiveDateTime, NaiveDate};
///
/// let dt = NaiveDate::from_ymd(2015, 9, 18)?.and_hms(23, 56, 4)?;
/// assert_eq!("2015-09-18T23:56:04".parse::<NaiveDateTime>(), Ok(dt));
///
/// let dt = NaiveDate::from_ymd(12345, 6, 7)?.and_hms_milli(7, 59, 59, 1_500)?; // leap second
/// assert_eq!("+12345-6-7T7:59:60.5".parse::<NaiveDateTime>(), Ok(dt));
///
/// assert!("foo".parse::<NaiveDateTime>().is_err());
/// # Ok::<_, chrono::Error>(())
/// ```
impl str::FromStr for NaiveDateTime {
    type Err = Error;

    fn from_str(s: &str) -> Result<NaiveDateTime, Error> {
        const ITEMS: &[Item<'static>] = &[
            Item::Numeric(Numeric::Year, Pad::Zero),
            Item::Space(""),
            Item::Literal("-"),
            Item::Numeric(Numeric::Month, Pad::Zero),
            Item::Space(""),
            Item::Literal("-"),
            Item::Numeric(Numeric::Day, Pad::Zero),
            Item::Space(""),
            Item::Literal("T"), // XXX shouldn't this be case-insensitive?
            Item::Numeric(Numeric::Hour, Pad::Zero),
            Item::Space(""),
            Item::Literal(":"),
            Item::Numeric(Numeric::Minute, Pad::Zero),
            Item::Space(""),
            Item::Literal(":"),
            Item::Numeric(Numeric::Second, Pad::Zero),
            Item::Fixed(Fixed::Nanosecond),
            Item::Space(""),
        ];

        let mut parsed = Parsed::new();
        parse(&mut parsed, s, ITEMS.iter())?;
        parsed.to_naive_datetime_with_offset(0)
    }
}

/// The default value for a NaiveDateTime is one with epoch 0
/// that is, 1st of January 1970 at 00:00:00.
///
/// # Example
///
/// ```rust
/// use chrono::NaiveDateTime;
///
/// let default_date = NaiveDateTime::default();
/// assert_eq!(default_date, NaiveDateTime::from_timestamp(0, 0)?);
/// # Ok::<_, chrono::Error>(())
/// ```
impl Default for NaiveDateTime {
    fn default() -> Self {
        NaiveDateTime::from_timestamp(0, 0).unwrap()
    }
}

#[cfg(all(test, feature = "serde"))]
fn test_encodable_json<F, E>(to_string: F)
where
    F: Fn(&NaiveDateTime) -> Result<String, E>,
    E: ::std::fmt::Debug,
{
    assert_eq!(
        to_string(&NaiveDate::from_ymd(2016, 7, 8).unwrap().and_hms_milli(9, 10, 48, 90).unwrap())
            .ok(),
        Some(r#""2016-07-08T09:10:48.090""#.into())
    );
    assert_eq!(
        to_string(&NaiveDate::from_ymd(2014, 7, 24).unwrap().and_hms(12, 34, 6).unwrap()).ok(),
        Some(r#""2014-07-24T12:34:06""#.into())
    );
    assert_eq!(
        to_string(&NaiveDate::from_ymd(0, 1, 1).unwrap().and_hms_milli(0, 0, 59, 1_000).unwrap())
            .ok(),
        Some(r#""0000-01-01T00:00:60""#.into())
    );
    assert_eq!(
        to_string(&NaiveDate::from_ymd(-1, 12, 31).unwrap().and_hms_nano(23, 59, 59, 7).unwrap())
            .ok(),
        Some(r#""-0001-12-31T23:59:59.000000007""#.into())
    );
    assert_eq!(
        to_string(&NaiveDate::MIN.and_hms(0, 0, 0).unwrap()).ok(),
        Some(r#""-262144-01-01T00:00:00""#.into())
    );
    assert_eq!(
        to_string(&NaiveDate::MAX.and_hms_nano(23, 59, 59, 1_999_999_999).unwrap()).ok(),
        Some(r#""+262143-12-31T23:59:60.999999999""#.into())
    );
}

#[cfg(all(test, feature = "serde"))]
fn test_decodable_json<F, E>(from_str: F)
where
    F: Fn(&str) -> Result<NaiveDateTime, E>,
    E: ::std::fmt::Debug,
{
    assert_eq!(
        from_str(r#""2016-07-08T09:10:48.090""#).unwrap(),
        NaiveDate::from_ymd(2016, 7, 8).unwrap().and_hms_milli(9, 10, 48, 90).unwrap()
    );
    assert_eq!(
        from_str(r#""2016-7-8T9:10:48.09""#).unwrap(),
        NaiveDate::from_ymd(2016, 7, 8).unwrap().and_hms_milli(9, 10, 48, 90).unwrap()
    );
    assert_eq!(
        from_str(r#""2014-07-24T12:34:06""#).unwrap(),
        NaiveDate::from_ymd(2014, 7, 24).unwrap().and_hms(12, 34, 6).unwrap()
    );
    assert_eq!(
        from_str(r#""0000-01-01T00:00:60""#).unwrap(),
        NaiveDate::from_ymd(0, 1, 1).unwrap().and_hms_milli(0, 0, 59, 1_000).unwrap()
    );
    assert_eq!(
        from_str(r#""0-1-1T0:0:60""#).unwrap(),
        NaiveDate::from_ymd(0, 1, 1).unwrap().and_hms_milli(0, 0, 59, 1_000).unwrap()
    );
    assert_eq!(
        from_str(r#""-0001-12-31T23:59:59.000000007""#).unwrap(),
        NaiveDate::from_ymd(-1, 12, 31).unwrap().and_hms_nano(23, 59, 59, 7).unwrap()
    );
    assert_eq!(
        from_str(r#""-262144-01-01T00:00:00""#).unwrap(),
        NaiveDate::MIN.and_hms(0, 0, 0).unwrap()
    );
    assert_eq!(
        from_str(r#""+262143-12-31T23:59:60.999999999""#).unwrap(),
        NaiveDate::MAX.and_hms_nano(23, 59, 59, 1_999_999_999).unwrap()
    );
    assert_eq!(
        from_str(r#""+262143-12-31T23:59:60.9999999999997""#).unwrap(), // excess digits are ignored
        NaiveDate::MAX.and_hms_nano(23, 59, 59, 1_999_999_999).unwrap()
    );

    // bad formats
    assert!(from_str(r#""""#).is_err());
    assert!(from_str(r#""2016-07-08""#).is_err());
    assert!(from_str(r#""09:10:48.090""#).is_err());
    assert!(from_str(r#""20160708T091048.090""#).is_err());
    assert!(from_str(r#""2000-00-00T00:00:00""#).is_err());
    assert!(from_str(r#""2000-02-30T00:00:00""#).is_err());
    assert!(from_str(r#""2001-02-29T00:00:00""#).is_err());
    assert!(from_str(r#""2002-02-28T24:00:00""#).is_err());
    assert!(from_str(r#""2002-02-28T23:60:00""#).is_err());
    assert!(from_str(r#""2002-02-28T23:59:61""#).is_err());
    assert!(from_str(r#""2016-07-08T09:10:48,090""#).is_err());
    assert!(from_str(r#""2016-07-08 09:10:48.090""#).is_err());
    assert!(from_str(r#""2016-007-08T09:10:48.090""#).is_err());
    assert!(from_str(r#""yyyy-mm-ddThh:mm:ss.fffffffff""#).is_err());
    assert!(from_str(r#"20160708000000"#).is_err());
    assert!(from_str(r#"{}"#).is_err());
    // pre-0.3.0 rustc-serialize format is now invalid
    assert!(from_str(r#"{"date":{"ymdf":20},"time":{"secs":0,"frac":0}}"#).is_err());
    assert!(from_str(r#"null"#).is_err());
}
