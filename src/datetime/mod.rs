// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! ISO 8601 date and time with time zone.

#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::string::String;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::Write;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use core::time::Duration;
use core::{fmt, hash, str};
#[cfg(feature = "std")]
use std::time::{SystemTime, UNIX_EPOCH};

use crate::duration::Duration as OldDuration;
#[cfg(feature = "unstable-locales")]
use crate::format::Locale;
use crate::format::{
    parse, parse_and_remainder, parse_rfc3339, Fixed, Item, ParseError, ParseResult, Parsed,
    StrftimeItems, TOO_LONG,
};
#[cfg(any(feature = "alloc", feature = "std"))]
use crate::format::{write_rfc3339, DelayedFormat};
use crate::naive::{Days, IsoWeek, NaiveDate, NaiveDateTime, NaiveTime};
#[cfg(feature = "clock")]
use crate::offset::Local;
use crate::offset::{FixedOffset, Offset, TimeZone, Utc};
#[allow(deprecated)]
use crate::Date;
use crate::{Datelike, Months, Timelike, Weekday};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

#[cfg(feature = "rustc-serialize")]
pub(super) mod rustc_serialize;

/// documented at re-export site
#[cfg(feature = "serde")]
pub(super) mod serde;

#[cfg(test)]
mod tests;

/// Specific formatting options for seconds. This may be extended in the
/// future, so exhaustive matching in external code is not recommended.
///
/// See the `TimeZone::to_rfc3339_opts` function for usage.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
#[allow(clippy::manual_non_exhaustive)]
pub enum SecondsFormat {
    /// Format whole seconds only, with no decimal point nor subseconds.
    Secs,

    /// Use fixed 3 subsecond digits. This corresponds to
    /// [Fixed::Nanosecond3](format/enum.Fixed.html#variant.Nanosecond3).
    Millis,

    /// Use fixed 6 subsecond digits. This corresponds to
    /// [Fixed::Nanosecond6](format/enum.Fixed.html#variant.Nanosecond6).
    Micros,

    /// Use fixed 9 subsecond digits. This corresponds to
    /// [Fixed::Nanosecond9](format/enum.Fixed.html#variant.Nanosecond9).
    Nanos,

    /// Automatically select one of `Secs`, `Millis`, `Micros`, or `Nanos` to
    /// display all available non-zero sub-second digits.  This corresponds to
    /// [Fixed::Nanosecond](format/enum.Fixed.html#variant.Nanosecond).
    AutoSi,

    // Do not match against this.
    #[doc(hidden)]
    __NonExhaustive,
}

/// ISO 8601 combined date and time with time zone.
///
/// There are some constructors implemented here (the `from_*` methods), but
/// the general-purpose constructors are all via the methods on the
/// [`TimeZone`](./offset/trait.TimeZone.html) implementations.
#[derive(Clone)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct DateTime<Tz: TimeZone> {
    datetime: NaiveDateTime,
    offset: Tz::Offset,
}

/// The minimum possible `DateTime<Utc>`.
#[deprecated(since = "0.4.20", note = "Use DateTime::MIN_UTC instead")]
pub const MIN_DATETIME: DateTime<Utc> = DateTime::<Utc>::MIN_UTC;
/// The maximum possible `DateTime<Utc>`.
#[deprecated(since = "0.4.20", note = "Use DateTime::MAX_UTC instead")]
pub const MAX_DATETIME: DateTime<Utc> = DateTime::<Utc>::MAX_UTC;

impl<Tz: TimeZone> DateTime<Tz> {
    /// Makes a new `DateTime` from its components: a `NaiveDateTime` in UTC and an `Offset`.
    ///
    /// This is a low-level method, intended for use cases such as deserializing a `DateTime` or
    /// passing it through FFI.
    ///
    /// For regular use you will probably want to use a method such as
    /// [`TimeZone::from_local_datetime`] or [`NaiveDateTime::and_local_timezone`] instead.
    ///
    /// # Example
    ///
    #[cfg_attr(not(feature = "clock"), doc = "```ignore")]
    #[cfg_attr(feature = "clock", doc = "```rust")]
    /// use chrono::{Local, DateTime};
    ///
    /// let dt = Local::now();
    /// // Get components
    /// let naive_utc = dt.naive_utc();
    /// let offset = dt.offset().clone();
    /// // Serialize, pass through FFI... and recreate the `DateTime`:
    /// let dt_new = DateTime::<Local>::from_naive_utc_and_offset(naive_utc, offset);
    /// assert_eq!(dt, dt_new);
    /// ```
    #[inline]
    #[must_use]
    pub fn from_naive_utc_and_offset(datetime: NaiveDateTime, offset: Tz::Offset) -> DateTime<Tz> {
        DateTime { datetime, offset }
    }

    /// Makes a new `DateTime` from its components: a `NaiveDateTime` in UTC and an `Offset`.
    #[inline]
    #[must_use]
    #[deprecated(
        since = "0.4.27",
        note = "Use TimeZone::from_utc_datetime() or DateTime::from_naive_utc_and_offset instead"
    )]
    pub fn from_utc(datetime: NaiveDateTime, offset: Tz::Offset) -> DateTime<Tz> {
        DateTime { datetime, offset }
    }

    /// Makes a new `DateTime` from a `NaiveDateTime` in *local* time and an `Offset`.
    ///
    /// # Panics
    ///
    /// Panics if the local datetime can't be converted to UTC because it would be out of range.
    ///
    /// This can happen if `datetime` is near the end of the representable range of `NaiveDateTime`,
    /// and the offset from UTC pushes it beyond that.
    #[inline]
    #[must_use]
    #[deprecated(
        since = "0.4.27",
        note = "Use TimeZone::from_local_datetime() or NaiveDateTime::and_local_timezone instead"
    )]
    pub fn from_local(datetime: NaiveDateTime, offset: Tz::Offset) -> DateTime<Tz> {
        let datetime_utc = datetime - offset.fix();

        DateTime { datetime: datetime_utc, offset }
    }

    /// Retrieves the date component with an associated timezone.
    ///
    /// Unless you are immediately planning on turning this into a `DateTime`
    /// with the same timezone you should use the [`date_naive`](DateTime::date_naive) method.
    ///
    /// [`NaiveDate`] is a more well-defined type, and has more traits implemented on it,
    /// so should be preferred to [`Date`] any time you truly want to operate on dates.
    ///
    /// # Panics
    ///
    /// [`DateTime`] internally stores the date and time in UTC with a [`NaiveDateTime`]. This
    /// method will panic if the offset from UTC would push the local date outside of the
    /// representable range of a [`Date`].
    #[inline]
    #[deprecated(since = "0.4.23", note = "Use `date_naive()` instead")]
    #[allow(deprecated)]
    #[must_use]
    pub fn date(&self) -> Date<Tz> {
        Date::from_utc(self.naive_local().date(), self.offset.clone())
    }

    /// Retrieves the date component.
    ///
    /// # Panics
    ///
    /// [`DateTime`] internally stores the date and time in UTC with a [`NaiveDateTime`]. This
    /// method will panic if the offset from UTC would push the local date outside of the
    /// representable range of a [`NaiveDate`].
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::prelude::*;
    ///
    /// let date: DateTime<Utc> = Utc.with_ymd_and_hms(2020, 1, 1, 0, 0, 0).unwrap();
    /// let other: DateTime<FixedOffset> = FixedOffset::east_opt(23).unwrap().with_ymd_and_hms(2020, 1, 1, 0, 0, 0).unwrap();
    /// assert_eq!(date.date_naive(), other.date_naive());
    /// ```
    #[inline]
    #[must_use]
    pub fn date_naive(&self) -> NaiveDate {
        let local = self.naive_local();
        NaiveDate::from_ymd_opt(local.year(), local.month(), local.day()).unwrap()
    }

    /// Retrieves the time component.
    #[inline]
    #[must_use]
    pub fn time(&self) -> NaiveTime {
        self.datetime.time() + self.offset.fix()
    }

    /// Returns the number of non-leap seconds since January 1, 1970 0:00:00 UTC
    /// (aka "UNIX timestamp").
    ///
    /// The reverse operation of creating a [`DateTime`] from a timestamp can be performed
    /// using [`from_timestamp`](DateTime::from_timestamp) or [`TimeZone::timestamp_opt`].
    ///
    /// ```
    /// use chrono::{DateTime, TimeZone, Utc};
    ///
    /// let dt: DateTime<Utc> = Utc.with_ymd_and_hms(2015, 5, 15, 0, 0, 0).unwrap();
    /// assert_eq!(dt.timestamp(), 1431648000);
    ///
    /// assert_eq!(DateTime::from_timestamp(dt.timestamp(), dt.timestamp_subsec_nanos()).unwrap(), dt);
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp(&self) -> i64 {
        self.datetime.timestamp()
    }

    /// Returns the number of non-leap-milliseconds since January 1, 1970 UTC.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Utc, NaiveDate};
    ///
    /// let dt = NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_milli_opt(0, 0, 1, 444).unwrap().and_local_timezone(Utc).unwrap();
    /// assert_eq!(dt.timestamp_millis(), 1_444);
    ///
    /// let dt = NaiveDate::from_ymd_opt(2001, 9, 9).unwrap().and_hms_milli_opt(1, 46, 40, 555).unwrap().and_local_timezone(Utc).unwrap();
    /// assert_eq!(dt.timestamp_millis(), 1_000_000_000_555);
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp_millis(&self) -> i64 {
        self.datetime.timestamp_millis()
    }

    /// Returns the number of non-leap-microseconds since January 1, 1970 UTC.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Utc, NaiveDate};
    ///
    /// let dt = NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_micro_opt(0, 0, 1, 444).unwrap().and_local_timezone(Utc).unwrap();
    /// assert_eq!(dt.timestamp_micros(), 1_000_444);
    ///
    /// let dt = NaiveDate::from_ymd_opt(2001, 9, 9).unwrap().and_hms_micro_opt(1, 46, 40, 555).unwrap().and_local_timezone(Utc).unwrap();
    /// assert_eq!(dt.timestamp_micros(), 1_000_000_000_000_555);
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp_micros(&self) -> i64 {
        self.datetime.timestamp_micros()
    }

    /// Returns the number of non-leap-nanoseconds since January 1, 1970 UTC.
    ///
    /// # Panics
    ///
    /// An `i64` with nanosecond precision can span a range of ~584 years. This function panics on
    /// an out of range `DateTime`.
    ///
    /// The dates that can be represented as nanoseconds are between 1677-09-21T00:12:44.0 and
    /// 2262-04-11T23:47:16.854775804.
    #[deprecated(since = "0.4.31", note = "use `timestamp_nanos_opt()` instead")]
    #[inline]
    #[must_use]
    pub fn timestamp_nanos(&self) -> i64 {
        self.timestamp_nanos_opt()
            .expect("value can not be represented in a timestamp with nanosecond precision.")
    }

    /// Returns the number of non-leap-nanoseconds since January 1, 1970 UTC.
    ///
    /// # Panics
    ///
    /// An `i64` with nanosecond precision can span a range of ~584 years. This function panics on
    /// an out of range `DateTime`.
    ///
    /// The dates that can be represented as nanoseconds are between 1677-09-21T00:12:44.0 and
    /// 2262-04-11T23:47:16.854775804.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Utc, NaiveDate};
    ///
    /// let dt = NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_nano_opt(0, 0, 1, 444).unwrap().and_local_timezone(Utc).unwrap();
    /// assert_eq!(dt.timestamp_nanos_opt(), Some(1_000_000_444));
    ///
    /// let dt = NaiveDate::from_ymd_opt(2001, 9, 9).unwrap().and_hms_nano_opt(1, 46, 40, 555).unwrap().and_local_timezone(Utc).unwrap();
    /// assert_eq!(dt.timestamp_nanos_opt(), Some(1_000_000_000_000_000_555));
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp_nanos_opt(&self) -> Option<i64> {
        self.datetime.timestamp_nanos_opt()
    }

    /// Returns the number of milliseconds since the last second boundary.
    ///
    /// In event of a leap second this may exceed 999.
    #[inline]
    #[must_use]
    pub fn timestamp_subsec_millis(&self) -> u32 {
        self.datetime.timestamp_subsec_millis()
    }

    /// Returns the number of microseconds since the last second boundary.
    ///
    /// In event of a leap second this may exceed 999,999.
    #[inline]
    #[must_use]
    pub fn timestamp_subsec_micros(&self) -> u32 {
        self.datetime.timestamp_subsec_micros()
    }

    /// Returns the number of nanoseconds since the last second boundary
    ///
    /// In event of a leap second this may exceed 999,999,999.
    #[inline]
    #[must_use]
    pub fn timestamp_subsec_nanos(&self) -> u32 {
        self.datetime.timestamp_subsec_nanos()
    }

    /// Retrieves an associated offset from UTC.
    #[inline]
    #[must_use]
    pub fn offset(&self) -> &Tz::Offset {
        &self.offset
    }

    /// Retrieves an associated time zone.
    #[inline]
    #[must_use]
    pub fn timezone(&self) -> Tz {
        TimeZone::from_offset(&self.offset)
    }

    /// Changes the associated time zone.
    /// The returned `DateTime` references the same instant of time from the perspective of the
    /// provided time zone.
    #[inline]
    #[must_use]
    pub fn with_timezone<Tz2: TimeZone>(&self, tz: &Tz2) -> DateTime<Tz2> {
        tz.from_utc_datetime(&self.datetime)
    }

    /// Fix the offset from UTC to its current value, dropping the associated timezone information.
    /// This it useful for converting a generic `DateTime<Tz: Timezone>` to `DateTime<FixedOffset>`.
    #[inline]
    #[must_use]
    pub fn fixed_offset(&self) -> DateTime<FixedOffset> {
        self.with_timezone(&self.offset().fix())
    }

    /// Adds given `Duration` to the current date and time.
    ///
    /// # Errors
    ///
    /// Returns `None` if the resulting date would be out of range.
    #[inline]
    #[must_use]
    pub fn checked_add_signed(self, rhs: OldDuration) -> Option<DateTime<Tz>> {
        let datetime = self.datetime.checked_add_signed(rhs)?;
        let tz = self.timezone();
        Some(tz.from_utc_datetime(&datetime))
    }

    /// Adds given `Months` to the current date and time.
    ///
    /// Uses the last day of the month if the day does not exist in the resulting month.
    ///
    /// See [`NaiveDate::checked_add_months`] for more details on behavior.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date would be out of range.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[must_use]
    pub fn checked_add_months(self, rhs: Months) -> Option<DateTime<Tz>> {
        self.naive_local()
            .checked_add_months(rhs)?
            .and_local_timezone(Tz::from_offset(&self.offset))
            .single()
    }

    /// Subtracts given `Duration` from the current date and time.
    ///
    /// # Errors
    ///
    /// Returns `None` if the resulting date would be out of range.
    #[inline]
    #[must_use]
    pub fn checked_sub_signed(self, rhs: OldDuration) -> Option<DateTime<Tz>> {
        let datetime = self.datetime.checked_sub_signed(rhs)?;
        let tz = self.timezone();
        Some(tz.from_utc_datetime(&datetime))
    }

    /// Subtracts given `Months` from the current date and time.
    ///
    /// Uses the last day of the month if the day does not exist in the resulting month.
    ///
    /// See [`NaiveDate::checked_sub_months`] for more details on behavior.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date would be out of range.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[must_use]
    pub fn checked_sub_months(self, rhs: Months) -> Option<DateTime<Tz>> {
        self.naive_local()
            .checked_sub_months(rhs)?
            .and_local_timezone(Tz::from_offset(&self.offset))
            .single()
    }

    /// Add a duration in [`Days`] to the date part of the `DateTime`.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date would be out of range.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[must_use]
    pub fn checked_add_days(self, days: Days) -> Option<Self> {
        self.naive_local()
            .checked_add_days(days)?
            .and_local_timezone(TimeZone::from_offset(&self.offset))
            .single()
    }

    /// Subtract a duration in [`Days`] from the date part of the `DateTime`.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date would be out of range.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[must_use]
    pub fn checked_sub_days(self, days: Days) -> Option<Self> {
        self.naive_local()
            .checked_sub_days(days)?
            .and_local_timezone(TimeZone::from_offset(&self.offset))
            .single()
    }

    /// Subtracts another `DateTime` from the current date and time.
    /// This does not overflow or underflow at all.
    #[inline]
    #[must_use]
    pub fn signed_duration_since<Tz2: TimeZone>(
        self,
        rhs: impl Borrow<DateTime<Tz2>>,
    ) -> OldDuration {
        self.datetime.signed_duration_since(rhs.borrow().datetime)
    }

    /// Returns a view to the naive UTC datetime.
    #[inline]
    #[must_use]
    pub fn naive_utc(&self) -> NaiveDateTime {
        self.datetime
    }

    /// Returns a view to the naive local datetime.
    ///
    /// # Panics
    ///
    /// [`DateTime`] internally stores the date and time in UTC with a [`NaiveDateTime`]. This
    /// method will panic if the offset from UTC would push the local datetime outside of the
    /// representable range of a [`NaiveDateTime`].
    #[inline]
    #[must_use]
    pub fn naive_local(&self) -> NaiveDateTime {
        self.datetime + self.offset.fix()
    }

    /// Retrieve the elapsed years from now to the given [`DateTime`].
    ///
    /// # Errors
    ///
    /// Returns `None` if `base < self`.
    #[must_use]
    pub fn years_since(&self, base: Self) -> Option<u32> {
        let mut years = self.year() - base.year();
        let earlier_time =
            (self.month(), self.day(), self.time()) < (base.month(), base.day(), base.time());

        years -= match earlier_time {
            true => 1,
            false => 0,
        };

        match years >= 0 {
            true => Some(years as u32),
            false => None,
        }
    }

    /// Returns an RFC 2822 date and time string such as `Tue, 1 Jul 2003 10:52:37 +0200`.
    ///
    /// # Panics
    ///
    /// Panics if the date can not be represented in this format: the year may not be negative and
    /// can not have more than 4 digits.
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[must_use]
    pub fn to_rfc2822(&self) -> String {
        let mut result = String::with_capacity(32);
        crate::format::write_rfc2822(&mut result, self.naive_local(), self.offset.fix())
            .expect("writing rfc2822 datetime to string should never fail");
        result
    }

    /// Returns an RFC 3339 and ISO 8601 date and time string such as `1996-12-19T16:39:57-08:00`.
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[must_use]
    pub fn to_rfc3339(&self) -> String {
        // For some reason a string with a capacity less than 32 is ca 20% slower when benchmarking.
        let mut result = String::with_capacity(32);
        let naive = self.naive_local();
        let offset = self.offset.fix();
        write_rfc3339(&mut result, naive, offset, SecondsFormat::AutoSi, false)
            .expect("writing rfc3339 datetime to string should never fail");
        result
    }

    /// Return an RFC 3339 and ISO 8601 date and time string with subseconds
    /// formatted as per `SecondsFormat`.
    ///
    /// If `use_z` is true and the timezone is UTC (offset 0), uses `Z` as
    /// per [`Fixed::TimezoneOffsetColonZ`]. If `use_z` is false, uses
    /// [`Fixed::TimezoneOffsetColon`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use chrono::{FixedOffset, SecondsFormat, TimeZone, Utc, NaiveDate};
    /// let dt = NaiveDate::from_ymd_opt(2018, 1, 26).unwrap().and_hms_micro_opt(18, 30, 9, 453_829).unwrap().and_local_timezone(Utc).unwrap();
    /// assert_eq!(dt.to_rfc3339_opts(SecondsFormat::Millis, false),
    ///            "2018-01-26T18:30:09.453+00:00");
    /// assert_eq!(dt.to_rfc3339_opts(SecondsFormat::Millis, true),
    ///            "2018-01-26T18:30:09.453Z");
    /// assert_eq!(dt.to_rfc3339_opts(SecondsFormat::Secs, true),
    ///            "2018-01-26T18:30:09Z");
    ///
    /// let pst = FixedOffset::east_opt(8 * 60 * 60).unwrap();
    /// let dt = pst.from_local_datetime(&NaiveDate::from_ymd_opt(2018, 1, 26).unwrap().and_hms_micro_opt(10, 30, 9, 453_829).unwrap()).unwrap();
    /// assert_eq!(dt.to_rfc3339_opts(SecondsFormat::Secs, true),
    ///            "2018-01-26T10:30:09+08:00");
    /// ```
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[must_use]
    pub fn to_rfc3339_opts(&self, secform: SecondsFormat, use_z: bool) -> String {
        let mut result = String::with_capacity(38);
        write_rfc3339(&mut result, self.naive_local(), self.offset.fix(), secform, use_z)
            .expect("writing rfc3339 datetime to string should never fail");
        result
    }

    /// The minimum possible `DateTime<Utc>`.
    pub const MIN_UTC: DateTime<Utc> = DateTime { datetime: NaiveDateTime::MIN, offset: Utc };
    /// The maximum possible `DateTime<Utc>`.
    pub const MAX_UTC: DateTime<Utc> = DateTime { datetime: NaiveDateTime::MAX, offset: Utc };
}

impl DateTime<Utc> {
    /// Makes a new [`DateTime<Utc>`] from the number of non-leap seconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp")
    /// and the number of nanoseconds since the last whole non-leap second.
    ///
    /// This is guaranteed to round-trip with regard to [`timestamp`](DateTime::timestamp) and
    /// [`timestamp_subsec_nanos`](DateTime::timestamp_subsec_nanos).
    ///
    /// If you need to create a `DateTime` with a [`TimeZone`] different from [`Utc`], use
    /// [`TimeZone::timestamp_opt`] or [`DateTime::with_timezone`].
    ///
    /// The nanosecond part can exceed 1,000,000,000 in order to represent a
    /// [leap second](NaiveTime#leap-second-handling), but only when `secs % 60 == 59`.
    /// (The true "UNIX timestamp" cannot represent a leap second unambiguously.)
    ///
    /// # Errors
    ///
    /// Returns `None` on out-of-range number of seconds and/or
    /// invalid nanosecond, otherwise returns `Some(DateTime {...})`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{DateTime, Utc};
    ///
    /// let dt: DateTime<Utc> = DateTime::<Utc>::from_timestamp(1431648000, 0).expect("invalid timestamp");
    ///
    /// assert_eq!(dt.to_string(), "2015-05-15 00:00:00 UTC");
    /// assert_eq!(DateTime::from_timestamp(dt.timestamp(), dt.timestamp_subsec_nanos()).unwrap(), dt);
    /// ```
    #[inline]
    #[must_use]
    pub fn from_timestamp(secs: i64, nsecs: u32) -> Option<Self> {
        NaiveDateTime::from_timestamp_opt(secs, nsecs).as_ref().map(NaiveDateTime::and_utc)
    }

    /// The Unix Epoch, 1970-01-01 00:00:00 UTC.
    pub const UNIX_EPOCH: Self = Self { datetime: NaiveDateTime::UNIX_EPOCH, offset: Utc };
}

impl Default for DateTime<Utc> {
    fn default() -> Self {
        Utc.from_utc_datetime(&NaiveDateTime::default())
    }
}

#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl Default for DateTime<Local> {
    fn default() -> Self {
        Local.from_utc_datetime(&NaiveDateTime::default())
    }
}

impl Default for DateTime<FixedOffset> {
    fn default() -> Self {
        FixedOffset::west_opt(0).unwrap().from_utc_datetime(&NaiveDateTime::default())
    }
}

/// Convert a `DateTime<Utc>` instance into a `DateTime<FixedOffset>` instance.
impl From<DateTime<Utc>> for DateTime<FixedOffset> {
    /// Convert this `DateTime<Utc>` instance into a `DateTime<FixedOffset>` instance.
    ///
    /// Conversion is done via [`DateTime::with_timezone`]. Note that the converted value returned by
    /// this will be created with a fixed timezone offset of 0.
    fn from(src: DateTime<Utc>) -> Self {
        src.with_timezone(&FixedOffset::east_opt(0).unwrap())
    }
}

/// Convert a `DateTime<Utc>` instance into a `DateTime<Local>` instance.
#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl From<DateTime<Utc>> for DateTime<Local> {
    /// Convert this `DateTime<Utc>` instance into a `DateTime<Local>` instance.
    ///
    /// Conversion is performed via [`DateTime::with_timezone`], accounting for the difference in timezones.
    fn from(src: DateTime<Utc>) -> Self {
        src.with_timezone(&Local)
    }
}

/// Convert a `DateTime<FixedOffset>` instance into a `DateTime<Utc>` instance.
impl From<DateTime<FixedOffset>> for DateTime<Utc> {
    /// Convert this `DateTime<FixedOffset>` instance into a `DateTime<Utc>` instance.
    ///
    /// Conversion is performed via [`DateTime::with_timezone`], accounting for the timezone
    /// difference.
    fn from(src: DateTime<FixedOffset>) -> Self {
        src.with_timezone(&Utc)
    }
}

/// Convert a `DateTime<FixedOffset>` instance into a `DateTime<Local>` instance.
#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl From<DateTime<FixedOffset>> for DateTime<Local> {
    /// Convert this `DateTime<FixedOffset>` instance into a `DateTime<Local>` instance.
    ///
    /// Conversion is performed via [`DateTime::with_timezone`]. Returns the equivalent value in local
    /// time.
    fn from(src: DateTime<FixedOffset>) -> Self {
        src.with_timezone(&Local)
    }
}

/// Convert a `DateTime<Local>` instance into a `DateTime<Utc>` instance.
#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl From<DateTime<Local>> for DateTime<Utc> {
    /// Convert this `DateTime<Local>` instance into a `DateTime<Utc>` instance.
    ///
    /// Conversion is performed via [`DateTime::with_timezone`], accounting for the difference in
    /// timezones.
    fn from(src: DateTime<Local>) -> Self {
        src.with_timezone(&Utc)
    }
}

/// Convert a `DateTime<Local>` instance into a `DateTime<FixedOffset>` instance.
#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl From<DateTime<Local>> for DateTime<FixedOffset> {
    /// Convert this `DateTime<Local>` instance into a `DateTime<FixedOffset>` instance.
    ///
    /// Conversion is performed via [`DateTime::with_timezone`].
    fn from(src: DateTime<Local>) -> Self {
        src.with_timezone(&src.offset().fix())
    }
}

/// Maps the local datetime to other datetime with given conversion function.
fn map_local<Tz: TimeZone, F>(dt: &DateTime<Tz>, mut f: F) -> Option<DateTime<Tz>>
where
    F: FnMut(NaiveDateTime) -> Option<NaiveDateTime>,
{
    f(dt.naive_local()).and_then(|datetime| dt.timezone().from_local_datetime(&datetime).single())
}

impl DateTime<FixedOffset> {
    /// Parses an RFC 2822 date-and-time string into a `DateTime<FixedOffset>` value.
    ///
    /// This parses valid RFC 2822 datetime strings (such as `Tue, 1 Jul 2003 10:52:37 +0200`)
    /// and returns a new [`DateTime`] instance with the parsed timezone as the [`FixedOffset`].
    ///
    /// RFC 2822 is the internet message standard that specifies the representation of times in HTTP
    /// and email headers. It is the 2001 revision of RFC 822, and is itself revised as RFC 5322 in
    /// 2008.
    ///
    /// # Support for the obsolete date format
    ///
    /// - A 2-digit year is interpreted to be a year in 1950-2049.
    /// - The standard allows comments and whitespace between many of the tokens. See [4.3] and
    ///   [Appendix A.5]
    /// - Single letter 'military' time zone names are parsed as a `-0000` offset.
    ///   They were defined with the wrong sign in RFC 822 and corrected in RFC 2822. But because
    ///   the meaning is now ambiguous, the standard says they should be be considered as `-0000`
    ///   unless there is out-of-band information confirming their meaning.
    ///   The exception is `Z`, which remains identical to `+0000`.
    ///
    /// [4.3]: https://www.rfc-editor.org/rfc/rfc2822#section-4.3
    /// [Appendix A.5]: https://www.rfc-editor.org/rfc/rfc2822#appendix-A.5
    ///
    /// # Example
    ///
    /// ```
    /// # use chrono::{DateTime, FixedOffset, TimeZone};
    /// assert_eq!(
    ///     DateTime::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 GMT").unwrap(),
    ///     FixedOffset::east_opt(0).unwrap().with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap()
    /// );
    /// ```
    pub fn parse_from_rfc2822(s: &str) -> ParseResult<DateTime<FixedOffset>> {
        const ITEMS: &[Item<'static>] = &[Item::Fixed(Fixed::RFC2822)];
        let mut parsed = Parsed::new();
        parse(&mut parsed, s, ITEMS.iter())?;
        parsed.to_datetime()
    }

    /// Parses an RFC 3339 date-and-time string into a `DateTime<FixedOffset>` value.
    ///
    /// Parses all valid RFC 3339 values (as well as the subset of valid ISO 8601 values that are
    /// also valid RFC 3339 date-and-time values) and returns a new [`DateTime`] with a
    /// [`FixedOffset`] corresponding to the parsed timezone. While RFC 3339 values come in a wide
    /// variety of shapes and sizes, `1996-12-19T16:39:57-08:00` is an example of the most commonly
    /// encountered variety of RFC 3339 formats.
    ///
    /// Why isn't this named `parse_from_iso8601`? That's because ISO 8601 allows representing
    /// values in a wide range of formats, only some of which represent actual date-and-time
    /// instances (rather than periods, ranges, dates, or times). Some valid ISO 8601 values are
    /// also simultaneously valid RFC 3339 values, but not all RFC 3339 values are valid ISO 8601
    /// values (or the other way around).
    pub fn parse_from_rfc3339(s: &str) -> ParseResult<DateTime<FixedOffset>> {
        let mut parsed = Parsed::new();
        let (s, _) = parse_rfc3339(&mut parsed, s)?;
        if !s.is_empty() {
            return Err(TOO_LONG);
        }
        parsed.to_datetime()
    }

    /// Parses a string from a user-specified format into a `DateTime<FixedOffset>` value.
    ///
    /// Note that this method *requires a timezone* in the input string. See
    /// [`NaiveDateTime::parse_from_str`](./naive/struct.NaiveDateTime.html#method.parse_from_str)
    /// for a version that does not require a timezone in the to-be-parsed str. The returned
    /// [`DateTime`] value will have a [`FixedOffset`] reflecting the parsed timezone.
    ///
    /// See the [`format::strftime` module](./format/strftime/index.html) for supported format
    /// sequences.
    ///
    /// # Example
    ///
    /// ```rust
    /// use chrono::{DateTime, FixedOffset, TimeZone, NaiveDate};
    ///
    /// let dt = DateTime::parse_from_str(
    ///     "1983 Apr 13 12:09:14.274 +0000", "%Y %b %d %H:%M:%S%.3f %z");
    /// assert_eq!(dt, Ok(FixedOffset::east_opt(0).unwrap().from_local_datetime(&NaiveDate::from_ymd_opt(1983, 4, 13).unwrap().and_hms_milli_opt(12, 9, 14, 274).unwrap()).unwrap()));
    /// ```
    pub fn parse_from_str(s: &str, fmt: &str) -> ParseResult<DateTime<FixedOffset>> {
        let mut parsed = Parsed::new();
        parse(&mut parsed, s, StrftimeItems::new(fmt))?;
        parsed.to_datetime()
    }

    /// Parses a string from a user-specified format into a `DateTime<FixedOffset>` value, and a
    /// slice with the remaining portion of the string.
    ///
    /// Note that this method *requires a timezone* in the input string. See
    /// [`NaiveDateTime::parse_and_remainder`] for a version that does not
    /// require a timezone in `s`. The returned [`DateTime`] value will have a [`FixedOffset`]
    /// reflecting the parsed timezone.
    ///
    /// See the [`format::strftime` module](./format/strftime/index.html) for supported format
    /// sequences.
    ///
    /// Similar to [`parse_from_str`](#method.parse_from_str).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use chrono::{DateTime, FixedOffset, TimeZone};
    /// let (datetime, remainder) = DateTime::parse_and_remainder(
    ///     "2015-02-18 23:16:09 +0200 trailing text", "%Y-%m-%d %H:%M:%S %z").unwrap();
    /// assert_eq!(
    ///     datetime,
    ///     FixedOffset::east_opt(2*3600).unwrap().with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap()
    /// );
    /// assert_eq!(remainder, " trailing text");
    /// ```
    pub fn parse_and_remainder<'a>(
        s: &'a str,
        fmt: &str,
    ) -> ParseResult<(DateTime<FixedOffset>, &'a str)> {
        let mut parsed = Parsed::new();
        let remainder = parse_and_remainder(&mut parsed, s, StrftimeItems::new(fmt))?;
        parsed.to_datetime().map(|d| (d, remainder))
    }
}

impl<Tz: TimeZone> DateTime<Tz>
where
    Tz::Offset: fmt::Display,
{
    /// Formats the combined date and time with the specified formatting items.
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    #[must_use]
    pub fn format_with_items<'a, I, B>(&self, items: I) -> DelayedFormat<I>
    where
        I: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        let local = self.naive_local();
        DelayedFormat::new_with_offset(Some(local.date()), Some(local.time()), &self.offset, items)
    }

    /// Formats the combined date and time per the specified format string.
    ///
    /// See the [`crate::format::strftime`] module for the supported escape sequences.
    ///
    /// # Example
    /// ```rust
    /// use chrono::prelude::*;
    ///
    /// let date_time: DateTime<Utc> = Utc.with_ymd_and_hms(2017, 04, 02, 12, 50, 32).unwrap();
    /// let formatted = format!("{}", date_time.format("%d/%m/%Y %H:%M"));
    /// assert_eq!(formatted, "02/04/2017 12:50");
    /// ```
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    #[must_use]
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_with_items(StrftimeItems::new(fmt))
    }

    /// Formats the combined date and time with the specified formatting items and locale.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[inline]
    #[must_use]
    pub fn format_localized_with_items<'a, I, B>(
        &self,
        items: I,
        locale: Locale,
    ) -> DelayedFormat<I>
    where
        I: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        let local = self.naive_local();
        DelayedFormat::new_with_offset_and_locale(
            Some(local.date()),
            Some(local.time()),
            &self.offset,
            items,
            locale,
        )
    }

    /// Formats the combined date and time per the specified format string and
    /// locale.
    ///
    /// See the [`crate::format::strftime`] module on the supported escape
    /// sequences.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[inline]
    #[must_use]
    pub fn format_localized<'a>(
        &self,
        fmt: &'a str,
        locale: Locale,
    ) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_localized_with_items(StrftimeItems::new_with_locale(fmt, locale), locale)
    }
}

impl<Tz: TimeZone> Datelike for DateTime<Tz> {
    #[inline]
    fn year(&self) -> i32 {
        self.naive_local().year()
    }
    #[inline]
    fn month(&self) -> u32 {
        self.naive_local().month()
    }
    #[inline]
    fn month0(&self) -> u32 {
        self.naive_local().month0()
    }
    #[inline]
    fn day(&self) -> u32 {
        self.naive_local().day()
    }
    #[inline]
    fn day0(&self) -> u32 {
        self.naive_local().day0()
    }
    #[inline]
    fn ordinal(&self) -> u32 {
        self.naive_local().ordinal()
    }
    #[inline]
    fn ordinal0(&self) -> u32 {
        self.naive_local().ordinal0()
    }
    #[inline]
    fn weekday(&self) -> Weekday {
        self.naive_local().weekday()
    }
    #[inline]
    fn iso_week(&self) -> IsoWeek {
        self.naive_local().iso_week()
    }

    #[inline]
    /// Makes a new `DateTime` with the year number changed, while keeping the same month and day.
    ///
    /// See also the [`NaiveDate::with_year`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date does not exist.
    /// - When the `NaiveDateTime` would be out of range.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    fn with_year(&self, year: i32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_year(year))
    }

    /// Makes a new `DateTime` with the month number (starting from 1) changed.
    ///
    /// See also the [`NaiveDate::with_month`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date does not exist.
    /// - The value for `month` is invalid.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[inline]
    fn with_month(&self, month: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_month(month))
    }

    /// Makes a new `DateTime` with the month number (starting from 0) changed.
    ///
    /// See also the [`NaiveDate::with_month0`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date does not exist.
    /// - The value for `month0` is invalid.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[inline]
    fn with_month0(&self, month0: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_month0(month0))
    }

    /// Makes a new `DateTime` with the month number (starting from 0) changed.
    ///
    /// See also the [`NaiveDate::with_day`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date does not exist.
    /// - The value for `day` is invalid.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[inline]
    fn with_day(&self, day: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_day(day))
    }

    /// Makes a new `DateTime` with the month number (starting from 0) changed.
    ///
    /// See also the [`NaiveDate::with_day0`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date does not exist.
    /// - The value for `day0` is invalid.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[inline]
    fn with_day0(&self, day0: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_day0(day0))
    }

    /// Makes a new `DateTime` with the month number (starting from 0) changed.
    ///
    /// See also the [`NaiveDate::with_ordinal`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date does not exist.
    /// - The value for `ordinal` is invalid.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_ordinal(ordinal))
    }

    /// Makes a new `DateTime` with the month number (starting from 0) changed.
    ///
    /// See also the [`NaiveDate::with_ordinal0`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The resulting date does not exist.
    /// - The value for `ordinal0` is invalid.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_ordinal0(ordinal0))
    }
}

impl<Tz: TimeZone> Timelike for DateTime<Tz> {
    #[inline]
    fn hour(&self) -> u32 {
        self.naive_local().hour()
    }
    #[inline]
    fn minute(&self) -> u32 {
        self.naive_local().minute()
    }
    #[inline]
    fn second(&self) -> u32 {
        self.naive_local().second()
    }
    #[inline]
    fn nanosecond(&self) -> u32 {
        self.naive_local().nanosecond()
    }

    /// Makes a new `DateTime` with the hour number changed.
    ///
    /// See also the [`NaiveTime::with_hour`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The value for `hour` is invalid.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[inline]
    fn with_hour(&self, hour: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_hour(hour))
    }

    /// Makes a new `DateTime` with the minute number changed.
    ///
    /// See also the [`NaiveTime::with_minute`] method.
    ///
    /// # Errors
    ///
    /// - The value for `minute` is invalid.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[inline]
    fn with_minute(&self, min: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_minute(min))
    }

    /// Makes a new `DateTime` with the second number changed.
    ///
    /// As with the [`second`](#method.second) method,
    /// the input range is restricted to 0 through 59.
    ///
    /// See also the [`NaiveTime::with_second`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if:
    /// - The value for `second` is invalid.
    /// - The local time at the resulting date does not exist or is ambiguous, for example during a
    ///   daylight saving time transition.
    #[inline]
    fn with_second(&self, sec: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_second(sec))
    }

    /// Makes a new `DateTime` with nanoseconds since the whole non-leap second changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    /// As with the [`NaiveDateTime::nanosecond`] method,
    /// the input range can exceed 1,000,000,000 for leap seconds.
    ///
    /// See also the [`NaiveTime::with_nanosecond`] method.
    ///
    /// # Errors
    ///
    /// Returns `None` if `nanosecond >= 2,000,000,000`.
    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_nanosecond(nano))
    }
}

// we need them as automatic impls cannot handle associated types
impl<Tz: TimeZone> Copy for DateTime<Tz> where <Tz as TimeZone>::Offset: Copy {}
unsafe impl<Tz: TimeZone> Send for DateTime<Tz> where <Tz as TimeZone>::Offset: Send {}

impl<Tz: TimeZone, Tz2: TimeZone> PartialEq<DateTime<Tz2>> for DateTime<Tz> {
    fn eq(&self, other: &DateTime<Tz2>) -> bool {
        self.datetime == other.datetime
    }
}

impl<Tz: TimeZone> Eq for DateTime<Tz> {}

impl<Tz: TimeZone, Tz2: TimeZone> PartialOrd<DateTime<Tz2>> for DateTime<Tz> {
    /// Compare two DateTimes based on their true time, ignoring time zones
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::prelude::*;
    ///
    /// let earlier = Utc.with_ymd_and_hms(2015, 5, 15, 2, 0, 0).unwrap().with_timezone(&FixedOffset::west_opt(1 * 3600).unwrap());
    /// let later   = Utc.with_ymd_and_hms(2015, 5, 15, 3, 0, 0).unwrap().with_timezone(&FixedOffset::west_opt(5 * 3600).unwrap());
    ///
    /// assert_eq!(earlier.to_string(), "2015-05-15 01:00:00 -01:00");
    /// assert_eq!(later.to_string(), "2015-05-14 22:00:00 -05:00");
    ///
    /// assert!(later > earlier);
    /// ```
    fn partial_cmp(&self, other: &DateTime<Tz2>) -> Option<Ordering> {
        self.datetime.partial_cmp(&other.datetime)
    }
}

impl<Tz: TimeZone> Ord for DateTime<Tz> {
    fn cmp(&self, other: &DateTime<Tz>) -> Ordering {
        self.datetime.cmp(&other.datetime)
    }
}

impl<Tz: TimeZone> hash::Hash for DateTime<Tz> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.datetime.hash(state)
    }
}

impl<Tz: TimeZone> Add<OldDuration> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn add(self, rhs: OldDuration) -> DateTime<Tz> {
        self.checked_add_signed(rhs).expect("`DateTime + Duration` overflowed")
    }
}

impl<Tz: TimeZone> Add<Duration> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn add(self, rhs: Duration) -> DateTime<Tz> {
        let rhs = OldDuration::from_std(rhs)
            .expect("overflow converting from core::time::Duration to chrono::Duration");
        self.checked_add_signed(rhs).expect("`DateTime + Duration` overflowed")
    }
}

impl<Tz: TimeZone> AddAssign<OldDuration> for DateTime<Tz> {
    #[inline]
    fn add_assign(&mut self, rhs: OldDuration) {
        let datetime =
            self.datetime.checked_add_signed(rhs).expect("`DateTime + Duration` overflowed");
        let tz = self.timezone();
        *self = tz.from_utc_datetime(&datetime);
    }
}

impl<Tz: TimeZone> AddAssign<Duration> for DateTime<Tz> {
    #[inline]
    fn add_assign(&mut self, rhs: Duration) {
        let rhs = OldDuration::from_std(rhs)
            .expect("overflow converting from core::time::Duration to chrono::Duration");
        *self += rhs;
    }
}

impl<Tz: TimeZone> Add<Months> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    fn add(self, rhs: Months) -> Self::Output {
        self.checked_add_months(rhs).unwrap()
    }
}

impl<Tz: TimeZone> Sub<OldDuration> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn sub(self, rhs: OldDuration) -> DateTime<Tz> {
        self.checked_sub_signed(rhs).expect("`DateTime - Duration` overflowed")
    }
}

impl<Tz: TimeZone> Sub<Duration> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn sub(self, rhs: Duration) -> DateTime<Tz> {
        let rhs = OldDuration::from_std(rhs)
            .expect("overflow converting from core::time::Duration to chrono::Duration");
        self.checked_sub_signed(rhs).expect("`DateTime - Duration` overflowed")
    }
}

impl<Tz: TimeZone> SubAssign<OldDuration> for DateTime<Tz> {
    #[inline]
    fn sub_assign(&mut self, rhs: OldDuration) {
        let datetime =
            self.datetime.checked_sub_signed(rhs).expect("`DateTime - Duration` overflowed");
        let tz = self.timezone();
        *self = tz.from_utc_datetime(&datetime)
    }
}

impl<Tz: TimeZone> SubAssign<Duration> for DateTime<Tz> {
    #[inline]
    fn sub_assign(&mut self, rhs: Duration) {
        let rhs = OldDuration::from_std(rhs)
            .expect("overflow converting from core::time::Duration to chrono::Duration");
        *self -= rhs;
    }
}

impl<Tz: TimeZone> Sub<Months> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    fn sub(self, rhs: Months) -> Self::Output {
        self.checked_sub_months(rhs).unwrap()
    }
}

impl<Tz: TimeZone> Sub<DateTime<Tz>> for DateTime<Tz> {
    type Output = OldDuration;

    #[inline]
    fn sub(self, rhs: DateTime<Tz>) -> OldDuration {
        self.signed_duration_since(rhs)
    }
}

impl<Tz: TimeZone> Sub<&DateTime<Tz>> for DateTime<Tz> {
    type Output = OldDuration;

    #[inline]
    fn sub(self, rhs: &DateTime<Tz>) -> OldDuration {
        self.signed_duration_since(rhs)
    }
}

impl<Tz: TimeZone> Add<Days> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    fn add(self, days: Days) -> Self::Output {
        self.checked_add_days(days).unwrap()
    }
}

impl<Tz: TimeZone> Sub<Days> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    fn sub(self, days: Days) -> Self::Output {
        self.checked_sub_days(days).unwrap()
    }
}

impl<Tz: TimeZone> fmt::Debug for DateTime<Tz> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.naive_local().fmt(f)?;
        self.offset.fmt(f)
    }
}

impl<Tz: TimeZone> fmt::Display for DateTime<Tz>
where
    Tz::Offset: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.naive_local().fmt(f)?;
        f.write_char(' ')?;
        self.offset.fmt(f)
    }
}

/// Accepts a relaxed form of RFC3339.
/// A space or a 'T' are accepted as the separator between the date and time
/// parts.
///
/// All of these examples are equivalent:
/// ```
/// # use chrono::{DateTime, Utc};
/// "2012-12-12T12:12:12Z".parse::<DateTime<Utc>>()?;
/// "2012-12-12 12:12:12Z".parse::<DateTime<Utc>>()?;
/// "2012-12-12 12:12:12+0000".parse::<DateTime<Utc>>()?;
/// "2012-12-12 12:12:12+00:00".parse::<DateTime<Utc>>()?;
/// # Ok::<(), chrono::ParseError>(())
/// ```
impl str::FromStr for DateTime<Utc> {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<DateTime<Utc>> {
        s.parse::<DateTime<FixedOffset>>().map(|dt| dt.with_timezone(&Utc))
    }
}

/// Accepts a relaxed form of RFC3339.
/// A space or a 'T' are accepted as the separator between the date and time
/// parts.
///
/// All of these examples are equivalent:
/// ```
/// # use chrono::{DateTime, Local};
/// "2012-12-12T12:12:12Z".parse::<DateTime<Local>>()?;
/// "2012-12-12 12:12:12Z".parse::<DateTime<Local>>()?;
/// "2012-12-12 12:12:12+0000".parse::<DateTime<Local>>()?;
/// "2012-12-12 12:12:12+00:00".parse::<DateTime<Local>>()?;
/// # Ok::<(), chrono::ParseError>(())
/// ```
#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl str::FromStr for DateTime<Local> {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<DateTime<Local>> {
        s.parse::<DateTime<FixedOffset>>().map(|dt| dt.with_timezone(&Local))
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl From<SystemTime> for DateTime<Utc> {
    fn from(t: SystemTime) -> DateTime<Utc> {
        let (sec, nsec) = match t.duration_since(UNIX_EPOCH) {
            Ok(dur) => (dur.as_secs() as i64, dur.subsec_nanos()),
            Err(e) => {
                // unlikely but should be handled
                let dur = e.duration();
                let (sec, nsec) = (dur.as_secs() as i64, dur.subsec_nanos());
                if nsec == 0 {
                    (-sec, 0)
                } else {
                    (-sec - 1, 1_000_000_000 - nsec)
                }
            }
        };
        Utc.timestamp_opt(sec, nsec).unwrap()
    }
}

#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl From<SystemTime> for DateTime<Local> {
    fn from(t: SystemTime) -> DateTime<Local> {
        DateTime::<Utc>::from(t).with_timezone(&Local)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<Tz: TimeZone> From<DateTime<Tz>> for SystemTime {
    fn from(dt: DateTime<Tz>) -> SystemTime {
        let sec = dt.timestamp();
        let nsec = dt.timestamp_subsec_nanos();
        if sec < 0 {
            // unlikely but should be handled
            UNIX_EPOCH - Duration::new(-sec as u64, 0) + Duration::new(0, nsec)
        } else {
            UNIX_EPOCH + Duration::new(sec as u64, nsec)
        }
    }
}

#[cfg(all(
    target_arch = "wasm32",
    feature = "wasmbind",
    not(any(target_os = "emscripten", target_os = "wasi"))
))]
#[cfg_attr(
    docsrs,
    doc(cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))
)]
impl From<js_sys::Date> for DateTime<Utc> {
    fn from(date: js_sys::Date) -> DateTime<Utc> {
        DateTime::<Utc>::from(&date)
    }
}

#[cfg(all(
    target_arch = "wasm32",
    feature = "wasmbind",
    not(any(target_os = "emscripten", target_os = "wasi"))
))]
#[cfg_attr(
    docsrs,
    doc(cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))
)]
impl From<&js_sys::Date> for DateTime<Utc> {
    fn from(date: &js_sys::Date) -> DateTime<Utc> {
        Utc.timestamp_millis_opt(date.get_time() as i64).unwrap()
    }
}

#[cfg(all(
    target_arch = "wasm32",
    feature = "wasmbind",
    not(any(target_os = "emscripten", target_os = "wasi"))
))]
#[cfg_attr(
    docsrs,
    doc(cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))
)]
impl From<DateTime<Utc>> for js_sys::Date {
    /// Converts a `DateTime<Utc>` to a JS `Date`. The resulting value may be lossy,
    /// any values that have a millisecond timestamp value greater/less than ±8,640,000,000,000,000
    /// (April 20, 271821 BCE ~ September 13, 275760 CE) will become invalid dates in JS.
    fn from(date: DateTime<Utc>) -> js_sys::Date {
        let js_millis = wasm_bindgen::JsValue::from_f64(date.timestamp_millis() as f64);
        js_sys::Date::new(&js_millis)
    }
}

// Note that implementation of Arbitrary cannot be simply derived for DateTime<Tz>, due to
// the nontrivial bound <Tz as TimeZone>::Offset: Arbitrary.
#[cfg(feature = "arbitrary")]
impl<'a, Tz> arbitrary::Arbitrary<'a> for DateTime<Tz>
where
    Tz: TimeZone,
    <Tz as TimeZone>::Offset: arbitrary::Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<DateTime<Tz>> {
        let datetime = NaiveDateTime::arbitrary(u)?;
        let offset = <Tz as TimeZone>::Offset::arbitrary(u)?;
        Ok(DateTime::from_utc(datetime, offset))
    }
}

#[cfg(all(test, any(feature = "rustc-serialize", feature = "serde")))]
fn test_encodable_json<FUtc, FFixed, E>(to_string_utc: FUtc, to_string_fixed: FFixed)
where
    FUtc: Fn(&DateTime<Utc>) -> Result<String, E>,
    FFixed: Fn(&DateTime<FixedOffset>) -> Result<String, E>,
    E: ::core::fmt::Debug,
{
    assert_eq!(
        to_string_utc(&Utc.with_ymd_and_hms(2014, 7, 24, 12, 34, 6).unwrap()).ok(),
        Some(r#""2014-07-24T12:34:06Z""#.into())
    );

    assert_eq!(
        to_string_fixed(
            &FixedOffset::east_opt(3660).unwrap().with_ymd_and_hms(2014, 7, 24, 12, 34, 6).unwrap()
        )
        .ok(),
        Some(r#""2014-07-24T12:34:06+01:01""#.into())
    );
    assert_eq!(
        to_string_fixed(
            &FixedOffset::east_opt(3650).unwrap().with_ymd_and_hms(2014, 7, 24, 12, 34, 6).unwrap()
        )
        .ok(),
        // An offset with seconds is not allowed by RFC 3339, so we round it to the nearest minute.
        // In this case `+01:00:50` becomes `+01:01`
        Some(r#""2014-07-24T12:34:06+01:01""#.into())
    );
}

#[cfg(all(test, feature = "clock", any(feature = "rustc-serialize", feature = "serde")))]
fn test_decodable_json<FUtc, FFixed, FLocal, E>(
    utc_from_str: FUtc,
    fixed_from_str: FFixed,
    local_from_str: FLocal,
) where
    FUtc: Fn(&str) -> Result<DateTime<Utc>, E>,
    FFixed: Fn(&str) -> Result<DateTime<FixedOffset>, E>,
    FLocal: Fn(&str) -> Result<DateTime<Local>, E>,
    E: ::core::fmt::Debug,
{
    // should check against the offset as well (the normal DateTime comparison will ignore them)
    fn norm<Tz: TimeZone>(dt: &Option<DateTime<Tz>>) -> Option<(&DateTime<Tz>, &Tz::Offset)> {
        dt.as_ref().map(|dt| (dt, dt.offset()))
    }

    assert_eq!(
        norm(&utc_from_str(r#""2014-07-24T12:34:06Z""#).ok()),
        norm(&Some(Utc.with_ymd_and_hms(2014, 7, 24, 12, 34, 6).unwrap()))
    );
    assert_eq!(
        norm(&utc_from_str(r#""2014-07-24T13:57:06+01:23""#).ok()),
        norm(&Some(Utc.with_ymd_and_hms(2014, 7, 24, 12, 34, 6).unwrap()))
    );

    assert_eq!(
        norm(&fixed_from_str(r#""2014-07-24T12:34:06Z""#).ok()),
        norm(&Some(
            FixedOffset::east_opt(0).unwrap().with_ymd_and_hms(2014, 7, 24, 12, 34, 6).unwrap()
        ))
    );
    assert_eq!(
        norm(&fixed_from_str(r#""2014-07-24T13:57:06+01:23""#).ok()),
        norm(&Some(
            FixedOffset::east_opt(60 * 60 + 23 * 60)
                .unwrap()
                .with_ymd_and_hms(2014, 7, 24, 13, 57, 6)
                .unwrap()
        ))
    );

    // we don't know the exact local offset but we can check that
    // the conversion didn't change the instant itself
    assert_eq!(
        local_from_str(r#""2014-07-24T12:34:06Z""#).expect("local should parse"),
        Utc.with_ymd_and_hms(2014, 7, 24, 12, 34, 6).unwrap()
    );
    assert_eq!(
        local_from_str(r#""2014-07-24T13:57:06+01:23""#).expect("local should parse with offset"),
        Utc.with_ymd_and_hms(2014, 7, 24, 12, 34, 6).unwrap()
    );

    assert!(utc_from_str(r#""2014-07-32T12:34:06Z""#).is_err());
    assert!(fixed_from_str(r#""2014-07-32T12:34:06Z""#).is_err());
}

#[cfg(all(test, feature = "clock", feature = "rustc-serialize"))]
fn test_decodable_json_timestamps<FUtc, FFixed, FLocal, E>(
    utc_from_str: FUtc,
    fixed_from_str: FFixed,
    local_from_str: FLocal,
) where
    FUtc: Fn(&str) -> Result<rustc_serialize::TsSeconds<Utc>, E>,
    FFixed: Fn(&str) -> Result<rustc_serialize::TsSeconds<FixedOffset>, E>,
    FLocal: Fn(&str) -> Result<rustc_serialize::TsSeconds<Local>, E>,
    E: ::core::fmt::Debug,
{
    fn norm<Tz: TimeZone>(dt: &Option<DateTime<Tz>>) -> Option<(&DateTime<Tz>, &Tz::Offset)> {
        dt.as_ref().map(|dt| (dt, dt.offset()))
    }

    assert_eq!(
        norm(&utc_from_str("0").ok().map(DateTime::from)),
        norm(&Some(Utc.with_ymd_and_hms(1970, 1, 1, 0, 0, 0).unwrap()))
    );
    assert_eq!(
        norm(&utc_from_str("-1").ok().map(DateTime::from)),
        norm(&Some(Utc.with_ymd_and_hms(1969, 12, 31, 23, 59, 59).unwrap()))
    );

    assert_eq!(
        norm(&fixed_from_str("0").ok().map(DateTime::from)),
        norm(&Some(
            FixedOffset::east_opt(0).unwrap().with_ymd_and_hms(1970, 1, 1, 0, 0, 0).unwrap()
        ))
    );
    assert_eq!(
        norm(&fixed_from_str("-1").ok().map(DateTime::from)),
        norm(&Some(
            FixedOffset::east_opt(0).unwrap().with_ymd_and_hms(1969, 12, 31, 23, 59, 59).unwrap()
        ))
    );

    assert_eq!(
        *fixed_from_str("0").expect("0 timestamp should parse"),
        Utc.with_ymd_and_hms(1970, 1, 1, 0, 0, 0).unwrap()
    );
    assert_eq!(
        *local_from_str("-1").expect("-1 timestamp should parse"),
        Utc.with_ymd_and_hms(1969, 12, 31, 23, 59, 59).unwrap()
    );
}
