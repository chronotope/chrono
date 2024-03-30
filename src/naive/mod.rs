//! Date and time types unconcerned with timezones.
//!
//! They are primarily building blocks for other types
//! (e.g. [`TimeZone`](../offset/trait.TimeZone.html)),
//! but can be also used for the simpler date and time handling.

use core::ops::RangeInclusive;

use crate::expect;
use crate::Weekday;

pub(crate) mod date;
pub(crate) mod datetime;
mod internals;
pub(crate) mod isoweek;
pub(crate) mod time;

pub use self::date::{NaiveDate, NaiveDateDaysIterator, NaiveDateWeeksIterator};
#[allow(deprecated)]
pub use self::date::{MAX_DATE, MIN_DATE};
#[allow(deprecated)]
pub use self::datetime::{NaiveDateTime, MAX_DATETIME, MIN_DATETIME};
pub use self::isoweek::IsoWeek;
pub use self::time::NaiveTime;

#[cfg(feature = "__internal_bench")]
#[doc(hidden)]
pub use self::internals::YearFlags as __BenchYearFlags;

/// A week represented by a [`NaiveDate`] and a [`Weekday`] which is the first
/// day of the week.
#[derive(Debug)]
pub struct NaiveWeek {
    date: NaiveDate,
    start: Weekday,
}

impl NaiveWeek {
    /// Create a new `NaiveWeek`
    pub(crate) const fn new(date: NaiveDate, start: Weekday) -> Self {
        Self { date, start }
    }

    /// Returns a date representing the first day of the week.
    ///
    /// # Panics
    ///
    /// Panics if the first day of the week happens to fall just out of range of `NaiveDate`
    /// (more than ca. 262,000 years away from common era).
    ///
    /// # Examples
    ///
    /// ```
    /// use chrono::{NaiveDate, Weekday};
    ///
    /// let date = NaiveDate::from_ymd_opt(2022, 4, 18).unwrap();
    /// let week = date.week(Weekday::Mon);
    /// assert!(week.first_day() <= date);
    /// ```
    #[inline]
    #[must_use]
    pub const fn first_day(&self) -> NaiveDate {
        let start = self.start.num_days_from_monday() as i32;
        let ref_day = self.date.weekday().num_days_from_monday() as i32;
        // Calculate the number of days to subtract from `self.date`.
        // Do not construct an intermediate date beyond `self.date`, because that may be out of
        // range if `date` is close to `NaiveDate::MAX`.
        let days = start - ref_day - if start > ref_day { 7 } else { 0 };
        expect(self.date.add_days(days), "first weekday out of range for `NaiveDate`")
    }

    /// Returns a date representing the last day of the week.
    ///
    /// # Panics
    ///
    /// Panics if the last day of the week happens to fall just out of range of `NaiveDate`
    /// (more than ca. 262,000 years away from common era).
    ///
    /// # Examples
    ///
    /// ```
    /// use chrono::{NaiveDate, Weekday};
    ///
    /// let date = NaiveDate::from_ymd_opt(2022, 4, 18).unwrap();
    /// let week = date.week(Weekday::Mon);
    /// assert!(week.last_day() >= date);
    /// ```
    #[inline]
    #[must_use]
    pub const fn last_day(&self) -> NaiveDate {
        let end = self.start.pred().num_days_from_monday() as i32;
        let ref_day = self.date.weekday().num_days_from_monday() as i32;
        // Calculate the number of days to add to `self.date`.
        // Do not construct an intermediate date before `self.date` (like with `first_day()`),
        // because that may be out of range if `date` is close to `NaiveDate::MIN`.
        let days = end - ref_day + if end < ref_day { 7 } else { 0 };
        expect(self.date.add_days(days), "last weekday out of range for `NaiveDate`")
    }

    /// Returns a [`RangeInclusive<T>`] representing the whole week bounded by
    /// [first_day](NaiveWeek::first_day) and [last_day](NaiveWeek::last_day) functions.
    ///
    /// # Panics
    ///
    /// Panics if the either the first or last day of the week happens to fall just out of range of
    /// `NaiveDate` (more than ca. 262,000 years away from common era).
    ///
    /// # Examples
    ///
    /// ```
    /// use chrono::{NaiveDate, Weekday};
    ///
    /// let date = NaiveDate::from_ymd_opt(2022, 4, 18).unwrap();
    /// let week = date.week(Weekday::Mon);
    /// let days = week.days();
    /// assert!(days.contains(&date));
    /// ```
    #[inline]
    #[must_use]
    pub const fn days(&self) -> RangeInclusive<NaiveDate> {
        self.first_day()..=self.last_day()
    }
}

/// A duration in calendar days.
///
/// This is useful because when using `TimeDelta` it is possible that adding `TimeDelta::days(1)`
/// doesn't increment the day value as expected due to it being a fixed number of seconds. This
/// difference applies only when dealing with `DateTime<TimeZone>` data types and in other cases
/// `TimeDelta::days(n)` and `Days::new(n)` are equivalent.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Days(pub(crate) u64);

impl Days {
    /// Construct a new `Days` from a number of days
    pub const fn new(num: u64) -> Self {
        Self(num)
    }
}

/// Serialization/Deserialization of `NaiveDateTime` in alternate formats
///
/// The various modules in here are intended to be used with serde's [`with` annotation] to
/// serialize as something other than the default ISO 8601 format.
///
/// [`with` annotation]: https://serde.rs/field-attrs.html#with
#[cfg(feature = "serde")]
pub mod serde {
    pub use super::datetime::serde::*;
}

#[cfg(test)]
mod test {
    use crate::{NaiveDate, Weekday};
    #[test]
    fn test_naiveweek() {
        let date = NaiveDate::from_ymd_opt(2022, 5, 18).unwrap();
        let asserts = [
            (Weekday::Mon, "Mon 2022-05-16", "Sun 2022-05-22"),
            (Weekday::Tue, "Tue 2022-05-17", "Mon 2022-05-23"),
            (Weekday::Wed, "Wed 2022-05-18", "Tue 2022-05-24"),
            (Weekday::Thu, "Thu 2022-05-12", "Wed 2022-05-18"),
            (Weekday::Fri, "Fri 2022-05-13", "Thu 2022-05-19"),
            (Weekday::Sat, "Sat 2022-05-14", "Fri 2022-05-20"),
            (Weekday::Sun, "Sun 2022-05-15", "Sat 2022-05-21"),
        ];
        for (start, first_day, last_day) in asserts {
            let week = date.week(start);
            let days = week.days();
            assert_eq!(Ok(week.first_day()), NaiveDate::parse_from_str(first_day, "%a %Y-%m-%d"));
            assert_eq!(Ok(week.last_day()), NaiveDate::parse_from_str(last_day, "%a %Y-%m-%d"));
            assert!(days.contains(&date));
        }
    }

    #[test]
    fn test_naiveweek_min_max() {
        let date_max = NaiveDate::MAX;
        assert!(date_max.week(Weekday::Mon).first_day() <= date_max);
        let date_min = NaiveDate::MIN;
        assert!(date_min.week(Weekday::Mon).last_day() >= date_min);
    }
}
