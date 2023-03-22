// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! ISO 8601 calendar date with time zone.
#![allow(deprecated)]

#[cfg(any(feature = "alloc", feature = "std", test))]
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use core::{fmt, hash};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

#[cfg(feature = "unstable-locales")]
use crate::format::Locale;
#[cfg(any(feature = "alloc", feature = "std", test))]
use crate::format::{DelayedFormat, Item, StrftimeItems};
use crate::naive::{IsoWeek, NaiveDate, NaiveTime};
use crate::offset::{TimeZone, Utc};
use crate::time_delta::TimeDelta;
use crate::{DateTime, Datelike, Error, Weekday};

/// ISO 8601 calendar date with time zone.
///
/// You almost certainly want to be using a [`NaiveDate`] instead of this type.
///
/// This type primarily exists to aid in the construction of DateTimes that
/// have a timezone by way of the [`TimeZone`] datelike constructors (e.g.
/// [`TimeZone::ymd`]).
///
/// This type should be considered ambiguous at best, due to the inherent lack
/// of precision required for the time zone resolution.
///
/// There are some guarantees on the usage of `Date<Tz>`:
///
/// - If properly constructed via [`TimeZone::ymd`] and others without an error,
///   the corresponding local date should exist for at least a moment.
///   (It may still have a gap from the offset changes.)
///
/// - The `TimeZone` is free to assign *any* [`Offset`](crate::offset::Offset) to the
///   local date, as long as that offset did occur in given day.
///
///   For example, if `2015-03-08T01:59-08:00` is followed by `2015-03-08T03:00-07:00`,
///   it may produce either `2015-03-08-08:00` or `2015-03-08-07:00`
///   but *not* `2015-03-08+00:00` and others.
///
/// - Once constructed as a full `DateTime`, [`DateTime::date`] and other associated
///   methods should return those for the original `Date`. For example, if `dt =
///   tz.ymd_opt(y,m,d).unwrap().hms(h,n,s)` were valid, `dt.date() == tz.ymd_opt(y,m,d).unwrap()`.
///
/// - The date is timezone-agnostic up to one day (i.e. practically always),
///   so the local date and UTC date should be equal for most cases
///   even though the raw calculation between `NaiveDate` and `Duration` may not.
#[deprecated(since = "0.4.23", note = "Use `NaiveDate` or `DateTime<Tz>` instead")]
#[derive(Clone)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct Date<Tz: TimeZone> {
    date: NaiveDate,
    offset: Tz::Offset,
}

/// The minimum possible `Date`.
#[allow(deprecated)]
#[deprecated(since = "0.4.20", note = "Use Date::MIN_UTC instead")]
pub const MIN_DATE: Date<Utc> = Date::<Utc>::MIN_UTC;
/// The maximum possible `Date`.
#[allow(deprecated)]
#[deprecated(since = "0.4.20", note = "Use Date::MAX_UTC instead")]
pub const MAX_DATE: Date<Utc> = Date::<Utc>::MAX_UTC;

impl<Tz: TimeZone> Date<Tz> {
    /// Makes a new `Date` with given *UTC* date and offset.
    /// The local date should be constructed via the `TimeZone` trait.
    //
    // note: this constructor is purposely not named to `new` to discourage the direct usage.
    #[inline]
    pub fn from_utc(date: NaiveDate, offset: Tz::Offset) -> Date<Tz> {
        Date { date, offset }
    }

    /// Makes a new `DateTime` from the current date and given `NaiveTime`.
    /// The offset in the current date is preserved.
    ///
    /// Returns `Err(Error)` on invalid datetime.
    #[inline]
    pub fn and_time(&self, time: NaiveTime) -> Result<DateTime<Tz>, Error> {
        let localdt = self.naive_local().and_time(time);
        self.timezone().from_local_datetime(&localdt)?.single()
    }

    /// Makes a new `DateTime` from the current date, hour, minute and second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `Err(Error)` on invalid hour, minute and/or second.
    #[inline]
    pub fn and_hms(&self, hour: u32, min: u32, sec: u32) -> Result<DateTime<Tz>, Error> {
        let time = NaiveTime::from_hms(hour, min, sec)?;
        self.and_time(time)
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `Err(Error)` on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn and_hms_milli(
        &self,
        hour: u32,
        min: u32,
        sec: u32,
        milli: u32,
    ) -> Result<DateTime<Tz>, Error> {
        let time = NaiveTime::from_hms_milli(hour, min, sec, milli)?;
        self.and_time(time)
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `Err(Error)` on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn and_hms_micro(
        &self,
        hour: u32,
        min: u32,
        sec: u32,
        micro: u32,
    ) -> Result<DateTime<Tz>, Error> {
        let time = NaiveTime::from_hms_micro(hour, min, sec, micro)?;
        self.and_time(time)
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `Err(Error)` on invalid hour, minute, second and/or nanosecond.
    #[inline]
    pub fn and_hms_nano(
        &self,
        hour: u32,
        min: u32,
        sec: u32,
        nano: u32,
    ) -> Result<DateTime<Tz>, Error> {
        let time = NaiveTime::from_hms_nano(hour, min, sec, nano)?;
        self.and_time(time)
    }

    /// Makes a new `Date` for the next date.
    ///
    /// Returns `Err(Error)` when `self` is the last representable date.
    ///
    /// ```
    /// use chrono::prelude::*;
    ///
    /// assert_eq!(Utc.ymd(2022, 09, 12)?.single()?.succ()?, Utc.ymd(2022, 09, 13)?.single()?);
    ///
    /// assert!(Date::<Utc>::MAX_UTC.succ().is_err());
    /// Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn succ(&self) -> Result<Date<Tz>, Error> {
        let date = self.date.succ()?;
        Ok(Date::from_utc(date, self.offset.clone()))
    }

    /// Makes a new `Date` for the prior date.
    ///
    /// Returns `Err(Error)` when `self` is the first representable date.
    ///
    /// ```
    /// use chrono::prelude::*;
    ///
    /// assert_eq!(Utc.ymd(2022, 09, 12)?.single()?.succ()?, Utc.ymd(2022, 09, 13)?.single()?);
    ///
    /// assert!(Date::<Utc>::MIN_UTC.pred().is_err());
    /// Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn pred(&self) -> Result<Date<Tz>, Error> {
        let date = self.date.pred()?;
        Ok(Date::from_utc(date, self.offset.clone()))
    }

    /// Retrieves an associated offset from UTC.
    #[inline]
    pub fn offset(&self) -> &Tz::Offset {
        &self.offset
    }

    /// Retrieves an associated time zone.
    #[inline]
    pub fn timezone(&self) -> Tz {
        TimeZone::from_offset(&self.offset)
    }

    /// Changes the associated time zone.
    /// This does not change the actual `Date` (but will change the string representation).
    #[inline]
    pub fn with_timezone<Tz2: TimeZone>(&self, tz: &Tz2) -> Result<Date<Tz2>, Error> {
        tz.from_utc_date(&self.date)
    }

    /// Adds given `Duration` to the current date.
    ///
    /// Returns `Err(Error)` when it will result in overflow.
    #[inline]
    pub fn checked_add_signed(self, rhs: TimeDelta) -> Result<Self, Error> {
        let date = self.date.checked_add_signed(rhs)?;
        Ok(Self { date, offset: self.offset })
    }

    /// Subtracts given `Duration` from the current date.
    ///
    /// Returns `Err(Error)` when it will result in overflow.
    #[inline]
    pub fn checked_sub_signed(self, rhs: TimeDelta) -> Result<Self, Error> {
        let date = self.date.checked_sub_signed(rhs)?;
        Ok(Self { date, offset: self.offset })
    }

    /// Subtracts another `Date` from the current date.
    /// Returns a `Duration` of integral numbers.
    ///
    /// This does not overflow or underflow at all,
    /// as all possible output fits in the range of `Duration`.
    #[inline]
    pub fn signed_duration_since<Tz2: TimeZone>(self, rhs: Date<Tz2>) -> TimeDelta {
        self.date.signed_duration_since(rhs.date)
    }

    /// Returns a view to the naive UTC date.
    #[inline]
    pub fn naive_utc(&self) -> NaiveDate {
        self.date
    }

    /// Returns a view to the naive local date.
    ///
    /// This is technically the same as [`naive_utc`](#method.naive_utc)
    /// because the offset is restricted to never exceed one day,
    /// but provided for the consistency.
    #[inline]
    pub fn naive_local(&self) -> NaiveDate {
        self.date
    }

    /// Returns the number of whole years from the given `base` until `self`.
    pub fn years_since(&self, base: Self) -> Option<u32> {
        let mut years = self.year() - base.year();
        if (self.month(), self.day()) < (base.month(), base.day()) {
            years -= 1;
        }

        match years >= 0 {
            true => Some(years as u32),
            false => None,
        }
    }

    /// The minimum possible `Date`.
    pub const MIN_UTC: Date<Utc> = Date { date: NaiveDate::MIN, offset: Utc };
    /// The maximum possible `Date`.
    pub const MAX_UTC: Date<Utc> = Date { date: NaiveDate::MAX, offset: Utc };
}

/// Maps the local date to other date with given conversion function.
fn map_local<Tz: TimeZone, F>(d: &Date<Tz>, mut f: F) -> Result<Date<Tz>, Error>
where
    F: FnMut(NaiveDate) -> Result<NaiveDate, Error>,
{
    let date = f(d.naive_local())?;
    d.timezone().from_local_date(&date)?.single()
}

impl<Tz: TimeZone> Date<Tz>
where
    Tz::Offset: fmt::Display,
{
    /// Formats the date with the specified formatting items.
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    pub fn format_with_items<'a, I, B>(&self, items: I) -> DelayedFormat<I>
    where
        I: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        DelayedFormat::new_with_offset(Some(self.naive_local()), None, &self.offset, items)
    }

    /// Formats the date with the specified format string.
    /// See the [`crate::format::strftime`] module
    /// on the supported escape sequences.
    ///
    /// # Example
    /// ```rust
    /// use chrono::prelude::*;
    ///
    /// let date_time: Date<Utc> = Utc.ymd(2017, 04, 02)?.single()?;
    /// let formatted = format!("{}", date_time.format("%d/%m/%Y"));
    /// assert_eq!(formatted, "02/04/2017");
    /// Ok::<_, chrono::Error>(())
    /// ```
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_with_items(StrftimeItems::new(fmt))
    }

    /// Formats the date with the specified formatting items and locale.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[inline]
    pub fn format_localized_with_items<'a, I, B>(
        &self,
        items: I,
        locale: Locale,
    ) -> DelayedFormat<I>
    where
        I: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        DelayedFormat::new_with_offset_and_locale(
            Some(self.naive_local()),
            None,
            &self.offset,
            items,
            locale,
        )
    }

    /// Formats the date with the specified format string and locale.
    /// See the [`crate::format::strftime`] module
    /// on the supported escape sequences.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[inline]
    pub fn format_localized<'a>(
        &self,
        fmt: &'a str,
        locale: Locale,
    ) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_localized_with_items(StrftimeItems::new_with_locale(fmt, locale), locale)
    }
}

impl<Tz: TimeZone> Datelike for Date<Tz> {
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
    fn with_year(&self, year: i32) -> Result<Date<Tz>, Error> {
        map_local(self, |date| date.with_year(year))
    }

    #[inline]
    fn with_month(&self, month: u32) -> Result<Date<Tz>, Error> {
        map_local(self, |date| date.with_month(month))
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Result<Date<Tz>, Error> {
        map_local(self, |date| date.with_month0(month0))
    }

    #[inline]
    fn with_day(&self, day: u32) -> Result<Date<Tz>, Error> {
        map_local(self, |date| date.with_day(day))
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Result<Date<Tz>, Error> {
        map_local(self, |date| date.with_day0(day0))
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Result<Date<Tz>, Error> {
        map_local(self, |date| date.with_ordinal(ordinal))
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Result<Date<Tz>, Error> {
        map_local(self, |date| date.with_ordinal0(ordinal0))
    }
}

// we need them as automatic impls cannot handle associated types
impl<Tz: TimeZone> Copy for Date<Tz> where <Tz as TimeZone>::Offset: Copy {}
unsafe impl<Tz: TimeZone> Send for Date<Tz> where <Tz as TimeZone>::Offset: Send {}

impl<Tz: TimeZone, Tz2: TimeZone> PartialEq<Date<Tz2>> for Date<Tz> {
    fn eq(&self, other: &Date<Tz2>) -> bool {
        self.date == other.date
    }
}

impl<Tz: TimeZone> Eq for Date<Tz> {}

impl<Tz: TimeZone> PartialOrd for Date<Tz> {
    fn partial_cmp(&self, other: &Date<Tz>) -> Option<Ordering> {
        self.date.partial_cmp(&other.date)
    }
}

impl<Tz: TimeZone> Ord for Date<Tz> {
    fn cmp(&self, other: &Date<Tz>) -> Ordering {
        self.date.cmp(&other.date)
    }
}

impl<Tz: TimeZone> hash::Hash for Date<Tz> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.date.hash(state)
    }
}

impl<Tz: TimeZone> Add<TimeDelta> for Date<Tz> {
    type Output = Date<Tz>;

    #[inline]
    fn add(self, rhs: TimeDelta) -> Date<Tz> {
        self.checked_add_signed(rhs).expect("`Date + Duration` overflowed")
    }
}

impl<Tz: TimeZone> AddAssign<TimeDelta> for Date<Tz> {
    #[inline]
    fn add_assign(&mut self, rhs: TimeDelta) {
        self.date = self.date.checked_add_signed(rhs).expect("`Date + Duration` overflowed");
    }
}

impl<Tz: TimeZone> Sub<TimeDelta> for Date<Tz> {
    type Output = Date<Tz>;

    #[inline]
    fn sub(self, rhs: TimeDelta) -> Date<Tz> {
        self.checked_sub_signed(rhs).expect("`Date - Duration` overflowed")
    }
}

impl<Tz: TimeZone> SubAssign<TimeDelta> for Date<Tz> {
    #[inline]
    fn sub_assign(&mut self, rhs: TimeDelta) {
        self.date = self.date.checked_sub_signed(rhs).expect("`Date - Duration` overflowed");
    }
}

impl<Tz: TimeZone> Sub<Date<Tz>> for Date<Tz> {
    type Output = TimeDelta;

    #[inline]
    fn sub(self, rhs: Date<Tz>) -> TimeDelta {
        self.signed_duration_since(rhs)
    }
}

impl<Tz: TimeZone> fmt::Debug for Date<Tz> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.naive_local().fmt(f)?;
        self.offset.fmt(f)
    }
}

impl<Tz: TimeZone> fmt::Display for Date<Tz>
where
    Tz::Offset: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.naive_local().fmt(f)?;
        self.offset.fmt(f)
    }
}

// Note that implementation of Arbitrary cannot be automatically derived for Date<Tz>, due to
// the nontrivial bound <Tz as TimeZone>::Offset: Arbitrary.
#[cfg(feature = "arbitrary")]
impl<'a, Tz> arbitrary::Arbitrary<'a> for Date<Tz>
where
    Tz: TimeZone,
    <Tz as TimeZone>::Offset: arbitrary::Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Date<Tz>> {
        let date = NaiveDate::arbitrary(u)?;
        let offset = <Tz as TimeZone>::Offset::arbitrary(u)?;
        Ok(Date::from_utc(date, offset))
    }
}

#[cfg(test)]
mod tests {
    use super::Date;

    use crate::time_delta::TimeDelta;
    use crate::{FixedOffset, NaiveDate, Utc};

    #[cfg(feature = "clock")]
    use crate::offset::{Local, TimeZone};

    #[test]
    #[cfg(feature = "clock")]
    fn test_years_elapsed() {
        const WEEKS_PER_YEAR: f32 = 52.1775;

        // This is always at least one year because 1 year = 52.1775 weeks.
        let one_year_ago =
            Utc::today().unwrap() - TimeDelta::weeks((WEEKS_PER_YEAR * 1.5).ceil() as i64);
        // A bit more than 2 years.
        let two_year_ago =
            Utc::today().unwrap() - TimeDelta::weeks((WEEKS_PER_YEAR * 2.5).ceil() as i64);

        assert_eq!(Utc::today().unwrap().years_since(one_year_ago), Some(1));
        assert_eq!(Utc::today().unwrap().years_since(two_year_ago), Some(2));

        // If the given DateTime is later than now, the function will always return 0.
        let future = Utc::today().unwrap() + TimeDelta::weeks(12);
        assert_eq!(Utc::today().unwrap().years_since(future), None);
    }

    #[test]
    fn test_date_add_assign() {
        let naivedate = NaiveDate::from_ymd(2000, 1, 1).unwrap();
        let date = Date::<Utc>::from_utc(naivedate, Utc);
        let mut date_add = date;

        date_add += TimeDelta::days(5);
        assert_eq!(date_add, date + TimeDelta::days(5));

        let timezone = FixedOffset::east(60 * 60).unwrap();
        let date = date.with_timezone(&timezone).unwrap();
        let date_add = date_add.with_timezone(&timezone).unwrap();

        assert_eq!(date_add, date + TimeDelta::days(5));

        let timezone = FixedOffset::west(2 * 60 * 60).unwrap();
        let date = date.with_timezone(&timezone).unwrap();
        let date_add = date_add.with_timezone(&timezone).unwrap();

        assert_eq!(date_add, date + TimeDelta::days(5));
    }

    #[test]
    #[cfg(feature = "clock")]
    fn test_date_add_assign_local() {
        let naivedate = NaiveDate::from_ymd(2000, 1, 1).unwrap();

        let date = Local.from_utc_date(&naivedate).unwrap();
        let mut date_add = date;

        date_add += TimeDelta::days(5);
        assert_eq!(date_add, date + TimeDelta::days(5));
    }

    #[test]
    fn test_date_sub_assign() {
        let naivedate = NaiveDate::from_ymd(2000, 1, 1).unwrap();
        let date = Date::<Utc>::from_utc(naivedate, Utc);
        let mut date_sub = date;

        date_sub -= TimeDelta::days(5);
        assert_eq!(date_sub, date - TimeDelta::days(5));

        let timezone = FixedOffset::east(60 * 60).unwrap();
        let date = date.with_timezone(&timezone).unwrap();
        let date_sub = date_sub.with_timezone(&timezone).unwrap();

        assert_eq!(date_sub, date - TimeDelta::days(5));

        let timezone = FixedOffset::west(2 * 60 * 60).unwrap();
        let date = date.with_timezone(&timezone).unwrap();
        let date_sub = date_sub.with_timezone(&timezone).unwrap();

        assert_eq!(date_sub, date - TimeDelta::days(5));
    }

    #[test]
    #[cfg(feature = "clock")]
    fn test_date_sub_assign_local() {
        let naivedate = NaiveDate::from_ymd(2000, 1, 1).unwrap();

        let date = Local.from_utc_date(&naivedate).unwrap();
        let mut date_sub = date;

        date_sub -= TimeDelta::days(5);
        assert_eq!(date_sub, date - TimeDelta::days(5));
    }
}
