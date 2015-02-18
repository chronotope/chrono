// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 calendar date without timezone.
 */

use std::{str, fmt, hash};
use std::num::{Int, ToPrimitive};
use std::ops::{Add, Sub};

use {Weekday, Datelike};
use div::div_mod_floor;
use duration::Duration;
use naive::time::NaiveTime;
use naive::datetime::NaiveDateTime;
use format::{Item, Numeric, Pad};
use format::{parse, Parsed, ParseError, ParseResult, DelayedFormat, StrftimeItems};

use self::internals::{DateImpl, Of, Mdf, YearFlags};

const MAX_YEAR: i32 = internals::MAX_YEAR as i32;
const MIN_YEAR: i32 = internals::MIN_YEAR as i32;

//   MAX_YEAR-12-31 minus 0000-01-01
// = ((MAX_YEAR+1)-01-01 minus 0001-01-01) + (0001-01-01 minus 0000-01-01) - 1 day
// = ((MAX_YEAR+1)-01-01 minus 0001-01-01) + 365 days
// = MAX_YEAR * 365 + (# of leap years from 0001 to MAX_YEAR) + 365 days
#[cfg(test)] // only used for testing
const MAX_DAYS_FROM_YEAR_0: i32 = MAX_YEAR * 365 +
                                  MAX_YEAR / 4 -
                                  MAX_YEAR / 100 +
                                  MAX_YEAR / 400 + 365;

//   MIN_YEAR-01-01 minus 0000-01-01
// = (MIN_YEAR+400n+1)-01-01 minus (400n+1)-01-01
// = ((MIN_YEAR+400n+1)-01-01 minus 0001-01-01) - ((400n+1)-01-01 minus 0001-01-01)
// = ((MIN_YEAR+400n+1)-01-01 minus 0001-01-01) - 146097n days
//
// n is set to 1000 for convenience.
#[cfg(test)] // only used for testing
const MIN_DAYS_FROM_YEAR_0: i32 = (MIN_YEAR + 400_000) * 365 +
                                  (MIN_YEAR + 400_000) / 4 -
                                  (MIN_YEAR + 400_000) / 100 +
                                  (MIN_YEAR + 400_000) / 400 - 146097_000;

/// ISO 8601 calendar date without timezone.
/// Allows for every proleptic Gregorian date from Jan 1, 262145 BCE to Dec 31, 262143 CE.
/// Also supports the conversion from ISO 8601 ordinal and week date.
#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct NaiveDate {
    ymdf: DateImpl, // (year << 13) | of
}

/// The minimum possible `NaiveDate`.
pub const MIN: NaiveDate = NaiveDate { ymdf: (MIN_YEAR << 13) | (1 << 4) | 0o07 /*FE*/ };
/// The maximum possible `NaiveDate`.
pub const MAX: NaiveDate = NaiveDate { ymdf: (MAX_YEAR << 13) | (365 << 4) | 0o17 /*F*/ };

// as it is hard to verify year flags in `MIN` and `MAX`, we use a separate run-time test.
#[test]
fn test_date_bounds() {
    let calculated_min = NaiveDate::from_ymd(MIN_YEAR, 1, 1);
    let calculated_max = NaiveDate::from_ymd(MAX_YEAR, 12, 31);
    assert!(MIN == calculated_min,
            "`MIN` should have a year flag {:?}", calculated_min.of().flags());
    assert!(MAX == calculated_max,
            "`MAX` should have a year flag {:?}", calculated_max.of().flags());
}

impl NaiveDate {
    /// Makes a new `NaiveDate` from year and packed ordinal-flags, with a verification.
    fn from_of(year: i32, of: Of) -> Option<NaiveDate> {
        if year >= MIN_YEAR && year <= MAX_YEAR && of.valid() {
            let Of(of) = of;
            Some(NaiveDate { ymdf: ((year << 13) as DateImpl) | (of as DateImpl) })
        } else {
            None
        }
    }

    /// Makes a new `NaiveDate` from year and packed month-day-flags, with a verification.
    fn from_mdf(year: i32, mdf: Mdf) -> Option<NaiveDate> {
        NaiveDate::from_of(year, mdf.to_of())
    }

    /// Makes a new `NaiveDate` from year, month and day.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// Fails on the out-of-range date, invalid month and/or day.
    pub fn from_ymd(year: i32, month: u32, day: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(year, month, day).expect("invalid or out-of-range date")
    }

    /// Makes a new `NaiveDate` from year, month and day.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// Returns `None` on the out-of-range date, invalid month and/or day.
    pub fn from_ymd_opt(year: i32, month: u32, day: u32) -> Option<NaiveDate> {
        let flags = YearFlags::from_year(year);
        NaiveDate::from_mdf(year, Mdf::new(month, day, flags))
    }

    /// Makes a new `NaiveDate` from year and day of year (DOY or "ordinal").
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// Fails on the out-of-range date and/or invalid DOY.
    pub fn from_yo(year: i32, ordinal: u32) -> NaiveDate {
        NaiveDate::from_yo_opt(year, ordinal).expect("invalid or out-of-range date")
    }

    /// Makes a new `NaiveDate` from year and day of year (DOY or "ordinal").
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// Returns `None` on the out-of-range date and/or invalid DOY.
    pub fn from_yo_opt(year: i32, ordinal: u32) -> Option<NaiveDate> {
        let flags = YearFlags::from_year(year);
        NaiveDate::from_of(year, Of::new(ordinal, flags))
    }

    /// Makes a new `NaiveDate` from ISO week date (year and week number) and day of the week (DOW).
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    /// The resulting `NaiveDate` may have a different year from the input year.
    ///
    /// Fails on the out-of-range date and/or invalid week number.
    pub fn from_isoywd(year: i32, week: u32, weekday: Weekday) -> NaiveDate {
        NaiveDate::from_isoywd_opt(year, week, weekday).expect("invalid or out-of-range date")
    }

    /// Makes a new `NaiveDate` from ISO week date (year and week number) and day of the week (DOW).
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    /// The resulting `NaiveDate` may have a different year from the input year.
    ///
    /// Returns `None` on the out-of-range date and/or invalid week number.
    pub fn from_isoywd_opt(year: i32, week: u32, weekday: Weekday) -> Option<NaiveDate> {
        let flags = YearFlags::from_year(year);
        let nweeks = flags.nisoweeks();
        if 1 <= week && week <= nweeks {
            // ordinal = week ordinal - delta
            let weekord = week * 7 + weekday as u32;
            let delta = flags.isoweek_delta();
            if weekord <= delta { // ordinal < 1, previous year
                let prevflags = YearFlags::from_year(year - 1);
                NaiveDate::from_of(year - 1, Of::new(weekord + prevflags.ndays() - delta,
                                                     prevflags))
            } else {
                let ordinal = weekord - delta;
                let ndays = flags.ndays();
                if ordinal <= ndays { // this year
                    NaiveDate::from_of(year, Of::new(ordinal, flags))
                } else { // ordinal > ndays, next year
                    let nextflags = YearFlags::from_year(year + 1);
                    NaiveDate::from_of(year + 1, Of::new(ordinal - ndays, nextflags))
                }
            }
        } else {
            None
        }
    }

    /// Makes a new `NaiveDate` from the number of days since January 1, 1 (Day 1)
    /// in the proleptic Gregorian calendar.
    ///
    /// Fails on the out-of-range date.
    #[inline]
    pub fn from_num_days_from_ce(days: i32) -> NaiveDate {
        NaiveDate::from_num_days_from_ce_opt(days).expect("out-of-range date")
    }

    /// Makes a new `NaiveDate` from the number of days since January 1, 1 (Day 1)
    /// in the proleptic Gregorian calendar.
    ///
    /// Returns `None` on the out-of-range date.
    pub fn from_num_days_from_ce_opt(days: i32) -> Option<NaiveDate> {
        let days = days + 365; // make January 1, 1 BCE equal to day 0
        let (year_div_400, cycle) = div_mod_floor(days, 146097);
        let (year_mod_400, ordinal) = internals::cycle_to_yo(cycle as u32);
        let flags = YearFlags::from_year_mod_400(year_mod_400 as i32);
        NaiveDate::from_of(year_div_400 * 400 + year_mod_400 as i32,
                           Of::new(ordinal, flags))
    }

    /// Parses a string with the specified format string and returns a new `NaiveDate`.
    /// See the `format::strftime` module on the supported escape sequences.
    pub fn parse_from_str(s: &str, fmt: &str) -> ParseResult<NaiveDate> {
        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, StrftimeItems::new(fmt)));
        parsed.to_naive_date()
    }

    /// Makes a new `NaiveDateTime` from the current date and given `NaiveTime`.
    #[inline]
    pub fn and_time(&self, time: NaiveTime) -> NaiveDateTime {
        NaiveDateTime::new(self.clone(), time)
    }

    /// Makes a new `NaiveDateTime` from the current date, hour, minute and second.
    ///
    /// Fails on invalid hour, minute and/or second.
    #[inline]
    pub fn and_hms(&self, hour: u32, min: u32, sec: u32) -> NaiveDateTime {
        self.and_hms_opt(hour, min, sec).expect("invalid time")
    }

    /// Makes a new `NaiveDateTime` from the current date, hour, minute and second.
    ///
    /// Returns `None` on invalid hour, minute and/or second.
    #[inline]
    pub fn and_hms_opt(&self, hour: u32, min: u32, sec: u32) -> Option<NaiveDateTime> {
        NaiveTime::from_hms_opt(hour, min, sec).map(|time| self.and_time(time))
    }

    /// Makes a new `NaiveDateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn and_hms_milli(&self, hour: u32, min: u32, sec: u32, milli: u32) -> NaiveDateTime {
        self.and_hms_milli_opt(hour, min, sec, milli).expect("invalid time")
    }

    /// Makes a new `NaiveDateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn and_hms_milli_opt(&self, hour: u32, min: u32, sec: u32,
                             milli: u32) -> Option<NaiveDateTime> {
        NaiveTime::from_hms_milli_opt(hour, min, sec, milli).map(|time| self.and_time(time))
    }

    /// Makes a new `NaiveDateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn and_hms_micro(&self, hour: u32, min: u32, sec: u32, micro: u32) -> NaiveDateTime {
        self.and_hms_micro_opt(hour, min, sec, micro).expect("invalid time")
    }

    /// Makes a new `NaiveDateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn and_hms_micro_opt(&self, hour: u32, min: u32, sec: u32,
                             micro: u32) -> Option<NaiveDateTime> {
        NaiveTime::from_hms_micro_opt(hour, min, sec, micro).map(|time| self.and_time(time))
    }

    /// Makes a new `NaiveDateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or nanosecond.
    #[inline]
    pub fn and_hms_nano(&self, hour: u32, min: u32, sec: u32, nano: u32) -> NaiveDateTime {
        self.and_hms_nano_opt(hour, min, sec, nano).expect("invalid time")
    }

    /// Makes a new `NaiveDateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or nanosecond.
    #[inline]
    pub fn and_hms_nano_opt(&self, hour: u32, min: u32, sec: u32,
                            nano: u32) -> Option<NaiveDateTime> {
        NaiveTime::from_hms_nano_opt(hour, min, sec, nano).map(|time| self.and_time(time))
    }

    /// Returns the packed month-day-flags.
    #[inline]
    fn mdf(&self) -> Mdf {
        self.of().to_mdf()
    }

    /// Returns the packed ordinal-flags.
    #[inline]
    fn of(&self) -> Of {
        Of((self.ymdf & 0b1111_11111_1111) as u32)
    }

    /// Makes a new `NaiveDate` with the packed month-day-flags changed.
    ///
    /// Returns `None` when the resulting `NaiveDate` would be invalid.
    #[inline]
    fn with_mdf(&self, mdf: Mdf) -> Option<NaiveDate> {
        self.with_of(mdf.to_of())
    }

    /// Makes a new `NaiveDate` with the packed ordinal-flags changed.
    ///
    /// Returns `None` when the resulting `NaiveDate` would be invalid.
    #[inline]
    fn with_of(&self, of: Of) -> Option<NaiveDate> {
        if of.valid() {
            let Of(of) = of;
            Some(NaiveDate { ymdf: (self.ymdf & !0b111111111_1111) | of as DateImpl })
        } else {
            None
        }
    }

    /// Makes a new `NaiveDate` for the next date.
    ///
    /// Fails when `self` is the last representable date.
    #[inline]
    pub fn succ(&self) -> NaiveDate {
        self.succ_opt().expect("out of bound")
    }

    /// Makes a new `NaiveDate` for the next date.
    ///
    /// Returns `None` when `self` is the last representable date.
    #[inline]
    pub fn succ_opt(&self) -> Option<NaiveDate> {
        self.with_of(self.of().succ()).or_else(|| NaiveDate::from_ymd_opt(self.year() + 1, 1, 1))
    }

    /// Makes a new `NaiveDate` for the prior date.
    ///
    /// Fails when `self` is the first representable date.
    #[inline]
    pub fn pred(&self) -> NaiveDate {
        self.pred_opt().expect("out of bound")
    }

    /// Makes a new `NaiveDate` for the prior date.
    ///
    /// Returns `None` when `self` is the first representable date.
    #[inline]
    pub fn pred_opt(&self) -> Option<NaiveDate> {
        self.with_of(self.of().pred()).or_else(|| NaiveDate::from_ymd_opt(self.year() - 1, 12, 31))
    }

    /// Adds the `days` part of given `Duration` to the current date.
    ///
    /// Returns `None` when it will result in overflow.
    pub fn checked_add(self, rhs: Duration) -> Option<NaiveDate> {
        let year = self.year();
        let (mut year_div_400, year_mod_400) = div_mod_floor(year, 400);
        let cycle = internals::yo_to_cycle(year_mod_400 as u32, self.of().ordinal());
        let cycle = try_opt!((cycle as i32).checked_add(try_opt!(rhs.num_days().to_i32())));
        let (cycle_div_400y, cycle) = div_mod_floor(cycle, 146097);
        year_div_400 += cycle_div_400y;

        let (year_mod_400, ordinal) = internals::cycle_to_yo(cycle as u32);
        let flags = YearFlags::from_year_mod_400(year_mod_400 as i32);
        NaiveDate::from_of(year_div_400 * 400 + year_mod_400 as i32,
                           Of::new(ordinal, flags))
    }

    /// Subtracts the `days` part of given `Duration` from the current date.
    ///
    /// Returns `None` when it will result in overflow.
    pub fn checked_sub(self, rhs: Duration) -> Option<NaiveDate> {
        let year = self.year();
        let (mut year_div_400, year_mod_400) = div_mod_floor(year, 400);
        let cycle = internals::yo_to_cycle(year_mod_400 as u32, self.of().ordinal());
        let cycle = try_opt!((cycle as i32).checked_sub(try_opt!(rhs.num_days().to_i32())));
        let (cycle_div_400y, cycle) = div_mod_floor(cycle, 146097);
        year_div_400 += cycle_div_400y;

        let (year_mod_400, ordinal) = internals::cycle_to_yo(cycle as u32);
        let flags = YearFlags::from_year_mod_400(year_mod_400 as i32);
        NaiveDate::from_of(year_div_400 * 400 + year_mod_400 as i32,
                           Of::new(ordinal, flags))
    }

    /// Formats the date with the specified formatting items.
    #[inline]
    pub fn format_with_items<'a, I>(&'a self, items: I) -> DelayedFormat<'a, I>
            where I: Iterator<Item=Item<'a>> + Clone {
        DelayedFormat::new(Some(self.clone()), None, items)
    }

    /// Formats the date with the specified format string.
    /// See the `format::strftime` module on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&'a self, fmt: &'a str) -> DelayedFormat<'a, StrftimeItems<'a>> {
        self.format_with_items(StrftimeItems::new(fmt))
    }
}

impl Datelike for NaiveDate {
    #[inline] fn year(&self) -> i32 { (self.ymdf >> 13) as i32 }
    #[inline] fn month(&self) -> u32 { self.mdf().month() }
    #[inline] fn month0(&self) -> u32 { self.mdf().month() - 1 }
    #[inline] fn day(&self) -> u32 { self.mdf().day() }
    #[inline] fn day0(&self) -> u32 { self.mdf().day() - 1 }
    #[inline] fn ordinal(&self) -> u32 { self.of().ordinal() }
    #[inline] fn ordinal0(&self) -> u32 { self.of().ordinal() - 1 }
    #[inline] fn weekday(&self) -> Weekday { self.of().weekday() }

    fn isoweekdate(&self) -> (i32, u32, Weekday) {
        let of = self.of();
        let year = self.year();
        let (rawweek, weekday) = of.isoweekdate_raw();
        if rawweek < 1 { // previous year
            let prevlastweek = YearFlags::from_year(year - 1).nisoweeks();
            (year - 1, prevlastweek, weekday)
        } else {
            let lastweek = of.flags().nisoweeks();
            if rawweek > lastweek { // next year
                (year + 1, 1, weekday)
            } else {
                (year, rawweek, weekday)
            }
        }
    }

    #[inline]
    fn with_year(&self, year: i32) -> Option<NaiveDate> {
        // we need to operate with `mdf` since we should keep the month and day number as is
        let mdf = self.mdf();

        // adjust the flags as needed
        let flags = YearFlags::from_year(year);
        let mdf = mdf.with_flags(flags);

        NaiveDate::from_mdf(year, mdf)
    }

    #[inline]
    fn with_month(&self, month: u32) -> Option<NaiveDate> {
        self.with_mdf(self.mdf().with_month(month))
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Option<NaiveDate> {
        self.with_mdf(self.mdf().with_month(month0 + 1))
    }

    #[inline]
    fn with_day(&self, day: u32) -> Option<NaiveDate> {
        self.with_mdf(self.mdf().with_day(day))
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Option<NaiveDate> {
        self.with_mdf(self.mdf().with_day(day0 + 1))
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<NaiveDate> {
        self.with_of(self.of().with_ordinal(ordinal))
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<NaiveDate> {
        self.with_of(self.of().with_ordinal(ordinal0 + 1))
    }
}

impl<H: hash::Hasher + hash::Writer> hash::Hash<H> for NaiveDate {
    fn hash(&self, state: &mut H) { self.ymdf.hash(state) }
}

impl Add<Duration> for NaiveDate {
    type Output = NaiveDate;

    #[inline]
    fn add(self, rhs: Duration) -> NaiveDate {
        self.checked_add(rhs).expect("`NaiveDate + Duration` overflowed")
    }
}

impl Sub<NaiveDate> for NaiveDate {
    type Output = Duration;

    fn sub(self, rhs: NaiveDate) -> Duration {
        let year1 = self.year();
        let year2 = rhs.year();
        let (year1_div_400, year1_mod_400) = div_mod_floor(year1, 400);
        let (year2_div_400, year2_mod_400) = div_mod_floor(year2, 400);
        let cycle1 = internals::yo_to_cycle(year1_mod_400 as u32, self.of().ordinal()) as i64;
        let cycle2 = internals::yo_to_cycle(year2_mod_400 as u32, rhs.of().ordinal()) as i64;
        Duration::days((year1_div_400 as i64 - year2_div_400 as i64) * 146097 + (cycle1 - cycle2))
    }
}

impl Sub<Duration> for NaiveDate {
    type Output = NaiveDate;

    #[inline]
    fn sub(self, rhs: Duration) -> NaiveDate {
        self.checked_sub(rhs).expect("`NaiveDate - Duration` overflowed")
    }
}

impl fmt::Debug for NaiveDate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let year = self.year();
        let mdf = self.mdf();
        if 0 <= year && year <= 9999 {
            write!(f, "{:04}-{:02}-{:02}", year, mdf.month(), mdf.day())
        } else {
            // ISO 8601 requires the explicit sign for out-of-range years
            write!(f, "{:+05}-{:02}-{:02}", year, mdf.month(), mdf.day())
        }
    }
}

impl fmt::Display for NaiveDate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(self, f) }
}

impl str::FromStr for NaiveDate {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<NaiveDate> {
        const ITEMS: &'static [Item<'static>] = &[
            Item::Space(""), Item::Numeric(Numeric::Year, Pad::Zero),
            Item::Space(""), Item::Literal("-"),
            Item::Space(""), Item::Numeric(Numeric::Month, Pad::Zero),
            Item::Space(""), Item::Literal("-"),
            Item::Space(""), Item::Numeric(Numeric::Day, Pad::Zero),
            Item::Space(""),
        ];

        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, ITEMS.iter().cloned()));
        parsed.to_naive_date()
    }
}

#[cfg(test)]
mod tests {
    use super::NaiveDate;
    use super::{MIN, MIN_YEAR, MIN_DAYS_FROM_YEAR_0};
    use super::{MAX, MAX_YEAR, MAX_DAYS_FROM_YEAR_0};
    use {Datelike, Weekday};
    use duration::Duration;
    use std::{i32, u32};
    use std::iter::{range_inclusive, range_step_inclusive};

    #[test]
    fn test_date_from_ymd() {
        let ymd_opt = |&: y,m,d| NaiveDate::from_ymd_opt(y, m, d);

        assert!(ymd_opt(2012, 0, 1).is_none());
        assert!(ymd_opt(2012, 1, 1).is_some());
        assert!(ymd_opt(2012, 2, 29).is_some());
        assert!(ymd_opt(2014, 2, 29).is_none());
        assert!(ymd_opt(2014, 3, 0).is_none());
        assert!(ymd_opt(2014, 3, 1).is_some());
        assert!(ymd_opt(2014, 3, 31).is_some());
        assert!(ymd_opt(2014, 3, 32).is_none());
        assert!(ymd_opt(2014, 12, 31).is_some());
        assert!(ymd_opt(2014, 13, 1).is_none());
    }

    #[test]
    fn test_date_from_yo() {
        let yo_opt = |&: y,o| NaiveDate::from_yo_opt(y, o);
        let ymd = |&: y,m,d| NaiveDate::from_ymd(y, m, d);

        assert_eq!(yo_opt(2012, 0), None);
        assert_eq!(yo_opt(2012, 1), Some(ymd(2012, 1, 1)));
        assert_eq!(yo_opt(2012, 2), Some(ymd(2012, 1, 2)));
        assert_eq!(yo_opt(2012, 32), Some(ymd(2012, 2, 1)));
        assert_eq!(yo_opt(2012, 60), Some(ymd(2012, 2, 29)));
        assert_eq!(yo_opt(2012, 61), Some(ymd(2012, 3, 1)));
        assert_eq!(yo_opt(2012, 100), Some(ymd(2012, 4, 9)));
        assert_eq!(yo_opt(2012, 200), Some(ymd(2012, 7, 18)));
        assert_eq!(yo_opt(2012, 300), Some(ymd(2012, 10, 26)));
        assert_eq!(yo_opt(2012, 366), Some(ymd(2012, 12, 31)));
        assert_eq!(yo_opt(2012, 367), None);

        assert_eq!(yo_opt(2014, 0), None);
        assert_eq!(yo_opt(2014, 1), Some(ymd(2014, 1, 1)));
        assert_eq!(yo_opt(2014, 2), Some(ymd(2014, 1, 2)));
        assert_eq!(yo_opt(2014, 32), Some(ymd(2014, 2, 1)));
        assert_eq!(yo_opt(2014, 59), Some(ymd(2014, 2, 28)));
        assert_eq!(yo_opt(2014, 60), Some(ymd(2014, 3, 1)));
        assert_eq!(yo_opt(2014, 100), Some(ymd(2014, 4, 10)));
        assert_eq!(yo_opt(2014, 200), Some(ymd(2014, 7, 19)));
        assert_eq!(yo_opt(2014, 300), Some(ymd(2014, 10, 27)));
        assert_eq!(yo_opt(2014, 365), Some(ymd(2014, 12, 31)));
        assert_eq!(yo_opt(2014, 366), None);
    }

    #[test]
    fn test_date_from_isoywd() {
        let isoywd_opt = |&: y,w,d| NaiveDate::from_isoywd_opt(y, w, d);
        let ymd = |&: y,m,d| NaiveDate::from_ymd(y, m, d);

        assert_eq!(isoywd_opt(2004, 0, Weekday::Sun), None);
        assert_eq!(isoywd_opt(2004, 1, Weekday::Mon), Some(ymd(2003, 12, 29)));
        assert_eq!(isoywd_opt(2004, 1, Weekday::Sun), Some(ymd(2004, 1, 4)));
        assert_eq!(isoywd_opt(2004, 2, Weekday::Mon), Some(ymd(2004, 1, 5)));
        assert_eq!(isoywd_opt(2004, 2, Weekday::Sun), Some(ymd(2004, 1, 11)));
        assert_eq!(isoywd_opt(2004, 52, Weekday::Mon), Some(ymd(2004, 12, 20)));
        assert_eq!(isoywd_opt(2004, 52, Weekday::Sun), Some(ymd(2004, 12, 26)));
        assert_eq!(isoywd_opt(2004, 53, Weekday::Mon), Some(ymd(2004, 12, 27)));
        assert_eq!(isoywd_opt(2004, 53, Weekday::Sun), Some(ymd(2005, 1, 2)));
        assert_eq!(isoywd_opt(2004, 54, Weekday::Mon), None);

        assert_eq!(isoywd_opt(2011, 0, Weekday::Sun), None);
        assert_eq!(isoywd_opt(2011, 1, Weekday::Mon), Some(ymd(2011, 1, 3)));
        assert_eq!(isoywd_opt(2011, 1, Weekday::Sun), Some(ymd(2011, 1, 9)));
        assert_eq!(isoywd_opt(2011, 2, Weekday::Mon), Some(ymd(2011, 1, 10)));
        assert_eq!(isoywd_opt(2011, 2, Weekday::Sun), Some(ymd(2011, 1, 16)));

        assert_eq!(isoywd_opt(2018, 51, Weekday::Mon), Some(ymd(2018, 12, 17)));
        assert_eq!(isoywd_opt(2018, 51, Weekday::Sun), Some(ymd(2018, 12, 23)));
        assert_eq!(isoywd_opt(2018, 52, Weekday::Mon), Some(ymd(2018, 12, 24)));
        assert_eq!(isoywd_opt(2018, 52, Weekday::Sun), Some(ymd(2018, 12, 30)));
        assert_eq!(isoywd_opt(2018, 53, Weekday::Mon), None);
    }

    #[test]
    fn test_date_from_isoymd_and_isoweekdate() {
        for year in range_inclusive(2000i32, 2400) {
            for week in range_inclusive(1u32, 53) {
                for &weekday in [Weekday::Mon, Weekday::Tue, Weekday::Wed, Weekday::Thu,
                                 Weekday::Fri, Weekday::Sat, Weekday::Sun].iter() {
                    let d = NaiveDate::from_isoywd_opt(year, week, weekday);
                    if d.is_some() {
                        let d = d.unwrap();
                        assert_eq!(d.weekday(), weekday);
                        let (year_, week_, weekday_) = d.isoweekdate();
                        assert_eq!(year_, year);
                        assert_eq!(week_, week);
                        assert_eq!(weekday_, weekday);
                    }
                }
            }
        }

        for year in range_inclusive(2000i32, 2400) {
            for month in range_inclusive(1u32, 12) {
                for day in range_inclusive(1u32, 31) {
                    let d = NaiveDate::from_ymd_opt(year, month, day);
                    if d.is_some() {
                        let d = d.unwrap();
                        let (year_, week_, weekday_) = d.isoweekdate();
                        let d_ = NaiveDate::from_isoywd(year_, week_, weekday_);
                        assert_eq!(d, d_);
                    }
                }
            }
        }
    }

    #[test]
    fn test_date_from_num_days_from_ce() {
        let from_ndays_from_ce = |&: days| NaiveDate::from_num_days_from_ce_opt(days);
        assert_eq!(from_ndays_from_ce(1), Some(NaiveDate::from_ymd(1, 1, 1)));
        assert_eq!(from_ndays_from_ce(2), Some(NaiveDate::from_ymd(1, 1, 2)));
        assert_eq!(from_ndays_from_ce(31), Some(NaiveDate::from_ymd(1, 1, 31)));
        assert_eq!(from_ndays_from_ce(32), Some(NaiveDate::from_ymd(1, 2, 1)));
        assert_eq!(from_ndays_from_ce(59), Some(NaiveDate::from_ymd(1, 2, 28)));
        assert_eq!(from_ndays_from_ce(60), Some(NaiveDate::from_ymd(1, 3, 1)));
        assert_eq!(from_ndays_from_ce(365), Some(NaiveDate::from_ymd(1, 12, 31)));
        assert_eq!(from_ndays_from_ce(365*1 + 1), Some(NaiveDate::from_ymd(2, 1, 1)));
        assert_eq!(from_ndays_from_ce(365*2 + 1), Some(NaiveDate::from_ymd(3, 1, 1)));
        assert_eq!(from_ndays_from_ce(365*3 + 1), Some(NaiveDate::from_ymd(4, 1, 1)));
        assert_eq!(from_ndays_from_ce(365*4 + 2), Some(NaiveDate::from_ymd(5, 1, 1)));
        assert_eq!(from_ndays_from_ce(146097 + 1), Some(NaiveDate::from_ymd(401, 1, 1)));
        assert_eq!(from_ndays_from_ce(146097*5 + 1), Some(NaiveDate::from_ymd(2001, 1, 1)));
        assert_eq!(from_ndays_from_ce(719163), Some(NaiveDate::from_ymd(1970, 1, 1)));
        assert_eq!(from_ndays_from_ce(0), Some(NaiveDate::from_ymd(0, 12, 31))); // 1 BCE
        assert_eq!(from_ndays_from_ce(-365), Some(NaiveDate::from_ymd(0, 1, 1)));
        assert_eq!(from_ndays_from_ce(-366), Some(NaiveDate::from_ymd(-1, 12, 31))); // 2 BCE

        for days in range_step_inclusive(-999900i32, 1000000, 100) {
            assert_eq!(from_ndays_from_ce(days).map(|d| d.num_days_from_ce()), Some(days));
        }

        assert_eq!(from_ndays_from_ce(MIN.num_days_from_ce()), Some(MIN));
        assert_eq!(from_ndays_from_ce(MIN.num_days_from_ce() - 1), None);
        assert_eq!(from_ndays_from_ce(MAX.num_days_from_ce()), Some(MAX));
        assert_eq!(from_ndays_from_ce(MAX.num_days_from_ce() + 1), None);
    }

    #[test]
    fn test_date_fields() {
        fn check(year: i32, month: u32, day: u32, ordinal: u32) {
            let d1 = NaiveDate::from_ymd(year, month, day);
            assert_eq!(d1.year(), year);
            assert_eq!(d1.month(), month);
            assert_eq!(d1.day(), day);
            assert_eq!(d1.ordinal(), ordinal);

            let d2 = NaiveDate::from_yo(year, ordinal);
            assert_eq!(d2.year(), year);
            assert_eq!(d2.month(), month);
            assert_eq!(d2.day(), day);
            assert_eq!(d2.ordinal(), ordinal);

            assert_eq!(d1, d2);
        }

        check(2012, 1, 1, 1);
        check(2012, 1, 2, 2);
        check(2012, 2, 1, 32);
        check(2012, 2, 29, 60);
        check(2012, 3, 1, 61);
        check(2012, 4, 9, 100);
        check(2012, 7, 18, 200);
        check(2012, 10, 26, 300);
        check(2012, 12, 31, 366);

        check(2014, 1, 1, 1);
        check(2014, 1, 2, 2);
        check(2014, 2, 1, 32);
        check(2014, 2, 28, 59);
        check(2014, 3, 1, 60);
        check(2014, 4, 10, 100);
        check(2014, 7, 19, 200);
        check(2014, 10, 27, 300);
        check(2014, 12, 31, 365);
    }

    #[test]
    fn test_date_weekday() {
        assert_eq!(NaiveDate::from_ymd(1582, 10, 15).weekday(), Weekday::Fri);
        // May 20, 1875 = ISO 8601 reference date
        assert_eq!(NaiveDate::from_ymd(1875, 5, 20).weekday(), Weekday::Thu);
        assert_eq!(NaiveDate::from_ymd(2000, 1, 1).weekday(), Weekday::Sat);
    }

    #[test]
    fn test_date_with_fields() {
        let d = NaiveDate::from_ymd(2000, 2, 29);
        assert_eq!(d.with_year(-400), Some(NaiveDate::from_ymd(-400, 2, 29)));
        assert_eq!(d.with_year(-100), None);
        assert_eq!(d.with_year(1600), Some(NaiveDate::from_ymd(1600, 2, 29)));
        assert_eq!(d.with_year(1900), None);
        assert_eq!(d.with_year(2000), Some(NaiveDate::from_ymd(2000, 2, 29)));
        assert_eq!(d.with_year(2001), None);
        assert_eq!(d.with_year(2004), Some(NaiveDate::from_ymd(2004, 2, 29)));
        assert_eq!(d.with_year(i32::MAX), None);

        let d = NaiveDate::from_ymd(2000, 4, 30);
        assert_eq!(d.with_month(0), None);
        assert_eq!(d.with_month(1), Some(NaiveDate::from_ymd(2000, 1, 30)));
        assert_eq!(d.with_month(2), None);
        assert_eq!(d.with_month(3), Some(NaiveDate::from_ymd(2000, 3, 30)));
        assert_eq!(d.with_month(4), Some(NaiveDate::from_ymd(2000, 4, 30)));
        assert_eq!(d.with_month(12), Some(NaiveDate::from_ymd(2000, 12, 30)));
        assert_eq!(d.with_month(13), None);
        assert_eq!(d.with_month(u32::MAX), None);

        let d = NaiveDate::from_ymd(2000, 2, 8);
        assert_eq!(d.with_day(0), None);
        assert_eq!(d.with_day(1), Some(NaiveDate::from_ymd(2000, 2, 1)));
        assert_eq!(d.with_day(29), Some(NaiveDate::from_ymd(2000, 2, 29)));
        assert_eq!(d.with_day(30), None);
        assert_eq!(d.with_day(u32::MAX), None);

        let d = NaiveDate::from_ymd(2000, 5, 5);
        assert_eq!(d.with_ordinal(0), None);
        assert_eq!(d.with_ordinal(1), Some(NaiveDate::from_ymd(2000, 1, 1)));
        assert_eq!(d.with_ordinal(60), Some(NaiveDate::from_ymd(2000, 2, 29)));
        assert_eq!(d.with_ordinal(61), Some(NaiveDate::from_ymd(2000, 3, 1)));
        assert_eq!(d.with_ordinal(366), Some(NaiveDate::from_ymd(2000, 12, 31)));
        assert_eq!(d.with_ordinal(367), None);
        assert_eq!(d.with_ordinal(u32::MAX), None);
    }

    #[test]
    fn test_date_num_days_from_ce() {
        assert_eq!(NaiveDate::from_ymd(1, 1, 1).num_days_from_ce(), 1);

        for year in range_inclusive(-9999i32, 10000) {
            assert_eq!(NaiveDate::from_ymd(year, 1, 1).num_days_from_ce(),
                       NaiveDate::from_ymd(year - 1, 12, 31).num_days_from_ce() + 1);
        }
    }

    #[test]
    fn test_date_succ() {
        let ymd = |&: y,m,d| NaiveDate::from_ymd(y, m, d);
        assert_eq!(ymd(2014, 5, 6).succ_opt(), Some(ymd(2014, 5, 7)));
        assert_eq!(ymd(2014, 5, 31).succ_opt(), Some(ymd(2014, 6, 1)));
        assert_eq!(ymd(2014, 12, 31).succ_opt(), Some(ymd(2015, 1, 1)));
        assert_eq!(ymd(2016, 2, 28).succ_opt(), Some(ymd(2016, 2, 29)));
        assert_eq!(ymd(MAX.year(), 12, 31).succ_opt(), None);
    }

    #[test]
    fn test_date_pred() {
        let ymd = |&: y,m,d| NaiveDate::from_ymd(y, m, d);
        assert_eq!(ymd(2016, 3, 1).pred_opt(), Some(ymd(2016, 2, 29)));
        assert_eq!(ymd(2015, 1, 1).pred_opt(), Some(ymd(2014, 12, 31)));
        assert_eq!(ymd(2014, 6, 1).pred_opt(), Some(ymd(2014, 5, 31)));
        assert_eq!(ymd(2014, 5, 7).pred_opt(), Some(ymd(2014, 5, 6)));
        assert_eq!(ymd(MIN.year(), 1, 1).pred_opt(), None);
    }

    #[test]
    fn test_date_add() {
        fn check((y1,m1,d1): (i32, u32, u32), rhs: Duration, ymd: Option<(i32, u32, u32)>) {
            let lhs = NaiveDate::from_ymd(y1, m1, d1);
            let sum = ymd.map(|(y,m,d)| NaiveDate::from_ymd(y, m, d));
            assert_eq!(lhs.checked_add(rhs), sum);
            assert_eq!(lhs.checked_sub(-rhs), sum);
        }

        check((2014, 1, 1), Duration::zero(), Some((2014, 1, 1)));
        check((2014, 1, 1), Duration::seconds(86399), Some((2014, 1, 1)));
        // always round towards zero
        check((2014, 1, 1), Duration::seconds(-86399), Some((2014, 1, 1)));
        check((2014, 1, 1), Duration::days(1), Some((2014, 1, 2)));
        check((2014, 1, 1), Duration::days(-1), Some((2013, 12, 31)));
        check((2014, 1, 1), Duration::days(364), Some((2014, 12, 31)));
        check((2014, 1, 1), Duration::days(365*4 + 1), Some((2018, 1, 1)));
        check((2014, 1, 1), Duration::days(365*400 + 97), Some((2414, 1, 1)));

        check((-7, 1, 1), Duration::days(365*12 + 3), Some((5, 1, 1)));

        // overflow check
        check((0, 1, 1), Duration::days(MAX_DAYS_FROM_YEAR_0 as i64), Some((MAX_YEAR, 12, 31)));
        check((0, 1, 1), Duration::days(MAX_DAYS_FROM_YEAR_0 as i64 + 1), None);
        check((0, 1, 1), Duration::max_value(), None);
        check((0, 1, 1), Duration::days(MIN_DAYS_FROM_YEAR_0 as i64), Some((MIN_YEAR, 1, 1)));
        check((0, 1, 1), Duration::days(MIN_DAYS_FROM_YEAR_0 as i64 - 1), None);
        check((0, 1, 1), Duration::min_value(), None);
    }

    #[test]
    fn test_date_sub() {
        fn check((y1,m1,d1): (i32, u32, u32), (y2,m2,d2): (i32, u32, u32), diff: Duration) {
            let lhs = NaiveDate::from_ymd(y1, m1, d1);
            let rhs = NaiveDate::from_ymd(y2, m2, d2);
            assert_eq!(lhs - rhs, diff);
            assert_eq!(rhs - lhs, -diff);
        }

        check((2014, 1, 1), (2014, 1, 1), Duration::zero());
        check((2014, 1, 2), (2014, 1, 1), Duration::days(1));
        check((2014, 12, 31), (2014, 1, 1), Duration::days(364));
        check((2015, 1, 3), (2014, 1, 1), Duration::days(365 + 2));
        check((2018, 1, 1), (2014, 1, 1), Duration::days(365*4 + 1));
        check((2414, 1, 1), (2014, 1, 1), Duration::days(365*400 + 97));

        check((MAX_YEAR, 12, 31), (0, 1, 1), Duration::days(MAX_DAYS_FROM_YEAR_0 as i64));
        check((MIN_YEAR, 1, 1), (0, 1, 1), Duration::days(MIN_DAYS_FROM_YEAR_0 as i64));
    }

    #[test]
    fn test_date_fmt() {
        assert_eq!(format!("{:?}", NaiveDate::from_ymd(2012,  3, 4)),   "2012-03-04");
        assert_eq!(format!("{:?}", NaiveDate::from_ymd(0,     3, 4)),   "0000-03-04");
        assert_eq!(format!("{:?}", NaiveDate::from_ymd(-307,  3, 4)),  "-0307-03-04");
        assert_eq!(format!("{:?}", NaiveDate::from_ymd(12345, 3, 4)), "+12345-03-04");

        assert_eq!(NaiveDate::from_ymd(2012,  3, 4).to_string(),   "2012-03-04");
        assert_eq!(NaiveDate::from_ymd(0,     3, 4).to_string(),   "0000-03-04");
        assert_eq!(NaiveDate::from_ymd(-307,  3, 4).to_string(),  "-0307-03-04");
        assert_eq!(NaiveDate::from_ymd(12345, 3, 4).to_string(), "+12345-03-04");

        // the format specifier should have no effect on `NaiveTime`
        assert_eq!(format!("{:+30?}", NaiveDate::from_ymd(1234, 5, 6)), "1234-05-06");
        assert_eq!(format!("{:30?}", NaiveDate::from_ymd(12345, 6, 7)), "+12345-06-07");
    }

    #[test]
    fn test_date_from_str() {
        // valid cases
        let valid = [
            "-0000000123456-1-2",
            "    -123456 - 1 - 2    ",
            "-12345-1-2",
            "-1234-12-31",
            "-7-6-5",
            "350-2-28",
            "360-02-29",
            "0360-02-29",
            "2015-2 -18",
            "+70-2-18",
            "+70000-2-18",
            "+00007-2-18",
        ];
        for &s in &valid {
            let d = match s.parse::<NaiveDate>() {
                Ok(d) => d,
                Err(e) => panic!("parsing `{}` has failed: {}", s, e)
            };
            let s_ = format!("{:?}", d);
            // `s` and `s_` may differ, but `s.parse()` and `s_.parse()` must be same
            let d_ = match s_.parse::<NaiveDate>() {
                Ok(d) => d,
                Err(e) => panic!("`{}` is parsed into `{:?}`, but reparsing that has failed: {}",
                                 s, d, e)
            };
            assert!(d == d_, "`{}` is parsed into `{:?}`, but reparsed result \
                              `{:?}` does not match", s, d, d_);
        }

        // some invalid cases
        // since `ParseErrorKind` is private, all we can do is to check if there was an error
        assert!("".parse::<NaiveDate>().is_err());
        assert!("x".parse::<NaiveDate>().is_err());
        assert!("2014".parse::<NaiveDate>().is_err());
        assert!("2014-01".parse::<NaiveDate>().is_err());
        assert!("2014-01-00".parse::<NaiveDate>().is_err());
        assert!("2014-13-57".parse::<NaiveDate>().is_err());
        assert!("9999999-9-9".parse::<NaiveDate>().is_err()); // out-of-bounds
    }

    #[test]
    fn test_date_parse_from_str() {
        let ymd = |&: y,m,d| NaiveDate::from_ymd(y,m,d);
        assert_eq!(NaiveDate::parse_from_str("2014-5-7T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
                   Ok(ymd(2014, 5, 7))); // ignore time and offset
        assert_eq!(NaiveDate::parse_from_str("2015-W06-1=2015-033", "%G-W%V-%u = %Y-%j"),
                   Ok(ymd(2015, 2, 2)));
        assert_eq!(NaiveDate::parse_from_str("Fri, 09 Aug 13", "%a, %d %b %y"),
                   Ok(ymd(2013, 8, 9)));
        assert!(NaiveDate::parse_from_str("Sat, 09 Aug 2013", "%a, %d %b %Y").is_err());
        assert!(NaiveDate::parse_from_str("2014-57", "%Y-%m-%d").is_err());
        assert!(NaiveDate::parse_from_str("2014", "%Y").is_err()); // insufficient
    }

    #[test]
    fn test_date_format() {
        let d = NaiveDate::from_ymd(2012, 3, 4);
        assert_eq!(d.format("%Y,%C,%y,%G,%g").to_string(), "2012,20,12,2012,12");
        assert_eq!(d.format("%m,%b,%h,%B").to_string(), "03,Mar,Mar,March");
        assert_eq!(d.format("%d,%e").to_string(), "04, 4");
        assert_eq!(d.format("%U,%W,%V").to_string(), "10,09,09");
        assert_eq!(d.format("%a,%A,%w,%u").to_string(), "Sun,Sunday,0,7");
        assert_eq!(d.format("%j").to_string(), "064"); // since 2012 is a leap year
        assert_eq!(d.format("%D,%x").to_string(), "03/04/12,03/04/12");
        assert_eq!(d.format("%F").to_string(), "2012-03-04");
        assert_eq!(d.format("%v").to_string(), " 4-Mar-2012");
        assert_eq!(d.format("%t%n%%%n%t").to_string(), "\t\n%\n\t");

        // non-four-digit years
        assert_eq!(NaiveDate::from_ymd(12345,  1, 1).format("%Y").to_string(), "+12345");
        assert_eq!(NaiveDate::from_ymd(1234,   1, 1).format("%Y").to_string(), "1234");
        assert_eq!(NaiveDate::from_ymd(123,    1, 1).format("%Y").to_string(), "0123");
        assert_eq!(NaiveDate::from_ymd(12,     1, 1).format("%Y").to_string(), "0012");
        assert_eq!(NaiveDate::from_ymd(1,      1, 1).format("%Y").to_string(), "0001");
        assert_eq!(NaiveDate::from_ymd(0,      1, 1).format("%Y").to_string(), "0000");
        assert_eq!(NaiveDate::from_ymd(-1,     1, 1).format("%Y").to_string(), "-0001");
        assert_eq!(NaiveDate::from_ymd(-12,    1, 1).format("%Y").to_string(), "-0012");
        assert_eq!(NaiveDate::from_ymd(-123,   1, 1).format("%Y").to_string(), "-0123");
        assert_eq!(NaiveDate::from_ymd(-1234,  1, 1).format("%Y").to_string(), "-1234");
        assert_eq!(NaiveDate::from_ymd(-12345, 1, 1).format("%Y").to_string(), "-12345");

        // corner cases
        assert_eq!(NaiveDate::from_ymd(2007, 12, 31).format("%G,%g,%U,%W,%V").to_string(),
                   "2008,08,53,53,01");
        assert_eq!(NaiveDate::from_ymd(2010, 1, 3).format("%G,%g,%U,%W,%V").to_string(),
                   "2009,09,01,00,53");
    }
}

/**
 * The internal implementation of the calendar and ordinal date.
 *
 * The current implementation is optimized for determining year, month, day and day of week. 
 * 4-bit `YearFlags` map to one of 14 possible classes of year in the Gregorian calendar,
 * which are included in every packed `NaiveDate` instance.
 * The conversion between the packed calendar date (`Mdf`) and the ordinal date (`Of`) is
 * based on the moderately-sized lookup table (~1.5KB)
 * and the packed representation is chosen for the efficient lookup.
 * Every internal data structure does not validate its input,
 * but the conversion keeps the valid value valid and the invalid value invalid
 * so that the user-facing `NaiveDate` can validate the input as late as possible.
 */
#[allow(dead_code)] // some internal methods have been left for consistency
mod internals {
    use std::{i32, num, fmt};
    use Weekday;
    use div::{div_rem, mod_floor};

    /// The internal date representation. This also includes the packed `Mdf` value.
    pub type DateImpl = i32;

    pub const MAX_YEAR: DateImpl = i32::MAX >> 13;
    pub const MIN_YEAR: DateImpl = i32::MIN >> 13;

    /// The year flags (aka the dominical letter).
    ///
    /// There are 14 possible classes of year in the Gregorian calendar:
    /// common and leap years starting with Monday through Sunday. 
    /// The `YearFlags` stores this information into 4 bits `abbb`,
    /// where `a` is `1` for the common year (simplifies the `Of` validation)
    /// and `bbb` is a non-zero `Weekday` (mapping `Mon` to 7) of the last day in the past year
    /// (simplifies the day of week calculation from the 1-based ordinal).
    #[derive(PartialEq, Eq, Copy)]
    pub struct YearFlags(pub u8);

    pub const A: YearFlags = YearFlags(0o15); pub const AG: YearFlags = YearFlags(0o05);
    pub const B: YearFlags = YearFlags(0o14); pub const BA: YearFlags = YearFlags(0o04);
    pub const C: YearFlags = YearFlags(0o13); pub const CB: YearFlags = YearFlags(0o03);
    pub const D: YearFlags = YearFlags(0o12); pub const DC: YearFlags = YearFlags(0o02);
    pub const E: YearFlags = YearFlags(0o11); pub const ED: YearFlags = YearFlags(0o01);
    pub const F: YearFlags = YearFlags(0o17); pub const FE: YearFlags = YearFlags(0o07);
    pub const G: YearFlags = YearFlags(0o16); pub const GF: YearFlags = YearFlags(0o06);

    static YEAR_TO_FLAGS: [YearFlags; 400] = [
        BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F,
        ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B,
        AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E,
        DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A,
        GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, // 100
        C,  B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A,
        GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D,
        CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G,
        FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C,
        BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, // 200
        E,  D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C,
        BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F,
        ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B,
        AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E,
        DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, // 300
        G,  F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E,
        DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A,
        GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D,
        CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G,
        FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, // 400
    ];

    static YEAR_DELTAS: [u8; 401] = [
         0,  1,  1,  1,  1,  2,  2,  2,  2,  3,  3,  3,  3,  4,  4,  4,  4,  5,  5,  5,
         5,  6,  6,  6,  6,  7,  7,  7,  7,  8,  8,  8,  8,  9,  9,  9,  9, 10, 10, 10,
        10, 11, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15,
        15, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 20,
        20, 21, 21, 21, 21, 22, 22, 22, 22, 23, 23, 23, 23, 24, 24, 24, 24, 25, 25, 25, // 100
        25, 25, 25, 25, 25, 26, 26, 26, 26, 27, 27, 27, 27, 28, 28, 28, 28, 29, 29, 29,
        29, 30, 30, 30, 30, 31, 31, 31, 31, 32, 32, 32, 32, 33, 33, 33, 33, 34, 34, 34,
        34, 35, 35, 35, 35, 36, 36, 36, 36, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39,
        39, 40, 40, 40, 40, 41, 41, 41, 41, 42, 42, 42, 42, 43, 43, 43, 43, 44, 44, 44,
        44, 45, 45, 45, 45, 46, 46, 46, 46, 47, 47, 47, 47, 48, 48, 48, 48, 49, 49, 49, // 200
        49, 49, 49, 49, 49, 50, 50, 50, 50, 51, 51, 51, 51, 52, 52, 52, 52, 53, 53, 53,
        53, 54, 54, 54, 54, 55, 55, 55, 55, 56, 56, 56, 56, 57, 57, 57, 57, 58, 58, 58,
        58, 59, 59, 59, 59, 60, 60, 60, 60, 61, 61, 61, 61, 62, 62, 62, 62, 63, 63, 63,
        63, 64, 64, 64, 64, 65, 65, 65, 65, 66, 66, 66, 66, 67, 67, 67, 67, 68, 68, 68,
        68, 69, 69, 69, 69, 70, 70, 70, 70, 71, 71, 71, 71, 72, 72, 72, 72, 73, 73, 73, // 300
        73, 73, 73, 73, 73, 74, 74, 74, 74, 75, 75, 75, 75, 76, 76, 76, 76, 77, 77, 77,
        77, 78, 78, 78, 78, 79, 79, 79, 79, 80, 80, 80, 80, 81, 81, 81, 81, 82, 82, 82,
        82, 83, 83, 83, 83, 84, 84, 84, 84, 85, 85, 85, 85, 86, 86, 86, 86, 87, 87, 87,
        87, 88, 88, 88, 88, 89, 89, 89, 89, 90, 90, 90, 90, 91, 91, 91, 91, 92, 92, 92,
        92, 93, 93, 93, 93, 94, 94, 94, 94, 95, 95, 95, 95, 96, 96, 96, 96, 97, 97, 97, 97 // 400+1
    ];

    pub fn cycle_to_yo(cycle: u32) -> (u32, u32) {
        let (mut year_mod_400, mut ordinal0) = div_rem(cycle, 365);
        let delta = YEAR_DELTAS[year_mod_400 as usize] as u32;
        if ordinal0 < delta {
            year_mod_400 -= 1;
            ordinal0 += 365 - YEAR_DELTAS[year_mod_400 as usize] as u32;
        } else {
            ordinal0 -= delta;
        }
        (year_mod_400, ordinal0 + 1)
    }

    pub fn yo_to_cycle(year_mod_400: u32, ordinal: u32) -> u32 {
        year_mod_400 * 365 + YEAR_DELTAS[year_mod_400 as usize] as u32 + ordinal - 1
    }

    impl YearFlags {
        #[inline]
        pub fn from_year(year: i32) -> YearFlags {
            let year = mod_floor(year, 400);
            YearFlags::from_year_mod_400(year)
        }

        #[inline]
        pub fn from_year_mod_400(year: i32) -> YearFlags {
            YEAR_TO_FLAGS[year as usize]
        }

        #[inline]
        pub fn ndays(&self) -> u32 {
            let YearFlags(flags) = *self;
            366 - (flags >> 3) as u32
        }

        #[inline]
        pub fn isoweek_delta(&self) -> u32 {
            let YearFlags(flags) = *self;
            let mut delta = flags as u32 & 0b111;
            if delta < 3 { delta += 7; }
            delta
        }

        #[inline]
        pub fn nisoweeks(&self) -> u32 {
            let YearFlags(flags) = *self;
            52 + ((0b00000100_00000110 >> flags as usize) & 1)
        }
    }

    impl fmt::Debug for YearFlags {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let YearFlags(flags) = *self;
            match flags {
                0o15 => "A".fmt(f),  0o05 => "AG".fmt(f),
                0o14 => "B".fmt(f),  0o04 => "BA".fmt(f),
                0o13 => "C".fmt(f),  0o03 => "CB".fmt(f),
                0o12 => "D".fmt(f),  0o02 => "DC".fmt(f),
                0o11 => "E".fmt(f),  0o01 => "ED".fmt(f),
                0o10 => "F?".fmt(f), 0o00 => "FE?".fmt(f), // non-canonical
                0o17 => "F".fmt(f),  0o07 => "FE".fmt(f),
                0o16 => "G".fmt(f),  0o06 => "GF".fmt(f),
                _ => write!(f, "YearFlags({})", flags),
            }
        }
    }

    pub const MIN_OL: u32 = 1 << 1;
    pub const MAX_OL: u32 = 366 << 1; // larger than the non-leap last day `(365 << 1) | 1`
    pub const MIN_MDL: u32 = (1 << 6) | (1 << 1);
    pub const MAX_MDL: u32 = (12 << 6) | (31 << 1) | 1;

    const XX: i8 = -128;
    static MDL_TO_OL: [i8; (MAX_MDL as usize + 1us)] = [
         XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX,
         XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX,
         XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX,
         XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, // 0
         XX, XX, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
         64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
         64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
         64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // 1
         XX, XX, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
         66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
         66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
         66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, XX, XX, XX, XX, XX, // 2
         XX, XX, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74,
         72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74,
         72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74,
         72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, // 3
         XX, XX, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76,
         74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76,
         74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76,
         74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, XX, XX, // 4
         XX, XX, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80,
         78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80,
         78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80,
         78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, // 5
         XX, XX, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82,
         80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82,
         80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82,
         80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, XX, XX, // 6
         XX, XX, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86,
         84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86,
         84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86,
         84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, // 7
         XX, XX, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88,
         86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88,
         86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88,
         86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, // 8
         XX, XX, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90,
         88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90,
         88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90,
         88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, XX, XX, // 9
         XX, XX, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94,
         92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94,
         92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94,
         92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, // 10
         XX, XX, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96,
         94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96,
         94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96,
         94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, XX, XX, // 11
         XX, XX, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100,
         98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100,
         98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100,
         98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100, // 12
    ];

    static OL_TO_MDL: [u8; (MAX_OL as usize + 1us)] = [
          0,  0,                                                         // 0
         64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
         64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
         64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
         64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,         // 1
         66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
         66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
         66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
         66, 66, 66, 66, 66, 66, 66, 66, 66,                             // 2
             74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74,
         72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74,
         72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74,
         72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72,     // 3
             76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76,
         74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76,
         74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76,
         74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74,             // 4
             80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80,
         78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80,
         78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80,
         78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78,     // 5
             82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82,
         80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82,
         80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82,
         80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80,             // 6
             86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86,
         84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86,
         84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86,
         84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84,     // 7
             88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88,
         86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88,
         86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88,
         86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86,     // 8
             90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90,
         88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90,
         88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90,
         88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88,             // 9
             94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94,
         92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94,
         92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94,
         92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92,     // 10
             96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96,
         94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96,
         94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96,
         94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94,             // 11
            100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100,
         98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100,
         98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100,
         98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,100, 98,     // 12
    ];

    /// Ordinal (day of year) and year flags: `(ordinal << 4) | flags`.
    ///
    /// The whole bits except for the least 3 bits are referred as `Ol` (ordinal and leap flag),
    /// which is an index to the `OL_TO_MDL` lookup table.
    #[derive(PartialEq, PartialOrd, Copy)]
    pub struct Of(pub u32);

    impl Of {
        #[inline]
        fn clamp_ordinal(ordinal: u32) -> u32 {
            if ordinal > 366 {0} else {ordinal}
        }

        #[inline]
        pub fn new(ordinal: u32, YearFlags(flags): YearFlags) -> Of {
            let ordinal = Of::clamp_ordinal(ordinal);
            Of((ordinal << 4) | (flags as u32))
        }

        #[inline]
        pub fn from_mdf(Mdf(mdf): Mdf) -> Of {
            let mdl = mdf >> 3;
            match MDL_TO_OL.get(mdl as usize) {
                Some(&v) => Of(mdf - ((v as i32 as u32 & 0x3ff) << 3)),
                None => Of(0)
            }
        }

        #[inline]
        pub fn valid(&self) -> bool {
            let Of(of) = *self;
            let ol = of >> 3;
            ol - MIN_OL <= MAX_OL - MIN_OL
        }

        #[inline]
        pub fn ordinal(&self) -> u32 {
            let Of(of) = *self;
            (of >> 4) as u32
        }

        #[inline]
        pub fn with_ordinal(&self, ordinal: u32) -> Of {
            let ordinal = Of::clamp_ordinal(ordinal);
            let Of(of) = *self;
            Of((of & 0b1111) | (ordinal << 4))
        }

        #[inline]
        pub fn flags(&self) -> YearFlags {
            let Of(of) = *self;
            YearFlags((of & 0b1111) as u8)
        }

        #[inline]
        pub fn with_flags(&self, YearFlags(flags): YearFlags) -> Of {
            let Of(of) = *self;
            Of((of & !0b1111) | (flags as u32))
        }

        #[inline]
        pub fn weekday(&self) -> Weekday {
            let Of(of) = *self;
            num::from_u32(((of >> 4) + (of & 0b111)) % 7).unwrap()
        }

        #[inline]
        pub fn isoweekdate_raw(&self) -> (u32, Weekday) {
            // week ordinal = ordinal + delta
            let Of(of) = *self;
            let weekord = (of >> 4) + self.flags().isoweek_delta();
            (weekord / 7, num::from_u32(weekord % 7).unwrap())
        }

        #[inline]
        pub fn to_mdf(&self) -> Mdf {
            Mdf::from_of(*self)
        }

        #[inline]
        pub fn succ(&self) -> Of {
            let Of(of) = *self;
            Of(of + (1 << 4))
        }

        #[inline]
        pub fn pred(&self) -> Of {
            let Of(of) = *self;
            Of(of - (1 << 4))
        }
    }

    impl fmt::Debug for Of {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let Of(of) = *self;
            write!(f, "Of(({} << 4) | {:#04o} /*{:?}*/)",
                   of >> 4, of & 0b1111, YearFlags((of & 0b1111) as u8))
        }
    }

    /// Month, day of month and year flags: `(month << 9) | (day << 4) | flags`
    ///
    /// The whole bits except for the least 3 bits are referred as `Mdl`
    /// (month, day of month and leap flag),
    /// which is an index to the `MDL_TO_OL` lookup table.
    #[derive(PartialEq, PartialOrd, Copy)]
    pub struct Mdf(pub u32);

    impl Mdf {
        #[inline]
        fn clamp_month(month: u32) -> u32 {
            if month > 12 {0} else {month}
        }

        #[inline]
        fn clamp_day(day: u32) -> u32 {
            if day > 31 {0} else {day}
        }

        #[inline]
        pub fn new(month: u32, day: u32, YearFlags(flags): YearFlags) -> Mdf {
            let month = Mdf::clamp_month(month);
            let day = Mdf::clamp_day(day);
            Mdf((month << 9) | (day << 4) | (flags as u32))
        }

        #[inline]
        pub fn from_of(Of(of): Of) -> Mdf {
            let ol = of >> 3;
            match OL_TO_MDL.get(ol as usize) {
                Some(&v) => Mdf(of + ((v as u32) << 3)),
                None => Mdf(0)
            }
        }

        #[inline]
        pub fn valid(&self) -> bool {
            let Mdf(mdf) = *self;
            let mdl = mdf >> 3;
            match MDL_TO_OL.get(mdl as usize) {
                Some(&v) => v >= 0,
                None => false
            }
        }

        #[inline]
        pub fn month(&self) -> u32 {
            let Mdf(mdf) = *self;
            (mdf >> 9) as u32
        }

        #[inline]
        pub fn with_month(&self, month: u32) -> Mdf {
            let month = Mdf::clamp_month(month);
            let Mdf(mdf) = *self;
            Mdf((mdf & 0b11111_1111) | (month << 9))
        }

        #[inline]
        pub fn day(&self) -> u32 {
            let Mdf(mdf) = *self;
            ((mdf >> 4) & 0b11111) as u32
        }

        #[inline]
        pub fn with_day(&self, day: u32) -> Mdf {
            let day = Mdf::clamp_day(day);
            let Mdf(mdf) = *self;
            Mdf((mdf & !0b11111_0000) | (day << 4))
        }

        #[inline]
        pub fn flags(&self) -> YearFlags {
            let Mdf(mdf) = *self;
            YearFlags((mdf & 0b1111) as u8)
        }

        #[inline]
        pub fn with_flags(&self, YearFlags(flags): YearFlags) -> Mdf {
            let Mdf(mdf) = *self;
            Mdf((mdf & !0b1111) | (flags as u32))
        }

        #[inline]
        pub fn to_of(&self) -> Of {
            Of::from_mdf(*self)
        }
    }

    impl fmt::Debug for Mdf {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let Mdf(mdf) = *self;
            write!(f, "Mdf(({} << 9) | ({} << 4) | {:#04o} /*{:?}*/)",
                   mdf >> 9, (mdf >> 4) & 0b11111, mdf & 0b1111, YearFlags((mdf & 0b1111) as u8))
        }
    }

    #[cfg(test)]
    mod tests {
        extern crate test;

        use Weekday;
        use super::{Of, Mdf};
        use super::{YearFlags, A, B, C, D, E, F, G, AG, BA, CB, DC, ED, FE, GF};
        use std::iter::range_inclusive;
        use std::u32;

        const NONLEAP_FLAGS: [YearFlags; 7] = [A, B, C, D, E, F, G];
        const LEAP_FLAGS: [YearFlags; 7] = [AG, BA, CB, DC, ED, FE, GF];
        const FLAGS: [YearFlags; 14] = [A, B, C, D, E, F, G, AG, BA, CB, DC, ED, FE, GF];

        #[test]
        fn test_year_flags_ndays_from_year() {
            assert_eq!(YearFlags::from_year(2014).ndays(), 365);
            assert_eq!(YearFlags::from_year(2012).ndays(), 366);
            assert_eq!(YearFlags::from_year(2000).ndays(), 366);
            assert_eq!(YearFlags::from_year(1900).ndays(), 365);
            assert_eq!(YearFlags::from_year(1600).ndays(), 366);
            assert_eq!(YearFlags::from_year(   1).ndays(), 365);
            assert_eq!(YearFlags::from_year(   0).ndays(), 366); // 1 BCE (proleptic Gregorian)
            assert_eq!(YearFlags::from_year(  -1).ndays(), 365); // 2 BCE
            assert_eq!(YearFlags::from_year(  -4).ndays(), 366); // 5 BCE
            assert_eq!(YearFlags::from_year( -99).ndays(), 365); // 100 BCE
            assert_eq!(YearFlags::from_year(-100).ndays(), 365); // 101 BCE
            assert_eq!(YearFlags::from_year(-399).ndays(), 365); // 400 BCE
            assert_eq!(YearFlags::from_year(-400).ndays(), 366); // 401 BCE
        }

        #[test]
        fn test_year_flags_nisoweeks() {
            assert_eq!(A.nisoweeks(), 52);
            assert_eq!(B.nisoweeks(), 52);
            assert_eq!(C.nisoweeks(), 52);
            assert_eq!(D.nisoweeks(), 53);
            assert_eq!(E.nisoweeks(), 52);
            assert_eq!(F.nisoweeks(), 52);
            assert_eq!(G.nisoweeks(), 52);
            assert_eq!(AG.nisoweeks(), 52);
            assert_eq!(BA.nisoweeks(), 52);
            assert_eq!(CB.nisoweeks(), 52);
            assert_eq!(DC.nisoweeks(), 53);
            assert_eq!(ED.nisoweeks(), 53);
            assert_eq!(FE.nisoweeks(), 52);
            assert_eq!(GF.nisoweeks(), 52);
        }

        #[bench]
        fn bench_year_flags_from_year(bh: &mut test::Bencher) {
            bh.iter(|| {
                for year in range(-999i32, 1000) {
                    YearFlags::from_year(year);
                }
            });
        }

        #[test]
        fn test_of() {
            fn check(expected: bool, flags: YearFlags, ordinal1: u32, ordinal2: u32) {
                for ordinal in range_inclusive(ordinal1, ordinal2) {
                    let of = Of::new(ordinal, flags);
                    assert!(of.valid() == expected,
                            "ordinal {} = {:?} should be {} for dominical year {:?}",
                            ordinal, of, if expected {"valid"} else {"invalid"}, flags);
                }
            }

            for &flags in NONLEAP_FLAGS.iter() {
                check(false, flags, 0, 0);
                check(true, flags, 1, 365);
                check(false, flags, 366, 1024);
                check(false, flags, u32::MAX, u32::MAX);
            }

            for &flags in LEAP_FLAGS.iter() {
                check(false, flags, 0, 0);
                check(true, flags, 1, 366);
                check(false, flags, 367, 1024);
                check(false, flags, u32::MAX, u32::MAX);
            }
        }

        #[test]
        fn test_mdf_valid() {
            fn check(expected: bool, flags: YearFlags, month1: u32, day1: u32,
                     month2: u32, day2: u32) {
                for month in range_inclusive(month1, month2) {
                    for day in range_inclusive(day1, day2) {
                        let mdf = Mdf::new(month, day, flags);
                        assert!(mdf.valid() == expected,
                                "month {} day {} = {:?} should be {} for dominical year {:?}",
                                month, day, mdf, if expected {"valid"} else {"invalid"}, flags);
                    }
                }
            }

            for &flags in NONLEAP_FLAGS.iter() {
                check(false, flags, 0, 0, 0, 1024);
                check(false, flags, 0, 0, 16, 0);
                check(true, flags,  1, 1,  1, 31); check(false, flags,  1, 32,  1, 1024);
                check(true, flags,  2, 1,  2, 28); check(false, flags,  2, 29,  2, 1024);
                check(true, flags,  3, 1,  3, 31); check(false, flags,  3, 32,  3, 1024);
                check(true, flags,  4, 1,  4, 30); check(false, flags,  4, 31,  4, 1024);
                check(true, flags,  5, 1,  5, 31); check(false, flags,  5, 32,  5, 1024);
                check(true, flags,  6, 1,  6, 30); check(false, flags,  6, 31,  6, 1024);
                check(true, flags,  7, 1,  7, 31); check(false, flags,  7, 32,  7, 1024);
                check(true, flags,  8, 1,  8, 31); check(false, flags,  8, 32,  8, 1024);
                check(true, flags,  9, 1,  9, 30); check(false, flags,  9, 31,  9, 1024);
                check(true, flags, 10, 1, 10, 31); check(false, flags, 10, 32, 10, 1024);
                check(true, flags, 11, 1, 11, 30); check(false, flags, 11, 31, 11, 1024);
                check(true, flags, 12, 1, 12, 31); check(false, flags, 12, 32, 12, 1024);
                check(false, flags, 13, 0, 16, 1024);
                check(false, flags, u32::MAX, 0, u32::MAX, 1024);
                check(false, flags, 0, u32::MAX, 16, u32::MAX);
                check(false, flags, u32::MAX, u32::MAX, u32::MAX, u32::MAX);
            }

            for &flags in LEAP_FLAGS.iter() {
                check(false, flags, 0, 0, 0, 1024);
                check(false, flags, 0, 0, 16, 0);
                check(true, flags,  1, 1,  1, 31); check(false, flags,  1, 32,  1, 1024);
                check(true, flags,  2, 1,  2, 29); check(false, flags,  2, 30,  2, 1024);
                check(true, flags,  3, 1,  3, 31); check(false, flags,  3, 32,  3, 1024);
                check(true, flags,  4, 1,  4, 30); check(false, flags,  4, 31,  4, 1024);
                check(true, flags,  5, 1,  5, 31); check(false, flags,  5, 32,  5, 1024);
                check(true, flags,  6, 1,  6, 30); check(false, flags,  6, 31,  6, 1024);
                check(true, flags,  7, 1,  7, 31); check(false, flags,  7, 32,  7, 1024);
                check(true, flags,  8, 1,  8, 31); check(false, flags,  8, 32,  8, 1024);
                check(true, flags,  9, 1,  9, 30); check(false, flags,  9, 31,  9, 1024);
                check(true, flags, 10, 1, 10, 31); check(false, flags, 10, 32, 10, 1024);
                check(true, flags, 11, 1, 11, 30); check(false, flags, 11, 31, 11, 1024);
                check(true, flags, 12, 1, 12, 31); check(false, flags, 12, 32, 12, 1024);
                check(false, flags, 13, 0, 16, 1024);
                check(false, flags, u32::MAX, 0, u32::MAX, 1024);
                check(false, flags, 0, u32::MAX, 16, u32::MAX);
                check(false, flags, u32::MAX, u32::MAX, u32::MAX, u32::MAX);
            }
        }

        #[test]
        fn test_of_fields() {
            for &flags in FLAGS.iter() {
                for ordinal in range_inclusive(1u32, 366) {
                    let of = Of::new(ordinal, flags);
                    if of.valid() {
                        assert_eq!(of.ordinal(), ordinal);
                    }
                }
            }
        }

        #[test]
        fn test_of_with_fields() {
            fn check(flags: YearFlags, ordinal: u32) {
                let of = Of::new(ordinal, flags);

                for ordinal in range_inclusive(0u32, 1024) {
                    let of = of.with_ordinal(ordinal);
                    assert_eq!(of.valid(), Of::new(ordinal, flags).valid());
                    if of.valid() {
                        assert_eq!(of.ordinal(), ordinal);
                    }
                }
            }

            for &flags in NONLEAP_FLAGS.iter() {
                check(flags, 1);
                check(flags, 365);
            }
            for &flags in LEAP_FLAGS.iter() {
                check(flags, 1);
                check(flags, 366);
            }
        }

        #[test]
        fn test_of_weekday() {
            assert_eq!(Of::new(1, A).weekday(), Weekday::Sun);
            assert_eq!(Of::new(1, B).weekday(), Weekday::Sat);
            assert_eq!(Of::new(1, C).weekday(), Weekday::Fri);
            assert_eq!(Of::new(1, D).weekday(), Weekday::Thu);
            assert_eq!(Of::new(1, E).weekday(), Weekday::Wed);
            assert_eq!(Of::new(1, F).weekday(), Weekday::Tue);
            assert_eq!(Of::new(1, G).weekday(), Weekday::Mon);
            assert_eq!(Of::new(1, AG).weekday(), Weekday::Sun);
            assert_eq!(Of::new(1, BA).weekday(), Weekday::Sat);
            assert_eq!(Of::new(1, CB).weekday(), Weekday::Fri);
            assert_eq!(Of::new(1, DC).weekday(), Weekday::Thu);
            assert_eq!(Of::new(1, ED).weekday(), Weekday::Wed);
            assert_eq!(Of::new(1, FE).weekday(), Weekday::Tue);
            assert_eq!(Of::new(1, GF).weekday(), Weekday::Mon);

            for &flags in FLAGS.iter() {
                let mut prev = Of::new(1, flags).weekday();
                for ordinal in range_inclusive(2u32, flags.ndays()) {
                    let of = Of::new(ordinal, flags);
                    let expected = prev.succ();
                    assert_eq!(of.weekday(), expected);
                    prev = expected;
                }
            }
        }

        #[test]
        fn test_mdf_fields() {
            for &flags in FLAGS.iter() {
                for month in range_inclusive(1u32, 12) {
                    for day in range_inclusive(1u32, 31) {
                        let mdf = Mdf::new(month, day, flags);
                        if mdf.valid() {
                            assert_eq!(mdf.month(), month);
                            assert_eq!(mdf.day(), day);
                        }
                    }
                }
            }
        }

        #[test]
        fn test_mdf_with_fields() {
            fn check(flags: YearFlags, month: u32, day: u32) {
                let mdf = Mdf::new(month, day, flags);

                for month in range_inclusive(0u32, 16) {
                    let mdf = mdf.with_month(month);
                    assert_eq!(mdf.valid(), Mdf::new(month, day, flags).valid());
                    if mdf.valid() {
                        assert_eq!(mdf.month(), month);
                        assert_eq!(mdf.day(), day);
                    }
                }

                for day in range_inclusive(0u32, 1024) {
                    let mdf = mdf.with_day(day);
                    assert_eq!(mdf.valid(), Mdf::new(month, day, flags).valid());
                    if mdf.valid() {
                        assert_eq!(mdf.month(), month);
                        assert_eq!(mdf.day(), day);
                    }
                }
            }

            for &flags in NONLEAP_FLAGS.iter() {
                check(flags, 1, 1);
                check(flags, 1, 31);
                check(flags, 2, 1);
                check(flags, 2, 28);
                check(flags, 2, 29);
                check(flags, 12, 31);
            }
            for &flags in LEAP_FLAGS.iter() {
                check(flags, 1, 1);
                check(flags, 1, 31);
                check(flags, 2, 1);
                check(flags, 2, 29);
                check(flags, 2, 30);
                check(flags, 12, 31);
            }
        }

        #[test]
        fn test_of_isoweekdate_raw() {
            for &flags in FLAGS.iter() {
                // January 4 should be in the first week
                let (week, _) = Of::new(4 /* January 4 */, flags).isoweekdate_raw();
                assert_eq!(week, 1);
            }
        }

        #[test]
        fn test_of_to_mdf() {
            for i in range_inclusive(0u32, 8192) {
                let of = Of(i);
                assert_eq!(of.valid(), of.to_mdf().valid());
            }
        }

        #[test]
        fn test_mdf_to_of() {
            for i in range_inclusive(0u32, 8192) {
                let mdf = Mdf(i);
                assert_eq!(mdf.valid(), mdf.to_of().valid());
            }
        }

        #[test]
        fn test_of_to_mdf_to_of() {
            for i in range_inclusive(0u32, 8192) {
                let of = Of(i);
                if of.valid() {
                    assert_eq!(of, of.to_mdf().to_of());
                }
            }
        }

        #[test]
        fn test_mdf_to_of_to_mdf() {
            for i in range_inclusive(0u32, 8192) {
                let mdf = Mdf(i);
                if mdf.valid() {
                    assert_eq!(mdf, mdf.to_of().to_mdf());
                }
            }
        }
    }
}

