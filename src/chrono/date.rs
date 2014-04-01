/*!
 * ISO 8601 calendar date.
 */

use std::fmt;
use num::Integer;
use duration::Duration;

use self::internals::{DateImpl, Of, Mdf, YearFlags};

pub static MAX_YEAR: int = internals::MAX_YEAR as int;
pub static MIN_YEAR: int = internals::MIN_YEAR as int;

/// The day of week (DOW).
#[deriving(Eq, TotalEq, FromPrimitive, Show)]
pub enum Weekday {
    Mon = 0,
    Tue = 1,
    Wed = 2,
    Thu = 3,
    Fri = 4,
    Sat = 5,
    Sun = 6,
}

impl Weekday {
    /// The next day in the week.
    #[inline]
    pub fn succ(&self) -> Weekday {
        match *self {
            Mon => Tue,
            Tue => Wed,
            Wed => Thu,
            Thu => Fri,
            Fri => Sat,
            Sat => Sun,
            Sun => Mon,
        }
    }

    /// The previous day in the week.
    #[inline]
    pub fn pred(&self) -> Weekday {
        match *self {
            Mon => Sun,
            Tue => Mon,
            Wed => Tue,
            Thu => Wed,
            Fri => Thu,
            Sat => Fri,
            Sun => Sat,
        }
    }

    /// Returns a DOW number starting from Monday = 1. (ISO 8601 weekday number)
    #[inline]
    pub fn number_from_monday(&self) -> uint {
        match *self {
            Mon => 1,
            Tue => 2,
            Wed => 3,
            Thu => 4,
            Fri => 5,
            Sat => 6,
            Sun => 7,
        }
    }

    /// Returns a DOW number starting from Sunday = 1.
    #[inline]
    pub fn number_from_sunday(&self) -> uint {
        match *self {
            Mon => 2,
            Tue => 3,
            Wed => 4,
            Thu => 5,
            Fri => 6,
            Sat => 7,
            Sun => 1,
        }
    }

    /// Returns a DOW number starting from Monday = 0.
    #[inline]
    pub fn ndays_from_monday(&self) -> uint {
        match *self {
            Mon => 0,
            Tue => 1,
            Wed => 2,
            Thu => 3,
            Fri => 4,
            Sat => 5,
            Sun => 6,
        }
    }

    /// Returns a DOW number starting from Sunday = 0.
    #[inline]
    pub fn ndays_from_sunday(&self) -> uint {
        match *self {
            Mon => 1,
            Tue => 2,
            Wed => 3,
            Thu => 4,
            Fri => 5,
            Sat => 6,
            Sun => 0,
        }
    }
}

pub trait Datelike {
    /// Returns the year number.
    fn year(&self) -> int;

    /// Returns the absolute year number starting from 1 with a boolean flag,
    /// which is false when the year predates the epoch (BCE/BC) and true otherwise (CE/AD).
    #[inline]
    fn year_ce(&self) -> (bool, uint) {
        let year = self.year();
        if year < 1 {
            (false, (1 - year) as uint)
        } else {
            (true, year as uint)
        }
    }

    /// Returns the month number starting from 1.
    fn month(&self) -> uint;

    /// Returns the month number starting from 0.
    fn month0(&self) -> uint;

    /// Returns the day of month starting from 1.
    fn day(&self) -> uint;

    /// Returns the day of month starting from 0.
    fn day0(&self) -> uint;

    /// Returns the day of year starting from 1.
    fn ordinal(&self) -> uint;

    /// Returns the day of year starting from 0.
    fn ordinal0(&self) -> uint;

    /// Returns the day of week.
    fn weekday(&self) -> Weekday;

    /// Returns the ISO week date: an adjusted year, week number and day of week.
    /// The adjusted year may differ from that of the calendar date.
    fn isoweekdate(&self) -> (int, uint, Weekday);

    /// Makes a new value with the year number changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_year(&self, year: int) -> Option<Self>;

    /// Makes a new value with the month number (starting from 1) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_month(&self, month: uint) -> Option<Self>;

    /// Makes a new value with the month number (starting from 0) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_month0(&self, month0: uint) -> Option<Self>;

    /// Makes a new value with the day of month (starting from 1) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_day(&self, day: uint) -> Option<Self>;

    /// Makes a new value with the day of month (starting from 0) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_day0(&self, day0: uint) -> Option<Self>;

    /// Makes a new value with the day of year (starting from 1) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_ordinal(&self, ordinal: uint) -> Option<Self>;

    /// Makes a new value with the day of year (starting from 0) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_ordinal0(&self, ordinal0: uint) -> Option<Self>;

    /// Returns the number of days since January 1, 1 (Day 1) in the proleptic Gregorian calendar.
    fn ndays_from_ce(&self) -> int {
        // we know this wouldn't overflow since year is limited to 1/2^13 of i32's full range.
        let mut year = self.year() - 1;
        let mut ndays = 0;
        if year < 0 {
            let excess = 1 + (-year) / 400;
            year += excess * 400;
            ndays -= excess * 146097;
        }
        let div_100 = year / 100;
        ndays += ((year * 1461) >> 2) - div_100 + (div_100 >> 2);
        ndays + self.ordinal() as int
    }
}

/// ISO 8601 calendar date without timezone.
/// Allows for every proleptic Gregorian date from Jan 1, 262145 BCE to Dec 31, 262143 CE.
/// Also supports the conversion from ISO 8601 ordinal and week date.
#[deriving(Eq, TotalEq, Ord, TotalOrd, Hash)]
pub struct DateZ {
    ymdf: DateImpl, // (year << 13) | of
}

impl DateZ {
    /// Makes a new `DateZ` from year and packed ordinal-flags, with a verification.
    fn from_of(year: int, of: Of) -> Option<DateZ> {
        if year >= MIN_YEAR && year <= MAX_YEAR && of.valid() {
            let Of(of) = of;
            Some(DateZ { ymdf: ((year << 13) as DateImpl) | (of as DateImpl) })
        } else {
            None
        }
    }

    /// Makes a new `DateZ` from year and packed month-day-flags, with a verification.
    fn from_mdf(year: int, mdf: Mdf) -> Option<DateZ> {
        DateZ::from_of(year, mdf.to_of())
    }

    /// Makes a new `DateZ` from year, month and day.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// Returns `None` on the out-of-range date, invalid month and/or day.
    pub fn from_ymd(year: int, month: uint, day: uint) -> Option<DateZ> {
        let flags = YearFlags::from_year(year);
        DateZ::from_mdf(year, Mdf::new(month, day, flags))
    }

    /// Makes a new `DateZ` from year and day of year (DOY or "ordinal").
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// Returns `None` on the out-of-range date and/or invalid DOY.
    pub fn from_yo(year: int, ordinal: uint) -> Option<DateZ> {
        let flags = YearFlags::from_year(year);
        DateZ::from_of(year, Of::new(ordinal, flags))
    }

    /// Makes a new `DateZ` from ISO week date (year and week number) and day of the week (DOW).
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    /// The resulting `DateZ` may have a different year from the input year.
    ///
    /// Returns `None` on the out-of-range date and/or invalid week number.
    pub fn from_isoywd(year: int, week: uint, weekday: Weekday) -> Option<DateZ> {
        let flags = YearFlags::from_year(year);
        let nweeks = flags.nisoweeks();
        if 1 <= week && week <= nweeks {
            // ordinal = week ordinal - delta
            let weekord = week * 7 + weekday as uint;
            let delta = flags.isoweek_delta();
            if weekord <= delta { // ordinal < 1, previous year
                let prevflags = YearFlags::from_year(year - 1);
                DateZ::from_of(year - 1, Of::new(weekord + prevflags.ndays() - delta, prevflags))
            } else {
                let ordinal = weekord - delta;
                let ndays = flags.ndays();
                if ordinal <= ndays { // this year
                    DateZ::from_of(year, Of::new(ordinal, flags))
                } else { // ordinal > ndays, next year
                    let nextflags = YearFlags::from_year(year + 1);
                    DateZ::from_of(year + 1, Of::new(ordinal - ndays, nextflags))
                }
            }
        } else {
            None
        }
    }

    /// Returns the packed month-day-flags.
    #[inline]
    fn mdf(&self) -> Mdf {
        self.of().to_mdf()
    }

    /// Returns the packed ordinal-flags.
    #[inline]
    fn of(&self) -> Of {
        Of((self.ymdf & 0b1111_11111_1111) as uint)
    }

    /// Makes a new `DateZ` with the packed month-day-flags changed.
    ///
    /// Returns `None` when the resulting `DateZ` would be invalid.
    #[inline]
    fn with_mdf(&self, mdf: Mdf) -> Option<DateZ> {
        self.with_of(mdf.to_of())
    }

    /// Makes a new `DateZ` with the packed ordinal-flags changed.
    ///
    /// Returns `None` when the resulting `DateZ` would be invalid.
    #[inline]
    fn with_of(&self, of: Of) -> Option<DateZ> {
        if of.valid() {
            let Of(of) = of;
            Some(DateZ { ymdf: (self.ymdf & !0b111111111_1111) | of as DateImpl })
        } else {
            None
        }
    }

    #[inline]
    pub fn succ(&self) -> Option<DateZ> {
        self.with_of(self.of().succ()).or_else(|| DateZ::from_ymd(self.year() + 1, 1, 1))
    }

    #[inline]
    pub fn pred(&self) -> Option<DateZ> {
        self.with_of(self.of().pred()).or_else(|| DateZ::from_ymd(self.year() - 1, 12, 31))
    }
}

impl Datelike for DateZ {
    #[inline] fn year(&self) -> int { (self.ymdf >> 13) as int }
    #[inline] fn month(&self) -> uint { self.mdf().month() }
    #[inline] fn month0(&self) -> uint { self.mdf().month() - 1 }
    #[inline] fn day(&self) -> uint { self.mdf().day() }
    #[inline] fn day0(&self) -> uint { self.mdf().day() - 1 }
    #[inline] fn ordinal(&self) -> uint { self.of().ordinal() }
    #[inline] fn ordinal0(&self) -> uint { self.of().ordinal() - 1 }
    #[inline] fn weekday(&self) -> Weekday { self.of().weekday() }

    fn isoweekdate(&self) -> (int, uint, Weekday) {
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
    fn with_year(&self, year: int) -> Option<DateZ> {
        // we need to operate with `mdf` since we should keep the month and day number as is
        let mdf = self.mdf();

        // adjust the flags as needed
        let flags = YearFlags::from_year(year);
        let mdf = mdf.with_flags(flags);

        DateZ::from_mdf(year, mdf)
    }

    #[inline]
    fn with_month(&self, month: uint) -> Option<DateZ> {
        self.with_mdf(self.mdf().with_month(month))
    }

    #[inline]
    fn with_month0(&self, month0: uint) -> Option<DateZ> {
        self.with_mdf(self.mdf().with_month(month0 + 1))
    }

    #[inline]
    fn with_day(&self, day: uint) -> Option<DateZ> {
        self.with_mdf(self.mdf().with_day(day))
    }

    #[inline]
    fn with_day0(&self, day0: uint) -> Option<DateZ> {
        self.with_mdf(self.mdf().with_day(day0 + 1))
    }

    #[inline]
    fn with_ordinal(&self, ordinal: uint) -> Option<DateZ> {
        self.with_of(self.of().with_ordinal(ordinal))
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: uint) -> Option<DateZ> {
        self.with_of(self.of().with_ordinal(ordinal0 + 1))
    }
}

impl Add<Duration,DateZ> for DateZ {
    fn add(&self, rhs: &Duration) -> DateZ {
        // TODO overflow

        let year = self.year();
        let (mut year_div_400, year_mod_400) = year.div_mod_floor(&400);
        let cycle = internals::yo_to_cycle(year_mod_400 as uint, self.of().ordinal());
        let cycle = cycle as int + rhs.ndays();
        let (cycle_div_400y, cycle) = cycle.div_mod_floor(&146097);
        year_div_400 += cycle_div_400y;

        let (year_mod_400, ordinal) = internals::cycle_to_yo(cycle as uint);
        let flags = unsafe { YearFlags::from_year_mod_400(year_mod_400 as int) };
        DateZ::from_of(year_div_400 * 400 + year_mod_400 as int, Of::new(ordinal, flags)).unwrap()
    }
}

/*
// Rust issue #7590, the current coherence checker can't handle multiple Add impls
impl Add<DateZ,DateZ> for Duration {
    #[inline]
    fn add(&self, rhs: &DateZ) -> DateZ { rhs.add(self) }
}
*/

impl Sub<DateZ,Duration> for DateZ {
    fn sub(&self, rhs: &DateZ) -> Duration {
        let year1 = self.year();
        let year2 = rhs.year();
        let (year1_div_400, year1_mod_400) = year1.div_mod_floor(&400);
        let (year2_div_400, year2_mod_400) = year2.div_mod_floor(&400);
        let cycle1 = internals::yo_to_cycle(year1_mod_400 as uint, self.of().ordinal()) as int;
        let cycle2 = internals::yo_to_cycle(year2_mod_400 as uint, rhs.of().ordinal()) as int;
        Duration::days((year1_div_400 - year2_div_400) * 146097 + (cycle1 - cycle2))
    }
}

impl fmt::Show for DateZ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let year = self.year();
        if 0 <= year && year <= 9999 {
            write!(f.buf, "{:04}-{:02}-{:02}", year, self.month(), self.day())
        } else {
            // ISO 8601 requires the explicit sign for out-of-range years
            write!(f.buf, "{:+05}-{:02}-{:02}", year, self.month(), self.day())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use duration::Duration;
    use std::{int, uint};
    use std::iter::range_inclusive;

    #[test]
    fn test_date_from_ymd() {
        assert!(DateZ::from_ymd(2012, 0, 1).is_none());
        assert!(DateZ::from_ymd(2012, 1, 1).is_some());
        assert!(DateZ::from_ymd(2012, 2, 29).is_some());
        assert!(DateZ::from_ymd(2014, 2, 29).is_none());
        assert!(DateZ::from_ymd(2014, 3, 0).is_none());
        assert!(DateZ::from_ymd(2014, 3, 1).is_some());
        assert!(DateZ::from_ymd(2014, 3, 31).is_some());
        assert!(DateZ::from_ymd(2014, 3, 32).is_none());
        assert!(DateZ::from_ymd(2014, 12, 31).is_some());
        assert!(DateZ::from_ymd(2014, 13, 1).is_none());
    }

    #[test]
    fn test_date_from_yo() {
        assert!(DateZ::from_yo(2012, 0).is_none());
        assert_eq!(DateZ::from_yo(2012, 1), DateZ::from_ymd(2012, 1, 1));
        assert_eq!(DateZ::from_yo(2012, 2), DateZ::from_ymd(2012, 1, 2));
        assert_eq!(DateZ::from_yo(2012, 32), DateZ::from_ymd(2012, 2, 1));
        assert_eq!(DateZ::from_yo(2012, 60), DateZ::from_ymd(2012, 2, 29));
        assert_eq!(DateZ::from_yo(2012, 61), DateZ::from_ymd(2012, 3, 1));
        assert_eq!(DateZ::from_yo(2012, 100), DateZ::from_ymd(2012, 4, 9));
        assert_eq!(DateZ::from_yo(2012, 200), DateZ::from_ymd(2012, 7, 18));
        assert_eq!(DateZ::from_yo(2012, 300), DateZ::from_ymd(2012, 10, 26));
        assert_eq!(DateZ::from_yo(2012, 366), DateZ::from_ymd(2012, 12, 31));
        assert!(DateZ::from_yo(2012, 367).is_none());

        assert!(DateZ::from_yo(2014, 0).is_none());
        assert_eq!(DateZ::from_yo(2014, 1), DateZ::from_ymd(2014, 1, 1));
        assert_eq!(DateZ::from_yo(2014, 2), DateZ::from_ymd(2014, 1, 2));
        assert_eq!(DateZ::from_yo(2014, 32), DateZ::from_ymd(2014, 2, 1));
        assert_eq!(DateZ::from_yo(2014, 59), DateZ::from_ymd(2014, 2, 28));
        assert_eq!(DateZ::from_yo(2014, 60), DateZ::from_ymd(2014, 3, 1));
        assert_eq!(DateZ::from_yo(2014, 100), DateZ::from_ymd(2014, 4, 10));
        assert_eq!(DateZ::from_yo(2014, 200), DateZ::from_ymd(2014, 7, 19));
        assert_eq!(DateZ::from_yo(2014, 300), DateZ::from_ymd(2014, 10, 27));
        assert_eq!(DateZ::from_yo(2014, 365), DateZ::from_ymd(2014, 12, 31));
        assert!(DateZ::from_yo(2014, 366).is_none());
    }

    #[test]
    fn test_date_from_isoywd() {
        assert!(DateZ::from_isoywd(2004, 0, Sun).is_none());
        assert_eq!(DateZ::from_isoywd(2004, 1, Mon), DateZ::from_ymd(2003, 12, 29));
        assert_eq!(DateZ::from_isoywd(2004, 1, Sun), DateZ::from_ymd(2004, 1, 4));
        assert_eq!(DateZ::from_isoywd(2004, 2, Mon), DateZ::from_ymd(2004, 1, 5));
        assert_eq!(DateZ::from_isoywd(2004, 2, Sun), DateZ::from_ymd(2004, 1, 11));
        assert_eq!(DateZ::from_isoywd(2004, 52, Mon), DateZ::from_ymd(2004, 12, 20));
        assert_eq!(DateZ::from_isoywd(2004, 52, Sun), DateZ::from_ymd(2004, 12, 26));
        assert_eq!(DateZ::from_isoywd(2004, 53, Mon), DateZ::from_ymd(2004, 12, 27));
        assert_eq!(DateZ::from_isoywd(2004, 53, Sun), DateZ::from_ymd(2005, 1, 2));
        assert!(DateZ::from_isoywd(2004, 54, Mon).is_none());

        assert!(DateZ::from_isoywd(2011, 0, Sun).is_none());
        assert_eq!(DateZ::from_isoywd(2011, 1, Mon), DateZ::from_ymd(2011, 1, 3));
        assert_eq!(DateZ::from_isoywd(2011, 1, Sun), DateZ::from_ymd(2011, 1, 9));
        assert_eq!(DateZ::from_isoywd(2011, 2, Mon), DateZ::from_ymd(2011, 1, 10));
        assert_eq!(DateZ::from_isoywd(2011, 2, Sun), DateZ::from_ymd(2011, 1, 16));

        assert_eq!(DateZ::from_isoywd(2018, 51, Mon), DateZ::from_ymd(2018, 12, 17));
        assert_eq!(DateZ::from_isoywd(2018, 51, Sun), DateZ::from_ymd(2018, 12, 23));
        assert_eq!(DateZ::from_isoywd(2018, 52, Mon), DateZ::from_ymd(2018, 12, 24));
        assert_eq!(DateZ::from_isoywd(2018, 52, Sun), DateZ::from_ymd(2018, 12, 30));
        assert!(DateZ::from_isoywd(2018, 53, Mon).is_none());
    }

    #[test]
    fn test_date_from_isoymd_and_isoweekdate() {
        for year in range_inclusive(2000i, 2400) {
            for week in range_inclusive(1u, 53) {
                for &weekday in [Mon, Tue, Wed, Thu, Fri, Sat, Sun].iter() {
                    let d = DateZ::from_isoywd(year, week, weekday);
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

        for year in range_inclusive(2000i, 2400) {
            for month in range_inclusive(1u, 12) {
                for day in range_inclusive(1u, 31) {
                    let d = DateZ::from_ymd(year, month, day);
                    if d.is_some() {
                        let d = d.unwrap();
                        let (year_, week_, weekday_) = d.isoweekdate();
                        let d_ = DateZ::from_isoywd(year_, week_, weekday_).unwrap();
                        assert_eq!(d, d_);
                    }
                }
            }
        }
    }

    #[test]
    fn test_date_fields() {
        fn check(year: int, month: uint, day: uint, ordinal: uint) {
            let d1 = DateZ::from_ymd(year, month, day);
            assert!(d1.is_some());
            assert_eq!(d1.unwrap().year(), year);
            assert_eq!(d1.unwrap().month(), month);
            assert_eq!(d1.unwrap().day(), day);
            assert_eq!(d1.unwrap().ordinal(), ordinal);

            let d2 = DateZ::from_yo(year, ordinal);
            assert!(d2.is_some());
            assert_eq!(d2.unwrap().year(), year);
            assert_eq!(d2.unwrap().month(), month);
            assert_eq!(d2.unwrap().day(), day);
            assert_eq!(d2.unwrap().ordinal(), ordinal);

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
        assert_eq!(DateZ::from_ymd(1582, 10, 15).unwrap().weekday(), Fri);
        assert_eq!(DateZ::from_ymd(1875, 5, 20).unwrap().weekday(), Thu); // ISO 8601 reference date
        assert_eq!(DateZ::from_ymd(2000, 1, 1).unwrap().weekday(), Sat);
    }

    #[test]
    fn test_date_with_fields() {
        let d = DateZ::from_ymd(2000, 2, 29).unwrap();
        assert_eq!(d.with_year(-400), DateZ::from_ymd(-400, 2, 29));
        assert_eq!(d.with_year(-100), None);
        assert_eq!(d.with_year(1600), DateZ::from_ymd(1600, 2, 29));
        assert_eq!(d.with_year(1900), None);
        assert_eq!(d.with_year(2000), DateZ::from_ymd(2000, 2, 29));
        assert_eq!(d.with_year(2001), None);
        assert_eq!(d.with_year(2004), DateZ::from_ymd(2004, 2, 29));
        assert_eq!(d.with_year(int::MAX), None);

        let d = DateZ::from_ymd(2000, 4, 30).unwrap();
        assert_eq!(d.with_month(0), None);
        assert_eq!(d.with_month(1), DateZ::from_ymd(2000, 1, 30));
        assert_eq!(d.with_month(2), None);
        assert_eq!(d.with_month(3), DateZ::from_ymd(2000, 3, 30));
        assert_eq!(d.with_month(4), DateZ::from_ymd(2000, 4, 30));
        assert_eq!(d.with_month(12), DateZ::from_ymd(2000, 12, 30));
        assert_eq!(d.with_month(13), None);
        assert_eq!(d.with_month(uint::MAX), None);

        let d = DateZ::from_ymd(2000, 2, 8).unwrap();
        assert_eq!(d.with_day(0), None);
        assert_eq!(d.with_day(1), DateZ::from_ymd(2000, 2, 1));
        assert_eq!(d.with_day(29), DateZ::from_ymd(2000, 2, 29));
        assert_eq!(d.with_day(30), None);
        assert_eq!(d.with_day(uint::MAX), None);

        let d = DateZ::from_ymd(2000, 5, 5).unwrap();
        assert_eq!(d.with_ordinal(0), None);
        assert_eq!(d.with_ordinal(1), DateZ::from_ymd(2000, 1, 1));
        assert_eq!(d.with_ordinal(60), DateZ::from_ymd(2000, 2, 29));
        assert_eq!(d.with_ordinal(61), DateZ::from_ymd(2000, 3, 1));
        assert_eq!(d.with_ordinal(366), DateZ::from_ymd(2000, 12, 31));
        assert_eq!(d.with_ordinal(367), None);
        assert_eq!(d.with_ordinal(uint::MAX), None);
    }

    #[test]
    fn test_date_ndays_from_ce() {
        assert_eq!(DateZ::from_ymd(1, 1, 1).unwrap().ndays_from_ce(), 1);

        for year in range_inclusive(-9999i, 10000) {
            assert_eq!(DateZ::from_ymd(year, 1, 1).unwrap().ndays_from_ce(),
                       DateZ::from_ymd(year - 1, 12, 31).unwrap().ndays_from_ce() + 1);
        }
    }

    #[test]
    fn test_date_succ() {
        assert_eq!(DateZ::from_ymd(2014, 5, 6).unwrap().succ(), DateZ::from_ymd(2014, 5, 7));
        assert_eq!(DateZ::from_ymd(2014, 5, 31).unwrap().succ(), DateZ::from_ymd(2014, 6, 1));
        assert_eq!(DateZ::from_ymd(2014, 12, 31).unwrap().succ(), DateZ::from_ymd(2015, 1, 1));
        assert_eq!(DateZ::from_ymd(2016, 2, 28).unwrap().succ(), DateZ::from_ymd(2016, 2, 29));
        assert_eq!(DateZ::from_ymd(MAX_YEAR, 12, 31).unwrap().succ(), None);
    }

    #[test]
    fn test_date_pred() {
        assert_eq!(DateZ::from_ymd(2016, 3, 1).unwrap().pred(), DateZ::from_ymd(2016, 2, 29));
        assert_eq!(DateZ::from_ymd(2015, 1, 1).unwrap().pred(), DateZ::from_ymd(2014, 12, 31));
        assert_eq!(DateZ::from_ymd(2014, 6, 1).unwrap().pred(), DateZ::from_ymd(2014, 5, 31));
        assert_eq!(DateZ::from_ymd(2014, 5, 7).unwrap().pred(), DateZ::from_ymd(2014, 5, 6));
        assert_eq!(DateZ::from_ymd(MIN_YEAR, 1, 1).unwrap().pred(), None);
    }

    #[test]
    fn test_date_add() {
        fn check((y1,m1,d1): (int, uint, uint), rhs: Duration, (y,m,d): (int, uint, uint)) {
            let lhs = DateZ::from_ymd(y1, m1, d1).unwrap();
            let sum = DateZ::from_ymd(y, m, d).unwrap();
            assert_eq!(lhs + rhs, sum);
            //assert_eq!(rhs + lhs, sum);
        }

        check((2014, 1, 1), Duration::zero(), (2014, 1, 1));
        check((2014, 1, 1), Duration::seconds(86399), (2014, 1, 1));
        check((2014, 1, 1), Duration::days(1), (2014, 1, 2));
        check((2014, 1, 1), Duration::days(-1), (2013, 12, 31));
        check((2014, 1, 1), Duration::days(364), (2014, 12, 31));
        check((2014, 1, 1), Duration::days(365*4 + 1), (2018, 1, 1));
        check((2014, 1, 1), Duration::days(365*400 + 97), (2414, 1, 1));

        check((-7, 1, 1), Duration::days(365*12 + 3), (5, 1, 1));
    }

    #[test]
    fn test_date_sub() {
        fn check((y1,m1,d1): (int, uint, uint), (y2,m2,d2): (int, uint, uint), diff: Duration) {
            let lhs = DateZ::from_ymd(y1, m1, d1).unwrap();
            let rhs = DateZ::from_ymd(y2, m2, d2).unwrap();
            assert_eq!(lhs - rhs, diff);
            assert_eq!(rhs - lhs, -diff);
        }

        check((2014, 1, 1), (2014, 1, 1), Duration::zero());
        check((2014, 1, 2), (2014, 1, 1), Duration::days(1));
        check((2014, 12, 31), (2014, 1, 1), Duration::days(364));
        check((2015, 1, 3), (2014, 1, 1), Duration::days(365 + 2));
        check((2018, 1, 1), (2014, 1, 1), Duration::days(365*4 + 1));
        check((2414, 1, 1), (2014, 1, 1), Duration::days(365*400 + 97));
    }

    #[test]
    fn test_date_fmt() {
        assert_eq!(DateZ::from_ymd(2012,  3, 4).unwrap().to_str(),  ~"2012-03-04");
        assert_eq!(DateZ::from_ymd(0,     3, 4).unwrap().to_str(),  ~"0000-03-04");
        assert_eq!(DateZ::from_ymd(-307,  3, 4).unwrap().to_str(), ~"-0307-03-04");
        assert_eq!(DateZ::from_ymd(12345, 3, 4).unwrap().to_str(), ~"+12345-03-04");
    }
}

/**
 * The internal implementation of the calendar and ordinal date.
 *
 * The current implementation is optimized for determining year, month, day and day of week. 
 * 4-bit `YearFlags` map to one of 14 possible classes of year in the Gregorian calendar,
 * which are included in every packed `DateZ` instance.
 * The conversion between the packed calendar date (`Mdf`) and the ordinal date (`Of`) is
 * based on the moderately-sized lookup table (~1.5KB)
 * and the packed representation is chosen for the efficient lookup.
 * Every internal data structure does not validate its input,
 * but the conversion keeps the valid value valid and the invalid value invalid
 * so that the user-facing `DateZ` can validate the input as late as possible.
 */
mod internals {
    use std::{i32, num, fmt};
    use num::Integer;
    pub use super::{Weekday, Sun, Mon, Tue, Wed, Thu, Fri, Sat};

    /// The internal date representation. This also includes the packed `Mdf` value.
    pub type DateImpl = i32;

    pub static MAX_YEAR: DateImpl = i32::MAX >> 13;
    pub static MIN_YEAR: DateImpl = i32::MIN >> 13;

    /// The year flags (aka the dominical letter).
    ///
    /// There are 14 possible classes of year in the Gregorian calendar:
    /// common and leap years starting with Monday through Sunday. 
    /// The `YearFlags` stores this information into 4 bits `abbb`,
    /// where `a` is `1` for the common year (simplifies the `Of` validation)
    /// and `bbb` is a non-zero `Weekday` (mapping `Mon` to 7) of the last day in the past year
    /// (simplifies the day of week calculation from the 1-based ordinal).
    #[deriving(Eq, TotalEq)]
    pub struct YearFlags(u8);

    pub static A: YearFlags = YearFlags(0o15); pub static AG: YearFlags = YearFlags(0o05);
    pub static B: YearFlags = YearFlags(0o14); pub static BA: YearFlags = YearFlags(0o04);
    pub static C: YearFlags = YearFlags(0o13); pub static CB: YearFlags = YearFlags(0o03);
    pub static D: YearFlags = YearFlags(0o12); pub static DC: YearFlags = YearFlags(0o02);
    pub static E: YearFlags = YearFlags(0o11); pub static ED: YearFlags = YearFlags(0o01);
    pub static F: YearFlags = YearFlags(0o17); pub static FE: YearFlags = YearFlags(0o07);
    pub static G: YearFlags = YearFlags(0o16); pub static GF: YearFlags = YearFlags(0o06);

    static YEAR_TO_FLAGS: [YearFlags, ..400] = [
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

    static YEAR_DELTAS: [u8, ..401] = [
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

    pub fn cycle_to_yo(cycle: uint) -> (uint, uint) {
        let (mut year_mod_400, mut ordinal0) = cycle.div_rem(&365);
        let delta = YEAR_DELTAS[year_mod_400] as uint;
        if ordinal0 < delta {
            year_mod_400 -= 1;
            ordinal0 += 365 - YEAR_DELTAS[year_mod_400] as uint;
        } else {
            ordinal0 -= delta;
        }
        (year_mod_400, ordinal0 + 1)
    }

    pub fn yo_to_cycle(year_mod_400: uint, ordinal: uint) -> uint {
        year_mod_400 * 365 + YEAR_DELTAS[year_mod_400] as uint + ordinal - 1
    }

    impl YearFlags {
        #[inline]
        pub fn from_year(year: int) -> YearFlags {
            let year = year.mod_floor(&400);
            unsafe { YearFlags::from_year_mod_400(year) }
        }

        #[inline]
        pub unsafe fn from_year_mod_400(year: int) -> YearFlags {
            YEAR_TO_FLAGS[year]
        }

        #[inline]
        pub fn ndays(&self) -> uint {
            let YearFlags(flags) = *self;
            366 - (flags >> 3) as uint
        }

        #[inline]
        pub fn isoweek_delta(&self) -> uint {
            let YearFlags(flags) = *self;
            let mut delta = flags as uint & 0b111;
            if delta < 3 { delta += 7; }
            delta
        }

        #[inline]
        pub fn nisoweeks(&self) -> uint {
            let YearFlags(flags) = *self;
            52 + ((0b00000100_00000110 >> flags as uint) & 1)
        }
    }

    impl fmt::Show for YearFlags {
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
                _ => write!(f.buf, "YearFlags({})", flags),
            }
        }
    }

    static MIN_OL: uint = 1 << 1;
    static MAX_OL: uint = 366 << 1; // larger than the non-leap last day `(365 << 1) | 1`
    static MIN_MDL: uint = (1 << 6) | (1 << 1);
    static MAX_MDL: uint = (12 << 6) | (31 << 1) | 1;

    static XX: i8 = -128;
    static MDL_TO_OL: [i8, ..MAX_MDL+1] = [
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

    static OL_TO_MDL: [u8, ..MAX_OL+1] = [
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
    #[deriving(Eq, Ord)]
    pub struct Of(uint);

    impl Of {
        #[inline]
        fn clamp_ordinal(ordinal: uint) -> uint {
            if ordinal > 366 {0} else {ordinal}
        }

        #[inline]
        pub fn new(ordinal: uint, YearFlags(flags): YearFlags) -> Of {
            let ordinal = Of::clamp_ordinal(ordinal);
            Of((ordinal << 4) | (flags as uint))
        }

        #[inline]
        pub fn from_mdf(Mdf(mdf): Mdf) -> Of {
            let mdl = mdf >> 3;
            match MDL_TO_OL.get(mdl) {
                Some(&v) => Of(mdf - ((v as int as uint & 0x3ff) << 3)),
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
        pub fn ordinal(&self) -> uint {
            let Of(of) = *self;
            (of >> 4) as uint
        }

        #[inline]
        pub fn with_ordinal(&self, ordinal: uint) -> Of {
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
            Of((of & !0b1111) | (flags as uint))
        }

        #[inline]
        pub fn weekday(&self) -> Weekday {
            let Of(of) = *self;
            num::from_uint(((of >> 4) + (of & 0b111)) % 7).unwrap()
        }

        #[inline]
        pub fn isoweekdate_raw(&self) -> (uint, Weekday) {
            // week ordinal = ordinal + delta
            let Of(of) = *self;
            let weekord = (of >> 4) + self.flags().isoweek_delta();
            (weekord / 7, num::from_uint(weekord % 7).unwrap())
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

    impl fmt::Show for Of {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let Of(of) = *self;
            write!(f.buf, "Of(({} << 4) | {:#04o} /*{}*/)",
                   of >> 4, of & 0b1111, YearFlags((of & 0b1111) as u8))
        }
    }

    /// Month, day of month and year flags: `(month << 9) | (day << 4) | flags`
    ///
    /// The whole bits except for the least 3 bits are referred as `Mdl`
    /// (month, day of month and leap flag),
    /// which is an index to the `MDL_TO_OL` lookup table.
    #[deriving(Eq, Ord)]
    pub struct Mdf(uint);

    impl Mdf {
        #[inline]
        fn clamp_month(month: uint) -> uint {
            if month > 12 {0} else {month}
        }

        #[inline]
        fn clamp_day(day: uint) -> uint {
            if day > 31 {0} else {day}
        }

        #[inline]
        pub fn new(month: uint, day: uint, YearFlags(flags): YearFlags) -> Mdf {
            let month = Mdf::clamp_month(month);
            let day = Mdf::clamp_day(day);
            Mdf((month << 9) | (day << 4) | (flags as uint))
        }

        #[inline]
        pub fn from_of(Of(of): Of) -> Mdf {
            let ol = of >> 3;
            match OL_TO_MDL.get(ol) {
                Some(&v) => Mdf(of + (v as uint << 3)),
                None => Mdf(0)
            }
        }

        #[inline]
        pub fn valid(&self) -> bool {
            let Mdf(mdf) = *self;
            let mdl = mdf >> 3;
            match MDL_TO_OL.get(mdl) {
                Some(&v) => v >= 0,
                None => false
            }
        }

        #[inline]
        pub fn month(&self) -> uint {
            let Mdf(mdf) = *self;
            (mdf >> 9) as uint
        }

        #[inline]
        pub fn with_month(&self, month: uint) -> Mdf {
            let month = Mdf::clamp_month(month);
            let Mdf(mdf) = *self;
            Mdf((mdf & 0b11111_1111) | (month << 9))
        }

        #[inline]
        pub fn day(&self) -> uint {
            let Mdf(mdf) = *self;
            ((mdf >> 4) & 0b11111) as uint
        }

        #[inline]
        pub fn with_day(&self, day: uint) -> Mdf {
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
            Mdf((mdf & !0b1111) | (flags as uint))
        }

        #[inline]
        pub fn to_of(&self) -> Of {
            Of::from_mdf(*self)
        }
    }

    impl fmt::Show for Mdf {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let Mdf(mdf) = *self;
            write!(f.buf, "Mdf(({} << 9) | ({} << 4) | {:#04o} /*{}*/)",
                   mdf >> 9, (mdf >> 4) & 0b11111, mdf & 0b1111, YearFlags((mdf & 0b1111) as u8))
        }
    }

    #[cfg(test)]
    mod tests {
        extern crate test;

        use super::*;
        use std::iter::range_inclusive;
        use std::uint;

        static NONLEAP_FLAGS: [YearFlags, ..7] = [A, B, C, D, E, F, G];
        static LEAP_FLAGS: [YearFlags, ..7] = [AG, BA, CB, DC, ED, FE, GF];
        static FLAGS: [YearFlags, ..14] = [A, B, C, D, E, F, G, AG, BA, CB, DC, ED, FE, GF];

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
        fn bench_year_flags_from_year(bh: &mut test::BenchHarness) {
            bh.iter(|| {
                for year in range(-999i, 1000) {
                    YearFlags::from_year(year);
                }
            });
        }

        #[test]
        fn test_of() {
            fn check(expected: bool, flags: YearFlags, ordinal1: uint, ordinal2: uint) {
                for ordinal in range_inclusive(ordinal1, ordinal2) {
                    let of = Of::new(ordinal, flags);
                    assert!(of.valid() == expected,
                            "ordinal {} = {} should be {} for dominical year {}",
                            ordinal, of, if expected {"valid"} else {"invalid"}, flags);
                }
            }

            for &flags in NONLEAP_FLAGS.iter() {
                check(false, flags, 0, 0);
                check(true, flags, 1, 365);
                check(false, flags, 366, 1024);
                check(false, flags, uint::MAX, uint::MAX);
            }

            for &flags in LEAP_FLAGS.iter() {
                check(false, flags, 0, 0);
                check(true, flags, 1, 366);
                check(false, flags, 367, 1024);
                check(false, flags, uint::MAX, uint::MAX);
            }
        }

        #[test]
        fn test_mdf_valid() {
            fn check(expected: bool, flags: YearFlags, month1: uint, day1: uint,
                     month2: uint, day2: uint) {
                for month in range_inclusive(month1, month2) {
                    for day in range_inclusive(day1, day2) {
                        let mdf = Mdf::new(month, day, flags);
                        assert!(mdf.valid() == expected,
                                "month {} day {} = {} should be {} for dominical year {}",
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
                check(false, flags, uint::MAX, 0, uint::MAX, 1024);
                check(false, flags, 0, uint::MAX, 16, uint::MAX);
                check(false, flags, uint::MAX, uint::MAX, uint::MAX, uint::MAX);
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
                check(false, flags, uint::MAX, 0, uint::MAX, 1024);
                check(false, flags, 0, uint::MAX, 16, uint::MAX);
                check(false, flags, uint::MAX, uint::MAX, uint::MAX, uint::MAX);
            }
        }

        #[test]
        fn test_of_fields() {
            for &flags in FLAGS.iter() {
                for ordinal in range_inclusive(1u, 366) {
                    let of = Of::new(ordinal, flags);
                    if of.valid() {
                        assert_eq!(of.ordinal(), ordinal);
                    }
                }
            }
        }

        #[test]
        fn test_of_with_fields() {
            fn check(flags: YearFlags, ordinal: uint) {
                let of = Of::new(ordinal, flags);

                for ordinal in range_inclusive(0u, 1024) {
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
            assert_eq!(Of::new(1, A).weekday(), Sun);
            assert_eq!(Of::new(1, B).weekday(), Sat);
            assert_eq!(Of::new(1, C).weekday(), Fri);
            assert_eq!(Of::new(1, D).weekday(), Thu);
            assert_eq!(Of::new(1, E).weekday(), Wed);
            assert_eq!(Of::new(1, F).weekday(), Tue);
            assert_eq!(Of::new(1, G).weekday(), Mon);
            assert_eq!(Of::new(1, AG).weekday(), Sun);
            assert_eq!(Of::new(1, BA).weekday(), Sat);
            assert_eq!(Of::new(1, CB).weekday(), Fri);
            assert_eq!(Of::new(1, DC).weekday(), Thu);
            assert_eq!(Of::new(1, ED).weekday(), Wed);
            assert_eq!(Of::new(1, FE).weekday(), Tue);
            assert_eq!(Of::new(1, GF).weekday(), Mon);

            for &flags in FLAGS.iter() {
                let mut prev = Of::new(1, flags).weekday();
                for ordinal in range_inclusive(2u, flags.ndays()) {
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
                for month in range_inclusive(1u, 12) {
                    for day in range_inclusive(1u, 31) {
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
            fn check(flags: YearFlags, month: uint, day: uint) {
                let mdf = Mdf::new(month, day, flags);

                for month in range_inclusive(0u, 16) {
                    let mdf = mdf.with_month(month);
                    assert_eq!(mdf.valid(), Mdf::new(month, day, flags).valid());
                    if mdf.valid() {
                        assert_eq!(mdf.month(), month);
                        assert_eq!(mdf.day(), day);
                    }
                }

                for day in range_inclusive(0u, 1024) {
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
            for i in range_inclusive(0u, 8192) {
                let of = Of(i);
                assert_eq!(of.valid(), of.to_mdf().valid());
            }
        }

        #[test]
        fn test_mdf_to_of() {
            for i in range_inclusive(0u, 8192) {
                let mdf = Mdf(i);
                assert_eq!(mdf.valid(), mdf.to_of().valid());
            }
        }

        #[test]
        fn test_of_to_mdf_to_of() {
            for i in range_inclusive(0u, 8192) {
                let of = Of(i);
                if of.valid() {
                    assert_eq!(of, of.to_mdf().to_of());
                }
            }
        }

        #[test]
        fn test_mdf_to_of_to_mdf() {
            for i in range_inclusive(0u, 8192) {
                let mdf = Mdf(i);
                if mdf.valid() {
                    assert_eq!(mdf, mdf.to_of().to_mdf());
                }
            }
        }
    }
}

