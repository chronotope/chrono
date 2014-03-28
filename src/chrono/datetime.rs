/*!
 * ISO 8601 date and time.
 */

use std::fmt;
use time::{Timelike, TimeZ};
use date::{Datelike, DateZ, Weekday};

#[deriving(Eq, TotalEq, Ord, TotalOrd, Hash)]
pub struct DateTimeZ {
    date: DateZ,
    time: TimeZ,
}

impl DateTimeZ {
    #[inline]
    pub fn new(date: DateZ, time: TimeZ) -> DateTimeZ {
        DateTimeZ { date: date, time: time }
    }

    #[inline]
    pub fn from_ymdhms(year: int, month: uint, day: uint,
                       hour: uint, min: uint, sec: uint) -> Option<DateTimeZ> {
        match (DateZ::from_ymd(year, month, day), TimeZ::from_hms(hour, min, sec)) {
            (Some(d), Some(t)) => Some(DateTimeZ::new(d, t)),
            (_, _) => None,
        }
    }

    #[inline]
    pub fn from_yohms(year: int, ordinal: uint,
                      hour: uint, min: uint, sec: uint) -> Option<DateTimeZ> {
        match (DateZ::from_yo(year, ordinal), TimeZ::from_hms(hour, min, sec)) {
            (Some(d), Some(t)) => Some(DateTimeZ::new(d, t)),
            (_, _) => None,
        }
    }

    #[inline]
    pub fn from_isoywdhms(year: int, week: uint, weekday: Weekday,
                          hour: uint, min: uint, sec: uint) -> Option<DateTimeZ> {
        match (DateZ::from_isoywd(year, week, weekday), TimeZ::from_hms(hour, min, sec)) {
            (Some(d), Some(t)) => Some(DateTimeZ::new(d, t)),
            (_, _) => None,
        }
    }

    /// Returns the number of non-leap seconds since January 1, 1970 0:00:00.
    /// Note that this does *not* account for the timezone!
    #[inline]
    pub fn nseconds_from_unix_epoch(&self) -> int {
        (self.date.ndays_from_ce() - 719163) * 86400 + self.time.nseconds_from_midnight() as int
    }
}

impl Datelike for DateTimeZ {
    #[inline] fn year(&self) -> int { self.date.year() }
    #[inline] fn month(&self) -> uint { self.date.month() }
    #[inline] fn month0(&self) -> uint { self.date.month0() }
    #[inline] fn day(&self) -> uint { self.date.day() }
    #[inline] fn day0(&self) -> uint { self.date.day0() }
    #[inline] fn ordinal(&self) -> uint { self.date.ordinal() }
    #[inline] fn ordinal0(&self) -> uint { self.date.ordinal0() }
    #[inline] fn weekday(&self) -> Weekday { self.date.weekday() }
    #[inline] fn isoweekdate(&self) -> (int, uint, Weekday) { self.date.isoweekdate() }

    #[inline]
    fn with_year(&self, year: int) -> Option<DateTimeZ> {
        self.date.with_year(year).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_month(&self, month: uint) -> Option<DateTimeZ> {
        self.date.with_month(month).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_month0(&self, month0: uint) -> Option<DateTimeZ> {
        self.date.with_month0(month0).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_day(&self, day: uint) -> Option<DateTimeZ> {
        self.date.with_day(day).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_day0(&self, day0: uint) -> Option<DateTimeZ> {
        self.date.with_day0(day0).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_ordinal(&self, ordinal: uint) -> Option<DateTimeZ> {
        self.date.with_ordinal(ordinal).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: uint) -> Option<DateTimeZ> {
        self.date.with_ordinal0(ordinal0).map(|d| DateTimeZ { date: d, ..*self })
    }
}

impl Timelike for DateTimeZ {
    #[inline] fn hour(&self) -> uint { self.time.hour() }
    #[inline] fn minute(&self) -> uint { self.time.minute() }
    #[inline] fn second(&self) -> uint { self.time.second() }
    #[inline] fn nanosecond(&self) -> uint { self.time.nanosecond() }

    #[inline]
    fn with_hour(&self, hour: uint) -> Option<DateTimeZ> {
        self.time.with_hour(hour).map(|t| DateTimeZ { time: t, ..*self })
    }

    #[inline]
    fn with_minute(&self, min: uint) -> Option<DateTimeZ> {
        self.time.with_minute(min).map(|t| DateTimeZ { time: t, ..*self })
    }

    #[inline]
    fn with_second(&self, sec: uint) -> Option<DateTimeZ> {
        self.time.with_second(sec).map(|t| DateTimeZ { time: t, ..*self })
    }

    #[inline]
    fn with_nanosecond(&self, nano: uint) -> Option<DateTimeZ> {
        self.time.with_nanosecond(nano).map(|t| DateTimeZ { time: t, ..*self })
    }
}

impl fmt::Show for DateTimeZ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}T{}", self.date, self.time)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_time_nseconds_from_unix_epoch() {
        let to_timestamp =
            |y,m,d,h,n,s| DateTimeZ::from_ymdhms(y,m,d,h,n,s).unwrap().nseconds_from_unix_epoch();
        assert_eq!(to_timestamp(1969, 12, 31, 23, 59, 59), -1);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 0), 0);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 1), 1);
        assert_eq!(to_timestamp(2001, 9, 9, 1, 46, 40), 1_000_000_000);
        assert_eq!(to_timestamp(2038, 1, 19, 3, 14, 7), 0x7fffffff);
    }
}

