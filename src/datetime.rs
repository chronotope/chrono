// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 date and time.
 */

use std::fmt;
use duration::Duration;
use time::{Timelike, TimeZ};
use date::{Datelike, DateZ, Weekday};

#[deriving(PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub fn from_ymdhms(year: i32, month: u32, day: u32,
                       hour: u32, min: u32, sec: u32) -> DateTimeZ {
        let dt = DateTimeZ::from_ymdhms_opt(year, month, day, hour, min, sec);
        dt.expect("invalid or out-of-range date or time")
    }

    #[inline]
    pub fn from_ymdhms_opt(year: i32, month: u32, day: u32,
                           hour: u32, min: u32, sec: u32) -> Option<DateTimeZ> {
        match (DateZ::from_ymd_opt(year, month, day), TimeZ::from_hms_opt(hour, min, sec)) {
            (Some(d), Some(t)) => Some(DateTimeZ::new(d, t)),
            (_, _) => None,
        }
    }

    #[inline]
    pub fn from_yohms(year: i32, ordinal: u32,
                      hour: u32, min: u32, sec: u32) -> DateTimeZ {
        let dt = DateTimeZ::from_yohms_opt(year, ordinal, hour, min, sec);
        dt.expect("invalid or out-of-range date or time")
    }

    #[inline]
    pub fn from_yohms_opt(year: i32, ordinal: u32,
                          hour: u32, min: u32, sec: u32) -> Option<DateTimeZ> {
        match (DateZ::from_yo_opt(year, ordinal), TimeZ::from_hms_opt(hour, min, sec)) {
            (Some(d), Some(t)) => Some(DateTimeZ::new(d, t)),
            (_, _) => None,
        }
    }

    #[inline]
    pub fn from_isoywdhms(year: i32, week: u32, weekday: Weekday,
                          hour: u32, min: u32, sec: u32) -> DateTimeZ {
        let dt = DateTimeZ::from_isoywdhms_opt(year, week, weekday, hour, min, sec);
        dt.expect("invalid or out-of-range date or time")
    }

    #[inline]
    pub fn from_isoywdhms_opt(year: i32, week: u32, weekday: Weekday,
                              hour: u32, min: u32, sec: u32) -> Option<DateTimeZ> {
        match (DateZ::from_isoywd_opt(year, week, weekday), TimeZ::from_hms_opt(hour, min, sec)) {
            (Some(d), Some(t)) => Some(DateTimeZ::new(d, t)),
            (_, _) => None,
        }
    }

    #[inline]
    pub fn date(&self) -> DateZ {
        self.date
    }

    #[inline]
    pub fn time(&self) -> TimeZ {
        self.time
    }

    /// Returns the number of non-leap seconds since January 1, 1970 0:00:00.
    /// Note that this does *not* account for the timezone!
    #[inline]
    pub fn nseconds_from_unix_epoch(&self) -> i64 {
        let ndays = self.date.ndays_from_ce() as i64;
        let nseconds = self.time.nseconds_from_midnight() as i64;
        (ndays - 719163) * 86400 + nseconds
    }
}

impl Datelike for DateTimeZ {
    #[inline] fn year(&self) -> i32 { self.date.year() }
    #[inline] fn month(&self) -> u32 { self.date.month() }
    #[inline] fn month0(&self) -> u32 { self.date.month0() }
    #[inline] fn day(&self) -> u32 { self.date.day() }
    #[inline] fn day0(&self) -> u32 { self.date.day0() }
    #[inline] fn ordinal(&self) -> u32 { self.date.ordinal() }
    #[inline] fn ordinal0(&self) -> u32 { self.date.ordinal0() }
    #[inline] fn weekday(&self) -> Weekday { self.date.weekday() }
    #[inline] fn isoweekdate(&self) -> (i32, u32, Weekday) { self.date.isoweekdate() }

    #[inline]
    fn with_year(&self, year: i32) -> Option<DateTimeZ> {
        self.date.with_year(year).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_month(&self, month: u32) -> Option<DateTimeZ> {
        self.date.with_month(month).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Option<DateTimeZ> {
        self.date.with_month0(month0).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_day(&self, day: u32) -> Option<DateTimeZ> {
        self.date.with_day(day).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Option<DateTimeZ> {
        self.date.with_day0(day0).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<DateTimeZ> {
        self.date.with_ordinal(ordinal).map(|d| DateTimeZ { date: d, ..*self })
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<DateTimeZ> {
        self.date.with_ordinal0(ordinal0).map(|d| DateTimeZ { date: d, ..*self })
    }
}

impl Timelike for DateTimeZ {
    #[inline] fn hour(&self) -> u32 { self.time.hour() }
    #[inline] fn minute(&self) -> u32 { self.time.minute() }
    #[inline] fn second(&self) -> u32 { self.time.second() }
    #[inline] fn nanosecond(&self) -> u32 { self.time.nanosecond() }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<DateTimeZ> {
        self.time.with_hour(hour).map(|t| DateTimeZ { time: t, ..*self })
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<DateTimeZ> {
        self.time.with_minute(min).map(|t| DateTimeZ { time: t, ..*self })
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<DateTimeZ> {
        self.time.with_second(sec).map(|t| DateTimeZ { time: t, ..*self })
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<DateTimeZ> {
        self.time.with_nanosecond(nano).map(|t| DateTimeZ { time: t, ..*self })
    }
}

impl Add<Duration,DateTimeZ> for DateTimeZ {
    fn add(&self, rhs: &Duration) -> DateTimeZ {
        let mut date = self.date + *rhs;
        let time = self.time + *rhs;
        if time < self.time {
            // since the time portion of the duration is always positive and bounded,
            // this condition always means that the time part has been overflowed.
            date = date.succ();
        }
        DateTimeZ { date: date, time: time }
    }
}

/*
// Rust issue #7590, the current coherence checker can't handle multiple Add impls
impl Add<DateTimeZ,DateTimeZ> for Duration {
    #[inline]
    fn add(&self, rhs: &DateTimeZ) -> DateTimeZ { rhs.add(self) }
}
*/

impl Sub<DateTimeZ,Duration> for DateTimeZ {
    fn sub(&self, rhs: &DateTimeZ) -> Duration {
        (self.date - rhs.date) + (self.time - rhs.time)
    }
}

impl fmt::Show for DateTimeZ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}T{}", self.date, self.time)
    }
}

#[cfg(test)]
mod tests {
    use super::DateTimeZ;
    use duration::Duration;

    #[test]
    fn test_datetime_add() {
        let ymdhms = |y,m,d,h,n,s| DateTimeZ::from_ymdhms(y,m,d,h,n,s);
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) + Duration::seconds(3600 + 60 + 1),
                   ymdhms(2014, 5, 6, 8, 9, 10));
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) + Duration::seconds(86399),
                   ymdhms(2014, 5, 7, 7, 8, 8));
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) + Duration::seconds(86400 * 10),
                   ymdhms(2014, 5, 16, 7, 8, 9));
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) + Duration::seconds(-86400 * 10),
                   ymdhms(2014, 4, 26, 7, 8, 9));
    }

    #[test]
    fn test_datetime_sub() {
        let ymdhms = |y,m,d,h,n,s| DateTimeZ::from_ymdhms(y,m,d,h,n,s);
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) - ymdhms(2014, 5, 6, 7, 8, 9), Duration::zero());
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 10) - ymdhms(2014, 5, 6, 7, 8, 9),
                   Duration::seconds(1));
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) - ymdhms(2014, 5, 6, 7, 8, 10),
                   Duration::seconds(-1));
        assert_eq!(ymdhms(2014, 5, 7, 7, 8, 9) - ymdhms(2014, 5, 6, 7, 8, 10),
                   Duration::seconds(86399));
        assert_eq!(ymdhms(2001, 9, 9, 1, 46, 39) - ymdhms(1970, 1, 1, 0, 0, 0),
                   Duration::seconds(999_999_999));
    }

    #[test]
    fn test_datetime_nseconds_from_unix_epoch() {
        let to_timestamp =
            |y,m,d,h,n,s| DateTimeZ::from_ymdhms(y,m,d,h,n,s).nseconds_from_unix_epoch();
        assert_eq!(to_timestamp(1969, 12, 31, 23, 59, 59), -1);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 0), 0);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 1), 1);
        assert_eq!(to_timestamp(2001, 9, 9, 1, 46, 40), 1_000_000_000);
        assert_eq!(to_timestamp(2038, 1, 19, 3, 14, 7), 0x7fffffff);
    }
}

