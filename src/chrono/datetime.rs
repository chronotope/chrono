/*!
 * ISO 8601 date and time.
 */

use std::fmt;
use time::Time;
use date::{Date, Weekday};

#[deriving(Eq, TotalEq, Ord, TotalOrd, Hash)]
pub struct DateTime {
    date: Date,
    time: Time,
}

impl DateTime {
    #[inline]
    pub fn new(date: Date, time: Time) -> DateTime {
        DateTime { date: date, time: time }
    }

    #[inline]
    pub fn from_ymdhms(year: int, month: uint, day: uint,
                       hour: uint, min: uint, sec: uint) -> Option<DateTime> {
        match (Date::from_ymd(year, month, day), Time::from_hms(hour, min, sec)) {
            (Some(d), Some(t)) => Some(DateTime::new(d, t)),
            (_, _) => None,
        }
    }

    #[inline]
    pub fn from_yohms(year: int, ordinal: uint,
                      hour: uint, min: uint, sec: uint) -> Option<DateTime> {
        match (Date::from_yo(year, ordinal), Time::from_hms(hour, min, sec)) {
            (Some(d), Some(t)) => Some(DateTime::new(d, t)),
            (_, _) => None,
        }
    }

    #[inline]
    pub fn from_isoywdhms(year: int, week: uint, weekday: Weekday,
                          hour: uint, min: uint, sec: uint) -> Option<DateTime> {
        match (Date::from_isoywd(year, week, weekday), Time::from_hms(hour, min, sec)) {
            (Some(d), Some(t)) => Some(DateTime::new(d, t)),
            (_, _) => None,
        }
    }

    /// Returns the year number.
    #[inline]
    pub fn year(&self) -> int {
        self.date.year()
    }

    /// Returns the absolute year number starting from 1 with a boolean flag,
    /// which is false when the year predates the epoch (BCE/BC) and true otherwise (CE/AD).
    #[inline]
    pub fn year_ce(&self) -> (bool, uint) {
        self.date.year_ce()
    }

    /// Returns the month number starting from 1.
    #[inline]
    pub fn month(&self) -> uint {
        self.date.month()
    }

    /// Returns the month number starting from 0.
    #[inline]
    pub fn month0(&self) -> uint {
        self.date.month0()
    }

    /// Returns the day of month starting from 1.
    #[inline]
    pub fn day(&self) -> uint {
        self.date.day()
    }

    /// Returns the day of month starting from 0.
    #[inline]
    pub fn day0(&self) -> uint {
        self.date.day0()
    }

    /// Returns the day of year starting from 1.
    #[inline]
    pub fn ordinal(&self) -> uint {
        self.date.ordinal()
    }

    /// Returns the day of year starting from 0.
    #[inline]
    pub fn ordinal0(&self) -> uint {
        self.date.ordinal0()
    }

    /// Returns the day of week.
    #[inline]
    pub fn weekday(&self) -> Weekday {
        self.date.weekday()
    }

    /// Returns the ISO week date: an adjusted year, week number and day of week.
    /// The adjusted year may differ from that of the calendar date.
    #[inline]
    pub fn isoweekdate(&self) -> (int, uint, Weekday) {
        self.date.isoweekdate()
    }

    /// Returns the hour number from 0 to 23.
    #[inline]
    pub fn hour(&self) -> uint {
        self.time.hour()
    }

    /// Returns the hour number from 1 to 12 with a boolean flag,
    /// which is false for AM and true for PM.
    #[inline]
    pub fn hour12(&self) -> (bool, uint) {
        self.time.hour12()
    }

    /// Returns the minute number from 0 to 59.
    #[inline]
    pub fn minute(&self) -> uint {
        self.time.minute()
    }

    /// Returns the second number from 0 to 59.
    #[inline]
    pub fn second(&self) -> uint {
        self.time.second()
    }

    /// Returns the number of nanoseconds since the whole non-leap second.
    /// The range from 1,000,000,000 to 1,999,999,999 represents the leap second.
    #[inline]
    pub fn nanosecond(&self) -> uint {
        self.time.nanosecond()
    }

    /// Makes a new `DateTime` with the year number changed.
    ///
    /// Returns `None` when the resulting `DateTime` would be invalid.
    #[inline]
    pub fn with_year(&self, year: int) -> Option<DateTime> {
        self.date.with_year(year).map(|d| DateTime { date: d, ..*self })
    }

    /// Makes a new `DateTime` with the month number (starting from 1) changed.
    ///
    /// Returns `None` when the resulting `DateTime` would be invalid.
    #[inline]
    pub fn with_month(&self, month: uint) -> Option<DateTime> {
        self.date.with_month(month).map(|d| DateTime { date: d, ..*self })
    }

    /// Makes a new `DateTime` with the month number (starting from 0) changed.
    ///
    /// Returns `None` when the resulting `DateTime` would be invalid.
    #[inline]
    pub fn with_month0(&self, month0: uint) -> Option<DateTime> {
        self.date.with_month0(month0).map(|d| DateTime { date: d, ..*self })
    }

    /// Makes a new `DateTime` with the day of month (starting from 1) changed.
    ///
    /// Returns `None` when the resulting `DateTime` would be invalid.
    #[inline]
    pub fn with_day(&self, day: uint) -> Option<DateTime> {
        self.date.with_day(day).map(|d| DateTime { date: d, ..*self })
    }

    /// Makes a new `DateTime` with the day of month (starting from 0) changed.
    ///
    /// Returns `None` when the resulting `DateTime` would be invalid.
    #[inline]
    pub fn with_day0(&self, day0: uint) -> Option<DateTime> {
        self.date.with_day0(day0).map(|d| DateTime { date: d, ..*self })
    }

    /// Makes a new `DateTime` with the day of year (starting from 1) changed.
    ///
    /// Returns `None` when the resulting `DateTime` would be invalid.
    #[inline]
    pub fn with_ordinal(&self, ordinal: uint) -> Option<DateTime> {
        self.date.with_ordinal(ordinal).map(|d| DateTime { date: d, ..*self })
    }

    /// Makes a new `DateTime` with the day of year (starting from 0) changed.
    ///
    /// Returns `None` when the resulting `DateTime` would be invalid.
    #[inline]
    pub fn with_ordinal0(&self, ordinal0: uint) -> Option<DateTime> {
        self.date.with_ordinal0(ordinal0).map(|d| DateTime { date: d, ..*self })
    }

    /// Makes a new `Time` with the hour number changed.
    ///
    /// Returns `None` when the resulting `Time` would be invalid.
    #[inline]
    pub fn with_hour(&self, hour: uint) -> Option<DateTime> {
        self.time.with_hour(hour).map(|t| DateTime { time: t, ..*self })
    }

    /// Makes a new `Time` with the minute number changed.
    ///
    /// Returns `None` when the resulting `Time` would be invalid.
    #[inline]
    pub fn with_minute(&self, min: uint) -> Option<DateTime> {
        self.time.with_minute(min).map(|t| DateTime { time: t, ..*self })
    }

    /// Makes a new `Time` with the second number changed.
    ///
    /// Returns `None` when the resulting `Time` would be invalid.
    #[inline]
    pub fn with_second(&self, sec: uint) -> Option<DateTime> {
        self.time.with_second(sec).map(|t| DateTime { time: t, ..*self })
    }

    /// Makes a new `Time` with nanoseconds since the whole non-leap second changed.
    ///
    /// Returns `None` when the resulting `Time` would be invalid.
    #[inline]
    pub fn with_nanosecond(&self, nano: uint) -> Option<DateTime> {
        self.time.with_nanosecond(nano).map(|t| DateTime { time: t, ..*self })
    }

    /// Returns the number of days since January 1, 1 (Day 1) in the proleptic Gregorian calendar.
    #[inline]
    pub fn ndays_from_ce(&self) -> int {
        self.date.ndays_from_ce()
    }

    /// Returns the number of non-leap seconds past the last midnight.
    #[inline]
    pub fn nseconds_from_midnight(&self) -> uint {
        self.time.nseconds_from_midnight()
    }

    /// Returns the number of non-leap seconds since January 1, 1970 0:00:00.
    /// Note that this does *not* account for the timezone!
    #[inline]
    pub fn nseconds_from_unix_epoch(&self) -> int {
        (self.date.ndays_from_ce() - 719163) * 86400 + self.time.nseconds_from_midnight() as int
    }
}

impl fmt::Show for DateTime {
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
            |y,m,d,h,n,s| DateTime::from_ymdhms(y,m,d,h,n,s).unwrap().nseconds_from_unix_epoch();
        assert_eq!(to_timestamp(1969, 12, 31, 23, 59, 59), -1);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 0), 0);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 1), 1);
        assert_eq!(to_timestamp(2001, 9, 9, 1, 46, 40), 1_000_000_000);
        assert_eq!(to_timestamp(2038, 1, 19, 3, 14, 7), 0x7fffffff);
    }
}

