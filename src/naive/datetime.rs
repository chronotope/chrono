// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 date and time without timezone.
 */

use std::{fmt, hash};
use std::num::{Int, ToPrimitive};
use std::ops::{Add, Sub};

use {Weekday, Timelike, Datelike};
use div::div_mod_floor;
use duration::Duration;
use naive::time::NaiveTime;
use naive::date::NaiveDate;
use format::DelayedFormat;

/// ISO 8601 combined date and time without timezone.
#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct NaiveDateTime {
    date: NaiveDate,
    time: NaiveTime,
}

impl NaiveDateTime {
    /// Makes a new `NaiveDateTime` from date and time components.
    /// Equivalent to `date.and_time(time)` and many other helper constructors on `NaiveDate`.
    #[inline]
    pub fn new(date: NaiveDate, time: NaiveTime) -> NaiveDateTime {
        NaiveDateTime { date: date, time: time }
    }

    /// Makes a new `NaiveDateTime` from the number of non-leap seconds
    /// since January 1, 1970 0:00:00 UTC and the number of nanoseconds
    /// since the last whole non-leap second.
    ///
    /// Fails on the out-of-range number of seconds and/or invalid nanosecond.
    #[inline]
    pub fn from_num_seconds_from_unix_epoch(secs: i64, nsecs: u32) -> NaiveDateTime {
        let datetime = NaiveDateTime::from_num_seconds_from_unix_epoch_opt(secs, nsecs);
        datetime.expect("invalid or out-of-range datetime")
    }

    /// Makes a new `NaiveDateTime` from the number of non-leap seconds
    /// since January 1, 1970 0:00:00 UTC and the number of nanoseconds
    /// since the last whole non-leap second.
    ///
    /// Returns `None` on the out-of-range number of seconds and/or invalid nanosecond.
    #[inline]
    pub fn from_num_seconds_from_unix_epoch_opt(secs: i64, nsecs: u32) -> Option<NaiveDateTime> {
        let (days, secs) = div_mod_floor(secs, 86400);
        let date = days.to_i32().and_then(|days| days.checked_add(719163))
                                .and_then(|days_ce| NaiveDate::from_num_days_from_ce_opt(days_ce));
        let time = NaiveTime::from_num_seconds_from_midnight_opt(secs as u32, nsecs);
        match (date, time) {
            (Some(date), Some(time)) => Some(NaiveDateTime { date: date, time: time }),
            (_, _) => None,
        }
    }

    /// Retrieves a date component.
    #[inline]
    pub fn date(&self) -> NaiveDate {
        self.date
    }

    /// Retrieves a time component.
    #[inline]
    pub fn time(&self) -> NaiveTime {
        self.time
    }

    /// Returns the number of non-leap seconds since January 1, 1970 0:00:00 UTC.
    /// Note that this does *not* account for the timezone!
    #[inline]
    pub fn num_seconds_from_unix_epoch(&self) -> i64 {
        let ndays = self.date.num_days_from_ce() as i64;
        let nseconds = self.time.num_seconds_from_midnight() as i64;
        (ndays - 719163) * 86400 + nseconds
    }

    /// Formats the combined date and time in the specified format string.
    /// See the `format` module on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&'a self, fmt: &'a str) -> DelayedFormat<'a> {
        DelayedFormat::new(Some(self.date.clone()), Some(self.time.clone()), fmt)
    }
}

impl Datelike for NaiveDateTime {
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
    fn with_year(&self, year: i32) -> Option<NaiveDateTime> {
        self.date.with_year(year).map(|d| NaiveDateTime { date: d, ..*self })
    }

    #[inline]
    fn with_month(&self, month: u32) -> Option<NaiveDateTime> {
        self.date.with_month(month).map(|d| NaiveDateTime { date: d, ..*self })
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Option<NaiveDateTime> {
        self.date.with_month0(month0).map(|d| NaiveDateTime { date: d, ..*self })
    }

    #[inline]
    fn with_day(&self, day: u32) -> Option<NaiveDateTime> {
        self.date.with_day(day).map(|d| NaiveDateTime { date: d, ..*self })
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Option<NaiveDateTime> {
        self.date.with_day0(day0).map(|d| NaiveDateTime { date: d, ..*self })
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<NaiveDateTime> {
        self.date.with_ordinal(ordinal).map(|d| NaiveDateTime { date: d, ..*self })
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<NaiveDateTime> {
        self.date.with_ordinal0(ordinal0).map(|d| NaiveDateTime { date: d, ..*self })
    }
}

impl Timelike for NaiveDateTime {
    #[inline] fn hour(&self) -> u32 { self.time.hour() }
    #[inline] fn minute(&self) -> u32 { self.time.minute() }
    #[inline] fn second(&self) -> u32 { self.time.second() }
    #[inline] fn nanosecond(&self) -> u32 { self.time.nanosecond() }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<NaiveDateTime> {
        self.time.with_hour(hour).map(|t| NaiveDateTime { time: t, ..*self })
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<NaiveDateTime> {
        self.time.with_minute(min).map(|t| NaiveDateTime { time: t, ..*self })
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<NaiveDateTime> {
        self.time.with_second(sec).map(|t| NaiveDateTime { time: t, ..*self })
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<NaiveDateTime> {
        self.time.with_nanosecond(nano).map(|t| NaiveDateTime { time: t, ..*self })
    }
}

impl<H: hash::Hasher + hash::Writer> hash::Hash<H> for NaiveDateTime {
    fn hash(&self, state: &mut H) { self.date.hash(state); self.time.hash(state) }
}

impl Add<Duration> for NaiveDateTime {
    type Output = NaiveDateTime;

    fn add(self, rhs: Duration) -> NaiveDateTime {
        // Duration does not directly give its parts, so we need some additional calculations.
        let days = rhs.num_days();
        let nanos = (rhs - Duration::days(days)).num_nanoseconds().unwrap();
        debug_assert!(Duration::days(days) + Duration::nanoseconds(nanos) == rhs);
        debug_assert!(-86400_000_000_000 < nanos && nanos < 86400_000_000_000);

        let mut date = self.date + Duration::days(days);
        let time = self.time + Duration::nanoseconds(nanos);

        // time always wraps around, but date needs to be adjusted for overflow.
        if nanos < 0 && time > self.time {
            date = date.pred();
        } else if nanos > 0 && time < self.time {
            date = date.succ();
        }
        NaiveDateTime { date: date, time: time }
    }
}

impl Sub<NaiveDateTime> for NaiveDateTime {
    type Output = Duration;

    fn sub(self, rhs: NaiveDateTime) -> Duration {
        (self.date - rhs.date) + (self.time - rhs.time)
    }
}

impl Sub<Duration> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn sub(self, rhs: Duration) -> NaiveDateTime { self.add(-rhs) }
}

impl fmt::Debug for NaiveDateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}T{:?}", self.date, self.time)
    }
}

impl fmt::Display for NaiveDateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.date, self.time)
    }
}

#[cfg(test)]
mod tests {
    use super::NaiveDateTime;
    use duration::Duration;
    use naive::date::NaiveDate;
    use std::i64;

    #[test]
    fn test_datetime_from_num_seconds_from_unix_epoch() {
        let from_timestamp = |&: secs| NaiveDateTime::from_num_seconds_from_unix_epoch_opt(secs, 0);
        let ymdhms = |&: y,m,d,h,n,s| NaiveDate::from_ymd(y,m,d).and_hms(h,n,s);
        assert_eq!(from_timestamp(-1), Some(ymdhms(1969, 12, 31, 23, 59, 59)));
        assert_eq!(from_timestamp(0), Some(ymdhms(1970, 1, 1, 0, 0, 0)));
        assert_eq!(from_timestamp(1), Some(ymdhms(1970, 1, 1, 0, 0, 1)));
        assert_eq!(from_timestamp(1_000_000_000), Some(ymdhms(2001, 9, 9, 1, 46, 40)));
        assert_eq!(from_timestamp(0x7fffffff), Some(ymdhms(2038, 1, 19, 3, 14, 7)));
        assert_eq!(from_timestamp(i64::MIN), None);
        assert_eq!(from_timestamp(i64::MAX), None);
    }

    #[test]
    fn test_datetime_add() {
        let ymdhms = |&: y,m,d,h,n,s| NaiveDate::from_ymd(y,m,d).and_hms(h,n,s);
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) + Duration::seconds(3600 + 60 + 1),
                   ymdhms(2014, 5, 6, 8, 9, 10));
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) + Duration::seconds(-(3600 + 60 + 1)),
                   ymdhms(2014, 5, 6, 6, 7, 8));
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) + Duration::seconds(86399),
                   ymdhms(2014, 5, 7, 7, 8, 8));
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) + Duration::seconds(86400 * 10),
                   ymdhms(2014, 5, 16, 7, 8, 9));
        assert_eq!(ymdhms(2014, 5, 6, 7, 8, 9) + Duration::seconds(-86400 * 10),
                   ymdhms(2014, 4, 26, 7, 8, 9));
    }

    #[test]
    fn test_datetime_sub() {
        let ymdhms = |&: y,m,d,h,n,s| NaiveDate::from_ymd(y,m,d).and_hms(h,n,s);
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
    fn test_datetime_num_seconds_from_unix_epoch() {
        let to_timestamp = |&: y,m,d,h,n,s|
            NaiveDate::from_ymd(y,m,d).and_hms(h,n,s).num_seconds_from_unix_epoch();
        assert_eq!(to_timestamp(1969, 12, 31, 23, 59, 59), -1);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 0), 0);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 1), 1);
        assert_eq!(to_timestamp(2001, 9, 9, 1, 46, 40), 1_000_000_000);
        assert_eq!(to_timestamp(2038, 1, 19, 3, 14, 7), 0x7fffffff);
    }

    #[test]
    fn test_datetime_format() {
        let dt = NaiveDate::from_ymd(2010, 9, 8).and_hms_milli(7, 6, 54, 321);
        assert_eq!(dt.format("%c").to_string(), "Wed Sep  8 07:06:54 2010");
        assert_eq!(dt.format("%t%n%%%n%t").to_string(), "\t\n%\n\t");
    }
}

