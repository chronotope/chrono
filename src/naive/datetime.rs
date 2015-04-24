// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 date and time without timezone.
 */

use std::{str, fmt, hash};
use std::ops::{Add, Sub};
use num::traits::ToPrimitive;

use {Weekday, Timelike, Datelike};
use div::div_mod_floor;
use duration::Duration;
use naive::time::NaiveTime;
use naive::date::NaiveDate;
use format::{Item, Numeric, Pad, Fixed};
use format::{parse, Parsed, ParseError, ParseResult, DelayedFormat, StrftimeItems};

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
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp")
    /// and the number of nanoseconds since the last whole non-leap second.
    ///
    /// Fails on the out-of-range number of seconds and/or invalid nanosecond.
    #[inline]
    pub fn from_timestamp(secs: i64, nsecs: u32) -> NaiveDateTime {
        let datetime = NaiveDateTime::from_timestamp_opt(secs, nsecs);
        datetime.expect("invalid or out-of-range datetime")
    }

    /// Makes a new `NaiveDateTime` from the number of non-leap seconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp")
    /// and the number of nanoseconds since the last whole non-leap second.
    ///
    /// Returns `None` on the out-of-range number of seconds and/or invalid nanosecond.
    #[inline]
    pub fn from_timestamp_opt(secs: i64, nsecs: u32) -> Option<NaiveDateTime> {
        let (days, secs) = div_mod_floor(secs, 86400);
        let date = days.to_i32().and_then(|days| days.checked_add(719163))
                                .and_then(|days_ce| NaiveDate::from_num_days_from_ce_opt(days_ce));
        let time = NaiveTime::from_num_seconds_from_midnight_opt(secs as u32, nsecs);
        match (date, time) {
            (Some(date), Some(time)) => Some(NaiveDateTime { date: date, time: time }),
            (_, _) => None,
        }
    }

    /// *Deprecated:* Same to `NaiveDateTime::from_timestamp`.
    #[inline]
    pub fn from_num_seconds_from_unix_epoch(secs: i64, nsecs: u32) -> NaiveDateTime {
        NaiveDateTime::from_timestamp(secs, nsecs)
    }

    /// *Deprecated:* Same to `NaiveDateTime::from_timestamp_opt`.
    #[inline]
    pub fn from_num_seconds_from_unix_epoch_opt(secs: i64, nsecs: u32) -> Option<NaiveDateTime> {
        NaiveDateTime::from_timestamp_opt(secs, nsecs)
    }

    /// Parses a string with the specified format string and returns a new `NaiveDateTime`.
    /// See the `format::strftime` module on the supported escape sequences.
    pub fn parse_from_str(s: &str, fmt: &str) -> ParseResult<NaiveDateTime> {
        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, StrftimeItems::new(fmt)));
        parsed.to_naive_datetime_with_offset(0) // no offset adjustment
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

    /// Returns the number of non-leap seconds since January 1, 1970 0:00:00 UTC
    /// (aka "UNIX timestamp").
    /// Note that this does *not* account for the timezone!
    #[inline]
    pub fn timestamp(&self) -> i64 {
        let ndays = self.date.num_days_from_ce() as i64;
        let nseconds = self.time.num_seconds_from_midnight() as i64;
        (ndays - 719163) * 86400 + nseconds
    }

    /// *Deprecated:* Same to `NaiveDateTime::timestamp`.
    #[inline]
    pub fn num_seconds_from_unix_epoch(&self) -> i64 {
        self.timestamp()
    }

    /// Adds given `Duration` to the current date and time.
    ///
    /// Returns `None` when it will result in overflow.
    pub fn checked_add(self, rhs: Duration) -> Option<NaiveDateTime> {
        // Duration does not directly give its parts, so we need some additional calculations.
        let days = rhs.num_days();
        let nanos = (rhs - Duration::days(days)).num_nanoseconds().unwrap();
        debug_assert!(Duration::days(days) + Duration::nanoseconds(nanos) == rhs);
        debug_assert!(-86400_000_000_000 < nanos && nanos < 86400_000_000_000);

        let mut date = try_opt!(self.date.checked_add(Duration::days(days)));
        let time = self.time + Duration::nanoseconds(nanos);

        // time always wraps around, but date needs to be adjusted for overflow.
        if nanos < 0 && time > self.time {
            date = try_opt!(date.pred_opt());
        } else if nanos > 0 && time < self.time {
            date = try_opt!(date.succ_opt());
        }
        Some(NaiveDateTime { date: date, time: time })
    }

    /// Subtracts given `Duration` from the current date and time.
    ///
    /// Returns `None` when it will result in overflow.
    pub fn checked_sub(self, rhs: Duration) -> Option<NaiveDateTime> {
        // Duration does not directly give its parts, so we need some additional calculations.
        let days = rhs.num_days();
        let nanos = (rhs - Duration::days(days)).num_nanoseconds().unwrap();
        debug_assert!(Duration::days(days) + Duration::nanoseconds(nanos) == rhs);
        debug_assert!(-86400_000_000_000 < nanos && nanos < 86400_000_000_000);

        let mut date = try_opt!(self.date.checked_sub(Duration::days(days)));
        let time = self.time - Duration::nanoseconds(nanos);

        // time always wraps around, but date needs to be adjusted for overflow.
        if nanos > 0 && time > self.time {
            date = try_opt!(date.pred_opt());
        } else if nanos < 0 && time < self.time {
            date = try_opt!(date.succ_opt());
        }
        Some(NaiveDateTime { date: date, time: time })
    }

    /// Formats the combined date and time with the specified formatting items.
    #[inline]
    pub fn format_with_items<'a, I>(&self, items: I) -> DelayedFormat<I>
            where I: Iterator<Item=Item<'a>> + Clone {
        DelayedFormat::new(Some(self.date.clone()), Some(self.time.clone()), items)
    }

    /// Formats the combined date and time with the specified format string.
    /// See the `format::strftime` module on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_with_items(StrftimeItems::new(fmt))
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

impl hash::Hash for NaiveDateTime {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.date.hash(state);
        self.time.hash(state);
    }
}

impl Add<Duration> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn add(self, rhs: Duration) -> NaiveDateTime {
        self.checked_add(rhs).expect("`NaiveDateTime + Duration` overflowed")
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
    fn sub(self, rhs: Duration) -> NaiveDateTime {
        self.checked_sub(rhs).expect("`NaiveDateTime - Duration` overflowed")
    }
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

impl str::FromStr for NaiveDateTime {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<NaiveDateTime> {
        const ITEMS: &'static [Item<'static>] = &[
            Item::Space(""), Item::Numeric(Numeric::Year, Pad::Zero),
            Item::Space(""), Item::Literal("-"),
            Item::Space(""), Item::Numeric(Numeric::Month, Pad::Zero),
            Item::Space(""), Item::Literal("-"),
            Item::Space(""), Item::Numeric(Numeric::Day, Pad::Zero),
            Item::Space(""), Item::Literal("T"), // XXX shouldn't this be case-insensitive?
            Item::Space(""), Item::Numeric(Numeric::Hour, Pad::Zero),
            Item::Space(""), Item::Literal(":"),
            Item::Space(""), Item::Numeric(Numeric::Minute, Pad::Zero),
            Item::Space(""), Item::Literal(":"),
            Item::Space(""), Item::Numeric(Numeric::Second, Pad::Zero),
            Item::Fixed(Fixed::Nanosecond), Item::Space(""),
        ];

        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, ITEMS.iter().cloned()));
        parsed.to_naive_datetime_with_offset(0)
    }
}

#[cfg(test)]
mod tests {
    use super::NaiveDateTime;
    use Datelike;
    use duration::Duration;
    use naive::date as naive_date;
    use naive::date::NaiveDate;
    use std::i64;

    #[test]
    fn test_datetime_from_timestamp() {
        let from_timestamp = |secs| NaiveDateTime::from_timestamp_opt(secs, 0);
        let ymdhms = |y,m,d,h,n,s| NaiveDate::from_ymd(y,m,d).and_hms(h,n,s);
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
        fn check((y,m,d,h,n,s): (i32,u32,u32,u32,u32,u32), rhs: Duration,
                 result: Option<(i32,u32,u32,u32,u32,u32)>) {
            let lhs = NaiveDate::from_ymd(y, m, d).and_hms(h, n, s);
            let sum = result.map(|(y,m,d,h,n,s)| NaiveDate::from_ymd(y, m, d).and_hms(h, n, s));
            assert_eq!(lhs.checked_add(rhs), sum);
            assert_eq!(lhs.checked_sub(-rhs), sum);
        };

        check((2014,5,6, 7,8,9), Duration::seconds(3600 + 60 + 1), Some((2014,5,6, 8,9,10)));
        check((2014,5,6, 7,8,9), Duration::seconds(-(3600 + 60 + 1)), Some((2014,5,6, 6,7,8)));
        check((2014,5,6, 7,8,9), Duration::seconds(86399), Some((2014,5,7, 7,8,8)));
        check((2014,5,6, 7,8,9), Duration::seconds(86400 * 10), Some((2014,5,16, 7,8,9)));
        check((2014,5,6, 7,8,9), Duration::seconds(-86400 * 10), Some((2014,4,26, 7,8,9)));
        check((2014,5,6, 7,8,9), Duration::seconds(86400 * 10), Some((2014,5,16, 7,8,9)));

        // overflow check
        // assumes that we have correct values for MAX/MIN_DAYS_FROM_YEAR_0 from `naive::date`.
        // (they are private constants, but the equivalence is tested in that module.)
        let max_days_from_year_0 = naive_date::MAX - NaiveDate::from_ymd(0,1,1);
        check((0,1,1, 0,0,0), max_days_from_year_0, Some((naive_date::MAX.year(),12,31, 0,0,0)));
        check((0,1,1, 0,0,0), max_days_from_year_0 + Duration::seconds(86399),
              Some((naive_date::MAX.year(),12,31, 23,59,59)));
        check((0,1,1, 0,0,0), max_days_from_year_0 + Duration::seconds(86400), None);
        check((0,1,1, 0,0,0), Duration::max_value(), None);

        let min_days_from_year_0 = naive_date::MIN - NaiveDate::from_ymd(0,1,1);
        check((0,1,1, 0,0,0), min_days_from_year_0, Some((naive_date::MIN.year(),1,1, 0,0,0)));
        check((0,1,1, 0,0,0), min_days_from_year_0 - Duration::seconds(1), None);
        check((0,1,1, 0,0,0), Duration::min_value(), None);
    }

    #[test]
    fn test_datetime_sub() {
        let ymdhms = |y,m,d,h,n,s| NaiveDate::from_ymd(y,m,d).and_hms(h,n,s);
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
    fn test_datetime_timestamp() {
        let to_timestamp = |y,m,d,h,n,s| NaiveDate::from_ymd(y,m,d).and_hms(h,n,s).timestamp();
        assert_eq!(to_timestamp(1969, 12, 31, 23, 59, 59), -1);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 0), 0);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 1), 1);
        assert_eq!(to_timestamp(2001, 9, 9, 1, 46, 40), 1_000_000_000);
        assert_eq!(to_timestamp(2038, 1, 19, 3, 14, 7), 0x7fffffff);
    }

    #[test]
    fn test_datetime_from_str() {
        // valid cases
        let valid = [
            "2015-2-18T23:16:9.15",
            "-77-02-18T23:16:09",
            "  +82701  -  05  -  6  T  15  :  9  : 60.898989898989   ",
        ];
        for &s in &valid {
            let d = match s.parse::<NaiveDateTime>() {
                Ok(d) => d,
                Err(e) => panic!("parsing `{}` has failed: {}", s, e)
            };
            let s_ = format!("{:?}", d);
            // `s` and `s_` may differ, but `s.parse()` and `s_.parse()` must be same
            let d_ = match s_.parse::<NaiveDateTime>() {
                Ok(d) => d,
                Err(e) => panic!("`{}` is parsed into `{:?}`, but reparsing that has failed: {}",
                                 s, d, e)
            };
            assert!(d == d_, "`{}` is parsed into `{:?}`, but reparsed result \
                              `{:?}` does not match", s, d, d_);
        }

        // some invalid cases
        // since `ParseErrorKind` is private, all we can do is to check if there was an error
        assert!("".parse::<NaiveDateTime>().is_err());
        assert!("x".parse::<NaiveDateTime>().is_err());
        assert!("15".parse::<NaiveDateTime>().is_err());
        assert!("15:8:9".parse::<NaiveDateTime>().is_err());
        assert!("15-8-9".parse::<NaiveDateTime>().is_err());
        assert!("2015-15-15T15:15:15".parse::<NaiveDateTime>().is_err());
        assert!("2012-12-12T12:12:12x".parse::<NaiveDateTime>().is_err());
        assert!("2012-123-12T12:12:12".parse::<NaiveDateTime>().is_err());
        assert!("+ 82701-123-12T12:12:12".parse::<NaiveDateTime>().is_err());
        assert!("+802701-123-12T12:12:12".parse::<NaiveDateTime>().is_err()); // out-of-bound
    }

    #[test]
    fn test_datetime_parse_from_str() {
        let ymdhms = |y,m,d,h,n,s| NaiveDate::from_ymd(y,m,d).and_hms(h,n,s);
        assert_eq!(NaiveDateTime::parse_from_str("2014-5-7T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
                   Ok(ymdhms(2014, 5, 7, 12, 34, 56))); // ignore offset
        assert_eq!(NaiveDateTime::parse_from_str("2015-W06-1 000000", "%G-W%V-%u%H%M%S"),
                   Ok(ymdhms(2015, 2, 2, 0, 0, 0)));
        assert_eq!(NaiveDateTime::parse_from_str("Fri, 09 Aug 2013 23:54:35 GMT",
                                                 "%a, %d %b %Y %H:%M:%S GMT"),
                   Ok(ymdhms(2013, 8, 9, 23, 54, 35)));
        assert!(NaiveDateTime::parse_from_str("Sat, 09 Aug 2013 23:54:35 GMT",
                                              "%a, %d %b %Y %H:%M:%S GMT").is_err());
        assert!(NaiveDateTime::parse_from_str("2014-5-7 12:3456", "%Y-%m-%d %H:%M:%S").is_err());
        assert!(NaiveDateTime::parse_from_str("12:34:56", "%H:%M:%S").is_err()); // insufficient
    }

    #[test]
    fn test_datetime_format() {
        let dt = NaiveDate::from_ymd(2010, 9, 8).and_hms_milli(7, 6, 54, 321);
        assert_eq!(dt.format("%c").to_string(), "Wed Sep  8 07:06:54 2010");
        assert_eq!(dt.format("%s").to_string(), "1283929614");
        assert_eq!(dt.format("%t%n%%%n%t").to_string(), "\t\n%\n\t");

        // a horror of leap second: coming near to you.
        let dt = NaiveDate::from_ymd(2012, 6, 30).and_hms_milli(23, 59, 59, 1_000);
        assert_eq!(dt.format("%c").to_string(), "Sat Jun 30 23:59:60 2012");
        assert_eq!(dt.format("%s").to_string(), "1341100799"); // not 1341100800, it's intentional.
    }
}

