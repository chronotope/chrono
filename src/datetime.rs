// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 date and time.
 */

use std::{fmt, hash};
use offset::Offset;
use duration::Duration;
use time::{Timelike, NaiveTime, Time};
use date::{Datelike, NaiveDate, Date, Weekday};

/// ISO 8601 combined date and time without timezone.
#[deriving(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
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

impl Add<Duration,NaiveDateTime> for NaiveDateTime {
    fn add(&self, rhs: &Duration) -> NaiveDateTime {
        // we want `(NaiveDate + days in Duration) + (NaiveTime + secs/nanos in Duration)`
        // to be equal to `NaiveDateTime + Duration`, but `NaiveDate + Duration` rounds towards zero.
        let mut date = self.date + Duration::days(rhs.to_tuple().val0());
        let time = self.time + *rhs;
        if time < self.time {
            // since the time portion of the duration is always positive and bounded,
            // this condition always means that the time part has been overflowed.
            date = date.succ();
        }
        NaiveDateTime { date: date, time: time }
    }
}

/*
// Rust issue #7590, the current coherence checker can't handle multiple Add impls
impl Add<NaiveDateTime,NaiveDateTime> for Duration {
    #[inline]
    fn add(&self, rhs: &NaiveDateTime) -> NaiveDateTime { rhs.add(self) }
}
*/

impl Sub<NaiveDateTime,Duration> for NaiveDateTime {
    fn sub(&self, rhs: &NaiveDateTime) -> Duration {
        (self.date - rhs.date) + (self.time - rhs.time)
    }
}

impl fmt::Show for NaiveDateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}T{}", self.date, self.time)
    }
}

/// ISO 8601 combined date and time with timezone.
#[deriving(Clone)]
pub struct DateTime<Off> {
    datetime: NaiveDateTime,
    offset: Off,
}

impl<Off:Offset> DateTime<Off> {
    /// Makes a new `DateTime` with given *UTC* datetime and offset.
    /// The local datetime should be constructed via the `Offset` trait.
    #[inline]
    pub fn from_utc(datetime: NaiveDateTime, offset: Off) -> DateTime<Off> {
        DateTime { datetime: datetime, offset: offset }
    }

    /// Retrieves a date component.
    #[inline]
    pub fn date(&self) -> Date<Off> {
        Date::from_utc(self.datetime.date().clone(), self.offset.clone())
    }

    /// Retrieves a time component.
    #[inline]
    pub fn time(&self) -> Time<Off> {
        Time::from_utc(self.datetime.time().clone(), self.offset.clone())
    }

    /// Returns the number of non-leap seconds since January 1, 1970 0:00:00 UTC.
    #[inline]
    pub fn num_seconds_from_unix_epoch(&self) -> i64 {
        self.datetime.num_seconds_from_unix_epoch()
    }

    /// Returns a view to the local datetime.
    fn local(&self) -> NaiveDateTime {
        self.offset.to_local_datetime(&self.datetime)
    }
}

impl<Off:Offset> Datelike for DateTime<Off> {
    #[inline] fn year(&self) -> i32 { self.local().year() }
    #[inline] fn month(&self) -> u32 { self.local().month() }
    #[inline] fn month0(&self) -> u32 { self.local().month0() }
    #[inline] fn day(&self) -> u32 { self.local().day() }
    #[inline] fn day0(&self) -> u32 { self.local().day0() }
    #[inline] fn ordinal(&self) -> u32 { self.local().ordinal() }
    #[inline] fn ordinal0(&self) -> u32 { self.local().ordinal0() }
    #[inline] fn weekday(&self) -> Weekday { self.local().weekday() }
    #[inline] fn isoweekdate(&self) -> (i32, u32, Weekday) { self.local().isoweekdate() }

    #[inline]
    fn with_year(&self, year: i32) -> Option<DateTime<Off>> {
        self.local().with_year(year)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }

    #[inline]
    fn with_month(&self, month: u32) -> Option<DateTime<Off>> {
        self.local().with_month(month)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Option<DateTime<Off>> {
        self.local().with_month0(month0)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }

    #[inline]
    fn with_day(&self, day: u32) -> Option<DateTime<Off>> {
        self.local().with_day(day)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Option<DateTime<Off>> {
        self.local().with_day0(day0)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<DateTime<Off>> {
        self.local().with_ordinal(ordinal)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<DateTime<Off>> {
        self.local().with_ordinal0(ordinal0)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }
}

impl<Off:Offset> Timelike for DateTime<Off> {
    #[inline] fn hour(&self) -> u32 { self.local().hour() }
    #[inline] fn minute(&self) -> u32 { self.local().minute() }
    #[inline] fn second(&self) -> u32 { self.local().second() }
    #[inline] fn nanosecond(&self) -> u32 { self.local().nanosecond() }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<DateTime<Off>> {
        self.local().with_hour(hour)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<DateTime<Off>> {
        self.local().with_minute(min)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<DateTime<Off>> {
        self.local().with_second(sec)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<DateTime<Off>> {
        self.local().with_nanosecond(nano)
            .and_then(|datetime| self.offset.from_local_datetime(&datetime).single())
    }
}

impl<Off:Offset> PartialEq for DateTime<Off> {
    fn eq(&self, other: &DateTime<Off>) -> bool { self.datetime == other.datetime }
}

impl<Off:Offset> Eq for DateTime<Off> {
}

impl<Off:Offset, Off2:Offset> Equiv<DateTime<Off2>> for DateTime<Off> {
    fn equiv(&self, other: &DateTime<Off2>) -> bool { self.datetime == other.datetime }
}

impl<Off:Offset> PartialOrd for DateTime<Off> {
    fn partial_cmp(&self, other: &DateTime<Off>) -> Option<Ordering> {
        self.datetime.partial_cmp(&other.datetime)
    }
}

impl<Off:Offset> Ord for DateTime<Off> {
    fn cmp(&self, other: &DateTime<Off>) -> Ordering { self.datetime.cmp(&other.datetime) }
}

impl<Off:Offset> hash::Hash for DateTime<Off> {
    fn hash(&self, state: &mut hash::sip::SipState) { self.datetime.hash(state) }
}

impl<Off:Offset> Add<Duration,DateTime<Off>> for DateTime<Off> {
    fn add(&self, rhs: &Duration) -> DateTime<Off> {
        DateTime { datetime: self.datetime + *rhs, offset: self.offset.clone() }
    }
}

/*
// Rust issue #7590, the current coherence checker can't handle multiple Add impls
impl<Off:Offset> Add<DateTime<Off>,DateTime<Off>> for Duration {
    #[inline]
    fn add(&self, rhs: &DateTime<Off>) -> DateTime<Off> { rhs.add(self) }
}
*/

impl<Off:Offset, Off2:Offset> Sub<DateTime<Off2>,Duration> for DateTime<Off> {
    fn sub(&self, rhs: &DateTime<Off2>) -> Duration {
        self.datetime - rhs.datetime
    }
}

impl<Off:Offset> fmt::Show for DateTime<Off> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.local(), self.offset)
    }
}

#[cfg(test)]
mod tests {
    use date::NaiveDate;
    use duration::Duration;

    #[test]
    fn test_datetime_add() {
        let ymdhms = |y,m,d,h,n,s| NaiveDate::from_ymd(y,m,d).and_hms(h,n,s);
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
    fn test_datetime_num_seconds_from_unix_epoch() {
        let to_timestamp =
            |y,m,d,h,n,s| NaiveDate::from_ymd(y,m,d).and_hms(h,n,s).num_seconds_from_unix_epoch();
        assert_eq!(to_timestamp(1969, 12, 31, 23, 59, 59), -1);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 0), 0);
        assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 1), 1);
        assert_eq!(to_timestamp(2001, 9, 9, 1, 46, 40), 1_000_000_000);
        assert_eq!(to_timestamp(2038, 1, 19, 3, 14, 7), 0x7fffffff);
    }

    #[test]
    #[allow(uppercase_variables)]
    fn test_datetime_offset() {
        use offset::{Offset, UTC, FixedOffset};
        let EDT = FixedOffset::east(4*60*60);
        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9).to_string(),
                   "2014-05-06T07:08:09Z".to_string());
        assert_eq!(EDT.ymd(2014, 5, 6).and_hms(7, 8, 9).to_string(),
                   "2014-05-06T07:08:09+04:00".to_string());
        assert!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9).equiv(&EDT.ymd(2014, 5, 6).and_hms(11, 8, 9)));
        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9) + Duration::seconds(3600 + 60 + 1),
                   UTC.ymd(2014, 5, 6).and_hms(8, 9, 10));
        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9) - EDT.ymd(2014, 5, 6).and_hms(10, 11, 12),
                   Duration::seconds(3600 - 3*60 - 3));
    }
}

