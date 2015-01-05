// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 date and time.
 */

use std::{fmt, hash};
use std::cmp::Ordering;
use std::ops::{Add, Sub};

use {Weekday, Timelike, Datelike};
use offset::Offset;
use duration::Duration;
use naive::datetime::NaiveDateTime;
use time::Time;
use date::Date;
use format::DelayedFormat;

/// ISO 8601 combined date and time with timezone.
#[derive(Clone)]
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

    /// Retrieves an associated offset.
    #[inline]
    pub fn offset<'a>(&'a self) -> &'a Off {
        &self.offset
    }

    /// Changes the associated offset.
    /// This does not change the actual `DateTime` (but will change the string representation).
    #[inline]
    pub fn with_offset<Off2:Offset>(&self, offset: Off2) -> DateTime<Off2> {
        DateTime::from_utc(self.datetime, offset)
    }

    /// Formats the combined date and time in the specified format string.
    /// See the `format` module on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&'a self, fmt: &'a str) -> DelayedFormat<'a> {
        let local = self.local();
        DelayedFormat::new_with_offset(Some(local.date()), Some(local.time()), &self.offset, fmt)
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

impl<Off:Offset, Off2:Offset> PartialEq<DateTime<Off2>> for DateTime<Off> {
    fn eq(&self, other: &DateTime<Off2>) -> bool { self.datetime == other.datetime }
}

impl<Off:Offset> Eq for DateTime<Off> {
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

impl<Off:Offset> Add<Duration> for DateTime<Off> {
    type Output = DateTime<Off>;

    fn add(self, rhs: Duration) -> DateTime<Off> {
        DateTime { datetime: self.datetime + rhs, offset: self.offset }
    }
}

impl<Off:Offset> Add<DateTime<Off>> for Duration {
    type Output = DateTime<Off>;

    #[inline]
    fn add(self, rhs: DateTime<Off>) -> DateTime<Off> { rhs.add(self) }
}

impl<Off:Offset, Off2:Offset> Sub<DateTime<Off2>> for DateTime<Off> {
    type Output = Duration;

    fn sub(self, rhs: DateTime<Off2>) -> Duration { self.datetime - rhs.datetime }
}

impl<Off:Offset> Sub<Duration> for DateTime<Off> {
    type Output = DateTime<Off>;

    #[inline]
    fn sub(self, rhs: Duration) -> DateTime<Off> { self.add(-rhs) }
}

impl<Off:Offset> fmt::Show for DateTime<Off> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.local(), self.offset)
    }
}

#[cfg(test)]
mod tests {
    use duration::Duration;
    use offset::{Offset, UTC, FixedOffset};

    #[test]
    #[allow(non_snake_case)]
    fn test_datetime_offset() {
        let EST = FixedOffset::east(5*60*60);
        let EDT = FixedOffset::east(4*60*60);

        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9).to_string(),
                   "2014-05-06T07:08:09Z".to_string());
        assert_eq!(EDT.ymd(2014, 5, 6).and_hms(7, 8, 9).to_string(),
                   "2014-05-06T07:08:09+04:00".to_string());
        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9), EDT.ymd(2014, 5, 6).and_hms(11, 8, 9));
        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9) + Duration::seconds(3600 + 60 + 1),
                   UTC.ymd(2014, 5, 6).and_hms(8, 9, 10));
        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9) - EDT.ymd(2014, 5, 6).and_hms(10, 11, 12),
                   Duration::seconds(3600 - 3*60 - 3));

        assert_eq!(*UTC.ymd(2014, 5, 6).and_hms(7, 8, 9).offset(), UTC);
        assert_eq!(*EDT.ymd(2014, 5, 6).and_hms(7, 8, 9).offset(), EDT);
        assert!(*EDT.ymd(2014, 5, 6).and_hms(7, 8, 9).offset() != EST);
    }
}

