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
use offset::{Offset, OffsetState};
use duration::Duration;
use naive::datetime::NaiveDateTime;
use time::Time;
use date::Date;
use format::DelayedFormat;

/// ISO 8601 combined date and time with timezone.
#[derive(Clone)]
pub struct DateTime<Off: Offset> {
    datetime: NaiveDateTime,
    offset: Off::State,
}

impl<Off: Offset> DateTime<Off> {
    /// Makes a new `DateTime` with given *UTC* datetime and offset.
    /// The local datetime should be constructed via the `Offset` trait.
    //
    // note: this constructor is purposedly not named to `new` to discourage the direct usage.
    #[inline]
    pub fn from_utc(datetime: NaiveDateTime, offset: Off::State) -> DateTime<Off> {
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

    /// Retrieves an associated offset state.
    #[inline]
    pub fn offset<'a>(&'a self) -> &'a Off::State {
        &self.offset
    }

    /// Retrieves an associated offset.
    #[inline]
    pub fn timezone(&self) -> Off {
        Offset::from_state(&self.offset)
    }

    /// Changes the associated offset.
    /// This does not change the actual `DateTime` (but will change the string representation).
    #[inline]
    pub fn with_timezone<Off2: Offset>(&self, tz: &Off2) -> DateTime<Off2> {
        tz.from_utc_datetime(&self.datetime)
    }

    /// Returns a view to the naive UTC datetime.
    #[inline]
    pub fn naive_utc(&self) -> NaiveDateTime {
        self.datetime
    }

    /// Returns a view to the naive local datetime.
    #[inline]
    pub fn naive_local(&self) -> NaiveDateTime {
        self.datetime + self.offset.local_minus_utc()
    }
}

/// Maps the local datetime to other datetime with given conversion function.
fn map_local<Off: Offset, F>(dt: &DateTime<Off>, mut f: F) -> Option<DateTime<Off>>
        where F: FnMut(NaiveDateTime) -> Option<NaiveDateTime> {
    f(dt.naive_local()).and_then(|datetime| dt.timezone().from_local_datetime(&datetime).single())
}

impl<Off: Offset> DateTime<Off> where Off::State: fmt::Display {
    /// Formats the combined date and time in the specified format string.
    /// See the `format` module on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&'a self, fmt: &'a str) -> DelayedFormat<'a> {
        let local = self.naive_local();
        DelayedFormat::new_with_offset(Some(local.date()), Some(local.time()), &self.offset, fmt)
    }
}

impl<Off: Offset> Datelike for DateTime<Off> {
    #[inline] fn year(&self) -> i32 { self.naive_local().year() }
    #[inline] fn month(&self) -> u32 { self.naive_local().month() }
    #[inline] fn month0(&self) -> u32 { self.naive_local().month0() }
    #[inline] fn day(&self) -> u32 { self.naive_local().day() }
    #[inline] fn day0(&self) -> u32 { self.naive_local().day0() }
    #[inline] fn ordinal(&self) -> u32 { self.naive_local().ordinal() }
    #[inline] fn ordinal0(&self) -> u32 { self.naive_local().ordinal0() }
    #[inline] fn weekday(&self) -> Weekday { self.naive_local().weekday() }
    #[inline] fn isoweekdate(&self) -> (i32, u32, Weekday) { self.naive_local().isoweekdate() }

    #[inline]
    fn with_year(&self, year: i32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_year(year))
    }

    #[inline]
    fn with_month(&self, month: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_month(month))
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_month0(month0))
    }

    #[inline]
    fn with_day(&self, day: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_day(day))
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_day0(day0))
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_ordinal(ordinal))
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_ordinal0(ordinal0))
    }
}

impl<Off: Offset> Timelike for DateTime<Off> {
    #[inline] fn hour(&self) -> u32 { self.naive_local().hour() }
    #[inline] fn minute(&self) -> u32 { self.naive_local().minute() }
    #[inline] fn second(&self) -> u32 { self.naive_local().second() }
    #[inline] fn nanosecond(&self) -> u32 { self.naive_local().nanosecond() }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_hour(hour))
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_minute(min))
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_second(sec))
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<DateTime<Off>> {
        map_local(self, |datetime| datetime.with_nanosecond(nano))
    }
}

impl<Off: Offset, Off2: Offset> PartialEq<DateTime<Off2>> for DateTime<Off> {
    fn eq(&self, other: &DateTime<Off2>) -> bool { self.datetime == other.datetime }
}

impl<Off: Offset> Eq for DateTime<Off> {
}

impl<Off: Offset> PartialOrd for DateTime<Off> {
    fn partial_cmp(&self, other: &DateTime<Off>) -> Option<Ordering> {
        self.datetime.partial_cmp(&other.datetime)
    }
}

impl<Off: Offset> Ord for DateTime<Off> {
    fn cmp(&self, other: &DateTime<Off>) -> Ordering { self.datetime.cmp(&other.datetime) }
}

impl<Off: Offset, H: hash::Hasher + hash::Writer> hash::Hash<H> for DateTime<Off> {
    fn hash(&self, state: &mut H) { self.datetime.hash(state) }
}

impl<Off: Offset> Add<Duration> for DateTime<Off> {
    type Output = DateTime<Off>;

    fn add(self, rhs: Duration) -> DateTime<Off> {
        DateTime { datetime: self.datetime + rhs, offset: self.offset }
    }
}

impl<Off: Offset, Off2: Offset> Sub<DateTime<Off2>> for DateTime<Off> {
    type Output = Duration;

    fn sub(self, rhs: DateTime<Off2>) -> Duration { self.datetime - rhs.datetime }
}

impl<Off: Offset> Sub<Duration> for DateTime<Off> {
    type Output = DateTime<Off>;

    #[inline]
    fn sub(self, rhs: Duration) -> DateTime<Off> { self.add(-rhs) }
}

impl<Off: Offset> fmt::Debug for DateTime<Off> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}{:?}", self.naive_local(), self.offset)
    }
}

impl<Off: Offset> fmt::Display for DateTime<Off> where Off::State: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.naive_local(), self.offset)
    }
}

#[cfg(test)]
mod tests {
    use {Datelike};
    use duration::Duration;
    use offset::Offset;
    use offset::utc::UTC;
    use offset::local::Local;
    use offset::fixed::FixedOffset;

    #[test]
    #[allow(non_snake_case)]
    fn test_datetime_offset() {
        let EST = FixedOffset::east(5*60*60);
        let EDT = FixedOffset::east(4*60*60);

        assert_eq!(format!("{}", UTC.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06 07:08:09 UTC");
        assert_eq!(format!("{}", EDT.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06 07:08:09 +04:00");
        assert_eq!(format!("{:?}", UTC.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06T07:08:09Z");
        assert_eq!(format!("{:?}", EDT.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06T07:08:09+04:00");

        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9), EDT.ymd(2014, 5, 6).and_hms(11, 8, 9));
        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9) + Duration::seconds(3600 + 60 + 1),
                   UTC.ymd(2014, 5, 6).and_hms(8, 9, 10));
        assert_eq!(UTC.ymd(2014, 5, 6).and_hms(7, 8, 9) - EDT.ymd(2014, 5, 6).and_hms(10, 11, 12),
                   Duration::seconds(3600 - 3*60 - 3));

        assert_eq!(*UTC.ymd(2014, 5, 6).and_hms(7, 8, 9).offset(), UTC);
        assert_eq!(*EDT.ymd(2014, 5, 6).and_hms(7, 8, 9).offset(), EDT);
        assert!(*EDT.ymd(2014, 5, 6).and_hms(7, 8, 9).offset() != EST);
    }

    #[test]
    fn test_datetime_fmt_with_local() {
        // if we are not around the year boundary, local and UTC date should have the same year
        let dt = Local::now().with_month(5).unwrap();
        assert_eq!(dt.format("%Y").to_string(), dt.with_timezone(&UTC).format("%Y").to_string());
    }
}

