// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 time with time zone.
 */

use std::{fmt, hash};
use std::cmp::Ordering;
use std::ops::{Add, Sub};

use Timelike;
use offset::{TimeZone, Offset};
use duration::Duration;
use naive::time::NaiveTime;
use format::DelayedFormat;

/// ISO 8601 time with timezone.
#[derive(Clone)]
pub struct Time<Tz: TimeZone> {
    time: NaiveTime,
    offset: Tz::Offset,
}

impl<Tz: TimeZone> Time<Tz> {
    /// Makes a new `Time` with given *UTC* time and offset.
    /// The local time should be constructed via the `TimeZone` trait.
    //
    // note: this constructor is purposedly not named to `new` to discourage the direct usage.
    #[inline]
    pub fn from_utc(time: NaiveTime, offset: Tz::Offset) -> Time<Tz> {
        Time { time: time, offset: offset }
    }

    /// Retrieves an associated offset from UTC.
    #[inline]
    pub fn offset<'a>(&'a self) -> &'a Tz::Offset {
        &self.offset
    }

    /// Retrieves an associated time zone.
    #[inline]
    pub fn timezone(&self) -> Tz {
        TimeZone::from_offset(&self.offset)
    }

    /// Changes the associated time zone.
    /// This does not change the actual `Time` (but will change the string representation).
    #[inline]
    pub fn with_timezone<Tz2: TimeZone>(&self, tz: &Tz2) -> Time<Tz2> {
        tz.from_utc_time(&self.time)
    }

    /// Returns a view to the naive UTC time.
    #[inline]
    pub fn naive_utc(&self) -> NaiveTime {
        self.time
    }

    /// Returns a view to the naive local time.
    #[inline]
    pub fn naive_local(&self) -> NaiveTime {
        self.time + self.offset.local_minus_utc()
    }
}

/// Maps the local time to other time with given conversion function.
fn map_local<Tz: TimeZone, F>(t: &Time<Tz>, mut f: F) -> Option<Time<Tz>>
        where F: FnMut(NaiveTime) -> Option<NaiveTime> {
    f(t.naive_local()).and_then(|time| t.timezone().from_local_time(&time).single())
}

impl<Tz: TimeZone> Time<Tz> where Tz::Offset: fmt::Display {
    /// Formats the time in the specified format string.
    /// See the `format` module on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&'a self, fmt: &'a str) -> DelayedFormat<'a> {
        DelayedFormat::new_with_offset(None, Some(self.naive_local()), &self.offset, fmt)
    }
}

impl<Tz: TimeZone> Timelike for Time<Tz> {
    #[inline] fn hour(&self) -> u32 { self.naive_local().hour() }
    #[inline] fn minute(&self) -> u32 { self.naive_local().minute() }
    #[inline] fn second(&self) -> u32 { self.naive_local().second() }
    #[inline] fn nanosecond(&self) -> u32 { self.naive_local().nanosecond() }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<Time<Tz>> {
        map_local(self, |time| time.with_hour(hour))
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<Time<Tz>> {
        map_local(self, |time| time.with_minute(min))
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<Time<Tz>> {
        map_local(self, |time| time.with_second(sec))
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<Time<Tz>> {
        map_local(self, |time| time.with_nanosecond(nano))
    }

    #[inline]
    fn num_seconds_from_midnight(&self) -> u32 { self.naive_local().num_seconds_from_midnight() }
}

impl<Tz: TimeZone, Tz2: TimeZone> PartialEq<Time<Tz2>> for Time<Tz> {
    fn eq(&self, other: &Time<Tz2>) -> bool { self.time == other.time }
}

impl<Tz: TimeZone> Eq for Time<Tz> {
}

impl<Tz: TimeZone> PartialOrd for Time<Tz> {
    fn partial_cmp(&self, other: &Time<Tz>) -> Option<Ordering> {
        self.time.partial_cmp(&other.time)
    }
}

impl<Tz: TimeZone> Ord for Time<Tz> {
    fn cmp(&self, other: &Time<Tz>) -> Ordering { self.time.cmp(&other.time) }
}

impl<Tz: TimeZone, H: hash::Hasher + hash::Writer> hash::Hash<H> for Time<Tz> {
    fn hash(&self, state: &mut H) { self.time.hash(state) }
}

impl<Tz: TimeZone> Add<Duration> for Time<Tz> {
    type Output = Time<Tz>;

    fn add(self, rhs: Duration) -> Time<Tz> {
        Time { time: self.time + rhs, offset: self.offset }
    }
}

impl<Tz: TimeZone, Tz2: TimeZone> Sub<Time<Tz2>> for Time<Tz> {
    type Output = Duration;

    fn sub(self, rhs: Time<Tz2>) -> Duration { self.time - rhs.time }
}

impl<Tz: TimeZone> Sub<Duration> for Time<Tz> {
    type Output = Time<Tz>;

    #[inline]
    fn sub(self, rhs: Duration) -> Time<Tz> { self.add(-rhs) }
}

impl<Tz: TimeZone> fmt::Debug for Time<Tz> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}{:?}", self.naive_local(), self.offset)
    }
}

impl<Tz: TimeZone> fmt::Display for Time<Tz> where Tz::Offset: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.naive_local(), self.offset)
    }
}

