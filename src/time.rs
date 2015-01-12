// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 time with timezone.
 */

use std::{fmt, hash};
use std::cmp::Ordering;
use std::ops::{Add, Sub};

use Timelike;
use offset::{Offset, OffsetState};
use duration::Duration;
use naive::time::NaiveTime;
use format::DelayedFormat;

/// ISO 8601 time with timezone.
#[derive(Clone)]
pub struct Time<Off: Offset> {
    time: NaiveTime,
    offset: Off::State,
}

impl<Off: Offset> Time<Off> {
    /// Makes a new `Time` with given *UTC* time and offset.
    /// The local time should be constructed via the `Offset` trait.
    //
    // note: this constructor is purposedly not named to `new` to discourage the direct usage.
    #[inline]
    pub fn from_utc(time: NaiveTime, offset: Off::State) -> Time<Off> {
        Time { time: time, offset: offset }
    }

    /// Retrieves an associated offset.
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
    /// This does not change the actual `Time` (but will change the string representation).
    #[inline]
    pub fn with_timezone<Off2: Offset>(&self, tz: &Off2) -> Time<Off2> {
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
fn map_local<Off: Offset, F>(t: &Time<Off>, mut f: F) -> Option<Time<Off>>
        where F: FnMut(NaiveTime) -> Option<NaiveTime> {
    f(t.naive_local()).and_then(|time| t.timezone().from_local_time(&time).single())
}

impl<Off: Offset> Time<Off> where Off::State: fmt::Display {
    /// Formats the time in the specified format string.
    /// See the `format` module on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&'a self, fmt: &'a str) -> DelayedFormat<'a> {
        DelayedFormat::new_with_offset(None, Some(self.naive_local()), &self.offset, fmt)
    }
}

impl<Off: Offset> Timelike for Time<Off> {
    #[inline] fn hour(&self) -> u32 { self.naive_local().hour() }
    #[inline] fn minute(&self) -> u32 { self.naive_local().minute() }
    #[inline] fn second(&self) -> u32 { self.naive_local().second() }
    #[inline] fn nanosecond(&self) -> u32 { self.naive_local().nanosecond() }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<Time<Off>> {
        map_local(self, |time| time.with_hour(hour))
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<Time<Off>> {
        map_local(self, |time| time.with_minute(min))
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<Time<Off>> {
        map_local(self, |time| time.with_second(sec))
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<Time<Off>> {
        map_local(self, |time| time.with_nanosecond(nano))
    }

    #[inline]
    fn num_seconds_from_midnight(&self) -> u32 { self.naive_local().num_seconds_from_midnight() }
}

impl<Off: Offset, Off2: Offset> PartialEq<Time<Off2>> for Time<Off> {
    fn eq(&self, other: &Time<Off2>) -> bool { self.time == other.time }
}

impl<Off: Offset> Eq for Time<Off> {
}

impl<Off: Offset> PartialOrd for Time<Off> {
    fn partial_cmp(&self, other: &Time<Off>) -> Option<Ordering> {
        self.time.partial_cmp(&other.time)
    }
}

impl<Off: Offset> Ord for Time<Off> {
    fn cmp(&self, other: &Time<Off>) -> Ordering { self.time.cmp(&other.time) }
}

impl<Off: Offset, H: hash::Hasher + hash::Writer> hash::Hash<H> for Time<Off> {
    fn hash(&self, state: &mut H) { self.time.hash(state) }
}

impl<Off: Offset> Add<Duration> for Time<Off> {
    type Output = Time<Off>;

    fn add(self, rhs: Duration) -> Time<Off> {
        Time { time: self.time + rhs, offset: self.offset }
    }
}

impl<Off: Offset, Off2: Offset> Sub<Time<Off2>> for Time<Off> {
    type Output = Duration;

    fn sub(self, rhs: Time<Off2>) -> Duration { self.time - rhs.time }
}

impl<Off: Offset> Sub<Duration> for Time<Off> {
    type Output = Time<Off>;

    #[inline]
    fn sub(self, rhs: Duration) -> Time<Off> { self.add(-rhs) }
}

impl<Off: Offset> fmt::Debug for Time<Off> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}{:?}", self.naive_local(), self.offset)
    }
}

impl<Off: Offset> fmt::Display for Time<Off> where Off::State: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.naive_local(), self.offset)
    }
}

