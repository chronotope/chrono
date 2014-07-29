// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 time with timezone.
 */

use std::{fmt, hash};

use Timelike;
use offset::Offset;
use duration::Duration;
use naive::time::NaiveTime;

/// ISO 8601 time with timezone.
#[deriving(Clone)]
pub struct Time<Off> {
    time: NaiveTime,
    offset: Off,
}

impl<Off:Offset> Time<Off> {
    /// Makes a new `Time` with given *UTC* time and offset.
    /// The local time should be constructed via the `Offset` trait.
    #[inline]
    pub fn from_utc(time: NaiveTime, offset: Off) -> Time<Off> {
        Time { time: time, offset: offset }
    }

    /// Returns a view to the local time.
    fn local(&self) -> NaiveTime {
        self.offset.to_local_time(&self.time)
    }
}

impl<Off:Offset> Timelike for Time<Off> {
    #[inline] fn hour(&self) -> u32 { self.local().hour() }
    #[inline] fn minute(&self) -> u32 { self.local().minute() }
    #[inline] fn second(&self) -> u32 { self.local().second() }
    #[inline] fn nanosecond(&self) -> u32 { self.local().nanosecond() }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<Time<Off>> {
        self.local().with_hour(hour)
            .and_then(|time| self.offset.from_local_time(&time).single())
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<Time<Off>> {
        self.local().with_minute(min)
            .and_then(|time| self.offset.from_local_time(&time).single())
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<Time<Off>> {
        self.local().with_second(sec)
            .and_then(|time| self.offset.from_local_time(&time).single())
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<Time<Off>> {
        self.local().with_nanosecond(nano)
            .and_then(|time| self.offset.from_local_time(&time).single())
    }

    #[inline]
    fn num_seconds_from_midnight(&self) -> u32 { self.local().num_seconds_from_midnight() }
}

impl<Off:Offset> PartialEq for Time<Off> {
    fn eq(&self, other: &Time<Off>) -> bool { self.time == other.time }
}

impl<Off:Offset> Eq for Time<Off> {
}

impl<Off:Offset, Off2:Offset> Equiv<Time<Off2>> for Time<Off> {
    fn equiv(&self, other: &Time<Off2>) -> bool { self.time == other.time }
}

impl<Off:Offset> PartialOrd for Time<Off> {
    fn partial_cmp(&self, other: &Time<Off>) -> Option<Ordering> {
        self.time.partial_cmp(&other.time)
    }
}

impl<Off:Offset> Ord for Time<Off> {
    fn cmp(&self, other: &Time<Off>) -> Ordering { self.time.cmp(&other.time) }
}

impl<Off:Offset> hash::Hash for Time<Off> {
    fn hash(&self, state: &mut hash::sip::SipState) { self.time.hash(state) }
}

impl<Off:Offset> Add<Duration,Time<Off>> for Time<Off> {
    fn add(&self, rhs: &Duration) -> Time<Off> {
        Time { time: self.time + *rhs, offset: self.offset.clone() }
    }
}

/*
// Rust issue #7590, the current coherence checker can't handle multiple Add impls
impl<Off:Offset> Add<Time<Off>,Time<Off>> for Duration {
    #[inline]
    fn add(&self, rhs: &Time<Off>) -> Time<Off> { rhs.add(self) }
}
*/

impl<Off:Offset, Off2:Offset> Sub<Time<Off2>,Duration> for Time<Off> {
    fn sub(&self, rhs: &Time<Off2>) -> Duration {
        self.time - rhs.time
    }
}

impl<Off:Offset> fmt::Show for Time<Off> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.local(), self.offset)
    }
}

