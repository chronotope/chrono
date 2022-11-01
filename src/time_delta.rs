// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Temporal quantification
use core::ops::Add;
use core::time::Duration;

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

#[derive(Clone, Copy, PartialOrd, Ord, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
/// A delta in time based on [`core::time::Duration`] and a direction.
///
/// This is because when asking for the delta between
/// two points in time, because there is no way to fix the ordering of those two points
/// via the type system, the delta could be either forwards or backwards. Generally this type
/// should be immediately unpacked after being used, either via a `match`, asserting the direction
/// with either of [`TimeDelta::forwards`] or [`TimeDelta::backwards`], or taking the absolute
/// value with [`TimeDelta::abs`] to get the contained `Duration` which can then be used
/// with other [`crate::DateTime`] or [`crate::NaiveDateTime`] values via `Add`, `Sub` or other functions.
pub enum TimeDelta {
    /// A duration heading in forwards in time
    Forwards(Duration),
    /// A duration heading in backwards in time
    Backwards(Duration),
}

impl TimeDelta {
    // has to be a function as Duration::new is only const on rust >= 1.53
    /// The minimum possible `Duration` (Equivalent to the max but heading backwards)
    pub fn min() -> TimeDelta {
        TimeDelta::Backwards(Duration::new(core::u64::MAX, MAX_NANOS_NON_LEAP))
    }

    /// A duration of zero length.
    pub const ZERO: TimeDelta = TimeDelta::Forwards(Duration::from_nanos(0));

    // has to be a function as Duration::new is only const on rust >= 1.53
    /// The maximum possible `Duration`
    pub fn max() -> TimeDelta {
        TimeDelta::Forwards(Duration::new(core::u64::MAX, MAX_NANOS_NON_LEAP))
    }

    /// Assert that the direction is forwards and throw away the `Duration` otherwise.
    pub fn forwards(self) -> Option<Duration> {
        match self {
            TimeDelta::Forwards(f) => Some(f),
            TimeDelta::Backwards(_) => None,
        }
    }

    /// Assert that the direction is backwards and throw away the `Duration` otherwise.
    pub fn backwards(self) -> Option<Duration> {
        match self {
            TimeDelta::Forwards(_) => None,
            TimeDelta::Backwards(b) => Some(b),
        }
    }

    /// Get the contained `Duration`, no matter which direction
    #[inline]
    pub fn abs(&self) -> Duration {
        match self {
            TimeDelta::Forwards(d) => *d,
            TimeDelta::Backwards(d) => *d,
        }
    }

    /// Checks whether the `TimeDelta` is in a forwards direction
    pub fn is_forwards(&self) -> bool {
        // TODO: use matches!. Currently avoiding due to 1.38 MSRV
        if let TimeDelta::Forwards(_) = self {
            true
        } else {
            false
        }
    }

    /// Checks whether the `TimeDelta` is in a backwards direction
    pub fn is_backwards(&self) -> bool {
        // TODO: use matches!. Currently avoiding due to 1.38 MSRV
        if let TimeDelta::Backwards(_) = self {
            true
        } else {
            false
        }
    }

    /// Checks whether two `TimeDelta`s are in the same direction
    pub fn is_same_direction(&self, other: TimeDelta) -> bool {
        self.is_forwards() && other.is_forwards() || self.is_backwards() && other.is_backwards()
    }

    /// Returns a constructor for the direction of the `TimeDelta`
    pub fn direction(&self) -> fn(Duration) -> TimeDelta {
        match self {
            TimeDelta::Forwards(_) => TimeDelta::Forwards,
            TimeDelta::Backwards(_) => TimeDelta::Backwards,
        }
    }
}

impl PartialEq<TimeDelta> for TimeDelta {
    fn eq(&self, other: &TimeDelta) -> bool {
        match (self, other) {
            (TimeDelta::Forwards(f1), TimeDelta::Forwards(f2)) => f1 == f2,
            (TimeDelta::Backwards(b1), TimeDelta::Backwards(b2)) => b1 == b2,
            (TimeDelta::Forwards(lhs), TimeDelta::Backwards(rhs))
            | (TimeDelta::Backwards(lhs), TimeDelta::Forwards(rhs)) => {
                *lhs == Duration::from_nanos(0) && *rhs == Duration::from_nanos(0)
            }
        }
    }
}

impl Eq for TimeDelta {}

impl From<Duration> for TimeDelta {
    fn from(s: Duration) -> Self {
        TimeDelta::Forwards(s)
    }
}

// we `impl` add as it is useful within at least this codebase
impl Add<TimeDelta> for TimeDelta {
    type Output = TimeDelta;
    fn add(self, rhs: TimeDelta) -> Self::Output {
        if self.is_same_direction(rhs) {
            self.direction()(self.abs() + rhs.abs())
        } else if self.abs() > rhs.abs() {
            self.direction()(self.abs() - rhs.abs())
        } else {
            rhs.direction()(rhs.abs() - self.abs())
        }
    }
}

const MAX_NANOS_NON_LEAP: u32 = 999_999_999;
