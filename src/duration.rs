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

use core::cmp::Ordering;
use core::convert::TryFrom;
use core::ops::{Add, Div, Mul, Neg, Sub};
use core::time::Duration;
use core::{fmt, i64};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

/// The number of nanoseconds in a microsecond.
const NANOS_PER_MICRO: i32 = 1000;
/// The number of nanoseconds in a millisecond.
const NANOS_PER_MILLI: i32 = 1_000_000;
/// The number of seconds in a minute.
const SECS_PER_MINUTE: i64 = 60;
/// The number of seconds in an hour.
const SECS_PER_HOUR: i64 = 3_600;
/// The number of (non-leap) seconds in days.
const SECS_PER_DAY: i64 = 8_6400;
/// The number of (non-leap) seconds in a week.
const SECS_PER_WEEK: i64 = 604_800;

const MAX_NANOS_NON_LEAP: u32 = 999_999_999;

/// ISO 8601 time duration with nanosecond precision.
///
/// This also allows for the negative duration; see individual methods for details.
#[derive(Clone, Copy, PartialOrd, Ord, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub enum TimeDelta {
    /// A duration heading in forwards in time
    Forwards(Duration),
    /// A duration heading in backwards in time
    Backwards(Duration),
}

// const MAX_CORE_DURATION: Duration = MAX_SECONDS_DURATION + Duration::from_nanos(999_999_999);

impl TimeDelta {
    // has to be a function as Duration::new is only const on rust >= 1.53
    /// The minimum possible `Duration` (Equivalent to the max but heading backwards)
    pub fn min() -> TimeDelta {
        TimeDelta::Backwards(Duration::new(
            #[allow(deprecated)]
            core::u64::MAX,
            MAX_NANOS_NON_LEAP,
        ))
    }

    /// A duration of zero length.
    pub const ZERO: TimeDelta = TimeDelta::Forwards(Duration::from_nanos(0));

    // has to be a function as Duration::new is only const on rust >= 1.53
    /// The maximum possible `Duration`
    pub fn max() -> TimeDelta {
        TimeDelta::Forwards(Duration::new(
            #[allow(deprecated)]
            core::u64::MAX,
            MAX_NANOS_NON_LEAP,
        ))
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

impl TimeDelta {
    /// Makes a new `Duration` with given number of weeks.
    /// Equivalent to `Duration::seconds(weeks * 7 * 24 * 60 * 60)` with overflow checks.
    /// Panics when the duration is out of bounds.
    #[inline]
    pub fn weeks(weeks: i64) -> TimeDelta {
        let secs = weeks.checked_mul(SECS_PER_WEEK).expect("Duration::weeks out of bounds");
        TimeDelta::seconds(secs)
    }

    /// Makes a new `Duration` with given number of days.
    /// Equivalent to `Duration::seconds(days * 24 * 60 * 60)` with overflow checks.
    /// Panics when the duration is out of bounds.
    #[inline]
    pub fn days(days: i64) -> TimeDelta {
        let secs = days.checked_mul(SECS_PER_DAY).expect("Duration::days out of bounds");
        TimeDelta::seconds(secs)
    }

    /// Makes a new `Duration` with given number of hours.
    /// Equivalent to `Duration::seconds(hours * 60 * 60)` with overflow checks.
    /// Panics when the duration is out of bounds.
    #[inline]
    pub fn hours(hours: i64) -> TimeDelta {
        let secs = hours.checked_mul(SECS_PER_HOUR).expect("Duration::hours ouf of bounds");
        TimeDelta::seconds(secs)
    }

    /// Makes a new `Duration` with given number of minutes.
    /// Equivalent to `Duration::seconds(minutes * 60)` with overflow checks.
    /// Panics when the duration is out of bounds.
    #[inline]
    pub fn minutes(minutes: i64) -> TimeDelta {
        let secs = minutes.checked_mul(SECS_PER_MINUTE).expect("Duration::minutes out of bounds");
        TimeDelta::seconds(secs)
    }

    /// Makes a new `Duration` with given number of seconds.
    /// Panics when the duration is more than `i64::MAX` seconds
    /// or less than `i64::MIN` seconds.
    #[inline]
    pub fn seconds(seconds: i64) -> TimeDelta {
        match seconds.cmp(&0) {
            Ordering::Greater => {
                TimeDelta::Forwards(Duration::from_secs(u64::try_from(seconds).unwrap()))
            }
            Ordering::Less => TimeDelta::Backwards(Duration::from_secs(
                u64::try_from(i128::from(seconds).abs()).unwrap(),
            )),
            Ordering::Equal => TimeDelta::ZERO,
        }
    }

    /// Makes a new `Duration` with given number of milliseconds.
    #[inline]
    pub fn milliseconds(milliseconds: i64) -> TimeDelta {
        match milliseconds.cmp(&0) {
            Ordering::Greater => {
                TimeDelta::Forwards(Duration::from_millis(u64::try_from(milliseconds).unwrap()))
            }
            Ordering::Less => TimeDelta::Backwards(Duration::from_millis(
                u64::try_from(i128::from(milliseconds).abs()).unwrap(),
            )),
            Ordering::Equal => TimeDelta::ZERO,
        }
    }

    /// Makes a new `Duration` with given number of microseconds.
    #[inline]
    pub fn microseconds(microseconds: i64) -> TimeDelta {
        match microseconds.cmp(&0) {
            Ordering::Greater => {
                TimeDelta::Forwards(Duration::from_micros(u64::try_from(microseconds).unwrap()))
            }
            Ordering::Less => TimeDelta::Backwards(Duration::from_micros(
                u64::try_from(i128::from(microseconds).abs()).unwrap(),
            )),
            Ordering::Equal => TimeDelta::ZERO,
        }
    }

    /// Makes a new `Duration` with given number of nanoseconds.
    #[inline]
    pub fn nanoseconds(nanos: i64) -> TimeDelta {
        match nanos.cmp(&0) {
            Ordering::Greater => {
                TimeDelta::Forwards(Duration::from_nanos(u64::try_from(nanos).unwrap()))
            }
            Ordering::Less => TimeDelta::Backwards(Duration::from_nanos(
                u64::try_from(i128::from(nanos).abs()).unwrap(),
            )),
            Ordering::Equal => TimeDelta::ZERO,
        }
    }

    /// Returns the total number of whole weeks in the duration.
    #[inline]
    pub fn num_weeks(&self) -> i64 {
        self.num_days() / 7
    }

    /// Returns the total number of whole days in the duration.
    pub fn num_days(&self) -> i64 {
        self.num_seconds() / SECS_PER_DAY
    }

    /// Returns the total number of whole hours in the duration.
    #[inline]
    pub fn num_hours(&self) -> i64 {
        self.num_seconds() / SECS_PER_HOUR
    }

    /// Returns the total number of whole minutes in the duration.
    #[inline]
    pub fn num_minutes(&self) -> i64 {
        self.num_seconds() / SECS_PER_MINUTE
    }

    /// Returns the total number of whole seconds in the duration.
    pub fn num_seconds(&self) -> i64 {
        match self {
            TimeDelta::Forwards(d) => i64::try_from(d.as_secs()).expect(""),
            TimeDelta::Backwards(d) => -i64::try_from(d.as_secs()).expect(""),
        }
    }

    // /// Returns the number of nanoseconds such that
    // /// `nanos_mod_sec() + num_seconds() * NANOS_PER_SEC` is the total number of
    // /// nanoseconds in the duration.
    // fn nanos_mod_sec(&self) -> i32 {
    //     if self.secs < 0 && self.nanos > 0 {
    //         self.nanos - NANOS_PER_SEC
    //     } else {
    //         self.nanos
    //     }
    // }

    /// Returns the total number of whole milliseconds in the duration,
    pub fn num_milliseconds(&self) -> i64 {
        match self {
            TimeDelta::Forwards(d) => i64::try_from(d.as_millis()).expect(""),
            TimeDelta::Backwards(d) => {
                -i64::try_from(i128::try_from(d.as_millis()).expect("")).expect("")
            }
        }
    }

    /// Returns the total number of whole microseconds in the duration,
    /// or `None` on overflow (exceeding 2^63 microseconds in either direction).
    pub fn num_microseconds(&self) -> Option<i64> {
        match self {
            TimeDelta::Forwards(d) => i64::try_from(d.as_micros()).ok(),
            TimeDelta::Backwards(d) => {
                i128::try_from(d.as_micros()).ok().map(Neg::neg).and_then(|n| i64::try_from(n).ok())
            }
        }
    }

    /// Returns the total number of whole nanoseconds in the duration,
    /// or `None` on overflow (exceeding 2^63 nanoseconds in either direction).
    pub fn num_nanoseconds(&self) -> Option<i64> {
        match self {
            TimeDelta::Forwards(d) => i64::try_from(d.as_nanos()).ok(),
            TimeDelta::Backwards(d) => {
                i128::try_from(d.as_nanos()).ok().map(Neg::neg).and_then(|n| i64::try_from(n).ok())
            }
        }
    }

    /// Add two durations, returning `None` if overflow occurred.
    pub fn checked_add(&self, rhs: &TimeDelta) -> Option<TimeDelta> {
        match (self, rhs) {
            (TimeDelta::Forwards(d), TimeDelta::Forwards(r)) => {
                d.checked_add(*r).map(TimeDelta::Forwards)
            }
            (TimeDelta::Backwards(d), TimeDelta::Backwards(r)) => {
                d.checked_add(*r).map(TimeDelta::Backwards)
            }
            (TimeDelta::Forwards(d), TimeDelta::Backwards(r)) if d > r => {
                d.checked_sub(*r).map(TimeDelta::Forwards)
            }
            (TimeDelta::Forwards(d), TimeDelta::Backwards(r)) if d < r => {
                r.checked_sub(*d).map(TimeDelta::Backwards)
            }
            (TimeDelta::Forwards(_), TimeDelta::Backwards(_)) => Some(TimeDelta::ZERO),
            (TimeDelta::Backwards(d), TimeDelta::Forwards(r)) if d < r => {
                r.checked_sub(*d).map(TimeDelta::Forwards)
            }
            (TimeDelta::Backwards(d), TimeDelta::Forwards(r)) if d > r => {
                d.checked_sub(*r).map(TimeDelta::Backwards)
            }
            (TimeDelta::Backwards(_), TimeDelta::Forwards(_)) => Some(TimeDelta::ZERO),
        }
    }

    /// Subtract two durations, returning `None` if overflow occurred.
    pub fn checked_sub(&self, rhs: &TimeDelta) -> Option<TimeDelta> {
        self.checked_add(&Neg::neg(*rhs))
    }

    // /// The minimum possible `Duration`: `i64::MIN` milliseconds.
    // #[inline]
    // pub fn min_value() -> TimeDelta {
    //     TimeDelta::min()
    // }

    // /// The maximum possible `Duration`: `i64::MAX` milliseconds.
    // #[inline]
    // pub fn max_value() -> TimeDelta {
    //     TimeDelta::max()
    // }

    // /// A duration where the stored seconds and nanoseconds are equal to zero.
    // #[inline]
    // pub fn ZERO -> TimeDelta {
    //     TimeDelta::ZERO
    // }

    /// Returns `true` if the duration equals `Duration::ZERO`.
    #[inline]
    pub fn is_zero(&self) -> bool {
        match self {
            TimeDelta::Forwards(d) => d.as_nanos() == 0,
            TimeDelta::Backwards(d) => d.as_nanos() == 0,
        }
    }

    /// Creates a `std::time::Duration` object from `time::Duration`
    ///
    /// This function errors when duration is less than zero. As standard
    /// library implementation is limited to non-negative values.
    #[inline]
    pub fn abs(&self) -> Duration {
        match self {
            TimeDelta::Forwards(d) => *d,
            TimeDelta::Backwards(d) => *d,
        }
    }
}

impl Neg for TimeDelta {
    type Output = TimeDelta;

    #[inline]
    fn neg(self) -> TimeDelta {
        match self {
            TimeDelta::Forwards(d) => TimeDelta::Backwards(d),
            TimeDelta::Backwards(d) => TimeDelta::Forwards(d),
        }
    }
}

impl<T> Add<T> for TimeDelta
where
    T: Into<TimeDelta>,
{
    type Output = TimeDelta;

    fn add(self, rhs: T) -> TimeDelta {
        self.checked_add(&rhs.into()).expect("")
    }
}

impl<T> Sub<T> for TimeDelta
where
    T: Into<TimeDelta>,
{
    type Output = TimeDelta;

    fn sub(self, rhs: T) -> TimeDelta {
        self.checked_sub(&rhs.into()).expect("")
    }
}

impl Mul<i32> for TimeDelta {
    type Output = TimeDelta;

    fn mul(self, rhs: i32) -> TimeDelta {
        match rhs.cmp(&0) {
            Ordering::Equal => TimeDelta::ZERO,
            Ordering::Greater => match self {
                TimeDelta::Forwards(d) => TimeDelta::Forwards(d * u32::try_from(rhs).unwrap()),
                TimeDelta::Backwards(d) => TimeDelta::Backwards(d * u32::try_from(rhs).unwrap()),
            },
            Ordering::Less => match self {
                TimeDelta::Forwards(d) => {
                    TimeDelta::Backwards(d * u32::try_from(i64::from(rhs).abs()).unwrap())
                }
                TimeDelta::Backwards(d) => {
                    TimeDelta::Forwards(d * u32::try_from(i64::from(rhs).abs()).unwrap())
                }
            },
        }
    }
}

impl Div<i32> for TimeDelta {
    type Output = TimeDelta;

    fn div(self, rhs: i32) -> TimeDelta {
        let quot = u32::try_from(i64::from(rhs).abs()).expect("u32(abs(i32)) will always succeed");
        match (self, rhs.cmp(&0)) {
            (_, Ordering::Equal) => panic!("Divide by zero"),
            (TimeDelta::Forwards(d), Ordering::Less) => TimeDelta::Backwards(d / quot),
            (TimeDelta::Forwards(d), Ordering::Greater) => TimeDelta::Forwards(d / quot),
            (TimeDelta::Backwards(d), Ordering::Less) => TimeDelta::Forwards(d / quot),
            (TimeDelta::Backwards(d), Ordering::Greater) => TimeDelta::Backwards(d / quot),
        }
    }
}

#[cfg(any(feature = "std", test))]
impl<'a> std::iter::Sum<&'a TimeDelta> for TimeDelta {
    fn sum<I: Iterator<Item = &'a TimeDelta>>(iter: I) -> TimeDelta {
        iter.fold(TimeDelta::ZERO, |acc, x| acc + *x)
    }
}

#[cfg(any(feature = "std", test))]
impl std::iter::Sum<TimeDelta> for TimeDelta {
    fn sum<I: Iterator<Item = TimeDelta>>(iter: I) -> TimeDelta {
        iter.fold(TimeDelta::ZERO, |acc, x| acc + x)
    }
}

impl fmt::Display for TimeDelta {
    /// Format a duration using the [ISO 8601] format
    ///
    /// [ISO 8601]: https://en.wikipedia.org/wiki/ISO_8601#Durations
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let dur = self.abs();

        let days = dur.as_secs() / u64::try_from(SECS_PER_DAY).unwrap();
        let remaining_seconds = dur.as_secs() - days * u64::try_from(SECS_PER_DAY).unwrap();
        let hasdate = days != 0;
        let hastime = (remaining_seconds != 0 || dur.subsec_nanos() != 0) || !hasdate;

        if let TimeDelta::Forwards(_) = self {
            write!(f, "P")?;
        } else {
            // technically speaking, negative duration is not valid ISO 8601,
            // so should we instead just base this on the abs value of the duration
            // and remove this branch??
            write!(f, "-P")?;
        }

        if hasdate {
            write!(f, "{}D", days)?;
        }

        if hastime {
            if dur.subsec_nanos() == 0 {
                write!(f, "T{}S", remaining_seconds)?;
            } else if dur.subsec_nanos() % u32::try_from(NANOS_PER_MILLI).unwrap() == 0 {
                write!(
                    f,
                    "T{}.{:03}S",
                    remaining_seconds,
                    dur.subsec_nanos() / u32::try_from(NANOS_PER_MILLI).unwrap()
                )?;
            } else if dur.subsec_nanos() % u32::try_from(NANOS_PER_MICRO).unwrap() == 0 {
                write!(
                    f,
                    "T{}.{:06}S",
                    remaining_seconds,
                    dur.subsec_nanos() / u32::try_from(NANOS_PER_MICRO).unwrap()
                )?;
            } else {
                write!(f, "T{}.{:09}S", remaining_seconds, dur.subsec_nanos())?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{TimeDelta, MAX_NANOS_NON_LEAP};
    use std::time::Duration;
    use std::{i32, i64};

    #[test]
    fn test_duration() {
        assert!(TimeDelta::seconds(1) != TimeDelta::ZERO);
        assert_eq!(TimeDelta::seconds(1) + TimeDelta::seconds(2), TimeDelta::seconds(3));
        assert_eq!(
            TimeDelta::seconds(86399) + TimeDelta::seconds(4),
            TimeDelta::days(1) + TimeDelta::seconds(3)
        );
        assert_eq!(TimeDelta::days(10) - TimeDelta::seconds(1000), TimeDelta::seconds(863000));
        assert_eq!(TimeDelta::days(10) - TimeDelta::seconds(1000000), TimeDelta::seconds(-136000));
        assert_eq!(
            TimeDelta::days(2) + TimeDelta::seconds(86399) + TimeDelta::nanoseconds(1234567890),
            TimeDelta::days(3) + TimeDelta::nanoseconds(234567890)
        );
        assert_eq!(-TimeDelta::days(3), TimeDelta::days(-3));
        assert_eq!(
            -(TimeDelta::days(3) + TimeDelta::seconds(70)),
            TimeDelta::days(-4) + TimeDelta::seconds(86400 - 70)
        );
    }

    #[test]
    fn test_duration_num_days() {
        assert_eq!(TimeDelta::ZERO.num_days(), 0);
        assert_eq!(TimeDelta::days(1).num_days(), 1);
        assert_eq!(TimeDelta::days(-1).num_days(), -1);
        assert_eq!(TimeDelta::seconds(86399).num_days(), 0);
        assert_eq!(TimeDelta::seconds(86401).num_days(), 1);
        assert_eq!(TimeDelta::seconds(-86399).num_days(), 0);
        assert_eq!(TimeDelta::seconds(-86401).num_days(), -1);
        assert_eq!(TimeDelta::days(i32::MAX as i64).num_days(), i32::MAX as i64);
        assert_eq!(TimeDelta::days(i32::MIN as i64).num_days(), i32::MIN as i64);
    }

    #[test]
    fn test_duration_num_seconds() {
        assert_eq!(TimeDelta::ZERO.num_seconds(), 0);
        assert_eq!(TimeDelta::seconds(1).num_seconds(), 1);
        assert_eq!(TimeDelta::seconds(-1).num_seconds(), -1);
        assert_eq!(TimeDelta::milliseconds(999).num_seconds(), 0);
        assert_eq!(TimeDelta::milliseconds(1001).num_seconds(), 1);
        assert_eq!(TimeDelta::milliseconds(-999).num_seconds(), 0);
        assert_eq!(TimeDelta::milliseconds(-1001).num_seconds(), -1);
    }

    #[test]
    fn test_duration_num_milliseconds() {
        assert_eq!(TimeDelta::ZERO.num_milliseconds(), 0);
        assert_eq!(TimeDelta::milliseconds(1).num_milliseconds(), 1);
        assert_eq!(TimeDelta::milliseconds(-1).num_milliseconds(), -1);
        assert_eq!(TimeDelta::microseconds(999).num_milliseconds(), 0);
        assert_eq!(TimeDelta::microseconds(1001).num_milliseconds(), 1);
        assert_eq!(TimeDelta::microseconds(-999).num_milliseconds(), 0);
        assert_eq!(TimeDelta::microseconds(-1001).num_milliseconds(), -1);
        assert_eq!(TimeDelta::milliseconds(i64::MAX).num_milliseconds(), i64::MAX);
        assert_eq!(TimeDelta::milliseconds(i64::MIN + 1).num_milliseconds(), i64::MIN + 1);
        // assert_eq!(MAX.num_milliseconds(), i64::MAX);
        // assert_eq!(MIN.num_milliseconds(), i64::MIN);
    }

    #[test]
    fn test_duration_num_microseconds() {
        assert_eq!(TimeDelta::ZERO.num_microseconds(), Some(0));
        assert_eq!(TimeDelta::microseconds(1).num_microseconds(), Some(1));
        assert_eq!(TimeDelta::microseconds(-1).num_microseconds(), Some(-1));
        assert_eq!(TimeDelta::nanoseconds(999).num_microseconds(), Some(0));
        assert_eq!(TimeDelta::nanoseconds(1001).num_microseconds(), Some(1));
        assert_eq!(TimeDelta::nanoseconds(-999).num_microseconds(), Some(0));
        assert_eq!(TimeDelta::nanoseconds(-1001).num_microseconds(), Some(-1));
        assert_eq!(TimeDelta::microseconds(i64::MAX).num_microseconds(), Some(i64::MAX));
        assert_eq!(TimeDelta::microseconds(i64::MIN + 1).num_microseconds(), Some(i64::MIN + 1));
        assert_eq!(TimeDelta::max().num_microseconds(), None);
        assert_eq!(TimeDelta::min().num_microseconds(), None);

        // overflow checks
        const MICROS_PER_DAY: i64 = 86_400_000_000;
        assert_eq!(
            TimeDelta::days(i64::MAX / MICROS_PER_DAY).num_microseconds(),
            Some(i64::MAX / MICROS_PER_DAY * MICROS_PER_DAY)
        );
        assert_eq!(
            TimeDelta::days(i64::MIN / MICROS_PER_DAY).num_microseconds(),
            Some(i64::MIN / MICROS_PER_DAY * MICROS_PER_DAY)
        );
        assert_eq!(TimeDelta::days(i64::MAX / MICROS_PER_DAY + 1).num_microseconds(), None);
        assert_eq!(TimeDelta::days(i64::MIN / MICROS_PER_DAY - 1).num_microseconds(), None);
    }

    #[test]
    fn test_duration_num_nanoseconds() {
        assert_eq!(TimeDelta::ZERO.num_nanoseconds(), Some(0));
        assert_eq!(TimeDelta::nanoseconds(1).num_nanoseconds(), Some(1));
        assert_eq!(TimeDelta::nanoseconds(-1).num_nanoseconds(), Some(-1));
        assert_eq!(TimeDelta::nanoseconds(i64::MAX).num_nanoseconds(), Some(i64::MAX));
        assert_eq!(TimeDelta::nanoseconds(i64::MIN).num_nanoseconds(), Some(i64::MIN));
        assert_eq!(TimeDelta::max().num_nanoseconds(), None);
        assert_eq!(TimeDelta::min().num_nanoseconds(), None);

        // overflow checks
        const NANOS_PER_DAY: i64 = 86_400_000_000_000;
        assert_eq!(
            TimeDelta::days(i64::MAX / NANOS_PER_DAY).num_nanoseconds(),
            Some(i64::MAX / NANOS_PER_DAY * NANOS_PER_DAY)
        );
        assert_eq!(
            TimeDelta::days(i64::MIN / NANOS_PER_DAY).num_nanoseconds(),
            Some(i64::MIN / NANOS_PER_DAY * NANOS_PER_DAY)
        );
        assert_eq!(TimeDelta::days(i64::MAX / NANOS_PER_DAY + 1).num_nanoseconds(), None);
        assert_eq!(TimeDelta::days(i64::MIN / NANOS_PER_DAY - 1).num_nanoseconds(), None);
    }

    #[test]
    fn test_duration_checked_ops() {
        assert_eq!(
            TimeDelta::milliseconds(i64::MAX).checked_add(&TimeDelta::microseconds(999)),
            Some(TimeDelta::milliseconds(i64::MAX - 1) + TimeDelta::microseconds(1999))
        );
        assert!(TimeDelta::max().checked_add(&TimeDelta::milliseconds(1)).is_none());

        assert_eq!(
            TimeDelta::milliseconds(i64::MIN + 1).checked_sub(&TimeDelta::milliseconds(1)),
            Some(TimeDelta::milliseconds(i64::MIN))
        );
        // assert!(TimeDelta::milliseconds(i64::MIN).checked_sub(&TimeDelta::milliseconds(i64::MAX)).is_none());
    }

    #[test]
    #[allow(clippy::erasing_op)]
    fn test_duration_mul() {
        assert_eq!(TimeDelta::ZERO * i32::MAX, TimeDelta::ZERO);
        assert_eq!(TimeDelta::ZERO * i32::MIN, TimeDelta::ZERO);
        assert_eq!(TimeDelta::nanoseconds(1) * 0, TimeDelta::ZERO);
        assert_eq!(TimeDelta::nanoseconds(1) * 1, TimeDelta::nanoseconds(1));
        assert_eq!(TimeDelta::nanoseconds(1) * 1_000_000_000, TimeDelta::seconds(1));
        assert_eq!(TimeDelta::nanoseconds(1) * -1_000_000_000, -TimeDelta::seconds(1));
        assert_eq!(-TimeDelta::nanoseconds(1) * 1_000_000_000, -TimeDelta::seconds(1));
        assert_eq!(
            TimeDelta::nanoseconds(30) * 333_333_333,
            TimeDelta::seconds(10) - TimeDelta::nanoseconds(10)
        );
        assert_eq!(
            (TimeDelta::nanoseconds(1) + TimeDelta::seconds(1) + TimeDelta::days(1)) * 3,
            TimeDelta::nanoseconds(3) + TimeDelta::seconds(3) + TimeDelta::days(3)
        );
        assert_eq!(TimeDelta::milliseconds(1500) * -2, TimeDelta::seconds(-3));
        assert_eq!(TimeDelta::milliseconds(-1500) * 2, TimeDelta::seconds(-3));
    }

    #[test]
    fn test_duration_div() {
        assert_eq!(TimeDelta::ZERO / i32::MAX, TimeDelta::ZERO);
        assert_eq!(TimeDelta::ZERO / i32::MIN, TimeDelta::ZERO);
        assert_eq!(TimeDelta::nanoseconds(123_456_789) / 1, TimeDelta::nanoseconds(123_456_789));
        assert_eq!(TimeDelta::nanoseconds(123_456_789) / -1, -TimeDelta::nanoseconds(123_456_789));
        assert_eq!(-TimeDelta::nanoseconds(123_456_789) / -1, TimeDelta::nanoseconds(123_456_789));
        assert_eq!(-TimeDelta::nanoseconds(123_456_789) / 1, -TimeDelta::nanoseconds(123_456_789));
        assert_eq!(TimeDelta::seconds(1) / 3, TimeDelta::nanoseconds(333_333_333));
        assert_eq!(TimeDelta::seconds(4) / 3, TimeDelta::nanoseconds(1_333_333_333));
        assert_eq!(TimeDelta::seconds(-1) / 2, TimeDelta::milliseconds(-500));
        assert_eq!(TimeDelta::seconds(1) / -2, TimeDelta::milliseconds(-500));
        assert_eq!(TimeDelta::seconds(-1) / -2, TimeDelta::milliseconds(500));
        assert_eq!(TimeDelta::seconds(-4) / 3, TimeDelta::nanoseconds(-1_333_333_333));
        assert_eq!(TimeDelta::seconds(-4) / -3, TimeDelta::nanoseconds(1_333_333_333));
    }

    #[test]
    fn test_duration_sum() {
        let duration_list_1 = [TimeDelta::ZERO, TimeDelta::seconds(1)];
        let sum_1: TimeDelta = duration_list_1.iter().sum();
        assert_eq!(sum_1, TimeDelta::seconds(1));

        let duration_list_2 =
            [TimeDelta::ZERO, TimeDelta::seconds(1), TimeDelta::seconds(6), TimeDelta::seconds(10)];
        let sum_2: TimeDelta = duration_list_2.iter().sum();
        assert_eq!(sum_2, TimeDelta::seconds(17));

        let duration_vec = vec![
            TimeDelta::ZERO,
            TimeDelta::seconds(1),
            TimeDelta::seconds(6),
            TimeDelta::seconds(10),
        ];
        let sum_3: TimeDelta = duration_vec.into_iter().sum();
        assert_eq!(sum_3, TimeDelta::seconds(17));
    }

    #[test]
    fn test_duration_fmt() {
        assert_eq!(TimeDelta::ZERO.to_string(), "PT0S");
        assert_eq!(TimeDelta::days(42).to_string(), "P42D");
        assert_eq!(TimeDelta::days(-42).to_string(), "-P42D");
        assert_eq!(TimeDelta::seconds(42).to_string(), "PT42S");
        assert_eq!(TimeDelta::milliseconds(42).to_string(), "PT0.042S");
        assert_eq!(TimeDelta::microseconds(42).to_string(), "PT0.000042S");
        assert_eq!(TimeDelta::nanoseconds(42).to_string(), "PT0.000000042S");
        assert_eq!((TimeDelta::days(7) + TimeDelta::milliseconds(6543)).to_string(), "P7DT6.543S");
        assert_eq!(TimeDelta::seconds(-86401).to_string(), "-P1DT1S");
        assert_eq!(TimeDelta::nanoseconds(-1).to_string(), "-PT0.000000001S");

        // the format specifier should have no effect on `Duration`
        assert_eq!(
            format!("{:30}", TimeDelta::days(1) + TimeDelta::milliseconds(2345)),
            "P1DT2.345S"
        );
    }

    #[test]
    fn test_to_std() {
        assert_eq!(TimeDelta::seconds(1).abs(), Duration::new(1, 0));
        assert_eq!(TimeDelta::seconds(86401).abs(), Duration::new(86401, 0));
        assert_eq!(TimeDelta::milliseconds(123).abs(), Duration::new(0, 123000000));
        assert_eq!(TimeDelta::milliseconds(123765).abs(), Duration::new(123, 765000000));
        assert_eq!(TimeDelta::nanoseconds(777).abs(), Duration::new(0, 777));
        assert_eq!(
            TimeDelta::max().abs(),
            Duration::new(
                #[allow(deprecated)]
                core::u64::MAX,
                MAX_NANOS_NON_LEAP
            )
        );
        assert_eq!(TimeDelta::seconds(-1).abs(), Duration::from_secs(1));
        assert_eq!(TimeDelta::milliseconds(-1).abs(), Duration::from_millis(1));
    }

    #[test]
    fn test_from_std() {
        assert_eq!((TimeDelta::seconds(1)), TimeDelta::from(Duration::new(1, 0)));
        assert_eq!((TimeDelta::seconds(86401)), TimeDelta::from(Duration::new(86401, 0)));
        assert_eq!((TimeDelta::milliseconds(123)), TimeDelta::from(Duration::new(0, 123000000)));
        assert_eq!(
            (TimeDelta::milliseconds(123765)),
            TimeDelta::from(Duration::new(123, 765000000))
        );
        assert_eq!((TimeDelta::nanoseconds(777)), TimeDelta::from(Duration::new(0, 777)));
        assert_eq!(
            TimeDelta::max(),
            TimeDelta::from(Duration::new(
                #[allow(deprecated)]
                core::u64::MAX,
                MAX_NANOS_NON_LEAP
            ))
        );
    }
}
