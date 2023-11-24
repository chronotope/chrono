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

use core::ops::{Add, Div, Mul, Neg, Sub};
use core::time::Duration as StdDuration;
use core::{fmt, i64};
#[cfg(feature = "std")]
use std::error::Error;

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

/// The number of nanoseconds in a microsecond.
const NANOS_PER_MICRO: i32 = 1000;
/// The number of nanoseconds in a millisecond.
const NANOS_PER_MILLI: i32 = 1_000_000;
/// The number of nanoseconds in seconds.
const NANOS_PER_SEC: i32 = 1_000_000_000;
/// The number of microseconds per second.
const MICROS_PER_SEC: i64 = 1_000_000;
/// The number of milliseconds per second.
const MILLIS_PER_SEC: i64 = 1000;
/// The number of seconds in a minute.
const SECS_PER_MINUTE: i64 = 60;
/// The number of seconds in an hour.
const SECS_PER_HOUR: i64 = 3600;
/// The number of (non-leap) seconds in days.
const SECS_PER_DAY: i64 = 86_400;
/// The number of (non-leap) seconds in a week.
const SECS_PER_WEEK: i64 = 604_800;

macro_rules! try_opt {
    ($e:expr) => {
        match $e {
            Some(v) => v,
            None => return None,
        }
    };
}

/// ISO 8601 time duration with nanosecond precision.
///
/// This also allows for the negative duration; see individual methods for details.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
#[cfg_attr(
    feature = "rkyv",
    archive_attr(derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash))
)]
#[cfg_attr(feature = "borsh", derive(borsh::BorshDeserialize, borsh::BorshSerialize))]
pub struct TimeDelta {
    secs: i64,
    nanos: i32, // Always 0 <= nanos < NANOS_PER_SEC
}

/// The minimum possible `TimeDelta`: `i64::MIN` milliseconds.
pub(crate) const MIN: TimeDelta = TimeDelta {
    secs: i64::MIN / MILLIS_PER_SEC - 1,
    nanos: NANOS_PER_SEC + (i64::MIN % MILLIS_PER_SEC) as i32 * NANOS_PER_MILLI,
};

/// The maximum possible `TimeDelta`: `i64::MAX` milliseconds.
pub(crate) const MAX: TimeDelta = TimeDelta {
    secs: i64::MAX / MILLIS_PER_SEC,
    nanos: (i64::MAX % MILLIS_PER_SEC) as i32 * NANOS_PER_MILLI,
};

impl TimeDelta {
    /// Makes a new `TimeDelta` with given number of weeks.
    /// Equivalent to `TimeDelta::seconds(weeks * 7 * 24 * 60 * 60)` with overflow checks.
    /// Panics when the duration is out of bounds.
    #[inline]
    #[must_use]
    pub fn weeks(weeks: i64) -> TimeDelta {
        let secs = weeks.checked_mul(SECS_PER_WEEK).expect("TimeDelta::weeks out of bounds");
        TimeDelta::seconds(secs)
    }

    /// Makes a new `TimeDelta` with given number of days.
    /// Equivalent to `TimeDelta::seconds(days * 24 * 60 * 60)` with overflow checks.
    /// Panics when the duration is out of bounds.
    #[inline]
    #[must_use]
    pub fn days(days: i64) -> TimeDelta {
        let secs = days.checked_mul(SECS_PER_DAY).expect("TimeDelta::days out of bounds");
        TimeDelta::seconds(secs)
    }

    /// Makes a new `TimeDelta` with given number of hours.
    /// Equivalent to `TimeDelta::seconds(hours * 60 * 60)` with overflow checks.
    /// Panics when the duration is out of bounds.
    #[inline]
    #[must_use]
    pub fn hours(hours: i64) -> TimeDelta {
        let secs = hours.checked_mul(SECS_PER_HOUR).expect("TimeDelta::hours ouf of bounds");
        TimeDelta::seconds(secs)
    }

    /// Makes a new `TimeDelta` with given number of minutes.
    /// Equivalent to `TimeDelta::seconds(minutes * 60)` with overflow checks.
    /// Panics when the duration is out of bounds.
    #[inline]
    #[must_use]
    pub fn minutes(minutes: i64) -> TimeDelta {
        let secs = minutes.checked_mul(SECS_PER_MINUTE).expect("TimeDelta::minutes out of bounds");
        TimeDelta::seconds(secs)
    }

    /// Makes a new `TimeDelta` with given number of seconds.
    /// Panics when the duration is more than `i64::MAX` milliseconds
    /// or less than `i64::MIN` milliseconds.
    #[inline]
    #[must_use]
    pub fn seconds(seconds: i64) -> TimeDelta {
        let d = TimeDelta { secs: seconds, nanos: 0 };
        if d < MIN || d > MAX {
            panic!("TimeDelta::seconds out of bounds");
        }
        d
    }

    /// Makes a new `TimeDelta` with given number of milliseconds.
    #[inline]
    pub const fn milliseconds(milliseconds: i64) -> TimeDelta {
        let (secs, millis) = div_mod_floor_64(milliseconds, MILLIS_PER_SEC);
        let nanos = millis as i32 * NANOS_PER_MILLI;
        TimeDelta { secs, nanos }
    }

    /// Makes a new `TimeDelta` with given number of microseconds.
    #[inline]
    pub const fn microseconds(microseconds: i64) -> TimeDelta {
        let (secs, micros) = div_mod_floor_64(microseconds, MICROS_PER_SEC);
        let nanos = micros as i32 * NANOS_PER_MICRO;
        TimeDelta { secs, nanos }
    }

    /// Makes a new `TimeDelta` with given number of nanoseconds.
    #[inline]
    pub const fn nanoseconds(nanos: i64) -> TimeDelta {
        let (secs, nanos) = div_mod_floor_64(nanos, NANOS_PER_SEC as i64);
        TimeDelta { secs, nanos: nanos as i32 }
    }

    /// Returns the total number of whole weeks in the duration.
    #[inline]
    pub const fn num_weeks(&self) -> i64 {
        self.num_days() / 7
    }

    /// Returns the total number of whole days in the duration.
    pub const fn num_days(&self) -> i64 {
        self.num_seconds() / SECS_PER_DAY
    }

    /// Returns the total number of whole hours in the duration.
    #[inline]
    pub const fn num_hours(&self) -> i64 {
        self.num_seconds() / SECS_PER_HOUR
    }

    /// Returns the total number of whole minutes in the duration.
    #[inline]
    pub const fn num_minutes(&self) -> i64 {
        self.num_seconds() / SECS_PER_MINUTE
    }

    /// Returns the total number of whole seconds in the duration.
    pub const fn num_seconds(&self) -> i64 {
        // If secs is negative, nanos should be subtracted from the duration.
        if self.secs < 0 && self.nanos > 0 {
            self.secs + 1
        } else {
            self.secs
        }
    }

    /// Returns the number of nanoseconds such that
    /// `nanos_mod_sec() + num_seconds() * NANOS_PER_SEC` is the total number of
    /// nanoseconds in the duration.
    const fn nanos_mod_sec(&self) -> i32 {
        if self.secs < 0 && self.nanos > 0 {
            self.nanos - NANOS_PER_SEC
        } else {
            self.nanos
        }
    }

    /// Returns the total number of whole milliseconds in the duration,
    pub const fn num_milliseconds(&self) -> i64 {
        // A proper TimeDelta will not overflow, because MIN and MAX are defined
        // such that the range is exactly i64 milliseconds.
        let secs_part = self.num_seconds() * MILLIS_PER_SEC;
        let nanos_part = self.nanos_mod_sec() / NANOS_PER_MILLI;
        secs_part + nanos_part as i64
    }

    /// Returns the total number of whole microseconds in the duration,
    /// or `None` on overflow (exceeding 2^63 microseconds in either direction).
    pub const fn num_microseconds(&self) -> Option<i64> {
        let secs_part = try_opt!(self.num_seconds().checked_mul(MICROS_PER_SEC));
        let nanos_part = self.nanos_mod_sec() / NANOS_PER_MICRO;
        secs_part.checked_add(nanos_part as i64)
    }

    /// Returns the total number of whole nanoseconds in the duration,
    /// or `None` on overflow (exceeding 2^63 nanoseconds in either direction).
    pub const fn num_nanoseconds(&self) -> Option<i64> {
        let secs_part = try_opt!(self.num_seconds().checked_mul(NANOS_PER_SEC as i64));
        let nanos_part = self.nanos_mod_sec();
        secs_part.checked_add(nanos_part as i64)
    }

    /// Add two durations, returning `None` if overflow occurred.
    #[must_use]
    pub fn checked_add(&self, rhs: &TimeDelta) -> Option<TimeDelta> {
        let mut secs = try_opt!(self.secs.checked_add(rhs.secs));
        let mut nanos = self.nanos + rhs.nanos;
        if nanos >= NANOS_PER_SEC {
            nanos -= NANOS_PER_SEC;
            secs = try_opt!(secs.checked_add(1));
        }
        let d = TimeDelta { secs, nanos };
        // Even if d is within the bounds of i64 seconds,
        // it might still overflow i64 milliseconds.
        if d < MIN || d > MAX {
            None
        } else {
            Some(d)
        }
    }

    /// Subtract two durations, returning `None` if overflow occurred.
    #[must_use]
    pub fn checked_sub(&self, rhs: &TimeDelta) -> Option<TimeDelta> {
        let mut secs = try_opt!(self.secs.checked_sub(rhs.secs));
        let mut nanos = self.nanos - rhs.nanos;
        if nanos < 0 {
            nanos += NANOS_PER_SEC;
            secs = try_opt!(secs.checked_sub(1));
        }
        let d = TimeDelta { secs, nanos };
        // Even if d is within the bounds of i64 seconds,
        // it might still overflow i64 milliseconds.
        if d < MIN || d > MAX {
            None
        } else {
            Some(d)
        }
    }

    /// Returns the duration as an absolute (non-negative) value.
    #[inline]
    pub const fn abs(&self) -> TimeDelta {
        if self.secs < 0 && self.nanos != 0 {
            TimeDelta { secs: (self.secs + 1).abs(), nanos: NANOS_PER_SEC - self.nanos }
        } else {
            TimeDelta { secs: self.secs.abs(), nanos: self.nanos }
        }
    }

    /// The minimum possible `TimeDelta`: `i64::MIN` milliseconds.
    #[inline]
    pub const fn min_value() -> TimeDelta {
        MIN
    }

    /// The maximum possible `TimeDelta`: `i64::MAX` milliseconds.
    #[inline]
    pub const fn max_value() -> TimeDelta {
        MAX
    }

    /// A duration where the stored seconds and nanoseconds are equal to zero.
    #[inline]
    pub const fn zero() -> TimeDelta {
        TimeDelta { secs: 0, nanos: 0 }
    }

    /// Returns `true` if the duration equals `TimeDelta::zero()`.
    #[inline]
    pub const fn is_zero(&self) -> bool {
        self.secs == 0 && self.nanos == 0
    }

    /// Creates a `TimeDelta` object from `std::time::Duration`
    ///
    /// This function errors when original duration is larger than the maximum
    /// value supported for this type.
    pub fn from_std(duration: StdDuration) -> Result<TimeDelta, OutOfRangeError> {
        // We need to check secs as u64 before coercing to i64
        if duration.as_secs() > MAX.secs as u64 {
            return Err(OutOfRangeError(()));
        }
        let d =
            TimeDelta { secs: duration.as_secs() as i64, nanos: duration.subsec_nanos() as i32 };
        if d > MAX {
            return Err(OutOfRangeError(()));
        }
        Ok(d)
    }

    /// Creates a `std::time::Duration` object from `TimeDelta`
    ///
    /// This function errors when duration is less than zero. As standard
    /// library implementation is limited to non-negative values.
    pub fn to_std(&self) -> Result<StdDuration, OutOfRangeError> {
        if self.secs < 0 {
            return Err(OutOfRangeError(()));
        }
        Ok(StdDuration::new(self.secs as u64, self.nanos as u32))
    }
}

impl Neg for TimeDelta {
    type Output = TimeDelta;

    #[inline]
    fn neg(self) -> TimeDelta {
        if self.nanos == 0 {
            TimeDelta { secs: -self.secs, nanos: 0 }
        } else {
            TimeDelta { secs: -self.secs - 1, nanos: NANOS_PER_SEC - self.nanos }
        }
    }
}

impl Add for TimeDelta {
    type Output = TimeDelta;

    fn add(self, rhs: TimeDelta) -> TimeDelta {
        let mut secs = self.secs + rhs.secs;
        let mut nanos = self.nanos + rhs.nanos;
        if nanos >= NANOS_PER_SEC {
            nanos -= NANOS_PER_SEC;
            secs += 1;
        }
        TimeDelta { secs, nanos }
    }
}

impl Sub for TimeDelta {
    type Output = TimeDelta;

    fn sub(self, rhs: TimeDelta) -> TimeDelta {
        let mut secs = self.secs - rhs.secs;
        let mut nanos = self.nanos - rhs.nanos;
        if nanos < 0 {
            nanos += NANOS_PER_SEC;
            secs -= 1;
        }
        TimeDelta { secs, nanos }
    }
}

impl Mul<i32> for TimeDelta {
    type Output = TimeDelta;

    fn mul(self, rhs: i32) -> TimeDelta {
        // Multiply nanoseconds as i64, because it cannot overflow that way.
        let total_nanos = self.nanos as i64 * rhs as i64;
        let (extra_secs, nanos) = div_mod_floor_64(total_nanos, NANOS_PER_SEC as i64);
        let secs = self.secs * rhs as i64 + extra_secs;
        TimeDelta { secs, nanos: nanos as i32 }
    }
}

impl Div<i32> for TimeDelta {
    type Output = TimeDelta;

    fn div(self, rhs: i32) -> TimeDelta {
        let mut secs = self.secs / rhs as i64;
        let carry = self.secs - secs * rhs as i64;
        let extra_nanos = carry * NANOS_PER_SEC as i64 / rhs as i64;
        let mut nanos = self.nanos / rhs + extra_nanos as i32;
        if nanos >= NANOS_PER_SEC {
            nanos -= NANOS_PER_SEC;
            secs += 1;
        }
        if nanos < 0 {
            nanos += NANOS_PER_SEC;
            secs -= 1;
        }
        TimeDelta { secs, nanos }
    }
}

impl<'a> core::iter::Sum<&'a TimeDelta> for TimeDelta {
    fn sum<I: Iterator<Item = &'a TimeDelta>>(iter: I) -> TimeDelta {
        iter.fold(TimeDelta::zero(), |acc, x| acc + *x)
    }
}

impl core::iter::Sum<TimeDelta> for TimeDelta {
    fn sum<I: Iterator<Item = TimeDelta>>(iter: I) -> TimeDelta {
        iter.fold(TimeDelta::zero(), |acc, x| acc + x)
    }
}

impl fmt::Display for TimeDelta {
    /// Format a duration using the [ISO 8601] format
    ///
    /// [ISO 8601]: https://en.wikipedia.org/wiki/ISO_8601#Durations
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // technically speaking, negative duration is not valid ISO 8601,
        // but we need to print it anyway.
        let (abs, sign) = if self.secs < 0 { (-*self, "-") } else { (*self, "") };

        let days = abs.secs / SECS_PER_DAY;
        let secs = abs.secs - days * SECS_PER_DAY;
        let hasdate = days != 0;
        let hastime = (secs != 0 || abs.nanos != 0) || !hasdate;

        write!(f, "{}P", sign)?;

        if hasdate {
            write!(f, "{}D", days)?;
        }
        if hastime {
            if abs.nanos == 0 {
                write!(f, "T{}S", secs)?;
            } else if abs.nanos % NANOS_PER_MILLI == 0 {
                write!(f, "T{}.{:03}S", secs, abs.nanos / NANOS_PER_MILLI)?;
            } else if abs.nanos % NANOS_PER_MICRO == 0 {
                write!(f, "T{}.{:06}S", secs, abs.nanos / NANOS_PER_MICRO)?;
            } else {
                write!(f, "T{}.{:09}S", secs, abs.nanos)?;
            }
        }
        Ok(())
    }
}

/// Represents error when converting `TimeDelta` to/from a standard library
/// implementation
///
/// The `std::time::Duration` supports a range from zero to `u64::MAX`
/// *seconds*, while this module supports signed range of up to
/// `i64::MAX` of *milliseconds*.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OutOfRangeError(());

impl fmt::Display for OutOfRangeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Source duration value is out of range for the target type")
    }
}

#[cfg(feature = "std")]
impl Error for OutOfRangeError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "out of range error"
    }
}

#[inline]
const fn div_mod_floor_64(this: i64, other: i64) -> (i64, i64) {
    (this.div_euclid(other), this.rem_euclid(other))
}

#[cfg(feature = "arbitrary")]
impl arbitrary::Arbitrary<'_> for TimeDelta {
    fn arbitrary(u: &mut arbitrary::Unstructured) -> arbitrary::Result<TimeDelta> {
        const MIN_SECS: i64 = i64::MIN / MILLIS_PER_SEC - 1;
        const MAX_SECS: i64 = i64::MAX / MILLIS_PER_SEC;

        let secs: i64 = u.int_in_range(MIN_SECS..=MAX_SECS)?;
        let nanos: i32 = u.int_in_range(0..=(NANOS_PER_SEC - 1))?;
        let duration = TimeDelta { secs, nanos };

        if duration < MIN || duration > MAX {
            Err(arbitrary::Error::IncorrectFormat)
        } else {
            Ok(duration)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::OutOfRangeError;
    use super::{TimeDelta, MAX, MIN};
    use core::time::Duration as StdDuration;

    #[test]
    fn test_duration() {
        assert!(TimeDelta::seconds(1) != TimeDelta::zero());
        assert_eq!(TimeDelta::seconds(1) + TimeDelta::seconds(2), TimeDelta::seconds(3));
        assert_eq!(
            TimeDelta::seconds(86_399) + TimeDelta::seconds(4),
            TimeDelta::days(1) + TimeDelta::seconds(3)
        );
        assert_eq!(TimeDelta::days(10) - TimeDelta::seconds(1000), TimeDelta::seconds(863_000));
        assert_eq!(
            TimeDelta::days(10) - TimeDelta::seconds(1_000_000),
            TimeDelta::seconds(-136_000)
        );
        assert_eq!(
            TimeDelta::days(2) + TimeDelta::seconds(86_399) + TimeDelta::nanoseconds(1_234_567_890),
            TimeDelta::days(3) + TimeDelta::nanoseconds(234_567_890)
        );
        assert_eq!(-TimeDelta::days(3), TimeDelta::days(-3));
        assert_eq!(
            -(TimeDelta::days(3) + TimeDelta::seconds(70)),
            TimeDelta::days(-4) + TimeDelta::seconds(86_400 - 70)
        );
    }

    #[test]
    fn test_duration_num_days() {
        assert_eq!(TimeDelta::zero().num_days(), 0);
        assert_eq!(TimeDelta::days(1).num_days(), 1);
        assert_eq!(TimeDelta::days(-1).num_days(), -1);
        assert_eq!(TimeDelta::seconds(86_399).num_days(), 0);
        assert_eq!(TimeDelta::seconds(86_401).num_days(), 1);
        assert_eq!(TimeDelta::seconds(-86_399).num_days(), 0);
        assert_eq!(TimeDelta::seconds(-86_401).num_days(), -1);
        assert_eq!(TimeDelta::days(i32::MAX as i64).num_days(), i32::MAX as i64);
        assert_eq!(TimeDelta::days(i32::MIN as i64).num_days(), i32::MIN as i64);
    }

    #[test]
    fn test_duration_num_seconds() {
        assert_eq!(TimeDelta::zero().num_seconds(), 0);
        assert_eq!(TimeDelta::seconds(1).num_seconds(), 1);
        assert_eq!(TimeDelta::seconds(-1).num_seconds(), -1);
        assert_eq!(TimeDelta::milliseconds(999).num_seconds(), 0);
        assert_eq!(TimeDelta::milliseconds(1001).num_seconds(), 1);
        assert_eq!(TimeDelta::milliseconds(-999).num_seconds(), 0);
        assert_eq!(TimeDelta::milliseconds(-1001).num_seconds(), -1);
    }

    #[test]
    fn test_duration_num_milliseconds() {
        assert_eq!(TimeDelta::zero().num_milliseconds(), 0);
        assert_eq!(TimeDelta::milliseconds(1).num_milliseconds(), 1);
        assert_eq!(TimeDelta::milliseconds(-1).num_milliseconds(), -1);
        assert_eq!(TimeDelta::microseconds(999).num_milliseconds(), 0);
        assert_eq!(TimeDelta::microseconds(1001).num_milliseconds(), 1);
        assert_eq!(TimeDelta::microseconds(-999).num_milliseconds(), 0);
        assert_eq!(TimeDelta::microseconds(-1001).num_milliseconds(), -1);
        assert_eq!(TimeDelta::milliseconds(i64::MAX).num_milliseconds(), i64::MAX);
        assert_eq!(TimeDelta::milliseconds(i64::MIN).num_milliseconds(), i64::MIN);
        assert_eq!(MAX.num_milliseconds(), i64::MAX);
        assert_eq!(MIN.num_milliseconds(), i64::MIN);
    }

    #[test]
    fn test_duration_num_microseconds() {
        assert_eq!(TimeDelta::zero().num_microseconds(), Some(0));
        assert_eq!(TimeDelta::microseconds(1).num_microseconds(), Some(1));
        assert_eq!(TimeDelta::microseconds(-1).num_microseconds(), Some(-1));
        assert_eq!(TimeDelta::nanoseconds(999).num_microseconds(), Some(0));
        assert_eq!(TimeDelta::nanoseconds(1001).num_microseconds(), Some(1));
        assert_eq!(TimeDelta::nanoseconds(-999).num_microseconds(), Some(0));
        assert_eq!(TimeDelta::nanoseconds(-1001).num_microseconds(), Some(-1));
        assert_eq!(TimeDelta::microseconds(i64::MAX).num_microseconds(), Some(i64::MAX));
        assert_eq!(TimeDelta::microseconds(i64::MIN).num_microseconds(), Some(i64::MIN));
        assert_eq!(MAX.num_microseconds(), None);
        assert_eq!(MIN.num_microseconds(), None);

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
        assert_eq!(TimeDelta::zero().num_nanoseconds(), Some(0));
        assert_eq!(TimeDelta::nanoseconds(1).num_nanoseconds(), Some(1));
        assert_eq!(TimeDelta::nanoseconds(-1).num_nanoseconds(), Some(-1));
        assert_eq!(TimeDelta::nanoseconds(i64::MAX).num_nanoseconds(), Some(i64::MAX));
        assert_eq!(TimeDelta::nanoseconds(i64::MIN).num_nanoseconds(), Some(i64::MIN));
        assert_eq!(MAX.num_nanoseconds(), None);
        assert_eq!(MIN.num_nanoseconds(), None);

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
            TimeDelta::milliseconds(i64::MAX - 1).checked_add(&TimeDelta::microseconds(999)),
            Some(TimeDelta::milliseconds(i64::MAX - 2) + TimeDelta::microseconds(1999))
        );
        assert!(TimeDelta::milliseconds(i64::MAX)
            .checked_add(&TimeDelta::microseconds(1000))
            .is_none());

        assert_eq!(
            TimeDelta::milliseconds(i64::MIN).checked_sub(&TimeDelta::milliseconds(0)),
            Some(TimeDelta::milliseconds(i64::MIN))
        );
        assert!(TimeDelta::milliseconds(i64::MIN)
            .checked_sub(&TimeDelta::milliseconds(1))
            .is_none());
    }

    #[test]
    fn test_duration_abs() {
        assert_eq!(TimeDelta::milliseconds(1300).abs(), TimeDelta::milliseconds(1300));
        assert_eq!(TimeDelta::milliseconds(1000).abs(), TimeDelta::milliseconds(1000));
        assert_eq!(TimeDelta::milliseconds(300).abs(), TimeDelta::milliseconds(300));
        assert_eq!(TimeDelta::milliseconds(0).abs(), TimeDelta::milliseconds(0));
        assert_eq!(TimeDelta::milliseconds(-300).abs(), TimeDelta::milliseconds(300));
        assert_eq!(TimeDelta::milliseconds(-700).abs(), TimeDelta::milliseconds(700));
        assert_eq!(TimeDelta::milliseconds(-1000).abs(), TimeDelta::milliseconds(1000));
        assert_eq!(TimeDelta::milliseconds(-1300).abs(), TimeDelta::milliseconds(1300));
        assert_eq!(TimeDelta::milliseconds(-1700).abs(), TimeDelta::milliseconds(1700));
    }

    #[test]
    #[allow(clippy::erasing_op)]
    fn test_duration_mul() {
        assert_eq!(TimeDelta::zero() * i32::MAX, TimeDelta::zero());
        assert_eq!(TimeDelta::zero() * i32::MIN, TimeDelta::zero());
        assert_eq!(TimeDelta::nanoseconds(1) * 0, TimeDelta::zero());
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
        assert_eq!(TimeDelta::zero() / i32::MAX, TimeDelta::zero());
        assert_eq!(TimeDelta::zero() / i32::MIN, TimeDelta::zero());
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
        let duration_list_1 = [TimeDelta::zero(), TimeDelta::seconds(1)];
        let sum_1: TimeDelta = duration_list_1.iter().sum();
        assert_eq!(sum_1, TimeDelta::seconds(1));

        let duration_list_2 = [
            TimeDelta::zero(),
            TimeDelta::seconds(1),
            TimeDelta::seconds(6),
            TimeDelta::seconds(10),
        ];
        let sum_2: TimeDelta = duration_list_2.iter().sum();
        assert_eq!(sum_2, TimeDelta::seconds(17));

        let duration_arr = [
            TimeDelta::zero(),
            TimeDelta::seconds(1),
            TimeDelta::seconds(6),
            TimeDelta::seconds(10),
        ];
        let sum_3: TimeDelta = duration_arr.into_iter().sum();
        assert_eq!(sum_3, TimeDelta::seconds(17));
    }

    #[test]
    fn test_duration_fmt() {
        assert_eq!(TimeDelta::zero().to_string(), "PT0S");
        assert_eq!(TimeDelta::days(42).to_string(), "P42D");
        assert_eq!(TimeDelta::days(-42).to_string(), "-P42D");
        assert_eq!(TimeDelta::seconds(42).to_string(), "PT42S");
        assert_eq!(TimeDelta::milliseconds(42).to_string(), "PT0.042S");
        assert_eq!(TimeDelta::microseconds(42).to_string(), "PT0.000042S");
        assert_eq!(TimeDelta::nanoseconds(42).to_string(), "PT0.000000042S");
        assert_eq!((TimeDelta::days(7) + TimeDelta::milliseconds(6543)).to_string(), "P7DT6.543S");
        assert_eq!(TimeDelta::seconds(-86_401).to_string(), "-P1DT1S");
        assert_eq!(TimeDelta::nanoseconds(-1).to_string(), "-PT0.000000001S");

        // the format specifier should have no effect on `TimeDelta`
        assert_eq!(
            format!("{:30}", TimeDelta::days(1) + TimeDelta::milliseconds(2345)),
            "P1DT2.345S"
        );
    }

    #[test]
    fn test_to_std() {
        assert_eq!(TimeDelta::seconds(1).to_std(), Ok(StdDuration::new(1, 0)));
        assert_eq!(TimeDelta::seconds(86_401).to_std(), Ok(StdDuration::new(86_401, 0)));
        assert_eq!(TimeDelta::milliseconds(123).to_std(), Ok(StdDuration::new(0, 123_000_000)));
        assert_eq!(
            TimeDelta::milliseconds(123_765).to_std(),
            Ok(StdDuration::new(123, 765_000_000))
        );
        assert_eq!(TimeDelta::nanoseconds(777).to_std(), Ok(StdDuration::new(0, 777)));
        assert_eq!(MAX.to_std(), Ok(StdDuration::new(9_223_372_036_854_775, 807_000_000)));
        assert_eq!(TimeDelta::seconds(-1).to_std(), Err(OutOfRangeError(())));
        assert_eq!(TimeDelta::milliseconds(-1).to_std(), Err(OutOfRangeError(())));
    }

    #[test]
    fn test_from_std() {
        assert_eq!(Ok(TimeDelta::seconds(1)), TimeDelta::from_std(StdDuration::new(1, 0)));
        assert_eq!(Ok(TimeDelta::seconds(86401)), TimeDelta::from_std(StdDuration::new(86_401, 0)));
        assert_eq!(
            Ok(TimeDelta::milliseconds(123)),
            TimeDelta::from_std(StdDuration::new(0, 123_000_000))
        );
        assert_eq!(
            Ok(TimeDelta::milliseconds(123_765)),
            TimeDelta::from_std(StdDuration::new(123, 765_000_000))
        );
        assert_eq!(Ok(TimeDelta::nanoseconds(777)), TimeDelta::from_std(StdDuration::new(0, 777)));
        assert_eq!(
            Ok(MAX),
            TimeDelta::from_std(StdDuration::new(9_223_372_036_854_775, 807_000_000))
        );
        assert_eq!(
            TimeDelta::from_std(StdDuration::new(9_223_372_036_854_776, 0)),
            Err(OutOfRangeError(()))
        );
        assert_eq!(
            TimeDelta::from_std(StdDuration::new(9_223_372_036_854_775, 807_000_001)),
            Err(OutOfRangeError(()))
        );
    }
}
