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

use core::ops::{Add, AddAssign, Div, Mul, Neg, Sub, SubAssign};
use core::time::Duration as StdDuration;
use core::{fmt, i64};
#[cfg(feature = "std")]
use std::error::Error;

use crate::{expect, try_opt};

#[cfg(any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"))]
use rkyv::{Archive, Deserialize, Serialize};

/// The number of nanoseconds in a microsecond.
const NANOS_PER_MICRO: i32 = 1000;
/// The number of nanoseconds in a millisecond.
const NANOS_PER_MILLI: i32 = 1_000_000;
/// The number of nanoseconds in seconds.
pub(crate) const NANOS_PER_SEC: i32 = 1_000_000_000;
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

/// ISO 8601 time duration with nanosecond precision.
///
/// This also allows for negative durations; see individual methods for details.
///
/// A `Duration` is represented internally as a complement of seconds and
/// nanoseconds. The range is restricted to that of `i64` milliseconds, with the
/// minimum value notably being set to `-i64::MAX` rather than allowing the full
/// range of `i64::MIN`. This is to allow easy flipping of sign, so that for
/// instance `abs()` can be called without any checks.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
#[cfg_attr(
    any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"),
    derive(Archive, Deserialize, Serialize),
    archive(compare(PartialEq, PartialOrd)),
    archive_attr(derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash))
)]
#[cfg_attr(feature = "rkyv-validation", archive(check_bytes))]
pub struct Duration {
    secs: i64,
    nanos: i32, // Always 0 <= nanos < NANOS_PER_SEC
}

/// The minimum possible `Duration`: `-i64::MAX` milliseconds.
pub(crate) const MIN: Duration = Duration {
    secs: -i64::MAX / MILLIS_PER_SEC - 1,
    nanos: NANOS_PER_SEC + (-i64::MAX % MILLIS_PER_SEC) as i32 * NANOS_PER_MILLI,
};

/// The maximum possible `Duration`: `i64::MAX` milliseconds.
pub(crate) const MAX: Duration = Duration {
    secs: i64::MAX / MILLIS_PER_SEC,
    nanos: (i64::MAX % MILLIS_PER_SEC) as i32 * NANOS_PER_MILLI,
};

impl Duration {
    /// Makes a new `Duration` with given number of seconds and nanoseconds.
    ///
    /// # Errors
    ///
    /// Returns `None` when the duration is out of bounds, or if `nanos` ≥ 1,000,000,000.
    pub(crate) const fn new(secs: i64, nanos: u32) -> Option<Duration> {
        if secs < MIN.secs
            || secs > MAX.secs
            || nanos > 1_000_000_000
            || (secs == MAX.secs && nanos > MAX.nanos as u32)
            || (secs == MIN.secs && nanos < MIN.nanos as u32)
        {
            return None;
        }
        Some(Duration { secs, nanos: nanos as i32 })
    }

    /// Makes a new `Duration` with the given number of weeks.
    ///
    /// Equivalent to `Duration::seconds(weeks * 7 * 24 * 60 * 60)` with
    /// overflow checks.
    ///
    /// # Panics
    ///
    /// Panics when the duration is out of bounds.
    #[inline]
    #[must_use]
    pub const fn weeks(weeks: i64) -> Duration {
        expect!(Duration::try_weeks(weeks), "Duration::weeks out of bounds")
    }

    /// Makes a new `Duration` with the given number of weeks.
    ///
    /// Equivalent to `Duration::seconds(weeks * 7 * 24 * 60 * 60)` with
    /// overflow checks.
    ///
    /// # Errors
    ///
    /// Returns `None` when the duration is out of bounds.
    #[inline]
    pub const fn try_weeks(weeks: i64) -> Option<Duration> {
        Duration::try_seconds(try_opt!(weeks.checked_mul(SECS_PER_WEEK)))
    }

    /// Makes a new `Duration` with the given number of days.
    ///
    /// Equivalent to `Duration::seconds(days * 24 * 60 * 60)` with overflow
    /// checks.
    ///
    /// # Panics
    ///
    /// Panics when the duration is out of bounds.
    #[inline]
    #[must_use]
    pub const fn days(days: i64) -> Duration {
        expect!(Duration::try_days(days), "Duration::days out of bounds")
    }

    /// Makes a new `Duration` with the given number of days.
    ///
    /// Equivalent to `Duration::seconds(days * 24 * 60 * 60)` with overflow
    /// checks.
    ///
    /// # Errors
    ///
    /// Returns `None` when the duration is out of bounds.
    #[inline]
    pub const fn try_days(days: i64) -> Option<Duration> {
        Duration::try_seconds(try_opt!(days.checked_mul(SECS_PER_DAY)))
    }

    /// Makes a new `Duration` with the given number of hours.
    ///
    /// Equivalent to `Duration::seconds(hours * 60 * 60)` with overflow checks.
    ///
    /// # Panics
    ///
    /// Panics when the duration is out of bounds.
    #[inline]
    #[must_use]
    pub const fn hours(hours: i64) -> Duration {
        expect!(Duration::try_hours(hours), "Duration::hours out of bounds")
    }

    /// Makes a new `Duration` with the given number of hours.
    ///
    /// Equivalent to `Duration::seconds(hours * 60 * 60)` with overflow checks.
    ///
    /// # Errors
    ///
    /// Returns `None` when the duration is out of bounds.
    #[inline]
    pub const fn try_hours(hours: i64) -> Option<Duration> {
        Duration::try_seconds(try_opt!(hours.checked_mul(SECS_PER_HOUR)))
    }

    /// Makes a new `Duration` with the given number of minutes.
    ///
    /// Equivalent to `Duration::seconds(minutes * 60)` with overflow checks.
    ///
    /// # Panics
    ///
    /// Panics when the duration is out of bounds.
    #[inline]
    #[must_use]
    pub const fn minutes(minutes: i64) -> Duration {
        expect!(Duration::try_minutes(minutes), "Duration::minutes out of bounds")
    }

    /// Makes a new `Duration` with the given number of minutes.
    ///
    /// Equivalent to `Duration::seconds(minutes * 60)` with overflow checks.
    ///
    /// # Errors
    ///
    /// Returns `None` when the duration is out of bounds.
    #[inline]
    pub const fn try_minutes(minutes: i64) -> Option<Duration> {
        Duration::try_seconds(try_opt!(minutes.checked_mul(SECS_PER_MINUTE)))
    }

    /// Makes a new `Duration` with the given number of seconds.
    ///
    /// # Panics
    ///
    /// Panics when the duration is out of bounds, i.e. when the value is more
    /// than `i64::MAX / 1_000` seconds or less than `-i64::MAX / 1_000` seconds
    /// (in this context, this is the same as `i64::MIN / 1_000` due to
    /// rounding).
    #[inline]
    #[must_use]
    pub const fn seconds(seconds: i64) -> Duration {
        expect!(Duration::try_seconds(seconds), "Duration::seconds out of bounds")
    }

    /// Makes a new `Duration` with the given number of seconds.
    ///
    /// # Errors
    ///
    /// Returns `None` when the duration is more than `i64::MAX / 1_000` seconds
    /// or less than `-i64::MAX / 1_000` seconds (in this context, this is the
    /// same as `i64::MIN / 1_000` due to rounding).
    #[inline]
    pub const fn try_seconds(seconds: i64) -> Option<Duration> {
        Duration::new(seconds, 0)
    }

    /// Makes a new `Duration` with the given number of milliseconds.
    ///
    /// # Panics
    ///
    /// Panics when the duration is out of bounds, i.e. when the duration is
    /// more than `i64::MAX` milliseconds or less than `-i64::MAX` milliseconds.
    /// Notably, this is not the same as `i64::MIN`.
    #[inline]
    pub const fn milliseconds(milliseconds: i64) -> Duration {
        expect!(Duration::try_milliseconds(milliseconds), "Duration::milliseconds out of bounds")
    }

    /// Makes a new `Duration` with the given number of milliseconds.
    ///
    /// # Errors
    ///
    /// Returns `None` when the duration is more than `i64::MAX` milliseconds or
    /// less than `-i64::MAX` milliseconds. Notably, this is not the same as
    /// `i64::MIN`.
    #[inline]
    pub const fn try_milliseconds(milliseconds: i64) -> Option<Duration> {
        // We don't need to compare against MAX, as this function accepts an
        // i64, and MAX is aligned to i64::MAX milliseconds.
        if milliseconds < -i64::MAX {
            return None;
        }
        let (secs, millis) = div_mod_floor_64(milliseconds, MILLIS_PER_SEC);
        let d = Duration { secs, nanos: millis as i32 * NANOS_PER_MILLI };
        Some(d)
    }

    /// Makes a new `Duration` with the given number of microseconds.
    ///
    /// The number of microseconds acceptable by this constructor is less than
    /// the total number that can actually be stored in a `Duration`, so it is
    /// not possible to specify a value that would be out of bounds. This
    /// function is therefore infallible.
    #[inline]
    pub const fn microseconds(microseconds: i64) -> Duration {
        let (secs, micros) = div_mod_floor_64(microseconds, MICROS_PER_SEC);
        let nanos = micros as i32 * NANOS_PER_MICRO;
        Duration { secs, nanos }
    }

    /// Makes a new `Duration` with the given number of nanoseconds.
    ///
    /// The number of nanoseconds acceptable by this constructor is less than
    /// the total number that can actually be stored in a `Duration`, so it is
    /// not possible to specify a value that would be out of bounds. This
    /// function is therefore infallible.
    #[inline]
    pub const fn nanoseconds(nanos: i64) -> Duration {
        let (secs, nanos) = div_mod_floor_64(nanos, NANOS_PER_SEC as i64);
        Duration { secs, nanos: nanos as i32 }
    }

    /// Returns the total number of whole weeks in the `Duration`.
    #[inline]
    pub const fn num_weeks(&self) -> i64 {
        self.num_days() / 7
    }

    /// Returns the total number of whole days in the `Duration`.
    pub const fn num_days(&self) -> i64 {
        self.num_seconds() / SECS_PER_DAY
    }

    /// Returns the total number of whole hours in the `Duration`.
    #[inline]
    pub const fn num_hours(&self) -> i64 {
        self.num_seconds() / SECS_PER_HOUR
    }

    /// Returns the total number of whole minutes in the `Duration`.
    #[inline]
    pub const fn num_minutes(&self) -> i64 {
        self.num_seconds() / SECS_PER_MINUTE
    }

    /// Returns the total number of whole seconds in the `Duration`.
    pub const fn num_seconds(&self) -> i64 {
        // If secs is negative, nanos should be subtracted from the duration.
        if self.secs < 0 && self.nanos > 0 {
            self.secs + 1
        } else {
            self.secs
        }
    }

    /// Returns the number of nanoseconds such that
    /// `subsec_nanos() + num_seconds() * NANOS_PER_SEC` is the total number of
    /// nanoseconds in the `Duration`.
    pub const fn subsec_nanos(&self) -> i32 {
        if self.secs < 0 && self.nanos > 0 {
            self.nanos - NANOS_PER_SEC
        } else {
            self.nanos
        }
    }

    /// Returns the total number of whole milliseconds in the `Duration`.
    pub const fn num_milliseconds(&self) -> i64 {
        // A proper Duration will not overflow, because MIN and MAX are defined such
        // that the range is within the bounds of an i64, from -i64::MAX through to
        // +i64::MAX inclusive. Notably, i64::MIN is excluded from this range.
        let secs_part = self.num_seconds() * MILLIS_PER_SEC;
        let nanos_part = self.subsec_nanos() / NANOS_PER_MILLI;
        secs_part + nanos_part as i64
    }

    /// Returns the total number of whole microseconds in the `Duration`,
    /// or `None` on overflow (exceeding 2^63 microseconds in either direction).
    pub const fn num_microseconds(&self) -> Option<i64> {
        let secs_part = try_opt!(self.num_seconds().checked_mul(MICROS_PER_SEC));
        let nanos_part = self.subsec_nanos() / NANOS_PER_MICRO;
        secs_part.checked_add(nanos_part as i64)
    }

    /// Returns the total number of whole nanoseconds in the `Duration`,
    /// or `None` on overflow (exceeding 2^63 nanoseconds in either direction).
    pub const fn num_nanoseconds(&self) -> Option<i64> {
        let secs_part = try_opt!(self.num_seconds().checked_mul(NANOS_PER_SEC as i64));
        let nanos_part = self.subsec_nanos();
        secs_part.checked_add(nanos_part as i64)
    }

    /// Add two `Duration`s, returning `None` if overflow occurred.
    #[must_use]
    pub const fn checked_add(&self, rhs: &Duration) -> Option<Duration> {
        // No overflow checks here because we stay comfortably within the range of an `i64`.
        // Range checks happen in `Duration::new`.
        let mut secs = self.secs + rhs.secs;
        let mut nanos = self.nanos + rhs.nanos;
        if nanos >= NANOS_PER_SEC {
            nanos -= NANOS_PER_SEC;
            secs += 1;
        }
        Duration::new(secs, nanos as u32)
    }

    /// Subtract two `Duration`s, returning `None` if overflow occurred.
    #[must_use]
    pub const fn checked_sub(&self, rhs: &Duration) -> Option<Duration> {
        // No overflow checks here because we stay comfortably within the range of an `i64`.
        // Range checks happen in `Duration::new`.
        let mut secs = self.secs - rhs.secs;
        let mut nanos = self.nanos - rhs.nanos;
        if nanos < 0 {
            nanos += NANOS_PER_SEC;
            secs -= 1;
        }
        Duration::new(secs, nanos as u32)
    }

    /// Returns the `Duration` as an absolute (non-negative) value.
    #[inline]
    pub const fn abs(&self) -> Duration {
        if self.secs < 0 && self.nanos != 0 {
            Duration { secs: (self.secs + 1).abs(), nanos: NANOS_PER_SEC - self.nanos }
        } else {
            Duration { secs: self.secs.abs(), nanos: self.nanos }
        }
    }

    /// The minimum possible `Duration`: `-i64::MAX` milliseconds.
    #[inline]
    pub const fn min_value() -> Duration {
        MIN
    }

    /// The maximum possible `Duration`: `i64::MAX` milliseconds.
    #[inline]
    pub const fn max_value() -> Duration {
        MAX
    }

    /// A `Duration` where the stored seconds and nanoseconds are equal to zero.
    #[inline]
    pub const fn zero() -> Duration {
        Duration { secs: 0, nanos: 0 }
    }

    /// Returns `true` if the `Duration` equals `Duration::zero()`.
    #[inline]
    pub const fn is_zero(&self) -> bool {
        self.secs == 0 && self.nanos == 0
    }

    /// Creates a `time::Duration` object from `std::time::Duration`
    ///
    /// This function errors when original duration is larger than the maximum
    /// value supported for this type.
    pub const fn from_std(duration: StdDuration) -> Result<Duration, OutOfRangeError> {
        // We need to check secs as u64 before coercing to i64
        if duration.as_secs() > MAX.secs as u64 {
            return Err(OutOfRangeError(()));
        }
        match Duration::new(duration.as_secs() as i64, duration.subsec_nanos()) {
            Some(d) => Ok(d),
            None => Err(OutOfRangeError(())),
        }
    }

    /// Creates a `std::time::Duration` object from `time::Duration`
    ///
    /// This function errors when duration is less than zero. As standard
    /// library implementation is limited to non-negative values.
    pub const fn to_std(&self) -> Result<StdDuration, OutOfRangeError> {
        if self.secs < 0 {
            return Err(OutOfRangeError(()));
        }
        Ok(StdDuration::new(self.secs as u64, self.nanos as u32))
    }
}

impl Neg for Duration {
    type Output = Duration;

    #[inline]
    fn neg(self) -> Duration {
        if self.nanos == 0 {
            Duration { secs: -self.secs, nanos: 0 }
        } else {
            Duration { secs: -self.secs - 1, nanos: NANOS_PER_SEC - self.nanos }
        }
    }
}

impl Add for Duration {
    type Output = Duration;

    fn add(self, rhs: Duration) -> Duration {
        self.checked_add(&rhs).expect("`Duration + Duration` overflowed")
    }
}

impl Sub for Duration {
    type Output = Duration;

    fn sub(self, rhs: Duration) -> Duration {
        self.checked_sub(&rhs).expect("`Duration - Duration` overflowed")
    }
}

impl AddAssign for Duration {
    fn add_assign(&mut self, rhs: Duration) {
        let new = self.checked_add(&rhs).expect("`Duration + Duration` overflowed");
        *self = new;
    }
}

impl SubAssign for Duration {
    fn sub_assign(&mut self, rhs: Duration) {
        let new = self.checked_sub(&rhs).expect("`Duration - Duration` overflowed");
        *self = new;
    }
}

impl Mul<i32> for Duration {
    type Output = Duration;

    fn mul(self, rhs: i32) -> Duration {
        // Multiply nanoseconds as i64, because it cannot overflow that way.
        let total_nanos = self.nanos as i64 * rhs as i64;
        let (extra_secs, nanos) = div_mod_floor_64(total_nanos, NANOS_PER_SEC as i64);
        let secs = self.secs * rhs as i64 + extra_secs;
        Duration { secs, nanos: nanos as i32 }
    }
}

impl Div<i32> for Duration {
    type Output = Duration;

    fn div(self, rhs: i32) -> Duration {
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
        Duration { secs, nanos }
    }
}

impl<'a> core::iter::Sum<&'a Duration> for Duration {
    fn sum<I: Iterator<Item = &'a Duration>>(iter: I) -> Duration {
        iter.fold(Duration::zero(), |acc, x| acc + *x)
    }
}

impl core::iter::Sum<Duration> for Duration {
    fn sum<I: Iterator<Item = Duration>>(iter: I) -> Duration {
        iter.fold(Duration::zero(), |acc, x| acc + x)
    }
}

impl fmt::Display for Duration {
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

/// Represents error when converting `Duration` to/from a standard library
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

#[cfg(all(feature = "arbitrary", feature = "std"))]
impl arbitrary::Arbitrary<'_> for Duration {
    fn arbitrary(u: &mut arbitrary::Unstructured) -> arbitrary::Result<Duration> {
        const MIN_SECS: i64 = -i64::MAX / MILLIS_PER_SEC - 1;
        const MAX_SECS: i64 = i64::MAX / MILLIS_PER_SEC;

        let secs: i64 = u.int_in_range(MIN_SECS..=MAX_SECS)?;
        let nanos: i32 = u.int_in_range(0..=(NANOS_PER_SEC - 1))?;
        let duration = Duration { secs, nanos };

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
    use super::{Duration, MAX, MIN};
    use core::time::Duration as StdDuration;

    #[test]
    fn test_duration() {
        assert!(Duration::seconds(1) != Duration::zero());
        assert_eq!(Duration::seconds(1) + Duration::seconds(2), Duration::seconds(3));
        assert_eq!(
            Duration::seconds(86_399) + Duration::seconds(4),
            Duration::days(1) + Duration::seconds(3)
        );
        assert_eq!(Duration::days(10) - Duration::seconds(1000), Duration::seconds(863_000));
        assert_eq!(Duration::days(10) - Duration::seconds(1_000_000), Duration::seconds(-136_000));
        assert_eq!(
            Duration::days(2) + Duration::seconds(86_399) + Duration::nanoseconds(1_234_567_890),
            Duration::days(3) + Duration::nanoseconds(234_567_890)
        );
        assert_eq!(-Duration::days(3), Duration::days(-3));
        assert_eq!(
            -(Duration::days(3) + Duration::seconds(70)),
            Duration::days(-4) + Duration::seconds(86_400 - 70)
        );

        let mut d = Duration::default();
        d += Duration::minutes(1);
        d -= Duration::seconds(30);
        assert_eq!(d, Duration::seconds(30));
    }

    #[test]
    fn test_duration_num_days() {
        assert_eq!(Duration::zero().num_days(), 0);
        assert_eq!(Duration::days(1).num_days(), 1);
        assert_eq!(Duration::days(-1).num_days(), -1);
        assert_eq!(Duration::seconds(86_399).num_days(), 0);
        assert_eq!(Duration::seconds(86_401).num_days(), 1);
        assert_eq!(Duration::seconds(-86_399).num_days(), 0);
        assert_eq!(Duration::seconds(-86_401).num_days(), -1);
        assert_eq!(Duration::days(i32::MAX as i64).num_days(), i32::MAX as i64);
        assert_eq!(Duration::days(i32::MIN as i64).num_days(), i32::MIN as i64);
    }

    #[test]
    fn test_duration_num_seconds() {
        assert_eq!(Duration::zero().num_seconds(), 0);
        assert_eq!(Duration::seconds(1).num_seconds(), 1);
        assert_eq!(Duration::seconds(-1).num_seconds(), -1);
        assert_eq!(Duration::milliseconds(999).num_seconds(), 0);
        assert_eq!(Duration::milliseconds(1001).num_seconds(), 1);
        assert_eq!(Duration::milliseconds(-999).num_seconds(), 0);
        assert_eq!(Duration::milliseconds(-1001).num_seconds(), -1);
    }
    #[test]
    fn test_duration_seconds_max_allowed() {
        let duration = Duration::seconds(i64::MAX / 1_000);
        assert_eq!(duration.num_seconds(), i64::MAX / 1_000);
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MAX as i128 / 1_000 * 1_000_000_000
        );
    }
    #[test]
    fn test_duration_seconds_max_overflow() {
        assert!(Duration::try_seconds(i64::MAX / 1_000 + 1).is_none());
    }
    #[test]
    #[should_panic(expected = "Duration::seconds out of bounds")]
    fn test_duration_seconds_max_overflow_panic() {
        let _ = Duration::seconds(i64::MAX / 1_000 + 1);
    }
    #[test]
    fn test_duration_seconds_min_allowed() {
        let duration = Duration::seconds(i64::MIN / 1_000); // Same as -i64::MAX / 1_000 due to rounding
        assert_eq!(duration.num_seconds(), i64::MIN / 1_000); // Same as -i64::MAX / 1_000 due to rounding
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            -i64::MAX as i128 / 1_000 * 1_000_000_000
        );
    }
    #[test]
    fn test_duration_seconds_min_underflow() {
        assert!(Duration::try_seconds(-i64::MAX / 1_000 - 1).is_none());
    }
    #[test]
    #[should_panic(expected = "Duration::seconds out of bounds")]
    fn test_duration_seconds_min_underflow_panic() {
        let _ = Duration::seconds(-i64::MAX / 1_000 - 1);
    }

    #[test]
    fn test_duration_num_milliseconds() {
        assert_eq!(Duration::zero().num_milliseconds(), 0);
        assert_eq!(Duration::milliseconds(1).num_milliseconds(), 1);
        assert_eq!(Duration::milliseconds(-1).num_milliseconds(), -1);
        assert_eq!(Duration::microseconds(999).num_milliseconds(), 0);
        assert_eq!(Duration::microseconds(1001).num_milliseconds(), 1);
        assert_eq!(Duration::microseconds(-999).num_milliseconds(), 0);
        assert_eq!(Duration::microseconds(-1001).num_milliseconds(), -1);
    }
    #[test]
    fn test_duration_milliseconds_max_allowed() {
        // The maximum number of milliseconds acceptable through the constructor is
        // equal to the number that can be stored in a Duration.
        let duration = Duration::milliseconds(i64::MAX);
        assert_eq!(duration.num_milliseconds(), i64::MAX);
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MAX as i128 * 1_000_000
        );
    }
    #[test]
    fn test_duration_milliseconds_max_overflow() {
        // Here we ensure that trying to add one millisecond to the maximum storable
        // value will fail.
        assert!(Duration::milliseconds(i64::MAX).checked_add(&Duration::milliseconds(1)).is_none());
    }
    #[test]
    fn test_duration_milliseconds_min_allowed() {
        // The minimum number of milliseconds acceptable through the constructor is
        // not equal to the number that can be stored in a Duration - there is a
        // difference of one (i64::MIN vs -i64::MAX).
        let duration = Duration::milliseconds(-i64::MAX);
        assert_eq!(duration.num_milliseconds(), -i64::MAX);
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            -i64::MAX as i128 * 1_000_000
        );
    }
    #[test]
    fn test_duration_milliseconds_min_underflow() {
        // Here we ensure that trying to subtract one millisecond from the minimum
        // storable value will fail.
        assert!(Duration::milliseconds(-i64::MAX)
            .checked_sub(&Duration::milliseconds(1))
            .is_none());
    }
    #[test]
    #[should_panic(expected = "Duration::milliseconds out of bounds")]
    fn test_duration_milliseconds_min_underflow_panic() {
        // Here we ensure that trying to create a value one millisecond below the
        // minimum storable value will fail. This test is necessary because the
        // storable range is -i64::MAX, but the constructor type of i64 will allow
        // i64::MIN, which is one value below.
        let _ = Duration::milliseconds(i64::MIN); // Same as -i64::MAX - 1
    }

    #[test]
    fn test_duration_num_microseconds() {
        assert_eq!(Duration::zero().num_microseconds(), Some(0));
        assert_eq!(Duration::microseconds(1).num_microseconds(), Some(1));
        assert_eq!(Duration::microseconds(-1).num_microseconds(), Some(-1));
        assert_eq!(Duration::nanoseconds(999).num_microseconds(), Some(0));
        assert_eq!(Duration::nanoseconds(1001).num_microseconds(), Some(1));
        assert_eq!(Duration::nanoseconds(-999).num_microseconds(), Some(0));
        assert_eq!(Duration::nanoseconds(-1001).num_microseconds(), Some(-1));

        // overflow checks
        const MICROS_PER_DAY: i64 = 86_400_000_000;
        assert_eq!(
            Duration::days(i64::MAX / MICROS_PER_DAY).num_microseconds(),
            Some(i64::MAX / MICROS_PER_DAY * MICROS_PER_DAY)
        );
        assert_eq!(
            Duration::days(-i64::MAX / MICROS_PER_DAY).num_microseconds(),
            Some(-i64::MAX / MICROS_PER_DAY * MICROS_PER_DAY)
        );
        assert_eq!(Duration::days(i64::MAX / MICROS_PER_DAY + 1).num_microseconds(), None);
        assert_eq!(Duration::days(-i64::MAX / MICROS_PER_DAY - 1).num_microseconds(), None);
    }
    #[test]
    fn test_duration_microseconds_max_allowed() {
        // The number of microseconds acceptable through the constructor is far
        // fewer than the number that can actually be stored in a Duration, so this
        // is not a particular insightful test.
        let duration = Duration::microseconds(i64::MAX);
        assert_eq!(duration.num_microseconds(), Some(i64::MAX));
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MAX as i128 * 1_000
        );
        // Here we create a Duration with the maximum possible number of
        // microseconds by creating a Duration with the maximum number of
        // milliseconds and then checking that the number of microseconds matches
        // the storage limit.
        let duration = Duration::milliseconds(i64::MAX);
        assert!(duration.num_microseconds().is_none());
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MAX as i128 * 1_000_000
        );
    }
    #[test]
    fn test_duration_microseconds_max_overflow() {
        // This test establishes that a Duration can store more microseconds than
        // are representable through the return of duration.num_microseconds().
        let duration = Duration::microseconds(i64::MAX) + Duration::microseconds(1);
        assert!(duration.num_microseconds().is_none());
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            (i64::MAX as i128 + 1) * 1_000
        );
        // Here we ensure that trying to add one microsecond to the maximum storable
        // value will fail.
        assert!(Duration::milliseconds(i64::MAX).checked_add(&Duration::microseconds(1)).is_none());
    }
    #[test]
    fn test_duration_microseconds_min_allowed() {
        // The number of microseconds acceptable through the constructor is far
        // fewer than the number that can actually be stored in a Duration, so this
        // is not a particular insightful test.
        let duration = Duration::microseconds(i64::MIN);
        assert_eq!(duration.num_microseconds(), Some(i64::MIN));
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MIN as i128 * 1_000
        );
        // Here we create a Duration with the minimum possible number of
        // microseconds by creating a Duration with the minimum number of
        // milliseconds and then checking that the number of microseconds matches
        // the storage limit.
        let duration = Duration::milliseconds(-i64::MAX);
        assert!(duration.num_microseconds().is_none());
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            -i64::MAX as i128 * 1_000_000
        );
    }
    #[test]
    fn test_duration_microseconds_min_underflow() {
        // This test establishes that a Duration can store more microseconds than
        // are representable through the return of duration.num_microseconds().
        let duration = Duration::microseconds(i64::MIN) - Duration::microseconds(1);
        assert!(duration.num_microseconds().is_none());
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            (i64::MIN as i128 - 1) * 1_000
        );
        // Here we ensure that trying to subtract one microsecond from the minimum
        // storable value will fail.
        assert!(Duration::milliseconds(-i64::MAX)
            .checked_sub(&Duration::microseconds(1))
            .is_none());
    }

    #[test]
    fn test_duration_num_nanoseconds() {
        assert_eq!(Duration::zero().num_nanoseconds(), Some(0));
        assert_eq!(Duration::nanoseconds(1).num_nanoseconds(), Some(1));
        assert_eq!(Duration::nanoseconds(-1).num_nanoseconds(), Some(-1));

        // overflow checks
        const NANOS_PER_DAY: i64 = 86_400_000_000_000;
        assert_eq!(
            Duration::days(i64::MAX / NANOS_PER_DAY).num_nanoseconds(),
            Some(i64::MAX / NANOS_PER_DAY * NANOS_PER_DAY)
        );
        assert_eq!(
            Duration::days(-i64::MAX / NANOS_PER_DAY).num_nanoseconds(),
            Some(-i64::MAX / NANOS_PER_DAY * NANOS_PER_DAY)
        );
        assert_eq!(Duration::days(i64::MAX / NANOS_PER_DAY + 1).num_nanoseconds(), None);
        assert_eq!(Duration::days(-i64::MAX / NANOS_PER_DAY - 1).num_nanoseconds(), None);
    }
    #[test]
    fn test_duration_nanoseconds_max_allowed() {
        // The number of nanoseconds acceptable through the constructor is far fewer
        // than the number that can actually be stored in a Duration, so this is not
        // a particular insightful test.
        let duration = Duration::nanoseconds(i64::MAX);
        assert_eq!(duration.num_nanoseconds(), Some(i64::MAX));
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MAX as i128
        );
        // Here we create a Duration with the maximum possible number of nanoseconds
        // by creating a Duration with the maximum number of milliseconds and then
        // checking that the number of nanoseconds matches the storage limit.
        let duration = Duration::milliseconds(i64::MAX);
        assert!(duration.num_nanoseconds().is_none());
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MAX as i128 * 1_000_000
        );
    }
    #[test]
    fn test_duration_nanoseconds_max_overflow() {
        // This test establishes that a Duration can store more nanoseconds than are
        // representable through the return of duration.num_nanoseconds().
        let duration = Duration::nanoseconds(i64::MAX) + Duration::nanoseconds(1);
        assert!(duration.num_nanoseconds().is_none());
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MAX as i128 + 1
        );
        // Here we ensure that trying to add one nanosecond to the maximum storable
        // value will fail.
        assert!(Duration::milliseconds(i64::MAX).checked_add(&Duration::nanoseconds(1)).is_none());
    }
    #[test]
    fn test_duration_nanoseconds_min_allowed() {
        // The number of nanoseconds acceptable through the constructor is far fewer
        // than the number that can actually be stored in a Duration, so this is not
        // a particular insightful test.
        let duration = Duration::nanoseconds(i64::MIN);
        assert_eq!(duration.num_nanoseconds(), Some(i64::MIN));
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MIN as i128
        );
        // Here we create a Duration with the minimum possible number of nanoseconds
        // by creating a Duration with the minimum number of milliseconds and then
        // checking that the number of nanoseconds matches the storage limit.
        let duration = Duration::milliseconds(-i64::MAX);
        assert!(duration.num_nanoseconds().is_none());
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            -i64::MAX as i128 * 1_000_000
        );
    }
    #[test]
    fn test_duration_nanoseconds_min_underflow() {
        // This test establishes that a Duration can store more nanoseconds than are
        // representable through the return of duration.num_nanoseconds().
        let duration = Duration::nanoseconds(i64::MIN) - Duration::nanoseconds(1);
        assert!(duration.num_nanoseconds().is_none());
        assert_eq!(
            duration.secs as i128 * 1_000_000_000 + duration.nanos as i128,
            i64::MIN as i128 - 1
        );
        // Here we ensure that trying to subtract one nanosecond from the minimum
        // storable value will fail.
        assert!(Duration::milliseconds(-i64::MAX).checked_sub(&Duration::nanoseconds(1)).is_none());
    }

    #[test]
    fn test_max() {
        assert_eq!(
            MAX.secs as i128 * 1_000_000_000 + MAX.nanos as i128,
            i64::MAX as i128 * 1_000_000
        );
        assert_eq!(MAX, Duration::milliseconds(i64::MAX));
        assert_eq!(MAX.num_milliseconds(), i64::MAX);
        assert_eq!(MAX.num_microseconds(), None);
        assert_eq!(MAX.num_nanoseconds(), None);
    }
    #[test]
    fn test_min() {
        assert_eq!(
            MIN.secs as i128 * 1_000_000_000 + MIN.nanos as i128,
            -i64::MAX as i128 * 1_000_000
        );
        assert_eq!(MIN, Duration::milliseconds(-i64::MAX));
        assert_eq!(MIN.num_milliseconds(), -i64::MAX);
        assert_eq!(MIN.num_microseconds(), None);
        assert_eq!(MIN.num_nanoseconds(), None);
    }

    #[test]
    fn test_duration_ord() {
        assert!(Duration::milliseconds(1) < Duration::milliseconds(2));
        assert!(Duration::milliseconds(2) > Duration::milliseconds(1));
        assert!(Duration::milliseconds(-1) > Duration::milliseconds(-2));
        assert!(Duration::milliseconds(-2) < Duration::milliseconds(-1));
        assert!(Duration::milliseconds(-1) < Duration::milliseconds(1));
        assert!(Duration::milliseconds(1) > Duration::milliseconds(-1));
        assert!(Duration::milliseconds(0) < Duration::milliseconds(1));
        assert!(Duration::milliseconds(0) > Duration::milliseconds(-1));
        assert!(Duration::milliseconds(1_001) < Duration::milliseconds(1_002));
        assert!(Duration::milliseconds(-1_001) > Duration::milliseconds(-1_002));
        assert!(Duration::nanoseconds(1_234_567_890) < Duration::nanoseconds(1_234_567_891));
        assert!(Duration::nanoseconds(-1_234_567_890) > Duration::nanoseconds(-1_234_567_891));
        assert!(Duration::milliseconds(i64::MAX) > Duration::milliseconds(i64::MAX - 1));
        assert!(Duration::milliseconds(-i64::MAX) < Duration::milliseconds(-i64::MAX + 1));
    }

    #[test]
    fn test_duration_checked_ops() {
        assert_eq!(
            Duration::milliseconds(i64::MAX).checked_add(&Duration::milliseconds(0)),
            Some(Duration::milliseconds(i64::MAX))
        );
        assert_eq!(
            Duration::milliseconds(i64::MAX - 1).checked_add(&Duration::microseconds(999)),
            Some(Duration::milliseconds(i64::MAX - 2) + Duration::microseconds(1999))
        );
        assert!(Duration::milliseconds(i64::MAX)
            .checked_add(&Duration::microseconds(1000))
            .is_none());
        assert!(Duration::milliseconds(i64::MAX).checked_add(&Duration::nanoseconds(1)).is_none());

        assert_eq!(
            Duration::milliseconds(-i64::MAX).checked_sub(&Duration::milliseconds(0)),
            Some(Duration::milliseconds(-i64::MAX))
        );
        assert_eq!(
            Duration::milliseconds(-i64::MAX + 1).checked_sub(&Duration::microseconds(999)),
            Some(Duration::milliseconds(-i64::MAX + 2) - Duration::microseconds(1999))
        );
        assert!(Duration::milliseconds(-i64::MAX)
            .checked_sub(&Duration::milliseconds(1))
            .is_none());
        assert!(Duration::milliseconds(-i64::MAX).checked_sub(&Duration::nanoseconds(1)).is_none());
    }

    #[test]
    fn test_duration_abs() {
        assert_eq!(Duration::milliseconds(1300).abs(), Duration::milliseconds(1300));
        assert_eq!(Duration::milliseconds(1000).abs(), Duration::milliseconds(1000));
        assert_eq!(Duration::milliseconds(300).abs(), Duration::milliseconds(300));
        assert_eq!(Duration::milliseconds(0).abs(), Duration::milliseconds(0));
        assert_eq!(Duration::milliseconds(-300).abs(), Duration::milliseconds(300));
        assert_eq!(Duration::milliseconds(-700).abs(), Duration::milliseconds(700));
        assert_eq!(Duration::milliseconds(-1000).abs(), Duration::milliseconds(1000));
        assert_eq!(Duration::milliseconds(-1300).abs(), Duration::milliseconds(1300));
        assert_eq!(Duration::milliseconds(-1700).abs(), Duration::milliseconds(1700));
        assert_eq!(Duration::milliseconds(-i64::MAX).abs(), Duration::milliseconds(i64::MAX));
    }

    #[test]
    #[allow(clippy::erasing_op)]
    fn test_duration_mul() {
        assert_eq!(Duration::zero() * i32::MAX, Duration::zero());
        assert_eq!(Duration::zero() * i32::MIN, Duration::zero());
        assert_eq!(Duration::nanoseconds(1) * 0, Duration::zero());
        assert_eq!(Duration::nanoseconds(1) * 1, Duration::nanoseconds(1));
        assert_eq!(Duration::nanoseconds(1) * 1_000_000_000, Duration::seconds(1));
        assert_eq!(Duration::nanoseconds(1) * -1_000_000_000, -Duration::seconds(1));
        assert_eq!(-Duration::nanoseconds(1) * 1_000_000_000, -Duration::seconds(1));
        assert_eq!(
            Duration::nanoseconds(30) * 333_333_333,
            Duration::seconds(10) - Duration::nanoseconds(10)
        );
        assert_eq!(
            (Duration::nanoseconds(1) + Duration::seconds(1) + Duration::days(1)) * 3,
            Duration::nanoseconds(3) + Duration::seconds(3) + Duration::days(3)
        );
        assert_eq!(Duration::milliseconds(1500) * -2, Duration::seconds(-3));
        assert_eq!(Duration::milliseconds(-1500) * 2, Duration::seconds(-3));
    }

    #[test]
    fn test_duration_div() {
        assert_eq!(Duration::zero() / i32::MAX, Duration::zero());
        assert_eq!(Duration::zero() / i32::MIN, Duration::zero());
        assert_eq!(Duration::nanoseconds(123_456_789) / 1, Duration::nanoseconds(123_456_789));
        assert_eq!(Duration::nanoseconds(123_456_789) / -1, -Duration::nanoseconds(123_456_789));
        assert_eq!(-Duration::nanoseconds(123_456_789) / -1, Duration::nanoseconds(123_456_789));
        assert_eq!(-Duration::nanoseconds(123_456_789) / 1, -Duration::nanoseconds(123_456_789));
        assert_eq!(Duration::seconds(1) / 3, Duration::nanoseconds(333_333_333));
        assert_eq!(Duration::seconds(4) / 3, Duration::nanoseconds(1_333_333_333));
        assert_eq!(Duration::seconds(-1) / 2, Duration::milliseconds(-500));
        assert_eq!(Duration::seconds(1) / -2, Duration::milliseconds(-500));
        assert_eq!(Duration::seconds(-1) / -2, Duration::milliseconds(500));
        assert_eq!(Duration::seconds(-4) / 3, Duration::nanoseconds(-1_333_333_333));
        assert_eq!(Duration::seconds(-4) / -3, Duration::nanoseconds(1_333_333_333));
    }

    #[test]
    fn test_duration_sum() {
        let duration_list_1 = [Duration::zero(), Duration::seconds(1)];
        let sum_1: Duration = duration_list_1.iter().sum();
        assert_eq!(sum_1, Duration::seconds(1));

        let duration_list_2 =
            [Duration::zero(), Duration::seconds(1), Duration::seconds(6), Duration::seconds(10)];
        let sum_2: Duration = duration_list_2.iter().sum();
        assert_eq!(sum_2, Duration::seconds(17));

        let duration_arr =
            [Duration::zero(), Duration::seconds(1), Duration::seconds(6), Duration::seconds(10)];
        let sum_3: Duration = duration_arr.into_iter().sum();
        assert_eq!(sum_3, Duration::seconds(17));
    }

    #[test]
    fn test_duration_fmt() {
        assert_eq!(Duration::zero().to_string(), "PT0S");
        assert_eq!(Duration::days(42).to_string(), "P42D");
        assert_eq!(Duration::days(-42).to_string(), "-P42D");
        assert_eq!(Duration::seconds(42).to_string(), "PT42S");
        assert_eq!(Duration::milliseconds(42).to_string(), "PT0.042S");
        assert_eq!(Duration::microseconds(42).to_string(), "PT0.000042S");
        assert_eq!(Duration::nanoseconds(42).to_string(), "PT0.000000042S");
        assert_eq!((Duration::days(7) + Duration::milliseconds(6543)).to_string(), "P7DT6.543S");
        assert_eq!(Duration::seconds(-86_401).to_string(), "-P1DT1S");
        assert_eq!(Duration::nanoseconds(-1).to_string(), "-PT0.000000001S");

        // the format specifier should have no effect on `Duration`
        assert_eq!(
            format!("{:30}", Duration::days(1) + Duration::milliseconds(2345)),
            "P1DT2.345S"
        );
    }

    #[test]
    fn test_to_std() {
        assert_eq!(Duration::seconds(1).to_std(), Ok(StdDuration::new(1, 0)));
        assert_eq!(Duration::seconds(86_401).to_std(), Ok(StdDuration::new(86_401, 0)));
        assert_eq!(Duration::milliseconds(123).to_std(), Ok(StdDuration::new(0, 123_000_000)));
        assert_eq!(
            Duration::milliseconds(123_765).to_std(),
            Ok(StdDuration::new(123, 765_000_000))
        );
        assert_eq!(Duration::nanoseconds(777).to_std(), Ok(StdDuration::new(0, 777)));
        assert_eq!(MAX.to_std(), Ok(StdDuration::new(9_223_372_036_854_775, 807_000_000)));
        assert_eq!(Duration::seconds(-1).to_std(), Err(OutOfRangeError(())));
        assert_eq!(Duration::milliseconds(-1).to_std(), Err(OutOfRangeError(())));
    }

    #[test]
    fn test_from_std() {
        assert_eq!(Ok(Duration::seconds(1)), Duration::from_std(StdDuration::new(1, 0)));
        assert_eq!(Ok(Duration::seconds(86_401)), Duration::from_std(StdDuration::new(86_401, 0)));
        assert_eq!(
            Ok(Duration::milliseconds(123)),
            Duration::from_std(StdDuration::new(0, 123_000_000))
        );
        assert_eq!(
            Ok(Duration::milliseconds(123_765)),
            Duration::from_std(StdDuration::new(123, 765_000_000))
        );
        assert_eq!(Ok(Duration::nanoseconds(777)), Duration::from_std(StdDuration::new(0, 777)));
        assert_eq!(
            Ok(MAX),
            Duration::from_std(StdDuration::new(9_223_372_036_854_775, 807_000_000))
        );
        assert_eq!(
            Duration::from_std(StdDuration::new(9_223_372_036_854_776, 0)),
            Err(OutOfRangeError(()))
        );
        assert_eq!(
            Duration::from_std(StdDuration::new(9_223_372_036_854_775, 807_000_001)),
            Err(OutOfRangeError(()))
        );
    }

    #[test]
    fn test_duration_const() {
        const ONE_WEEK: Duration = Duration::weeks(1);
        const ONE_DAY: Duration = Duration::days(1);
        const ONE_HOUR: Duration = Duration::hours(1);
        const ONE_MINUTE: Duration = Duration::minutes(1);
        const ONE_SECOND: Duration = Duration::seconds(1);
        const ONE_MILLI: Duration = Duration::milliseconds(1);
        const ONE_MICRO: Duration = Duration::microseconds(1);
        const ONE_NANO: Duration = Duration::nanoseconds(1);
        let combo: Duration = ONE_WEEK
            + ONE_DAY
            + ONE_HOUR
            + ONE_MINUTE
            + ONE_SECOND
            + ONE_MILLI
            + ONE_MICRO
            + ONE_NANO;

        assert!(ONE_WEEK != Duration::zero());
        assert!(ONE_DAY != Duration::zero());
        assert!(ONE_HOUR != Duration::zero());
        assert!(ONE_MINUTE != Duration::zero());
        assert!(ONE_SECOND != Duration::zero());
        assert!(ONE_MILLI != Duration::zero());
        assert!(ONE_MICRO != Duration::zero());
        assert!(ONE_NANO != Duration::zero());
        assert_eq!(
            combo,
            Duration::seconds(86400 * 7 + 86400 + 3600 + 60 + 1)
                + Duration::nanoseconds(1 + 1_000 + 1_000_000)
        );
    }

    #[test]
    #[cfg(feature = "rkyv-validation")]
    fn test_rkyv_validation() {
        let duration = Duration::seconds(1);
        let bytes = rkyv::to_bytes::<_, 16>(&duration).unwrap();
        assert_eq!(rkyv::from_bytes::<Duration>(&bytes).unwrap(), duration);
    }
}
