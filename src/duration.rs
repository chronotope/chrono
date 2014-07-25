// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 duration.
 */

use std::{fmt, num, i32};
use num::Integer;

/// `Duration`'s `days` component should have no more than this value.
static MIN_DAYS: i32 = i32::MIN;
/// `Duration`'s `days` component should have no less than this value.
static MAX_DAYS: i32 = i32::MAX;

/// The number of nanoseconds in seconds.
static NANOS_PER_SEC: i32 = 1_000_000_000;
/// The number of (non-leap) seconds in days.
static SECS_PER_DAY: i32 = 86400;

macro_rules! earlyexit(
    ($e:expr) => (match $e { Some(v) => v, None => return None })
)

/// ISO 8601 time duration with nanosecond precision.
/// This also allows for the negative duration; see individual methods for details.
#[deriving(PartialEq, Eq, PartialOrd, Ord)]
pub struct Duration {
    days: i32,
    secs: u32,
    nanos: u32,
}

/// The minimum possible `Duration`.
pub static MIN: Duration = Duration { days: MIN_DAYS, secs: 0, nanos: 0 };
/// The maximum possible `Duration`.
pub static MAX: Duration = Duration { days: MAX_DAYS, secs: SECS_PER_DAY as u32 - 1,
                                      nanos: NANOS_PER_SEC as u32 - 1 };

impl Duration {
    /// Makes a new `Duration` with given number of days, seconds and nanoseconds.
    ///
    /// Fails when the duration is out of bounds.
    #[inline]
    pub fn new(days: i32, secs: i32, nanos: i32) -> Duration {
        Duration::new_opt(days, secs, nanos).expect("Duration::new out of bounds")
    }

    /// Makes a new `Duration` with given number of days, seconds and nanoseconds.
    /// Returns `None` when the duration is out of bounds.
    pub fn new_opt(days: i32, secs: i32, nanos: i32) -> Option<Duration> {
        let (secs_, nanos) = nanos.div_mod_floor(&NANOS_PER_SEC);
        let secs = earlyexit!(secs.checked_add(&secs_));
        let (days_, secs) = secs.div_mod_floor(&SECS_PER_DAY);
        let days = earlyexit!(days.checked_add(&days_).and_then(|v| v.to_i32()));
        Some(Duration { days: days, secs: secs as u32, nanos: nanos as u32 })
    }

    /// Makes a new `Duration` with zero seconds.
    #[inline]
    pub fn zero() -> Duration {
        Duration { days: 0, secs: 0, nanos: 0 }
    }

    /// Makes a new `Duration` with given number of weeks.
    /// Equivalent to `Duration::new(weeks * 7, 0, 0)` with overflow checks.
    ///
    /// Fails when the duration is out of bounds.
    #[inline]
    pub fn weeks(weeks: i32) -> Duration {
        let days = weeks.checked_mul(&7).expect("Duration::weeks out of bounds");
        Duration::days(days)
    }

    /// Makes a new `Duration` with given number of days.
    /// Equivalent to `Duration::new(days, 0, 0)`.
    ///
    /// Fails when the duration is out of bounds.
    #[inline]
    pub fn days(days: i32) -> Duration {
        let days = days.to_i32().expect("Duration::days out of bounds");
        Duration { days: days, secs: 0, nanos: 0 }
    }

    /// Makes a new `Duration` with given number of hours.
    /// Equivalent to `Duration::new(0, hours * 3600, 0)` with overflow checks.
    ///
    /// Fails when the duration is out of bounds.
    #[inline]
    pub fn hours(hours: i32) -> Duration {
        let (days, hours) = hours.div_mod_floor(&(SECS_PER_DAY / 3600));
        let secs = hours * 3600;
        Duration { secs: secs as u32, ..Duration::days(days) }
    }

    /// Makes a new `Duration` with given number of minutes.
    /// Equivalent to `Duration::new(0, mins * 60, 0)` with overflow checks.
    ///
    /// Fails when the duration is out of bounds.
    #[inline]
    pub fn minutes(mins: i32) -> Duration {
        let (days, mins) = mins.div_mod_floor(&(SECS_PER_DAY / 60));
        let secs = mins * 60;
        Duration { secs: secs as u32, ..Duration::days(days) }
    }

    /// Makes a new `Duration` with given number of seconds.
    /// Equivalent to `Duration::new(0, secs, 0)`.
    ///
    /// Fails when the duration is out of bounds.
    #[inline]
    pub fn seconds(secs: i32) -> Duration {
        let (days, secs) = secs.div_mod_floor(&SECS_PER_DAY);
        Duration { secs: secs as u32, ..Duration::days(days) }
    }

    /// Makes a new `Duration` with given number of milliseconds.
    /// Equivalent to `Duration::new(0, 0, millis * 1_000_000)` with overflow checks.
    ///
    /// Fails when the duration is out of bounds.
    #[inline]
    pub fn milliseconds(millis: i32) -> Duration {
        let (secs, millis) = millis.div_mod_floor(&(NANOS_PER_SEC / 1_000_000));
        let nanos = millis * 1_000_000;
        Duration { nanos: nanos as u32, ..Duration::seconds(secs) }
    }

    /// Makes a new `Duration` with given number of microseconds.
    /// Equivalent to `Duration::new(0, 0, micros * 1_000)` with overflow checks.
    ///
    /// Fails when the duration is out of bounds.
    #[inline]
    pub fn microseconds(micros: i32) -> Duration {
        let (secs, micros) = micros.div_mod_floor(&(NANOS_PER_SEC / 1_000));
        let nanos = micros * 1_000;
        Duration { nanos: nanos as u32, ..Duration::seconds(secs) }
    }

    /// Makes a new `Duration` with given number of nanoseconds.
    /// Equivalent to `Duration::new(0, 0, nanos)`.
    ///
    /// Fails when the duration is out of bounds.
    #[inline]
    pub fn nanoseconds(nanos: i32) -> Duration {
        let (secs, nanos) = nanos.div_mod_floor(&NANOS_PER_SEC);
        Duration { nanos: nanos as u32, ..Duration::seconds(secs) }
    }

    /// Returns the number of days in the duration.
    /// For the negative duration, this is a largest integral number of days smaller than `self`.
    #[inline]
    pub fn ndays(&self) -> i32 {
        self.days as i32
    }

    /// Returns the number of (non-leap) seconds in the duration.
    /// This never goes negative even when the duration is negative.
    #[inline]
    pub fn nseconds(&self) -> u32 {
        self.secs as u32
    }

    /// Returns the number of nanoseconds in the duration.
    /// This never goes negative even when the duration is negative.
    #[inline]
    pub fn nnanoseconds(&self) -> u32 {
        self.nanos as u32
    }
}

impl num::Bounded for Duration {
    #[inline] fn min_value() -> Duration { MIN }
    #[inline] fn max_value() -> Duration { MAX }
}

impl num::Zero for Duration {
    #[inline]
    fn zero() -> Duration {
        Duration { days: 0, secs: 0, nanos: 0 }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.days == 0 && self.secs == 0 && self.nanos == 0
    }
}

impl Neg<Duration> for Duration {
    fn neg(&self) -> Duration {
        // XXX overflow (e.g. `-Duration::days(i32::MIN as i32)`)
        let mut days = -(self.days as i32);
        let mut secs = -(self.secs as i32);
        let mut nanos = -(self.nanos as i32);
        if nanos < 0 {
            nanos += NANOS_PER_SEC;
            secs -= 1;
        }
        if secs < 0 {
            secs += SECS_PER_DAY;
            days -= 1;
        }
        Duration { days: days as i32, secs: secs as u32, nanos: nanos as u32 }
    }
}

impl Add<Duration,Duration> for Duration {
    fn add(&self, rhs: &Duration) -> Duration {
        let mut days = self.days + rhs.days;
        let mut secs = self.secs + rhs.secs;
        let mut nanos = self.nanos + rhs.nanos;
        if nanos >= NANOS_PER_SEC as u32 {
            nanos -= NANOS_PER_SEC as u32;
            secs += 1;
        }
        if secs >= SECS_PER_DAY as u32 {
            secs -= SECS_PER_DAY as u32;
            days += 1;
        }
        Duration { days: days, secs: secs, nanos: nanos }
    }
}

impl num::CheckedAdd for Duration {
    fn checked_add(&self, rhs: &Duration) -> Option<Duration> {
        let mut days = earlyexit!(self.days.checked_add(&rhs.days));
        let mut secs = self.secs + rhs.secs;
        let mut nanos = self.nanos + rhs.nanos;
        if nanos >= NANOS_PER_SEC as u32 {
            nanos -= NANOS_PER_SEC as u32;
            secs += 1;
        }
        if secs >= SECS_PER_DAY as u32 {
            secs -= SECS_PER_DAY as u32;
            days = earlyexit!(days.checked_add(&1));
        }
        Some(Duration { days: days, secs: secs, nanos: nanos })
    }
}

impl Sub<Duration,Duration> for Duration {
    fn sub(&self, rhs: &Duration) -> Duration {
        let mut days = self.days - rhs.days;
        let mut secs = self.secs as i32 - rhs.secs as i32;
        let mut nanos = self.nanos as i32 - rhs.nanos as i32;
        if nanos < 0 {
            nanos += NANOS_PER_SEC;
            secs -= 1;
        }
        if secs < 0 {
            secs += SECS_PER_DAY;
            days -= 1;
        }
        Duration { days: days, secs: secs as u32, nanos: nanos as u32 }
    }
}

impl num::CheckedSub for Duration {
    fn checked_sub(&self, rhs: &Duration) -> Option<Duration> {
        let mut days = earlyexit!(self.days.checked_sub(&rhs.days));
        let mut secs = self.secs as i32 - rhs.secs as i32;
        let mut nanos = self.nanos as i32 - rhs.nanos as i32;
        if nanos < 0 {
            nanos += NANOS_PER_SEC;
            secs -= 1;
        }
        if secs < 0 {
            secs += SECS_PER_DAY;
            days = earlyexit!(days.checked_sub(&1));
        }
        Some(Duration { days: days, secs: secs as u32, nanos: nanos as u32 })
    }
}

impl Mul<i32,Duration> for Duration {
    fn mul(&self, rhs: &i32) -> Duration {
        /// Given `0 <= y < limit <= 2^30`,
        /// returns `(h,l)` such that `x * y = h * limit + l` where `0 <= l < limit`.
        fn mul_i64_u32_limit(x: i64, y: u32, limit: u32) -> (i64,u32) {
            let y = y as i64;
            let limit = limit as i64;
            let (xh, xl) = x.div_mod_floor(&limit);
            let (h, l) = (xh * y, xl * y);
            let (h_, l) = l.div_rem(&limit);
            (h + h_, l as u32)
        }

        let rhs = *rhs as i64;
        let (secs1, nanos) = mul_i64_u32_limit(rhs, self.nanos, NANOS_PER_SEC as u32);
        let (days1, secs1) = secs1.div_mod_floor(&(SECS_PER_DAY as i64));
        let (days2, secs2) = mul_i64_u32_limit(rhs, self.secs, SECS_PER_DAY as u32);
        let mut days = self.days as i64 * rhs + days1 + days2;
        let mut secs = secs1 as u32 + secs2;
        if secs >= SECS_PER_DAY as u32 {
            secs -= 1;
            days += 1;
        }
        Duration { days: days as i32, secs: secs, nanos: nanos }
    }
}

impl Div<i32,Duration> for Duration {
    fn div(&self, rhs: &i32) -> Duration {
        let (rhs, days, secs, nanos) = if *rhs < 0 {
            let negated = -*self;
            (-*rhs as i64, negated.days as i64, negated.secs as i64, negated.nanos as i64)
        } else {
            (*rhs as i64, self.days as i64, self.secs as i64, self.nanos as i64)
        };

        let (days, carry) = days.div_mod_floor(&rhs);
        let secs = secs + carry * SECS_PER_DAY as i64;
        let (secs, carry) = secs.div_mod_floor(&rhs);
        let nanos = nanos + carry * NANOS_PER_SEC as i64;
        let nanos = nanos / rhs;
        Duration { days: days as i32, secs: secs as u32, nanos: nanos as u32 }
    }
}

impl fmt::Show for Duration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let hasdate = self.days != 0;
        let hastime = (self.secs != 0 || self.nanos != 0) || !hasdate;

        try!(write!(f, "P"));
        if hasdate {
            // technically speaking the negative part is not the valid ISO 8601,
            // but we need to print it anyway.
            try!(write!(f, "{}D", self.days));
        }
        if hastime {
            if self.nanos == 0 {
                try!(write!(f, "T{}S", self.secs));
            } else if self.nanos % 1_000_000 == 0 {
                try!(write!(f, "T{}.{:03}S", self.secs, self.nanos / 1_000_000));
            } else if self.nanos % 1_000 == 0 {
                try!(write!(f, "T{}.{:06}S", self.secs, self.nanos / 1_000));
            } else {
                try!(write!(f, "T{}.{:09}S", self.secs, self.nanos));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{Duration, MIN_DAYS, MAX_DAYS};
    use std::i32;

    #[test]
    fn test_duration() {
        assert_eq!(Duration::zero(), Duration::zero());
        assert!(Duration::zero() != Duration::seconds(1));
        assert_eq!(Duration::seconds(1) + Duration::seconds(2), Duration::seconds(3));
        assert_eq!(Duration::seconds(86399) + Duration::seconds(4),
                   Duration::days(1) + Duration::seconds(3));
        assert_eq!(Duration::days(10) - Duration::seconds(1000), Duration::seconds(863000));
        assert_eq!(Duration::days(10) - Duration::seconds(1000000), Duration::seconds(-136000));
        assert_eq!(Duration::days(2) + Duration::seconds(86399) + Duration::nanoseconds(1234567890),
                   Duration::days(3) + Duration::nanoseconds(234567890));
        assert_eq!(-Duration::days(3), Duration::days(-3));
        assert_eq!(-(Duration::days(3) + Duration::seconds(70)),
                   Duration::days(-4) + Duration::seconds(86400-70));
    }

    #[test]
    fn test_duration_checked_ops() {
        assert_eq!(Duration::days(MAX_DAYS).checked_add(&Duration::seconds(86399)),
                   Some(Duration::days(MAX_DAYS - 1) + Duration::seconds(86400+86399)));
        assert!(Duration::days(MAX_DAYS).checked_add(&Duration::seconds(86400)).is_none());

        assert_eq!(Duration::days(MIN_DAYS).checked_sub(&Duration::seconds(0)),
                   Some(Duration::days(MIN_DAYS)));
        assert!(Duration::days(MIN_DAYS).checked_sub(&Duration::seconds(1)).is_none());
    }

    #[test]
    fn test_duration_mul() {
        assert_eq!(Duration::zero() * i32::MAX, Duration::zero());
        assert_eq!(Duration::zero() * i32::MIN, Duration::zero());
        assert_eq!(Duration::nanoseconds(1) * 0, Duration::zero());
        assert_eq!(Duration::nanoseconds(1) * 1, Duration::nanoseconds(1));
        assert_eq!(Duration::nanoseconds(1) * 1_000_000_000, Duration::seconds(1));
        assert_eq!(Duration::nanoseconds(1) * -1_000_000_000, -Duration::seconds(1));
        assert_eq!(-Duration::nanoseconds(1) * 1_000_000_000, -Duration::seconds(1));
        assert_eq!(Duration::nanoseconds(30) * 333_333_333,
                   Duration::seconds(10) - Duration::nanoseconds(10));
        assert_eq!((Duration::nanoseconds(1) + Duration::seconds(1) + Duration::days(1)) * 3,
                   Duration::nanoseconds(3) + Duration::seconds(3) + Duration::days(3));
    }

    #[test]
    fn test_duration_div() {
        assert_eq!(Duration::zero() / i32::MAX, Duration::zero());
        assert_eq!(Duration::zero() / i32::MIN, Duration::zero());
        assert_eq!(Duration::nanoseconds(123_456_789) / 1, Duration::nanoseconds(123_456_789));
        assert_eq!(Duration::nanoseconds(123_456_789) / -1, -Duration::nanoseconds(123_456_789));
        assert_eq!(-Duration::nanoseconds(123_456_789) / -1, Duration::nanoseconds(123_456_789));
        assert_eq!(-Duration::nanoseconds(123_456_789) / 1, -Duration::nanoseconds(123_456_789));
    }

    #[test]
    fn test_duration_fmt() {
        assert_eq!(Duration::zero().to_string(), "PT0S".to_string());
        assert_eq!(Duration::days(42).to_string(), "P42D".to_string());
        assert_eq!(Duration::days(-42).to_string(), "P-42D".to_string());
        assert_eq!(Duration::seconds(42).to_string(), "PT42S".to_string());
        assert_eq!(Duration::milliseconds(42).to_string(), "PT0.042S".to_string());
        assert_eq!(Duration::microseconds(42).to_string(), "PT0.000042S".to_string());
        assert_eq!(Duration::nanoseconds(42).to_string(), "PT0.000000042S".to_string());
        assert_eq!((Duration::days(7) + Duration::milliseconds(6543)).to_string(),
                   "P7DT6.543S".to_string());

        // the format specifier should have no effect on `Duration`
        assert_eq!(format!("{:30}", Duration::days(1) + Duration::milliseconds(2345)),
                   "P1DT2.345S".to_string());
    }
}

