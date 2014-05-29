// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 duration.
 */

use std::{fmt, num, i32};
use num::Integer;

pub static MIN_DAYS: int = i32::MIN as int;
pub static MAX_DAYS: int = i32::MAX as int;

static NANOS_PER_SEC: int = 1_000_000_000;
static SECS_PER_DAY: int = 86400;

macro_rules! earlyexit(
    ($e:expr) => (match $e { Some(v) => v, None => return None })
)

#[deriving(Eq, TotalEq, Ord, TotalOrd)]
pub struct Duration {
    days: i32,
    secs: u32,
    nanos: u32,
}

impl Duration {
    pub fn new(days: int, secs: int, nanos: int) -> Option<Duration> {
        let (secs_, nanos) = nanos.div_mod_floor(&NANOS_PER_SEC);
        let secs = earlyexit!(secs.checked_add(&secs_));
        let (days_, secs) = secs.div_mod_floor(&SECS_PER_DAY);
        let days = earlyexit!(days.checked_add(&days_).and_then(|v| v.to_i32()));
        Some(Duration { days: days, secs: secs as u32, nanos: nanos as u32 })
    }

    #[inline]
    pub fn zero() -> Duration {
        Duration { days: 0, secs: 0, nanos: 0 }
    }

    #[inline]
    pub fn weeks(weeks: int) -> Duration {
        Duration::days(weeks * 7)
    }

    #[inline]
    pub fn days(days: int) -> Duration {
        let days = days.to_i32().expect("Duration::days out of bounds");
        Duration { days: days, secs: 0, nanos: 0 }
    }

    #[inline]
    pub fn hours(hours: int) -> Duration {
        Duration::seconds(hours * 3600)
    }

    #[inline]
    pub fn minutes(mins: int) -> Duration {
        Duration::seconds(mins * 60)
    }

    #[inline]
    pub fn seconds(secs: int) -> Duration {
        let (days, secs) = secs.div_mod_floor(&SECS_PER_DAY);
        Duration { secs: secs as u32, ..Duration::days(days) }
    }

    #[inline]
    pub fn milliseconds(millis: int) -> Duration {
        Duration::nanoseconds(millis * 1_000_000)
    }

    #[inline]
    pub fn microseconds(micros: int) -> Duration {
        Duration::nanoseconds(micros * 1_000)
    }

    #[inline]
    pub fn nanoseconds(nanos: int) -> Duration {
        let (secs, nanos) = nanos.div_mod_floor(&NANOS_PER_SEC);
        Duration { nanos: nanos as u32, ..Duration::seconds(secs) }
    }

    #[inline]
    pub fn ndays(&self) -> int {
        self.days as int
    }

    #[inline]
    pub fn nseconds(&self) -> uint {
        self.secs as uint
    }

    #[inline]
    pub fn nnanoseconds(&self) -> uint {
        self.nanos as uint
    }
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
        // XXX overflow (e.g. `-Duration::days(i32::MIN as int)`)
        let mut days = -(self.days as int);
        let mut secs = -(self.secs as int);
        let mut nanos = -(self.nanos as int);
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
        let mut secs = self.secs as int - rhs.secs as int;
        let mut nanos = self.nanos as int - rhs.nanos as int;
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
        let mut secs = self.secs as int - rhs.secs as int;
        let mut nanos = self.nanos as int - rhs.nanos as int;
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

impl Mul<int,Duration> for Duration {
    fn mul(&self, rhs: &int) -> Duration {
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

impl Div<int,Duration> for Duration {
    fn div(&self, rhs: &int) -> Duration {
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

        try!('P'.fmt(f));
        if hasdate {
            // technically speaking the negative part is not the valid ISO 8601,
            // but we need to print it anyway.
            try!(write!(f, "{}D", self.days));
        }
        if hastime {
            if self.nanos == 0 {
                try!(write!(f, "T{}S", self.secs));
            } else if self.nanos % 1_000_000 == 0 {
                try!(write!(f, "T{},{:03}S", self.secs, self.nanos / 1_000_000));
            } else if self.nanos % 1_000 == 0 {
                try!(write!(f, "T{},{:06}S", self.secs, self.nanos / 1_000));
            } else {
                try!(write!(f, "T{},{:09}S", self.secs, self.nanos));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::int;

    #[test]
    fn test_duration() {
        assert_eq!(Duration::zero(), Duration::zero());
        assert!(Duration::zero() != Duration::seconds(1));
        assert_eq!(Duration::seconds(1) + Duration::seconds(2), Duration::seconds(3));
        assert_eq!(Duration::seconds(86399) + Duration::seconds(4),
                   Duration::days(1) + Duration::seconds(3));
        assert_eq!(Duration::days(10) - Duration::seconds(1000), Duration::seconds(863000));
        assert_eq!(Duration::days(10) - Duration::seconds(1000000), Duration::seconds(-136000));
        assert_eq!(Duration::days(2) + Duration::seconds(86391) + Duration::nanoseconds(9876543210),
                   Duration::days(3) + Duration::nanoseconds(876543210));
        assert_eq!(-Duration::days(3), Duration::days(-3));
        assert_eq!(-(Duration::days(3) + Duration::seconds(70)),
                   Duration::days(-4) + Duration::seconds(86400-70));
    }

    #[test]
    #[cfg(target_word_size = "64")]
    fn test_duration_carry() {
        assert_eq!(Duration::seconds((MAX_DAYS + 1) * 86400 - 1),
                   Duration::new(MAX_DAYS, 86399, 0).unwrap());
        assert_eq!(Duration::seconds(MIN_DAYS * 86400),
                   Duration::new(MIN_DAYS, 0, 0).unwrap());

        // 86400 * 10^9 * (2^31-1) exceeds 2^63-1, so there is no test for nanoseconds
    }

    #[test]
    #[should_fail]
    #[cfg(target_word_size = "64")]
    fn test_duration_days_out_of_bound_1() {
        Duration::days(MAX_DAYS + 1);
    }

    #[test]
    #[should_fail]
    #[cfg(target_word_size = "64")]
    fn test_duration_days_out_of_bound_2() {
        Duration::days(MIN_DAYS - 1);
    }

    #[test]
    #[should_fail]
    #[cfg(target_word_size = "64")]
    fn test_duration_seconds_out_of_bound_1() {
        Duration::seconds((MAX_DAYS + 1) * 86400);
    }

    #[test]
    #[should_fail]
    #[cfg(target_word_size = "64")]
    fn test_duration_seconds_out_of_bound_2() {
        Duration::seconds(MIN_DAYS * 86400 - 1);
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
        assert_eq!(Duration::zero() * int::MAX, Duration::zero());
        assert_eq!(Duration::zero() * int::MIN, Duration::zero());
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
    #[cfg(target_word_size = "64")]
    fn test_duration_mul_64() {
        assert_eq!(Duration::nanoseconds(1) * 86400_000_000_000, Duration::days(1));
        assert_eq!((Duration::seconds(13) + Duration::nanoseconds(333_333_333)) * 64800,
                   Duration::days(10) - Duration::nanoseconds(21600));
        assert_eq!((Duration::nanoseconds(1) + Duration::seconds(1) +
                    Duration::days(1)) * 2_000_000_000,
                   Duration::nanoseconds(2_000_000_000) + Duration::seconds(2_000_000_000) +
                   Duration::days(2_000_000_000));
    }

    #[test]
    fn test_duration_div() {
        assert_eq!(Duration::zero() / int::MAX, Duration::zero());
        assert_eq!(Duration::zero() / int::MIN, Duration::zero());
        assert_eq!(Duration::nanoseconds(123_456_789) / 1, Duration::nanoseconds(123_456_789));
        assert_eq!(Duration::nanoseconds(123_456_789) / -1, -Duration::nanoseconds(123_456_789));
        assert_eq!(-Duration::nanoseconds(123_456_789) / -1, Duration::nanoseconds(123_456_789));
        assert_eq!(-Duration::nanoseconds(123_456_789) / 1, -Duration::nanoseconds(123_456_789));
    }

    #[test]
    #[cfg(target_word_size = "64")]
    fn test_duration_div_64() {
        assert_eq!(Duration::nanoseconds(  999_999_999_999_999_999) / 9,
                   Duration::nanoseconds(  111_111_111_111_111_111));
        assert_eq!(Duration::nanoseconds(1_000_000_000_000_000_000) / 9,
                   Duration::nanoseconds(  111_111_111_111_111_111));
        assert_eq!(-Duration::nanoseconds(  999_999_999_999_999_999) / 9,
                   -Duration::nanoseconds(  111_111_111_111_111_111));
        assert_eq!(-Duration::nanoseconds(1_000_000_000_000_000_000) / 9,
                   -Duration::nanoseconds(  111_111_111_111_111_112)); // XXX inconsistent
    }

    #[test]
    fn test_duration_fmt() {
        assert_eq!(Duration::zero().to_str(), "PT0S".to_string());
        assert_eq!(Duration::days(42).to_str(), "P42D".to_string());
        assert_eq!(Duration::days(-42).to_str(), "P-42D".to_string());
        assert_eq!(Duration::seconds(42).to_str(), "PT42S".to_string());
        assert_eq!(Duration::milliseconds(42).to_str(), "PT0,042S".to_string());
        assert_eq!(Duration::microseconds(42).to_str(), "PT0,000042S".to_string());
        assert_eq!(Duration::nanoseconds(42).to_str(), "PT0,000000042S".to_string());
        assert_eq!((Duration::days(7) + Duration::milliseconds(6543)).to_str(),
                   "P7DT6,543S".to_string());
    }
}

