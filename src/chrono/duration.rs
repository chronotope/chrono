// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 duration.
 */

use std::{fmt, num};
use num::Integer;

static NANOS_PER_SEC: int = 1_000_000_000;
static SECS_PER_DAY: int = 86400;

#[deriving(Eq, TotalEq, Ord, TotalOrd)]
pub struct Duration {
    days: int,
    secs: u32,
    nanos: u32,
}

impl Duration {
    pub fn new(days: int, secs: int, nanos: int) -> Option<Duration> {
        let (secs_, nanos) = nanos.div_mod_floor(&NANOS_PER_SEC);
        let secs = match secs.checked_add(&secs_) { Some(v) => v, None => return None };
        let (days_, secs) = secs.div_mod_floor(&SECS_PER_DAY);
        let days = match days.checked_add(&days_) { Some(v) => v, None => return None };
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
        self.days
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
        let mut days = -self.days;
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
        Duration { days: days, secs: secs as u32, nanos: nanos as u32 }
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
        let mut days = match self.days.checked_add(&rhs.days) { Some(v) => v, None => return None };
        let mut secs = self.secs + rhs.secs;
        let mut nanos = self.nanos + rhs.nanos;
        if nanos >= NANOS_PER_SEC as u32 {
            nanos -= NANOS_PER_SEC as u32;
            secs += 1;
        }
        if secs >= SECS_PER_DAY as u32 {
            secs -= SECS_PER_DAY as u32;
            days = match days.checked_add(&1) { Some(v) => v, None => return None };
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
        let mut days = match self.days.checked_sub(&rhs.days) { Some(v) => v, None => return None };
        let mut secs = self.secs as int - rhs.secs as int;
        let mut nanos = self.nanos as int - rhs.nanos as int;
        if nanos < 0 {
            nanos += NANOS_PER_SEC;
            secs -= 1;
        }
        if secs < 0 {
            secs += SECS_PER_DAY;
            days = match days.checked_sub(&1) { Some(v) => v, None => return None };
        }
        Some(Duration { days: days, secs: secs as u32, nanos: nanos as u32 })
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
            try!(write!(f.buf, "{}D", self.days));
        }
        if hastime {
            if self.nanos == 0 {
                try!(write!(f.buf, "T{}S", self.secs));
            } else if self.nanos % 1_000_000 == 0 {
                try!(write!(f.buf, "T{},{:03}S", self.secs, self.nanos / 1_000_000));
            } else if self.nanos % 1_000 == 0 {
                try!(write!(f.buf, "T{},{:06}S", self.secs, self.nanos / 1_000));
            } else {
                try!(write!(f.buf, "T{},{:09}S", self.secs, self.nanos));
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
    fn test_duration_checked_ops() {
        assert_eq!(Duration::days(int::MAX).checked_add(&Duration::seconds(86399)),
                   Some(Duration::days(int::MAX - 1) + Duration::seconds(86400+86399)));
        assert!(Duration::days(int::MAX).checked_add(&Duration::seconds(86400)).is_none());

        assert_eq!(Duration::days(int::MIN).checked_sub(&Duration::seconds(0)),
                   Some(Duration::days(int::MIN)));
        assert!(Duration::days(int::MIN).checked_sub(&Duration::seconds(1)).is_none());
    }

    #[test]
    fn test_duration_fmt() {
        assert_eq!(Duration::zero().to_str(), ~"PT0S");
        assert_eq!(Duration::days(42).to_str(), ~"P42D");
        assert_eq!(Duration::days(-42).to_str(), ~"P-42D");
        assert_eq!(Duration::seconds(42).to_str(), ~"PT42S");
        assert_eq!(Duration::milliseconds(42).to_str(), ~"PT0,042S");
        assert_eq!(Duration::microseconds(42).to_str(), ~"PT0,000042S");
        assert_eq!(Duration::nanoseconds(42).to_str(), ~"PT0,000000042S");
        assert_eq!((Duration::days(7) + Duration::milliseconds(6543)).to_str(), ~"P7DT6,543S");
    }
}

