// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 time.
 */

use std::fmt;
use num::Integer;
use duration::Duration;

/// The common set of methods for time component.
pub trait Timelike {
    /// Returns the hour number from 0 to 23.
    fn hour(&self) -> u32;

    /// Returns the hour number from 1 to 12 with a boolean flag,
    /// which is false for AM and true for PM.
    #[inline]
    fn hour12(&self) -> (bool, u32) {
        let hour = self.hour();
        let mut hour12 = hour % 12;
        if hour12 == 0 { hour12 = 12; }
        (hour >= 12, hour12)
    }

    /// Returns the minute number from 0 to 59.
    fn minute(&self) -> u32;

    /// Returns the second number from 0 to 59.
    fn second(&self) -> u32;

    /// Returns the number of nanoseconds since the whole non-leap second.
    /// The range from 1,000,000,000 to 1,999,999,999 represents the leap second.
    fn nanosecond(&self) -> u32;

    /// Makes a new value with the hour number changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_hour(&self, hour: u32) -> Option<Self>;

    /// Makes a new value with the minute number changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_minute(&self, min: u32) -> Option<Self>;

    /// Makes a new value with the second number changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_second(&self, sec: u32) -> Option<Self>;

    /// Makes a new value with nanoseconds since the whole non-leap second changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_nanosecond(&self, nano: u32) -> Option<Self>;

    /// Returns the number of non-leap seconds past the last midnight.
    #[inline]
    fn num_seconds_from_midnight(&self) -> u32 {
        self.hour() * 3600 + self.minute() * 60 + self.second()
    }
}

/// ISO 8601 time without timezone.
/// Allows for the nanosecond precision and optional leap second representation.
#[deriving(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TimeZ {
    hour: u8,
    min: u8,
    sec: u8,
    frac: u32,
}

impl TimeZ {
    /// Makes a new `TimeZ` from hour, minute and second.
    ///
    /// Fails on invalid hour, minute and/or second.
    #[inline]
    pub fn from_hms(hour: u32, min: u32, sec: u32) -> TimeZ {
        TimeZ::from_hms_opt(hour, min, sec).expect("invalid time")
    }

    /// Makes a new `TimeZ` from hour, minute and second.
    ///
    /// Returns `None` on invalid hour, minute and/or second.
    #[inline]
    pub fn from_hms_opt(hour: u32, min: u32, sec: u32) -> Option<TimeZ> {
        TimeZ::from_hms_nano_opt(hour, min, sec, 0)
    }

    /// Makes a new `TimeZ` from hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn from_hms_milli(hour: u32, min: u32, sec: u32, milli: u32) -> TimeZ {
        TimeZ::from_hms_milli_opt(hour, min, sec, milli).expect("invalid time")
    }

    /// Makes a new `TimeZ` from hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn from_hms_milli_opt(hour: u32, min: u32, sec: u32, milli: u32) -> Option<TimeZ> {
        milli.checked_mul(&1_000_000).and_then(|nano| TimeZ::from_hms_nano_opt(hour, min, sec,
                                                                               nano))
    }

    /// Makes a new `TimeZ` from hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn from_hms_micro(hour: u32, min: u32, sec: u32, micro: u32) -> TimeZ {
        TimeZ::from_hms_micro_opt(hour, min, sec, micro).expect("invalid time")
    }

    /// Makes a new `TimeZ` from hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn from_hms_micro_opt(hour: u32, min: u32, sec: u32, micro: u32) -> Option<TimeZ> {
        micro.checked_mul(&1_000).and_then(|nano| TimeZ::from_hms_nano_opt(hour, min, sec, nano))
    }

    /// Makes a new `TimeZ` from hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or nanosecond.
    pub fn from_hms_nano(hour: u32, min: u32, sec: u32, nano: u32) -> TimeZ {
        TimeZ::from_hms_nano_opt(hour, min, sec, nano).expect("invalid time")
    }

    /// Makes a new `TimeZ` from hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or nanosecond.
    pub fn from_hms_nano_opt(hour: u32, min: u32, sec: u32, nano: u32) -> Option<TimeZ> {
        if hour >= 24 || min >= 60 || sec >= 60 || nano >= 2_000_000_000 { return None; }
        Some(TimeZ { hour: hour as u8, min: min as u8, sec: sec as u8, frac: nano as u32 })
    }
}

impl Timelike for TimeZ {
    #[inline] fn hour(&self) -> u32 { self.hour as u32 }
    #[inline] fn minute(&self) -> u32 { self.min as u32 }
    #[inline] fn second(&self) -> u32 { self.sec as u32 }
    #[inline] fn nanosecond(&self) -> u32 { self.frac as u32 }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<TimeZ> {
        if hour >= 24 { return None; }
        Some(TimeZ { hour: hour as u8, ..*self })
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<TimeZ> {
        if min >= 60 { return None; }
        Some(TimeZ { min: min as u8, ..*self })
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<TimeZ> {
        if sec >= 60 { return None; }
        Some(TimeZ { sec: sec as u8, ..*self })
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<TimeZ> {
        if nano >= 2_000_000_000 { return None; }
        Some(TimeZ { frac: nano as u32, ..*self })
    }
}

impl Add<Duration,TimeZ> for TimeZ {
    fn add(&self, rhs: &Duration) -> TimeZ {
        let (_, rhssecs, rhsnanos) = rhs.to_tuple();
        let mut secs = self.num_seconds_from_midnight() as i32 + rhssecs as i32;
        let mut nanos = self.frac + rhsnanos;

        // always ignore leap seconds after the current whole second
        let maxnanos = if self.frac >= 1_000_000_000 {2_000_000_000} else {1_000_000_000};

        if nanos >= maxnanos {
            nanos -= maxnanos;
            secs += 1;
        }
        let (mins, s) = secs.div_rem(&60);
        let (hours, m) = mins.div_rem(&60);
        let h = hours % 24;
        TimeZ { hour: h as u8, min: m as u8, sec: s as u8, frac: nanos }
    }
}

/*
// Rust issue #7590, the current coherence checker can't handle multiple Add impls
impl Add<TimeZ,TimeZ> for Duration {
    #[inline]
    fn add(&self, rhs: &TimeZ) -> TimeZ { rhs.add(self) }
}
*/

impl Sub<TimeZ,Duration> for TimeZ {
    fn sub(&self, rhs: &TimeZ) -> Duration {
        // the number of whole non-leap seconds
        let secs = (self.hour as i32 - rhs.hour as i32) * 3600 +
                   (self.min  as i32 - rhs.min  as i32) * 60 +
                   (self.sec  as i32 - rhs.sec  as i32) - 1;

        // the fractional second from the rhs to the next non-leap second
        let maxnanos = if rhs.frac >= 1_000_000_000 {2_000_000_000} else {1_000_000_000};
        let nanos1 = maxnanos - rhs.frac;

        // the fractional second from the last leap or non-leap second to the lhs
        let lastfrac = if self.frac >= 1_000_000_000 {1_000_000_000} else {0};
        let nanos2 = self.frac - lastfrac;

        Duration::seconds(secs) + Duration::nanoseconds(nanos1 as i32 + nanos2 as i32)
    }
}

impl fmt::Show for TimeZ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (sec, nano) = if self.frac >= 1_000_000_000 {
            (self.sec + 1, self.frac - 1_000_000_000)
        } else {
            (self.sec, self.frac)
        };

        try!(write!(f, "{:02}:{:02}:{:02}", self.hour, self.min, sec));
        if nano == 0 {
            Ok(())
        } else if nano % 1_000_000 == 0 {
            write!(f, ",{:03}", nano / 1_000_000)
        } else if nano % 1_000 == 0 {
            write!(f, ",{:06}", nano / 1_000)
        } else {
            write!(f, ",{:09}", nano)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::TimeZ;
    use duration::Duration;
    use std::u32;

    #[test]
    fn test_time_from_hms_milli() {
        assert_eq!(TimeZ::from_hms_milli_opt(3, 5, 7, 0),
                   Some(TimeZ::from_hms_nano(3, 5, 7, 0)));
        assert_eq!(TimeZ::from_hms_milli_opt(3, 5, 7, 777),
                   Some(TimeZ::from_hms_nano(3, 5, 7, 777_000_000)));
        assert_eq!(TimeZ::from_hms_milli_opt(3, 5, 7, 1_999),
                   Some(TimeZ::from_hms_nano(3, 5, 7, 1_999_000_000)));
        assert_eq!(TimeZ::from_hms_milli_opt(3, 5, 7, 2_000), None);
        assert_eq!(TimeZ::from_hms_milli_opt(3, 5, 7, 5_000), None); // overflow check
        assert_eq!(TimeZ::from_hms_milli_opt(3, 5, 7, u32::MAX), None);
    }

    #[test]
    fn test_time_from_hms_micro() {
        assert_eq!(TimeZ::from_hms_micro_opt(3, 5, 7, 0),
                   Some(TimeZ::from_hms_nano(3, 5, 7, 0)));
        assert_eq!(TimeZ::from_hms_micro_opt(3, 5, 7, 333),
                   Some(TimeZ::from_hms_nano(3, 5, 7, 333_000)));
        assert_eq!(TimeZ::from_hms_micro_opt(3, 5, 7, 777_777),
                   Some(TimeZ::from_hms_nano(3, 5, 7, 777_777_000)));
        assert_eq!(TimeZ::from_hms_micro_opt(3, 5, 7, 1_999_999),
                   Some(TimeZ::from_hms_nano(3, 5, 7, 1_999_999_000)));
        assert_eq!(TimeZ::from_hms_micro_opt(3, 5, 7, 2_000_000), None);
        assert_eq!(TimeZ::from_hms_micro_opt(3, 5, 7, 5_000_000), None); // overflow check
        assert_eq!(TimeZ::from_hms_micro_opt(3, 5, 7, u32::MAX), None);
    }

    #[test]
    fn test_time_add() {
        fn check(lhs: TimeZ, rhs: Duration, sum: TimeZ) {
            assert_eq!(lhs + rhs, sum);
            //assert_eq!(rhs + lhs, sum);
        }

        let hmsm = |h,m,s,mi| TimeZ::from_hms_milli(h, m, s, mi);

        check(hmsm(3, 5, 7, 900), Duration::zero(), hmsm(3, 5, 7, 900));
        check(hmsm(3, 5, 7, 900), Duration::milliseconds(100), hmsm(3, 5, 8, 0));
        check(hmsm(3, 5, 7, 1_300), Duration::milliseconds(800), hmsm(3, 5, 8, 100));
        check(hmsm(3, 5, 7, 900), Duration::seconds(86399), hmsm(3, 5, 6, 900)); // overwrap
        check(hmsm(3, 5, 7, 900), Duration::seconds(-86399), hmsm(3, 5, 8, 900));
        check(hmsm(3, 5, 7, 900), Duration::days(12345), hmsm(3, 5, 7, 900));
    }

    #[test]
    fn test_time_sub() {
        fn check(lhs: TimeZ, rhs: TimeZ, diff: Duration) {
            // `time1 - time2 = duration` is equivalent to `time2 - time1 = -duration`
            assert_eq!(lhs - rhs, diff);
            assert_eq!(rhs - lhs, -diff);
        }

        let hmsm = |h,m,s,mi| TimeZ::from_hms_milli(h, m, s, mi);

        check(hmsm(3, 5, 7, 900), hmsm(3, 5, 7, 900), Duration::zero());
        check(hmsm(3, 5, 7, 900), hmsm(3, 5, 7, 600), Duration::milliseconds(300));
        check(hmsm(3, 5, 7, 200), hmsm(2, 4, 6, 200), Duration::seconds(3600 + 60 + 1));
        check(hmsm(3, 5, 7, 200), hmsm(2, 4, 6, 300),
                   Duration::seconds(3600 + 60) + Duration::milliseconds(900));

        // treats the leap second as if it coincides with the prior non-leap second,
        // as required by `time1 - time2 = duration` and `time2 - time1 = -duration` equivalence.
        check(hmsm(3, 5, 7, 200), hmsm(3, 5, 6, 1_800), Duration::milliseconds(400));
        check(hmsm(3, 5, 7, 1_200), hmsm(3, 5, 6, 1_800), Duration::milliseconds(400));
        check(hmsm(3, 5, 7, 1_200), hmsm(3, 5, 6, 800), Duration::milliseconds(400));

        // additional equality: `time1 + duration = time2` is equivalent to
        // `time2 - time1 = duration` IF AND ONLY IF `time2` represents a non-leap second.
        assert_eq!(hmsm(3, 5, 6, 800) + Duration::milliseconds(400), hmsm(3, 5, 7, 200));
        assert_eq!(hmsm(3, 5, 6, 1_800) + Duration::milliseconds(400), hmsm(3, 5, 7, 200));
    }

    #[test]
    fn test_time_fmt() {
        assert_eq!(TimeZ::from_hms_milli(23, 59, 59, 999).to_string(),
                   "23:59:59,999".to_string());
        assert_eq!(TimeZ::from_hms_milli(23, 59, 59, 1_000).to_string(),
                   "23:59:60".to_string());
        assert_eq!(TimeZ::from_hms_milli(23, 59, 59, 1_001).to_string(),
                   "23:59:60,001".to_string());
        assert_eq!(TimeZ::from_hms_micro(0, 0, 0, 43210).to_string(),
                   "00:00:00,043210".to_string());
        assert_eq!(TimeZ::from_hms_nano(0, 0, 0, 6543210).to_string(),
                   "00:00:00,006543210".to_string());

        // the format specifier should have no effect on `TimeZ`
        assert_eq!(format!("{:30}", TimeZ::from_hms_milli(3, 5, 7, 9)),
                   "03:05:07,009".to_string());
    }
}

