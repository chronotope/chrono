// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 time without timezone.
 */

use std::{str, fmt, hash};
use std::ops::{Add, Sub};

use Timelike;
use div::div_mod_floor;
use duration::Duration;
use format::{Item, Numeric, Pad, Fixed};
use format::{parse, Parsed, ParseError, ParseResult, DelayedFormat, StrftimeItems};

/// ISO 8601 time without timezone.
/// Allows for the nanosecond precision and optional leap second representation.
#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
#[cfg_attr(feature = "rustc-serialize", derive(RustcEncodable, RustcDecodable))]
pub struct NaiveTime {
    secs: u32,
    frac: u32,
}

impl NaiveTime {
    /// Makes a new `NaiveTime` from hour, minute and second.
    ///
    /// Fails on invalid hour, minute and/or second.
    #[inline]
    pub fn from_hms(hour: u32, min: u32, sec: u32) -> NaiveTime {
        NaiveTime::from_hms_opt(hour, min, sec).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from hour, minute and second.
    ///
    /// Returns `None` on invalid hour, minute and/or second.
    #[inline]
    pub fn from_hms_opt(hour: u32, min: u32, sec: u32) -> Option<NaiveTime> {
        NaiveTime::from_hms_nano_opt(hour, min, sec, 0)
    }

    /// Makes a new `NaiveTime` from hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn from_hms_milli(hour: u32, min: u32, sec: u32, milli: u32) -> NaiveTime {
        NaiveTime::from_hms_milli_opt(hour, min, sec, milli).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn from_hms_milli_opt(hour: u32, min: u32, sec: u32, milli: u32) -> Option<NaiveTime> {
        milli.checked_mul(1_000_000)
             .and_then(|nano| NaiveTime::from_hms_nano_opt(hour, min, sec, nano))
    }

    /// Makes a new `NaiveTime` from hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn from_hms_micro(hour: u32, min: u32, sec: u32, micro: u32) -> NaiveTime {
        NaiveTime::from_hms_micro_opt(hour, min, sec, micro).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn from_hms_micro_opt(hour: u32, min: u32, sec: u32, micro: u32) -> Option<NaiveTime> {
        micro.checked_mul(1_000)
             .and_then(|nano| NaiveTime::from_hms_nano_opt(hour, min, sec, nano))
    }

    /// Makes a new `NaiveTime` from hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or nanosecond.
    #[inline]
    pub fn from_hms_nano(hour: u32, min: u32, sec: u32, nano: u32) -> NaiveTime {
        NaiveTime::from_hms_nano_opt(hour, min, sec, nano).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or nanosecond.
    #[inline]
    pub fn from_hms_nano_opt(hour: u32, min: u32, sec: u32, nano: u32) -> Option<NaiveTime> {
        if hour >= 24 || min >= 60 || sec >= 60 || nano >= 2_000_000_000 { return None; }
        let secs = hour * 3600 + min * 60 + sec;
        Some(NaiveTime { secs: secs, frac: nano })
    }

    /// Makes a new `NaiveTime` from the number of seconds since midnight and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Fails on invalid number of seconds and/or nanosecond.
    #[inline]
    pub fn from_num_seconds_from_midnight(secs: u32, nano: u32) -> NaiveTime {
        NaiveTime::from_num_seconds_from_midnight_opt(secs, nano).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from the number of seconds since midnight and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid number of seconds and/or nanosecond.
    #[inline]
    pub fn from_num_seconds_from_midnight_opt(secs: u32, nano: u32) -> Option<NaiveTime> {
        if secs >= 86400 || nano >= 2_000_000_000 { return None; }
        Some(NaiveTime { secs: secs, frac: nano })
    }

    /// Parses a string with the specified format string and returns a new `NaiveTime`.
    /// See the `format::strftime` module on the supported escape sequences.
    pub fn parse_from_str(s: &str, fmt: &str) -> ParseResult<NaiveTime> {
        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, StrftimeItems::new(fmt)));
        parsed.to_naive_time()
    }

    /// Formats the time with the specified formatting items.
    #[inline]
    pub fn format_with_items<'a, I>(&self, items: I) -> DelayedFormat<I>
            where I: Iterator<Item=Item<'a>> + Clone {
        DelayedFormat::new(None, Some(self.clone()), items)
    }

    /// Formats the time with the specified format string.
    /// See the `format::strftime` module on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_with_items(StrftimeItems::new(fmt))
    }

    /// Returns a triple of the hour, minute and second numbers.
    fn hms(&self) -> (u32, u32, u32) {
        let (mins, sec) = div_mod_floor(self.secs, 60);
        let (hour, min) = div_mod_floor(mins, 60);
        (hour, min, sec)
    }
}

impl Timelike for NaiveTime {
    #[inline] fn hour(&self) -> u32 { self.hms().0 }
    #[inline] fn minute(&self) -> u32 { self.hms().1 }
    #[inline] fn second(&self) -> u32 { self.hms().2 }
    #[inline] fn nanosecond(&self) -> u32 { self.frac }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<NaiveTime> {
        if hour >= 24 { return None; }
        let secs = hour * 3600 + self.secs % 3600;
        Some(NaiveTime { secs: secs, ..*self })
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<NaiveTime> {
        if min >= 60 { return None; }
        let secs = self.secs / 3600 * 3600 + min * 60 + self.secs % 60;
        Some(NaiveTime { secs: secs, ..*self })
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<NaiveTime> {
        if sec >= 60 { return None; }
        let secs = self.secs / 60 * 60 + sec;
        Some(NaiveTime { secs: secs, ..*self })
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<NaiveTime> {
        if nano >= 2_000_000_000 { return None; }
        Some(NaiveTime { frac: nano, ..*self })
    }

    #[inline]
    fn num_seconds_from_midnight(&self) -> u32 {
        self.secs // do not repeat the calculation!
    }
}

impl hash::Hash for NaiveTime {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.secs.hash(state);
        self.frac.hash(state);
    }
}

impl Add<Duration> for NaiveTime {
    type Output = NaiveTime;

    fn add(self, rhs: Duration) -> NaiveTime {
        // there is no direct interface in `Duration` to get only the nanosecond part,
        // so we need to do the additional calculation here.
        let mut rhssecs = rhs.num_seconds();
        let mut rhs2 = rhs - Duration::seconds(rhssecs);
        if rhs2 < Duration::zero() { // possible when rhs < 0
            rhssecs -= 1;
            rhs2 = rhs2 + Duration::seconds(1);
        }
        debug_assert!(rhs2 >= Duration::zero());
        let mut secs = self.secs + (rhssecs % 86400 + 86400) as u32;
        let mut nanos = self.frac + rhs2.num_nanoseconds().unwrap() as u32;

        // always ignore leap seconds after the current whole second
        let maxnanos = if self.frac >= 1_000_000_000 {2_000_000_000} else {1_000_000_000};

        if nanos >= maxnanos {
            nanos -= maxnanos;
            secs += 1;
        }
        NaiveTime { secs: secs % 86400, frac: nanos }
    }
}

impl Sub<NaiveTime> for NaiveTime {
    type Output = Duration;

    fn sub(self, rhs: NaiveTime) -> Duration {
        // the number of whole non-leap seconds
        let secs = self.secs as i64 - rhs.secs as i64 - 1;

        // the fractional second from the rhs to the next non-leap second
        let maxnanos = if rhs.frac >= 1_000_000_000 {2_000_000_000} else {1_000_000_000};
        let nanos1 = maxnanos - rhs.frac;

        // the fractional second from the last leap or non-leap second to the lhs
        let lastfrac = if self.frac >= 1_000_000_000 {1_000_000_000} else {0};
        let nanos2 = self.frac - lastfrac;

        Duration::seconds(secs) + Duration::nanoseconds(nanos1 as i64 + nanos2 as i64)
    }
}

impl Sub<Duration> for NaiveTime {
    type Output = NaiveTime;

    #[inline]
    fn sub(self, rhs: Duration) -> NaiveTime { self.add(-rhs) }
}

impl fmt::Debug for NaiveTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (hour, min, sec) = self.hms();
        let (sec, nano) = if self.frac >= 1_000_000_000 {
            (sec + 1, self.frac - 1_000_000_000)
        } else {
            (sec, self.frac)
        };

        try!(write!(f, "{:02}:{:02}:{:02}", hour, min, sec));
        if nano == 0 {
            Ok(())
        } else if nano % 1_000_000 == 0 {
            write!(f, ".{:03}", nano / 1_000_000)
        } else if nano % 1_000 == 0 {
            write!(f, ".{:06}", nano / 1_000)
        } else {
            write!(f, ".{:09}", nano)
        }
    }
}

impl fmt::Display for NaiveTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(self, f) }
}

impl str::FromStr for NaiveTime {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<NaiveTime> {
        const ITEMS: &'static [Item<'static>] = &[
            Item::Space(""), Item::Numeric(Numeric::Hour, Pad::Zero),
            Item::Space(""), Item::Literal(":"),
            Item::Space(""), Item::Numeric(Numeric::Minute, Pad::Zero),
            Item::Space(""), Item::Literal(":"),
            Item::Space(""), Item::Numeric(Numeric::Second, Pad::Zero),
            Item::Fixed(Fixed::Nanosecond), Item::Space(""),
        ];

        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, ITEMS.iter().cloned()));
        parsed.to_naive_time()
    }
}

#[cfg(test)]
mod tests {
    use super::NaiveTime;
    use Timelike;
    use duration::Duration;
    use std::u32;

    #[test]
    fn test_time_from_hms_milli() {
        assert_eq!(NaiveTime::from_hms_milli_opt(3, 5, 7, 0),
                   Some(NaiveTime::from_hms_nano(3, 5, 7, 0)));
        assert_eq!(NaiveTime::from_hms_milli_opt(3, 5, 7, 777),
                   Some(NaiveTime::from_hms_nano(3, 5, 7, 777_000_000)));
        assert_eq!(NaiveTime::from_hms_milli_opt(3, 5, 7, 1_999),
                   Some(NaiveTime::from_hms_nano(3, 5, 7, 1_999_000_000)));
        assert_eq!(NaiveTime::from_hms_milli_opt(3, 5, 7, 2_000), None);
        assert_eq!(NaiveTime::from_hms_milli_opt(3, 5, 7, 5_000), None); // overflow check
        assert_eq!(NaiveTime::from_hms_milli_opt(3, 5, 7, u32::MAX), None);
    }

    #[test]
    fn test_time_from_hms_micro() {
        assert_eq!(NaiveTime::from_hms_micro_opt(3, 5, 7, 0),
                   Some(NaiveTime::from_hms_nano(3, 5, 7, 0)));
        assert_eq!(NaiveTime::from_hms_micro_opt(3, 5, 7, 333),
                   Some(NaiveTime::from_hms_nano(3, 5, 7, 333_000)));
        assert_eq!(NaiveTime::from_hms_micro_opt(3, 5, 7, 777_777),
                   Some(NaiveTime::from_hms_nano(3, 5, 7, 777_777_000)));
        assert_eq!(NaiveTime::from_hms_micro_opt(3, 5, 7, 1_999_999),
                   Some(NaiveTime::from_hms_nano(3, 5, 7, 1_999_999_000)));
        assert_eq!(NaiveTime::from_hms_micro_opt(3, 5, 7, 2_000_000), None);
        assert_eq!(NaiveTime::from_hms_micro_opt(3, 5, 7, 5_000_000), None); // overflow check
        assert_eq!(NaiveTime::from_hms_micro_opt(3, 5, 7, u32::MAX), None);
    }

    #[test]
    fn test_time_hms() {
        assert_eq!(NaiveTime::from_hms(3, 5, 7).hour(), 3);
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_hour(0),
                   Some(NaiveTime::from_hms(0, 5, 7)));
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_hour(23),
                   Some(NaiveTime::from_hms(23, 5, 7)));
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_hour(24), None);
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_hour(u32::MAX), None);

        assert_eq!(NaiveTime::from_hms(3, 5, 7).minute(), 5);
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_minute(0),
                   Some(NaiveTime::from_hms(3, 0, 7)));
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_minute(59),
                   Some(NaiveTime::from_hms(3, 59, 7)));
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_minute(60), None);
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_minute(u32::MAX), None);

        assert_eq!(NaiveTime::from_hms(3, 5, 7).second(), 7);
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_second(0),
                   Some(NaiveTime::from_hms(3, 5, 0)));
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_second(59),
                   Some(NaiveTime::from_hms(3, 5, 59)));
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_second(60), None);
        assert_eq!(NaiveTime::from_hms(3, 5, 7).with_second(u32::MAX), None);
    }

    #[test]
    fn test_time_add() {
        fn check(lhs: NaiveTime, rhs: Duration, sum: NaiveTime) {
            assert_eq!(lhs + rhs, sum);
            //assert_eq!(rhs + lhs, sum);
        }

        let hmsm = |h,m,s,mi| NaiveTime::from_hms_milli(h, m, s, mi);

        check(hmsm(3, 5, 7, 900), Duration::zero(), hmsm(3, 5, 7, 900));
        check(hmsm(3, 5, 7, 900), Duration::milliseconds(100), hmsm(3, 5, 8, 0));
        check(hmsm(3, 5, 7, 1_300), Duration::milliseconds(800), hmsm(3, 5, 8, 100));
        check(hmsm(3, 5, 7, 900), Duration::seconds(86399), hmsm(3, 5, 6, 900)); // overwrap
        check(hmsm(3, 5, 7, 900), Duration::seconds(-86399), hmsm(3, 5, 8, 900));
        check(hmsm(3, 5, 7, 900), Duration::days(12345), hmsm(3, 5, 7, 900));

        // regression tests for #37
        check(hmsm(0, 0, 0, 0), Duration::milliseconds(-990), hmsm(23, 59, 59, 10));
        check(hmsm(0, 0, 0, 0), Duration::milliseconds(-9990), hmsm(23, 59, 50, 10));
    }

    #[test]
    fn test_time_sub() {
        fn check(lhs: NaiveTime, rhs: NaiveTime, diff: Duration) {
            // `time1 - time2 = duration` is equivalent to `time2 - time1 = -duration`
            assert_eq!(lhs - rhs, diff);
            assert_eq!(rhs - lhs, -diff);
        }

        let hmsm = |h,m,s,mi| NaiveTime::from_hms_milli(h, m, s, mi);

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
        assert_eq!(format!("{}", NaiveTime::from_hms_milli(23, 59, 59, 999)), "23:59:59.999");
        assert_eq!(format!("{}", NaiveTime::from_hms_milli(23, 59, 59, 1_000)), "23:59:60");
        assert_eq!(format!("{}", NaiveTime::from_hms_milli(23, 59, 59, 1_001)), "23:59:60.001");
        assert_eq!(format!("{}", NaiveTime::from_hms_micro(0, 0, 0, 43210)), "00:00:00.043210");
        assert_eq!(format!("{}", NaiveTime::from_hms_nano(0, 0, 0, 6543210)), "00:00:00.006543210");

        // the format specifier should have no effect on `NaiveTime`
        assert_eq!(format!("{:30}", NaiveTime::from_hms_milli(3, 5, 7, 9)), "03:05:07.009");
    }

    #[test]
    fn test_date_from_str() {
        // valid cases
        let valid = [
            "0:0:0",
            "0:0:0.0000000",
            "0:0:0.0000003",
            " 4 : 3 : 2.1 ",
            " 09:08:07 ",
            " 9:8:07 ",
            "23:59:60.373929310237",
        ];
        for &s in &valid {
            let d = match s.parse::<NaiveTime>() {
                Ok(d) => d,
                Err(e) => panic!("parsing `{}` has failed: {}", s, e)
            };
            let s_ = format!("{:?}", d);
            // `s` and `s_` may differ, but `s.parse()` and `s_.parse()` must be same
            let d_ = match s_.parse::<NaiveTime>() {
                Ok(d) => d,
                Err(e) => panic!("`{}` is parsed into `{:?}`, but reparsing that has failed: {}",
                                 s, d, e)
            };
            assert!(d == d_, "`{}` is parsed into `{:?}`, but reparsed result \
                              `{:?}` does not match", s, d, d_);
        }

        // some invalid cases
        // since `ParseErrorKind` is private, all we can do is to check if there was an error
        assert!("".parse::<NaiveTime>().is_err());
        assert!("x".parse::<NaiveTime>().is_err());
        assert!("15".parse::<NaiveTime>().is_err());
        assert!("15:8".parse::<NaiveTime>().is_err());
        assert!("15:8:x".parse::<NaiveTime>().is_err());
        assert!("15:8:9x".parse::<NaiveTime>().is_err());
        assert!("23:59:61".parse::<NaiveTime>().is_err());
        assert!("12:34:56.x".parse::<NaiveTime>().is_err());
        assert!("12:34:56. 0".parse::<NaiveTime>().is_err());
    }

    #[test]
    fn test_time_parse_from_str() {
        let hms = |h,m,s| NaiveTime::from_hms(h,m,s);
        assert_eq!(NaiveTime::parse_from_str("2014-5-7T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
                   Ok(hms(12, 34, 56))); // ignore date and offset
        assert_eq!(NaiveTime::parse_from_str("PM 12:59", "%P %H:%M"),
                   Ok(hms(12, 59, 0)));
        assert!(NaiveTime::parse_from_str("12:3456", "%H:%M:%S").is_err());
    }

    #[test]
    fn test_time_format() {
        let t = NaiveTime::from_hms_nano(3, 5, 7, 98765432);
        assert_eq!(t.format("%H,%k,%I,%l,%P,%p").to_string(), "03, 3,03, 3,am,AM");
        assert_eq!(t.format("%M").to_string(), "05");
        assert_eq!(t.format("%S,%f").to_string(), "07,098765432");
        assert_eq!(t.format("%R").to_string(), "03:05");
        assert_eq!(t.format("%T,%X").to_string(), "03:05:07,03:05:07");
        assert_eq!(t.format("%r").to_string(), "03:05:07 AM");
        assert_eq!(t.format("%t%n%%%n%t").to_string(), "\t\n%\n\t");

        // corner cases
        assert_eq!(NaiveTime::from_hms(13, 57, 9).format("%r").to_string(), "01:57:09 PM");
        assert_eq!(NaiveTime::from_hms_milli(23, 59, 59, 1_000).format("%X").to_string(),
                   "23:59:60");
    }
}

