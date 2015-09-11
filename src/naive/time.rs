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
///
/// # Leap second WHAT?
///
/// Since 1960s, the manmade atomic clock has been so accurate that
/// it is much more accurate than Earth's own motion.
/// It became desirable to define the civil time in terms of the atomic clock,
/// but that risks the desynchronization of the civil time from Earth.
/// To account for this, the designers of the Coordinated Universal Time (UTC)
/// made that the UTC should be kept within 0.9 seconds of the observed Earth-bound time.
/// When the mean solar day is longer than the ideal (86,400 seconds),
/// the error slowly accumulates and it is necessary to add a **leap second**
/// to slow the UTC down a bit.
/// (We may also remove a second to speed the UTC up a bit, but it never happened.)
/// The leap second, if any, follows 23:59:59 of June 30 or December 31 in the UTC.
///
/// Fast forward to the 21st century,
/// we have seen 26 leap seconds from January 1972 to December 2015.
/// Yes, 26 seconds. Probably you can read this paragraph within 26 seconds.
/// But those 26 seconds, and possibly more in the future, are never predictable,
/// and whether to add a leap second or not is known only before 6 months.
/// Internet-based clocks (via NTP) do account for known leap seconds,
/// but the system API normally doesn't (and often can't, with no network connection)
/// and there is no reliable way to retrieve leap second information.
///
/// Chrono does not try to accurately implement leap seconds; it is impossible.
/// Rather, **it allows for leap seconds but behaves as if there are *no other* leap seconds.**
/// Various time arithmetics will ignore any possible leap second(s)
/// except when the operand were actually a leap second.
/// The leap second is indicated via fractional seconds more than 1 second,
/// so values like `NaiveTime::from_hms_milli(23, 56, 4, 1_005)` are allowed;
/// that value would mean 5ms after the beginning of a leap second following 23:56:04.
/// Parsing and formatting will correctly handle times that look like leap seconds,
/// and you can then conveniently ignore leap seconds if you are not prepared for them.
///
/// If you cannot tolerate this behavior,
/// you must use a separate `TimeZone` for the International Atomic Time (TAI).
/// TAI is like UTC but has no leap seconds, and thus slightly differs from UTC.
/// Chrono 0.2 does not provide such implementation, but it is planned for 0.3.
#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
#[cfg_attr(feature = "rustc-serialize", derive(RustcEncodable, RustcDecodable))]
pub struct NaiveTime {
    secs: u32,
    frac: u32,
}

impl NaiveTime {
    /// Makes a new `NaiveTime` from hour, minute and second.
    ///
    /// No [leap second](#leap-second-what?) is allowed here;
    /// use `NaiveTime::from_hms_*` methods with a subsecond parameter instead.
    ///
    /// Panics on invalid hour, minute and/or second.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_hms(23, 56, 4);
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 0);
    /// ~~~~
    #[inline]
    pub fn from_hms(hour: u32, min: u32, sec: u32) -> NaiveTime {
        NaiveTime::from_hms_opt(hour, min, sec).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from hour, minute and second.
    ///
    /// No [leap second](#leap-second-what?) is allowed here;
    /// use `NaiveTime::from_hms_*_opt` methods with a subsecond parameter instead.
    ///
    /// Returns `None` on invalid hour, minute and/or second.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::NaiveTime;
    ///
    /// let hms = |h,m,s| NaiveTime::from_hms_opt(h, m, s);
    /// assert!(hms(0, 0, 0).is_some());
    /// assert!(hms(23, 59, 59).is_some());
    /// assert!(hms(24, 0, 0).is_none());
    /// assert!(hms(23, 60, 0).is_none());
    /// assert!(hms(23, 59, 60).is_none());
    /// ~~~~
    #[inline]
    pub fn from_hms_opt(hour: u32, min: u32, sec: u32) -> Option<NaiveTime> {
        NaiveTime::from_hms_nano_opt(hour, min, sec, 0)
    }

    /// Makes a new `NaiveTime` from hour, minute, second and millisecond.
    ///
    /// The millisecond part can exceed 1,000
    /// in order to represent the [leap second](#leap-second-what?).
    ///
    /// Panics on invalid hour, minute, second and/or millisecond.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_hms_milli(23, 56, 4, 12);
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 12_000_000);
    /// ~~~~
    #[inline]
    pub fn from_hms_milli(hour: u32, min: u32, sec: u32, milli: u32) -> NaiveTime {
        NaiveTime::from_hms_milli_opt(hour, min, sec, milli).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from hour, minute, second and millisecond.
    ///
    /// The millisecond part can exceed 1,000
    /// in order to represent the [leap second](#leap-second-what?).
    ///
    /// Returns `None` on invalid hour, minute, second and/or millisecond.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::NaiveTime;
    ///
    /// let hmsm = |h,m,s,milli| NaiveTime::from_hms_milli_opt(h, m, s, milli);
    /// assert!(hmsm(0, 0, 0, 0).is_some());
    /// assert!(hmsm(23, 59, 59, 999).is_some());
    /// assert!(hmsm(23, 59, 59, 1_999).is_some()); // a leap second following 23:59:59
    /// assert!(hmsm(24, 0, 0, 0).is_none());
    /// assert!(hmsm(23, 60, 0, 0).is_none());
    /// assert!(hmsm(23, 59, 60, 0).is_none());
    /// assert!(hmsm(23, 59, 59, 2_000).is_none());
    /// ~~~~
    #[inline]
    pub fn from_hms_milli_opt(hour: u32, min: u32, sec: u32, milli: u32) -> Option<NaiveTime> {
        milli.checked_mul(1_000_000)
             .and_then(|nano| NaiveTime::from_hms_nano_opt(hour, min, sec, nano))
    }

    /// Makes a new `NaiveTime` from hour, minute, second and microsecond.
    ///
    /// The microsecond part can exceed 1,000,000
    /// in order to represent the [leap second](#leap-second-what?).
    ///
    /// Panics on invalid hour, minute, second and/or microsecond.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_hms_micro(23, 56, 4, 12_345);
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 12_345_000);
    /// ~~~~
    #[inline]
    pub fn from_hms_micro(hour: u32, min: u32, sec: u32, micro: u32) -> NaiveTime {
        NaiveTime::from_hms_micro_opt(hour, min, sec, micro).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from hour, minute, second and microsecond.
    ///
    /// The microsecond part can exceed 1,000,000
    /// in order to represent the [leap second](#leap-second-what?).
    ///
    /// Returns `None` on invalid hour, minute, second and/or microsecond.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::NaiveTime;
    ///
    /// let hmsu = |h,m,s,micro| NaiveTime::from_hms_micro_opt(h, m, s, micro);
    /// assert!(hmsu(0, 0, 0, 0).is_some());
    /// assert!(hmsu(23, 59, 59, 999_999).is_some());
    /// assert!(hmsu(23, 59, 59, 1_999_999).is_some()); // a leap second following 23:59:59
    /// assert!(hmsu(24, 0, 0, 0).is_none());
    /// assert!(hmsu(23, 60, 0, 0).is_none());
    /// assert!(hmsu(23, 59, 60, 0).is_none());
    /// assert!(hmsu(23, 59, 59, 2_000_000).is_none());
    /// ~~~~
    #[inline]
    pub fn from_hms_micro_opt(hour: u32, min: u32, sec: u32, micro: u32) -> Option<NaiveTime> {
        micro.checked_mul(1_000)
             .and_then(|nano| NaiveTime::from_hms_nano_opt(hour, min, sec, nano))
    }

    /// Makes a new `NaiveTime` from hour, minute, second and nanosecond.
    ///
    /// The nanosecond part can exceed 1,000,000,000
    /// in order to represent the [leap second](#leap-second-what?).
    ///
    /// Panics on invalid hour, minute, second and/or nanosecond.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678);
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 12_345_678);
    /// ~~~~
    #[inline]
    pub fn from_hms_nano(hour: u32, min: u32, sec: u32, nano: u32) -> NaiveTime {
        NaiveTime::from_hms_nano_opt(hour, min, sec, nano).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from hour, minute, second and nanosecond.
    ///
    /// The nanosecond part can exceed 1,000,000,000
    /// in order to represent the [leap second](#leap-second-what?).
    ///
    /// Returns `None` on invalid hour, minute, second and/or nanosecond.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::NaiveTime;
    ///
    /// let hmsn = |h,m,s,nano| NaiveTime::from_hms_nano_opt(h, m, s, nano);
    /// assert!(hmsn(0, 0, 0, 0).is_some());
    /// assert!(hmsn(23, 59, 59, 999_999_999).is_some());
    /// assert!(hmsn(23, 59, 59, 1_999_999_999).is_some()); // a leap second following 23:59:59
    /// assert!(hmsn(24, 0, 0, 0).is_none());
    /// assert!(hmsn(23, 60, 0, 0).is_none());
    /// assert!(hmsn(23, 59, 60, 0).is_none());
    /// assert!(hmsn(23, 59, 59, 2_000_000_000).is_none());
    /// ~~~~
    #[inline]
    pub fn from_hms_nano_opt(hour: u32, min: u32, sec: u32, nano: u32) -> Option<NaiveTime> {
        if hour >= 24 || min >= 60 || sec >= 60 || nano >= 2_000_000_000 { return None; }
        let secs = hour * 3600 + min * 60 + sec;
        Some(NaiveTime { secs: secs, frac: nano })
    }

    /// Makes a new `NaiveTime` from the number of seconds since midnight and nanosecond.
    ///
    /// The nanosecond part can exceed 1,000,000,000
    /// in order to represent the [leap second](#leap-second-what?).
    ///
    /// Panics on invalid number of seconds and/or nanosecond.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_num_seconds_from_midnight(86164, 12_345_678);
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 12_345_678);
    /// ~~~~
    #[inline]
    pub fn from_num_seconds_from_midnight(secs: u32, nano: u32) -> NaiveTime {
        NaiveTime::from_num_seconds_from_midnight_opt(secs, nano).expect("invalid time")
    }

    /// Makes a new `NaiveTime` from the number of seconds since midnight and nanosecond.
    ///
    /// The nanosecond part can exceed 1,000,000,000
    /// in order to represent the [leap second](#leap-second-what?).
    ///
    /// Returns `None` on invalid number of seconds and/or nanosecond.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::NaiveTime;
    ///
    /// let secs = |secs,nano| NaiveTime::from_num_seconds_from_midnight_opt(secs, nano);
    /// assert!(secs(0, 0).is_some());
    /// assert!(secs(86399, 999_999_999).is_some());
    /// assert!(secs(86399, 1_999_999_999).is_some()); // a leap second following 23:59:59
    /// assert!(secs(86400, 0).is_none());
    /// assert!(secs(86399, 2_000_000_000).is_none());
    /// ~~~~
    #[inline]
    pub fn from_num_seconds_from_midnight_opt(secs: u32, nano: u32) -> Option<NaiveTime> {
        if secs >= 86400 || nano >= 2_000_000_000 { return None; }
        Some(NaiveTime { secs: secs, frac: nano })
    }

    /// Parses a string with the specified format string and returns a new `NaiveTime`.
    /// See the [`format::strftime` module](../../format/strftime/index.html)
    /// on the supported escape sequences.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::NaiveTime;
    ///
    /// assert_eq!(NaiveTime::parse_from_str("23:56:04", "%H:%M:%S"),
    ///            Ok(NaiveTime::from_hms(23, 56, 4)));
    /// assert_eq!(NaiveTime::parse_from_str("pm012345.6789", "%p%I%M%S%.f"),
    ///            Ok(NaiveTime::from_hms_micro(13, 23, 45, 678_900)));
    /// ~~~~
    ///
    /// Date and offset is ignored for the purpose of parsing.
    ///
    /// ~~~~
    /// # use chrono::NaiveTime;
    /// assert_eq!(NaiveTime::parse_from_str("2014-5-17T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
    ///            Ok(NaiveTime::from_hms(12, 34, 56)));
    /// ~~~~
    ///
    /// [Leap seconds](#leap-second-what?) are correctly handled by
    /// treating any time of the form `hh:mm:60` as a leap second.
    /// (This equally applies to the formatting, so the round trip is possible.)
    ///
    /// ~~~~
    /// # use chrono::NaiveTime;
    /// assert_eq!(NaiveTime::parse_from_str("08:59:60.123", "%H:%M:%S%.f"),
    ///            Ok(NaiveTime::from_hms_milli(8, 59, 59, 1_123)));
    /// ~~~~
    ///
    /// Missing seconds are assumed to be zero,
    /// but out-of-bound times or insufficient fields are errors otherwise.
    ///
    /// ~~~~
    /// # use chrono::NaiveTime;
    /// assert_eq!(NaiveTime::parse_from_str("7:15", "%H:%M"),
    ///            Ok(NaiveTime::from_hms(7, 15, 0)));
    ///
    /// assert!(NaiveTime::parse_from_str("04m33s", "%Mm%Ss").is_err());
    /// assert!(NaiveTime::parse_from_str("12", "%H").is_err());
    /// assert!(NaiveTime::parse_from_str("17:60", "%H:%M").is_err());
    /// assert!(NaiveTime::parse_from_str("24:00:00", "%H:%M:%S").is_err());
    /// ~~~~
    ///
    /// All parsed fields should be consistent to each other, otherwise it's an error.
    /// Here `%H` is for 24-hour clocks, unlike `%I`,
    /// and thus can be independently determined without AM/PM.
    ///
    /// ~~~~
    /// # use chrono::NaiveTime;
    /// assert!(NaiveTime::parse_from_str("13:07 AM", "%H:%M %p").is_err());
    /// ~~~~
    pub fn parse_from_str(s: &str, fmt: &str) -> ParseResult<NaiveTime> {
        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, StrftimeItems::new(fmt)));
        parsed.to_naive_time()
    }

    /// Formats the time with the specified formatting items.
    /// Otherwise it is same to the ordinary `format` method.
    ///
    /// The `Iterator` of items should be `Clone`able,
    /// since the resulting `DelayedFormat` value may be formatted multiple times.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::NaiveTime;
    /// use chrono::format::strftime::StrftimeItems;
    ///
    /// let fmt = StrftimeItems::new("%H:%M:%S");
    /// let t = NaiveTime::from_hms(23, 56, 4);
    /// assert_eq!(t.format_with_items(fmt.clone()).to_string(), "23:56:04");
    /// assert_eq!(t.format("%H:%M:%S").to_string(), "23:56:04");
    /// ~~~~
    #[inline]
    pub fn format_with_items<'a, I>(&self, items: I) -> DelayedFormat<I>
            where I: Iterator<Item=Item<'a>> + Clone {
        DelayedFormat::new(None, Some(self.clone()), items)
    }

    /// Formats the time with the specified format string.
    /// See the [`format::strftime` module](../../format/strftime/index.html)
    /// on the supported escape sequences.
    ///
    /// This returns a `DelayedFormat`,
    /// which gets converted to a string only when actual formatting happens.
    /// You may use the `to_string` method to get a `String`,
    /// or just feed it into `print!` and other formatting macros.
    /// (In this way it avoids the redundant memory allocation.)
    ///
    /// A wrong format string does *not* issue an error immediately.
    /// Rather, converting or formatting the `DelayedFormat` fails.
    /// You are recommended to immediately use `DelayedFormat` for this reason.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::NaiveTime;
    ///
    /// let t = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678);
    /// assert_eq!(t.format("%H:%M:%S").to_string(), "23:56:04");
    /// assert_eq!(t.format("%H:%M:%S%.6f").to_string(), "23:56:04.012345");
    /// assert_eq!(t.format("%-I:%M %p").to_string(), "11:56 PM");
    /// ~~~~
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

