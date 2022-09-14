// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! ISO 8601 time without timezone.

#[cfg(any(feature = "alloc", feature = "std", test))]
use core::borrow::Borrow;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use core::{fmt, str};

use num_integer::div_mod_floor;
#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use crate::error::ErrorKind;
#[cfg(any(feature = "alloc", feature = "std", test))]
use crate::format::DelayedFormat;
use crate::format::{parse, ParseError, ParseResult, Parsed, StrftimeItems};
use crate::format::{Fixed, Item, Numeric, Pad};
use crate::{Error, TimeDelta, Timelike};

#[cfg(feature = "serde")]
mod serde;

#[cfg(test)]
mod tests;

/// ISO 8601 time without timezone.
/// Allows for the nanosecond precision and optional leap second representation.
///
/// # Leap Second Handling
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
/// Various operations will ignore any possible leap second(s)
/// except when any of the operands were actually leap seconds.
///
/// If you cannot tolerate this behavior,
/// you must use a separate `TimeZone` for the International Atomic Time (TAI).
/// TAI is like UTC but has no leap seconds, and thus slightly differs from UTC.
/// Chrono does not yet provide such implementation, but it is planned.
///
/// ## Representing Leap Seconds
///
/// The leap second is indicated via fractional seconds more than 1 second.
/// This makes possible to treat a leap second as the prior non-leap second
/// if you don't care about sub-second accuracy.
/// You should use the proper formatting to get the raw leap second.
///
/// All methods accepting fractional seconds will accept such values.
///
/// ```
/// use chrono::{NaiveDate, NaiveTime, Utc, TimeZone};
///
/// let t = NaiveTime::from_hms_milli(8, 59, 59, 1_000);
///
/// let dt1 = NaiveDate::from_ymd(2015, 7, 1)?.and_hms_micro(8, 59, 59, 1_000_000)?;
///
/// let dt2 = Utc.ymd(2015, 6, 30)?.and_hms_nano(23, 59, 59, 1_000_000_000)?;
/// # let _ = (t, dt1, dt2);
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Note that the leap second can happen anytime given an appropriate time zone;
/// 2015-07-01 01:23:60 would be a proper leap second if UTC+01:24 had existed.
/// Practically speaking, though, by the time of the first leap second on 1972-06-30,
/// every time zone offset around the world has standardized to the 5-minute alignment.
///
/// ## Date And Time Arithmetics
///
/// As a concrete example, let's assume that `03:00:60` and `04:00:60` are leap seconds.
/// In reality, of course, leap seconds are separated by at least 6 months.
/// We will also use some intuitive concise notations for the explanation.
///
/// `Time + TimeDelta`
/// (short for [`NaiveTime::overflowing_add_signed`](#method.overflowing_add_signed)):
///
/// - `03:00:00 + 1s = 03:00:01`.
/// - `03:00:59 + 60s = 03:02:00`.
/// - `03:00:59 + 1s = 03:01:00`.
/// - `03:00:60 + 1s = 03:01:00`.
///   Note that the sum is identical to the previous.
/// - `03:00:60 + 60s = 03:01:59`.
/// - `03:00:60 + 61s = 03:02:00`.
/// - `03:00:60.1 + 0.8s = 03:00:60.9`.
///
/// `Time - TimeDelta`
/// (short for [`NaiveTime::overflowing_sub_signed`](#method.overflowing_sub_signed)):
///
/// - `03:00:00 - 1s = 02:59:59`.
/// - `03:01:00 - 1s = 03:00:59`.
/// - `03:01:00 - 60s = 03:00:00`.
/// - `03:00:60 - 60s = 03:00:00`.
///   Note that the result is identical to the previous.
/// - `03:00:60.7 - 0.4s = 03:00:60.3`.
/// - `03:00:60.7 - 0.9s = 03:00:59.8`.
///
/// `Time - Time`
/// (short for [`NaiveTime::signed_duration_since`](#method.signed_duration_since)):
///
/// - `04:00:00 - 03:00:00 = 3600s`.
/// - `03:01:00 - 03:00:00 = 60s`.
/// - `03:00:60 - 03:00:00 = 60s`.
///   Note that the difference is identical to the previous.
/// - `03:00:60.6 - 03:00:59.4 = 1.2s`.
/// - `03:01:00 - 03:00:59.8 = 0.2s`.
/// - `03:01:00 - 03:00:60.5 = 0.5s`.
///   Note that the difference is larger than the previous,
///   even though the leap second clearly follows the previous whole second.
/// - `04:00:60.9 - 03:00:60.1 =
///   (04:00:60.9 - 04:00:00) + (04:00:00 - 03:01:00) + (03:01:00 - 03:00:60.1) =
///   60.9s + 3540s + 0.9s = 3601.8s`.
///
/// In general,
///
/// - `Time + TimeDelta` unconditionally equals to `TimeDelta + Time`.
///
/// - `Time - TimeDelta` unconditionally equals to `Time + (-TimeDelta)`.
///
/// - `Time1 - Time2` unconditionally equals to `-(Time2 - Time1)`.
///
/// - Associativity does not generally hold, because
///   `(Time + TimeDelta1) - TimeDelta2` no longer equals to `Time + (TimeDelta1 - TimeDelta2)`
///   for two positive durations.
///
///     - As a special case, `(Time + TimeDelta) - TimeDelta` also does not equal to `Time`.
///
///     - If you can assume that all durations have the same sign, however,
///       then the associativity holds:
///       `(Time + TimeDelta1) + TimeDelta2` equals to `Time + (TimeDelta1 + TimeDelta2)`
///       for two positive durations.
///
/// ## Reading And Writing Leap Seconds
///
/// The "typical" leap seconds on the minute boundary are
/// correctly handled both in the formatting and parsing.
/// The leap second in the human-readable representation
/// will be represented as the second part being 60, as required by ISO 8601.
///
/// ```
/// use chrono::{Utc, TimeZone};
///
/// let dt = Utc.ymd(2015, 6, 30)?.and_hms_milli(23, 59, 59, 1_000)?;
/// assert_eq!(format!("{:?}", dt), "2015-06-30T23:59:60Z");
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// There are hypothetical leap seconds not on the minute boundary
/// nevertheless supported by Chrono.
/// They are allowed for the sake of completeness and consistency;
/// there were several "exotic" time zone offsets with fractional minutes prior to UTC after all.
/// For such cases the human-readable representation is ambiguous
/// and would be read back to the next non-leap second.
///
/// ```
/// use chrono::{DateTime, Utc, TimeZone};
///
/// let dt = Utc.ymd(2015, 6, 30)?.and_hms_milli(23, 56, 4, 1_000)?;
/// assert_eq!(format!("{:?}", dt), "2015-06-30T23:56:05Z");
///
/// let dt = Utc.ymd(2015, 6, 30)?.and_hms(23, 56, 5)?;
/// assert_eq!(format!("{:?}", dt), "2015-06-30T23:56:05Z");
/// assert_eq!(DateTime::<Utc>::parse_from_rfc3339("2015-06-30T23:56:05Z")?, dt);
/// # Ok::<_, Box<dyn std::error::Error>>(())
/// ```
///
/// Since Chrono alone cannot determine any existence of leap seconds,
/// **there is absolutely no guarantee that the leap second read has actually happened**.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct NaiveTime {
    secs: u32,
    frac: u32,
}

impl NaiveTime {
    /// A constant naive time which corresponds to midnight.
    pub(crate) const MIDNIGHT: NaiveTime = NaiveTime { secs: 0, frac: 0 };

    /// Makes a new `NaiveTime` from hour, minute and second.
    ///
    /// No [leap second](#leap-second-handling) is allowed here; use
    /// `NaiveTime::from_hms_*` methods with a subsecond parameter instead.
    ///
    /// Returns `Err(Error)` on invalid hour, minute and/or second.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_hms(23, 56, 4)?;
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 0);
    ///
    /// let from_hms = NaiveTime::from_hms;
    ///
    /// assert!(from_hms(0, 0, 0).is_ok());
    /// assert!(from_hms(23, 59, 59).is_ok());
    /// assert!(from_hms(24, 0, 0).is_err());
    /// assert!(from_hms(23, 60, 0).is_err());
    /// assert!(from_hms(23, 59, 60).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn from_hms(hour: u32, min: u32, sec: u32) -> Result<NaiveTime, Error> {
        NaiveTime::from_hms_nano(hour, min, sec, 0)
    }

    /// Makes a new `NaiveTime` which is set to midnight at `00:00`.
    pub(crate) fn midnight() -> NaiveTime {
        NaiveTime::MIDNIGHT
    }

    /// Makes a new `NaiveTime` from hour, minute, second and millisecond.
    ///
    /// The millisecond part can exceed 1,000
    /// in order to represent the [leap second](#leap-second-handling).
    ///
    /// Returns `Err(Error)` on invalid hour, minute, second and/or millisecond.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_hms_milli(23, 56, 4, 12)?;
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 12_000_000);
    ///
    /// let from_hms_milli = NaiveTime::from_hms_milli;
    ///
    /// assert!(from_hms_milli(0, 0, 0, 0).is_ok());
    /// assert!(from_hms_milli(23, 59, 59, 999).is_ok());
    /// assert!(from_hms_milli(23, 59, 59, 1_999).is_ok()); // a leap second after 23:59:59
    /// assert!(from_hms_milli(24, 0, 0, 0).is_err());
    /// assert!(from_hms_milli(23, 60, 0, 0).is_err());
    /// assert!(from_hms_milli(23, 59, 60, 0).is_err());
    /// assert!(from_hms_milli(23, 59, 59, 2_000).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn from_hms_milli(hour: u32, min: u32, sec: u32, milli: u32) -> Result<NaiveTime, Error> {
        let nano = milli.checked_mul(1_000_000).ok_or(ErrorKind::InvalidTime)?;
        NaiveTime::from_hms_nano(hour, min, sec, nano)
    }

    /// Makes a new `NaiveTime` from hour, minute, second and microsecond.
    ///
    /// The microsecond part can exceed 1,000,000 in order to represent the
    /// [leap second](#leap-second-handling).
    ///
    /// Returns `Err(Error)` on invalid hour, minute, second and/or
    /// microsecond.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_hms_micro(23, 56, 4, 12_345)?;
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 12_345_000);
    ///
    /// let from_hms_micro = NaiveTime::from_hms_micro;
    ///
    /// assert!(from_hms_micro(0, 0, 0, 0).is_ok());
    /// assert!(from_hms_micro(23, 59, 59, 999_999).is_ok());
    /// assert!(from_hms_micro(23, 59, 59, 1_999_999).is_ok()); // a leap second after 23:59:59
    /// assert!(from_hms_micro(24, 0, 0, 0).is_err());
    /// assert!(from_hms_micro(23, 60, 0, 0).is_err());
    /// assert!(from_hms_micro(23, 59, 60, 0).is_err());
    /// assert!(from_hms_micro(23, 59, 59, 2_000_000).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn from_hms_micro(hour: u32, min: u32, sec: u32, micro: u32) -> Result<NaiveTime, Error> {
        let nano = micro.checked_mul(1_000).ok_or(ErrorKind::InvalidTime)?;
        NaiveTime::from_hms_nano(hour, min, sec, nano)
    }

    /// Makes a new `NaiveTime` from hour, minute, second and nanosecond.
    ///
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the
    /// [leap second](#leap-second-handling).
    ///
    /// Returns `Err(Error)` on invalid hour, minute, second and/or
    /// nanosecond.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?;
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 12_345_678);
    ///
    /// let from_hms_nano = NaiveTime::from_hms_nano;
    ///
    /// assert!(from_hms_nano(0, 0, 0, 0).is_ok());
    /// assert!(from_hms_nano(23, 59, 59, 999_999_999).is_ok());
    /// assert!(from_hms_nano(23, 59, 59, 1_999_999_999).is_ok()); // a leap second after 23:59:59
    /// assert!(from_hms_nano(24, 0, 0, 0).is_err());
    /// assert!(from_hms_nano(23, 60, 0, 0).is_err());
    /// assert!(from_hms_nano(23, 59, 60, 0).is_err());
    /// assert!(from_hms_nano(23, 59, 59, 2_000_000_000).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn from_hms_nano(hour: u32, min: u32, sec: u32, nano: u32) -> Result<NaiveTime, Error> {
        if hour >= 24 || min >= 60 || sec >= 60 || nano >= 2_000_000_000 {
            return Err(Error::new(ErrorKind::InvalidTime));
        }
        let secs = hour * 3600 + min * 60 + sec;
        Ok(NaiveTime { secs, frac: nano })
    }

    /// Makes a new `NaiveTime` from the number of seconds since midnight and
    /// nanosecond.
    ///
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the
    /// [leap second](#leap-second-handling).
    ///
    /// Returns `Err(Error)` on invalid number of seconds and/or
    /// nanosecond.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let t = NaiveTime::from_num_seconds_from_midnight(86164, 12_345_678)?;
    /// assert_eq!(t.hour(), 23);
    /// assert_eq!(t.minute(), 56);
    /// assert_eq!(t.second(), 4);
    /// assert_eq!(t.nanosecond(), 12_345_678);
    ///
    /// let from_num_seconds_from_midnight = NaiveTime::from_num_seconds_from_midnight;
    ///
    /// assert!(from_num_seconds_from_midnight(0, 0).is_ok());
    /// assert!(from_num_seconds_from_midnight(86399, 999_999_999).is_ok());
    /// assert!(from_num_seconds_from_midnight(86399, 1_999_999_999).is_ok()); // a leap second after 23:59:59
    /// assert!(from_num_seconds_from_midnight(86_400, 0).is_err());
    /// assert!(from_num_seconds_from_midnight(86399, 2_000_000_000).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn from_num_seconds_from_midnight(secs: u32, nano: u32) -> Result<NaiveTime, Error> {
        if secs >= 86_400 || nano >= 2_000_000_000 {
            return Err(Error::new(ErrorKind::InvalidTime));
        }
        Ok(NaiveTime { secs, frac: nano })
    }

    /// Parses a string with the specified format string and returns a new `NaiveTime`.
    /// See the [`format::strftime` module](../format/strftime/index.html)
    /// on the supported escape sequences.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveTime;
    ///
    /// let parse_from_str = NaiveTime::parse_from_str;
    ///
    /// assert_eq!(parse_from_str("23:56:04", "%H:%M:%S")?,
    ///            NaiveTime::from_hms(23, 56, 4)?);
    /// assert_eq!(parse_from_str("pm012345.6789", "%p%I%M%S%.f")?,
    ///            NaiveTime::from_hms_micro(13, 23, 45, 678_900)?);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Date and offset is ignored for the purpose of parsing.
    ///
    /// ```
    /// # use chrono::NaiveTime;
    /// # let parse_from_str = NaiveTime::parse_from_str;
    /// assert_eq!(parse_from_str("2014-5-17T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z")?,
    ///            NaiveTime::from_hms(12, 34, 56)?);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// [Leap seconds](#leap-second-handling) are correctly handled by
    /// treating any time of the form `hh:mm:60` as a leap second.
    /// (This equally applies to the formatting, so the round trip is possible.)
    ///
    /// ```
    /// # use chrono::NaiveTime;
    /// # let parse_from_str = NaiveTime::parse_from_str;
    /// assert_eq!(parse_from_str("08:59:60.123", "%H:%M:%S%.f")?,
    ///            NaiveTime::from_hms_milli(8, 59, 59, 1_123)?);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Missing seconds are assumed to be zero,
    /// but out-of-bound times or insufficient fields are errors otherwise.
    ///
    /// ```
    /// # use chrono::NaiveTime;
    /// # let parse_from_str = NaiveTime::parse_from_str;
    /// assert_eq!(parse_from_str("7:15", "%H:%M")?,
    ///            NaiveTime::from_hms(7, 15, 0)?);
    ///
    /// assert!(parse_from_str("04m33s", "%Mm%Ss").is_err());
    /// assert!(parse_from_str("12", "%H").is_err());
    /// assert!(parse_from_str("17:60", "%H:%M").is_err());
    /// assert!(parse_from_str("24:00:00", "%H:%M:%S").is_err());
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// All parsed fields should be consistent to each other, otherwise it's an error.
    /// Here `%H` is for 24-hour clocks, unlike `%I`,
    /// and thus can be independently determined without AM/PM.
    ///
    /// ```
    /// # use chrono::NaiveTime;
    /// # let parse_from_str = NaiveTime::parse_from_str;
    /// assert!(parse_from_str("13:07 AM", "%H:%M %p").is_err());
    /// ```
    pub fn parse_from_str(s: &str, fmt: &str) -> ParseResult<NaiveTime> {
        let mut parsed = Parsed::new();
        parse(&mut parsed, s, StrftimeItems::new(fmt))?;
        parsed.to_naive_time()
    }

    /// Adds given `TimeDelta` to the current time,
    /// and also returns the number of *seconds*
    /// in the integral number of days ignored from the addition.
    /// (We cannot return `TimeDelta` because it is subject to overflow or underflow.)
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeDelta, NaiveTime};
    ///
    /// let from_hms = NaiveTime::from_hms;
    ///
    /// assert_eq!(from_hms(3, 4, 5)?.overflowing_add_signed(TimeDelta::hours(11)),
    ///            (from_hms(14, 4, 5)?, 0));
    /// assert_eq!(from_hms(3, 4, 5)?.overflowing_add_signed(TimeDelta::hours(23)),
    ///            (from_hms(2, 4, 5)?, 86_400));
    /// assert_eq!(from_hms(3, 4, 5)?.overflowing_add_signed(TimeDelta::hours(-7)),
    ///            (from_hms(20, 4, 5)?, -86_400));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    pub fn overflowing_add_signed(&self, mut rhs: TimeDelta) -> (NaiveTime, i64) {
        let mut secs = self.secs;
        let mut frac = self.frac;

        // check if `self` is a leap second and adding `rhs` would escape that leap second.
        // if it's the case, update `self` and `rhs` to involve no leap second;
        // otherwise the addition immediately finishes.
        if frac >= 1_000_000_000 {
            let rfrac = 2_000_000_000 - frac;
            if rhs >= TimeDelta::nanoseconds(i64::from(rfrac)) {
                rhs = rhs - TimeDelta::nanoseconds(i64::from(rfrac));
                secs += 1;
                frac = 0;
            } else if rhs < TimeDelta::nanoseconds(-i64::from(frac)) {
                rhs = rhs + TimeDelta::nanoseconds(i64::from(frac));
                frac = 0;
            } else {
                frac = (i64::from(frac) + rhs.num_nanoseconds().unwrap()) as u32;
                debug_assert!(frac < 2_000_000_000);
                return (NaiveTime { secs, frac }, 0);
            }
        }
        debug_assert!(secs <= 86_400);
        debug_assert!(frac < 1_000_000_000);

        let rhssecs = rhs.num_seconds();
        let rhsfrac = (rhs - TimeDelta::seconds(rhssecs)).num_nanoseconds().unwrap();
        debug_assert_eq!(TimeDelta::seconds(rhssecs) + TimeDelta::nanoseconds(rhsfrac), rhs);
        let rhssecsinday = rhssecs % 86_400;
        let mut morerhssecs = rhssecs - rhssecsinday;
        let rhssecs = rhssecsinday as i32;
        let rhsfrac = rhsfrac as i32;
        debug_assert!(-86_400 < rhssecs && rhssecs < 86_400);
        debug_assert_eq!(morerhssecs % 86_400, 0);
        debug_assert!(-1_000_000_000 < rhsfrac && rhsfrac < 1_000_000_000);

        let mut secs = secs as i32 + rhssecs;
        let mut frac = frac as i32 + rhsfrac;
        debug_assert!(-86_400 < secs && secs < 2 * 86_400);
        debug_assert!(-1_000_000_000 < frac && frac < 2_000_000_000);

        if frac < 0 {
            frac += 1_000_000_000;
            secs -= 1;
        } else if frac >= 1_000_000_000 {
            frac -= 1_000_000_000;
            secs += 1;
        }
        debug_assert!((-86_400..2 * 86_400).contains(&secs));
        debug_assert!((0..1_000_000_000).contains(&frac));

        if secs < 0 {
            secs += 86_400;
            morerhssecs -= 86_400;
        } else if secs >= 86_400 {
            secs -= 86_400;
            morerhssecs += 86_400;
        }
        debug_assert!((0..86_400).contains(&secs));

        (NaiveTime { secs: secs as u32, frac: frac as u32 }, morerhssecs)
    }

    /// Subtracts given `TimeDelta` from the current time,
    /// and also returns the number of *seconds*
    /// in the integral number of days ignored from the subtraction.
    /// (We cannot return `TimeDelta` because it is subject to overflow or underflow.)
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeDelta, NaiveTime};
    ///
    /// let from_hms = NaiveTime::from_hms;
    ///
    /// assert_eq!(from_hms(3, 4, 5)?.overflowing_sub_signed(TimeDelta::hours(2)),
    ///            (from_hms(1, 4, 5)?, 0));
    /// assert_eq!(from_hms(3, 4, 5)?.overflowing_sub_signed(TimeDelta::hours(17)),
    ///            (from_hms(10, 4, 5)?, 86_400));
    /// assert_eq!(from_hms(3, 4, 5)?.overflowing_sub_signed(TimeDelta::hours(-22)),
    ///            (from_hms(1, 4, 5)?, -86_400));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    pub fn overflowing_sub_signed(&self, rhs: TimeDelta) -> (NaiveTime, i64) {
        let (time, rhs) = self.overflowing_add_signed(-rhs);
        (time, -rhs) // safe to negate, rhs is within +/- (2^63 / 1000)
    }

    /// Subtracts another `NaiveTime` from the current time.
    /// Returns a `TimeDelta` within +/- 1 day.
    /// This does not overflow or underflow at all.
    ///
    /// As a part of Chrono's [leap second handling](#leap-second-handling),
    /// the subtraction assumes that **there is no leap second ever**,
    /// except when any of the `NaiveTime`s themselves represents a leap second
    /// in which case the assumption becomes that
    /// **there are exactly one (or two) leap second(s) ever**.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{TimeDelta, NaiveTime};
    ///
    /// let from_hmsm = NaiveTime::from_hms_milli;
    /// let since = NaiveTime::signed_duration_since;
    ///
    /// assert_eq!(since(from_hmsm(3, 5, 7, 900)?, from_hmsm(3, 5, 7, 900)?),
    ///            TimeDelta::zero());
    /// assert_eq!(since(from_hmsm(3, 5, 7, 900)?, from_hmsm(3, 5, 7, 875)?),
    ///            TimeDelta::milliseconds(25));
    /// assert_eq!(since(from_hmsm(3, 5, 7, 900)?, from_hmsm(3, 5, 6, 925)?),
    ///            TimeDelta::milliseconds(975));
    /// assert_eq!(since(from_hmsm(3, 5, 7, 900)?, from_hmsm(3, 5, 0, 900)?),
    ///            TimeDelta::seconds(7));
    /// assert_eq!(since(from_hmsm(3, 5, 7, 900)?, from_hmsm(3, 0, 7, 900)?),
    ///            TimeDelta::seconds(5 * 60));
    /// assert_eq!(since(from_hmsm(3, 5, 7, 900)?, from_hmsm(0, 5, 7, 900)?),
    ///            TimeDelta::seconds(3 * 3600));
    /// assert_eq!(since(from_hmsm(3, 5, 7, 900)?, from_hmsm(4, 5, 7, 900)?),
    ///            TimeDelta::seconds(-3600));
    /// assert_eq!(since(from_hmsm(3, 5, 7, 900)?, from_hmsm(2, 4, 6, 800)?),
    ///            TimeDelta::seconds(3600 + 60 + 1) + TimeDelta::milliseconds(100));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// Leap seconds are handled, but the subtraction assumes that
    /// there were no other leap seconds happened.
    ///
    /// ```
    /// # use chrono::{TimeDelta, NaiveTime};
    /// # let from_hmsm = NaiveTime::from_hms_milli;
    /// # let since = NaiveTime::signed_duration_since;
    /// assert_eq!(since(from_hmsm(3, 0, 59, 1_000)?, from_hmsm(3, 0, 59, 0)?),
    ///            TimeDelta::seconds(1));
    /// assert_eq!(since(from_hmsm(3, 0, 59, 1_500)?, from_hmsm(3, 0, 59, 0)?),
    ///            TimeDelta::milliseconds(1500));
    /// assert_eq!(since(from_hmsm(3, 0, 59, 1_000)?, from_hmsm(3, 0, 0, 0)?),
    ///            TimeDelta::seconds(60));
    /// assert_eq!(since(from_hmsm(3, 0, 0, 0)?, from_hmsm(2, 59, 59, 1_000)?),
    ///            TimeDelta::seconds(1));
    /// assert_eq!(since(from_hmsm(3, 0, 59, 1_000)?, from_hmsm(2, 59, 59, 1_000)?),
    ///            TimeDelta::seconds(61));
    /// # Ok::<_, chrono::Error>(())
    /// ```
    pub fn signed_duration_since(self, rhs: NaiveTime) -> TimeDelta {
        //     |    |    :leap|    |    |    |    |    |    |    :leap|    |
        //     |    |    :    |    |    |    |    |    |    |    :    |    |
        // ----+----+-----*---+----+----+----+----+----+----+-------*-+----+----
        //          |   `rhs` |                             |    `self`
        //          |======================================>|       |
        //          |     |  `self.secs - rhs.secs`         |`self.frac`
        //          |====>|   |                             |======>|
        //      `rhs.frac`|========================================>|
        //          |     |   |        `self - rhs`         |       |

        use core::cmp::Ordering;

        let secs = i64::from(self.secs) - i64::from(rhs.secs);
        let frac = i64::from(self.frac) - i64::from(rhs.frac);

        // `secs` may contain a leap second yet to be counted
        let adjust = match self.secs.cmp(&rhs.secs) {
            Ordering::Greater => {
                if rhs.frac >= 1_000_000_000 {
                    1
                } else {
                    0
                }
            }
            Ordering::Equal => 0,
            Ordering::Less => {
                if self.frac >= 1_000_000_000 {
                    -1
                } else {
                    0
                }
            }
        };

        TimeDelta::seconds(secs + adjust) + TimeDelta::nanoseconds(frac)
    }

    /// Formats the time with the specified formatting items.
    /// Otherwise it is the same as the ordinary [`format`](#method.format) method.
    ///
    /// The `Iterator` of items should be `Clone`able,
    /// since the resulting `DelayedFormat` value may be formatted multiple times.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveTime;
    /// use chrono::format::strftime::StrftimeItems;
    ///
    /// let fmt = StrftimeItems::new("%H:%M:%S");
    /// let t = NaiveTime::from_hms(23, 56, 4)?;
    /// assert_eq!(t.format_with_items(fmt.clone()).to_string(), "23:56:04");
    /// assert_eq!(t.format("%H:%M:%S").to_string(), "23:56:04");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// The resulting `DelayedFormat` can be formatted directly via the `Display` trait.
    ///
    /// ```
    /// # use chrono::NaiveTime;
    /// # use chrono::format::strftime::StrftimeItems;
    /// # let fmt = StrftimeItems::new("%H:%M:%S").clone();
    /// # let t = NaiveTime::from_hms(23, 56, 4)?;
    /// assert_eq!(format!("{}", t.format_with_items(fmt)), "23:56:04");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    pub fn format_with_items<'a, I, B>(&self, items: I) -> DelayedFormat<I>
    where
        I: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        DelayedFormat::new(None, Some(*self), items)
    }

    /// Formats the time with the specified format string.
    /// See the [`format::strftime` module](../format/strftime/index.html)
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
    /// ```
    /// use chrono::NaiveTime;
    ///
    /// let t = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?;
    /// assert_eq!(t.format("%H:%M:%S").to_string(), "23:56:04");
    /// assert_eq!(t.format("%H:%M:%S%.6f").to_string(), "23:56:04.012345");
    /// assert_eq!(t.format("%-I:%M %p").to_string(), "11:56 PM");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// The resulting `DelayedFormat` can be formatted directly via the `Display` trait.
    ///
    /// ```
    /// # use chrono::NaiveTime;
    /// # let t = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?;
    /// assert_eq!(format!("{}", t.format("%H:%M:%S")), "23:56:04");
    /// assert_eq!(format!("{}", t.format("%H:%M:%S%.6f")), "23:56:04.012345");
    /// assert_eq!(format!("{}", t.format("%-I:%M %p")), "11:56 PM");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
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

    pub(super) const MIN: Self = Self { secs: 0, frac: 0 };
    pub(super) const MAX: Self = Self { secs: 23 * 3600 + 59 * 60 + 59, frac: 999_999_999 };
}

impl Timelike for NaiveTime {
    /// Returns the hour number from 0 to 23.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// assert_eq!(NaiveTime::from_hms(0, 0, 0)?.hour(), 0);
    /// assert_eq!(NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?.hour(), 23);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn hour(&self) -> u32 {
        self.hms().0
    }

    /// Returns the minute number from 0 to 59.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// assert_eq!(NaiveTime::from_hms(0, 0, 0)?.minute(), 0);
    /// assert_eq!(NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?.minute(), 56);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn minute(&self) -> u32 {
        self.hms().1
    }

    /// Returns the second number from 0 to 59.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// assert_eq!(NaiveTime::from_hms(0, 0, 0)?.second(), 0);
    /// assert_eq!(NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?.second(), 4);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// This method never returns 60 even when it is a leap second.
    /// ([Why?](#leap-second-handling))
    /// Use the proper [formatting method](#method.format) to get a human-readable representation.
    ///
    /// ```
    /// # use chrono::{NaiveTime, Timelike};
    /// let leap = NaiveTime::from_hms_milli(23, 59, 59, 1_000)?;
    /// assert_eq!(leap.second(), 59);
    /// assert_eq!(leap.format("%H:%M:%S").to_string(), "23:59:60");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn second(&self) -> u32 {
        self.hms().2
    }

    /// Returns the number of nanoseconds since the whole non-leap second.
    /// The range from 1,000,000,000 to 1,999,999,999 represents
    /// the [leap second](#leap-second-handling).
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// assert_eq!(NaiveTime::from_hms(0, 0, 0)?.nanosecond(), 0);
    /// assert_eq!(NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?.nanosecond(), 12_345_678);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// Leap seconds may have seemingly out-of-range return values.
    /// You can reduce the range with `time.nanosecond() % 1_000_000_000`, or
    /// use the proper [formatting method](#method.format) to get a human-readable representation.
    ///
    /// ```
    /// # use chrono::{NaiveTime, Timelike};
    /// let leap = NaiveTime::from_hms_milli(23, 59, 59, 1_000)?;
    /// assert_eq!(leap.nanosecond(), 1_000_000_000);
    /// assert_eq!(leap.format("%H:%M:%S%.9f").to_string(), "23:59:60.000000000");
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn nanosecond(&self) -> u32 {
        self.frac
    }

    /// Makes a new `NaiveTime` with the hour number changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveTime` would be
    /// invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let dt = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?;
    /// assert_eq!(dt.with_hour(7)?, NaiveTime::from_hms_nano(7, 56, 4, 12_345_678)?);
    /// assert!(dt.with_hour(24).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_hour(&self, hour: u32) -> Result<NaiveTime, Error> {
        if hour >= 24 {
            return Err(Error::new(ErrorKind::InvalidTime));
        }
        let secs = hour * 3600 + self.secs % 3600;
        Ok(NaiveTime { secs, ..*self })
    }

    /// Makes a new `NaiveTime` with the minute number changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveTime` would be
    /// invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let dt = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?;
    /// assert_eq!(dt.with_minute(45)?, NaiveTime::from_hms_nano(23, 45, 4, 12_345_678)?);
    /// assert!(dt.with_minute(60).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_minute(&self, min: u32) -> Result<NaiveTime, Error> {
        if min >= 60 {
            return Err(Error::new(ErrorKind::InvalidTime));
        }
        let secs = self.secs / 3600 * 3600 + min * 60 + self.secs % 60;
        Ok(NaiveTime { secs, ..*self })
    }

    /// Makes a new `NaiveTime` with the second number changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveTime` would be
    /// invalid. As with the [`second`](#method.second) method, the input range
    /// is restricted to 0 through 59.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let dt = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?;
    /// assert_eq!(dt.with_second(17)?, NaiveTime::from_hms_nano(23, 56, 17, 12_345_678)?);
    /// assert!(dt.with_second(60).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_second(&self, sec: u32) -> Result<NaiveTime, Error> {
        if sec >= 60 {
            return Err(Error::new(ErrorKind::InvalidTime));
        }
        let secs = self.secs / 60 * 60 + sec;
        Ok(NaiveTime { secs, ..*self })
    }

    /// Makes a new `NaiveTime` with nanoseconds since the whole non-leap second
    /// changed.
    ///
    /// Returns `Err(Error)` when the resulting `NaiveTime` would be
    /// invalid. As with the [`nanosecond`](#method.nanosecond) method, the
    /// input range can exceed 1,000,000,000 for leap seconds.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// let dt = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?;
    /// assert_eq!(dt.with_nanosecond(333_333_333)?, NaiveTime::from_hms_nano(23, 56, 4, 333_333_333)?);
    /// assert!(dt.with_nanosecond(2_000_000_000).is_err());
    /// # Ok::<_, chrono::Error>(())
    /// ```
    ///
    /// Leap seconds can theoretically follow *any* whole second. The following
    /// would be a proper leap second at the time zone offset of UTC-00:03:57
    /// (there are several historical examples comparable to this "non-sense"
    /// offset), and therefore is allowed.
    ///
    /// ```
    /// # use chrono::{NaiveTime, Timelike};
    /// # let dt = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?;
    /// assert_eq!(dt.with_nanosecond(1_333_333_333)?, NaiveTime::from_hms_nano(23, 56, 4, 1_333_333_333)?);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Result<NaiveTime, Error> {
        if nano >= 2_000_000_000 {
            return Err(Error::new(ErrorKind::InvalidTime));
        }
        Ok(NaiveTime { frac: nano, ..*self })
    }

    /// Returns the number of non-leap seconds past the last midnight.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveTime, Timelike};
    ///
    /// assert_eq!(NaiveTime::from_hms(1, 2, 3)?.num_seconds_from_midnight(),
    ///            3723);
    /// assert_eq!(NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?.num_seconds_from_midnight(),
    ///            86164);
    /// assert_eq!(NaiveTime::from_hms_milli(23, 59, 59, 1_000)?.num_seconds_from_midnight(),
    ///            86399);
    /// # Ok::<_, chrono::Error>(())
    /// ```
    #[inline]
    fn num_seconds_from_midnight(&self) -> u32 {
        self.secs // do not repeat the calculation!
    }
}

/// An addition of `TimeDelta` to `NaiveTime` wraps around and never overflows or underflows.
/// In particular the addition ignores integral number of days.
///
/// As a part of Chrono's [leap second handling](#leap-second-handling),
/// the addition assumes that **there is no leap second ever**,
/// except when the `NaiveTime` itself represents a leap second
/// in which case the assumption becomes that **there is exactly a single leap second ever**.
///
/// # Example
///
/// ```
/// use chrono::{TimeDelta, NaiveTime};
///
/// let from_hmsm = NaiveTime::from_hms_milli;
///
/// assert_eq!(from_hmsm(3, 5, 7, 0)? + TimeDelta::zero(), from_hmsm(3, 5, 7, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? + TimeDelta::seconds(1), from_hmsm(3, 5, 8, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? + TimeDelta::seconds(-1), from_hmsm(3, 5, 6, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? + TimeDelta::seconds(60 + 4), from_hmsm(3, 6, 11, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? + TimeDelta::seconds(7*60*60 - 6*60), from_hmsm(9, 59, 7, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? + TimeDelta::milliseconds(80), from_hmsm(3, 5, 7, 80)?);
/// assert_eq!(from_hmsm(3, 5, 7, 950)? + TimeDelta::milliseconds(280), from_hmsm(3, 5, 8, 230)?);
/// assert_eq!(from_hmsm(3, 5, 7, 950)? + TimeDelta::milliseconds(-980), from_hmsm(3, 5, 6, 970)?);
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// The addition wraps around.
///
/// ```
/// # use chrono::{TimeDelta, NaiveTime};
/// # let from_hmsm = NaiveTime::from_hms_milli;
/// assert_eq!(from_hmsm(3, 5, 7, 0)? + TimeDelta::seconds(22*60*60), from_hmsm(1, 5, 7, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? + TimeDelta::seconds(-8*60*60), from_hmsm(19, 5, 7, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? + TimeDelta::days(800), from_hmsm(3, 5, 7, 0)?);
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds are handled, but the addition assumes that it is the only leap second happened.
///
/// ```
/// # use chrono::{TimeDelta, NaiveTime};
/// # let from_hmsm = NaiveTime::from_hms_milli;
/// let leap = from_hmsm(3, 5, 59, 1_300)?;
/// assert_eq!(leap + TimeDelta::zero(), from_hmsm(3, 5, 59, 1_300)?);
/// assert_eq!(leap + TimeDelta::milliseconds(-500), from_hmsm(3, 5, 59, 800)?);
/// assert_eq!(leap + TimeDelta::milliseconds(500), from_hmsm(3, 5, 59, 1_800)?);
/// assert_eq!(leap + TimeDelta::milliseconds(800), from_hmsm(3, 6, 0, 100)?);
/// assert_eq!(leap + TimeDelta::seconds(10), from_hmsm(3, 6, 9, 300)?);
/// assert_eq!(leap + TimeDelta::seconds(-10), from_hmsm(3, 5, 50, 300)?);
/// assert_eq!(leap + TimeDelta::days(1), from_hmsm(3, 5, 59, 300)?);
/// # Ok::<_, chrono::Error>(())
/// ```
impl Add<TimeDelta> for NaiveTime {
    type Output = NaiveTime;

    #[inline]
    fn add(self, rhs: TimeDelta) -> NaiveTime {
        self.overflowing_add_signed(rhs).0
    }
}

impl AddAssign<TimeDelta> for NaiveTime {
    #[inline]
    fn add_assign(&mut self, rhs: TimeDelta) {
        *self = self.add(rhs);
    }
}

/// A subtraction of `TimeDelta` from `NaiveTime` wraps around and never overflows or underflows.
/// In particular the addition ignores integral number of days.
/// It is the same as the addition with a negated `TimeDelta`.
///
/// As a part of Chrono's [leap second handling](#leap-second-handling),
/// the addition assumes that **there is no leap second ever**,
/// except when the `NaiveTime` itself represents a leap second
/// in which case the assumption becomes that **there is exactly a single leap second ever**.
///
/// # Example
///
/// ```
/// use chrono::{TimeDelta, NaiveTime};
///
/// let from_hmsm = NaiveTime::from_hms_milli;
///
/// assert_eq!(from_hmsm(3, 5, 7, 0)? - TimeDelta::zero(), from_hmsm(3, 5, 7, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? - TimeDelta::seconds(1), from_hmsm(3, 5, 6, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? - TimeDelta::seconds(60 + 5), from_hmsm(3, 4, 2, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? - TimeDelta::seconds(2*60*60 + 6*60), from_hmsm(0, 59, 7, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? - TimeDelta::milliseconds(80), from_hmsm(3, 5, 6, 920)?);
/// assert_eq!(from_hmsm(3, 5, 7, 950)? - TimeDelta::milliseconds(280), from_hmsm(3, 5, 7, 670)?);
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// The subtraction wraps around.
///
/// ```
/// # use chrono::{TimeDelta, NaiveTime};
/// # let from_hmsm = NaiveTime::from_hms_milli;
/// assert_eq!(from_hmsm(3, 5, 7, 0)? - TimeDelta::seconds(8*60*60), from_hmsm(19, 5, 7, 0)?);
/// assert_eq!(from_hmsm(3, 5, 7, 0)? - TimeDelta::days(800), from_hmsm(3, 5, 7, 0)?);
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds are handled, but the subtraction assumes that it is the only leap second happened.
///
/// ```
/// # use chrono::{TimeDelta, NaiveTime};
/// # let from_hmsm = NaiveTime::from_hms_milli;
/// let leap = from_hmsm(3, 5, 59, 1_300)?;
///
/// assert_eq!(leap - TimeDelta::zero(),  from_hmsm(3, 5, 59, 1_300)?);
/// assert_eq!(leap - TimeDelta::milliseconds(200), from_hmsm(3, 5, 59, 1_100)?);
/// assert_eq!(leap - TimeDelta::milliseconds(500), from_hmsm(3, 5, 59, 800)?);
/// assert_eq!(leap - TimeDelta::seconds(60), from_hmsm(3, 5, 0, 300)?);
/// assert_eq!(leap - TimeDelta::days(1), from_hmsm(3, 6, 0, 300)?);
/// # Ok::<_, chrono::Error>(())
/// ```
impl Sub<TimeDelta> for NaiveTime {
    type Output = NaiveTime;

    #[inline]
    fn sub(self, rhs: TimeDelta) -> NaiveTime {
        self.overflowing_sub_signed(rhs).0
    }
}

impl SubAssign<TimeDelta> for NaiveTime {
    #[inline]
    fn sub_assign(&mut self, rhs: TimeDelta) {
        *self = self.sub(rhs);
    }
}

/// Subtracts another `NaiveTime` from the current time.
/// Returns a `TimeDelta` within +/- 1 day.
/// This does not overflow or underflow at all.
///
/// As a part of Chrono's [leap second handling](#leap-second-handling),
/// the subtraction assumes that **there is no leap second ever**,
/// except when any of the `NaiveTime`s themselves represents a leap second
/// in which case the assumption becomes that
/// **there are exactly one (or two) leap second(s) ever**.
///
/// The implementation is a wrapper around
/// [`NaiveTime::signed_duration_since`](#method.signed_duration_since).
///
/// # Example
///
/// ```
/// use chrono::{TimeDelta, NaiveTime};
///
/// let from_hmsm = NaiveTime::from_hms_milli;
///
/// assert_eq!(from_hmsm(3, 5, 7, 900)? - from_hmsm(3, 5, 7, 900)?, TimeDelta::zero());
/// assert_eq!(from_hmsm(3, 5, 7, 900)? - from_hmsm(3, 5, 7, 875)?, TimeDelta::milliseconds(25));
/// assert_eq!(from_hmsm(3, 5, 7, 900)? - from_hmsm(3, 5, 6, 925)?, TimeDelta::milliseconds(975));
/// assert_eq!(from_hmsm(3, 5, 7, 900)? - from_hmsm(3, 5, 0, 900)?, TimeDelta::seconds(7));
/// assert_eq!(from_hmsm(3, 5, 7, 900)? - from_hmsm(3, 0, 7, 900)?, TimeDelta::seconds(5 * 60));
/// assert_eq!(from_hmsm(3, 5, 7, 900)? - from_hmsm(0, 5, 7, 900)?, TimeDelta::seconds(3 * 3600));
/// assert_eq!(from_hmsm(3, 5, 7, 900)? - from_hmsm(4, 5, 7, 900)?, TimeDelta::seconds(-3600));
/// assert_eq!(from_hmsm(3, 5, 7, 900)? - from_hmsm(2, 4, 6, 800)?,
///            TimeDelta::seconds(3600 + 60 + 1) + TimeDelta::milliseconds(100));
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds are handled, but the subtraction assumes that
/// there were no other leap seconds happened.
///
/// ```
/// # use chrono::{TimeDelta, NaiveTime};
/// # let from_hmsm = NaiveTime::from_hms_milli;
/// assert_eq!(from_hmsm(3, 0, 59, 1_000)? - from_hmsm(3, 0, 59, 0)?, TimeDelta::seconds(1));
/// assert_eq!(from_hmsm(3, 0, 59, 1_500)? - from_hmsm(3, 0, 59, 0)?,
///            TimeDelta::milliseconds(1500));
/// assert_eq!(from_hmsm(3, 0, 59, 1_000)? - from_hmsm(3, 0, 0, 0)?, TimeDelta::seconds(60));
/// assert_eq!(from_hmsm(3, 0, 0, 0)? - from_hmsm(2, 59, 59, 1_000)?, TimeDelta::seconds(1));
/// assert_eq!(from_hmsm(3, 0, 59, 1_000)? - from_hmsm(2, 59, 59, 1_000)?,
///            TimeDelta::seconds(61));
/// # Ok::<_, chrono::Error>(())
/// ```
impl Sub<NaiveTime> for NaiveTime {
    type Output = TimeDelta;

    #[inline]
    fn sub(self, rhs: NaiveTime) -> TimeDelta {
        self.signed_duration_since(rhs)
    }
}

/// The `Debug` output of the naive time `t` is the same as
/// [`t.format("%H:%M:%S%.f")`](../format/strftime/index.html).
///
/// The string printed can be readily parsed via the `parse` method on `str`.
///
/// It should be noted that, for leap seconds not on the minute boundary,
/// it may print a representation not distinguishable from non-leap seconds.
/// This doesn't matter in practice, since such leap seconds never happened.
/// (By the time of the first leap second on 1972-06-30,
/// every time zone offset around the world has standardized to the 5-minute alignment.)
///
/// # Example
///
/// ```
/// use chrono::NaiveTime;
///
/// assert_eq!(format!("{:?}", NaiveTime::from_hms(23, 56, 4)?), "23:56:04");
/// assert_eq!(format!("{:?}", NaiveTime::from_hms_milli(23, 56, 4, 12)?), "23:56:04.012");
/// assert_eq!(format!("{:?}", NaiveTime::from_hms_micro(23, 56, 4, 1234)?), "23:56:04.001234");
/// assert_eq!(format!("{:?}", NaiveTime::from_hms_nano(23, 56, 4, 123456)?), "23:56:04.000123456");
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds may also be used.
///
/// ```
/// # use chrono::NaiveTime;
/// assert_eq!(format!("{:?}", NaiveTime::from_hms_milli(6, 59, 59, 1_500)?), "06:59:60.500");
/// # Ok::<_, chrono::Error>(())
/// ```
impl fmt::Debug for NaiveTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (hour, min, sec) = self.hms();
        let (sec, nano) = if self.frac >= 1_000_000_000 {
            (sec + 1, self.frac - 1_000_000_000)
        } else {
            (sec, self.frac)
        };

        write!(f, "{:02}:{:02}:{:02}", hour, min, sec)?;
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

/// The `Display` output of the naive time `t` is the same as
/// [`t.format("%H:%M:%S%.f")`](../format/strftime/index.html).
///
/// The string printed can be readily parsed via the `parse` method on `str`.
///
/// It should be noted that, for leap seconds not on the minute boundary,
/// it may print a representation not distinguishable from non-leap seconds.
/// This doesn't matter in practice, since such leap seconds never happened.
/// (By the time of the first leap second on 1972-06-30,
/// every time zone offset around the world has standardized to the 5-minute alignment.)
///
/// # Example
///
/// ```
/// use chrono::NaiveTime;
///
/// assert_eq!(format!("{}", NaiveTime::from_hms(23, 56, 4)?),  "23:56:04");
/// assert_eq!(format!("{}", NaiveTime::from_hms_milli(23, 56, 4, 12)?), "23:56:04.012");
/// assert_eq!(format!("{}", NaiveTime::from_hms_micro(23, 56, 4, 1234)?), "23:56:04.001234");
/// assert_eq!(format!("{}", NaiveTime::from_hms_nano(23, 56, 4, 123456)?), "23:56:04.000123456");
/// # Ok::<_, chrono::Error>(())
/// ```
///
/// Leap seconds may also be used.
///
/// ```
/// # use chrono::NaiveTime;
/// assert_eq!(format!("{}", NaiveTime::from_hms_milli(6, 59, 59, 1_500)?), "06:59:60.500");
/// # Ok::<_, chrono::Error>(())
/// ```
impl fmt::Display for NaiveTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// Parsing a `str` into a `NaiveTime` uses the same format,
/// [`%H:%M:%S%.f`](../format/strftime/index.html), as in `Debug` and `Display`.
///
/// # Example
///
/// ```
/// use chrono::NaiveTime;
///
/// let t = NaiveTime::from_hms(23, 56, 4)?;
/// assert_eq!("23:56:04".parse::<NaiveTime>(), Ok(t));
///
/// let t = NaiveTime::from_hms_nano(23, 56, 4, 12_345_678)?;
/// assert_eq!("23:56:4.012345678".parse::<NaiveTime>(), Ok(t));
///
/// let t = NaiveTime::from_hms_nano(23, 59, 59, 1_234_567_890)?; // leap second
/// assert_eq!("23:59:60.23456789".parse::<NaiveTime>(), Ok(t));
///
/// assert!("foo".parse::<NaiveTime>().is_err());
/// # Ok::<_, chrono::Error>(())
/// ```
impl str::FromStr for NaiveTime {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<NaiveTime> {
        const ITEMS: &[Item<'static>] = &[
            Item::Numeric(Numeric::Hour, Pad::Zero),
            Item::Space(""),
            Item::Literal(":"),
            Item::Numeric(Numeric::Minute, Pad::Zero),
            Item::Space(""),
            Item::Literal(":"),
            Item::Numeric(Numeric::Second, Pad::Zero),
            Item::Fixed(Fixed::Nanosecond),
            Item::Space(""),
        ];

        let mut parsed = Parsed::new();
        parse(&mut parsed, s, ITEMS.iter())?;
        parsed.to_naive_time()
    }
}

/// The default value for a NaiveTime is midnight, 00:00:00 exactly.
///
/// # Example
///
/// ```rust
/// use chrono::NaiveTime;
///
/// let default_time = NaiveTime::default();
/// assert_eq!(default_time, NaiveTime::from_hms(0, 0, 0)?);
/// # Ok::<_, chrono::Error>(())
/// ```
impl Default for NaiveTime {
    fn default() -> Self {
        NaiveTime::midnight()
    }
}

#[cfg(all(test, feature = "serde"))]
fn test_encodable_json<F, E>(to_string: F)
where
    F: Fn(&NaiveTime) -> Result<String, E>,
    E: ::std::fmt::Debug,
{
    assert_eq!(
        to_string(&NaiveTime::from_hms(0, 0, 0).unwrap()).ok(),
        Some(r#""00:00:00""#.into())
    );
    assert_eq!(
        to_string(&NaiveTime::from_hms_milli(0, 0, 0, 950).unwrap()).ok(),
        Some(r#""00:00:00.950""#.into())
    );
    assert_eq!(
        to_string(&NaiveTime::from_hms_milli(0, 0, 59, 1_000).unwrap()).ok(),
        Some(r#""00:00:60""#.into())
    );
    assert_eq!(
        to_string(&NaiveTime::from_hms(0, 1, 2).unwrap()).ok(),
        Some(r#""00:01:02""#.into())
    );
    assert_eq!(
        to_string(&NaiveTime::from_hms_nano(3, 5, 7, 98765432).unwrap()).ok(),
        Some(r#""03:05:07.098765432""#.into())
    );
    assert_eq!(
        to_string(&NaiveTime::from_hms(7, 8, 9).unwrap()).ok(),
        Some(r#""07:08:09""#.into())
    );
    assert_eq!(
        to_string(&NaiveTime::from_hms_micro(12, 34, 56, 789).unwrap()).ok(),
        Some(r#""12:34:56.000789""#.into())
    );
    assert_eq!(
        to_string(&NaiveTime::from_hms_nano(23, 59, 59, 1_999_999_999).unwrap()).ok(),
        Some(r#""23:59:60.999999999""#.into())
    );
}

#[cfg(all(test, feature = "serde"))]
fn test_decodable_json<F, E>(from_str: F)
where
    F: Fn(&str) -> Result<NaiveTime, E>,
    E: ::std::fmt::Debug,
{
    assert_eq!(from_str(r#""00:00:00""#).unwrap(), NaiveTime::from_hms(0, 0, 0).unwrap());
    assert_eq!(from_str(r#""0:0:0""#).unwrap(), NaiveTime::from_hms(0, 0, 0).unwrap());
    assert_eq!(
        from_str(r#""00:00:00.950""#).unwrap(),
        NaiveTime::from_hms_milli(0, 0, 0, 950).unwrap()
    );
    assert_eq!(
        from_str(r#""0:0:0.95""#).unwrap(),
        NaiveTime::from_hms_milli(0, 0, 0, 950).unwrap()
    );
    assert_eq!(
        from_str(r#""00:00:60""#).unwrap(),
        NaiveTime::from_hms_milli(0, 0, 59, 1_000).unwrap()
    );
    assert_eq!(from_str(r#""00:01:02""#).unwrap(), NaiveTime::from_hms(0, 1, 2).unwrap());
    assert_eq!(
        from_str(r#""03:05:07.098765432""#).unwrap(),
        NaiveTime::from_hms_nano(3, 5, 7, 98765432).unwrap()
    );
    assert_eq!(from_str(r#""07:08:09""#).unwrap(), NaiveTime::from_hms(7, 8, 9).unwrap());
    assert_eq!(
        from_str(r#""12:34:56.000789""#).unwrap(),
        NaiveTime::from_hms_micro(12, 34, 56, 789).unwrap()
    );
    assert_eq!(
        from_str(r#""23:59:60.999999999""#).unwrap(),
        NaiveTime::from_hms_nano(23, 59, 59, 1_999_999_999).unwrap()
    );
    assert_eq!(
        from_str(r#""23:59:60.9999999999997""#).unwrap(), // excess digits are ignored
        NaiveTime::from_hms_nano(23, 59, 59, 1_999_999_999).unwrap()
    );

    // bad formats
    assert!(from_str(r#""""#).is_err());
    assert!(from_str(r#""000000""#).is_err());
    assert!(from_str(r#""00:00:61""#).is_err());
    assert!(from_str(r#""00:60:00""#).is_err());
    assert!(from_str(r#""24:00:00""#).is_err());
    assert!(from_str(r#""23:59:59,1""#).is_err());
    assert!(from_str(r#""012:34:56""#).is_err());
    assert!(from_str(r#""hh:mm:ss""#).is_err());
    assert!(from_str(r#"0"#).is_err());
    assert!(from_str(r#"86399"#).is_err());
    assert!(from_str(r#"{}"#).is_err());
    // pre-0.3.0 rustc-serialize format is now invalid
    assert!(from_str(r#"{"secs":0,"frac":0}"#).is_err());
    assert!(from_str(r#"null"#).is_err());
}
