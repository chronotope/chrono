// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The time zone which has a fixed offset from UTC.

use core::fmt;
use core::num::NonZeroI32;
use core::str::FromStr;

#[cfg(any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"))]
use rkyv::{Archive, Deserialize, Serialize};

use super::{LocalResult, Offset, TimeZone};
use crate::format::{scan, ParseError, OUT_OF_RANGE};
use crate::naive::{NaiveDate, NaiveDateTime};

const OFFSET_NORMAL: i32 = 1;
const OFFSET_UNKNOWN: i32 = 2;

/// A fixed offset of clock time from [Coordinated Universal Time] (UTC) stored to seconds granularity.
/// A `FixedOffset` can be used to indicate a time zone.
///
/// This type implements the [`TimeZone`] trait.
///
/// The valid range of offsets is UTC-23:59:59 to UTC+23:59:59.
///
/// ## Creating a `FixedOffset`
///
/// - Use [`FixedOffset::east_opt`] with a value in _seconds_ to create a new [`FixedOffset`].
///   The offset is to be given as local time minus UTC time.
/// - Use [`FixedOffset::west_opt`] with a value in _seconds_ to create the value from an offset
///   given as UTC time minus local time.
///
/// See the [`east_opt`](#method.east_opt) and [`west_opt`](#method.west_opt) methods for examples.
///
/// ## Encoding an unknown offset
///
/// RFC 3339 and RFC 2822 make a distinction between an offset of `+00:00` and `-00:00`.
///
/// [RFC 2822]:
/// > The form "+0000" SHOULD be used to indicate a time zone at Universal Time. Though "-0000"
/// > also indicates Universal Time, it is used to indicate that the time was generated on a system
/// > that may be in a local time zone other than Universal Time and therefore indicates that the
/// > date-time contains no information about the local time zone.
///
/// [RFC 3339]:
/// > If the time in UTC is known, but the offset to local time is unknown, this can be represented
/// > with an offset of "-00:00". This differs semantically from an offset of "Z" or "+00:00",
/// > which imply that UTC is the preferred reference point for the specified time.
///
/// An offset of `00:00` that indicates there is no information about the local timezone can be
/// created with [`FixedOffset::OFFSET_UNKNOWN`]. Use [`no_offset_info()`](#method.no_offset_info)
/// to inspect whether `00:00` carries the extra annotation.
///
/// Besides formatting `-00:00` is not treated any differently in chrono from `+00:00`.
///
/// [Coordinated Universal Time]: https://en.wikipedia.org/wiki/Coordinated_Universal_Time
/// [RFC 2822]: https://www.rfc-editor.org/rfc/rfc2822.html#section-3.3
/// [RFC 3339]: https://www.rfc-editor.org/rfc/rfc3339.html#section-4.3
#[derive(Eq, Copy, Clone)]
#[cfg_attr(
    any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"),
    derive(Archive, Deserialize, Serialize),
    archive(compare(PartialEq)),
    archive_attr(derive(Clone, Copy, PartialEq, Eq, Hash, Debug))
)]
#[cfg_attr(feature = "rkyv-validation", archive(check_bytes))]
pub struct FixedOffset {
    // Encodes an offset in seconds, with the value shifted two bits to the left.
    // The remaining bits encode flags:
    // - `OFFSET_NORMAL` sets one flag to a non-zero value, so we can encode it in a `NonZeroI32`
    //   and get niche optimization.
    // - `OFFSET_UNKNOWN` to preserve the difference RFC 2822 and RFC 3339 make between an offset
    //    of +0:00 and -0:00.
    // Advantage of this encoding is that it only takes a single shift right to get offset in
    // seconds.
    //
    // Use `local_minus_utc()` to get the offset in seconds, and `no_offset_info()` to inspect the
    // `OFFSET_UNKNOWN` flag.
    local_minus_utc: NonZeroI32,
}

// Compare with only the offset. `-00:00` compares equal to `+00:00`
impl PartialEq for FixedOffset {
    fn eq(&self, other: &Self) -> bool {
        self.local_minus_utc() == other.local_minus_utc()
    }
}

// Hash only the offset. `-00:00` hashes equal to `+00:00`
impl core::hash::Hash for FixedOffset {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.local_minus_utc().hash(state);
    }
}

// Workaround because `unwrap` in `NonZeroI32::new(val).unwrap()` is not const.
#[allow(unconditional_panic)]
const fn nonzero_i32_new(val: i32) -> NonZeroI32 {
    match NonZeroI32::new(val) {
        Some(v) => v,
        None => [][0],
    }
}

impl FixedOffset {
    /// Makes a new `FixedOffset` for the Eastern Hemisphere with given timezone difference.
    /// The negative `secs` means the Western Hemisphere.
    ///
    /// Panics on the out-of-bound `secs`.
    #[deprecated(since = "0.4.23", note = "use `east_opt()` instead")]
    #[must_use]
    pub fn east(secs: i32) -> FixedOffset {
        FixedOffset::east_opt(secs).expect("FixedOffset::east out of bounds")
    }

    /// Makes a new `FixedOffset` for the Eastern Hemisphere with given timezone difference.
    /// The negative `secs` means the Western Hemisphere.
    ///
    /// Returns `None` on the out-of-bound `secs`.
    ///
    /// # Example
    ///
    #[cfg_attr(not(feature = "std"), doc = "```ignore")]
    #[cfg_attr(feature = "std", doc = "```")]
    /// use chrono::{FixedOffset, TimeZone};
    /// let hour = 3600;
    /// let datetime =
    ///     FixedOffset::east_opt(5 * hour).unwrap().with_ymd_and_hms(2016, 11, 08, 0, 0, 0).unwrap();
    /// assert_eq!(&datetime.to_rfc3339(), "2016-11-08T00:00:00+05:00")
    /// ```
    #[must_use]
    pub const fn east_opt(secs: i32) -> Option<FixedOffset> {
        if -86_400 < secs && secs < 86_400 {
            Some(FixedOffset { local_minus_utc: nonzero_i32_new(secs << 2 | OFFSET_NORMAL) })
        } else {
            None
        }
    }

    /// Makes a new `FixedOffset` for the Western Hemisphere with given timezone difference.
    /// The negative `secs` means the Eastern Hemisphere.
    ///
    /// Panics on the out-of-bound `secs`.
    #[deprecated(since = "0.4.23", note = "use `west_opt()` instead")]
    #[must_use]
    pub fn west(secs: i32) -> FixedOffset {
        FixedOffset::west_opt(secs).expect("FixedOffset::west out of bounds")
    }

    /// Makes a new `FixedOffset` for the Western Hemisphere with given timezone difference.
    /// The negative `secs` means the Eastern Hemisphere.
    ///
    /// Returns `None` on the out-of-bound `secs`.
    ///
    /// # Example
    ///
    #[cfg_attr(not(feature = "std"), doc = "```ignore")]
    #[cfg_attr(feature = "std", doc = "```")]
    /// use chrono::{FixedOffset, TimeZone};
    /// let hour = 3600;
    /// let datetime =
    ///     FixedOffset::west_opt(5 * hour).unwrap().with_ymd_and_hms(2016, 11, 08, 0, 0, 0).unwrap();
    /// assert_eq!(&datetime.to_rfc3339(), "2016-11-08T00:00:00-05:00")
    /// ```
    #[must_use]
    pub const fn west_opt(secs: i32) -> Option<FixedOffset> {
        if -86_400 < secs && secs < 86_400 {
            Some(FixedOffset { local_minus_utc: nonzero_i32_new(-secs << 2 | OFFSET_NORMAL) })
        } else {
            None
        }
    }

    /// Returns the number of seconds to add to convert from UTC to the local time.
    #[inline]
    pub const fn local_minus_utc(&self) -> i32 {
        self.local_minus_utc.get() >> 2
    }

    /// Returns the number of seconds to add to convert from the local time to UTC.
    #[inline]
    pub const fn utc_minus_local(&self) -> i32 {
        -self.local_minus_utc()
    }

    /// Returns true if this `FixedOffset` contains no offset data (in some formats encoded as
    /// `-00:00`).
    ///
    /// In some formats, such as RFC 2822 and RFC 3339, `-00:00` can represent timestamps for which
    /// only the time in UTC is known, and the relation to local time is not avaliable (anymore).
    #[inline]
    pub const fn no_offset_info(&self) -> bool {
        self.local_minus_utc.get() == OFFSET_UNKNOWN
    }

    /// A special value to indicate no offset information is available.
    /// The created offset will have the value `-00:00`.
    pub const OFFSET_UNKNOWN: FixedOffset =
        FixedOffset { local_minus_utc: nonzero_i32_new(OFFSET_UNKNOWN) };
}

/// Parsing a `str` into a `FixedOffset` uses the format [`%z`](crate::format::strftime).
impl FromStr for FixedOffset {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (_, offset) = scan::timezone_offset(s, scan::colon_or_space, false, false, true)?;
        Self::east_opt(offset).ok_or(OUT_OF_RANGE)
    }
}

impl TimeZone for FixedOffset {
    type Offset = FixedOffset;

    fn from_offset(offset: &FixedOffset) -> FixedOffset {
        *offset
    }

    fn offset_from_local_date(&self, _local: &NaiveDate) -> LocalResult<FixedOffset> {
        LocalResult::Single(*self)
    }
    fn offset_from_local_datetime(&self, _local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        LocalResult::Single(*self)
    }

    fn offset_from_utc_date(&self, _utc: &NaiveDate) -> FixedOffset {
        *self
    }
    fn offset_from_utc_datetime(&self, _utc: &NaiveDateTime) -> FixedOffset {
        *self
    }
}

impl Offset for FixedOffset {
    fn fix(&self) -> FixedOffset {
        *self
    }
}

impl fmt::Debug for FixedOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.no_offset_info() {
            // In RFC 3339 `-00:00` can represent timestamps for which only the time in UTC is
            // known, and the relation to local time is not avaliable (anymore).
            return write!(f, "-00:00");
        }
        let offset = self.local_minus_utc();
        let (sign, offset) = if offset < 0 { ('-', -offset) } else { ('+', offset) };
        let sec = offset.rem_euclid(60);
        let mins = offset.div_euclid(60);
        let min = mins.rem_euclid(60);
        let hour = mins.div_euclid(60);
        if sec == 0 {
            write!(f, "{}{:02}:{:02}", sign, hour, min)
        } else {
            write!(f, "{}{:02}:{:02}:{:02}", sign, hour, min, sec)
        }
    }
}

impl fmt::Display for FixedOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

#[cfg(all(feature = "arbitrary", feature = "std"))]
impl arbitrary::Arbitrary<'_> for FixedOffset {
    fn arbitrary(u: &mut arbitrary::Unstructured) -> arbitrary::Result<FixedOffset> {
        let secs = u.int_in_range(-86_399..=86_399)?;
        let fixed_offset = FixedOffset::east_opt(secs)
            .expect("Could not generate a valid chrono::FixedOffset. It looks like implementation of Arbitrary for FixedOffset is erroneous.");
        Ok(fixed_offset)
    }
}

#[cfg(test)]
mod tests {
    use super::FixedOffset;
    use crate::offset::TimeZone;
    use std::str::FromStr;

    #[test]
    fn test_date_extreme_offset() {
        // starting from 0.3 we don't have an offset exceeding one day.
        // this makes everything easier!
        let offset = FixedOffset::east_opt(86399).unwrap();
        assert_eq!(
            format!("{:?}", offset.with_ymd_and_hms(2012, 2, 29, 5, 6, 7).unwrap()),
            "2012-02-29T05:06:07+23:59:59"
        );
        let offset = FixedOffset::east_opt(-86399).unwrap();
        assert_eq!(
            format!("{:?}", offset.with_ymd_and_hms(2012, 2, 29, 5, 6, 7).unwrap()),
            "2012-02-29T05:06:07-23:59:59"
        );
        let offset = FixedOffset::west_opt(86399).unwrap();
        assert_eq!(
            format!("{:?}", offset.with_ymd_and_hms(2012, 3, 4, 5, 6, 7).unwrap()),
            "2012-03-04T05:06:07-23:59:59"
        );
        let offset = FixedOffset::west_opt(-86399).unwrap();
        assert_eq!(
            format!("{:?}", offset.with_ymd_and_hms(2012, 3, 4, 5, 6, 7).unwrap()),
            "2012-03-04T05:06:07+23:59:59"
        );
    }

    #[test]
    fn test_parse_offset() {
        let offset = FixedOffset::from_str("-0500").unwrap();
        assert_eq!(offset.local_minus_utc(), -5 * 3600);
        let offset = FixedOffset::from_str("-08:00").unwrap();
        assert_eq!(offset.local_minus_utc(), -8 * 3600);
        let offset = FixedOffset::from_str("+06:30").unwrap();
        assert_eq!(offset.local_minus_utc(), (6 * 3600) + 1800);
    }

    #[test]
    #[cfg(feature = "rkyv-validation")]
    fn test_rkyv_validation() {
        let offset = FixedOffset::from_str("-0500").unwrap();
        let bytes = rkyv::to_bytes::<_, 4>(&offset).unwrap();
        assert_eq!(rkyv::from_bytes::<FixedOffset>(&bytes).unwrap(), offset);
    }
}
