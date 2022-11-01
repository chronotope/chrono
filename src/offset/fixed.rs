// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The time zone which has a fixed offset from UTC.

use core::convert::TryFrom;
use core::fmt;
use core::ops::{Add, Sub};
use core::time::Duration;

use num_integer::div_mod_floor;
#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use super::{LocalResult, Offset, TimeZone};
use crate::naive::{NaiveDate, NaiveDateTime, NaiveTime};
use crate::DateTime;
use crate::Timelike;

/// The time zone with fixed offset, from UTC-23:59:59 to UTC+23:59:59.
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on a `FixedOffset` struct is the preferred way to construct
/// `DateTime<FixedOffset>` instances. See the [`east`](#method.east) and
/// [`west`](#method.west) methods for examples.
#[derive(PartialEq, Eq, Hash, Copy, Clone)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct FixedOffset {
    local_minus_utc: i32,
}

impl FixedOffset {
    /// Makes a new `FixedOffset` for the Eastern Hemisphere with given timezone difference.
    /// The negative `secs` means the Western Hemisphere.
    ///
    /// Panics on the out-of-bound `secs`.
    #[deprecated(since = "0.4.23", note = "use `east_opt()` instead")]
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
    /// ```
    /// use chrono::{FixedOffset, TimeZone};
    /// let hour = 3600;
    /// let datetime = FixedOffset::east_opt(5 * hour).unwrap().ymd_opt(2016, 11, 08).unwrap()
    ///                                           .and_hms_opt(0, 0, 0).unwrap();
    /// assert_eq!(&datetime.to_rfc3339(), "2016-11-08T00:00:00+05:00")
    /// ```
    pub fn east_opt(secs: i32) -> Option<FixedOffset> {
        if -86_400 < secs && secs < 86_400 {
            Some(FixedOffset { local_minus_utc: secs })
        } else {
            None
        }
    }

    /// Makes a new `FixedOffset` for the Western Hemisphere with given timezone difference.
    /// The negative `secs` means the Eastern Hemisphere.
    ///
    /// Panics on the out-of-bound `secs`.
    #[deprecated(since = "0.4.23", note = "use `west_opt()` instead")]
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
    /// ```
    /// use chrono::{FixedOffset, TimeZone};
    /// let hour = 3600;
    /// let datetime = FixedOffset::west_opt(5 * hour).unwrap().ymd_opt(2016, 11, 08).unwrap()
    ///                                           .and_hms_opt(0, 0, 0).unwrap();
    /// assert_eq!(&datetime.to_rfc3339(), "2016-11-08T00:00:00-05:00")
    /// ```
    pub fn west_opt(secs: i32) -> Option<FixedOffset> {
        if -86_400 < secs && secs < 86_400 {
            Some(FixedOffset { local_minus_utc: -secs })
        } else {
            None
        }
    }

    /// Returns the number of seconds to add to convert from UTC to the local time.
    #[inline]
    pub fn local_minus_utc(&self) -> i32 {
        self.local_minus_utc
    }

    /// Returns the number of seconds to add to convert from the local time to UTC.
    #[inline]
    pub fn utc_minus_local(&self) -> i32 {
        -self.local_minus_utc
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
        let offset = self.local_minus_utc;
        let (sign, offset) = if offset < 0 { ('-', -offset) } else { ('+', offset) };
        let (mins, sec) = div_mod_floor(offset, 60);
        let (hour, min) = div_mod_floor(mins, 60);
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

// addition or subtraction of FixedOffset to/from Timelike values is the same as
// adding or subtracting the offset's local_minus_utc value
// but keep keeps the leap second information.
// this should be implemented more efficiently, but for the time being, this is generic right now.

fn add_with_leapsecond<T>(lhs: &T, rhs: u32) -> T
where
    T: Timelike + Add<Duration, Output = T>,
{
    // extract and temporarily remove the fractional part and later recover it
    let nanos = lhs.nanosecond();
    let lhs = lhs.with_nanosecond(0).unwrap();
    (lhs + Duration::from_secs(rhs.into())).with_nanosecond(nanos).unwrap()
}

fn sub_with_leapsecond<T>(lhs: &T, rhs: u32) -> T
where
    T: Timelike + Sub<Duration, Output = T>,
{
    // extract and temporarily remove the fractional part and later recover it
    let nanos = lhs.nanosecond();
    let lhs = lhs.with_nanosecond(0).unwrap();
    (lhs - Duration::from_secs(rhs.into())).with_nanosecond(nanos).unwrap()
}

impl Add<FixedOffset> for NaiveTime {
    type Output = NaiveTime;

    #[inline]
    fn add(self, rhs: FixedOffset) -> NaiveTime {
        if rhs.local_minus_utc > 0 {
            add_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc).unwrap())
        } else {
            sub_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc.abs()).unwrap())
        }
    }
}

impl Sub<FixedOffset> for NaiveTime {
    type Output = NaiveTime;

    #[inline]
    fn sub(self, rhs: FixedOffset) -> NaiveTime {
        if rhs.local_minus_utc > 0 {
            sub_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc.abs()).unwrap())
        } else {
            add_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc).unwrap())
        }
    }
}

impl Add<FixedOffset> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn add(self, rhs: FixedOffset) -> NaiveDateTime {
        if rhs.local_minus_utc > 0 {
            add_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc).unwrap())
        } else {
            sub_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc.abs()).unwrap())
        }
    }
}

impl Sub<FixedOffset> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn sub(self, rhs: FixedOffset) -> NaiveDateTime {
        if rhs.local_minus_utc > 0 {
            sub_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc).unwrap())
        } else {
            add_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc.abs()).unwrap())
        }
    }
}

impl<Tz: TimeZone> Add<FixedOffset> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn add(self, rhs: FixedOffset) -> DateTime<Tz> {
        if rhs.local_minus_utc > 0 {
            add_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc).unwrap())
        } else {
            sub_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc.abs()).unwrap())
        }
    }
}

impl<Tz: TimeZone> Sub<FixedOffset> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn sub(self, rhs: FixedOffset) -> DateTime<Tz> {
        if rhs.local_minus_utc > 0 {
            sub_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc).unwrap())
        } else {
            add_with_leapsecond(&self, u32::try_from(rhs.local_minus_utc.abs()).unwrap())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::FixedOffset;
    use crate::offset::TimeZone;

    #[test]
    fn test_date_extreme_offset() {
        // starting from 0.3 we don't have an offset exceeding one day.
        // this makes everything easier!
        assert_eq!(
            format!("{:?}", FixedOffset::east_opt(86399).unwrap().ymd_opt(2012, 2, 29).unwrap()),
            "2012-02-29+23:59:59".to_string()
        );
        assert_eq!(
            format!(
                "{:?}",
                FixedOffset::east_opt(86399)
                    .unwrap()
                    .ymd_opt(2012, 2, 29)
                    .unwrap()
                    .and_hms_opt(5, 6, 7)
                    .unwrap()
            ),
            "2012-02-29T05:06:07+23:59:59".to_string()
        );
        assert_eq!(
            format!("{:?}", FixedOffset::west_opt(86399).unwrap().ymd_opt(2012, 3, 4).unwrap()),
            "2012-03-04-23:59:59".to_string()
        );
        assert_eq!(
            format!(
                "{:?}",
                FixedOffset::west_opt(86399)
                    .unwrap()
                    .ymd_opt(2012, 3, 4)
                    .unwrap()
                    .and_hms_opt(5, 6, 7)
                    .unwrap()
            ),
            "2012-03-04T05:06:07-23:59:59".to_string()
        );
    }
}
