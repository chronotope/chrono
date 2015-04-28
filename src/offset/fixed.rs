// This is a part of rust-chrono.
// Copyright (c) 2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * The time zone which has a fixed offset from UTC.
 */

use std::fmt;

use div::div_mod_floor;
use duration::Duration;
use naive::date::NaiveDate;
use naive::datetime::NaiveDateTime;
use super::{TimeZone, Offset, LocalResult};

/// The time zone with fixed offset, from UTC-23:59:59 to UTC+23:59:59.
#[derive(Copy, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "rustc-serialize", derive(RustcEncodable, RustcDecodable))]
pub struct FixedOffset {
    local_minus_utc: i32,
}

impl FixedOffset {
    /// Makes a new `FixedOffset` for the Eastern Hemisphere with given timezone difference.
    /// The negative `secs` means the Western Hemisphere.
    ///
    /// Fails on the out-of-bound `secs`.
    pub fn east(secs: i32) -> FixedOffset {
        FixedOffset::east_opt(secs).expect("FixedOffset::east out of bounds")
    }

    /// Makes a new `FixedOffset` for the Eastern Hemisphere with given timezone difference.
    /// The negative `secs` means the Western Hemisphere.
    ///
    /// Returns `None` on the out-of-bound `secs`.
    pub fn east_opt(secs: i32) -> Option<FixedOffset> {
        if -86400 < secs && secs < 86400 {
            Some(FixedOffset { local_minus_utc: secs })
        } else {
            None
        }
    }

    /// Makes a new `FixedOffset` for the Western Hemisphere with given timezone difference.
    /// The negative `secs` means the Eastern Hemisphere.
    ///
    /// Fails on the out-of-bound `secs`.
    pub fn west(secs: i32) -> FixedOffset {
        FixedOffset::west_opt(secs).expect("FixedOffset::west out of bounds")
    }

    /// Makes a new `FixedOffset` for the Western Hemisphere with given timezone difference.
    /// The negative `secs` means the Eastern Hemisphere.
    ///
    /// Returns `None` on the out-of-bound `secs`.
    pub fn west_opt(secs: i32) -> Option<FixedOffset> {
        if -86400 < secs && secs < 86400 {
            Some(FixedOffset { local_minus_utc: -secs })
        } else {
            None
        }
    }
}

impl TimeZone for FixedOffset {
    type Offset = FixedOffset;

    fn from_offset(offset: &FixedOffset) -> FixedOffset { offset.clone() }

    fn offset_from_local_date(&self, _local: &NaiveDate) -> LocalResult<FixedOffset> {
        LocalResult::Single(self.clone())
    }
    fn offset_from_local_datetime(&self, _local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        LocalResult::Single(self.clone())
    }

    fn offset_from_utc_date(&self, _utc: &NaiveDate) -> FixedOffset { self.clone() }
    fn offset_from_utc_datetime(&self, _utc: &NaiveDateTime) -> FixedOffset { self.clone() }
}

impl Offset for FixedOffset {
    fn local_minus_utc(&self) -> Duration { Duration::seconds(self.local_minus_utc as i64) }
}

impl fmt::Debug for FixedOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let offset = self.local_minus_utc;
        let (sign, offset) = if offset < 0 {('-', -offset)} else {('+', offset)};
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(self, f) }
}

