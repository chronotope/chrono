// This is a part of rust-chrono.
// Copyright (c) 2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * The UTC (Coordinated Universal Time) time zone.
 */

use std::fmt;
use stdtime;

use duration::Duration;
use naive::date::NaiveDate;
use naive::time::NaiveTime;
use naive::datetime::NaiveDateTime;
use date::Date;
use datetime::DateTime;
use super::{Offset, OffsetState, LocalResult};

/// The UTC offset. This is the most efficient offset when you don't need the local time.
/// It is also used as an offset state (which is also a dummy type).
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct UTC;

impl UTC {
    /// Returns a `Date` which corresponds to the current date.
    pub fn today() -> Date<UTC> { UTC::now().date() }

    /// Returns a `DateTime` which corresponds to the current date.
    pub fn now() -> DateTime<UTC> {
        let spec = stdtime::get_time();
        let naive = NaiveDateTime::from_num_seconds_from_unix_epoch(spec.sec, spec.nsec as u32);
        DateTime::from_utc(naive, UTC)
    }
}

impl Offset for UTC {
    type State = UTC;

    fn from_state(_state: &UTC) -> UTC { UTC }

    fn state_from_local_date(&self, _local: &NaiveDate) -> LocalResult<UTC> {
        LocalResult::Single(UTC)
    }
    fn state_from_local_time(&self, _local: &NaiveTime) -> LocalResult<UTC> {
        LocalResult::Single(UTC)
    }
    fn state_from_local_datetime(&self, _local: &NaiveDateTime) -> LocalResult<UTC> {
        LocalResult::Single(UTC)
    }

    fn state_from_utc_date(&self, _utc: &NaiveDate) -> UTC { UTC }
    fn state_from_utc_time(&self, _utc: &NaiveTime) -> UTC { UTC }
    fn state_from_utc_datetime(&self, _utc: &NaiveDateTime) -> UTC { UTC}
}

impl OffsetState for UTC {
    fn local_minus_utc(&self) -> Duration { Duration::zero() }
}

impl fmt::Debug for UTC {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Z") }
}

impl fmt::Display for UTC {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "UTC") }
}

