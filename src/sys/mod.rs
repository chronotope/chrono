// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Platform wrappers for converting UTC times to and from the local time zone.
//!
//! This code was rescued from v0.1 of the time crate, which is no longer
//! maintained. It has been substantially stripped down to the bare minimum
//! required by chrono.

use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(all(not(unix), not(windows)))]
#[path = "stub.rs"]
mod inner;

#[cfg(all(windows, not(target_arch = "wasm32"), not(target_env = "sgx")))]
#[path = "windows.rs"]
mod inner;

use inner::{local_tm_to_time, time_to_local_tm, utc_tm_to_time};

/// A record specifying a time value in seconds and nanoseconds, where
/// nanoseconds represent the offset from the given second.
///
/// For example a timespec of 1.2 seconds after the beginning of the epoch would
/// be represented as {sec: 1, nsec: 200000000}.
pub(crate) struct Timespec {
    pub(crate) sec: i64,
    pub(crate) nsec: i32,
}

impl Timespec {
    /// Constructs a timespec representing the current time in UTC.
    pub(crate) fn now() -> Timespec {
        let st =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
        Timespec { sec: st.as_secs() as i64, nsec: st.subsec_nanos() as i32 }
    }

    /// Converts this timespec into the system's local time.
    pub(crate) fn local(self) -> Tm {
        let mut tm = Tm {
            tm_sec: 0,
            tm_min: 0,
            tm_hour: 0,
            tm_mday: 0,
            tm_mon: 0,
            tm_year: 0,
            tm_wday: 0,
            tm_yday: 0,
            tm_isdst: 0,
            tm_utcoff: 0,
            tm_nsec: 0,
        };
        time_to_local_tm(self.sec, &mut tm);
        tm.tm_nsec = self.nsec;
        tm
    }
}

/// Holds a calendar date and time broken down into its components (year, month,
/// day, and so on), also called a broken-down time value.
// FIXME: use c_int instead of i32?
#[cfg(feature = "clock")]
#[repr(C)]
pub(crate) struct Tm {
    /// Seconds after the minute - [0, 60]
    pub(crate) tm_sec: i32,

    /// Minutes after the hour - [0, 59]
    pub(crate) tm_min: i32,

    /// Hours after midnight - [0, 23]
    pub(crate) tm_hour: i32,

    /// Day of the month - [1, 31]
    pub(crate) tm_mday: i32,

    /// Months since January - [0, 11]
    pub(crate) tm_mon: i32,

    /// Years since 1900
    pub(crate) tm_year: i32,

    /// Days since Sunday - [0, 6]. 0 = Sunday, 1 = Monday, ..., 6 = Saturday.
    pub(crate) tm_wday: i32,

    /// Days since January 1 - [0, 365]
    pub(crate) tm_yday: i32,

    /// Daylight Saving Time flag.
    ///
    /// This value is positive if Daylight Saving Time is in effect, zero if
    /// Daylight Saving Time is not in effect, and negative if this information
    /// is not available.
    pub(crate) tm_isdst: i32,

    /// Identifies the time zone that was used to compute this broken-down time
    /// value, including any adjustment for Daylight Saving Time. This is the
    /// number of seconds east of UTC. For example, for U.S. Pacific Daylight
    /// Time, the value is `-7*60*60 = -25200`.
    pub(crate) tm_utcoff: i32,

    /// Nanoseconds after the second - [0, 10<sup>9</sup> - 1]
    pub(crate) tm_nsec: i32,
}

impl Tm {
    /// Convert time to the seconds from January 1, 1970
    pub(crate) fn to_timespec(&self) -> Timespec {
        let sec = match self.tm_utcoff {
            0 => utc_tm_to_time(self),
            _ => local_tm_to_time(self),
        };
        Timespec { sec, nsec: self.tm_nsec }
    }
}
