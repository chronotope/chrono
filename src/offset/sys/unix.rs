// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::time::{SystemTime, UNIX_EPOCH};
use std::{io, mem, ptr};

use libc::{self, time_t};

use super::{DateTime, FixedOffset, Local, NaiveDate, NaiveDateTime, NaiveTime};
use crate::{Datelike, Timelike};

pub(super) fn now() -> DateTime<Local> {
    let st = SystemTime::now().duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
    localize(st.as_secs() as i64, st.subsec_nanos() as i32)
}

/// Converts a local `NaiveDateTime` to the `time::Timespec`.
pub(super) fn naive_to_local(d: &NaiveDateTime, local: bool) -> DateTime<Local> {
    let unix = match local {
        false => utc_naive_to_unix(d),
        true => local_naive_to_unix(d),
    };

    localize(unix, d.nanosecond() as i32)
}

/// Converts a `time::Tm` struct into the timezone-aware `DateTime`.
/// This assumes that `time` is working correctly, i.e. any error is fatal.
fn localize(unix: i64, nanos: i32) -> DateTime<Local> {
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

    unsafe {
        let mut out = mem::zeroed();
        if libc::localtime_r(&(unix as time_t), &mut out).is_null() {
            panic!("localtime_r failed: {}", io::Error::last_os_error());
        }
        #[cfg(any(target_os = "solaris", target_os = "illumos"))]
        let gmtoff = {
            tzset();
            // < 0 means we don't know; assume we're not in DST.
            if out.tm_isdst == 0 {
                // timezone is seconds west of UTC, tm_gmtoff is seconds east
                -timezone
            } else if out.tm_isdst > 0 {
                -altzone
            } else {
                -timezone
            }
        };
        #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
        let gmtoff = out.tm_gmtoff;

        tm.tm_sec = out.tm_sec;
        tm.tm_min = out.tm_min;
        tm.tm_hour = out.tm_hour;
        tm.tm_mday = out.tm_mday;
        tm.tm_mon = out.tm_mon;
        tm.tm_year = out.tm_year;
        tm.tm_wday = out.tm_wday;
        tm.tm_yday = out.tm_yday;
        tm.tm_isdst = out.tm_isdst;
        tm.tm_utcoff = gmtoff as i32;
    }

    tm.tm_nsec = nanos;
    if tm.tm_sec >= 60 {
        tm.tm_nsec += (tm.tm_sec - 59) * 1_000_000_000;
        tm.tm_sec = 59;
    }

    let date = NaiveDate::from_yo(tm.tm_year + 1900, tm.tm_yday as u32 + 1);
    let time = NaiveTime::from_hms_nano(
        tm.tm_hour as u32,
        tm.tm_min as u32,
        tm.tm_sec as u32,
        tm.tm_nsec as u32,
    );

    let offset = FixedOffset::east(tm.tm_utcoff);
    DateTime::from_utc(date.and_time(time) - offset, offset)
}

/// Holds a calendar date and time broken down into its components (year, month,
/// day, and so on), also called a broken-down time value.
// FIXME: use c_int instead of i32?
#[repr(C)]
struct Tm {
    /// Seconds after the minute - [0, 60]
    tm_sec: i32,

    /// Minutes after the hour - [0, 59]
    tm_min: i32,

    /// Hours after midnight - [0, 23]
    tm_hour: i32,

    /// Day of the month - [1, 31]
    tm_mday: i32,

    /// Months since January - [0, 11]
    tm_mon: i32,

    /// Years since 1900
    tm_year: i32,

    /// Days since Sunday - [0, 6]. 0 = Sunday, 1 = Monday, ..., 6 = Saturday.
    tm_wday: i32,

    /// Days since January 1 - [0, 365]
    tm_yday: i32,

    /// Daylight Saving Time flag.
    ///
    /// This value is positive if Daylight Saving Time is in effect, zero if
    /// Daylight Saving Time is not in effect, and negative if this information
    /// is not available.
    tm_isdst: i32,

    /// Identifies the time zone that was used to compute this broken-down time
    /// value, including any adjustment for Daylight Saving Time. This is the
    /// number of seconds east of UTC. For example, for U.S. Pacific Daylight
    /// Time, the value is `-7*60*60 = -25200`.
    tm_utcoff: i32,

    /// Nanoseconds after the second - [0, 10<sup>9</sup> - 1]
    tm_nsec: i32,
}

#[cfg(any(target_os = "solaris", target_os = "illumos"))]
extern "C" {
    static timezone: time_t;
    static altzone: time_t;
}

#[cfg(any(target_os = "solaris", target_os = "illumos"))]
fn tzset() {
    extern "C" {
        fn tzset();
    }
    unsafe { tzset() }
}

#[cfg(any(target_os = "nacl", target_os = "solaris", target_os = "illumos"))]
unsafe fn timegm(tm: *mut libc::tm) -> time_t {
    use std::env::{remove_var, set_var, var_os};
    extern "C" {
        fn tzset();
    }

    let ret;

    let current_tz = var_os("TZ");
    set_var("TZ", "UTC");
    tzset();

    ret = libc::mktime(tm);

    if let Some(tz) = current_tz {
        set_var("TZ", tz);
    } else {
        remove_var("TZ");
    }
    tzset();

    ret
}

fn utc_naive_to_unix(d: &NaiveDateTime) -> i64 {
    #[cfg(not(any(
        all(target_os = "android", target_pointer_width = "32"),
        target_os = "nacl",
        target_os = "solaris",
        target_os = "illumos"
    )))]
    use libc::timegm;
    #[cfg(all(target_os = "android", target_pointer_width = "32"))]
    use libc::timegm64 as timegm;

    let mut tm = naive_to_tm(d);
    unsafe { timegm(&mut tm) as i64 }
}

fn local_naive_to_unix(d: &NaiveDateTime) -> i64 {
    let mut tm = naive_to_tm(d);
    unsafe { libc::mktime(&mut tm) as i64 }
}

fn naive_to_tm(d: &NaiveDateTime) -> libc::tm {
    libc::tm {
        tm_sec: d.second() as i32,
        tm_min: d.minute() as i32,
        tm_hour: d.hour() as i32,
        tm_mday: d.day() as i32,
        tm_mon: d.month0() as i32,
        tm_year: d.year() - 1900,
        tm_wday: 0, // to_local ignores this
        tm_yday: 0, // and this
        tm_isdst: -1,
        #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
        tm_gmtoff: 0,
        #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
        tm_zone: ptr::null_mut(),
    }
}
