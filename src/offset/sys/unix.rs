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
use std::{io, ptr};

#[cfg(not(any(
    all(target_os = "android", target_pointer_width = "32"),
    target_os = "nacl",
    target_os = "solaris",
    target_os = "illumos"
)))]
use libc::timegm;
#[cfg(all(target_os = "android", target_pointer_width = "32"))]
use libc::timegm64 as timegm;
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
fn localize(unix: i64, mut nanos: i32) -> DateTime<Local> {
    let mut tm = libc::tm {
        tm_sec: 0,
        tm_min: 0,
        tm_hour: 0,
        tm_mday: 0,
        tm_mon: 0,
        tm_year: 0,
        tm_wday: 0,
        tm_yday: 0,
        tm_isdst: 0,
        #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
        tm_gmtoff: 0,
        #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
        tm_zone: ptr::null_mut(),
    };

    unsafe {
        if libc::localtime_r(&(unix as time_t), &mut tm).is_null() {
            panic!("localtime_r failed: {}", io::Error::last_os_error());
        }
    }

    #[cfg(any(target_os = "solaris", target_os = "illumos"))]
    let offset = unsafe {
        tzset();
        // < 0 means we don't know; assume we're not in DST.
        if tm.tm_isdst == 0 {
            // timezone is seconds west of UTC, tm_gmtoff is seconds east
            -timezone
        } else if tm.tm_isdst > 0 {
            -altzone
        } else {
            -timezone
        }
    };
    #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
    let offset = tm.tm_gmtoff;

    if tm.tm_sec >= 60 {
        nanos += (tm.tm_sec - 59) * 1_000_000_000;
        tm.tm_sec = 59;
    }

    let date = NaiveDate::from_yo(tm.tm_year + 1900, tm.tm_yday as u32 + 1);
    let time = NaiveTime::from_hms_nano(
        tm.tm_hour as u32,
        tm.tm_min as u32,
        tm.tm_sec as u32,
        nanos as u32,
    );

    let offset = FixedOffset::east(offset as i32);
    DateTime::from_utc(date.and_time(time) - offset, offset)
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
