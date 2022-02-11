// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::Tm;
use libc::{self, time_t};
use std::mem;

fn rust_tm_to_tm(rust_tm: &Tm, tm: &mut libc::tm) {
    tm.tm_sec = rust_tm.tm_sec;
    tm.tm_min = rust_tm.tm_min;
    tm.tm_hour = rust_tm.tm_hour;
    tm.tm_mday = rust_tm.tm_mday;
    tm.tm_mon = rust_tm.tm_mon;
    tm.tm_year = rust_tm.tm_year;
    tm.tm_wday = rust_tm.tm_wday;
    tm.tm_yday = rust_tm.tm_yday;
    tm.tm_isdst = rust_tm.tm_isdst;
}

fn tm_to_rust_tm(tm: &libc::tm, utcoff: i32, rust_tm: &mut Tm) {
    rust_tm.tm_sec = tm.tm_sec;
    rust_tm.tm_min = tm.tm_min;
    rust_tm.tm_hour = tm.tm_hour;
    rust_tm.tm_mday = tm.tm_mday;
    rust_tm.tm_mon = tm.tm_mon;
    rust_tm.tm_year = tm.tm_year;
    rust_tm.tm_wday = tm.tm_wday;
    rust_tm.tm_yday = tm.tm_yday;
    rust_tm.tm_isdst = tm.tm_isdst;
    rust_tm.tm_utcoff = utcoff;
}

pub fn time_to_local_tm(sec: i64, tm: &mut Tm) {
    let out = rl_localtime::localtime(sec as time_t)
        .unwrap_or_else(|error| {
            panic!("localtime_r failed: {}", error);
        });

    let gmtoff = out.tm_gmtoff;
    tm_to_rust_tm(&out, gmtoff as i32, tm);
}

pub fn utc_tm_to_time(rust_tm: &Tm) -> i64 {
    let mut tm = unsafe { mem::zeroed() };
    rust_tm_to_tm(rust_tm, &mut tm);
    rl_localtime::timegm(tm) as i64
}

pub fn local_tm_to_time(rust_tm: &Tm) -> i64 {
    let mut tm = unsafe { mem::zeroed() };
    rust_tm_to_tm(rust_tm, &mut tm);
    rl_localtime::mktime(tm) as i64
}
