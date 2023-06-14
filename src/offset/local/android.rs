use super::{FixedOffset, NaiveDateTime};
use crate::traits::{Datelike, Timelike};
use crate::LocalResult;
use libc::{localtime_r, mktime, time_t};
use std::io;
use std::mem;
use std::ptr::null;

pub(super) fn offset_from_utc_datetime(utc: &NaiveDateTime) -> LocalResult<FixedOffset> {
    let time = utc.timestamp() as time_t;
    // Safe because an all-zero `struct tm` is valid.
    let mut result = unsafe { mem::zeroed() };
    // Safe because localtime_r only accesses the pointers passed to it during the call. It does
    // also try to read the `TZ` environment variable, but we can assume it's not set on Android as
    // the timezone is read from a system property instead.
    unsafe {
        if localtime_r(&time, &mut result).is_null() {
            panic!("localtime_r failed: {}", io::Error::last_os_error());
        }
    }
    LocalResult::Single(
        FixedOffset::east_opt(
            result.tm_gmtoff.try_into().expect("localtime_r returned invalid UTC offset"),
        )
        .expect("localtime_r returned invalid UTC offset"),
    )
}

pub(super) fn offset_from_local_datetime(local: &NaiveDateTime) -> LocalResult<FixedOffset> {
    // Calling mktime with different isdst values allows us to detect the ambiguous case where DST
    // ends.
    let (utc_timestamp, isdst) = mktime_with_dst(local, -1);
    let (utc_timestamp0, isdst0) = mktime_with_dst(local, 0);
    let (utc_timestamp1, isdst1) = mktime_with_dst(local, 1);
    if utc_timestamp == -1 {
        LocalResult::None
    } else if isdst0 == isdst1 {
        LocalResult::Single(offset_from_timestamp(local, utc_timestamp))
    } else {
        LocalResult::Ambiguous(
            offset_from_timestamp(local, utc_timestamp0),
            offset_from_timestamp(local, utc_timestamp1),
        )
    }
}

fn offset_from_timestamp(local: &NaiveDateTime, utc_timestamp: time_t) -> FixedOffset {
    FixedOffset::east_opt(
        (local.timestamp() - utc_timestamp).try_into().expect("Invalid UTC offset"),
    )
    .expect("Invalid UTC offset")
}

/// Calls `mktime` from libc with the given local date-time and isdst value.
///
/// Returns the timestamp and new isdst value set by `mktime`.
fn mktime_with_dst(local: &NaiveDateTime, isdst: i32) -> (time_t, i32) {
    let mut tm = libc::tm {
        tm_sec: local.second() as i32,
        tm_min: local.minute() as i32,
        tm_hour: local.hour() as i32,
        tm_mday: local.day() as i32,
        tm_mon: local.month0() as i32,
        tm_year: local.year() - 1900,
        tm_wday: 0,
        tm_yday: 0,
        tm_isdst: isdst,
        tm_gmtoff: 0,
        tm_zone: null(),
    };
    // Safe because mktime only accesses struct it is passed during the call, and doesn't store the
    // pointer to access later. It does also try to read the `TZ` environment variable, but we can
    // assume it's not set on Android as the timezone is read from a system property instead.
    let timestamp = unsafe { mktime(&mut tm) };
    (timestamp, tm.tm_isdst)
}
