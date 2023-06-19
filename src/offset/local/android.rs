use super::{FixedOffset, NaiveDateTime};
use crate::traits::{Datelike, Timelike};
use crate::LocalResult;
use libc::{c_char, c_void, dlsym, localtime_r, mktime, time_t, tm, RTLD_DEFAULT};
use once_cell::sync::Lazy;
use std::io;
use std::mem::{self, transmute};
use std::ops::Deref;
use std::ptr::null;

enum Timezone {}

#[allow(non_camel_case_types)]
type timezone_t = *mut Timezone;

/// Timezone access functions added in API level 35. These are prefereable to `localtime_r` /
/// `mktime` if they are available, as they don't access environment variables and so avoid any
/// potential thread-safety issues with them.
struct TimezoneFunctions {
    localtime_rz: unsafe extern "C" fn(timezone_t, *const time_t, *mut tm) -> *mut tm,
    mktime_z: unsafe extern "C" fn(timezone_t, *mut tm) -> time_t,
    tzalloc: unsafe extern "C" fn(*const c_char) -> timezone_t,
    tzfree: unsafe extern "C" fn(timezone_t),
}

impl TimezoneFunctions {
    /// Loads the functions dynamically from libc if they are available, or returns `None` if any of
    /// the functions is not available.
    fn load() -> Option<Self> {
        // Safe because we give dlsym valid arguments, check all the return values for nulls, and
        // cast the function pointers to the correct types as defined in Bionic libc.
        unsafe {
            let localtime_rz = dlsym(RTLD_DEFAULT, b"localtime_rz\0".as_ptr());
            let mktime_z = dlsym(RTLD_DEFAULT, b"mktime_z\0".as_ptr());
            let tzalloc = dlsym(RTLD_DEFAULT, b"tzalloc\0".as_ptr());
            let tzfree = dlsym(RTLD_DEFAULT, b"tzfree\0".as_ptr());
            if localtime_rz.is_null() || mktime_z.is_null() || tzalloc.is_null() || tzfree.is_null()
            {
                return None;
            }
            Some(Self {
                localtime_rz: transmute::<*mut c_void, _>(localtime_rz),
                mktime_z: transmute::<*mut c_void, _>(mktime_z),
                tzalloc: transmute::<*mut c_void, _>(tzalloc),
                tzfree: transmute::<*mut c_void, _>(tzfree),
            })
        }
    }
}

static TZ_FUNCTIONS: Lazy<Option<TimezoneFunctions>> = Lazy::new(|| TimezoneFunctions::load());

pub(super) fn offset_from_utc_datetime(utc: &NaiveDateTime) -> LocalResult<FixedOffset> {
    let time = utc.timestamp() as time_t;
    // Safe because an all-zero `struct tm` is valid.
    let mut result = unsafe { mem::zeroed() };

    if let Some(tz_functions) = TZ_FUNCTIONS.deref() {
        // Safe because:
        // - tzalloc accepts a null pointer to use the current system timezone.
        // - localtime_rz only accesses the pointers passed to it during the call, which are valid
        //   at that point.
        // - tzfree is only called after the timezone_t is no longer used.
        unsafe {
            let timezone = (tz_functions.tzalloc)(null());
            if timezone.is_null() {
                panic!("tzalloc failed: {}", io::Error::last_os_error());
            }
            if (tz_functions.localtime_rz)(timezone, &time, &mut result).is_null() {
                panic!("localtime_rz failed: {}", io::Error::last_os_error());
            }
            (tz_functions.tzfree)(timezone);
        }
    } else {
        // Safe because localtime_r only accesses the pointers passed to it during the call. It does
        // also try to read the `TZ` environment variable, but we can assume it's not set on Android
        // as the timezone is read from a system property instead.
        unsafe {
            if localtime_r(&time, &mut result).is_null() {
                panic!("localtime_r failed: {}", io::Error::last_os_error());
            }
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
    let timestamp;
    if let Some(tz_functions) = TZ_FUNCTIONS.deref() {
        // Safe because:
        // - tzalloc accepts a null pointer to use the current system timezone.
        // - mktime only accesses the struct tm it is passed during the call, and doesn't store the
        //   pointer to access later. The tm_zone it sets may only be valid as long as the timezone
        //   is, but that's fine as we don't access tm_zone.
        // - tzfree is only called after the timezone_t is no longer used.
        unsafe {
            let timezone = (tz_functions.tzalloc)(null());
            if timezone.is_null() {
                panic!("tzalloc failed: {}", io::Error::last_os_error());
            }
            timestamp = (tz_functions.mktime_z)(timezone, &mut tm);
            (tz_functions.tzfree)(timezone);
        }
    } else {
        // Safe because mktime only accesses the struct it is passed during the call, and doesn't
        // store the pointer to access later. It does also try to read the `TZ` environment
        // variable, but we can assume it's not set on Android as the timezone is read from a system
        // property instead.
        timestamp = unsafe { mktime(&mut tm) };
    }
    (timestamp, tm.tm_isdst)
}
