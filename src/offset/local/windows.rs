// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::mem::MaybeUninit;
use std::io::Error;
use std::ptr;
use std::result::Result;

use winapi::shared::minwindef::FILETIME;
use winapi::um::minwinbase::SYSTEMTIME;
use winapi::um::timezoneapi::{
    SystemTimeToFileTime, SystemTimeToTzSpecificLocalTime, TzSpecificLocalTimeToSystemTime,
};

use super::FixedOffset;
use crate::{Datelike, LocalResult, NaiveDateTime, Timelike};

/// This macro calls a Windows API FFI and checks whether the function errored with the provided error_id. If an error returns,
/// the macro will return an `Error::last_os_error()`.
///
/// # Safety
///
/// The provided error ID must align with the provided Windows API, providing the wrong ID could lead to UB.
macro_rules! windows_sys_call {
    ($name:ident($($arg:expr),*), $error_id:expr) => {
        if $name($($arg),*) == $error_id {
            return Err(Error::last_os_error());
        }
    }
}

const HECTONANOSECS_IN_SEC: i64 = 10_000_000;
const HECTONANOSEC_TO_UNIX_EPOCH: i64 = 11_644_473_600 * HECTONANOSECS_IN_SEC;

pub(super) fn offset_from_utc_datetime(utc: &NaiveDateTime) -> LocalResult<FixedOffset> {
    offset(utc, false)
}

pub(super) fn offset_from_local_datetime(local: &NaiveDateTime) -> LocalResult<FixedOffset> {
    offset(local, true)
}

/// Converts a local `NaiveDateTime` to the `time::Timespec`.
pub(super) fn offset(d: &NaiveDateTime, local: bool) -> LocalResult<FixedOffset> {
    let naive_sys_time = system_time_from_naive_date_time(d);

    let local_sys_time = match local {
        false => from_utc_time(naive_sys_time),
        true => from_local_time(naive_sys_time),
    };

    if let Ok(offset) = local_sys_time {
        return LocalResult::Single(offset);
    }
    LocalResult::None
}

fn from_utc_time(utc_time: SYSTEMTIME) -> Result<FixedOffset, Error> {
    let local_time = utc_to_local_time(&utc_time)?;
    let utc_secs = system_time_as_unix_seconds(&utc_time)?;
    let local_secs = system_time_as_unix_seconds(&local_time)?;
    let offset = (local_secs - utc_secs) as i32;
    Ok(FixedOffset::east_opt(offset).unwrap())
}

fn from_local_time(local_time: SYSTEMTIME) -> Result<FixedOffset, Error> {
    let utc_time = local_to_utc_time(&local_time)?;
    let utc_secs = system_time_as_unix_seconds(&utc_time)?;
    let local_secs = system_time_as_unix_seconds(&local_time)?;
    let offset = (local_secs - utc_secs) as i32;
    Ok(FixedOffset::east_opt(offset).unwrap())
}

fn system_time_from_naive_date_time(dt: &NaiveDateTime) -> SYSTEMTIME {
    SYSTEMTIME {
        // Valid values: 1601-30827
        wYear: dt.year() as u16,
        // Valid values:1-12
        wMonth: dt.month() as u16,
        // Valid values: 0-6, starting Sunday.
        // NOTE: enum returns 1-7, starting Monday, so we are
        // off here, but this is not currently used in local.
        wDayOfWeek: dt.weekday() as u16,
        // Valid values: 1-31
        wDay: dt.day() as u16,
        // Valid values: 0-23
        wHour: dt.hour() as u16,
        // Valid values: 0-59
        wMinute: dt.minute() as u16,
        // Valid values: 0-59
        wSecond: dt.second() as u16,
        // Valid values: 0-999
        wMilliseconds: 0,
    }
}

pub(crate) fn local_to_utc_time(local: &SYSTEMTIME) -> Result<SYSTEMTIME, Error> {
    let mut sys_time = MaybeUninit::<SYSTEMTIME>::uninit();
    unsafe {
        windows_sys_call!(
            TzSpecificLocalTimeToSystemTime(ptr::null(), local, sys_time.as_mut_ptr()),
            0
        )
    };
    // SAFETY: TzSpecificLocalTimeToSystemTime must have succeeded at this point, so we can
    // assume the value is initialized.
    Ok(unsafe { sys_time.assume_init() })
}

pub(crate) fn utc_to_local_time(utc_time: &SYSTEMTIME) -> Result<SYSTEMTIME, Error> {
    let mut local = MaybeUninit::<SYSTEMTIME>::uninit();
    unsafe {
        windows_sys_call!(
            SystemTimeToTzSpecificLocalTime(ptr::null(), utc_time, local.as_mut_ptr()),
            0
        )
    };
    // SAFETY: SystemTimeToTzSpecificLocalTime must have succeeded at this point, so we can
    // assume the value is initialized.
    Ok(unsafe { local.assume_init() })
}

/// Returns a i64 value representing the unix seconds conversion of the current `WinSystemTime`.
pub(crate) fn system_time_as_unix_seconds(st: &SYSTEMTIME) -> Result<i64, Error> {
    let mut init = MaybeUninit::<FILETIME>::uninit();
    unsafe { windows_sys_call!(SystemTimeToFileTime(st, init.as_mut_ptr()), 0) }
    // SystemTimeToFileTime must have succeeded at this point, so we can assum the value is
    // initalized.
    let filetime = unsafe { init.assume_init() };
    let bit_shift = ((filetime.dwHighDateTime as u64) << 32) | (filetime.dwLowDateTime as u64);
    let unix_secs = (bit_shift as i64 - HECTONANOSEC_TO_UNIX_EPOCH) / HECTONANOSECS_IN_SEC;
    Ok(unix_secs)
}
