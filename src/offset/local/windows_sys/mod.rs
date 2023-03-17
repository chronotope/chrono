use std::{fmt, io::Error, ptr, result::Result};

use winapi::shared::minwindef::*;
use winapi::um::minwinbase::SYSTEMTIME;
use winapi::um::timezoneapi::*;

/// This macro calls a Windows API FFI and checks whether the function errored with the provided error_id. If an error returns,
/// the macro will return an `Error::last_os_error()`.
///
/// # Safety
///
/// This macro can only check one idea, and provided error ID must be the corresponding error ID.
macro_rules! windows_sys_call {
    ($name:ident($($arg:expr),*), $error_id:expr) => {
        if $name($($arg),*) == $error_id {
            return Err(Error::last_os_error());
        }
    }
}

const HECTONANOSECS_IN_SEC: i64 = 10_000_000;
const HECTONANOSEC_TO_UNIX_EPOCH: i64 = 11_644_473_600 * HECTONANOSECS_IN_SEC;

use crate::{Datelike, NaiveDateTime, Timelike};

/// Chrono's internal wrapper of Window's [SYSTEMTIME][spec] structure that
/// provides a variety of methods for interacting with Window's system calls
/// and `SYSTEMTIME`.
///
/// [spec]: https://learn.microsoft.com/en-us/windows/win32/api/minwinbase/ns-minwinbase-systemtime
pub(crate) struct WinSystemTime {
    inner: SYSTEMTIME,
}

impl fmt::Debug for WinSystemTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WinSystemTime")
            .field("year", &self.inner.wYear)
            .field("month", &self.inner.wMonth)
            .field("dayOfWeek", &self.inner.wDayOfWeek)
            .field("day", &self.inner.wDay)
            .field("hour", &self.inner.wHour)
            .field("minute", &self.inner.wMinute)
            .field("second", &self.inner.wSecond)
            .field("ms", &self.inner.wMilliseconds)
            .finish()
    }
}

impl WinSystemTime {
    /// Creates a new empty `WinSystemTime`.
    pub(crate) fn new() -> Self {
        let st = SYSTEMTIME {
            wYear: 0,
            wMonth: 0,
            wDayOfWeek: 0,
            wDay: 0,
            wHour: 0,
            wMinute: 0,
            wSecond: 0,
            wMilliseconds: 0,
        };

        Self { inner: st }
    }

    /// Creates a `WinSystemTime` from a [`NaiveDateTime`].
    pub(crate) fn from_naive_datetime(dt: &NaiveDateTime) -> Self {
        let st = SYSTEMTIME {
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
        };

        Self { inner: st }
    }

    /// Creates a `WinSystemTime` from an i64 unix seconds value.
    pub(crate) fn from_unix_seconds(seconds: i64) -> Result<Self, Error> {
        let t = ((seconds * HECTONANOSECS_IN_SEC) + HECTONANOSEC_TO_UNIX_EPOCH) as u64;
        let filetime = FILETIME { dwLowDateTime: t as u32, dwHighDateTime: (t >> 32) as u32 };
        let mut st = WinSystemTime::new();
        unsafe { windows_sys_call!(FileTimeToSystemTime(&filetime, st.mut_inner()), 0) };
        Ok(st)
    }

    /// Return `WinSystemTime`'s inner `SYSTEMTIME` struct.
    pub(crate) fn inner(&self) -> SYSTEMTIME {
        self.inner
    }

    /// Returns a mutable reference to `WinSystemTime`'s internal `SYSTEMTIME`
    pub(crate) fn mut_inner(&mut self) -> &mut SYSTEMTIME {
        &mut self.inner
    }

    /// Returns a new `WinSystemTime` representing the current `WinSystemTime` converted to utc time.
    pub(crate) fn as_utc_time(&self) -> Result<WinSystemTime, Error> {
        let mut sys_time = Self::new();
        unsafe {
            windows_sys_call!(
                TzSpecificLocalTimeToSystemTime(ptr::null(), &self.inner(), sys_time.mut_inner()),
                0
            )
        };
        Ok(sys_time)
    }

    /// Returns a new `WinSystemTime` representing the current `WinSystemTime` converted to the local timezone specific time.
    pub(crate) fn as_time_zone_specific(&self) -> Result<WinSystemTime, Error> {
        let mut local = WinSystemTime::new();
        unsafe {
            windows_sys_call!(
                SystemTimeToTzSpecificLocalTime(ptr::null(), &self.inner(), local.mut_inner()),
                0
            )
        };
        Ok(local)
    }

    /// Returns a Window's `FILETIME` struct representing the current `WinSystemTime`.
    pub(crate) fn as_file_time(&self) -> Result<FILETIME, Error> {
        let mut filetime = FILETIME { dwLowDateTime: 0, dwHighDateTime: 0 };
        unsafe { windows_sys_call!(SystemTimeToFileTime(&self.inner(), &mut filetime), 0) };
        Ok(filetime)
    }

    /// Returns a i64 value representing the unix seconds conversion of the current `WinSystemTime`.
    pub(crate) fn as_unix_seconds(&self) -> Result<i64, Error> {
        let filetime = self.as_file_time()?;
        // Convert filetime to u64 value
        let bit_shift = ((filetime.dwHighDateTime as u64) << 32) | (filetime.dwLowDateTime as u64);
        let unix_secs = (bit_shift as i64 - HECTONANOSEC_TO_UNIX_EPOCH) / HECTONANOSECS_IN_SEC;
        Ok(unix_secs)
    }
}
