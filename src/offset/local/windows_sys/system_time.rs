use std::{fmt, io::Error, ptr, result::Result};

use super::WinFileTime;

use winapi::um::minwinbase::SYSTEMTIME;
use winapi::um::timezoneapi::*;

use crate::{windows_sys_call, Datelike, NaiveDateTime, Timelike};

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

    pub(crate) fn from_naive_datetime(dt: &NaiveDateTime) -> Self {
        let st = SYSTEMTIME {
            wYear: dt.year() as u16,
            wMonth: dt.month() as u16,
            wDayOfWeek: (dt.weekday() as u16) + 1,
            wDay: dt.day() as u16,
            wHour: dt.hour() as u16,
            wMinute: dt.minute() as u16,
            wSecond: dt.second() as u16,
            wMilliseconds: 0,
        };

        Self { inner: st }
    }

    pub(crate) fn inner(&self) -> SYSTEMTIME {
        self.inner
    }

    pub(crate) fn mut_inner(&mut self) -> &mut SYSTEMTIME {
        &mut self.inner
    }

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

    pub(crate) fn as_file_time(&self) -> Result<WinFileTime, Error> {
        let mut filetime = WinFileTime::new();
        unsafe { windows_sys_call!(SystemTimeToFileTime(&self.inner(), filetime.mut_inner()), 0) };
        Ok(filetime)
    }
}
