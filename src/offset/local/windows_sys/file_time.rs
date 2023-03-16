use std::{io::Error, result::Result};

use super::WinSystemTime;
use crate::windows_sys_call;

use winapi::shared::minwindef::*;
use winapi::um::timezoneapi::*;

const HECTONANOSECS_IN_SEC: i64 = 10_000_000;
const HECTONANOSEC_TO_UNIX_EPOCH: i64 = 11_644_473_600 * HECTONANOSECS_IN_SEC;

pub(crate) struct WinFileTime {
    inner: FILETIME,
}

impl WinFileTime {
    pub(crate) fn new() -> Self {
        let ft = FILETIME { dwLowDateTime: 0, dwHighDateTime: 0 };
        Self { inner: ft }
    }

    pub(crate) fn inner(&self) -> FILETIME {
        self.inner
    }

    pub(crate) fn from_seconds(sec: i64) -> Self {
        let t = ((sec * HECTONANOSECS_IN_SEC) + HECTONANOSEC_TO_UNIX_EPOCH) as u64;
        let ft = FILETIME { dwLowDateTime: t as u32, dwHighDateTime: (t >> 32) as u32 };
        Self { inner: ft }
    }

    pub(crate) fn mut_inner(&mut self) -> &mut FILETIME {
        &mut self.inner
    }

    pub(crate) const fn as_unix_seconds(&self) -> i64 {
        let t = self.as_u64() as i64;
        (t - HECTONANOSEC_TO_UNIX_EPOCH) / HECTONANOSECS_IN_SEC
    }

    pub(crate) const fn as_u64(&self) -> u64 {
        ((self.inner.dwHighDateTime as u64) << 32) | (self.inner.dwLowDateTime as u64)
    }

    pub(crate) fn as_system_time(&self) -> Result<WinSystemTime, Error> {
        let mut st = WinSystemTime::new();
        unsafe { windows_sys_call!(FileTimeToSystemTime(&self.inner(), st.mut_inner()), 0) };
        Ok(st)
    }
}
