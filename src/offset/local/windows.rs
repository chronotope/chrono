// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::io::Error;
use std::result::Result;
use std::time::{SystemTime, UNIX_EPOCH};

use super::windows_sys::WinSystemTime;

use super::{FixedOffset, Local};
use crate::{DateTime, LocalResult, NaiveDate, NaiveDateTime, NaiveTime, Timelike};

pub(super) fn now() -> DateTime<Local> {
    InnerDuration::now_locally().datetime()
}

/// Converts a local `NaiveDateTime` to the `time::Timespec`.
pub(super) fn naive_to_local(d: &NaiveDateTime, local: bool) -> LocalResult<DateTime<Local>> {
    let naive_sys_time = WinSystemTime::from_naive_datetime(d);

    let local_sys_time = match local {
        false => LocalSysTime::from_utc_time(naive_sys_time),
        true => LocalSysTime::from_local_time(naive_sys_time),
    };

    if let Ok(mut local) = local_sys_time {
        assert_eq!(local.nsecs, 0);
        local.set_nsecs(d.nanosecond() as i32);

        return LocalResult::Single(local.datetime());
    }

    LocalResult::None
}

struct InnerDuration {
    sec: i64,
    nsec: i32,
}

impl InnerDuration {
    /// Constructs a new LocalSysTime representing the current time in UTC
    /// Constructs a timespec representing the current time in UTC.
    fn now_locally() -> LocalSysTime {
        let st =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
        let now_duration = Self { sec: st.as_secs() as i64, nsec: st.subsec_nanos() as i32 };
        LocalSysTime::from_duration(now_duration)
            .expect("Now should not fail to produce a local sys time")
    }

    fn from_seconds(sec: i64) -> Self {
        Self { sec, nsec: 0 }
    }
}

struct LocalSysTime {
    inner: WinSystemTime,
    offset: i32,
    nsecs: i32,
}

impl LocalSysTime {
    pub(crate) fn from_duration(dur: InnerDuration) -> Result<Self, Error> {
        let utc_sys_time = WinSystemTime::from_unix_seconds(dur.sec)?;

        let local_sys_time = utc_sys_time.as_time_zone_specific()?;
        let local_secs = local_sys_time.as_unix_seconds()?;

        let offset = (local_secs - dur.sec) as i32;

        Ok(Self { inner: local_sys_time, offset, nsecs: dur.nsec })
    }

    fn from_utc_time(utc_time: WinSystemTime) -> Result<Self, Error> {
        let duration = InnerDuration::from_seconds(utc_time.as_unix_seconds()?);
        Self::from_duration(duration)
    }

    fn from_local_time(local_time: WinSystemTime) -> Result<Self, Error> {
        let utc_time = local_time.as_utc_time()?;
        let duration = InnerDuration::from_seconds(utc_time.as_unix_seconds()?);
        Self::from_duration(duration)
    }

    fn set_nsecs(&mut self, nsecs: i32) {
        self.nsecs = nsecs;
    }

    fn datetime(self) -> DateTime<Local> {
        let st = self.inner.inner();

        let date =
            NaiveDate::from_ymd_opt(st.wYear as i32, st.wMonth as u32, st.wDay as u32).unwrap();
        let time = NaiveTime::from_hms_nano(
            st.wHour as u32,
            st.wMinute as u32,
            st.wSecond as u32,
            self.nsecs as u32,
        );

        let offset = FixedOffset::east_opt(self.offset).unwrap();
        DateTime::from_utc(date.and_time(time) - offset, offset)
    }
}
