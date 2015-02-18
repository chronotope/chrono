// This is a part of rust-chrono.
// Copyright (c) 2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * The local (system) time zone.
 */

use stdtime;

use {Datelike, Timelike};
use duration::Duration;
use naive::date::NaiveDate;
use naive::time::NaiveTime;
use naive::datetime::NaiveDateTime;
use date::Date;
use time::Time;
use datetime::DateTime;
use super::{TimeZone, LocalResult};
use super::fixed::FixedOffset;

/// Converts a `time::Tm` struct into the timezone-aware `DateTime`.
/// This assumes that `time` is working correctly, i.e. any error is fatal.
fn tm_to_datetime(mut tm: stdtime::Tm) -> DateTime<Local> {
    if tm.tm_sec >= 60 {
        tm.tm_sec = 59;
        tm.tm_nsec += (tm.tm_sec - 59) * 1_000_000_000;
    }

    // from_yo is more efficient than from_ymd (since it's the internal representation).
    let date = NaiveDate::from_yo(tm.tm_year + 1900, tm.tm_yday as u32 + 1);
    let time = NaiveTime::from_hms_nano(tm.tm_hour as u32, tm.tm_min as u32,
                                        tm.tm_sec as u32, tm.tm_nsec as u32);
    let offset = FixedOffset::east(tm.tm_utcoff);
    DateTime::from_utc(date.and_time(time) + Duration::seconds(-tm.tm_utcoff as i64), offset)
}

/// Converts a local `NaiveDateTime` to the `time::Timespec`.
fn datetime_to_timespec(d: &NaiveDateTime) -> stdtime::Timespec {
    let tm = stdtime::Tm {
        tm_sec: d.second() as i32,
        tm_min: d.minute() as i32,
        tm_hour: d.hour() as i32,
        tm_mday: d.day() as i32,
        tm_mon: d.month0() as i32, // yes, C is that strange...
        tm_year: d.year() - 1900, // this doesn't underflow, we know that d is `NaiveDateTime`.
        tm_wday: 0, // to_local ignores this
        tm_yday: 0, // and this
        tm_isdst: -1,
        tm_utcoff: 1, // this is arbitrary but should be nonzero
                      // in order to make `to_timespec` use `rust_mktime` internally.
        tm_nsec: d.nanosecond() as i32,
    };
    tm.to_timespec()
}

/// The local timescale. This is implemented via the standard `time` crate.
#[derive(Copy, Clone)]
pub struct Local;

impl Local {
    /// Returns a `Date` which corresponds to the current date.
    pub fn today() -> Date<Local> {
        Local::now().date()
    }

    /// Returns a `DateTime` which corresponds to the current date.
    pub fn now() -> DateTime<Local> {
        tm_to_datetime(stdtime::now())
    }
}

impl TimeZone for Local {
    type Offset = FixedOffset;

    fn from_offset(_offset: &FixedOffset) -> Local { Local }

    // they are easier to define in terms of the finished date and time unlike other offsets
    fn offset_from_local_date(&self, local: &NaiveDate) -> LocalResult<FixedOffset> {
        self.from_local_date(local).map(|&: date| *date.offset())
    }
    fn offset_from_local_time(&self, local: &NaiveTime) -> LocalResult<FixedOffset> {
        self.from_local_time(local).map(|&: time| *time.offset())
    }
    fn offset_from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        self.from_local_datetime(local).map(|&: datetime| *datetime.offset())
    }

    fn offset_from_utc_date(&self, utc: &NaiveDate) -> FixedOffset {
        *self.from_utc_date(utc).offset()
    }
    fn offset_from_utc_time(&self, utc: &NaiveTime) -> FixedOffset {
        *self.from_utc_time(utc).offset()
    }
    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> FixedOffset {
        *self.from_utc_datetime(utc).offset()
    }

    // override them for avoiding redundant works
    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<Local>> {
        self.from_local_datetime(&local.and_hms(0, 0, 0)).map(|datetime| datetime.date())
    }
    fn from_local_time(&self, _local: &NaiveTime) -> LocalResult<Time<Local>> {
        LocalResult::None // we have no information about this time
    }
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Local>> {
        let timespec = datetime_to_timespec(local);
        LocalResult::Single(tm_to_datetime(stdtime::at(timespec)))
    }

    fn from_utc_date(&self, utc: &NaiveDate) -> Date<Local> {
        self.from_utc_datetime(&utc.and_hms(0, 0, 0)).date()
    }
    fn from_utc_time(&self, _utc: &NaiveTime) -> Time<Local> {
        unimplemented!() // we have no information about this time
    }
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Local> {
        let timespec = datetime_to_timespec(utc);
        tm_to_datetime(stdtime::at_utc(timespec))
    }
}

