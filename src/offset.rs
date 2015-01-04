// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * Offsets from the local time to UTC.
 */

use std::borrow::IntoCow;
use std::fmt;
use std::str::SendStr;
use stdtime;

use {Weekday, Datelike, Timelike};
use div::div_mod_floor;
use duration::Duration;
use naive::date::NaiveDate;
use naive::time::NaiveTime;
use naive::datetime::NaiveDateTime;
use date::Date;
use time::Time;
use datetime::DateTime;

/// The conversion result from the local time to the timezone-aware datetime types.
#[derive(Clone, PartialEq, Show)]
pub enum LocalResult<T> {
    /// Given local time representation is invalid.
    /// This can occur when, for example, the positive timezone transition.
    None,
    /// Given local time representation has a single unique result.
    Single(T),
    /// Given local time representation has multiple results and thus ambiguous.
    /// This can occur when, for example, the negative timezone transition.
    Ambiguous(T /*min*/, T /*max*/),
}

impl<T> LocalResult<T> {
    /// Returns `Some` only when the conversion result is unique, or `None` otherwise.
    pub fn single(self) -> Option<T> {
        match self { LocalResult::Single(t) => Some(t), _ => None }
    }

    /// Returns `Some` for the earliest possible conversion result, or `None` if none.
    pub fn earliest(self) -> Option<T> {
        match self { LocalResult::Single(t) | LocalResult::Ambiguous(t,_) => Some(t), _ => None }
    }

    /// Returns `Some` for the latest possible conversion result, or `None` if none.
    pub fn latest(self) -> Option<T> {
        match self { LocalResult::Single(t) | LocalResult::Ambiguous(_,t) => Some(t), _ => None }
    }
}

impl<Off:Offset> LocalResult<Date<Off>> {
    /// Makes a new `DateTime` from the current date and given `NaiveTime`.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    pub fn and_time(self, time: NaiveTime) -> LocalResult<DateTime<Off>> {
        match self {
            LocalResult::Single(d) => d.and_time(time)
                                       .map_or(LocalResult::None, LocalResult::Single),
            _ => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the current date, hour, minute and second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    pub fn and_hms_opt(self, hour: u32, min: u32, sec: u32) -> LocalResult<DateTime<Off>> {
        match self {
            LocalResult::Single(d) => d.and_hms_opt(hour, min, sec)
                                       .map_or(LocalResult::None, LocalResult::Single),
            _ => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    pub fn and_hms_milli_opt(self, hour: u32, min: u32, sec: u32,
                             milli: u32) -> LocalResult<DateTime<Off>> {
        match self {
            LocalResult::Single(d) => d.and_hms_milli_opt(hour, min, sec, milli)
                                       .map_or(LocalResult::None, LocalResult::Single),
            _ => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    pub fn and_hms_micro_opt(self, hour: u32, min: u32, sec: u32,
                             micro: u32) -> LocalResult<DateTime<Off>> {
        match self {
            LocalResult::Single(d) => d.and_hms_micro_opt(hour, min, sec, micro)
                                       .map_or(LocalResult::None, LocalResult::Single),
            _ => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    pub fn and_hms_nano_opt(self, hour: u32, min: u32, sec: u32,
                            nano: u32) -> LocalResult<DateTime<Off>> {
        match self {
            LocalResult::Single(d) => d.and_hms_nano_opt(hour, min, sec, nano)
                                       .map_or(LocalResult::None, LocalResult::Single),
            _ => LocalResult::None,
        }
    }

}

impl<T:fmt::Show> LocalResult<T> {
    /// Returns the single unique conversion result, or fails accordingly.
    pub fn unwrap(self) -> T {
        match self {
            LocalResult::None => panic!("No such local time"),
            LocalResult::Single(t) => t,
            LocalResult::Ambiguous(t1,t2) => {
                panic!("Ambiguous local time, ranging from {} to {}", t1, t2)
            }
        }
    }
}

/// The offset from the local time to UTC.
pub trait Offset: Clone + fmt::Show {
    /// Makes a new `Date` from year, month, day and the current offset.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// The offset normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Fails on the out-of-range date, invalid month and/or day.
    fn ymd(&self, year: i32, month: u32, day: u32) -> Date<Self> {
        self.ymd_opt(year, month, day).unwrap()
    }

    /// Makes a new `Date` from year, month, day and the current offset.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// The offset normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Returns `None` on the out-of-range date, invalid month and/or day.
    fn ymd_opt(&self, year: i32, month: u32, day: u32) -> LocalResult<Date<Self>> {
        match NaiveDate::from_ymd_opt(year, month, day) {
            Some(d) => self.from_local_date(&d),
            None => LocalResult::None,
        }
    }

    /// Makes a new `Date` from year, day of year (DOY or "ordinal") and the current offset.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// The offset normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Fails on the out-of-range date and/or invalid DOY.
    fn yo(&self, year: i32, ordinal: u32) -> Date<Self> {
        self.yo_opt(year, ordinal).unwrap()
    }

    /// Makes a new `Date` from year, day of year (DOY or "ordinal") and the current offset.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// The offset normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Returns `None` on the out-of-range date and/or invalid DOY.
    fn yo_opt(&self, year: i32, ordinal: u32) -> LocalResult<Date<Self>> {
        match NaiveDate::from_yo_opt(year, ordinal) {
            Some(d) => self.from_local_date(&d),
            None => LocalResult::None,
        }
    }

    /// Makes a new `Date` from ISO week date (year and week number), day of the week (DOW) and
    /// the current offset.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    /// The resulting `Date` may have a different year from the input year.
    ///
    /// The offset normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Fails on the out-of-range date and/or invalid week number.
    fn isoywd(&self, year: i32, week: u32, weekday: Weekday) -> Date<Self> {
        self.isoywd_opt(year, week, weekday).unwrap()
    }

    /// Makes a new `Date` from ISO week date (year and week number), day of the week (DOW) and
    /// the current offset.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    /// The resulting `Date` may have a different year from the input year.
    ///
    /// The offset normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Returns `None` on the out-of-range date and/or invalid week number.
    fn isoywd_opt(&self, year: i32, week: u32, weekday: Weekday) -> LocalResult<Date<Self>> {
        match NaiveDate::from_isoywd_opt(year, week, weekday) {
            Some(d) => self.from_local_date(&d),
            None => LocalResult::None,
        }
    }

    /// Makes a new `Time` from hour, minute, second and the current offset.
    ///
    /// Fails on invalid hour, minute and/or second.
    fn hms(&self, hour: u32, min: u32, sec: u32) -> Time<Self> {
        self.hms_opt(hour, min, sec).unwrap()
    }

    /// Makes a new `Time` from hour, minute, second and the current offset.
    ///
    /// Returns `None` on invalid hour, minute and/or second.
    fn hms_opt(&self, hour: u32, min: u32, sec: u32) -> LocalResult<Time<Self>> {
        match NaiveTime::from_hms_opt(hour, min, sec) {
            Some(t) => self.from_local_time(&t),
            None => LocalResult::None,
        }
    }

    /// Makes a new `Time` from hour, minute, second, millisecond and the current offset.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or millisecond.
    fn hms_milli(&self, hour: u32, min: u32, sec: u32, milli: u32) -> Time<Self> {
        self.hms_milli_opt(hour, min, sec, milli).unwrap()
    }

    /// Makes a new `Time` from hour, minute, second, millisecond and the current offset.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or millisecond.
    fn hms_milli_opt(&self, hour: u32, min: u32, sec: u32, milli: u32) -> LocalResult<Time<Self>> {
        match NaiveTime::from_hms_milli_opt(hour, min, sec, milli) {
            Some(t) => self.from_local_time(&t),
            None => LocalResult::None,
        }
    }

    /// Makes a new `Time` from hour, minute, second, microsecond and the current offset.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or microsecond.
    fn hms_micro(&self, hour: u32, min: u32, sec: u32, micro: u32) -> Time<Self> {
        self.hms_micro_opt(hour, min, sec, micro).unwrap()
    }

    /// Makes a new `Time` from hour, minute, second, microsecond and the current offset.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or microsecond.
    fn hms_micro_opt(&self, hour: u32, min: u32, sec: u32, micro: u32) -> LocalResult<Time<Self>> {
        match NaiveTime::from_hms_micro_opt(hour, min, sec, micro) {
            Some(t) => self.from_local_time(&t),
            None => LocalResult::None,
        }
    }

    /// Makes a new `Time` from hour, minute, second, nanosecond and the current offset.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Fails on invalid hour, minute, second and/or nanosecond.
    fn hms_nano(&self, hour: u32, min: u32, sec: u32, nano: u32) -> Time<Self> {
        self.hms_nano_opt(hour, min, sec, nano).unwrap()
    }

    /// Makes a new `Time` from hour, minute, second, nanosecond and the current offset.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or nanosecond.
    fn hms_nano_opt(&self, hour: u32, min: u32, sec: u32, nano: u32) -> LocalResult<Time<Self>> {
        match NaiveTime::from_hms_nano_opt(hour, min, sec, nano) {
            Some(t) => self.from_local_time(&t),
            None => LocalResult::None,
        }
    }

    /// Returns a name or abbreviation of this offset.
    fn name(&self) -> SendStr;

    /// Returns the *current* offset from UTC to the local time.
    fn local_minus_utc(&self) -> Duration;

    /// Converts the local `NaiveDate` to the timezone-aware `Date` if possible.
    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<Self>>;

    /// Converts the local `NaiveTime` to the timezone-aware `Time` if possible.
    fn from_local_time(&self, local: &NaiveTime) -> LocalResult<Time<Self>>;

    /// Converts the local `NaiveDateTime` to the timezone-aware `DateTime` if possible.
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Self>>;

    /// Converts the UTC `NaiveDate` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    fn to_local_date(&self, utc: &NaiveDate) -> NaiveDate;

    /// Converts the UTC `NaiveTime` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    fn to_local_time(&self, utc: &NaiveTime) -> NaiveTime;

    /// Converts the UTC `NaiveDateTime` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    fn to_local_datetime(&self, utc: &NaiveDateTime) -> NaiveDateTime;
}

/// The UTC timescale. This is the most efficient offset when you don't need the local time.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct UTC;

impl UTC {
    /// Returns a `Date` which corresponds to the current date.
    pub fn today() -> Date<UTC> { UTC::now().date() }

    /// Returns a `DateTime` which corresponds to the current date.
    pub fn now() -> DateTime<UTC> {
        let spec = stdtime::get_time();
        let naive = NaiveDateTime::from_num_seconds_from_unix_epoch(spec.sec, spec.nsec as u32);
        DateTime::from_utc(naive, UTC)
    }
}

impl Offset for UTC {
    fn name(&self) -> SendStr { "UTC".into_cow() }
    fn local_minus_utc(&self) -> Duration { Duration::zero() }

    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<UTC>> {
        LocalResult::Single(Date::from_utc(local.clone(), UTC))
    }
    fn from_local_time(&self, local: &NaiveTime) -> LocalResult<Time<UTC>> {
        LocalResult::Single(Time::from_utc(local.clone(), UTC))
    }
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<UTC>> {
        LocalResult::Single(DateTime::from_utc(local.clone(), UTC))
    }

    fn to_local_date(&self, utc: &NaiveDate) -> NaiveDate { utc.clone() }
    fn to_local_time(&self, utc: &NaiveTime) -> NaiveTime { utc.clone() }
    fn to_local_datetime(&self, utc: &NaiveDateTime) -> NaiveDateTime { utc.clone() }
}

impl fmt::Show for UTC {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Z") }
}

/// The fixed offset, from UTC-23:59:59 to UTC+23:59:59.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct FixedOffset {
    local_minus_utc: i32,
}

impl FixedOffset {
    /// Makes a new `FixedOffset` for the Eastern Hemisphere with given timezone difference.
    /// The negative `secs` means the Western Hemisphere.
    ///
    /// Fails on the out-of-bound `secs`.
    pub fn east(secs: i32) -> FixedOffset {
        FixedOffset::east_opt(secs).expect("FixedOffset::east out of bounds")
    }

    /// Makes a new `FixedOffset` for the Eastern Hemisphere with given timezone difference.
    /// The negative `secs` means the Western Hemisphere.
    ///
    /// Returns `None` on the out-of-bound `secs`.
    pub fn east_opt(secs: i32) -> Option<FixedOffset> {
        if -86400 < secs && secs < 86400 {
            Some(FixedOffset { local_minus_utc: secs })
        } else {
            None
        }
    }

    /// Makes a new `FixedOffset` for the Western Hemisphere with given timezone difference.
    /// The negative `secs` means the Eastern Hemisphere.
    ///
    /// Fails on the out-of-bound `secs`.
    pub fn west(secs: i32) -> FixedOffset {
        FixedOffset::west_opt(secs).expect("FixedOffset::west out of bounds")
    }

    /// Makes a new `FixedOffset` for the Western Hemisphere with given timezone difference.
    /// The negative `secs` means the Eastern Hemisphere.
    ///
    /// Returns `None` on the out-of-bound `secs`.
    pub fn west_opt(secs: i32) -> Option<FixedOffset> {
        if -86400 < secs && secs < 86400 {
            Some(FixedOffset { local_minus_utc: -secs })
        } else {
            None
        }
    }
}

impl Offset for FixedOffset {
    fn name(&self) -> SendStr { "UTC".into_cow() } // XXX
    fn local_minus_utc(&self) -> Duration { Duration::seconds(self.local_minus_utc as i64) }

    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<FixedOffset>> {
        LocalResult::Single(Date::from_utc(local.clone(), self.clone()))
    }
    fn from_local_time(&self, local: &NaiveTime) -> LocalResult<Time<FixedOffset>> {
        let t = Time::from_utc(*local + Duration::seconds(-self.local_minus_utc as i64),
                               self.clone());
        LocalResult::Single(t)
    }
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<FixedOffset>> {
        let dt = DateTime::from_utc(*local + Duration::seconds(-self.local_minus_utc as i64),
                                    self.clone());
        LocalResult::Single(dt)
    }

    fn to_local_date(&self, utc: &NaiveDate) -> NaiveDate {
        utc.clone()
    }
    fn to_local_time(&self, utc: &NaiveTime) -> NaiveTime {
        *utc + Duration::seconds(self.local_minus_utc as i64)
    }
    fn to_local_datetime(&self, utc: &NaiveDateTime) -> NaiveDateTime {
        *utc + Duration::seconds(self.local_minus_utc as i64)
    }
}

impl fmt::Show for FixedOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let offset = self.local_minus_utc;
        let (sign, offset) = if offset < 0 {('-', -offset)} else {('+', offset)};
        let (mins, sec) = div_mod_floor(offset, 60);
        let (hour, min) = div_mod_floor(mins, 60);
        if sec == 0 {
            write!(f, "{}{:02}:{:02}", sign, hour, min)
        } else {
            write!(f, "{}{:02}:{:02}:{:02}", sign, hour, min, sec)
        }
    }
}

/// The local timescale. This is implemented via the standard `time` crate.
#[derive(Copy, Clone)]
pub struct Local {
    cached: FixedOffset,
}

impl Local {
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
        let offset = Local { cached: FixedOffset::east(tm.tm_utcoff) };
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

    /// Returns a `Date` which corresponds to the current date.
    pub fn today() -> Date<Local> {
        Local::now().date()
    }

    /// Returns a `DateTime` which corresponds to the current date.
    pub fn now() -> DateTime<Local> {
        Local::tm_to_datetime(stdtime::now())
    }
}

impl Offset for Local {
    fn name(&self) -> SendStr { "LMT".into_cow() } // XXX XXX
    fn local_minus_utc(&self) -> Duration { self.cached.local_minus_utc() }

    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<Local>> {
        match self.from_local_datetime(&local.and_hms(0, 0, 0)) {
            LocalResult::None => LocalResult::None,
            LocalResult::Single(dt) => LocalResult::Single(dt.date()),
            LocalResult::Ambiguous(min, max) => {
                let min = min.date();
                let max = max.date();
                if min == max {LocalResult::Single(min)} else {LocalResult::Ambiguous(min, max)}
            }
        }
    }

    fn from_local_time(&self, local: &NaiveTime) -> LocalResult<Time<Local>> {
        // XXX we don't have enough information here, so we assume that the timezone remains same
        LocalResult::Single(Time::from_utc(local.clone(), self.clone()))
    }

    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Local>> {
        let timespec = Local::datetime_to_timespec(local);
        LocalResult::Single(Local::tm_to_datetime(stdtime::at(timespec)))
    }

    fn to_local_date(&self, utc: &NaiveDate) -> NaiveDate { self.cached.to_local_date(utc) }
    fn to_local_time(&self, utc: &NaiveTime) -> NaiveTime { self.cached.to_local_time(utc) }
    fn to_local_datetime(&self, utc: &NaiveDateTime) -> NaiveDateTime {
        self.cached.to_local_datetime(utc)
    }
}

impl fmt::Show for Local {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.cached.fmt(f) }
}

