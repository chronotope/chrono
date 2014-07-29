// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * Offsets from the local time to UTC.
 */

use std::fmt;
use num::Integer;
use duration::Duration;
use date::{NaiveDate, Date, Weekday};
use time::{NaiveTime, Time};
use datetime::{NaiveDateTime, DateTime};

/// The conversion result from the local time to the timezone-aware datetime types.
pub enum LocalResult<T> {
    /// Given local time representation is invalid.
    /// This can occur when, for example, the positive timezone transition.
    NoResult,
    /// Given local time representation has a single unique result.
    Single(T),
    /// Given local time representation has multiple results and thus ambiguous.
    /// This can occur when, for example, the negative timezone transition.
    Ambiguous(T /*min*/, T /*max*/),
}

impl<T> LocalResult<T> {
    /// Returns `Some` only when the conversion result is unique, or `None` otherwise.
    pub fn single(self) -> Option<T> {
        match self { Single(t) => Some(t), _ => None }
    }

    /// Returns `Some` for the earliest possible conversion result, or `None` if none.
    pub fn earliest(self) -> Option<T> {
        match self { Single(t) | Ambiguous(t,_) => Some(t), _ => None }
    }

    /// Returns `Some` for the latest possible conversion result, or `None` if none.
    pub fn latest(self) -> Option<T> {
        match self { Single(t) | Ambiguous(_,t) => Some(t), _ => None }
    }
}

impl<T:fmt::Show> LocalResult<T> {
    /// Returns the single unique conversion result, or fails accordingly.
    pub fn unwrap(self) -> T {
        match self {
            NoResult => fail!("No such local time"),
            Single(t) => t,
            Ambiguous(t1,t2) => fail!("Ambiguous local time, ranging from {} to {}", t1, t2),
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
            None => NoResult,
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
            None => NoResult,
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
            None => NoResult,
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
            None => NoResult,
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
            None => NoResult,
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
            None => NoResult,
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
            None => NoResult,
        }
    }

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
#[deriving(Clone)]
pub struct UTC;

impl Offset for UTC {
    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<UTC>> {
        Single(Date::from_utc(local.clone(), UTC))
    }
    fn from_local_time(&self, local: &NaiveTime) -> LocalResult<Time<UTC>> {
        Single(Time::from_utc(local.clone(), UTC))
    }
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<UTC>> {
        Single(DateTime::from_utc(local.clone(), UTC))
    }

    fn to_local_date(&self, utc: &NaiveDate) -> NaiveDate { utc.clone() }
    fn to_local_time(&self, utc: &NaiveTime) -> NaiveTime { utc.clone() }
    fn to_local_datetime(&self, utc: &NaiveDateTime) -> NaiveDateTime { utc.clone() }
}

impl fmt::Show for UTC {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Z") }
}

/// The fixed offset, from UTC-23:59:59 to UTC+23:59:59.
#[deriving(Clone)]
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
    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<FixedOffset>> {
        Single(Date::from_utc(local.clone(), self.clone()))
    }
    fn from_local_time(&self, local: &NaiveTime) -> LocalResult<Time<FixedOffset>> {
        Single(Time::from_utc(*local + Duration::seconds(-self.local_minus_utc), self.clone()))
    }
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<FixedOffset>> {
        Single(DateTime::from_utc(*local + Duration::seconds(-self.local_minus_utc), self.clone()))
    }

    fn to_local_date(&self, utc: &NaiveDate) -> NaiveDate {
        utc.clone()
    }
    fn to_local_time(&self, utc: &NaiveTime) -> NaiveTime {
        *utc + Duration::seconds(self.local_minus_utc)
    }
    fn to_local_datetime(&self, utc: &NaiveDateTime) -> NaiveDateTime {
        *utc + Duration::seconds(self.local_minus_utc)
    }
}

impl fmt::Show for FixedOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let offset = self.local_minus_utc;
        let (sign, offset) = if offset < 0 {('-', -offset)} else {('+', offset)};
        let (mins, sec) = offset.div_mod_floor(&60);
        let (hour, min) = mins.div_mod_floor(&60);
        if sec == 0 {
            write!(f, "{}{:02}:{:02}", sign, hour, min)
        } else {
            write!(f, "{}{:02}:{:02}:{:02}", sign, hour, min, sec)
        }
    }
}

