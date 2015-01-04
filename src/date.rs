// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * ISO 8601 calendar date with timezone.
 */

use std::{fmt, hash};
use std::cmp::Ordering;
use std::ops::{Add, Sub};

use {Weekday, Datelike};
use duration::Duration;
use offset::{Offset, UTC};
use naive;
use naive::date::NaiveDate;
use naive::time::NaiveTime;
use datetime::DateTime;
use format::DelayedFormat;

/// ISO 8601 calendar date with timezone.
#[derive(Clone)]
pub struct Date<Off> {
    date: NaiveDate,
    offset: Off,
}

/// The minimum possible `Date`.
pub const MIN: Date<UTC> = Date { date: naive::date::MIN, offset: UTC };
/// The maximum possible `Date`.
pub const MAX: Date<UTC> = Date { date: naive::date::MAX, offset: UTC };

impl<Off:Offset> Date<Off> {
    /// Makes a new `Date` with given *UTC* date and offset.
    /// The local date should be constructed via the `Offset` trait.
    #[inline]
    pub fn from_utc(date: NaiveDate, offset: Off) -> Date<Off> {
        Date { date: date, offset: offset }
    }

    /// Makes a new `DateTime` from the current date and given `NaiveTime`.
    /// The offset in the current date is preserved.
    ///
    /// Fails on invalid datetime.
    #[inline]
    pub fn and_time(&self, time: NaiveTime) -> Option<DateTime<Off>> {
        let localdt = self.offset.to_local_date(&self.date).and_time(time);
        self.offset.from_local_datetime(&localdt).single()
    }

    /// Makes a new `DateTime` from the current date, hour, minute and second.
    /// The offset in the current date is preserved.
    ///
    /// Fails on invalid hour, minute and/or second.
    #[inline]
    pub fn and_hms(&self, hour: u32, min: u32, sec: u32) -> DateTime<Off> {
        self.and_hms_opt(hour, min, sec).expect("invalid time")
    }

    /// Makes a new `DateTime` from the current date, hour, minute and second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `None` on invalid hour, minute and/or second.
    #[inline]
    pub fn and_hms_opt(&self, hour: u32, min: u32, sec: u32) -> Option<DateTime<Off>> {
        NaiveTime::from_hms_opt(hour, min, sec).and_then(|time| self.and_time(time))
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Fails on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn and_hms_milli(&self, hour: u32, min: u32, sec: u32, milli: u32) -> DateTime<Off> {
        self.and_hms_milli_opt(hour, min, sec, milli).expect("invalid time")
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `None` on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn and_hms_milli_opt(&self, hour: u32, min: u32, sec: u32,
                             milli: u32) -> Option<DateTime<Off>> {
        NaiveTime::from_hms_milli_opt(hour, min, sec, milli).and_then(|time| self.and_time(time))
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Fails on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn and_hms_micro(&self, hour: u32, min: u32, sec: u32, micro: u32) -> DateTime<Off> {
        self.and_hms_micro_opt(hour, min, sec, micro).expect("invalid time")
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `None` on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn and_hms_micro_opt(&self, hour: u32, min: u32, sec: u32,
                             micro: u32) -> Option<DateTime<Off>> {
        NaiveTime::from_hms_micro_opt(hour, min, sec, micro).and_then(|time| self.and_time(time))
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Fails on invalid hour, minute, second and/or nanosecond.
    #[inline]
    pub fn and_hms_nano(&self, hour: u32, min: u32, sec: u32, nano: u32) -> DateTime<Off> {
        self.and_hms_nano_opt(hour, min, sec, nano).expect("invalid time")
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `None` on invalid hour, minute, second and/or nanosecond.
    #[inline]
    pub fn and_hms_nano_opt(&self, hour: u32, min: u32, sec: u32,
                            nano: u32) -> Option<DateTime<Off>> {
        NaiveTime::from_hms_nano_opt(hour, min, sec, nano).and_then(|time| self.and_time(time))
    }

    /// Makes a new `Date` for the next date.
    ///
    /// Fails when `self` is the last representable date.
    #[inline]
    pub fn succ(&self) -> Date<Off> {
        self.succ_opt().expect("out of bound")
    }

    /// Makes a new `Date` for the next date.
    ///
    /// Returns `None` when `self` is the last representable date.
    #[inline]
    pub fn succ_opt(&self) -> Option<Date<Off>> {
        self.date.succ_opt().map(|date| Date::from_utc(date, self.offset.clone()))
    }

    /// Makes a new `Date` for the prior date.
    ///
    /// Fails when `self` is the first representable date.
    #[inline]
    pub fn pred(&self) -> Date<Off> {
        self.pred_opt().expect("out of bound")
    }

    /// Makes a new `Date` for the prior date.
    ///
    /// Returns `None` when `self` is the first representable date.
    #[inline]
    pub fn pred_opt(&self) -> Option<Date<Off>> {
        self.date.pred_opt().map(|date| Date::from_utc(date, self.offset.clone()))
    }

    /// Retrieves an associated offset.
    #[inline]
    pub fn offset<'a>(&'a self) -> &'a Off {
        &self.offset
    }

    /// Changes the associated offset.
    /// This does not change the actual `Date` (but will change the string representation).
    #[inline]
    pub fn with_offset<Off2:Offset>(&self, offset: Off2) -> Date<Off2> {
        Date::from_utc(self.date, offset)
    }

    /// Formats the date in the specified format string.
    /// See the `format` module on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&'a self, fmt: &'a str) -> DelayedFormat<'a> {
        DelayedFormat::new_with_offset(Some(self.local()), None, &self.offset, fmt)
    }

    /// Returns a view to the local date.
    fn local(&self) -> NaiveDate {
        self.offset.to_local_date(&self.date)
    }
}

impl<Off:Offset> Datelike for Date<Off> {
    #[inline] fn year(&self) -> i32 { self.local().year() }
    #[inline] fn month(&self) -> u32 { self.local().month() }
    #[inline] fn month0(&self) -> u32 { self.local().month0() }
    #[inline] fn day(&self) -> u32 { self.local().day() }
    #[inline] fn day0(&self) -> u32 { self.local().day0() }
    #[inline] fn ordinal(&self) -> u32 { self.local().ordinal() }
    #[inline] fn ordinal0(&self) -> u32 { self.local().ordinal0() }
    #[inline] fn weekday(&self) -> Weekday { self.local().weekday() }
    #[inline] fn isoweekdate(&self) -> (i32, u32, Weekday) { self.local().isoweekdate() }

    #[inline]
    fn with_year(&self, year: i32) -> Option<Date<Off>> {
        self.local().with_year(year)
            .and_then(|date| self.offset.from_local_date(&date).single())
    }

    #[inline]
    fn with_month(&self, month: u32) -> Option<Date<Off>> {
        self.local().with_month(month)
            .and_then(|date| self.offset.from_local_date(&date).single())
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Option<Date<Off>> {
        self.local().with_month0(month0)
            .and_then(|date| self.offset.from_local_date(&date).single())
    }

    #[inline]
    fn with_day(&self, day: u32) -> Option<Date<Off>> {
        self.local().with_day(day)
            .and_then(|date| self.offset.from_local_date(&date).single())
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Option<Date<Off>> {
        self.local().with_day0(day0)
            .and_then(|date| self.offset.from_local_date(&date).single())
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<Date<Off>> {
        self.local().with_ordinal(ordinal)
            .and_then(|date| self.offset.from_local_date(&date).single())
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<Date<Off>> {
        self.local().with_ordinal0(ordinal0)
            .and_then(|date| self.offset.from_local_date(&date).single())
    }
}

impl<Off:Offset, Off2:Offset> PartialEq<Date<Off2>> for Date<Off> {
    fn eq(&self, other: &Date<Off2>) -> bool { self.date == other.date }
}

impl<Off:Offset> Eq for Date<Off> {
}

impl<Off:Offset> PartialOrd for Date<Off> {
    fn partial_cmp(&self, other: &Date<Off>) -> Option<Ordering> {
        self.date.partial_cmp(&other.date)
    }
}

impl<Off:Offset> Ord for Date<Off> {
    fn cmp(&self, other: &Date<Off>) -> Ordering { self.date.cmp(&other.date) }
}

impl<Off:Offset> hash::Hash for Date<Off> {
    fn hash(&self, state: &mut hash::sip::SipState) { self.date.hash(state) }
}

impl<Off:Offset> Add<Duration,Date<Off>> for Date<Off> {
    fn add(self, rhs: Duration) -> Date<Off> {
        Date { date: self.date + rhs, offset: self.offset }
    }
}

impl<Off:Offset> Add<Date<Off>,Date<Off>> for Duration {
    #[inline]
    fn add(self, rhs: Date<Off>) -> Date<Off> { rhs.add(self) }
}

impl<Off:Offset, Off2:Offset> Sub<Date<Off2>,Duration> for Date<Off> {
    fn sub(self, rhs: Date<Off2>) -> Duration { self.date - rhs.date }
}

impl<Off:Offset> Sub<Duration,Date<Off>> for Date<Off> {
    #[inline]
    fn sub(self, rhs: Duration) -> Date<Off> { self.add(-rhs) }
}

impl<Off:Offset> fmt::Show for Date<Off> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.local(), self.offset)
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::IntoCow;
    use std::fmt;
    use std::str::SendStr;

    use duration::Duration;
    use naive::date::NaiveDate;
    use naive::time::NaiveTime;
    use naive::datetime::NaiveDateTime;
    use super::Date;
    use time::Time;
    use datetime::DateTime;
    use offset::{Offset, LocalResult};

    #[derive(Copy, Clone, PartialEq, Eq)]
    struct UTC1y; // same to UTC but with an offset of 365 days

    impl Offset for UTC1y {
        fn name(&self) -> SendStr { "UTC+8760".into_cow() } // yes, no kidding
        fn local_minus_utc(&self) -> Duration { Duration::zero() }

        fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<UTC1y>> {
            LocalResult::Single(Date::from_utc(*local - Duration::days(365), UTC1y))
        }
        fn from_local_time(&self, local: &NaiveTime) -> LocalResult<Time<UTC1y>> {
            LocalResult::Single(Time::from_utc(local.clone(), UTC1y))
        }
        fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<UTC1y>> {
            LocalResult::Single(DateTime::from_utc(*local - Duration::days(365), UTC1y))
        }

        fn to_local_date(&self, utc: &NaiveDate) -> NaiveDate { *utc + Duration::days(365) }
        fn to_local_time(&self, utc: &NaiveTime) -> NaiveTime { utc.clone() }
        fn to_local_datetime(&self, utc: &NaiveDateTime) -> NaiveDateTime {
            *utc + Duration::days(365)
        }
    }

    impl fmt::Show for UTC1y {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "+8760:00") }
    }

    #[test]
    fn test_date_weird_offset() {
        assert_eq!(UTC1y.ymd(2012, 2, 29).to_string(),
                   "2012-02-29+8760:00".to_string());
        assert_eq!(UTC1y.ymd(2012, 2, 29).and_hms(5, 6, 7).to_string(),
                   "2012-02-29T05:06:07+8760:00".to_string());
        assert_eq!(UTC1y.ymd(2012, 3, 4).to_string(),
                   "2012-03-04+8760:00".to_string());
        assert_eq!(UTC1y.ymd(2012, 3, 4).and_hms(5, 6, 7).to_string(),
                   "2012-03-04T05:06:07+8760:00".to_string());
    }
}

