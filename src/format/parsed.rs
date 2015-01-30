// This is a part of rust-chrono.
// Copyright (c) 2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * A collection of parsed date and time items.
 * They can be constructed incrementally while being checked for consistency.
 */

use std::num::{Int, ToPrimitive};

use {Datelike, Timelike};
use Weekday;
use div::div_rem;
use duration::Duration;
use offset::FixedOffset;
use naive::date::NaiveDate;
use naive::time::NaiveTime;
use naive::datetime::NaiveDateTime;

/// Parsed parts of date and time.
#[allow(missing_copy_implementations)]
#[derive(Clone, Debug)]
pub struct Parsed {
    /// Year divided by 100. Implies that the year is >= 1 BCE.
    ///
    /// Due to the common usage, if this field is missing but `year_mod_100` is present,
    /// it is inferred to 19 when `year_mod_100 >= 70` and 20 otherwise.
    pub year_div_100: Option<u32>,
    /// Year modulo 100. Implies that the year is >= 1 BCE.
    pub year_mod_100: Option<u32>,
    /// Year in the ISO week date, divided by 100. Implies that the year is >= 1 BCE.
    ///
    /// Due to the common usage, if this field is missing but `isoyear_mod_100` is present,
    /// it is inferred to 19 when `isoyear_mod_100 >= 70` and 20 otherwise.
    pub isoyear_div_100: Option<u32>,
    /// Year in the ISO week date, modulo 100. Implies that the year is >= 1 BCE.
    pub isoyear_mod_100: Option<u32>,
    /// Month (1--12).
    pub month: Option<u32>,
    /// Week number, where the week 1 starts at the first Sunday of January.
    /// (0--53, 1--53 or 1--52 depending on the year).
    pub week_from_sun: Option<u32>,
    /// Week number, where the week 1 starts at the first Monday of January.
    /// (0--53, 1--53 or 1--52 depending on the year).
    pub week_from_mon: Option<u32>,
    /// ISO week number (1--52 or 1--53 depending on the year).
    pub isoweek: Option<u32>,
    /// Day of the week.
    pub weekday: Option<Weekday>,
    /// Day of the year (1--365 or 1--366 depending on the year).
    pub ordinal: Option<u32>,
    /// Day of the month (1--28, 1--29, 1--30 or 1--31 depending on the month).
    pub day: Option<u32>,
    /// Hour number divided by 12 (0--1). 0 indicates AM and 1 indicates PM.
    pub hour_div_12: Option<u32>,
    /// Hour number modulo 12 (0--11).
    pub hour_mod_12: Option<u32>,
    /// Minute number (0--59).
    pub minute: Option<u32>,
    /// Second number (0--60, accounting for leap seconds).
    pub second: Option<u32>,
    /// The number of nanoseconds since the whole second (0--999,999,999).
    pub nanosecond: Option<u32>,
    /// The number of non-leap seconds since January 1, 1970 0:00:00 UTC.
    ///
    /// This can be off by one if `second` is 60 (a leap second).
    pub timestamp: Option<i64>,
    /// Offset from the local time to UTC, in seconds.
    pub offset: Option<i32>,
}

/// Checks if `old` is either empty or has the same value to `new` (i.e. "consistent"),
/// and if it is empty, set `old` to `new` as well.
/// Returns true when `old` is consistent to `new`.
fn set_if_consistent<T: PartialEq>(old: &mut Option<T>, new: T) -> bool {
    if let Some(ref old) = *old {
        *old == new
    } else {
        *old = Some(new);
        true
    }
}

impl Parsed {
    /// Returns the initial value of parsed parts.
    pub fn new() -> Parsed {
        Parsed { year_div_100: None, year_mod_100: None, isoyear_div_100: None,
                 isoyear_mod_100: None, month: None, week_from_sun: None, week_from_mon: None,
                 isoweek: None, weekday: None, ordinal: None, day: None, hour_div_12: None,
                 hour_mod_12: None, minute: None, second: None, nanosecond: None,
                 timestamp: None, offset: None }
    }

    /// Tries to set the `year_div_100` field from given value. Returns true if it's consistent.
    pub fn set_year_div_100(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.year_div_100, v))
    }

    /// Tries to set the `year_mod_100` field from given value. Returns true if it's consistent.
    pub fn set_year_mod_100(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.year_mod_100, v))
    }

    /// Tries to set both `year_div_100` and `year_mod_100` fields from given value.
    /// Returns true if it's consistent.
    pub fn set_year(&mut self, value: i64) -> bool {
        if value < 0 { return false; }
        let (q, r) = div_rem(value, 100);
        self.set_year_div_100(q) && set_if_consistent(&mut self.year_mod_100, r as u32)
    }

    /// Tries to set the `isoyear_div_100` field from given value. Returns true if it's consistent.
    pub fn set_isoyear_div_100(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.isoyear_div_100, v))
    }

    /// Tries to set the `isoyear_mod_100` field from given value. Returns true if it's consistent.
    pub fn set_isoyear_mod_100(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.isoyear_mod_100, v))
    }

    /// Tries to set both `isoyear_div_100` and `isoyear_mod_100` fields from given value.
    /// Returns true if it's consistent.
    pub fn set_isoyear(&mut self, value: i64) -> bool {
        if value < 0 { return false; }
        let (q, r) = div_rem(value, 100);
        self.set_isoyear_div_100(q) && set_if_consistent(&mut self.isoyear_mod_100, r as u32)
    }

    /// Tries to set the `month` field from given value. Returns true if it's consistent.
    pub fn set_month(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.month, v))
    }

    /// Tries to set the `week_from_sun` field from given value. Returns true if it's consistent.
    pub fn set_week_from_sun(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.week_from_sun, v))
    }

    /// Tries to set the `week_from_mon` field from given value. Returns true if it's consistent.
    pub fn set_week_from_mon(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.week_from_mon, v))
    }

    /// Tries to set the `isoweek` field from given value. Returns true if it's consistent.
    pub fn set_isoweek(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.isoweek, v))
    }

    /// Tries to set the `weekday` field from given value. Returns true if it's consistent.
    pub fn set_weekday(&mut self, value: Weekday) -> bool {
        set_if_consistent(&mut self.weekday, value)
    }

    /// Tries to set the `ordinal` field from given value. Returns true if it's consistent.
    pub fn set_ordinal(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.ordinal, v))
    }

    /// Tries to set the `day` field from given value. Returns true if it's consistent.
    pub fn set_day(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.day, v))
    }

    /// Tries to set the `hour_div_12` field from given value. (`false` for AM, `true` for PM)
    /// Returns true if it's consistent.
    pub fn set_ampm(&mut self, value: bool) -> bool {
        set_if_consistent(&mut self.hour_div_12, if value {1} else {0})
    }

    /// Tries to set the `hour_mod_12` field from given hour number in 12-hour clocks.
    /// Returns true if it's consistent.
    pub fn set_hour12(&mut self, value: i64) -> bool {
        1 <= value && value <= 12 && set_if_consistent(&mut self.hour_mod_12, value as u32 % 12)
    }

    /// Tries to set both `hour_div_12` and `hour_mod_12` fields from given value.
    /// Returns true if it's consistent.
    pub fn set_hour(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.hour_div_12, v / 12) &&
                                               set_if_consistent(&mut self.hour_mod_12, v % 12))
    }

    /// Tries to set the `minute` field from given value. Returns true if it's consistent.
    pub fn set_minute(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.minute, v))
    }

    /// Tries to set the `second` field from given value. Returns true if it's consistent.
    pub fn set_second(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.second, v))
    }

    /// Tries to set the `nanosecond` field from given value. Returns true if it's consistent.
    pub fn set_nanosecond(&mut self, value: i64) -> bool {
        value.to_u32().map_or(false, |&mut: v| set_if_consistent(&mut self.nanosecond, v))
    }

    /// Tries to set the `timestamp` field from given value. Returns true if it's consistent.
    pub fn set_timestamp(&mut self, value: i64) -> bool {
        set_if_consistent(&mut self.timestamp, value)
    }

    /// Tries to set the `offset` field from given value. Returns true if it's consistent.
    pub fn set_offset(&mut self, value: i64) -> bool {
        value.to_i32().map_or(false, |&mut: v| set_if_consistent(&mut self.offset, v))
    }

    /// Returns a parsed naive date out of given fields.
    /// If the input is insufficient, ambiguous or inconsistent, returns `None` instead.
    ///
    /// This method is able to determine the date from given subset of fields:
    ///
    /// - Year, month, day.
    /// - Year, day of the year (ordinal).
    /// - Year, week number counted from Sunday or Monday, day of the week.
    /// - ISO week date.
    ///
    /// Gregorian year and ISO week date year can have their century number (`*_div_100`) omitted,
    /// the two-digit year is used to guess the century number then.
    pub fn to_naive_date(&self) -> Option<NaiveDate> {
        let given_year = match (self.year_div_100, self.year_mod_100) {
            (Some(q), Some(r @ 0...99)) =>
                Some(try_opt!(try_opt!(try_opt!(q.checked_mul(100)).checked_add(r)).to_i32())),
            (None, Some(r @ 0...69)) => Some(2000 + r as i32),
            (None, Some(r @ 70...99)) => Some(1900 + r as i32),
            (_, _) => None,
        };
        let given_isoyear = match (self.isoyear_div_100, self.isoyear_mod_100) {
            (Some(q), Some(r @ 0...99)) =>
                Some(try_opt!(try_opt!(try_opt!(q.checked_mul(100)).checked_add(r)).to_i32())),
            (None, Some(r @ 0...69)) => Some(2000 + r as i32),
            (None, Some(r @ 70...99)) => Some(1900 + r as i32),
            (_, _) => None,
        };

        // verify the normal year-month-day date.
        let verify_ymd = |&: date: NaiveDate| {
            let year = date.year();
            let month = date.month();
            let day = date.day();
            (given_year.unwrap_or(year) == year &&
             self.month.unwrap_or(month) == month &&
             self.day.unwrap_or(day) == day)
        };

        // verify the ISO week date.
        let verify_isoweekdate = |&: date: NaiveDate| {
            let (isoyear, isoweek, weekday) = date.isoweekdate();
            (given_isoyear.unwrap_or(isoyear) == isoyear &&
             self.isoweek.unwrap_or(isoweek) == isoweek &&
             self.weekday.unwrap_or(weekday) == weekday)
        };

        // verify the ordinal and other (non-ISO) week dates.
        let verify_ordinal = |&: date: NaiveDate| {
            let ordinal = date.ordinal();
            let weekday = date.weekday();
            let week_from_sun = (ordinal - weekday.num_days_from_sunday() + 7) / 7;
            let week_from_mon = (ordinal - weekday.num_days_from_monday() + 7) / 7;
            (self.ordinal.unwrap_or(ordinal) == ordinal &&
             self.week_from_sun.unwrap_or(week_from_sun) == week_from_sun &&
             self.week_from_mon.unwrap_or(week_from_mon) == week_from_mon)
        };

        // test several possibilities.
        // tries to construct a full `NaiveDate` as much as possible, then verifies that
        // it is consistent with other given fields.
        let (verified, parsed_date) = match (given_year, given_isoyear, self) {
            (Some(year), _, &Parsed { month: Some(month), day: Some(day), .. }) => {
                // year, month, day
                let date = try_opt!(NaiveDate::from_ymd_opt(year, month, day));
                (verify_isoweekdate(date) && verify_ordinal(date), date)
            },

            (Some(year), _, &Parsed { ordinal: Some(ordinal), .. }) => {
                // year, day of the year
                let date = try_opt!(NaiveDate::from_yo_opt(year, ordinal));
                (verify_ymd(date) && verify_isoweekdate(date) && verify_ordinal(date), date)
            },

            (Some(year), _, &Parsed { week_from_sun: Some(week_from_sun),
                                      weekday: Some(weekday), .. }) => {
                // year, week (starting at 1st Sunday), day of the week
                let newyear = try_opt!(NaiveDate::from_yo_opt(year, 1));
                let firstweek = 6 - newyear.weekday().num_days_from_sunday();

                // `firstweek+1`-th day of January is the beginning of the week 1.
                if week_from_sun > 53 { return None; } // can it overflow? then give up.
                let ndays = firstweek + (week_from_sun - 1) * 7 + weekday.num_days_from_sunday();
                let date = try_opt!(newyear.checked_add(Duration::days(ndays as i64)));

                (verify_ymd(date) && verify_isoweekdate(date) && verify_ordinal(date), date)
            },

            (Some(year), _, &Parsed { week_from_mon: Some(week_from_mon),
                                      weekday: Some(weekday), .. }) => {
                // year, week (starting at 1st Monday), day of the week
                let newyear = try_opt!(NaiveDate::from_yo_opt(year, 1));
                let firstweek = 6 - newyear.weekday().num_days_from_monday();

                // `firstweek+1`-th day of January is the beginning of the week 1.
                if week_from_mon > 53 { return None; } // can it overflow? then give up.
                let ndays = firstweek + (week_from_mon - 1) * 7 + weekday.num_days_from_monday();
                let date = try_opt!(newyear.checked_add(Duration::days(ndays as i64)));

                (verify_ymd(date) && verify_isoweekdate(date) && verify_ordinal(date), date)
            },

            (_, Some(isoyear), &Parsed { isoweek: Some(isoweek), weekday: Some(weekday), .. }) => {
                // ISO year, week, day of the week
                let date = try_opt!(NaiveDate::from_isoywd_opt(isoyear, isoweek, weekday));
                (verify_ymd(date) && verify_ordinal(date), date)
            },

            (_, _, _) => return None // insufficient input
        };

        if verified {
            Some(parsed_date)
        } else {
            None
        }
    }

    /// Returns a parsed naive time out of given fields.
    /// If the input is insufficient, ambiguous or inconsistent, returns `None` instead.
    ///
    /// This method is able to determine the time from given subset of fields:
    ///
    /// - Hour, minute. (second and nanosecond assumed to be 0)
    /// - Hour, minute, second. (nanosecond assumed to be 0)
    /// - Hour, minute, second, nanosecond.
    ///
    /// It is able to handle leap seconds when given second is 60.
    pub fn to_naive_time(&self) -> Option<NaiveTime> {
        let hour_div_12 = match self.hour_div_12 { Some(v @ 0...1)  => v, _ => return None };
        let hour_mod_12 = match self.hour_mod_12 { Some(v @ 0...11) => v, _ => return None };
        let hour = hour_div_12 * 12 + hour_mod_12;

        let minute = match self.minute { Some(v @ 0...59) => v, _ => return None };

        // we allow omitting seconds or nanoseconds, but they should be in the range.
        let (second, mut nano) = match self.second.unwrap_or(0) {
            v @ 0...59 => (v, 0),
            60 => (60, 1_000_000_000),
            _ => return None
        };
        nano += match self.nanosecond {
            None => 0,
            Some(v @ 0...999_999_999) if self.second.is_some() => v,
            _ => return None
        };

        NaiveTime::from_hms_nano_opt(hour, minute, second, nano)
    }

    /// Returns a parsed naive date and time out of given fields.
    /// If the input is insufficient, ambiguous or inconsistent, returns `None` instead.
    ///
    /// This method is able to determine the combined date and time
    /// from date and time fields or a single `timestamp` field.
    /// Either way those fields have to be consistent to each other.
    pub fn to_naive_datetime(&self) -> Option<NaiveDateTime> {
        let date = self.to_naive_date();
        let time = self.to_naive_time();
        if let (Some(date), Some(time)) = (date, time) {
            let datetime = date.and_time(time);

            // verify the timestamp field if any
            let timestamp = datetime.num_seconds_from_unix_epoch();
            if let Some(given_timestamp) = self.timestamp {
                // if `datetime` represents a leap second, it might be off by one second.
                if given_timestamp != timestamp &&
                   !(datetime.nanosecond() >= 1_000_000_000 && given_timestamp != timestamp + 1) {
                    return None;
                }
            }

            Some(datetime)
        } else if let Some(timestamp) = self.timestamp {
            // reconstruct date and time fields from timestamp
            let datetime =
                try_opt!(NaiveDateTime::from_num_seconds_from_unix_epoch_opt(timestamp, 0));

            // fill year, month, day, hour, minute and second fields from timestamp.
            // if existing fields are consistent, this will allow the full date/time reconstruction.
            let mut parsed = self.clone();
            if !parsed.set_year  (datetime.year()   as i64) { return None; }
            if !parsed.set_month (datetime.month()  as i64) { return None; }
            if !parsed.set_day   (datetime.day()    as i64) { return None; }
            if !parsed.set_hour  (datetime.hour()   as i64) { return None; }
            if !parsed.set_minute(datetime.minute() as i64) { return None; }
            if !(parsed.second == Some(60) && datetime.second() == 59) {
                // `datetime.second` cannot be 60, so we can know if this is a leap second
                // only when the original `parsed` had that. do not try to reset it.
                if !parsed.set_second(datetime.second() as i64) { return None; }
            }

            // validate other fields (e.g. week) and return
            let date = try_opt!(self.to_naive_date());
            let time = try_opt!(self.to_naive_time());
            Some(date.and_time(time))
        } else {
            None
        }
    }

    /// Returns a parsed fixed time zone offset out of given fields.
    pub fn to_fixed_offset(&self) -> Option<FixedOffset> {
        self.offset.and_then(|offset| FixedOffset::east_opt(offset))
    }
}

#[cfg(test)]
mod tests {
    use super::Parsed;
    use Datelike;
    use naive::date::{self, NaiveDate};
    use naive::time::NaiveTime;

    #[test]
    fn test_parsed_set_fields() {
        // year*, isoyear*
        let mut p = Parsed::new();
        assert!(p.set_year(1987));
        assert!(!p.set_year(1986));
        assert!(!p.set_year(1988));
        assert!(p.set_year(1987));
        assert!(!p.set_year_div_100(18));
        assert!(p.set_year_div_100(19));
        assert!(!p.set_year_div_100(20));
        assert!(!p.set_year_mod_100(86));
        assert!(p.set_year_mod_100(87));
        assert!(!p.set_year_mod_100(88));

        let mut p = Parsed::new();
        assert!(p.set_year_div_100(20));
        assert!(p.set_year_mod_100(15));
        assert!(!p.set_year(2014));
        assert!(!p.set_year(1915));
        assert!(p.set_year(2015));

        let mut p = Parsed::new();
        assert!(!p.set_year(-1));
        assert!(!p.set_year_div_100(-1));
        assert!(!p.set_year_mod_100(-1));
        assert!(p.set_year(0));
        assert!(p.set_year_div_100(0));
        assert!(p.set_year_mod_100(0));

        let mut p = Parsed::new();
        assert!(p.set_year_div_100(8));
        assert!(!p.set_year_div_100(0x1_0000_0008));

        // month, week*, isoweek, ordinal, day, minute, second, nanosecond, offset
        let mut p = Parsed::new();
        assert!(p.set_month(7));
        assert!(!p.set_month(1));
        assert!(!p.set_month(6));
        assert!(!p.set_month(8));
        assert!(!p.set_month(12));

        let mut p = Parsed::new();
        assert!(p.set_month(8));
        assert!(!p.set_month(0x1_0000_0008));

        // hour
        let mut p = Parsed::new();
        assert!(p.set_hour(12));
        assert!(!p.set_hour(11));
        assert!(!p.set_hour(13));
        assert!(p.set_hour(12));
        assert!(!p.set_ampm(false));
        assert!(p.set_ampm(true));
        assert!(p.set_hour12(12));
        assert!(!p.set_hour12(0)); // requires canonical representation
        assert!(!p.set_hour12(1));
        assert!(!p.set_hour12(11));

        let mut p = Parsed::new();
        assert!(p.set_ampm(true));
        assert!(p.set_hour12(7));
        assert!(!p.set_hour(7));
        assert!(!p.set_hour(18));
        assert!(p.set_hour(19));

        // timestamp
        let mut p = Parsed::new();
        assert!(p.set_timestamp(1_234_567_890));
        assert!(!p.set_timestamp(1_234_567_889));
        assert!(!p.set_timestamp(1_234_567_891));
    }

    #[test]
    fn test_parsed_to_naive_date() {
        macro_rules! parse {
            ($($k:ident: $v:expr),*) => (
                Parsed { $($k: Some($v),)* ..Parsed::new() }.to_naive_date()
            )
        }

        let ymd = |&: y,m,d| Some(NaiveDate::from_ymd(y, m, d));

        // omission of fields
        assert_eq!(parse!(), None);
        assert_eq!(parse!(year_div_100: 19), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84, month: 1), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84, month: 1, day: 2), ymd(1984, 1, 2));
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84, day: 2), None);
        assert_eq!(parse!(year_div_100: 19, month: 1, day: 2), None);

        // out-of-range conditions
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84, month: 2, day: 29), ymd(1984, 2, 29));
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 83, month: 2, day: 29), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 83, month: 13, day: 1), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 83, month: 12, day: 31),
                   ymd(1983, 12, 31));
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 83, month: 12, day: 32), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 83, month: 12, day: 0), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 100, month: 1, day: 1), None);
        let max_year = date::MAX.year();
        assert_eq!(parse!(year_div_100: max_year as u32 / 100,
                          year_mod_100: max_year as u32 % 100, month: 1, day: 1),
                   ymd(max_year, 1, 1));
        assert_eq!(parse!(year_div_100: (max_year + 1) as u32 / 100,
                          year_mod_100: (max_year + 1) as u32 % 100, month: 1, day: 1),
                   None);

        // TODO more tests
    }

    #[test]
    fn test_parsed_to_naive_time() {
        macro_rules! parse {
            ($($k:ident: $v:expr),*) => (
                Parsed { $($k: Some($v),)* ..Parsed::new() }.to_naive_time()
            )
        }

        let hms = |&: h,m,s| Some(NaiveTime::from_hms(h, m, s));
        let hmsn = |&: h,m,s,n| Some(NaiveTime::from_hms_nano(h, m, s, n));

        // omission of fields
        assert_eq!(parse!(), None);
        assert_eq!(parse!(hour_div_12: 0), None);
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1), None);
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23), hms(1,23,0));
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 45), hms(1,23,45));
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 45,
                          nanosecond: 678_901_234),
                   hmsn(1,23,45,678_901_234));
        assert_eq!(parse!(hour_div_12: 1, hour_mod_12: 11, minute: 45, second: 6), hms(23,45,6));
        assert_eq!(parse!(hour_mod_12: 1, minute: 23), None);
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23,
                          nanosecond: 456_789_012),
                   None);

        // TODO more tests
    }
}

