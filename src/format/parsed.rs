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
use offset::{Offset, FixedOffset};
use naive::date::NaiveDate;
use naive::time::NaiveTime;
use naive::datetime::NaiveDateTime;
use datetime::DateTime;

/// Parsed parts of date and time.
#[allow(missing_copy_implementations)]
#[derive(Clone, PartialEq, Debug)]
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
                let firstweek = match newyear.weekday() {
                    Weekday::Sun => 0,
                    Weekday::Mon => 6,
                    Weekday::Tue => 5,
                    Weekday::Wed => 4,
                    Weekday::Thu => 3,
                    Weekday::Fri => 2,
                    Weekday::Sat => 1,
                };

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
                let firstweek = match newyear.weekday() {
                    Weekday::Sun => 1,
                    Weekday::Mon => 0,
                    Weekday::Tue => 6,
                    Weekday::Wed => 5,
                    Weekday::Thu => 4,
                    Weekday::Fri => 3,
                    Weekday::Sat => 2,
                };

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
            60 => (59, 1_000_000_000),
            _ => return None
        };
        nano += match self.nanosecond {
            None => 0,
            Some(v @ 0...999_999_999) if self.second.is_some() => v,
            _ => return None
        };

        NaiveTime::from_hms_nano_opt(hour, minute, second, nano)
    }

    /// Returns a parsed naive date and time out of given fields,
    /// except for the `offset` field (assumed to have a given value).
    /// If the input is insufficient, ambiguous or inconsistent, returns `None` instead.
    ///
    /// This method is able to determine the combined date and time
    /// from date and time fields or a single `timestamp` field.
    /// Either way those fields have to be consistent to each other.
    fn to_naive_datetime_with_offset(&self, offset: i32) -> Option<NaiveDateTime> {
        let date = self.to_naive_date();
        let time = self.to_naive_time();
        if let (Some(date), Some(time)) = (date, time) {
            let datetime = date.and_time(time);

            // verify the timestamp field if any
            // the following is safe, `num_seconds_from_unix_epoch` is very limited in range
            let timestamp = datetime.num_seconds_from_unix_epoch() - offset as i64;
            if let Some(given_timestamp) = self.timestamp {
                // if `datetime` represents a leap second, it might be off by one second.
                if given_timestamp != timestamp &&
                   !(datetime.nanosecond() >= 1_000_000_000 && given_timestamp == timestamp + 1) {
                    return None;
                }
            }

            Some(datetime)
        } else if let Some(timestamp) = self.timestamp {
            // reconstruct date and time fields from timestamp
            let ts = try_opt!(timestamp.checked_add(offset as i64));
            let mut datetime = try_opt!(NaiveDateTime::from_num_seconds_from_unix_epoch_opt(ts, 0));

            // fill year, ordinal, hour, minute and second fields from timestamp.
            // if existing fields are consistent, this will allow the full date/time reconstruction.
            let mut parsed = self.clone();
            if parsed.second == Some(60) {
                // `datetime.second()` cannot be 60, so this is the only case for a leap second.
                match datetime.second() {
                    // it's okay, just do not try to overwrite the existing field.
                    59 => {}
                    // `datetime` is known to be off by one second.
                    0 => { datetime = datetime - Duration::seconds(1); }
                    // otherwise it is impossible.
                    _ => return None
                }
                // ...and we have the correct candidates for other fields.
            } else {
                if !parsed.set_second(datetime.second() as i64) { return None; }
            }
            if !parsed.set_year   (datetime.year()    as i64) { return None; }
            if !parsed.set_ordinal(datetime.ordinal() as i64) { return None; }
            if !parsed.set_hour   (datetime.hour()    as i64) { return None; }
            if !parsed.set_minute (datetime.minute()  as i64) { return None; }
            if !parsed.set_nanosecond(0) { return None; } // no nanosecond precision in timestamp

            // validate other fields (e.g. week) and return
            let date = try_opt!(parsed.to_naive_date());
            let time = try_opt!(parsed.to_naive_time());
            Some(date.and_time(time))
        } else {
            None
        }
    }

    /// Returns a parsed naive date and time out of given fields assuming UTC.
    /// If the input is insufficient, ambiguous or inconsistent, returns `None` instead.
    ///
    /// This method is able to determine the combined date and time
    /// from date and time fields (assumed to be UTC) or a single `timestamp` field.
    /// Either way those fields have to be consistent to each other.
    pub fn to_naive_datetime_utc(&self) -> Option<NaiveDateTime> {
        self.to_naive_datetime_with_offset(0)
    }

    /// Returns a parsed fixed time zone offset out of given fields.
    pub fn to_fixed_offset(&self) -> Option<FixedOffset> {
        self.offset.and_then(|offset| FixedOffset::east_opt(offset))
    }

    /// Returns a parsed timezone-aware date and time out of given fields.
    /// If the input is insufficient, ambiguous or inconsistent, returns `None` instead.
    ///
    /// This method is able to determine the combined date and time
    /// from date and time fields or a single `timestamp` field, plus a time zone offset.
    /// Either way those fields have to be consistent to each other.
    pub fn to_datetime(&self) -> Option<DateTime<FixedOffset>> {
        let offset = try_opt!(self.offset);
        let datetime = try_opt!(self.to_naive_datetime_with_offset(offset));
        let offset = try_opt!(FixedOffset::east_opt(offset));
        offset.from_local_datetime(&datetime).single()
    }
}

#[cfg(test)]
mod tests {
    use super::Parsed;
    use Datelike;
    use Weekday;
    use naive::date::{self, NaiveDate};
    use naive::time::NaiveTime;
    use offset::{Offset, FixedOffset};

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

        // ymd: omission of fields
        assert_eq!(parse!(), None);
        assert_eq!(parse!(year_div_100: 19), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84, month: 1), None);
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84, month: 1, day: 2), ymd(1984, 1, 2));
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84, day: 2), None);
        assert_eq!(parse!(year_div_100: 19, month: 1, day: 2), None);
        assert_eq!(parse!(year_mod_100: 70, month: 1, day: 2), ymd(1970, 1, 2));
        assert_eq!(parse!(year_mod_100: 69, month: 1, day: 2), ymd(2069, 1, 2));

        // ymd: out-of-range conditions
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

        // weekdates
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 0), None);
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 0), None);
        assert_eq!(parse!(year_mod_100: 0, weekday: Weekday::Sun), None);
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 0, weekday: Weekday::Fri), None);
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 0, weekday: Weekday::Fri), None);
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 0, weekday: Weekday::Sat), ymd(2000,1,1));
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 0, weekday: Weekday::Sat), ymd(2000,1,1));
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 0, weekday: Weekday::Sun), ymd(2000,1,2));
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 1, weekday: Weekday::Sun), ymd(2000,1,2));
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 1, weekday: Weekday::Mon), ymd(2000,1,3));
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 1, weekday: Weekday::Mon), ymd(2000,1,3));
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 1, weekday: Weekday::Sat), ymd(2000,1,8));
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 1, weekday: Weekday::Sat), ymd(2000,1,8));
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 1, weekday: Weekday::Sun), ymd(2000,1,9));
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 2, weekday: Weekday::Sun), ymd(2000,1,9));
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 2, weekday: Weekday::Mon),
                   ymd(2000,1,10));
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 52, weekday: Weekday::Sat),
                   ymd(2000,12,30));
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 53, weekday: Weekday::Sun),
                   ymd(2000,12,31));
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 53, weekday: Weekday::Mon), None);
        assert_eq!(parse!(year_mod_100: 0, week_from_sun: 0xffffffff, weekday: Weekday::Mon), None);
        assert_eq!(parse!(year_mod_100: 6, week_from_sun: 0, weekday: Weekday::Sat), None);
        assert_eq!(parse!(year_mod_100: 6, week_from_sun: 1, weekday: Weekday::Sun), ymd(2006,1,1));

        // weekdates: conflicting inputs
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 1, week_from_sun: 1,
                          weekday: Weekday::Sat),
                   ymd(2000,1,8));
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 1, week_from_sun: 2,
                          weekday: Weekday::Sun),
                   ymd(2000,1,9));
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 1, week_from_sun: 1,
                          weekday: Weekday::Sun),
                   None);
        assert_eq!(parse!(year_mod_100: 0, week_from_mon: 2, week_from_sun: 2,
                          weekday: Weekday::Sun),
                   None);

        // ISO weekdates
        assert_eq!(parse!(isoyear_mod_100: 4, isoweek: 53), None);
        assert_eq!(parse!(isoyear_mod_100: 4, isoweek: 53, weekday: Weekday::Fri), ymd(2004,12,31));
        assert_eq!(parse!(isoyear_mod_100: 4, isoweek: 53, weekday: Weekday::Sat), ymd(2005,1,1));
        assert_eq!(parse!(isoyear_mod_100: 4, isoweek: 0xffffffff, weekday: Weekday::Sat), None);
        assert_eq!(parse!(isoyear_mod_100: 5, isoweek: 0, weekday: Weekday::Thu), None);
        assert_eq!(parse!(isoyear_mod_100: 5, isoweek: 5, weekday: Weekday::Thu), ymd(2005,2,3));
        assert_eq!(parse!(isoyear_mod_100: 5, weekday: Weekday::Thu), None);

        // year and ordinal
        assert_eq!(parse!(ordinal: 123), None);
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 0, ordinal: 0), None);
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 0, ordinal: 1), ymd(2000,1,1));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 0, ordinal: 60), ymd(2000,2,29));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 0, ordinal: 61), ymd(2000,3,1));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 0, ordinal: 366), ymd(2000,12,31));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 0, ordinal: 367), None);
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 0, ordinal: 0xffffffff), None);
        assert_eq!(parse!(year_div_100: 21, year_mod_100: 0, ordinal: 0), None);
        assert_eq!(parse!(year_div_100: 21, year_mod_100: 0, ordinal: 1), ymd(2100,1,1));
        assert_eq!(parse!(year_div_100: 21, year_mod_100: 0, ordinal: 59), ymd(2100,2,28));
        assert_eq!(parse!(year_div_100: 21, year_mod_100: 0, ordinal: 60), ymd(2100,3,1));
        assert_eq!(parse!(year_div_100: 21, year_mod_100: 0, ordinal: 365), ymd(2100,12,31));
        assert_eq!(parse!(year_div_100: 21, year_mod_100: 0, ordinal: 366), None);
        assert_eq!(parse!(year_div_100: 21, year_mod_100: 0, ordinal: 0xffffffff), None);

        // more complex cases
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 14, month: 12, day: 31, ordinal: 365,
                          isoyear_div_100: 20, isoyear_mod_100: 15, isoweek: 1,
                          week_from_sun: 52, week_from_mon: 52, weekday: Weekday::Wed),
                   ymd(2014, 12, 31));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 14, month: 12, ordinal: 365,
                          isoyear_div_100: 20, isoyear_mod_100: 15, isoweek: 1,
                          week_from_sun: 52, week_from_mon: 52),
                   ymd(2014, 12, 31));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 14, month: 12, day: 31, ordinal: 365,
                          isoyear_div_100: 20, isoyear_mod_100: 14, isoweek: 53,
                          week_from_sun: 52, week_from_mon: 52, weekday: Weekday::Wed),
                   None); // inconsistent (no ISO week date 2014-W53-3)
        assert_eq!(parse!(year_div_100: 20, month: 12, isoyear_div_100: 20, isoyear_mod_100: 15,
                          isoweek: 1, week_from_sun: 52, week_from_mon: 52),
                   None); // ambiguous (2014-12-29, 2014-12-30, 2014-12-31)
        assert_eq!(parse!(year_div_100: 20, isoyear_mod_100: 15, ordinal: 366),
                   None); // technically not ambiguous (2014-12-31) but made so to avoid complexity
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

        // out-of-range conditions
        assert_eq!(parse!(hour_div_12: 2, hour_mod_12: 0, minute: 0), None);
        assert_eq!(parse!(hour_div_12: 1, hour_mod_12: 12, minute: 0), None);
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 60), None);
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 61), None);
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 34,
                          nanosecond: 1_000_000_000),
                   None);

        // leap seconds
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 60),
                   hmsn(1,23,59,1_000_000_000));
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 60,
                          nanosecond: 999_999_999),
                   hmsn(1,23,59,1_999_999_999));
    }

    #[test]
    fn test_parsed_to_naive_datetime_utc() {
        macro_rules! parse {
            ($($k:ident: $v:expr),*) => (
                Parsed { $($k: Some($v),)* ..Parsed::new() }.to_naive_datetime_utc()
            )
        }

        let ymdhms = |&: y,m,d,h,n,s| Some(NaiveDate::from_ymd(y, m, d).and_hms(h, n, s));
        let ymdhmsn =
            |&: y,m,d,h,n,s,nano| Some(NaiveDate::from_ymd(y, m, d).and_hms_nano(h, n, s, nano));

        // omission of fields
        assert_eq!(parse!(), None);
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 15, month: 1, day: 30,
                          hour_div_12: 1, hour_mod_12: 2, minute: 38),
                   ymdhms(2015,1,30, 14,38,0));
        assert_eq!(parse!(year_mod_100: 97, month: 1, day: 30,
                          hour_div_12: 1, hour_mod_12: 2, minute: 38, second: 5),
                   ymdhms(1997,1,30, 14,38,5));
        assert_eq!(parse!(year_mod_100: 12, ordinal: 34, hour_div_12: 0, hour_mod_12: 5,
                          minute: 6, second: 7, nanosecond: 890_123_456),
                   ymdhmsn(2012,2,3, 5,6,7,890_123_456));
        assert_eq!(parse!(timestamp: 0), ymdhms(1970,1,1, 0,0,0));
        assert_eq!(parse!(timestamp: 1, nanosecond: 0), ymdhms(1970,1,1, 0,0,1));
        assert_eq!(parse!(timestamp: 1, nanosecond: 1), None);
        assert_eq!(parse!(timestamp: 1_420_000_000), ymdhms(2014,12,31, 4,26,40));
        assert_eq!(parse!(timestamp: -0x1_0000_0000), ymdhms(1833,11,24, 17,31,44));

        // full fields
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 14, month: 12, day: 31, ordinal: 365,
                          isoyear_div_100: 20, isoyear_mod_100: 15, isoweek: 1,
                          week_from_sun: 52, week_from_mon: 52, weekday: Weekday::Wed,
                          hour_div_12: 0, hour_mod_12: 4, minute: 26, second: 40,
                          nanosecond: 12_345_678, timestamp: 1_420_000_000),
                   ymdhmsn(2014,12,31, 4,26,40,12_345_678));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 14, month: 12, day: 31, ordinal: 365,
                          isoyear_div_100: 20, isoyear_mod_100: 15, isoweek: 1,
                          week_from_sun: 52, week_from_mon: 52, weekday: Weekday::Wed,
                          hour_div_12: 0, hour_mod_12: 4, minute: 26, second: 40,
                          nanosecond: 12_345_678, timestamp: 1_419_999_999),
                   None);

        // more timestamps
        let max_days_from_year_1970 = date::MAX - NaiveDate::from_ymd(1970,1,1);
        let year_0_from_year_1970 = NaiveDate::from_ymd(0,1,1) - NaiveDate::from_ymd(1970,1,1);
        // XXX does not work, reparsing requires the proper handling of years before 0
        //let min_days_from_year_1970 = date::MIN - NaiveDate::from_ymd(1970,1,1);
        //assert_eq!(parse!(timestamp: min_days_from_year_1970.num_seconds()),
        //           ymdhms(date::MIN.year(),1,1, 0,0,0));
        assert_eq!(parse!(timestamp: year_0_from_year_1970.num_seconds()),
                   ymdhms(0,1,1, 0,0,0));
        assert_eq!(parse!(timestamp: max_days_from_year_1970.num_seconds() + 86399),
                   ymdhms(date::MAX.year(),12,31, 23,59,59));

        // leap seconds #1: partial fields
        assert_eq!(parse!(second: 59, timestamp: 1_341_100_798), None);
        assert_eq!(parse!(second: 59, timestamp: 1_341_100_799), ymdhms(2012,6,30, 23,59,59));
        assert_eq!(parse!(second: 59, timestamp: 1_341_100_800), None);
        assert_eq!(parse!(second: 60, timestamp: 1_341_100_799),
                   ymdhmsn(2012,6,30, 23,59,59,1_000_000_000));
        assert_eq!(parse!(second: 60, timestamp: 1_341_100_800),
                   ymdhmsn(2012,6,30, 23,59,59,1_000_000_000));
        assert_eq!(parse!(second: 0, timestamp: 1_341_100_800), ymdhms(2012,7,1, 0,0,0));
        assert_eq!(parse!(second: 1, timestamp: 1_341_100_800), None);
        assert_eq!(parse!(second: 60, timestamp: 1_341_100_801), None);

        // leap seconds #2: full fields
        // we need to have separate tests for them since it uses another control flow.
        assert_eq!(parse!(year_mod_100: 12, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 59, timestamp: 1_341_100_798),
                   None);
        assert_eq!(parse!(year_mod_100: 12, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 59, timestamp: 1_341_100_799),
                   ymdhms(2012,6,30, 23,59,59));
        assert_eq!(parse!(year_mod_100: 12, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 59, timestamp: 1_341_100_800),
                   None);
        assert_eq!(parse!(year_mod_100: 12, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 60, timestamp: 1_341_100_799),
                   ymdhmsn(2012,6,30, 23,59,59,1_000_000_000));
        assert_eq!(parse!(year_mod_100: 12, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 60, timestamp: 1_341_100_800),
                   ymdhmsn(2012,6,30, 23,59,59,1_000_000_000));
        assert_eq!(parse!(year_mod_100: 12, ordinal: 183, hour_div_12: 0, hour_mod_12: 0,
                          minute: 0, second: 0, timestamp: 1_341_100_800),
                   ymdhms(2012,7,1, 0,0,0));
        assert_eq!(parse!(year_mod_100: 12, ordinal: 183, hour_div_12: 0, hour_mod_12: 0,
                          minute: 0, second: 1, timestamp: 1_341_100_800),
                   None);
        assert_eq!(parse!(year_mod_100: 12, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 60, timestamp: 1_341_100_801),
                   None);
    }

    #[test]
    fn test_parsed_to_datetime() {
        macro_rules! parse {
            ($($k:ident: $v:expr),*) => (
                Parsed { $($k: Some($v),)* ..Parsed::new() }.to_datetime()
            )
        }

        let ymdhmsn =
            |&: y,m,d,h,n,s,nano,off| Some(FixedOffset::east(off).ymd(y, m, d)
                                                                 .and_hms_nano(h, n, s, nano));

        assert_eq!(parse!(offset: 0), None);
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 14, ordinal: 365, hour_div_12: 0,
                          hour_mod_12: 4, minute: 26, second: 40, nanosecond: 12_345_678),
                   None);
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 14, ordinal: 365,
                          hour_div_12: 0, hour_mod_12: 4, minute: 26, second: 40,
                          nanosecond: 12_345_678, offset: 0),
                   ymdhmsn(2014,12,31, 4,26,40,12_345_678, 0));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 14, ordinal: 365,
                          hour_div_12: 1, hour_mod_12: 1, minute: 26, second: 40,
                          nanosecond: 12_345_678, offset: 32400),
                   ymdhmsn(2014,12,31, 13,26,40,12_345_678, 32400));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 14, ordinal: 365,
                          hour_div_12: 0, hour_mod_12: 1, minute: 42, second: 4,
                          nanosecond: 12_345_678, offset: -9876),
                   ymdhmsn(2014,12,31, 1,42,4,12_345_678, -9876));
        assert_eq!(parse!(year_div_100: 20, year_mod_100: 15, ordinal: 1,
                          hour_div_12: 0, hour_mod_12: 4, minute: 26, second: 40,
                          nanosecond: 12_345_678, offset: 86400),
                   None); // `FixedOffset` does not support such huge offset
    }
}

