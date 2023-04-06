// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! A collection of parsed date and time items.
//! They can be constructed incrementally while being checked for consistency.

use core::convert::TryFrom;

use num_integer::div_rem;

use crate::naive::{NaiveDate, NaiveDateTime, NaiveTime};
use crate::offset::{FixedOffset, Offset, TimeZone};
use crate::{DateTime, Datelike, Error, TimeDelta, Timelike, Weekday};

/// Parsed parts of date and time. There are two classes of methods:
///
/// - `set_*` methods try to set given field(s) while checking for the consistency.
///   It may or may not check for the range constraint immediately (for efficiency reasons).
///
/// - `to_*` methods try to make a concrete date and time value out of set fields.
///   It fully checks any remaining out-of-range conditions and inconsistent/impossible fields.
#[non_exhaustive]
#[derive(Clone, PartialEq, Eq, Debug, Default, Hash)]
pub struct Parsed {
    /// Year.
    ///
    /// This can be negative unlike [`year_div_100`](#structfield.year_div_100)
    /// and [`year_mod_100`](#structfield.year_mod_100) fields.
    pub year: Option<i32>,

    /// Year divided by 100. Implies that the year is >= 1 BCE when set.
    ///
    /// Due to the common usage, if this field is missing but
    /// [`year_mod_100`](#structfield.year_mod_100) is present,
    /// it is inferred to 19 when `year_mod_100 >= 70` and 20 otherwise.
    pub year_div_100: Option<i32>,

    /// Year modulo 100. Implies that the year is >= 1 BCE when set.
    pub year_mod_100: Option<i32>,

    /// Year in the [ISO week date](../naive/struct.NaiveDate.html#week-date).
    ///
    /// This can be negative unlike [`isoyear_div_100`](#structfield.isoyear_div_100) and
    /// [`isoyear_mod_100`](#structfield.isoyear_mod_100) fields.
    pub isoyear: Option<i32>,

    /// Year in the [ISO week date](../naive/struct.NaiveDate.html#week-date), divided by 100.
    /// Implies that the year is >= 1 BCE when set.
    ///
    /// Due to the common usage, if this field is missing but
    /// [`isoyear_mod_100`](#structfield.isoyear_mod_100) is present,
    /// it is inferred to 19 when `isoyear_mod_100 >= 70` and 20 otherwise.
    pub isoyear_div_100: Option<i32>,

    /// Year in the [ISO week date](../naive/struct.NaiveDate.html#week-date), modulo 100.
    /// Implies that the year is >= 1 BCE when set.
    pub isoyear_mod_100: Option<i32>,

    /// Month (1--12).
    pub month: Option<u32>,

    /// Week number, where the week 1 starts at the first Sunday of January
    /// (0--53, 1--53 or 1--52 depending on the year).
    pub week_from_sun: Option<u32>,

    /// Week number, where the week 1 starts at the first Monday of January
    /// (0--53, 1--53 or 1--52 depending on the year).
    pub week_from_mon: Option<u32>,

    /// [ISO week number](../naive/struct.NaiveDate.html#week-date)
    /// (1--52 or 1--53 depending on the year).
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

    /// The number of non-leap seconds since the midnight UTC on January 1, 1970.
    ///
    /// This can be off by one if [`second`](#structfield.second) is 60 (a leap second).
    pub timestamp: Option<i64>,

    /// Offset from the local time to UTC, in seconds.
    pub offset: Option<i32>,
}

/// Checks if `old` is either empty or has the same value as `new` (i.e. "consistent"),
/// and if it is empty, set `old` to `new` as well.
#[inline]
fn set_if_consistent<T: PartialEq>(old: &mut Option<T>, new: T) -> Result<(), Error> {
    if let Some(ref old) = *old {
        if *old == new {
            Ok(())
        } else {
            Err(Error::ParsingImpossible)
        }
    } else {
        *old = Some(new);
        Ok(())
    }
}

impl Parsed {
    /// Returns the initial value of parsed parts.
    pub fn new() -> Parsed {
        Parsed::default()
    }

    /// Tries to set the [`year`](#structfield.year) field from given value.
    #[inline]
    pub fn set_year(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.year,
            i32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`year_div_100`](#structfield.year_div_100) field from given value.
    #[inline]
    pub fn set_year_div_100(&mut self, value: i64) -> Result<(), Error> {
        if value < 0 {
            return Err(Error::ParsingOutOfRange);
        }
        set_if_consistent(
            &mut self.year_div_100,
            i32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`year_mod_100`](#structfield.year_mod_100) field from given value.
    #[inline]
    pub fn set_year_mod_100(&mut self, value: i64) -> Result<(), Error> {
        if value < 0 {
            return Err(Error::ParsingOutOfRange);
        }
        set_if_consistent(
            &mut self.year_mod_100,
            i32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`isoyear`](#structfield.isoyear) field from given value.
    #[inline]
    pub fn set_isoyear(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.isoyear,
            i32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`isoyear_div_100`](#structfield.isoyear_div_100) field from given value.
    #[inline]
    pub fn set_isoyear_div_100(&mut self, value: i64) -> Result<(), Error> {
        if value < 0 {
            return Err(Error::ParsingOutOfRange);
        }
        set_if_consistent(
            &mut self.isoyear_div_100,
            i32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`isoyear_mod_100`](#structfield.isoyear_mod_100) field from given value.
    #[inline]
    pub fn set_isoyear_mod_100(&mut self, value: i64) -> Result<(), Error> {
        if value < 0 {
            return Err(Error::ParsingOutOfRange);
        }
        set_if_consistent(
            &mut self.isoyear_mod_100,
            i32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`month`](#structfield.month) field from given value.
    #[inline]
    pub fn set_month(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.month,
            u32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`week_from_sun`](#structfield.week_from_sun) field from given value.
    #[inline]
    pub fn set_week_from_sun(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.week_from_sun,
            u32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`week_from_mon`](#structfield.week_from_mon) field from given value.
    #[inline]
    pub fn set_week_from_mon(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.week_from_mon,
            u32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`isoweek`](#structfield.isoweek) field from given value.
    #[inline]
    pub fn set_isoweek(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.isoweek,
            u32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`weekday`](#structfield.weekday) field from given value.
    #[inline]
    pub fn set_weekday(&mut self, value: Weekday) -> Result<(), Error> {
        set_if_consistent(&mut self.weekday, value)
    }

    /// Tries to set the [`ordinal`](#structfield.ordinal) field from given value.
    #[inline]
    pub fn set_ordinal(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.ordinal,
            u32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`day`](#structfield.day) field from given value.
    #[inline]
    pub fn set_day(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.day,
            u32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`hour_div_12`](#structfield.hour_div_12) field from given value.
    /// (`false` for AM, `true` for PM)
    #[inline]
    pub fn set_ampm(&mut self, value: bool) -> Result<(), Error> {
        set_if_consistent(&mut self.hour_div_12, u32::from(value))
    }

    /// Tries to set the [`hour_mod_12`](#structfield.hour_mod_12) field from
    /// given hour number in 12-hour clocks.
    #[inline]
    pub fn set_hour12(&mut self, value: i64) -> Result<(), Error> {
        if !(1..=12).contains(&value) {
            return Err(Error::ParsingOutOfRange);
        }
        set_if_consistent(&mut self.hour_mod_12, value as u32 % 12)
    }

    /// Tries to set both [`hour_div_12`](#structfield.hour_div_12) and
    /// [`hour_mod_12`](#structfield.hour_mod_12) fields from given value.
    #[inline]
    pub fn set_hour(&mut self, value: i64) -> Result<(), Error> {
        let v = u32::try_from(value)?;
        set_if_consistent(&mut self.hour_div_12, v / 12)?;
        set_if_consistent(&mut self.hour_mod_12, v % 12)?;
        Ok(())
    }

    /// Tries to set the [`minute`](#structfield.minute) field from given value.
    #[inline]
    pub fn set_minute(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.minute,
            u32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`second`](#structfield.second) field from given value.
    #[inline]
    pub fn set_second(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.second,
            u32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`nanosecond`](#structfield.nanosecond) field from given value.
    #[inline]
    pub fn set_nanosecond(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.nanosecond,
            u32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Tries to set the [`timestamp`](#structfield.timestamp) field from given value.
    #[inline]
    pub fn set_timestamp(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(&mut self.timestamp, value)
    }

    /// Tries to set the [`offset`](#structfield.offset) field from given value.
    #[inline]
    pub fn set_offset(&mut self, value: i64) -> Result<(), Error> {
        set_if_consistent(
            &mut self.offset,
            i32::try_from(value).map_err(|_| Error::ParsingOutOfRange)?,
        )
    }

    /// Returns a parsed naive date out of given fields.
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
    pub fn to_naive_date(&self) -> Result<NaiveDate, Error> {
        fn resolve_year(
            y: Option<i32>,
            q: Option<i32>,
            r: Option<i32>,
        ) -> Result<Option<i32>, Error> {
            match (y, q, r) {
                // if there is no further information, simply return the given full year.
                // this is a common case, so let's avoid division here.
                (y, None, None) => Ok(y),

                // if there is a full year *and* also quotient and/or modulo,
                // check if present quotient and/or modulo is consistent to the full year.
                // since the presence of those fields means a positive full year,
                // we should filter a negative full year first.
                (Some(y), q, r @ Some(0..=99)) | (Some(y), q, r @ None) => {
                    if y < 0 {
                        return Err(Error::ParsingOutOfRange);
                    }
                    let (q_, r_) = div_rem(y, 100);
                    if q.unwrap_or(q_) == q_ && r.unwrap_or(r_) == r_ {
                        Ok(Some(y))
                    } else {
                        Err(Error::ParsingImpossible)
                    }
                }

                // the full year is missing but we have quotient and modulo.
                // reconstruct the full year. make sure that the result is always positive.
                (None, Some(q), Some(r @ 0..=99)) => {
                    if q < 0 {
                        return Err(Error::ParsingOutOfRange);
                    }
                    let y = q.checked_mul(100).and_then(|v| v.checked_add(r));
                    Ok(Some(y.ok_or(Error::ParsingOutOfRange)?))
                }

                // we only have modulo. try to interpret a modulo as a conventional two-digit year.
                // note: we are affected by Rust issue #18060. avoid multiple range patterns.
                (None, None, Some(r @ 0..=99)) => Ok(Some(r + if r < 70 { 2000 } else { 1900 })),

                // otherwise it is an out-of-bound or insufficient condition.
                (None, Some(_), None) => Err(Error::ParsingNotEnough),
                (_, _, Some(_)) => Err(Error::ParsingOutOfRange),
            }
        }

        let given_year = resolve_year(self.year, self.year_div_100, self.year_mod_100)?;
        let given_isoyear = resolve_year(self.isoyear, self.isoyear_div_100, self.isoyear_mod_100)?;

        // verify the normal year-month-day date.
        let verify_ymd = |date: NaiveDate| {
            let year = date.year();
            let (year_div_100, year_mod_100) = if year >= 0 {
                let (q, r) = div_rem(year, 100);
                (Some(q), Some(r))
            } else {
                (None, None) // they should be empty to be consistent
            };
            let month = date.month();
            let day = date.day();
            self.year.unwrap_or(year) == year
                && self.year_div_100.or(year_div_100) == year_div_100
                && self.year_mod_100.or(year_mod_100) == year_mod_100
                && self.month.unwrap_or(month) == month
                && self.day.unwrap_or(day) == day
        };

        // verify the ISO week date.
        let verify_isoweekdate = |date: NaiveDate| {
            let week = date.iso_week();
            let isoyear = week.year();
            let isoweek = week.week();
            let weekday = date.weekday();
            let (isoyear_div_100, isoyear_mod_100) = if isoyear >= 0 {
                let (q, r) = div_rem(isoyear, 100);
                (Some(q), Some(r))
            } else {
                (None, None) // they should be empty to be consistent
            };
            self.isoyear.unwrap_or(isoyear) == isoyear
                && self.isoyear_div_100.or(isoyear_div_100) == isoyear_div_100
                && self.isoyear_mod_100.or(isoyear_mod_100) == isoyear_mod_100
                && self.isoweek.unwrap_or(isoweek) == isoweek
                && self.weekday.unwrap_or(weekday) == weekday
        };

        // verify the ordinal and other (non-ISO) week dates.
        let verify_ordinal = |date: NaiveDate| {
            let ordinal = date.ordinal();
            let week_from_sun = date.weeks_from(Weekday::Sun);
            let week_from_mon = date.weeks_from(Weekday::Mon);
            self.ordinal.unwrap_or(ordinal) == ordinal
                && self.week_from_sun.map_or(week_from_sun, |v| v as i32) == week_from_sun
                && self.week_from_mon.map_or(week_from_mon, |v| v as i32) == week_from_mon
        };

        // test several possibilities.
        // tries to construct a full `NaiveDate` as much as possible, then verifies that
        // it is consistent with other given fields.
        let (verified, parsed_date) = match (given_year, given_isoyear, self) {
            (Some(year), _, &Parsed { month: Some(month), day: Some(day), .. }) => {
                // year, month, day
                let date = NaiveDate::from_ymd(year, month, day)?;
                (verify_isoweekdate(date) && verify_ordinal(date), date)
            }

            (Some(year), _, &Parsed { ordinal: Some(ordinal), .. }) => {
                // year, day of the year
                let date = NaiveDate::from_yo(year, ordinal)?;
                (verify_ymd(date) && verify_isoweekdate(date) && verify_ordinal(date), date)
            }

            (
                Some(year),
                _,
                &Parsed { week_from_sun: Some(week_from_sun), weekday: Some(weekday), .. },
            ) => {
                // year, week (starting at 1st Sunday), day of the week
                let newyear = NaiveDate::from_yo(year, 1)?;
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
                if week_from_sun > 53 {
                    return Err(Error::ParsingOutOfRange);
                } // can it overflow?
                let ndays = firstweek
                    + (week_from_sun as i32 - 1) * 7
                    + weekday.num_days_from_sunday() as i32;
                let date = newyear.checked_add_signed(TimeDelta::days(i64::from(ndays)))?;
                if date.year() != year {
                    return Err(Error::ParsingOutOfRange);
                } // early exit for correct error

                (verify_ymd(date) && verify_isoweekdate(date) && verify_ordinal(date), date)
            }

            (
                Some(year),
                _,
                &Parsed { week_from_mon: Some(week_from_mon), weekday: Some(weekday), .. },
            ) => {
                // year, week (starting at 1st Monday), day of the week
                let newyear = NaiveDate::from_yo(year, 1)?;
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
                if week_from_mon > 53 {
                    return Err(Error::ParsingOutOfRange);
                } // can it overflow?
                let ndays = firstweek
                    + (week_from_mon as i32 - 1) * 7
                    + weekday.num_days_from_monday() as i32;
                let date = newyear.checked_add_signed(TimeDelta::days(i64::from(ndays)))?;
                if date.year() != year {
                    return Err(Error::ParsingOutOfRange);
                } // early exit for correct error

                (verify_ymd(date) && verify_isoweekdate(date) && verify_ordinal(date), date)
            }

            (_, Some(isoyear), &Parsed { isoweek: Some(isoweek), weekday: Some(weekday), .. }) => {
                // ISO year, week, day of the week
                let date = NaiveDate::from_isoywd(isoyear, isoweek, weekday)?;
                (verify_ymd(date) && verify_ordinal(date), date)
            }

            (_, _, _) => return Err(Error::ParsingNotEnough),
        };

        if verified {
            Ok(parsed_date)
        } else {
            Err(Error::ParsingImpossible)
        }
    }

    /// Returns a parsed naive time out of given fields.
    ///
    /// This method is able to determine the time from given subset of fields:
    ///
    /// - Hour, minute. (second and nanosecond assumed to be 0)
    /// - Hour, minute, second. (nanosecond assumed to be 0)
    /// - Hour, minute, second, nanosecond.
    ///
    /// It is able to handle leap seconds when given second is 60.
    pub fn to_naive_time(&self) -> Result<NaiveTime, Error> {
        let hour_div_12 = match self.hour_div_12 {
            Some(v @ 0..=1) => v,
            Some(_) => return Err(Error::ParsingOutOfRange),
            None => return Err(Error::ParsingNotEnough),
        };
        let hour_mod_12 = match self.hour_mod_12 {
            Some(v @ 0..=11) => v,
            Some(_) => return Err(Error::ParsingOutOfRange),
            None => return Err(Error::ParsingNotEnough),
        };
        let hour = hour_div_12 * 12 + hour_mod_12;

        let minute = match self.minute {
            Some(v @ 0..=59) => v,
            Some(_) => return Err(Error::ParsingOutOfRange),
            None => return Err(Error::ParsingNotEnough),
        };

        // we allow omitting seconds or nanoseconds, but they should be in the range.
        let (second, mut nano) = match self.second.unwrap_or(0) {
            v @ 0..=59 => (v, 0),
            60 => (59, 1_000_000_000),
            _ => return Err(Error::ParsingOutOfRange),
        };
        nano += match self.nanosecond {
            Some(v @ 0..=999_999_999) if self.second.is_some() => v,
            Some(0..=999_999_999) => return Err(Error::ParsingNotEnough), // second is missing
            Some(_) => return Err(Error::ParsingOutOfRange),
            None => 0,
        };

        NaiveTime::from_hms_nano(hour, minute, second, nano)
    }

    /// Returns a parsed naive date and time out of given fields,
    /// except for the [`offset`](#structfield.offset) field (assumed to have a given value).
    /// This is required for parsing a local time or other known-timezone inputs.
    ///
    /// This method is able to determine the combined date and time
    /// from date and time fields or a single [`timestamp`](#structfield.timestamp) field.
    /// Either way those fields have to be consistent to each other.
    pub fn to_naive_datetime_with_offset(&self, offset: i32) -> Result<NaiveDateTime, Error> {
        match (self.to_naive_date(), self.to_naive_time(), self.timestamp) {
            // Both are unproblematic
            (Ok(date), Ok(time), _) => {
                let datetime = date.and_time(time);

                // verify the timestamp field if any
                // the following is safe, `timestamp` is very limited in range
                let timestamp = datetime.timestamp() - i64::from(offset);
                if let Some(given_timestamp) = self.timestamp {
                    // if `datetime` represents a leap second, it might be off by one second.
                    if given_timestamp != timestamp
                        && !(datetime.nanosecond() >= 1_000_000_000
                            && given_timestamp == timestamp + 1)
                    {
                        return Err(Error::ParsingImpossible);
                    }
                }

                Ok(datetime)
            }

            // If either is problematic, fallback on the timestamp
            // TODO, the condition for reconstruction of date and time fields from timestamp is unclear
            (Err(e1), _, Some(ts)) => self.reconstruct_from_timestamp(ts, offset).map_err(|_| e1),
            (_, Err(e2), Some(ts)) => self.reconstruct_from_timestamp(ts, offset).map_err(|_| e2),

            // If both are problematic or timestamp is not available, return the first error
            (Err(e1), _, None) => Err(e1),
            (_, Err(e2), None) => Err(e2),
        }
    }

    fn reconstruct_from_timestamp(
        &self,
        mut timestamp: i64,
        offset: i32,
    ) -> Result<NaiveDateTime, Error> {
        timestamp = timestamp.checked_add(i64::from(offset)).ok_or(Error::ParsingOutOfRange)?;
        let mut datetime = NaiveDateTime::from_timestamp(timestamp, 0)?;

        // fill year, ordinal, hour, minute and second fields from timestamp.
        // if existing fields are consistent, this will allow the full date/time reconstruction.
        let mut parsed = self.clone();
        if parsed.second == Some(60) {
            // `datetime.second()` cannot be 60, so this is the only case for a leap second.
            match datetime.second() {
                // it's okay, just do not try to overwrite the existing field.
                59 => (),
                // `datetime` is known to be off by one second.
                0 => datetime -= TimeDelta::seconds(1),
                // otherwise it is impossible.
                _ => return Err(Error::ParsingImpossible),
            }
        // ...and we have the correct candidates for other fields.
        } else {
            parsed.set_second(i64::from(datetime.second()))?;
        }
        parsed.set_year(i64::from(datetime.year()))?;
        parsed.set_ordinal(i64::from(datetime.ordinal()))?; // more efficient than ymd
        parsed.set_hour(i64::from(datetime.hour()))?;
        parsed.set_minute(i64::from(datetime.minute()))?;

        // validate other fields (e.g. week) and return
        let date = parsed.to_naive_date()?;
        let time = parsed.to_naive_time()?;
        Ok(date.and_time(time))
    }

    /// Returns a parsed fixed time zone offset out of given fields.
    pub fn to_fixed_offset(&self) -> Result<FixedOffset, Error> {
        let offset = self.offset.ok_or(Error::ParsingOutOfRange)?;
        FixedOffset::east(offset)
    }

    /// Returns a parsed timezone-aware date and time out of given fields.
    ///
    /// This method is able to determine the combined date and time
    /// from date and time fields or a single [`timestamp`](#structfield.timestamp) field,
    /// plus a time zone offset.
    /// Either way those fields have to be consistent to each other.
    pub fn to_datetime(&self) -> Result<DateTime<FixedOffset>, Error> {
        let offset = self.offset.ok_or(Error::ParsingNotEnough)?;
        let datetime = self.to_naive_datetime_with_offset(offset)?;
        let offset = FixedOffset::east(offset)?;

        // this is used to prevent an overflow when calling FixedOffset::from_local_datetime
        // TODO: is this still needed?
        datetime.checked_sub_signed(TimeDelta::seconds(i64::from(offset.local_minus_utc())))?;

        offset.from_local_datetime(&datetime)?.single()
    }

    /// Returns a parsed timezone-aware date and time out of given fields,
    /// with an additional `TimeZone` used to interpret and validate the local date.
    ///
    /// This method is able to determine the combined date and time
    /// from date and time fields or a single [`timestamp`](#structfield.timestamp) field,
    /// plus a time zone offset.
    /// Either way those fields have to be consistent to each other.
    /// If parsed fields include an UTC offset, it also has to be consistent to
    /// [`offset`](#structfield.offset).
    pub fn to_datetime_with_timezone<Tz: TimeZone>(&self, tz: &Tz) -> Result<DateTime<Tz>, Error> {
        // if we have `timestamp` specified, guess an offset from that.
        let mut guessed_offset = 0;
        if let Some(timestamp) = self.timestamp {
            // make a naive `DateTime` from given timestamp and (if any) nanosecond.
            // an empty `nanosecond` is always equal to zero, so missing nanosecond is fine.
            let nanosecond = self.nanosecond.unwrap_or(0);
            let dt = NaiveDateTime::from_timestamp(timestamp, nanosecond)?;
            guessed_offset = tz.offset_from_utc_datetime(&dt)?.fix().local_minus_utc();
        }

        // `guessed_offset` should be correct when `self.timestamp` is given.
        // it will be 0 otherwise, but this is fine as the algorithm ignores offset for that case.
        let datetime = self.to_naive_datetime_with_offset(guessed_offset)?;

        let dt = tz.from_local_datetime(&datetime)?.single()?;

        // checks if the given `DateTime` has a consistent `Offset` with given `self.offset`.
        match self.offset {
            Some(so) => match dt.offset().fix().local_minus_utc() == so {
                true => Ok(dt),
                false => Err(Error::ParsingImpossible),
            },
            None => Ok(dt),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Parsed;
    use crate::naive::{NaiveDate, NaiveTime};
    use crate::offset::{FixedOffset, TimeZone, Utc};
    use crate::Weekday::*;
    use crate::{Datelike, Error};

    macro_rules! ymd {
        ($year:expr, $month:expr, $day:expr) => {
            NaiveDate::from_ymd($year, $month, $day).unwrap()
        };
    }

    #[test]
    fn test_parsed_set_fields() {
        // year*, isoyear*
        let mut p = Parsed::new();
        assert_eq!(p.set_year(1987), Ok(()));
        assert_eq!(p.set_year(1986), Err(Error::ParsingImpossible));
        assert_eq!(p.set_year(1988), Err(Error::ParsingImpossible));
        assert_eq!(p.set_year(1987), Ok(()));
        assert_eq!(p.set_year_div_100(20), Ok(())); // independent to `year`
        assert_eq!(p.set_year_div_100(21), Err(Error::ParsingImpossible));
        assert_eq!(p.set_year_div_100(19), Err(Error::ParsingImpossible));
        assert_eq!(p.set_year_mod_100(37), Ok(())); // ditto
        assert_eq!(p.set_year_mod_100(38), Err(Error::ParsingImpossible));
        assert_eq!(p.set_year_mod_100(36), Err(Error::ParsingImpossible));

        let mut p = Parsed::new();
        assert_eq!(p.set_year(0), Ok(()));
        assert_eq!(p.set_year_div_100(0), Ok(()));
        assert_eq!(p.set_year_mod_100(0), Ok(()));

        let mut p = Parsed::new();
        assert_eq!(p.set_year_div_100(-1), Err(Error::ParsingOutOfRange));
        assert_eq!(p.set_year_mod_100(-1), Err(Error::ParsingOutOfRange));
        assert_eq!(p.set_year(-1), Ok(()));
        assert_eq!(p.set_year(-2), Err(Error::ParsingImpossible));
        assert_eq!(p.set_year(0), Err(Error::ParsingImpossible));

        let mut p = Parsed::new();
        assert_eq!(p.set_year_div_100(0x1_0000_0008), Err(Error::ParsingOutOfRange));
        assert_eq!(p.set_year_div_100(8), Ok(()));
        assert_eq!(p.set_year_div_100(0x1_0000_0008), Err(Error::ParsingOutOfRange));

        // month, week*, isoweek, ordinal, day, minute, second, nanosecond, offset
        let mut p = Parsed::new();
        assert_eq!(p.set_month(7), Ok(()));
        assert_eq!(p.set_month(1), Err(Error::ParsingImpossible));
        assert_eq!(p.set_month(6), Err(Error::ParsingImpossible));
        assert_eq!(p.set_month(8), Err(Error::ParsingImpossible));
        assert_eq!(p.set_month(12), Err(Error::ParsingImpossible));

        let mut p = Parsed::new();
        assert_eq!(p.set_month(8), Ok(()));
        assert_eq!(p.set_month(0x1_0000_0008), Err(Error::ParsingOutOfRange));

        // hour
        let mut p = Parsed::new();
        assert_eq!(p.set_hour(12), Ok(()));
        assert_eq!(p.set_hour(11), Err(Error::ParsingImpossible));
        assert_eq!(p.set_hour(13), Err(Error::ParsingImpossible));
        assert_eq!(p.set_hour(12), Ok(()));
        assert_eq!(p.set_ampm(false), Err(Error::ParsingImpossible));
        assert_eq!(p.set_ampm(true), Ok(()));
        assert_eq!(p.set_hour12(12), Ok(()));
        assert_eq!(p.set_hour12(0), Err(Error::ParsingOutOfRange)); // requires canonical representation
        assert_eq!(p.set_hour12(1), Err(Error::ParsingImpossible));
        assert_eq!(p.set_hour12(11), Err(Error::ParsingImpossible));

        let mut p = Parsed::new();
        assert_eq!(p.set_ampm(true), Ok(()));
        assert_eq!(p.set_hour12(7), Ok(()));
        assert_eq!(p.set_hour(7), Err(Error::ParsingImpossible));
        assert_eq!(p.set_hour(18), Err(Error::ParsingImpossible));
        assert_eq!(p.set_hour(19), Ok(()));

        // timestamp
        let mut p = Parsed::new();
        assert_eq!(p.set_timestamp(1_234_567_890), Ok(()));
        assert_eq!(p.set_timestamp(1_234_567_889), Err(Error::ParsingImpossible));
        assert_eq!(p.set_timestamp(1_234_567_891), Err(Error::ParsingImpossible));
    }

    #[test]
    fn test_parsed_to_naive_date() {
        macro_rules! parse {
            ($($k:ident: $v:expr),*) => (
                Parsed { $($k: Some($v),)* ..Parsed::new() }.to_naive_date()
            )
        }

        // ymd: omission of fields
        assert_eq!(parse!(), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(year: 1984), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(year: 1984, month: 1), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(year: 1984, month: 1, day: 2), Ok(ymd!(1984, 1, 2)));
        assert_eq!(parse!(year: 1984, day: 2), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(year_div_100: 19), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(year_div_100: 19, year_mod_100: 84), Err(Error::ParsingNotEnough));
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 84, month: 1),
            Err(Error::ParsingNotEnough)
        );
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 84, month: 1, day: 2),
            Ok(ymd!(1984, 1, 2))
        );
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 84, day: 2),
            Err(Error::ParsingNotEnough)
        );
        assert_eq!(parse!(year_div_100: 19, month: 1, day: 2), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(year_mod_100: 70, month: 1, day: 2), Ok(ymd!(1970, 1, 2)));
        assert_eq!(parse!(year_mod_100: 69, month: 1, day: 2), Ok(ymd!(2069, 1, 2)));

        // ymd: out-of-range conditions
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 84, month: 2, day: 29),
            Ok(ymd!(1984, 2, 29))
        );
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 83, month: 2, day: 29),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 83, month: 13, day: 1),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 83, month: 12, day: 31),
            Ok(ymd!(1983, 12, 31))
        );
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 83, month: 12, day: 32),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 83, month: 12, day: 0),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: 100, month: 1, day: 1),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year_div_100: 19, year_mod_100: -1, month: 1, day: 1),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(parse!(year_div_100: 0, year_mod_100: 0, month: 1, day: 1), Ok(ymd!(0, 1, 1)));
        assert_eq!(
            parse!(year_div_100: -1, year_mod_100: 42, month: 1, day: 1),
            Err(Error::ParsingOutOfRange)
        );
        let max_year = NaiveDate::MAX.year();
        assert_eq!(
            parse!(year_div_100: max_year / 100,
                          year_mod_100: max_year % 100, month: 1, day: 1),
            Ok(ymd!(max_year, 1, 1))
        );
        assert_eq!(
            parse!(year_div_100: (max_year + 1) / 100,
                          year_mod_100: (max_year + 1) % 100, month: 1, day: 1),
            Err(Error::ParsingOutOfRange)
        );

        // ymd: conflicting inputs
        assert_eq!(parse!(year: 1984, year_div_100: 19, month: 1, day: 1), Ok(ymd!(1984, 1, 1)));
        assert_eq!(
            parse!(year: 1984, year_div_100: 20, month: 1, day: 1),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(parse!(year: 1984, year_mod_100: 84, month: 1, day: 1), Ok(ymd!(1984, 1, 1)));
        assert_eq!(
            parse!(year: 1984, year_mod_100: 83, month: 1, day: 1),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(year: 1984, year_div_100: 19, year_mod_100: 84, month: 1, day: 1),
            Ok(ymd!(1984, 1, 1))
        );
        assert_eq!(
            parse!(year: 1984, year_div_100: 18, year_mod_100: 94, month: 1, day: 1),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(year: 1984, year_div_100: 18, year_mod_100: 184, month: 1, day: 1),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year: -1, year_div_100: 0, year_mod_100: -1, month: 1, day: 1),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year: -1, year_div_100: -1, year_mod_100: 99, month: 1, day: 1),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year: -1, year_div_100: 0, month: 1, day: 1),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year: -1, year_mod_100: 99, month: 1, day: 1),
            Err(Error::ParsingOutOfRange)
        );

        // weekdates
        assert_eq!(parse!(year: 2000, week_from_mon: 0), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(year: 2000, week_from_sun: 0), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(year: 2000, weekday: Sun), Err(Error::ParsingNotEnough));
        assert_eq!(
            parse!(year: 2000, week_from_mon: 0, weekday: Fri),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year: 2000, week_from_sun: 0, weekday: Fri),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(parse!(year: 2000, week_from_mon: 0, weekday: Sat), Ok(ymd!(2000, 1, 1)));
        assert_eq!(parse!(year: 2000, week_from_sun: 0, weekday: Sat), Ok(ymd!(2000, 1, 1)));
        assert_eq!(parse!(year: 2000, week_from_mon: 0, weekday: Sun), Ok(ymd!(2000, 1, 2)));
        assert_eq!(parse!(year: 2000, week_from_sun: 1, weekday: Sun), Ok(ymd!(2000, 1, 2)));
        assert_eq!(parse!(year: 2000, week_from_mon: 1, weekday: Mon), Ok(ymd!(2000, 1, 3)));
        assert_eq!(parse!(year: 2000, week_from_sun: 1, weekday: Mon), Ok(ymd!(2000, 1, 3)));
        assert_eq!(parse!(year: 2000, week_from_mon: 1, weekday: Sat), Ok(ymd!(2000, 1, 8)));
        assert_eq!(parse!(year: 2000, week_from_sun: 1, weekday: Sat), Ok(ymd!(2000, 1, 8)));
        assert_eq!(parse!(year: 2000, week_from_mon: 1, weekday: Sun), Ok(ymd!(2000, 1, 9)));
        assert_eq!(parse!(year: 2000, week_from_sun: 2, weekday: Sun), Ok(ymd!(2000, 1, 9)));
        assert_eq!(parse!(year: 2000, week_from_mon: 2, weekday: Mon), Ok(ymd!(2000, 1, 10)));
        assert_eq!(parse!(year: 2000, week_from_sun: 52, weekday: Sat), Ok(ymd!(2000, 12, 30)));
        assert_eq!(parse!(year: 2000, week_from_sun: 53, weekday: Sun), Ok(ymd!(2000, 12, 31)));
        assert_eq!(
            parse!(year: 2000, week_from_sun: 53, weekday: Mon),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year: 2000, week_from_sun: 0xffffffff, weekday: Mon),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(year: 2006, week_from_sun: 0, weekday: Sat),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(parse!(year: 2006, week_from_sun: 1, weekday: Sun), Ok(ymd!(2006, 1, 1)));

        // weekdates: conflicting inputs
        assert_eq!(
            parse!(year: 2000, week_from_mon: 1, week_from_sun: 1, weekday: Sat),
            Ok(ymd!(2000, 1, 8))
        );
        assert_eq!(
            parse!(year: 2000, week_from_mon: 1, week_from_sun: 2, weekday: Sun),
            Ok(ymd!(2000, 1, 9))
        );
        assert_eq!(
            parse!(year: 2000, week_from_mon: 1, week_from_sun: 1, weekday: Sun),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(year: 2000, week_from_mon: 2, week_from_sun: 2, weekday: Sun),
            Err(Error::ParsingImpossible)
        );

        // ISO weekdates
        assert_eq!(parse!(isoyear: 2004, isoweek: 53), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(isoyear: 2004, isoweek: 53, weekday: Fri), Ok(ymd!(2004, 12, 31)));
        assert_eq!(parse!(isoyear: 2004, isoweek: 53, weekday: Sat), Ok(ymd!(2005, 1, 1)));
        assert_eq!(
            parse!(isoyear: 2004, isoweek: 0xffffffff, weekday: Sat),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(parse!(isoyear: 2005, isoweek: 0, weekday: Thu), Err(Error::ParsingOutOfRange));
        assert_eq!(parse!(isoyear: 2005, isoweek: 5, weekday: Thu), Ok(ymd!(2005, 2, 3)));
        assert_eq!(parse!(isoyear: 2005, weekday: Thu), Err(Error::ParsingNotEnough));

        // year and ordinal
        assert_eq!(parse!(ordinal: 123), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(year: 2000, ordinal: 0), Err(Error::ParsingOutOfRange));
        assert_eq!(parse!(year: 2000, ordinal: 1), Ok(ymd!(2000, 1, 1)));
        assert_eq!(parse!(year: 2000, ordinal: 60), Ok(ymd!(2000, 2, 29)));
        assert_eq!(parse!(year: 2000, ordinal: 61), Ok(ymd!(2000, 3, 1)));
        assert_eq!(parse!(year: 2000, ordinal: 366), Ok(ymd!(2000, 12, 31)));
        assert_eq!(parse!(year: 2000, ordinal: 367), Err(Error::ParsingOutOfRange));
        assert_eq!(parse!(year: 2000, ordinal: 0xffffffff), Err(Error::ParsingOutOfRange));
        assert_eq!(parse!(year: 2100, ordinal: 0), Err(Error::ParsingOutOfRange));
        assert_eq!(parse!(year: 2100, ordinal: 1), Ok(ymd!(2100, 1, 1)));
        assert_eq!(parse!(year: 2100, ordinal: 59), Ok(ymd!(2100, 2, 28)));
        assert_eq!(parse!(year: 2100, ordinal: 60), Ok(ymd!(2100, 3, 1)));
        assert_eq!(parse!(year: 2100, ordinal: 365), Ok(ymd!(2100, 12, 31)));
        assert_eq!(parse!(year: 2100, ordinal: 366), Err(Error::ParsingOutOfRange));
        assert_eq!(parse!(year: 2100, ordinal: 0xffffffff), Err(Error::ParsingOutOfRange));

        // more complex cases
        assert_eq!(
            parse!(year: 2014, month: 12, day: 31, ordinal: 365, isoyear: 2015, isoweek: 1,
                          week_from_sun: 52, week_from_mon: 52, weekday: Wed),
            Ok(ymd!(2014, 12, 31))
        );
        assert_eq!(
            parse!(year: 2014, month: 12, ordinal: 365, isoyear: 2015, isoweek: 1,
                          week_from_sun: 52, week_from_mon: 52),
            Ok(ymd!(2014, 12, 31))
        );
        assert_eq!(
            parse!(year: 2014, month: 12, day: 31, ordinal: 365, isoyear: 2014, isoweek: 53,
                          week_from_sun: 52, week_from_mon: 52, weekday: Wed),
            Err(Error::ParsingImpossible)
        ); // no ISO week date 2014-W53-3
        assert_eq!(
            parse!(year: 2012, isoyear: 2015, isoweek: 1,
                          week_from_sun: 52, week_from_mon: 52),
            Err(Error::ParsingNotEnough)
        ); // ambiguous (2014-12-29, 2014-12-30, 2014-12-31)
        assert_eq!(
            parse!(year_div_100: 20, isoyear_mod_100: 15, ordinal: 366),
            Err(Error::ParsingNotEnough)
        );
        // technically unique (2014-12-31) but Chrono gives up
    }

    #[test]
    fn test_parsed_to_naive_time() {
        macro_rules! parse {
            ($($k:ident: $v:expr),*) => (
                Parsed { $($k: Some($v),)* ..Parsed::new() }.to_naive_time()
            )
        }

        let hms = |h, m, s| NaiveTime::from_hms(h, m, s).unwrap();
        let hmsn = |h, m, s, n| NaiveTime::from_hms_nano(h, m, s, n).unwrap();

        // omission of fields
        assert_eq!(parse!(), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(hour_div_12: 0), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23), Ok(hms(1, 23, 0)));
        assert_eq!(
            parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 45),
            Ok(hms(1, 23, 45))
        );
        assert_eq!(
            parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 45,
                          nanosecond: 678_901_234),
            Ok(hmsn(1, 23, 45, 678_901_234))
        );
        assert_eq!(
            parse!(hour_div_12: 1, hour_mod_12: 11, minute: 45, second: 6),
            Ok(hms(23, 45, 6))
        );
        assert_eq!(parse!(hour_mod_12: 1, minute: 23), Err(Error::ParsingNotEnough));
        assert_eq!(
            parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, nanosecond: 456_789_012),
            Err(Error::ParsingNotEnough)
        );

        // out-of-range conditions
        assert_eq!(
            parse!(hour_div_12: 2, hour_mod_12: 0, minute: 0),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(hour_div_12: 1, hour_mod_12: 12, minute: 0),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(hour_div_12: 0, hour_mod_12: 1, minute: 60),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 61),
            Err(Error::ParsingOutOfRange)
        );
        assert_eq!(
            parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 34,
                          nanosecond: 1_000_000_000),
            Err(Error::ParsingOutOfRange)
        );

        // leap seconds
        assert_eq!(
            parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 60),
            Ok(hmsn(1, 23, 59, 1_000_000_000))
        );
        assert_eq!(
            parse!(hour_div_12: 0, hour_mod_12: 1, minute: 23, second: 60,
                          nanosecond: 999_999_999),
            Ok(hmsn(1, 23, 59, 1_999_999_999))
        );
    }

    #[test]
    fn test_parsed_to_naive_datetime_with_offset() {
        macro_rules! parse {
            (offset = $offset:expr; $($k:ident: $v:expr),*) => (
                Parsed { $($k: Some($v),)* ..Parsed::new() }.to_naive_datetime_with_offset($offset)
            );
            ($($k:ident: $v:expr),*) => (parse!(offset = 0; $($k: $v),*))
        }

        let ymdhms =
            |y, m, d, h, n, s| NaiveDate::from_ymd(y, m, d).unwrap().and_hms(h, n, s).unwrap();
        let ymdhmsn = |y, m, d, h, n, s, nano| {
            NaiveDate::from_ymd(y, m, d).unwrap().and_hms_nano(h, n, s, nano).unwrap()
        };

        // omission of fields
        assert_eq!(parse!(), Err(Error::ParsingNotEnough));
        assert_eq!(
            parse!(year: 2015, month: 1, day: 30,
                          hour_div_12: 1, hour_mod_12: 2, minute: 38),
            Ok(ymdhms(2015, 1, 30, 14, 38, 0))
        );
        assert_eq!(
            parse!(year: 1997, month: 1, day: 30,
                          hour_div_12: 1, hour_mod_12: 2, minute: 38, second: 5),
            Ok(ymdhms(1997, 1, 30, 14, 38, 5))
        );
        assert_eq!(
            parse!(year: 2012, ordinal: 34, hour_div_12: 0, hour_mod_12: 5,
                          minute: 6, second: 7, nanosecond: 890_123_456),
            Ok(ymdhmsn(2012, 2, 3, 5, 6, 7, 890_123_456))
        );
        assert_eq!(parse!(timestamp: 0), Ok(ymdhms(1970, 1, 1, 0, 0, 0)));
        assert_eq!(parse!(timestamp: 1, nanosecond: 0), Ok(ymdhms(1970, 1, 1, 0, 0, 1)));
        assert_eq!(parse!(timestamp: 1, nanosecond: 1), Ok(ymdhmsn(1970, 1, 1, 0, 0, 1, 1)));
        assert_eq!(parse!(timestamp: 1_420_000_000), Ok(ymdhms(2014, 12, 31, 4, 26, 40)));
        assert_eq!(parse!(timestamp: -0x1_0000_0000), Ok(ymdhms(1833, 11, 24, 17, 31, 44)));

        // full fields
        assert_eq!(
            parse!(year: 2014, year_div_100: 20, year_mod_100: 14, month: 12, day: 31,
                          ordinal: 365, isoyear: 2015, isoyear_div_100: 20, isoyear_mod_100: 15,
                          isoweek: 1, week_from_sun: 52, week_from_mon: 52, weekday: Wed,
                          hour_div_12: 0, hour_mod_12: 4, minute: 26, second: 40,
                          nanosecond: 12_345_678, timestamp: 1_420_000_000),
            Ok(ymdhmsn(2014, 12, 31, 4, 26, 40, 12_345_678))
        );
        assert_eq!(
            parse!(year: 2014, year_div_100: 20, year_mod_100: 14, month: 12, day: 31,
                          ordinal: 365, isoyear: 2015, isoyear_div_100: 20, isoyear_mod_100: 15,
                          isoweek: 1, week_from_sun: 52, week_from_mon: 52, weekday: Wed,
                          hour_div_12: 0, hour_mod_12: 4, minute: 26, second: 40,
                          nanosecond: 12_345_678, timestamp: 1_419_999_999),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(offset = 32400;
                          year: 2014, year_div_100: 20, year_mod_100: 14, month: 12, day: 31,
                          ordinal: 365, isoyear: 2015, isoyear_div_100: 20, isoyear_mod_100: 15,
                          isoweek: 1, week_from_sun: 52, week_from_mon: 52, weekday: Wed,
                          hour_div_12: 0, hour_mod_12: 4, minute: 26, second: 40,
                          nanosecond: 12_345_678, timestamp: 1_419_967_600),
            Ok(ymdhmsn(2014, 12, 31, 4, 26, 40, 12_345_678))
        );

        // more timestamps
        let max_days_from_year_1970 = NaiveDate::MAX.signed_duration_since(ymd!(1970, 1, 1));
        let year_0_from_year_1970 = ymd!(0, 1, 1).signed_duration_since(ymd!(1970, 1, 1));
        let min_days_from_year_1970 = NaiveDate::MIN.signed_duration_since(ymd!(1970, 1, 1));
        assert_eq!(
            parse!(timestamp: min_days_from_year_1970.num_seconds()),
            Ok(ymdhms(NaiveDate::MIN.year(), 1, 1, 0, 0, 0))
        );
        assert_eq!(
            parse!(timestamp: year_0_from_year_1970.num_seconds()),
            Ok(ymdhms(0, 1, 1, 0, 0, 0))
        );
        assert_eq!(
            parse!(timestamp: max_days_from_year_1970.num_seconds() + 86399),
            Ok(ymdhms(NaiveDate::MAX.year(), 12, 31, 23, 59, 59))
        );

        // leap seconds #1: partial fields
        assert_eq!(parse!(second: 59, timestamp: 1_341_100_798), Err(Error::ParsingNotEnough));
        assert_eq!(
            parse!(second: 59, timestamp: 1_341_100_799),
            Ok(ymdhms(2012, 6, 30, 23, 59, 59))
        );
        assert_eq!(parse!(second: 59, timestamp: 1_341_100_800), Err(Error::ParsingNotEnough));
        assert_eq!(
            parse!(second: 60, timestamp: 1_341_100_799),
            Ok(ymdhmsn(2012, 6, 30, 23, 59, 59, 1_000_000_000))
        );
        assert_eq!(
            parse!(second: 60, timestamp: 1_341_100_800),
            Ok(ymdhmsn(2012, 6, 30, 23, 59, 59, 1_000_000_000))
        );
        assert_eq!(parse!(second: 0, timestamp: 1_341_100_800), Ok(ymdhms(2012, 7, 1, 0, 0, 0)));
        assert_eq!(parse!(second: 1, timestamp: 1_341_100_800), Err(Error::ParsingNotEnough));
        assert_eq!(parse!(second: 60, timestamp: 1_341_100_801), Err(Error::ParsingNotEnough));

        // leap seconds #2: full fields
        // we need to have separate tests for them since it uses another control flow.
        assert_eq!(
            parse!(year: 2012, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 59, timestamp: 1_341_100_798),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(year: 2012, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 59, timestamp: 1_341_100_799),
            Ok(ymdhms(2012, 6, 30, 23, 59, 59))
        );
        assert_eq!(
            parse!(year: 2012, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 59, timestamp: 1_341_100_800),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(year: 2012, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 60, timestamp: 1_341_100_799),
            Ok(ymdhmsn(2012, 6, 30, 23, 59, 59, 1_000_000_000))
        );
        assert_eq!(
            parse!(year: 2012, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 60, timestamp: 1_341_100_800),
            Ok(ymdhmsn(2012, 6, 30, 23, 59, 59, 1_000_000_000))
        );
        assert_eq!(
            parse!(year: 2012, ordinal: 183, hour_div_12: 0, hour_mod_12: 0,
                          minute: 0, second: 0, timestamp: 1_341_100_800),
            Ok(ymdhms(2012, 7, 1, 0, 0, 0))
        );
        assert_eq!(
            parse!(year: 2012, ordinal: 183, hour_div_12: 0, hour_mod_12: 0,
                          minute: 0, second: 1, timestamp: 1_341_100_800),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(year: 2012, ordinal: 182, hour_div_12: 1, hour_mod_12: 11,
                          minute: 59, second: 60, timestamp: 1_341_100_801),
            Err(Error::ParsingImpossible)
        );

        // error codes
        assert_eq!(
            parse!(year: 2015, month: 1, day: 20, weekday: Tue,
                          hour_div_12: 2, hour_mod_12: 1, minute: 35, second: 20),
            Err(Error::ParsingOutOfRange)
        ); // `hour_div_12` is out of range
    }

    #[test]
    fn test_parsed_to_datetime() -> Result<(), crate::Error> {
        macro_rules! parse {
            ($($k:ident: $v:expr),*) => (
                Parsed { $($k: Some($v),)* ..Parsed::new() }.to_datetime()
            )
        }

        let ymdhmsn = |y, m, d, h, n, s, nano, off| {
            FixedOffset::east(off)?
                .from_local_datetime(&NaiveDate::from_ymd(y, m, d)?.and_hms_nano(h, n, s, nano)?)?
                .single()
        };

        assert_eq!(parse!(offset: 0), Err(Error::ParsingNotEnough));
        assert_eq!(
            parse!(year: 2014, ordinal: 365, hour_div_12: 0, hour_mod_12: 4,
                          minute: 26, second: 40, nanosecond: 12_345_678),
            Err(Error::ParsingNotEnough)
        );
        assert_eq!(
            parse!(year: 2014, ordinal: 365, hour_div_12: 0, hour_mod_12: 4,
                          minute: 26, second: 40, nanosecond: 12_345_678, offset: 0),
            ymdhmsn(2014, 12, 31, 4, 26, 40, 12_345_678, 0)
        );
        assert_eq!(
            parse!(year: 2014, ordinal: 365, hour_div_12: 1, hour_mod_12: 1,
                          minute: 26, second: 40, nanosecond: 12_345_678, offset: 32400),
            ymdhmsn(2014, 12, 31, 13, 26, 40, 12_345_678, 32400)
        );
        assert_eq!(
            parse!(year: 2014, ordinal: 365, hour_div_12: 0, hour_mod_12: 1,
                          minute: 42, second: 4, nanosecond: 12_345_678, offset: -9876),
            ymdhmsn(2014, 12, 31, 1, 42, 4, 12_345_678, -9876)
        );
        assert_eq!(
            parse!(year: 2015, ordinal: 1, hour_div_12: 0, hour_mod_12: 4,
                          minute: 26, second: 40, nanosecond: 12_345_678, offset: 86_400),
            Err(Error::InvalidTimeZone)
        ); // `FixedOffset` does not support such huge offset
        Ok(())
    }

    #[test]
    fn test_parsed_to_datetime_with_timezone() -> Result<(), crate::Error> {
        macro_rules! parse {
            ($tz:expr; $($k:ident: $v:expr),*) => (
                Parsed { $($k: Some($v),)* ..Parsed::new() }.to_datetime_with_timezone(&$tz)
            )
        }

        // single result from ymdhms
        assert_eq!(
            parse!(Utc;
                          year: 2014, ordinal: 365, hour_div_12: 0, hour_mod_12: 4,
                          minute: 26, second: 40, nanosecond: 12_345_678, offset: 0),
            Utc.from_local_datetime(
                &NaiveDate::from_ymd(2014, 12, 31)?.and_hms_nano(4, 26, 40, 12_345_678)?
            )?
            .single()
        );
        assert_eq!(
            parse!(Utc;
                          year: 2014, ordinal: 365, hour_div_12: 1, hour_mod_12: 1,
                          minute: 26, second: 40, nanosecond: 12_345_678, offset: 32400),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(FixedOffset::east(32400).unwrap();
                          year: 2014, ordinal: 365, hour_div_12: 0, hour_mod_12: 4,
                          minute: 26, second: 40, nanosecond: 12_345_678, offset: 0),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(FixedOffset::east(32400).unwrap();
                          year: 2014, ordinal: 365, hour_div_12: 1, hour_mod_12: 1,
                          minute: 26, second: 40, nanosecond: 12_345_678, offset: 32400),
            FixedOffset::east(32400)?
                .from_local_datetime(
                    &NaiveDate::from_ymd(2014, 12, 31)?.and_hms_nano(13, 26, 40, 12_345_678)?
                )?
                .single()
        );

        // single result from timestamp
        assert_eq!(
            parse!(Utc; timestamp: 1_420_000_000, offset: 0),
            Utc.with_ymd_and_hms(2014, 12, 31, 4, 26, 40)?.single()
        );
        assert_eq!(
            parse!(Utc; timestamp: 1_420_000_000, offset: 32400),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(FixedOffset::east(32400).unwrap(); timestamp: 1_420_000_000, offset: 0),
            Err(Error::ParsingImpossible)
        );
        assert_eq!(
            parse!(FixedOffset::east(32400).unwrap(); timestamp: 1_420_000_000, offset: 32400),
            FixedOffset::east(32400)?.with_ymd_and_hms(2014, 12, 31, 13, 26, 40)?.single()
        );

        // TODO test with a variable time zone (for None and Ambiguous cases)
        Ok(())
    }
}
