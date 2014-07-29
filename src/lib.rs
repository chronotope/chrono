// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
Experimental date and time handling for Rust.
*/

#![comment = "Date and time library for Rust"]
#![license = "MIT"]

#![feature(macro_rules)]
#![deny(missing_doc)]

extern crate num;

pub use duration::Duration;
pub use offset::{Offset, LocalResult};
pub use offset::{UTC, FixedOffset};
pub use naive::date::NaiveDate;
pub use naive::time::NaiveTime;
pub use naive::datetime::NaiveDateTime;
pub use date::Date;
pub use time::Time;
pub use datetime::DateTime;

pub mod duration;
pub mod offset;
pub mod naive {
    //! Date and time types which do not concern about the timezones.
    //!
    //! They are primarily building blocks for other types (e.g. `Offset`),
    //! but can be also used for the simpler date and time handling.
    pub mod date;
    pub mod time;
    pub mod datetime;
}
pub mod date;
pub mod time;
pub mod datetime;

/// The day of week (DOW).
///
/// The order of the days of week depends on the context.
/// One should prefer `*_from_monday` or `*_from_sunday` methods to get the correct result.
#[deriving(PartialEq, Eq, Clone, FromPrimitive, Show)]
pub enum Weekday {
    /// Monday.
    Mon = 0,
    /// Tuesday.
    Tue = 1,
    /// Wednesday.
    Wed = 2,
    /// Thursday.
    Thu = 3,
    /// Friday.
    Fri = 4,
    /// Saturday.
    Sat = 5,
    /// Sunday.
    Sun = 6,
}

impl Weekday {
    /// The next day in the week.
    #[inline]
    pub fn succ(&self) -> Weekday {
        match *self {
            Mon => Tue,
            Tue => Wed,
            Wed => Thu,
            Thu => Fri,
            Fri => Sat,
            Sat => Sun,
            Sun => Mon,
        }
    }

    /// The previous day in the week.
    #[inline]
    pub fn pred(&self) -> Weekday {
        match *self {
            Mon => Sun,
            Tue => Mon,
            Wed => Tue,
            Thu => Wed,
            Fri => Thu,
            Sat => Fri,
            Sun => Sat,
        }
    }

    /// Returns a DOW number starting from Monday = 1. (ISO 8601 weekday number)
    #[inline]
    pub fn number_from_monday(&self) -> u32 {
        match *self {
            Mon => 1,
            Tue => 2,
            Wed => 3,
            Thu => 4,
            Fri => 5,
            Sat => 6,
            Sun => 7,
        }
    }

    /// Returns a DOW number starting from Sunday = 1.
    #[inline]
    pub fn number_from_sunday(&self) -> u32 {
        match *self {
            Mon => 2,
            Tue => 3,
            Wed => 4,
            Thu => 5,
            Fri => 6,
            Sat => 7,
            Sun => 1,
        }
    }

    /// Returns a DOW number starting from Monday = 0.
    #[inline]
    pub fn num_days_from_monday(&self) -> u32 {
        match *self {
            Mon => 0,
            Tue => 1,
            Wed => 2,
            Thu => 3,
            Fri => 4,
            Sat => 5,
            Sun => 6,
        }
    }

    /// Returns a DOW number starting from Sunday = 0.
    #[inline]
    pub fn num_days_from_sunday(&self) -> u32 {
        match *self {
            Mon => 1,
            Tue => 2,
            Wed => 3,
            Thu => 4,
            Fri => 5,
            Sat => 6,
            Sun => 0,
        }
    }
}

/// The common set of methods for date component.
pub trait Datelike {
    /// Returns the year number.
    fn year(&self) -> i32;

    /// Returns the absolute year number starting from 1 with a boolean flag,
    /// which is false when the year predates the epoch (BCE/BC) and true otherwise (CE/AD).
    #[inline]
    fn year_ce(&self) -> (bool, u32) {
        let year = self.year();
        if year < 1 {
            (false, (1 - year) as u32)
        } else {
            (true, year as u32)
        }
    }

    /// Returns the month number starting from 1.
    fn month(&self) -> u32;

    /// Returns the month number starting from 0.
    fn month0(&self) -> u32;

    /// Returns the day of month starting from 1.
    fn day(&self) -> u32;

    /// Returns the day of month starting from 0.
    fn day0(&self) -> u32;

    /// Returns the day of year starting from 1.
    fn ordinal(&self) -> u32;

    /// Returns the day of year starting from 0.
    fn ordinal0(&self) -> u32;

    /// Returns the day of week.
    fn weekday(&self) -> Weekday;

    /// Returns the ISO week date: an adjusted year, week number and day of week.
    /// The adjusted year may differ from that of the calendar date.
    fn isoweekdate(&self) -> (i32, u32, Weekday);

    /// Makes a new value with the year number changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_year(&self, year: i32) -> Option<Self>;

    /// Makes a new value with the month number (starting from 1) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_month(&self, month: u32) -> Option<Self>;

    /// Makes a new value with the month number (starting from 0) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_month0(&self, month0: u32) -> Option<Self>;

    /// Makes a new value with the day of month (starting from 1) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_day(&self, day: u32) -> Option<Self>;

    /// Makes a new value with the day of month (starting from 0) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_day0(&self, day0: u32) -> Option<Self>;

    /// Makes a new value with the day of year (starting from 1) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_ordinal(&self, ordinal: u32) -> Option<Self>;

    /// Makes a new value with the day of year (starting from 0) changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_ordinal0(&self, ordinal0: u32) -> Option<Self>;

    /// Returns the number of days since January 1, 1 (Day 1) in the proleptic Gregorian calendar.
    fn num_days_from_ce(&self) -> i32 {
        // we know this wouldn't overflow since year is limited to 1/2^13 of i32's full range.
        let mut year = self.year() - 1;
        let mut ndays = 0;
        if year < 0 {
            let excess = 1 + (-year) / 400;
            year += excess * 400;
            ndays -= excess * 146097;
        }
        let div_100 = year / 100;
        ndays += ((year * 1461) >> 2) - div_100 + (div_100 >> 2);
        ndays + self.ordinal() as i32
    }
}

/// The common set of methods for time component.
pub trait Timelike {
    /// Returns the hour number from 0 to 23.
    fn hour(&self) -> u32;

    /// Returns the hour number from 1 to 12 with a boolean flag,
    /// which is false for AM and true for PM.
    #[inline]
    fn hour12(&self) -> (bool, u32) {
        let hour = self.hour();
        let mut hour12 = hour % 12;
        if hour12 == 0 { hour12 = 12; }
        (hour >= 12, hour12)
    }

    /// Returns the minute number from 0 to 59.
    fn minute(&self) -> u32;

    /// Returns the second number from 0 to 59.
    fn second(&self) -> u32;

    /// Returns the number of nanoseconds since the whole non-leap second.
    /// The range from 1,000,000,000 to 1,999,999,999 represents the leap second.
    fn nanosecond(&self) -> u32;

    /// Makes a new value with the hour number changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_hour(&self, hour: u32) -> Option<Self>;

    /// Makes a new value with the minute number changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_minute(&self, min: u32) -> Option<Self>;

    /// Makes a new value with the second number changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_second(&self, sec: u32) -> Option<Self>;

    /// Makes a new value with nanoseconds since the whole non-leap second changed.
    ///
    /// Returns `None` when the resulting value would be invalid.
    fn with_nanosecond(&self, nano: u32) -> Option<Self>;

    /// Returns the number of non-leap seconds past the last midnight.
    #[inline]
    fn num_seconds_from_midnight(&self) -> u32 {
        self.hour() * 3600 + self.minute() * 60 + self.second()
    }
}

#[test]
fn test_readme_doomsday() {
    use std::iter::range_inclusive;

    for y in range_inclusive(naive::date::MIN.year(), naive::date::MAX.year()) {
        // even months
        let d4   = NaiveDate::from_ymd(y,  4,  4);
        let d6   = NaiveDate::from_ymd(y,  6,  6);
        let d8   = NaiveDate::from_ymd(y,  8,  8);
        let d10  = NaiveDate::from_ymd(y, 10, 10);
        let d12  = NaiveDate::from_ymd(y, 12, 12);

        // nine to five, seven-eleven
        let d59  = NaiveDate::from_ymd(y,  5,  9);
        let d95  = NaiveDate::from_ymd(y,  9,  5);
        let d711 = NaiveDate::from_ymd(y,  7, 11);
        let d117 = NaiveDate::from_ymd(y, 11,  7);

        // "March 0"
        let d30  = NaiveDate::from_ymd(y,  3,  1).pred();

        let weekday = d30.weekday();
        let other_dates = [d4, d6, d8, d10, d12, d59, d95, d711, d117];
        assert!(other_dates.iter().all(|d| d.weekday() == weekday));
    }
}

