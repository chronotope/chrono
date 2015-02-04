// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!

# Chrono 0.2.0-dev

Date and time handling for Rust. (also known as `rust-chrono`)
It aims to be a feature-complete superset of the [time](https://github.com/rust-lang/time) library.
In particular,

* Chrono strictly adheres to ISO 8601.
* Chrono is timezone-aware by default, with separate timezone-naive types.
* Chrono is space-optimal and (while not being the primary goal) reasonably efficient.

There were several previous attempts to bring a good date and time library to Rust,
which Chrono builts upon and should acknowledge:

* [Initial research on the wiki](https://github.com/rust-lang/rust/wiki/Lib-datetime)
* Dietrich Epp's [datetime-rs](https://github.com/depp/datetime-rs)
* Luis de Bethencourt's [rust-datetime](https://github.com/luisbg/rust-datetime)

## Overview

### Duration

Chrono used to have a `Duration` type, which represents the time span.
Now Rust standard library includes it as `std::time::duration::Duration` and
Chrono simply reexports it.

### Date and Time

Chrono provides a `DateTime` type for the combined date and time.

`DateTime`, among others, is timezone-aware and
must be constructed from the timezone object (`Offset`).
`DateTime`s with different offsets do not mix, but can be converted to each other.

You can get the current date and time in the UTC timezone (`UTC::now()`)
or in the local timezone (`Local::now()`).

~~~~ {.rust}
use chrono::{UTC, Local, DateTime};

let utc: DateTime<UTC> = UTC::now();       // e.g. `2014-11-28T12:45:59.324310806Z`
let local: DateTime<Local> = Local::now(); // e.g. `2014-11-28T21:45:59.324310806+09:00`
# let _ = utc; let _ = local;
~~~~

Alternatively, you can create your own date and time.
This is a bit verbose due to Rust's lack of function and method overloading,
but in turn we get a rich combination of initialization methods.

~~~~ {.rust}
use chrono::{UTC, Offset, Weekday, LocalResult};

let dt = UTC.ymd(2014, 7, 8).and_hms(9, 10, 11); // `2014-07-08T09:10:11Z`
// July 8 is 188th day of the year 2014 (`o` for "ordinal")
assert_eq!(dt, UTC.yo(2014, 189).and_hms(9, 10, 11));
// July 8 is Tuesday in ISO week 28 of the year 2014.
assert_eq!(dt, UTC.isoywd(2014, 28, Weekday::Tue).and_hms(9, 10, 11));

let dt = UTC.ymd(2014, 7, 8).and_hms_milli(9, 10, 11, 12); // `2014-07-08T09:10:11.012Z`
assert_eq!(dt, UTC.ymd(2014, 7, 8).and_hms_micro(9, 10, 11, 12_000));
assert_eq!(dt, UTC.ymd(2014, 7, 8).and_hms_nano(9, 10, 11, 12_000_000));

// dynamic verification
assert_eq!(UTC.ymd_opt(2014, 7, 8).and_hms_opt(21, 15, 33),
           LocalResult::Single(UTC.ymd(2014, 7, 8).and_hms(21, 15, 33)));
assert_eq!(UTC.ymd_opt(2014, 7, 8).and_hms_opt(80, 15, 33), LocalResult::None);
assert_eq!(UTC.ymd_opt(2014, 7, 38).and_hms_opt(21, 15, 33), LocalResult::None);
~~~~

Various properties are available to the date and time, and can be altered individually.
Most of them are defined in the traits `Datelike` and `Timelike` which you should `use` before.
Addition and subtraction is also supported.
The following illustrates most supported operations to the date and time:

~~~~ {.rust}
# /* we intentionally fake the datetime...
use chrono::{UTC, Local, Datelike, Timelike, Weekday, Duration};

// assume this returned `2014-11-28T21:45:59.324310806+09:00`:
let dt = Local::now();
# */ // up to here. we now define a fixed datetime for the illustrative purpose.
# use chrono::{UTC, FixedOffset, Offset, Datelike, Timelike, Weekday, Duration};
# let dt = FixedOffset::east(9*3600).ymd(2014, 11, 28).and_hms_nano(21, 45, 59, 324310806);

// property accessors
assert_eq!((dt.year(), dt.month(), dt.day()), (2014, 11, 28));
assert_eq!((dt.month0(), dt.day0()), (10, 27)); // for unfortunate souls
assert_eq!((dt.hour(), dt.minute(), dt.second()), (21, 45, 59));
assert_eq!(dt.weekday(), Weekday::Fri);
assert_eq!(dt.weekday().number_from_monday(), 5); // Mon=1, ..., Sat=7
assert_eq!(dt.ordinal(), 332); // the day of year
assert_eq!(dt.num_days_from_ce(), 735565); // the number of days from and including Jan 1, 1

// offset accessor and manipulation
assert_eq!(dt.offset().local_minus_utc(), Duration::hours(9));
assert_eq!(dt.with_offset(UTC), UTC.ymd(2014, 11, 28).and_hms_nano(12, 45, 59, 324310806));

// a sample of property manipulations (validates dynamically)
assert_eq!(dt.with_day(29).unwrap().weekday(), Weekday::Sat); // 2014-11-29 is Saturday
assert_eq!(dt.with_day(32), None);
assert_eq!(dt.with_year(-300).unwrap().num_days_from_ce(), -109606); // November 29, 301 BCE

// arithmetic operations
assert_eq!(UTC.ymd(2014, 11, 14).and_hms(8, 9, 10) - UTC.ymd(2014, 11, 14).and_hms(10, 9, 8),
           Duration::seconds(-2 * 3600 + 2));
assert_eq!(UTC.ymd(1970, 1, 1).and_hms(0, 0, 0) + Duration::seconds(1_000_000_000),
           UTC.ymd(2001, 9, 9).and_hms(1, 46, 40));
assert_eq!(UTC.ymd(1970, 1, 1).and_hms(0, 0, 0) - Duration::seconds(1_000_000_000),
           UTC.ymd(1938, 4, 24).and_hms(22, 13, 20));
~~~~

Formatting is done via the `format` method,
which format is equivalent to the familiar `strftime` format.
(See the `format::strftime` module documentation for full syntax.)
The default `to_string` method and `{:?}` specifier also give a reasonable representation.

~~~~ {.rust}
use chrono::{UTC, Offset};

let dt = UTC.ymd(2014, 11, 28).and_hms(12, 0, 9);
assert_eq!(dt.format("%Y-%m-%d %H:%M:%S").to_string(), "2014-11-28 12:00:09");
assert_eq!(dt.format("%a %b %e %T %Y").to_string(), "Fri Nov 28 12:00:09 2014");
assert_eq!(dt.format("%a %b %e %T %Y").to_string(), dt.format("%c").to_string());

assert_eq!(dt.to_string(), "2014-11-28 12:00:09 UTC");
assert_eq!(format!("{:?}", dt), "2014-11-28T12:00:09Z");
~~~~

Parsing can be done with two methods:

- `DateTime::from_str` parses a date and time with offsets and returns `DateTime<FixedOffset>`.
  This should be used when the offset is a part of input and the caller cannot guess that.
  It *cannot* be used when the offset can be missing.

- `Offset::datetime_from_str` is similar but returns `DateTime` of given offset.
  When the explicit offset is missing from the input, it simply uses given offset.
  It issues an error when the input contains an explicit offset different from the current offset.

More detailed control over the parsing process is available via `format` module.

~~~~ {.rust}
use chrono::{UTC, Offset, DateTime};

let dt = UTC.ymd(2014, 11, 28).and_hms(12, 0, 9);
assert_eq!(UTC.datetime_from_str("2014-11-28 12:00:09", "%Y-%m-%d %H:%M:%S"), Ok(dt.clone()));
assert_eq!(UTC.datetime_from_str("Fri Nov 28 12:00:09 2014", "%a %b %e %T %Y"), Ok(dt.clone()));
assert_eq!(DateTime::from_str("2014-11-28 21:00:09 +09:00",
                              "%Y-%m-%d %H:%M:%S %z").map(|dt| dt.with_offset(UTC)), Ok(dt));

// oops, the year is missing!
assert!(UTC.datetime_from_str("Fri Nov 28 12:00:09", "%a %b %e %T %Y").is_err());
// oops, the format string does not include the year at all!
assert!(UTC.datetime_from_str("Fri Nov 28 12:00:09", "%a %b %e %T").is_err());
// oops, the weekday is incorrect!
assert!(UTC.datetime_from_str("Sat Nov 28 12:00:09 2014", "%a %b %e %T %Y").is_err());
~~~~

### Individual date and time

Chrono also provides an individual date type (`Date`) and time type (`Time`).
They also have offsets attached, and have to be constructed via offsets.
Most operations available to `DateTime` are also available to `Date` and `Time`
whenever appropriate.

~~~~ {.rust}
use chrono::{UTC, Local, Offset, LocalResult, Datelike, Weekday};

# // these *may* fail, but only very rarely. just rerun the test if you were that unfortunate ;)
assert_eq!(UTC::today(), UTC::now().date());
assert_eq!(Local::today(), Local::now().date());

assert_eq!(UTC.ymd(2014, 11, 28).weekday(), Weekday::Fri);
assert_eq!(UTC.ymd_opt(2014, 11, 31), LocalResult::None);
assert_eq!(UTC.hms_milli(7, 8, 9, 10).format("%H%M%S").to_string(), "070809");
~~~~

`DateTime` has two methods, `date` and `time`,
which return narrow views to its date and time components respectively.

### Naive date and time

Chrono provides naive counterparts to `Date`, `Time` and `DateTime`
as `NaiveDate`, `NaiveTime` and `NaiveDateTime` respectively.

They have almost equivalent interfaces as their timezone-aware twins,
but are not associated to offsets obviously and can be quite low-level.
They are mostly useful for building blocks for higher-level types.

## Limitations

Only proleptic Gregorian calendar (i.e. extended to support older dates) is supported.
Be very careful if you really have to deal with pre-20C dates, they can be in Julian or others.

Date types are limited in about +/- 262,000 years from the common epoch.
Time types are limited in the nanosecond accuracy.

Leap seconds are supported in the representation but Chrono doesn't try to make use of them.
(The main reason is that leap seconds are not really predictable.)
Almost *every* operation over the possible leap seconds will ignore them.
Consider using `NaiveDateTime` with the implicit TAI (International Atomic Time) scale if you want.

Chrono inherently does not support an inaccurate or partial date and time representation.
Any operation that can be ambiguous will return `None` in such cases.
For example, "a month later" of 2014-01-30 is not well-defined
and consequently `UTC.ymd(2014, 1, 30).with_month(2)` returns `None`.

Advanced offset handling is not yet supported (but is planned in 0.3).

*/

#![doc(html_root_url = "https://lifthrasiir.github.io/rust-chrono/")]

#![feature(core, collections, hash, std_misc)] // lib stability features as per RFC #507
#![cfg_attr(test, feature(test))] // ditto
#![deny(missing_docs)]

extern crate "time" as stdtime;

pub use duration::Duration;
pub use offset::{Offset, LocalResult};
pub use offset::{UTC, FixedOffset, Local};
pub use naive::date::NaiveDate;
pub use naive::time::NaiveTime;
pub use naive::datetime::NaiveDateTime;
pub use date::Date;
pub use time::Time;
pub use datetime::DateTime;
pub use format::{ParseError, ParseResult};

// useful throughout the codebase
macro_rules! try_opt {
    ($e:expr) => (match $e { Some(v) => v, None => return None })
}

mod div;
pub mod duration {
    //! ISO 8601 duration.
    //!
    //! This used to be a part of rust-chrono,
    //! but has been subsequently merged into Rust's standard library.
    pub use std::time::duration::{MIN, MAX, Duration};
}
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
pub mod format;

/// The day of week (DOW).
///
/// The order of the days of week depends on the context.
/// One should prefer `*_from_monday` or `*_from_sunday` methods to get the correct result.
#[derive(PartialEq, Eq, Copy, Clone, FromPrimitive, Debug)]
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
            Weekday::Mon => Weekday::Tue,
            Weekday::Tue => Weekday::Wed,
            Weekday::Wed => Weekday::Thu,
            Weekday::Thu => Weekday::Fri,
            Weekday::Fri => Weekday::Sat,
            Weekday::Sat => Weekday::Sun,
            Weekday::Sun => Weekday::Mon,
        }
    }

    /// The previous day in the week.
    #[inline]
    pub fn pred(&self) -> Weekday {
        match *self {
            Weekday::Mon => Weekday::Sun,
            Weekday::Tue => Weekday::Mon,
            Weekday::Wed => Weekday::Tue,
            Weekday::Thu => Weekday::Wed,
            Weekday::Fri => Weekday::Thu,
            Weekday::Sat => Weekday::Fri,
            Weekday::Sun => Weekday::Sat,
        }
    }

    /// Returns a DOW number starting from Monday = 1. (ISO 8601 weekday number)
    #[inline]
    pub fn number_from_monday(&self) -> u32 {
        match *self {
            Weekday::Mon => 1,
            Weekday::Tue => 2,
            Weekday::Wed => 3,
            Weekday::Thu => 4,
            Weekday::Fri => 5,
            Weekday::Sat => 6,
            Weekday::Sun => 7,
        }
    }

    /// Returns a DOW number starting from Sunday = 1.
    #[inline]
    pub fn number_from_sunday(&self) -> u32 {
        match *self {
            Weekday::Mon => 2,
            Weekday::Tue => 3,
            Weekday::Wed => 4,
            Weekday::Thu => 5,
            Weekday::Fri => 6,
            Weekday::Sat => 7,
            Weekday::Sun => 1,
        }
    }

    /// Returns a DOW number starting from Monday = 0.
    #[inline]
    pub fn num_days_from_monday(&self) -> u32 {
        match *self {
            Weekday::Mon => 0,
            Weekday::Tue => 1,
            Weekday::Wed => 2,
            Weekday::Thu => 3,
            Weekday::Fri => 4,
            Weekday::Sat => 5,
            Weekday::Sun => 6,
        }
    }

    /// Returns a DOW number starting from Sunday = 0.
    #[inline]
    pub fn num_days_from_sunday(&self) -> u32 {
        match *self {
            Weekday::Mon => 1,
            Weekday::Tue => 2,
            Weekday::Wed => 3,
            Weekday::Thu => 4,
            Weekday::Fri => 5,
            Weekday::Sat => 6,
            Weekday::Sun => 0,
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

