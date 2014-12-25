[Chrono][doc] 0.1.6
===================

[![Chrono on Travis CI][travis-image]][travis]

[travis-image]: https://travis-ci.org/lifthrasiir/rust-chrono.png
[travis]: https://travis-ci.org/lifthrasiir/rust-chrono

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

[Complete Documentation][doc]

[doc]: https://lifthrasiir.github.io/rust-chrono/chrono/

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
use chrono::{UTC, Local, Datelike, Timelike, Weekday, Duration};

// assume this returned `2014-11-28T21:45:59.324310806+09:00`:
let dt = Local::now();

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
The default `to_string` method also gives a reasonable representation.

~~~~ {.rust}
use chrono::{UTC, Offset};

let dt = UTC.ymd(2014, 11, 28).and_hms(12, 0, 9);
assert_eq!(dt.format("%Y-%m-%d %H:%M:%S").to_string(), "2014-11-28 12:00:09".to_string());
assert_eq!(dt.format("%a %b %e %T %Y").to_string(), "Fri Nov 28 12:00:09 2014".to_string());
assert_eq!(dt.format("%a %b %e %T %Y").to_string(), dt.format("%c").to_string());

assert_eq!(dt.to_string(), "2014-11-28T12:00:09Z".to_string());
~~~~

### Individual date and time

Chrono also provides an individual date type (`Date`) and time type (`Time`).
They also have offsets attached, and have to be constructed via offsets.
Most operations available to `DateTime` are also available to `Date` and `Time`
whenever appropriate.

~~~~ {.rust}
use chrono::{UTC, Local, Offset, LocalResult, Datelike, Weekday};

assert_eq!(UTC::today(), UTC::now().date());
assert_eq!(Local::today(), Local::now().date());

assert_eq!(UTC.ymd(2014, 11, 28).weekday(), Weekday::Fri);
assert_eq!(UTC.ymd_opt(2014, 11, 31), LocalResult::None);
assert_eq!(UTC.hms_milli(7, 8, 9, 10).format("%H%M%S").to_string(), "070809".to_string());
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

Advanced offset handling and date/time parsing is not yet supported (but is planned).

