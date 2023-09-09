//! # Chrono: Date and Time for Rust
//!

//! Chrono aims to provide all functionality needed to do correct operations on dates and times in the
//! [proleptic Gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar):
//!
//! * The [`DateTime`](https://docs.rs/chrono/latest/chrono/struct.DateTime.html) type is timezone-aware
//!   by default, with separate timezone-naive types.
//! * Operations that may produce an invalid or ambiguous date and time return `Option` or
//!   [`LocalResult`](https://docs.rs/chrono/latest/chrono/offset/enum.LocalResult.html).
//! * Configurable parsing and formatting with a `strftime` inspired date and time formatting syntax.
//! * The [`Local`](https://docs.rs/chrono/latest/chrono/offset/struct.Local.html) timezone works with
//!   the current timezone of the OS.
//! * Types and operations are implemented to be reasonably efficient.
//!
//! Timezone data is not shipped with chrono by default to limit binary sizes. Use the companion crate
//! [Chrono-TZ](https://crates.io/crates/chrono-tz) or [`tzfile`](https://crates.io/crates/tzfile) for
//! full timezone support.
//!
//! ### Features
//!
//! Chrono supports various runtime environments and operating systems, and has
//! several features that may be enabled or disabled.
//!
//! Default features:
//!
//! - `alloc`: Enable features that depend on allocation (primarily string formatting)
//! - `std`: Enables functionality that depends on the standard library. This
//!   is a superset of `alloc` and adds interoperation with standard library types
//!   and traits.
//! - `clock`: Enables reading the system time (`now`) that depends on the standard library for
//! UNIX-like operating systems and the Windows API (`winapi`) for Windows.
//! - `wasmbind`: Interface with the JS Date API for the `wasm32` target.
//!
//! Optional features:
//!
//! - [`serde`][]: Enable serialization/deserialization via serde.
//! - `rkyv`: Enable serialization/deserialization via rkyv.
//! - `arbitrary`: construct arbitrary instances of a type with the Arbitrary crate.
//! - `unstable-locales`: Enable localization. This adds various methods with a
//!   `_localized` suffix. The implementation and API may change or even be
//!   removed in a patch release. Feedback welcome.
//! - `oldtime`: this feature no langer has a function, but once offered compatibility with the
//!   `time` 0.1 crate.
//!
//! [`serde`]: https://github.com/serde-rs/serde
//! [wasm-bindgen]: https://github.com/rustwasm/wasm-bindgen
//!
//! See the [cargo docs][] for examples of specifying features.
//!
//! [cargo docs]: https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#choosing-features
//!
//! ## Overview
//!
//! ### Duration
//!
//! Chrono currently uses its own [`Duration`] type to represent the magnitude
//! of a time span. Since this has the same name as the newer, standard type for
//! duration, the reference will refer this type as `OldDuration`.
//!
//! Note that this is an "accurate" duration represented as seconds and
//! nanoseconds and does not represent "nominal" components such as days or
//! months.
//!
//! Chrono does not yet natively support
//! the standard [`Duration`](https://doc.rust-lang.org/std/time/struct.Duration.html) type,
//! but it will be supported in the future.
//! Meanwhile you can convert between two types with
//! [`Duration::from_std`](https://docs.rs/time/0.1.40/time/struct.Duration.html#method.from_std)
//! and
//! [`Duration::to_std`](https://docs.rs/time/0.1.40/time/struct.Duration.html#method.to_std)
//! methods.
//!
//! ### Date and Time
//!
//! Chrono provides a
//! [**`DateTime`**](./struct.DateTime.html)
//! type to represent a date and a time in a timezone.
//!
//! For more abstract moment-in-time tracking such as internal timekeeping
//! that is unconcerned with timezones, consider
//! [`time::SystemTime`](https://doc.rust-lang.org/std/time/struct.SystemTime.html),
//! which tracks your system clock, or
//! [`time::Instant`](https://doc.rust-lang.org/std/time/struct.Instant.html), which
//! is an opaque but monotonically-increasing representation of a moment in time.
//!
//! `DateTime` is timezone-aware and must be constructed from
//! the [**`TimeZone`**](./offset/trait.TimeZone.html) object,
//! which defines how the local date is converted to and back from the UTC date.
//! There are three well-known `TimeZone` implementations:
//!
//! * [**`Utc`**](./offset/struct.Utc.html) specifies the UTC time zone. It is most efficient.
//!
//! * [**`Local`**](./offset/struct.Local.html) specifies the system local time zone.
//!
//! * [**`FixedOffset`**](./offset/struct.FixedOffset.html) specifies
//!   an arbitrary, fixed time zone such as UTC+09:00 or UTC-10:30.
//!   This often results from the parsed textual date and time.
//!   Since it stores the most information and does not depend on the system environment,
//!   you would want to normalize other `TimeZone`s into this type.
//!
//! `DateTime`s with different `TimeZone` types are distinct and do not mix,
//! but can be converted to each other using
//! the [`DateTime::with_timezone`](./struct.DateTime.html#method.with_timezone) method.
//!
//! You can get the current date and time in the UTC time zone
//! ([`Utc::now()`](./offset/struct.Utc.html#method.now))
//! or in the local time zone
//! ([`Local::now()`](./offset/struct.Local.html#method.now)).
//!
#![cfg_attr(not(feature = "clock"), doc = "```ignore")]
#![cfg_attr(feature = "clock", doc = "```rust")]
//! use chrono::prelude::*;
//!
//! let utc: DateTime<Utc> = Utc::now();       // e.g. `2014-11-28T12:45:59.324310806Z`
//! let local: DateTime<Local> = Local::now(); // e.g. `2014-11-28T21:45:59.324310806+09:00`
//! # let _ = utc; let _ = local;
//! ```
//!
//! Alternatively, you can create your own date and time.
//! This is a bit verbose due to Rust's lack of function and method overloading,
//! but in turn we get a rich combination of initialization methods.
//!
#![cfg_attr(not(feature = "std"), doc = "```ignore")]
#![cfg_attr(feature = "std", doc = "```rust")]
//! use chrono::prelude::*;
//! use chrono::offset::LocalResult;
//!
//! # fn doctest() -> Option<()> {
//!
//! let dt = Utc.with_ymd_and_hms(2014, 7, 8, 9, 10, 11).unwrap(); // `2014-07-08T09:10:11Z`
//! assert_eq!(dt, NaiveDate::from_ymd_opt(2014, 7, 8)?.and_hms_opt(9, 10, 11)?.and_local_timezone(Utc).unwrap());
//!
//! // July 8 is 188th day of the year 2014 (`o` for "ordinal")
//! assert_eq!(dt, NaiveDate::from_yo_opt(2014, 189)?.and_hms_opt(9, 10, 11)?.and_utc());
//! // July 8 is Tuesday in ISO week 28 of the year 2014.
//! assert_eq!(dt, NaiveDate::from_isoywd_opt(2014, 28, Weekday::Tue)?.and_hms_opt(9, 10, 11)?.and_utc());
//!
//! let dt = NaiveDate::from_ymd_opt(2014, 7, 8)?.and_hms_milli_opt(9, 10, 11, 12)?.and_local_timezone(Utc).unwrap(); // `2014-07-08T09:10:11.012Z`
//! assert_eq!(dt, NaiveDate::from_ymd_opt(2014, 7, 8)?.and_hms_micro_opt(9, 10, 11, 12_000)?.and_local_timezone(Utc).unwrap());
//! assert_eq!(dt, NaiveDate::from_ymd_opt(2014, 7, 8)?.and_hms_nano_opt(9, 10, 11, 12_000_000)?.and_local_timezone(Utc).unwrap());
//!
//! // dynamic verification
//! assert_eq!(Utc.with_ymd_and_hms(2014, 7, 8, 21, 15, 33),
//!            LocalResult::Single(NaiveDate::from_ymd_opt(2014, 7, 8)?.and_hms_opt(21, 15, 33)?.and_utc()));
//! assert_eq!(Utc.with_ymd_and_hms(2014, 7, 8, 80, 15, 33), LocalResult::None);
//! assert_eq!(Utc.with_ymd_and_hms(2014, 7, 38, 21, 15, 33), LocalResult::None);
//!
//! // other time zone objects can be used to construct a local datetime.
//! // obviously, `local_dt` is normally different from `dt`, but `fixed_dt` should be identical.
//! let local_dt = Local.from_local_datetime(&NaiveDate::from_ymd_opt(2014, 7, 8).unwrap().and_hms_milli_opt(9, 10, 11, 12).unwrap()).unwrap();
//! let fixed_dt = FixedOffset::east_opt(9 * 3600).unwrap().from_local_datetime(&NaiveDate::from_ymd_opt(2014, 7, 8).unwrap().and_hms_milli_opt(18, 10, 11, 12).unwrap()).unwrap();
//! assert_eq!(dt, fixed_dt);
//! # let _ = local_dt;
//! # Some(())
//! # }
//! # doctest().unwrap();
//! ```
//!
//! Various properties are available to the date and time, and can be altered individually.
//! Most of them are defined in the traits [`Datelike`](./trait.Datelike.html) and
//! [`Timelike`](./trait.Timelike.html) which you should `use` before.
//! Addition and subtraction is also supported.
//! The following illustrates most supported operations to the date and time:
//!
//! ```rust
//! use chrono::prelude::*;
//! use chrono::Duration;
//!
//! // assume this returned `2014-11-28T21:45:59.324310806+09:00`:
//! let dt = FixedOffset::east_opt(9*3600).unwrap().from_local_datetime(&NaiveDate::from_ymd_opt(2014, 11, 28).unwrap().and_hms_nano_opt(21, 45, 59, 324310806).unwrap()).unwrap();
//!
//! // property accessors
//! assert_eq!((dt.year(), dt.month(), dt.day()), (2014, 11, 28));
//! assert_eq!((dt.month0(), dt.day0()), (10, 27)); // for unfortunate souls
//! assert_eq!((dt.hour(), dt.minute(), dt.second()), (21, 45, 59));
//! assert_eq!(dt.weekday(), Weekday::Fri);
//! assert_eq!(dt.weekday().number_from_monday(), 5); // Mon=1, ..., Sun=7
//! assert_eq!(dt.ordinal(), 332); // the day of year
//! assert_eq!(dt.num_days_from_ce(), 735565); // the number of days from and including Jan 1, 1
//!
//! // time zone accessor and manipulation
//! assert_eq!(dt.offset().fix().local_minus_utc(), 9 * 3600);
//! assert_eq!(dt.timezone(), FixedOffset::east_opt(9 * 3600).unwrap());
//! assert_eq!(dt.with_timezone(&Utc), NaiveDate::from_ymd_opt(2014, 11, 28).unwrap().and_hms_nano_opt(12, 45, 59, 324310806).unwrap().and_local_timezone(Utc).unwrap());
//!
//! // a sample of property manipulations (validates dynamically)
//! assert_eq!(dt.with_day(29).unwrap().weekday(), Weekday::Sat); // 2014-11-29 is Saturday
//! assert_eq!(dt.with_day(32), None);
//! assert_eq!(dt.with_year(-300).unwrap().num_days_from_ce(), -109606); // November 29, 301 BCE
//!
//! // arithmetic operations
//! let dt1 = Utc.with_ymd_and_hms(2014, 11, 14, 8, 9, 10).unwrap();
//! let dt2 = Utc.with_ymd_and_hms(2014, 11, 14, 10, 9, 8).unwrap();
//! assert_eq!(dt1.signed_duration_since(dt2), Duration::seconds(-2 * 3600 + 2));
//! assert_eq!(dt2.signed_duration_since(dt1), Duration::seconds(2 * 3600 - 2));
//! assert_eq!(Utc.with_ymd_and_hms(1970, 1, 1, 0, 0, 0).unwrap() + Duration::seconds(1_000_000_000),
//!            Utc.with_ymd_and_hms(2001, 9, 9, 1, 46, 40).unwrap());
//! assert_eq!(Utc.with_ymd_and_hms(1970, 1, 1, 0, 0, 0).unwrap() - Duration::seconds(1_000_000_000),
//!            Utc.with_ymd_and_hms(1938, 4, 24, 22, 13, 20).unwrap());
//! ```
//!
//! ### Formatting and Parsing
//!
//! Formatting is done via the [`format`](./struct.DateTime.html#method.format) method,
//! which format is equivalent to the familiar `strftime` format.
//!
//! See [`format::strftime`](./format/strftime/index.html#specifiers)
//! documentation for full syntax and list of specifiers.
//!
//! The default `to_string` method and `{:?}` specifier also give a reasonable representation.
//! Chrono also provides [`to_rfc2822`](./struct.DateTime.html#method.to_rfc2822) and
//! [`to_rfc3339`](./struct.DateTime.html#method.to_rfc3339) methods
//! for well-known formats.
//!
//! Chrono now also provides date formatting in almost any language without the
//! help of an additional C library. This functionality is under the feature
//! `unstable-locales`:
//!
//! ```toml
//! chrono = { version = "0.4", features = ["unstable-locales"] }
//! ```
//!
//! The `unstable-locales` feature requires and implies at least the `alloc` feature.
//!
//! ```rust
//! # #[allow(unused_imports)]
//! use chrono::prelude::*;
//!
//! # #[cfg(feature = "unstable-locales")]
//! # fn test() {
//! let dt = Utc.with_ymd_and_hms(2014, 11, 28, 12, 0, 9).unwrap();
//! assert_eq!(dt.format("%Y-%m-%d %H:%M:%S").to_string(), "2014-11-28 12:00:09");
//! assert_eq!(dt.format("%a %b %e %T %Y").to_string(), "Fri Nov 28 12:00:09 2014");
//! assert_eq!(dt.format_localized("%A %e %B %Y, %T", Locale::fr_BE).to_string(), "vendredi 28 novembre 2014, 12:00:09");
//!
//! assert_eq!(dt.format("%a %b %e %T %Y").to_string(), dt.format("%c").to_string());
//! assert_eq!(dt.to_string(), "2014-11-28 12:00:09 UTC");
//! assert_eq!(dt.to_rfc2822(), "Fri, 28 Nov 2014 12:00:09 +0000");
//! assert_eq!(dt.to_rfc3339(), "2014-11-28T12:00:09+00:00");
//! assert_eq!(format!("{:?}", dt), "2014-11-28T12:00:09Z");
//!
//! // Note that milli/nanoseconds are only printed if they are non-zero
//! let dt_nano = NaiveDate::from_ymd_opt(2014, 11, 28).unwrap().and_hms_nano_opt(12, 0, 9, 1).unwrap().and_local_timezone(Utc).unwrap();
//! assert_eq!(format!("{:?}", dt_nano), "2014-11-28T12:00:09.000000001Z");
//! # }
//! # #[cfg(not(feature = "unstable-locales"))]
//! # fn test() {}
//! # if cfg!(feature = "unstable-locales") {
//! #    test();
//! # }
//! ```
//!
//! Parsing can be done with three methods:
//!
//! 1. The standard [`FromStr`](https://doc.rust-lang.org/std/str/trait.FromStr.html) trait
//!    (and [`parse`](https://doc.rust-lang.org/std/primitive.str.html#method.parse) method
//!    on a string) can be used for parsing `DateTime<FixedOffset>`, `DateTime<Utc>` and
//!    `DateTime<Local>` values. This parses what the `{:?}`
//!    ([`std::fmt::Debug`](https://doc.rust-lang.org/std/fmt/trait.Debug.html))
//!    format specifier prints, and requires the offset to be present.
//!
//! 2. [`DateTime::parse_from_str`](./struct.DateTime.html#method.parse_from_str) parses
//!    a date and time with offsets and returns `DateTime<FixedOffset>`.
//!    This should be used when the offset is a part of input and the caller cannot guess that.
//!    It *cannot* be used when the offset can be missing.
//!    [`DateTime::parse_from_rfc2822`](./struct.DateTime.html#method.parse_from_rfc2822)
//!    and
//!    [`DateTime::parse_from_rfc3339`](./struct.DateTime.html#method.parse_from_rfc3339)
//!    are similar but for well-known formats.
//!
//! 3. [`Offset::datetime_from_str`](./offset/trait.TimeZone.html#method.datetime_from_str) is
//!    similar but returns `DateTime` of given offset.
//!    When the explicit offset is missing from the input, it simply uses given offset.
//!    It issues an error when the input contains an explicit offset different
//!    from the current offset.
//!
//! More detailed control over the parsing process is available via
//! [`format`](./format/index.html) module.
//!
//! ```rust
//! use chrono::prelude::*;
//!
//! let dt = Utc.with_ymd_and_hms(2014, 11, 28, 12, 0, 9).unwrap();
//! let fixed_dt = dt.with_timezone(&FixedOffset::east_opt(9*3600).unwrap());
//!
//! // method 1
//! assert_eq!("2014-11-28T12:00:09Z".parse::<DateTime<Utc>>(), Ok(dt.clone()));
//! assert_eq!("2014-11-28T21:00:09+09:00".parse::<DateTime<Utc>>(), Ok(dt.clone()));
//! assert_eq!("2014-11-28T21:00:09+09:00".parse::<DateTime<FixedOffset>>(), Ok(fixed_dt.clone()));
//!
//! // method 2
//! assert_eq!(DateTime::parse_from_str("2014-11-28 21:00:09 +09:00", "%Y-%m-%d %H:%M:%S %z"),
//!            Ok(fixed_dt.clone()));
//! assert_eq!(DateTime::parse_from_rfc2822("Fri, 28 Nov 2014 21:00:09 +0900"),
//!            Ok(fixed_dt.clone()));
//! assert_eq!(DateTime::parse_from_rfc3339("2014-11-28T21:00:09+09:00"), Ok(fixed_dt.clone()));
//!
//! // oops, the year is missing!
//! assert!(DateTime::parse_from_str("Fri Nov 28 12:00:09", "%a %b %e %T %Y").is_err());
//! // oops, the format string does not include the year at all!
//! assert!(DateTime::parse_from_str("Fri Nov 28 12:00:09", "%a %b %e %T").is_err());
//! // oops, the weekday is incorrect!
//! assert!(DateTime::parse_from_str("Sat Nov 28 12:00:09 2014", "%a %b %e %T %Y").is_err());
//! ```
//!
//! Again : See [`format::strftime`](./format/strftime/index.html#specifiers)
//! documentation for full syntax and list of specifiers.
//!
//! ### Conversion from and to EPOCH timestamps
//!
//! Use [`DateTime::from_timestamp(seconds, nanoseconds)`](DateTime::from_timestamp)
//! to construct a [`DateTime<Utc>`] from a UNIX timestamp
//! (seconds, nanoseconds that passed since January 1st 1970).
//!
//! Use [`DateTime.timestamp`](DateTime::timestamp) to get the timestamp (in seconds)
//! from a [`DateTime`]. Additionally, you can use
//! [`DateTime.timestamp_subsec_nanos`](DateTime::timestamp_subsec_nanos)
//! to get the number of additional number of nanoseconds.
//!
#![cfg_attr(not(feature = "std"), doc = "```ignore")]
#![cfg_attr(feature = "std", doc = "```rust")]
//! // We need the trait in scope to use Utc::timestamp().
//! use chrono::{DateTime, Utc};
//!
//! // Construct a datetime from epoch:
//! let dt: DateTime<Utc> = DateTime::from_timestamp(1_500_000_000, 0).unwrap();
//! assert_eq!(dt.to_rfc2822(), "Fri, 14 Jul 2017 02:40:00 +0000");
//!
//! // Get epoch value from a datetime:
//! let dt = DateTime::parse_from_rfc2822("Fri, 14 Jul 2017 02:40:00 +0000").unwrap();
//! assert_eq!(dt.timestamp(), 1_500_000_000);
//! ```
//!
//! ### Naive date and time
//!
//! Chrono provides naive counterparts to `Date`, (non-existent) `Time` and `DateTime`
//! as [**`NaiveDate`**](./naive/struct.NaiveDate.html),
//! [**`NaiveTime`**](./naive/struct.NaiveTime.html) and
//! [**`NaiveDateTime`**](./naive/struct.NaiveDateTime.html) respectively.
//!
//! They have almost equivalent interfaces as their timezone-aware twins,
//! but are not associated to time zones obviously and can be quite low-level.
//! They are mostly useful for building blocks for higher-level types.
//!
//! Timezone-aware `DateTime` and `Date` types have two methods returning naive versions:
//! [`naive_local`](./struct.DateTime.html#method.naive_local) returns
//! a view to the naive local time,
//! and [`naive_utc`](./struct.DateTime.html#method.naive_utc) returns
//! a view to the naive UTC time.
//!
//! ## Limitations
//!
//! Only the proleptic Gregorian calendar (i.e. extended to support older dates) is supported.
//! Date types are limited to about +/- 262,000 years from the common epoch.
//! Time types are limited to nanosecond accuracy.
//! Leap seconds can be represented, but Chrono does not fully support them.
//! See [Leap Second Handling](https://docs.rs/chrono/latest/chrono/naive/struct.NaiveTime.html#leap-second-handling).
//!
//! ## Rust version requirements
//!
//! The Minimum Supported Rust Version (MSRV) is currently **Rust 1.57.0**.
//!
//! The MSRV is explicitly tested in CI. It may be bumped in minor releases, but this is not done
//! lightly.
//!
//! Chrono inherently does not support an inaccurate or partial date and time representation.
//! Any operation that can be ambiguous will return `None` in such cases.
//! For example, "a month later" of 2014-01-30 is not well-defined
//! and consequently `Utc.ymd_opt(2014, 1, 30).unwrap().with_month(2)` returns `None`.
//!
//! Non ISO week handling is not yet supported.
//! For now you can use the [chrono_ext](https://crates.io/crates/chrono_ext)
//! crate ([sources](https://github.com/bcourtine/chrono-ext/)).
//!
//! Advanced time zone handling is not yet supported.
//! For now you can try the [Chrono-tz](https://github.com/chronotope/chrono-tz/) crate instead.
//!
//! ## Relation between chrono and time 0.1
//!
//! Rust first had a `time` module added to `std` in its 0.7 release. It later moved to
//! `libextra`, and then to a `libtime` library shipped alongside the standard library. In 2014
//! work on chrono started in order to provide a full-featured date and time library in Rust.
//! Some improvements from chrono made it into the standard library; notably, `chrono::Duration`
//! was included as `std::time::Duration` ([rust#15934]) in 2014.
//!
//! In preparation of Rust 1.0 at the end of 2014 `libtime` was moved out of the Rust distro and
//! into the `time` crate to eventually be redesigned ([rust#18832], [rust#18858]), like the
//! `num` and `rand` crates. Of course chrono kept its dependency on this `time` crate. `time`
//! started re-exporting `std::time::Duration` during this period. Later, the standard library was
//! changed to have a more limited unsigned `Duration` type ([rust#24920], [RFC 1040]), while the
//! `time` crate kept the full functionality with `time::Duration`. `time::Duration` had been a
//! part of chrono's public API.
//!
//! By 2016 `time` 0.1 lived under the `rust-lang-deprecated` organisation and was not actively
//! maintained ([time#136]). chrono absorbed the platform functionality and `Duration` type of the
//! `time` crate in [chrono#478] (the work started in [chrono#286]). In order to preserve
//! compatibility with downstream crates depending on `time` and `chrono` sharing a `Duration`
//! type, chrono kept depending on time 0.1. chrono offered the option to opt out of the `time`
//! dependency by disabling the `oldtime` feature (swapping it out for an effectively similar
//! chrono type). In 2019, @jhpratt took over maintenance on the `time` crate and released what
//! amounts to a new crate as `time` 0.2.
//!
//! [rust#15934]: https://github.com/rust-lang/rust/pull/15934
//! [rust#18832]: https://github.com/rust-lang/rust/pull/18832#issuecomment-62448221
//! [rust#18858]: https://github.com/rust-lang/rust/pull/18858
//! [rust#24920]: https://github.com/rust-lang/rust/pull/24920
//! [RFC 1040]: https://rust-lang.github.io/rfcs/1040-duration-reform.html
//! [time#136]: https://github.com/time-rs/time/issues/136
//! [chrono#286]: https://github.com/chronotope/chrono/pull/286
//! [chrono#478]: https://github.com/chronotope/chrono/pull/478
//!
//! ## Security advisories
//!
//! In November of 2020 [CVE-2020-26235] and [RUSTSEC-2020-0071] were opened against the `time` crate.
//! @quininer had found that calls to `localtime_r` may be unsound ([chrono#499]). Eventually, almost
//! a year later, this was also made into a security advisory against chrono as [RUSTSEC-2020-0159],
//! which had platform code similar to `time`.
//!
//! On Unix-like systems a process is given a timezone id or description via the `TZ` environment
//! variable. We need this timezone data to calculate the current local time from a value that is
//! in UTC, such as the time from the system clock. `time` 0.1 and chrono used the POSIX function
//! `localtime_r` to do the conversion to local time, which reads the `TZ` variable.
//!
//! Rust assumes the environment to be writable and uses locks to access it from multiple threads.
//! Some other programming languages and libraries use similar locking strategies, but these are
//! typically not shared across languages. More importantly, POSIX declares modifying the
//! environment in a multi-threaded process as unsafe, and `getenv` in libc can't be changed to
//! take a lock because it returns a pointer to the data (see [rust#27970] for more discussion).
//!
//! Since version 4.20 chrono no longer uses `localtime_r`, instead using Rust code to query the
//! timezone (from the `TZ` variable or via `iana-time-zone` as a fallback) and work with data
//! from the system timezone database directly. The code for this was forked from the [tz-rs crate]
//! by @x-hgg-x. As such, chrono now respects the Rust lock when reading the `TZ` environment
//! variable. In general, code should avoid modifying the environment.
//!
//! [CVE-2020-26235]: https://nvd.nist.gov/vuln/detail/CVE-2020-26235
//! [RUSTSEC-2020-0071]: https://rustsec.org/advisories/RUSTSEC-2020-0071
//! [chrono#499]: https://github.com/chronotope/chrono/pull/499
//! [RUSTSEC-2020-0159]: https://rustsec.org/advisories/RUSTSEC-2020-0159.html
//! [rust#27970]: https://github.com/rust-lang/rust/issues/27970
//! [chrono#677]: https://github.com/chronotope/chrono/pull/677
//! [tz-rs crate]: https://crates.io/crates/tz-rs
//!
//! ## Removing time 0.1
//!
//! Because time 0.1 has been unmaintained for years, however, the security advisory mentioned
//! above has not been addressed. While chrono maintainers were careful not to break backwards
//! compatibility with the `time::Duration` type, there has been a long stream of issues from
//! users inquiring about the time 0.1 dependency with the vulnerability. We investigated the
//! potential breakage of removing the time 0.1 dependency in [chrono#1095] using a crater-like
//! experiment and determined that the potential for breaking (public) dependencies is very low.
//! We reached out to those few crates that did still depend on compatibility with time 0.1.
//!
//! As such, for chrono 0.4.30 we have decided to swap out the time 0.1 `Duration` implementation
//! for a local one that will offer a strict superset of the existing API going forward. This
//! will prevent most downstream users from being affected by the security vulnerability in time
//! 0.1 while minimizing the ecosystem impact of semver-incompatible version churn.
//!
//! [chrono#1095]: https://github.com/chronotope/chrono/pull/1095

#![doc(html_root_url = "https://docs.rs/chrono/latest/", test(attr(deny(warnings))))]
#![cfg_attr(feature = "bench", feature(test))] // lib stability features as per RFC #507
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![warn(unreachable_pub)]
#![deny(clippy::tests_outside_test_module)]
#![cfg_attr(not(any(feature = "std", test)), no_std)]
// can remove this if/when rustc-serialize support is removed
// keeps clippy happy in the meantime
#![cfg_attr(feature = "rustc-serialize", allow(deprecated))]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;

mod duration;
pub use duration::Duration;
#[cfg(feature = "std")]
pub use duration::OutOfRangeError;

use core::fmt;

/// A convenience module appropriate for glob imports (`use chrono::prelude::*;`).
pub mod prelude {
    #[doc(no_inline)]
    #[allow(deprecated)]
    pub use crate::Date;
    #[cfg(feature = "clock")]
    #[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
    #[doc(no_inline)]
    pub use crate::Local;
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[doc(no_inline)]
    pub use crate::Locale;
    #[doc(no_inline)]
    pub use crate::SubsecRound;
    #[doc(no_inline)]
    pub use crate::{DateTime, SecondsFormat};
    #[doc(no_inline)]
    pub use crate::{Datelike, Month, Timelike, Weekday};
    #[doc(no_inline)]
    pub use crate::{FixedOffset, Utc};
    #[doc(no_inline)]
    pub use crate::{NaiveDate, NaiveDateTime, NaiveTime};
    #[doc(no_inline)]
    pub use crate::{Offset, TimeZone};
}

mod date;
#[allow(deprecated)]
pub use date::{Date, MAX_DATE, MIN_DATE};

mod datetime;
#[cfg(feature = "rustc-serialize")]
#[cfg_attr(docsrs, doc(cfg(feature = "rustc-serialize")))]
pub use datetime::rustc_serialize::TsSeconds;
#[allow(deprecated)]
pub use datetime::{DateTime, SecondsFormat, MAX_DATETIME, MIN_DATETIME};

pub mod format;
/// L10n locales.
#[cfg(feature = "unstable-locales")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
pub use format::Locale;
pub use format::{ParseError, ParseResult};

pub mod naive;
#[doc(no_inline)]
pub use naive::{Days, IsoWeek, NaiveDate, NaiveDateTime, NaiveTime, NaiveWeek};

pub mod offset;
#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
#[doc(no_inline)]
pub use offset::Local;
#[doc(no_inline)]
pub use offset::{FixedOffset, LocalResult, Offset, TimeZone, Utc};

mod round;
pub use round::{DurationRound, RoundingError, SubsecRound};

mod weekday;
pub use weekday::{ParseWeekdayError, Weekday};

mod month;
pub use month::{Month, Months, ParseMonthError};

mod traits;
pub use traits::{Datelike, Timelike};

#[cfg(feature = "__internal_bench")]
#[doc(hidden)]
pub use naive::__BenchYearFlags;

/// Serialization/Deserialization with serde.
///
/// This module provides default implementations for `DateTime` using the [RFC 3339][1] format and various
/// alternatives for use with serde's [`with` annotation][2].
///
/// *Available on crate feature 'serde' only.*
///
/// [1]: https://tools.ietf.org/html/rfc3339
/// [2]: https://serde.rs/field-attrs.html#with
#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
pub mod serde {
    pub use super::datetime::serde::*;
}

/// Out of range error type used in various converting APIs
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct OutOfRange {
    _private: (),
}

impl OutOfRange {
    const fn new() -> OutOfRange {
        OutOfRange { _private: () }
    }
}

impl fmt::Display for OutOfRange {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "out of range")
    }
}

impl fmt::Debug for OutOfRange {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "out of range")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for OutOfRange {}

/// Workaround because `?` is not (yet) available in const context.
#[macro_export]
macro_rules! try_opt {
    ($e:expr) => {
        match $e {
            Some(v) => v,
            None => return None,
        }
    };
}

/// Workaround because `.expect()` is not (yet) available in const context.
#[macro_export]
macro_rules! expect {
    ($e:expr, $m:literal) => {
        match $e {
            Some(v) => v,
            None => panic!($m),
        }
    };
}
