ChangeLog for Chrono
====================

This documents all notable changes to [Chrono](https://github.com/lifthrasiir/rust-chrono).

Chrono obeys the principle of [Semantic Versioning](http://semver.org/).

There were/are numerous minor versions before 1.0 due to the language changes.
Versions with only mechnical changes will be omitted from the following list.

## 0.2.14 (2015-05-15)

### Fixed

- `NaiveDateTime +/- Duration` or `NaiveTime +/- Duration` could have gone wrong
  when the `Duration` to be added is negative and has a fractional second part.
  This was caused by an underflow in the conversion from `Duration` to the parts;
  the lack of tests for this case allowed a bug. (#37)

## 0.2.13 (2015-04-29)

### Added

- The optional dependency on `rustc_serialize` and
  relevant `Rustc{En,De}codable` implementations for supported types has been added.
  This is enabled by the `rustc-serialize` Cargo feature. (#34)

### Changed

- `chrono::Duration` reexport is changed to that of crates.io `time` crate.
  This enables Rust 1.0 beta compatibility.

## 0.2.4 (2015-03-03)

### Fixed

- Clarified the meaning of `Date<Tz>` and fixed unwanted conversion problem
  that only occurs with positive UTC offsets. (#27)

## 0.2.3 (2015-02-27)

### Added

- `DateTime<Tz>` and `Date<Tz>` is now `Copy`/`Send` when `Tz::Offset` is `Copy`/`Send`.
  The implementations for them were mistakenly omitted. (#25)

### Fixed

- `Local::from_utc_datetime` didn't set a correct offset. (#26)

## 0.2.1 (2015-02-21)

### Changed

- `DelayedFormat` no longer conveys a redundant lifetime.

## 0.2.0 (2015-02-19)

### Added

- `Offset` is splitted into `TimeZone` (constructor) and `Offset` (storage) types.
  You would normally see only the former, as the latter is mostly an implementation detail.
  Most importantly, `Local` now can be used to directly construct timezone-aware values.

  Some types (currently, `UTC` and `FixedOffset`) are both `TimeZone` and `Offset`,
  but others aren't (e.g. `Local` is not what is being stored to each `DateTime` values).

- `LocalResult::map` convenience method has been added.

- `TimeZone` now allows a construction of `DateTime` values from UNIX timestamp,
  via `timestamp` and `timestamp_opt` methods.

- `TimeZone` now also has a method for parsing `DateTime`, namely `datetime_from_str`.

- The following methods have been added to all date and time types:

    - `checked_add`
    - `checked_sub`
    - `format_with_items`

- The following methods have been added to all timezone-aware types:

    - `timezone`
    - `with_timezone`
    - `naive_utc`
    - `naive_local`

- `parse_from_str` method has been added to all naive types and `DateTime<FixedOffset>`.

- All naive types and instances of `DateTime` with time zones `UTC`, `Local` and `FixedOffset`
  implement the `FromStr` trait. They parse what `std::fmt::Debug` would print.

- `chrono::format` has been greatly rewritten.

    - The formatting syntax parser is modular now, available at `chrono::format::strftime`.

    - The parser and resolution algorithm is also modular, the former is available at
      `chrono::format::parse` while the latter is available at `chrono::format::parsed`.

    - Explicit support for RFC 2822 and 3339 syntaxes is landed.

    - There is a minor formatting difference with atypical values,
      e.g. for years not between 1 BCE and 9999 CE.

### Changed

- Most uses of `Offset` are converted to `TimeZone`.
  In fact, *all* user-facing code is expected to be `Offset`-free.

- `[Naive]DateTime::*num_seconds_from_unix_epoch*` methods have been renamed to
  simply `timestamp` or `from_timestamp*`. The original names have been deprecated.

### Removed

- `Time` has been removed. This also prompts a related set of methods in `TimeZone`.

  This is in principle possible, but in practice has seen a little use
  because it can only be meaningfully constructed via an existing `DateTime` value.
  This made many operations to `Time` unintuitive or ambiguous,
  so we simply let it go.

  In the case that `Time` is really required, one can use a simpler `NaiveTime`.
  `NaiveTime` and `NaiveDate` can be freely combined and splitted,
  and `TimeZone::from_{local,utc}_datetime` can be used to convert from/to the local time.

- `with_offset` method has been removed. Use `with_timezone` method instead.
  (This is not deprecated since it is an integral part of offset reform.)

## 0.1.14 (2015-01-10)

### Added

- Added a missing `std::fmt::String` impl for `Local`.

## 0.1.13 (2015-01-10)

### Changed

- Most types now implement both `std::fmt::Show` and `std::fmt::String`,
  with the former used for the stricter output and the latter used for more casual output.

### Removed

- `Offset::name` has been replaced by a `std::fmt::String` implementation to `Offset`.

## 0.1.12 (2015-01-08)

### Removed

- `Duration + T` no longer works due to the updated impl reachability rules.
  Use `T + Duration` as a workaround.

## 0.1.4 (2014-12-13)

### Fixed

- Fixed a bug that `Date::and_*` methods with an offset that can change the date are
  off by one day.

## 0.1.3 (2014-11-28)

### Added

- `{Date,Time,DateTime}::with_offset` methods have been added.

- `LocalResult` now implements a common set of traits.

- `LocalResult::and_*` methods have been added.
  They are useful for safely chaining `LocalResult<Date<Off>>` methods
  to make `LocalResult<DateTime<Off>>`.

### Changed

- `Offset::name` now returns `SendStr`.

- `{Date,Time} - Duration` overloadings are now allowed.

## 0.1.2 (2014-11-24)

### Added

- `Duration + Date` overloading is now allowed.

### Changed

- Chrono no longer needs `num` dependency.

## 0.1.0 (2014-11-20)

The initial version that was available to `crates.io`.

