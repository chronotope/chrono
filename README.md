[Chrono][docsrs]: Timezone-aware date and time handling
========================================

[![Chrono GitHub Actions][gh-image]][gh-checks]
[![Chrono on crates.io][cratesio-image]][cratesio]
[![Chrono on docs.rs][docsrs-image]][docsrs]
[![Chat][discord-image]][discord]
[![codecov.io][codecov-img]][codecov-link]

[gh-image]: https://github.com/chronotope/chrono/actions/workflows/test.yml/badge.svg?branch=0.5.x
[gh-checks]: https://github.com/chronotope/chrono/actions/workflows/test.yml?query=branch%3A0.5.x
[cratesio-image]: https://img.shields.io/crates/v/chrono.svg
[cratesio]: https://crates.io/crates/chrono
[docsrs-image]: https://docs.rs/chrono/badge.svg
[docsrs]: https://docs.rs/chrono
[discord-image]: https://img.shields.io/discord/976380008299917365?logo=discord
[discord]: https://discord.gg/sXpav4PS7M
[codecov-img]: https://img.shields.io/codecov/c/github/chronotope/chrono?logo=codecov
[codecov-link]: https://codecov.io/gh/chronotope/chrono

Chrono aims to provide all functionality needed to do correct operations on dates and times in the
[proleptic Gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar):

* The [`DateTime`](https://docs.rs/chrono/latest/chrono/struct.DateTime.html) type is timezone-aware
  by default, with separate timezone-naive types.
* Operations that may produce an invalid or ambiguous date and time return `Option` or
  [`MappedLocalTime`](https://docs.rs/chrono/latest/chrono/offset/enum.MappedLocalTime.html).
* Configurable parsing and formatting with an `strftime` inspired date and time formatting syntax.
* The [`Local`](https://docs.rs/chrono/latest/chrono/offset/struct.Local.html) timezone works with
  the current timezone of the OS.
* Types and operations are implemented to be reasonably efficient.

Timezone data is not shipped with chrono by default to limit binary sizes. Use the companion crate
[Chrono-TZ](https://crates.io/crates/chrono-tz) or [`tzfile`](https://crates.io/crates/tzfile) for
full timezone support.

## Documentation

See [docs.rs](https://docs.rs/chrono/latest/chrono/) for the API reference.

## Limitations

* Only the proleptic Gregorian calendar (i.e. extended to support older dates) is supported.
* Date types are limited to about +/- 262,000 years from the common epoch.
* Time types are limited to nanosecond accuracy.
* Leap seconds can be represented, but Chrono does not fully support them.
  See [Leap Second Handling](https://docs.rs/chrono/latest/chrono/naive/struct.NaiveTime.html#leap-second-handling).

## Crate features

Default features:

* `std`: Implements `TryFrom<SystemTime>` and `std::error::Error` for error types, implies `alloc`.
* `alloc`: Enable features that depend on allocation (primarily string formatting).
* `clock`: Enables reading the local timezone (`Local`), implies `now`.
* `now`: Enables reading the system time (`now()`), on most platforms using the standard library.

Optional features:

* `serde`: Enable serialization/deserialization via [serde].
* `rkyv-16`: Enable serialization/deserialization via [rkyv], using 16-bit integers for integral `*size` types.
* `rkyv-32`: Enable serialization/deserialization via [rkyv], using 32-bit integers for integral `*size` types.
* `rkyv-64`: Enable serialization/deserialization via [rkyv], using 64-bit integers for integral `*size` types.
* `rkyv-validation`: Enable rkyv validation support using `bytecheck`.
* `arbitrary`: Construct arbitrary instances of a type with the [arbitrary] crate.
* `wasmbind`: Interface with the JS Date API for the `wasm32` target.
* `unstable-locales`: Enable localization. This adds various methods with a `_localized` suffix.
  The implementation and API may change or even be removed in a patch release. Feedback welcome.

Note: The `rkyv-{16,32,64}` features are mutually exclusive.

[serde]: https://github.com/serde-rs/serde
[rkyv]: https://github.com/rkyv/rkyv
[arbitrary]: https://github.com/rust-fuzz/arbitrary/

## Rust version requirements

The Minimum Supported Rust Version (MSRV) is currently **Rust 1.61.0**.

The MSRV is explicitly tested in CI. It may be bumped in minor releases, but this is not done
lightly.

## License

This project is licensed under either of

* [Apache License, Version 2.0](https://www.apache.org/licenses/LICENSE-2.0)
* [MIT License](https://opensource.org/licenses/MIT)

at your option.
