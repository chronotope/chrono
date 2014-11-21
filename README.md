Rust-chrono
===========

[![Rust-chrono on Travis CI][travis-image]][travis]

[travis-image]: https://travis-ci.org/lifthrasiir/rust-chrono.png
[travis]: https://travis-ci.org/lifthrasiir/rust-chrono

Date and time handling for Rust.

[Complete Documentation](https://lifthrasiir.github.io/rust-chrono/chrono/)

```rust
// find out if the doomsday rule is correct!
use chrono::{Weekday, NaiveDate, naive};
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
```

Design Goals
------------

* 1-to-1 correspondence with ISO 8601.
* Timezone-aware by default.
* Space efficient.
* Moderate lookup table size, should not exceed a few KBs.
* Avoid divisions as much as possible.

References
----------

* https://github.com/mozilla/rust/wiki/Lib-datetime
* https://github.com/luisbg/rust-datetime/wiki/Use-Cases

