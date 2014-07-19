// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

#![comment = "Date and time library for Rust"]
#![license = "MIT"]

#![feature(macro_rules)]

extern crate num;

pub use duration::{MIN_DAYS, MAX_DAYS, Duration};
pub use date::{MAX_YEAR, MIN_YEAR, Weekday, Mon, Tue, Wed, Thu, Fri, Sat, Sun};
pub use date::{Datelike, DateZ};
pub use time::{Timelike, TimeZ};
pub use datetime::DateTimeZ;

pub mod duration;
pub mod date;
pub mod time;
pub mod datetime;

#[test]
fn test_readme_doomsday() {
    use std::iter::range_inclusive;

    for y in range_inclusive(MIN_YEAR, MAX_YEAR) {
        // even months
        let d4   = DateZ::from_ymd(y,  4,  4);
        let d6   = DateZ::from_ymd(y,  6,  6);
        let d8   = DateZ::from_ymd(y,  8,  8);
        let d10  = DateZ::from_ymd(y, 10, 10);
        let d12  = DateZ::from_ymd(y, 12, 12);

        // nine to five, seven-eleven
        let d59  = DateZ::from_ymd(y,  5,  9);
        let d95  = DateZ::from_ymd(y,  9,  5);
        let d711 = DateZ::from_ymd(y,  7, 11);
        let d117 = DateZ::from_ymd(y, 11,  7);

        // "March 0"
        let d30  = DateZ::from_ymd(y,  3,  1).pred();

        let weekday = d30.weekday();
        let other_dates = [d4, d6, d8, d10, d12, d59, d95, d711, d117];
        assert!(other_dates.iter().all(|d| d.weekday() == weekday));
    }
}

