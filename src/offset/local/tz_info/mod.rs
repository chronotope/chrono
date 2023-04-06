#![allow(dead_code)]
#![warn(unreachable_pub)]

mod timezone;
pub(crate) use timezone::TimeZone;

mod parser;
mod rule;

// MSRV: 1.38
#[inline]
const fn rem_euclid(v: i64, rhs: i64) -> i64 {
    let r = v % rhs;
    if r < 0 {
        if rhs < 0 {
            r - rhs
        } else {
            r + rhs
        }
    } else {
        r
    }
}

/// Number of hours in one day
const HOURS_PER_DAY: i64 = 24;
/// Number of seconds in one hour
const SECONDS_PER_HOUR: i64 = 3600;
/// Number of seconds in one day
const SECONDS_PER_DAY: i64 = SECONDS_PER_HOUR * HOURS_PER_DAY;
/// Number of days in one week
const DAYS_PER_WEEK: i64 = 7;

/// Month days in a normal year
const DAY_IN_MONTHS_NORMAL_YEAR: [i64; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
/// Cumulated month days in a normal year
const CUMUL_DAY_IN_MONTHS_NORMAL_YEAR: [i64; 12] =
    [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];
