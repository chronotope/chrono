// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The internal implementation of the calendar and ordinal date.
//!
//! The current implementation is optimized for determining year, month, day and day of week.
//! 4-bit `YearFlags` map to one of 14 possible classes of year in the Gregorian calendar,
//! which are included in every packed `NaiveDate` instance.
//! The conversion between the packed calendar date (`Mdf`) and the ordinal date (`Of`) is
//! based on the moderately-sized lookup table (~1.5KB)
//! and the packed representation is chosen for the efficient lookup.
//! Every internal data structure does not validate its input,
//! but the conversion keeps the valid value valid and the invalid value invalid
//! so that the user-facing `NaiveDate` can validate the input as late as possible.

#![cfg_attr(feature = "__internal_bench", allow(missing_docs))]

use crate::Weekday;
use core::{fmt, i32};

/// The internal date representation: `year << 13 | Of`
pub(super) type DateImpl = i32;

pub(super) const MAX_YEAR: DateImpl = i32::MAX >> 13;
pub(super) const MIN_YEAR: DateImpl = i32::MIN >> 13;

/// The year flags (aka the dominical letter).
///
/// There are 14 possible classes of year in the Gregorian calendar:
/// common and leap years starting with Monday through Sunday.
/// The `YearFlags` stores this information into 4 bits `abbb`,
/// where `a` is `1` for the common year (simplifies the `Of` validation)
/// and `bbb` is a non-zero `Weekday` (mapping `Mon` to 7) of the last day in the past year
/// (simplifies the day of week calculation from the 1-based ordinal).
#[allow(unreachable_pub)] // public as an alias for benchmarks only
#[derive(PartialEq, Eq, Copy, Clone, Hash)]
pub struct YearFlags(pub(super) u8);

pub(super) const A: YearFlags = YearFlags(0o15);
pub(super) const AG: YearFlags = YearFlags(0o05);
pub(super) const B: YearFlags = YearFlags(0o14);
pub(super) const BA: YearFlags = YearFlags(0o04);
pub(super) const C: YearFlags = YearFlags(0o13);
pub(super) const CB: YearFlags = YearFlags(0o03);
pub(super) const D: YearFlags = YearFlags(0o12);
pub(super) const DC: YearFlags = YearFlags(0o02);
pub(super) const E: YearFlags = YearFlags(0o11);
pub(super) const ED: YearFlags = YearFlags(0o01);
pub(super) const F: YearFlags = YearFlags(0o17);
pub(super) const FE: YearFlags = YearFlags(0o07);
pub(super) const G: YearFlags = YearFlags(0o16);
pub(super) const GF: YearFlags = YearFlags(0o06);

const YEAR_TO_FLAGS: &[YearFlags; 400] = &[
    BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA,
    G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G,
    F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F,
    E, DC, B, A, G, FE, D, C, B, AG, F, E, D, // 100
    C, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC,
    B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B,
    A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A,
    G, FE, D, C, B, AG, F, E, D, CB, A, G, F, // 200
    E, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE,
    D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D,
    C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C,
    B, AG, F, E, D, CB, A, G, F, ED, C, B, A, // 300
    G, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B, AG,
    F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F,
    E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E,
    D, CB, A, G, F, ED, C, B, A, GF, E, D, C, // 400
];

const YEAR_DELTAS: &[u8; 401] = &[
    0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8,
    8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14,
    15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 20, 20,
    21, 21, 21, 21, 22, 22, 22, 22, 23, 23, 23, 23, 24, 24, 24, 24, 25, 25, 25, // 100
    25, 25, 25, 25, 25, 26, 26, 26, 26, 27, 27, 27, 27, 28, 28, 28, 28, 29, 29, 29, 29, 30, 30, 30,
    30, 31, 31, 31, 31, 32, 32, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 35, 35, 36, 36, 36,
    36, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 39, 40, 40, 40, 40, 41, 41, 41, 41, 42, 42, 42,
    42, 43, 43, 43, 43, 44, 44, 44, 44, 45, 45, 45, 45, 46, 46, 46, 46, 47, 47, 47, 47, 48, 48, 48,
    48, 49, 49, 49, // 200
    49, 49, 49, 49, 49, 50, 50, 50, 50, 51, 51, 51, 51, 52, 52, 52, 52, 53, 53, 53, 53, 54, 54, 54,
    54, 55, 55, 55, 55, 56, 56, 56, 56, 57, 57, 57, 57, 58, 58, 58, 58, 59, 59, 59, 59, 60, 60, 60,
    60, 61, 61, 61, 61, 62, 62, 62, 62, 63, 63, 63, 63, 64, 64, 64, 64, 65, 65, 65, 65, 66, 66, 66,
    66, 67, 67, 67, 67, 68, 68, 68, 68, 69, 69, 69, 69, 70, 70, 70, 70, 71, 71, 71, 71, 72, 72, 72,
    72, 73, 73, 73, // 300
    73, 73, 73, 73, 73, 74, 74, 74, 74, 75, 75, 75, 75, 76, 76, 76, 76, 77, 77, 77, 77, 78, 78, 78,
    78, 79, 79, 79, 79, 80, 80, 80, 80, 81, 81, 81, 81, 82, 82, 82, 82, 83, 83, 83, 83, 84, 84, 84,
    84, 85, 85, 85, 85, 86, 86, 86, 86, 87, 87, 87, 87, 88, 88, 88, 88, 89, 89, 89, 89, 90, 90, 90,
    90, 91, 91, 91, 91, 92, 92, 92, 92, 93, 93, 93, 93, 94, 94, 94, 94, 95, 95, 95, 95, 96, 96, 96,
    96, 97, 97, 97, 97, // 400+1
];

pub(super) const fn cycle_to_yo(cycle: u32) -> (u32, u32) {
    let mut year_mod_400 = cycle / 365;
    let mut ordinal0 = cycle % 365;
    let delta = YEAR_DELTAS[year_mod_400 as usize] as u32;
    if ordinal0 < delta {
        year_mod_400 -= 1;
        ordinal0 += 365 - YEAR_DELTAS[year_mod_400 as usize] as u32;
    } else {
        ordinal0 -= delta;
    }
    (year_mod_400, ordinal0 + 1)
}

pub(super) const fn yo_to_cycle(year_mod_400: u32, ordinal: u32) -> u32 {
    year_mod_400 * 365 + YEAR_DELTAS[year_mod_400 as usize] as u32 + ordinal - 1
}

impl YearFlags {
    #[allow(unreachable_pub)] // public as an alias for benchmarks only
    #[doc(hidden)] // for benchmarks only
    #[inline]
    #[must_use]
    pub const fn from_year(year: i32) -> YearFlags {
        let year = year.rem_euclid(400);
        YearFlags::from_year_mod_400(year)
    }

    #[inline]
    pub(super) const fn from_year_mod_400(year: i32) -> YearFlags {
        YEAR_TO_FLAGS[year as usize]
    }

    #[inline]
    pub(super) const fn ndays(&self) -> u32 {
        let YearFlags(flags) = *self;
        366 - (flags >> 3) as u32
    }

    #[inline]
    pub(super) const fn isoweek_delta(&self) -> u32 {
        let YearFlags(flags) = *self;
        let mut delta = (flags & 0b0111) as u32;
        if delta < 3 {
            delta += 7;
        }
        delta
    }

    #[inline]
    pub(super) const fn nisoweeks(&self) -> u32 {
        let YearFlags(flags) = *self;
        52 + ((0b0000_0100_0000_0110 >> flags as usize) & 1)
    }
}

impl fmt::Debug for YearFlags {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let YearFlags(flags) = *self;
        match flags {
            0o15 => "A".fmt(f),
            0o05 => "AG".fmt(f),
            0o14 => "B".fmt(f),
            0o04 => "BA".fmt(f),
            0o13 => "C".fmt(f),
            0o03 => "CB".fmt(f),
            0o12 => "D".fmt(f),
            0o02 => "DC".fmt(f),
            0o11 => "E".fmt(f),
            0o01 => "ED".fmt(f),
            0o10 => "F?".fmt(f),
            0o00 => "FE?".fmt(f), // non-canonical
            0o17 => "F".fmt(f),
            0o07 => "FE".fmt(f),
            0o16 => "G".fmt(f),
            0o06 => "GF".fmt(f),
            _ => write!(f, "YearFlags({})", flags),
        }
    }
}

// OL: (ordinal << 1) | leap year flag
pub(super) const MIN_OL: u32 = 1 << 1;
pub(super) const MAX_OL: u32 = 366 << 1; // `(366 << 1) | 1` would be day 366 in a non-leap year
pub(super) const MAX_MDL: u32 = (12 << 6) | (31 << 1) | 1;

const XX: i8 = -128;
const MDL_TO_OL: &[i8; MAX_MDL as usize + 1] = &[
    XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX,
    XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX,
    XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, // 0
    XX, XX, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // 1
    XX, XX, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
    66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
    66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, XX, XX, XX, XX, XX, // 2
    XX, XX, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74,
    72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74,
    72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, // 3
    XX, XX, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76,
    74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76,
    74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, XX, XX, // 4
    XX, XX, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80,
    78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80,
    78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, // 5
    XX, XX, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82,
    80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82,
    80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, XX, XX, // 6
    XX, XX, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86,
    84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86,
    84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, // 7
    XX, XX, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88,
    86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88,
    86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, // 8
    XX, XX, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90,
    88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90,
    88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, XX, XX, // 9
    XX, XX, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94,
    92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94,
    92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, // 10
    XX, XX, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96,
    94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96,
    94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, XX, XX, // 11
    XX, XX, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98,
    100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100,
    98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98,
    100, // 12
];

const OL_TO_MDL: &[u8; MAX_OL as usize + 1] = &[
    0, 0, // 0
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // 1
    66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
    66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
    66, 66, 66, 66, 66, 66, 66, 66, 66, // 2
    74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72,
    74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72,
    74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, 74, 72, // 3
    76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74,
    76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74,
    76, 74, 76, 74, 76, 74, 76, 74, 76, 74, 76, 74, // 4
    80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78,
    80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78,
    80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, 80, 78, // 5
    82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80,
    82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80,
    82, 80, 82, 80, 82, 80, 82, 80, 82, 80, 82, 80, // 6
    86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84,
    86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84,
    86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, 86, 84, // 7
    88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86,
    88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86,
    88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, 88, 86, // 8
    90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88,
    90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88,
    90, 88, 90, 88, 90, 88, 90, 88, 90, 88, 90, 88, // 9
    94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92,
    94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92,
    94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, 94, 92, // 10
    96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94,
    96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94,
    96, 94, 96, 94, 96, 94, 96, 94, 96, 94, 96, 94, // 11
    100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100,
    98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98,
    100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100, 98, 100,
    98, // 12
];

/// Ordinal (day of year) and year flags: `(ordinal << 4) | flags`.
///
/// The whole bits except for the least 3 bits are referred as `Ol` (ordinal and leap flag),
/// which is an index to the `OL_TO_MDL` lookup table.
///
/// The methods implemented on `Of` always return a valid value.
#[derive(PartialEq, PartialOrd, Copy, Clone)]
pub(super) struct Of(u32);

impl Of {
    #[inline]
    pub(super) const fn new(ordinal: u32, YearFlags(flags): YearFlags) -> Option<Of> {
        let of = Of((ordinal << 4) | flags as u32);
        of.validate()
    }

    pub(super) const fn from_date_impl(date_impl: DateImpl) -> Of {
        // We assume the value in the `DateImpl` is valid.
        Of((date_impl & 0b1_1111_1111_1111) as u32)
    }

    #[inline]
    pub(super) const fn from_mdf(Mdf(mdf): Mdf) -> Option<Of> {
        let mdl = mdf >> 3;
        if mdl > MAX_MDL {
            // Panicking on out-of-bounds indexing would be reasonable, but just return `None`.
            return None;
        }
        // Array is indexed from `[1..=MAX_MDL]`, with a `0` index having a meaningless value.
        let v = MDL_TO_OL[mdl as usize];
        let of = Of(mdf.wrapping_sub((v as i32 as u32 & 0x3ff) << 3));
        of.validate()
    }

    #[inline]
    pub(super) const fn inner(&self) -> u32 {
        self.0
    }

    /// Returns `(ordinal << 1) | leap-year-flag`.
    #[inline]
    const fn ol(&self) -> u32 {
        self.0 >> 3
    }

    #[inline]
    const fn validate(self) -> Option<Of> {
        let ol = self.ol();
        match ol >= MIN_OL && ol <= MAX_OL {
            true => Some(self),
            false => None,
        }
    }

    #[inline]
    pub(super) const fn ordinal(&self) -> u32 {
        self.0 >> 4
    }

    #[inline]
    pub(super) const fn with_ordinal(&self, ordinal: u32) -> Option<Of> {
        let of = Of((ordinal << 4) | (self.0 & 0b1111));
        of.validate()
    }

    #[inline]
    pub(super) const fn flags(&self) -> YearFlags {
        YearFlags((self.0 & 0b1111) as u8)
    }

    #[inline]
    pub(super) const fn weekday(&self) -> Weekday {
        let Of(of) = *self;
        weekday_from_u32_mod7((of >> 4) + (of & 0b111))
    }

    #[inline]
    pub(super) fn isoweekdate_raw(&self) -> (u32, Weekday) {
        // week ordinal = ordinal + delta
        let Of(of) = *self;
        let weekord = (of >> 4).wrapping_add(self.flags().isoweek_delta());
        (weekord / 7, weekday_from_u32_mod7(weekord))
    }

    #[cfg_attr(feature = "cargo-clippy", allow(clippy::wrong_self_convention))]
    #[inline]
    pub(super) const fn to_mdf(&self) -> Mdf {
        Mdf::from_of(*self)
    }

    /// Returns an `Of` with the next day, or `None` if this is the last day of the year.
    #[inline]
    pub(super) const fn succ(&self) -> Option<Of> {
        let of = Of(self.0 + (1 << 4));
        of.validate()
    }

    /// Returns an `Of` with the previous day, or `None` if this is the first day of the year.
    #[inline]
    pub(super) const fn pred(&self) -> Option<Of> {
        match self.ordinal() {
            1 => None,
            _ => Some(Of(self.0 - (1 << 4))),
        }
    }
}

impl fmt::Debug for Of {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Of(of) = *self;
        write!(
            f,
            "Of(({} << 4) | {:#04o} /*{:?}*/)",
            of >> 4,
            of & 0b1111,
            YearFlags((of & 0b1111) as u8)
        )
    }
}

/// Month, day of month and year flags: `(month << 9) | (day << 4) | flags`
///
/// The whole bits except for the least 3 bits are referred as `Mdl`
/// (month, day of month and leap flag),
/// which is an index to the `MDL_TO_OL` lookup table.
///
/// The methods implemented on `Mdf` do not always return a valid value.
/// Dates that can't exist, like February 30, can still be represented.
/// Use `Mdl::valid` to check whether the date is valid.
#[derive(PartialEq, PartialOrd, Copy, Clone)]
pub(super) struct Mdf(u32);

impl Mdf {
    #[inline]
    pub(super) const fn new(month: u32, day: u32, YearFlags(flags): YearFlags) -> Option<Mdf> {
        match month >= 1 && month <= 12 && day >= 1 && day <= 31 {
            true => Some(Mdf((month << 9) | (day << 4) | flags as u32)),
            false => None,
        }
    }

    #[inline]
    pub(super) const fn from_of(Of(of): Of) -> Mdf {
        let ol = of >> 3;
        if ol <= MAX_OL {
            // Array is indexed from `[1..=MAX_OL]`, with a `0` index having a meaningless value.
            Mdf(of + ((OL_TO_MDL[ol as usize] as u32) << 3))
        } else {
            // Panicking here would be reasonable, but we are just going on with a safe value.
            Mdf(0)
        }
    }

    #[cfg(test)]
    pub(super) const fn valid(&self) -> bool {
        let Mdf(mdf) = *self;
        let mdl = mdf >> 3;
        if mdl <= MAX_MDL {
            // Array is indexed from `[1..=MAX_MDL]`, with a `0` index having a meaningless value.
            MDL_TO_OL[mdl as usize] >= 0
        } else {
            // Panicking here would be reasonable, but we are just going on with a safe value.
            false
        }
    }

    #[inline]
    pub(super) const fn month(&self) -> u32 {
        let Mdf(mdf) = *self;
        mdf >> 9
    }

    #[inline]
    pub(super) const fn with_month(&self, month: u32) -> Option<Mdf> {
        if month > 12 {
            return None;
        }

        let Mdf(mdf) = *self;
        Some(Mdf((mdf & 0b1_1111_1111) | (month << 9)))
    }

    #[inline]
    pub(super) const fn day(&self) -> u32 {
        let Mdf(mdf) = *self;
        (mdf >> 4) & 0b1_1111
    }

    #[inline]
    pub(super) const fn with_day(&self, day: u32) -> Option<Mdf> {
        if day > 31 {
            return None;
        }

        let Mdf(mdf) = *self;
        Some(Mdf((mdf & !0b1_1111_0000) | (day << 4)))
    }

    #[inline]
    pub(super) const fn with_flags(&self, YearFlags(flags): YearFlags) -> Mdf {
        let Mdf(mdf) = *self;
        Mdf((mdf & !0b1111) | flags as u32)
    }

    #[cfg_attr(feature = "cargo-clippy", allow(clippy::wrong_self_convention))]
    #[inline]
    pub(super) const fn to_of(&self) -> Option<Of> {
        Of::from_mdf(*self)
    }
}

impl fmt::Debug for Mdf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Mdf(mdf) = *self;
        write!(
            f,
            "Mdf(({} << 9) | ({} << 4) | {:#04o} /*{:?}*/)",
            mdf >> 9,
            (mdf >> 4) & 0b1_1111,
            mdf & 0b1111,
            YearFlags((mdf & 0b1111) as u8)
        )
    }
}

/// Create a `Weekday` from an `u32`, with Monday = 0.
/// Infallible, takes any `n` and applies `% 7`.
#[inline]
const fn weekday_from_u32_mod7(n: u32) -> Weekday {
    match n % 7 {
        0 => Weekday::Mon,
        1 => Weekday::Tue,
        2 => Weekday::Wed,
        3 => Weekday::Thu,
        4 => Weekday::Fri,
        5 => Weekday::Sat,
        _ => Weekday::Sun,
    }
}

#[cfg(test)]
mod tests {
    use std::u32;

    use super::weekday_from_u32_mod7;
    use super::{Mdf, Of};
    use super::{YearFlags, A, AG, B, BA, C, CB, D, DC, E, ED, F, FE, G, GF};
    use crate::Weekday;

    const NONLEAP_FLAGS: [YearFlags; 7] = [A, B, C, D, E, F, G];
    const LEAP_FLAGS: [YearFlags; 7] = [AG, BA, CB, DC, ED, FE, GF];
    const FLAGS: [YearFlags; 14] = [A, B, C, D, E, F, G, AG, BA, CB, DC, ED, FE, GF];

    #[test]
    fn test_year_flags_ndays_from_year() {
        assert_eq!(YearFlags::from_year(2014).ndays(), 365);
        assert_eq!(YearFlags::from_year(2012).ndays(), 366);
        assert_eq!(YearFlags::from_year(2000).ndays(), 366);
        assert_eq!(YearFlags::from_year(1900).ndays(), 365);
        assert_eq!(YearFlags::from_year(1600).ndays(), 366);
        assert_eq!(YearFlags::from_year(1).ndays(), 365);
        assert_eq!(YearFlags::from_year(0).ndays(), 366); // 1 BCE (proleptic Gregorian)
        assert_eq!(YearFlags::from_year(-1).ndays(), 365); // 2 BCE
        assert_eq!(YearFlags::from_year(-4).ndays(), 366); // 5 BCE
        assert_eq!(YearFlags::from_year(-99).ndays(), 365); // 100 BCE
        assert_eq!(YearFlags::from_year(-100).ndays(), 365); // 101 BCE
        assert_eq!(YearFlags::from_year(-399).ndays(), 365); // 400 BCE
        assert_eq!(YearFlags::from_year(-400).ndays(), 366); // 401 BCE
    }

    #[test]
    fn test_year_flags_nisoweeks() {
        assert_eq!(A.nisoweeks(), 52);
        assert_eq!(B.nisoweeks(), 52);
        assert_eq!(C.nisoweeks(), 52);
        assert_eq!(D.nisoweeks(), 53);
        assert_eq!(E.nisoweeks(), 52);
        assert_eq!(F.nisoweeks(), 52);
        assert_eq!(G.nisoweeks(), 52);
        assert_eq!(AG.nisoweeks(), 52);
        assert_eq!(BA.nisoweeks(), 52);
        assert_eq!(CB.nisoweeks(), 52);
        assert_eq!(DC.nisoweeks(), 53);
        assert_eq!(ED.nisoweeks(), 53);
        assert_eq!(FE.nisoweeks(), 52);
        assert_eq!(GF.nisoweeks(), 52);
    }

    #[test]
    fn test_of() {
        fn check(expected: bool, flags: YearFlags, ordinal1: u32, ordinal2: u32) {
            for ordinal in ordinal1..=ordinal2 {
                let of = match Of::new(ordinal, flags) {
                    Some(of) => of,
                    None if !expected => continue,
                    None => panic!("Of::new({}, {:?}) returned None", ordinal, flags),
                };

                assert!(
                    of.validate().is_some() == expected,
                    "ordinal {} = {:?} should be {} for dominical year {:?}",
                    ordinal,
                    of,
                    if expected { "valid" } else { "invalid" },
                    flags
                );
            }
        }

        for &flags in NONLEAP_FLAGS.iter() {
            check(false, flags, 0, 0);
            check(true, flags, 1, 365);
            check(false, flags, 366, 1024);
            check(false, flags, u32::MAX, u32::MAX);
        }

        for &flags in LEAP_FLAGS.iter() {
            check(false, flags, 0, 0);
            check(true, flags, 1, 366);
            check(false, flags, 367, 1024);
            check(false, flags, u32::MAX, u32::MAX);
        }
    }

    #[test]
    fn test_mdf_valid() {
        fn check(expected: bool, flags: YearFlags, month1: u32, day1: u32, month2: u32, day2: u32) {
            for month in month1..=month2 {
                for day in day1..=day2 {
                    let mdf = match Mdf::new(month, day, flags) {
                        Some(mdf) => mdf,
                        None if !expected => continue,
                        None => panic!("Mdf::new({}, {}, {:?}) returned None", month, day, flags),
                    };

                    assert!(
                        mdf.valid() == expected,
                        "month {} day {} = {:?} should be {} for dominical year {:?}",
                        month,
                        day,
                        mdf,
                        if expected { "valid" } else { "invalid" },
                        flags
                    );
                }
            }
        }

        for &flags in NONLEAP_FLAGS.iter() {
            check(false, flags, 0, 0, 0, 1024);
            check(false, flags, 0, 0, 16, 0);
            check(true, flags, 1, 1, 1, 31);
            check(false, flags, 1, 32, 1, 1024);
            check(true, flags, 2, 1, 2, 28);
            check(false, flags, 2, 29, 2, 1024);
            check(true, flags, 3, 1, 3, 31);
            check(false, flags, 3, 32, 3, 1024);
            check(true, flags, 4, 1, 4, 30);
            check(false, flags, 4, 31, 4, 1024);
            check(true, flags, 5, 1, 5, 31);
            check(false, flags, 5, 32, 5, 1024);
            check(true, flags, 6, 1, 6, 30);
            check(false, flags, 6, 31, 6, 1024);
            check(true, flags, 7, 1, 7, 31);
            check(false, flags, 7, 32, 7, 1024);
            check(true, flags, 8, 1, 8, 31);
            check(false, flags, 8, 32, 8, 1024);
            check(true, flags, 9, 1, 9, 30);
            check(false, flags, 9, 31, 9, 1024);
            check(true, flags, 10, 1, 10, 31);
            check(false, flags, 10, 32, 10, 1024);
            check(true, flags, 11, 1, 11, 30);
            check(false, flags, 11, 31, 11, 1024);
            check(true, flags, 12, 1, 12, 31);
            check(false, flags, 12, 32, 12, 1024);
            check(false, flags, 13, 0, 16, 1024);
            check(false, flags, u32::MAX, 0, u32::MAX, 1024);
            check(false, flags, 0, u32::MAX, 16, u32::MAX);
            check(false, flags, u32::MAX, u32::MAX, u32::MAX, u32::MAX);
        }

        for &flags in LEAP_FLAGS.iter() {
            check(false, flags, 0, 0, 0, 1024);
            check(false, flags, 0, 0, 16, 0);
            check(true, flags, 1, 1, 1, 31);
            check(false, flags, 1, 32, 1, 1024);
            check(true, flags, 2, 1, 2, 29);
            check(false, flags, 2, 30, 2, 1024);
            check(true, flags, 3, 1, 3, 31);
            check(false, flags, 3, 32, 3, 1024);
            check(true, flags, 4, 1, 4, 30);
            check(false, flags, 4, 31, 4, 1024);
            check(true, flags, 5, 1, 5, 31);
            check(false, flags, 5, 32, 5, 1024);
            check(true, flags, 6, 1, 6, 30);
            check(false, flags, 6, 31, 6, 1024);
            check(true, flags, 7, 1, 7, 31);
            check(false, flags, 7, 32, 7, 1024);
            check(true, flags, 8, 1, 8, 31);
            check(false, flags, 8, 32, 8, 1024);
            check(true, flags, 9, 1, 9, 30);
            check(false, flags, 9, 31, 9, 1024);
            check(true, flags, 10, 1, 10, 31);
            check(false, flags, 10, 32, 10, 1024);
            check(true, flags, 11, 1, 11, 30);
            check(false, flags, 11, 31, 11, 1024);
            check(true, flags, 12, 1, 12, 31);
            check(false, flags, 12, 32, 12, 1024);
            check(false, flags, 13, 0, 16, 1024);
            check(false, flags, u32::MAX, 0, u32::MAX, 1024);
            check(false, flags, 0, u32::MAX, 16, u32::MAX);
            check(false, flags, u32::MAX, u32::MAX, u32::MAX, u32::MAX);
        }
    }

    #[test]
    fn test_of_fields() {
        for &flags in FLAGS.iter() {
            for ordinal in 1u32..=366 {
                if let Some(of) = Of::new(ordinal, flags) {
                    assert_eq!(of.ordinal(), ordinal);
                }
            }
        }
    }

    #[test]
    fn test_of_with_fields() {
        fn check(flags: YearFlags, ordinal: u32) {
            let of = Of::new(ordinal, flags).unwrap();

            for ordinal in 0u32..=1024 {
                let of = of.with_ordinal(ordinal);
                assert_eq!(of, Of::new(ordinal, flags));
                if let Some(of) = of {
                    assert_eq!(of.ordinal(), ordinal);
                }
            }
        }

        for &flags in NONLEAP_FLAGS.iter() {
            check(flags, 1);
            check(flags, 365);
        }
        for &flags in LEAP_FLAGS.iter() {
            check(flags, 1);
            check(flags, 366);
        }
    }

    #[test]
    fn test_of_weekday() {
        assert_eq!(Of::new(1, A).unwrap().weekday(), Weekday::Sun);
        assert_eq!(Of::new(1, B).unwrap().weekday(), Weekday::Sat);
        assert_eq!(Of::new(1, C).unwrap().weekday(), Weekday::Fri);
        assert_eq!(Of::new(1, D).unwrap().weekday(), Weekday::Thu);
        assert_eq!(Of::new(1, E).unwrap().weekday(), Weekday::Wed);
        assert_eq!(Of::new(1, F).unwrap().weekday(), Weekday::Tue);
        assert_eq!(Of::new(1, G).unwrap().weekday(), Weekday::Mon);
        assert_eq!(Of::new(1, AG).unwrap().weekday(), Weekday::Sun);
        assert_eq!(Of::new(1, BA).unwrap().weekday(), Weekday::Sat);
        assert_eq!(Of::new(1, CB).unwrap().weekday(), Weekday::Fri);
        assert_eq!(Of::new(1, DC).unwrap().weekday(), Weekday::Thu);
        assert_eq!(Of::new(1, ED).unwrap().weekday(), Weekday::Wed);
        assert_eq!(Of::new(1, FE).unwrap().weekday(), Weekday::Tue);
        assert_eq!(Of::new(1, GF).unwrap().weekday(), Weekday::Mon);

        for &flags in FLAGS.iter() {
            let mut prev = Of::new(1, flags).unwrap().weekday();
            for ordinal in 2u32..=flags.ndays() {
                let of = Of::new(ordinal, flags).unwrap();
                let expected = prev.succ();
                assert_eq!(of.weekday(), expected);
                prev = expected;
            }
        }
    }

    #[test]
    fn test_mdf_fields() {
        for &flags in FLAGS.iter() {
            for month in 1u32..=12 {
                for day in 1u32..31 {
                    let mdf = match Mdf::new(month, day, flags) {
                        Some(mdf) => mdf,
                        None => continue,
                    };

                    if mdf.valid() {
                        assert_eq!(mdf.month(), month);
                        assert_eq!(mdf.day(), day);
                    }
                }
            }
        }
    }

    #[test]
    fn test_mdf_with_fields() {
        fn check(flags: YearFlags, month: u32, day: u32) {
            let mdf = Mdf::new(month, day, flags).unwrap();

            for month in 0u32..=16 {
                let mdf = match mdf.with_month(month) {
                    Some(mdf) => mdf,
                    None if month > 12 => continue,
                    None => panic!("failed to create Mdf with month {}", month),
                };

                if mdf.valid() {
                    assert_eq!(mdf.month(), month);
                    assert_eq!(mdf.day(), day);
                }
            }

            for day in 0u32..=1024 {
                let mdf = match mdf.with_day(day) {
                    Some(mdf) => mdf,
                    None if day > 31 => continue,
                    None => panic!("failed to create Mdf with month {}", month),
                };

                if mdf.valid() {
                    assert_eq!(mdf.month(), month);
                    assert_eq!(mdf.day(), day);
                }
            }
        }

        for &flags in NONLEAP_FLAGS.iter() {
            check(flags, 1, 1);
            check(flags, 1, 31);
            check(flags, 2, 1);
            check(flags, 2, 28);
            check(flags, 2, 29);
            check(flags, 12, 31);
        }
        for &flags in LEAP_FLAGS.iter() {
            check(flags, 1, 1);
            check(flags, 1, 31);
            check(flags, 2, 1);
            check(flags, 2, 29);
            check(flags, 2, 30);
            check(flags, 12, 31);
        }
    }

    #[test]
    fn test_of_isoweekdate_raw() {
        for &flags in FLAGS.iter() {
            // January 4 should be in the first week
            let (week, _) = Of::new(4 /* January 4 */, flags).unwrap().isoweekdate_raw();
            assert_eq!(week, 1);
        }
    }

    #[test]
    fn test_of_to_mdf() {
        for i in 0u32..=8192 {
            if let Some(of) = Of(i).validate() {
                assert!(of.to_mdf().valid());
            }
        }
    }

    #[test]
    fn test_mdf_to_of() {
        for i in 0u32..=8192 {
            let mdf = Mdf(i);
            assert_eq!(mdf.valid(), mdf.to_of().is_some());
        }
    }

    #[test]
    fn test_of_to_mdf_to_of() {
        for i in 0u32..=8192 {
            if let Some(of) = Of(i).validate() {
                assert_eq!(of, of.to_mdf().to_of().unwrap());
            }
        }
    }

    #[test]
    fn test_mdf_to_of_to_mdf() {
        for i in 0u32..=8192 {
            let mdf = Mdf(i);
            if mdf.valid() {
                assert_eq!(mdf, mdf.to_of().unwrap().to_mdf());
            }
        }
    }

    #[test]
    fn test_invalid_returns_none() {
        let regular_year = YearFlags::from_year(2023);
        let leap_year = YearFlags::from_year(2024);
        assert!(Of::new(0, regular_year).is_none());
        assert!(Of::new(366, regular_year).is_none());
        assert!(Of::new(366, leap_year).is_some());
        assert!(Of::new(367, regular_year).is_none());

        assert!(Mdf::new(0, 1, regular_year).is_none());
        assert!(Mdf::new(13, 1, regular_year).is_none());
        assert!(Mdf::new(1, 0, regular_year).is_none());
        assert!(Mdf::new(1, 32, regular_year).is_none());
        assert!(Mdf::new(2, 31, regular_year).is_some());

        assert!(Of::from_mdf(Mdf::new(2, 30, regular_year).unwrap()).is_none());
        assert!(Of::from_mdf(Mdf::new(2, 30, leap_year).unwrap()).is_none());
        assert!(Of::from_mdf(Mdf::new(2, 29, regular_year).unwrap()).is_none());
        assert!(Of::from_mdf(Mdf::new(2, 29, leap_year).unwrap()).is_some());
        assert!(Of::from_mdf(Mdf::new(2, 28, regular_year).unwrap()).is_some());

        assert!(Of::new(365, regular_year).unwrap().succ().is_none());
        assert!(Of::new(365, leap_year).unwrap().succ().is_some());
        assert!(Of::new(366, leap_year).unwrap().succ().is_none());

        assert!(Of::new(1, regular_year).unwrap().pred().is_none());
        assert!(Of::new(1, leap_year).unwrap().pred().is_none());
    }

    #[test]
    fn test_weekday_from_u32_mod7() {
        for i in 0..=1000 {
            assert_eq!(weekday_from_u32_mod7(i), Weekday::try_from((i % 7) as u8).unwrap());
        }
        assert_eq!(weekday_from_u32_mod7(u32::MAX), Weekday::Thu);
    }
}
