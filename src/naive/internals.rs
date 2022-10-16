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
#![allow(unreachable_pub)]

use crate::Weekday;
use core::convert::TryFrom;
use core::{fmt, i32};
use num_integer::{div_rem, mod_floor};
use num_traits::FromPrimitive;

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

/// The internal date representation. This also includes the packed `Mdf` value.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct DateImpl(i32); // (year << 13) | of

impl DateImpl {
    pub(super) fn from_parts(year: i32, of: Of) -> Option<DateImpl> {
        if !(MIN_YEAR..=MAX_YEAR).contains(&year) {
            return None;
        }

        let of = i32::try_from(of.0).ok()?;
        Some(DateImpl(year << 13 | of))
    }

    // should this return an Option ?
    pub(super) fn of(&self) -> Of {
        Of((self.0 & 0b1_1111_1111_1111) as u32)
    }

    pub(super) fn year(&self) -> i32 {
        // self.0 & !0b1_1111_1111_1111

        self.0 >> 13
    }

    #[inline]
    pub(super) fn succ_opt(&self) -> Option<DateImpl> {
        let of = self.of();
        let current_year = self.year();
        if of.ordinal() == of.flags().ndays() {
            let next_year = current_year.checked_add(1)?;
            if next_year > MAX_YEAR {
                return None;
            }
            let new_flags = YearFlags::from_year(next_year);
            DateImpl::from_parts(next_year, Of::new(1, new_flags)?)
        } else {
            DateImpl::from_parts(current_year, Of::new(of.ordinal() + 1, of.flags())?)
        }
    }

    #[inline]
    pub(super) fn pred_opt(&self) -> Option<DateImpl> {
        let of = self.of();
        let current_year = self.year();
        if of.ordinal() == 1 {
            let prev_year = current_year.checked_sub(1)?;
            if prev_year < MIN_YEAR {
                return None;
            }
            let new_flags = YearFlags::from_year(prev_year);
            DateImpl::from_parts(prev_year, Of::new(new_flags.ndays(), new_flags)?)
        } else {
            DateImpl::from_parts(current_year, Of::new(of.ordinal() - 1, of.flags())?)
        }
    }

    /// The minimum possible `Date` (January 1, 262145 BCE).
    pub(super) const MIN: DateImpl = DateImpl((MIN_YEAR << 13) | (1 << 4) | 0o07 /*FE*/);
    /// The maximum possible `Date` (December 31, 262143 CE).
    pub(super) const MAX: DateImpl = DateImpl((MAX_YEAR << 13) | (365 << 4) | 0o17 /*F*/);
}

// note that this allows for larger year range than `NaiveDate`.
// this is crucial because we have an edge case for the first and last week supported,
// which year number might not match the calendar year number.#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone)]
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct WeekImpl(i32); // (year << 10) | (week << 4) | flag

impl WeekImpl {
    pub(super) fn from_parts(year: i32, week: u16, flags: YearFlags) -> Option<WeekImpl> {
        let week_part = i32::try_from(week << 4).ok()?;
        let flags_part = i32::from(flags.0);
        Some(WeekImpl((year << 10) | week_part | flags_part))
    }

    pub(super) fn year(&self) -> i32 {
        self.0 >> 10
    }
    pub(super) fn week(&self) -> u32 {
        u32::try_from((self.0 >> 4) & 0x3f).unwrap()
    }
}

pub(super) const MAX_YEAR: i32 = i32::MAX >> 13;
pub(super) const MIN_YEAR: i32 = i32::MIN >> 13;

/// The year flags (aka the dominical letter).
///
/// There are 14 possible classes of year in the Gregorian calendar:
/// common and leap years starting with Monday through Sunday.
/// The `YearFlags` stores this information into 4 bits `abbb`,
/// where `a` is `1` for the common year (simplifies the `Of` validation)
/// and `bbb` is a non-zero `Weekday` (mapping `Mon` to 7) of the last day in the past year
/// (simplifies the day of week calculation from the 1-based ordinal).
#[allow(unreachable_pub)] // public as an alias for benchmarks only
#[derive(PartialEq, Eq, Copy, Clone)]
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

static YEAR_TO_FLAGS: [YearFlags; 400] = [
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

static YEAR_DELTAS: [u8; 401] = [
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

pub(super) fn cycle_to_yo(cycle: u32) -> (u32, u32) {
    let (mut year_mod_400, mut ordinal0) = div_rem(cycle, 365);
    let delta = u32::from(YEAR_DELTAS[year_mod_400 as usize]);
    if ordinal0 < delta {
        year_mod_400 -= 1;
        ordinal0 += 365 - u32::from(YEAR_DELTAS[year_mod_400 as usize]);
    } else {
        ordinal0 -= delta;
    }
    (year_mod_400, ordinal0 + 1)
}

pub(super) fn yo_to_cycle(year_mod_400: u32, ordinal: u32) -> u32 {
    year_mod_400 * 365 + u32::from(YEAR_DELTAS[year_mod_400 as usize]) + ordinal - 1
}

impl YearFlags {
    #[allow(unreachable_pub)] // public as an alias for benchmarks only
    #[doc(hidden)] // for benchmarks only
    #[inline]
    pub fn from_year(year: i32) -> YearFlags {
        let year = mod_floor(year, 400);
        YearFlags::from_year_mod_400(year)
    }

    #[inline]
    pub(super) fn from_year_mod_400(year: i32) -> YearFlags {
        YEAR_TO_FLAGS[year as usize]
    }

    #[inline]
    pub(super) fn ndays(&self) -> u32 {
        let YearFlags(flags) = *self;
        366 - u32::from(flags >> 3)
    }

    #[inline]
    pub(super) fn isoweek_delta(&self) -> u32 {
        let YearFlags(flags) = *self;
        let mut delta = u32::from(flags) & 0b0111;
        if delta < 3 {
            delta += 7;
        }
        delta
    }

    #[inline]
    pub(super) fn nisoweeks(&self) -> u32 {
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

pub(super) const MIN_OL: u32 = 1 << 1;
pub(super) const MAX_OL: u32 = 366 << 1; // larger than the non-leap last day `(365 << 1) | 1`
pub(super) const MAX_MDL: u32 = (12 << 6) | (31 << 1) | 1;

const XX: i8 = -128;
static MDL_TO_OL: [i8; MAX_MDL as usize + 1] = [
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

static OL_TO_MDL: [u8; MAX_OL as usize + 1] = [
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
#[derive(PartialEq, PartialOrd, Copy, Clone)]
pub(super) struct Of(u32);

impl Of {
    // this function should only allow creation of valid Of.
    // otherwise it will return None.
    #[inline]
    pub(super) fn new(ordinal: u32, yf: YearFlags) -> Option<Of> {
        match (1_u32..=yf.ndays()).contains(&ordinal) {
            true => {
                let raw = (ordinal << 4) | u32::from(yf.0);
                if (MIN_OL..=MAX_OL).contains(&(raw >> 3)) {
                    Some(Of(raw))
                } else {
                    None
                }
            }
            false => None,
        }
    }

    #[inline]
    pub(super) fn from_mdf(Mdf(mdf): Mdf) -> Option<Of> {
        let mdl = mdf >> 3;
        let proposed_ol = *MDL_TO_OL.get(mdl as usize)?;
        if proposed_ol < 1 {
            return None;
        }
        Some(Of(mdf.wrapping_sub((i32::from(proposed_ol) as u32 & 0x3ff) << 3)))
    }

    #[inline]
    pub(super) fn ordinal(&self) -> u32 {
        let Of(of) = *self;
        of >> 4
    }

    #[inline]
    pub(super) fn with_ordinal(&self, ordinal: u32) -> Option<Of> {
        Of::new(ordinal, self.flags())
    }

    #[inline]
    pub(super) fn flags(&self) -> YearFlags {
        let Of(of) = *self;
        YearFlags((of & 0b1111) as u8)
    }

    #[inline]
    pub(super) fn weekday(&self) -> Weekday {
        let Of(of) = *self;
        Weekday::from_u32(((of >> 4) + (of & 0b111)) % 7).unwrap()
    }

    #[inline]
    pub(super) fn isoweekdate_raw(&self) -> (u32, Weekday) {
        // week ordinal = ordinal + delta
        let Of(of) = *self;
        let weekord = (of >> 4).wrapping_add(self.flags().isoweek_delta());
        (weekord / 7, Weekday::from_u32(weekord % 7).unwrap())
    }

    #[inline]
    pub(super) fn to_mdf(self) -> Mdf {
        Mdf::from_of(self)
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
#[derive(PartialEq, PartialOrd, Copy, Clone)]
pub(super) struct Mdf(u32);

impl Mdf {
    // this function should only allow creation of valid Mdf.
    // otherwise it will return None.
    #[inline]
    pub(super) fn new(month: u32, day: u32, YearFlags(flags): YearFlags) -> Option<Mdf> {
        if !(1..=12).contains(&month) || !(1..=31).contains(&day) {
            return None;
        }
        let raw = (month << 9) | (day << 4) | u32::from(flags);

        let mdl = raw >> 3;
        match MDL_TO_OL.get(mdl as usize) {
            Some(&v) if v >= 0 => Some(Mdf(raw)),
            Some(_) | None => None,
        }
    }

    #[inline]
    pub(super) fn from_of(Of(of): Of) -> Mdf {
        let ol = of >> 3;
        match OL_TO_MDL.get(ol as usize) {
            Some(&v) => Mdf(of + (u32::from(v) << 3)),
            None => Mdf(0),
        }
    }

    #[inline]
    pub(super) fn month(&self) -> u32 {
        let Mdf(mdf) = *self;
        mdf >> 9
    }

    #[inline]
    pub(super) fn with_month(&self, month: u32) -> Option<Mdf> {
        if month > 12 {
            return None;
        }

        let Mdf(mdf) = *self;
        Some(Mdf((mdf & 0b1_1111_1111) | (month << 9)))
    }

    #[inline]
    pub(super) fn day(&self) -> u32 {
        let Mdf(mdf) = *self;
        (mdf >> 4) & 0b1_1111
    }

    #[inline]
    pub(super) fn with_day(&self, day: u32) -> Option<Mdf> {
        if day > 31 {
            return None;
        }

        let Mdf(mdf) = *self;
        Some(Mdf((mdf & !0b1_1111_0000) | (day << 4)))
    }

    #[inline]
    pub(super) fn with_flags(&self, YearFlags(flags): YearFlags) -> Mdf {
        let Mdf(mdf) = *self;
        Mdf((mdf & !0b1111) | u32::from(flags))
    }

    #[inline]
    pub(super) fn to_of(self) -> Option<Of> {
        Of::from_mdf(self)
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

#[cfg(test)]
mod tests {
    use num_iter::range_inclusive;
    use std::u32;

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
            for ordinal in range_inclusive(ordinal1, ordinal2) {
                match Of::new(ordinal, flags) {
                    Some(of) => assert!(
                        expected,
                        "ordinal {} = {:?} should be {} for dominical year {:?}",
                        ordinal,
                        Some(of),
                        if expected { "valid" } else { "invalid" },
                        flags
                    ),
                    None => assert!(
                        !expected,
                        "ordinal {} = {:?} should be {} for dominical year {:?}",
                        ordinal,
                        None::<Of>,
                        if expected { "valid" } else { "invalid" },
                        flags
                    ),
                };
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
            for month in range_inclusive(month1, month2) {
                for day in range_inclusive(day1, day2) {
                    match Mdf::new(month, day, flags) {
                        Some(mdf) => assert!(
                            expected,
                            "month {} day {} = {:?} should be {} for dominical year {:?}",
                            month,
                            day,
                            Some(mdf),
                            if expected { "valid" } else { "invalid" },
                            flags
                        ),
                        None => assert!(
                            !expected,
                            "month {} day {} = {:?} should be {} for dominical year {:?}",
                            month,
                            day,
                            None::<Mdf>,
                            if expected { "valid" } else { "invalid" },
                            flags
                        ),
                    };
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
            for ordinal in range_inclusive(1u32, 366) {
                match Of::new(ordinal, flags) {
                    Some(of) => {
                        assert_eq!(of.ordinal(), ordinal)
                    }
                    None => {
                        assert_eq!(flags.ndays(), 365);
                        assert_eq!(ordinal, 366);
                    }
                }
            }
        }
    }

    #[test]
    fn test_of_with_fields() {
        fn check(flags: YearFlags, ordinal: u32) {
            let of = Of::new(ordinal, flags).unwrap();

            for ordinal in range_inclusive(0u32, 1024) {
                match of.with_ordinal(ordinal) {
                    Some(of) => {
                        assert_eq!(Of::new(ordinal, flags), Some(of));
                        assert_eq!(of.ordinal(), ordinal);
                    }
                    // this should always succeed so it's a bug if not
                    None if (1..=flags.ndays()).contains(&ordinal) => {
                        panic!("failed to create Of with ordinal {}", ordinal);
                    }
                    None => continue,
                };
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
            for ordinal in range_inclusive(2u32, flags.ndays()) {
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
            for month in range_inclusive(1u32, 12) {
                for day in range_inclusive(1u32, 31) {
                    match Mdf::new(month, day, flags) {
                        Some(mdf) => {
                            assert_eq!(mdf.month(), month);
                            assert_eq!(mdf.day(), day);
                        }
                        None => continue,
                    };
                }
            }
        }
    }

    #[test]
    fn test_mdf_with_fields() {
        fn check(should_succeed: bool, flags: YearFlags, month: u32, day: u32) {
            if let Some(mdf) = Mdf::new(month, day, flags) {
                if !should_succeed {
                    panic!("Mdf invalidly created from {:?} month {} day {}", flags, month, day)
                }
                for month in range_inclusive(0u32, 16) {
                    match mdf.with_month(month) {
                        Some(mdf) => {
                            assert_eq!(mdf.month(), month);
                            assert_eq!(mdf.day(), day);
                        }
                        None if month > 12 => continue,
                        None => panic!("failed to create Mdf with month {}", month),
                    };
                }

                for day in range_inclusive(0u32, 1024) {
                    match mdf.with_day(day) {
                        Some(mdf) => {
                            assert_eq!(mdf.month(), month);
                            assert_eq!(mdf.day(), day);
                        }
                        None if day > 31 => continue,
                        None => panic!("failed to create Mdf with month {}", month),
                    };
                }
            } else if should_succeed {
                panic!("Mdf creation should have succeed but instead failed from: {:?} month {} day {}", flags, month, day);
            }
        }

        for &flags in NONLEAP_FLAGS.iter() {
            check(true, flags, 1, 1);
            check(true, flags, 1, 31);
            check(true, flags, 2, 1);
            check(true, flags, 2, 28);
            check(false, flags, 2, 29);
            check(true, flags, 12, 31);
        }
        for &flags in LEAP_FLAGS.iter() {
            check(true, flags, 1, 1);
            check(true, flags, 1, 31);
            check(true, flags, 2, 1);
            check(true, flags, 2, 29);
            check(false, flags, 2, 30);
            check(true, flags, 12, 31);
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
    fn test_of_to_mdf_roundtrip() {
        for flags in FLAGS.iter() {
            for ordinal in 1..=366 {
                assert_eq!(
                    Of::new(ordinal, *flags).map(Of::to_mdf).and_then(Mdf::to_of),
                    Of::new(ordinal, *flags),
                );
            }
        }
    }

    #[test]
    fn test_mdf_to_of_roundtrip() {
        for flags in FLAGS.iter() {
            for month in 1..=12 {
                for day in 1..=31 {
                    assert_eq!(
                        Mdf::new(month, day, *flags).and_then(Mdf::to_of).map(Of::to_mdf),
                        Mdf::new(month, day, *flags),
                    )
                }
            }
        }
    }
}
