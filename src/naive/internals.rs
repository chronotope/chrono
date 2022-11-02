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
use core::i32;
use num_integer::{div_rem, mod_floor};
use ordinal_flags::Of;
use year_flags::YearTypeFlag;

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

pub(super) const MAX_YEAR: i16 = i16::MAX;
pub(super) const MIN_YEAR: i16 = i16::MIN;

// DateImpl of [u8; 4]
// first two u8 -> represents an i16 of the year
// next two u8 store the ordinal, ordinal reg flag, leap flag and year flags as follows:
// 3rd u8 -> ordinal of 0.255 (interpreted as 1..256)
// 4th u8 -> year flags. values 0..13 is standard flags, values 14..26 is same but we add 256 to the ordinal.

/// The internal date representation. This also includes the packed `Mdf` value.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct DateImpl(i16, Of);

#[cfg(feature = "arbitrary")]
impl arbitrary::Arbitrary<'_> for DateImpl {
    fn arbitrary(u: &mut arbitrary::Unstructured) -> arbitrary::Result<DateImpl> {
        let year = u.int_in_range(MIN_YEAR..=MAX_YEAR)?;
        let flag = YearTypeFlag::from_year(year);
        let ord = u.int_in_range(1..=flag.ndays())?;
        let of = Of::new(ord, flag).ok_or(arbitrary::Error::IncorrectFormat)?;
        Ok(DateImpl::from_parts(year, of))
    }
}

impl DateImpl {
    pub(super) fn from_yo(year: i16, ord: u16) -> Option<DateImpl> {
        let flag = YearTypeFlag::from_year(year);
        let of = Of::new(ord, flag)?;
        Some(DateImpl::from_parts(year, of))
    }

    pub(super) fn from_ymd(year: i16, month: u8, day: u8) -> Option<DateImpl> {
        let flag = YearTypeFlag::from_year(year);
        todo!()
        // let of = Of::new(ord, flag)?;
        // Some(DateImpl::from_parts(year, of))
    }

    pub(super) fn from_num_days_from_ce_opt(days: i32) -> Option<DateImpl> {
        todo!()
        // let days = days + 365; // make December 31, 1 BCE equal to day 0
        // let (year_div_400, cycle) = div_mod_floor(days, 146_097);
        // let (year_mod_400, ordinal) = internals::cycle_to_yo(cycle as u32);
        // let flags = YearTypeFlag::from_year_mod_400(year_mod_400 as i32);
        // NaiveDate::from_parts(year_div_400 * 400 + year_mod_400 as i32, Of::new(ordinal, flags)?)
    }

    pub(super) fn from_isoywd_opt(year: i16, week: u16, weekday: Weekday) -> Option<DateImpl> {
        todo!()
        // let flags = YearFlags::from_year(year);
        // let nweeks = flags.nisoweeks();
        // if 1 <= week && week <= nweeks {
        //     // ordinal = week ordinal - delta
        //     let weekord = week * 7 + weekday as u32;
        //     let delta = flags.isoweek_delta();
        //     if weekord <= delta {
        //         // ordinal < 1, previous year
        //         let prevflags = YearFlags::from_year(year - 1);
        //         NaiveDate::from_parts(
        //             year - 1,
        //             Of::new(weekord + prevflags.ndays() - delta, prevflags)?,
        //         )
        //     } else {
        //         let ordinal = weekord - delta;
        //         let ndays = flags.ndays();
        //         if ordinal <= ndays {
        //             // this year
        //             NaiveDate::from_parts(year, Of::new(ordinal, flags)?)
        //         } else {
        //             // ordinal > ndays, next year
        //             let nextflags = YearFlags::from_year(year + 1);
        //             NaiveDate::from_parts(year + 1, Of::new(ordinal - ndays, nextflags)?)
        //         }
        //     }
        // } else {
        //     None
        // }
    }

    pub(super) fn from_weekday_of_month_opt(
        year: i16,
        month: u16,
        weekday: Weekday,
        n: u8,
    ) -> Option<DateImpl> {
        todo!()
        // if n == 0 {
        //     return None;
        // }
        // let first = NaiveDate::from_ymd_opt(year, month, 1)?.weekday();
        // let first_to_dow = (7 + weekday.number_from_monday() - first.number_from_monday()) % 7;
        // let day = (u32::from(n) - 1) * 7 + first_to_dow + 1;
        // NaiveDate::from_ymd_opt(year, month, day)
    }

    pub(super) fn diff_months(self, months: i32) -> Option<Self> {
        let (years, left) = ((months / 12), (months % 12));

        let years = i16::try_from(years).ok()?;
        let left = i16::try_from(left).ok()?;

        // Determine new year (without taking months into account for now

        let year = if (years > 0 && years > (MAX_YEAR - self.year()))
            || (years < 0 && years < (MIN_YEAR - self.year()))
        {
            return None;
        } else {
            (self.year()) + years
        };

        // Determine new month

        let month = i16::from(self.month()) + left;
        let (year, month) = if month <= 0 {
            if year == (MIN_YEAR) {
                return None;
            }

            (year - 1, month + 12)
        } else if month > 12 {
            if year == (MAX_YEAR) {
                return None;
            }

            (year + 1, month - 12)
        } else {
            (year, month)
        };

        let month = u8::try_from(month).ok()?;

        // Clamp original day in case new month is shorter

        let flags = YearTypeFlag::from_year(year);
        let feb_days = if flags.is_leap() { 29 } else { 28 };
        let days = [31, feb_days, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
        let day = Ord::min(self.day_of_month(), days[(month - 1) as usize]);

        DateImpl::from_ymd(year, month, day)
    }

    pub(super) fn from_parts(year: i16, of: Of) -> DateImpl {
        DateImpl(year, of)
    }

    pub(super) fn of(&self) -> Of {
        self.1
    }
    pub(super) fn weekday(&self) -> Weekday {
        self.of().weekday()
    }
    pub(super) fn ordinal(&self) -> u16 {
        self.of().ordinal()
    }

    pub(super) fn month(&self) -> u8 {
        self.of().month()
    }

    pub(super) fn day_of_month(&self) -> u8 {
        self.of().day_of_month()
    }

    pub(super) fn year(&self) -> i16 {
        self.0
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
            let new_flags = YearTypeFlag::from_year(next_year);
            Some(DateImpl::from_parts(next_year, Of::new(1, new_flags)?))
        } else {
            Some(DateImpl::from_parts(current_year, Of::new(of.ordinal() + 1, of.flags())?))
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
            let new_flags = YearTypeFlag::from_year(prev_year);
            Some(DateImpl::from_parts(prev_year, Of::new(new_flags.ndays(), new_flags)?))
        } else {
            Some(DateImpl::from_parts(current_year, Of::new(of.ordinal() - 1, of.flags())?))
        }
    }

    /// The minimum possible `Date` (January 1, 262145 BCE).
    pub(super) const MIN: DateImpl = DateImpl(i16::MIN, Of::MIN_YEAR_MIN);
    /// The maximum possible `Date` (December 31, 262143 CE).
    pub(super) const MAX: DateImpl = DateImpl(i16::MAX, Of::MAX_YEAR_MAX);
}

// note that this allows for larger year range than `NaiveDate`.
// this is crucial because we have an edge case for the first and last week supported,
// which year number might not match the calendar year number.#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone)]
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct WeekImpl(DateImpl); // (year << 10) | (week << 4) | flag

impl WeekImpl {
    pub(super) fn from_parts(year: i16, week: u16, flags: YearTypeFlag) -> Option<WeekImpl> {
        todo!()
        // let week_part = i32::try_from(week << 4).ok()?;
        // let flags_part = i32::from(flags.0);
        // Some(WeekImpl((year << 10) | week_part | flags_part))
    }

    pub(super) fn year(&self) -> i16 {
        todo!()
        // self.0 >> 10
    }
    pub(super) fn week(&self) -> u8 {
        todo!()
        // u32::try_from((self.0 >> 4) & 0x3f).unwrap()
    }

    /// Returns the corresponding `IsoWeek` from the year and the `Of` internal value.
    //
    // internal use only. we don't expose the public constructor for `IsoWeek` for now,
    // because the year range for the week date and the calendar date do not match and
    // it is confusing to have a date that is out of range in one and not in another.
    // currently we sidestep this issue by making `IsoWeek` fully dependent of `Datelike`.
    pub(super) fn iso_week_from_yof(year: i16, ordinal: u16) -> Option<WeekImpl> {
        todo!()
        // let (rawweek, _) = of.isoweekdate_raw();
        // let (year, week) = if rawweek < 1 {
        //     // previous year
        //     let prevlastweek = YearTypeFlag::from_year(year - 1).nisoweeks();
        //     (year - 1, prevlastweek)
        // } else {
        //     let lastweek = of.flags().nisoweeks();
        //     if rawweek > lastweek {
        //         // next year
        //         (year + 1, 1)
        //     } else {
        //         (year, rawweek)
        //     }
        // };
        // Some(WeekImpl::from_parts(year, week as u16, of.flags())?)
    }
}

pub mod year_flags {
    use super::*;
    pub use YearTypeFlag::*;

    /// The year flags (aka the dominical letter).
    ///
    /// There are 14 possible classes of year in the Gregorian calendar:
    /// common and leap years starting with Monday through Sunday.
    /// The `YearFlags` stores this information into 4 bits `abbb`,
    /// where `a` is `1` for the common year (simplifies the `Of` validation)
    /// and `bbb` is a non-zero `Weekday` (mapping `Mon` to 7) of the last day in the past year
    /// (simplifies the day of week calculation from the 1-based ordinal).
    #[allow(unreachable_pub)]
    // public as an alias for benchmarks only
    // #[derive(PartialEq, Eq, Copy, Clone)]
    // pub struct YearFlags(u8);
    #[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
    #[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
    pub enum YearTypeFlag {
        A,
        AG,
        B,
        BA,
        C,
        CB,
        D,
        DC,
        E,
        ED,
        F,
        FE,
        G,
        GF,
    }

    // pub(super) const A: YearFlags = YearFlags(0o15);
    // pub(super) const AG: YearFlags = YearFlags(0o05);
    // pub(super) const B: YearFlags = YearFlags(0o14);
    // pub(super) const BA: YearFlags = YearFlags(0o04);
    // pub(super) const C: YearFlags = YearFlags(0o13);
    // pub(super) const CB: YearFlags = YearFlags(0o03);
    // pub(super) const D: YearFlags = YearFlags(0o12);
    // pub(super) const DC: YearFlags = YearFlags(0o02);
    // pub(super) const E: YearFlags = YearFlags(0o11);
    // pub(super) const ED: YearFlags = YearFlags(0o01);
    // pub(super) const F: YearFlags = YearFlags(0o17);
    // pub(super) const FE: YearFlags = YearFlags(0o07);
    // pub(super) const G: YearFlags = YearFlags(0o16);
    // pub(super) const GF: YearFlags = YearFlags(0o06);

    pub(super) static YEAR_TO_FLAGS: [YearTypeFlag; 400] = [
        BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C,
        BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C,
        BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C,
        BA, G, F, E, DC, B, A, G, FE, D, C, B, AG, F, E, D, // 100
        C, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E,
        DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E,
        DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E,
        DC, B, A, G, FE, D, C, B, AG, F, E, D, CB, A, G, F, // 200
        E, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G,
        FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G,
        FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G,
        FE, D, C, B, AG, F, E, D, CB, A, G, F, ED, C, B, A, // 300
        G, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B,
        AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B,
        AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, BA, G, F, E, DC, B, A, G, FE, D, C, B,
        AG, F, E, D, CB, A, G, F, ED, C, B, A, GF, E, D, C, // 400
    ];

    static YEAR_DELTAS: [u8; 401] = [
        0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8,
        8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14,
        14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19,
        20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 23, 23, 23, 23, 24, 24, 24, 24, 25, 25,
        25, // 100
        25, 25, 25, 25, 25, 26, 26, 26, 26, 27, 27, 27, 27, 28, 28, 28, 28, 29, 29, 29, 29, 30, 30,
        30, 30, 31, 31, 31, 31, 32, 32, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 35, 35, 36,
        36, 36, 36, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 39, 40, 40, 40, 40, 41, 41, 41, 41,
        42, 42, 42, 42, 43, 43, 43, 43, 44, 44, 44, 44, 45, 45, 45, 45, 46, 46, 46, 46, 47, 47, 47,
        47, 48, 48, 48, 48, 49, 49, 49, // 200
        49, 49, 49, 49, 49, 50, 50, 50, 50, 51, 51, 51, 51, 52, 52, 52, 52, 53, 53, 53, 53, 54, 54,
        54, 54, 55, 55, 55, 55, 56, 56, 56, 56, 57, 57, 57, 57, 58, 58, 58, 58, 59, 59, 59, 59, 60,
        60, 60, 60, 61, 61, 61, 61, 62, 62, 62, 62, 63, 63, 63, 63, 64, 64, 64, 64, 65, 65, 65, 65,
        66, 66, 66, 66, 67, 67, 67, 67, 68, 68, 68, 68, 69, 69, 69, 69, 70, 70, 70, 70, 71, 71, 71,
        71, 72, 72, 72, 72, 73, 73, 73, // 300
        73, 73, 73, 73, 73, 74, 74, 74, 74, 75, 75, 75, 75, 76, 76, 76, 76, 77, 77, 77, 77, 78, 78,
        78, 78, 79, 79, 79, 79, 80, 80, 80, 80, 81, 81, 81, 81, 82, 82, 82, 82, 83, 83, 83, 83, 84,
        84, 84, 84, 85, 85, 85, 85, 86, 86, 86, 86, 87, 87, 87, 87, 88, 88, 88, 88, 89, 89, 89, 89,
        90, 90, 90, 90, 91, 91, 91, 91, 92, 92, 92, 92, 93, 93, 93, 93, 94, 94, 94, 94, 95, 95, 95,
        95, 96, 96, 96, 96, 97, 97, 97, 97, // 400+1
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

    impl YearTypeFlag {
        pub fn ndays(&self) -> u16 {
            match self.is_leap() {
                true => 366,
                false => 365,
            }
        }

        pub fn is_leap(&self) -> bool {
            match self {
                YearTypeFlag::A => false,
                YearTypeFlag::AG => true,
                YearTypeFlag::B => false,
                YearTypeFlag::BA => true,
                YearTypeFlag::C => false,
                YearTypeFlag::CB => true,
                YearTypeFlag::D => false,
                YearTypeFlag::DC => true,
                YearTypeFlag::E => false,
                YearTypeFlag::ED => true,
                YearTypeFlag::F => false,
                YearTypeFlag::FE => true,
                YearTypeFlag::G => false,
                YearTypeFlag::GF => true,
            }
        }

        #[allow(unreachable_pub)] // public as an alias for benchmarks only
        #[doc(hidden)] // for benchmarks only
        #[inline]
        pub fn from_year(year: i16) -> YearTypeFlag {
            let year = mod_floor(year, 400);
            YearTypeFlag::from_year_mod_400(year)
        }

        #[inline]
        fn from_year_mod_400(year_mod_400: i16) -> YearTypeFlag {
            YEAR_TO_FLAGS[year_mod_400 as usize]
        }

        #[inline]
        pub(super) fn isoweek_delta(&self) -> u32 {
            todo!()
            // let YearTypeFlag(flags) = *self;
            // let mut delta = u32::from(flags) & 0b0111;
            // if delta < 3 {
            //     delta += 7;
            // }
            // delta
        }

        #[inline]
        pub(super) fn nisoweeks(&self) -> u32 {
            todo!()

            // let YearFlags(flags) = *self;
            // 52 + ((0b0000_0100_0000_0110 >> flags as usize) & 1)
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

mod ordinal_flags {
    use super::*;
    use core::num::NonZeroU16;
    use core::num::NonZeroU8;

    // this could be extended to store some extra flags for year as well.
    #[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
    #[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
    enum OrdinalFlagAndYearFlag {
        A0,
        AG0,
        B0,
        BA0,
        C0,
        CB0,
        D0,
        DC0,
        E0,
        ED0,
        F0,
        FE0,
        G0,
        GF0,
        A1,
        AG1,
        B1,
        BA1,
        C1,
        CB1,
        D1,
        DC1,
        E1,
        ED1,
        F1,
        FE1,
        G1,
        GF1,
    }

    impl YearTypeFlag {
        fn with_ordinal_second_reigster(&self, second_register: bool) -> OrdinalFlagAndYearFlag {
            match self {
                YearTypeFlag::A => {
                    if second_register {
                        OrdinalFlagAndYearFlag::A1
                    } else {
                        OrdinalFlagAndYearFlag::A0
                    }
                }
                YearTypeFlag::AG => {
                    if second_register {
                        OrdinalFlagAndYearFlag::AG1
                    } else {
                        OrdinalFlagAndYearFlag::AG0
                    }
                }
                YearTypeFlag::B => {
                    if second_register {
                        OrdinalFlagAndYearFlag::B1
                    } else {
                        OrdinalFlagAndYearFlag::B0
                    }
                }
                YearTypeFlag::BA => {
                    if second_register {
                        OrdinalFlagAndYearFlag::BA1
                    } else {
                        OrdinalFlagAndYearFlag::BA0
                    }
                }
                YearTypeFlag::C => {
                    if second_register {
                        OrdinalFlagAndYearFlag::C1
                    } else {
                        OrdinalFlagAndYearFlag::C0
                    }
                }
                YearTypeFlag::CB => {
                    if second_register {
                        OrdinalFlagAndYearFlag::CB1
                    } else {
                        OrdinalFlagAndYearFlag::CB0
                    }
                }
                YearTypeFlag::D => {
                    if second_register {
                        OrdinalFlagAndYearFlag::D1
                    } else {
                        OrdinalFlagAndYearFlag::D0
                    }
                }
                YearTypeFlag::DC => {
                    if second_register {
                        OrdinalFlagAndYearFlag::DC1
                    } else {
                        OrdinalFlagAndYearFlag::DC0
                    }
                }
                YearTypeFlag::E => {
                    if second_register {
                        OrdinalFlagAndYearFlag::E1
                    } else {
                        OrdinalFlagAndYearFlag::E0
                    }
                }
                YearTypeFlag::ED => {
                    if second_register {
                        OrdinalFlagAndYearFlag::ED1
                    } else {
                        OrdinalFlagAndYearFlag::ED0
                    }
                }
                YearTypeFlag::F => {
                    if second_register {
                        OrdinalFlagAndYearFlag::F1
                    } else {
                        OrdinalFlagAndYearFlag::F0
                    }
                }
                YearTypeFlag::FE => {
                    if second_register {
                        OrdinalFlagAndYearFlag::FE1
                    } else {
                        OrdinalFlagAndYearFlag::FE0
                    }
                }
                YearTypeFlag::G => {
                    if second_register {
                        OrdinalFlagAndYearFlag::G1
                    } else {
                        OrdinalFlagAndYearFlag::G0
                    }
                }
                YearTypeFlag::GF => {
                    if second_register {
                        OrdinalFlagAndYearFlag::GF1
                    } else {
                        OrdinalFlagAndYearFlag::GF0
                    }
                }
            }
        }
    }

    impl OrdinalFlagAndYearFlag {
        fn ordinal_second_register(&self) -> bool {
            match self {
                OrdinalFlagAndYearFlag::A0
                | OrdinalFlagAndYearFlag::AG0
                | OrdinalFlagAndYearFlag::B0
                | OrdinalFlagAndYearFlag::BA0
                | OrdinalFlagAndYearFlag::C0
                | OrdinalFlagAndYearFlag::CB0
                | OrdinalFlagAndYearFlag::D0
                | OrdinalFlagAndYearFlag::DC0
                | OrdinalFlagAndYearFlag::E0
                | OrdinalFlagAndYearFlag::ED0
                | OrdinalFlagAndYearFlag::F0
                | OrdinalFlagAndYearFlag::FE0
                | OrdinalFlagAndYearFlag::G0
                | OrdinalFlagAndYearFlag::GF0 => false,
                OrdinalFlagAndYearFlag::A1
                | OrdinalFlagAndYearFlag::AG1
                | OrdinalFlagAndYearFlag::B1
                | OrdinalFlagAndYearFlag::BA1
                | OrdinalFlagAndYearFlag::C1
                | OrdinalFlagAndYearFlag::CB1
                | OrdinalFlagAndYearFlag::D1
                | OrdinalFlagAndYearFlag::DC1
                | OrdinalFlagAndYearFlag::E1
                | OrdinalFlagAndYearFlag::ED1
                | OrdinalFlagAndYearFlag::F1
                | OrdinalFlagAndYearFlag::FE1
                | OrdinalFlagAndYearFlag::G1
                | OrdinalFlagAndYearFlag::GF1 => true,
            }
        }
        fn internal(&self) -> YearTypeFlag {
            match self {
                OrdinalFlagAndYearFlag::A0 => YearTypeFlag::A,
                OrdinalFlagAndYearFlag::AG0 => YearTypeFlag::AG,
                OrdinalFlagAndYearFlag::B0 => YearTypeFlag::B,
                OrdinalFlagAndYearFlag::BA0 => YearTypeFlag::BA,
                OrdinalFlagAndYearFlag::C0 => YearTypeFlag::C,
                OrdinalFlagAndYearFlag::CB0 => YearTypeFlag::CB,
                OrdinalFlagAndYearFlag::D0 => YearTypeFlag::D,
                OrdinalFlagAndYearFlag::DC0 => YearTypeFlag::DC,
                OrdinalFlagAndYearFlag::E0 => YearTypeFlag::E,
                OrdinalFlagAndYearFlag::ED0 => YearTypeFlag::ED,
                OrdinalFlagAndYearFlag::F0 => YearTypeFlag::F,
                OrdinalFlagAndYearFlag::FE0 => YearTypeFlag::FE,
                OrdinalFlagAndYearFlag::G0 => YearTypeFlag::G,
                OrdinalFlagAndYearFlag::GF0 => YearTypeFlag::GF,
                OrdinalFlagAndYearFlag::A1 => YearTypeFlag::A,
                OrdinalFlagAndYearFlag::AG1 => YearTypeFlag::AG,
                OrdinalFlagAndYearFlag::B1 => YearTypeFlag::B,
                OrdinalFlagAndYearFlag::BA1 => YearTypeFlag::BA,
                OrdinalFlagAndYearFlag::C1 => YearTypeFlag::C,
                OrdinalFlagAndYearFlag::CB1 => YearTypeFlag::CB,
                OrdinalFlagAndYearFlag::D1 => YearTypeFlag::D,
                OrdinalFlagAndYearFlag::DC1 => YearTypeFlag::DC,
                OrdinalFlagAndYearFlag::E1 => YearTypeFlag::E,
                OrdinalFlagAndYearFlag::ED1 => YearTypeFlag::ED,
                OrdinalFlagAndYearFlag::F1 => YearTypeFlag::F,
                OrdinalFlagAndYearFlag::FE1 => YearTypeFlag::FE,
                OrdinalFlagAndYearFlag::G1 => YearTypeFlag::G,
                OrdinalFlagAndYearFlag::GF1 => YearTypeFlag::GF,
            }
        }
    }

    #[rustfmt::skip]
    const LEAP_ORDINAL_TO_MONTH: [u8; 366] = [
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // Jan
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,       // Feb
        3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, // Mar
        4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,    // Apr
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, // May
        6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,    // Jun
        7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, // Jul
        8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, // Aug
        9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,    // Sep
       10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10, // Oct
       11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,    // Nov
       12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12, // Dec
    ];

    #[rustfmt::skip]
    const LEAP_ORDINAL_TO_DAY: [u8; 366] = [
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Jan
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,       // Feb
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Mar
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,    // Apr
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // May
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,    // Jun
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Jul
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Aug
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,    // Sep
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Oct
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,    // Nov
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Dec
    ];

    #[rustfmt::skip]
    const ORDINAL_TO_MONTH: [u8; 365] = [
         1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // Jan
         2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,          // Feb
         3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, // Mar
         4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,    // Apr
         5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, // May
         6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,    // Jun
         7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, // Jul
         8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, // Aug
         9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,    // Sep
        10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10, // Oct
        11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,    // Nov
        12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12, // Dec
    ];

    #[rustfmt::skip]
    const ORDINAL_TO_DAY: [u8; 365] = [
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Jan
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,          // Feb
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Mar
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,    // Apr
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // May
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,    // Jun
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Jul
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Aug
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,    // Sep
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Oct
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,    // Nov
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31, // Dec
    ];

    /// Ordinal (day of year) and year flags: `(ordinal << 4) | flags`.
    ///
    /// The whole bits except for the least 3 bits are referred as `Ol` (ordinal and leap flag),
    /// which is an index to the `OL_TO_MDL` lookup table.
    #[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
    #[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
    pub(super) struct Of(NonZeroU8, OrdinalFlagAndYearFlag);

    impl Of {
        pub(super) const MIN_YEAR_MIN: Of =
            Of(unsafe { NonZeroU8::new_unchecked(1) }, OrdinalFlagAndYearFlag::A0);
        pub(super) const MAX_YEAR_MAX: Of =
            Of(unsafe { NonZeroU8::new_unchecked(365) }, OrdinalFlagAndYearFlag::A0);

        // this function should only allow creation of valid Of.
        // otherwise it will return None.
        #[inline]
        pub(super) fn new(ordinal: u16, yf: YearTypeFlag) -> Option<Of> {
            match (1_u16..=yf.ndays()).contains(&ordinal) {
                true if ordinal > 255 => Some(Of(
                    NonZeroU8::new((ordinal - 255) as u8)?,
                    yf.with_ordinal_second_reigster(true),
                )),
                true => {
                    Some(Of(NonZeroU8::new(ordinal as u8)?, yf.with_ordinal_second_reigster(false)))
                }
                false => None,
            }
        }

        pub(super) fn from_ordinal_and_year(ordinal: u16, year: i16) -> Option<Of> {
            let year_type = YearTypeFlag::from_year(year);
            Of::new(ordinal, year_type)
        }

        pub(super) fn month(&self) -> u8 {
            if self.1.internal().is_leap() {
                LEAP_ORDINAL_TO_MONTH[usize::from(self.ordinal())]
            } else {
                ORDINAL_TO_MONTH[usize::from(self.ordinal())]
            }
        }

        pub(super) fn day_of_month(&self) -> u8 {
            if self.1.internal().is_leap() {
                LEAP_ORDINAL_TO_DAY[usize::from(self.ordinal())]
            } else {
                ORDINAL_TO_DAY[usize::from(self.ordinal())]
            }
        }

        #[inline]
        pub(super) fn ordinal(&self) -> u16 {
            if self.1.ordinal_second_register() {
                u16::from(self.0.get()) + 255
            } else {
                self.0.get().into()
            }
        }

        #[inline]
        pub(super) fn with_ordinal(&self, ordinal: u16) -> Option<Of> {
            Of::new(ordinal, self.flags())
        }

        #[inline]
        pub(super) fn flags(&self) -> YearTypeFlag {
            self.1.internal()
        }

        #[inline]
        pub(super) fn weekday(&self) -> Weekday {
            todo!()
            // let Of(of) = *self;
            // Weekday::from_u32(((of >> 4) + (of & 0b111)) % 7).unwrap()
        }

        #[inline]
        pub(super) fn isoweekdate_raw(&self) -> (u32, Weekday) {
            todo!()
            // week ordinal = ordinal + delta
            // let Of(of) = *self;
            // let weekord = (of >> 4).wrapping_add(self.flags().isoweek_delta());
            // (weekord / 7, Weekday::from_u32(weekord % 7).unwrap())
        }
    }
}

#[cfg(test)]
mod tests {
    use num_iter::range_inclusive;

    use super::year_flags::{YearTypeFlag, A, AG, B, BA, C, CB, D, DC, E, ED, F, FE, G, GF};
    use super::Of;
    use crate::Weekday;

    const NONLEAP_FLAGS: [YearTypeFlag; 7] = [A, B, C, D, E, F, G];
    const LEAP_FLAGS: [YearTypeFlag; 7] = [AG, BA, CB, DC, ED, FE, GF];
    const FLAGS: [YearTypeFlag; 14] = [A, B, C, D, E, F, G, AG, BA, CB, DC, ED, FE, GF];

    #[test]
    fn test_year_flags_ndays_from_year() {
        assert_eq!(YearTypeFlag::from_year(2014).ndays(), 365);
        assert_eq!(YearTypeFlag::from_year(2012).ndays(), 366);
        assert_eq!(YearTypeFlag::from_year(2000).ndays(), 366);
        assert_eq!(YearTypeFlag::from_year(1900).ndays(), 365);
        assert_eq!(YearTypeFlag::from_year(1600).ndays(), 366);
        assert_eq!(YearTypeFlag::from_year(1).ndays(), 365);
        assert_eq!(YearTypeFlag::from_year(0).ndays(), 366); // 1 BCE (proleptic Gregorian)
        assert_eq!(YearTypeFlag::from_year(-1).ndays(), 365); // 2 BCE
        assert_eq!(YearTypeFlag::from_year(-4).ndays(), 366); // 5 BCE
        assert_eq!(YearTypeFlag::from_year(-99).ndays(), 365); // 100 BCE
        assert_eq!(YearTypeFlag::from_year(-100).ndays(), 365); // 101 BCE
        assert_eq!(YearTypeFlag::from_year(-399).ndays(), 365); // 400 BCE
        assert_eq!(YearTypeFlag::from_year(-400).ndays(), 366); // 401 BCE
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
        fn check(expected: bool, flags: YearTypeFlag, ordinal1: u16, ordinal2: u16) {
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
            check(false, flags, u16::MAX, u16::MAX);
        }

        for &flags in LEAP_FLAGS.iter() {
            check(false, flags, 0, 0);
            check(true, flags, 1, 366);
            check(false, flags, 367, 1024);
            check(false, flags, u16::MAX, u16::MAX);
        }
    }

    #[test]
    fn test_of_fields() {
        for &flags in FLAGS.iter() {
            for ordinal in range_inclusive(1u16, 366) {
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
        fn check(flags: YearTypeFlag, ordinal: u16) {
            let of = Of::new(ordinal, flags).unwrap();

            for ordinal in range_inclusive(0u16, 1024) {
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
        assert_eq!(Of::new(1, A).weekday(), Weekday::Sun);
        assert_eq!(Of::new(1, B).weekday(), Weekday::Sat);
        assert_eq!(Of::new(1, C).weekday(), Weekday::Fri);
        assert_eq!(Of::new(1, D).weekday(), Weekday::Thu);
        assert_eq!(Of::new(1, E).weekday(), Weekday::Wed);
        assert_eq!(Of::new(1, F).weekday(), Weekday::Tue);
        assert_eq!(Of::new(1, G).weekday(), Weekday::Mon);
        assert_eq!(Of::new(1, AG).weekday(), Weekday::Sun);
        assert_eq!(Of::new(1, BA).weekday(), Weekday::Sat);
        assert_eq!(Of::new(1, CB).weekday(), Weekday::Fri);
        assert_eq!(Of::new(1, DC).weekday(), Weekday::Thu);
        assert_eq!(Of::new(1, ED).weekday(), Weekday::Wed);
        assert_eq!(Of::new(1, FE).weekday(), Weekday::Tue);
        assert_eq!(Of::new(1, GF).weekday(), Weekday::Mon);

        for &flags in FLAGS.iter() {
            let mut prev = Of::new(1, flags).unwrap().weekday();
            for ordinal in range_inclusive(2u16, flags.ndays()) {
                let of = Of::new(ordinal, flags).unwrap();
                let expected = prev.succ();
                assert_eq!(of.weekday(), expected);
                prev = expected;
            }
        }
    }

    #[test]
    fn test_of_isoweekdate_raw() {
        for &flags in FLAGS.iter() {
            // January 4 should be in the first week
            let (week, _) = Of::new(4 /* January 4 */, flags).isoweekdate_raw();
            assert_eq!(week, 1);
        }
    }
}
