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
#![allow(dead_code)]

use core::convert::TryFrom;
use core::hash::Hash;
use core::i32;
use num_integer::div_mod_floor;
use num_integer::{div_rem, mod_floor};
use ordinal_flags::Of;
use year_flags::{cycle_to_yo, yo_to_cycle, YearTypeFlag};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use crate::{Month, Weekday};
use core::num::{NonZeroU16, NonZeroU8};

pub(super) const MAX_YEAR: i16 = i16::MAX;
pub(super) const MIN_YEAR: i16 = i16::MIN;

const DAYS_IN_CYCLE: i32 = 146_097;

// useful in const fns
macro_rules! try_opt {
    ($e:expr) => {
        match $e {
            Some(v) => v,
            None => return None,
        }
    };
}

macro_rules! try_from_i32_to_i16 {
    ($e:expr) => {
        if $e >= i16::MIN as i32 && $e <= i16::MAX as i32 {
            $e as i16
        } else {
            return None;
        }
    };
}

macro_rules! try_from_u32_to_u16 {
    ($e:expr) => {
        if $e <= u16::MAX as u32 {
            $e as u16
        } else {
            return None;
        }
    };
}

macro_rules! try_from_i64_to_i32 {
    ($e:expr) => {
        if $e >= i32::MIN as i64 && $e <= i32::MAX as i64 {
            $e as i32
        } else {
            return None;
        }
    };
}

macro_rules! try_from_u32_to_i32 {
    ($e:expr) => {
        if $e <= i32::MAX as u32 {
            $e as i32
        } else {
            return None;
        }
    };
}

// forces the cosnt validation
#[cfg(feature = "const-validation")]
macro_rules! ymd {
    ($y:expr, $m:expr, $d:expr) => {{
        const _: DateImpl = DateImpl::from_ymd_validated($y, $m, $d);

        DateImpl::from_ymd_validated($y, $m, $d)
    }};
}

// forces the cosnt validation
#[cfg(feature = "const-validation")]
macro_rules! yo {
    ($y:expr, $o:expr) => {{
        const _: DateImpl = DateImpl::from_yo_validated($y, $m, $d);

        DateImpl::from_yo_validated($y, $m, $d)
    }};
}

// DateImpl of [u8; 4]
// first two u8 -> represents an i16 of the year
// next two u8 store the ordinal, ordinal reg flag, leap flag and year flags as follows:
// 3rd u8 -> ordinal of 0.255 (interpreted as 1..256)
// 4th u8 -> year flags. values 0..13 is standard flags, values 14..26 is same but we add 256 to the ordinal.

/// The internal date representation. This also includes the packed `Mdf` value.
#[derive(PartialOrd, Ord, Copy, Clone, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct DateImpl(i16, Of);

impl PartialEq for DateImpl {
    fn eq(&self, other: &DateImpl) -> bool {
        // dbg!(self, other);
        self.0 == other.0 && self.1 == other.1
    }
}

impl Eq for DateImpl {}

impl Hash for DateImpl {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write_i16(self.0);
        self.1.hash(state)
    }
}

#[cfg(feature = "arbitrary")]
impl arbitrary::Arbitrary<'_> for DateImpl {
    fn arbitrary(u: &mut arbitrary::Unstructured) -> arbitrary::Result<DateImpl> {
        let year = u.int_in_range(MIN_YEAR..=MAX_YEAR)?;
        let flag = YearTypeFlag::from_year(year);
        let ord = u.int_in_range(1..=flag.ndays())?;
        DateImpl::from_yo(year, ord).ok_or(arbitrary::Error::IncorrectFormat)
    }
}

impl DateImpl {
    pub(super) const CE: DateImpl =
        DateImpl(1, Of::start_of_year(YearTypeFlag::calculate_from_year(1)));

    pub(super) const fn from_yo(year: i16, ord: u16) -> Option<DateImpl> {
        let flag = YearTypeFlag::calculate_from_year(year);
        match Of::new(ord, flag) {
            Some(of) => Some(DateImpl(year, of)),
            None => None,
        }
    }

    #[track_caller]
    #[cfg(feature = "const-validation")]
    pub(super) const fn from_yo_validated(year: i16, ord: u16) -> DateImpl {
        let flag = YearTypeFlag::calculate_from_year(year);
        match Of::new(ord, flag) {
            Some(of) => DateImpl(year, of),
            None => panic!("Invalid combination for year and ordinal"),
        }
    }

    pub(super) const fn from_ymd(year: i16, month: Month, day: u8) -> Option<DateImpl> {
        // dbg!(year, month, day);
        let of = try_opt!(Of::from_ymd(year, month, day));
        // dbg!(of);
        Some(DateImpl(year, of))
    }

    #[track_caller]
    #[cfg(feature = "const-validation")]
    pub(super) const fn from_ymd_validated(year: i16, month: Month, day: u8) -> DateImpl {
        match Of::from_ymd(year, month, day) {
            Some(of) => DateImpl(year, of),
            None => panic!("Invalid combination for year, month and day"),
        }
    }

    pub(super) const fn from_num_days_from_ce_opt(days: i32) -> Option<DateImpl> {
        // todo!()
        let days = try_opt!(days.checked_add(365)); // make December 31, 1 BCE equal to day 0
                                                    // dbg!(days);
        let (year_div_400, cycle) = const_div_mod_floor_i32(days, DAYS_IN_CYCLE);
        // dbg!(year_div_400, cycle);
        let (year_mod_400, ordinal) = cycle_to_yo(cycle as u32);
        // dbg!(year_mod_400, ordinal);
        let flags = YearTypeFlag::calculate_from_year(year_mod_400 as i16);
        // dbg!(flags);
        let year_base = year_div_400.checked_mul(400);
        // dbg!(year_base);
        let year = try_opt!(year_base).checked_add(try_from_u32_to_i32!(year_mod_400));
        // dbg!(year);
        DateImpl::from_yo(try_from_i32_to_i16!(try_opt!(year)), ordinal as u16)
    }

    pub(super) const fn from_isoywd_opt(
        year: i32,
        week: u16,
        weekday: Weekday,
    ) -> Option<DateImpl> {
        // dbg!(year, week, weekday);
        // https://en.wikipedia.org/wiki/ISO_week_date#Calculating_an_ordinal_or_month_date_from_a_week_date
        let flags =
            YearTypeFlag::calculate_from_year(const_mod_floor_i16((year % 400) as i16, 400));

        if week == 0 || week > flags.nisoweeks() as u16 {
            return None;
        }

        const fn base_ordinal(week: u16, weekday: Weekday, flags: YearTypeFlag) -> Option<u16> {
            let week_ord = try_opt!(try_opt!(try_opt!(week.checked_mul(7)).checked_sub(6))
                .checked_add(weekday.num_days_from_monday() as u16));

            let ord = try_opt!(flags.week_1_jan_delta_days_from_jan_1_calendar_adj(week_ord));

            if ord == 0 {
                None
            } else {
                Some(ord)
            }
        }

        let base_ord = base_ordinal(week, weekday, flags);

        match base_ord {
            Some(ord) if ord <= flags.ndays().get() => {
                // matching cy
                // let adj = mult_week.checked_sub(u16::from(flags.jan_1_weekday().num_days_from_monday()))?.checked_add(u16::from(weekday.num_days_from_monday()) + 1)?;
                // dbg!("regular");
                // dbg!(flags.jan_1_weekday().num_days_from_monday(), weekday.num_days_from_monday(), adj);
                let cal_year = try_from_i32_to_i16!(year);
                // let ordinal = adj;
                // dbg!(cal_year, flags, ord);
                DateImpl::from_yo(cal_year, ord)
            }
            Some(ord) => {
                // next CY
                let cal_year = try_from_i32_to_i16!(year + 1);
                let adj_ord = try_opt!(ord.checked_sub(flags.ndays().get()));
                // dbg!(cal_year, alt_flags, adj_ord);
                DateImpl::from_yo(cal_year, adj_ord)
            }
            None => {
                // prev cy
                let cal_year = try_from_i32_to_i16!(year - 1);
                let alt_flags = YearTypeFlag::calculate_from_year(cal_year);

                let ord =
                    try_opt!(flags
                        .week_1_jan_delta_days_from_jan_1_calendar_adj(alt_flags.ndays().get()));
                // dbg!(ord);
                let adj_ord = ord + 1 + weekday.num_days_from_monday() as u16;
                // dbg!(cal_year, adj_ord, Of::from_ordinal_and_year(adj_ord, cal_year).unwrap().weekday());
                DateImpl::from_yo(cal_year, adj_ord)
            }
        }
    }

    // the ISOWEEK year has a wider range
    pub(super) const fn isoweek_year(&self) -> i32 {
        // dbg!(self);

        // https://en.wikipedia.org/wiki/ISO_week_date#Calculating_the_week_number_from_an_ordinal_date
        let num = (self.ordinal().get() + 9 - self.weekday().num_days_from_monday() as u16) / 7;
        // dbg!(num);
        match num {
            0 => self.year() as i32 - 1,
            53 => {
                match YearTypeFlag::calculate_from_year(const_mod_floor_i16(self.year(), 400) + 1)
                    .jan_1_weekday()
                {
                    Weekday::Tue | Weekday::Wed | Weekday::Thu => self.year() as i32 + 1,
                    Weekday::Mon | Weekday::Fri | Weekday::Sat | Weekday::Sun => self.year() as i32,
                }
                // dbg!(self.weekday(), YearTypeFlag::calculate_from_year(mod_floor(self.year(), 400) + 1).jan_1_weekday());
                // todo!()
            }
            _ => self.year() as i32, // Ordering::Greater => todo!(),
        }
        // if ordinal is less than or equal to the max days in last week of prev year,
        // then we are in the last week of the prev year
        // if self.ordinal().get()
        //     < self.year_type().ordinal_of_first_day_of_first_week_in_matching_year()
        // {
        //     i32::from(self.year()) - 1
        // } else if self.ordinal().get() > self.year_type().ordinal_of_last_day_in_last_week_in_matching_year() {
        //     i32::from(self.year()) + 1
        // } else {
        //     self.year().into()
        // }
    }

    // u16 for convenience as u16 is a lot more convenient than Option<u8>!
    pub(super) const fn isoweek_number(&self) -> u16 {
        // dbg!(self);

        // https://en.wikipedia.org/wiki/ISO_week_date#Calculating_the_week_number_from_an_ordinal_date
        let num = (self.ordinal().get() + 9 - self.weekday().num_days_from_monday() as u16) / 7;
        // dbg!(num);
        match num {
            0 => YearTypeFlag::calculate_from_year(const_mod_floor_i16(self.year(), 400) - 1)
                .nisoweeks() as u16,
            53 => {
                let next_year_flags =
                    YearTypeFlag::calculate_from_year(const_mod_floor_i16(self.year(), 400) + 1);
                match next_year_flags {
                    YearTypeFlag::BA | YearTypeFlag::B | YearTypeFlag::C | YearTypeFlag::CB => 53,
                    _ => 1,
                }
            }
            weeks => weeks,
        }
    }

    pub(super) const fn from_weekday_of_month_opt(
        year: i16,
        month: Month,
        weekday: Weekday,
        n: u8,
    ) -> Option<DateImpl> {
        // todo!()
        if n == 0 {
            return None;
        }
        let first = try_opt!(DateImpl::from_ymd(year, month, 1)).weekday();
        let first_to_dow = (7 + weekday.number_from_monday() - first.number_from_monday()) % 7;
        let day = (n - 1) * 7 + first_to_dow + 1;
        DateImpl::from_ymd(year, month, day)
    }

    pub(super) const fn diff_months(self, months: i32) -> Option<Self> {
        let (years, left) = ((months / 12), (months % 12));

        let years = try_from_i32_to_i16!(years);
        let left = try_from_i32_to_i16!(left);
        // Determine new year (without taking months into account for now

        let year = if (years > 0 && years > try_opt!(MAX_YEAR.checked_sub(self.year())))
            || (years < 0 && years < try_opt!(MIN_YEAR.checked_add(self.year())))
        {
            return None;
        } else {
            (self.year()) + years
        };

        // Determine new month

        let month = self.month().number_from_month() as i16 + left;
        let (year, month) = if month <= 0 {
            if year == (MIN_YEAR) {
                return None;
            }

            (try_opt!(year.checked_sub(1)), try_opt!(month.checked_add(12)))
        } else if month > 12 {
            if year == (MAX_YEAR) {
                return None;
            }

            (try_opt!(year.checked_add(1)), try_opt!(month.checked_sub(12)))
        } else {
            (year, month)
        };

        let month = try_opt!(Month::try_from_i16(month));
        // Clamp original day in case new month is shorter

        let flags = YearTypeFlag::calculate_from_year(year);

        let days1 = self.day_of_month().get();
        let days2 = flags.days_in_month(month).get();
        let day = if days1 < days2 { days1 } else { days2 };

        DateImpl::from_ymd(year, month, day)
    }

    pub(super) const fn year_type(&self) -> YearTypeFlag {
        self.of().flags()
    }
    const fn of(&self) -> Of {
        self.1
    }
    pub(super) const fn weekday(&self) -> Weekday {
        self.of().weekday()
    }
    pub(super) const fn ordinal(&self) -> NonZeroU16 {
        self.of().ordinal()
    }

    pub(super) const fn month(&self) -> Month {
        self.of().month()
    }

    pub(super) const fn day_of_month(&self) -> NonZeroU8 {
        self.of().day_of_month()
    }

    pub(super) const fn year(&self) -> i16 {
        self.0
    }

    pub(super) const fn diff_days(self, days: i64) -> Option<Self> {
        // will later be swapped to proper impl once checked_*_signed are removed
        self.checked_add_signed(days)
    }

    pub const fn signed_duration_since(self, rhs: DateImpl) -> i64 {
        let year1 = self.year();
        let year2 = rhs.year();
        let (year1_div_400, year1_mod_400) = const_div_mod_floor_i16(year1, 400);
        let (year2_div_400, year2_mod_400) = const_div_mod_floor_i16(year2, 400);
        let cycle1 = yo_to_cycle(year1_mod_400 as u32, self.ordinal().get());
        let cycle2 = yo_to_cycle(year2_mod_400 as u32, rhs.ordinal().get());

        (year1_div_400 as i64 - year2_div_400 as i64) * DAYS_IN_CYCLE as i64
            + (cycle1 as i64 - cycle2 as i64)
    }

    pub(super) const fn checked_add_signed(self, rhs: i64) -> Option<Self> {
        // dbg!(self);
        let rhs = try_from_i64_to_i32!(rhs);
        // dbg!(rhs);
        let year = self.year();
        // dbg!(year);
        let (mut year_div_400, year_mod_400) = const_div_mod_floor_i16(year, 400);
        // dbg!(year_div_400, year_mod_400);
        let cycle = yo_to_cycle(year_mod_400 as u32, self.ordinal().get());
        // dbg!(cycle);
        let cycle = try_opt!((cycle as i32).checked_add(rhs));
        // dbg!(cycle);
        let (cycle_div_400y, cycle) = const_div_mod_floor_i32(cycle, DAYS_IN_CYCLE);
        // dbg!(cycle_div_400y, cycle);
        year_div_400 = try_opt!(year_div_400.checked_add(try_from_i32_to_i16!(cycle_div_400y)));
        // dbg!(year_div_400);
        let (year_mod_400, ordinal) = cycle_to_yo(cycle as u32);
        // dbg!(year_mod_400, ordinal);
        let year_mod_400 = try_from_u32_to_u16!(year_mod_400);
        // dbg!(year_mod_400);
        let ordinal = try_from_u32_to_u16!(ordinal);
        // dbg!(ordinal);
        let year_base = (year_div_400 as i32).checked_mul(400);
        // dbg!(year_base);
        let year = try_opt!(year_base).checked_add(year_mod_400 as i32);
        // dbg!(year);
        let year = try_from_i32_to_i16!(try_opt!(year));
        // dbg!(year);
        DateImpl::from_yo(year, ordinal)
    }

    pub(super) const fn checked_sub_signed(self, rhs: i64) -> Option<Self> {
        // dbg!(self);
        let rhs = try_from_i64_to_i32!(rhs);
        // dbg!(rhs);
        let year = self.year();
        // dbg!(year);
        let (mut year_div_400, year_mod_400) = const_div_mod_floor_i16(year, 400);
        // dbg!(year_div_400, year_mod_400);
        let cycle = yo_to_cycle(year_mod_400 as u32, self.ordinal().get());
        // dbg!(cycle);
        let cycle = try_opt!((cycle as i32).checked_sub(rhs));
        // dbg!(cycle);
        let (cycle_div_400y, cycle) = const_div_mod_floor_i32(cycle, DAYS_IN_CYCLE);
        // dbg!(cycle_div_400y, cycle);
        year_div_400 = try_opt!(year_div_400.checked_add(try_from_i32_to_i16!(cycle_div_400y)));
        // dbg!(year_div_400);

        let (year_mod_400, ordinal) = cycle_to_yo(cycle as u32);
        // dbg!(year_mod_400, ordinal);

        let year_mod_400 = try_from_u32_to_u16!(year_mod_400);
        // dbg!(year_mod_400);

        let ordinal = try_from_u32_to_u16!(ordinal);

        let year_base = (year_div_400 as i32).checked_mul(400);
        // dbg!(year_base);
        let year = try_opt!(year_base).checked_add(year_mod_400 as i32);
        // dbg!(year);
        let year = try_from_i32_to_i16!(try_opt!(year));
        // dbg!(year);

        DateImpl::from_yo(year, ordinal)
    }

    #[inline]
    pub(super) const fn succ_opt(&self) -> Option<DateImpl> {
        let of = self.of();
        let current_year = self.year();
        if of.ordinal().get() == of.flags().ndays().get() {
            let next_year = try_opt!(current_year.checked_add(1));
            DateImpl::from_yo(next_year, 1)
        } else {
            DateImpl::from_yo(current_year, of.ordinal().get() + 1)
        }
    }

    #[inline]
    pub(super) const fn pred_opt(&self) -> Option<DateImpl> {
        let of = self.of();
        let current_year = self.year();
        if of.ordinal().get() == 1 {
            let prev_year = try_opt!(current_year.checked_sub(1));
            let new_flags = YearTypeFlag::calculate_from_year(prev_year);
            DateImpl::from_yo(prev_year, new_flags.ndays().get())
        } else {
            DateImpl::from_yo(current_year, of.ordinal().get() - 1)
        }
    }

    /// The minimum possible `Date` (January 1, 262145 BCE).
    pub(super) const MIN: DateImpl = DateImpl(i16::MIN, Of::MIN_YEAR_MIN);
    /// The maximum possible `Date` (December 31, 262143 CE).
    pub(super) const MAX: DateImpl = DateImpl(i16::MAX, Of::MAX_YEAR_MAX);
}

// from num-integer, copied so it can be const
/// Floored integer modulo
#[inline]
const fn const_mod_floor_i16(a: i16, b: i16) -> i16 {
    // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
    // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
    let r = a % b;
    if (r > 0 && b < 0) || (r < 0 && b > 0) {
        r + b
    } else {
        r
    }
}

// from num-integer, copied so it can be const
/// Floored integer modulo
#[inline]
const fn const_mod_floor_i32(a: i32, b: i32) -> i32 {
    // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
    // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
    let r = a % b;
    if (r > 0 && b < 0) || (r < 0 && b > 0) {
        r + b
    } else {
        r
    }
}

// from num-integer, copied so it can be const
/// Floored integer modulo
#[inline]
const fn const_div_floor_i16(a: i16, b: i16) -> i16 {
    // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
    // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
    let (d, r) = (a / b, a % b);
    if (r > 0 && b < 0) || (r < 0 && b > 0) {
        d - 1
    } else {
        d
    }
}

// from num-integer, copied so it can be const
/// Floored integer modulo
#[inline]
const fn const_div_floor_i32(a: i32, b: i32) -> i32 {
    // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
    // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
    let (d, r) = (a / b, a % b);
    if (r > 0 && b < 0) || (r < 0 && b > 0) {
        d - 1
    } else {
        d
    }
}

// from num-integer, copied so it can be const
/// Floored integer modulo
#[inline]
const fn const_div_mod_floor_i16(a: i16, b: i16) -> (i16, i16) {
    (const_div_floor_i16(a, b), const_mod_floor_i16(a, b))
}

// from num-integer, copied so it can be const
/// Floored integer modulo
#[inline]
const fn const_div_mod_floor_i32(a: i32, b: i32) -> (i32, i32) {
    (const_div_floor_i32(a, b), const_mod_floor_i32(a, b))
}

const fn is_leap(astronomical_year: i16) -> bool {
    if astronomical_year % 4 != 0 {
        return false;
    }

    if astronomical_year % 400 == 0 {
        return true;
    }

    if astronomical_year % 100 == 0 {
        return false;
    }

    true
}

pub fn ndays(astronomical_year: i16) -> NonZeroU16 {
    match is_leap(astronomical_year) {
        true => unsafe { NonZeroU16::new_unchecked(366) },
        false => unsafe { NonZeroU16::new_unchecked(365) },
    }
}

pub mod year_flags {
    use super::*;
    use crate::Month;
    use core::num::NonZeroU16;
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
    // https://en.wikipedia.org/wiki/Dominical_letter
    pub enum YearTypeFlag {
        A,  // Common, Sunday start
        AG, // Leap, Sunday start
        B,  // Common, Saturday start
        BA, // Leap, Saturday start
        C,  // Common, Friday start
        CB, // Leap, Friday start
        D,  // Common, Thursday start
        DC, // Leap, Thursday start
        E,  // Common, Wednesday start
        ED, // Leap, Wednesday start
        F,  // Common, Tuesday start
        FE, // Leap, Tuesday start
        G,  // Common, Monday start
        GF, // Leap, Monday start
    }

    pub(super) const fn year_deltas(year_mod_400: u32) -> u32 {
        if year_mod_400 == 0 {
            return 0;
        }
        let adj = (year_mod_400 - 1) / 100;
        let base = (year_mod_400 - 1) / 4 + 1;
        base - adj
    }

    pub(super) const fn cycle_to_yo(cycle: u32) -> (u32, u32) {
        let (mut year_mod_400, mut ordinal0) = (cycle / 365, cycle % 365);
        let delta = year_deltas(year_mod_400);
        if ordinal0 < delta {
            year_mod_400 -= 1;
            ordinal0 += 365 - year_deltas(year_mod_400);
        } else {
            ordinal0 -= delta;
        }
        (year_mod_400, ordinal0 + 1)
    }

    pub(super) const fn yo_to_cycle(year_mod_400: u32, ordinal: u16) -> u32 {
        year_mod_400 * 365 + year_deltas(year_mod_400) + ordinal as u32 - 1
    }

    impl YearTypeFlag {
        pub const fn ndays(&self) -> NonZeroU16 {
            match self.is_leap() {
                true => unsafe { NonZeroU16::new_unchecked(366) },
                false => unsafe { NonZeroU16::new_unchecked(365) },
            }
        }

        pub const fn is_leap(&self) -> bool {
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

        pub const fn jan_1_weekday(&self) -> Weekday {
            match self {
                YearTypeFlag::A => Weekday::Sun,  // Common, Sunday start
                YearTypeFlag::AG => Weekday::Sun, // Leap, Sunday start
                YearTypeFlag::B => Weekday::Sat,  // Common, Saturday start
                YearTypeFlag::BA => Weekday::Sat, // Leap, Saturday start
                YearTypeFlag::C => Weekday::Fri,  // Common, Friday start
                YearTypeFlag::CB => Weekday::Fri, // Leap, Friday start
                YearTypeFlag::D => Weekday::Thu,  // Common, Thursday start
                YearTypeFlag::DC => Weekday::Thu, // Leap, Thursday start
                YearTypeFlag::E => Weekday::Wed,  // Common, Wednesday start
                YearTypeFlag::ED => Weekday::Wed, // Leap, Wednesday start
                YearTypeFlag::F => Weekday::Tue,  // Common, Tuesday start
                YearTypeFlag::FE => Weekday::Tue, // Leap, Tuesday start
                YearTypeFlag::G => Weekday::Mon,  // Common, Monday start
                YearTypeFlag::GF => Weekday::Mon, // Leap, Monday start
            }
        }

        pub const fn ordinal_of_last_day_in_last_week_in_matching_year(&self) -> u16 {
            self.ndays().get()
                - match self {
                    YearTypeFlag::A => 0,
                    YearTypeFlag::AG => 1,
                    YearTypeFlag::B => 0,
                    YearTypeFlag::BA => 0,
                    YearTypeFlag::C => 0,
                    YearTypeFlag::CB => 0,
                    YearTypeFlag::D => 0,
                    YearTypeFlag::DC => 0,
                    YearTypeFlag::E => 3,
                    YearTypeFlag::ED => 0,
                    YearTypeFlag::F => 2,
                    YearTypeFlag::FE => 3,
                    YearTypeFlag::G => 1,
                    YearTypeFlag::GF => 2,
                }
        }

        pub const fn ordinal_of_first_day_of_first_week_in_matching_year(&self) -> u16 {
            match self {
                YearTypeFlag::A => 2,
                YearTypeFlag::AG => 2,
                YearTypeFlag::B => 3,
                YearTypeFlag::BA => 3,
                YearTypeFlag::C => 4,
                YearTypeFlag::CB => 4,
                YearTypeFlag::D => 5,
                YearTypeFlag::DC => 5,
                YearTypeFlag::E => 6,
                YearTypeFlag::ED => 6,
                YearTypeFlag::F => 7,
                YearTypeFlag::FE => 7,
                YearTypeFlag::G => 1,
                YearTypeFlag::GF => 1,
            }
        }

        pub const fn days_in_month(&self, month: Month) -> NonZeroU8 {
            let d = match month {
                Month::January => 31,
                Month::February if self.is_leap() => 29,
                Month::February => 28,
                Month::March => 31,
                Month::April => 30,
                Month::May => 31,
                Month::June => 30,
                Month::July => 31,
                Month::August => 31,
                Month::September => 30,
                Month::October => 31,
                Month::November => 30,
                Month::December => 31,
            };
            unsafe { NonZeroU8::new_unchecked(d) }
        }

        pub const fn month_to_start_ordinal(&self, month: Month) -> u16 {
            if self.is_leap() {
                match month {
                    Month::January => 0,
                    Month::February => 31,
                    Month::March => 60,
                    Month::April => 91,
                    Month::May => 121,
                    Month::June => 152,
                    Month::July => 182,
                    Month::August => 213,
                    Month::September => 244,
                    Month::October => 274,
                    Month::November => 305,
                    Month::December => 335,
                }
            } else {
                match month {
                    Month::January => 0,
                    Month::February => 31,
                    Month::March => 59,
                    Month::April => 90,
                    Month::May => 120,
                    Month::June => 151,
                    Month::July => 181,
                    Month::August => 212,
                    Month::September => 243,
                    Month::October => 273,
                    Month::November => 304,
                    Month::December => 334,
                }
            }
        }

        pub const fn calculate_from_year(year: i16) -> YearTypeFlag {
            // https://en.wikipedia.org/wiki/Dominical_letter#De_Morgan's_rule
            let year = const_mod_floor_i16(year, 400);
            let de_morgan = const_mod_floor_i16(
                const_mod_floor_i16(year, 100)
                    + const_mod_floor_i16(year, 100) / 4
                    + 5 * const_mod_floor_i16(year / 100, 4)
                    - 1,
                7,
            );
            let leap_dl = const_mod_floor_i16(de_morgan - 1, 7);

            match is_leap(year) {
                true => match leap_dl {
                    6 => YearTypeFlag::AG,
                    5 => YearTypeFlag::BA,
                    4 => YearTypeFlag::CB,
                    3 => YearTypeFlag::DC,
                    2 => YearTypeFlag::ED,
                    1 => YearTypeFlag::FE,
                    0 => YearTypeFlag::GF,
                    #[cfg(feature = "const-validation")]
                    _ => unreachable!(),
                    #[cfg(not(feature = "const-validation"))]
                    _ => YearTypeFlag::AG, // sentinel value
                },
                false => match de_morgan {
                    6 => YearTypeFlag::A,
                    5 => YearTypeFlag::B,
                    4 => YearTypeFlag::C,
                    3 => YearTypeFlag::D,
                    2 => YearTypeFlag::E,
                    1 => YearTypeFlag::F,
                    0 => YearTypeFlag::G,
                    #[cfg(feature = "const-validation")]
                    _ => unreachable!(),
                    #[cfg(not(feature = "const-validation"))]
                    _ => YearTypeFlag::A, // sentinel value
                },
            }
        }

        // #[inline]
        // pub fn from_year_mod_400(year_mod_400: i16) -> YearTypeFlag {
        //     let year_mod_400 = year_mod_400 % 400;
        //     // assert!(0 <= year_mod_400 && year_mod_400 <= 399);
        //     YEAR_TO_FLAGS[year_mod_400 as usize]
        // }

        // #[inline]
        // pub(super) fn isoweek_delta(&self) -> u8 {
        //     match self.jan_1_weekday() {
        //         Weekday::Mon => 0,
        //         Weekday::Tue => 6,
        //         Weekday::Wed => 5,
        //         Weekday::Thu => 4,
        //         Weekday::Fri => 3,
        //         Weekday::Sat => 2,
        //         Weekday::Sun => 1,
        //     }
        // }

        pub(super) const fn week_1_jan_delta_days_from_jan_1_calendar(&self) -> i8 {
            match self.jan_1_weekday() {
                Weekday::Mon => 0,
                Weekday::Tue => -1,
                Weekday::Wed => -2,
                Weekday::Thu => -3,
                Weekday::Fri => 3,
                Weekday::Sat => 2,
                Weekday::Sun => 1,
            }
        }

        pub(super) const fn week_1_jan_delta_days_from_jan_1_calendar_adj(
            &self,
            week_ord: u16,
        ) -> Option<u16> {
            match self.jan_1_weekday() {
                Weekday::Mon => Some(week_ord),
                Weekday::Tue => week_ord.checked_sub(1),
                Weekday::Wed => week_ord.checked_sub(2),
                Weekday::Thu => week_ord.checked_sub(3),
                Weekday::Fri => week_ord.checked_add(3),
                Weekday::Sat => week_ord.checked_add(2),
                Weekday::Sun => week_ord.checked_add(1),
            }
        }

        #[inline]
        // https://en.wikipedia.org/wiki/ISO_week_date
        pub(super) const fn nisoweeks(&self) -> u8 {
            match self {
                YearTypeFlag::D | YearTypeFlag::DC | YearTypeFlag::ED => 53,
                _ => 52,
            }
        }
    }
}

mod ordinal_flags {
    use super::*;
    use core::num::NonZeroU16;
    use core::num::NonZeroU8;

    // this could be extended to store some extra flags for year as well.
    #[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
    #[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
    pub enum OrdinalFlagAndYearFlag {
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
        const fn with_ordinal_second_reigster(
            &self,
            second_register: bool,
        ) -> OrdinalFlagAndYearFlag {
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
        const fn ordinal_second_register(&self) -> bool {
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
        const fn internal(&self) -> YearTypeFlag {
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

    /// Ordinal (day of year) and year flags: `(ordinal << 4) | flags`.
    ///
    /// The whole bits except for the least 3 bits are referred as `Ol` (ordinal and leap flag),
    /// which is an index to the `OL_TO_MDL` lookup table.
    #[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
    #[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
    pub struct Of(NonZeroU8, OrdinalFlagAndYearFlag);

    impl Of {
        pub(super) const MIN_YEAR_MIN: Of = Of(
            unsafe { NonZeroU8::new_unchecked(1) },
            YearTypeFlag::calculate_from_year(i16::MIN).with_ordinal_second_reigster(false),
        );
        pub(super) const MAX_YEAR_MAX: Of = Of(
            unsafe {
                NonZeroU8::new_unchecked(110 /* 365 - 255 */)
            },
            YearTypeFlag::calculate_from_year(i16::MAX).with_ordinal_second_reigster(true),
        );

        pub const fn start_of_year(yf: YearTypeFlag) -> Of {
            Of(unsafe { NonZeroU8::new_unchecked(1) }, yf.with_ordinal_second_reigster(false))
        }

        // this function should only allow creation of valid Of.
        // otherwise it will return None.
        #[inline]
        pub(super) const fn new(ordinal: u16, yf: YearTypeFlag) -> Option<Of> {
            match 1_u16 <= ordinal && ordinal <= yf.ndays().get() {
                true if ordinal > 255 => Some(Of(
                    match NonZeroU8::new((ordinal - 255) as u8) {
                        Some(o) => o,
                        None => return None,
                    },
                    yf.with_ordinal_second_reigster(true),
                )),
                true => Some(Of(
                    match NonZeroU8::new(ordinal as u8) {
                        Some(o) => o,
                        None => return None,
                    },
                    yf.with_ordinal_second_reigster(false),
                )),
                false => None,
            }
        }

        // pub(super) fn from_ymd(year: i16, month: Month, day: u8) -> Option<Of> {
        //     if day == 0 {
        //         return None;
        //     }

        //     let month_idx = usize::from(month.number_from_month().checked_sub(1)?);

        //     let year_type = YearTypeFlag::calculate_from_year(year);

        //     let ordinal = match is_leap(year) {
        //         true => {
        //             if day > dbg!(*LEAP_DAYS_IN_MONTH.get(month_idx)?) {
        //                 return None;
        //             }
        //             *LEAP_MONTH_TO_START_ORDINAL.get(month_idx)? + u16::from(day)
        //         }
        //         false => {
        //             if day > dbg!(*DAYS_IN_MONTH.get(month_idx)?) {
        //                 return None;
        //             }
        //             *MONTH_TO_START_ORDINAL.get(month_idx)? + u16::from(day)
        //         }
        //     };
        //     Of::new(ordinal, year_type)
        // }

        pub(super) const fn from_ymd(year: i16, month: Month, day: u8) -> Option<Of> {
            if day == 0 {
                return None;
            }

            // let month_idx = usize::from(try_opt!(month.number_from_month().checked_sub(1)));

            let year_type = YearTypeFlag::calculate_from_year(year);

            if day > year_type.days_in_month(month).get() {
                return None;
            }

            let ordinal = year_type.month_to_start_ordinal(month).checked_add(day as u16);

            Of::new(try_opt!(ordinal), year_type)
        }

        pub(super) const fn from_ordinal_and_year(ordinal: u16, year: i16) -> Option<Of> {
            let year_type = YearTypeFlag::calculate_from_year(year);
            Of::new(ordinal, year_type)
        }

        #[allow(clippy::collapsible_else_if)]
        // manual binary search.
        // might be better as just a match with 365/366 arms but will leave for now
        // not collapsing the if else to match the syntax to the binary search semantics
        pub(super) const fn month(&self) -> Month {
            let ord = self.ordinal().get();
            if self.flags().is_leap() {
                if ord >= 183 {
                    if ord >= 275 {
                        if ord >= 336 {
                            Month::December
                        } else {
                            if ord >= 306 {
                                Month::November
                            } else {
                                Month::October
                            }
                        }
                    } else {
                        if ord >= 245 {
                            Month::September
                        } else {
                            if ord >= 214 {
                                Month::August
                            } else {
                                Month::July
                            }
                        }
                    }
                } else {
                    if ord >= 92 {
                        if ord >= 153 {
                            Month::June
                        } else {
                            if ord >= 122 {
                                Month::May
                            } else {
                                Month::April
                            }
                        }
                    } else {
                        if ord >= 61 {
                            Month::March
                        } else {
                            if ord >= 32 {
                                Month::February
                            } else {
                                Month::January
                            }
                        }
                    }
                }
            } else {
                if ord >= 182 {
                    if ord >= 274 {
                        if ord >= 335 {
                            Month::December
                        } else {
                            if ord >= 305 {
                                Month::November
                            } else {
                                Month::October
                            }
                        }
                    } else {
                        if ord >= 244 {
                            Month::September
                        } else {
                            if ord >= 213 {
                                Month::August
                            } else {
                                Month::July
                            }
                        }
                    }
                } else {
                    if ord >= 91 {
                        if ord >= 152 {
                            Month::June
                        } else {
                            if ord >= 121 {
                                Month::May
                            } else {
                                Month::April
                            }
                        }
                    } else {
                        if ord >= 60 {
                            Month::March
                        } else {
                            if ord >= 32 {
                                Month::February
                            } else {
                                Month::January
                            }
                        }
                    }
                }
            }
        }

        pub(super) const fn day_of_month(&self) -> NonZeroU8 {
            let month = self.month();
            let ord = self.ordinal().get();
            let month_start_ordinal = self.flags().month_to_start_ordinal(month);

            // assert!(ord > month_start_ordinal);
            let dom = ord - month_start_ordinal;
            // assert!(dom >= 1 && dom <= self.flags().days_in_month(month).get() as u16);
            unsafe { NonZeroU8::new_unchecked(dom as u8) }
        }

        #[inline]
        pub(super) const fn ordinal(&self) -> NonZeroU16 {
            let n = if self.1.ordinal_second_register() {
                (self.0.get() as u16) + 255
            } else {
                self.0.get() as u16
            };
            unsafe { NonZeroU16::new_unchecked(n) }
        }

        #[inline]
        pub(super) const fn with_ordinal(&self, ordinal: u16) -> Option<Of> {
            Of::new(ordinal, self.flags())
        }

        #[inline]
        pub(super) const fn flags(&self) -> YearTypeFlag {
            self.1.internal()
        }

        #[inline]
        pub(super) const fn weekday(&self) -> Weekday {
            let start_at = self.flags().jan_1_weekday();
            let ord = self.ordinal().get();
            // dbg!(start_at, ord, (u16::from(start_at.num_days_from_monday()) + ord) % 7);
            // dbg!(
            //     ord + 6,
            //     ord + 6 - u16::from(start_at.num_days_from_monday()),
            //     (ord + 6 - u16::from(start_at.num_days_from_monday())) % 7,
            // );

            match (start_at.num_days_from_monday() as u16 + ord - 1) % 7 {
                0 => Weekday::Mon,
                1 => Weekday::Tue,
                2 => Weekday::Wed,
                3 => Weekday::Thu,
                4 => Weekday::Fri,
                5 => Weekday::Sat,
                6 => Weekday::Sun,

                #[cfg(feature = "const-validation")]
                _ => unreachable!(),
                #[cfg(not(feature = "const-validation"))]
                _ => Weekday::Mon, // sentinel value
            }
        }

        // #[inline]
        // pub(super) fn isoweekdate_raw(&self) -> (u8, Weekday) {

        //     todo!()
        // }
    }
}

#[cfg(test)]
mod tests {
    use num_iter::range_inclusive;

    use super::year_flags::{YearTypeFlag, A, AG, B, BA, C, CB, D, DC, E, ED, F, FE, G, GF};
    use super::{ndays, Of};
    use crate::naive::internals::is_leap;
    use crate::naive::internals::year_flags::year_deltas;
    use crate::{Month, Weekday};
    use num_integer::mod_floor;

    const NONLEAP_FLAGS: [YearTypeFlag; 7] = [A, B, C, D, E, F, G];
    const LEAP_FLAGS: [YearTypeFlag; 7] = [AG, BA, CB, DC, ED, FE, GF];
    const FLAGS: [YearTypeFlag; 14] = [A, B, C, D, E, F, G, AG, BA, CB, DC, ED, FE, GF];

    #[test]
    fn test_year_flags_ndays_from_year() {
        assert_eq!(YearTypeFlag::calculate_from_year(2014).ndays().get(), 365);
        assert_eq!(YearTypeFlag::calculate_from_year(2012).ndays().get(), 366);
        assert_eq!(YearTypeFlag::calculate_from_year(2000).ndays().get(), 366);
        assert_eq!(YearTypeFlag::calculate_from_year(1900).ndays().get(), 365);
        assert_eq!(YearTypeFlag::calculate_from_year(1600).ndays().get(), 366);
        assert_eq!(YearTypeFlag::calculate_from_year(1).ndays().get(), 365);
        assert_eq!(YearTypeFlag::calculate_from_year(0).ndays().get(), 366); // 1 BCE (proleptic Gregorian)
        assert_eq!(YearTypeFlag::calculate_from_year(-1).ndays().get(), 365); // 2 BCE
        assert_eq!(YearTypeFlag::calculate_from_year(-4).ndays().get(), 366); // 5 BCE
        assert_eq!(YearTypeFlag::calculate_from_year(-99).ndays().get(), 365); // 100 BCE
        assert_eq!(YearTypeFlag::calculate_from_year(-100).ndays().get(), 365); // 101 BCE
        assert_eq!(YearTypeFlag::calculate_from_year(-399).ndays().get(), 365); // 400 BCE
        assert_eq!(YearTypeFlag::calculate_from_year(-400).ndays().get(), 366); // 401 BCE
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

        // for &flags in LEAP_FLAGS.iter() {
        //     check(false, flags, 0, 0);
        //     check(true, flags, 1, 366);
        //     check(false, flags, 367, 1024);
        //     check(false, flags, u16::MAX, u16::MAX);
        // }
    }

    #[test]
    fn test_of_fields() {
        for &flags in FLAGS.iter() {
            for ordinal in range_inclusive(1u16, 366) {
                match Of::new(ordinal, flags) {
                    Some(of) => assert_eq!(of.ordinal().get(), ordinal),
                    None => {
                        assert_eq!(flags.ndays().get(), 365);
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
                        assert_eq!(of.ordinal().get(), ordinal);
                    }
                    // this should always succeed so it's a bug if not
                    None if (1..=flags.ndays().get()).contains(&ordinal) => {
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
        // for &flags in LEAP_FLAGS.iter() {
        //     check(flags, 1);
        //     check(flags, 366);
        // }
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
            for ordinal in range_inclusive(2u16, flags.ndays().get()) {
                let of = Of::new(ordinal, flags).unwrap();
                let expected = prev.succ();
                assert_eq!(of.weekday(), expected);
                prev = expected;
            }
        }
    }

    // #[test]
    // fn test_of_isoweekdate_raw() {
    //     for &flags in FLAGS.iter() {
    //         // January 4 should be in the first week
    //         let (week, _) = Of::new(4 /* January 4 */, flags).unwrap().isoweekdate_raw();
    //         assert_eq!(week, 1);
    //     }
    // }

    #[cfg(feature = "const-validation")]
    #[test]
    fn test_const_ymd() {
        use super::DateImpl;
        use crate::Month;

        let res = std::panic::catch_unwind(|| {
            let _ = DateImpl::from_ymd_validated(2022, Month::January, 0);
        });
        assert!(res.is_err());
        let _ = DateImpl::from_ymd_validated(2022, Month::January, 1);
        let _ = DateImpl::from_ymd_validated(2022, Month::December, 31);
        let res = std::panic::catch_unwind(|| {
            let _ = DateImpl::from_ymd_validated(2022, Month::December, 32);
        });
        assert!(res.is_err());

        ymd!(2022, Month::January, 5);
        ymd!(2022, Month::January, 1);
        ymd!(2022, Month::January, 2);
    }

    #[test]
    fn test_ndays() {
        for i in i16::MIN..=i16::MAX {
            ndays(i);
        }
    }

    const YEAR_TO_FLAGS: &[YearTypeFlag] = &[
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

    const MONTH_TO_START_ORDINAL: [u16; 12] = [
        0,   // Jan
        31,  // Feb
        59,  // Mar
        90,  // Apr
        120, // May
        151, // Jun
        181, // Jul
        212, // Aug
        243, // Sep
        273, // Oct
        304, // Nov
        334, // Dec
    ];

    const LEAP_MONTH_TO_START_ORDINAL: [u16; 12] = [
        0,   // Jan
        31,  // Feb
        60,  // Mar
        91,  // Apr
        121, // May
        152, // Jun
        182, // Jul
        213, // Aug
        244, // Sep
        274, // Oct
        305, // Nov
        335, // Dec
    ];

    const DAYS_IN_MONTH: [u8; 12] = [
        31, // Jan
        28, // Feb
        31, // Mar
        30, // Apr
        31, // May
        30, // Jun
        31, // Jul
        31, // Aug
        30, // Sep
        31, // Oct
        30, // Nov
        31, // Dec
    ];

    const LEAP_DAYS_IN_MONTH: [u8; 12] = [
        31, // Jan
        29, // Feb
        31, // Mar
        30, // Apr
        31, // May
        30, // Jun
        31, // Jul
        31, // Aug
        30, // Sep
        31, // Oct
        30, // Nov
        31, // Dec
    ];

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

    #[test]
    fn test_year_flags_fns() {
        for y in i16::MIN..=i16::MAX {
            let flags = YearTypeFlag::calculate_from_year(y);

            assert_eq!(flags.is_leap(), is_leap(y));

            assert_eq!(flags, YEAR_TO_FLAGS[mod_floor(y, 400) as usize]);

            flags.ndays();
        }
    }

    #[test]
    fn test_year_flags_ymd() {
        for y in i16::MIN..=i16::MAX {
            let flags = YearTypeFlag::calculate_from_year(y);

            for month in [
                Month::January,
                Month::February,
                Month::March,
                Month::April,
                Month::May,
                Month::June,
                Month::July,
                Month::August,
                Month::September,
                Month::October,
                Month::November,
                Month::December,
            ]
            .iter()
            .copied()
            {
                flags.days_in_month(month);

                let month_start = flags.month_to_start_ordinal(month);

                if flags.is_leap() {
                    assert_eq!(
                        month_start,
                        LEAP_MONTH_TO_START_ORDINAL[month.number_from_month() as usize - 1]
                    )
                } else {
                    assert_eq!(
                        month_start,
                        MONTH_TO_START_ORDINAL[month.number_from_month() as usize - 1]
                    )
                }

                let days_in_month = flags.days_in_month(month);

                if flags.is_leap() {
                    assert_eq!(
                        days_in_month.get(),
                        LEAP_DAYS_IN_MONTH[month.number_from_month() as usize - 1]
                    )
                } else {
                    assert_eq!(
                        days_in_month.get(),
                        DAYS_IN_MONTH[month.number_from_month() as usize - 1]
                    )
                }

                for day in 1..=31 {
                    if let Some(of) = Of::from_ymd(y, month, day) {
                        of.weekday();
                        assert_eq!(of.flags(), flags);
                        assert_eq!(of.month(), month);
                        assert_eq!(of.day_of_month().get(), day);
                    }
                }
            }
        }
    }

    #[test]
    fn test_year_flags_yo() {
        for y in i16::MIN..=i16::MAX {
            let flags = YearTypeFlag::calculate_from_year(y);
            for ord in 1..=366 {
                if let Some(of) = Of::from_ordinal_and_year(ord, y) {
                    of.weekday();
                    assert_eq!(of.ordinal().get(), ord);
                    assert_eq!(of.flags(), flags);

                    if of.flags().is_leap() {
                        assert_eq!(
                            of.day_of_month().get(),
                            LEAP_ORDINAL_TO_DAY[of.ordinal().get() as usize - 1],
                        );
                        assert_eq!(
                            of.month().number_from_month(),
                            LEAP_ORDINAL_TO_MONTH[of.ordinal().get() as usize - 1],
                        );
                    } else {
                        assert_eq!(
                            of.day_of_month().get(),
                            ORDINAL_TO_DAY[of.ordinal().get() as usize - 1],
                        );
                        assert_eq!(
                            of.month().number_from_month(),
                            ORDINAL_TO_MONTH[of.ordinal().get() as usize - 1],
                        );
                    }
                }
            }
        }
    }

    const YEAR_DELTAS: [u32; 401] = [
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

    #[test]
    fn test_year_deltas() {
        for i in 0..=399 {
            assert_eq!(year_deltas(i), YEAR_DELTAS[i as usize],);
        }
    }
}
