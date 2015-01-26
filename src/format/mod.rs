// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * Formatting utilities for date and time.
 */

use std::fmt;

use {Datelike, Timelike};
use div::{div_floor, mod_floor};
use duration::Duration;
use offset::Offset;
use naive::date::NaiveDate;
use naive::time::NaiveTime;

pub use self::strftime::StrftimeItems;

/// Padding characters for numeric items.
#[derive(Copy, PartialEq, Eq, Debug)]
pub enum Pad {
    /// No padding.
    None,
    /// Zero (`0`) padding.
    Zero,
    /// Space padding.
    Space,
}

/// Numeric item types.
#[derive(Copy, PartialEq, Eq, Debug)]
pub enum Numeric {
    /// Full Gregorian year.
    Year,
    /// Gregorian year divided by 100 (century number). Always rounds towards minus infinity.
    YearDiv100,
    /// Gregorian year modulo 100. Cannot be negative.
    YearMod100,
    /// Year in the ISO week date.
    IsoYear,
    /// Year in the ISO week date, divided by 100. Always rounds towards minus infinity.
    IsoYearDiv100,
    /// Year in the ISO week date, modulo 100. Cannot be negative.
    IsoYearMod100,
    /// Month.
    Month,
    /// Day of the month.
    Day,
    /// Week number, where the week 1 starts at the first Sunday of January.
    WeekFromSun,
    /// Week number, where the week 1 starts at the first Monday of January.
    WeekFromMon,
    /// Week number in the ISO week date.
    IsoWeek,
    /// Day of the week, where Sunday = 0 and Saturday = 6.
    NumDaysFromSun,
    /// Day of the week, where Monday = 1 and Sunday = 7.
    WeekdayFromMon,
    /// Day of the year.
    Ordinal,
    /// Hour number in the 24-hour clocks.
    Hour,
    /// Hour number in the 12-hour clocks.
    Hour12,
    /// The number of minutes since the last whole hour.
    Minute,
    /// The number of seconds since the last whole minute.
    Second,
    /// The number of nanoseconds since the last whole second.
    Nanosecond,
    /// The number of non-leap seconds since January 1, 1970 0:00:00 UTC.
    Timestamp,
}

/// Fixed-format item types.
#[derive(Copy, PartialEq, Eq, Debug)]
pub enum Fixed {
    /// Abbreviated month names.
    ShortMonthName,
    /// Full month names.
    LongMonthName,
    /// Abbreviated day of the week names.
    ShortWeekdayName,
    /// FUll day of the week names.
    LongWeekdayName,
    /// AM/PM in upper cases.
    LowerAmPm,
    /// AM/PM in lower cases.
    UpperAmPm,
    /// Timezone name.
    TimezoneName,
    /// Offset from the local time to UTC (`+09:00` or `-04:00` or `+00:00`).
    TimezoneOffset,
    /// Offset from the local time to UTC (`+09:00` or `-04:00` or `Z`).
    TimezoneOffsetZ,
}

/// A single formatting item. This is used for both formatting and parsing.
#[derive(Copy, PartialEq, Eq, Debug)]
pub enum Item<'a> {
    /// A literally printed and parsed text.
    Literal(&'a str),
    /// Whitespace. Prints literally but parses zero or more whitespace.
    Space(&'a str),
    /// Numeric item. Can be optionally padded to the maximal length (if any) when formatting;
    /// the parser simply ignores any padded whitespace and zeroes.
    Numeric(Numeric, Pad),
    /// Fixed-format item.
    Fixed(Fixed),
    /// Issues a formatting error. Used to signal an invalid format string.
    Error,
}

macro_rules! lit  { ($x:expr) => (Item::Literal($x)) }
macro_rules! sp   { ($x:expr) => (Item::Space($x)) }
macro_rules! num  { ($x:ident) => (Item::Numeric(Numeric::$x, Pad::None)) }
macro_rules! num0 { ($x:ident) => (Item::Numeric(Numeric::$x, Pad::Zero)) }
macro_rules! nums { ($x:ident) => (Item::Numeric(Numeric::$x, Pad::Space)) }
macro_rules! fix  { ($x:ident) => (Item::Fixed(Fixed::$x)) }

/// Abbreviated month names.
static SHORT_MONTHS: [&'static str; 12] =
    ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];

/// Full month names.
static LONG_MONTHS: [&'static str; 12] =
    ["January", "February", "March", "April", "May", "June",
     "July", "August", "September", "October", "November", "December"];

/// Abbreviated weekday names.
static SHORT_WEEKDAYS: [&'static str; 7] =
    ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];

/// FUll weekday names.
static LONG_WEEKDAYS: [&'static str; 7] =
    ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"];

/// Tries to format given arguments with given formatting items.
/// Internally used by `DelayedFormat`.
pub fn format<'a, I>(w: &mut fmt::Formatter, date: Option<&NaiveDate>, time: Option<&NaiveTime>,
                     off: Option<&(String, Duration)>, items: I) -> fmt::Result
        where I: Iterator<Item=Item<'a>> {
    for item in items {
        match item {
            Item::Literal(s) | Item::Space(s) => try!(write!(w, "{}", s)),

            Item::Numeric(spec, pad) => {
                use self::Numeric::*;
                let week_from_sun =
                    |&: d: &NaiveDate| (d.ordinal() - d.weekday().num_days_from_sunday() + 7) / 7;
                let week_from_mon =
                    |&: d: &NaiveDate| (d.ordinal() - d.weekday().num_days_from_monday() + 7) / 7;
                let (width, v) = match spec {
                    Year           => (4, date.map(|d| d.year() as i64)),
                    YearDiv100     => (2, date.map(|d| div_floor(d.year() as i64, 100))),
                    YearMod100     => (2, date.map(|d| mod_floor(d.year() as i64, 100))),
                    IsoYear        => (4, date.map(|d| d.isoweekdate().0 as i64)),
                    IsoYearDiv100  => (2, date.map(|d| div_floor(d.isoweekdate().0 as i64, 100))),
                    IsoYearMod100  => (2, date.map(|d| mod_floor(d.isoweekdate().0 as i64, 100))),
                    Month          => (2, date.map(|d| d.month() as i64)),
                    Day            => (2, date.map(|d| d.day() as i64)),
                    WeekFromSun    => (2, date.map(|d| week_from_sun(d) as i64)),
                    WeekFromMon    => (2, date.map(|d| week_from_mon(d) as i64)),
                    IsoWeek        => (2, date.map(|d| d.isoweekdate().1 as i64)),
                    NumDaysFromSun => (1, date.map(|d| d.weekday().num_days_from_sunday() as i64)),
                    WeekdayFromMon => (1, date.map(|d| d.weekday().number_from_monday() as i64)),
                    Ordinal        => (3, date.map(|d| d.ordinal() as i64)),
                    Hour           => (2, time.map(|t| t.hour() as i64)),
                    Hour12         => (2, time.map(|t| t.hour12().1 as i64)),
                    Minute         => (2, time.map(|t| t.minute() as i64)),
                    Second         => (2, time.map(|t| (t.second() +
                                                        t.nanosecond() / 1_000_000_000) as i64)),
                    Nanosecond     => (9, time.map(|t| (t.nanosecond() % 1_000_000_000) as i64)),
                    Timestamp      => (1, match (date, time) {
                        (Some(d), Some(t)) => Some(d.and_time(*t).num_seconds_from_unix_epoch()),
                        (_, _) => None
                    }),
                };
                if let Some(v) = v {
                    match pad {
                        Pad::None => try!(write!(w, "{}", v)),
                        Pad::Zero => try!(write!(w, "{:01$}", v, width)),
                        Pad::Space => try!(write!(w, "{:1$}", v, width)),
                    }
                } else {
                    return Err(fmt::Error); // insufficient arguments for given format
                }
            },

            Item::Fixed(spec) => {
                use self::Fixed::*;
                let ret = match spec {
                    ShortMonthName =>
                        date.map(|d| write!(w, "{}", SHORT_MONTHS[d.month0() as usize])),
                    LongMonthName =>
                        date.map(|d| write!(w, "{}", LONG_MONTHS[d.month0() as usize])),
                    ShortWeekdayName =>
                        date.map(|d| write!(w, "{}",
                            SHORT_WEEKDAYS[d.weekday() .num_days_from_monday() as usize])),
                    LongWeekdayName =>
                        date.map(|d| write!(w, "{}",
                            LONG_WEEKDAYS[d.weekday().num_days_from_monday() as usize])),
                    LowerAmPm =>
                        time.map(|t| write!(w, "{}", if t.hour12().0 {"pm"} else {"am"})),
                    UpperAmPm =>
                        time.map(|t| write!(w, "{}", if t.hour12().0 {"PM"} else {"AM"})),
                    TimezoneName =>
                        off.map(|&(ref name, _)| write!(w, "{}", *name)),
                    TimezoneOffset =>
                        off.map(|&(_, ref local_minus_utc)| {
                            let off = local_minus_utc.num_minutes();
                            let (sign, off) = if off < 0 {('-', -off)} else {('+', off)};
                            write!(w, "{}{:02}{:02}", sign, off / 60, off % 60)
                        }),
                    TimezoneOffsetZ =>
                        off.map(|&(_, ref local_minus_utc)| {
                            let off = local_minus_utc.num_minutes();
                            if off != 0 {
                                let (sign, off) = if off < 0 {('-', -off)} else {('+', off)};
                                write!(w, "{}{:02}{:02}", sign, off / 60, off % 60)
                            } else {
                                write!(w, "Z")
                            }
                        }),
                };
                match ret {
                    Some(ret) => try!(ret),
                    None => return Err(fmt::Error), // insufficient arguments for given format
                }
            },

            Item::Error => return Err(fmt::Error),
        }
    }

    Ok(())
}

/// A *temporary* object which can be used as an argument to `format!` or others.
/// This is normally constructed via `format` methods of each date and time type.
#[derive(Debug)]
pub struct DelayedFormat<'a, I: Iterator<Item=Item<'a>> + Clone> {
    /// The date view, if any.
    date: Option<NaiveDate>,
    /// The time view, if any.
    time: Option<NaiveTime>,
    /// The name and local-to-UTC difference for the offset (timezone), if any.
    off: Option<(String, Duration)>,
    /// An iterator returning formatting items.
    items: I,
}

impl<'a, I: Iterator<Item=Item<'a>> + Clone> DelayedFormat<'a, I> {
    /// Makes a new `DelayedFormat` value out of local date and time.
    pub fn new(date: Option<NaiveDate>, time: Option<NaiveTime>, items: I) -> DelayedFormat<'a, I> {
        DelayedFormat { date: date, time: time, off: None, items: items }
    }

    /// Makes a new `DelayedFormat` value out of local date and time and UTC offset.
    pub fn new_with_offset<Off>(date: Option<NaiveDate>, time: Option<NaiveTime>,
                                offset: &Off, items: I) -> DelayedFormat<'a, I>
            where Off: Offset + fmt::Display {
        let name_and_diff = (offset.to_string(), offset.local_minus_utc());
        DelayedFormat { date: date, time: time, off: Some(name_and_diff), items: items }
    }
}

impl<'a, I: Iterator<Item=Item<'a>> + Clone> fmt::Display for DelayedFormat<'a, I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        format(f, self.date.as_ref(), self.time.as_ref(), self.off.as_ref(), self.items.clone())
    }
}

pub mod strftime;

