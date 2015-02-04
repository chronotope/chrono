// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * Formatting utilities for date and time.
 */

use std::fmt;
use std::iter;
use std::usize;
use std::error::Error;

use {Datelike, Timelike};
use Weekday;
use div::{div_floor, mod_floor};
use duration::Duration;
use offset::Offset;
use naive::date::NaiveDate;
use naive::time::NaiveTime;

use self::parsed::Parsed;
pub use self::strftime::StrftimeItems;

/// Padding characters for numeric items.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Pad {
    /// No padding.
    None,
    /// Zero (`0`) padding.
    Zero,
    /// Space padding.
    Space,
}

/// Numeric item types.
/// They have associated formatting width (FW) and parsing width (PW).
///
/// The **formatting width** is the minimal width to be formatted.
/// If the number is too short, and the padding is not `Pad::None`, then it is left-padded.
/// If the number is too long or (in some cases) negative, it is printed as is.
///
/// The **parsing width** is the maximal width to be scanned.
/// The parser only tries to consume from one to given number of digits (greedily). 
/// It also trims the preceding whitespaces if any.
/// It cannot parse the negative number, so some date and time cannot be formatted then
/// parsed with the same formatting items.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Numeric {
    /// Full Gregorian year (FW=PW=4).
    Year,
    /// Gregorian year divided by 100 (century number; FW=PW=2).
    /// Always rounds towards minus infinity.
    YearDiv100,
    /// Gregorian year modulo 100 (FW=PW=2). Cannot be negative.
    YearMod100,
    /// Year in the ISO week date (FW=PW=4).
    IsoYear,
    /// Year in the ISO week date, divided by 100 (FW=PW=2). Always rounds towards minus infinity.
    IsoYearDiv100,
    /// Year in the ISO week date, modulo 100 (FW=PW=2). Cannot be negative.
    IsoYearMod100,
    /// Month (FW=PW=2).
    Month,
    /// Day of the month (FW=PW=2).
    Day,
    /// Week number, where the week 1 starts at the first Sunday of January (FW=PW=2).
    WeekFromSun,
    /// Week number, where the week 1 starts at the first Monday of January (FW=PW=2).
    WeekFromMon,
    /// Week number in the ISO week date (FW=PW=2).
    IsoWeek,
    /// Day of the week, where Sunday = 0 and Saturday = 6 (FW=PW=1).
    NumDaysFromSun,
    /// Day of the week, where Monday = 1 and Sunday = 7 (FW=PW=1).
    WeekdayFromMon,
    /// Day of the year (FW=PW=3).
    Ordinal,
    /// Hour number in the 24-hour clocks (FW=PW=2).
    Hour,
    /// Hour number in the 12-hour clocks (FW=PW=2).
    Hour12,
    /// The number of minutes since the last whole hour (FW=PW=2).
    Minute,
    /// The number of seconds since the last whole minute (FW=PW=2).
    Second,
    /// The number of nanoseconds since the last whole second (FW=PW=9).
    Nanosecond,
    /// The number of non-leap seconds since January 1, 1970 0:00:00 UTC (FW=1, PW=infinity).
    Timestamp,
}

/// Fixed-format item types.
///
/// They have their own rules of formatting and parsing.
/// Otherwise noted, they print in the specified cases but parse case-insensitively.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Fixed {
    /// Abbreviated month names.
    ///
    /// Prints a three-letter-long name in the title case, reads the same name in any case.
    ShortMonthName,
    /// Full month names.
    ///
    /// Prints a full name in the title case, reads either a short or full name in any case.
    LongMonthName,
    /// Abbreviated day of the week names.
    ///
    /// Prints a three-letter-long name in the title case, reads the same name in any case.
    ShortWeekdayName,
    /// Full day of the week names.
    ///
    /// Prints a full name in the title case, reads either a short or full name in any case.
    LongWeekdayName,
    /// AM/PM.
    ///
    /// Prints in lower case, reads in any case.
    LowerAmPm,
    /// AM/PM.
    ///
    /// Prints in upper case, reads in any case.
    UpperAmPm,
    /// Timezone name.
    ///
    /// It does not support parsing, its use in the parser is an immediate failure.
    TimezoneName,
    /// Offset from the local time to UTC (`+09:00` or `-04:00` or `+00:00`).
    ///
    /// In the parser, the colon can be omitted and/or surrounded with any amount of whitespaces.
    /// The offset is limited from `-24:00` to `+24:00`, which is same to `FixedOffset`'s range.
    TimezoneOffset,
    /// Offset from the local time to UTC (`+09:00` or `-04:00` or `Z`).
    ///
    /// In the parser, the colon can be omitted and/or surrounded with any amount of whitespaces,
    /// and `Z` can be either in upper case or in lower case.
    /// The offset is limited from `-24:00` to `+24:00`, which is same to `FixedOffset`'s range.
    TimezoneOffsetZ,
}

/// A single formatting item. This is used for both formatting and parsing.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Item<'a> {
    /// A literally printed and parsed text.
    Literal(&'a str),
    /// Whitespace. Prints literally but reads zero or more whitespace.
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

/// Tries to format given arguments with given formatting items.
/// Internally used by `DelayedFormat`.
pub fn format<'a, I>(w: &mut fmt::Formatter, date: Option<&NaiveDate>, time: Option<&NaiveTime>,
                     off: Option<&(String, Duration)>, items: I) -> fmt::Result
        where I: Iterator<Item=Item<'a>> {
    // full and abbreviated month and weekday names
    static SHORT_MONTHS: [&'static str; 12] =
        ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
    static LONG_MONTHS: [&'static str; 12] =
        ["January", "February", "March", "April", "May", "June",
         "July", "August", "September", "October", "November", "December"];
    static SHORT_WEEKDAYS: [&'static str; 7] =
        ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
    static LONG_WEEKDAYS: [&'static str; 7] =
        ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"];

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
                            SHORT_WEEKDAYS[d.weekday().num_days_from_monday() as usize])),
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

/// An error from the `parse` function.
#[derive(Debug, Clone, PartialEq, Copy)]
pub struct ParseError(ParseErrorKind);

#[derive(Debug, Clone, PartialEq, Copy)]
enum ParseErrorKind {
    /// Given field is out of permitted range.
    OutOfRange,

    /// There is no possible date and time value with given set of fields.
    ///
    /// This does not include the out-of-range conditions, which are trivially invalid.
    /// It includes the case that there are one or more fields that are inconsistent to each other.
    Impossible,

    /// Given set of fields is not enough to make a requested date and time value.
    ///
    /// Note that there *may* be a case that given fields constrain the possible values so much
    /// that there is a unique possible value. Chrono only tries to be correct for
    /// most useful sets of fields however, as such constraint solving can be expensive.
    NotEnough,

    /// The input string has some invalid character sequence for given formatting items.
    Invalid,

    /// The input string has been prematurely ended.
    TooShort,

    /// All formatting items have been read but there is a remaining input.
    TooLong,

    /// There was an error on the formatting string, or there were non-supported formating items.
    BadFormat,
}

/// Same to `Result<T, ParseError>`.
pub type ParseResult<T> = Result<T, ParseError>;

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.description().fmt(f)
    }
}

impl Error for ParseError {
    fn description(&self) -> &str {
        match self.0 {
            ParseErrorKind::OutOfRange => "input is out of range",
            ParseErrorKind::Impossible => "no possible date and time matching input",
            ParseErrorKind::NotEnough => "input is not enough for unique date and time",
            ParseErrorKind::Invalid => "input contains invalid characters",
            ParseErrorKind::TooShort => "premature end of input",
            ParseErrorKind::TooLong => "trailing input",
            ParseErrorKind::BadFormat => "bad or unsupported format string",
        }
    }
}

// to be used in this module and submodules
const OUT_OF_RANGE: ParseError = ParseError(ParseErrorKind::OutOfRange);
const IMPOSSIBLE:   ParseError = ParseError(ParseErrorKind::Impossible);
const NOT_ENOUGH:   ParseError = ParseError(ParseErrorKind::NotEnough);
const INVALID:      ParseError = ParseError(ParseErrorKind::Invalid);
const TOO_SHORT:    ParseError = ParseError(ParseErrorKind::TooShort);
const TOO_LONG:     ParseError = ParseError(ParseErrorKind::TooLong);
const BAD_FORMAT:   ParseError = ParseError(ParseErrorKind::BadFormat);

/// Tries to parse given string into `parsed` with given formatting items.
/// Returns `Ok` when the entire string has been parsed (otherwise `parsed` should not be used).
/// There should be no trailing string after parsing; use a stray `Item::Space` to trim whitespaces.
///
/// This particular date and time parser is:
///
/// - Greedy. It will consume the longest possible prefix.
///   For example, `April` is always consumed entirely when the long month name is requested;
///   it equally accepts `Apr`, but prefers the longer prefix in this case.
/// - Padding-agnostic (for numeric items). The `Pad` field is completely ignored,
///   so one can prepend any number of whitespace then any number of zeroes before numbers.
/// - (Still) obeying the intrinsic parsing width. This allows, for example, parsing `HHMMSS`.
pub fn parse<'a, I>(parsed: &mut Parsed, mut s: &str, items: I) -> ParseResult<()>
        where I: Iterator<Item=Item<'a>> {
    // lowercased month and weekday names
    static LONG_MONTHS: [&'static str; 12] =
        ["january", "february", "march", "april", "may", "june",
         "july", "august", "september", "october", "november", "december"];
    static LONG_WEEKDAYS: [&'static str; 7] =
        ["monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"];

    // tries to parse the month index (0 through 11) with the first three ASCII letters.
    fn parse_short_month(s: &str) -> ParseResult<u8> {
        if s.len() < 3 { return Err(TOO_SHORT); }
        let s = s.as_bytes();
        match [s[0] | 32, s[1] | 32, s[2] | 32] {
            [b'j',b'a',b'n'] => Ok(0),
            [b'f',b'e',b'b'] => Ok(1),
            [b'm',b'a',b'r'] => Ok(2),
            [b'a',b'p',b'r'] => Ok(3),
            [b'm',b'a',b'y'] => Ok(4),
            [b'j',b'u',b'n'] => Ok(5),
            [b'j',b'u',b'l'] => Ok(6),
            [b'a',b'u',b'g'] => Ok(7),
            [b's',b'e',b'p'] => Ok(8),
            [b'o',b'c',b't'] => Ok(9),
            [b'n',b'o',b'v'] => Ok(10),
            [b'd',b'e',b'c'] => Ok(11),
            _ => Err(INVALID)
        }
    }

    // tries to parse the weekday with the first three ASCII letters.
    fn parse_short_weekday(s: &str) -> ParseResult<Weekday> {
        if s.len() < 3 { return Err(TOO_SHORT); }
        let s = s.as_bytes();
        match [s[0] | 32, s[1] | 32, s[2] | 32] {
            [b'm',b'o',b'n'] => Ok(Weekday::Mon),
            [b't',b'u',b'e'] => Ok(Weekday::Tue),
            [b'w',b'e',b'd'] => Ok(Weekday::Wed),
            [b't',b'h',b'u'] => Ok(Weekday::Thu),
            [b'f',b'r',b'i'] => Ok(Weekday::Fri),
            [b's',b'a',b't'] => Ok(Weekday::Sat),
            [b's',b'u',b'n'] => Ok(Weekday::Sun),
            _ => Err(INVALID)
        }
    }

    // tries to consume `\s*[-+]\d\d[\s:]*\d\d` and return an offset in seconds
    fn parse_timezone_offset(mut s: &str, allow_zulu: bool) -> ParseResult<(&str, i32)> {
        s = s.trim_left();

        // + or -, or Z/z if `allow_zulu` is true
        let negative = match s.as_bytes().first() {
            Some(&b'+') => false,
            Some(&b'-') => true,
            Some(&b'z') | Some(&b'Z') if allow_zulu => return Ok((&s[1..], 0)),
            Some(_) => return Err(INVALID),
            None => return Err(TOO_SHORT),
        };
        s = &s[1..];

        // hours (00--24, where 24 is allowed only with 24:00)
        // the range check happens later for this reason.
        let hours = match s.as_bytes() {
            [h1 @ b'0'...b'2', h2 @ b'0'...b'9', ..] => ((h1 - b'0') * 10 + (h2 - b'0')) as i32,
            [b'3'...b'9', b'0'...b'9', ..] => return Err(OUT_OF_RANGE),
            [] | [_] => return Err(TOO_SHORT),
            _ => return Err(INVALID),
        };
        s = &s[2..];

        // optional colons and whitespaces
        s = s.trim_left_matches(|&: c: char| c == ':' || c.is_whitespace());

        // minutes (00--59)
        let minutes = match s.as_bytes() {
            [m1 @ b'0'...b'5', m2 @ b'0'...b'9', ..] => ((m1 - b'0') * 10 + (m2 - b'0')) as i32,
            [b'6'...b'9', b'0'...b'9', ..] => return Err(OUT_OF_RANGE),
            [] | [_] => return Err(TOO_SHORT),
            _ => return Err(INVALID),
        };
        s = &s[2..];

        let seconds = hours * 3600 + minutes * 60;
        if seconds > 86400 { return Err(OUT_OF_RANGE); } // range check for hours
        Ok((s, if negative {-seconds} else {seconds}))
    }

    // compares two slice case-insensitively (in ASCII).
    // assumes the `pattern` is already converted to lower case.
    fn equals_ascii_nocase(s: &str, pattern: &str) -> bool {
        iter::order::equals(s.as_bytes().iter().map(|&: &c| match c { b'A'...b'Z' => c + 32,
                                                                      _ => c }),
                            pattern.as_bytes().iter().cloned())
    }

    for item in items {
        match item {
            Item::Literal(prefix) => {
                if s.len() < prefix.len() { return Err(TOO_SHORT); }
                if !s.starts_with(prefix) { return Err(INVALID); }
                s = &s[prefix.len()..];
            }

            Item::Space(_) => {
                s = s.trim_left();
            }

            Item::Numeric(spec, _pad) => {
                use self::Numeric::*;

                fn set_weekday_with_num_days_from_sunday(p: &mut Parsed,
                                                         v: i64) -> ParseResult<()> {
                    p.set_weekday(match v {
                        0 => Weekday::Sun, 1 => Weekday::Mon, 2 => Weekday::Tue,
                        3 => Weekday::Wed, 4 => Weekday::Thu, 5 => Weekday::Fri,
                        6 => Weekday::Sat, _ => return Err(OUT_OF_RANGE)
                    })
                }

                fn set_weekday_with_number_from_monday(p: &mut Parsed, v: i64) -> ParseResult<()> {
                    p.set_weekday(match v {
                        1 => Weekday::Mon, 2 => Weekday::Tue, 3 => Weekday::Wed,
                        4 => Weekday::Thu, 5 => Weekday::Fri, 6 => Weekday::Sat,
                        7 => Weekday::Sun, _ => return Err(OUT_OF_RANGE)
                    })
                }

                let (width, set): (usize, fn(&mut Parsed, i64) -> ParseResult<()>) = match spec {
                    Year           => (4, Parsed::set_year),
                    YearDiv100     => (2, Parsed::set_year_div_100),
                    YearMod100     => (2, Parsed::set_year_mod_100),
                    IsoYear        => (4, Parsed::set_isoyear),
                    IsoYearDiv100  => (2, Parsed::set_isoyear_div_100),
                    IsoYearMod100  => (2, Parsed::set_isoyear_mod_100),
                    Month          => (2, Parsed::set_month),
                    Day            => (2, Parsed::set_day),
                    WeekFromSun    => (2, Parsed::set_week_from_sun),
                    WeekFromMon    => (2, Parsed::set_week_from_mon),
                    IsoWeek        => (2, Parsed::set_isoweek),
                    NumDaysFromSun => (1, set_weekday_with_num_days_from_sunday),
                    WeekdayFromMon => (1, set_weekday_with_number_from_monday),
                    Ordinal        => (3, Parsed::set_ordinal),
                    Hour           => (2, Parsed::set_hour),
                    Hour12         => (2, Parsed::set_hour12),
                    Minute         => (2, Parsed::set_minute),
                    Second         => (2, Parsed::set_second),
                    Nanosecond     => (9, Parsed::set_nanosecond),
                    Timestamp      => (usize::MAX, Parsed::set_timestamp),
                };

                // strip zero or more whitespaces
                s = s.trim_left();

                // scan digits
                let mut win = s.as_bytes();
                if win.len() > width { win = &win[..width]; }
                let upto = win.iter().position(|&c| c < b'0' || b'9' < c).unwrap_or(win.len());
                if upto == 0 { // no digits detected
                    return Err(if win.is_empty() {TOO_SHORT} else {INVALID});
                }

                // overflow is possible with `Timestamp` for example
                // we have no other error cause, and can safely replace the error to our version
                let v = try!(s[..upto].parse().map_err(|_| OUT_OF_RANGE));
                try!(set(parsed, v));
                s = &s[upto..];
            }

            Item::Fixed(spec) => {
                use self::Fixed::*;

                match spec {
                    ShortMonthName => {
                        let month0 = try!(parse_short_month(s));
                        try!(parsed.set_month(month0 as i64 + 1));
                        s = &s[3..];
                    }

                    LongMonthName => {
                        let month0 = try!(parse_short_month(s));
                        let long = LONG_MONTHS[month0 as usize];
                        // three-letter abbreviation is a prefix of the corresponding long name
                        if s.len() >= long.len() && equals_ascii_nocase(&s[3..long.len()],
                                                                        &long[3..]) {
                            // *optionally* consume the long form if possible
                            s = &s[long.len()..];
                        } else {
                            s = &s[3..];
                        }
                        try!(parsed.set_month(month0 as i64 + 1));
                    }

                    ShortWeekdayName => {
                        let weekday = try!(parse_short_weekday(s));
                        try!(parsed.set_weekday(weekday));
                        s = &s[3..];
                    }

                    LongWeekdayName => {
                        let weekday = try!(parse_short_weekday(s));
                        let long = LONG_WEEKDAYS[weekday.num_days_from_monday() as usize];
                        // three-letter abbreviation is a prefix of the corresponding long name
                        if s.len() >= long.len() && equals_ascii_nocase(&s[3..long.len()],
                                                                        &long[3..]) {
                            // *optionally* consume the long form if possible
                            s = &s[long.len()..];
                        } else {
                            s = &s[3..];
                        }
                        try!(parsed.set_weekday(weekday));
                    }

                    LowerAmPm | UpperAmPm => {
                        if s.len() < 2 { return Err(TOO_SHORT); }
                        let ampm = match [s.as_bytes()[0] | 32, s.as_bytes()[1] | 32] {
                            [b'a',b'm'] => false,
                            [b'p',b'm'] => true,
                            _ => return Err(INVALID)
                        };
                        try!(parsed.set_ampm(ampm));
                        s = &s[2..];
                    }

                    TimezoneName => return Err(BAD_FORMAT),

                    TimezoneOffset | TimezoneOffsetZ => {
                        let allow_zulu = spec == TimezoneOffsetZ;
                        let (s_, offset) = try!(parse_timezone_offset(s, allow_zulu));
                        s = s_;
                        try!(parsed.set_offset(offset as i64));
                    }
                }
            }

            Item::Error => {
                return Err(BAD_FORMAT);
            }
        }
    }

    // if there are trailling chars, it is an error
    if !s.is_empty() {
        Err(TOO_LONG)
    } else {
        Ok(())
    }
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

pub mod parsed;

pub mod strftime;

#[cfg(test)]
#[test]
fn test_parse() {
    macro_rules! check {
        ($fmt:expr, $items:expr; $err:expr) => ({
            assert_eq!(parse(&mut Parsed::new(), $fmt, $items.iter().cloned()), Err($err));
        });

        ($fmt:expr, $items:expr; $($k:ident: $v:expr),*) => ({
            let mut parsed = Parsed::new();
            assert_eq!(parse(&mut parsed, $fmt, $items.iter().cloned()), Ok(()));
            assert_eq!(parsed, Parsed { $($k: Some($v),)* ..Parsed::new() });
        });
    }

    // empty string
    check!("",  []; );
    check!(" ", []; TOO_LONG);
    check!("a", []; TOO_LONG);

    // whitespaces
    check!("",          [sp!("")]; );
    check!(" ",         [sp!("")]; );
    check!("\t",        [sp!("")]; );
    check!(" \n\r  \n", [sp!("")]; );
    check!("a",         [sp!("")]; TOO_LONG);

    // literal
    check!("",    [lit!("a")]; TOO_SHORT);
    check!(" ",   [lit!("a")]; INVALID);
    check!("a",   [lit!("a")]; );
    check!("aa",  [lit!("a")]; TOO_LONG);
    check!("A",   [lit!("a")]; INVALID);
    check!("xy",  [lit!("xy")]; );
    check!("xy",  [lit!("x"), lit!("y")]; );
    check!("x y", [lit!("x"), lit!("y")]; INVALID);
    check!("xy",  [lit!("x"), sp!(""), lit!("y")]; );
    check!("x y", [lit!("x"), sp!(""), lit!("y")]; );

    // numeric
    check!("1987",        [num!(Year)]; year_div_100: 19, year_mod_100: 87);
    check!("1987 ",       [num!(Year)]; TOO_LONG);
    check!("0x12",        [num!(Year)]; TOO_LONG); // `0` is parsed
    check!("x123",        [num!(Year)]; INVALID);
    check!("2015",        [num!(Year)]; year_div_100: 20, year_mod_100: 15);
    check!("0000",        [num!(Year)]; year_div_100:  0, year_mod_100:  0);
    check!("9999",        [num!(Year)]; year_div_100: 99, year_mod_100: 99);
    check!(" \t987",      [num!(Year)]; year_div_100:  9, year_mod_100: 87);
    check!("5",           [num!(Year)]; year_div_100:  0, year_mod_100:  5);
    check!("-42",         [num!(Year)]; INVALID);
    check!("+42",         [num!(Year)]; INVALID);
    check!("5\0",         [num!(Year)]; TOO_LONG);
    check!("\05",         [num!(Year)]; INVALID);
    check!("",            [num!(Year)]; TOO_SHORT);
    check!("12345",       [num!(Year), lit!("5")]; year_div_100: 12, year_mod_100: 34);
    check!("12345",       [nums!(Year), lit!("5")]; year_div_100: 12, year_mod_100: 34);
    check!("12345",       [num0!(Year), lit!("5")]; year_div_100: 12, year_mod_100: 34);
    check!("12341234",    [num!(Year), num!(Year)]; year_div_100: 12, year_mod_100: 34);
    check!("1234 1234",   [num!(Year), num!(Year)]; year_div_100: 12, year_mod_100: 34);
    check!("1234 1235",   [num!(Year), num!(Year)]; IMPOSSIBLE);
    check!("1234 1234",   [num!(Year), lit!("x"), num!(Year)]; INVALID);
    check!("1234x1234",   [num!(Year), lit!("x"), num!(Year)]; year_div_100: 12, year_mod_100: 34);
    check!("1234xx1234",  [num!(Year), lit!("x"), num!(Year)]; INVALID);
    check!("1234 x 1234", [num!(Year), lit!("x"), num!(Year)]; INVALID);

    // various numeric fields
    check!("1234 5678",
           [num!(Year), num!(IsoYear)];
           year_div_100: 12, year_mod_100: 34, isoyear_div_100: 56, isoyear_mod_100: 78);
    check!("12 34 56 78",
           [num!(YearDiv100), num!(YearMod100), num!(IsoYearDiv100), num!(IsoYearMod100)];
           year_div_100: 12, year_mod_100: 34, isoyear_div_100: 56, isoyear_mod_100: 78);
    check!("1 2 3 4 5 6",
           [num!(Month), num!(Day), num!(WeekFromSun), num!(WeekFromMon), num!(IsoWeek),
            num!(NumDaysFromSun)];
           month: 1, day: 2, week_from_sun: 3, week_from_mon: 4, isoweek: 5, weekday: Weekday::Sat);
    check!("7 89 01",
           [num!(WeekdayFromMon), num!(Ordinal), num!(Hour12)];
           weekday: Weekday::Sun, ordinal: 89, hour_mod_12: 1);
    check!("23 45 6 78901234 567890123",
           [num!(Hour), num!(Minute), num!(Second), num!(Nanosecond), num!(Timestamp)];
           hour_div_12: 1, hour_mod_12: 11, minute: 45, second: 6, nanosecond: 78_901_234,
           timestamp: 567_890_123);

    // fixed: month and weekday names
    check!("apr",       [fix!(ShortMonthName)]; month: 4);
    check!("Apr",       [fix!(ShortMonthName)]; month: 4);
    check!("APR",       [fix!(ShortMonthName)]; month: 4);
    check!("ApR",       [fix!(ShortMonthName)]; month: 4);
    check!("April",     [fix!(ShortMonthName)]; TOO_LONG); // `Apr` is parsed
    check!("A",         [fix!(ShortMonthName)]; TOO_SHORT);
    check!("Sol",       [fix!(ShortMonthName)]; INVALID);
    check!("Apr",       [fix!(LongMonthName)]; month: 4);
    check!("Apri",      [fix!(LongMonthName)]; TOO_LONG); // `Apr` is parsed
    check!("April",     [fix!(LongMonthName)]; month: 4);
    check!("Aprill",    [fix!(LongMonthName)]; TOO_LONG);
    check!("Aprill",    [fix!(LongMonthName), lit!("l")]; month: 4);
    check!("Aprl",      [fix!(LongMonthName), lit!("l")]; month: 4);
    check!("April",     [fix!(LongMonthName), lit!("il")]; TOO_SHORT); // do not backtrack
    check!("thu",       [fix!(ShortWeekdayName)]; weekday: Weekday::Thu);
    check!("Thu",       [fix!(ShortWeekdayName)]; weekday: Weekday::Thu);
    check!("THU",       [fix!(ShortWeekdayName)]; weekday: Weekday::Thu);
    check!("tHu",       [fix!(ShortWeekdayName)]; weekday: Weekday::Thu);
    check!("Thursday",  [fix!(ShortWeekdayName)]; TOO_LONG); // `Thu` is parsed
    check!("T",         [fix!(ShortWeekdayName)]; TOO_SHORT);
    check!("The",       [fix!(ShortWeekdayName)]; INVALID);
    check!("Nop",       [fix!(ShortWeekdayName)]; INVALID);
    check!("Thu",       [fix!(LongWeekdayName)]; weekday: Weekday::Thu);
    check!("Thur",      [fix!(LongWeekdayName)]; TOO_LONG); // `Thu` is parsed
    check!("Thurs",     [fix!(LongWeekdayName)]; TOO_LONG); // ditto
    check!("Thursday",  [fix!(LongWeekdayName)]; weekday: Weekday::Thu);
    check!("Thursdays", [fix!(LongWeekdayName)]; TOO_LONG);
    check!("Thursdays", [fix!(LongWeekdayName), lit!("s")]; weekday: Weekday::Thu);
    check!("Thus",      [fix!(LongWeekdayName), lit!("s")]; weekday: Weekday::Thu);
    check!("Thursday",  [fix!(LongWeekdayName), lit!("rsday")]; TOO_SHORT); // do not backtrack

    // fixed: am/pm
    check!("am",  [fix!(LowerAmPm)]; hour_div_12: 0);
    check!("pm",  [fix!(LowerAmPm)]; hour_div_12: 1);
    check!("AM",  [fix!(LowerAmPm)]; hour_div_12: 0);
    check!("PM",  [fix!(LowerAmPm)]; hour_div_12: 1);
    check!("am",  [fix!(UpperAmPm)]; hour_div_12: 0);
    check!("pm",  [fix!(UpperAmPm)]; hour_div_12: 1);
    check!("AM",  [fix!(UpperAmPm)]; hour_div_12: 0);
    check!("PM",  [fix!(UpperAmPm)]; hour_div_12: 1);
    check!("Am",  [fix!(LowerAmPm)]; hour_div_12: 0);
    check!(" Am", [fix!(LowerAmPm)]; INVALID);
    check!("ame", [fix!(LowerAmPm)]; TOO_LONG); // `am` is parsed
    check!("a",   [fix!(LowerAmPm)]; TOO_SHORT);
    check!("p",   [fix!(LowerAmPm)]; TOO_SHORT);
    check!("x",   [fix!(LowerAmPm)]; TOO_SHORT);
    check!("xx",  [fix!(LowerAmPm)]; INVALID);
    check!("",    [fix!(LowerAmPm)]; TOO_SHORT);

    // fixed: timezone offsets
    check!("+00:00",    [fix!(TimezoneOffset)]; offset: 0);
    check!("-00:00",    [fix!(TimezoneOffset)]; offset: 0);
    check!("+00:01",    [fix!(TimezoneOffset)]; offset: 60);
    check!("-00:01",    [fix!(TimezoneOffset)]; offset: -60);
    check!("+00:30",    [fix!(TimezoneOffset)]; offset: 30 * 60);
    check!("-00:30",    [fix!(TimezoneOffset)]; offset: -30 * 60);
    check!("+04:56",    [fix!(TimezoneOffset)]; offset: 296 * 60);
    check!("-04:56",    [fix!(TimezoneOffset)]; offset: -296 * 60);
    check!("+24:00",    [fix!(TimezoneOffset)]; offset: 24 * 60 * 60);
    check!("-24:00",    [fix!(TimezoneOffset)]; offset: -24 * 60 * 60);
    check!("+24:01",    [fix!(TimezoneOffset)]; OUT_OF_RANGE);
    check!("-24:01",    [fix!(TimezoneOffset)]; OUT_OF_RANGE);
    check!("+00:59",    [fix!(TimezoneOffset)]; offset: 59 * 60);
    check!("+00:60",    [fix!(TimezoneOffset)]; OUT_OF_RANGE);
    check!("+00:99",    [fix!(TimezoneOffset)]; OUT_OF_RANGE);
    check!("+99:00",    [fix!(TimezoneOffset)]; OUT_OF_RANGE);
    check!("#12:34",    [fix!(TimezoneOffset)]; INVALID);
    check!("12:34",     [fix!(TimezoneOffset)]; INVALID);
    check!("+12:34 ",   [fix!(TimezoneOffset)]; TOO_LONG);
    check!(" +12:34",   [fix!(TimezoneOffset)]; offset: 754 * 60);
    check!("\t -12:34", [fix!(TimezoneOffset)]; offset: -754 * 60);
    check!("",          [fix!(TimezoneOffset)]; TOO_SHORT);
    check!("+",         [fix!(TimezoneOffset)]; TOO_SHORT);
    check!("+1",        [fix!(TimezoneOffset)]; TOO_SHORT);
    check!("+12",       [fix!(TimezoneOffset)]; TOO_SHORT);
    check!("+123",      [fix!(TimezoneOffset)]; TOO_SHORT);
    check!("+1234",     [fix!(TimezoneOffset)]; offset: 754 * 60);
    check!("+12345",    [fix!(TimezoneOffset)]; TOO_LONG);
    check!("+12345",    [fix!(TimezoneOffset), num!(Day)]; offset: 754 * 60, day: 5);
    check!("Z",         [fix!(TimezoneOffset)]; INVALID);
    check!("z",         [fix!(TimezoneOffset)]; INVALID);
    check!("Z",         [fix!(TimezoneOffsetZ)]; offset: 0);
    check!("z",         [fix!(TimezoneOffsetZ)]; offset: 0);
    check!("Y",         [fix!(TimezoneOffsetZ)]; INVALID);
    check!("Zulu",      [fix!(TimezoneOffsetZ), lit!("ulu")]; offset: 0);
    check!("zulu",      [fix!(TimezoneOffsetZ), lit!("ulu")]; offset: 0);
    check!("+1234ulu",  [fix!(TimezoneOffsetZ), lit!("ulu")]; offset: 754 * 60);
    check!("+12:34ulu", [fix!(TimezoneOffsetZ), lit!("ulu")]; offset: 754 * 60);
    check!("???",       [fix!(TimezoneName)]; BAD_FORMAT); // not allowed

    // some practical examples
    check!("2015-02-04T14:37:05+09:00",
           [num!(Year), lit!("-"), num!(Month), lit!("-"), num!(Day), lit!("T"),
            num!(Hour), lit!(":"), num!(Minute), lit!(":"), num!(Second), fix!(TimezoneOffset)];
           year_div_100: 20, year_mod_100: 15, month: 2, day: 4,
           hour_div_12: 1, hour_mod_12: 2, minute: 37, second: 5, offset: 32400);
    check!("Mon, 10 Jun 2013 09:32:37 GMT",
           [fix!(ShortWeekdayName), lit!(","), sp!(" "), num!(Day), sp!(" "),
            fix!(ShortMonthName), sp!(" "), num!(Year), sp!(" "), num!(Hour), lit!(":"),
            num!(Minute), lit!(":"), num!(Second), sp!(" "), lit!("GMT")];
           year_div_100: 20, year_mod_100: 13, month: 6, day: 10, weekday: Weekday::Mon,
           hour_div_12: 0, hour_mod_12: 9, minute: 32, second: 37);
    check!("20060102150405",
           [num!(Year), num!(Month), num!(Day), num!(Hour), num!(Minute), num!(Second)];
           year_div_100: 20, year_mod_100: 6, month: 1, day: 2,
           hour_div_12: 1, hour_mod_12: 3, minute: 4, second: 5);
    check!("3:14PM",
           [num!(Hour12), lit!(":"), num!(Minute), fix!(LowerAmPm)];
           hour_div_12: 1, hour_mod_12: 3, minute: 14);
    check!("12345678901234.56789",
           [num!(Timestamp), lit!("."), num!(Nanosecond)];
           nanosecond: 56_789, timestamp: 12_345_678_901_234);
}

