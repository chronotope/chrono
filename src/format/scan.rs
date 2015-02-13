// This is a part of rust-chrono.
// Copyright (c) 2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * Various scanning routines for the parser.
 */

use std::iter;
use std::num::Int;

use Weekday;
use super::{ParseResult, TOO_SHORT, INVALID, OUT_OF_RANGE};

/// Returns true when two slices are equal case-insensitively (in ASCII).
/// Assumes that the `pattern` is already converted to lower case.
fn equals(s: &str, pattern: &str) -> bool {
    iter::order::equals(s.as_bytes().iter().map(|&c| match c { b'A'...b'Z' => c + 32, _ => c }),
                        pattern.as_bytes().iter().cloned())
}

/// Tries to parse the non-negative number from `min` to `max` digits.
///
/// If `left_aligned` is true, the number is assumed to be followed by zero digits
/// so that the padded digits are exactly `max` digits long (like fractions).
/// For example, given `max` of 8, `123` is parsed as 123 when right-aligned
/// and 12300000 when left-aligned.
///
/// The absence of digits at all is an unconditional error.
/// More than `max` digits are consumed up to the first `max` digits.
/// Any number that does not fit in `i64` is an error.
pub fn number(s: &str, min: usize, max: usize, left_aligned: bool) -> ParseResult<(&str, i64)> {
    assert!(min <= max);

    // limit `s` to given number of digits
    let mut window = s.as_bytes();
    if window.len() > max { window = &window[..max]; }

    // scan digits
    let upto = window.iter().position(|&c| c < b'0' || b'9' < c).unwrap_or(window.len());
    if upto < min {
        return Err(if window.is_empty() {TOO_SHORT} else {INVALID});
    }

    // we can overflow here, which is the only possible cause of error from `parse`.
    let mut v: i64 = try!(s[..upto].parse().map_err(|_| OUT_OF_RANGE));

    // scale the number if it is left-aligned. this can also overflow.
    if left_aligned {
        for _ in upto..max {
            v = try!(v.checked_mul(10).ok_or(OUT_OF_RANGE));
        }
    }

    Ok((&s[upto..], v))
}

/// Tries to parse the month index (0 through 11) with the first three ASCII letters.
pub fn short_month0(s: &str) -> ParseResult<(&str, u8)> {
    if s.len() < 3 { return Err(TOO_SHORT); }
    let buf = s.as_bytes();
    let month0 = match [buf[0] | 32, buf[1] | 32, buf[2] | 32] {
        [b'j',b'a',b'n'] => 0,
        [b'f',b'e',b'b'] => 1,
        [b'm',b'a',b'r'] => 2,
        [b'a',b'p',b'r'] => 3,
        [b'm',b'a',b'y'] => 4,
        [b'j',b'u',b'n'] => 5,
        [b'j',b'u',b'l'] => 6,
        [b'a',b'u',b'g'] => 7,
        [b's',b'e',b'p'] => 8,
        [b'o',b'c',b't'] => 9,
        [b'n',b'o',b'v'] => 10,
        [b'd',b'e',b'c'] => 11,
        _ => return Err(INVALID)
    };
    Ok((&s[3..], month0))
}

/// Tries to parse the weekday with the first three ASCII letters.
pub fn short_weekday(s: &str) -> ParseResult<(&str, Weekday)> {
    if s.len() < 3 { return Err(TOO_SHORT); }
    let buf = s.as_bytes();
    let weekday = match [buf[0] | 32, buf[1] | 32, buf[2] | 32] {
        [b'm',b'o',b'n'] => Weekday::Mon,
        [b't',b'u',b'e'] => Weekday::Tue,
        [b'w',b'e',b'd'] => Weekday::Wed,
        [b't',b'h',b'u'] => Weekday::Thu,
        [b'f',b'r',b'i'] => Weekday::Fri,
        [b's',b'a',b't'] => Weekday::Sat,
        [b's',b'u',b'n'] => Weekday::Sun,
        _ => return Err(INVALID)
    };
    Ok((&s[3..], weekday))
}

/// Tries to parse the month index (0 through 11) with short or long month names.
/// It prefers long month names to short month names when both are possible.
pub fn short_or_long_month0(s: &str) -> ParseResult<(&str, u8)> {
    // lowercased month names, minus first three chars
    static LONG_MONTH_SUFFIXES: [&'static str; 12] =
        ["uary", "ruary", "ch", "il", "", "e", "y", "ust", "tember", "ober", "ember", "ember"];

    let (mut s, month0) = try!(short_month0(s));

    // tries to consume the suffix if possible
    let suffix = LONG_MONTH_SUFFIXES[month0 as usize];
    if s.len() >= suffix.len() && equals(&s[..suffix.len()], suffix) {
        s = &s[suffix.len()..];
    }

    Ok((s, month0))
}

/// Tries to parse the weekday with short or long weekday names.
/// It prefers long weekday names to short weekday names when both are possible.
pub fn short_or_long_weekday(s: &str) -> ParseResult<(&str, Weekday)> {
    // lowercased weekday names, minus first three chars
    static LONG_WEEKDAY_SUFFIXES: [&'static str; 7] =
        ["day", "sday", "nesday", "rsday", "day", "urday", "sunday"];

    let (mut s, weekday) = try!(short_weekday(s));

    // tries to consume the suffix if possible
    let suffix = LONG_WEEKDAY_SUFFIXES[weekday.num_days_from_monday() as usize];
    if s.len() >= suffix.len() && equals(&s[..suffix.len()], suffix) {
        s = &s[suffix.len()..];
    }

    Ok((s, weekday))
}

/// Consumes any number (including zero) of colon or spaces.
pub fn colon_or_space(s: &str) -> ParseResult<&str> {
    Ok(s.trim_left_matches(|c: char| c == ':' || c.is_whitespace()))
}

/// Tries to parse `[-+]\d\d` continued by `\d\d`. Return an offset in seconds if possible.
///
/// The additional `colon` may be used to parse a mandatory or optional `:`
/// between hours and minutes, and should return either a new suffix or `None` when parsing fails.
pub fn timezone_offset<F>(mut s: &str, mut colon: F) -> ParseResult<(&str, i32)>
        where F: FnMut(&str) -> ParseResult<&str> {
    let negative = match s.as_bytes().first() {
        Some(&b'+') => false,
        Some(&b'-') => true,
        Some(_) => return Err(INVALID),
        None => return Err(TOO_SHORT),
    };
    s = &s[1..];

    // hours (00--99)
    let hours = match s.as_bytes() {
        [h1 @ b'0'...b'9', h2 @ b'0'...b'9', ..] => ((h1 - b'0') * 10 + (h2 - b'0')) as i32,
        [] | [_] => return Err(TOO_SHORT),
        _ => return Err(INVALID),
    };
    s = &s[2..];

    // colons (and possibly other separators)
    s = try!(colon(s));

    // minutes (00--59)
    let minutes = match s.as_bytes() {
        [m1 @ b'0'...b'5', m2 @ b'0'...b'9', ..] => ((m1 - b'0') * 10 + (m2 - b'0')) as i32,
        [b'6'...b'9', b'0'...b'9', ..] => return Err(OUT_OF_RANGE),
        [] | [_] => return Err(TOO_SHORT),
        _ => return Err(INVALID),
    };
    s = &s[2..];

    let seconds = hours * 3600 + minutes * 60;
    Ok((s, if negative {-seconds} else {seconds}))
}

/// Same to `timezone_offset` but also allows for `z`/`Z` which is same to `+00:00`.
pub fn timezone_offset_zulu<F>(s: &str, colon: F) -> ParseResult<(&str, i32)>
        where F: FnMut(&str) -> ParseResult<&str> {
    match s.as_bytes().first() {
        Some(&b'z') | Some(&b'Z') => Ok((&s[1..], 0)),
        _ => timezone_offset(s, colon),
    }
}

