// This is a part of rust-chrono.
// Copyright (c) 2014-2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
 * Formatting utilities for date and time.
 */

use std::fmt;

use {Datelike, Timelike};
use duration::Duration;
use offset::Offset;
use naive::date::NaiveDate;
use naive::time::NaiveTime;

/// The internal workhouse for `DelayedFormat`.
fn format(w: &mut fmt::Formatter, date: Option<&NaiveDate>, time: Option<&NaiveTime>,
          off: Option<&(String, Duration)>, fmt: &str) -> fmt::Result {
    static SHORT_MONTHS: [&'static str; 12] =
        ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
    static LONG_MONTHS: [&'static str; 12] =
        ["January", "February", "March", "April", "May", "June",
         "July", "August", "September", "October", "November", "December"];
    static SHORT_WEEKDAYS: [&'static str; 7] =
        ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
    static LONG_WEEKDAYS: [&'static str; 7] =
        ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"];

    let mut parts = fmt.split('%');
    match parts.next() {
        Some(first) => try!(write!(w, "{}", first)),
        None => return Ok(()),
    }

    let mut last_was_percent = false;
    for part in parts {
        if last_was_percent { // `%%<part>`
            last_was_percent = false;
            try!(write!(w, "%{}", part));
            continue;
        }

        let (head, tail) = match part.slice_shift_char() {
            Some((head, tail)) => (Some(head), tail),
            None => (None, ""),
        };
        match (head, date, time, off) {
            // year
            (Some('Y'), Some(d), _, _) => try!(write!(w, "{}", d.year())),
            (Some('C'), Some(d), _, _) => try!(write!(w, "{:02}", d.year() / 100)),
            (Some('y'), Some(d), _, _) => try!(write!(w, "{:02}", d.year() % 100)),
            (Some('G'), Some(d), _, _) => try!(write!(w, "{:04}", d.isoweekdate().0)),
            (Some('g'), Some(d), _, _) => try!(write!(w, "{:02}", d.isoweekdate().0 % 100)),

            // month
            (Some('m'), Some(d), _, _) => try!(write!(w, "{:02}", d.month())),
            (Some('b'), Some(d), _, _) | (Some('h'), Some(d), _, _) =>
                try!(write!(w, "{}", SHORT_MONTHS[d.month0() as usize])),
            (Some('B'), Some(d), _, _) =>
                try!(write!(w, "{}", LONG_MONTHS[d.month0() as usize])),

            // day of month
            (Some('d'), Some(d), _, _) => try!(write!(w, "{:02}", d.day())),
            (Some('e'), Some(d), _, _) => try!(write!(w, "{:2}", d.day())),

            // week
            (Some('U'), Some(d), _, _) =>
                try!(write!(w, "{:02}", (d.ordinal() - d.weekday().num_days_from_sunday()
                                                     + 7) / 7)),
            (Some('W'), Some(d), _, _) =>
                try!(write!(w, "{:02}", (d.ordinal() - d.weekday().num_days_from_monday()
                                                     + 7) / 7)),
            (Some('V'), Some(d), _, _) => try!(write!(w, "{:02}", d.isoweekdate().1)),

            // day of week
            (Some('a'), Some(d), _, _) =>
                try!(write!(w, "{}", SHORT_WEEKDAYS[d.weekday().num_days_from_monday() as usize])),
            (Some('A'), Some(d), _, _) =>
                try!(write!(w, "{}", LONG_WEEKDAYS[d.weekday().num_days_from_monday() as usize])),
            (Some('w'), Some(d), _, _) => try!(write!(w, "{}", d.weekday().num_days_from_sunday())),
            (Some('u'), Some(d), _, _) => try!(write!(w, "{}", d.weekday().number_from_monday())),

            // day of year
            (Some('j'), Some(d), _, _) => try!(write!(w, "{:03}", d.ordinal())),

            // combined date
            (Some('D'), Some(d), _, _) | (Some('x'), Some(d), _, _) => // `%m/%d/%y`
                try!(write!(w, "{:02}/{:02}/{:02}", d.month(), d.day(), d.year() % 100)),
            (Some('F'), Some(d), _, _) => // `%Y-%m-%d'
                try!(write!(w, "{:04}-{:02}-{:02}", d.year(), d.month(), d.day())),
            (Some('v'), Some(d), _, _) => // `%e-%b-%Y'
                try!(write!(w, "{:2}-{}-{:04}", d.day(), SHORT_MONTHS[d.month0() as usize],
                                                d.year())),

            // hour
            (Some('H'), _, Some(t), _) => try!(write!(w, "{:02}", t.hour())),
            (Some('k'), _, Some(t), _) => try!(write!(w, "{:2}", t.hour())),
            (Some('I'), _, Some(t), _) => try!(write!(w, "{:02}", t.hour12().1)),
            (Some('l'), _, Some(t), _) => try!(write!(w, "{:2}", t.hour12().1)),
            (Some('P'), _, Some(t), _) =>
                try!(write!(w, "{}", if t.hour12().0 {"pm"} else {"am"})),
            (Some('p'), _, Some(t), _) =>
                try!(write!(w, "{}", if t.hour12().0 {"PM"} else {"AM"})),

            // minute
            (Some('M'), _, Some(t), _) => try!(write!(w, "{:02}", t.minute())),

            // second and below
            (Some('S'), _, Some(t), _) => try!(write!(w, "{:02}", t.second())),
            (Some('f'), _, Some(t), _) => try!(write!(w, "{:09}", t.nanosecond())),

            // combined time
            (Some('R'), _, Some(t), _) => // `%H:%M`
                try!(write!(w, "{:02}:{:02}", t.hour(), t.minute())),
            (Some('T'), _, Some(t), _) | (Some('X'), _, Some(t), _) => // `%H:%M:%S`
                try!(write!(w, "{:02}:{:02}:{:02}", t.hour(), t.minute(), t.second())),
            (Some('r'), _, Some(t), _) => { // `%I:%M:%S %p`
                let (is_pm, hour12) = t.hour12();
                try!(write!(w, "{:02}:{:02}:{:02} {}", hour12, t.minute(), t.second(),
                               if is_pm {"PM"} else {"AM"}))
            },

            // timezone
            (Some('Z'), _, _, Some(&(ref name, _))) => try!(write!(w, "{}", *name)),
            (Some('z'), _, _, Some(&(_, ref local_minus_utc))) => {
                let off = local_minus_utc.num_minutes();
                let (sign, off) = if off < 0 {('-', -off)} else {('+', off)};
                try!(write!(w, "{}{:02}{:02}", sign, off / 60, off % 60))
            },

            /*
            // timestamp
            (Some('s'), Some(d), Some(t), Some(o)) => { // XXX
                let datetime = o.from_local_datetime(&d.and_time(t.clone())).unwrap();
                try!(write!(w, "{}", datetime.num_seconds_from_unix_epoch()))
            },
            */

            // combined date and time
            (Some('c'), Some(d), Some(t), _) => // `%a %b %e %T %Y`
                try!(write!(w, "{} {} {:2} {:02}:{:02}:{:02} {:04}",
                               SHORT_WEEKDAYS[d.weekday().num_days_from_monday() as usize],
                               SHORT_MONTHS[d.month0() as usize], d.day(),
                               t.hour(), t.minute(), t.second(), d.year())),
            (Some('+'), Some(d), Some(t),
                        Some(&(_, ref local_minus_utc))) => { // `%Y-%m-%dT%H:%M:%S` plus tz
                let off = local_minus_utc.num_minutes();
                let (sign, off) = if off < 0 {('-', -off)} else {('+', off)};
                try!(write!(w, "{}-{:02}-{:02}T{:02}:{:02}:{:02}{}{:02}:{:02}",
                               d.year(), d.month(), d.day(), t.hour(), t.minute(), t.second(),
                               sign, off / 60, off % 60))
            },

            // special characters
            (Some('t'), _, _, _) => try!(write!(w, "\t")),
            (Some('n'), _, _, _) => try!(write!(w, "\n")),

            // TODO issue a detailed error if possible
            (Some(_), _, _, _) => return Err(fmt::Error),

            (None, _, _, _) => {
                // if there is the next part, a single `%` and that part should be printed
                // in verbatim. otherwise it is an error (the stray `%`).
                last_was_percent = true;
            }
        }

        try!(write!(w, "{}", tail));
    }

    if last_was_percent { // a stray `%`
        // TODO issue a detailed error if possible
        Err(fmt::Error)
    } else {
        Ok(())
    }
}

/// A *temporary* object which can be used as an argument to `format!` or others.
/// This is normally constructed via `format` methods of each date and time type.
#[derive(Show)]
pub struct DelayedFormat<'a> {
    /// The date view, if any.
    date: Option<NaiveDate>,
    /// The time view, if any.
    time: Option<NaiveTime>,
    /// The name and local-to-UTC difference for the offset (timezone), if any.
    off: Option<(String, Duration)>,
    /// The format string.
    fmt: &'a str,
}

impl<'a> DelayedFormat<'a> {
    /// Makes a new `DelayedFormat` value out of local date and time.
    pub fn new(date: Option<NaiveDate>, time: Option<NaiveTime>,
               fmt: &'a str) -> DelayedFormat<'a> {
        DelayedFormat { date: date, time: time, off: None, fmt: fmt }
    }

    /// Makes a new `DelayedFormat` value out of local date and time and UTC offset.
    pub fn new_with_offset<Off>(date: Option<NaiveDate>, time: Option<NaiveTime>,
                                offset: &Off, fmt: &'a str) -> DelayedFormat<'a>
            where Off: Offset + fmt::String {
        let name_and_diff = (offset.to_string(), offset.local_minus_utc());
        DelayedFormat { date: date, time: time, off: Some(name_and_diff), fmt: fmt }
    }
}

impl<'a> fmt::String for DelayedFormat<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ret = format(f, self.date.as_ref(), self.time.as_ref(), self.off.as_ref(), self.fmt);
        ret.map_err(|_| fmt::Error) // we don't have any good means to pass detailed errors...
    }
}

