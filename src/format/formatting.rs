// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! Date and time formatting routines.

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::string::{String, ToString};
#[cfg(any(feature = "alloc", feature = "std", test))]
use core::borrow::Borrow;
use core::fmt;
use core::fmt::Write;

#[cfg(any(feature = "alloc", feature = "std", test))]
use crate::naive::{NaiveDate, NaiveTime};
#[cfg(any(feature = "alloc", feature = "std", test))]
use crate::offset::{FixedOffset, Offset};
#[cfg(any(feature = "alloc", feature = "std", test))]
use crate::{Datelike, Timelike, Weekday};

#[cfg(feature = "unstable-locales")]
use super::locales;
#[cfg(any(feature = "alloc", feature = "std", test))]
use super::{Fixed, InternalFixed, InternalInternal, Item, Locale, Numeric, Pad};

#[cfg(any(feature = "alloc", feature = "std", test))]
struct Locales {
    short_months: &'static [&'static str],
    long_months: &'static [&'static str],
    short_weekdays: &'static [&'static str],
    long_weekdays: &'static [&'static str],
    am_pm: &'static [&'static str],
}

#[cfg(any(feature = "alloc", feature = "std", test))]
impl Locales {
    fn new(_locale: Option<Locale>) -> Self {
        #[cfg(feature = "unstable-locales")]
        {
            let locale = _locale.unwrap_or(Locale::POSIX);
            Self {
                short_months: locales::short_months(locale),
                long_months: locales::long_months(locale),
                short_weekdays: locales::short_weekdays(locale),
                long_weekdays: locales::long_weekdays(locale),
                am_pm: locales::am_pm(locale),
            }
        }
        #[cfg(not(feature = "unstable-locales"))]
        Self {
            short_months: &[
                "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
            ],
            long_months: &[
                "January",
                "February",
                "March",
                "April",
                "May",
                "June",
                "July",
                "August",
                "September",
                "October",
                "November",
                "December",
            ],
            short_weekdays: &["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"],
            long_weekdays: &[
                "Sunday",
                "Monday",
                "Tuesday",
                "Wednesday",
                "Thursday",
                "Friday",
                "Saturday",
            ],
            am_pm: &["AM", "PM"],
        }
    }
}

/// A *temporary* object which can be used as an argument to `format!` or others.
/// This is normally constructed via `format` methods of each date and time type.
#[cfg(any(feature = "alloc", feature = "std", test))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
#[derive(Debug)]
pub struct DelayedFormat<I> {
    /// The date view, if any.
    date: Option<NaiveDate>,
    /// The time view, if any.
    time: Option<NaiveTime>,
    /// The name and local-to-UTC difference for the offset (timezone), if any.
    off: Option<(String, FixedOffset)>,
    /// An iterator returning formatting items.
    items: I,
    /// Locale used for text.
    // TODO: Only used with the locale feature. We should make this property
    // only present when the feature is enabled.
    #[cfg(feature = "unstable-locales")]
    locale: Option<Locale>,
}

#[cfg(any(feature = "alloc", feature = "std", test))]
impl<'a, I: Iterator<Item = B> + Clone, B: Borrow<Item<'a>>> DelayedFormat<I> {
    /// Makes a new `DelayedFormat` value out of local date and time.
    #[must_use]
    pub fn new(date: Option<NaiveDate>, time: Option<NaiveTime>, items: I) -> DelayedFormat<I> {
        DelayedFormat {
            date,
            time,
            off: None,
            items,
            #[cfg(feature = "unstable-locales")]
            locale: None,
        }
    }

    /// Makes a new `DelayedFormat` value out of local date and time and UTC offset.
    #[must_use]
    pub fn new_with_offset<Off>(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        offset: &Off,
        items: I,
    ) -> DelayedFormat<I>
    where
        Off: Offset + fmt::Display,
    {
        let name_and_diff = (offset.to_string(), offset.fix());
        DelayedFormat {
            date,
            time,
            off: Some(name_and_diff),
            items,
            #[cfg(feature = "unstable-locales")]
            locale: None,
        }
    }

    /// Makes a new `DelayedFormat` value out of local date and time and locale.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[must_use]
    pub fn new_with_locale(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        items: I,
        locale: Locale,
    ) -> DelayedFormat<I> {
        DelayedFormat { date, time, off: None, items, locale: Some(locale) }
    }

    /// Makes a new `DelayedFormat` value out of local date and time, UTC offset and locale.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[must_use]
    pub fn new_with_offset_and_locale<Off>(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        offset: &Off,
        items: I,
        locale: Locale,
    ) -> DelayedFormat<I>
    where
        Off: Offset + fmt::Display,
    {
        let name_and_diff = (offset.to_string(), offset.fix());
        DelayedFormat { date, time, off: Some(name_and_diff), items, locale: Some(locale) }
    }
}

#[cfg(any(feature = "alloc", feature = "std", test))]
impl<'a, I: Iterator<Item = B> + Clone, B: Borrow<Item<'a>>> fmt::Display for DelayedFormat<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        #[cfg(feature = "unstable-locales")]
        {
            if let Some(locale) = self.locale {
                return format_localized(
                    f,
                    self.date.as_ref(),
                    self.time.as_ref(),
                    self.off.as_ref(),
                    self.items.clone(),
                    locale,
                );
            }
        }

        format(f, self.date.as_ref(), self.time.as_ref(), self.off.as_ref(), self.items.clone())
    }
}

/// Tries to format given arguments with given formatting items.
/// Internally used by `DelayedFormat`.
#[cfg(any(feature = "alloc", feature = "std", test))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
pub fn format<'a, I, B>(
    w: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    items: I,
) -> fmt::Result
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<Item<'a>>,
{
    let mut result = String::new();
    for item in items {
        format_inner(&mut result, date, time, off, item.borrow(), None)?;
    }
    w.pad(&result)
}
/// Formats single formatting item
#[cfg(any(feature = "alloc", feature = "std", test))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
pub fn format_item(
    w: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    item: &Item<'_>,
) -> fmt::Result {
    let mut result = String::new();
    format_inner(&mut result, date, time, off, item, None)?;
    w.pad(&result)
}

/// Tries to format given arguments with given formatting items.
/// Internally used by `DelayedFormat`.
#[cfg(feature = "unstable-locales")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
pub fn format_localized<'a, I, B>(
    w: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    items: I,
    locale: Locale,
) -> fmt::Result
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<Item<'a>>,
{
    let mut result = String::new();
    for item in items {
        format_inner(&mut result, date, time, off, item.borrow(), Some(locale))?;
    }
    w.pad(&result)
}

/// Formats single formatting item
#[cfg(feature = "unstable-locales")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
pub fn format_item_localized(
    w: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    item: &Item<'_>,
    locale: Locale,
) -> fmt::Result {
    let mut result = String::new();
    format_inner(&mut result, date, time, off, item, Some(locale))?;
    w.pad(&result)
}

#[cfg(any(feature = "alloc", feature = "std", test))]
fn format_inner(
    result: &mut String,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    item: &Item<'_>,
    locale: Option<Locale>,
) -> fmt::Result {
    let locale = Locales::new(locale);

    match *item {
        Item::Literal(s) | Item::Space(s) => result.push_str(s),
        #[cfg(any(feature = "alloc", feature = "std", test))]
        Item::OwnedLiteral(ref s) | Item::OwnedSpace(ref s) => result.push_str(s),

        Item::Numeric(ref spec, ref pad) => {
            use self::Numeric::*;

            let week_from_sun = |d: &NaiveDate| d.weeks_from(Weekday::Sun);
            let week_from_mon = |d: &NaiveDate| d.weeks_from(Weekday::Mon);

            let (width, v) = match *spec {
                Year => (4, date.map(|d| i64::from(d.year()))),
                YearDiv100 => (2, date.map(|d| i64::from(d.year()).div_euclid(100))),
                YearMod100 => (2, date.map(|d| i64::from(d.year()).rem_euclid(100))),
                IsoYear => (4, date.map(|d| i64::from(d.iso_week().year()))),
                IsoYearDiv100 => (2, date.map(|d| i64::from(d.iso_week().year()).div_euclid(100))),
                IsoYearMod100 => (2, date.map(|d| i64::from(d.iso_week().year()).rem_euclid(100))),
                Month => (2, date.map(|d| i64::from(d.month()))),
                Day => (2, date.map(|d| i64::from(d.day()))),
                WeekFromSun => (2, date.map(|d| i64::from(week_from_sun(d)))),
                WeekFromMon => (2, date.map(|d| i64::from(week_from_mon(d)))),
                IsoWeek => (2, date.map(|d| i64::from(d.iso_week().week()))),
                NumDaysFromSun => (1, date.map(|d| i64::from(d.weekday().num_days_from_sunday()))),
                WeekdayFromMon => (1, date.map(|d| i64::from(d.weekday().number_from_monday()))),
                Ordinal => (3, date.map(|d| i64::from(d.ordinal()))),
                Hour => (2, time.map(|t| i64::from(t.hour()))),
                Hour12 => (2, time.map(|t| i64::from(t.hour12().1))),
                Minute => (2, time.map(|t| i64::from(t.minute()))),
                Second => (2, time.map(|t| i64::from(t.second() + t.nanosecond() / 1_000_000_000))),
                Nanosecond => (9, time.map(|t| i64::from(t.nanosecond() % 1_000_000_000))),
                Timestamp => (
                    1,
                    match (date, time, off) {
                        (Some(d), Some(t), None) => Some(d.and_time(*t).timestamp()),
                        (Some(d), Some(t), Some(&(_, off))) => {
                            Some((d.and_time(*t) - off).timestamp())
                        }
                        (_, _, _) => None,
                    },
                ),

                // for the future expansion
                Internal(ref int) => match int._dummy {},
            };

            if let Some(v) = v {
                if (spec == &Year || spec == &IsoYear) && !(0..10_000).contains(&v) {
                    // non-four-digit years require an explicit sign as per ISO 8601
                    match *pad {
                        Pad::None => write!(result, "{:+}", v),
                        Pad::Zero => write!(result, "{:+01$}", v, width + 1),
                        Pad::Space => write!(result, "{:+1$}", v, width + 1),
                    }
                } else {
                    match *pad {
                        Pad::None => write!(result, "{}", v),
                        Pad::Zero => write!(result, "{:01$}", v, width),
                        Pad::Space => write!(result, "{:1$}", v, width),
                    }
                }?
            } else {
                return Err(fmt::Error); // insufficient arguments for given format
            }
        }

        Item::Fixed(ref spec) => {
            use self::Fixed::*;

            let ret =
                match *spec {
                    ShortMonthName => date.map(|d| {
                        result.push_str(locale.short_months[d.month0() as usize]);
                        Ok(())
                    }),
                    LongMonthName => date.map(|d| {
                        result.push_str(locale.long_months[d.month0() as usize]);
                        Ok(())
                    }),
                    ShortWeekdayName => date.map(|d| {
                        result.push_str(
                            locale.short_weekdays[d.weekday().num_days_from_sunday() as usize],
                        );
                        Ok(())
                    }),
                    LongWeekdayName => date.map(|d| {
                        result.push_str(
                            locale.long_weekdays[d.weekday().num_days_from_sunday() as usize],
                        );
                        Ok(())
                    }),
                    LowerAmPm => time.map(|t| {
                        let ampm = if t.hour12().0 { locale.am_pm[1] } else { locale.am_pm[0] };
                        for char in ampm.chars() {
                            result.extend(char.to_lowercase())
                        }
                        Ok(())
                    }),
                    UpperAmPm => time.map(|t| {
                        result.push_str(if t.hour12().0 {
                            locale.am_pm[1]
                        } else {
                            locale.am_pm[0]
                        });
                        Ok(())
                    }),
                    Nanosecond => time.map(|t| {
                        let nano = t.nanosecond() % 1_000_000_000;
                        if nano == 0 {
                            Ok(())
                        } else if nano % 1_000_000 == 0 {
                            write!(result, ".{:03}", nano / 1_000_000)
                        } else if nano % 1_000 == 0 {
                            write!(result, ".{:06}", nano / 1_000)
                        } else {
                            write!(result, ".{:09}", nano)
                        }
                    }),
                    Nanosecond3 => time.map(|t| {
                        let nano = t.nanosecond() % 1_000_000_000;
                        write!(result, ".{:03}", nano / 1_000_000)
                    }),
                    Nanosecond6 => time.map(|t| {
                        let nano = t.nanosecond() % 1_000_000_000;
                        write!(result, ".{:06}", nano / 1_000)
                    }),
                    Nanosecond9 => time.map(|t| {
                        let nano = t.nanosecond() % 1_000_000_000;
                        write!(result, ".{:09}", nano)
                    }),
                    Internal(InternalFixed { val: InternalInternal::Nanosecond3NoDot }) => time
                        .map(|t| {
                            let nano = t.nanosecond() % 1_000_000_000;
                            write!(result, "{:03}", nano / 1_000_000)
                        }),
                    Internal(InternalFixed { val: InternalInternal::Nanosecond6NoDot }) => time
                        .map(|t| {
                            let nano = t.nanosecond() % 1_000_000_000;
                            write!(result, "{:06}", nano / 1_000)
                        }),
                    Internal(InternalFixed { val: InternalInternal::Nanosecond9NoDot }) => time
                        .map(|t| {
                            let nano = t.nanosecond() % 1_000_000_000;
                            write!(result, "{:09}", nano)
                        }),
                    TimezoneName => off.map(|(name, _)| {
                        result.push_str(name);
                        Ok(())
                    }),
                    TimezoneOffsetColon => off
                        .map(|&(_, off)| write_local_minus_utc(result, off, false, Colons::Single)),
                    TimezoneOffsetDoubleColon => off
                        .map(|&(_, off)| write_local_minus_utc(result, off, false, Colons::Double)),
                    TimezoneOffsetTripleColon => off
                        .map(|&(_, off)| write_local_minus_utc(result, off, false, Colons::Triple)),
                    TimezoneOffsetColonZ => off
                        .map(|&(_, off)| write_local_minus_utc(result, off, true, Colons::Single)),
                    TimezoneOffset => {
                        off.map(|&(_, off)| write_local_minus_utc(result, off, false, Colons::None))
                    }
                    TimezoneOffsetZ => {
                        off.map(|&(_, off)| write_local_minus_utc(result, off, true, Colons::None))
                    }
                    Internal(InternalFixed { val: InternalInternal::TimezoneOffsetPermissive }) => {
                        return Err(fmt::Error);
                    }
                    RFC2822 =>
                    // same as `%a, %d %b %Y %H:%M:%S %z`
                    {
                        if let (Some(d), Some(t), Some(&(_, off))) = (date, time, off) {
                            Some(write_rfc2822_inner(result, d, t, off, locale))
                        } else {
                            None
                        }
                    }
                    RFC3339 =>
                    // same as `%Y-%m-%dT%H:%M:%S%.f%:z`
                    {
                        if let (Some(d), Some(t), Some(&(_, off))) = (date, time, off) {
                            Some(write_rfc3339(result, crate::NaiveDateTime::new(*d, *t), off))
                        } else {
                            None
                        }
                    }
                };

            match ret {
                Some(ret) => ret?,
                None => return Err(fmt::Error), // insufficient arguments for given format
            }
        }

        Item::Error => return Err(fmt::Error),
    }
    Ok(())
}

#[cfg(any(feature = "alloc", feature = "std", test))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Colons {
    None,
    Single,
    Double,
    Triple,
}

/// Prints an offset from UTC in the format of `+HHMM` or `+HH:MM`.
/// `Z` instead of `+00[:]00` is allowed when `allow_zulu` is true.
#[cfg(any(feature = "alloc", feature = "std", test))]
fn write_local_minus_utc(
    result: &mut String,
    off: FixedOffset,
    allow_zulu: bool,
    colon_type: Colons,
) -> fmt::Result {
    let off = off.local_minus_utc();
    if allow_zulu && off == 0 {
        result.push('Z');
        return Ok(());
    }
    let (sign, off) = if off < 0 { ('-', -off) } else { ('+', off) };
    result.push(sign);

    write_hundreds(result, (off / 3600) as u8)?;

    match colon_type {
        Colons::None => write_hundreds(result, (off / 60 % 60) as u8),
        Colons::Single => {
            result.push(':');
            write_hundreds(result, (off / 60 % 60) as u8)
        }
        Colons::Double => {
            result.push(':');
            write_hundreds(result, (off / 60 % 60) as u8)?;
            result.push(':');
            write_hundreds(result, (off % 60) as u8)
        }
        Colons::Triple => Ok(()),
    }
}

/// Writes the date, time and offset to the string. same as `%Y-%m-%dT%H:%M:%S%.f%:z`
#[cfg(any(feature = "alloc", feature = "std", test))]
pub(crate) fn write_rfc3339(
    result: &mut String,
    dt: crate::NaiveDateTime,
    off: FixedOffset,
) -> fmt::Result {
    // reuse `Debug` impls which already print ISO 8601 format.
    // this is faster in this way.
    write!(result, "{:?}", dt)?;
    write_local_minus_utc(result, off, false, Colons::Single)
}

#[cfg(any(feature = "alloc", feature = "std", test))]
/// write datetimes like `Tue, 1 Jul 2003 10:52:37 +0200`, same as `%a, %d %b %Y %H:%M:%S %z`
pub(crate) fn write_rfc2822(
    result: &mut String,
    dt: crate::NaiveDateTime,
    off: FixedOffset,
) -> fmt::Result {
    write_rfc2822_inner(result, &dt.date(), &dt.time(), off, Locales::new(None))
}

#[cfg(any(feature = "alloc", feature = "std", test))]
/// write datetimes like `Tue, 1 Jul 2003 10:52:37 +0200`, same as `%a, %d %b %Y %H:%M:%S %z`
fn write_rfc2822_inner(
    result: &mut String,
    d: &NaiveDate,
    t: &NaiveTime,
    off: FixedOffset,
    locale: Locales,
) -> fmt::Result {
    let year = d.year();
    // RFC2822 is only defined on years 0 through 9999
    if !(0..=9999).contains(&year) {
        return Err(fmt::Error);
    }

    result.push_str(locale.short_weekdays[d.weekday().num_days_from_sunday() as usize]);
    result.push_str(", ");
    write_hundreds(result, d.day() as u8)?;
    result.push(' ');
    result.push_str(locale.short_months[d.month0() as usize]);
    result.push(' ');
    write_hundreds(result, (year / 100) as u8)?;
    write_hundreds(result, (year % 100) as u8)?;
    result.push(' ');
    write_hundreds(result, t.hour() as u8)?;
    result.push(':');
    write_hundreds(result, t.minute() as u8)?;
    result.push(':');
    let sec = t.second() + t.nanosecond() / 1_000_000_000;
    write_hundreds(result, sec as u8)?;
    result.push(' ');
    write_local_minus_utc(result, off, false, Colons::None)
}

/// Equivalent to `{:02}` formatting for n < 100.
pub(crate) fn write_hundreds(w: &mut impl Write, n: u8) -> fmt::Result {
    if n >= 100 {
        return Err(fmt::Error);
    }

    let tens = b'0' + n / 10;
    let ones = b'0' + n % 10;
    w.write_char(tens as char)?;
    w.write_char(ones as char)
}
