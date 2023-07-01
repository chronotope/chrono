// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! Date and time formatting routines.

#[cfg(feature = "alloc")]
use alloc::string::{String, ToString};
#[cfg(any(feature = "alloc", feature = "std"))]
use core::borrow::Borrow;
use core::fmt;
use core::fmt::Write;

#[cfg(any(feature = "alloc", feature = "std"))]
use crate::naive::{NaiveDate, NaiveDateTime, NaiveTime};
#[cfg(any(feature = "alloc", feature = "std"))]
use crate::offset::{FixedOffset, Offset};
#[cfg(any(feature = "alloc", feature = "std"))]
use crate::{Datelike, Timelike, Weekday};

#[cfg(feature = "unstable-locales")]
use super::locales;
#[cfg(any(feature = "alloc", feature = "std"))]
use super::{
    Colons, Fixed, InternalFixed, InternalInternal, Item, Locale, Numeric, OffsetFormat,
    OffsetPrecision, Pad,
};

#[cfg(any(feature = "alloc", feature = "std"))]
struct Locales {
    short_months: &'static [&'static str],
    long_months: &'static [&'static str],
    short_weekdays: &'static [&'static str],
    long_weekdays: &'static [&'static str],
    am_pm: &'static [&'static str],
}

#[cfg(any(feature = "alloc", feature = "std"))]
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
#[cfg(any(feature = "alloc", feature = "std"))]
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

#[cfg(any(feature = "alloc", feature = "std"))]
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

#[cfg(any(feature = "alloc", feature = "std"))]
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
#[cfg(any(feature = "alloc", feature = "std"))]
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
#[cfg(any(feature = "alloc", feature = "std"))]
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

#[cfg(any(feature = "alloc", feature = "std"))]
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
        #[cfg(any(feature = "alloc", feature = "std"))]
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

            let ret = match *spec {
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
                    result.push_str(if t.hour12().0 { locale.am_pm[1] } else { locale.am_pm[0] });
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
                Internal(InternalFixed { val: InternalInternal::Nanosecond3NoDot }) => {
                    time.map(|t| {
                        let nano = t.nanosecond() % 1_000_000_000;
                        write!(result, "{:03}", nano / 1_000_000)
                    })
                }
                Internal(InternalFixed { val: InternalInternal::Nanosecond6NoDot }) => {
                    time.map(|t| {
                        let nano = t.nanosecond() % 1_000_000_000;
                        write!(result, "{:06}", nano / 1_000)
                    })
                }
                Internal(InternalFixed { val: InternalInternal::Nanosecond9NoDot }) => {
                    time.map(|t| {
                        let nano = t.nanosecond() % 1_000_000_000;
                        write!(result, "{:09}", nano)
                    })
                }
                TimezoneName => off.map(|(name, _)| {
                    result.push_str(name);
                    Ok(())
                }),
                TimezoneOffset | TimezoneOffsetZ => off.map(|&(_, off)| {
                    OffsetFormat {
                        precision: OffsetPrecision::Minutes,
                        colons: Colons::Maybe,
                        allow_zulu: *spec == TimezoneOffsetZ,
                        padding: Pad::Zero,
                    }
                    .format(result, off)
                }),
                TimezoneOffsetColon | TimezoneOffsetColonZ => off.map(|&(_, off)| {
                    OffsetFormat {
                        precision: OffsetPrecision::Minutes,
                        colons: Colons::Colon,
                        allow_zulu: *spec == TimezoneOffsetColonZ,
                        padding: Pad::Zero,
                    }
                    .format(result, off)
                }),
                TimezoneOffsetDoubleColon => off.map(|&(_, off)| {
                    OffsetFormat {
                        precision: OffsetPrecision::Seconds,
                        colons: Colons::Colon,
                        allow_zulu: false,
                        padding: Pad::Zero,
                    }
                    .format(result, off)
                }),
                TimezoneOffsetTripleColon => off.map(|&(_, off)| {
                    OffsetFormat {
                        precision: OffsetPrecision::Hours,
                        colons: Colons::None,
                        allow_zulu: false,
                        padding: Pad::Zero,
                    }
                    .format(result, off)
                }),
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
                        Some(write_rfc3339(result, NaiveDateTime::new(*d, *t), off))
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

#[cfg(any(feature = "alloc", feature = "std"))]
impl OffsetFormat {
    /// Writes an offset from UTC with the format defined by `self`.
    fn format(&self, w: &mut impl Write, off: FixedOffset) -> fmt::Result {
        let off = off.local_minus_utc();
        if self.allow_zulu && off == 0 {
            w.write_char('Z')?;
            return Ok(());
        }
        let (sign, off) = if off < 0 { ('-', -off) } else { ('+', off) };

        let hours;
        let mut mins = 0;
        let mut secs = 0;
        let precision = match self.precision {
            OffsetPrecision::Hours => {
                // Minutes and seconds are simply truncated
                hours = (off / 3600) as u8;
                OffsetPrecision::Hours
            }
            OffsetPrecision::Minutes | OffsetPrecision::OptionalMinutes => {
                // Round seconds to the nearest minute.
                let minutes = (off + 30) / 60;
                mins = (minutes % 60) as u8;
                hours = (minutes / 60) as u8;
                if self.precision == OffsetPrecision::OptionalMinutes && mins == 0 {
                    OffsetPrecision::Hours
                } else {
                    OffsetPrecision::Minutes
                }
            }
            OffsetPrecision::Seconds
            | OffsetPrecision::OptionalSeconds
            | OffsetPrecision::OptionalMinutesAndSeconds => {
                let minutes = off / 60;
                secs = (off % 60) as u8;
                mins = (minutes % 60) as u8;
                hours = (minutes / 60) as u8;
                if self.precision != OffsetPrecision::Seconds && secs == 0 {
                    if self.precision == OffsetPrecision::OptionalMinutesAndSeconds && mins == 0 {
                        OffsetPrecision::Hours
                    } else {
                        OffsetPrecision::Minutes
                    }
                } else {
                    OffsetPrecision::Seconds
                }
            }
        };
        let colons = self.colons == Colons::Colon;

        if hours < 10 {
            if self.padding == Pad::Space {
                w.write_char(' ')?;
            }
            w.write_char(sign)?;
            if self.padding == Pad::Zero {
                w.write_char('0')?;
            }
            w.write_char((b'0' + hours) as char)?;
        } else {
            w.write_char(sign)?;
            write_hundreds(w, hours)?;
        }
        if let OffsetPrecision::Minutes | OffsetPrecision::Seconds = precision {
            if colons {
                w.write_char(':')?;
            }
            write_hundreds(w, mins)?;
        }
        if let OffsetPrecision::Seconds = precision {
            if colons {
                w.write_char(':')?;
            }
            write_hundreds(w, secs)?;
        }
        Ok(())
    }
}

/// Writes the date, time and offset to the string. same as `%Y-%m-%dT%H:%M:%S%.f%:z`
#[cfg(any(feature = "alloc", feature = "std"))]
pub(crate) fn write_rfc3339(
    result: &mut String,
    dt: NaiveDateTime,
    off: FixedOffset,
) -> fmt::Result {
    // reuse `Debug` impls which already print ISO 8601 format.
    // this is faster in this way.
    write!(result, "{:?}", dt)?;
    OffsetFormat {
        precision: OffsetPrecision::Minutes,
        colons: Colons::Colon,
        allow_zulu: false,
        padding: Pad::Zero,
    }
    .format(result, off)
}

#[cfg(any(feature = "alloc", feature = "std"))]
/// write datetimes like `Tue, 1 Jul 2003 10:52:37 +0200`, same as `%a, %d %b %Y %H:%M:%S %z`
pub(crate) fn write_rfc2822(
    result: &mut String,
    dt: NaiveDateTime,
    off: FixedOffset,
) -> fmt::Result {
    write_rfc2822_inner(result, &dt.date(), &dt.time(), off, Locales::new(None))
}

#[cfg(any(feature = "alloc", feature = "std"))]
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
    OffsetFormat {
        precision: OffsetPrecision::Minutes,
        colons: Colons::None,
        allow_zulu: false,
        padding: Pad::Zero,
    }
    .format(result, off)
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

#[cfg(test)]
#[cfg(any(feature = "alloc", feature = "std"))]
mod tests {
    use super::{Colons, OffsetFormat, OffsetPrecision, Pad};
    use crate::FixedOffset;

    #[test]
    fn test_offset_formatting() {
        fn check_all(precision: OffsetPrecision, expected: [[&str; 7]; 12]) {
            fn check(
                precision: OffsetPrecision,
                colons: Colons,
                padding: Pad,
                allow_zulu: bool,
                offsets: [FixedOffset; 7],
                expected: [&str; 7],
            ) {
                let offset_format = OffsetFormat { precision, colons, allow_zulu, padding };
                for (offset, expected) in offsets.iter().zip(expected.iter()) {
                    let mut output = String::new();
                    offset_format.format(&mut output, *offset).unwrap();
                    assert_eq!(&output, expected);
                }
            }
            // +03:45, -03:30, +11:00, -11:00:22, +02:34:26, -12:34:30, +00:00
            let offsets = [
                FixedOffset::east_opt(13_500).unwrap(),
                FixedOffset::east_opt(-12_600).unwrap(),
                FixedOffset::east_opt(39_600).unwrap(),
                FixedOffset::east_opt(-39_622).unwrap(),
                FixedOffset::east_opt(9266).unwrap(),
                FixedOffset::east_opt(-45270).unwrap(),
                FixedOffset::east_opt(0).unwrap(),
            ];
            check(precision, Colons::Colon, Pad::Zero, false, offsets, expected[0]);
            check(precision, Colons::Colon, Pad::Zero, true, offsets, expected[1]);
            check(precision, Colons::Colon, Pad::Space, false, offsets, expected[2]);
            check(precision, Colons::Colon, Pad::Space, true, offsets, expected[3]);
            check(precision, Colons::Colon, Pad::None, false, offsets, expected[4]);
            check(precision, Colons::Colon, Pad::None, true, offsets, expected[5]);
            check(precision, Colons::None, Pad::Zero, false, offsets, expected[6]);
            check(precision, Colons::None, Pad::Zero, true, offsets, expected[7]);
            check(precision, Colons::None, Pad::Space, false, offsets, expected[8]);
            check(precision, Colons::None, Pad::Space, true, offsets, expected[9]);
            check(precision, Colons::None, Pad::None, false, offsets, expected[10]);
            check(precision, Colons::None, Pad::None, true, offsets, expected[11]);
            // `Colons::Maybe` should format the same as `Colons::None`
            check(precision, Colons::Maybe, Pad::Zero, false, offsets, expected[6]);
            check(precision, Colons::Maybe, Pad::Zero, true, offsets, expected[7]);
            check(precision, Colons::Maybe, Pad::Space, false, offsets, expected[8]);
            check(precision, Colons::Maybe, Pad::Space, true, offsets, expected[9]);
            check(precision, Colons::Maybe, Pad::None, false, offsets, expected[10]);
            check(precision, Colons::Maybe, Pad::None, true, offsets, expected[11]);
        }
        check_all(
            OffsetPrecision::Hours,
            [
                ["+03", "-03", "+11", "-11", "+02", "-12", "+00"],
                ["+03", "-03", "+11", "-11", "+02", "-12", "Z"],
                [" +3", " -3", "+11", "-11", " +2", "-12", " +0"],
                [" +3", " -3", "+11", "-11", " +2", "-12", "Z"],
                ["+3", "-3", "+11", "-11", "+2", "-12", "+0"],
                ["+3", "-3", "+11", "-11", "+2", "-12", "Z"],
                ["+03", "-03", "+11", "-11", "+02", "-12", "+00"],
                ["+03", "-03", "+11", "-11", "+02", "-12", "Z"],
                [" +3", " -3", "+11", "-11", " +2", "-12", " +0"],
                [" +3", " -3", "+11", "-11", " +2", "-12", "Z"],
                ["+3", "-3", "+11", "-11", "+2", "-12", "+0"],
                ["+3", "-3", "+11", "-11", "+2", "-12", "Z"],
            ],
        );
        check_all(
            OffsetPrecision::Minutes,
            [
                ["+03:45", "-03:30", "+11:00", "-11:00", "+02:34", "-12:35", "+00:00"],
                ["+03:45", "-03:30", "+11:00", "-11:00", "+02:34", "-12:35", "Z"],
                [" +3:45", " -3:30", "+11:00", "-11:00", " +2:34", "-12:35", " +0:00"],
                [" +3:45", " -3:30", "+11:00", "-11:00", " +2:34", "-12:35", "Z"],
                ["+3:45", "-3:30", "+11:00", "-11:00", "+2:34", "-12:35", "+0:00"],
                ["+3:45", "-3:30", "+11:00", "-11:00", "+2:34", "-12:35", "Z"],
                ["+0345", "-0330", "+1100", "-1100", "+0234", "-1235", "+0000"],
                ["+0345", "-0330", "+1100", "-1100", "+0234", "-1235", "Z"],
                [" +345", " -330", "+1100", "-1100", " +234", "-1235", " +000"],
                [" +345", " -330", "+1100", "-1100", " +234", "-1235", "Z"],
                ["+345", "-330", "+1100", "-1100", "+234", "-1235", "+000"],
                ["+345", "-330", "+1100", "-1100", "+234", "-1235", "Z"],
            ],
        );
        #[rustfmt::skip]
        check_all(
            OffsetPrecision::Seconds,
            [
                ["+03:45:00", "-03:30:00", "+11:00:00", "-11:00:22", "+02:34:26", "-12:34:30", "+00:00:00"],
                ["+03:45:00", "-03:30:00", "+11:00:00", "-11:00:22", "+02:34:26", "-12:34:30", "Z"],
                [" +3:45:00", " -3:30:00", "+11:00:00", "-11:00:22", " +2:34:26", "-12:34:30", " +0:00:00"],
                [" +3:45:00", " -3:30:00", "+11:00:00", "-11:00:22", " +2:34:26", "-12:34:30", "Z"],
                ["+3:45:00", "-3:30:00", "+11:00:00", "-11:00:22", "+2:34:26", "-12:34:30", "+0:00:00"],
                ["+3:45:00", "-3:30:00", "+11:00:00", "-11:00:22", "+2:34:26", "-12:34:30", "Z"],
                ["+034500", "-033000", "+110000", "-110022", "+023426", "-123430", "+000000"],
                ["+034500", "-033000", "+110000", "-110022", "+023426", "-123430", "Z"],
                [" +34500", " -33000", "+110000", "-110022", " +23426", "-123430", " +00000"],
                [" +34500", " -33000", "+110000", "-110022", " +23426", "-123430", "Z"],
                ["+34500", "-33000", "+110000", "-110022", "+23426", "-123430", "+00000"],
                ["+34500", "-33000", "+110000", "-110022", "+23426", "-123430", "Z"],
            ],
        );
        check_all(
            OffsetPrecision::OptionalMinutes,
            [
                ["+03:45", "-03:30", "+11", "-11", "+02:34", "-12:35", "+00"],
                ["+03:45", "-03:30", "+11", "-11", "+02:34", "-12:35", "Z"],
                [" +3:45", " -3:30", "+11", "-11", " +2:34", "-12:35", " +0"],
                [" +3:45", " -3:30", "+11", "-11", " +2:34", "-12:35", "Z"],
                ["+3:45", "-3:30", "+11", "-11", "+2:34", "-12:35", "+0"],
                ["+3:45", "-3:30", "+11", "-11", "+2:34", "-12:35", "Z"],
                ["+0345", "-0330", "+11", "-11", "+0234", "-1235", "+00"],
                ["+0345", "-0330", "+11", "-11", "+0234", "-1235", "Z"],
                [" +345", " -330", "+11", "-11", " +234", "-1235", " +0"],
                [" +345", " -330", "+11", "-11", " +234", "-1235", "Z"],
                ["+345", "-330", "+11", "-11", "+234", "-1235", "+0"],
                ["+345", "-330", "+11", "-11", "+234", "-1235", "Z"],
            ],
        );
        check_all(
            OffsetPrecision::OptionalSeconds,
            [
                ["+03:45", "-03:30", "+11:00", "-11:00:22", "+02:34:26", "-12:34:30", "+00:00"],
                ["+03:45", "-03:30", "+11:00", "-11:00:22", "+02:34:26", "-12:34:30", "Z"],
                [" +3:45", " -3:30", "+11:00", "-11:00:22", " +2:34:26", "-12:34:30", " +0:00"],
                [" +3:45", " -3:30", "+11:00", "-11:00:22", " +2:34:26", "-12:34:30", "Z"],
                ["+3:45", "-3:30", "+11:00", "-11:00:22", "+2:34:26", "-12:34:30", "+0:00"],
                ["+3:45", "-3:30", "+11:00", "-11:00:22", "+2:34:26", "-12:34:30", "Z"],
                ["+0345", "-0330", "+1100", "-110022", "+023426", "-123430", "+0000"],
                ["+0345", "-0330", "+1100", "-110022", "+023426", "-123430", "Z"],
                [" +345", " -330", "+1100", "-110022", " +23426", "-123430", " +000"],
                [" +345", " -330", "+1100", "-110022", " +23426", "-123430", "Z"],
                ["+345", "-330", "+1100", "-110022", "+23426", "-123430", "+000"],
                ["+345", "-330", "+1100", "-110022", "+23426", "-123430", "Z"],
            ],
        );
        check_all(
            OffsetPrecision::OptionalMinutesAndSeconds,
            [
                ["+03:45", "-03:30", "+11", "-11:00:22", "+02:34:26", "-12:34:30", "+00"],
                ["+03:45", "-03:30", "+11", "-11:00:22", "+02:34:26", "-12:34:30", "Z"],
                [" +3:45", " -3:30", "+11", "-11:00:22", " +2:34:26", "-12:34:30", " +0"],
                [" +3:45", " -3:30", "+11", "-11:00:22", " +2:34:26", "-12:34:30", "Z"],
                ["+3:45", "-3:30", "+11", "-11:00:22", "+2:34:26", "-12:34:30", "+0"],
                ["+3:45", "-3:30", "+11", "-11:00:22", "+2:34:26", "-12:34:30", "Z"],
                ["+0345", "-0330", "+11", "-110022", "+023426", "-123430", "+00"],
                ["+0345", "-0330", "+11", "-110022", "+023426", "-123430", "Z"],
                [" +345", " -330", "+11", "-110022", " +23426", "-123430", " +0"],
                [" +345", " -330", "+11", "-110022", " +23426", "-123430", "Z"],
                ["+345", "-330", "+11", "-110022", "+23426", "-123430", "+0"],
                ["+345", "-330", "+11", "-110022", "+23426", "-123430", "Z"],
            ],
        );
    }
}
