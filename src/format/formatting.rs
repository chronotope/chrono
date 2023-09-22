// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! Date and time formatting routines.

#[cfg(feature = "alloc")]
use alloc::string::{String, ToString};
use core::borrow::Borrow;
use core::fmt::{self, Display, Write};
use core::marker::PhantomData;

use crate::datetime::SecondsFormat;
use crate::{
    DateTime, Datelike, FixedOffset, NaiveDate, NaiveDateTime, NaiveTime, Offset, TimeZone,
    Timelike, Utc, Weekday,
};

use super::locales;
use super::{
    Colons, Fixed, InternalFixed, InternalInternal, Item, Locale, Numeric, OffsetFormat,
    OffsetPrecision, Pad, ParseError,
};
use locales::*;

/// Formatting specification for type `T` using formatting items provided by `I`.
///
/// The input type `T` is a type such as [`NaiveDate`] or [`DateTime<Tz>`].
/// Not all input types can be used in combination with all formatting [`Item`]'s. For example
/// [`NaiveDate`] can't be used in combination with items for time or offset. On creation of a
/// `FormattingSpec` the items are verified to be usable with the input type.
///
/// Formatting [`Item`]'s are provided by a type `I` that implement `IntoIter<Item<Item<'_>>`,
/// such as the [`StrftimeItems`] iterator, `Vec<Item<'_>>`, an array, or `&[Item<'_>]` slice.
///
/// [`StrftimeItems`]: crate::format::StrftimeItems
#[derive(Clone, Debug)]
pub struct FormattingSpec<T, I> {
    pub(crate) items: I,
    pub(crate) date_time_type: PhantomData<T>,
    #[allow(dead_code)]
    pub(crate) locale: Locale,
}

impl<'a, J, Tz: TimeZone> FormattingSpec<DateTime<Tz>, J> {
    /// Create a new `FormattingSpec` that can be used to format multiple [`DateTime`]'s.
    ///
    /// # Errors
    ///
    /// Returns an error if one of the formatting [`Item`]'s is [`Item::Error`], or requires a
    /// value the input type doesn't have, such as an hour or an offset from UTC on a [`NaiveDate`]
    /// type.
    ///
    /// # Example 1
    ///
    /// Take a slice as argument for `from_items`. This is the most efficient way to use a
    /// `FormattingSpec`.
    ///
    #[cfg_attr(not(any(feature = "alloc", feature = "std")), doc = "```ignore")]
    #[cfg_attr(any(feature = "alloc", feature = "std"), doc = "```rust")]
    /// # use chrono::{ParseError, TimeZone};
    /// use chrono::{DateTime, Utc};
    /// use chrono::format::{FormattingSpec, StrftimeItems};
    ///
    /// let fmt_str = "%a, %Y-%m-%d %H:%M:%S";
    /// let fmt_items = StrftimeItems::new(&fmt_str).parse()?;
    /// let formatter = FormattingSpec::<DateTime<Utc>, _>::from_items(fmt_items.as_slice())?;
    ///
    /// // We can format multiple values without re-parsing the format string.
    /// let dt1 = Utc.with_ymd_and_hms(2023, 4, 5, 6, 7, 8).unwrap();
    /// assert_eq!(dt1.format_with(&formatter).to_string(), "Wed, 2023-04-05 06:07:08");
    /// let dt2 = Utc.with_ymd_and_hms(2023, 6, 7, 8, 9, 10).unwrap();
    /// assert_eq!(dt2.format_with(&formatter).to_string(), "Wed, 2023-06-07 08:09:10");
    /// # Ok::<(), ParseError>(())
    /// ```
    ///
    /// # Example 2
    ///
    /// Take a [`StrftimeItems`] iterator as argument for `from_items`.
    ///
    /// The [`StrftimeItems`] iterator will parse the format string on creation of the
    /// `FormattingSpec`, and reparse it on every use during formatting. This can be a simple
    /// solution if you need to work without `std` or `alloc`.
    ///
    /// But if you can allocate, [`DateTime::format_to_string`] is an easier and slightly more
    /// performant alternative.
    ///
    /// [`StrftimeItems`]: crate::format::StrftimeItems
    ///
    /// ```ignore
    /// # use chrono::{ParseError, TimeZone};
    /// use chrono::{DateTime, Utc};
    /// use chrono::format::{FormattingSpec, StrftimeItems};
    ///
    /// let fmt_str = "%a, %Y-%m-%d %H:%M:%S";
    /// let fmt_str_iter = StrftimeItems::new(&fmt_str);
    /// let formatter = FormattingSpec::<DateTime<Utc>, _>::from_items(fmt_str_iter)?; // parse 1
    ///
    /// let dt1 = Utc.with_ymd_and_hms(2023, 4, 5, 6, 7, 8).unwrap();
    /// assert_eq!(dt1.format_with(&formatter).to_string(), "Wed, 2023-04-05 06:07:08"); // parse 2
    /// let dt2 = Utc.with_ymd_and_hms(2023, 6, 7, 8, 9, 10).unwrap();
    /// assert_eq!(dt2.format_with(&formatter).to_string(), "Wed, 2023-06-07 08:09:10"); // parse 3
    /// # Ok::<(), ParseError>(())
    /// ```
    ///
    /// # Example 3
    ///
    /// Take a `Vec` as argument for `from_items`. This creates an owned `FormattingSpec`.
    ///
    /// An owned `FormattingSpec` comes with a disadvantage: it will create owned [`Formatter`]'s
    /// in turn, which involves cloning the `Vec` on every use.
    ///
    #[cfg_attr(not(any(feature = "alloc", feature = "std")), doc = "```ignore")]
    #[cfg_attr(any(feature = "alloc", feature = "std"), doc = "```rust")]
    /// # use chrono::{ParseError, TimeZone};
    /// use chrono::{DateTime, Utc};
    /// use chrono::format::{FormattingSpec, StrftimeItems};
    ///
    /// let fmt_str = "%a, %Y-%m-%d %H:%M:%S";
    /// let fmt_items = StrftimeItems::new(&fmt_str).parse()?;
    /// let formatter = FormattingSpec::<DateTime<Utc>, _>::from_items(fmt_items)?; // clone 1
    ///
    /// let dt1 = Utc.with_ymd_and_hms(2023, 4, 5, 6, 7, 8).unwrap();
    /// assert_eq!(dt1.format_with(&formatter).to_string(), "Wed, 2023-04-05 06:07:08"); // clone 2 & 3
    /// let dt2 = Utc.with_ymd_and_hms(2023, 6, 7, 8, 9, 10).unwrap();
    /// assert_eq!(dt2.format_with(&formatter).to_string(), "Wed, 2023-06-07 08:09:10"); // clone 4 & 5
    /// # Ok::<(), ParseError>(())
    /// ```
    pub fn from_items<I, B>(items: I) -> Result<Self, ParseError>
    where
        I: IntoIterator<Item = B, IntoIter = J>,
        J: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        let items = items.into_iter();
        let locale = locales::default_locale();
        for item in items.clone() {
            item.borrow().check_fields(true, true, true, locale)?
        }
        Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
    }

    /// Create a new `FormattingSpec` that can be used to format multiple [`DateTime`]'s localized
    /// for `locale`.
    ///
    /// You may want to combine this with the locale-aware [`StrftimeItems::new_with_locale`].
    ///
    /// # Errors
    ///
    /// Returns an error if one of the formatting [`Item`]'s is for a value the input type doesn't
    /// have, such as an hour or an offset from UTC on a [`NaiveDate`] type.
    ///
    /// Also errors if the locale does not support an [`Item`], which may happen with the
    /// [`Fixed::UpperAmPm`] and [`Fixed::LowerAmPm`] items (`%P` and `%p` formatting specifiers).
    ///
    /// [`StrftimeItems::new_with_locale`]: crate::format::StrftimeItems::new_with_locale
    ///
    /// # Example
    ///
    /// Take a slice as argument. This is the most efficient way to use a `FormattingSpec`.
    ///
    #[cfg_attr(not(any(feature = "alloc", feature = "std")), doc = "```ignore")]
    #[cfg_attr(any(feature = "alloc", feature = "std"), doc = "```rust")]
    /// # use chrono::{ParseError, TimeZone};
    /// use chrono::{NaiveDate, Utc};
    /// use chrono::format::{FormattingSpec, Locale, StrftimeItems};
    ///
    /// let date = NaiveDate::from_ymd_opt(2023, 4, 5).unwrap();
    ///
    /// let fmt_str = "%a %-d %B ’%y";
    /// let items = StrftimeItems::new_with_locale(&fmt_str, Locale::nl_NL).parse()?;
    /// let formatter = FormattingSpec::<NaiveDate, _>::from_items_localized(&items, Locale::nl_NL)?;
    /// assert_eq!(date.format_with(&formatter).to_string(), "wo 5 april ’23");
    ///
    /// let dt2 = Utc.with_ymd_and_hms(2023, 6, 7, 8, 9, 10).unwrap();
    /// assert_eq!(dt2.format_with(&formatter.into()).to_string(), "wo 7 juni ’23");
    /// # Ok::<(), ParseError>(())
    /// ```
    #[cfg(feature = "unstable-locales")]
    pub fn from_items_localized<I, B>(items: I, locale: Locale) -> Result<Self, ParseError>
    where
        I: IntoIterator<Item = B, IntoIter = J>,
        J: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        let items = items.into_iter();
        for item in items.clone() {
            item.borrow().check_fields(true, true, true, locale)?
        }
        Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
    }
}

// TODO: once our MSRV >= 1.61 change this impl to take a generic `Tz` trait bound.
// Trait bounds on const fn parameters were not supported before.
impl<'a> FormattingSpec<DateTime<Utc>, &'a [Item<'a>]> {
    /// Creates a new `FormattingSpec` given a slice of [`Item`]'s.
    ///
    /// The difference with the more generic [`FormattingSpec::from_items`] is that `from_slice` is
    /// usable in `const` context.
    ///
    /// # Errors
    ///
    /// Returns an error if one of the formatting [`Item`]'s is for a value the input type doesn't
    /// have, such as an hour or an offset from UTC on a [`NaiveDate`] type.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::format::*;
    /// # use chrono::{DateTime, Utc, TimeZone};
    ///
    /// // A manual implementation of `DateTime::to_rfc3339`
    /// const RFC3339_ITEMS: &[Item<'static>] = &[
    ///     Item::Numeric(Numeric::Year, Pad::Zero),
    ///     Item::Literal("-"),
    ///     Item::Numeric(Numeric::Month, Pad::Zero),
    ///     Item::Literal("-"),
    ///     Item::Numeric(Numeric::Day, Pad::Zero),
    ///     Item::Literal("T"),
    ///     Item::Numeric(Numeric::Hour, Pad::Zero),
    ///     Item::Literal(":"),
    ///     Item::Numeric(Numeric::Minute, Pad::Zero),
    ///     Item::Literal(":"),
    ///     Item::Numeric(Numeric::Second, Pad::Zero),
    ///     Item::Fixed(Fixed::Nanosecond),
    ///     Item::Fixed(Fixed::TimezoneOffsetColon),
    /// ];
    /// const RFC3339_SPEC: FormattingSpec<DateTime<Utc>, &[Item<'_>]> =
    ///     match FormattingSpec::<DateTime<Utc>, _>::from_slice(RFC3339_ITEMS) {
    ///         Ok(spec) => spec,
    ///         Err(_) => panic!(), // Will give a compile error if the `Item`s are incorrect.
    ///     };
    ///
    /// let datetime = Utc.with_ymd_and_hms(2023, 6, 7, 8, 9, 10).unwrap();
    /// assert_eq!(datetime.format_with(&RFC3339_SPEC).to_string(), "2023-06-07T08:09:10+00:00");
    /// ```
    pub const fn from_slice(items: &'a [Item<'a>]) -> Result<Self, ParseError> {
        let locale = locales::default_locale();
        let mut i = 0;
        while i < items.len() {
            if let Err(e) = items[i].check_fields(true, true, true, locale) {
                return Err(e);
            }
            i += 1;
        }
        Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
    }

    /// Creates a new `FormattingSpec` given a slice of [`Item`]'s and a `locale`.
    ///
    /// The difference with the more generic [`FormattingSpec::from_items_localized`] is that
    /// `from_slice_localized` is usable in `const` context.
    ///
    /// You may want to combine this with the locale-aware [`StrftimeItems::new_with_locale`].
    ///
    /// [`StrftimeItems::new_with_locale`]: crate::format::StrftimeItems::new_with_locale
    ///
    /// # Errors
    ///
    /// Returns an error if one of the formatting [`Item`]'s is for a value the input type doesn't
    /// have, such as an hour or an offset from UTC on a [`NaiveDate`] type.
    #[cfg(feature = "unstable-locales")]
    pub const fn from_slice_localized(
        items: &'a [Item<'a>],
        locale: Locale,
    ) -> Result<Self, ParseError> {
        let mut i = 0;
        while i < items.len() {
            if let Err(e) = items[i].check_fields(true, true, true, locale) {
                return Err(e);
            }
            i += 1;
        }
        Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
    }
}

impl<'a> FormattingSpec<DateTime<FixedOffset>, &'a [Item<'a>]> {
    /// Creates a new `FormattingSpec` given a slice of [`Item`]'s.
    pub const fn from_slice(items: &'a [Item<'a>]) -> Result<Self, ParseError> {
        let locale = locales::default_locale();
        let mut i = 0;
        while i < items.len() {
            if let Err(e) = items[i].check_fields(true, true, true, locale) {
                return Err(e);
            }
            i += 1;
        }
        Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
    }

    /// Creates a new `FormattingSpec` given a slice of [`Item`]'s and a `locale`.
    #[cfg(feature = "unstable-locales")]
    pub const fn from_slice_localized(
        items: &'a [Item<'a>],
        locale: Locale,
    ) -> Result<Self, ParseError> {
        let mut i = 0;
        while i < items.len() {
            if let Err(e) = items[i].check_fields(true, true, true, locale) {
                return Err(e);
            }
            i += 1;
        }
        Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
    }
}

macro_rules! formatting_spec_impls {
    ($type:ty, $date:literal, $time:literal, $off:literal) => {
        impl<'a, J> FormattingSpec<$type, J> {
            /// Create a new `FormattingSpec` that can be used to format multiple [`DateTime`]'s.
            #[doc = concat!("[`", stringify!($type), "`]'s.")]
            pub fn from_items<I, B>(items: I) -> Result<Self, ParseError>
            where
                I: IntoIterator<Item = B, IntoIter = J>,
                J: Iterator<Item = B> + Clone,
                B: Borrow<Item<'a>>,
            {
                let items = items.into_iter();
                let locale = locales::default_locale();
                for item in items.clone() {
                    item.borrow().check_fields($date, $time, $off, locale)?
                }
                Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
            }

            /// Create a new `FormattingSpec` that can be used to format multiple [`DateTime`]'s
            /// localized for `locale`.
            #[doc = concat!("[`", stringify!($type), "`]'s.")]
            #[cfg(feature = "unstable-locales")]
            pub fn from_items_localized<I, B>(items: I, locale: Locale) -> Result<Self, ParseError>
            where
                I: IntoIterator<Item = B, IntoIter = J>,
                J: Iterator<Item = B> + Clone,
                B: Borrow<Item<'a>>,
            {
                let items = items.into_iter();
                for item in items.clone() {
                    item.borrow().check_fields($date, $time, $off, locale)?
                }
                Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
            }
        }

        impl<'a> FormattingSpec<$type, &'a [Item<'a>]> {
            /// Creates a new `FormattingSpec` given a slice of [`Item`]'s.
            pub const fn from_slice(items: &'a [Item<'a>]) -> Result<Self, ParseError> {
                let locale = locales::default_locale();
                let mut i = 0;
                while i < items.len() {
                    if let Err(e) = items[i].check_fields($date, $time, $off, locale) {
                        return Err(e);
                    }
                    i += 1;
                }
                Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
            }

            /// Creates a new `FormattingSpec` given a slice of [`Item`]'s and a `locale`.
            #[cfg(feature = "unstable-locales")]
            pub const fn from_slice_localized(
                items: &'a [Item<'a>],
                locale: Locale,
            ) -> Result<Self, ParseError> {
                let mut i = 0;
                while i < items.len() {
                    if let Err(e) = items[i].check_fields(true, true, true, locale) {
                        return Err(e);
                    }
                    i += 1;
                }
                Ok(FormattingSpec { items, date_time_type: PhantomData, locale })
            }
        }
    };
}

formatting_spec_impls!(NaiveDateTime, true, true, false);
formatting_spec_impls!(NaiveDate, true, false, false);
formatting_spec_impls!(NaiveTime, false, true, false);

impl<T, I> FormattingSpec<T, I> {
    /// Unwraps this `FormattingSpec<T, I>`, returning the underlying iterator `I`.
    pub fn into_inner(self) -> I {
        self.items
    }

    /// Returns the locale of this `FormattingSpec`.
    #[cfg(feature = "unstable-locales")]
    pub fn locale(&self) -> Locale {
        self.locale
    }
}

impl<'a, T, I, J, B> FormattingSpec<T, I>
where
    I: IntoIterator<Item = B, IntoIter = J> + Clone,
    J: Iterator<Item = B> + Clone,
    B: Borrow<Item<'a>>,
{
    /// Makes a new `Formatter` with this `FormattingSpec` and a local date, time and/or UTC offset.
    ///
    /// # Errors/panics
    ///
    /// If the iterator given for `items` returns [`Item::Error`], the `Display` implementation of
    /// `Formatter` will return an error, which causes a panic when used in combination with
    /// [`to_string`](ToString::to_string), [`println!`] and [`format!`].
    pub(crate) fn formatter<Off>(
        &self,
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        offset: Option<Off>,
    ) -> Formatter<J, Off> {
        let items = self.items.clone().into_iter();
        Formatter { date, time, offset, items, locale: self.locale }
    }
}
macro_rules! formatting_spec_from_impls {
    ($src:ty, $dst:ty) => {
        impl<I> From<FormattingSpec<$src, I>> for FormattingSpec<$dst, I> {
            fn from(value: FormattingSpec<$src, I>) -> Self {
                Self { items: value.items, date_time_type: PhantomData, locale: value.locale }
            }
        }
    };
}
formatting_spec_from_impls!(NaiveTime, NaiveDateTime);
formatting_spec_from_impls!(NaiveDate, NaiveDateTime);
formatting_spec_from_impls!(NaiveTime, DateTime<Utc>);
formatting_spec_from_impls!(NaiveDate, DateTime<Utc>);
formatting_spec_from_impls!(NaiveDateTime, DateTime<Utc>);

/// A *temporary* object which can be used as an argument to [`format!`] or others.
/// This is normally constructed via the `format_with` methods of each date and time type.
#[derive(Debug)]
pub struct Formatter<I, Off> {
    /// The date view, if any.
    date: Option<NaiveDate>,
    /// The time view, if any.
    time: Option<NaiveTime>,
    /// The offset from UTC, if any
    offset: Option<Off>,
    /// An iterator returning formatting items.
    items: I,
    /// Locale used for text
    /// ZST if the `unstable-locales` feature is not enabled.
    locale: Locale,
}

impl<'a, I, B, Off> Formatter<I, Off>
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<Item<'a>>,
    Off: Offset + Display,
{
    /// Makes a new `Formatter` value out of local date and time and UTC offset.
    ///
    /// # Errors/panics
    ///
    /// If the iterator given for `items` returns [`Item::Error`], the `Display` implementation of
    /// `Formatter` will return an error, which causes a panic when used in combination with
    /// [`to_string`](ToString::to_string), [`println!`] and [`format!`].
    #[must_use]
    pub fn new(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        offset: Option<Off>,
        items: I,
    ) -> Formatter<I, Off> {
        Formatter { date, time, offset, items, locale: default_locale() }
    }

    /// Makes a new `DelayedFormat` value out of local date and time, UTC offset and locale.
    ///
    /// # Errors/panics
    ///
    /// If the iterator given for `items` returns [`Item::Error`], the `Display` implementation of
    /// `Formatter` will return an error, which causes a panic when used in combination with
    /// [`to_string`](ToString::to_string), [`println!`] and [`format!`].
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[must_use]
    pub fn new_with_locale(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        offset: Option<Off>,
        items: I,
        locale: Locale,
    ) -> Formatter<I, Off> {
        Formatter { date, time, offset, items, locale }
    }

    #[inline]
    fn format(&self, w: &mut impl Write) -> fmt::Result {
        for item in self.items.clone() {
            match *item.borrow() {
                Item::Literal(s) | Item::Space(s) => w.write_str(s),
                #[cfg(any(feature = "alloc", feature = "std"))]
                Item::OwnedLiteral(ref s) | Item::OwnedSpace(ref s) => w.write_str(s),
                Item::Numeric(ref spec, pad) => self.format_numeric(w, spec, pad),
                Item::Fixed(ref spec) => self.format_fixed(w, spec),
                Item::Error => Err(fmt::Error),
            }?;
        }
        Ok(())
    }

    #[cfg(any(feature = "alloc", feature = "std"))]
    fn format_with_parameters(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Justify/pad/truncate the formatted result by rendering it to a temporary `String`
        // first.
        let mut result = String::new();
        self.format(&mut result)?;
        f.pad(&result)
    }

    #[cfg(not(any(feature = "alloc", feature = "std")))]
    fn format_with_parameters(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // We have to replicate the `fmt::Formatter:pad` method without allocating.
        let mut counter = CountingSink::new();
        self.format(&mut counter)?;
        let chars_count = counter.chars_written();

        if let Some(max_width) = f.precision() {
            if chars_count > max_width {
                let mut truncating_writer = TruncatingWriter::new(f, max_width);
                return self.format(&mut truncating_writer);
            }
        }
        if let Some(min_width) = f.width() {
            if chars_count < min_width {
                let padding = min_width - chars_count;
                let (before, after) = match f.align().unwrap_or(fmt::Alignment::Left) {
                    fmt::Alignment::Left => (0, padding),
                    fmt::Alignment::Right => (padding, 0),
                    fmt::Alignment::Center => (padding / 2, (padding + 1) / 2),
                };
                let fill = f.fill();
                for _ in 0..before {
                    f.write_char(fill)?;
                }
                self.format(f)?;
                for _ in 0..after {
                    f.write_char(fill)?;
                }
                return Ok(());
            }
        }
        self.format(f)
    }

    fn format_numeric(&self, w: &mut impl Write, spec: &Numeric, pad: Pad) -> fmt::Result {
        use self::Numeric::*;

        fn write_one(w: &mut impl Write, v: u8) -> fmt::Result {
            w.write_char((b'0' + v) as char)
        }

        fn write_two(w: &mut impl Write, v: u8, pad: Pad) -> fmt::Result {
            let ones = b'0' + v % 10;
            match (v / 10, pad) {
                (0, Pad::None) => {}
                (0, Pad::Space) => w.write_char(' ')?,
                (tens, _) => w.write_char((b'0' + tens) as char)?,
            }
            w.write_char(ones as char)
        }

        #[inline]
        fn write_year(w: &mut impl Write, year: i32, pad: Pad) -> fmt::Result {
            if (1000..=9999).contains(&year) {
                // fast path
                write_hundreds(w, (year / 100) as u8)?;
                write_hundreds(w, (year % 100) as u8)
            } else {
                write_n(w, 4, year as i64, pad, !(0..10_000).contains(&year))
            }
        }

        fn write_n(
            w: &mut impl Write,
            n: usize,
            v: i64,
            pad: Pad,
            always_sign: bool,
        ) -> fmt::Result {
            if always_sign {
                match pad {
                    Pad::None => write!(w, "{:+}", v),
                    Pad::Zero => write!(w, "{:+01$}", v, n + 1),
                    Pad::Space => write!(w, "{:+1$}", v, n + 1),
                }
            } else {
                match pad {
                    Pad::None => write!(w, "{}", v),
                    Pad::Zero => write!(w, "{:01$}", v, n),
                    Pad::Space => write!(w, "{:1$}", v, n),
                }
            }
        }

        match (spec, self.date, self.time) {
            (Year, Some(d), _) => write_year(w, d.year(), pad),
            (YearDiv100, Some(d), _) => write_two(w, d.year().div_euclid(100) as u8, pad),
            (YearMod100, Some(d), _) => write_two(w, d.year().rem_euclid(100) as u8, pad),
            (IsoYear, Some(d), _) => write_year(w, d.iso_week().year(), pad),
            (IsoYearDiv100, Some(d), _) => {
                write_two(w, d.iso_week().year().div_euclid(100) as u8, pad)
            }
            (IsoYearMod100, Some(d), _) => {
                write_two(w, d.iso_week().year().rem_euclid(100) as u8, pad)
            }
            (Month, Some(d), _) => write_two(w, d.month() as u8, pad),
            (Day, Some(d), _) => write_two(w, d.day() as u8, pad),
            (WeekFromSun, Some(d), _) => write_two(w, d.weeks_from(Weekday::Sun) as u8, pad),
            (WeekFromMon, Some(d), _) => write_two(w, d.weeks_from(Weekday::Mon) as u8, pad),
            (IsoWeek, Some(d), _) => write_two(w, d.iso_week().week() as u8, pad),
            (NumDaysFromSun, Some(d), _) => write_one(w, d.weekday().num_days_from_sunday() as u8),
            (WeekdayFromMon, Some(d), _) => write_one(w, d.weekday().number_from_monday() as u8),
            (Ordinal, Some(d), _) => write_n(w, 3, d.ordinal() as i64, pad, false),
            (Hour, _, Some(t)) => write_two(w, t.hour() as u8, pad),
            (Hour12, _, Some(t)) => write_two(w, t.hour12().1 as u8, pad),
            (Minute, _, Some(t)) => write_two(w, t.minute() as u8, pad),
            (Second, _, Some(t)) => {
                write_two(w, (t.second() + t.nanosecond() / 1_000_000_000) as u8, pad)
            }
            (Nanosecond, _, Some(t)) => {
                write_n(w, 9, (t.nanosecond() % 1_000_000_000) as i64, pad, false)
            }
            (Timestamp, Some(d), Some(t)) => {
                let offset = self.offset.as_ref().map(|o| i64::from(o.fix().local_minus_utc()));
                let timestamp = d.and_time(t).timestamp() - offset.unwrap_or(0);
                write_n(w, 9, timestamp, pad, false)
            }
            (Internal(_), _, _) => Ok(()), // for future expansion
            _ => Err(fmt::Error),          // insufficient arguments for given format
        }
    }

    fn format_fixed(&self, w: &mut impl Write, spec: &Fixed) -> fmt::Result {
        use Fixed::*;
        use InternalInternal::*;

        match (spec, self.date, self.time, self.offset.as_ref()) {
            (ShortMonthName, Some(d), _, _) => {
                w.write_str(short_months(self.locale)[d.month0() as usize])
            }
            (LongMonthName, Some(d), _, _) => {
                w.write_str(long_months(self.locale)[d.month0() as usize])
            }
            (ShortWeekdayName, Some(d), _, _) => w.write_str(
                short_weekdays(self.locale)[d.weekday().num_days_from_sunday() as usize],
            ),
            (LongWeekdayName, Some(d), _, _) => {
                w.write_str(long_weekdays(self.locale)[d.weekday().num_days_from_sunday() as usize])
            }
            (LowerAmPm, _, Some(t), _) => {
                let ampm = if t.hour12().0 { am_pm(self.locale)[1] } else { am_pm(self.locale)[0] };
                if ampm.is_empty() {
                    return Err(fmt::Error);
                }
                for c in ampm.chars().flat_map(|c| c.to_lowercase()) {
                    w.write_char(c)?
                }
                Ok(())
            }
            (UpperAmPm, _, Some(t), _) => {
                let ampm = if t.hour12().0 { am_pm(self.locale)[1] } else { am_pm(self.locale)[0] };
                if ampm.is_empty() {
                    return Err(fmt::Error);
                }
                w.write_str(ampm)
            }
            (Nanosecond, _, Some(t), _) => {
                let nano = t.nanosecond() % 1_000_000_000;
                if nano == 0 {
                    Ok(())
                } else {
                    w.write_str(decimal_point(self.locale))?;
                    if nano % 1_000_000 == 0 {
                        write!(w, "{:03}", nano / 1_000_000)
                    } else if nano % 1_000 == 0 {
                        write!(w, "{:06}", nano / 1_000)
                    } else {
                        write!(w, "{:09}", nano)
                    }
                }
            }
            (Nanosecond3, _, Some(t), _) => {
                w.write_str(decimal_point(self.locale))?;
                write!(w, "{:03}", t.nanosecond() / 1_000_000 % 1000)
            }
            (Nanosecond6, _, Some(t), _) => {
                w.write_str(decimal_point(self.locale))?;
                write!(w, "{:06}", t.nanosecond() / 1_000 % 1_000_000)
            }
            (Nanosecond9, _, Some(t), _) => {
                w.write_str(decimal_point(self.locale))?;
                write!(w, "{:09}", t.nanosecond() % 1_000_000_000)
            }
            (Internal(InternalFixed { val: Nanosecond3NoDot }), _, Some(t), _) => {
                write!(w, "{:03}", t.nanosecond() / 1_000_000 % 1_000)
            }
            (Internal(InternalFixed { val: Nanosecond6NoDot }), _, Some(t), _) => {
                write!(w, "{:06}", t.nanosecond() / 1_000 % 1_000_000)
            }
            (Internal(InternalFixed { val: Nanosecond9NoDot }), _, Some(t), _) => {
                write!(w, "{:09}", t.nanosecond() % 1_000_000_000)
            }
            (TimezoneName, _, _, Some(off)) => write!(w, "{}", off),
            (TimezoneOffset | TimezoneOffsetZ, _, _, Some(off)) => {
                let offset_format = OffsetFormat {
                    precision: OffsetPrecision::Minutes,
                    colons: Colons::Maybe,
                    allow_zulu: *spec == TimezoneOffsetZ,
                    padding: Pad::Zero,
                };
                offset_format.format(w, off.fix())
            }
            (TimezoneOffsetColon | TimezoneOffsetColonZ, _, _, Some(off)) => {
                let offset_format = OffsetFormat {
                    precision: OffsetPrecision::Minutes,
                    colons: Colons::Colon,
                    allow_zulu: *spec == TimezoneOffsetColonZ,
                    padding: Pad::Zero,
                };
                offset_format.format(w, off.fix())
            }
            (TimezoneOffsetDoubleColon, _, _, Some(off)) => {
                let offset_format = OffsetFormat {
                    precision: OffsetPrecision::Seconds,
                    colons: Colons::Colon,
                    allow_zulu: false,
                    padding: Pad::Zero,
                };
                offset_format.format(w, off.fix())
            }
            (TimezoneOffsetTripleColon, _, _, Some(off)) => {
                let offset_format = OffsetFormat {
                    precision: OffsetPrecision::Hours,
                    colons: Colons::None,
                    allow_zulu: false,
                    padding: Pad::Zero,
                };
                offset_format.format(w, off.fix())
            }
            (RFC2822, Some(d), Some(t), Some(off)) => {
                write_rfc2822_inner(w, d, t, off.fix(), self.locale)
            }
            (RFC3339, Some(d), Some(t), Some(off)) => write_rfc3339(
                w,
                crate::NaiveDateTime::new(d, t),
                off.fix(),
                SecondsFormat::AutoSi,
                false,
            ),
            _ => Err(fmt::Error), // insufficient arguments for given format
        }
    }
}

impl<'a, I, B, Off> Display for Formatter<I, Off>
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<Item<'a>>,
    Off: Offset + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if f.width().is_some() || f.precision().is_some() {
            self.format_with_parameters(f)
        } else {
            self.format(f)
        }
    }
}

/// Only used to make `DelayedFormat` a wrapper around `Formatter`.
#[cfg(any(feature = "alloc", feature = "std"))]
#[derive(Clone, Debug)]
struct OffsetFormatter {
    offset: FixedOffset,
    tz_name: String,
}

#[cfg(any(feature = "alloc", feature = "std"))]
impl Offset for OffsetFormatter {
    fn fix(&self) -> FixedOffset {
        self.offset
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
impl Display for OffsetFormatter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.tz_name)
    }
}

/// A *temporary* object which can be used as an argument to `format!` or others.
/// This is normally constructed via `format` methods of each date and time type.
#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
#[derive(Debug)]
pub struct DelayedFormat<I> {
    inner: Formatter<I, OffsetFormatter>,
}

#[cfg(any(feature = "alloc", feature = "std"))]
impl<'a, I: Iterator<Item = B> + Clone, B: Borrow<Item<'a>>> DelayedFormat<I> {
    /// Makes a new `DelayedFormat` value out of local date and time.
    #[must_use]
    pub fn new(date: Option<NaiveDate>, time: Option<NaiveTime>, items: I) -> DelayedFormat<I> {
        DelayedFormat { inner: Formatter::new(date, time, None, items) }
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
        Off: Offset + Display,
    {
        let offset = Some(OffsetFormatter { offset: offset.fix(), tz_name: offset.to_string() });
        DelayedFormat { inner: Formatter::new(date, time, offset, items) }
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
        DelayedFormat { inner: Formatter::new_with_locale(date, time, None, items, locale) }
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
        Off: Offset + Display,
    {
        let offset = Some(OffsetFormatter { offset: offset.fix(), tz_name: offset.to_string() });
        DelayedFormat { inner: Formatter::new_with_locale(date, time, offset, items, locale) }
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
impl<'a, I: Iterator<Item = B> + Clone, B: Borrow<Item<'a>>> Display for DelayedFormat<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// Tries to format given arguments with given formatting items.
/// Internally used by `DelayedFormat`.
#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
#[deprecated(since = "0.4.32")]
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
    let offset = off.cloned().map(|(tz_name, offset)| OffsetFormatter { tz_name, offset });
    Formatter::new(date.copied(), time.copied(), offset, items).fmt(w)
}

/// Formats single formatting item
#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
#[deprecated(since = "0.4.32")]
pub fn format_item(
    w: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    item: &Item<'_>,
) -> fmt::Result {
    let offset = off.cloned().map(|(tz_name, offset)| OffsetFormatter { tz_name, offset });
    Formatter::new(date.copied(), time.copied(), offset, [item].into_iter()).fmt(w)
}

/// Tries to format given arguments with given formatting items.
/// Internally used by `DelayedFormat`.
#[cfg(all(feature = "unstable-locales", any(feature = "alloc", feature = "std")))]
#[deprecated(since = "0.4.32")]
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
    let offset = off.cloned().map(|(tz_name, offset)| OffsetFormatter { tz_name, offset });
    Formatter::new_with_locale(date.copied(), time.copied(), offset, items, locale).fmt(w)
}

/// Formats single formatting item
#[cfg(all(feature = "unstable-locales", any(feature = "alloc", feature = "std")))]
#[deprecated(since = "0.4.32")]
pub fn format_item_localized(
    w: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    item: &Item<'_>,
    locale: Locale,
) -> fmt::Result {
    let offset = off.cloned().map(|(tz_name, offset)| OffsetFormatter { tz_name, offset });
    Formatter::new_with_locale(date.copied(), time.copied(), offset, [item].into_iter(), locale)
        .fmt(w)
}

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
#[inline]
pub(crate) fn write_rfc3339(
    w: &mut impl Write,
    dt: NaiveDateTime,
    off: FixedOffset,
    secform: SecondsFormat,
    use_z: bool,
) -> fmt::Result {
    let year = dt.date().year();
    if (0..=9999).contains(&year) {
        write_hundreds(w, (year / 100) as u8)?;
        write_hundreds(w, (year % 100) as u8)?;
    } else {
        // ISO 8601 requires the explicit sign for out-of-range years
        write!(w, "{:+05}", year)?;
    }
    w.write_char('-')?;
    write_hundreds(w, dt.date().month() as u8)?;
    w.write_char('-')?;
    write_hundreds(w, dt.date().day() as u8)?;

    w.write_char('T')?;

    let (hour, min, mut sec) = dt.time().hms();
    let mut nano = dt.nanosecond();
    if nano >= 1_000_000_000 {
        sec += 1;
        nano -= 1_000_000_000;
    }
    write_hundreds(w, hour as u8)?;
    w.write_char(':')?;
    write_hundreds(w, min as u8)?;
    w.write_char(':')?;
    let sec = sec;
    write_hundreds(w, sec as u8)?;

    match secform {
        SecondsFormat::Secs => {}
        SecondsFormat::Millis => write!(w, ".{:03}", nano / 1_000_000)?,
        SecondsFormat::Micros => write!(w, ".{:06}", nano / 1000)?,
        SecondsFormat::Nanos => write!(w, ".{:09}", nano)?,
        SecondsFormat::AutoSi => {
            if nano == 0 {
            } else if nano % 1_000_000 == 0 {
                write!(w, ".{:03}", nano / 1_000_000)?
            } else if nano % 1_000 == 0 {
                write!(w, ".{:06}", nano / 1_000)?
            } else {
                write!(w, ".{:09}", nano)?
            }
        }
        SecondsFormat::__NonExhaustive => unreachable!(),
    };

    OffsetFormat {
        precision: OffsetPrecision::Minutes,
        colons: Colons::Colon,
        allow_zulu: use_z,
        padding: Pad::Zero,
    }
    .format(w, off)
}

#[cfg(any(feature = "alloc", feature = "std"))]
/// write datetimes like `Tue, 1 Jul 2003 10:52:37 +0200`, same as `%a, %d %b %Y %H:%M:%S %z`
pub(crate) fn write_rfc2822(
    w: &mut impl Write,
    dt: NaiveDateTime,
    off: FixedOffset,
) -> fmt::Result {
    write_rfc2822_inner(w, dt.date(), dt.time(), off, default_locale())
}

/// write datetimes like `Tue, 1 Jul 2003 10:52:37 +0200`, same as `%a, %d %b %Y %H:%M:%S %z`
fn write_rfc2822_inner(
    w: &mut impl Write,
    d: NaiveDate,
    t: NaiveTime,
    off: FixedOffset,
    locale: Locale,
) -> fmt::Result {
    let year = d.year();
    // RFC2822 is only defined on years 0 through 9999
    if !(0..=9999).contains(&year) {
        return Err(fmt::Error);
    }

    w.write_str(short_weekdays(locale)[d.weekday().num_days_from_sunday() as usize])?;
    w.write_str(", ")?;
    let day = d.day();
    if day < 10 {
        w.write_char((b'0' + day as u8) as char)?;
    } else {
        write_hundreds(w, day as u8)?;
    }
    w.write_char(' ')?;
    w.write_str(short_months(locale)[d.month0() as usize])?;
    w.write_char(' ')?;
    write_hundreds(w, (year / 100) as u8)?;
    write_hundreds(w, (year % 100) as u8)?;
    w.write_char(' ')?;

    let (hour, min, sec) = t.hms();
    write_hundreds(w, hour as u8)?;
    w.write_char(':')?;
    write_hundreds(w, min as u8)?;
    w.write_char(':')?;
    let sec = sec + t.nanosecond() / 1_000_000_000;
    write_hundreds(w, sec as u8)?;
    w.write_char(' ')?;
    OffsetFormat {
        precision: OffsetPrecision::Minutes,
        colons: Colons::None,
        allow_zulu: false,
        padding: Pad::Zero,
    }
    .format(w, off)
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

/// Sink that counts the number of bytes written to it.
#[cfg(not(any(feature = "alloc", feature = "std")))]
struct CountingSink {
    written: usize,
}

#[cfg(not(any(feature = "alloc", feature = "std")))]
impl CountingSink {
    fn new() -> Self {
        Self { written: 0 }
    }

    fn chars_written(&self) -> usize {
        self.written
    }
}

#[cfg(not(any(feature = "alloc", feature = "std")))]
impl Write for CountingSink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.written = self.written.checked_add(s.chars().count()).ok_or(fmt::Error)?;
        Ok(())
    }
}

// `Write` adaptor that only emits up to `max` characters.
#[cfg(not(any(feature = "alloc", feature = "std")))]
struct TruncatingWriter<'a, 'b> {
    formatter: &'a mut fmt::Formatter<'b>,
    chars_remaining: usize,
}

#[cfg(not(any(feature = "alloc", feature = "std")))]
impl<'a, 'b> TruncatingWriter<'a, 'b> {
    fn new(formatter: &'a mut fmt::Formatter<'b>, max: usize) -> Self {
        Self { formatter, chars_remaining: max }
    }
}

#[cfg(not(any(feature = "alloc", feature = "std")))]
impl<'a, 'b> Write for TruncatingWriter<'a, 'b> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let max = self.chars_remaining;
        let char_count = s.chars().count();
        let (s, count) = if char_count <= max {
            (s, char_count)
        } else {
            let (i, _) = s.char_indices().nth(max).unwrap();
            (&s[..i], max)
        };
        self.chars_remaining -= count;
        self.formatter.write_str(s)
    }
}

#[cfg(test)]
#[cfg(any(feature = "alloc", feature = "std"))]
mod tests {
    use super::{Colons, OffsetFormat, OffsetPrecision, Pad};
    use crate::format::{FormattingSpec, ParseError, StrftimeItems};
    use crate::{DateTime, FixedOffset};
    #[cfg(any(feature = "alloc", feature = "std"))]
    use crate::{NaiveDate, NaiveTime, TimeZone, Timelike, Utc};

    #[test]
    #[cfg(any(feature = "alloc", feature = "std"))]
    fn test_date_format() {
        let ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();

        let d = ymd(2012, 3, 4);
        assert_eq!(d.format_to_string("%Y,%C,%y,%G,%g").unwrap(), "2012,20,12,2012,12");
        assert_eq!(d.format_to_string("%m,%b,%h,%B").unwrap(), "03,Mar,Mar,March");
        assert_eq!(d.format_to_string("%d,%e").unwrap(), "04, 4");
        assert_eq!(d.format_to_string("%U,%W,%V").unwrap(), "10,09,09");
        assert_eq!(d.format_to_string("%a,%A,%w,%u").unwrap(), "Sun,Sunday,0,7");
        assert_eq!(d.format_to_string("%j").unwrap(), "064"); // since 2012 is a leap year
        assert_eq!(d.format_to_string("%D,%x").unwrap(), "03/04/12,03/04/12");
        assert_eq!(d.format_to_string("%F").unwrap(), "2012-03-04");
        assert_eq!(d.format_to_string("%v").unwrap(), " 4-Mar-2012");
        assert_eq!(d.format_to_string("%t%n%%%n%t").unwrap(), "\t\n%\n\t");

        // non-four-digit years
        assert_eq!(ymd(12345, 1, 1).format_to_string("%Y").unwrap(), "+12345");
        assert_eq!(ymd(1234, 1, 1).format_to_string("%Y").unwrap(), "1234");
        assert_eq!(ymd(123, 1, 1).format_to_string("%Y").unwrap(), "0123");
        assert_eq!(ymd(12, 1, 1).format_to_string("%Y").unwrap(), "0012");
        assert_eq!(ymd(1, 1, 1).format_to_string("%Y").unwrap(), "0001");
        assert_eq!(ymd(0, 1, 1).format_to_string("%Y").unwrap(), "0000");
        assert_eq!(ymd(-1, 1, 1).format_to_string("%Y").unwrap(), "-0001");
        assert_eq!(ymd(-12, 1, 1).format_to_string("%Y").unwrap(), "-0012");
        assert_eq!(ymd(-123, 1, 1).format_to_string("%Y").unwrap(), "-0123");
        assert_eq!(ymd(-1234, 1, 1).format_to_string("%Y").unwrap(), "-1234");
        assert_eq!(ymd(-12345, 1, 1).format_to_string("%Y").unwrap(), "-12345");

        // corner cases
        assert_eq!(ymd(2007, 12, 31).format_to_string("%G,%U,%W,%V").unwrap(), "2008,52,53,01");
        assert_eq!(ymd(2010, 1, 3).format_to_string("%G,%U,%W,%V").unwrap(), "2009,01,00,53");
    }

    #[test]
    #[cfg(any(feature = "alloc", feature = "std"))]
    fn test_time_format() {
        let t = NaiveTime::from_hms_nano_opt(3, 5, 7, 98765432).unwrap();
        assert_eq!(t.format_to_string("%H,%k,%I,%l,%P,%p").unwrap(), "03, 3,03, 3,am,AM");
        assert_eq!(t.format_to_string("%M").unwrap(), "05");
        assert_eq!(t.format_to_string("%S,%f,%.f").unwrap(), "07,098765432,.098765432");
        assert_eq!(t.format_to_string("%.3f,%.6f,%.9f").unwrap(), ".098,.098765,.098765432");
        assert_eq!(t.format_to_string("%R").unwrap(), "03:05");
        assert_eq!(t.format_to_string("%T,%X").unwrap(), "03:05:07,03:05:07");
        assert_eq!(t.format_to_string("%r").unwrap(), "03:05:07 AM");
        assert_eq!(t.format_to_string("%t%n%%%n%t").unwrap(), "\t\n%\n\t");

        let t = NaiveTime::from_hms_micro_opt(3, 5, 7, 432100).unwrap();
        assert_eq!(t.format_to_string("%S,%f,%.f").unwrap(), "07,432100000,.432100");
        assert_eq!(t.format_to_string("%.3f,%.6f,%.9f").unwrap(), ".432,.432100,.432100000");

        let t = NaiveTime::from_hms_milli_opt(3, 5, 7, 210).unwrap();
        assert_eq!(t.format_to_string("%S,%f,%.f").unwrap(), "07,210000000,.210");
        assert_eq!(t.format_to_string("%.3f,%.6f,%.9f").unwrap(), ".210,.210000,.210000000");

        let t = NaiveTime::from_hms_opt(3, 5, 7).unwrap();
        assert_eq!(t.format_to_string("%S,%f,%.f").unwrap(), "07,000000000,");
        assert_eq!(t.format_to_string("%.3f,%.6f,%.9f").unwrap(), ".000,.000000,.000000000");

        // corner cases
        assert_eq!(
            NaiveTime::from_hms_opt(13, 57, 9).unwrap().format_to_string("%r").unwrap(),
            "01:57:09 PM"
        );
        assert_eq!(
            NaiveTime::from_hms_milli_opt(23, 59, 59, 1_000)
                .unwrap()
                .format_to_string("%X")
                .unwrap(),
            "23:59:60"
        );
    }

    #[test]
    #[cfg(any(feature = "alloc", feature = "std"))]
    fn test_datetime_format() {
        let dt =
            NaiveDate::from_ymd_opt(2010, 9, 8).unwrap().and_hms_milli_opt(7, 6, 54, 321).unwrap();
        assert_eq!(dt.format_to_string("%c").unwrap(), "Wed Sep  8 07:06:54 2010");
        assert_eq!(dt.format_to_string("%s").unwrap(), "1283929614");
        assert_eq!(dt.format_to_string("%t%n%%%n%t").unwrap(), "\t\n%\n\t");

        // a horror of leap second: coming near to you.
        let dt = NaiveDate::from_ymd_opt(2012, 6, 30)
            .unwrap()
            .and_hms_milli_opt(23, 59, 59, 1_000)
            .unwrap();
        assert_eq!(dt.format_to_string("%c").unwrap(), "Sat Jun 30 23:59:60 2012");
        assert_eq!(dt.format_to_string("%s").unwrap(), "1341100799"); // not 1341100800, it's intentional.
    }

    #[test]
    fn test_datetime_format_alignment() -> Result<(), ParseError> {
        let datetime = Utc
            .with_ymd_and_hms(2007, 1, 2, 12, 34, 56)
            .unwrap()
            .with_nanosecond(123456789)
            .unwrap();

        // Item::Literal, odd number of padding bytes.
        let fmtr = FormattingSpec::<DateTime<Utc>, _>::from_items(StrftimeItems::new("%%"))?;
        let percent = datetime.format_with(&fmtr);
        assert_eq!("   %", format!("{:>4}", percent));
        assert_eq!("%   ", format!("{:<4}", percent));
        assert_eq!(" %  ", format!("{:^4}", percent));

        // Item::Numeric, custom non-ASCII padding character
        let fmtr = FormattingSpec::<DateTime<Utc>, _>::from_items(StrftimeItems::new("%Y"))?;
        let year = datetime.format_with(&fmtr);
        assert_eq!("——2007", format!("{:—>6}", year));
        assert_eq!("2007——", format!("{:—<6}", year));
        assert_eq!("—2007—", format!("{:—^6}", year));

        // Item::Fixed
        let fmtr = FormattingSpec::<DateTime<Utc>, _>::from_items(StrftimeItems::new("%Z"))?;
        let tz = datetime.format_with(&fmtr);
        assert_eq!("  UTC", format!("{:>5}", tz));
        assert_eq!("UTC  ", format!("{:<5}", tz));
        assert_eq!(" UTC ", format!("{:^5}", tz));

        // [Item::Numeric, Item::Space, Item::Literal, Item::Space, Item::Numeric]
        let fmtr = FormattingSpec::<DateTime<Utc>, _>::from_items(StrftimeItems::new("%Y %B %d"))?;
        let ymd = datetime.format_with(&fmtr);
        assert_eq!("  2007 January 02", format!("{:>17}", ymd));
        assert_eq!("2007 January 02  ", format!("{:<17}", ymd));
        assert_eq!(" 2007 January 02 ", format!("{:^17}", ymd));

        // Truncated
        let fmtr = FormattingSpec::<DateTime<Utc>, _>::from_items(StrftimeItems::new("%T%.6f"))?;
        let time = datetime.format_with(&fmtr);
        assert_eq!("12:34:56.1234", format!("{:.13}", time));
        Ok(())
    }

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
