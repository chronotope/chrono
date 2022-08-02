use super::{Fixed, Item, Numeric, Pad};

/// Useful macro
#[macro_export]
macro_rules! items {

    ( $pad:expr;   $( $i:tt ),+  $(,)?) => {
        {
            #[allow(unused_imports)]
            use $crate::format::Item::{*, Numeric as N, Fixed as F};
            #[allow(unused_imports)]
            use $crate::format::Fixed::*;
            #[allow(unused_imports)]
            use $crate::format::Numeric::*;
            #[allow(unused_imports)]
            use $crate::format::Pad::{Zero, Space, None as NoPadding};
            &[
                $(
                    __item_with_pad!($pad, $i),
                )*
            ]
        }
    };

    ( $( $i:expr ),+ $(,)?) => {
        {
            #[allow(unused_imports)]
            use $crate::format::Item::{*, Numeric as N, Fixed as F};
            #[allow(unused_imports)]
            use $crate::format::Fixed::*;
            #[allow(unused_imports)]
            use $crate::format::Numeric::*;
            #[allow(unused_imports)]
            use $crate::format::Pad::{Zero, Space, None as NoPadding};
            &[
                $(
                    __item!($i),
                )*
            ]
        }
    };

}

#[doc(hidden)]
#[macro_export]
macro_rules! __item_with_pad {
    // plugs in the default padding
    // eg year, month
    ( $pad:expr, $item:ident ) => {
        $crate::format::literal::$item($pad)
    };

    // user provided padding
    // eg year(Pad::Zero), etc
    ( $_:expr, $item:literal ) => {
        $crate::format::Item::Literal($item)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __item {
    // user provided padding
    // eg year(Pad::Zero), etc
    ( $item:literal ) => {
        $crate::format::Item::Literal($item)
    };

    // user provided padding
    // eg year(Pad::Zero), etc
    ( $item:expr ) => {
        $item
    };
}

#[cfg(test)]
mod tests {
    use crate::format::{Item, Numeric, Pad, StrftimeItems};

    const ISO8601_A: &[Item<'static>] = items![
        Zero; year, "-", month, "-", day, "T", hour, ":", minute, ":", second, "Z"
    ];

    const ISO8601_B: &[Item<'static>] = items![
        super::year(Zero),
        "-",
        super::month(Zero),
        "-",
        super::day(Zero),
        "T",
        super::hour(Zero),
        ":",
        super::minute(Zero),
        ":",
        super::second(Zero),
        "Z"
    ];

    const ISO8601_C: &[Item<'static>] = &[
        super::year(Pad::Zero),
        super::lit("-"),
        super::month(Pad::Zero),
        super::lit("-"),
        super::day(Pad::Zero),
        super::lit("T"),
        super::hour(Pad::Zero),
        super::lit(":"),
        super::minute(Pad::Zero),
        super::lit(":"),
        super::second(Pad::Zero),
        super::lit("Z"),
    ];

    const ISO8601_D: &[Item<'static>] = items![
        Numeric(Year, Zero),
        "-",
        Numeric(Month, Zero),
        "-",
        Numeric(Day, Zero),
        "T",
        Numeric(Hour, Zero),
        ":",
        Numeric(Minute, Zero),
        ":",
        Numeric(Second, Zero),
        "Z",
    ];

    const ISO8601_E: &[Item<'static>] = items![
        N(Year, Zero),
        "-",
        N(Month, Zero),
        "-",
        N(Day, Zero),
        "T",
        N(Hour, Zero),
        ":",
        N(Minute, Zero),
        ":",
        N(Second, Zero),
        "Z",
    ];

    const ISO8601_F: &[Item<'static>] = &[
        Item::Numeric(Numeric::Year, Pad::Zero),
        Item::Literal("-"),
        Item::Numeric(Numeric::Month, Pad::Zero),
        Item::Literal("-"),
        Item::Numeric(Numeric::Day, Pad::Zero),
        Item::Literal("T"),
        Item::Numeric(Numeric::Hour, Pad::Zero),
        Item::Literal(":"),
        Item::Numeric(Numeric::Minute, Pad::Zero),
        Item::Literal(":"),
        Item::Numeric(Numeric::Second, Pad::Zero),
        Item::Literal("Z"),
    ];

    #[test]
    fn test_items_strftime_equivalent() {
        assert_eq!(
            ISO8601_A.to_vec(),
            StrftimeItems::new("%Y-%m-%dT%H:%M:%SZ").collect::<Vec<_>>(),
        );
        assert_eq!(
            ISO8601_B.to_vec(),
            StrftimeItems::new("%Y-%m-%dT%H:%M:%SZ").collect::<Vec<_>>(),
        );
        assert_eq!(
            ISO8601_C.to_vec(),
            StrftimeItems::new("%Y-%m-%dT%H:%M:%SZ").collect::<Vec<_>>(),
        );
        assert_eq!(
            ISO8601_D.to_vec(),
            StrftimeItems::new("%Y-%m-%dT%H:%M:%SZ").collect::<Vec<_>>(),
        );
        assert_eq!(
            ISO8601_E.to_vec(),
            StrftimeItems::new("%Y-%m-%dT%H:%M:%SZ").collect::<Vec<_>>(),
        );
        assert_eq!(
            ISO8601_F.to_vec(),
            StrftimeItems::new("%Y-%m-%dT%H:%M:%SZ").collect::<Vec<_>>(),
        );
    }
}

/// Produces the `Item` for ...
pub const fn lit(s: &'static str) -> Item<'static> {
    Item::Literal(s)
}

/// Produces the `Item` for ...
pub const fn space(s: &'static str) -> Item<'static> {
    Item::Space(s)
}

/// Produces the `Item` for ...
pub const fn year(pad: Pad) -> Item<'static> {
    Item::Numeric(Numeric::Year, pad)
}

/// Produces the `Item` for ...
pub const fn year00(pad: Pad) -> Item<'static> {
    Item::Numeric(Numeric::YearMod100, pad)
}

/// Produces the `Item` for ...
pub const fn month(pad: Pad) -> Item<'static> {
    Item::Numeric(Numeric::Month, pad)
}

/// Produces the `Item` for ...
pub const fn short_month() -> Item<'static> {
    Item::Fixed(Fixed::ShortMonthName)
}

/// Produces the `Item` for ...
pub const fn long_month() -> Item<'static> {
    Item::Fixed(Fixed::LongMonthName)
}

/// Produces the `Item` for ...
pub const fn day(pad: Pad) -> Item<'static> {
    Item::Numeric(Numeric::Day, pad)
}

/// Produces the `Item` for ...
pub const fn short_day() -> Item<'static> {
    Item::Fixed(Fixed::ShortWeekdayName)
}

/// Produces the `Item` for ...
pub const fn long_day() -> Item<'static> {
    Item::Fixed(Fixed::LongWeekdayName)
}

/// Produces the `Item` for ...
pub const fn hour(pad: Pad) -> Item<'static> {
    Item::Numeric(Numeric::Hour, pad)
}

/// Produces the `Item` for ...
pub const fn hour12(pad: Pad) -> Item<'static> {
    Item::Numeric(Numeric::Hour12, pad)
}

/// Produces the `Item` for ...
pub const fn minute(pad: Pad) -> Item<'static> {
    Item::Numeric(Numeric::Minute, pad)
}

/// Produces the `Item` for ...
pub const fn second(pad: Pad) -> Item<'static> {
    Item::Numeric(Numeric::Second, pad)
}

// remainig from Numeric
//     YearDiv100,
//     IsoYear,
//     IsoYearDiv100,
//     IsoYearMod100,
//     WeekFromSun,
//     WeekFromMon,
//     IsoWeek,
//     NumDaysFromSun,
//     WeekdayFromMon,
//     Ordinal,
//     Hour,
//     Hour12,
//     Minute,
//     Second,
//     Nanosecond,
//     Timestamp,

// remainin from Fixed
// LowerAmPm,
// UpperAmPm,
// Nanosecond,
// Nanosecond3,
// Nanosecond6,
// Nanosecond9,
// TimezoneName,
// TimezoneOffsetColon,
//  TimezoneOffsetColonZ,
// TimezoneOffset,
//  TimezoneOffsetZ,
//     RFC2822,
//     RFC3339,
