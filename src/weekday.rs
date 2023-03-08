use core::fmt;

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

/// The day of week.
///
/// The order of the days of week depends on the context.
/// (This is why this type does *not* implement `PartialOrd` or `Ord` traits.)
/// One should prefer `*_from_monday` or `*_from_sunday` methods to get the correct result.
#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
#[cfg_attr(feature = "rustc-serialize", derive(RustcEncodable, RustcDecodable))]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Weekday {
    /// Monday.
    Mon = 0,
    /// Tuesday.
    Tue = 1,
    /// Wednesday.
    Wed = 2,
    /// Thursday.
    Thu = 3,
    /// Friday.
    Fri = 4,
    /// Saturday.
    Sat = 5,
    /// Sunday.
    Sun = 6,
}

impl Weekday {
    /// The next day in the week.
    ///
    /// `w`:        | `Mon` | `Tue` | `Wed` | `Thu` | `Fri` | `Sat` | `Sun`
    /// ----------- | ----- | ----- | ----- | ----- | ----- | ----- | -----
    /// `w.succ()`: | `Tue` | `Wed` | `Thu` | `Fri` | `Sat` | `Sun` | `Mon`
    #[inline]
    pub fn succ(&self) -> Weekday {
        match *self {
            Weekday::Mon => Weekday::Tue,
            Weekday::Tue => Weekday::Wed,
            Weekday::Wed => Weekday::Thu,
            Weekday::Thu => Weekday::Fri,
            Weekday::Fri => Weekday::Sat,
            Weekday::Sat => Weekday::Sun,
            Weekday::Sun => Weekday::Mon,
        }
    }

    /// The previous day in the week.
    ///
    /// `w`:        | `Mon` | `Tue` | `Wed` | `Thu` | `Fri` | `Sat` | `Sun`
    /// ----------- | ----- | ----- | ----- | ----- | ----- | ----- | -----
    /// `w.pred()`: | `Sun` | `Mon` | `Tue` | `Wed` | `Thu` | `Fri` | `Sat`
    #[inline]
    pub fn pred(&self) -> Weekday {
        match *self {
            Weekday::Mon => Weekday::Sun,
            Weekday::Tue => Weekday::Mon,
            Weekday::Wed => Weekday::Tue,
            Weekday::Thu => Weekday::Wed,
            Weekday::Fri => Weekday::Thu,
            Weekday::Sat => Weekday::Fri,
            Weekday::Sun => Weekday::Sat,
        }
    }

    /// Returns a day-of-week number starting from Monday = 1. (ISO 8601 weekday number)
    ///
    /// `w`:                      | `Mon` | `Tue` | `Wed` | `Thu` | `Fri` | `Sat` | `Sun`
    /// ------------------------- | ----- | ----- | ----- | ----- | ----- | ----- | -----
    /// `w.number_from_monday()`: | 1     | 2     | 3     | 4     | 5     | 6     | 7
    #[inline]
    pub const fn number_from_monday(&self) -> u32 {
        self.num_days_from(Weekday::Mon) + 1
    }

    /// Returns a day-of-week number starting from Sunday = 1.
    ///
    /// `w`:                      | `Mon` | `Tue` | `Wed` | `Thu` | `Fri` | `Sat` | `Sun`
    /// ------------------------- | ----- | ----- | ----- | ----- | ----- | ----- | -----
    /// `w.number_from_sunday()`: | 2     | 3     | 4     | 5     | 6     | 7     | 1
    #[inline]
    pub const fn number_from_sunday(&self) -> u32 {
        self.num_days_from(Weekday::Sun) + 1
    }

    /// Returns a day-of-week number starting from Monday = 0.
    ///
    /// `w`:                        | `Mon` | `Tue` | `Wed` | `Thu` | `Fri` | `Sat` | `Sun`
    /// --------------------------- | ----- | ----- | ----- | ----- | ----- | ----- | -----
    /// `w.num_days_from_monday()`: | 0     | 1     | 2     | 3     | 4     | 5     | 6
    #[inline]
    pub const fn num_days_from_monday(&self) -> u32 {
        self.num_days_from(Weekday::Mon)
    }

    /// Returns a day-of-week number starting from Sunday = 0.
    ///
    /// `w`:                        | `Mon` | `Tue` | `Wed` | `Thu` | `Fri` | `Sat` | `Sun`
    /// --------------------------- | ----- | ----- | ----- | ----- | ----- | ----- | -----
    /// `w.num_days_from_sunday()`: | 1     | 2     | 3     | 4     | 5     | 6     | 0
    #[inline]
    pub const fn num_days_from_sunday(&self) -> u32 {
        self.num_days_from(Weekday::Sun)
    }

    /// Returns a day-of-week number starting from the parameter `day` (D) = 0.
    ///
    /// `w`:                        | `D` | `D+1` | `D+2` | `D+3` | `D+4` | `D+5` | `D+6`
    /// --------------------------- | ----- | ----- | ----- | ----- | ----- | ----- | -----
    /// `w.num_days_from(wd)`:      | 0     | 1     | 2     | 3     | 4     | 5     | 6
    #[inline]
    pub(crate) const fn num_days_from(&self, day: Weekday) -> u32 {
        (*self as u32 + 7 - day as u32) % 7
    }
}

impl fmt::Display for Weekday {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match *self {
            Weekday::Mon => "Mon",
            Weekday::Tue => "Tue",
            Weekday::Wed => "Wed",
            Weekday::Thu => "Thu",
            Weekday::Fri => "Fri",
            Weekday::Sat => "Sat",
            Weekday::Sun => "Sun",
        })
    }
}

/// Any weekday can be represented as an integer from 0 to 6, which equals to
/// [`Weekday::num_days_from_monday`](#method.num_days_from_monday) in this implementation.
/// Do not heavily depend on this though; use explicit methods whenever possible.
impl num_traits::FromPrimitive for Weekday {
    #[inline]
    fn from_i64(n: i64) -> Option<Weekday> {
        match n {
            0 => Some(Weekday::Mon),
            1 => Some(Weekday::Tue),
            2 => Some(Weekday::Wed),
            3 => Some(Weekday::Thu),
            4 => Some(Weekday::Fri),
            5 => Some(Weekday::Sat),
            6 => Some(Weekday::Sun),
            _ => None,
        }
    }

    #[inline]
    fn from_u64(n: u64) -> Option<Weekday> {
        match n {
            0 => Some(Weekday::Mon),
            1 => Some(Weekday::Tue),
            2 => Some(Weekday::Wed),
            3 => Some(Weekday::Thu),
            4 => Some(Weekday::Fri),
            5 => Some(Weekday::Sat),
            6 => Some(Weekday::Sun),
            _ => None,
        }
    }
}

/// An error resulting from reading `Weekday` value with `FromStr`.
#[derive(Clone, PartialEq, Eq)]
pub struct ParseWeekdayError {
    pub(crate) _dummy: (),
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for ParseWeekdayError {}

impl fmt::Display for ParseWeekdayError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_fmt(format_args!("{:?}", self))
    }
}

impl fmt::Debug for ParseWeekdayError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ParseWeekdayError {{ .. }}")
    }
}

#[cfg(test)]
mod tests {
    use num_traits::FromPrimitive;

    use super::Weekday;

    #[test]
    fn test_num_days_from() {
        for i in 0..7 {
            let base_day = Weekday::from_u64(i).unwrap();

            assert_eq!(base_day.num_days_from_monday(), base_day.num_days_from(Weekday::Mon));
            assert_eq!(base_day.num_days_from_sunday(), base_day.num_days_from(Weekday::Sun));

            assert_eq!(base_day.num_days_from(base_day), 0);

            assert_eq!(base_day.num_days_from(base_day.pred()), 1);
            assert_eq!(base_day.num_days_from(base_day.pred().pred()), 2);
            assert_eq!(base_day.num_days_from(base_day.pred().pred().pred()), 3);
            assert_eq!(base_day.num_days_from(base_day.pred().pred().pred().pred()), 4);
            assert_eq!(base_day.num_days_from(base_day.pred().pred().pred().pred().pred()), 5);
            assert_eq!(
                base_day.num_days_from(base_day.pred().pred().pred().pred().pred().pred()),
                6
            );

            assert_eq!(base_day.num_days_from(base_day.succ()), 6);
            assert_eq!(base_day.num_days_from(base_day.succ().succ()), 5);
            assert_eq!(base_day.num_days_from(base_day.succ().succ().succ()), 4);
            assert_eq!(base_day.num_days_from(base_day.succ().succ().succ().succ()), 3);
            assert_eq!(base_day.num_days_from(base_day.succ().succ().succ().succ().succ()), 2);
            assert_eq!(
                base_day.num_days_from(base_day.succ().succ().succ().succ().succ().succ()),
                1
            );
        }
    }
}

// the actual `FromStr` implementation is in the `format` module to leverage the existing code

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
mod weekday_serde {
    use super::Weekday;
    use core::fmt;
    use serde::{de, ser};

    impl ser::Serialize for Weekday {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: ser::Serializer,
        {
            serializer.collect_str(&self)
        }
    }

    struct WeekdayVisitor;

    impl<'de> de::Visitor<'de> for WeekdayVisitor {
        type Value = Weekday;

        fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("Weekday")
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            value.parse().map_err(|_| E::custom("short or long weekday names expected"))
        }
    }

    impl<'de> de::Deserialize<'de> for Weekday {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: de::Deserializer<'de>,
        {
            deserializer.deserialize_str(WeekdayVisitor)
        }
    }

    #[test]
    fn test_serde_serialize() {
        use serde_json::to_string;
        use Weekday::*;

        let cases: Vec<(Weekday, &str)> = vec![
            (Mon, "\"Mon\""),
            (Tue, "\"Tue\""),
            (Wed, "\"Wed\""),
            (Thu, "\"Thu\""),
            (Fri, "\"Fri\""),
            (Sat, "\"Sat\""),
            (Sun, "\"Sun\""),
        ];

        for (weekday, expected_str) in cases {
            let string = to_string(&weekday).unwrap();
            assert_eq!(string, expected_str);
        }
    }

    #[test]
    fn test_serde_deserialize() {
        use serde_json::from_str;
        use Weekday::*;

        let cases: Vec<(&str, Weekday)> = vec![
            ("\"mon\"", Mon),
            ("\"MONDAY\"", Mon),
            ("\"MonDay\"", Mon),
            ("\"mOn\"", Mon),
            ("\"tue\"", Tue),
            ("\"tuesday\"", Tue),
            ("\"wed\"", Wed),
            ("\"wednesday\"", Wed),
            ("\"thu\"", Thu),
            ("\"thursday\"", Thu),
            ("\"fri\"", Fri),
            ("\"friday\"", Fri),
            ("\"sat\"", Sat),
            ("\"saturday\"", Sat),
            ("\"sun\"", Sun),
            ("\"sunday\"", Sun),
        ];

        for (str, expected_weekday) in cases {
            let weekday = from_str::<Weekday>(str).unwrap();
            assert_eq!(weekday, expected_weekday);
        }

        let errors: Vec<&str> =
            vec!["\"not a weekday\"", "\"monDAYs\"", "\"mond\"", "mon", "\"thur\"", "\"thurs\""];

        for str in errors {
            from_str::<Weekday>(str).unwrap_err();
        }
    }
}
