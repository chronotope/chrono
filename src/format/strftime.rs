// This is a part of rust-chrono.
// Copyright (c) 2015, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

/*!
`strftime`/`strptime`-inspired date and time formatting syntax.

## Specifiers

The following specifiers are available both to formatting and parsing.

Spec. | Example       | Description
----- | ------------- | -----------
      |               | **DATE SPECIFIERS:**
`%Y`  | `2001`        | The full proleptic Gregorian year, zero-padded to 4 digits. [1]
`%C`  | `20`          | The proleptic Gregorian year divided by 100, zero-padded to 2 digits. [2]
`%y`  | `01`          | The proleptic Gregorian year modulo 100, zero-padded to 2 digits. [2]
      |               |
`%m`  | `07`          | Month number (01--12), zero-padded to 2 digits.
`%b`  | `Jul`         | Abbreviated month name. Always 3 letters.
`%B`  | `July`        | Full month name. Also accepts corresponding abbreviation in parsing.
`%h`  | `Jul`         | Same to `%b`.
      |               |
`%d`  | `08`          | Day number (01--31), zero-padded to 2 digits.
`%e`  | ` 8`          | Same to `%d` but space-padded.
      |               |
`%a`  | `Sun`         | Abbreviated weekday name. Always 3 letters.
`%A`  | `Sunday`      | Full weekday name. Also accepts corresponding abbreviation in parsing.
`%w`  | `0`           | Sunday = 0, Monday = 1, ..., Saturday = 6.
`%u`  | `7`           | Monday = 1, Tuesday = 2, ..., Sunday = 7. (ISO 8601)
      |               |
`%U`  | `28`          | Week number starting with Sunday (00--53), zero-padded to 2 digits. [3]
`%W`  | `27`          | Same to `%U`, but week 1 starts with the first Monday in that year instead.
      |               |
`%G`  | `2001`        | Same to `%Y` but uses the year number in ISO 8601 week date. [4]
`%g`  | `01`          | Same to `%y` but uses the year number in ISO 8601 week date. [4]
`%V`  | `27`          | Same to `%U` but uses the week number in ISO 8601 week date (01--53). [4]
      |               |
`%j`  | `189`         | Day of the year (001--366), zero-padded to 3 digits.
      |               |
`%D`  | `08/07/2001`  | Month-day-year format. Same to `%m/%d/%Y`.
`%x`  | `08/07/2001`  | Same to `%D`.
`%F`  | `2001-07-08`  | Year-month-day format (ISO 8601). Same to `%Y-%m-%d`.
`%v`  | ` 7-Jul-2001` | Day-month-year format. Same to `%e-%b-%Y`.
      |               |
      |               | **TIME SPECIFIERS:**
`%H`  | `00`          | Hour number (00--23), zero-padded to 2 digits.
`%k`  | ` 0`          | Same to `%H` but space-padded.
`%I`  | `12`          | Hour number in 12-hour clocks (01--12), zero-padded to 2 digits.
`%l`  | `12`          | Same to `%I` but space-padded.
      |               |
`%P`  | `am`          | `am` or `pm` in 12-hour clocks.
`%p`  | `AM`          | `AM` or `PM` in 12-hour clocks.
      |               |
`%M`  | `34`          | Minute number (00--59), zero-padded to 2 digits.
`%S`  | `60`          | Second number (00--60), zero-padded to 2 digits. [5]
`%f`  | `026413966`   | The number of nanoseconds since last whole second, zero-padded to 9 digits.
      |               |
`%R`  | `00:34`       | Hour-minute format. Same to `%H:%M`.
`%T`  | `00:34:60`    | Hour-minute-second format. Same to `%H:%M:%S`.
`%x`  | `00:34:60`    | Same to `%T`.
`%r`  | `12:34:60 AM` | Hour-minute-second format in 12-hour clocks. Same to `%I:%M:%S %p`.
      |               |
      |               | **TIME ZONE SPECIFIERS:**
`%Z`  | `ACST`        | Local time zone name.
`%z`  | `+09:30`      | Offset from the local time to UTC (with UTC being `+00:00`).
      |               |
      |               | **DATE & TIME SPECIFIERS:**
`%c`  | `Sun Jul  8 00:34:60 2001` | `ctime` date & time format. Same to `%a %b %e %T %Y` sans `\n`.
`%+`  | `2001-07-08T00:34:60+09:30` | ISO 8601 date & time format. Close to `%Y-%m-%dT%H:%M:%S%z`.
      |               |
`%s`  | `994485899`   | UNIX timestamp, the number of seconds since 1970-01-01 00:00 UTC. [6]
      |               |
      |               | **SPECIAL SPECIFIERS:**
`%t`  |               | Literal tab (`\t`).
`%n`  |               | Literal newline (`\n`).
`%%`  |               | Literal percent sign.

Notes:

1. `%Y`:
   Negative years are allowed in formatting but not in parsing.

2. `%C`, `%y`:
   This is floor division, so 100 BCE (year number -99) will print `-1` and `99` respectively.

3. `%U`:
   Week 1 starts with the first Sunday in that year.
   It is possible to have week 0 for days before the first Sunday.

4. `%G`, `%g`, `%V`:
   Week 1 is the first week with at least 4 days in that year.
   Week 0 does not exist, so this should be used with `%G` or `%g`.

5. `%S`:
   It accounts for leap seconds, so `60` is possible.

6. `%s`:
   This is not padded and can be negative.
   For the purpose of Chrono, it only accounts for non-leap seconds
   so it slightly differs from ISO C `strftime` behavior.

*/

use super::{Item, Numeric, Fixed, Pad};

/// Parsing iterator for `strftime`-like format strings.
#[derive(Clone)]
pub struct StrftimeItems<'a> {
    /// Remaining portion of the string.
    remainder: &'a str,
    /// If the current specifier is composed of multiple formatting items (e.g. `%+`),
    /// parser refers to the statically reconstructed slice of them.
    /// If `recons` is not empty they have to be returned earlier than the `remainder`.
    recons: &'static [Item<'static>],
}

impl<'a> StrftimeItems<'a> {
    /// Creates a new parsing iterator from the `strftime`-like format string.
    pub fn new(s: &'a str) -> StrftimeItems<'a> {
        static FMT_NONE: [Item<'static>; 0] = [];
        StrftimeItems { remainder: s, recons: &FMT_NONE }
    }
}

impl<'a> Iterator for StrftimeItems<'a> {
    type Item = Item<'a>;

    fn next(&mut self) -> Option<Item<'a>> {
        // we have some reconstructed items to return
        if !self.recons.is_empty() {
            let item = self.recons[0];
            self.recons = &self.recons[1..];
            return Some(item);
        }

        match self.remainder.slice_shift_char() {
            // we are done
            None => return None,

            // the next item is a specifier
            Some(('%', remainder)) => {
                self.remainder = remainder;

                let (spec, remainder) = match self.remainder.slice_shift_char() {
                    Some(x) => x,
                    None => return Some(Item::Error), // premature end of string
                };
                self.remainder = remainder;

                macro_rules! recons {
                    [$head:expr, $($tail:expr),+] => ({
                        const RECONS: &'static [Item<'static>] = &[$($tail),+];
                        self.recons = RECONS;
                        $head
                    })
                }

                match spec {
                    'A' => Some(fix!(LongWeekdayName)),
                    'B' => Some(fix!(LongMonthName)),
                    'C' => Some(num0!(YearDiv100)),
                    'D' => Some(recons![num0!(Month), lit!("/"), num0!(Day), lit!("/"),
                                        num0!(YearMod100)]),
                    'F' => Some(recons![num0!(Year), lit!("-"), num0!(Month), lit!("-"),
                                        num0!(Day)]),
                    'G' => Some(num0!(IsoYear)),
                    'H' => Some(num0!(Hour)),
                    'I' => Some(num0!(Hour12)),
                    'M' => Some(num0!(Minute)),
                    'P' => Some(fix!(LowerAmPm)),
                    'R' => Some(recons![num0!(Hour), lit!(":"), num0!(Minute)]),
                    'S' => Some(num0!(Second)),
                    'T' => Some(recons![num0!(Hour), lit!(":"), num0!(Minute), lit!(":"),
                                        num0!(Second)]),
                    'U' => Some(num0!(WeekFromSun)),
                    'V' => Some(num0!(IsoWeek)),
                    'W' => Some(num0!(WeekFromMon)),
                    'X' => Some(recons![num0!(Hour), lit!(":"), num0!(Minute), lit!(":"),
                                        num0!(Second)]),
                    'Y' => Some(num0!(Year)),
                    'Z' => Some(fix!(TimezoneName)),
                    'a' => Some(fix!(ShortWeekdayName)),
                    'b' => Some(fix!(ShortMonthName)),
                    'c' => Some(recons![fix!(ShortWeekdayName), sp!(" "), fix!(ShortMonthName),
                                        sp!(" "), nums!(Day), sp!(" "), num0!(Hour), lit!(":"),
                                        num0!(Minute), lit!(":"), num0!(Second), sp!(" "),
                                        num0!(Year)]),
                    'd' => Some(num0!(Day)),
                    'e' => Some(nums!(Day)),
                    'f' => Some(num0!(Nanosecond)),
                    'g' => Some(num0!(IsoYearMod100)),
                    'h' => Some(fix!(ShortMonthName)),
                    'j' => Some(num0!(Ordinal)),
                    'k' => Some(nums!(Hour)),
                    'l' => Some(nums!(Hour12)),
                    'm' => Some(num0!(Month)),
                    'n' => Some(sp!("\n")),
                    'p' => Some(fix!(UpperAmPm)),
                    'r' => Some(recons![num0!(Hour12), lit!(":"), num0!(Minute), lit!(":"),
                                        num0!(Second), sp!(" "), fix!(UpperAmPm)]),
                    's' => Some(num!(Timestamp)),
                    't' => Some(sp!("\t")),
                    'u' => Some(num!(WeekdayFromMon)),
                    'v' => Some(recons![nums!(Day), lit!("-"), fix!(ShortMonthName), lit!("-"),
                                        num0!(Year)]),
                    'w' => Some(num!(NumDaysFromSun)),
                    'x' => Some(recons![num0!(Month), lit!("/"), num0!(Day), lit!("/"),
                                        num0!(YearMod100)]),
                    'y' => Some(num0!(YearMod100)),
                    'z' => Some(fix!(TimezoneOffset)),
                    '+' => Some(fix!(RFC3339)),
                    '%' => Some(lit!("%")),
                    _ => Some(Item::Error), // no such specifier
                }
            },

            // the next item is space
            Some((c, _)) if c.is_whitespace() => {
                // `%` is not a whitespace, so `c != '%'` is redundant
                let nextspec = self.remainder.find(|c: char| !c.is_whitespace())
                                             .unwrap_or(self.remainder.len());
                assert!(nextspec > 0);
                let item = sp!(&self.remainder[..nextspec]);
                self.remainder = &self.remainder[nextspec..];
                Some(item)
            },

            // the next item is literal
            _ => {
                let nextspec = self.remainder.find(|c: char| c.is_whitespace() || c == '%')
                                             .unwrap_or(self.remainder.len());
                assert!(nextspec > 0);
                let item = lit!(&self.remainder[..nextspec]);
                self.remainder = &self.remainder[nextspec..];
                Some(item)
            },
        }
    }
}

#[cfg(test)]
#[test]
fn test_strftime_items() {
    fn parse_and_collect<'a>(s: &'a str) -> Vec<Item<'a>> {
        // map any error into `[Item::Error]`. useful for easy testing.
        let items = StrftimeItems::new(s);
        let items = items.map(|spec| if spec == Item::Error {None} else {Some(spec)});
        items.collect::<Option<Vec<_>>>().unwrap_or(vec![Item::Error])
    }

    assert_eq!(parse_and_collect(""), []);
    assert_eq!(parse_and_collect(" \t\n\r "), [sp!(" \t\n\r ")]);
    assert_eq!(parse_and_collect("hello?"), [lit!("hello?")]);
    assert_eq!(parse_and_collect("a  b\t\nc"), [lit!("a"), sp!("  "), lit!("b"), sp!("\t\n"),
                                                lit!("c")]);
    assert_eq!(parse_and_collect("100%%"), [lit!("100"), lit!("%")]);
    assert_eq!(parse_and_collect("100%% ok"), [lit!("100"), lit!("%"), sp!(" "), lit!("ok")]);
    assert_eq!(parse_and_collect("%%PDF-1.0"), [lit!("%"), lit!("PDF-1.0")]);
    assert_eq!(parse_and_collect("%Y-%m-%d"), [num0!(Year), lit!("-"), num0!(Month), lit!("-"),
                                               num0!(Day)]);
    assert_eq!(parse_and_collect("[%F]"), parse_and_collect("[%Y-%m-%d]"));
    assert_eq!(parse_and_collect("%m %d"), [num0!(Month), sp!(" "), num0!(Day)]);
    assert_eq!(parse_and_collect("%"), [Item::Error]);
    assert_eq!(parse_and_collect("%%"), [lit!("%")]);
    assert_eq!(parse_and_collect("%%%"), [Item::Error]);
    assert_eq!(parse_and_collect("%%%%"), [lit!("%"), lit!("%")]);
    assert_eq!(parse_and_collect("foo%?"), [Item::Error]);
    assert_eq!(parse_and_collect("bar%42"), [Item::Error]);
    assert_eq!(parse_and_collect("quux% +"), [Item::Error]);
}

