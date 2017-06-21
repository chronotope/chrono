// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! ISO 8601 date and time with time zone.

use std::{str, fmt, hash};
use std::cmp::Ordering;
use std::ops::{Add, Sub};
#[cfg(feature = "rustc-serialize")]
use std::ops::Deref;
use std::time::{SystemTime, UNIX_EPOCH};
use oldtime::Duration as OldDuration;

use {Weekday, Timelike, Datelike};
use offset::{TimeZone, Offset, Utc, Local, FixedOffset};
use naive::{NaiveTime, NaiveDateTime, IsoWeek};
use Date;
use format::{Item, Numeric, Pad, Fixed};
use format::{parse, Parsed, ParseError, ParseResult, DelayedFormat, StrftimeItems};

/// ISO 8601 combined date and time with time zone.
///
/// There are some constructors implemented here (the `from_*` methods), but
/// the general-purpose constructors are all via the methods on the
/// [`TimeZone`](./offset/trait.TimeZone.html) implementations.
#[derive(Clone)]
pub struct DateTime<Tz: TimeZone> {
    datetime: NaiveDateTime,
    offset: Tz::Offset,
}

/// A DateTime that can be deserialized from a timestamp
///
/// A timestamp here is seconds since the epoch
#[cfg(feature = "rustc-serialize")]
pub struct TsSeconds<Tz: TimeZone>(DateTime<Tz>);

#[cfg(feature = "rustc-serialize")]
impl<Tz: TimeZone> From<TsSeconds<Tz>> for DateTime<Tz> {
    /// Pull the inner DateTime<Tz> out
    fn from(obj: TsSeconds<Tz>) -> DateTime<Tz> {
        obj.0
    }
}

#[cfg(feature = "rustc-serialize")]
impl<Tz: TimeZone> Deref for TsSeconds<Tz> {
    type Target = DateTime<Tz>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}


impl<Tz: TimeZone> DateTime<Tz> {
    /// Makes a new `DateTime` with given *UTC* datetime and offset.
    /// The local datetime should be constructed via the `TimeZone` trait.
    ///
    /// # Example
    ///
    /// ~~~~
    /// use chrono::{DateTime, TimeZone, NaiveDateTime, Utc};
    ///
    /// let dt = DateTime::<Utc>::from_utc(NaiveDateTime::from_timestamp(61, 0), Utc);
    /// assert_eq!(Utc.timestamp(61, 0), dt);
    /// ~~~~
    //
    // note: this constructor is purposedly not named to `new` to discourage the direct usage.
    #[inline]
    pub fn from_utc(datetime: NaiveDateTime, offset: Tz::Offset) -> DateTime<Tz> {
        DateTime { datetime: datetime, offset: offset }
    }

    /// Retrieves a date component.
    #[inline]
    pub fn date(&self) -> Date<Tz> {
        Date::from_utc(self.naive_local().date(), self.offset.clone())
    }

    /// Retrieves a time component.
    /// Unlike `date`, this is not associated to the time zone.
    #[inline]
    pub fn time(&self) -> NaiveTime {
        self.datetime.time() + self.offset.fix()
    }

    /// Returns the number of non-leap seconds since January 1, 1970 0:00:00 UTC
    /// (aka "UNIX timestamp").
    #[inline]
    pub fn timestamp(&self) -> i64 {
        self.datetime.timestamp()
    }

    /// Returns the number of milliseconds since the last second boundary
    ///
    /// warning: in event of a leap second, this may exceed 999
    ///
    /// note: this is not the number of milliseconds since January 1, 1970 0:00:00 UTC
    #[inline]
    pub fn timestamp_subsec_millis(&self) -> u32 {
        self.datetime.timestamp_subsec_millis()
    }

    /// Returns the number of microseconds since the last second boundary
    ///
    /// warning: in event of a leap second, this may exceed 999_999
    ///
    /// note: this is not the number of microseconds since January 1, 1970 0:00:00 UTC
    #[inline]
    pub fn timestamp_subsec_micros(&self) -> u32 {
        self.datetime.timestamp_subsec_micros()
    }

    /// Returns the number of nanoseconds since the last second boundary
    ///
    /// warning: in event of a leap second, this may exceed 999_999_999
    ///
    /// note: this is not the number of nanoseconds since January 1, 1970 0:00:00 UTC
    #[inline]
    pub fn timestamp_subsec_nanos(&self) -> u32 {
        self.datetime.timestamp_subsec_nanos()
    }

    /// Retrieves an associated offset from UTC.
    #[inline]
    pub fn offset<'a>(&'a self) -> &'a Tz::Offset {
        &self.offset
    }

    /// Retrieves an associated time zone.
    #[inline]
    pub fn timezone(&self) -> Tz {
        TimeZone::from_offset(&self.offset)
    }

    /// Changes the associated time zone.
    /// This does not change the actual `DateTime` (but will change the string representation).
    #[inline]
    pub fn with_timezone<Tz2: TimeZone>(&self, tz: &Tz2) -> DateTime<Tz2> {
        tz.from_utc_datetime(&self.datetime)
    }

    /// Adds given `Duration` to the current date and time.
    ///
    /// Returns `None` when it will result in overflow.
    #[inline]
    pub fn checked_add_signed(self, rhs: OldDuration) -> Option<DateTime<Tz>> {
        let datetime = try_opt!(self.datetime.checked_add_signed(rhs));
        Some(DateTime { datetime: datetime, offset: self.offset })
    }

    /// Subtracts given `Duration` from the current date and time.
    ///
    /// Returns `None` when it will result in overflow.
    #[inline]
    pub fn checked_sub_signed(self, rhs: OldDuration) -> Option<DateTime<Tz>> {
        let datetime = try_opt!(self.datetime.checked_sub_signed(rhs));
        Some(DateTime { datetime: datetime, offset: self.offset })
    }

    /// Subtracts another `DateTime` from the current date and time.
    /// This does not overflow or underflow at all.
    #[inline]
    pub fn signed_duration_since<Tz2: TimeZone>(self, rhs: DateTime<Tz2>) -> OldDuration {
        self.datetime.signed_duration_since(rhs.datetime)
    }

    /// Returns a view to the naive UTC datetime.
    #[inline]
    pub fn naive_utc(&self) -> NaiveDateTime {
        self.datetime
    }

    /// Returns a view to the naive local datetime.
    #[inline]
    pub fn naive_local(&self) -> NaiveDateTime {
        self.datetime + self.offset.fix()
    }
}

/// Maps the local datetime to other datetime with given conversion function.
fn map_local<Tz: TimeZone, F>(dt: &DateTime<Tz>, mut f: F) -> Option<DateTime<Tz>>
        where F: FnMut(NaiveDateTime) -> Option<NaiveDateTime> {
    f(dt.naive_local()).and_then(|datetime| dt.timezone().from_local_datetime(&datetime).single())
}

impl DateTime<FixedOffset> {
    /// Parses an RFC 2822 date and time string such as `Tue, 1 Jul 2003 10:52:37 +0200`,
    /// then returns a new `DateTime` with a parsed `FixedOffset`.
    pub fn parse_from_rfc2822(s: &str) -> ParseResult<DateTime<FixedOffset>> {
        const ITEMS: &'static [Item<'static>] = &[Item::Fixed(Fixed::RFC2822)];
        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, ITEMS.iter().cloned()));
        parsed.to_datetime()
    }

    /// Parses an RFC 3339 and ISO 8601 date and time string such as `1996-12-19T16:39:57-08:00`,
    /// then returns a new `DateTime` with a parsed `FixedOffset`.
    ///
    /// Why isn't this named `parse_from_iso8601`? That's because ISO 8601 allows some freedom
    /// over the syntax and RFC 3339 exercises that freedom to rigidly define a fixed format.
    pub fn parse_from_rfc3339(s: &str) -> ParseResult<DateTime<FixedOffset>> {
        const ITEMS: &'static [Item<'static>] = &[Item::Fixed(Fixed::RFC3339)];
        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, ITEMS.iter().cloned()));
        parsed.to_datetime()
    }

    /// Parses a string with the specified format string and
    /// returns a new `DateTime` with a parsed `FixedOffset`.
    /// See the [`format::strftime` module](./format/strftime/index.html)
    /// on the supported escape sequences.
    ///
    /// See also `Offset::datetime_from_str` which gives a local `DateTime` on specific time zone.
    pub fn parse_from_str(s: &str, fmt: &str) -> ParseResult<DateTime<FixedOffset>> {
        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, StrftimeItems::new(fmt)));
        parsed.to_datetime()
    }
}

impl<Tz: TimeZone> DateTime<Tz> where Tz::Offset: fmt::Display {
    /// Returns an RFC 2822 date and time string such as `Tue, 1 Jul 2003 10:52:37 +0200`.
    pub fn to_rfc2822(&self) -> String {
        const ITEMS: &'static [Item<'static>] = &[Item::Fixed(Fixed::RFC2822)];
        self.format_with_items(ITEMS.iter().cloned()).to_string()
    }

    /// Returns an RFC 3339 and ISO 8601 date and time string such as `1996-12-19T16:39:57-08:00`.
    pub fn to_rfc3339(&self) -> String {
        const ITEMS: &'static [Item<'static>] = &[Item::Fixed(Fixed::RFC3339)];
        self.format_with_items(ITEMS.iter().cloned()).to_string()
    }

    /// Formats the combined date and time with the specified formatting items.
    #[inline]
    pub fn format_with_items<'a, I>(&self, items: I) -> DelayedFormat<I>
            where I: Iterator<Item=Item<'a>> + Clone {
        let local = self.naive_local();
        DelayedFormat::new_with_offset(Some(local.date()), Some(local.time()), &self.offset, items)
    }

    /// Formats the combined date and time with the specified format string.
    /// See the [`format::strftime` module](./format/strftime/index.html)
    /// on the supported escape sequences.
    #[inline]
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_with_items(StrftimeItems::new(fmt))
    }
}

impl<Tz: TimeZone> Datelike for DateTime<Tz> {
    #[inline] fn year(&self) -> i32 { self.naive_local().year() }
    #[inline] fn month(&self) -> u32 { self.naive_local().month() }
    #[inline] fn month0(&self) -> u32 { self.naive_local().month0() }
    #[inline] fn day(&self) -> u32 { self.naive_local().day() }
    #[inline] fn day0(&self) -> u32 { self.naive_local().day0() }
    #[inline] fn ordinal(&self) -> u32 { self.naive_local().ordinal() }
    #[inline] fn ordinal0(&self) -> u32 { self.naive_local().ordinal0() }
    #[inline] fn weekday(&self) -> Weekday { self.naive_local().weekday() }
    #[inline] fn iso_week(&self) -> IsoWeek { self.naive_local().iso_week() }

    #[inline]
    fn with_year(&self, year: i32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_year(year))
    }

    #[inline]
    fn with_month(&self, month: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_month(month))
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_month0(month0))
    }

    #[inline]
    fn with_day(&self, day: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_day(day))
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_day0(day0))
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_ordinal(ordinal))
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_ordinal0(ordinal0))
    }
}

impl<Tz: TimeZone> Timelike for DateTime<Tz> {
    #[inline] fn hour(&self) -> u32 { self.naive_local().hour() }
    #[inline] fn minute(&self) -> u32 { self.naive_local().minute() }
    #[inline] fn second(&self) -> u32 { self.naive_local().second() }
    #[inline] fn nanosecond(&self) -> u32 { self.naive_local().nanosecond() }

    #[inline]
    fn with_hour(&self, hour: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_hour(hour))
    }

    #[inline]
    fn with_minute(&self, min: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_minute(min))
    }

    #[inline]
    fn with_second(&self, sec: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_second(sec))
    }

    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<DateTime<Tz>> {
        map_local(self, |datetime| datetime.with_nanosecond(nano))
    }
}

// we need them as automatic impls cannot handle associated types
impl<Tz: TimeZone> Copy for DateTime<Tz> where <Tz as TimeZone>::Offset: Copy {}
unsafe impl<Tz: TimeZone> Send for DateTime<Tz> where <Tz as TimeZone>::Offset: Send {}

impl<Tz: TimeZone, Tz2: TimeZone> PartialEq<DateTime<Tz2>> for DateTime<Tz> {
    fn eq(&self, other: &DateTime<Tz2>) -> bool { self.datetime == other.datetime }
}

impl<Tz: TimeZone> Eq for DateTime<Tz> {
}

impl<Tz: TimeZone> PartialOrd for DateTime<Tz> {
    fn partial_cmp(&self, other: &DateTime<Tz>) -> Option<Ordering> {
        self.datetime.partial_cmp(&other.datetime)
    }
}

impl<Tz: TimeZone> Ord for DateTime<Tz> {
    fn cmp(&self, other: &DateTime<Tz>) -> Ordering { self.datetime.cmp(&other.datetime) }
}

impl<Tz: TimeZone> hash::Hash for DateTime<Tz> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) { self.datetime.hash(state) }
}

impl<Tz: TimeZone> Add<OldDuration> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn add(self, rhs: OldDuration) -> DateTime<Tz> {
        self.checked_add_signed(rhs).expect("`DateTime + Duration` overflowed")
    }
}

impl<Tz: TimeZone> Sub<OldDuration> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn sub(self, rhs: OldDuration) -> DateTime<Tz> {
        self.checked_sub_signed(rhs).expect("`DateTime - Duration` overflowed")
    }
}

impl<Tz: TimeZone> fmt::Debug for DateTime<Tz> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}{:?}", self.naive_local(), self.offset)
    }
}

impl<Tz: TimeZone> fmt::Display for DateTime<Tz> where Tz::Offset: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.naive_local(), self.offset)
    }
}

impl str::FromStr for DateTime<FixedOffset> {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<DateTime<FixedOffset>> {
        const ITEMS: &'static [Item<'static>] = &[
            Item::Space(""), Item::Numeric(Numeric::Year, Pad::Zero),
            Item::Space(""), Item::Literal("-"),
            Item::Space(""), Item::Numeric(Numeric::Month, Pad::Zero),
            Item::Space(""), Item::Literal("-"),
            Item::Space(""), Item::Numeric(Numeric::Day, Pad::Zero),
            Item::Space(""), Item::Literal("T"), // XXX shouldn't this be case-insensitive?
            Item::Space(""), Item::Numeric(Numeric::Hour, Pad::Zero),
            Item::Space(""), Item::Literal(":"),
            Item::Space(""), Item::Numeric(Numeric::Minute, Pad::Zero),
            Item::Space(""), Item::Literal(":"),
            Item::Space(""), Item::Numeric(Numeric::Second, Pad::Zero),
                             Item::Fixed(Fixed::Nanosecond),
            Item::Space(""), Item::Fixed(Fixed::TimezoneOffsetZ),
            Item::Space(""),
        ];

        let mut parsed = Parsed::new();
        try!(parse(&mut parsed, s, ITEMS.iter().cloned()));
        parsed.to_datetime()
    }
}

impl str::FromStr for DateTime<Utc> {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<DateTime<Utc>> {
        s.parse::<DateTime<FixedOffset>>().map(|dt| dt.with_timezone(&Utc))
    }
}

impl str::FromStr for DateTime<Local> {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<DateTime<Local>> {
        s.parse::<DateTime<FixedOffset>>().map(|dt| dt.with_timezone(&Local))
    }
}

impl From<SystemTime> for DateTime<Utc> {
    fn from(t: SystemTime) -> DateTime<Utc> {
        let (sec, nsec) = match t.duration_since(UNIX_EPOCH) {
            Ok(dur) => (dur.as_secs() as i64, dur.subsec_nanos()),
            Err(e) => { // unlikely but should be handled
                let dur = e.duration();
                let (sec, nsec) = (dur.as_secs() as i64, dur.subsec_nanos());
                if nsec == 0 {
                    (-sec, 0)
                } else {
                    (-sec - 1, 1_000_000_000 - nsec)
                }
            },
        };
        Utc.timestamp(sec, nsec)
    }
}

impl From<SystemTime> for DateTime<Local> {
    fn from(t: SystemTime) -> DateTime<Local> {
        DateTime::<Utc>::from(t).with_timezone(&Local)
    }
}

impl<Tz: TimeZone> From<DateTime<Tz>> for SystemTime {
    fn from(dt: DateTime<Tz>) -> SystemTime {
        use std::time::Duration;

        let sec = dt.timestamp();
        let nsec = dt.timestamp_subsec_nanos();
        if sec < 0 {
            // unlikely but should be handled
            UNIX_EPOCH - Duration::new(-sec as u64, 0) + Duration::new(0, nsec)
        } else {
            UNIX_EPOCH + Duration::new(sec as u64, nsec)
        }
    }
}

#[cfg(all(test, any(feature = "rustc-serialize", feature = "serde")))]
fn test_encodable_json<FUtc, FFixed, E>(to_string_utc: FUtc, to_string_fixed: FFixed)
    where FUtc: Fn(&DateTime<Utc>) -> Result<String, E>,
          FFixed: Fn(&DateTime<FixedOffset>) -> Result<String, E>,
          E: ::std::fmt::Debug
{
    assert_eq!(to_string_utc(&Utc.ymd(2014, 7, 24).and_hms(12, 34, 6)).ok(),
               Some(r#""2014-07-24T12:34:06Z""#.into()));

    assert_eq!(to_string_fixed(&FixedOffset::east(3660).ymd(2014, 7, 24).and_hms(12, 34, 6)).ok(),
               Some(r#""2014-07-24T12:34:06+01:01""#.into()));
    assert_eq!(to_string_fixed(&FixedOffset::east(3650).ymd(2014, 7, 24).and_hms(12, 34, 6)).ok(),
               Some(r#""2014-07-24T12:34:06+01:00:50""#.into()));
}

#[cfg(all(test, any(feature = "rustc-serialize", feature = "serde")))]
fn test_decodable_json<FUtc, FFixed, FLocal, E>(utc_from_str: FUtc,
                                                fixed_from_str: FFixed,
                                                local_from_str: FLocal)
    where FUtc: Fn(&str) -> Result<DateTime<Utc>, E>,
          FFixed: Fn(&str) -> Result<DateTime<FixedOffset>, E>,
          FLocal: Fn(&str) -> Result<DateTime<Local>, E>,
          E: ::std::fmt::Debug
{
    // should check against the offset as well (the normal DateTime comparison will ignore them)
    fn norm<Tz: TimeZone>(dt: &Option<DateTime<Tz>>) -> Option<(&DateTime<Tz>, &Tz::Offset)> {
        dt.as_ref().map(|dt| (dt, dt.offset()))
    }

    assert_eq!(norm(&utc_from_str(r#""2014-07-24T12:34:06Z""#).ok()),
               norm(&Some(Utc.ymd(2014, 7, 24).and_hms(12, 34, 6))));
    assert_eq!(norm(&utc_from_str(r#""2014-07-24T13:57:06+01:23""#).ok()),
               norm(&Some(Utc.ymd(2014, 7, 24).and_hms(12, 34, 6))));

    assert_eq!(norm(&fixed_from_str(r#""2014-07-24T12:34:06Z""#).ok()),
               norm(&Some(FixedOffset::east(0).ymd(2014, 7, 24).and_hms(12, 34, 6))));
    assert_eq!(norm(&fixed_from_str(r#""2014-07-24T13:57:06+01:23""#).ok()),
               norm(&Some(FixedOffset::east(60*60 + 23*60).ymd(2014, 7, 24).and_hms(13, 57, 6))));

    // we don't know the exact local offset but we can check that
    // the conversion didn't change the instant itself
    assert_eq!(local_from_str(r#""2014-07-24T12:34:06Z""#)
                   .expect("local shouuld parse"),
               Utc.ymd(2014, 7, 24).and_hms(12, 34, 6));
    assert_eq!(local_from_str(r#""2014-07-24T13:57:06+01:23""#)
                   .expect("local should parse with offset"),
               Utc.ymd(2014, 7, 24).and_hms(12, 34, 6));

    assert!(utc_from_str(r#""2014-07-32T12:34:06Z""#).is_err());
    assert!(fixed_from_str(r#""2014-07-32T12:34:06Z""#).is_err());
}

#[cfg(all(test, feature = "rustc-serialize"))]
fn test_decodable_json_timestamps<FUtc, FFixed, FLocal, E>(utc_from_str: FUtc,
                                                           fixed_from_str: FFixed,
                                                           local_from_str: FLocal)
    where FUtc: Fn(&str) -> Result<TsSeconds<Utc>, E>,
          FFixed: Fn(&str) -> Result<TsSeconds<FixedOffset>, E>,
          FLocal: Fn(&str) -> Result<TsSeconds<Local>, E>,
          E: ::std::fmt::Debug
{
    fn norm<Tz: TimeZone>(dt: &Option<DateTime<Tz>>) -> Option<(&DateTime<Tz>, &Tz::Offset)> {
        dt.as_ref().map(|dt| (dt, dt.offset()))
    }

    assert_eq!(norm(&utc_from_str("0").ok().map(DateTime::from)),
               norm(&Some(Utc.ymd(1970, 1, 1).and_hms(0, 0, 0))));
    assert_eq!(norm(&utc_from_str("-1").ok().map(DateTime::from)),
               norm(&Some(Utc.ymd(1969, 12, 31).and_hms(23, 59, 59))));

    assert_eq!(norm(&fixed_from_str("0").ok().map(DateTime::from)),
               norm(&Some(FixedOffset::east(0).ymd(1970, 1, 1).and_hms(0, 0, 0))));
    assert_eq!(norm(&fixed_from_str("-1").ok().map(DateTime::from)),
               norm(&Some(FixedOffset::east(0).ymd(1969, 12, 31).and_hms(23, 59, 59))));

    assert_eq!(*fixed_from_str("0").expect("0 timestamp should parse"),
               Utc.ymd(1970, 1, 1).and_hms(0, 0, 0));
    assert_eq!(*local_from_str("-1").expect("-1 timestamp should parse"),
               Utc.ymd(1969, 12, 31).and_hms(23, 59, 59));
}

#[cfg(feature = "rustc-serialize")]
mod rustc_serialize {
    use std::fmt;
    use super::{DateTime, TsSeconds};
    use offset::{TimeZone, LocalResult, Utc, Local, FixedOffset};
    use rustc_serialize::{Encodable, Encoder, Decodable, Decoder};

    impl<Tz: TimeZone> Encodable for DateTime<Tz> {
        fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
            format!("{:?}", self).encode(s)
        }
    }

    // try!-like function to convert a LocalResult into a serde-ish Result
    fn from<T, D>(me: LocalResult<T>, d: &mut D) -> Result<T, D::Error>
        where D: Decoder,
              T: fmt::Display,
    {
        match me {
            LocalResult::None => Err(d.error(
                "value is not a legal timestamp")),
            LocalResult::Ambiguous(..) => Err(d.error(
                "value is an ambiguous timestamp")),
            LocalResult::Single(val) => Ok(val)
        }
    }

    impl Decodable for DateTime<FixedOffset> {
        fn decode<D: Decoder>(d: &mut D) -> Result<DateTime<FixedOffset>, D::Error> {
            d.read_str()?.parse::<DateTime<FixedOffset>>()
                    .map_err(|_| d.error("invalid date and time"))
        }
    }

    impl Decodable for TsSeconds<FixedOffset> {
        fn decode<D: Decoder>(d: &mut D) -> Result<TsSeconds<FixedOffset>, D::Error> {
            from(FixedOffset::east(0).timestamp_opt(d.read_i64()?, 0), d)
                .map(|dt| TsSeconds(dt))
        }
    }

    impl Decodable for DateTime<Utc> {
        fn decode<D: Decoder>(d: &mut D) -> Result<DateTime<Utc>, D::Error> {
            d.read_str()?
                .parse::<DateTime<FixedOffset>>()
                .map(|dt| dt.with_timezone(&Utc))
                .map_err(|_| d.error("invalid date and time"))
        }
    }

    impl Decodable for TsSeconds<Utc> {
        fn decode<D: Decoder>(d: &mut D) -> Result<TsSeconds<Utc>, D::Error> {
            from(Utc.timestamp_opt(d.read_i64()?, 0), d)
                .map(|dt| TsSeconds(dt))
        }
    }

    impl Decodable for DateTime<Local> {
        fn decode<D: Decoder>(d: &mut D) -> Result<DateTime<Local>, D::Error> {
            match d.read_str()?.parse::<DateTime<FixedOffset>>() {
                Ok(dt) => Ok(dt.with_timezone(&Local)),
                Err(_) => Err(d.error("invalid date and time")),
            }
        }
    }

    impl Decodable for TsSeconds<Local> {
        fn decode<D: Decoder>(d: &mut D) -> Result<TsSeconds<Local>, D::Error> {
            from(Utc.timestamp_opt(d.read_i64()?, 0), d)
                .map(|dt| TsSeconds(dt.with_timezone(&Local)))
        }
    }

    #[cfg(test)] use rustc_serialize::json;

    #[test]
    fn test_encodable() {
        super::test_encodable_json(json::encode, json::encode);
    }

    #[test]
    fn test_decodable() {
        super::test_decodable_json(json::decode, json::decode, json::decode);
    }

    #[test]
    fn test_decodable_timestamps() {
        super::test_decodable_json_timestamps(json::decode, json::decode, json::decode);
    }

}

/// Ser/de helpers
///
/// The various modules in here are intended to be used with serde's [`with`
/// annotation](https://serde.rs/attributes.html#field-attributes).
#[cfg(feature = "serde")]
pub mod serde {
    use std::fmt;
    use super::DateTime;
    use offset::{TimeZone, LocalResult, Utc, Local, FixedOffset};
    use serdelib::{ser, de};

    /// Ser/de to/from timestamps in seconds
    ///
    /// Intended for use with `serde`'s `with` attribute.
    ///
    /// # Example:
    ///
    /// ```rust
    /// # // We mark this ignored so that we can test on 1.13 (which does not
    /// # // support custom derive), and run tests with --ignored on beta and
    /// # // nightly to actually trigger these.
    /// #
    /// # #[macro_use] extern crate serde_derive;
    /// # #[macro_use] extern crate serde_json;
    /// # extern crate chrono;
    /// # use chrono::{TimeZone, DateTime, Utc};
    /// use chrono::serde::ts_seconds;
    /// #[derive(Deserialize, Serialize)]
    /// struct S {
    ///     #[serde(with = "ts_seconds")]
    ///     time: DateTime<Utc>
    /// }
    ///
    /// # fn example() -> Result<S, serde_json::Error> {
    /// let time = Utc.ymd(2015, 5, 15).and_hms(10, 0, 0);
    /// let my_s = S {
    ///     time: time.clone(),
    /// };
    ///
    /// let as_string = serde_json::to_string(&my_s)?;
    /// assert_eq!(as_string, r#"{"time":1431684000}"#);
    /// let my_s: S = serde_json::from_str(&as_string)?;
    /// assert_eq!(my_s.time, time);
    /// # Ok(my_s)
    /// # }
    /// # fn main() { example().unwrap(); }
    /// ```
    pub mod ts_seconds {
        use std::fmt;
        use serdelib::{ser, de};

        use {DateTime, Utc, FixedOffset};
        use offset::TimeZone;
        use super::from;

        /// Deserialize a DateTime from a seconds timestamp
        ///
        /// Intended for use with `serde`s `deserialize_with` attribute.
        ///
        /// # Example:
        ///
        /// ```rust
        /// # // We mark this ignored so that we can test on 1.13 (which does not
        /// # // support custom derive), and run tests with --ignored on beta and
        /// # // nightly to actually trigger these.
        /// #
        /// # #[macro_use] extern crate serde_derive;
        /// # #[macro_use] extern crate serde_json;
        /// # extern crate chrono;
        /// # use chrono::{DateTime, Utc};
        /// use chrono::serde::ts_seconds::deserialize as from_ts;
        /// #[derive(Deserialize)]
        /// struct S {
        ///     #[serde(deserialize_with = "from_ts")]
        ///     time: DateTime<Utc>
        /// }
        ///
        /// # fn example() -> Result<S, serde_json::Error> {
        /// let my_s: S = serde_json::from_str(r#"{ "time": 1431684000 }"#)?;
        /// # Ok(my_s)
        /// # }
        /// # fn main() { example().unwrap(); }
        /// ```
        pub fn deserialize<'de, D>(d: D) -> Result<DateTime<Utc>, D::Error>
            where D: de::Deserializer<'de>
        {
            Ok(try!(d.deserialize_i64(SecondsTimestampVisitor).map(|dt| dt.with_timezone(&Utc))))
        }

        /// Serialize a UTC datetime into an integer number of seconds since the epoch
        ///
        /// Intended for use with `serde`s `serialize_with` attribute.
        ///
        /// # Example:
        ///
        /// ```rust
        /// # // We mark this ignored so that we can test on 1.13 (which does not
        /// # // support custom derive), and run tests with --ignored on beta and
        /// # // nightly to actually trigger these.
        /// #
        /// # #[macro_use] extern crate serde_derive;
        /// # #[macro_use] extern crate serde_json;
        /// # extern crate chrono;
        /// # use chrono::{TimeZone, DateTime, Utc};
        /// use chrono::serde::ts_seconds::serialize as to_ts;
        /// #[derive(Serialize)]
        /// struct S {
        ///     #[serde(serialize_with = "to_ts")]
        ///     time: DateTime<Utc>
        /// }
        ///
        /// # fn example() -> Result<String, serde_json::Error> {
        /// let my_s = S {
        ///     time: Utc.ymd(2015, 5, 15).and_hms(10, 0, 0),
        /// };
        /// let as_string = serde_json::to_string(&my_s)?;
        /// assert_eq!(as_string, r#"{"time":1431684000}"#);
        /// # Ok(as_string)
        /// # }
        /// # fn main() { example().unwrap(); }
        /// ```
        pub fn serialize<S>(dt: &DateTime<Utc>, serializer: S) -> Result<S::Ok, S::Error>
            where S: ser::Serializer
        {
            serializer.serialize_i64(dt.timestamp())
        }

        struct SecondsTimestampVisitor;

        impl<'de> de::Visitor<'de> for SecondsTimestampVisitor {
            type Value = DateTime<FixedOffset>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result
            {
                write!(formatter, "a unix timestamp in seconds")
            }

            /// Deserialize a timestamp in seconds since the epoch
            fn visit_i64<E>(self, value: i64) -> Result<DateTime<FixedOffset>, E>
                where E: de::Error
            {
                from(FixedOffset::east(0).timestamp_opt(value, 0), value)
            }

            /// Deserialize a timestamp in seconds since the epoch
            fn visit_u64<E>(self, value: u64) -> Result<DateTime<FixedOffset>, E>
                where E: de::Error
            {
                from(FixedOffset::east(0).timestamp_opt(value as i64, 0), value)
            }
        }

    }

    // TODO not very optimized for space (binary formats would want something better)

    impl<Tz: TimeZone> ser::Serialize for DateTime<Tz> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where S: ser::Serializer
        {
            struct FormatWrapped<'a, D: 'a> {
                inner: &'a D
            }

            impl<'a, D: fmt::Debug> fmt::Display for FormatWrapped<'a, D> {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    self.inner.fmt(f)
                }
            }

            // Debug formatting is correct RFC3339, and it allows Zulu.
            serializer.collect_str(&FormatWrapped { inner: &self })
        }
    }

    // try!-like function to convert a LocalResult into a serde-ish Result
    fn from<T, E, V>(me: LocalResult<T>, ts: V) -> Result<T, E>
        where E: de::Error,
              V: fmt::Display,
              T: fmt::Display,
    {
        match me {
            LocalResult::None => Err(E::custom(
                format!("value is not a legal timestamp: {}", ts))),
            LocalResult::Ambiguous(min, max) => Err(E::custom(
                format!("value is an ambiguous timestamp: {}, could be either of {}, {}",
                        ts, min, max))),
            LocalResult::Single(val) => Ok(val)
        }
    }

    struct DateTimeVisitor;

    impl<'de> de::Visitor<'de> for DateTimeVisitor {
        type Value = DateTime<FixedOffset>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result
        {
            write!(formatter, "a formatted date and time string or a unix timestamp")
        }

        fn visit_str<E>(self, value: &str) -> Result<DateTime<FixedOffset>, E>
            where E: de::Error
        {
            value.parse().map_err(|err| E::custom(format!("{}", err)))
        }
    }

    /// Deserialize a value that optionally includes a timezone offset in its
    /// string representation
    ///
    /// The serialized value can be either a string representation or a unix
    /// timestamp
    impl<'de> de::Deserialize<'de> for DateTime<FixedOffset> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where D: de::Deserializer<'de>
        {
            deserializer.deserialize_str(DateTimeVisitor)
        }
    }

    /// Deserialize into a UTC value
    ///
    /// The serialized value can be either a string representation or a unix
    /// timestamp
    impl<'de> de::Deserialize<'de> for DateTime<Utc> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where D: de::Deserializer<'de>
        {
            deserializer.deserialize_str(DateTimeVisitor).map(|dt| dt.with_timezone(&Utc))
        }
    }

    /// Deserialize a value that includes no timezone in its string
    /// representation
    ///
    /// The serialized value can be either a string representation or a unix
    /// timestamp
    impl<'de> de::Deserialize<'de> for DateTime<Local> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where D: de::Deserializer<'de>
        {
            deserializer.deserialize_str(DateTimeVisitor).map(|dt| dt.with_timezone(&Local))
        }
    }

    #[cfg(test)] extern crate serde_json;
    #[cfg(test)] extern crate bincode;

    #[test]
    fn test_serde_serialize() {
        super::test_encodable_json(self::serde_json::to_string, self::serde_json::to_string);
    }

    #[test]
    fn test_serde_deserialize() {
        super::test_decodable_json(|input| self::serde_json::from_str(&input), |input| self::serde_json::from_str(&input),
                                   |input| self::serde_json::from_str(&input));
    }

    #[test]
    fn test_serde_bincode() {
        // Bincode is relevant to test separately from JSON because
        // it is not self-describing.
        use self::bincode::{Infinite, serialize, deserialize};

        let dt = Utc.ymd(2014, 7, 24).and_hms(12, 34, 6);
        let encoded = serialize(&dt, Infinite).unwrap();
        let decoded: DateTime<Utc> = deserialize(&encoded).unwrap();
        assert_eq!(dt, decoded);
        assert_eq!(dt.offset(), decoded.offset());
    }
}

#[cfg(test)]
mod tests {
    use super::DateTime;
    use Datelike;
    use naive::{NaiveTime, NaiveDate};
    use offset::{TimeZone, Utc, Local, FixedOffset};
    use oldtime::Duration;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    #[allow(non_snake_case)]
    fn test_datetime_offset() {
        let Est = FixedOffset::west(5*60*60);
        let Edt = FixedOffset::west(4*60*60);
        let Kst = FixedOffset::east(9*60*60);

        assert_eq!(format!("{}", Utc.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06 07:08:09 UTC");
        assert_eq!(format!("{}", Edt.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06 07:08:09 -04:00");
        assert_eq!(format!("{}", Kst.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06 07:08:09 +09:00");
        assert_eq!(format!("{:?}", Utc.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06T07:08:09Z");
        assert_eq!(format!("{:?}", Edt.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06T07:08:09-04:00");
        assert_eq!(format!("{:?}", Kst.ymd(2014, 5, 6).and_hms(7, 8, 9)),
                   "2014-05-06T07:08:09+09:00");

        // edge cases
        assert_eq!(format!("{:?}", Utc.ymd(2014, 5, 6).and_hms(0, 0, 0)),
                   "2014-05-06T00:00:00Z");
        assert_eq!(format!("{:?}", Edt.ymd(2014, 5, 6).and_hms(0, 0, 0)),
                   "2014-05-06T00:00:00-04:00");
        assert_eq!(format!("{:?}", Kst.ymd(2014, 5, 6).and_hms(0, 0, 0)),
                   "2014-05-06T00:00:00+09:00");
        assert_eq!(format!("{:?}", Utc.ymd(2014, 5, 6).and_hms(23, 59, 59)),
                   "2014-05-06T23:59:59Z");
        assert_eq!(format!("{:?}", Edt.ymd(2014, 5, 6).and_hms(23, 59, 59)),
                   "2014-05-06T23:59:59-04:00");
        assert_eq!(format!("{:?}", Kst.ymd(2014, 5, 6).and_hms(23, 59, 59)),
                   "2014-05-06T23:59:59+09:00");

        let dt = Utc.ymd(2014, 5, 6).and_hms(7, 8, 9);
        assert_eq!(dt, Edt.ymd(2014, 5, 6).and_hms(3, 8, 9));
        assert_eq!(dt + Duration::seconds(3600 + 60 + 1), Utc.ymd(2014, 5, 6).and_hms(8, 9, 10));
        assert_eq!(dt.signed_duration_since(Edt.ymd(2014, 5, 6).and_hms(10, 11, 12)),
                   Duration::seconds(-7*3600 - 3*60 - 3));

        assert_eq!(*Utc.ymd(2014, 5, 6).and_hms(7, 8, 9).offset(), Utc);
        assert_eq!(*Edt.ymd(2014, 5, 6).and_hms(7, 8, 9).offset(), Edt);
        assert!(*Edt.ymd(2014, 5, 6).and_hms(7, 8, 9).offset() != Est);
    }

    #[test]
    fn test_datetime_date_and_time() {
        let tz = FixedOffset::east(5*60*60);
        let d = tz.ymd(2014, 5, 6).and_hms(7, 8, 9);
        assert_eq!(d.time(), NaiveTime::from_hms(7, 8, 9));
        assert_eq!(d.date(), tz.ymd(2014, 5, 6));
        assert_eq!(d.date().naive_local(), NaiveDate::from_ymd(2014, 5, 6));
        assert_eq!(d.date().and_time(d.time()), Some(d));

        let tz = FixedOffset::east(4*60*60);
        let d = tz.ymd(2016, 5, 4).and_hms(3, 2, 1);
        assert_eq!(d.time(), NaiveTime::from_hms(3, 2, 1));
        assert_eq!(d.date(), tz.ymd(2016, 5, 4));
        assert_eq!(d.date().naive_local(), NaiveDate::from_ymd(2016, 5, 4));
        assert_eq!(d.date().and_time(d.time()), Some(d));

        let tz = FixedOffset::west(13*60*60);
        let d = tz.ymd(2017, 8, 9).and_hms(12, 34, 56);
        assert_eq!(d.time(), NaiveTime::from_hms(12, 34, 56));
        assert_eq!(d.date(), tz.ymd(2017, 8, 9));
        assert_eq!(d.date().naive_local(), NaiveDate::from_ymd(2017, 8, 9));
        assert_eq!(d.date().and_time(d.time()), Some(d));
    }

    #[test]
    fn test_datetime_with_timezone() {
        let local_now = Local::now();
        let utc_now = local_now.with_timezone(&Utc);
        let local_now2 = utc_now.with_timezone(&Local);
        assert_eq!(local_now, local_now2);
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_datetime_rfc2822_and_rfc3339() {
        let EDT = FixedOffset::east(5*60*60);
        assert_eq!(Utc.ymd(2015, 2, 18).and_hms(23, 16, 9).to_rfc2822(),
                   "Wed, 18 Feb 2015 23:16:09 +0000");
        assert_eq!(Utc.ymd(2015, 2, 18).and_hms(23, 16, 9).to_rfc3339(),
                   "2015-02-18T23:16:09+00:00");
        assert_eq!(EDT.ymd(2015, 2, 18).and_hms_milli(23, 16, 9, 150).to_rfc2822(),
                   "Wed, 18 Feb 2015 23:16:09 +0500");
        assert_eq!(EDT.ymd(2015, 2, 18).and_hms_milli(23, 16, 9, 150).to_rfc3339(),
                   "2015-02-18T23:16:09.150+05:00");
        assert_eq!(EDT.ymd(2015, 2, 18).and_hms_micro(23, 59, 59, 1_234_567).to_rfc2822(),
                   "Wed, 18 Feb 2015 23:59:60 +0500");
        assert_eq!(EDT.ymd(2015, 2, 18).and_hms_micro(23, 59, 59, 1_234_567).to_rfc3339(),
                   "2015-02-18T23:59:60.234567+05:00");

        assert_eq!(DateTime::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 +0000"),
                   Ok(FixedOffset::east(0).ymd(2015, 2, 18).and_hms(23, 16, 9)));
        assert_eq!(DateTime::parse_from_rfc3339("2015-02-18T23:16:09Z"),
                   Ok(FixedOffset::east(0).ymd(2015, 2, 18).and_hms(23, 16, 9)));
        assert_eq!(DateTime::parse_from_rfc2822("Wed, 18 Feb 2015 23:59:60 +0500"),
                   Ok(EDT.ymd(2015, 2, 18).and_hms_milli(23, 59, 59, 1_000)));
        assert_eq!(DateTime::parse_from_rfc3339("2015-02-18T23:59:60.234567+05:00"),
                   Ok(EDT.ymd(2015, 2, 18).and_hms_micro(23, 59, 59, 1_234_567)));
    }

    #[test]
    fn test_datetime_from_str() {
        assert_eq!("2015-2-18T23:16:9.15Z".parse::<DateTime<FixedOffset>>(),
                   Ok(FixedOffset::east(0).ymd(2015, 2, 18).and_hms_milli(23, 16, 9, 150)));
        assert_eq!("2015-2-18T13:16:9.15-10:00".parse::<DateTime<FixedOffset>>(),
                   Ok(FixedOffset::west(10 * 3600).ymd(2015, 2, 18).and_hms_milli(13, 16, 9, 150)));
        assert!("2015-2-18T23:16:9.15".parse::<DateTime<FixedOffset>>().is_err());

        assert_eq!("2015-2-18T23:16:9.15Z".parse::<DateTime<Utc>>(),
                   Ok(Utc.ymd(2015, 2, 18).and_hms_milli(23, 16, 9, 150)));
        assert_eq!("2015-2-18T13:16:9.15-10:00".parse::<DateTime<Utc>>(),
                   Ok(Utc.ymd(2015, 2, 18).and_hms_milli(23, 16, 9, 150)));
        assert!("2015-2-18T23:16:9.15".parse::<DateTime<Utc>>().is_err());

        // no test for `DateTime<Local>`, we cannot verify that much.
    }

    #[test]
    fn test_datetime_parse_from_str() {
        let ymdhms = |y,m,d,h,n,s,off| FixedOffset::east(off).ymd(y,m,d).and_hms(h,n,s);
        assert_eq!(DateTime::parse_from_str("2014-5-7T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
                   Ok(ymdhms(2014, 5, 7, 12, 34, 56, 570*60))); // ignore offset
        assert!(DateTime::parse_from_str("20140507000000", "%Y%m%d%H%M%S").is_err()); // no offset
        assert!(DateTime::parse_from_str("Fri, 09 Aug 2013 23:54:35 GMT",
                                         "%a, %d %b %Y %H:%M:%S GMT").is_err());
        assert_eq!(Utc.datetime_from_str("Fri, 09 Aug 2013 23:54:35 GMT",
                                         "%a, %d %b %Y %H:%M:%S GMT"),
                   Ok(Utc.ymd(2013, 8, 9).and_hms(23, 54, 35)));
    }

    #[test]
    fn test_datetime_format_with_local() {
        // if we are not around the year boundary, local and UTC date should have the same year
        let dt = Local::now().with_month(5).unwrap();
        assert_eq!(dt.format("%Y").to_string(), dt.with_timezone(&Utc).format("%Y").to_string());
    }

    #[test]
    fn test_datetime_is_copy() {
        // UTC is known to be `Copy`.
        let a = Utc::now();
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn test_datetime_is_send() {
        use std::thread;

        // UTC is known to be `Send`.
        let a = Utc::now();
        thread::spawn(move || {
            let _ = a;
        }).join().unwrap();
    }

    #[test]
    fn test_subsecond_part() {
        let datetime = Utc.ymd(2014, 7, 8).and_hms_nano(9, 10, 11, 1234567);

        assert_eq!(1,       datetime.timestamp_subsec_millis());
        assert_eq!(1234,    datetime.timestamp_subsec_micros());
        assert_eq!(1234567, datetime.timestamp_subsec_nanos());
    }

    #[test]
    fn test_from_system_time() {
        use std::time::Duration;

        let epoch = Utc.ymd(1970, 1, 1).and_hms(0, 0, 0);

        // SystemTime -> DateTime<Utc>
        assert_eq!(DateTime::<Utc>::from(UNIX_EPOCH), epoch);
        assert_eq!(DateTime::<Utc>::from(UNIX_EPOCH + Duration::new(999_999_999, 999_999_999)),
                   Utc.ymd(2001, 9, 9).and_hms_nano(1, 46, 39, 999_999_999));
        assert_eq!(DateTime::<Utc>::from(UNIX_EPOCH - Duration::new(999_999_999, 999_999_999)),
                   Utc.ymd(1938, 4, 24).and_hms_nano(22, 13, 20, 1));

        // DateTime<Utc> -> SystemTime
        assert_eq!(SystemTime::from(epoch), UNIX_EPOCH);
        assert_eq!(SystemTime::from(Utc.ymd(2001, 9, 9).and_hms_nano(1, 46, 39, 999_999_999)),
                   UNIX_EPOCH + Duration::new(999_999_999, 999_999_999));
        assert_eq!(SystemTime::from(Utc.ymd(1938, 4, 24).and_hms_nano(22, 13, 20, 1)),
                   UNIX_EPOCH - Duration::new(999_999_999, 999_999_999));

        // DateTime<any tz> -> SystemTime (via `with_timezone`)
        assert_eq!(SystemTime::from(epoch.with_timezone(&Local)), UNIX_EPOCH);
        assert_eq!(SystemTime::from(epoch.with_timezone(&FixedOffset::east(32400))), UNIX_EPOCH);
        assert_eq!(SystemTime::from(epoch.with_timezone(&FixedOffset::west(28800))), UNIX_EPOCH);
    }
}
