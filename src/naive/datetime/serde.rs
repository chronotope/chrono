use core::fmt;
use serde::{de, ser};

use super::NaiveDateTime;
use crate::offset::LocalResult;

/// Serialize a `NaiveDateTime` as an RFC 3339 string
///
/// See [the `serde` module](./serde/index.html) for alternate
/// serialization formats.
impl ser::Serialize for NaiveDateTime {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        struct FormatWrapped<'a, D: 'a> {
            inner: &'a D,
        }

        impl<'a, D: fmt::Debug> fmt::Display for FormatWrapped<'a, D> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.inner.fmt(f)
            }
        }

        serializer.collect_str(&FormatWrapped { inner: &self })
    }
}

struct NaiveDateTimeVisitor;

impl<'de> de::Visitor<'de> for NaiveDateTimeVisitor {
    type Value = NaiveDateTime;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a formatted date and time string")
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        value.parse().map_err(E::custom)
    }
}

impl<'de> de::Deserialize<'de> for NaiveDateTime {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserializer.deserialize_str(NaiveDateTimeVisitor)
    }
}

/// Used to serialize/deserialize from nanosecond-precision timestamps
///
/// # Example:
///
/// ```rust
/// # // We mark this ignored so that we can test on 1.13 (which does not
/// # // support custom derive), and run tests with --ignored on beta and
/// # // nightly to actually trigger these.
/// #
/// # #[macro_use] extern crate serde_derive;
/// # extern crate serde_json;
/// # extern crate serde;
/// # extern crate chrono;
/// # use chrono::{TimeZone, NaiveDate, NaiveDateTime, Utc};
/// use chrono::naive::serde::ts_nanoseconds;
/// #[derive(Deserialize, Serialize)]
/// struct S {
///     #[serde(with = "ts_nanoseconds")]
///     time: NaiveDateTime
/// }
///
/// # fn example() -> Result<S, serde_json::Error> {
/// let time = NaiveDate::from_ymd(2018, 5, 17).and_hms_nano(02, 04, 59, 918355733);
/// let my_s = S {
///     time: time.clone(),
/// };
///
/// let as_string = serde_json::to_string(&my_s)?;
/// assert_eq!(as_string, r#"{"time":1526522699918355733}"#);
/// let my_s: S = serde_json::from_str(&as_string)?;
/// assert_eq!(my_s.time, time);
/// # Ok(my_s)
/// # }
/// # fn main() { example().unwrap(); }
/// ```
pub mod ts_nanoseconds {
    use core::fmt;
    use serde::{de, ser};

    use super::ne_timestamp;
    use crate::NaiveDateTime;

    /// Serialize a UTC datetime into an integer number of nanoseconds since the epoch
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
    /// # #[macro_use] extern crate serde;
    /// # extern crate chrono;
    /// # use chrono::{TimeZone, NaiveDate, NaiveDateTime, Utc};
    /// # use serde::Serialize;
    /// use chrono::naive::serde::ts_nanoseconds::serialize as to_nano_ts;
    /// #[derive(Serialize)]
    /// struct S {
    ///     #[serde(serialize_with = "to_nano_ts")]
    ///     time: NaiveDateTime
    /// }
    ///
    /// # fn example() -> Result<String, serde_json::Error> {
    /// let my_s = S {
    ///     time: NaiveDate::from_ymd(2018, 5, 17).and_hms_nano(02, 04, 59, 918355733),
    /// };
    /// let as_string = serde_json::to_string(&my_s)?;
    /// assert_eq!(as_string, r#"{"time":1526522699918355733}"#);
    /// # Ok(as_string)
    /// # }
    /// # fn main() { example().unwrap(); }
    /// ```
    pub fn serialize<S>(dt: &NaiveDateTime, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        serializer.serialize_i64(dt.timestamp_nanos())
    }

    /// Deserialize a `DateTime` from a nanoseconds timestamp
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
    /// # extern crate serde;
    /// # extern crate chrono;
    /// # use chrono::{NaiveDateTime, Utc};
    /// # use serde::Deserialize;
    /// use chrono::naive::serde::ts_nanoseconds::deserialize as from_nano_ts;
    /// #[derive(Deserialize)]
    /// struct S {
    ///     #[serde(deserialize_with = "from_nano_ts")]
    ///     time: NaiveDateTime
    /// }
    ///
    /// # fn example() -> Result<S, serde_json::Error> {
    /// let my_s: S = serde_json::from_str(r#"{ "time": 1526522699918355733 }"#)?;
    /// # Ok(my_s)
    /// # }
    /// # fn main() { example().unwrap(); }
    /// ```
    pub fn deserialize<'de, D>(d: D) -> Result<NaiveDateTime, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        d.deserialize_i64(NaiveDateTimeFromNanoSecondsVisitor)
    }

    struct NaiveDateTimeFromNanoSecondsVisitor;

    impl<'de> de::Visitor<'de> for NaiveDateTimeFromNanoSecondsVisitor {
        type Value = NaiveDateTime;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a unix timestamp")
        }

        fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            NaiveDateTime::from_timestamp_opt(value / 1_000_000_000, (value % 1_000_000_000) as u32)
                .ok_or_else(|| E::custom(ne_timestamp(value)))
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            NaiveDateTime::from_timestamp_opt(
                value as i64 / 1_000_000_000,
                (value as i64 % 1_000_000_000) as u32,
            )
            .ok_or_else(|| E::custom(ne_timestamp(value)))
        }
    }
}

/// Used to serialize/deserialize from millisecond-precision timestamps
///
/// # Example:
///
/// ```rust
/// # // We mark this ignored so that we can test on 1.13 (which does not
/// # // support custom derive), and run tests with --ignored on beta and
/// # // nightly to actually trigger these.
/// #
/// # #[macro_use] extern crate serde_derive;
/// # extern crate serde_json;
/// # extern crate serde;
/// # extern crate chrono;
/// # use chrono::{TimeZone, NaiveDate, NaiveDateTime, Utc};
/// use chrono::naive::serde::ts_milliseconds;
/// #[derive(Deserialize, Serialize)]
/// struct S {
///     #[serde(with = "ts_milliseconds")]
///     time: NaiveDateTime
/// }
///
/// # fn example() -> Result<S, serde_json::Error> {
/// let time = NaiveDate::from_ymd(2018, 5, 17).and_hms_milli(02, 04, 59, 918);
/// let my_s = S {
///     time: time.clone(),
/// };
///
/// let as_string = serde_json::to_string(&my_s)?;
/// assert_eq!(as_string, r#"{"time":1526522699918}"#);
/// let my_s: S = serde_json::from_str(&as_string)?;
/// assert_eq!(my_s.time, time);
/// # Ok(my_s)
/// # }
/// # fn main() { example().unwrap(); }
/// ```
pub mod ts_milliseconds {
    use core::fmt;
    use serde::{de, ser};

    use super::ne_timestamp;
    use crate::NaiveDateTime;

    /// Serialize a UTC datetime into an integer number of milliseconds since the epoch
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
    /// # #[macro_use] extern crate serde;
    /// # extern crate chrono;
    /// # use chrono::{TimeZone, NaiveDate, NaiveDateTime, Utc};
    /// # use serde::Serialize;
    /// use chrono::naive::serde::ts_milliseconds::serialize as to_milli_ts;
    /// #[derive(Serialize)]
    /// struct S {
    ///     #[serde(serialize_with = "to_milli_ts")]
    ///     time: NaiveDateTime
    /// }
    ///
    /// # fn example() -> Result<String, serde_json::Error> {
    /// let my_s = S {
    ///     time: NaiveDate::from_ymd(2018, 5, 17).and_hms_milli(02, 04, 59, 918),
    /// };
    /// let as_string = serde_json::to_string(&my_s)?;
    /// assert_eq!(as_string, r#"{"time":1526522699918}"#);
    /// # Ok(as_string)
    /// # }
    /// # fn main() { example().unwrap(); }
    /// ```
    pub fn serialize<S>(dt: &NaiveDateTime, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        serializer.serialize_i64(dt.timestamp_millis())
    }

    /// Deserialize a `DateTime` from a milliseconds timestamp
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
    /// # extern crate serde;
    /// # extern crate chrono;
    /// # use chrono::{NaiveDateTime, Utc};
    /// # use serde::Deserialize;
    /// use chrono::naive::serde::ts_milliseconds::deserialize as from_milli_ts;
    /// #[derive(Deserialize)]
    /// struct S {
    ///     #[serde(deserialize_with = "from_milli_ts")]
    ///     time: NaiveDateTime
    /// }
    ///
    /// # fn example() -> Result<S, serde_json::Error> {
    /// let my_s: S = serde_json::from_str(r#"{ "time": 1526522699918 }"#)?;
    /// # Ok(my_s)
    /// # }
    /// # fn main() { example().unwrap(); }
    /// ```
    pub fn deserialize<'de, D>(d: D) -> Result<NaiveDateTime, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        d.deserialize_i64(NaiveDateTimeFromMilliSecondsVisitor)
    }

    struct NaiveDateTimeFromMilliSecondsVisitor;

    impl<'de> de::Visitor<'de> for NaiveDateTimeFromMilliSecondsVisitor {
        type Value = NaiveDateTime;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a unix timestamp")
        }

        fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            NaiveDateTime::from_timestamp_opt(value / 1000, ((value % 1000) * 1_000_000) as u32)
                .ok_or_else(|| E::custom(ne_timestamp(value)))
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            NaiveDateTime::from_timestamp_opt(
                (value / 1000) as i64,
                ((value % 1000) * 1_000_000) as u32,
            )
            .ok_or_else(|| E::custom(ne_timestamp(value)))
        }
    }
}

/// Used to serialize/deserialize from second-precision timestamps
///
/// # Example:
///
/// ```rust
/// # // We mark this ignored so that we can test on 1.13 (which does not
/// # // support custom derive), and run tests with --ignored on beta and
/// # // nightly to actually trigger these.
/// #
/// # #[macro_use] extern crate serde_derive;
/// # extern crate serde_json;
/// # extern crate serde;
/// # extern crate chrono;
/// # use chrono::{TimeZone, NaiveDate, NaiveDateTime, Utc};
/// use chrono::naive::serde::ts_seconds;
/// #[derive(Deserialize, Serialize)]
/// struct S {
///     #[serde(with = "ts_seconds")]
///     time: NaiveDateTime
/// }
///
/// # fn example() -> Result<S, serde_json::Error> {
/// let time = NaiveDate::from_ymd(2015, 5, 15).and_hms(10, 0, 0);
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
    use core::fmt;
    use serde::{de, ser};

    use super::ne_timestamp;
    use crate::NaiveDateTime;

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
    /// # #[macro_use] extern crate serde;
    /// # extern crate chrono;
    /// # use chrono::{TimeZone, NaiveDate, NaiveDateTime, Utc};
    /// # use serde::Serialize;
    /// use chrono::naive::serde::ts_seconds::serialize as to_ts;
    /// #[derive(Serialize)]
    /// struct S {
    ///     #[serde(serialize_with = "to_ts")]
    ///     time: NaiveDateTime
    /// }
    ///
    /// # fn example() -> Result<String, serde_json::Error> {
    /// let my_s = S {
    ///     time: NaiveDate::from_ymd(2015, 5, 15).and_hms(10, 0, 0),
    /// };
    /// let as_string = serde_json::to_string(&my_s)?;
    /// assert_eq!(as_string, r#"{"time":1431684000}"#);
    /// # Ok(as_string)
    /// # }
    /// # fn main() { example().unwrap(); }
    /// ```
    pub fn serialize<S>(dt: &NaiveDateTime, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        serializer.serialize_i64(dt.timestamp())
    }

    /// Deserialize a `DateTime` from a seconds timestamp
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
    /// # extern crate serde;
    /// # extern crate chrono;
    /// # use chrono::{NaiveDateTime, Utc};
    /// # use serde::Deserialize;
    /// use chrono::naive::serde::ts_seconds::deserialize as from_ts;
    /// #[derive(Deserialize)]
    /// struct S {
    ///     #[serde(deserialize_with = "from_ts")]
    ///     time: NaiveDateTime
    /// }
    ///
    /// # fn example() -> Result<S, serde_json::Error> {
    /// let my_s: S = serde_json::from_str(r#"{ "time": 1431684000 }"#)?;
    /// # Ok(my_s)
    /// # }
    /// # fn main() { example().unwrap(); }
    /// ```
    pub fn deserialize<'de, D>(d: D) -> Result<NaiveDateTime, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        d.deserialize_i64(NaiveDateTimeFromSecondsVisitor)
    }

    struct NaiveDateTimeFromSecondsVisitor;

    impl<'de> de::Visitor<'de> for NaiveDateTimeFromSecondsVisitor {
        type Value = NaiveDateTime;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a unix timestamp")
        }

        fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            NaiveDateTime::from_timestamp_opt(value, 0)
                .ok_or_else(|| E::custom(ne_timestamp(value)))
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            NaiveDateTime::from_timestamp_opt(value as i64, 0)
                .ok_or_else(|| E::custom(ne_timestamp(value)))
        }
    }
}

#[test]
fn test_serde_serialize() {
    super::test_encodable_json(serde_json::to_string);
}

#[test]
fn test_serde_deserialize() {
    super::test_decodable_json(|input| serde_json::from_str(input));
}

// Bincode is relevant to test separately from JSON because
// it is not self-describing.
#[test]
fn test_serde_bincode() {
    use crate::naive::NaiveDate;
    use bincode::{deserialize, serialize, Infinite};

    let dt = NaiveDate::from_ymd(2016, 7, 8).and_hms_milli(9, 10, 48, 90);
    let encoded = serialize(&dt, Infinite).unwrap();
    let decoded: NaiveDateTime = deserialize(&encoded).unwrap();
    assert_eq!(dt, decoded);
}

#[test]
fn test_serde_bincode_optional() {
    use crate::prelude::*;
    use crate::serde::ts_nanoseconds_option;
    use bincode::{deserialize, serialize, Infinite};
    use serde_derive::{Deserialize, Serialize};

    #[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
    struct Test {
        one: Option<i64>,
        #[serde(with = "ts_nanoseconds_option")]
        two: Option<DateTime<Utc>>,
    }

    let expected = Test { one: Some(1), two: Some(Utc.ymd(1970, 1, 1).and_hms(0, 1, 1)) };
    let bytes: Vec<u8> = serialize(&expected, Infinite).unwrap();
    let actual = deserialize::<Test>(&(bytes)).unwrap();

    assert_eq!(expected, actual);
}

// lik? function to convert a LocalResult into a serde-ish Result
pub(crate) fn serde_from<T, E, V>(me: LocalResult<T>, ts: &V) -> Result<T, E>
where
    E: de::Error,
    V: fmt::Display,
    T: fmt::Display,
{
    match me {
        LocalResult::None => Err(E::custom(ne_timestamp(ts))),
        LocalResult::Ambiguous(min, max) => {
            Err(E::custom(SerdeError::Ambiguous { timestamp: ts, min, max }))
        }
        LocalResult::Single(val) => Ok(val),
    }
}

#[cfg(feature = "serde")]
enum SerdeError<V: fmt::Display, D: fmt::Display> {
    NonExistent { timestamp: V },
    Ambiguous { timestamp: V, min: D, max: D },
}

/// Construct a [`SerdeError::NonExistent`]
#[cfg(feature = "serde")]
fn ne_timestamp<T: fmt::Display>(ts: T) -> SerdeError<T, u8> {
    SerdeError::NonExistent::<T, u8> { timestamp: ts }
}

#[cfg(feature = "serde")]
impl<V: fmt::Display, D: fmt::Display> fmt::Debug for SerdeError<V, D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ChronoSerdeError({})", self)
    }
}

// impl<V: fmt::Display, D: fmt::Debug> core::error::Error for SerdeError<V, D> {}
#[cfg(feature = "serde")]
impl<V: fmt::Display, D: fmt::Display> fmt::Display for SerdeError<V, D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SerdeError::NonExistent { timestamp } => {
                write!(f, "value is not a legal timestamp: {}", timestamp)
            }
            SerdeError::Ambiguous { timestamp, min, max } => write!(
                f,
                "value is an ambiguous timestamp: {}, could be either of {}, {}",
                timestamp, min, max
            ),
        }
    }
}
