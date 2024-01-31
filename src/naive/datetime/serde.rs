use core::fmt;
use serde::{de, ser};

use super::NaiveDateTime;
use crate::serde::invalid_ts;
use crate::DateTime;
use crate::{infallible, serde_module};

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

struct NanoSecondsTimestampVisitor;

serde_module! {
    type: NaiveDateTime,
    module: ts_nanoseconds,
    module_opt: ts_nanoseconds_option,
    doc: r##"
# Errors

An `i64` with nanosecond precision can span a range of ~584 years. Serializing a `NaiveDateTime`
beyond that range returns an error.

The dates that can be represented as nanoseconds are between 1677-09-21T00:12:44.0 and
2262-04-11T23:47:16.854775804.

# Example

```rust
# use chrono::{NaiveDate, NaiveDateTime};
# use serde_derive::{Deserialize, Serialize};
use chrono::naive::serde::ts_nanoseconds;
#[derive(Deserialize, Serialize)]
struct S {
    #[serde(with = "ts_nanoseconds")]
    time: NaiveDateTime
}

let time = NaiveDate::from_ymd_opt(2018, 5, 17).unwrap().and_hms_nano_opt(02, 04, 59, 918355733).unwrap();
let my_s = S {
    time: time.clone(),
};

let as_string = serde_json::to_string(&my_s)?;
assert_eq!(as_string, r#"{"time":1526522699918355733}"#);
let my_s: S = serde_json::from_str(&as_string)?;
assert_eq!(my_s.time, time);
# Ok::<(), serde_json::Error>(())
```"##,
    serialize_i64: |dt| NaiveDateTime::and_utc(dt).timestamp_nanos_opt()
        .ok_or("value out of range for a timestamp with nanosecond precision"),
    deserialize_i64: NanoSecondsTimestampVisitor,
    expecting: "a unix timestamp in nanoseconds",
    visit_i64(i64): |value: i64| DateTime::from_timestamp(
        value.div_euclid(1_000_000_000),
        (value.rem_euclid(1_000_000_000)) as u32,
    )
    .map(|dt| dt.naive_utc())
    .ok_or_else(|| invalid_ts(value)),
    visit_u64(u64): |value: u64| DateTime::from_timestamp((value / 1_000_000_000) as i64, (value % 1_000_000_000) as u32)
    .map(|dt| dt.naive_utc())
    .ok_or_else(|| invalid_ts(value)),
}

struct MicroSecondsTimestampVisitor;

serde_module! {
    type: NaiveDateTime,
    module: ts_microseconds,
    module_opt: ts_microseconds_option,
    doc: r##"
# Example

```rust
# use chrono::{NaiveDate, NaiveDateTime};
# use serde_derive::{Deserialize, Serialize};
use chrono::naive::serde::ts_microseconds;
#[derive(Deserialize, Serialize)]
struct S {
    #[serde(with = "ts_microseconds")]
    time: NaiveDateTime
}

let time = NaiveDate::from_ymd_opt(2018, 5, 17).unwrap().and_hms_micro_opt(02, 04, 59, 918355).unwrap();
let my_s = S {
    time: time.clone(),
};

let as_string = serde_json::to_string(&my_s)?;
assert_eq!(as_string, r#"{"time":1526522699918355}"#);
let my_s: S = serde_json::from_str(&as_string)?;
assert_eq!(my_s.time, time);
# Ok::<(), serde_json::Error>(())
```"##,
    serialize_i64: infallible!(|dt| NaiveDateTime::and_utc(dt).timestamp_micros()),
    deserialize_i64: MicroSecondsTimestampVisitor,
    expecting: "a unix timestamp in microseconds",
    visit_i64(i64): |value: i64| DateTime::from_timestamp_micros(value)
    .map(|dt| dt.naive_utc())
    .ok_or_else(|| invalid_ts(value)),
    visit_u64(u64): |value: u64| DateTime::from_timestamp(
        (value / 1_000_000) as i64,
        ((value % 1_000_000) * 1_000) as u32,
    )
    .map(|dt| dt.naive_utc())
    .ok_or_else(|| invalid_ts(value)),
}

struct MilliSecondsTimestampVisitor;

serde_module! {
    type: NaiveDateTime,
    module: ts_milliseconds,
    module_opt: ts_milliseconds_option,
    doc: r##"
# Example

```rust
# use chrono::{NaiveDate, NaiveDateTime};
# use serde_derive::{Deserialize, Serialize};
use chrono::naive::serde::ts_milliseconds;
#[derive(Deserialize, Serialize)]
struct S {
    #[serde(with = "ts_milliseconds")]
    time: NaiveDateTime
}

let time = NaiveDate::from_ymd_opt(2018, 5, 17).unwrap().and_hms_milli_opt(02, 04, 59, 918).unwrap();
let my_s = S {
    time: time.clone(),
};

let as_string = serde_json::to_string(&my_s)?;
assert_eq!(as_string, r#"{"time":1526522699918}"#);
let my_s: S = serde_json::from_str(&as_string)?;
assert_eq!(my_s.time, time);
# Ok::<(), serde_json::Error>(())
```"##,
    serialize_i64: infallible!(|dt| NaiveDateTime::and_utc(dt).timestamp_millis()),
    deserialize_i64: MilliSecondsTimestampVisitor,
    expecting: "a unix timestamp in milliseconds",
    visit_i64(i64): |value: i64| DateTime::from_timestamp_millis(value)
    .map(|dt| dt.naive_utc())
    .ok_or_else(|| invalid_ts(value)),
    visit_u64(u64): |value: u64| DateTime::from_timestamp((value / 1000) as i64, ((value % 1000) * 1_000_000) as u32)
    .map(|dt| dt.naive_utc())
    .ok_or_else(|| invalid_ts(value)),
}

struct SecondsTimestampVisitor;

serde_module! {
    type: NaiveDateTime,
    module: ts_seconds,
    module_opt: ts_seconds_option,
    doc: r##"
# Example

```rust
# use chrono::{NaiveDate, NaiveDateTime};
# use serde_derive::{Deserialize, Serialize};
use chrono::naive::serde::ts_seconds;
#[derive(Deserialize, Serialize)]
struct S {
    #[serde(with = "ts_seconds")]
    time: NaiveDateTime
}

let time = NaiveDate::from_ymd_opt(2015, 5, 15).unwrap().and_hms_opt(10, 0, 0).unwrap();
let my_s = S {
    time: time.clone(),
};

let as_string = serde_json::to_string(&my_s)?;
assert_eq!(as_string, r#"{"time":1431684000}"#);
let my_s: S = serde_json::from_str(&as_string)?;
assert_eq!(my_s.time, time);
# Ok::<(), serde_json::Error>(())
```"##,
    serialize_i64: infallible!(|dt| NaiveDateTime::and_utc(dt).timestamp()),
    deserialize_i64: SecondsTimestampVisitor,
    expecting: "a unix timestamp",
    visit_i64(i64): |value: i64| DateTime::from_timestamp(value, 0)
    .map(|dt| dt.naive_utc())
    .ok_or_else(|| invalid_ts(value)),
    visit_u64(u64): |value: u64| DateTime::from_timestamp(value as i64, 0)
    .map(|dt| dt.naive_utc())
    .ok_or_else(|| invalid_ts(value)),
}

#[cfg(test)]
mod tests {
    use crate::naive::datetime::{test_decodable_json, test_encodable_json};
    use crate::serde::ts_nanoseconds_option;
    use crate::{DateTime, NaiveDate, NaiveDateTime, TimeZone, Utc};

    use bincode::{deserialize, serialize};
    use serde_derive::{Deserialize, Serialize};

    #[test]
    fn test_serde_serialize() {
        test_encodable_json(serde_json::to_string);
    }

    #[test]
    fn test_serde_deserialize() {
        test_decodable_json(|input| serde_json::from_str(input));
    }

    // Bincode is relevant to test separately from JSON because
    // it is not self-describing.
    #[test]
    fn test_serde_bincode() {
        let dt =
            NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_milli_opt(9, 10, 48, 90).unwrap();
        let encoded = serialize(&dt).unwrap();
        let decoded: NaiveDateTime = deserialize(&encoded).unwrap();
        assert_eq!(dt, decoded);
    }

    #[test]
    fn test_serde_bincode_optional() {
        #[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
        struct Test {
            one: Option<i64>,
            #[serde(with = "ts_nanoseconds_option")]
            two: Option<DateTime<Utc>>,
        }

        let expected =
            Test { one: Some(1), two: Some(Utc.with_ymd_and_hms(1970, 1, 1, 0, 1, 1).unwrap()) };
        let bytes: Vec<u8> = serialize(&expected).unwrap();
        let actual = deserialize::<Test>(&(bytes)).unwrap();

        assert_eq!(expected, actual);
    }
}
