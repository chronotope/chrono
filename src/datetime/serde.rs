use core::fmt;
use serde::{de, ser};

use super::DateTime;
use crate::format::{write_rfc3339, SecondsFormat};
#[cfg(feature = "clock")]
use crate::offset::Local;
use crate::offset::{FixedOffset, Offset, TimeZone, Utc};
use crate::serde::invalid_ts;
use crate::{infallible, serde_module};

#[doc(hidden)]
#[derive(Debug)]
pub struct SecondsTimestampVisitor;

#[doc(hidden)]
#[derive(Debug)]
pub struct NanoSecondsTimestampVisitor;

#[doc(hidden)]
#[derive(Debug)]
pub struct MicroSecondsTimestampVisitor;

#[doc(hidden)]
#[derive(Debug)]
pub struct MilliSecondsTimestampVisitor;

/// Serialize into an ISO 8601 formatted string.
///
/// See [the `serde` module](./serde/index.html) for alternate
/// serializations.
impl<Tz: TimeZone> ser::Serialize for DateTime<Tz> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        struct FormatIso8601<'a, Tz: TimeZone> {
            inner: &'a DateTime<Tz>,
        }

        impl<'a, Tz: TimeZone> fmt::Display for FormatIso8601<'a, Tz> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let naive = self.inner.naive_local();
                let offset = self.inner.offset.fix();
                write_rfc3339(f, naive, offset, SecondsFormat::AutoSi, true)
            }
        }

        serializer.collect_str(&FormatIso8601 { inner: self })
    }
}

struct DateTimeVisitor;

impl<'de> de::Visitor<'de> for DateTimeVisitor {
    type Value = DateTime<FixedOffset>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a formatted date and time string or a unix timestamp")
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        value.parse().map_err(E::custom)
    }
}

/// Deserialize a value that optionally includes a timezone offset in its
/// string representation
///
/// The value to be deserialized must be an rfc3339 string.
///
/// See [the `serde` module](./serde/index.html) for alternate
/// deserialization formats.
impl<'de> de::Deserialize<'de> for DateTime<FixedOffset> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserializer.deserialize_str(DateTimeVisitor)
    }
}

/// Deserialize into a UTC value
///
/// The value to be deserialized must be an rfc3339 string.
///
/// See [the `serde` module](./serde/index.html) for alternate
/// deserialization formats.
impl<'de> de::Deserialize<'de> for DateTime<Utc> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserializer.deserialize_str(DateTimeVisitor).map(|dt| dt.with_timezone(&Utc))
    }
}

/// Deserialize a value that includes no timezone in its string
/// representation
///
/// The value to be deserialized must be an rfc3339 string.
///
/// See [the `serde` module](./serde/index.html) for alternate
/// serialization formats.
#[cfg(feature = "clock")]
impl<'de> de::Deserialize<'de> for DateTime<Local> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserializer.deserialize_str(DateTimeVisitor).map(|dt| dt.with_timezone(&Local))
    }
}

serde_module! {
    type: DateTime<Utc>,
    module: ts_nanoseconds,
    module_opt: ts_nanoseconds_option,
    doc: r##"
# Errors

An `i64` with nanosecond precision can span a range of ~584 years. Serializing a `DateTime` beyond
that range returns an error.

The dates that can be represented as nanoseconds are between 1677-09-21T00:12:44.0 and
2262-04-11T23:47:16.854775804.

# Example

```rust
# use chrono::{DateTime, Utc, NaiveDate};
# use serde_derive::{Deserialize, Serialize};
use chrono::serde::ts_nanoseconds;
#[derive(Deserialize, Serialize)]
struct S {
    #[serde(with = "ts_nanoseconds")]
    time: DateTime<Utc>
}

let time = NaiveDate::from_ymd_opt(2018, 5, 17)
    .unwrap()
    .and_hms_nano_opt(02, 04, 59, 918355733)
    .unwrap()
    .and_utc();
let my_s = S {
    time: time.clone(),
};

let as_string = serde_json::to_string(&my_s)?;
assert_eq!(as_string, r#"{"time":1526522699918355733}"#);
let my_s: S = serde_json::from_str(&as_string)?;
assert_eq!(my_s.time, time);
# Ok::<(), serde_json::Error>(())
```"##,
    serialize_i64: |dt| DateTime::timestamp_nanos_opt(dt)
        .ok_or("value out of range for a timestamp with nanosecond precision"),
    deserialize_i64: NanoSecondsTimestampVisitor,
    expecting: "a unix timestamp in nanoseconds",
    visit_i64(i64): |value: i64| DateTime::from_timestamp(
        value.div_euclid(1_000_000_000),
        (value.rem_euclid(1_000_000_000)) as u32,
    )
    .ok_or_else(|| invalid_ts(value)),
    visit_u64(u64): |value: u64| DateTime::from_timestamp((value / 1_000_000_000) as i64, (value % 1_000_000_000) as u32)
    .ok_or_else(|| invalid_ts(value)),
}

serde_module! {
    type: DateTime<Utc>,
    module: ts_microseconds,
    module_opt: ts_microseconds_option,
    doc: r##"
# Example

```rust
# use chrono::{DateTime, Utc, NaiveDate};
# use serde_derive::{Deserialize, Serialize};
use chrono::serde::ts_microseconds;
#[derive(Deserialize, Serialize)]
struct S {
    #[serde(with = "ts_microseconds")]
    time: DateTime<Utc>
}

let time = NaiveDate::from_ymd_opt(2018, 5, 17)
    .unwrap()
    .and_hms_micro_opt(02, 04, 59, 918355)
    .unwrap()
    .and_utc();
let my_s = S {
    time: time.clone(),
};

let as_string = serde_json::to_string(&my_s)?;
assert_eq!(as_string, r#"{"time":1526522699918355}"#);
let my_s: S = serde_json::from_str(&as_string)?;
assert_eq!(my_s.time, time);
# Ok::<(), serde_json::Error>(())
```"##,
    serialize_i64: infallible!(DateTime::timestamp_micros),
    deserialize_i64: MicroSecondsTimestampVisitor,
    expecting: "a unix timestamp in microseconds",
    visit_i64(i64): |value: i64| DateTime::from_timestamp(
        value.div_euclid(1_000_000),
        (value.rem_euclid(1_000_000) * 1000) as u32,
    )
    .ok_or_else(|| invalid_ts(value)),
    visit_u64(u64): |value: u64| DateTime::from_timestamp(
        (value / 1_000_000) as i64,
        ((value % 1_000_000) * 1_000) as u32,
    )
    .ok_or_else(|| invalid_ts(value)),
}

serde_module! {
    type: DateTime<Utc>,
    module: ts_milliseconds,
    module_opt: ts_milliseconds_option,
    doc: r##"
# Example

```rust
# use chrono::{DateTime, Utc, NaiveDate};
# use serde_derive::{Deserialize, Serialize};
use chrono::serde::ts_milliseconds;
#[derive(Deserialize, Serialize)]
struct S {
    #[serde(with = "ts_milliseconds")]
    time: DateTime<Utc>
}

let time = NaiveDate::from_ymd_opt(2018, 5, 17)
    .unwrap()
    .and_hms_milli_opt(02, 04, 59, 918)
    .unwrap()
    .and_utc();
let my_s = S {
    time: time.clone(),
};

let as_string = serde_json::to_string(&my_s)?;
assert_eq!(as_string, r#"{"time":1526522699918}"#);
let my_s: S = serde_json::from_str(&as_string)?;
assert_eq!(my_s.time, time);
# Ok::<(), serde_json::Error>(())
```"##,
    serialize_i64: infallible!(DateTime::timestamp_millis),
    deserialize_i64: MilliSecondsTimestampVisitor,
    expecting: "a unix timestamp in milliseconds",
    visit_i64(i64): |value: i64| DateTime::from_timestamp_millis(value).ok_or_else(|| invalid_ts(value)),
    visit_u64(u64): |value: u64| DateTime::from_timestamp((value / 1000) as i64, ((value % 1000) * 1_000_000) as u32)
    .ok_or_else(|| invalid_ts(value)),
}

serde_module! {
    type: DateTime<Utc>,
    module: ts_seconds,
    module_opt: ts_seconds_option,
    doc: r##"
# Example

```rust
# use chrono::{TimeZone, DateTime, Utc};
# use serde_derive::{Deserialize, Serialize};
use chrono::serde::ts_seconds;
#[derive(Deserialize, Serialize)]
struct S {
    #[serde(with = "ts_seconds")]
    time: DateTime<Utc>
}

let time = Utc.with_ymd_and_hms(2015, 5, 15, 10, 0, 0).unwrap();
let my_s = S {
    time: time.clone(),
};

let as_string = serde_json::to_string(&my_s)?;
assert_eq!(as_string, r#"{"time":1431684000}"#);
let my_s: S = serde_json::from_str(&as_string)?;
assert_eq!(my_s.time, time);
# Ok::<(), serde_json::Error>(())
```"##,
    serialize_i64: infallible!(DateTime::timestamp),
    deserialize_i64: SecondsTimestampVisitor,
    expecting: "a unix timestamp in seconds",
    visit_i64(i64): |value: i64| DateTime::from_timestamp(value, 0).ok_or_else(|| invalid_ts(value)),
    visit_u64(u64): |value: u64| if value > i64::MAX as u64 {
        Err(invalid_ts(value))
    } else {
        DateTime::from_timestamp(value as i64, 0).ok_or_else(|| invalid_ts(value))
    },
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "clock")]
    use crate::datetime::test_decodable_json;
    use crate::datetime::test_encodable_json;
    use crate::{DateTime, FixedOffset, TimeZone, Utc};
    use core::fmt;

    #[test]
    fn test_serde_serialize() {
        test_encodable_json(serde_json::to_string, serde_json::to_string);
    }

    #[cfg(feature = "clock")]
    #[test]
    fn test_serde_deserialize() {
        test_decodable_json(
            |input| serde_json::from_str(input),
            |input| serde_json::from_str(input),
            |input| serde_json::from_str(input),
        );
    }

    #[test]
    fn test_serde_bincode() {
        // Bincode is relevant to test separately from JSON because
        // it is not self-describing.
        use bincode::{deserialize, serialize};

        let dt = Utc.with_ymd_and_hms(2014, 7, 24, 12, 34, 6).unwrap();
        let encoded = serialize(&dt).unwrap();
        let decoded: DateTime<Utc> = deserialize(&encoded).unwrap();
        assert_eq!(dt, decoded);
        assert_eq!(dt.offset(), decoded.offset());
    }

    #[test]
    fn test_serde_no_offset_debug() {
        use crate::{LocalResult, NaiveDate, NaiveDateTime, Offset};
        use core::fmt::Debug;

        #[derive(Clone)]
        struct TestTimeZone;
        impl Debug for TestTimeZone {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "TEST")
            }
        }
        impl TimeZone for TestTimeZone {
            type Offset = TestTimeZone;
            fn from_offset(_state: &TestTimeZone) -> TestTimeZone {
                TestTimeZone
            }
            fn offset_from_local_date(&self, _local: &NaiveDate) -> LocalResult<TestTimeZone> {
                LocalResult::Single(TestTimeZone)
            }
            fn offset_from_local_datetime(
                &self,
                _local: &NaiveDateTime,
            ) -> LocalResult<TestTimeZone> {
                LocalResult::Single(TestTimeZone)
            }
            fn offset_from_utc_date(&self, _utc: &NaiveDate) -> TestTimeZone {
                TestTimeZone
            }
            fn offset_from_utc_datetime(&self, _utc: &NaiveDateTime) -> TestTimeZone {
                TestTimeZone
            }
        }
        impl Offset for TestTimeZone {
            fn fix(&self) -> FixedOffset {
                FixedOffset::east_opt(15 * 60 * 60).unwrap()
            }
        }

        let tz = TestTimeZone;
        assert_eq!(format!("{:?}", &tz), "TEST");

        let dt = tz.with_ymd_and_hms(2023, 4, 24, 21, 10, 33).unwrap();
        let encoded = serde_json::to_string(&dt).unwrap();
        dbg!(&encoded);
        let decoded: DateTime<FixedOffset> = serde_json::from_str(&encoded).unwrap();
        assert_eq!(dt, decoded);
        assert_eq!(dt.offset().fix(), *decoded.offset());
    }
}
