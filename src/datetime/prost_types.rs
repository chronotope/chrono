use std::time::SystemTime;

use prost_types::{Timestamp, TimestampError};

use crate::{DateTime, TimeZone, Utc};

/// Tries to converts a `prost_types::Timestamp` to a `chrono::DateTime`.
impl TryFrom<Timestamp> for DateTime<Utc> {
    type Error = TimestampError;

    fn try_from(value: Timestamp) -> Result<Self, Self::Error> {
        let system_time = SystemTime::try_from(value)?;
        Ok(DateTime::from(system_time))
    }
}

/// Converts a `chrono::DateTime` to a `prost_types::Timestamp`.
impl<Tz: TimeZone> From<DateTime<Tz>> for Timestamp {
    fn from(value: DateTime<Tz>) -> Timestamp {
        Timestamp { seconds: value.timestamp(), nanos: value.timestamp_subsec_nanos() as _ }
    }
}

#[test]
fn conversion() {
    let now = Utc::now();
    let timestamp = Timestamp::from(now.clone());
    let now_converted = DateTime::try_from(timestamp).expect("prost_types --> chrono");

    assert_eq!(now, now_converted);
}
