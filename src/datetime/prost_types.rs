use std::time::SystemTime;

use prost_types::{Timestamp, TimestampError};

use crate::{DateTime, Utc};

impl TryFrom<Timestamp> for DateTime<Utc> {
    type Error = TimestampError;

    fn try_from(value: Timestamp) -> Result<Self, Self::Error> {
        let system_time = SystemTime::try_from(value)?;
        Ok(DateTime::from(system_time))
    }
}

impl From<DateTime<Utc>> for Timestamp {
    fn from(value: DateTime<Utc>) -> Timestamp {
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
