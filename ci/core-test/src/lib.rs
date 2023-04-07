#![no_std]

use chrono::{TimeZone, Utc};

pub fn create_time() -> Result<(), chrono::Error> {
    let _ = Utc.with_ymd_and_hms(2019, 1, 1, 0, 0, 0)?.single()?;
    Ok(())
}
