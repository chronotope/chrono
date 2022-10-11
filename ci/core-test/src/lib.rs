#![no_std]

use chrono::{TimeZone, Utc};

pub fn create_time() {
    let _ = Utc.ymd_opt(2019, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();
}
