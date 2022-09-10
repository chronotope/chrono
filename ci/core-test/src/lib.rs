#![no_std]

use chrono::{TimeZone, Utc};

pub fn create_time() {
    let _ = Utc.ymd(2019, 1, 1).unwrap().and_hms(0, 0, 0).unwrap();
}
