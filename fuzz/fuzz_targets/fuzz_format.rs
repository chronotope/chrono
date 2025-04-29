#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: (String, String)| {
    use chrono::prelude::*;
    let _ = DateTime::parse_from_str(&data.0, &data.1);
});
