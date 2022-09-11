#![cfg(all(
    target_arch = "wasm32",
    feature = "wasmbind",
    not(any(target_os = "emscripten", target_os = "wasi"))
))]

use std::convert::TryFrom;

use chrono::prelude::*;
use wasm_bindgen_test::*;

#[wasm_bindgen_test]
fn now() {
    let utc: DateTime<Utc> = Utc::now().unwrap();
    let local: DateTime<Local> = Local::now().unwrap();

    // Ensure time set by the test script is correct
    let now = env!("NOW");
    let actual = Utc.datetime_from_str(&now, "%s").unwrap();
    let diff = utc - actual;
    assert!(
        diff < chrono::TimeDelta::minutes(5),
        "expected {} - {} == {} < 5m (env var: {})",
        utc,
        actual,
        diff,
        now,
    );

    let tz = env!("TZ");
    eprintln!("testing with tz={}", tz);

    // Ensure offset retrieved when getting local time is correct
    let expected_offset = match tz {
        "ACST-9:30" => FixedOffset::east(19 * 30 * 60).unwrap(),
        "Asia/Katmandu" => FixedOffset::east(23 * 15 * 60).unwrap(), // No DST thankfully
        "EDT" | "EST4" | "-0400" => FixedOffset::east(-4 * 60 * 60).unwrap(),
        "EST" | "-0500" => FixedOffset::east(-5 * 60 * 60).unwrap(),
        "UTC0" | "+0000" => FixedOffset::east(0).unwrap(),
        tz => panic!("unexpected TZ {}", tz),
    };
    assert_eq!(
        &expected_offset,
        local.offset(),
        "expected: {:?} local: {:?}",
        expected_offset,
        local.offset(),
    );
}

#[wasm_bindgen_test]
fn from_is_exact() {
    let now = js_sys::Date::new_0();

    let dt = DateTime::<Utc>::try_from(now.clone()).unwrap();

    assert_eq!(now.get_time() as i64, dt.timestamp_millis());
}

#[wasm_bindgen_test]
fn local_from_local_datetime() {
    let now = Local::now().unwrap();
    let ndt = now.naive_local();
    let res = Local.from_local_datetime(&ndt).unwrap().single().unwrap();
    assert_eq!(now, res);
}

#[wasm_bindgen_test]
fn convert_all_parts_with_milliseconds() {
    let time: DateTime<Utc> = "2020-12-01T03:01:55.974Z".parse().unwrap();
    let js_date = js_sys::Date::from(time);

    assert_eq!(js_date.get_utc_full_year(), 2020);
    assert_eq!(js_date.get_utc_month(), 12);
    assert_eq!(js_date.get_utc_date(), 1);
    assert_eq!(js_date.get_utc_hours(), 3);
    assert_eq!(js_date.get_utc_minutes(), 1);
    assert_eq!(js_date.get_utc_seconds(), 55);
    assert_eq!(js_date.get_utc_milliseconds(), 974);
}
