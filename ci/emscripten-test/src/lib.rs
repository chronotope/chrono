use chrono::{DateTime, Local, Utc};
use std::ffi::{c_char, CString};

#[no_mangle]
extern "C" fn current_time_utc() -> *const c_char {
    let utc: DateTime<Utc> = Utc::now();
    let time = utc.to_rfc3339();

    CString::new(time).unwrap().into_raw()
}

#[no_mangle]
extern "C" fn current_time_local() -> *const c_char {
    let local: DateTime<Local> = Local::now();
    let time = local.to_rfc3339();

    CString::new(time).unwrap().into_raw()
}

#[no_mangle]
extern "C" fn timezone_offset() -> i32 {
    Local::now().offset().utc_minus_local()
}
