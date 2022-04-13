// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::sync::Once;

use super::tz_info::TimeZone;
use super::{DateTime, FixedOffset, Local, NaiveDateTime};
use crate::Utc;

pub(super) fn now() -> DateTime<Local> {
    let now = Utc::now().naive_utc();
    DateTime::from_utc(now, offset(now, false))
}

pub(super) fn naive_to_local(d: &NaiveDateTime, local: bool) -> DateTime<Local> {
    let subtract = match local {
        true => offset(*d, local),
        false => FixedOffset::east(0),
    };

    DateTime::from_utc(*d - subtract, offset(*d, local))
}

fn offset(d: NaiveDateTime, local: bool) -> FixedOffset {
    let info = unsafe {
        INIT.call_once(|| {
            INFO = Some(TimeZone::local().expect("unable to parse localtime info"));
        });
        INFO.as_ref().unwrap()
    };

    if local {
        FixedOffset::east(
            info.find_local_time_type_from_local(d.timestamp()).expect("unable to select local time type").offset(),
        )
    } else {
        FixedOffset::east(
            info.find_local_time_type(d.timestamp()).expect("unable to select local time type").offset(),
        )
    }
}

static mut INFO: Option<TimeZone> = None;
static INIT: Once = Once::new();
