// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::{DateTime, FixedOffset, Local, NaiveDateTime};
use crate::offset::tz_info::TimeZone;
use crate::Utc;

pub(super) fn now() -> DateTime<Local> {
    let now = Utc::now();
    DateTime::from_utc(now.naive_utc(), offset(now.timestamp()))
}

pub(super) fn naive_to_local(d: &NaiveDateTime, local: bool) -> DateTime<Local> {
    let offset = match local {
        true => offset(d.timestamp()),
        false => FixedOffset::east(0),
    };

    DateTime::from_utc(*d - offset, offset)
}

fn offset(unix: i64) -> FixedOffset {
    FixedOffset::east(
        TimeZone::local()
            .expect("unable to parse localtime info")
            .find_local_time_type(unix)
            .expect("unable to select local time type")
            .offset(),
    )
}
