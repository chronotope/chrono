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
use crate::{Datelike, LocalResult, Utc};

pub(super) fn now() -> DateTime<Local> {
    let now = Utc::now().naive_utc();
    DateTime::from_utc(now, offset(now, false).unwrap())
}

pub(super) fn naive_to_local(d: &NaiveDateTime, local: bool) -> LocalResult<DateTime<Local>> {
    if local {
        match offset(*d, true) {
            LocalResult::None => LocalResult::None,
            LocalResult::Ambiguous(early, late) => LocalResult::Ambiguous(
                DateTime::from_utc(*d - early, early),
                DateTime::from_utc(*d - late, late),
            ),
            LocalResult::Single(offset) => {
                LocalResult::Single(DateTime::from_utc(*d - offset, offset))
            }
        }
    } else {
        LocalResult::Single(DateTime::from_utc(*d, offset(*d, false).unwrap()))
    }
}

fn offset(d: NaiveDateTime, local: bool) -> LocalResult<FixedOffset> {
    let info = unsafe {
        INIT.call_once(|| {
            INFO = Some(TimeZone::local().expect("unable to parse localtime info"));
        });
        INFO.as_ref().unwrap()
    };

    if local {
        // we pass through the year as the year of a local point in time must either be valid in that locale, or
        // the entire time was skipped in which case we will return LocalResult::None anywa.
        match info
            .find_local_time_type_from_local(d.timestamp(), d.year())
            .expect("unable to select local time type")
        {
            LocalResult::None => LocalResult::None,
            LocalResult::Ambiguous(early, late) => LocalResult::Ambiguous(
                FixedOffset::east(early.offset()),
                FixedOffset::east(late.offset()),
            ),
            LocalResult::Single(tt) => LocalResult::Single(FixedOffset::east(tt.offset())),
        }
    } else {
        LocalResult::Single(FixedOffset::east(
            info.find_local_time_type(d.timestamp())
                .expect("unable to select local time type")
                .offset(),
        ))
    }
}

static mut INFO: Option<TimeZone> = None;
static INIT: Once = Once::new();
