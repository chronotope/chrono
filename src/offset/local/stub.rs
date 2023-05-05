// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::{FixedOffset, LocalResult, NaiveDateTime};

pub(super) fn offset_from_utc_datetime(_utc_time: &NaiveDateTime) -> LocalResult<FixedOffset> {
    LocalResult::Single(FixedOffset::east_opt(0).unwrap())
}

pub(super) fn offset_from_local_datetime(_local_time: &NaiveDateTime) -> LocalResult<FixedOffset> {
    LocalResult::Single(FixedOffset::east_opt(0).unwrap())
}
