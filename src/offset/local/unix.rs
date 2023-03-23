// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
#![allow(dead_code)]

use std::{cell::RefCell, collections::hash_map, env, fs, hash::Hasher, time::SystemTime};

use super::tz_info::TimeZone;
use super::{DateTime, FixedOffset, Local, NaiveDateTime};
use crate::offset::LocalResult;
use crate::{Datelike, Error, Utc};

pub(super) fn now() -> Result<DateTime<Local>, Error> {
    let now = Utc::now()?.naive_utc();

    match naive_to_local(&now, false)? {
        LocalResult::Single(dt) => Ok(dt),
        _ => Err(Error::AmbiguousDate),
    }
}

pub(super) fn naive_to_local(
    d: &NaiveDateTime,
    local: bool,
) -> Result<LocalResult<DateTime<Local>>, Error> {
    TZ_INFO.with(|maybe_cache| {
        maybe_cache.borrow_mut().get_or_insert_with(Cache::default).offset(*d, local)
    })
}

// we have to store the `Cache` in an option as it can't
// be initalized in a static context.
thread_local! {
    static TZ_INFO: RefCell<Option<Cache>> = Default::default();
}

enum Source {
    LocalTime { mtime: SystemTime },
    Environment { hash: u64 },
}

impl Source {
    fn new(env_tz: Option<&str>) -> Source {
        match env_tz {
            Some(tz) => {
                let mut hasher = hash_map::DefaultHasher::new();
                hasher.write(tz.as_bytes());
                let hash = hasher.finish();
                Source::Environment { hash }
            }
            None => match fs::symlink_metadata("/etc/localtime") {
                Ok(data) => Source::LocalTime {
                    // we have to pick a sensible default when the mtime fails
                    // by picking SystemTime::now() we raise the probability of
                    // the cache being invalidated if/when the mtime starts working
                    mtime: data.modified().unwrap_or_else(|_| SystemTime::now()),
                },
                Err(_) => {
                    // as above, now() should be a better default than some constant
                    // TODO: see if we can improve caching in the case where the fallback is a valid timezone
                    Source::LocalTime { mtime: SystemTime::now() }
                }
            },
        }
    }
}

struct Cache {
    zone: TimeZone,
    source: Source,
    last_checked: SystemTime,
}

#[cfg(target_os = "android")]
const TZDB_LOCATION: &str = " /system/usr/share/zoneinfo";

#[cfg(target_os = "aix")]
const TZDB_LOCATION: &str = "/usr/share/lib/zoneinfo";

#[allow(dead_code)] // keeps the cfg simpler
#[cfg(not(any(target_os = "android", target_os = "aix")))]
const TZDB_LOCATION: &str = "/usr/share/zoneinfo";

fn fallback_timezone() -> Option<TimeZone> {
    let tz_name = iana_time_zone::get_timezone().ok()?;
    let bytes = fs::read(format!("{}/{}", TZDB_LOCATION, tz_name)).ok()?;
    TimeZone::from_tz_data(&bytes).ok()
}

impl Default for Cache {
    fn default() -> Cache {
        // default to UTC if no local timezone can be found
        let env_tz = env::var("TZ").ok();
        let env_ref = env_tz.as_deref();
        Cache {
            last_checked: SystemTime::now(),
            source: Source::new(env_ref),
            zone: current_zone(env_ref),
        }
    }
}

fn current_zone(var: Option<&str>) -> TimeZone {
    TimeZone::local(var).ok().or_else(fallback_timezone).unwrap_or_else(TimeZone::utc)
}

impl Cache {
    fn offset(
        &mut self,
        d: NaiveDateTime,
        local: bool,
    ) -> Result<LocalResult<DateTime<Local>>, Error> {
        // TODO Check why this was added
        // if self.source.out_of_date() {
        //     *self = Cache::default();
        // }

        if !local {
            let offset = FixedOffset::east(
                self.zone
                    .find_local_time_type(d.timestamp())
                    .expect("unable to select local time type")
                    .offset(),
            )?;

            return Ok(LocalResult::Single(DateTime::from_utc(d, offset)));
        }

        // we pass through the year as the year of a local point in time must either be valid in that locale, or
        // the entire time was skipped in which case we will return LocalResult::None anywa.
        match self
            .zone
            .find_local_time_type_from_local(d.timestamp(), d.year())
            .expect("unable to select local time type")
        {
            None => Err(Error::MissingDate),
            Some(LocalResult::Ambiguous(early, late)) => {
                let early_offset = FixedOffset::east(early.offset())?;
                let late_offset = FixedOffset::east(late.offset())?;

                Ok(LocalResult::Ambiguous(
                    DateTime::from_utc(d - early_offset, early_offset),
                    DateTime::from_utc(d - late_offset, late_offset),
                ))
            }
            Some(LocalResult::Single(tt)) => {
                let offset = FixedOffset::east(tt.offset())?;
                Ok(LocalResult::Single(DateTime::from_utc(d - offset, offset)))
            }
        }
    }
}
