// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::{cell::RefCell, collections::hash_map, env, fs, hash::Hasher, time::SystemTime};

use super::tz_info::TimeZone;
use super::{FixedOffset, NaiveDateTime};
use crate::{Datelike, MappedLocalTime};

pub(super) fn offset_from_utc_datetime(utc: &NaiveDateTime) -> MappedLocalTime<FixedOffset> {
    TZ_INFO.with(|cache| {
        let mut cache_ref = cache.borrow_mut();
        let tz_info = cache_ref.tz_info();
        let offset = tz_info
            .find_local_time_type(utc.and_utc().timestamp())
            .expect("unable to select local time type")
            .offset();

        match FixedOffset::east_opt(offset) {
            Some(offset) => MappedLocalTime::Single(offset),
            None => MappedLocalTime::None,
        }
    })
}

pub(super) fn offset_from_local_datetime(local: &NaiveDateTime) -> MappedLocalTime<FixedOffset> {
    TZ_INFO.with(|cache| {
        let mut cache_ref = cache.borrow_mut();
        let tz_info = cache_ref.tz_info();
        tz_info
            .find_local_time_type_from_local(local.and_utc().timestamp(), local.year())
            .expect("unable to select local time type")
            .and_then(|o| FixedOffset::east_opt(o.offset()))
    })
}

struct Cache {
    zone: Option<TimeZone>,
    source: Source,
    last_checked: SystemTime,
}

#[cfg(target_os = "aix")]
const TZDB_LOCATION: &str = "/usr/share/lib/zoneinfo";

#[cfg(not(any(target_os = "android", target_os = "aix")))]
const TZDB_LOCATION: &str = "/usr/share/zoneinfo";

fn fallback_timezone() -> Option<TimeZone> {
    let tz_name = iana_time_zone::get_timezone().ok()?;
    #[cfg(not(target_os = "android"))]
    let bytes = fs::read(format!("{}/{}", TZDB_LOCATION, tz_name)).ok()?;
    #[cfg(target_os = "android")]
    let bytes = android_tzdata::find_tz_data(&tz_name).ok()?;
    TimeZone::from_tz_data(&bytes).ok()
}

impl Cache {
    fn tz_info(&mut self) -> &TimeZone {
        self.refresh_cache();
        self.zone.as_ref().unwrap()
    }

    /// Refresh our cached data if necessary.
    ///
    /// If the cache has been around for less than a second then we reuse it unconditionally. This is
    /// a reasonable tradeoff because the timezone generally won't be changing _that_ often, but if
    /// the time zone does change, it will reflect sufficiently quickly from an application user's
    /// perspective.
    fn refresh_cache(&mut self) {
        let now = SystemTime::now();
        if let Ok(d) = now.duration_since(self.last_checked) {
            if d.as_secs() < 1 && self.source != Source::Uninitialized {
                return;
            }
        }

        if self.needs_update() {
            self.read_tz_info();
        }
        self.last_checked = now;
    }

    /// Check if any of the `TZ` environment variable or `/etc/localtime` have changed.
    fn needs_update(&self) -> bool {
        let env_tz = env::var("TZ").ok();
        let env_ref = env_tz.as_deref();
        let new_source = Source::new(env_ref);

        match (&self.source, &new_source) {
            (Source::Environment { hash: old_hash }, Source::Environment { hash })
                if old_hash == hash =>
            {
                false
            }
            (Source::LocalTime, Source::LocalTime) => {
                match fs::symlink_metadata("/etc/localtime").and_then(|m| m.modified()) {
                    Ok(mtime) => mtime > self.last_checked,
                    Err(_) => false,
                }
            }
            _ => true,
        }
    }

    /// Try to get the current time zone data.
    ///
    /// The following sources are tried in order:
    /// - `TZ` environment variable, containing:
    ///   - the POSIX TZ rule
    ///   - an absolute path
    ///   - an IANA time zone name in combination with the platform time zone database
    /// - the `/etc/localtime` symlink
    /// - the global IANA time zone name in combination with the platform time zone database
    /// - fall back to UTC if all else fails
    fn read_tz_info(&mut self) {
        let env_tz = env::var("TZ").ok();
        self.source = Source::new(env_tz.as_deref());
        self.zone = Some(
            TimeZone::local(env_tz.as_deref())
                .ok()
                .or_else(fallback_timezone)
                .unwrap_or_else(TimeZone::utc),
        );
    }
}

thread_local! {
    static TZ_INFO: RefCell<Cache> = const { RefCell::new(
        Cache {
            zone: None,
            source: Source::Uninitialized,
            last_checked: SystemTime::UNIX_EPOCH,
        }
    ) };
}

#[derive(PartialEq)]
enum Source {
    Environment { hash: u64 },
    LocalTime,
    Uninitialized,
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
            None => Source::LocalTime,
        }
    }
}
