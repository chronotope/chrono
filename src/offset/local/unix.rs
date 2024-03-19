// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cell::RefCell;
use std::collections::hash_map;
use std::env;
use std::fs;
use std::hash::Hasher;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

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

struct CachedTzInfo {
    zone: Option<TimeZone>,
    source: Source,
    last_checked: SystemTime,
}

impl CachedTzInfo {
    fn tz_info(&mut self) -> &TimeZone {
        self.refresh_cache();
        self.zone.as_ref().unwrap()
    }

    // Refresh our cached data if necessary.
    //
    // If the cache has been around for less than a second then we reuse it unconditionally. This is
    // a reasonable tradeoff because the timezone generally won't be changing _that_ often, but if
    // the time zone does change, it will reflect sufficiently quickly from an application user's
    // perspective.
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
        self.source = Source::new(env::var("TZ").ok().as_deref());

        let tz_var = TzEnvVar::get();
        if let Some(tz_var) = tz_var {
            if self.read_from_tz_env(&tz_var).is_ok() {
                return;
            }
        }
        #[cfg(not(target_os = "android"))]
        if self.read_from_symlink().is_ok() {
            return;
        }
        if self.read_with_tz_name().is_ok() {
            return;
        }
        self.zone = Some(TimeZone::utc());
    }

    /// Read the `TZ` environment variable or the TZif file that it points to.
    fn read_from_tz_env(&mut self, tz_var: &TzEnvVar) -> Result<(), ()> {
        match tz_var {
            TzEnvVar::TzString(tz_string) => {
                self.zone = Some(TimeZone::from_tz_string(tz_string).map_err(|_| ())?);
            }
            TzEnvVar::Path(path) => {
                let path = PathBuf::from(&path[1..]);
                let tzif = fs::read(path).map_err(|_| ())?;
                self.zone = Some(TimeZone::from_tz_data(&tzif).map_err(|_| ())?);
            }
            TzEnvVar::TzName(tz_id) => self.read_tzif(&tz_id[1..])?,
            #[cfg(not(target_os = "android"))]
            TzEnvVar::LocaltimeSymlink => self.read_from_symlink()?,
        };
        Ok(())
    }

    /// Read the Tzif file that `/etc/localtime` is symlinked to.
    #[cfg(not(target_os = "android"))]
    fn read_from_symlink(&mut self) -> Result<(), ()> {
        let tzif = fs::read("/etc/localtime").map_err(|_| ())?;
        self.zone = Some(TimeZone::from_tz_data(&tzif).map_err(|_| ())?);
        Ok(())
    }

    /// Get the IANA time zone name of the system by whichever means the `iana_time_zone` crate gets
    /// it, and try to read the corresponding TZif data.
    fn read_with_tz_name(&mut self) -> Result<(), ()> {
        let tz_name = iana_time_zone::get_timezone().map_err(|_| ())?;
        self.read_tzif(&tz_name)
    }

    /// Try to read the TZif data for the specified time zone name.
    fn read_tzif(&mut self, tz_name: &str) -> Result<(), ()> {
        let tzif = self.read_tzif_inner(tz_name)?;
        self.zone = Some(TimeZone::from_tz_data(&tzif).map_err(|_| ())?);
        Ok(())
    }

    #[cfg(not(target_os = "android"))]
    fn read_tzif_inner(&self, tz_name: &str) -> Result<Vec<u8>, ()> {
        let path = self.tzdb_dir()?.join(tz_name);
        let tzif = fs::read(path).map_err(|_| ())?;
        Ok(tzif)
    }
    #[cfg(target_os = "android")]
    fn read_tzif_inner(&self, tz_name: &str) -> Result<Vec<u8>, ()> {
        let tzif = android_tzdata::find_tz_data(&tz_name).map_err(|_| ())?;
        Ok(tzif)
    }

    /// Get the location of the time zone database directory with TZif files.
    #[cfg(not(target_os = "android"))]
    fn tzdb_dir(&self) -> Result<PathBuf, ()> {
        // Possible system timezone directories
        const ZONE_INFO_DIRECTORIES: [&str; 4] =
            ["/usr/share/zoneinfo", "/share/zoneinfo", "/etc/zoneinfo", "/usr/share/lib/zoneinfo"];

        for dir in &ZONE_INFO_DIRECTORIES {
            let path = PathBuf::from(dir);
            if path.exists() {
                return Ok(path);
            }
        }
        Err(())
    }
}

thread_local! {
    static TZ_INFO: RefCell<CachedTzInfo> = const { RefCell::new(
        CachedTzInfo {
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

/// Type of the `TZ` environment variable.
///
/// Supported formats are:
/// - a POSIX TZ string
/// - an absolute path (starting with `:/`, as supported by glibc and others)
/// - a time zone name (starting with `:`, as supported by glibc and others)
/// - "localtime" (supported by Solaris and maybe others)
enum TzEnvVar {
    TzString(String),
    Path(String),   // Value still starts with `:`
    TzName(String), // Value still starts with `:`
    #[cfg(not(target_os = "android"))]
    LocaltimeSymlink,
}

impl TzEnvVar {
    /// Get the current value of the `TZ` environment variable and determine its format.
    fn get() -> Option<TzEnvVar> {
        match env::var("TZ").ok() {
            None => None,
            Some(s) if s.is_empty() => None,
            #[cfg(not(target_os = "android"))]
            Some(s) if s == "localtime" => Some(TzEnvVar::LocaltimeSymlink),
            Some(tz_var) => match tz_var.strip_prefix(':') {
                Some(path) if Path::new(&path).is_absolute() => Some(TzEnvVar::Path(tz_var)),
                Some(_) => Some(TzEnvVar::TzName(tz_var)),
                None => Some(TzEnvVar::TzString(tz_var)),
            },
        }
    }
}
