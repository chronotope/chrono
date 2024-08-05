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
use std::env;
use std::fs;
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
    tz_var: Option<TzEnvVar>,
    tz_name: Option<String>,
    path: Option<PathBuf>,
    tzdb_dir: Option<PathBuf>,
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

    /// Check if any of the environment variables or files have changed, or the name of the current
    /// time zone as determined by the `iana_time_zone` crate.
    fn needs_update(&self) -> bool {
        if self.tz_env_var_changed() {
            return true;
        }
        if self.source == Source::TzEnvVar {
            return false; // No need for further checks if the cached value came from the `TZ` var.
        }
        if self.symlink_changed() {
            return true;
        }
        if self.source == Source::Localtime {
            return false; // No need for further checks if the cached value came from the symlink.
        }
        if self.tz_name_changed() {
            return true;
        }
        false
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
        let tz_var = TzEnvVar::get();
        match tz_var {
            None => self.tz_var = None,
            Some(tz_var) => {
                if self.read_from_tz_env(&tz_var).is_ok() {
                    self.tz_var = Some(tz_var);
                    return;
                }
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
        self.source = Source::Utc;
    }

    /// Read the `TZ` environment variable or the TZif file that it points to.
    fn read_from_tz_env(&mut self, tz_var: &TzEnvVar) -> Result<(), ()> {
        match tz_var {
            TzEnvVar::TzString(tz_string) => {
                self.zone = Some(TimeZone::from_tz_string(tz_string).map_err(|_| ())?);
                self.path = None;
            }
            TzEnvVar::Path(path) => {
                let path = PathBuf::from(&path[1..]);
                let tzif = fs::read(&path).map_err(|_| ())?;
                self.zone = Some(TimeZone::from_tz_data(&tzif).map_err(|_| ())?);
                self.path = Some(path);
            }
            TzEnvVar::TzName(tz_id) => self.read_tzif(&tz_id[1..])?,
            #[cfg(not(target_os = "android"))]
            TzEnvVar::LocaltimeSymlink => self.read_from_symlink()?,
        };
        self.source = Source::TzEnvVar;
        Ok(())
    }

    /// Check if the `TZ` environment variable has changed, or the file it points to.
    fn tz_env_var_changed(&self) -> bool {
        let tz_var = TzEnvVar::get();
        match (&self.tz_var, &tz_var) {
            (None, None) => false,
            (Some(TzEnvVar::TzString(a)), Some(TzEnvVar::TzString(b))) if a == b => false,
            (Some(TzEnvVar::Path(a)), Some(TzEnvVar::Path(b))) if a == b => {
                self.mtime_changed(self.path.as_deref())
            }
            (Some(TzEnvVar::TzName(a)), Some(TzEnvVar::TzName(b))) if a == b => {
                self.mtime_changed(self.path.as_deref()) || self.tzdb_dir_changed()
            }
            #[cfg(not(target_os = "android"))]
            (Some(TzEnvVar::LocaltimeSymlink), Some(TzEnvVar::LocaltimeSymlink)) => {
                self.symlink_changed()
            }
            _ => true,
        }
    }

    /// Read the Tzif file that `/etc/localtime` is symlinked to.
    #[cfg(not(target_os = "android"))]
    fn read_from_symlink(&mut self) -> Result<(), ()> {
        let tzif = fs::read("/etc/localtime").map_err(|_| ())?;
        self.zone = Some(TimeZone::from_tz_data(&tzif).map_err(|_| ())?);
        self.source = Source::Localtime;
        Ok(())
    }

    /// Check if the `/etc/localtime` symlink or its target has changed.
    fn symlink_changed(&self) -> bool {
        self.mtime_changed(Some(Path::new("/etc/localtime")))
    }

    /// Get the IANA time zone name of the system by whichever means the `iana_time_zone` crate gets
    /// it, and try to read the corresponding TZif data.
    fn read_with_tz_name(&mut self) -> Result<(), ()> {
        let tz_name = iana_time_zone::get_timezone().map_err(|_| ())?;
        self.read_tzif(&tz_name)?;
        self.tz_name = Some(tz_name);
        self.source = Source::TimeZoneName;
        Ok(())
    }

    /// Check if the IANA time zone name has changed, or the file it points to.
    fn tz_name_changed(&self) -> bool {
        self.tz_name != iana_time_zone::get_timezone().ok()
            || self.tzdb_dir_changed()
            || self.mtime_changed(self.path.as_deref())
    }

    /// Try to read the TZif data for the specified time zone name.
    fn read_tzif(&mut self, tz_name: &str) -> Result<(), ()> {
        let (tzif, path) = self.read_tzif_inner(tz_name)?;
        self.zone = Some(TimeZone::from_tz_data(&tzif).map_err(|_| ())?);
        self.path = path;
        Ok(())
    }

    #[cfg(not(target_os = "android"))]
    fn read_tzif_inner(&mut self, tz_name: &str) -> Result<(Vec<u8>, Option<PathBuf>), ()> {
        let path = self.tzdb_dir()?.join(tz_name);
        let tzif = fs::read(&path).map_err(|_| ())?;
        Ok((tzif, Some(path)))
    }
    #[cfg(target_os = "android")]
    fn read_tzif_inner(&mut self, tz_name: &str) -> Result<(Vec<u8>, Option<PathBuf>), ()> {
        let tzif = android_tzdata::find_tz_data(&tz_name).map_err(|_| ())?;
        Ok((tzif, None))
    }

    /// Get the location of the time zone database directory with TZif files.
    #[cfg(not(target_os = "android"))]
    fn tzdb_dir(&mut self) -> Result<PathBuf, ()> {
        // Possible system timezone directories
        const ZONE_INFO_DIRECTORIES: [&str; 4] =
            ["/usr/share/zoneinfo", "/share/zoneinfo", "/etc/zoneinfo", "/usr/share/lib/zoneinfo"];

        // Use the value of the `TZDIR` environment variable if set.
        if let Some(tz_dir) = env::var_os("TZDIR") {
            if !tz_dir.is_empty() {
                let path = PathBuf::from(tz_dir);
                if path.exists() {
                    return Ok(path);
                }
            }
        }

        // Use the cached value
        if let Some(dir) = self.tzdb_dir.as_ref() {
            return Ok(PathBuf::from(dir));
        }

        // No cached value yet, try the various possible system timezone directories.
        for dir in &ZONE_INFO_DIRECTORIES {
            let path = PathBuf::from(dir);
            if path.exists() {
                self.tzdb_dir = Some(path.clone());
                return Ok(path);
            }
        }
        Err(())
    }

    /// Check if the location that the `TZDIR` environment variable points to has changed.
    fn tzdb_dir_changed(&self) -> bool {
        #[cfg(not(target_os = "android"))]
        if let Some(tz_dir) = env::var_os("TZDIR") {
            if !tz_dir.is_empty()
                && Some(tz_dir.as_os_str()) != self.tzdb_dir.as_ref().map(|d| d.as_os_str())
            {
                return true;
            }
        }
        false
    }

    /// Returns `true` if the modification time of the TZif file or symlink is more recent then
    /// `self.last_checked`.
    ///
    /// Also returns `true` if there was an error getting the modification time.
    /// If the file is a symlink this method checks the symlink and the final target.
    fn mtime_changed(&self, path: Option<&Path>) -> bool {
        fn inner(path: &Path, last_checked: SystemTime) -> Result<bool, std::io::Error> {
            let metadata = fs::symlink_metadata(path)?;
            if metadata.modified()? > last_checked {
                return Ok(true);
            }
            if metadata.is_symlink() && fs::metadata(path)?.modified()? > last_checked {
                return Ok(true);
            }
            Ok(false)
        }
        match path {
            Some(path) => inner(path, self.last_checked).unwrap_or(true),
            None => false,
        }
    }
}

thread_local! {
    static TZ_INFO: RefCell<CachedTzInfo> = const { RefCell::new(
        CachedTzInfo {
            zone: None,
            source: Source::Uninitialized,
            last_checked: SystemTime::UNIX_EPOCH,
            tz_var: None,
            tz_name: None,
            path: None,
            tzdb_dir: None,
        }
    ) };
}

#[derive(PartialEq)]
enum Source {
    TzEnvVar,
    Localtime,
    TimeZoneName,
    Utc,
    Uninitialized,
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
