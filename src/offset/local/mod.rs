// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The local (system) time zone.

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use super::fixed::FixedOffset;
use crate::naive::{NaiveDate, NaiveDateTime};
use crate::offset::LocalResult;
use crate::{ChronoError, Date, DateTime, TimeZone};

// we don't want `stub.rs` when the target_os is not wasi or emscripten
// as we use js-sys to get the date instead
#[cfg(all(
    not(unix),
    not(windows),
    not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))
))]
#[path = "stub.rs"]
mod inner;

#[cfg(unix)]
#[path = "unix.rs"]
mod inner;

#[cfg(windows)]
#[path = "windows.rs"]
mod inner;

#[cfg(unix)]
mod tz_info;

/// The local timescale. This is implemented via the standard `time` crate.
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on the Local struct is the preferred way to construct `DateTime<Local>`
/// instances.
///
/// # Example
///
/// ```
/// use chrono::{Local, DateTime, TimeZone};
///
/// let dt: DateTime<Local> = Local::now()?;
/// let dt: DateTime<Local> = Local.timestamp(0, 0)?;
/// # Ok::<_, chrono::ChronoError>(())
/// ```
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct Local;

impl Local {
    /// Returns a `Date` which corresponds to the current date.
    pub fn today() -> Result<Date<Local>, ChronoError> {
        Ok(Local::now()?.date())
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))]
    pub fn now() -> Result<DateTime<Local>, ChronoError> {
        inner::now()
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))]
    pub fn now() -> DateTime<Local> {
        use super::Utc;
        let now: DateTime<Utc> = super::Utc::now();

        // Workaround missing timezone logic in `time` crate
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        DateTime::from_utc(now.naive_utc(), offset)
    }
}

impl TimeZone for Local {
    type Offset = FixedOffset;

    fn from_offset(_offset: &FixedOffset) -> Local {
        Local
    }

    // they are easier to define in terms of the finished date and time unlike other offsets
    fn offset_from_local_date(
        &self,
        local: &NaiveDate,
    ) -> Result<LocalResult<Self::Offset>, ChronoError> {
        Ok(self.from_local_date(local)?.map(|o| *o.offset()))
    }

    fn offset_from_local_datetime(
        &self,
        local: &NaiveDateTime,
    ) -> Result<LocalResult<Self::Offset>, ChronoError> {
        Ok(self.from_local_datetime(local)?.map(|o| *o.offset()))
    }

    fn offset_from_utc_date(&self, utc: &NaiveDate) -> Result<FixedOffset, ChronoError> {
        Ok(*self.from_utc_date(utc)?.offset())
    }

    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> Result<FixedOffset, ChronoError> {
        Ok(*self.from_utc_datetime(utc)?.offset())
    }

    // override them for avoiding redundant works
    fn from_local_date(&self, local: &NaiveDate) -> Result<LocalResult<Date<Local>>, ChronoError> {
        // this sounds very strange, but required for keeping `TimeZone::ymd` sane.
        // in the other words, we use the offset at the local midnight
        // but keep the actual date unaltered (much like `FixedOffset`).
        let midnight = self.from_local_datetime(&local.and_midnight())?;
        Ok(midnight.map(|midnight| Date::from_utc(*local, *midnight.offset())))
    }

    #[cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))]
    fn from_local_datetime(&self, local: &NaiveDateTime) -> Result<DateTime<Local>, ChronoError> {
        let mut local = local.clone();
        // Get the offset from the js runtime
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        local -= crate::TimeDelta::seconds(offset.local_minus_utc() as i64);
        Ok(DateTime::from_utc(local, offset))
    }

    #[cfg(not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))]
    fn from_local_datetime(
        &self,
        local: &NaiveDateTime,
    ) -> Result<LocalResult<DateTime<Local>>, ChronoError> {
        inner::naive_to_local(local, true)
    }

    fn from_utc_date(&self, utc: &NaiveDate) -> Result<Date<Local>, ChronoError> {
        let midnight = self.from_utc_datetime(&utc.and_midnight())?;
        Ok(Date::from_utc(*utc, *midnight.offset()))
    }

    #[cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> Result<DateTime<Local>, ChronoError> {
        // Get the offset from the js runtime
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        DateTime::from_utc(*utc, offset)
    }

    #[cfg(not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> Result<DateTime<Local>, ChronoError> {
        inner::naive_to_local(utc, false)?.single()
    }
}

#[cfg(test)]
mod tests {
    use super::Local;
    use crate::offset::TimeZone;
    use crate::{Datelike, TimeDelta};
    #[cfg(unix)]
    use crate::{NaiveDate, NaiveDateTime, Timelike};

    #[cfg(unix)]
    use std::{path, process};

    #[cfg(unix)]
    fn verify_against_date_command_local(path: &'static str, dt: NaiveDateTime) {
        let output = process::Command::new(path)
            .arg("-d")
            .arg(format!("{}-{:02}-{:02} {:02}:05:01", dt.year(), dt.month(), dt.day(), dt.hour()))
            .arg("+%Y-%m-%d %H:%M:%S %:z")
            .output()
            .unwrap();

        let date_command_str = String::from_utf8(output.stdout).unwrap();

        // The below would be preferred. At this stage neither earliest() or latest()
        // seems to be consistent with the output of the `date` command, so we simply
        // compare both.
        // let local = Local
        //     .from_local_datetime(&NaiveDate::from_ymd(year, month, day).and_hms(hour, 5, 1))
        //     // looks like the "date" command always returns a given time when it is ambiguous
        //     .earliest();

        // if let Some(local) = local {
        //     assert_eq!(format!("{}\n", local), date_command_str);
        // } else {
        //     // we are in a "Spring forward gap" due to DST, and so date also returns ""
        //     assert_eq!("", date_command_str);
        // }

        // This is used while a decision is made wheter the `date` output needs to
        // be exactly matched, or whether LocalResult::Ambigious should be handled
        // differently
        let dt = Local
            .from_local_datetime(
                &NaiveDate::from_ymd(dt.year(), dt.month(), dt.day())
                    .unwrap()
                    .and_hms(dt.hour(), 5, 1)
                    .unwrap(),
            )
            .unwrap()
            .single()
            .unwrap();

        assert_eq!(format!("{}\n", dt), date_command_str);
    }

    #[test]
    #[cfg(unix)]
    fn try_verify_against_date_command() {
        let date_path = "/usr/bin/date";

        if !path::Path::new(date_path).exists() {
            // date command not found, skipping
            // avoid running this on macOS, which has path /bin/date
            // as the required CLI arguments are not present in the
            // macOS build.
            return;
        }

        let mut date = NaiveDate::from_ymd(1975, 1, 1).unwrap().and_hms(0, 0, 0).unwrap();

        while date.year() < 2078 {
            if (1975..=1977).contains(&date.year())
                || (2020..=2022).contains(&date.year())
                || (2073..=2077).contains(&date.year())
            {
                verify_against_date_command_local(date_path, date);
            }

            date += crate::TimeDelta::hours(1);
        }
    }

    #[test]
    fn verify_correct_offsets() {
        let now = Local::now().unwrap();
        let from_local = Local.from_local_datetime(&now.naive_local()).unwrap().unwrap();
        let from_utc = Local.from_utc_datetime(&now.naive_utc()).unwrap();

        assert_eq!(now.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(now.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(now, from_local);
        assert_eq!(now, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_past() {
        // let distant_past = Local::now() - Duration::days(365 * 100);
        let distant_past = Local::now().unwrap() - TimeDelta::days(250 * 31);
        let from_local = Local.from_local_datetime(&distant_past.naive_local()).unwrap().unwrap();
        let from_utc = Local.from_utc_datetime(&distant_past.naive_utc()).unwrap();

        assert_eq!(distant_past.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(distant_past.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(distant_past, from_local);
        assert_eq!(distant_past, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_future() {
        let distant_future = Local::now().unwrap() + TimeDelta::days(250 * 31);
        let from_local = Local.from_local_datetime(&distant_future.naive_local()).unwrap().unwrap();
        let from_utc = Local.from_utc_datetime(&distant_future.naive_utc()).unwrap();

        assert_eq!(
            distant_future.offset().local_minus_utc(),
            from_local.offset().local_minus_utc()
        );
        assert_eq!(distant_future.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(distant_future, from_local);
        assert_eq!(distant_future, from_utc);
    }

    #[test]
    fn test_local_date_sanity_check() {
        // issue #27
        assert_eq!(Local.ymd(2999, 12, 28).unwrap().unwrap().day(), 28);
    }

    #[test]
    fn test_leap_second() {
        // issue #123
        let today = Local::today().unwrap();

        let dt = today.and_hms_milli(1, 2, 59, 1000).unwrap();
        let timestr = dt.time().to_string();
        // the OS API may or may not support the leap second,
        // but there are only two sensible options.
        assert!(timestr == "01:02:60" || timestr == "01:03:00", "unexpected timestr {:?}", timestr);

        let dt = today.and_hms_milli(1, 2, 3, 1234).unwrap();
        let timestr = dt.time().to_string();
        assert!(
            timestr == "01:02:03.234" || timestr == "01:02:04.234",
            "unexpected timestr {:?}",
            timestr
        );
    }
}
