// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The local (system) time zone.

use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use super::fixed::FixedOffset;
use super::utc::Utc;
use super::{LocalResult, TimeZone};

#[cfg(windows)]
use crate::naive::NaiveTime;
use crate::naive::{NaiveDate, NaiveDateTime};
use crate::{Date, DateTime};
#[cfg(windows)]
use crate::{Datelike, Timelike};

#[cfg(all(not(unix), not(windows)))]
#[path = "sys/stub.rs"]
mod inner;

#[cfg(unix)]
#[path = "sys/unix.rs"]
mod inner;

#[cfg(windows)]
#[path = "sys/windows.rs"]
mod inner;

use inner::{local_tm_to_time, time_to_local_tm, utc_tm_to_time};

#[cfg(all(unix, not(all(target_arch = "wasm32", feature = "wasmbind"))))]
mod tz_localtime {
    use super::*;
    use crate::{Datelike, Duration, NaiveTime};
    use std::{env, path};
    use tz::{error, timezone};

    const LOCALTIME_LOCATION: &str = "/etc/localtime";

    fn current_offset(
        tz: &tz::TimeZone,
        now: DateTime<Utc>,
    ) -> Result<FixedOffset, error::TzError> {
        let local = tz.find_local_time_type(now.timestamp())?;

        // create and return a FixedOffset which will be used to create the local time
        Ok(FixedOffset::east(local.ut_offset()))
    }

    fn offset_from_local(
        tz: &tz::TimeZone,
        local: NaiveDateTime,
    ) -> Result<FixedOffset, error::TzError> {
        // ignoring extra rules for now
        // also its not clear whether the given `local` includes or doesn't include leap seconds?
        // get the last transition time
        let last = tz.as_ref().transitions().last();

        // if there is no transitions, or if we are later than the last transition,
        // then we must try to use the extra rule(s)
        if last
            .map(|last_tt| {
                last_tt.unix_leap_time()
                    + i64::from(
                        tz.as_ref().local_time_types()[last_tt.local_time_type_index()].ut_offset(),
                    )
                    < local.timestamp()
            })
            .unwrap_or(true)
        {
            match tz.as_ref().extra_rule() {
                Some(timezone::TransitionRule::Fixed(fix)) => {
                    return Ok(FixedOffset::east(fix.ut_offset()));
                }
                Some(timezone::TransitionRule::Alternate(alt)) => {
                    match (alt.dst_start(), alt.dst_end()) {
                        (
                            timezone::RuleDay::MonthWeekDay(start @ timezone::MonthWeekDay { .. }),
                            timezone::RuleDay::MonthWeekDay(end @ timezone::MonthWeekDay { .. }),
                        ) => {
                            let start = naivedatetime_from_mwd(local, start, alt.dst_start_time());
                            let end = naivedatetime_from_mwd(local, end, alt.dst_end_time());

                            use std::cmp::Ordering;
                            match start.cmp(&end) {
                                Ordering::Less if local >= start && local < end => {
                                    // southern hemisphere
                                    return Ok(FixedOffset::east(alt.dst().ut_offset()));
                                }
                                Ordering::Equal | Ordering::Greater
                                    if local >= start || local < end =>
                                {
                                    // northern hemisphere
                                    return Ok(FixedOffset::east(alt.dst().ut_offset()));
                                }
                                _ => {
                                    return Ok(FixedOffset::east(alt.std().ut_offset()));
                                }
                            }
                        }
                        _ => {
                            todo!("Handle non month-week-day alt rule")
                        }
                    }
                }
                None => {
                    return Err(error::OutOfRangeError("The given local time is either too early or too late for the range of transitions available and there is no extra rule to find the timezone").into());
                }
            }
        }

        // otherwise we go through all of the local times
        let mut prev_offset = None;
        for tt in tz.as_ref().transitions() {
            let local_offset = tz.as_ref().local_time_types()[tt.local_time_type_index()];

            if tt.unix_leap_time() + i64::from(local_offset.ut_offset()) > local.timestamp() {
                break;
            } else {
                prev_offset = Some(local_offset.ut_offset());
            }
        }

        // create and return a FixedOffset which will be used to create the local time
        if let Some(offset) = prev_offset {
            Ok(FixedOffset::east(offset))
        } else {
            // in this case we were earlier than the earliest time. we should use the first one in this case.
            let first_local_time_type = tz
                .as_ref()
                .local_time_types()
                .get(0)
                .ok_or(error::OutOfRangeError("No available transition times"))?;

            Ok(FixedOffset::east(first_local_time_type.ut_offset()))
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_naive_time_from_seconds() {
            assert_eq!(naive_time_from_seconds(1), NaiveTime::from_hms(0, 0, 1),);
            assert_eq!(naive_time_from_seconds(3661), NaiveTime::from_hms(1, 1, 1),);
            assert_eq!(
                naive_time_from_seconds(22 * 60 * 60 + 15 * 60 + 7),
                NaiveTime::from_hms(22, 15, 7),
            );
        }

        #[test]
        fn test_naive_date_from_mwd_parts() {
            assert_eq!(naive_date_from_mwd_parts(2022, 1, 1, 5), NaiveDate::from_ymd(2022, 1, 7));
            assert_eq!(naive_date_from_mwd_parts(2022, 1, 1, 3), NaiveDate::from_ymd(2022, 1, 5));
            assert_eq!(naive_date_from_mwd_parts(2022, 1, 1, 6), NaiveDate::from_ymd(2022, 1, 1));
            assert_eq!(naive_date_from_mwd_parts(2022, 1, 2, 1), NaiveDate::from_ymd(2022, 1, 10));
            assert_eq!(naive_date_from_mwd_parts(2022, 1, 2, 3), NaiveDate::from_ymd(2022, 1, 12));
            assert_eq!(naive_date_from_mwd_parts(2022, 1, 2, 6), NaiveDate::from_ymd(2022, 1, 8));
            assert_eq!(naive_date_from_mwd_parts(2022, 3, 1, 0), NaiveDate::from_ymd(2022, 3, 6));
            assert_eq!(naive_date_from_mwd_parts(2022, 3, 1, 1), NaiveDate::from_ymd(2022, 3, 7));
            assert_eq!(naive_date_from_mwd_parts(2022, 3, 1, 2), NaiveDate::from_ymd(2022, 3, 1));
            assert_eq!(naive_date_from_mwd_parts(2022, 3, 1, 3), NaiveDate::from_ymd(2022, 3, 2));
            assert_eq!(naive_date_from_mwd_parts(2022, 3, 1, 4), NaiveDate::from_ymd(2022, 3, 3));
            assert_eq!(naive_date_from_mwd_parts(2022, 3, 1, 5), NaiveDate::from_ymd(2022, 3, 4));
            assert_eq!(naive_date_from_mwd_parts(2022, 3, 1, 6), NaiveDate::from_ymd(2022, 3, 5));
        }
    }

    fn naive_time_from_seconds(start_time: i32) -> NaiveTime {
        use std::convert::TryFrom;
        let h = start_time / 3600;
        let m = (start_time - 3600 * h) / 60;
        let s = start_time - 3600 * h - 60 * m;
        NaiveTime::from_hms(
            u32::try_from(h).unwrap(),
            u32::try_from(m).unwrap(),
            u32::try_from(s).unwrap(),
        )
    }

    fn naive_date_from_mwd_parts(year: i32, month: u32, week_num: u32, week_day: u32) -> NaiveDate {
        // get the first day of the relevant week
        let base = (week_num.saturating_sub(1)) * 7 + 1;

        // build a date from the first day of the relevant week.
        // this is the earliest possible date that it will be
        let base_date = NaiveDate::from_ymd(year, month, base);

        let base_from_sunday = base_date.weekday().num_days_from_sunday();

        use std::cmp::Ordering;
        match base_from_sunday.cmp(&week_day) {
            Ordering::Equal => base_date,
            Ordering::Greater => {
                base_date + Duration::days(i64::from(7 - (base_from_sunday - week_day)))
            }
            Ordering::Less => base_date + Duration::days(i64::from(week_day - base_from_sunday)),
        }
    }

    fn naivedatetime_from_mwd(
        local: NaiveDateTime,
        mwd: &timezone::MonthWeekDay,
        start_time: i32,
    ) -> NaiveDateTime {
        naive_date_from_mwd_parts(
            local.year(),
            local.month(),
            mwd.week().into(),
            mwd.week_day().into(),
        )
        .and_time(naive_time_from_seconds(start_time))
    }

    fn utc_now() -> DateTime<Local> {
        DateTime::<Local>::from_utc(Utc::now().naive_local(), FixedOffset::east(0))
    }

    fn utc_from_local(local: NaiveDateTime) -> DateTime<Local> {
        DateTime::<Local>::from_utc(local, FixedOffset::east(0))
    }

    fn try_now() -> Result<DateTime<Local>, error::TzError> {
        if let Ok(tz) = get_local_tz() {
            let base = Utc::now();
            let current_offset = current_offset(&tz, base)?;
            let local = DateTime::<Local>::from_utc(base.naive_local(), current_offset);
            Ok(local)
        } else {
            // error while getting tz, tz assumed to be UTC.
            Ok(utc_now())
        }
    }

    pub(crate) fn now() -> DateTime<Local> {
        match try_now() {
            Ok(n) => n,
            // #TODO: could use log/tracing to have a warning show here
            Err(_) => utc_now(),
        }
    }

    fn get_local_tz() -> Result<tz::TimeZone, error::TzError> {
        if let Ok(tz_val) = env::var("TZ") {
            timezone::TimeZone::from_posix_tz(&tz_val)
        } else if path::Path::new(LOCALTIME_LOCATION).exists() {
            timezone::TimeZone::local()
        } else {
            eprintln!("Falling back to UTC as no TZ env var or /etc/localtime is available");
            Ok(tz::TimeZone::utc())
        }
    }

    fn try_from_utc(utc: NaiveDateTime) -> Result<DateTime<Local>, error::TzError> {
        if let Ok(tz) = get_local_tz() {
            let current_offset = current_offset(&tz, DateTime::from_utc(utc, Utc))?;
            let local = DateTime::<Local>::from_utc(utc, current_offset);
            Ok(local)
        } else {
            // error while getting tz, tz assumed to be UTC.
            eprintln!("Error while determining local time zone, falling back to UTC");
            let local = DateTime::<Local>::from_utc(utc, FixedOffset::east(0));
            Ok(local)
        }
    }

    pub(crate) fn from_utc(utc: NaiveDateTime) -> DateTime<Local> {
        match try_from_utc(utc) {
            Ok(n) => n,
            Err(e) => panic!("Unable to calculate local time offset due to: {}", e),
        }
    }

    fn try_from_local(local: NaiveDateTime) -> Result<DateTime<Local>, error::TzError> {
        if let Ok(tz) = get_local_tz() {
            let relevant_offset = offset_from_local(&tz, local)?;

            let local = DateTime::<Local>::from_utc(local - relevant_offset, relevant_offset);

            Ok(local)
        } else {
            // no file found, tz assumed to be UTC.
            eprintln!("Error while determining local time zone, falling back to UTC");
            Ok(utc_from_local(local))
        }
    }

    pub(crate) fn from_local(local: NaiveDateTime) -> DateTime<Local> {
        match try_from_local(local) {
            Ok(n) => n,
            // #TODO: could use log/tracing to have a warning show here
            Err(e) => panic!("Unable to calculate local time offset due to: {}", e),
        }
    }
}

#[cfg(target_os = "wasi")]
compile_error!("the `clock` feature is not supported on WASI");

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
/// let dt: DateTime<Local> = Local::now();
/// let dt: DateTime<Local> = Local.timestamp(0, 0);
/// ```
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct Local;

impl Local {
    /// Returns a `Date` which corresponds to the current date.
    pub fn today() -> Date<Local> {
        Local::now().date()
    }

    /// Returns a `DateTime` which corresponds to the current date.
    #[cfg(all(unix, not(all(target_arch = "wasm32", feature = "wasmbind"))))]
    pub fn now() -> DateTime<Local> {
        tz_localtime::now()
    }

    /// Returns a `DateTime` which corresponds to the current date.
    #[cfg(windows)]

    pub fn now() -> DateTime<Local> {
        tm_to_datetime(Timespec::now().local())
    }

    /// Returns a `DateTime` which corresponds to the current date.
    #[cfg(all(target_arch = "wasm32", feature = "wasmbind"))]
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
    fn offset_from_local_date(&self, local: &NaiveDate) -> LocalResult<FixedOffset> {
        self.from_local_date(local).map(|date| *date.offset())
    }

    fn offset_from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        self.from_local_datetime(local).map(|datetime| *datetime.offset())
    }

    fn offset_from_utc_date(&self, utc: &NaiveDate) -> FixedOffset {
        *self.from_utc_date(utc).offset()
    }

    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> FixedOffset {
        *self.from_utc_datetime(utc).offset()
    }

    // override them for avoiding redundant works
    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<Local>> {
        // this sounds very strange, but required for keeping `TimeZone::ymd` sane.
        // in the other words, we use the offset at the local midnight
        // but keep the actual date unaltered (much like `FixedOffset`).
        let midnight = self.from_local_datetime(&local.and_hms(0, 0, 0));
        midnight.map(|datetime| Date::from_utc(*local, *datetime.offset()))
    }

    #[cfg(all(target_arch = "wasm32", feature = "wasmbind"))]
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Local>> {
        let mut local = local.clone();
        // Get the offset from the js runtime
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        local -= crate::Duration::seconds(offset.local_minus_utc() as i64);
        LocalResult::Single(DateTime::from_utc(local, offset))
    }

    #[cfg(all(unix, not(all(target_arch = "wasm32", feature = "wasmbind"))))]
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Local>> {
        LocalResult::Single(tz_localtime::from_local(*local))
    }

    #[cfg(windows)]
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Local>> {
        LocalResult::Single(naive_to_local(local, true))
    }

    fn from_utc_date(&self, utc: &NaiveDate) -> Date<Local> {
        let midnight = self.from_utc_datetime(&utc.and_hms(0, 0, 0));
        Date::from_utc(*utc, *midnight.offset())
    }

    #[cfg(all(target_arch = "wasm32", feature = "wasmbind"))]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Local> {
        // Get the offset from the js runtime
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        DateTime::from_utc(*utc, offset)
    }

    #[cfg(all(unix, not(all(target_arch = "wasm32", feature = "wasmbind"))))]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Local> {
        tz_localtime::from_utc(*utc)
    }

    #[cfg(windows)]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Local> {
        naive_to_local(utc, false)
    }
}

/// Converts a local `NaiveDateTime` to the `time::Timespec`.
#[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
fn naive_to_local(d: &NaiveDateTime, local: bool) -> DateTime<Local> {
    let tm = Tm {
        tm_sec: d.second() as i32,
        tm_min: d.minute() as i32,
        tm_hour: d.hour() as i32,
        tm_mday: d.day() as i32,
        tm_mon: d.month0() as i32, // yes, C is that strange...
        tm_year: d.year() - 1900,  // this doesn't underflow, we know that d is `NaiveDateTime`.
        tm_wday: 0,                // to_local ignores this
        tm_yday: 0,                // and this
        tm_isdst: -1,
        // This seems pretty fake?
        tm_utcoff: if local { 1 } else { 0 },
        // do not set this, OS APIs are heavily inconsistent in terms of leap second handling
        tm_nsec: 0,
    };

    let spec = Timespec {
        sec: match local {
            false => utc_tm_to_time(&tm),
            true => local_tm_to_time(&tm),
        },
        nsec: tm.tm_nsec,
    };

    // Adjust for leap seconds
    let mut tm = spec.local();
    assert_eq!(tm.tm_nsec, 0);
    tm.tm_nsec = d.nanosecond() as i32;

    tm_to_datetime(tm)
}

/// Converts a `time::Tm` struct into the timezone-aware `DateTime`.
/// This assumes that `time` is working correctly, i.e. any error is fatal.
#[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
fn tm_to_datetime(mut tm: Tm) -> DateTime<Local> {
    if tm.tm_sec >= 60 {
        tm.tm_nsec += (tm.tm_sec - 59) * 1_000_000_000;
        tm.tm_sec = 59;
    }

    #[cfg(not(windows))]
    fn tm_to_naive_date(tm: &Tm) -> NaiveDate {
        // from_yo is more efficient than from_ymd (since it's the internal representation).
        NaiveDate::from_yo(tm.tm_year + 1900, tm.tm_yday as u32 + 1)
    }

    #[cfg(windows)]
    fn tm_to_naive_date(tm: &Tm) -> NaiveDate {
        // ...but tm_yday is broken in Windows (issue #85)
        NaiveDate::from_ymd(tm.tm_year + 1900, tm.tm_mon as u32 + 1, tm.tm_mday as u32)
    }

    let date = tm_to_naive_date(&tm);
    let time = NaiveTime::from_hms_nano(
        tm.tm_hour as u32,
        tm.tm_min as u32,
        tm.tm_sec as u32,
        tm.tm_nsec as u32,
    );
    let offset = FixedOffset::east(tm.tm_utcoff);
    DateTime::from_utc(date.and_time(time) - offset, offset)
}

/// A record specifying a time value in seconds and nanoseconds, where
/// nanoseconds represent the offset from the given second.
///
/// For example a timespec of 1.2 seconds after the beginning of the epoch would
/// be represented as {sec: 1, nsec: 200000000}.
pub(super) struct Timespec {
    sec: i64,
    nsec: i32,
}

impl Timespec {
    /// Constructs a timespec representing the current time in UTC.
    pub(super) fn now() -> Timespec {
        let st =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
        Timespec { sec: st.as_secs() as i64, nsec: st.subsec_nanos() as i32 }
    }

    /// Converts this timespec into the system's local time.
    pub(super) fn local(self) -> Tm {
        let mut tm = Tm {
            tm_sec: 0,
            tm_min: 0,
            tm_hour: 0,
            tm_mday: 0,
            tm_mon: 0,
            tm_year: 0,
            tm_wday: 0,
            tm_yday: 0,
            tm_isdst: 0,
            tm_utcoff: 0,
            tm_nsec: 0,
        };
        time_to_local_tm(self.sec, &mut tm);
        tm.tm_nsec = self.nsec;
        tm
    }
}

/// Holds a calendar date and time broken down into its components (year, month,
/// day, and so on), also called a broken-down time value.
// FIXME: use c_int instead of i32?
#[cfg(feature = "clock")]
#[repr(C)]
pub(crate) struct Tm {
    /// Seconds after the minute - [0, 60]
    pub(crate) tm_sec: i32,

    /// Minutes after the hour - [0, 59]
    pub(crate) tm_min: i32,

    /// Hours after midnight - [0, 23]
    pub(crate) tm_hour: i32,

    /// Day of the month - [1, 31]
    pub(crate) tm_mday: i32,

    /// Months since January - [0, 11]
    pub(crate) tm_mon: i32,

    /// Years since 1900
    pub(crate) tm_year: i32,

    /// Days since Sunday - [0, 6]. 0 = Sunday, 1 = Monday, ..., 6 = Saturday.
    pub(crate) tm_wday: i32,

    /// Days since January 1 - [0, 365]
    pub(crate) tm_yday: i32,

    /// Daylight Saving Time flag.
    ///
    /// This value is positive if Daylight Saving Time is in effect, zero if
    /// Daylight Saving Time is not in effect, and negative if this information
    /// is not available.
    pub(crate) tm_isdst: i32,

    /// Identifies the time zone that was used to compute this broken-down time
    /// value, including any adjustment for Daylight Saving Time. This is the
    /// number of seconds east of UTC. For example, for U.S. Pacific Daylight
    /// Time, the value is `-7*60*60 = -25200`.
    pub(crate) tm_utcoff: i32,

    /// Nanoseconds after the second - [0, 10<sup>9</sup> - 1]
    pub(crate) tm_nsec: i32,
}

#[cfg(test)]
mod tests {
    use super::Local;
    use crate::offset::TimeZone;
    use crate::{Datelike, Duration, NaiveDate};

    use std::{path, process};

    #[cfg(unix)]
    fn verify_against_date_command(path: path::PathBuf) {
        let output = process::Command::new(path)
            .arg("-d")
            .arg("2021-03-05 22:05:01")
            .arg("+%Y-%m-%d %H:%M:%S %:z")
            .output()
            .unwrap();

        let date_command_str = String::from_utf8(output.stdout).unwrap();

        let local =
            Local.from_local_datetime(&NaiveDate::from_ymd(2021, 3, 5).and_hms(22, 5, 1)).unwrap();

        assert_eq!(format!("{}\n", local), date_command_str)
    }

    #[test]
    #[cfg(unix)]
    fn try_verify_against_date_command() {
        for date_path in ["/usr/bin/date", "/bin/date"] {
            if path::Path::new(date_path).exists() {
                verify_against_date_command(date_path.into())
            }
        }
        // date command not found, skipping
    }

    #[test]
    fn verify_correct_offsets() {
        let now = Local::now();
        let from_local = Local.from_local_datetime(&now.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&now.naive_utc());

        assert_eq!(now.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(now.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(now, from_local);
        assert_eq!(now, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_past() {
        let distant_past = Local::now() - Duration::days(365 * 10000);
        let from_local = Local.from_local_datetime(&distant_past.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&distant_past.naive_utc());
        assert_eq!(distant_past.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(distant_past.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(distant_past, from_local);
        assert_eq!(distant_past, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_future() {
        let distant_future = Local::now() + Duration::days(365 * 10000);
        let from_local = Local.from_local_datetime(&distant_future.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&distant_future.naive_utc());
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
        assert_eq!(Local.ymd(2999, 12, 28).day(), 28);
    }

    #[test]
    fn test_leap_second() {
        // issue #123
        let today = Local::today();

        let dt = today.and_hms_milli(1, 2, 59, 1000);
        let timestr = dt.time().to_string();
        // the OS API may or may not support the leap second,
        // but there are only two sensible options.
        assert!(timestr == "01:02:60" || timestr == "01:03:00", "unexpected timestr {:?}", timestr);

        let dt = today.and_hms_milli(1, 2, 3, 1234);
        let timestr = dt.time().to_string();
        assert!(
            timestr == "01:02:03.234" || timestr == "01:02:04.234",
            "unexpected timestr {:?}",
            timestr
        );
    }
}
