// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The UTC (Coordinated Universal Time) time zone.

use core::fmt;
#[cfg(all(
    feature = "clock",
    not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))
))]
use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use super::{FixedOffset, LocalResult, Offset, TimeZone};
use crate::naive::{NaiveDate, NaiveDateTime};
#[cfg(feature = "clock")]
#[allow(deprecated)]
use crate::{Date, DateTime};

/// The UTC time zone. This is the most efficient time zone when you don't need the local time.
/// It is also used as an offset (which is also a dummy type).
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on the UTC struct is the preferred way to construct `DateTime<Utc>`
/// instances.
///
/// # Example
///
/// ```
/// use chrono::{TimeZone, NaiveDateTime, Utc};
///
/// let dt = Utc.from_utc_datetime(&NaiveDateTime::from_timestamp_opt(61, 0).unwrap());
///
/// assert_eq!(Utc.timestamp_opt(61, 0).unwrap(), dt);
/// assert_eq!(Utc.with_ymd_and_hms(1970, 1, 1, 0, 1, 1).unwrap(), dt);
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Utc;

#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl Utc {
    /// Returns a `Date` which corresponds to the current date.
    #[deprecated(
        since = "0.4.23",
        note = "use `Utc::now()` instead, potentially with `.date_naive()`"
    )]
    #[allow(deprecated)]
    #[must_use]
    pub fn today() -> Date<Utc> {
        Utc::now().date()
    }

    /// Returns a `DateTime<Utc>` which corresponds to the current date and time in UTC.
    ///
    /// See also the similar [`Local::now()`] which returns `DateTime<Local>`, i.e. the local date
    /// and time including offset from UTC.
    ///
    /// [`Local::now()`]: crate::Local::now
    ///
    /// # Example
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// # use chrono::{FixedOffset, Utc};
    /// // Current time in UTC
    /// let now_utc = Utc::now();
    ///
    /// // Current date in UTC
    /// let today_utc = now_utc.date_naive();
    ///
    /// // Current time in some timezone (let's use +05:00)
    /// let offset = FixedOffset::east_opt(5 * 60 * 60).unwrap();
    /// let now_with_offset = Utc::now().with_timezone(&offset);
    /// ```
    #[cfg(not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))]
    #[must_use]
    pub fn now() -> DateTime<Utc> {
        let now =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
        let naive =
            NaiveDateTime::from_timestamp_opt(now.as_secs() as i64, now.subsec_nanos()).unwrap();
        Utc.from_utc_datetime(&naive)
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))]
    #[must_use]
    pub fn now() -> DateTime<Utc> {
        let now = js_sys::Date::new_0();
        DateTime::<Utc>::from(now)
    }
}

impl TimeZone for Utc {
    type Offset = Utc;

    fn from_offset(_state: &Utc) -> Utc {
        Utc
    }

    fn offset_from_local_date(&self, _local: &NaiveDate) -> LocalResult<Utc> {
        LocalResult::Single(Utc)
    }
    fn offset_from_local_datetime(&self, _local: &NaiveDateTime) -> LocalResult<Utc> {
        LocalResult::Single(Utc)
    }

    fn offset_from_utc_date(&self, _utc: &NaiveDate) -> Utc {
        Utc
    }
    fn offset_from_utc_datetime(&self, _utc: &NaiveDateTime) -> Utc {
        Utc
    }
}

impl Offset for Utc {
    fn fix(&self) -> FixedOffset {
        FixedOffset::east_opt(0).unwrap()
    }
}

impl fmt::Debug for Utc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Z")
    }
}

impl fmt::Display for Utc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "UTC")
    }
}
