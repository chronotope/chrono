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

use super::{FixedOffset, FixedTimeZone, Offset, TimeZone};
use crate::naive::{NaiveDate, NaiveDateTime};
#[cfg(feature = "clock")]
#[allow(deprecated)]
use crate::{Date, DateTime};
use crate::{Error, LocalResult};

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
/// use chrono::{DateTime, TimeZone, NaiveDateTime, Utc};
///
/// let dt = DateTime::<Utc>::from_utc(NaiveDateTime::from_timestamp(61, 0)?, Utc);
///
/// assert_eq!(Utc.timestamp(61, 0)?, dt);
/// assert_eq!(Utc.ymd(1970, 1, 1)?.and_hms(0, 1, 1)?, dt);
/// # Ok::<_, chrono::Error>(())
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Utc;

#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl Utc {
    /// Returns a `Date` which corresponds to the current date.
    #[allow(deprecated)]
    pub fn today() -> Result<Date<Utc>, Error> {
        Ok(Utc::now()?.date())
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))]
    pub fn now() -> Result<DateTime<Utc>, Error> {
        let now =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
        let naive = NaiveDateTime::from_timestamp(now.as_secs() as i64, now.subsec_nanos())?;
        Ok(DateTime::from_utc(naive, Utc))
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))]
    pub fn now() -> Result<DateTime<Utc>, Error> {
        use std::convert::TryFrom;

        let now = js_sys::Date::new_0();
        DateTime::<Utc>::try_from(now)
    }
}

impl TimeZone for Utc {
    type Offset = Self;

    fn from_offset(_: &Self) -> Self {
        Self
    }

    fn offset_from_local_date(&self, _: &NaiveDate) -> Result<LocalResult<Self>, Error> {
        Ok(LocalResult::Single(Self))
    }

    fn offset_from_local_datetime(&self, _: &NaiveDateTime) -> Result<LocalResult<Self>, Error> {
        Ok(LocalResult::Single(Self))
    }

    fn offset_from_utc_date(&self, _: &NaiveDate) -> Result<Self, Error> {
        Ok(Self)
    }

    fn offset_from_utc_datetime(&self, _: &NaiveDateTime) -> Result<Self, Error> {
        Ok(Self)
    }
}

impl FixedTimeZone for Utc {
    fn offset_from_utc_date_fixed(&self, _: &NaiveDate) -> Self::Offset {
        Self
    }

    fn offset_from_utc_datetime_fixed(&self, _: &NaiveDateTime) -> Self::Offset {
        Self
    }
}

impl Offset for Utc {
    fn fix(&self) -> FixedOffset {
        FixedOffset::UTC
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
