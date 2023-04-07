// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

use crate::datetime::DateTime;
use crate::naive::NaiveDateTime;
use crate::time_delta::TimeDelta;
use crate::Error;
use crate::TimeZone;
use crate::Timelike;
use core::cmp::Ordering;
use core::marker::Sized;
use core::ops::{Add, Sub};

/// Extension trait for subsecond rounding or truncation to a maximum number
/// of digits. Rounding can be used to decrease the error variance when
/// serializing/persisting to lower precision. Truncation is the default
/// behavior in Chrono display formatting.  Either can be used to guarantee
/// equality (e.g. for testing) when round-tripping through a lower precision
/// format.
pub trait SubsecRound {
    /// Return a copy rounded to the specified number of subsecond digits. With
    /// 9 or more digits, self is returned unmodified. Halfway values are
    /// rounded up (away from zero).
    ///
    /// # Example
    /// ``` rust
    /// # use chrono::{DateTime, SubsecRound, Timelike, TimeZone, Utc, NaiveDate};
    /// let dt = NaiveDate::from_ymd(2018, 1, 11)?.and_hms_milli(12, 0, 0, 154)?.and_local_timezone(Utc)?;
    /// assert_eq!(dt.round_subsecs(2).nanosecond(), 150_000_000);
    /// assert_eq!(dt.round_subsecs(1).nanosecond(), 200_000_000);
    /// # Ok::<(), chrono::Error>(())
    /// ```
    fn round_subsecs(self, digits: u16) -> Self;

    /// Return a copy truncated to the specified number of subsecond
    /// digits. With 9 or more digits, self is returned unmodified.
    ///
    /// # Example
    /// ``` rust
    /// # use chrono::{DateTime, SubsecRound, Timelike, TimeZone, Utc, NaiveDate};
    /// let dt = NaiveDate::from_ymd(2018, 1, 11)?.and_hms_milli(12, 0, 0, 154)?.and_local_timezone(Utc)?;
    /// assert_eq!(dt.trunc_subsecs(2).nanosecond(), 150_000_000);
    /// assert_eq!(dt.trunc_subsecs(1).nanosecond(), 100_000_000);
    /// # Ok::<(), chrono::Error>(())
    /// ```
    fn trunc_subsecs(self, digits: u16) -> Self;
}

impl<T> SubsecRound for T
where
    T: Timelike + Add<TimeDelta, Output = T> + Sub<TimeDelta, Output = T>,
{
    fn round_subsecs(self, digits: u16) -> T {
        let span = span_for_digits(digits);
        let delta_down = self.nanosecond() % span;
        if delta_down > 0 {
            let delta_up = span - delta_down;
            if delta_up <= delta_down {
                self + TimeDelta::nanoseconds(delta_up.into())
            } else {
                self - TimeDelta::nanoseconds(delta_down.into())
            }
        } else {
            self // unchanged
        }
    }

    fn trunc_subsecs(self, digits: u16) -> T {
        let span = span_for_digits(digits);
        let delta_down = self.nanosecond() % span;
        if delta_down > 0 {
            self - TimeDelta::nanoseconds(delta_down.into())
        } else {
            self // unchanged
        }
    }
}

// Return the maximum span in nanoseconds for the target number of digits.
const fn span_for_digits(digits: u16) -> u32 {
    // fast lookup form of: 10^(9-min(9,digits))
    match digits {
        0 => 1_000_000_000,
        1 => 100_000_000,
        2 => 10_000_000,
        3 => 1_000_000,
        4 => 100_000,
        5 => 10_000,
        6 => 1_000,
        7 => 100,
        8 => 10,
        _ => 1,
    }
}

/// Extension trait for rounding or truncating a DateTime by a TimeDelta.
///
/// # Limitations
/// Both rounding and truncating are done via [`TimeDelta::num_nanoseconds`] and
/// [`DateTime::timestamp_nanos`]. This means that they will fail if either the
/// `TimeDelta` or the `DateTime` are too big to represented as nanoseconds. They
/// will also fail if the `TimeDelta` is bigger than the timestamp.
pub trait DurationRound: Sized {
    /// Return a copy rounded by TimeDelta.
    ///
    /// # Example
    /// ``` rust
    /// # use chrono::{DateTime, DurationRound, TimeDelta, TimeZone, Utc, NaiveDate};
    /// let dt = NaiveDate::from_ymd(2018, 1, 11)?.and_hms_milli(12, 0, 0, 154)?.and_local_timezone(Utc)?;
    /// assert_eq!(
    ///     dt.duration_round(TimeDelta::milliseconds(10))?.to_string(),
    ///     "2018-01-11 12:00:00.150 UTC"
    /// );
    /// assert_eq!(
    ///     dt.duration_round(TimeDelta::days(1))?.to_string(),
    ///     "2018-01-12 00:00:00 UTC"
    /// );
    /// # Ok::<(), chrono::Error>(())
    /// ```
    fn duration_round(self, duration: TimeDelta) -> Result<Self, Error>;

    /// Return a copy truncated by TimeDelta.
    ///
    /// # Example
    /// ``` rust
    /// # use chrono::{DateTime, DurationRound, TimeDelta, TimeZone, Utc, NaiveDate};
    /// let dt = NaiveDate::from_ymd(2018, 1, 11)?.and_hms_milli(12, 0, 0, 154)?.and_local_timezone(Utc)?;
    /// assert_eq!(
    ///     dt.duration_trunc(TimeDelta::milliseconds(10))?.to_string(),
    ///     "2018-01-11 12:00:00.150 UTC"
    /// );
    /// assert_eq!(
    ///     dt.duration_trunc(TimeDelta::days(1))?.to_string(),
    ///     "2018-01-11 00:00:00 UTC"
    /// );
    /// # Ok::<(), chrono::Error>(())
    /// ```
    fn duration_trunc(self, duration: TimeDelta) -> Result<Self, Error>;
}

/// The maximum number of seconds a DateTime can be to be represented as nanoseconds
const MAX_SECONDS_TIMESTAMP_FOR_NANOS: i64 = 9_223_372_036;

impl<Tz: TimeZone> DurationRound for DateTime<Tz> {
    fn duration_round(self, duration: TimeDelta) -> Result<Self, Error> {
        duration_round(self.naive_local(), self, duration)
    }

    fn duration_trunc(self, duration: TimeDelta) -> Result<Self, Error> {
        duration_trunc(self.naive_local(), self, duration)
    }
}

impl DurationRound for NaiveDateTime {
    fn duration_round(self, duration: TimeDelta) -> Result<Self, Error> {
        duration_round(self, self, duration)
    }

    fn duration_trunc(self, duration: TimeDelta) -> Result<Self, Error> {
        duration_trunc(self, self, duration)
    }
}

fn duration_round<T>(naive: NaiveDateTime, original: T, duration: TimeDelta) -> Result<T, Error>
where
    T: Timelike + Add<TimeDelta, Output = T> + Sub<TimeDelta, Output = T>,
{
    if let Some(span) = duration.num_nanoseconds() {
        if naive.timestamp().abs() > MAX_SECONDS_TIMESTAMP_FOR_NANOS {
            return Err(Error::TimestampExceedsLimit);
        }
        let stamp = naive.timestamp_nanos();
        if span > stamp.abs() {
            return Err(Error::DurationExceedsTimestamp);
        }
        if span == 0 {
            return Ok(original);
        }
        let delta_down = stamp % span;
        if delta_down == 0 {
            Ok(original)
        } else {
            let (delta_up, delta_down) = if delta_down < 0 {
                (delta_down.abs(), span - delta_down.abs())
            } else {
                (span - delta_down, delta_down)
            };
            if delta_up <= delta_down {
                Ok(original + TimeDelta::nanoseconds(delta_up))
            } else {
                Ok(original - TimeDelta::nanoseconds(delta_down))
            }
        }
    } else {
        Err(Error::DurationExceedsLimit)
    }
}

fn duration_trunc<T>(naive: NaiveDateTime, original: T, duration: TimeDelta) -> Result<T, Error>
where
    T: Timelike + Add<TimeDelta, Output = T> + Sub<TimeDelta, Output = T>,
{
    if let Some(span) = duration.num_nanoseconds() {
        if naive.timestamp().abs() > MAX_SECONDS_TIMESTAMP_FOR_NANOS {
            return Err(Error::TimestampExceedsLimit);
        }
        let stamp = naive.timestamp_nanos();
        if span > stamp.abs() {
            return Err(Error::DurationExceedsTimestamp);
        }
        let delta_down = stamp % span;
        match delta_down.cmp(&0) {
            Ordering::Equal => Ok(original),
            Ordering::Greater => Ok(original - TimeDelta::nanoseconds(delta_down)),
            Ordering::Less => Ok(original - TimeDelta::nanoseconds(span - delta_down.abs())),
        }
    } else {
        Err(Error::DurationExceedsLimit)
    }
}

#[cfg(test)]
mod tests {
    use super::{DurationRound, SubsecRound, TimeDelta};
    use crate::offset::{FixedOffset, TimeZone, Utc};
    use crate::NaiveDate;
    use crate::Timelike;

    #[test]
    fn test_round_subsecs() -> Result<(), crate::Error> {
        let pst = FixedOffset::east(8 * 60 * 60)?;
        let dt = pst
            .from_local_datetime(
                &NaiveDate::from_ymd(2018, 1, 11)?.and_hms_nano(10, 5, 13, 84_660_684)?,
            )?
            .single()?;

        assert_eq!(dt.round_subsecs(10), dt);
        assert_eq!(dt.round_subsecs(9), dt);
        assert_eq!(dt.round_subsecs(8).nanosecond(), 84_660_680);
        assert_eq!(dt.round_subsecs(7).nanosecond(), 84_660_700);
        assert_eq!(dt.round_subsecs(6).nanosecond(), 84_661_000);
        assert_eq!(dt.round_subsecs(5).nanosecond(), 84_660_000);
        assert_eq!(dt.round_subsecs(4).nanosecond(), 84_700_000);
        assert_eq!(dt.round_subsecs(3).nanosecond(), 85_000_000);
        assert_eq!(dt.round_subsecs(2).nanosecond(), 80_000_000);
        assert_eq!(dt.round_subsecs(1).nanosecond(), 100_000_000);

        assert_eq!(dt.round_subsecs(0).nanosecond(), 0);
        assert_eq!(dt.round_subsecs(0).second(), 13);

        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2018, 1, 11)?.and_hms_nano(
                10,
                5,
                27,
                750_500_000,
            )?)?
            .single()?;
        assert_eq!(dt.round_subsecs(9), dt);
        assert_eq!(dt.round_subsecs(4), dt);
        assert_eq!(dt.round_subsecs(3).nanosecond(), 751_000_000);
        assert_eq!(dt.round_subsecs(2).nanosecond(), 750_000_000);
        assert_eq!(dt.round_subsecs(1).nanosecond(), 800_000_000);

        assert_eq!(dt.round_subsecs(0).nanosecond(), 0);
        assert_eq!(dt.round_subsecs(0).second(), 28);
        Ok(())
    }

    #[test]
    fn test_round_leap_nanos() -> Result<(), crate::Error> {
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2016, 12, 31)?.and_hms_nano(
                23,
                59,
                59,
                1_750_500_000,
            )?)?
            .single()?;
        assert_eq!(dt.round_subsecs(9), dt);
        assert_eq!(dt.round_subsecs(4), dt);
        assert_eq!(dt.round_subsecs(2).nanosecond(), 1_750_000_000);
        assert_eq!(dt.round_subsecs(1).nanosecond(), 1_800_000_000);
        assert_eq!(dt.round_subsecs(1).second(), 59);

        assert_eq!(dt.round_subsecs(0).nanosecond(), 0);
        assert_eq!(dt.round_subsecs(0).second(), 0);
        Ok(())
    }

    #[test]
    fn test_trunc_subsecs() -> Result<(), crate::Error> {
        let pst = FixedOffset::east(8 * 60 * 60)?;
        let dt = pst
            .from_local_datetime(
                &NaiveDate::from_ymd(2018, 1, 11)?.and_hms_nano(10, 5, 13, 84_660_684)?,
            )?
            .single()?;

        assert_eq!(dt.trunc_subsecs(10), dt);
        assert_eq!(dt.trunc_subsecs(9), dt);
        assert_eq!(dt.trunc_subsecs(8).nanosecond(), 84_660_680);
        assert_eq!(dt.trunc_subsecs(7).nanosecond(), 84_660_600);
        assert_eq!(dt.trunc_subsecs(6).nanosecond(), 84_660_000);
        assert_eq!(dt.trunc_subsecs(5).nanosecond(), 84_660_000);
        assert_eq!(dt.trunc_subsecs(4).nanosecond(), 84_600_000);
        assert_eq!(dt.trunc_subsecs(3).nanosecond(), 84_000_000);
        assert_eq!(dt.trunc_subsecs(2).nanosecond(), 80_000_000);
        assert_eq!(dt.trunc_subsecs(1).nanosecond(), 0);

        assert_eq!(dt.trunc_subsecs(0).nanosecond(), 0);
        assert_eq!(dt.trunc_subsecs(0).second(), 13);

        let dt = pst
            .from_local_datetime(&NaiveDate::from_ymd(2018, 1, 11)?.and_hms_nano(
                10,
                5,
                27,
                750_500_000,
            )?)?
            .single()?;
        assert_eq!(dt.trunc_subsecs(9), dt);
        assert_eq!(dt.trunc_subsecs(4), dt);
        assert_eq!(dt.trunc_subsecs(3).nanosecond(), 750_000_000);
        assert_eq!(dt.trunc_subsecs(2).nanosecond(), 750_000_000);
        assert_eq!(dt.trunc_subsecs(1).nanosecond(), 700_000_000);

        assert_eq!(dt.trunc_subsecs(0).nanosecond(), 0);
        assert_eq!(dt.trunc_subsecs(0).second(), 27);
        Ok(())
    }

    #[test]
    fn test_trunc_leap_nanos() -> Result<(), crate::Error> {
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2016, 12, 31)?.and_hms_nano(
                23,
                59,
                59,
                1_750_500_000,
            )?)?
            .single()?;
        assert_eq!(dt.trunc_subsecs(9), dt);
        assert_eq!(dt.trunc_subsecs(4), dt);
        assert_eq!(dt.trunc_subsecs(2).nanosecond(), 1_750_000_000);
        assert_eq!(dt.trunc_subsecs(1).nanosecond(), 1_700_000_000);
        assert_eq!(dt.trunc_subsecs(1).second(), 59);

        assert_eq!(dt.trunc_subsecs(0).nanosecond(), 1_000_000_000);
        assert_eq!(dt.trunc_subsecs(0).second(), 59);
        Ok(())
    }

    #[test]
    fn test_duration_round() -> Result<(), crate::Error> {
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2016, 12, 31)?.and_hms_nano(
                23,
                59,
                59,
                175_500_000,
            )?)?
            .single()?;

        assert_eq!(
            dt.duration_round(TimeDelta::zero())?.to_string(),
            "2016-12-31 23:59:59.175500 UTC"
        );

        assert_eq!(
            dt.duration_round(TimeDelta::milliseconds(10))?.to_string(),
            "2016-12-31 23:59:59.180 UTC"
        );

        // round up
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2012, 12, 12)?.and_hms_milli(18, 22, 30, 0)?)?
            .single()?;
        assert_eq!(
            dt.duration_round(TimeDelta::minutes(5))?.to_string(),
            "2012-12-12 18:25:00 UTC"
        );
        // round down
        let dt = Utc
            .from_local_datetime(
                &NaiveDate::from_ymd(2012, 12, 12)?.and_hms_milli(18, 22, 29, 999)?,
            )?
            .single()?;
        assert_eq!(
            dt.duration_round(TimeDelta::minutes(5))?.to_string(),
            "2012-12-12 18:20:00 UTC"
        );

        assert_eq!(
            dt.duration_round(TimeDelta::minutes(10))?.to_string(),
            "2012-12-12 18:20:00 UTC"
        );
        assert_eq!(
            dt.duration_round(TimeDelta::minutes(30))?.to_string(),
            "2012-12-12 18:30:00 UTC"
        );
        assert_eq!(dt.duration_round(TimeDelta::hours(1))?.to_string(), "2012-12-12 18:00:00 UTC");
        assert_eq!(dt.duration_round(TimeDelta::days(1))?.to_string(), "2012-12-13 00:00:00 UTC");

        // timezone east
        let dt = FixedOffset::east(3600)?.with_ymd_and_hms(2020, 10, 27, 15, 0, 0)?.single()?;
        assert_eq!(
            dt.duration_round(TimeDelta::days(1))?.to_string(),
            "2020-10-28 00:00:00 +01:00"
        );
        assert_eq!(
            dt.duration_round(TimeDelta::weeks(1))?.to_string(),
            "2020-10-29 00:00:00 +01:00"
        );

        // timezone west
        let dt = FixedOffset::west(3600)?.with_ymd_and_hms(2020, 10, 27, 15, 0, 0)?.single()?;
        assert_eq!(
            dt.duration_round(TimeDelta::days(1))?.to_string(),
            "2020-10-28 00:00:00 -01:00"
        );
        assert_eq!(
            dt.duration_round(TimeDelta::weeks(1))?.to_string(),
            "2020-10-29 00:00:00 -01:00"
        );
        Ok(())
    }

    #[test]
    fn test_duration_round_naive() -> Result<(), crate::Error> {
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2016, 12, 31)?.and_hms_nano(
                23,
                59,
                59,
                175_500_000,
            )?)?
            .single()?
            .naive_utc();

        assert_eq!(dt.duration_round(TimeDelta::zero())?.to_string(), "2016-12-31 23:59:59.175500");

        assert_eq!(
            dt.duration_round(TimeDelta::milliseconds(10))?.to_string(),
            "2016-12-31 23:59:59.180"
        );

        // round up
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2012, 12, 12)?.and_hms_milli(18, 22, 30, 0)?)?
            .single()?
            .naive_utc();
        assert_eq!(dt.duration_round(TimeDelta::minutes(5))?.to_string(), "2012-12-12 18:25:00");
        // round down
        let dt = Utc
            .from_local_datetime(
                &NaiveDate::from_ymd(2012, 12, 12)?.and_hms_milli(18, 22, 29, 999)?,
            )?
            .single()?
            .naive_utc();
        assert_eq!(dt.duration_round(TimeDelta::minutes(5))?.to_string(), "2012-12-12 18:20:00");

        assert_eq!(dt.duration_round(TimeDelta::minutes(10))?.to_string(), "2012-12-12 18:20:00");
        assert_eq!(dt.duration_round(TimeDelta::minutes(30))?.to_string(), "2012-12-12 18:30:00");
        assert_eq!(dt.duration_round(TimeDelta::hours(1))?.to_string(), "2012-12-12 18:00:00");
        assert_eq!(dt.duration_round(TimeDelta::days(1))?.to_string(), "2012-12-13 00:00:00");
        Ok(())
    }

    #[test]
    fn test_duration_round_pre_epoch() -> Result<(), crate::Error> {
        let dt = Utc.with_ymd_and_hms(1969, 12, 12, 12, 12, 12)?.single()?;
        assert_eq!(
            dt.duration_round(TimeDelta::minutes(10))?.to_string(),
            "1969-12-12 12:10:00 UTC"
        );
        Ok(())
    }

    #[test]
    fn test_duration_trunc() -> Result<(), crate::Error> {
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2016, 12, 31)?.and_hms_nano(
                23,
                59,
                59,
                175_500_000,
            )?)?
            .single()?;

        assert_eq!(
            dt.duration_trunc(TimeDelta::milliseconds(10))?.to_string(),
            "2016-12-31 23:59:59.170 UTC"
        );

        // would round up
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2012, 12, 12)?.and_hms_milli(18, 22, 30, 0)?)?
            .single()?;
        assert_eq!(
            dt.duration_trunc(TimeDelta::minutes(5))?.to_string(),
            "2012-12-12 18:20:00 UTC"
        );
        // would round down
        let dt = Utc
            .from_local_datetime(
                &NaiveDate::from_ymd(2012, 12, 12)?.and_hms_milli(18, 22, 29, 999)?,
            )?
            .single()?;
        assert_eq!(
            dt.duration_trunc(TimeDelta::minutes(5))?.to_string(),
            "2012-12-12 18:20:00 UTC"
        );
        assert_eq!(
            dt.duration_trunc(TimeDelta::minutes(10))?.to_string(),
            "2012-12-12 18:20:00 UTC"
        );
        assert_eq!(
            dt.duration_trunc(TimeDelta::minutes(30))?.to_string(),
            "2012-12-12 18:00:00 UTC"
        );
        assert_eq!(dt.duration_trunc(TimeDelta::hours(1))?.to_string(), "2012-12-12 18:00:00 UTC");
        assert_eq!(dt.duration_trunc(TimeDelta::days(1))?.to_string(), "2012-12-12 00:00:00 UTC");

        // timezone east
        let dt = FixedOffset::east(3600)?.with_ymd_and_hms(2020, 10, 27, 15, 0, 0)?.single()?;
        assert_eq!(
            dt.duration_trunc(TimeDelta::days(1))?.to_string(),
            "2020-10-27 00:00:00 +01:00"
        );
        assert_eq!(
            dt.duration_trunc(TimeDelta::weeks(1))?.to_string(),
            "2020-10-22 00:00:00 +01:00"
        );

        // timezone west
        let dt = FixedOffset::west(3600)?.with_ymd_and_hms(2020, 10, 27, 15, 0, 0)?.single()?;
        assert_eq!(
            dt.duration_trunc(TimeDelta::days(1))?.to_string(),
            "2020-10-27 00:00:00 -01:00"
        );
        assert_eq!(
            dt.duration_trunc(TimeDelta::weeks(1))?.to_string(),
            "2020-10-22 00:00:00 -01:00"
        );
        Ok(())
    }

    #[test]
    fn test_duration_round_error() -> Result<(), crate::Error> {
        use crate::{DurationRound, Error, NaiveDate, TimeDelta, TimeZone, Utc};

        let dt = Utc.with_ymd_and_hms(1970, 12, 12, 0, 0, 0)?.single()?;
        assert_eq!(dt.duration_round(TimeDelta::days(365)), Err(Error::DurationExceedsTimestamp),);

        let dt = NaiveDate::from_ymd(2260, 12, 31)?
            .and_hms_nano(23, 59, 59, 1_75_500_000)?
            .and_local_timezone(Utc)?;
        assert_eq!(dt.duration_round(TimeDelta::days(300 * 365)), Err(Error::DurationExceedsLimit));

        let dt = Utc.with_ymd_and_hms(2300, 12, 12, 0, 0, 0)?.single()?;
        assert_eq!(dt.duration_round(TimeDelta::days(1)), Err(Error::TimestampExceedsLimit),);

        Ok(())
    }

    #[test]
    fn test_duration_trunc_naive() -> Result<(), crate::Error> {
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2016, 12, 31)?.and_hms_nano(
                23,
                59,
                59,
                175_500_000,
            )?)?
            .single()?
            .naive_utc();

        assert_eq!(
            dt.duration_trunc(TimeDelta::milliseconds(10))?.to_string(),
            "2016-12-31 23:59:59.170"
        );

        // would round up
        let dt = Utc
            .from_local_datetime(&NaiveDate::from_ymd(2012, 12, 12)?.and_hms_milli(18, 22, 30, 0)?)?
            .single()?
            .naive_utc();
        assert_eq!(dt.duration_trunc(TimeDelta::minutes(5))?.to_string(), "2012-12-12 18:20:00");
        // would round down
        let dt = Utc
            .from_local_datetime(
                &NaiveDate::from_ymd(2012, 12, 12)?.and_hms_milli(18, 22, 29, 999)?,
            )?
            .single()?
            .naive_utc();
        assert_eq!(dt.duration_trunc(TimeDelta::minutes(5))?.to_string(), "2012-12-12 18:20:00");
        assert_eq!(dt.duration_trunc(TimeDelta::minutes(10))?.to_string(), "2012-12-12 18:20:00");
        assert_eq!(dt.duration_trunc(TimeDelta::minutes(30))?.to_string(), "2012-12-12 18:00:00");
        assert_eq!(dt.duration_trunc(TimeDelta::hours(1))?.to_string(), "2012-12-12 18:00:00");
        assert_eq!(dt.duration_trunc(TimeDelta::days(1))?.to_string(), "2012-12-12 00:00:00");
        Ok(())
    }

    #[test]
    fn test_duration_trunc_pre_epoch() -> Result<(), crate::Error> {
        let dt = Utc.with_ymd_and_hms(1969, 12, 12, 12, 12, 12)?.single()?;
        assert_eq!(
            dt.duration_trunc(TimeDelta::minutes(10))?.to_string(),
            "1969-12-12 12:10:00 UTC"
        );
        Ok(())
    }
}
