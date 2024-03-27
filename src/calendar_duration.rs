use core::fmt;
use core::num::NonZeroU64;
use core::str;
use core::time::Duration;

use crate::format::{parse_iso8601_duration, ParseError, TOO_LONG};
use crate::{expect, try_opt};

/// Duration type capable of expressing a duration as a combination of multiple units.
///
/// A duration can be expressed as a combination of four components: *months*, *days*, *minutes*,
/// and *seconds and nanoseconds*. This type is compatible with the definition of an ISO 8601
/// duration.
///
/// # Components
///
/// The *months* and *days* components are called components with a "nominal" durations, and can
/// also be used to express years and weeks respectively.
///
/// The *minutes*, and *seconds and nanoseconds* components are called components with an "accurate"
/// duration. Hours can be expressed with the *minutes* component. The definition of a minute is not
/// exactly 60 seconds; it can also be 61 or 59 in the presence of leap seconds.
///
/// To keep operations with a `CalendarDate` sane a large value for the *seconds* component is
/// mutually exclusive with the presence of a *minutes* component. If the *minutes* component is set
/// the *seconds* component is limited to 60 seconds.
///
/// **Note**: The distinction between *minutes and seconds* components and only a *seconds*
/// component prepares the `CalendarDate` type for working with leap seconds accurately.
/// However they currently behave the same because full support for leap seconds is not yet
/// implemented in chrono.
///
/// | component           | limit                    |
/// |---------------------|--------------------------|
/// | months              | `u32::MAX`               |
/// | days                | `u32::MAX`               |
/// | minutes and seconds | `u64::MAX >> 8` and `60` |
/// | seconds             | `u64::MAX >> 2`          |
/// | nanoseconds         | `999_999_999`            |
///
/// # Examples
///
/// ```
/// # use chrono::CalendarDuration;
/// // Encoding 1½ year as a duration of a year and 6 months:
/// let _duration = CalendarDuration::new().with_years_and_months(1, 6).unwrap();
///
/// // Encoding 1½ year as a duration of 12 months and 183 days (366 / 2):
/// let _duration = CalendarDuration::new().with_months(12).with_days(183);
///
/// // Encoding 1½ year as a duration of 548 days (365 + 366 / 2):
/// let _duration = CalendarDuration::new().with_days(548);
///
/// // Encoding 1½ year as a duration in seconds:
/// let _duration = CalendarDuration::new().with_seconds(548 * 24 * 60 * 60).unwrap();
/// ```
///
/// # Formatting and parsing
///
/// The [`Display`](fmt::Display) implementation will format a `CalendarDuration` to the ISO 8601
/// duration format with designators.
///
/// The [`FromStr`](str::FromStr) implementation currently only supports the same duration with
/// designators format, and not yet the ISO 8601 alternate format that is similar to how dates and
/// times are encoded.
///
/// The designator format always starts with `P` (period), followed by number-designator pairs.
/// First are the pairs for the "nominal" components, then a `T` (time), and then the pairs for the
/// "accurate" components. Any number-designator pair may be missing when zero, as long as there is
/// at least one pair. The last pair may contain a decimal fraction instead of an integer.
///
/// Supported formats:
/// - `Pnn̲Ynn̲Mnn̲DTnn̲Hnn̲Mnn̲S`. Components: `Y` for years, `M` for months, `D` for days, `H` for
///   hours, `M` for minutes, and `S` for seconds.
/// - `Pnn̲W`. The only allowed component is `W` for weeks.
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// use std::str::FromStr;
/// use chrono::CalendarDuration;
///
/// let duration = CalendarDuration::new().with_months(105).with_days(5).with_hms(6, 5, 4).unwrap();
///
/// // Formatting and parsing
/// let formatted = duration.to_string();
/// assert_eq!(formatted, "P8Y9M5DT6H5M4S"); // months and minutes are decomposed
/// assert_eq!(CalendarDuration::from_str(&formatted)?, duration);
/// assert_eq!(formatted.parse(), Ok(duration));
///
/// // Seconds are not decomposed
/// assert_eq!(CalendarDuration::new().with_seconds(123_456).unwrap().to_string(), "PT123456S");
///
/// // Multiple ISO 8601 duration strings can parse to the same `CalendarDate` because we consider
/// // years a shorthand for 12 months, and consider hours a shorthand for 60 minutes.
/// assert_eq!("P105M5DT6H5M4S".parse(), Ok(duration));
/// assert_eq!("P8Y9M5DT6H5M4S".parse(), Ok(duration));
/// assert_eq!("P8Y9M5DT365M4S".parse(), Ok(duration));
///
/// // The weeks format can be parsed, but we consistently format a duration with days.
/// assert_eq!("P5W".parse(), Ok(CalendarDuration::new().with_weeks_and_days(5, 0).unwrap()));
/// assert_eq!("P5W".parse::<CalendarDuration>()?.to_string(), "P35D");
///
/// // Any number-designator pair can be used to encode a duration of zero. We format it as "P0D".
/// assert_eq!(CalendarDuration::new().to_string(), "P0D");
/// assert_eq!("PT0S".parse(), Ok(CalendarDuration::new())); // 0 seconds equals 0 days
///
/// # }
/// # Ok::<(), chrono::ParseError>(())
/// ```
///
/// ## Fractional values
///
/// ISO 8601 optionally allows fractional values, even in places where they are ill-defined. Chrono
/// only supports parsing a fractional value for components that can be encoded in the same base
/// component:
/// - Fractional years will be expressed in months.
/// - Fractional weeks will be expressed in days.
/// - Fractional hours, minutes or seconds will be expressed in minutes, seconds and nanoseconds.
///
/// The ISO 8601 format has no designator for subsecond components but expects them to be specified
/// as a fraction. We format nanoseconds as a fraction of a second without trailing zero's.
///
/// Both `,`  and `.` are supported as decimal separators when parsing. Although the comma is
/// preferred by ISO 8601 we use `.` when formatting.
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use chrono::CalendarDuration;
/// let duration = CalendarDuration::new().with_hms(0, 3, 5).unwrap().with_millis(330).unwrap();
/// assert_eq!(duration.to_string(), "PT3M5.33S");
/// assert_eq!("PT3M5,33S".parse(), Ok(duration));
///
/// assert_eq!("P12,5Y".parse(), Ok(CalendarDuration::new().with_years_and_months(12, 6).unwrap()));
/// assert_eq!("P1.43W".parse(), Ok(CalendarDuration::new().with_days(10))); // horrible :-)
/// assert_eq!("PT6,25H".parse(), Ok(CalendarDuration::new().with_hms(6, 15, 0).unwrap()));
/// # }
/// # Ok::<(), chrono::ParseError>(())
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CalendarDuration {
    // Components with a nominal duration
    months: u32,
    days: u32,
    // Components with an accurate duration
    mins_and_secs: MinutesAndSeconds,
    nanos: u32,
}

impl Default for CalendarDuration {
    fn default() -> Self {
        CalendarDuration::new()
    }
}

impl fmt::Debug for CalendarDuration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (mins, secs) = self.mins_and_secs();
        f.debug_struct("CalendarDuration")
            .field("months", &self.months)
            .field("days", &self.days)
            .field("minutes", &mins)
            .field("seconds", &secs)
            .field("nanos", &self.nanos)
            .finish()
    }
}

impl fmt::Display for CalendarDuration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("P")?;
        // Plenty of ways to encode an empty string. `P0D` is short and not too strange.
        if self.is_zero() {
            return f.write_str("0D");
        }

        // Nominal components
        let years = self.months / 12;
        let months = self.months % 12;
        if years > 0 {
            f.write_fmt(format_args!("{}Y", years))?;
        }
        if months > 0 {
            f.write_fmt(format_args!("{}M", months))?;
        }
        if self.days > 0 {
            f.write_fmt(format_args!("{}D", self.days))?;
        }

        // Accurate components
        let (mins, secs) = self.mins_and_secs();
        if mins == 0 && secs == 0 && self.nanos() == 0 {
            return Ok(());
        }
        f.write_str("T")?;
        let hours = mins / 60;
        let mins = mins % 60;
        if hours > 0 {
            f.write_fmt(format_args!("{}H", hours))?;
        }
        if mins > 0 {
            f.write_fmt(format_args!("{}M", mins))?;
        }

        if secs == 0 && self.nanos == 0 {
            return Ok(());
        }
        f.write_fmt(format_args!("{}", secs))?;
        if self.nanos > 0 {
            // Count the number of significant digits, while removing all trailing zero's.
            let mut figures = 9usize;
            let mut fraction_digits = self.nanos;
            loop {
                let div = fraction_digits / 10;
                let last_digit = fraction_digits % 10;
                if last_digit != 0 {
                    break;
                }
                fraction_digits = div;
                figures -= 1;
            }
            f.write_fmt(format_args!(".{:01$}", fraction_digits, figures))?;
        }
        f.write_str("S")?;
        Ok(())
    }
}

impl str::FromStr for CalendarDuration {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<CalendarDuration, ParseError> {
        let (s, duration) = parse_iso8601_duration(s)?;
        if !s.is_empty() {
            return Err(TOO_LONG);
        }
        Ok(duration)
    }
}

impl CalendarDuration {
    /// Create a new duration initialized to `0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::CalendarDuration;
    /// // Duration in calendar months and days.
    /// let _ = CalendarDuration::new().with_months(15).with_days(5);
    /// // Duration in calendar days, and 3 hours.
    /// let _ = CalendarDuration::new().with_days(5).with_hms(3, 0, 0).unwrap();
    /// // Duration that will precisely count the number of seconds, including leap seconds.
    /// let _ = CalendarDuration::new().with_seconds(23_456).unwrap().with_millis(789).unwrap();
    /// ```
    #[must_use]
    pub const fn new() -> Self {
        Self {
            months: 0,
            days: 0,
            mins_and_secs: expect(MinutesAndSeconds::from_seconds(0), "in range"),
            nanos: 0,
        }
    }

    /// Set the months component of this duration to `months`.
    #[must_use]
    pub const fn with_months(mut self, months: u32) -> Self {
        self.months = months;
        self
    }

    /// Set the months component of this duration to `years * 12 + months`.
    ///
    ///  # Errors
    ///
    /// Returns `None` if the value of the months component would be out of range.
    pub const fn with_years_and_months(mut self, years: u32, months: u32) -> Option<Self> {
        self.months = try_opt!(try_opt!(years.checked_mul(12)).checked_add(months));
        Some(self)
    }

    /// Set the days component of this duration to `days`.
    #[must_use]
    pub const fn with_days(mut self, days: u32) -> Self {
        self.days = days;
        self
    }

    /// Set the days component of this duration to `weeks * 7 + days`.
    ///
    ///  # Errors
    ///
    /// Returns `None` if the value of the days component would be out of range.
    pub const fn with_weeks_and_days(mut self, weeks: u32, days: u32) -> Option<Self> {
        self.days = try_opt!(try_opt!(weeks.checked_mul(7)).checked_add(days));
        Some(self)
    }

    /// Sets the accurate component of this duration to a value in minutes and seconds.
    ///
    /// The definition of a minute is not exactly 60 seconds; it can also be 61 or 59 in the
    /// presence of leap seconds.
    ///
    /// Durations made with this method are the closest thing to working like leap seconds don't
    /// exists.
    ///
    /// # Errors
    ///
    /// Returns `None`:
    /// - if `seconds` exceeds 60
    /// - if the value of the minutes component (`hours * 60 + minutes`) would be out of range.
    pub const fn with_hms(mut self, hours: u64, minutes: u64, seconds: u8) -> Option<Self> {
        let minutes = try_opt!(try_opt!(hours.checked_mul(60)).checked_add(minutes));
        self.mins_and_secs =
            try_opt!(MinutesAndSeconds::from_minutes_and_seconds(minutes, seconds as u64));
        Some(self)
    }

    /// Sets the accurate component of this duration to a value in seconds.
    ///
    /// This duration will count an exact number of seconds, which includes the counting of leap
    /// seconds.
    ///
    /// The minutes component will be set to zero.
    ///
    /// # Errors
    ///
    /// Returns `None` if the value of the seconds component would be out of range.
    #[must_use]
    pub const fn with_seconds(mut self, seconds: u64) -> Option<Self> {
        self.mins_and_secs = try_opt!(MinutesAndSeconds::from_seconds(seconds));
        Some(self)
    }

    /// Sets the nanoseconds component of this duration to `nanos`.
    ///
    /// # Errors
    ///
    /// Returns `None` if `nanos` exceeds 999_999_999.
    pub const fn with_nanos(mut self, nanos: u32) -> Option<Self> {
        if nanos >= 1_000_000_000 {
            return None;
        }
        self.nanos = nanos;
        Some(self)
    }

    /// Sets the nanoseconds component of this duration to `micros * 1000`.
    ///
    /// # Errors
    ///
    /// Returns `None` if `micros` exceeds 999_999.
    pub const fn with_micros(self, micros: u32) -> Option<Self> {
        if micros >= 1_000_000 {
            return None;
        }
        self.with_nanos(micros * 1000)
    }

    /// Sets the nanoseconds component of this duration to `millis * 1000`.
    ///
    /// # Errors
    ///
    /// Returns `None` if `millis` exceeds 999.
    pub const fn with_millis(self, millis: u32) -> Option<Self> {
        if millis >= 1000 {
            return None;
        }
        self.with_nanos(millis * 1_000_000)
    }

    /// Returns the `months` component of this calendar duration.
    pub const fn months(&self) -> u32 {
        self.months
    }

    /// Returns the `days` component of this calendar duration.
    pub const fn days(&self) -> u32 {
        self.days
    }

    /// Returns the `minutes` and `seconds` components of this calendar duration.
    pub const fn mins_and_secs(&self) -> (u64, u64) {
        self.mins_and_secs.mins_and_secs()
    }

    /// Returns the `nanos` component of this calendar duration.
    pub const fn nanos(&self) -> u32 {
        self.nanos
    }

    /// Returns `true` if this `CalendarDuration` spans no time.
    pub const fn is_zero(&self) -> bool {
        let (mins, secs) = self.mins_and_secs();
        self.months == 0 && self.days == 0 && mins == 0 && secs == 0 && self.nanos == 0
    }
}

impl From<Duration> for CalendarDuration {
    fn from(value: Duration) -> Self {
        Self::new()
            .with_seconds(value.as_secs())
            .expect("value of `Duration` out of range")
            .with_nanos(value.subsec_nanos())
            .unwrap()
    }
}

/// Type to encode either seconds, or minutes and up to 60 seconds.
///
/// We don't allow having both an `u64` with minutes and an `u64` with seconds.
/// Having two components in a `CalendarDuration` whose only subtle difference is how they behave
/// around leap seconds will make the type unintuitive.
///
/// # Encoding
///
/// - Seconds:                                     `seconds << 2 | 0b10`
/// - Minutes and up to 60 seconds: `minutes << 8 | seconds << 2 | 0b11`
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct MinutesAndSeconds(NonZeroU64);

impl MinutesAndSeconds {
    const fn from_seconds(secs: u64) -> Option<Self> {
        if secs >= (1 << 62) {
            return None;
        }
        Some(Self(expect(NonZeroU64::new(secs << 2 | 0b10), "can't fail, non-zero")))
    }

    const fn from_minutes_and_seconds(mins: u64, secs: u64) -> Option<Self> {
        if mins >= (1 << 56) || secs > 60 {
            return None;
        }
        // The `(mins > 0) as u64` causes a value without minutes to have the same encoding as
        // one created with `from_seconds`.
        let val = mins << 8 | secs << 2 | (mins > 0) as u64 | 0b10;
        Some(Self(expect(NonZeroU64::new(val), "can't fail, non-zero")))
    }

    /// Returns the `minutes` and `seconds` components.
    const fn mins_and_secs(&self) -> (u64, u64) {
        let value = self.0.get();
        match value & 0b01 == 0 {
            true => (0, value >> 2),
            false => (value >> 8, (value >> 2) & 0b11_1111),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::CalendarDuration;
    use std::time::Duration;

    #[test]
    fn test_basic_functionality() {
        #[track_caller]
        fn compare(d: CalendarDuration, months: u32, days: u32, mins: u64, secs: u64, nanos: u32) {
            assert_eq!(d.months(), months);
            assert_eq!(d.days(), days);
            assert_eq!((d.mins_and_secs()), (mins, secs));
            assert_eq!(d.nanos(), nanos);
        }

        let duration = CalendarDuration::new()
            .with_months(1)
            .with_days(2)
            .with_hms(3, 4, 5)
            .unwrap()
            .with_nanos(6)
            .unwrap();
        compare(duration, 1, 2, 3 * 60 + 4, 5, 6);

        compare(CalendarDuration::new().with_months(18), 18, 0, 0, 0, 0);
        compare(CalendarDuration::new().with_years_and_months(1, 6).unwrap(), 18, 0, 0, 0, 0);
        compare(CalendarDuration::new().with_days(15), 0, 15, 0, 0, 0);
        compare(CalendarDuration::new().with_weeks_and_days(2, 1).unwrap(), 0, 15, 0, 0, 0);
        compare(CalendarDuration::new().with_hms(3, 4, 5).unwrap(), 0, 0, 3 * 60 + 4, 5, 0);
        compare(CalendarDuration::new().with_seconds(123_456).unwrap(), 0, 0, 0, 123_456, 0);
        compare(CalendarDuration::new().with_nanos(123_456_789).unwrap(), 0, 0, 0, 0, 123_456_789);

        compare(CalendarDuration::new(), 0, 0, 0, 0, 0);
        assert!(CalendarDuration::new().is_zero());
        assert!(CalendarDuration::default().is_zero());
    }

    #[test]
    fn test_invalid_returns_none() {
        assert!(CalendarDuration::new().with_years_and_months(0, u32::MAX).is_some());
        assert!(CalendarDuration::new().with_years_and_months(u32::MAX / 12 + 1, 0).is_none());
        assert!(CalendarDuration::new().with_years_and_months(u32::MAX, 0).is_none());
        assert!(CalendarDuration::new().with_years_and_months(u32::MAX, 1).is_none());

        assert!(CalendarDuration::new().with_weeks_and_days(0, u32::MAX).is_some());
        assert!(CalendarDuration::new().with_weeks_and_days(u32::MAX / 7 + 1, 0).is_none());
        assert!(CalendarDuration::new().with_weeks_and_days(u32::MAX, 0).is_none());
        assert!(CalendarDuration::new().with_weeks_and_days(u32::MAX, 1).is_none());

        const MAX_MINUTES: u64 = u64::MAX >> 8;
        const MAX_HOURS: u64 = MAX_MINUTES / 60;
        assert!(CalendarDuration::new().with_hms(100, 100, 60).is_some());
        assert!(CalendarDuration::new().with_hms(0, 0, 61).is_none());
        assert!(CalendarDuration::new().with_hms(0, MAX_MINUTES, 0).is_some());
        assert!(CalendarDuration::new().with_hms(0, MAX_MINUTES + 1, 0).is_none());
        assert!(CalendarDuration::new().with_hms(MAX_HOURS, MAX_MINUTES % 60, 0).is_some());
        assert!(CalendarDuration::new().with_hms(MAX_HOURS, MAX_MINUTES % 60 + 1, 0).is_none());
        assert!(CalendarDuration::new().with_hms(MAX_HOURS + 1, 0, 0).is_none());
        assert!(CalendarDuration::new().with_hms(u64::MAX, 0, 0).is_none());
        assert!(CalendarDuration::new().with_hms(0, u64::MAX, 0).is_none());
        assert!(CalendarDuration::new().with_hms(0, 0, u8::MAX).is_none());

        const MAX_SECONDS: u64 = u64::MAX >> 2;
        assert!(CalendarDuration::new().with_seconds(100).is_some());
        assert!(CalendarDuration::new().with_seconds(MAX_SECONDS).is_some());
        assert!(CalendarDuration::new().with_seconds(MAX_SECONDS + 1).is_none());
        assert!(CalendarDuration::new().with_seconds(u64::MAX).is_none());

        assert!(CalendarDuration::new().with_nanos(1_000_000_000).is_none());
        assert!(CalendarDuration::new().with_nanos(u32::MAX).is_none());
        assert!(CalendarDuration::new().with_micros(1_000_000).is_none());
        assert!(CalendarDuration::new().with_micros(u32::MAX).is_none());
        assert!(CalendarDuration::new().with_millis(1_000_000).is_none());
        assert!(CalendarDuration::new().with_millis(u32::MAX).is_none());
    }

    #[test]
    fn test_seconds_compare_equal() {
        let new = CalendarDuration::new;
        assert_eq!(new().with_hms(0, 0, 1), new().with_seconds(1));
        assert_eq!(new().with_hms(0, 0, 60), new().with_seconds(60));
        assert_ne!(new().with_hms(0, 1, 0), new().with_seconds(60));
    }

    #[test]
    fn test_from_std_duration() {
        assert_eq!(
            CalendarDuration::new().with_seconds(7).unwrap().with_nanos(8).unwrap(),
            Duration::new(7, 8).into()
        );
    }

    #[test]
    #[should_panic]
    fn test_from_extreme_duration_panics() {
        let _ = CalendarDuration::from(Duration::new(1 << 62, 0));
    }

    #[test]
    fn test_display_format() {
        let new = CalendarDuration::new;

        assert_eq!(
            new().with_months(45).with_days(5).with_hms(6, 5, 43).unwrap().to_string(),
            "P3Y9M5DT6H5M43S"
        );
        assert_eq!(new().to_string(), "P0D");
        assert_eq!(new().with_years_and_months(2, 0).unwrap().to_string(), "P2Y");
        assert_eq!(new().with_months(3).to_string(), "P3M");
        assert_eq!(new().with_weeks_and_days(3, 4).unwrap().to_string(), "P25D");
        assert_eq!(new().with_days(25).to_string(), "P25D");
        assert_eq!(new().with_hms(2, 0, 0).unwrap().to_string(), "PT2H");
        assert_eq!(new().with_hms(0, 3, 0).unwrap().to_string(), "PT3M");
        assert_eq!(new().with_hms(0, 0, 15).unwrap().to_string(), "PT15S");
        assert_eq!(
            new().with_hms(2, 3, 45).unwrap().with_millis(678).unwrap().to_string(),
            "PT2H3M45.678S"
        );
        assert_eq!(new().with_seconds(123_456).unwrap().to_string(), "PT123456S");
        assert_eq!(new().with_micros(123).unwrap().to_string(), "PT0.000123S");
        assert_eq!(new().with_days(5).with_millis(123).unwrap().to_string(), "P5DT0.123S");
    }
}
