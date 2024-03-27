use super::scan;
use super::{ParseResult, INVALID, OUT_OF_RANGE};
use crate::CalendarDuration;

/// Parser for the ISO 8601 duration format with designators.
///
/// Supported formats:
/// - `Pnn̲Ynn̲Mnn̲DTnn̲Hnn̲Mnn̲S`
/// - `Pnn̲W`
///
/// Any number-designator pair may be missing when zero, as long as there is at least one pair.
/// The last pair may contain a decimal fraction instead of an integer.
///
/// - Fractional years will be expressed in months.
/// - Fractional weeks will be expressed in days.
/// - Fractional hours, minutes or seconds will be expressed in minutes, seconds and nanoseconds.
pub(crate) fn parse_iso8601_duration(mut s: &str) -> ParseResult<(&str, CalendarDuration)> {
    macro_rules! consume {
        ($e:expr) => {{
            $e.map(|(s_, v)| {
                s = s_;
                v
            })
        }};
    }

    s = scan::char(s, b'P')?;
    let mut duration = CalendarDuration::new();

    let mut next = consume!(Decimal::parse(s)).ok();
    if let Some(val) = next {
        if let Some(s_) = s.strip_prefix('W') {
            s = s_;
            let days = u32::try_from(val.mul(7)?).map_err(|_| OUT_OF_RANGE)?;
            return Ok((s, duration.with_days(days))); // Nothing is allowed after a week value
        }
        if let Some(s_) = s.strip_prefix('Y') {
            s = s_;
            let months = u32::try_from(val.mul(12)?).map_err(|_| OUT_OF_RANGE)?;
            duration = duration.with_months(months);
            if val.fraction.is_some() {
                return Ok((s, duration)); // Nothing is allowed after a fractional value
            }
            next = consume!(Decimal::parse(s)).ok();
        }
    }

    if let (Some(val), Some(s_)) = (next, s.strip_prefix('M')) {
        s = s_;
        let months = u32::try_from(val.integer()?)
            .ok()
            .and_then(|m| m.checked_add(duration.months())) // Combine with months set by `Y`.
            .ok_or(OUT_OF_RANGE)?;
        duration = duration.with_months(months);
        next = consume!(Decimal::parse(s)).ok();
    }

    if let (Some(val), Some(s_)) = (next, s.strip_prefix('D')) {
        s = s_;
        duration = duration.with_days(u32::try_from(val.integer()?).map_err(|_| OUT_OF_RANGE)?);
        next = None;
    }

    if next.is_some() {
        // We have a number but no allowed designator.
        return Err(INVALID);
    }

    if s.starts_with('T') {
        duration = consume!(parse_iso8601_duration_time(s, duration))?
    }
    Ok((s, duration))
}

/// Parser for the time part of the ISO 8601 duration format with designators.
pub(crate) fn parse_iso8601_duration_time(
    mut s: &str,
    duration: CalendarDuration,
) -> ParseResult<(&str, CalendarDuration)> {
    macro_rules! consume_or_return {
        ($e:expr, $return:expr) => {{
            match $e {
                Ok((s_, next)) => {
                    s = s_;
                    next
                }
                Err(_) => return $return,
            }
        }};
    }

    fn set_hms_nano(
        duration: CalendarDuration,
        hours: u64,
        minutes: u64,
        seconds: u64,
        nanoseconds: u32,
    ) -> ParseResult<CalendarDuration> {
        let duration = match (hours, minutes, seconds) {
            (0, 0, s) => duration.with_seconds(s).ok_or(OUT_OF_RANGE)?,
            (h, m, s @ 0..=60) => duration.with_hms(h, m, s as u8).ok_or(OUT_OF_RANGE)?,
            _ => return Err(OUT_OF_RANGE),
        };
        Ok(duration.with_nanos(nanoseconds).unwrap())
    }

    s = scan::char(s, b'T')?;
    let mut hours = 0;
    let mut minutes = 0;
    let mut incomplete = true; // at least one component is required

    let (s_, mut next) = Decimal::parse(s)?;
    s = s_;
    if let Some(s_) = s.strip_prefix('H') {
        s = s_;
        incomplete = false;
        match next.integer() {
            Ok(h) => hours = h,
            _ => {
                let (secs, nanos) = next.mul_with_nanos(3600)?;
                return Ok((s, set_hms_nano(duration, 0, secs / 60, secs % 60, nanos)?));
            }
        }
        next = consume_or_return!(
            Decimal::parse(s),
            Ok((s, set_hms_nano(duration, hours, minutes, 0, 0)?))
        );
    }

    if let Some(s_) = s.strip_prefix('M') {
        s = s_;
        incomplete = false;
        match next.integer() {
            Ok(m) => minutes = m,
            _ => {
                let (secs, nanos) = next.mul_with_nanos(60)?;
                return Ok((s, set_hms_nano(duration, hours, secs / 60, secs % 60, nanos)?));
            }
        }
        next = consume_or_return!(
            Decimal::parse(s),
            Ok((s, set_hms_nano(duration, hours, minutes, 0, 0)?))
        );
    }

    if let Some(s_) = s.strip_prefix('S') {
        s = s_;
        let (secs, nanos) = next.mul_with_nanos(1)?;
        return Ok((s, set_hms_nano(duration, hours, minutes, secs, nanos)?));
    }

    if incomplete {
        return Err(INVALID);
    }
    Ok((s, set_hms_nano(duration, hours, minutes, 0, 0)?))
}

/// Helper type for parsing decimals (as in an ISO 8601 duration).
#[derive(Copy, Clone)]
struct Decimal {
    base: u64,
    fraction: Option<Fraction>,
}

impl Decimal {
    fn parse(s: &str) -> ParseResult<(&str, Self)> {
        let (s, num) = scan::number(s, 1, usize::MAX)?;
        let (s, frac) = match Fraction::parse(s) {
            Ok((s, frac)) => (s, Some(frac)),
            Err(_) => (s, None),
        };
        let result = Decimal { base: num as u64, fraction: frac };
        Ok((s, result))
    }

    /// Multiplying this `Decimal` with `unit`.
    ///
    /// Returns `None` on out of range.
    fn mul(&self, unit: u64) -> ParseResult<u64> {
        let frac = self.fraction.unwrap_or(Fraction(0)).mul(unit);
        self.base.checked_mul(unit).and_then(|n| n.checked_add(frac)).ok_or(OUT_OF_RANGE)
    }

    /// Returns the result of multiplying this `Decimal` with `unit`.
    ///
    /// Returns two integers to represent the whole number and the fraction as nanos.
    fn mul_with_nanos(&self, unit: u64) -> ParseResult<(u64, u32)> {
        let (whole_from_rounding, fraction_as_nanos) =
            self.fraction.unwrap_or(Fraction(0)).mul_with_nanos(unit);
        let whole = (self.base)
            .checked_mul(unit)
            .and_then(|n| n.checked_add(whole_from_rounding))
            .ok_or(OUT_OF_RANGE)?;
        Ok((whole, fraction_as_nanos as u32))
    }

    /// Returns the value of this `Decimal` if it is an integer, otherwise `None`.
    fn integer(&self) -> ParseResult<u64> {
        match self.fraction {
            None => Ok(self.base),
            _ => Err(INVALID),
        }
    }
}

/// Helper type for parsing fractional numbers.
///
/// The fraction is stored as an integer in the range 0..=10^15.
/// With this limit `10^15 * 3600` fits in an `u64` without overflow.
///
// We don't use `f64` to support targets that may not have floating point support.
#[derive(Copy, Clone)]
struct Fraction(u64);

impl Fraction {
    /// Supported formats are `,fraction` and `.fraction`.
    /// `fraction` can have an unlimited length. We only keep the first 15 digits, and look at the
    /// 16th digit for correct rounding.
    fn parse(mut s: &str) -> ParseResult<(&str, Self)> {
        s = match s.as_bytes().first() {
            Some(&b',' | &b'.') => &s[1..],
            _ => return Err(INVALID),
        };
        let digits_in_fraction = s.as_bytes().iter().take_while(|c| c.is_ascii_digit()).count();
        let mut fraction = scan::number(s, 1, 15).map(|(_, f)| f)? as u64;
        if digits_in_fraction <= 15 {
            fraction *= POW10[15 - digits_in_fraction];
        } else if s.as_bytes()[15] >= b'5' {
            fraction += 1;
        }
        s = &s[digits_in_fraction..];
        Ok((s, Fraction(fraction)))
    }

    /// Returns the result of multiplying this `Fraction` with `unit`.
    ///
    /// Rounds to the nearest integer.
    fn mul(&self, unit: u64) -> u64 {
        assert!(unit <= 3600); // assumption to prevent overflow later.
        (self.0 * unit + POW10[15] / 2) / POW10[15]
    }

    /// Returns the result of multiplying this `Fraction` with `unit`.
    ///
    /// Returns two integers to represent the whole number and the fraction as nanos.
    fn mul_with_nanos(&self, unit: u64) -> (u64, u64) {
        assert!(unit <= 3600); // assumption to prevent overflow later.
        let div = POW10[15 - 9];
        let huge = self.0 * unit + div / 2;
        let whole = huge / POW10[15];
        let fraction_as_nanos = (huge % POW10[15]) / div;
        (whole, fraction_as_nanos)
    }
}

const POW10: [u64; 16] = [
    1, // unused, for easy indexing
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
    10_000_000_000,
    100_000_000_000,
    1_000_000_000_000,
    10_000_000_000_000,
    100_000_000_000_000,
    1_000_000_000_000_000,
];

#[cfg(test)]
mod tests {
    use super::{parse_iso8601_duration, parse_iso8601_duration_time, Fraction};
    use crate::format::{INVALID, OUT_OF_RANGE, TOO_SHORT};
    use crate::CalendarDuration;

    #[test]
    fn test_parse_fraction() {
        let (_, fraction) = Fraction::parse(",123").unwrap();
        assert_eq!(fraction.0, 123_000_000_000_000);
        let (_, fraction) = Fraction::parse(",123456789012345").unwrap();
        assert_eq!(fraction.0, 123_456_789_012_345);
        let (_, fraction) = Fraction::parse(",1234567890123454").unwrap();
        assert_eq!(fraction.0, 123_456_789_012_345);
        let (_, fraction) = Fraction::parse(",1234567890123455").unwrap();
        assert_eq!(fraction.0, 123_456_789_012_346);

        let (_, fraction) = Fraction::parse(",5").unwrap();
        assert_eq!(fraction.mul_with_nanos(1), (0, 500_000_000));
    }

    #[test]
    fn test_parse_duration_time() {
        let parse = parse_iso8601_duration_time;
        let d = CalendarDuration::new();

        assert_eq!(parse("T12H", d), Ok(("", d.with_hms(12, 0, 0).unwrap())));
        assert_eq!(parse("T12.25H", d), Ok(("", d.with_hms(12, 15, 0).unwrap())));
        assert_eq!(parse("T12,25H", d), Ok(("", d.with_hms(12, 15, 0).unwrap())));
        assert_eq!(parse("T34M", d), Ok(("", d.with_hms(0, 34, 0).unwrap())));
        assert_eq!(parse("T34.25M", d), Ok(("", d.with_hms(0, 34, 15).unwrap())));
        assert_eq!(parse("T56S", d), Ok(("", d.with_seconds(56).unwrap())));
        assert_eq!(parse("T0.789S", d), Ok(("", d.with_millis(789).unwrap())));
        assert_eq!(parse("T0,789S", d), Ok(("", d.with_millis(789).unwrap())));
        assert_eq!(parse("T12H34M", d), Ok(("", d.with_hms(12, 34, 0).unwrap())));
        assert_eq!(parse("T12H34M60S", d), Ok(("", d.with_hms(12, 34, 60).unwrap())));
        assert_eq!(
            parse("T12H34M56.789S", d),
            Ok(("", d.with_hms(12, 34, 56).unwrap().with_millis(789).unwrap()))
        );
        assert_eq!(parse("T12H56S", d), Ok(("", d.with_hms(12, 0, 56).unwrap())));
        assert_eq!(parse("T34M56S", d), Ok(("", d.with_hms(0, 34, 56).unwrap())));

        // Data after a fraction is not considered part of the value
        assert_eq!(parse("T12.5H16M", d), Ok(("16M", d.with_hms(12, 30, 0).unwrap())));
        assert_eq!(parse("T12H16.5M30S", d), Ok(("30S", d.with_hms(12, 16, 30).unwrap())));

        // Zero values
        assert_eq!(parse("T0H", d), Ok(("", d)));
        assert_eq!(parse("T0M", d), Ok(("", d)));
        assert_eq!(parse("T0S", d), Ok(("", d)));
        assert_eq!(parse("T0,0S", d), Ok(("", d)));

        // Empty or invalid values
        assert_eq!(parse("T", d), Err(TOO_SHORT));
        assert_eq!(parse("TH", d), Err(INVALID));
        assert_eq!(parse("TM", d), Err(INVALID));
        assert_eq!(parse("TS", d), Err(INVALID));
        assert_eq!(parse("T.5S", d), Err(INVALID));
        assert_eq!(parse("T,5S", d), Err(INVALID));

        // Date components
        assert_eq!(parse("T5W", d), Err(INVALID));
        assert_eq!(parse("T5Y", d), Err(INVALID));
        assert_eq!(parse("T5D", d), Err(INVALID));

        // Max values
        const MAX_MINUTES: u64 = u64::MAX >> 8; // 1200959900632132
        const MAX_HOURS: u64 = MAX_MINUTES / 60; // 72057594037927935
        const MAX_SECONDS: u64 = u64::MAX >> 2; // 4611686018427387903
        assert_eq!(parse("T1200959900632132H", d), Ok(("", d.with_hms(MAX_HOURS, 0, 0).unwrap())));
        assert_eq!(parse("T1200959900632133H", d), Err(OUT_OF_RANGE));
        assert_eq!(
            parse("T1200959900632132.05H", d),
            Ok(("", d.with_hms(MAX_HOURS, 3, 0).unwrap()))
        );
        assert_eq!(parse("T1200959900632132.5H", d), Err(OUT_OF_RANGE));
        assert_eq!(
            parse("T72057594037927935M", d),
            Ok(("", d.with_hms(0, MAX_MINUTES, 0).unwrap()))
        );
        assert_eq!(parse("T72057594037927936M", d), Err(OUT_OF_RANGE));
        assert_eq!(
            parse("T72057594037927935.25M", d),
            Ok(("", d.with_hms(0, MAX_MINUTES, 15).unwrap()))
        );
        assert_eq!(
            parse("T4611686018427387903S", d),
            Ok(("", d.with_seconds(MAX_SECONDS).unwrap()))
        );
        assert_eq!(parse("T4611686018427387904S", d), Err(OUT_OF_RANGE));
        assert_eq!(
            parse("T4611686018427387903.25S", d),
            Ok(("", d.with_seconds(u64::MAX >> 2).unwrap().with_millis(250).unwrap()))
        );
        assert_eq!(
            parse("T4611686018427387903.999999999S", d),
            Ok(("", d.with_seconds(MAX_SECONDS).unwrap().with_nanos(999_999_999).unwrap()))
        );
        assert_eq!(parse("T4611686018427387903.9999999995S", d), Err(OUT_OF_RANGE));
        assert_eq!(parse("T12H34M61S", d), Err(OUT_OF_RANGE));
    }

    #[test]
    fn test_parse_duration() {
        let d = CalendarDuration::new();
        assert_eq!(
            parse_iso8601_duration("P12Y"),
            Ok(("", d.with_years_and_months(12, 0).unwrap()))
        );
        assert_eq!(parse_iso8601_duration("P34M"), Ok(("", d.with_months(34))));
        assert_eq!(parse_iso8601_duration("P56D"), Ok(("", d.with_days(56))));
        assert_eq!(parse_iso8601_duration("P78W"), Ok(("", d.with_weeks_and_days(78, 0).unwrap())));

        // Fractional date values
        assert_eq!(
            parse_iso8601_duration("P1.25Y"),
            Ok(("", d.with_years_and_months(1, 3).unwrap()))
        );
        assert_eq!(
            parse_iso8601_duration("P1.99Y"),
            Ok(("", d.with_years_and_months(2, 0).unwrap()))
        );
        assert_eq!(parse_iso8601_duration("P1.4W"), Ok(("", d.with_days(10))));
        assert_eq!(parse_iso8601_duration("P1.95W"), Ok(("", d.with_days(14))));
        assert_eq!(parse_iso8601_duration("P1.5M"), Err(INVALID));
        assert_eq!(parse_iso8601_duration("P1.5D"), Err(INVALID));

        // Data after a fraction is not considered part of the value
        assert_eq!(
            parse_iso8601_duration("P1.25Y5D"),
            Ok(("5D", d.with_years_and_months(1, 3).unwrap()))
        );
        assert_eq!(
            parse_iso8601_duration("P1.25YT3H"),
            Ok(("T3H", d.with_years_and_months(1, 3).unwrap()))
        );

        // Zero values
        assert_eq!(parse_iso8601_duration("P0Y"), Ok(("", d)));
        assert_eq!(parse_iso8601_duration("P0M"), Ok(("", d)));
        assert_eq!(parse_iso8601_duration("P0W"), Ok(("", d)));
        assert_eq!(parse_iso8601_duration("P0D"), Ok(("", d)));
        assert_eq!(parse_iso8601_duration("PT0M"), Ok(("", d)));
        assert_eq!(parse_iso8601_duration("PT0S"), Ok(("", d)));

        // Invalid designator at a position where another designator can be expected.
        assert_eq!(parse_iso8601_duration("P12Y12Y"), Err(INVALID));
        assert_eq!(parse_iso8601_duration("P12M12M"), Err(INVALID));
        assert_eq!(parse_iso8601_duration("P12M12Y"), Err(INVALID));

        // Trailing data
        assert_eq!(
            parse_iso8601_duration("P12W34D"),
            Ok(("34D", d.with_weeks_and_days(12, 0).unwrap()))
        );
        assert_eq!(parse_iso8601_duration("P12D12D"), Ok(("12D", d.with_days(12))));
        assert_eq!(parse_iso8601_duration("P12D12Y"), Ok(("12Y", d.with_days(12))));
    }
}
