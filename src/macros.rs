//! Macro's for easy initialization of date and time values.

/// Create a [`NaiveDate`](crate::naive::NaiveDate) with a statically known value.
///
/// Supported formats are 'year-month-day' and 'year-ordinal'.
///
/// The input is checked at compile time.
///
/// Note: rustfmt wants to add spaces around `-` in this macro.
/// For nice formatting use `#[rustfmt::skip::macros(date)]`, or use as `date! {2023-09-08}`
///
/// # Examples
/// ```
/// use chrono::date;
///
/// assert_eq!(date!(2023-09-08), date!(2023-251));
/// ```
#[macro_export]
macro_rules! date {
    ($y:literal-$m:literal-$d:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            const DATE: $crate::NaiveDate = match $crate::NaiveDate::from_ymd_opt($y, $m, $d) {
                Some(d) => d,
                None => panic!("invalid calendar date"),
            };
            DATE
        }
    }};
    ($y:literal-$o:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            const DATE: $crate::NaiveDate = match $crate::NaiveDate::from_yo_opt($y, $o) {
                Some(d) => d,
                None => panic!("invalid ordinal date"),
            };
            DATE
        }
    }};
}

/// Create a [`NaiveTime`](crate::naive::NaiveTime) with a statically known value.
///
/// Supported formats are 'hour:minute' and 'hour:minute:second'.
///
/// The input is checked at compile time.
///
/// # Examples
/// ```
/// use chrono::time;
/// # use chrono::Timelike;
///
/// assert_eq!(time!(7:03), time!(7:03:00));
/// let leap_second = time!(23:59:60);
/// # assert!(leap_second.second() == 59 && leap_second.nanosecond() == 1_000_000_000);
/// ```
#[macro_export]
macro_rules! time {
    ($h:literal:$m:literal:$s:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            const SECS_NANOS: (u32, u32) = match $s {
                60u32 => (59, 1_000_000_000),
                s => (s, 0),
            };
            const TIME: $crate::NaiveTime =
                match $crate::NaiveTime::from_hms_nano_opt($h, $m, SECS_NANOS.0, SECS_NANOS.1) {
                    Some(t) => t,
                    None => panic!("invalid time"),
                };
            TIME
        }
    }};
    ($h:literal:$m:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            const TIME: $crate::NaiveTime = match $crate::NaiveTime::from_hms_opt($h, $m, 0) {
                Some(t) => t,
                None => panic!("invalid time"),
            };
            TIME
        }
    }};
}

/// Create a [`NaiveDateTime`](crate::naive::NaiveDateTime) with a statically known value.
///
/// The input is checked at compile time.
///
/// # Examples
/// ```
/// use chrono::datetime;
///
/// let _ = datetime!(2023-09-08 7:03);
/// let _ = datetime!(2023-09-08 7:03:25);
/// ```
#[macro_export]
macro_rules! datetime {
    ($y:literal-$m:literal-$d:literal $h:literal:$min:literal:$s:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            const DATE: $crate::NaiveDate = match $crate::NaiveDate::from_ymd_opt($y, $m, $d) {
                Some(d) => d,
                None => panic!("invalid calendar date"),
            };
            const SECS_NANOS: (u32, u32) = match $s {
                60u32 => (59, 1_000_000_000),
                s => (s, 0),
            };
            const TIME: $crate::NaiveTime =
                match $crate::NaiveTime::from_hms_nano_opt($h, $min, SECS_NANOS.0, SECS_NANOS.1) {
                    Some(t) => t,
                    None => panic!("invalid time"),
                };
            DATE.and_time(TIME)
        }
    }};
    ($y:literal-$m:literal-$d:literal $h:literal:$min:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            const DATE: $crate::NaiveDate = match $crate::NaiveDate::from_ymd_opt($y, $m, $d) {
                Some(d) => d,
                None => panic!("invalid calendar date"),
            };
            const TIME: $crate::NaiveTime = match $crate::NaiveTime::from_hms_opt($h, $min, 0) {
                Some(t) => t,
                None => panic!("invalid time"),
            };
            DATE.and_time(TIME)
        }
    }};
}

#[cfg(test)]
#[rustfmt::skip::macros(date)]
mod tests {
    use crate::{NaiveDate, NaiveDateTime, NaiveTime};

    #[test]
    fn init_macros() {
        assert_eq!(date!(2023-09-08), NaiveDate::from_ymd_opt(2023, 9, 8).unwrap());
        assert_eq!(date!(2023-253), NaiveDate::from_yo_opt(2023, 253).unwrap());
        assert_eq!(time!(7:03), NaiveTime::from_hms_opt(7, 3, 0).unwrap());
        assert_eq!(time!(7:03:25), NaiveTime::from_hms_opt(7, 3, 25).unwrap());
        assert_eq!(
            time!(23:59:60),
            NaiveTime::from_hms_nano_opt(23, 59, 59, 1_000_000_000).unwrap()
        );
        assert_eq!(
            datetime!(2023-09-08 7:03),
            NaiveDate::from_ymd_opt(2023, 9, 8).unwrap().and_hms_opt(7, 3, 0).unwrap(),
        );
        assert_eq!(
            datetime!(2023-09-08 7:03:25),
            NaiveDate::from_ymd_opt(2023, 9, 8).unwrap().and_hms_opt(7, 3, 25).unwrap(),
        );
    }

    #[test]
    fn macros_are_const() {
        const DATE: NaiveDate = date!(2023-09-08);
        const TIME: NaiveTime = time!(7:03:25);
        const NAIVEDATETIME: NaiveDateTime = datetime!(2023-09-08 7:03:25);
        assert_eq!(DATE.and_time(TIME), NAIVEDATETIME);
    }
}
