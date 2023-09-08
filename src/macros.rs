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

#[cfg(test)]
#[rustfmt::skip::macros(date)]
mod tests {
    use crate::NaiveDate;

    #[test]
    fn init_macros() {
        assert_eq!(date!(2023-09-08), NaiveDate::from_ymd_opt(2023, 9, 8).unwrap());
        assert_eq!(date!(2023-253), NaiveDate::from_yo_opt(2023, 253).unwrap());
    }

    #[test]
    fn macros_are_const() {
        const DATE: NaiveDate = date!(2023-09-08);
    }
}
