//! Error type
use core::fmt;

/// Error type for date and time operations.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// There is not enough information to create a date/time.
    ///
    /// An example is parsing a string with not enough date/time fields, or the result of a
    /// time that is ambiguous during a time zone transition (due to for example DST).
    Ambiguous,

    /// A date or datetime does not exist.
    ///
    /// Examples are:
    /// - April 31,
    /// - February 29 in a non-leap year,
    /// - a time that falls in the gap created by moving the clock forward during a DST transition,
    /// - a leap second on a non-minute boundary.
    DoesNotExist,

    /// Some of the date or time components are not consistent with each other.
    ///
    /// An example is parsing 'Sunday 2023-04-21', while that date is a Friday.
    Inconsistent,

    /// One or more of the arguments to a function are invalid.
    ///
    /// An example is creating a `NaiveTime` with 25 as the hour value.
    InvalidArgument,

    /// Character does not match with the expected format (during parsing).
    InvalidCharacter,

    /// The result, or an intermediate value necessary for calculating a result, would be out of
    /// range.
    ///
    /// An example is a date for the year 500.000, which is out of the range supported by chrono's
    /// types.
    OutOfRange,

    /// All formatting items have been read but there is a remaining input.
    TooLong,

    /// The input string has been prematurely ended.
    // TEMPORARY
    TooShort,

    /// The format string contains a formatting specifier that is not supported.
    UnsupportedSpecifier,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Ambiguous => write!(f, "not enough information for a unique date and time"),
            Error::DoesNotExist => write!(f, "date or datetime does not exist"),
            Error::Inconsistent => {
                write!(f, "some of the date or time components are not consistent with each other")
            }
            Error::InvalidArgument => write!(f, "invalid parameter"),
            Error::InvalidCharacter => write!(f, "input doesn't match with the expected format"),
            Error::OutOfRange => write!(f, "date outside of the supported range"),
            Error::TooLong => write!(f, "trailing input"),
            Error::TooShort => write!(f, "premature end of input"),
            Error::UnsupportedSpecifier => {
                write!(f, "format string contains a formatting specifier that is not supported")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}
