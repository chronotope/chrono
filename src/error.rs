//! Error type
use core::fmt;

use crate::offset::TzLookupError;

/// Error type for date and time operations.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// There is not enough information to create a date/time.
    ///
    /// An example is parsing a string with not enough date/time fields, or the result of a
    /// time that is ambiguous during a time zone transitions (due to for example DST).
    Ambiguous,

    /// A date or datetime does not exist.
    ///
    /// Examples are:
    /// - April 31,
    /// - February 29 in a non-leap year,
    /// - a time that falls in the gap created by moving the clock forward during a DST transition,
    /// - a leap second on a non-minute boundary.
    DoesNotExist,

    /// One or more of the arguments to a function are invalid.
    ///
    /// An example is creating a `NaiveTime` with 25 as the hour value.
    InvalidArgument,

    /// The result, or an intermediate value necessary for calculating a result, would be out of
    /// range.
    ///
    /// An example is a date for the year 500.000, which is out of the range supported by chrono's
    /// types.
    OutOfRange,

    /// Lookup of a local datetime in a timezone failed.
    TzLookupFailure(TzLookupError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Ambiguous => write!(f, "not enough information for a concrete date/time"),
            Error::DoesNotExist => write!(f, "date or datetime does not exist"),
            Error::InvalidArgument => write!(f, "invalid parameter"),
            Error::OutOfRange => write!(f, "date outside of the supported range"),
            Error::TzLookupFailure(e) => fmt::Display::fmt(&e, f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}
