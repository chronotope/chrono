//! Error type
use core::fmt;

/// Error type for date and time operations.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Error {
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
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::DoesNotExist => write!(f, "date or datetime does not exist"),
            Error::InvalidArgument => write!(f, "invalid parameter"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}
