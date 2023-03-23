// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

use core::fmt;
use std::time::SystemTimeError;

/// Chrono error
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Invalid date
    InvalidDate,
    /// Invalid time
    InvalidTime,
    /// Invalid date time
    InvalidDateTime,
    /// Invalid time zone
    InvalidTimeZone,
    /// Ambigious date
    AmbiguousDate,
    /// Missing date
    #[cfg(all(unix, feature = "clock"))]
    MissingDate,
    #[cfg(all(windows, feature = "clock"))]
    SystemTimeBeforeEpoch,
    #[cfg(all(windows, feature = "clock"))]
    SystemError(std::io::Error),

    /// Given field is out of permitted range.
    ParsingOutOfRange,

    /// There is no possible date and time value with given set of fields.
    ///
    /// This does not include the out-of-range conditions, which are trivially invalid.
    /// It includes the case that there are one or more fields that are inconsistent to each other.
    ParsingImpossible,

    /// Given set of fields is not enough to make a requested date and time value.
    ///
    /// Note that there *may* be a case that given fields constrain the possible values so much
    /// that there is a unique possible value. Chrono only tries to be correct for
    /// most useful sets of fields however, as such constraint solving can be expensive.
    ParsingNotEnough,

    /// The input string has some invalid character sequence for given formatting items.
    ParsingInvalid,

    /// The input string has been prematurely ended.
    ParsingTooShort,

    /// All formatting items have been read but there is a remaining input.
    ParsingTooLong,

    /// There was an error on the formatting string, or there were non-supported formating items.
    ParsingBadFormat,

    /// Date time error
    DateTime(&'static str),
    /// Local time type search error
    FindLocalTimeType(&'static str),
    /// Local time type error
    LocalTimeType(&'static str),
    /// Invalid slice for integer conversion
    InvalidSlice(&'static str),
    /// Invalid Tzif file
    InvalidTzFile(&'static str),
    /// Invalid TZ string
    InvalidTzString(&'static str),
    /// I/O error
    Io(std::io::ErrorKind),
    /// Out of range error
    OutOfRange(&'static str),
    /// Integer parsing error
    ParseInt(core::num::ParseIntError),
    /// Date time projection error
    ProjectDateTime(&'static str),
    /// System time error
    SystemTime,
    /// Time zone error
    TimeZone(&'static str),
    /// Transition rule error
    TransitionRule(&'static str),
    /// Unsupported Tzif file
    UnsupportedTzFile(&'static str),
    /// Unsupported TZ string
    UnsupportedTzString(&'static str),
    /// UTF-8 error
    Utf8(core::str::Utf8Error),

    /// Error when tryint to convert from int
    TryFromIntError,

    /// Error when tryint to convert a string to utf8
    FromUtf8Error,

    /// Unexpected end of file
    UnexpectedEOF,

    /// Invalid data
    InvalidData,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidDate => write!(f, "invalid date"),
            Error::InvalidTime => write!(f, "invalid time"),
            Error::InvalidDateTime => write!(f, "invalid date time"),
            Error::InvalidTimeZone => write!(f, "invalid time zone"),
            Error::AmbiguousDate => write!(f, "tried to operate over ambiguous date"),
            #[cfg(all(unix, feature = "clock"))]
            Error::MissingDate => write!(f, "missing date"),
            #[cfg(all(windows, feature = "clock"))]
            Error::SystemTimeBeforeEpoch => write!(f, "system time before Unix epoch"),
            #[cfg(all(windows, feature = "clock"))]

            Error::SystemError(error) => write!(f, "system error: {}", error),
            Error::ParsingOutOfRange => write!(f, "input is out of range"),
            Error::ParsingImpossible => write!(f, "no possible date and time matching input"),
            Error::ParsingNotEnough => write!(f, "input is not enough for unique date and time"),
            Error::ParsingInvalid => write!(f, "input contains invalid characters"),
            Error::ParsingTooShort => write!(f, "premature end of input"),
            Error::ParsingTooLong => write!(f, "trailing input"),
            Error::ParsingBadFormat => write!(f, "bad or unsupported format string"),

            Error::DateTime(error) => write!(f, "invalid date time: {}", error),
            Error::FindLocalTimeType(error) => error.fmt(f),
            Error::LocalTimeType(error) => write!(f, "invalid local time type: {}", error),
            Error::InvalidSlice(error) => error.fmt(f),
            Error::InvalidTzString(error) => write!(f, "invalid TZ string: {}", error),
            Error::InvalidTzFile(error) => error.fmt(f),
            Error::Io(error) => error.fmt(f),
            Error::OutOfRange(error) => error.fmt(f),
            Error::ParseInt(error) => error.fmt(f),
            Error::ProjectDateTime(error) => error.fmt(f),
            Error::SystemTime => write!(f, "opposite direction of system time"),
            Error::TransitionRule(error) => write!(f, "invalid transition rule: {}", error),
            Error::TimeZone(error) => write!(f, "invalid time zone: {}", error),
            Error::UnsupportedTzFile(error) => error.fmt(f),
            Error::UnsupportedTzString(error) => write!(f, "unsupported TZ string: {}", error),
            Error::Utf8(error) => error.fmt(f),

            Error::TryFromIntError => write!(f, "failed to convert int"),
            Error::FromUtf8Error => write!(f, "failed to convert utf8"),

            Error::UnexpectedEOF => write!(f, "unexpected end of file"),
            Error::InvalidData => write!(f, "invalid data"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            #[cfg(all(windows, feature = "clock"))]
            ErrorKind::SystemError(error) => Some(error),
            _ => None,
        }
    }
}

impl From<std::string::FromUtf8Error> for Error {
    fn from(_: std::string::FromUtf8Error) -> Self {
        Error::FromUtf8Error
    }
}

impl From<core::num::TryFromIntError> for Error {
    fn from(_: core::num::TryFromIntError) -> Self {
        Error::TryFromIntError
    }
}

impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Self {
        Error::Io(error.kind())
    }
}

impl From<core::num::ParseIntError> for Error {
    fn from(error: core::num::ParseIntError) -> Self {
        Error::ParseInt(error)
    }
}

impl From<SystemTimeError> for Error {
    fn from(_: SystemTimeError) -> Self {
        Error::SystemTime
    }
}

impl From<core::str::Utf8Error> for Error {
    fn from(error: core::str::Utf8Error) -> Self {
        Error::Utf8(error)
    }
}