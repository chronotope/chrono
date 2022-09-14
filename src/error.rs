use core::fmt;

/// Internal representation of the chrono error.
#[derive(Debug)]
pub(crate) enum ErrorKind {
    InvalidDate,
    InvalidTime,
    InvalidDateTime,
    InvalidTimeZone,
    AmbiguousDate,
    #[cfg(all(unix, feature = "clock"))]
    MissingDate,
    #[cfg(all(windows, feature = "clock"))]
    SystemTimeBeforeEpoch,
    #[cfg(all(windows, feature = "clock"))]
    SystemError(std::io::Error),
}

/// The error raised for an invalid date time.
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

impl Error {
    /// Internal constructor for a chrono error.
    #[inline]
    pub(crate) fn new(kind: ErrorKind) -> Self {
        Self { kind }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ErrorKind::InvalidDate => write!(f, "invalid date"),
            ErrorKind::InvalidTime => write!(f, "invalid time"),
            ErrorKind::InvalidDateTime => write!(f, "invalid date time"),
            ErrorKind::InvalidTimeZone => write!(f, "invalid time zone"),
            ErrorKind::AmbiguousDate => write!(f, "tried to operate over ambiguous date"),
            #[cfg(all(unix, feature = "clock"))]
            ErrorKind::MissingDate => write!(f, "missing date"),
            #[cfg(all(windows, feature = "clock"))]
            ErrorKind::SystemTimeBeforeEpoch => write!(f, "system time before Unix epoch"),
            #[cfg(all(windows, feature = "clock"))]
            ErrorKind::SystemError(error) => write!(f, "system error: {}", error),
        }
    }
}

impl From<ErrorKind> for Error {
    #[inline]
    fn from(kind: ErrorKind) -> Self {
        Self::new(kind)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.kind {
            #[cfg(all(windows, feature = "clock"))]
            ErrorKind::SystemError(error) => Some(error),
            _ => None,
        }
    }
}

/// Implementation used in many test cases.
#[cfg(test)]
impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[cfg(test)]
impl PartialEq for ErrorKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            #[cfg(all(windows, feature = "clock"))]
            (Self::SystemError(l0), Self::SystemError(r0)) => l0.kind() == r0.kind(),
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}
