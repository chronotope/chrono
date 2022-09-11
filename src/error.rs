use core::fmt;

/// Internal representation of the chrono error.
#[derive(Debug)]
pub(crate) enum ChronoErrorKind {
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
pub struct ChronoError {
    kind: ChronoErrorKind,
}

impl ChronoError {
    /// Internal constructor for a chrono error.
    #[inline]
    pub(crate) fn new(kind: ChronoErrorKind) -> Self {
        Self { kind }
    }
}

impl fmt::Display for ChronoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ChronoErrorKind::InvalidDate => write!(f, "invalid date"),
            ChronoErrorKind::InvalidTime => write!(f, "invalid time"),
            ChronoErrorKind::InvalidDateTime => write!(f, "invalid date time"),
            ChronoErrorKind::InvalidTimeZone => write!(f, "invalid time zone"),
            ChronoErrorKind::AmbiguousDate => write!(f, "tried to operate over ambiguous date"),
            #[cfg(all(unix, feature = "clock"))]
            ChronoErrorKind::MissingDate => write!(f, "missing date"),
            #[cfg(all(windows, feature = "clock"))]
            ChronoErrorKind::SystemTimeBeforeEpoch => write!(f, "system time before Unix epoch"),
            #[cfg(all(windows, feature = "clock"))]
            ChronoErrorKind::SystemError(error) => write!(f, "system error: {}", error),
        }
    }
}

impl From<ChronoErrorKind> for ChronoError {
    #[inline]
    fn from(kind: ChronoErrorKind) -> Self {
        Self::new(kind)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ChronoError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.kind {
            #[cfg(all(windows, feature = "clock"))]
            ChronoErrorKind::SystemError(error) => Some(error),
            _ => None,
        }
    }
}

/// Implementation used in many test cases.
#[cfg(test)]
impl PartialEq for ChronoError {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[cfg(test)]
impl PartialEq for ChronoErrorKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            #[cfg(all(windows, feature = "clock"))]
            (Self::SystemError(l0), Self::SystemError(r0)) => l0.kind() == r0.kind(),
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}
