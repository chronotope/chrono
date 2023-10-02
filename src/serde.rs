//! Serialization/Deserialization with serde.
//!
//! This module provides default implementations for `DateTime` using the [RFC 3339][1] format and
//! various alternatives for use with serde's [`with` annotation][2].
//!
//! *Available on crate feature 'serde' only.*
//!
//! [1]: https://tools.ietf.org/html/rfc3339
//! [2]: https://serde.rs/field-attrs.html#with
use core::fmt;
use serde::de;

pub use crate::datetime::serde::*;

/// Create a custom `de::Error` with `SerdeError::InvalidTimestamp`.
pub(crate) fn invalid_ts<E, T>(value: T) -> E
where
    E: de::Error,
    T: fmt::Display,
{
    E::custom(SerdeError::InvalidTimestamp(value))
}

enum SerdeError<T: fmt::Display> {
    InvalidTimestamp(T),
}

impl<T: fmt::Display> fmt::Display for SerdeError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SerdeError::InvalidTimestamp(ts) => {
                write!(f, "value is not a legal timestamp: {}", ts)
            }
        }
    }
}
