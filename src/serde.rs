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

/// Macro to take care of the boilerplate of a module for use with serde's `with` attribute.
/// This creates two modules: one for the regular (de)serialization and one for an optional type.
#[doc(hidden)]
#[macro_export]
macro_rules! serde_module {
    (
        type: $type:ty,
        module: $module:ident,
        module_opt: $module_opt:ident,
        doc: $doc:literal,
        $serialize_to:ident: $serialize_fn:expr,
        $deserialize_from:ident: $visitor:ident,
        expecting: $expecting:literal,
        $($visit:ident($visit_ty:ty): $visit_fn:expr,)+
    ) => {
        #[doc=concat!("Serialize/deserialize a `", stringify!($type), "` to/from ", $expecting, ".")]
        ///
        /// Intended for use with the [`#[serde(with = "module")]` annotation](
        /// https://serde.rs/field-attrs.html#with).
        #[doc=$doc]
        #[allow(clippy::redundant_closure_call)]
        pub mod $module {
            use serde::{de, ser};
            use core::fmt;
            use super::*;

            #[doc=concat!("Serialize a `", stringify!($type), "` to ", $expecting, ".")]
            pub fn serialize<S>(dt: &$type, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: ser::Serializer,
            {
                serializer
                    .$serialize_to($serialize_fn(dt).map_err(ser::Error::custom)?)
            }

            #[doc=concat!("Deserialize ", $expecting, " to a `", stringify!($type), "`.")]
            pub fn deserialize<'de, D>(d: D) -> Result<$type, D::Error>
            where
                D: de::Deserializer<'de>,
            {
                d.$deserialize_from($visitor)
            }

            impl<'de> de::Visitor<'de> for $visitor {
                type Value = $type;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str($expecting)
                }

                $(fn $visit<E>(self, value: $visit_ty) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    $visit_fn(value)
                })+
            }
        }

        #[doc=concat!("Serialize/deserialize an `Option<", stringify!($type), ">` to/from ", $expecting, ".")]
        ///
        /// Intended for use with `serde`'s `with` attribute.
        #[allow(clippy::redundant_closure_call)]
        pub mod $module_opt {
            use serde::{de, ser};
            use core::fmt;
            use super::*;

            #[doc=concat!("Serialize an `Option<", stringify!($type), ">` to ", $expecting, ".")]
            pub fn serialize<S>(opt: &Option<$type>, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: ser::Serializer,
            {
                match *opt {
                    Some(ref dt) => serializer.serialize_some(&$serialize_fn(dt).map_err(ser::Error::custom)?),
                    None => serializer.serialize_none(),
                }
            }

            #[doc=concat!("Deserialize ", $expecting, " to an `Option<", stringify!($type), ">`.")]
            pub fn deserialize<'de, D>(d: D) -> Result<Option<$type>, D::Error>
            where
                D: de::Deserializer<'de>,
            {
                d.deserialize_option(OptionVisitor)
            }

            struct OptionVisitor;

            impl<'de> de::Visitor<'de> for OptionVisitor {
                type Value = Option<$type>;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str(concat!($expecting, " or none"))
                }

                fn visit_some<D>(self, d: D) -> Result<Self::Value, D::Error>
                where
                    D: de::Deserializer<'de>,
                {
                    d.$deserialize_from($visitor).map(Some)
                }

                fn visit_none<E>(self) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    Ok(None)
                }

                fn visit_unit<E>(self) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    Ok(None)
                }
            }
        }
    };
}

/// Wrap a function as a closure that returns `Result<_, Infallible>`
#[macro_export]
#[doc(hidden)]
macro_rules! infallible {
    ($fn:expr) => {
        |val| Ok::<_, core::convert::Infallible>($fn(val))
    };
}
