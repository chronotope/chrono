#[cfg(test)]
use core::fmt::{self, Write};

/// Compare the `Display` format of `value` against `expected`.
///
/// This is similar to writing `assert_eq!(value.to_string(), "expected")`, but works without any
/// allocations (and is shorter to write).
#[cfg(test)]
#[track_caller]
pub(crate) fn assert_display_eq<D>(value: D, expected: &str)
where
    D: fmt::Display,
{
    write!(&mut WriteCompare::new(expected), "{}", value).unwrap();
}

/// Compare the `Debug` format of `value` against `expected`.
///
/// This is similar to writing `assert_eq!(format!("{:?}", value), "expected")`, but works without
/// any allocations (and is shorter to write).
#[cfg(test)]
#[track_caller]
pub(crate) fn assert_debug_eq<D>(value: D, expected: &str)
where
    D: fmt::Debug,
{
    write!(&mut WriteCompare::new(expected), "{:?}", value).unwrap();
}

/// Sink that will return an error when bytes are written to it that do not match `expected`.
///
/// This can be used to test `Display` or `Debug` implementations in a pure `no_std` environment.
#[cfg(test)]
#[allow(dead_code)]
pub(crate) struct WriteCompare<'a> {
    expected: &'a str,
    remainder: &'a str,
}

#[cfg(test)]
impl<'a> WriteCompare<'a> {
    pub(crate) fn new(expected: &'a str) -> Self {
        Self { expected, remainder: expected }
    }
}

#[cfg(test)]
impl<'a> Write for WriteCompare<'a> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if let Some(remainder) = self.remainder.strip_prefix(s) {
            self.remainder = remainder;
            Ok(())
        } else {
            #[cfg(feature = "std")]
            eprintln!(
                "formatting difference: `(left == right)`\n  left: `\"{:?}{:?}(...)\"`\n right: `\"{:?}\"`",
                &self.expected[..(self.expected.len() - self.remainder.len())],
                s,
                self.expected
            );
            Err(fmt::Error)
        }
    }
}
