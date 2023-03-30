// All code cribbed from num-integer. We do this to minimize dependencies and
// build-time.
//
// num-integer is released under the terms of the MIT OR Apache-2.0 licenses,
// as is this code. These are the same licenses as Chrono itself.

pub(crate) trait Integer: Copy {
    fn div_rem(self, other: Self) -> (Self, Self);
    fn div_floor(self, other: Self) -> Self;
    fn mod_floor(self, other: Self) -> Self;
}

// Implements the Integer trait for a signed integer type.
macro_rules! impl_integer_signed {
    ($t: ty) => {
        impl Integer for $t {
            #[inline]
            fn div_rem(self, other: Self) -> (Self, Self) {
                (self / other, self % other)
            }

            #[inline]
            fn div_floor(self, other: Self) -> Self {
                // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
                // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
                let (d, r) = self.div_rem(other);
                if (r > 0 && other < 0) || (r < 0 && other > 0) {
                    d - 1
                } else {
                    d
                }
            }

            #[inline]
            fn mod_floor(self, other: Self) -> Self {
                // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
                // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
                let r = self % other;
                if (r > 0 && other < 0) || (r < 0 && other > 0) {
                    r + other
                } else {
                    r
                }
            }
        }
    };
}

// Implements the Integer trait for a unsigned integer type.
macro_rules! impl_integer_unsigned {
    ($t: ty) => {
        impl Integer for $t {
            #[inline]
            fn div_rem(self, other: Self) -> (Self, Self) {
                (self / other, self % other)
            }

            #[inline]
            fn div_floor(self, other: Self) -> Self {
                self / other
            }

            #[inline]
            fn mod_floor(self, other: Self) -> Self {
                self % other
            }
        }
    };
}

impl_integer_signed!(i32);
impl_integer_signed!(i64);
impl_integer_unsigned!(u32);

pub(crate) fn div_mod_floor<T: Integer>(x: T, y: T) -> (T, T) {
    (div_floor(x, y), mod_floor(x, y))
}

pub(crate) fn div_rem<T: Integer>(x: T, y: T) -> (T, T) {
    x.div_rem(y)
}

pub(crate) fn div_floor<T: Integer>(x: T, y: T) -> T {
    x.div_floor(y)
}

pub(crate) fn mod_floor<T: Integer>(x: T, y: T) -> T {
    x.mod_floor(y)
}
