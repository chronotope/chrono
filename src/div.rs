// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// Copyright 2013-2014 The Rust Project Developers.
// See README.md and LICENSE.txt for details.

//! Integer division utilities. (Shamelessly copied from [num](https://github.com/rust-lang/num/))

// Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
// December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)

use std::ops::{Add, Sub, Div, Rem};
use std::num::{Zero, One};

/// Same as `(a / b, a % b)`.
#[inline]
pub fn div_rem<T>(a: T, b: T) -> (T, T)
        where T: Copy + Div<T,Output=T> + Rem<T,Output=T> {
    (a / b, a % b)
}

/// Calculates a floored integer quotient.
#[inline]
pub fn div_floor<T>(a: T, b: T) -> T
        where T: Copy + Ord + Zero + One +
                 Add<T,Output=T> + Sub<T,Output=T> + Div<T,Output=T> + Rem<T,Output=T> {
    div_mod_floor(a, b).0
}

/// Calculates a floored modulo.
#[inline]
pub fn mod_floor<T>(a: T, b: T) -> T
        where T: Copy + Ord + Zero + One +
                 Add<T,Output=T> + Sub<T,Output=T> + Div<T,Output=T> + Rem<T,Output=T> {
    div_mod_floor(a, b).1
}

/// Calculates a floored integer quotient and modulo.
#[inline]
pub fn div_mod_floor<T>(a: T, b: T) -> (T, T)
        where T: Copy + Ord + Zero + One +
                 Add<T,Output=T> + Sub<T,Output=T> + Div<T,Output=T> + Rem<T,Output=T> {
    let zero = Zero::zero();
    let one = One::one();
    match (a / b, a % b) {
        (d, r) if (r > zero && b < zero) || (r < zero && b > zero) => (d - one, r + b),
        (d, r)                                                     => (d, r),
    }
}

#[cfg(test)]
mod tests {
    use super::{mod_floor, div_mod_floor};

    #[test]
    fn test_mod_floor() {
        assert_eq!(mod_floor( 8,  3),  2);
        assert_eq!(mod_floor( 8, -3), -1);
        assert_eq!(mod_floor(-8,  3),  1);
        assert_eq!(mod_floor(-8, -3), -2);

        assert_eq!(mod_floor( 1,  2),  1);
        assert_eq!(mod_floor( 1, -2), -1);
        assert_eq!(mod_floor(-1,  2),  1);
        assert_eq!(mod_floor(-1, -2), -1);
    }

    #[test]
    fn test_div_mod_floor() {
        assert_eq!(div_mod_floor( 8,  3), ( 2,  2));
        assert_eq!(div_mod_floor( 8, -3), (-3, -1));
        assert_eq!(div_mod_floor(-8,  3), (-3,  1));
        assert_eq!(div_mod_floor(-8, -3), ( 2, -2));

        assert_eq!(div_mod_floor( 1,  2), ( 0,  1));
        assert_eq!(div_mod_floor( 1, -2), (-1, -1));
        assert_eq!(div_mod_floor(-1,  2), (-1,  1));
        assert_eq!(div_mod_floor(-1, -2), ( 0, -1));
    }
}

