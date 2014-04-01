// This is a part of rust-chrono.
// Copyright (c) 2014, Kang Seonghoon.
// See README.md and LICENSE.txt for details.

#![crate_id = "chrono#0.1.0"]
#![crate_type = "lib"]
#![comment = "Date and time library for Rust"]
#![license = "MIT"]

#![feature(globs, macro_rules)]

extern crate num;

pub mod duration;
pub mod date;
pub mod time;
pub mod datetime;

