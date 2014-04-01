Rust-chrono
===========

[![Rust-chrono on Travis CI][travis-image]][travis]

[travis-image]: https://travis-ci.org/lifthrasiir/rust-chrono.png
[travis]: https://travis-ci.org/lifthrasiir/rust-chrono

Date and time handling for Rust.

Design Goals
------------

* 1-to-1 correspondence with ISO 8601.
* Timezone-aware by default.
* Space efficient.
* Moderate lookup table size, should not exceed a few KBs.
* Avoid divisions as long as possible.

References
----------

* https://github.com/mozilla/rust/wiki/Lib-datetime
* https://github.com/luisbg/rust-datetime/wiki/Use-Cases

