#!/bin/bash

# This is the script that's executed by travis, you can run it yourself to run
# the exact same suite

set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

channel() {
    if [ -n "${TRAVIS}" ]; then
        if [ "${TRAVIS_RUST_VERSION}" = "${CHANNEL}" ]; then
            pwd
            (set -x; cargo "$@")
        fi
    elif [ -n "${APPVEYOR}" ]; then
        if [ "${APPVEYOR_RUST_CHANNEL}" = "${CHANNEL}" ]; then
            pwd
            (set -x; cargo "$@")
        fi
    else
        pwd
        (set -x; cargo "+${CHANNEL}" "$@")
    fi
}

build_and_test() {
  # interleave building and testing in hope that it saves time
  # also vary the local time zone to (hopefully) catch tz-dependent bugs
  # also avoid doc-testing multiple times---it takes a lot and rarely helps
  cargo clean
  channel build -v
  TZ=ACST-9:30 channel test -v --lib
  channel build -v --features rustc-serialize
  TZ=EST4 channel test -v --features rustc-serialize --lib
  channel build -v --features 'serde bincode'
  TZ=UTC0 channel test -v --features 'serde bincode'
}

build_only() {
  # Rust 1.13 doesn't support custom derive, so, to avoid doctests which
  # validate that, we just build there.
  cargo clean
  channel build -v
  channel build -v --features rustc-serialize
  channel build -v --features 'serde bincode'
}

rustc --version
cargo --version

CHANNEL=nightly
build_and_test

CHANNEL=beta
build_and_test

CHANNEL=stable
build_and_test

CHANNEL=1.13.0
build_only
