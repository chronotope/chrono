#!/bin/bash

# This is the script that's executed by travis, you can run it yourself to run
# the exact same suite
#
# When running it locally the most important thing to set is the CHANNEL env
# var, otherwise it will run tests against every version of rust that it knows
# about (nightly, beta, stable, 1.13.0):
#
#     $ CHANNEL=stable ./ci/travis.sh

set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"


main() {
    if [[ -n "$CHANNEL" ]] ; then
        if [[ "$CHANNEL" == 1.13.0 ]]; then
            banner "Building $CHANNEL"
            build_only
        else
            banner "Building/testing $CHANNEL"
            build_and_test
            banner "Testing Core $CHANNEL"
            build_core_test
        fi
    else
        CHANNEL=nightly
        matching_banner "Test $CHANNEL"
        if [[ "${CLIPPY}" = y ]] ; then
            run_clippy
        else
            build_and_test
        fi

        CHANNEL=beta
        matching_banner "Test $CHANNEL"
        build_and_test

        CHANNEL=stable
        matching_banner "Test $CHANNEL"
        build_and_test
        build_core_test

        CHANNEL=1.13.0
        matching_banner "Test $CHANNEL"
        build_only
    fi
}

build_and_test() {
  # interleave building and testing in hope that it saves time
  # also vary the local time zone to (hopefully) catch tz-dependent bugs
  # also avoid doc-testing multiple times---it takes a lot and rarely helps
  cargo clean

  if [ "${WASMBIND}" != "y" ]; then
      build_and_test_nonwasm
  else
      build_and_test_wasm
  fi

  if [[ "$CHANNEL" == stable ]]; then
      if [[ -n "$TRAVIS" ]] ; then
          check_readme
      fi
  fi
}

build_and_test_nonwasm() {
  channel build -v
  TZ=ACST-9:30 channel test -v --lib
  channel build -v --features rustc-serialize
  TZ=EST4 channel test -v --features rustc-serialize --lib
  channel build -v --features serde
  TZ=UTC0 channel test -v --features serde --lib
  channel build -v --features serde,rustc-serialize
  TZ=Asia/Katmandu channel test -v --features serde,rustc-serialize

  # without default "clock" feature
  channel build -v --no-default-features --features std
  TZ=ACST-9:30 channel test -v --no-default-features --lib
  channel build -v --no-default-features --features std,rustc-serialize
  TZ=EST4 channel test -v --no-default-features --features rustc-serialize --lib
  channel build -v --no-default-features --features std,serde
  TZ=UTC0 channel test -v --no-default-features --features serde --lib
  channel build -v --no-default-features --features std,serde,rustc-serialize
  TZ=Asia/Katmandu channel test -v --no-default-features --features std,serde,rustc-serialize --lib

  channel build -v --no-default-features --features 'serde'
  TZ=UTC0 channel test -v --no-default-features --features 'serde' --lib

  channel build -v --no-default-features --features 'alloc serde'
  TZ=UTC0 channel test -v --no-default-features --features 'alloc serde' --lib
}

build_and_test_wasm() {
    touch tests/wasm.rs # ensure rebuild happens so TZ / NOW take effect
    TZ=ACST-9:30 NOW=$(date +%s) wasm-pack test --node -- --features wasmbind
    touch tests/wasm.rs
    TZ=EST4 NOW=$(date +%s) wasm-pack test --node -- --features wasmbind
    touch tests/wasm.rs
    TZ=UTC0 NOW=$(date +%s) wasm-pack test --node -- --features wasmbind
    touch tests/wasm.rs
    TZ=Asia/Katmandu NOW=$(date +%s) wasm-pack test --node -- --features wasmbind
}

build_only() {
  # Rust 1.13 doesn't support custom derive, so, to avoid doctests which
  # validate that, we just build there.
  cargo clean
  channel build -v
  channel build -v --features rustc-serialize
  channel build -v --features serde
  channel build -v --no-default-features --features std
}

build_core_test() {
    channel_run rustup target add thumbv6m-none-eabi --toolchain "$CHANNEL"
    (
        cd ci/core-test
        channel build -v --target thumbv6m-none-eabi
    )
}

run_clippy() {
    # cached installation will not work on a later nightly
    if [ -n "${TRAVIS}" ] && ! cargo install clippy --debug --force; then
        echo "COULD NOT COMPILE CLIPPY, IGNORING CLIPPY TESTS"
        exit
    fi

    cargo clippy --features 'serde rustc-serialize' -- -Dclippy
}

check_readme() {
    make readme
    (set -x; git diff --exit-code -- README.md) ; echo $?
}

# script helpers

banner() {
    echo "======================================================================"
    echo "$*"
    echo "======================================================================"
}

underline() {
    echo "$*"
    echo "${*//?/^}"
}

matching_banner() {
    if channel_matches || ! is_ci ; then
        banner "$*"
        echo_versions
    fi
}

echo_versions() {
    channel_run rustc --version
    channel_run cargo --version
    node --version
}

channel() {
    channel_run cargo "$@"
}

channel_run() {
    if channel_matches ; then
        local the_cmd="$ $*"
        underline "$the_cmd"
        "$@"
    elif ! is_ci ; then
        local cmd="$1"
        shift
        if [[ $cmd == cargo || $cmd == rustc ]] ; then
            underline "$ $cmd +${CHANNEL} $*"
            "$cmd" "+${CHANNEL}" "$@"
        else
            underline "$ $cmd $*"
            "$cmd" "$@"
        fi
    fi
}

channel_matches() {
    if is_ci ; then
        if [[ "${TRAVIS_RUST_VERSION}" = "${CHANNEL}"
              || "${APPVEYOR_RUST_CHANNEL}" = "${CHANNEL}" ]] ; then
            return 0
        fi
    fi
    return 1
}

is_ci() {
    if [[ -n "$TRAVIS" || -n "$APPVEYOR" ]] ; then
        return 0
    else
        return 1
    fi
}

main
