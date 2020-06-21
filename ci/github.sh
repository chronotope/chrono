#!/usr/bin/env bash

set -euo pipefail

TEST_TZS=(ACST-9:30 EST4 UTC0 Asia/Katmandu)
FEATURES=(std serde clock "alloc serde")
RUST_113_FEATURES=(rustc-serialize serde)

main() {
    if [[ $RUST_VERSION != 1.13.0 ]]; then
        if [[ $KIND == lint ]]; then
            do_lints
        elif [[ $WASM == yes_wasm ]]; then
            test_wasm
        elif [[ $CORE == no_std ]]; then
            test_core
        elif [[ $EXHAUSTIVE_TZ == y ]]; then
            test_all_tzs
        else
            test_regular UTC0
        fi
    elif [[ $RUST_VERSION == 1.13.0 ]]; then
        test_113
    else
        echo "ERROR: didn't run any tests"
        exit 1
    fi
}

do_lints() {
    # TODO: get clippy clean
    # runt cargo clippy --color=always || true
    runt make readme
    runv git diff --exit-code -- README.md
}

test_all_tzs() {
    for tz in "${TEST_TZS[@]}"; do
        test_regular "$tz"
    done
}

test_regular() {
    tz="$1" && shift

    runt env TZ="$tz" cargo test --features __doctest --color=always -- --color=always
    for feature in "${FEATURES[@]}"; do
        runt env TZ="$tz" cargo test --no-default-features --features "$feature" --lib --color=always -- --color=always
    done
}

test_113() {
    runv cargo build --color=always
    for feature in "${RUST_113_FEATURES[@]}"; do
        runt cargo build --features "$feature" --color=always
    done
}

test_core() {
    (
        cd ci/core-test
        runt cargo build --target thumbv6m-none-eabi --color=always
    )
}

test_wasm() {
    if ! command -v node; then
        echo "node is not installed, can't run wasm-pack tests"
        exit 1
    fi
    if ! command -v wasm-pack >/dev/null; then
        echo ">$ curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh" >&2
        curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
    fi
    now=$(date +%s)
    for tz in "${TEST_TZS[@]}"; do
        runt env TZ="$tz" NOW="$now" wasm-pack test --node -- --features wasmbind
    done
}

runt() {
    echo "======================================================================" >&2
    runv "$@"
}

runv() {
    echo ">$ $*" >&2
    # stdout is swallowed by gh actions
    "$@" >&2
}

main
