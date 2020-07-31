#!/usr/bin/env bash

set -euo pipefail

# shellcheck source=ci/_shlib.sh
source "${BASH_SOURCE[0]%/*}/_shlib.sh"

TEST_TZS=(ACST-9:30 EST4 UTC0 Asia/Katmandu)
FEATURES=(std serde clock "alloc serde" unstable-locales)
RUST_113_FEATURES=(rustc-serialize serde)

main() {
    if [[ "$*" =~ "-h" ]]; then
        echo -n "usage: ENV_VARS... $0

Recognized environment variables. Their values are as they are so that they are
meaningful in the github actions feature matrix UI.

    RUST_VERSION        The rust version currently being tested
                        This doesn't set the version, it is just used to test
    WASM                Empty or 'yes_wasm'
    CORE                'std' or 'no_std'
    EXHAUSTIVE_TZ       Emptly or 'all_tzs'
"
        exit
    fi

    runv cargo --version

    if [[ ${RUST_VERSION:-} != 1.13.0 ]]; then
        if [[ ${WASM:-} == yes_wasm ]]; then
            test_wasm
        elif [[ ${WASM:-} == wasm_simple ]]; then
            test_wasm_simple
        elif [[ ${CORE:-} == no_std ]]; then
            test_core
        elif [[ ${EXHAUSTIVE_TZ:-} == all_tzs ]]; then
            test_all_tzs
        else
            test_regular UTC0
        fi
    elif [[ ${RUST_VERSION:-} == 1.13.0 ]]; then
        test_113
    else
        echo "ERROR: didn't run any tests"
        exit 1
    fi
}

test_all_tzs() {
    for tz in "${TEST_TZS[@]}"; do
        test_regular "$tz"
    done
}

test_regular() {
    tz="$1" && shift

    runt env TZ="$tz" cargo test --features __doctest,unstable-locales --color=always -- --color=always
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
        echo "::group::curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh"
        curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
        runv wasm-pack --version
    fi
    test_wasm_simple
}

test_wasm_simple() {
    now=$(date +%s)
    tz=$(date +%z)
    runt env TZ="$tz" NOW="$now" wasm-pack test --node -- --features wasmbind
}

main "$@"
