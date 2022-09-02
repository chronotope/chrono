#!/usr/bin/env bash

set -euo pipefail

# shellcheck source=ci/_shlib.sh
source "${BASH_SOURCE[0]%/*}/_shlib.sh"

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
    CHECK_COMBINATORIC  Combine various features and verify that we compile
"
        exit
    fi

    runv cargo --version

    if [[ ${RUST_VERSION:-} != 1.38.0 ]]; then
        if [[ ${WASM:-} == yes_wasm ]]; then
            test_wasm
        elif [[ ${WASM:-} == wasm_simple ]]; then
            test_wasm_simple
        elif [[ ${WASM:-} == wasm_emscripten ]]; then
            test_wasm_emscripten
        elif [[ ${WASM:-} == wasm_unknown ]]; then
            test_wasm_unknown
        elif [[ ${WASM:-} == wasm_unknown_no_wasmbind ]]; then
            test_wasm_unknown_no_wasmbind
        elif [[ ${WASM:-} == wasm_wasi ]]; then
            test_wasm_wasi
        else
            test_regular UTC0
        fi
    else
        echo "ERROR: didn't run any tests"
        exit 1
    fi
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
    if ! runt env TZ="$(date +%z)" NOW="$(date +%s)" wasm-pack test --node ; then
        # sometimes on github the initial build takes 8-10 minutes, and we
        # check that the time makes sense inside the test by approximately
        # comparing it to the env var,
        #
        # so re-run the test in case it took too long
        runt env TZ="$(date +%z)" NOW="$(date +%s)" wasm-pack test --node
    fi
}

test_wasm_emscripten() {
    runt cargo build --target wasm32-unknown-emscripten
}

test_wasm_unknown() {
    runt cargo build --target wasm32-unknown-unknown
}

test_wasm_unknown_no_wasmbind() {
    runt cargo build --target wasm32-unknown-unknown --no-default-features --features clock,std
}

test_wasm_wasi() {
    runt cargo build --target wasm32-wasi
}

main "$@"
