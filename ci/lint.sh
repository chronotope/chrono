#!/usr/bin/env bash

set -euo pipefail

# shellcheck source=ci/_shlib.sh
source "${BASH_SOURCE[0]%/*}/_shlib.sh"

main() {
    # rustflags are present because of: https://github.com/rust-lang/rust-clippy/issues/5749
    runt env RUSTFLAGS="-Dwarnings" cargo clippy --color=always -- -D warnings -A clippy::manual-non-exhaustive
    runt cargo fmt -- --check --color=always
    runt make readme
    runv git diff --exit-code -- README.md
}

main
