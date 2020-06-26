#!/usr/bin/env bash

set -euo pipefail

# shellcheck source=ci/_shlib.sh
source "${BASH_SOURCE[0]%/*}/_shlib.sh"

main() {
    # TODO: get clippy clean
    # runt cargo clippy --color=always || true
    runt make readme
    runv git diff --exit-code -- README.md
}

main
