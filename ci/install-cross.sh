#!/usr/bin/env bash

set -euxo pipefail

main() {
    local target=
    if [[ "$(os)" == "ubuntu-latest" || "$(os)" == Linux ]]; then
        target=x86_64-unknown-linux-musl
        # shellcheck disable=SC2209
        sort=sort
    else
        target=x86_64-apple-darwin
        sort=gsort
    fi

    # This fetches latest stable release
    local tag
    tag=$(git ls-remote --tags --refs --exit-code https://github.com/rust-embedded/cross \
              | cut -d/ -f3 \
              | grep -E '^v[0.1.0-9.]+$' \
              | $sort --version-sort \
              | tail -n1)

    curl -LSfs https://japaric.github.io/trust/install.sh | \
        sh -s -- \
           --force \
           --git rust-embedded/cross \
           --tag "$tag" \
           --target $target

    cross --version
}

# get an os name, either github's pre-set one or the result of uname
os() {
    if [ -n "${OS_NAME:-}" ]; then
        echo "$OS_NAME"
        return
    fi
    uname
}

main
