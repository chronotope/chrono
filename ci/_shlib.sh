#!/usr/bin/env bash

# Use github workflow commands to make sections of the tests more obvious
# https://help.github.com/en/actions/reference/workflow-commands-for-github-actions


# Run a test as a "group" -- output will be folded and hidden by default
runt() {
    echo "::group::$*"
    # stdout is occasionally swallowed by gh actions
    "$@" >&2
    echo "::endgroup::$*"
}

runv() {
    echo "🚀>$ $*" >&2
    # stdout is occasionally swallowed by gh actions
    "$@" >&2
}
