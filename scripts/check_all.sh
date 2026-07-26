#!/bin/bash
# check_all.sh - Compatibility wrapper for the authoritative Trust repo gate.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRUST_TARGO="${TRUST_CHECK_ALL_TARGO:-$REPO_ROOT/build/host/stage2/bin/targo}"
case "$TRUST_TARGO" in
    /*) ;;
    *) TRUST_TARGO="$REPO_ROOT/$TRUST_TARGO" ;;
esac

usage() {
    cat <<'EOF'
Usage: scripts/check_all.sh [check|tests]

Modes:
  check   Run the authoritative compile/syntax/metadata gate. This is the default.
  tests   Run that gate and the extended Rust test suites.

Set TRUST_CHECK_ALL_RUN_TESTS=1 to run extended tests from the default mode.
Set TRUST_CHECK_ALL_RUN_HOST_DIAGNOSTICS=1 to run advisory host Cargo diagnostics.
Set TRUST_CHECK_ALL_TARGO=/path/to/build/<host>/stage2/bin/targo to select a
repo-local stage2 Targo executable.
EOF
}

truthy() {
    case "${1:-}" in
        1|true|TRUE|yes|YES|on|ON) return 0 ;;
        0|false|FALSE|no|NO|off|OFF|'') return 1 ;;
        *)
            echo "Invalid boolean value for $2: $1" >&2
            exit 2
            ;;
    esac
}

RUN_TESTS="${TRUST_CHECK_ALL_RUN_TESTS:-0}"
case "${1:-check}" in
    check) ;;
    tests|test|--run-tests) RUN_TESTS=1 ;;
    -h|--help|help)
        usage
        exit 0
        ;;
    *)
        echo "Unknown check_all mode: $1" >&2
        usage >&2
        exit 2
        ;;
esac
if [ "$#" -gt 1 ]; then
    echo "Unexpected extra check_all argument: $2" >&2
    usage >&2
    exit 2
fi

if [ ! -x "$TRUST_TARGO" ]; then
    echo "Missing repo-local stage2 Trust targo required for golden checks: $TRUST_TARGO" >&2
    echo "DETAIL: ambient Cargo/Targo is never accepted as release-gate evidence." >&2
    exit 1
fi

# Preserve the legacy interpreter selector while keeping all gate sequencing,
# policy, and failure semantics in the Rust-native command below.
if [ -n "${PYTHON:-}" ] && [ -z "${TRUST_SCRIPT_PYTHON:-}" ]; then
    export TRUST_SCRIPT_PYTHON="$PYTHON"
fi

ARGS=(trust gate check-all --repo-root "$REPO_ROOT" --targo "$TRUST_TARGO")
if truthy "$RUN_TESTS" TRUST_CHECK_ALL_RUN_TESTS; then
    ARGS+=(--run-tests)
fi
if truthy "${TRUST_CHECK_ALL_RUN_HOST_DIAGNOSTICS:-0}" TRUST_CHECK_ALL_RUN_HOST_DIAGNOSTICS; then
    ARGS+=(--host-diagnostics)
fi

exec "$TRUST_TARGO" "${ARGS[@]}"
