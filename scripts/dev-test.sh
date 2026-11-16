#!/usr/bin/env bash
# Trust development test script
# Runs tests for trust verification crates only (not the full inherited upstream compiler test suite).
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
#
# Usage:
#   ./scripts/dev-test.sh                    # Test all trust crates
#   ./scripts/dev-test.sh trust-vcgen        # Test a single crate
#   ./scripts/dev-test.sh trust-vcgen trust-router  # Test multiple crates
#   ./scripts/dev-test.sh --lib              # Library tests only (no doc tests)
#   ./scripts/dev-test.sh --filter "bmc"     # Filter test names
#   ./scripts/dev-test.sh --help             # Show this help
#
# Environment:
#   TRUST_CRATES_DIR   Override crates directory (default: <repo>/crates)
#   TRUST_JOBS         Override parallel job count (default: system cores)
#   TRUST_VERBOSE      Set to 1 for verbose test output
#   TRUST_TARGO_BIN   Override Trust targo binary for Trust-owned runs
#   TRUST_REQUIRE_TARGO
#                      Set to 1 to require Trust targo; implied by --release
#                      and TRUST_RELEASE_GATE=1
#   TRUST_TARGO_TRUST_BIN
#                      Set BY this script: a run that includes
#                      trust-integration-tests' tests/*.rs builds targo-trust
#                      and exports a private copy of it, replacing any value
#                      from the caller. Other runs pass the caller's value on;
#                      no test they run reads it

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CRATES_DIR="${TRUST_CRATES_DIR:-${REPO_ROOT}/crates}"
# Memory-aware default: cap -j by BOTH cores and RAM (~5 GB/job). Defaulting to
# hw.ncpu on a 24 GB host exhausted the VM compressor and panicked the machine
# (see scripts/build.sh). Override with TRUST_JOBS.
_trust_ncpu="$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 8)"
_trust_mem_bytes="$(sysctl -n hw.memsize 2>/dev/null || awk '/MemTotal/ {print $2*1024; exit}' /proc/meminfo 2>/dev/null || echo $((16 * 1024 * 1024 * 1024)))"
_trust_mem_jobs=$(( _trust_mem_bytes / (5 * 1024 * 1024 * 1024) ))
[ "${_trust_mem_jobs}" -lt 1 ] && _trust_mem_jobs=1
if [ "${_trust_ncpu}" -lt "${_trust_mem_jobs}" ]; then _trust_default_jobs="${_trust_ncpu}"; else _trust_default_jobs="${_trust_mem_jobs}"; fi
JOBS="${TRUST_JOBS:-${_trust_default_jobs}}"
VERBOSE="${TRUST_VERBOSE:-0}"
RELEASE_GATE="${TRUST_RELEASE_GATE:-0}"
REQUIRE_TRUST_CARGO_ENV="${TRUST_REQUIRE_TARGO:-0}"
TRUST_TARGO_CMD=()
TRUST_TARGO_LABEL=""

# --- Options ---
LIB_ONLY=""
FILTER=""
CRATES=()
RELEASE=""

usage() {
    cat <<'USAGE'
dev-test.sh -- run tests for Trust verification crates

USAGE:
  ./scripts/dev-test.sh [OPTIONS] [CRATE...]

ARGUMENTS:
  CRATE...       One or more crate names to test (e.g., trust-vcgen trust-router).
                 If omitted, tests all workspace crates.

OPTIONS:
  --lib          Run library tests only (skip doc tests and integration tests).
  --filter STR   Filter test names by substring (passed to the selected Cargo
                 test runner after --).
  --release      Test in release mode.
  --list         List available trust crates and exit.
  --verbose      Verbose test output (equivalent to TRUST_VERBOSE=1).
  --help         Show this help message.

ENVIRONMENT:
  TRUST_CRATES_DIR   Path to crates workspace (default: <repo>/crates)
  TRUST_JOBS         Parallel job count (default: system CPU count)
  TRUST_VERBOSE      Set to 1 for verbose output
  TRUST_TARGO_BIN   Path to the stage2 Trust targo binary.
  TRUST_REQUIRE_TARGO
                     Set to 1 to require Trust targo. This is implied by
                     --release and TRUST_RELEASE_GATE=1.
  TRUST_TARGO_TRUST_BIN
                     Set BY this script. A run that includes
                     trust-integration-tests' integration tests (no CRATE list,
                     or trust-integration-tests, without --lib) first builds
                     targo-trust from this tree and exports a private copy,
                     replacing any value from the caller:
                     binary_to_trust_ir_e2e and scale_fixture_crate run it and
                     fail without it. A failed build fails the run. Other runs
                     pass the caller's value on; no test they run reads it.

EXAMPLES:
  ./scripts/dev-test.sh                         # All trust crate tests
  ./scripts/dev-test.sh trust-vcgen             # Single crate
  ./scripts/dev-test.sh trust-vcgen trust-types # Multiple crates
  ./scripts/dev-test.sh --lib                   # Library tests only (fastest)
  ./scripts/dev-test.sh --filter "bmc"          # Tests matching "bmc"
  ./scripts/dev-test.sh trust-router --lib      # Single crate, lib only

NOTES:
  - Tests run inside crates/ workspace, NOT the root rustc workspace.
  - Use --lib to skip doc tests for faster feedback.
  - CARGO_SKIP_CACHE=1 is set to avoid stale test cache results.
  - trust-mir-extract, trust-thir-lower and trust-witness require rustc_private
    and are excluded from the crates/ workspace; this script dispatches them to
    `x.py test --stage 1 crates/<name>` (bootstrap's per-crate test step), which
    RUNS their tests rather than declaring them untestable.
USAGE
    exit 0
}

# --- Parse arguments ---
while [[ $# -gt 0 ]]; do
    case "$1" in
        --lib)      LIB_ONLY="--lib"; shift ;;
        --filter)
            if [[ $# -lt 2 ]]; then
                echo "error: --filter requires an argument" >&2
                exit 1
            fi
            FILTER="$2"; shift 2
            ;;
        --release)  RELEASE="--release"; shift ;;
        --list)
            echo "Available trust crates:"
            # List crate directories that contain a Cargo.toml
            for d in "${CRATES_DIR}"/trust-*/; do
                if [[ -f "${d}Cargo.toml" ]]; then
                    echo "  $(basename "$d")"
                fi
            done
            exit 0
            ;;
        --verbose)  VERBOSE="1"; shift ;;
        --help|-h)  usage ;;
        -*)
            echo "error: unknown option: $1" >&2
            echo "Run with --help for usage." >&2
            exit 1
            ;;
        *)
            CRATES+=("$1"); shift
            ;;
    esac
done

# --- Logging ---
log() {
    echo "[dev-test] $(date '+%H:%M:%S') $*"
}

tool_runs() {
    local tool="$1"
    "$tool" -vV >/dev/null 2>&1 || "$tool" --version >/dev/null 2>&1
}

resolve_trust_cargo_cmd() {
    local allow_selector_fallback="${1:-0}"
    local candidate
    local selector_targo

    if [[ -n "${TRUST_TARGO_BIN:-}" ]]; then
        if [[ ! -x "$TRUST_TARGO_BIN" ]]; then
            echo "error: TRUST_TARGO_BIN is not executable: $TRUST_TARGO_BIN" >&2
            return 2
        fi
        if [[ "$(basename "$TRUST_TARGO_BIN")" != "targo" ]]; then
            echo "error: TRUST_TARGO_BIN must point at canonical targo, got: $TRUST_TARGO_BIN" >&2
            return 2
        fi
        if ! tool_runs "$TRUST_TARGO_BIN"; then
            echo "error: TRUST_TARGO_BIN is not a runnable Trust targo: $TRUST_TARGO_BIN" >&2
            return 2
        fi
        TRUST_TARGO_CMD=("$TRUST_TARGO_BIN" --unverified)
        TRUST_TARGO_LABEL="TRUST_TARGO_BIN=$TRUST_TARGO_BIN"
        return 0
    fi

    for candidate in "$REPO_ROOT"/build/*/stage2/bin "$REPO_ROOT/build/host/stage2/bin"; do
        if [[ -x "$candidate/targo" && -x "$candidate/trustc" ]] &&
            tool_runs "$candidate/targo" && tool_runs "$candidate/trustc"; then
            TRUST_TARGO_CMD=("$candidate/targo" --unverified)
            TRUST_TARGO_LABEL="$candidate/targo"
            return 0
        fi
    done

    if [[ "$allow_selector_fallback" != "1" ]]; then
        return 1
    fi

    selector_targo="$(command -v targo 2>/dev/null || true)"
    if [[ -n "$selector_targo" ]] && tool_runs "$selector_targo"; then
        TRUST_TARGO_CMD=("$selector_targo" --unverified)
        TRUST_TARGO_LABEL="targo developer selector ($selector_targo)"
        return 0
    fi

    if command -v rustup >/dev/null 2>&1 &&
        rustup run trust targo --version >/dev/null 2>&1; then
        TRUST_TARGO_CMD=(rustup run trust targo --unverified)
        TRUST_TARGO_LABEL="rustup run trust targo developer selector"
        return 0
    fi

    return 1
}

resolve_cargo_cmd() {
    local require_trust_cargo="$1"

    TRUST_TARGO_CMD=()
    TRUST_TARGO_LABEL=""

    if [[ "$require_trust_cargo" == "1" ]]; then
        if resolve_trust_cargo_cmd 0; then
            return 0
        fi
    elif resolve_trust_cargo_cmd 1; then
        return 0
    fi

    if [[ "$require_trust_cargo" == "1" || -n "${TRUST_TARGO_BIN:-}" ]]; then
        echo "error: Trust targo not found. Build/link stage2 Trust Cargo or set" \
            "TRUST_TARGO_BIN to the Trust-owned targo binary." >&2
        return 2
    fi

    if command -v targo >/dev/null 2>&1; then
        TRUST_TARGO_CMD=(targo --unverified)
        TRUST_TARGO_LABEL="targo developer fallback ($(command -v targo))"
        echo "DEV-FALLBACK: dev-test is using a PATH targo because stage2 Trust targo was not required." >&2
        echo "Set TRUST_REQUIRE_TARGO=1, TRUST_RELEASE_GATE=1, --release, or" \
            "TRUST_TARGO_BIN=/path/to/targo for stage2 Trust-owned targo." >&2
        return 0
    fi

    echo "error: no Trust targo was found." >&2
    return 2
}

# --- Environment ---
export CARGO_INCREMENTAL=1
export CARGO_SKIP_CACHE=1

case "$RELEASE_GATE" in
    0|1)
        ;;
    *)
        echo "error: TRUST_RELEASE_GATE must be 0 or 1 (got: $RELEASE_GATE)" >&2
        exit 2
        ;;
esac

case "$REQUIRE_TRUST_CARGO_ENV" in
    0|1)
        ;;
    *)
        echo "error: TRUST_REQUIRE_TARGO must be 0 or 1 (got: $REQUIRE_TRUST_CARGO_ENV)" >&2
        exit 2
        ;;
esac

if [[ ! -d "$CRATES_DIR" ]]; then
    echo "error: crates directory not found: $CRATES_DIR" >&2
    exit 1
fi

# --- Build test command ---
REQUIRE_TRUST_CARGO="$REQUIRE_TRUST_CARGO_ENV"
if [[ "$RELEASE_GATE" == "1" || -n "$RELEASE" ]]; then
    REQUIRE_TRUST_CARGO="1"
fi

CARGO_ARGS=(-j "$JOBS")
if [[ "$VERBOSE" == "1" ]]; then
    CARGO_ARGS+=(-v)
fi
if [[ -n "$RELEASE" ]]; then
    CARGO_ARGS+=("$RELEASE")
fi

# The three rustc_private consumers need bootstrap's compiler sysroot. They
# are root members but deliberately outside default-members; route explicit
# requests through x.py so their tests receive the required private libraries.
#
# Deliberately `x.py test`, NOT `x.py check`: check compiles the test targets but
# executes ZERO of them, so a check-dispatch would print green having run 0 of
# trust-mir-extract's ~487 tests — the ladder's own named anti-pattern ("a rung
# that misses the break is worse than no rung"), inside a test runner where no
# caveat sits in front of the reader.
#
# trust-spec-temporal is intentionally NOT in this list: it is not a
# rustc_private exclusion but a separate [workspace] root, and bootstrap has no
# step for it.
RUSTC_PRIVATE_CRATES=(trust-mir-extract trust-thir-lower trust-witness)
if [[ ${#CRATES[@]} -eq 0 ]]; then
    # An omitted crate list means *all* Trust crates, including the three
    # rustc_private crates that are deliberately outside `crates/`' workspace.
    # Keep CRATES empty so the Cargo invocation below still selects the full
    # ordinary workspace, but explicitly feed every excluded crate through
    # bootstrap first.
    DISPATCH_CANDIDATES=("${RUSTC_PRIVATE_CRATES[@]}")
else
    # Explicit selection remains narrow: dispatch only requested excluded
    # crates, and leave the other requested names for the Cargo invocation.
    DISPATCH_CANDIDATES=("${CRATES[@]}")
fi
REMAINING=()
XPY_RC=0
for crate in "${DISPATCH_CANDIDATES[@]}"; do
    dispatched=0
    for rp in "${RUSTC_PRIVATE_CRATES[@]}"; do
        if [[ "$crate" == "$rp" ]]; then
            log "dispatching ${crate} to bootstrap (rustc_private; not in the crates/ workspace)"
            if ! python3 "$REPO_ROOT/x.py" test --stage 1 "crates/${crate}"; then
                XPY_RC=1
            fi
            dispatched=1
            break
        fi
    done
    if [[ "$dispatched" == "0" ]]; then
        REMAINING+=("$crate")
    fi
done
if [[ "$XPY_RC" != "0" ]]; then
    echo "error: bootstrap-dispatched crate tests FAILED" >&2
    exit 1
fi
if [[ ${#CRATES[@]} -gt 0 ]]; then
    if [[ ${#REMAINING[@]} -eq 0 ]]; then
        # Every explicitly requested crate was bootstrap-dispatched and passed.
        exit 0
    fi
    CRATES=("${REMAINING[@]}")
fi

# Target selection: specific crates or full workspace
if [[ ${#CRATES[@]} -gt 0 ]]; then
    for crate in "${CRATES[@]}"; do
        # Validate crate exists
        if [[ ! -d "${CRATES_DIR}/${crate}" ]]; then
            echo "error: crate not found: ${crate}" >&2
            echo "Run with --list to see available crates." >&2
            exit 1
        fi
        CARGO_ARGS+=(-p "$crate")
    done
fi
# With no -p selection, Cargo uses the canonical developer default-members.

if [[ -n "$LIB_ONLY" ]]; then
    CARGO_ARGS+=("$LIB_ONLY")
fi

# Test name filter goes after --
TEST_ARGS=()
if [[ -n "$FILTER" ]]; then
    TEST_ARGS=(-- "$FILTER")
fi

# --- Run tests ---
resolve_cargo_cmd "$REQUIRE_TRUST_CARGO"
log "Cargo: ${TRUST_TARGO_LABEL}"
if [[ "$REQUIRE_TRUST_CARGO" == "1" ]]; then
    log "Trust targo required"
fi
if [[ ${#CRATES[@]} -gt 0 ]]; then
    log "Testing crates: ${CRATES[*]}"
else
    log "Testing all trust crates"
fi
if [[ -n "$LIB_ONLY" ]]; then
    log "Mode: library tests only"
fi
if [[ -n "$FILTER" ]]; then
    log "Filter: ${FILTER}"
fi

# trust-integration-tests' binary_to_trust_ir_e2e and scale_fixture_crate run
# the targo-trust TRUST_TARGO_TRUST_BIN names, and fail without it. Build it as
# scripts/check_crates_tests_scoped.py does, with its parser: the path is the
# one cargo's compiler-artifact message reports, and the tests get a private
# copy, which a build sharing the target dir cannot relink under them. A --lib
# run, or a crate list without trust-integration-tests, runs neither test.
NEEDS_TARGO_TRUST=0
if [[ -z "$LIB_ONLY" ]]; then
    if [[ ${#CRATES[@]} -eq 0 ]]; then
        NEEDS_TARGO_TRUST=1
    else
        for crate in "${CRATES[@]}"; do
            if [[ "$crate" == "trust-integration-tests" ]]; then
                NEEDS_TARGO_TRUST=1
            fi
        done
    fi
fi
if [[ "$NEEDS_TARGO_TRUST" == "1" ]]; then
    TARGO_TRUST_DIR="$(mktemp -d "${TMPDIR:-/tmp}/dev-test-targo-trust.XXXXXX")"
    trap 'rm -rf "${TARGO_TRUST_DIR:?}"' EXIT
    log "Building targo-trust for trust-integration-tests"
    if ! targo_trust_messages="$(cd "$REPO_ROOT" && "${TRUST_TARGO_CMD[@]}" build \
        --manifest-path targo-trust/Cargo.toml --bin targo-trust --locked \
        --message-format json-render-diagnostics)"; then
        echo "error: targo-trust failed to build; trust-integration-tests runs it and is never skipped." >&2
        exit 1
    fi
    targo_trust_built="$(printf '%s\n' "$targo_trust_messages" | python3 -c 'import importlib.util, sys
spec = importlib.util.spec_from_file_location("lane", sys.argv[1])
lane = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lane)
built = lane.targo_trust_executable(sys.stdin)
print(built or sys.exit("error: no compiler-artifact message named the targo-trust bin"))' \
        "$REPO_ROOT/scripts/check_crates_tests_scoped.py")"
    # -c: an APFS clone on macOS (no new disk for ~200 MB; cp falls back to
    # a copy where it cannot clone). GNU cp reads -c as an SELinux option.
    if [[ "$(uname -s)" == "Darwin" ]]; then
        cp -c -p "$targo_trust_built" "$TARGO_TRUST_DIR/targo-trust"
    else
        cp -p "$targo_trust_built" "$TARGO_TRUST_DIR/targo-trust"
    fi
    export TRUST_TARGO_TRUST_BIN="$TARGO_TRUST_DIR/targo-trust"
    log "targo-trust: built ${targo_trust_built}; the tests get the copy TRUST_TARGO_TRUST_BIN=${TRUST_TARGO_TRUST_BIN}"
fi

start_time=$(date +%s)

if [[ -n "$FILTER" ]]; then
    (cd "$CRATES_DIR" && "${TRUST_TARGO_CMD[@]}" test "${CARGO_ARGS[@]}" "${TEST_ARGS[@]}" 2>&1)
else
    (cd "$CRATES_DIR" && "${TRUST_TARGO_CMD[@]}" test "${CARGO_ARGS[@]}" 2>&1)
fi
exit_code=$?

end_time=$(date +%s)
elapsed=$(( end_time - start_time ))
minutes=$(( elapsed / 60 ))
seconds=$(( elapsed % 60 ))

if [[ $exit_code -eq 0 ]]; then
    log "Tests PASSED in ${minutes}m ${seconds}s."
else
    log "Tests FAILED after ${minutes}m ${seconds}s (exit code ${exit_code})."
    exit $exit_code
fi
