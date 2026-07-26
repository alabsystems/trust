#!/usr/bin/env bash
# Trust development build script
# Optimized for fast iteration on the verification pipeline crates.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
#
# Usage:
#   ./scripts/dev-build.sh              # Build trust crates (explicit unverified lane)
#   ./scripts/dev-build.sh --check      # Type-check only, no linking
#   ./scripts/dev-build.sh --release    # Build in release mode
#   ./scripts/dev-build.sh --stage1     # Build stage 1 Trust compiler via x.py
#   ./scripts/dev-build.sh --help       # Show this help
#
# Environment:
#   TRUST_CRATES_DIR   Override crates directory (default: <repo>/crates)
#   TRUST_JOBS         Override parallel job count (default: system cores)
#   TRUST_VERBOSE      Set to 1 for verbose cargo output

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

# --- Modes ---
MODE="build"       # build | check | stage1
RELEASE=""
TIMINGS=""

usage() {
    cat <<'USAGE'
dev-build.sh -- fast development builds for Trust verification crates

USAGE:
  ./scripts/dev-build.sh [OPTIONS]

OPTIONS:
  --check       Type-check only (explicit unverified lane). No linking, fastest feedback.
  --release     Build in release mode (optimized, slower compile).
  --stage1      Build stage 1 trustc compiler via x.py (not trust crates).
  --timings     Generate cargo build timings report (cargo-timings.html).
  --verbose     Verbose cargo output (equivalent to TRUST_VERBOSE=1).
  --help        Show this help message.

ENVIRONMENT:
  TRUST_CRATES_DIR   Path to crates workspace (default: <repo>/crates)
  TRUST_JOBS         Parallel job count (default: system CPU count)
  TRUST_VERBOSE      Set to 1 for verbose output

EXAMPLES:
  ./scripts/dev-build.sh                # Incremental build, trust crates
  ./scripts/dev-build.sh --check        # Fast type-check (no codegen)
  ./scripts/dev-build.sh --release      # Optimized build
  ./scripts/dev-build.sh --stage1       # Build stage 1 compiler
  TRUST_JOBS=4 ./scripts/dev-build.sh   # Limit parallelism

NOTES:
  - Builds run inside crates/ workspace, not the root rustc workspace.
  - CARGO_INCREMENTAL=1 is set automatically for faster rebuilds.
  - The cargo build cache wrapper (CARGO_SKIP_CACHE) is set to avoid stale results.
USAGE
    exit 0
}

# --- Parse arguments ---
while [[ $# -gt 0 ]]; do
    case "$1" in
        --check)    MODE="check";   shift ;;
        --release)  RELEASE="--release"; shift ;;
        --stage1)   MODE="stage1";  shift ;;
        --timings)  TIMINGS="--timings"; shift ;;
        --verbose)  VERBOSE="1";    shift ;;
        --help|-h)  usage ;;
        *)
            echo "error: unknown option: $1" >&2
            echo "Run with --help for usage." >&2
            exit 1
            ;;
    esac
done

# --- Logging ---
log() {
    echo "[dev-build] $(date '+%H:%M:%S') $*"
}

# --- Environment for optimal builds ---
export CARGO_INCREMENTAL=1
export CARGO_SKIP_CACHE=1

CARGO_FLAGS="-j ${JOBS}"
if [[ "$VERBOSE" == "1" ]]; then
    CARGO_FLAGS="${CARGO_FLAGS} -v"
fi
if [[ -n "$RELEASE" ]]; then
    CARGO_FLAGS="${CARGO_FLAGS} ${RELEASE}"
fi
if [[ -n "$TIMINGS" ]]; then
    CARGO_FLAGS="${CARGO_FLAGS} ${TIMINGS}"
fi

# --- Build functions ---

build_trust_crates() {
    local cmd="$1"
    local label="$2"

    if [[ ! -d "$CRATES_DIR" ]]; then
        echo "error: crates directory not found: $CRATES_DIR" >&2
        exit 1
    fi

    log "${label} trust crates (${JOBS} jobs)..."
    local start_time
    start_time=$(date +%s)

    # shellcheck disable=SC2086
    (cd "$CRATES_DIR" && targo --unverified ${cmd} ${CARGO_FLAGS} --workspace 2>&1)
    local exit_code=$?

    local end_time
    end_time=$(date +%s)
    local elapsed=$(( end_time - start_time ))
    local minutes=$(( elapsed / 60 ))
    local seconds=$(( elapsed % 60 ))

    if [[ $exit_code -eq 0 ]]; then
        log "${label} complete in ${minutes}m ${seconds}s."
    else
        log "${label} FAILED after ${minutes}m ${seconds}s (exit code ${exit_code})."
        exit $exit_code
    fi
}

build_stage1() {
    log "Building stage 1 compiler via x.py (${JOBS} jobs)..."
    local start_time
    start_time=$(date +%s)

    local xpy_flags="-j ${JOBS}"
    if [[ "$VERBOSE" == "1" ]]; then
        xpy_flags="${xpy_flags} -v"
    fi

    # shellcheck disable=SC2086
    (cd "$REPO_ROOT" && python3 x.py build --stage 1 ${xpy_flags} 2>&1)
    local exit_code=$?

    local end_time
    end_time=$(date +%s)
    local elapsed=$(( end_time - start_time ))
    local minutes=$(( elapsed / 60 ))
    local seconds=$(( elapsed % 60 ))

    if [[ $exit_code -eq 0 ]]; then
        log "Stage 1 build complete in ${minutes}m ${seconds}s."
        # Show compiler location
        local compiler
        compiler=$(find "${REPO_ROOT}/build" -name trustc -type f -perm +111 2>/dev/null | head -1)
        if [[ -n "$compiler" ]]; then
            log "Compiler: ${compiler}"
        fi
    else
        log "Stage 1 build FAILED after ${minutes}m ${seconds}s (exit code ${exit_code})."
        exit $exit_code
    fi
}

# --- Main ---
case "$MODE" in
    check)
        build_trust_crates "check" "Type-checking"
        ;;
    build)
        build_trust_crates "build" "Building"
        ;;
    stage1)
        build_stage1
        ;;
esac
