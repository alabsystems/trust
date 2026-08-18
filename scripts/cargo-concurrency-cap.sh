#!/usr/bin/env bash
# cargo-concurrency-cap.sh - Concurrency limiter for host cargo builds
#
# Limits concurrent host cargo build/check/test processes using a mkdir-based
# semaphore, and explicitly caps each Cargo invocation's rustc job fanout.
# Automatically monitors aggregate RSS of the Cargo process tree.
# Works on macOS and Linux (no flock dependency).
#
# Usage:
#   ./scripts/cargo-concurrency-cap.sh build --release
#   ./scripts/cargo-concurrency-cap.sh test -p trust-vcgen
#   ./scripts/cargo-concurrency-cap.sh check --all
#
# Environment:
#   TRUST_MAX_CONCURRENT - Max parallel host Cargo processes (default: derived
#                          host job budget / jobs per invocation)
#   TRUST_CARGO_JOBS     - Rustc jobs per Cargo invocation (default: 1)
#                          TRUST_JOBS/CARGO_BUILD_JOBS are compatibility fallbacks
#   TRUST_LOCK_DIR       - Directory for lock files (default: /tmp/trust-cargo-locks)
#   TRUST_LOCK_TIMEOUT   - Seconds to wait for a lock slot (default: 600)
#   TRUST_RSS_MONITOR    - Set to "0" to disable RSS monitoring (default: enabled)
#
# Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

# --- Configuration ---

# Detect CPU count (macOS + Linux). Linux commonly has a `sysctl` binary, but
# it does not provide macOS's hw.ncpu key; testing only command availability
# silently reported 4 CPUs on the 20-CPU Spark host.
if [[ "$(uname -s 2>/dev/null || true)" == "Darwin" ]]; then
    NUM_CPUS="$(sysctl -n hw.ncpu 2>/dev/null || echo 4)"
elif command -v nproc >/dev/null 2>&1; then
    NUM_CPUS="$(nproc 2>/dev/null || echo 4)"
elif command -v getconf >/dev/null 2>&1; then
    NUM_CPUS="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)"
elif [[ -f /proc/cpuinfo ]]; then
    NUM_CPUS="$(grep -c '^processor' /proc/cpuinfo 2>/dev/null || echo 4)"
else
    NUM_CPUS=4
fi

is_positive_integer() {
    [[ "$1" =~ ^[1-9][0-9]*$ ]]
}

if ! is_positive_integer "$NUM_CPUS"; then
    echo "[cargo-cap] ERROR: detected invalid CPU count: $NUM_CPUS" >&2
    exit 2
fi

if [[ $# -eq 0 ]]; then
    # Keep the historical no-argument behavior: print resolved defaults and
    # usage without acquiring a semaphore slot or launching Cargo.
    NO_CARGO_ARGS=1
else
    NO_CARGO_ARGS=0
fi

# Cargo's CLI --jobs overrides CARGO_BUILD_JOBS. Canonicalize positive job
# arguments for the documented build/check/test commands so the cap cannot be
# silently bypassed. Arguments after `cargo test --` belong to the test binary.
CARGO_SUBCOMMAND="${1:-}"
CARGO_ARGS=()
PASSTHROUGH_ARGS=()
CLI_CARGO_JOBS=""
if [[ "$NO_CARGO_ARGS" -eq 0 ]] && [[ "$CARGO_SUBCOMMAND" =~ ^(build|check|test)$ ]]; then
    shift
    AFTER_SEPARATOR=0
    while [[ $# -gt 0 ]]; do
        if [[ "$AFTER_SEPARATOR" -eq 1 ]]; then
            PASSTHROUGH_ARGS+=("$1")
            shift
            continue
        fi
        case "$1" in
            --)
                AFTER_SEPARATOR=1
                shift
                ;;
            -j|--jobs)
                if [[ $# -lt 2 ]]; then
                    echo "[cargo-cap] ERROR: $1 requires a positive integer" >&2
                    exit 2
                fi
                CLI_CARGO_JOBS="$2"
                shift 2
                ;;
            --jobs=*)
                CLI_CARGO_JOBS="${1#--jobs=}"
                shift
                ;;
            -j*)
                CLI_CARGO_JOBS="${1#-j}"
                shift
                ;;
            *)
                CARGO_ARGS+=("$1")
                shift
                ;;
        esac
    done
fi

CARGO_JOBS="${TRUST_CARGO_JOBS:-${TRUST_JOBS:-${CARGO_BUILD_JOBS:-1}}}"
if [[ -n "$CLI_CARGO_JOBS" ]]; then
    CARGO_JOBS="$CLI_CARGO_JOBS"
fi
if ! is_positive_integer "$CARGO_JOBS"; then
    echo "[cargo-cap] ERROR: Cargo jobs must be a positive integer (got: $CARGO_JOBS)" >&2
    exit 2
fi

# Bound total declared rustc jobs by BOTH cores/2 and RAM (~5 GiB each). The
# previous semaphore counted Cargo parents but left every parent free to fan
# out to all CPUs, invalidating this memory calculation.
MEM_BYTES="$(sysctl -n hw.memsize 2>/dev/null || awk '/MemTotal/ {print $2*1024; exit}' /proc/meminfo 2>/dev/null || echo $((16 * 1024 * 1024 * 1024)))"
MEM_MAX=$((MEM_BYTES / (5 * 1024 * 1024 * 1024)))
[[ "$MEM_MAX" -lt 1 ]] && MEM_MAX=1
CPU_MAX=$((NUM_CPUS / 2))
[[ "$CPU_MAX" -lt 1 ]] && CPU_MAX=1
if [[ "$CPU_MAX" -lt "$MEM_MAX" ]]; then
    HOST_JOB_BUDGET="$CPU_MAX"
else
    HOST_JOB_BUDGET="$MEM_MAX"
fi

DEFAULT_MAX=$((HOST_JOB_BUDGET / CARGO_JOBS))
[[ "$DEFAULT_MAX" -lt 1 ]] && DEFAULT_MAX=1

MAX_CONCURRENT="${TRUST_MAX_CONCURRENT:-$DEFAULT_MAX}"
if ! is_positive_integer "$MAX_CONCURRENT"; then
    echo "[cargo-cap] ERROR: TRUST_MAX_CONCURRENT must be a positive integer (got: $MAX_CONCURRENT)" >&2
    exit 2
fi
if (( CARGO_JOBS > HOST_JOB_BUDGET )); then
    echo "[cargo-cap] ERROR: ${CARGO_JOBS} Cargo jobs exceed host budget ${HOST_JOB_BUDGET}" >&2
    exit 2
fi
if (( MAX_CONCURRENT * CARGO_JOBS > HOST_JOB_BUDGET )); then
    echo "[cargo-cap] ERROR: ${MAX_CONCURRENT} invocations x ${CARGO_JOBS} jobs exceed host budget ${HOST_JOB_BUDGET}" >&2
    exit 2
fi

readonly MAX_CONCURRENT
readonly CARGO_JOBS
readonly HOST_JOB_BUDGET
readonly LOCK_DIR="${TRUST_LOCK_DIR:-/tmp/trust-cargo-locks}"
readonly LOCK_TIMEOUT="${TRUST_LOCK_TIMEOUT:-600}"
readonly RSS_MONITOR="${TRUST_RSS_MONITOR:-1}"
if ! is_positive_integer "$LOCK_TIMEOUT"; then
    echo "[cargo-cap] ERROR: TRUST_LOCK_TIMEOUT must be a positive integer (got: $LOCK_TIMEOUT)" >&2
    exit 2
fi

CARGO_LAUNCH_ARGS=()
if [[ "$NO_CARGO_ARGS" -eq 0 ]] && [[ "$CARGO_SUBCOMMAND" =~ ^(build|check|test)$ ]]; then
    # Bash 3.2 (the macOS system shell) treats an expansion of an initialized
    # but empty array as an unbound variable under `set -u`. Append only when
    # non-empty so `cargo check` is as valid as `cargo check -p crate`.
    CARGO_LAUNCH_ARGS=("$CARGO_SUBCOMMAND" --jobs "$CARGO_JOBS")
    if [[ "${#CARGO_ARGS[@]}" -gt 0 ]]; then
        CARGO_LAUNCH_ARGS+=("${CARGO_ARGS[@]}")
    fi
    if [[ "$AFTER_SEPARATOR" -eq 1 ]]; then
        CARGO_LAUNCH_ARGS+=(--)
        if [[ "${#PASSTHROUGH_ARGS[@]}" -gt 0 ]]; then
            CARGO_LAUNCH_ARGS+=("${PASSTHROUGH_ARGS[@]}")
        fi
    fi
elif [[ "$NO_CARGO_ARGS" -eq 0 ]]; then
    # Preserve the historical arbitrary-Cargo-command surface. Commands other
    # than the documented build/check/test lanes still receive the environment
    # cap, but their argument ordering is left untouched for compatibility.
    CARGO_LAUNCH_ARGS=("$@")
fi

# Resolve paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MONITOR_SCRIPT="$SCRIPT_DIR/monitor-build-memory.sh"

# Find host cargo
REAL_CARGO=""
if [[ -n "${TRUST_REAL_CARGO:-}" ]] && [[ -x "${TRUST_REAL_CARGO}" ]]; then
    REAL_CARGO="$TRUST_REAL_CARGO"
fi
if [[ -z "$REAL_CARGO" ]]; then
    for loc in "$HOME/.cargo/bin/cargo" /opt/homebrew/bin/cargo /usr/local/bin/cargo /usr/bin/cargo; do
        if [[ -x "$loc" ]]; then
            REAL_CARGO="$loc"
            break
        fi
    done
fi
if [[ -z "$REAL_CARGO" ]]; then
    echo "[cargo-cap] ERROR: Cannot find host cargo binary" >&2
    exit 1
fi

# --- Semaphore implementation (mkdir-based, POSIX-portable) ---
#
# Each "slot" is a directory: $LOCK_DIR/slot_N/
# mkdir is atomic -- exactly one process succeeds.
# The lock holder writes its PID to slot_N/pid for stale lock detection.

mkdir -p "$LOCK_DIR"

ACQUIRED_SLOT=""

acquire_slot() {
    local waited=0
    while true; do
        for i in $(seq 0 $((MAX_CONCURRENT - 1))); do
            local slotdir="$LOCK_DIR/slot_$i"
            if mkdir "$slotdir" 2>/dev/null; then
                echo $$ > "$slotdir/pid"
                ACQUIRED_SLOT="$i"
                echo "$i"
                return 0
            fi
            # Check for stale locks (holder PID no longer exists)
            if [[ -f "$slotdir/pid" ]]; then
                local holder_pid
                holder_pid=$(cat "$slotdir/pid" 2>/dev/null || echo "")
                if [[ -n "$holder_pid" ]] && ! kill -0 "$holder_pid" 2>/dev/null; then
                    # Stale lock -- previous holder died
                    rm -rf "$slotdir" 2>/dev/null || true
                    if mkdir "$slotdir" 2>/dev/null; then
                        echo $$ > "$slotdir/pid"
                        ACQUIRED_SLOT="$i"
                        echo "$i"
                        return 0
                    fi
                fi
            fi
        done

        if [[ "$waited" -ge "$LOCK_TIMEOUT" ]]; then
            echo "[cargo-cap] ERROR: Timeout waiting for build slot after ${LOCK_TIMEOUT}s" >&2
            echo "[cargo-cap] ${MAX_CONCURRENT} concurrent builds already running" >&2
            return 1
        fi

        if [[ "$((waited % 30))" -eq 0 ]] && [[ "$waited" -gt 0 ]]; then
            echo "[cargo-cap] Waiting for build slot... (${waited}s/${LOCK_TIMEOUT}s, max=${MAX_CONCURRENT})" >&2
        fi

        sleep 2
        waited=$((waited + 2))
    done
}

release_slot() {
    local slot="$1"
    rm -rf "$LOCK_DIR/slot_$slot" 2>/dev/null || true
}

# --- Main ---

if [[ "$NO_CARGO_ARGS" -eq 1 ]]; then
    echo "Usage: cargo-concurrency-cap.sh <cargo-args...>" >&2
    echo "  e.g.: cargo-concurrency-cap.sh build --release" >&2
    echo "" >&2
    echo "Environment:" >&2
    echo "  TRUST_MAX_CONCURRENT=$MAX_CONCURRENT (host job budget=$HOST_JOB_BUDGET)" >&2
    echo "  TRUST_CARGO_JOBS=$CARGO_JOBS" >&2
    echo "  TRUST_LOCK_DIR=$LOCK_DIR" >&2
    echo "  TRUST_LOCK_TIMEOUT=${LOCK_TIMEOUT}s" >&2
    exit 0
fi

echo "[cargo-cap] Acquiring build slot (max concurrent: $MAX_CONCURRENT, jobs each: $CARGO_JOBS, host budget: $HOST_JOB_BUDGET)..." >&2
SLOT=$(acquire_slot)
printf '[cargo-cap] Acquired slot %s. Running host cargo:' "$SLOT" >&2
printf ' %q' "$REAL_CARGO" "${CARGO_LAUNCH_ARGS[@]}" >&2
printf '\n' >&2

# Cleanup on exit (including signals)
MONITOR_PID=""
cleanup() {
    if [[ -n "$MONITOR_PID" ]]; then
        kill "$MONITOR_PID" 2>/dev/null || true
        wait "$MONITOR_PID" 2>/dev/null || true
    fi
    release_slot "$SLOT"
    echo "[cargo-cap] Released slot $SLOT" >&2
}
trap cleanup EXIT INT TERM

# Launch host cargo
CARGO_BUILD_JOBS="$CARGO_JOBS" "$REAL_CARGO" "${CARGO_LAUNCH_ARGS[@]}" &
CARGO_PID=$!

# Launch RSS monitor in background (if enabled and script exists)
if [[ "$RSS_MONITOR" != "0" ]] && [[ -x "$MONITOR_SCRIPT" ]]; then
    "$MONITOR_SCRIPT" "$CARGO_PID" &
    MONITOR_PID=$!
fi

# Wait for host cargo to finish, propagate exit code
wait "$CARGO_PID"
EXIT_CODE=$?

exit "$EXIT_CODE"
