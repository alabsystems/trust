#!/usr/bin/env bash
# cargo-concurrency-cap.sh - Concurrency limiter for host cargo builds
#
# Limits concurrent host cargo build/check/test processes using mkdir-based semaphore.
# Automatically monitors RSS of the host cargo process and logs peak memory.
# Works on macOS and Linux (no flock dependency).
#
# Usage:
#   ./scripts/cargo-concurrency-cap.sh build --release
#   ./scripts/cargo-concurrency-cap.sh test -p trust-vcgen
#   ./scripts/cargo-concurrency-cap.sh check --all
#
# Environment:
#   TRUST_MAX_CONCURRENT - Max parallel host cargo processes (default: num_cpus / 2)
#   TRUST_LOCK_DIR       - Directory for lock files (default: /tmp/trust-cargo-locks)
#   TRUST_LOCK_TIMEOUT   - Seconds to wait for a lock slot (default: 600)
#   TRUST_RSS_MONITOR    - Set to "0" to disable RSS monitoring (default: enabled)
#
# Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

# --- Configuration ---

# Detect CPU count (macOS + Linux)
if command -v sysctl &>/dev/null; then
    NUM_CPUS=$(sysctl -n hw.ncpu 2>/dev/null || echo 4)
elif [[ -f /proc/cpuinfo ]]; then
    NUM_CPUS=$(grep -c '^processor' /proc/cpuinfo 2>/dev/null || echo 4)
else
    NUM_CPUS=4
fi

# Cap concurrent cargo invocations by BOTH cores/2 and RAM (~5 GB each). On a
# 24 GB host NUM_CPUS/2 alone (=7) lets concurrent cargo builds blow past RAM
# and panic the machine; bound by memory too. Override with TRUST_MAX_CONCURRENT.
MEM_BYTES="$(sysctl -n hw.memsize 2>/dev/null || awk '/MemTotal/ {print $2*1024; exit}' /proc/meminfo 2>/dev/null || echo $((16 * 1024 * 1024 * 1024)))"
MEM_MAX=$((MEM_BYTES / (5 * 1024 * 1024 * 1024)))
[[ "$MEM_MAX" -lt 1 ]] && MEM_MAX=1
CPU_MAX=$((NUM_CPUS / 2))
[[ "$CPU_MAX" -lt 1 ]] && CPU_MAX=1
if [[ "$CPU_MAX" -lt "$MEM_MAX" ]]; then DEFAULT_MAX="$CPU_MAX"; else DEFAULT_MAX="$MEM_MAX"; fi

readonly MAX_CONCURRENT="${TRUST_MAX_CONCURRENT:-$DEFAULT_MAX}"
readonly LOCK_DIR="${TRUST_LOCK_DIR:-/tmp/trust-cargo-locks}"
readonly LOCK_TIMEOUT="${TRUST_LOCK_TIMEOUT:-600}"
readonly RSS_MONITOR="${TRUST_RSS_MONITOR:-1}"

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

if [[ $# -eq 0 ]]; then
    echo "Usage: cargo-concurrency-cap.sh <cargo-args...>" >&2
    echo "  e.g.: cargo-concurrency-cap.sh build --release" >&2
    echo "" >&2
    echo "Environment:" >&2
    echo "  TRUST_MAX_CONCURRENT=$MAX_CONCURRENT (num_cpus/2=$((NUM_CPUS/2)))" >&2
    echo "  TRUST_LOCK_DIR=$LOCK_DIR" >&2
    echo "  TRUST_LOCK_TIMEOUT=${LOCK_TIMEOUT}s" >&2
    exit 0
fi

echo "[cargo-cap] Acquiring build slot (max concurrent: $MAX_CONCURRENT)..." >&2
SLOT=$(acquire_slot)
echo "[cargo-cap] Acquired slot $SLOT. Running host cargo: $REAL_CARGO $*" >&2

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
"$REAL_CARGO" "$@" &
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
