#!/usr/bin/env bash
# monitor-build-memory.sh - RSS monitor for build processes
#
# Polls aggregate RSS of a PID and all descendants every N seconds, records the
# sampled peak, and warns if it exceeds a threshold.
# Output goes to metrics/build-rss.log (append mode).
#
# Usage:
#   ./scripts/monitor-build-memory.sh <PID> [POLL_INTERVAL_SEC] [WARN_THRESHOLD_KB]
#
# Environment:
#   TRUST_RSS_LOG       - Log file path (default: metrics/build-rss.log)
#   TRUST_RSS_INTERVAL  - Poll interval in seconds (default: 10)
#   TRUST_RSS_WARN_KB   - Warning threshold in KB (default: 8388608 = 8GB)
#
# Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

readonly PID="${1:?Usage: monitor-build-memory.sh <PID> [POLL_SEC] [WARN_KB]}"
readonly POLL_SEC="${2:-${TRUST_RSS_INTERVAL:-10}}"
readonly WARN_KB="${3:-${TRUST_RSS_WARN_KB:-8388608}}"  # 8GB in KB

# Resolve repo root (script lives in scripts/)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
# shellcheck source=lib/process_tree.sh
. "$SCRIPT_DIR/lib/process_tree.sh"

readonly LOG_FILE="${TRUST_RSS_LOG:-$REPO_ROOT/metrics/build-rss.log}"
mkdir -p "$(dirname "$LOG_FILE")"

# Validate PID exists
if ! kill -0 "$PID" 2>/dev/null; then
    echo "[rss-monitor] ERROR: PID $PID does not exist" >&2
    exit 1
fi

PEAK_RSS=0
PEAK_PROCESS_COUNT=0
SAMPLE_COUNT=0
START_TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
STOP_REQUESTED=0
SLEEP_PID=""

request_stop() {
    STOP_REQUESTED=1
    if [[ -n "$SLEEP_PID" ]]; then
        kill "$SLEEP_PID" 2>/dev/null || true
    fi
}
trap request_stop INT TERM

echo "[rss-monitor] Monitoring process tree rooted at PID $PID (poll=${POLL_SEC}s, warn=${WARN_KB}KB)"

while [[ "$STOP_REQUESTED" -eq 0 ]] && kill -0 "$PID" 2>/dev/null; do
    # macOS and Linux ps report RSS in KB. Sum one synchronized snapshot of
    # Cargo/the build root and all descendants; the tiny parent alone is not a
    # meaningful build-memory measurement.
    TREE_SAMPLE="$(trust_process_tree_rss_kb "$PID")" || break
    if [[ -z "$TREE_SAMPLE" ]]; then
        break
    fi
    read -r RSS_KB PROCESS_COUNT <<<"$TREE_SAMPLE"

    SAMPLE_COUNT=$((SAMPLE_COUNT + 1))

    if [[ "$RSS_KB" -gt "$PEAK_RSS" ]]; then
        PEAK_RSS="$RSS_KB"
        PEAK_PROCESS_COUNT="$PROCESS_COUNT"
    fi

    # Warn if over threshold
    if [[ "$RSS_KB" -gt "$WARN_KB" ]]; then
        WARN_MB=$((RSS_KB / 1024))
        THRESH_MB=$((WARN_KB / 1024))
        echo "[rss-monitor] WARNING: PID $PID process-tree RSS=${WARN_MB}MB exceeds ${THRESH_MB}MB threshold" >&2
    fi

    sleep "$POLL_SEC" &
    SLEEP_PID=$!
    if [[ "$STOP_REQUESTED" -ne 0 ]]; then
        kill "$SLEEP_PID" 2>/dev/null || true
    fi
    wait "$SLEEP_PID" 2>/dev/null || true
    SLEEP_PID=""
done

trap - INT TERM

END_TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
PEAK_MB=$((PEAK_RSS / 1024))

# Append structured log entry
{
    echo "---"
    echo "pid: $PID"
    echo "scope: process_tree"
    echo "start: $START_TS"
    echo "end: $END_TS"
    echo "samples: $SAMPLE_COUNT"
    echo "peak_rss_kb: $PEAK_RSS"
    echo "peak_rss_mb: $PEAK_MB"
    echo "peak_process_count: $PEAK_PROCESS_COUNT"
    echo "warn_threshold_kb: $WARN_KB"
    echo "exceeded_threshold: $([ "$PEAK_RSS" -gt "$WARN_KB" ] && echo true || echo false)"
} >> "$LOG_FILE"

echo "[rss-monitor] PID $PID monitoring ended. Peak process-tree RSS: ${PEAK_MB}MB (${SAMPLE_COUNT} samples). Log: $LOG_FILE"
