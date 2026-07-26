#!/usr/bin/env bash
# monitor-build-memory.sh - RSS monitor for build processes
#
# Polls RSS of a given PID every N seconds, records peak, warns if > threshold.
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

readonly LOG_FILE="${TRUST_RSS_LOG:-$REPO_ROOT/metrics/build-rss.log}"
mkdir -p "$(dirname "$LOG_FILE")"

# Validate PID exists
if ! kill -0 "$PID" 2>/dev/null; then
    echo "[rss-monitor] ERROR: PID $PID does not exist" >&2
    exit 1
fi

PEAK_RSS=0
SAMPLE_COUNT=0
START_TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

echo "[rss-monitor] Monitoring PID $PID (poll=${POLL_SEC}s, warn=${WARN_KB}KB)"

while kill -0 "$PID" 2>/dev/null; do
    # macOS ps reports RSS in KB
    RSS_KB=$(ps -o rss= -p "$PID" 2>/dev/null | tr -d ' ') || break
    if [[ -z "$RSS_KB" ]]; then
        break
    fi

    SAMPLE_COUNT=$((SAMPLE_COUNT + 1))

    if [[ "$RSS_KB" -gt "$PEAK_RSS" ]]; then
        PEAK_RSS="$RSS_KB"
    fi

    # Warn if over threshold
    if [[ "$RSS_KB" -gt "$WARN_KB" ]]; then
        WARN_MB=$((RSS_KB / 1024))
        THRESH_MB=$((WARN_KB / 1024))
        echo "[rss-monitor] WARNING: PID $PID RSS=${WARN_MB}MB exceeds ${THRESH_MB}MB threshold" >&2
    fi

    sleep "$POLL_SEC"
done

END_TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
PEAK_MB=$((PEAK_RSS / 1024))

# Append structured log entry
{
    echo "---"
    echo "pid: $PID"
    echo "start: $START_TS"
    echo "end: $END_TS"
    echo "samples: $SAMPLE_COUNT"
    echo "peak_rss_kb: $PEAK_RSS"
    echo "peak_rss_mb: $PEAK_MB"
    echo "warn_threshold_kb: $WARN_KB"
    echo "exceeded_threshold: $([ "$PEAK_RSS" -gt "$WARN_KB" ] && echo true || echo false)"
} >> "$LOG_FILE"

echo "[rss-monitor] PID $PID exited. Peak RSS: ${PEAK_MB}MB (${SAMPLE_COUNT} samples). Log: $LOG_FILE"
