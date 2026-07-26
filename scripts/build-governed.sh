#!/usr/bin/env bash
# build-governed.sh — OOM-safe wrapper around scripts/build.sh.
#
# Two efficiency fixes over a bare `build.sh`:
#   1. Jobs sized from AVAILABLE (free) memory, not total. build.sh budgets
#      ~5 GiB/job off hw.memsize, so two concurrent builds (or a build + a
#      clippy gate) each pick ~ncpu jobs from the same total and OOM-kill each
#      other. Here -j is capped by what's actually free *right now*.
#   2. A live governor (build-mem-governor.sh) pauses/resumes the heaviest
#      compiler process under memory pressure, so a build under-estimate
#      degrades to "slower" instead of "SIGKILLed".
#
# Usage:  ./scripts/build-governed.sh [build.sh args...]
#   e.g.  ./scripts/build-governed.sh            # full stage2 build, governed
#         ./scripts/build-governed.sh stage1     # forwarded to build.sh
#
# Env:
#   TRUST_JOBS              Force job count (skips the free-mem calc)
#   TRUST_PER_JOB_GIB       GiB budgeted per job (default 5)
#   TRUST_GOV_*            Passed through to build-mem-governor.sh
#
# Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
readonly PER_JOB_GIB="${TRUST_PER_JOB_GIB:-5}"

avail_mib() {
  if [ -r /proc/meminfo ]; then
    awk '/MemAvailable/ {print int($2/1024); exit}' /proc/meminfo
    return
  fi
  local pagesize free inactive spec purge
  pagesize="$(sysctl -n hw.pagesize 2>/dev/null || echo 16384)"
  eval "$(vm_stat 2>/dev/null | awk -F: '
    /Pages free/        {gsub(/[ .]/,"",$2); print "free="$2}
    /Pages inactive/    {gsub(/[ .]/,"",$2); print "inactive="$2}
    /Pages speculative/ {gsub(/[ .]/,"",$2); print "spec="$2}
    /Pages purgeable/   {gsub(/[ .]/,"",$2); print "purge="$2}')"
  echo $(( ( ${free:-0} + ${inactive:-0} + ${spec:-0} + ${purge:-0} ) * pagesize / 1048576 ))
}

ncpu="$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 8)"
if [ -n "${TRUST_JOBS:-}" ]; then
  jobs="$TRUST_JOBS"
  src="TRUST_JOBS override"
else
  avail="$(avail_mib)"
  jobs=$(( avail / 1024 / PER_JOB_GIB ))
  [ "$jobs" -lt 1 ] && jobs=1
  [ "$jobs" -gt "$ncpu" ] && jobs="$ncpu"
  src="free=${avail}MiB / ${PER_JOB_GIB}GiB-per-job, capped at ${ncpu} cores"
fi
echo "[build-governed] jobs=$jobs ($src)" >&2

# Launch the real build (reusing build.sh's logic) with the free-mem job cap,
# then attach the governor to it.
TRUST_JOBS="$jobs" bash "$SCRIPT_DIR/build.sh" "$@" &
build_pid=$!

bash "$SCRIPT_DIR/build-mem-governor.sh" "$build_pid" &
gov_pid=$!

# Ensure the governor is reaped (and releases any paused procs) on our exit.
trap 'kill "$gov_pid" 2>/dev/null || true' INT TERM EXIT

wait "$build_pid"
rc=$?
kill "$gov_pid" 2>/dev/null || true
echo "[build-governed] build exited rc=$rc" >&2
exit "$rc"
