#!/usr/bin/env bash
# build-mem-governor.sh — OOM-safe dynamic throttle for Trust toolchain builds.
#
# The existing job sizing in build.sh budgets ~5 GiB/job off *total* RAM, which
# over-subscribes when two builds (or a build + a clippy gate) run concurrently:
# each picks ~ncpu jobs from the same total, the sum blows past physical RAM, and
# the OS OOM-kills compiler processes (SIGKILL) mid-build — losing the whole run.
#
# This governor watches *available* memory while a build runs and, when it dips
# below the critical floor, SIGSTOPs the largest compiler child (rustc/trustc/
# cc1/cc1plus) to relieve pressure — then SIGCONTs paused children once memory
# recovers. Pausing (not killing) means the build always finishes; it just
# serializes the heaviest steps under pressure instead of dying.
#
# Usage:
#   ./scripts/build-mem-governor.sh <ROOT_PID>
#   # typically launched alongside a build:  x.py build … & gov $! ; wait
#
# Env (all optional):
#   TRUST_GOV_CRITICAL_GIB  Pause heaviest child when avail < this   (default 6)
#   TRUST_GOV_RESUME_GIB    Resume paused children when avail >= this (default 12)
#   TRUST_GOV_POLL_SEC      Poll interval seconds                     (default 3)
#   TRUST_GOV_LOG           Log file (default: metrics/build-governor.log)
#
# Exits when ROOT_PID exits. Always SIGCONTs anything it paused (even on signal).
#
# Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.

set -uo pipefail

readonly ROOT_PID="${1:?Usage: build-mem-governor.sh <ROOT_PID>}"
readonly CRIT_GIB="${TRUST_GOV_CRITICAL_GIB:-6}"
readonly RESUME_GIB="${TRUST_GOV_RESUME_GIB:-12}"
readonly POLL_SEC="${TRUST_GOV_POLL_SEC:-3}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
readonly LOG="${TRUST_GOV_LOG:-$REPO_ROOT/metrics/build-governor.log}"
mkdir -p "$(dirname "$LOG")"

# Compiler processes worth pausing (the real memory hogs).
readonly HOG_RE='rustc|trustc|cc1plus|cc1|clang|lld|ld64'

# Track what we've paused so we always resume it.
PAUSED=""

log() { printf '%s [governor] %s\n' "$(date -u +%H:%M:%S)" "$*" | tee -a "$LOG" >&2; }

# Available memory in MiB — portable across macOS (vm_stat) and Linux (/proc).
avail_mib() {
  if [ -r /proc/meminfo ]; then
    awk '/MemAvailable/ {print int($2/1024); exit}' /proc/meminfo
    return
  fi
  # macOS: available ~= (free + inactive + speculative + purgeable) * pagesize
  local pagesize free inactive spec purge
  pagesize="$(sysctl -n hw.pagesize 2>/dev/null || echo 16384)"
  eval "$(vm_stat 2>/dev/null | awk -F: '
    /Pages free/        {gsub(/[ .]/,"",$2); print "free="$2}
    /Pages inactive/    {gsub(/[ .]/,"",$2); print "inactive="$2}
    /Pages speculative/ {gsub(/[ .]/,"",$2); print "spec="$2}
    /Pages purgeable/   {gsub(/[ .]/,"",$2); print "purge="$2}')"
  echo $(( ( ${free:-0} + ${inactive:-0} + ${spec:-0} + ${purge:-0} ) * pagesize / 1048576 ))
}

# Heaviest live hog by RSS among descendants of ROOT_PID (and the wider build).
# Returns "PID RSS_MIB" or empty. (Build subprocesses aren't all direct children
# of ROOT_PID under cargo/x.py, so match by command across the session.)
heaviest_hog() {
  ps -axo pid=,rss=,comm= 2>/dev/null \
    | awk -v re="$HOG_RE" '$3 ~ re && $1 != '"$$"' {print $1, int($2/1024)}' \
    | sort -k2 -nr | head -1
}

resume_all() {
  local p
  for p in $PAUSED; do kill -CONT "$p" 2>/dev/null || true; done
  [ -n "$PAUSED" ] && log "resumed all paused children on exit"
  PAUSED=""
}
trap 'resume_all; exit 0' INT TERM EXIT

# Initial advisory: report a free-memory-aware safe job count (callers can use it).
_ncpu="$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 8)"
_avail0="$(avail_mib)"
_safe_jobs=$(( _avail0 / 1024 / 5 ))   # ~5 GiB/job, from AVAILABLE (not total) RAM
[ "$_safe_jobs" -lt 1 ] && _safe_jobs=1
[ "$_safe_jobs" -gt "$_ncpu" ] && _safe_jobs=$_ncpu
log "start: root=$ROOT_PID avail=${_avail0}MiB ncpu=${_ncpu} -> free-mem-safe jobs≈${_safe_jobs} (crit=${CRIT_GIB}G resume=${RESUME_GIB}G)"

PAUSE_EVENTS=0
while kill -0 "$ROOT_PID" 2>/dev/null; do
  avail="$(avail_mib)"
  crit_mib=$(( CRIT_GIB * 1024 ))
  resume_mib=$(( RESUME_GIB * 1024 ))

  if [ "$avail" -lt "$crit_mib" ]; then
    # Under pressure: pause the single largest compiler process not already paused.
    read -r hp hr <<<"$(heaviest_hog)"
    if [ -n "${hp:-}" ] && ! printf '%s' " $PAUSED " | grep -q " $hp "; then
      if kill -STOP "$hp" 2>/dev/null; then
        PAUSED="$PAUSED $hp"
        PAUSE_EVENTS=$((PAUSE_EVENTS+1))
        log "PRESSURE avail=${avail}MiB < ${crit_mib} — paused PID $hp (${hr}MiB) [$PAUSE_EVENTS total]"
      fi
    fi
  elif [ "$avail" -ge "$resume_mib" ] && [ -n "$PAUSED" ]; then
    # Recovered: resume one paused child at a time (gentle ramp back up).
    local_p="${PAUSED##* }"
    PAUSED="${PAUSED% *}"
    kill -CONT "$local_p" 2>/dev/null || true
    log "RECOVER avail=${avail}MiB >= ${resume_mib} — resumed PID $local_p"
  fi

  # Reap zombies among paused set (process may have finished while stopped).
  newp=""
  for p in $PAUSED; do kill -0 "$p" 2>/dev/null && newp="$newp $p"; done
  PAUSED="$newp"

  sleep "$POLL_SEC"
done

resume_all
log "done: root $ROOT_PID exited; $PAUSE_EVENTS pause event(s)"
trap - INT TERM EXIT
exit 0
