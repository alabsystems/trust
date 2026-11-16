#!/usr/bin/env bash
# The detector proofs for `scripts/machine_preflight.sh`.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# Two defects, both measured on this machine before they were fixed:
#
#  * PACKAGE-CACHE: every process with a cargo cache lock file OPEN was graded
#    as a HOLDER, and every idle one past five minutes as "wedged, blocking
#    every cargo/targo". A process WAITING for the lock has the file open too,
#    and every running build holds `.package-cache-mutate` SHARED for its whole
#    life, which blocks no build (2026-09-27: ten such builds were reported as
#    ten wedges while `.package-cache` was free).
#  * SELF-TEST: the spinner had to exceed a fixed 40% CPU three seconds after
#    it started. At load 41-51 on 18 cores a pure busy-loop gets its fair share
#    and no more, so the self-test declared a working detector broken.
#
# The lock cases run real flock holders and waiters (perl) against a throwaway
# CARGO_HOME, so the verdict under test is about real kernel lock state. The
# wedge age is overridden to 0 s so a case does not wait five minutes.
set -euo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
PREFLIGHT="$REPO_ROOT/scripts/machine_preflight.sh"
TMP=$(mktemp -d)
PIDS=()
cleanup() {
  release_all
  rm -rf "$TMP"
}
trap cleanup EXIT

PASSED=0
fail() { printf 'machine_preflight_test: %s\n' "$*" >&2; exit 1; }
ok()   { PASSED=$((PASSED + 1)); printf '  ok  %s\n' "$*"; }

[ -f "$PREFLIGHT" ] || fail "preflight is missing: $PREFLIGHT"
command -v perl >/dev/null 2>&1 || fail "perl is required to hold real flocks"

export CARGO_HOME="$TMP/cargo"
mkdir -p "$CARGO_HOME"
: >"$CARGO_HOME/.package-cache"
: >"$CARGO_HOME/.package-cache-mutate"

# hold MODE FILE [spin]: open FILE, take a flock (ex|sh|none), then idle or spin.
hold() {
  local mode=$1 file=$2 spin=${3:-idle}
  perl -MFcntl=:flock -e '
    my ($mode, $file, $spin) = @ARGV;
    open(my $f, "<", $file) or die "open $file: $!";
    flock($f, $mode eq "ex" ? LOCK_EX : LOCK_SH) or die "flock: $!" if $mode ne "none";
    if ($spin eq "spin") { my $t = time + 60; 1 while time < $t } else { sleep 60 }
  ' "$mode" "$file" "$spin" &
  PIDS+=("$!")
}
release_all() {
  for p in "${PIDS[@]:-}"; do
    [ -n "$p" ] || continue
    kill -9 "$p" 2>/dev/null || true
    wait "$p" 2>/dev/null || true
  done
  PIDS=()
}
# The cache section of one preflight run.
cache_section() {
  # The preflight's own exit status reflects the whole machine (other
  # sections may report real problems); only this section is under test.
  { MACHINE_PREFLIGHT_WEDGE_MIN_SECS=0 sh "$PREFLIGHT" "$@" 2>&1 || true; } \
    | awk '/^== cargo package-cache lock ==/ {on=1; next} /^== / {on=0} on'
}
problems() { printf '%s\n' "$1" | grep -c '^PROBLEM' || true; }

# --- A: builds holding .package-cache-mutate SHARED block nobody ---------------
hold sh "$CARGO_HOME/.package-cache-mutate"
hold sh "$CARGO_HOME/.package-cache-mutate"
hold sh "$CARGO_HOME/.package-cache-mutate"
sleep 2
OUT=$(cache_section)
[ "$(problems "$OUT")" -eq 0 ] || fail "shared holders were reported as wedges:
$OUT"
printf '%s\n' "$OUT" | grep -q '.package-cache-mutate: held SHARED' \
  || fail "shared state not reported:
$OUT"
ok "three idle SHARED holders of -mutate are not wedges"
release_all

# --- B: a file that is merely OPEN is not a held lock --------------------------
hold none "$CARGO_HOME/.package-cache"
sleep 2
OUT=$(cache_section)
[ "$(problems "$OUT")" -eq 0 ] || fail "an idle process with the file open was reported as a holder:
$OUT"
printf '%s\n' "$OUT" | grep -q '.package-cache: unlocked' || fail "unlocked state not reported:
$OUT"
ok "an idle opener of an unlocked file is not a wedge"
release_all

# --- C: a busy holder with an idle WAITER queued behind it -------------------
hold ex "$CARGO_HOME/.package-cache" spin
sleep 1
hold ex "$CARGO_HOME/.package-cache"   # blocks in flock: a waiter
sleep 2
OUT=$(cache_section)
[ "$(problems "$OUT")" -eq 0 ] || fail "an idle waiter behind a working holder was reported as a wedged holder:
$OUT"
printf '%s\n' "$OUT" | grep -q 'held EXCLUSIVE and a process that could be its holder is making progress' \
  || fail "the making-progress verdict is missing:
$OUT"
ok "a waiter queued behind a working holder is not a wedge"
release_all

# --- D: an idle exclusive holder with a waiter: ONE wedge, not two -----------
hold ex "$CARGO_HOME/.package-cache"
sleep 1
hold ex "$CARGO_HOME/.package-cache"
sleep 2
OUT=$(cache_section)
[ "$(problems "$OUT")" -eq 1 ] || fail "an idle exclusive holder with one waiter must be exactly one problem:
$OUT"
printf '%s\n' "$OUT" | grep -q 'EXCLUSIVE' || fail "the wedge does not say the lock is exclusive:
$OUT"
ok "an idle exclusive holder is one wedge, however many wait behind it"
release_all

# --- E: the self-test's detector fires at the machine's current load ---------
OUT=$(sh "$PREFLIGHT" --self-test 2>&1 || true)
printf '%s\n' "$OUT" | grep -q 'detector fired on a live spinner' \
  || fail "the self-test's spinner was not detected (load: $(uptime)):
$(printf '%s\n' "$OUT" | sed -n '/orphaned CPU hogs/p;/self-test/,$p')"
ok "the self-test detects its spinner at the current load"

printf 'machine_preflight_test: %d checks passed\n' "$PASSED"
