#!/bin/zsh
# Run a trust-ir producer scorecard sweep UNDER A MEASUREMENT SENTINEL.
#
#   usage: scripts/run_measurement_sweep.sh <out-dir-name> "<purpose>" [sample-size]
#   e.g.   scripts/run_measurement_sweep.sh postbuild-soundness "dyn false-PROVE fix + slice 20"
#
# WHY THIS EXISTS
#
# A wait is not a lock. `pgrep -x bootstrap` only sees a build that has ALREADY started, and
# nothing in the tree expressed the converse: that a 37-minute measurement is in flight and the
# binary underneath it must not move. `x.py build` deletes `stage1/bin/rustc` at start, so a
# build launched during a sweep kills it.
#
# Measured this session: slice 20 shipped with its corpus sweep never run because it was killed
# three times this way; a further sweep died at 4m27s and another at 37s. That is the entire
# reason `postbuild-slice20-control` is not a valid post-slice-20 control.
#
# So this publishes `.trust-measurement-in-flight` at the repo root. The contract is one line:
# READ IT BEFORE YOU BUILD. It carries pid, start time, purpose and expected duration, so a lane
# that finds it can decide to wait rather than guess.
#
# THE TRAP IS THE LOAD-BEARING HALF. A sentinel that outlives its sweep blocks every other lane
# indefinitely — a worse failure than the one it prevents. It is removed on success, failure,
# INT and TERM alike, and `--force` exists for the case where a crash left one behind.
set -u

# Default to THIS script's own repo rather than a hardcoded home path: the
# publication boundary bans absolute /Users/... paths in exported content, and
# the sweep is exported. TRUST_REPO still overrides for out-of-tree runs.
REPO=${TRUST_REPO:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}
SENTINEL=$REPO/.trust-measurement-in-flight
RUSTC=${TRUST_RUSTC:-$REPO/build/aarch64-apple-darwin/stage1/bin/rustc}

if [ "${1:-}" = "--force" ]; then
  rm -f "$SENTINEL"; echo "removed a stale sentinel"; shift
fi

OUT_NAME=${1:?usage: run_measurement_sweep.sh <out-dir-name> "<purpose>" [sample-size]}
PURPOSE=${2:-unspecified}
SIZE=${3:-2000}
OUT=$REPO/reports/trust-ir-producer-baseline-2026-07-01/$OUT_NAME

# --- refusals, cheapest first -------------------------------------------------
if [ -e "$SENTINEL" ]; then
  echo "REFUSING: a measurement is already in flight —"; sed 's/^/    /' "$SENTINEL"
  echo "  (if that pid is dead, re-run with --force)"; exit 3
fi
if pgrep -x bootstrap >/dev/null; then
  echo "REFUSING: bootstrap is running; a sweep started now would be killed by it"; exit 3
fi
if [ ! -x "$RUSTC" ]; then
  echo "REFUSING: $RUSTC is missing (x.py deletes it at build start)"; exit 3
fi

# A rebuilt driver over an unstaged sysroot answers E0463 on EVERY file, which the scorecard
# faithfully records as ~2000 compile failures rather than "not ready". That has already produced
# one bogus measurement. Prove compilability before reserving the window.
#
# `-Z trust-verify=off` IS LOAD-BEARING, and omitting it made this gate refuse unconditionally.
# trustc is batteries-on: with verification live, `println!` raises an unproven panic-freedom
# obligation for an absent callee (std's body is not in the lowered bundle), the fail-closed
# default turns that into a BUILD ERROR, and the probe exits non-zero. That is the verifier
# working correctly — so the check reported "stage1 cannot compile hello-world" on a perfectly
# healthy stage1, every time, and no sweep could ever start. Measured 2026-08-19: exit 1 with
# "an unproven panic-freedom obligation for a call to an absent callee ... is a build error".
#
# The probe must therefore invoke the compiler THE WAY THE SWEEP DOES. The scorecard passes
# `-Z trust-verify=off` on every sampled file (producer-only measurement; the trust-ir hook is
# independent of the verifier), so a smoke test that omits it is not testing the thing that is
# about to run. It also still catches the case it exists for: an unstaged sysroot answers E0463
# whether or not the verifier is on.
TMP=$(mktemp -d)
printf 'fn main(){println!("ok");}\n' > "$TMP/hw.rs"
if ! "$RUSTC" -Z trust-verify=off --edition 2021 --emit=metadata --crate-type lib \
       -o "$TMP/hw.rmeta" "$TMP/hw.rs" >/dev/null 2>&1; then
  echo "REFUSING: stage1 rustc does not compile hello-world (E0463 / unstaged sysroot?)"
  rm -rf "$TMP"; exit 3
fi
rm -rf "$TMP"

cleanup() { rm -f "$SENTINEL"; }
trap cleanup EXIT INT TERM

{
  echo "pid=$$"
  echo "started=$(date '+%Y-%m-%d %H:%M:%S')"
  echo "purpose=$PURPOSE"
  echo "out=$OUT"
  echo "rustc=$("$RUSTC" --version)"
  echo "sample_size=$SIZE"
  echo "expected_minutes=~37"
  echo "contract=DO NOT run x.py while this file exists; it deletes stage1/bin/rustc"
} > "$SENTINEL"

echo "=== measurement sentinel published:"; sed 's/^/    /' "$SENTINEL"; echo

python3 "$REPO/scripts/trust_ir_producer_scorecard.py" \
  --trustc "$RUSTC" --out-dir "$OUT" \
  --sample-size "$SIZE" --jobs 8 --timeout 60
rc=$?
echo "=== sweep exited rc=$rc at $(date '+%H:%M:%S'); sentinel released"
exit $rc
