#!/usr/bin/env bash
# Trust temporal/ty gate — `#[trust::terminating]` state-machine convergence.
#
# Engages the ty (temporal) lane end-to-end: Trust extracts an enum-step
# transition machine `fn step(s: E) -> E { match s { .. } }` from MIR and
# exhaustively model-checks the finite transition graph for a non-trivial cycle.
# `#[trust::terminating]` asserts the machine CONVERGES (reaches a fixed point
# from every state — no livelock). This is a property rustc cannot express.
#
#   temporal/proved/*.rs  -> convergent machine: compiles, emits
#                            "`#[trust::terminating]` PROVED" (exit 0).
#   temporal/mutant/*.rs  -> livelocking machine (a >=2-state cycle): Trust
#                            REJECTS the assertion with a build error
#                            "`#[trust::terminating]` FAILED" (exit != 0),
#                            proving the temporal check is non-vacuous.
#
# Verification is batteries-on. No ay subprocess is needed — the model check
# is a pure finite-state graph analysis.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"
FIX="$REPO_ROOT/tests/trust-falsification/temporal"
# The shims dir must EXIST: a missing LIBRARY_PATH entry makes ld warn
# "search path not found", which leaks into diagnostics-sensitive tests.
mkdir -p /tmp/trust_link_shims
export LIBRARY_PATH="/tmp/trust_link_shims:/opt/homebrew/opt/z3/lib:${LIBRARY_PATH:-}"

if [ ! -x "$TRUSTC" ]; then
  echo "ERROR: trustc not found at $TRUSTC"
  exit 2
fi

TMPDIR_GATE="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_GATE"' EXIT

# Compile a fixture -> echo "exit_code|||output".
run_of() {
  local out
  out="$("$TRUSTC" --edition 2021 --crate-type lib "$1" \
        -o "$TMPDIR_GATE/$(basename "$1").rlib" 2>&1)"
  printf '%s|||%s' "$?" "$out"
}

failed=0

# A proved fixture must compile (exit 0) and emit a temporal `PROVED` verdict;
# a mutant must be REJECTED (exit != 0) with a temporal `FAILED` verdict. The
# assertion kind (terminating / reachable) is matched generically.
for f in "$FIX"/proved/*.rs; do
  [ -e "$f" ] || continue
  res="$(run_of "$f")"; code="${res%%|||*}"; out="${res#*|||}"
  if [ "$code" -eq 0 ] && grep -qE '`#\[trust::(terminating|reachable)\]` PROVED' <<<"$out"; then
    echo "PASS  proved   $(basename "$f")  — temporal property PROVED by exhaustive model checking"
  else
    echo "FAIL  proved   $(basename "$f")  — expected exit 0 + a temporal PROVED (got exit $code)"
    failed=1
  fi
done

for f in "$FIX"/mutant/*.rs; do
  [ -e "$f" ] || continue
  res="$(run_of "$f")"; code="${res%%|||*}"; out="${res#*|||}"
  if [ "$code" -ne 0 ] && grep -qE '`#\[trust::(terminating|reachable)\]` FAILED' <<<"$out"; then
    echo "PASS  mutant   $(basename "$f")  — sound: temporal property violation REJECTED (build error)"
  else
    echo "FAIL  mutant   $(basename "$f")  — VACUOUS: temporal violation not rejected (got exit $code)"
    failed=1
  fi
done

if [ "$failed" -eq 0 ]; then
  echo "TEMPORAL GATE: GREEN — convergent machines prove terminating, livelocks are rejected (ty engaged)"
  exit 0
else
  echo "TEMPORAL GATE: RED — temporal/ty convergence check regressed"
  exit 1
fi
