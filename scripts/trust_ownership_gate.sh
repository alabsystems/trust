#!/usr/bin/env bash
# Trust ownership / trust-vc gate — `#[trust::must_consume]` linearity.
#
# Engages the trust-vc (ownership) lane end-to-end. Rust's AFFINE type system
# lets an owned value be silently DROPPED; `#[trust::must_consume]` asserts
# LINEARITY — the owned by-value parameter must be MOVED OUT (consumed) on every
# path to a return, never dropped. Trust verifies it with a sound forward
# reachability over the MIR move dataflow (a property rustc cannot express).
#
#   ownership/proved/*.rs  -> the parameter is consumed on every path: compiles,
#                             emits "`#[trust::must_consume]` PROVED" (exit 0).
#   ownership/mutant/*.rs  -> the parameter is dropped (leaked) on some path:
#                             Trust REJECTS it with a build error
#                             "`#[trust::must_consume]` FAILED" (exit != 0),
#                             proving the linearity check is non-vacuous.
#
# Pure MIR dataflow — no ay subprocess needed.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"
FIX="$REPO_ROOT/tests/trust-falsification/ownership"
# No z3/LIBRARY_PATH export: the `ay` SMT solver is pure-Rust and stage2 `trustc`
# links no libz3 (verified 2026-08-01: no z3-sys/links="z3" in any Cargo.lock;
# `otool -L trustc` is z3-clean). Re-adding one would resurrect a dead knob.

if [ ! -x "$TRUSTC" ]; then
  echo "ERROR: trustc not found at $TRUSTC"
  exit 2
fi

TMPDIR_GATE="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_GATE"' EXIT

run_of() {
  local out
  out="$("$TRUSTC" --edition 2021 --crate-type lib "$1" \
        -o "$TMPDIR_GATE/$(basename "$1").rlib" 2>&1)"
  printf '%s|||%s' "$?" "$out"
}

failed=0

for f in "$FIX"/proved/*.rs; do
  [ -e "$f" ] || continue
  res="$(run_of "$f")"; code="${res%%|||*}"; out="${res#*|||}"
  if [ "$code" -eq 0 ] && grep -q '`#\[trust::must_consume\]` PROVED' <<<"$out"; then
    echo "PASS  proved   $(basename "$f")  — LINEAR: owned parameter consumed on every path (PROVED)"
  else
    echo "FAIL  proved   $(basename "$f")  — expected exit 0 + must_consume PROVED (got exit $code)"
    failed=1
  fi
done

for f in "$FIX"/mutant/*.rs; do
  [ -e "$f" ] || continue
  res="$(run_of "$f")"; code="${res%%|||*}"; out="${res#*|||}"
  if [ "$code" -ne 0 ] && grep -q '`#\[trust::must_consume\]` FAILED' <<<"$out"; then
    echo "PASS  mutant   $(basename "$f")  — sound: leaked parameter REJECTED (build error)"
  else
    echo "FAIL  mutant   $(basename "$f")  — VACUOUS: leak not rejected (got exit $code)"
    failed=1
  fi
done

if [ "$failed" -eq 0 ]; then
  echo "OWNERSHIP GATE: GREEN — linear params prove must-consume, leaks are rejected (trust-vc engaged)"
  exit 0
else
  echo "OWNERSHIP GATE: RED — ownership/trust-vc linearity check regressed"
  exit 1
fi
