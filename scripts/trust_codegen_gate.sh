#!/usr/bin/env bash
# Trust verified-codegen / trust-cg gate — `#[trust::verified_codegen]`.
#
# Engages the trust-cg (verified codegen) lane end-to-end. Stock rustc/LLVM
# codegen is UNVERIFIED. `#[trust::verified_codegen]` lowers the function to
# trust-cg's LIR, compares the lowering's round trip, then emits real machine
# code, decodes the emitted bytes, and discharges equality between their machine
# semantics and the semantics auto-derived from the IR.
#
# The gate distinguishes the two checks, because they are not interchangeable:
# the round trip compares block count, argument count, and the arithmetic
# operation multiset without ever inspecting an instruction, so it cannot witness
# a miscompile in the encoding, the register allocation, or the ABI.
#
#   codegen/proved/*.rs          -> the byte-level gate DECIDED: compiles and
#                                   emits PROVED (kernel-re-checked) or VALIDATED
#                                   (ay is the sole authority) (exit 0).
#   codegen/roundtrip-only/*.rs  -> inside the lowerable fragment, outside the
#                                   byte-level gate's: compiles and emits the
#                                   honest "not machine-checked" note (exit 0).
#                                   This is what catches the whole lane silently
#                                   degrading to the structural claim.
#   codegen/mutant/*.rs          -> outside the lowerable fragment, or a refuted
#                                   emission: Trust REJECTS it with a build error
#                                   "`#[trust::verified_codegen]` FAILED"
#                                   (exit != 0), proving the gate is non-vacuous.
#
# No fixture here can be an actual miscompile — Rust source cannot ask the
# backend to emit wrong code. The negative control for that lives where a wrong
# emission can be constructed: `trust-cg-bridge`'s
# `miscompiled_emission_is_refuted_through_the_public_entry_point` corrupts an
# emitted instruction and requires the gate to refute it. What these fixtures
# pin is the reporting: that a decided verdict and an undecided one stay
# distinguishable in what the user is told.
#
# Exit codes: 0 GREEN, 1 RED (a fixture landed in the wrong class), 2 setup
# error, 3 INCONCLUSIVE (the byte-level lane did not decide on this host — its
# machine semantics are wired for AArch64 only, so an x86_64 or Windows host
# reaches nothing stronger than the structural claim). INCONCLUSIVE is not a
# pass: it says the strongest claim was unavailable, not that it held.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"
FIX="$REPO_ROOT/tests/trust-falsification/codegen"
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

# The exact note tails `trust_verify.rs::verify_codegen_attr` emits. Each grade
# is matched on its own so no fixture class can be satisfied by a weaker one.
MACHINE_CHECKED='`#\[trust::verified_codegen\]` (PROVED|VALIDATED)'
ROUND_TRIP_ONLY='`#\[trust::verified_codegen\]` not machine-checked'
REJECTED='`#\[trust::verified_codegen\]` FAILED'

failed=0
inconclusive=0

for f in "$FIX"/proved/*.rs; do
  [ -e "$f" ] || continue
  res="$(run_of "$f")"; code="${res%%|||*}"; out="${res#*|||}"
  if [ "$code" -eq 0 ] && grep -qE "$MACHINE_CHECKED" <<<"$out"; then
    grade="$(grep -oE "$MACHINE_CHECKED" <<<"$out" | grep -oE 'PROVED|VALIDATED' | head -1)"
    echo "PASS  proved   $(basename "$f")  — VERIFIED CODEGEN: emitted machine code equals IR semantics ($grade)"
  elif [ "$code" -eq 0 ] && grep -qE "$ROUND_TRIP_ONLY" <<<"$out"; then
    echo "INCONCLUSIVE  proved   $(basename "$f")  — the byte-level lane did not decide here:"
    grep -E "$ROUND_TRIP_ONLY" -A 2 <<<"$out" | sed 's/^/        /'
    inconclusive=1
  else
    echo "FAIL  proved   $(basename "$f")  — expected exit 0 + a machine-checked grade (got exit $code)"
    failed=1
  fi
done

for f in "$FIX"/roundtrip-only/*.rs; do
  [ -e "$f" ] || continue
  res="$(run_of "$f")"; code="${res%%|||*}"; out="${res#*|||}"
  if [ "$code" -eq 0 ] && grep -qE "$ROUND_TRIP_ONLY" <<<"$out"; then
    echo "PASS  rt-only  $(basename "$f")  — honest: structural round trip only, not reported as a proof"
  elif [ "$code" -eq 0 ] && grep -qE "$MACHINE_CHECKED" <<<"$out"; then
    echo "FAIL  rt-only  $(basename "$f")  — OVERCLAIM: a function outside the byte-level fragment reported a machine-checked grade"
    failed=1
  else
    echo "FAIL  rt-only  $(basename "$f")  — expected exit 0 + the not-machine-checked note (got exit $code)"
    failed=1
  fi
done

for f in "$FIX"/mutant/*.rs; do
  [ -e "$f" ] || continue
  res="$(run_of "$f")"; code="${res%%|||*}"; out="${res#*|||}"
  if [ "$code" -ne 0 ] && grep -qE "$REJECTED" <<<"$out"; then
    echo "PASS  mutant   $(basename "$f")  — sound: unverifiable lowering REJECTED (build error)"
  else
    echo "FAIL  mutant   $(basename "$f")  — VACUOUS: unverifiable lowering not rejected (got exit $code)"
    failed=1
  fi
done

if [ "$failed" -ne 0 ]; then
  echo "CODEGEN GATE: RED — trust-cg verified-codegen check regressed"
  exit 1
fi
if [ "$inconclusive" -ne 0 ]; then
  echo "CODEGEN GATE: INCONCLUSIVE — nothing overclaimed, but the byte-level"
  echo "  output-preservation lane could not decide the proved fixtures on this"
  echo "  host. Its machine semantics are wired for AArch64 only. Re-run on an"
  echo "  AArch64 host for a GREEN verdict; do not read this as a pass."
  exit 3
fi
echo "CODEGEN GATE: GREEN — emitted machine code proved equal to IR semantics, unverifiable lowerings rejected (trust-cg engaged)"
exit 0
