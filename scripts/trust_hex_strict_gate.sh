#!/usr/bin/env bash
# trust_hex_strict_gate.sh — pin `crates/trust-hex` at a NON-VACUOUS pass of the
# authenticated strict lane, on BOTH policies, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-hex` is the second `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it. Measured
# 2026-08-29 at stage1 driver `7b7fdb7dc`, identically under the default
# `unix_hardened` policy and under `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 41 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive (41 total)
#   Coverage: 18/18 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=6, arithmetic_overflow_mul=2,
#                   arithmetic_overflow_shr=1, arithmetic_overflow_sub=3,
#                   hardened_panic_boundary=12, postcondition=16,
#                   shift_overflow_shr=1
#
# A pass is worth nothing on its own, for four reasons this repo has paid for,
# and every assertion below exists for one of them:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower,
#     and reports `0 failed` with `Coverage: complete`. So the compile status is
#     asserted, not inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`; a pass whose
#     rows are mostly `unreachable` deletes no runtime check. So the kind split
#     is asserted and `unreachable` is asserted ABSENT. All 41 rows here are
#     16 postconditions + 13 primary safety + 12 hardened twins.
#  3. A pass never seen to fail is not evidence. Three mutations run, each
#     refuting a DIFFERENT mechanism: a direct contract, the composition that
#     carries every other contract, and a real safety obligation.
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it by name.
#
# The Summary line alone can read like a pass at a nonzero exit. Every assertion
# here is on the EXIT CODE and the `Gate:` line, never the Summary.
#
# Usage:  scripts/trust_hex_strict_gate.sh          (~2 min, 5 verified runs)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-hex/src/lib.rs"
TARGO="${TARGO:-$REPO_ROOT/build/aarch64-apple-darwin/stage1/bin/targo}"

[ -x "$TARGO" ] || { echo "REFUSE: no targo at $TARGO (set TARGO=...)"; exit 2; }
# Two behavioural discriminators; a stage whose targo was never rebuilt ships
# upstream cargo under the name `targo` and verifies NOTHING while succeeding.
# (`targo trust --help` is NOT one of them — cargo resolves the sibling
# `targo-trust` binary and answers it.)
"$TARGO" --unverified --version >/dev/null 2>&1 \
  || { echo "REFUSE: $TARGO rejects --unverified — it is cargo-in-disguise, not targo"; exit 2; }
[ -x "$(dirname "$TARGO")/trustc" ] \
  || { echo "REFUSE: no sibling trustc beside $TARGO — the stage1 sysroot is not assembled"; exit 2; }

BACKUP="$(mktemp)"; cp "$SRC" "$BACKUP"
PRISTINE_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
restore() { cp "$BACKUP" "$SRC"; }
trap 'restore; rm -f "$BACKUP"' EXIT INT TERM

fails=0
LOG=""
run() { # run [policy]; sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-hex ) > "$LOG" 2>&1
  RC=$?
}
gate_line() { grep -oE 'Gate: [A-Z]+ \[strict lane, exit [0-9]+\]' "$LOG" | tail -1; }
fail() { echo "  FAIL $*"; fails=$((fails+1)); }

# `mutate <old> <new>` — refuses if the anchor is not unique, so a source edit
# that moves a mutation out from under this gate is a loud failure, never a
# silently-skipped control.
mutate() {
  python3 - "$SRC" "$1" "$2" <<'PY' || exit 3
import sys
p, old, new = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(p).read()
if s.count(old) != 1:
    sys.exit(f"anchor matched {s.count(old)} times, expected 1:\n{old}")
open(p, "w").write(s.replace(old, new))
PY
}

echo "trust-hex strict gate:"

# ---------------------------------------------------------------------------
# 1. THE PASS, asserted on exit code, Gate, compile status, coverage AND the
#    kind split — never on the Summary alone.
# ---------------------------------------------------------------------------
run
G="$(gate_line)"
[ -n "$G" ] || fail "pristine: no Gate: line — the lane did not run (vacuous)"
[ "$RC" -eq 0 ] || fail "pristine: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "pristine: Gate is '$G'";; esac
# (1) the crate actually compiled — a lowering abort emits no obligations
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 18/18 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 18/18 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 41 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(41 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# (2) NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert
#     the real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=6 arithmetic_overflow_mul=2 arithmetic_overflow_shr=1 \
            arithmetic_overflow_sub=3 hardened_panic_boundary=12 postcondition=16 \
            shift_overflow_shr=1; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
[ "$fails" -eq 0 ] && echo "  ok   pristine  $G  [16 postcondition + 13 safety + 12 hardened-twin, 0 unreachable]"
rm -f "$LOG"

# ---------------------------------------------------------------------------
# 2. THE SAME PASS UNDER `-Ztrust-policy=certify`.
#    A misspelled TRUSTFLAGS is dropped, so first prove the flag path reaches
#    the compiler by requiring a bogus policy to be REJECTED BY NAME. Without
#    this control, "certify passed" is indistinguishable from "certify never ran".
# ---------------------------------------------------------------------------
run "-Ztrust-policy=bogus_not_a_policy"
grep -q "incorrect value \`bogus_not_a_policy\` for unstable option \`trust-policy\`" "$LOG" \
  || fail "TRUSTFLAGS control: a bogus policy was NOT rejected — the flag never reaches the compiler, so the certify run below proves nothing"
rm -f "$LOG"

run "-Ztrust-policy=certify"
G="$(gate_line)"
[ "$RC" -eq 0 ] || fail "certify: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "certify: Gate is '$G'";; esac
grep -qE 'Summary: 41 proved, 0 failed, .*0 inconclusive \(41 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
[ "$fails" -eq 0 ] && echo "  ok   certify   $G"
rm -f "$LOG"

# ---------------------------------------------------------------------------
# 3. MUTATION A — a tier-1 contract made FALSE at its own body.
#    `low_nibble` is the one contract proved directly (arithmetic-free body,
#    constant bound) rather than by composition, so it is the control for that
#    mechanism on its own.
# ---------------------------------------------------------------------------
mutate 'pub fn low_nibble(byte: u8) -> u8 ensures result <= 15 {
    byte & 15
}' 'pub fn low_nibble(byte: u8) -> u8 ensures result <= 15 {
    byte
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a FALSE postcondition still passed  $G"; else echo "  ok   mutation A (low_nibble drops its mask)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_hex::low_nibble`' "$LOG" \
  || fail "mutation A: low_nibble was NOT refuted"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 4. MUTATION B — the COMPOSITION CARRIER broken.
#    Every tier-1 bound except `low_nibble`'s is inherited from a private
#    `clamp*` postcondition. Breaking `clamp102` must refute `lower_hex_digit`
#    as well as `clamp102` itself. If it ever refutes only `clamp102`, the
#    composition stopped carrying and `lower_hex_digit`'s bound is being proved
#    by something else — which is the exact shape that would let a wrapper keep
#    a green row after its evidence went away.
# ---------------------------------------------------------------------------
mutate 'fn clamp102(v: u8) -> u8 ensures result <= 102 {
    if v > 102 { 102 } else { v }
}' 'fn clamp102(v: u8) -> u8 ensures result <= 102 {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: a broken composition carrier still passed  $G"; else echo "  ok   mutation B (clamp102 stops clamping)  rc=$RC  $G"; fi
for f in clamp102 lower_hex_digit; do
  grep -q "verification failed for \`trust_hex::$f\`" "$LOG" \
    || fail "mutation B: $f was NOT refuted — composition is not carrying the bound"
done
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 5. MUTATION C — a real SAFETY obligation made false: drop the guard that keeps
#    `ascii - 48` from underflowing. This must produce a hard `[FAILED]` row,
#    not merely an `unknown`; an unknown would mean the gate is only detecting
#    coverage gaps. This is the obligation `trust-json`'s `decode_hex_escape`
#    discharges by inspection, on untrusted input.
# ---------------------------------------------------------------------------
mutate '    if ascii < 48 {
        return 16;
    }
    if ascii < 58 {' '    if ascii < 58 {'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an unguarded subtraction still passed  $G"; else echo "  ok   mutation C (raw_hex_digit_value loses its ascii<48 guard)  rc=$RC  $G"; fi
grep -qE '^\s*\[FAILED\] \[overflow:sub\]' "$LOG" \
  || fail "mutation C: no [FAILED] [overflow:sub] row — the gate saw a coverage gap, not a refutation"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 6. The restore actually restored. A gate that leaves a mutation behind turns
#    the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
