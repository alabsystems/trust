#!/usr/bin/env bash
# trust_ratio_strict_gate.sh — pin `crates/trust-ratio` at a NON-VACUOUS pass of
# the authenticated strict lane, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-ratio` is the first `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it. Measured
# 2026-08-28 at stage1 `8d4210bcf`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 30 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive (30 total)
#   Coverage: 13/13 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=1, arithmetic_overflow_mul=3,
#                   arithmetic_overflow_sub=3, division_by_zero=3,
#                   hardened_panic_boundary=9, postcondition=11
#
# A pass is worth nothing on its own, for three separate reasons this repo has
# paid for, and every assertion below exists for one of them:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower,
#     and reports `0 failed` with `Coverage: complete`. So the compile status is
#     asserted, not inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`; a pass whose
#     rows are mostly `unreachable` deletes no runtime check. So the kind split
#     is asserted and `unreachable` is asserted ABSENT.
#  3. A pass never seen to fail is not evidence. So two mutations run: one
#     breaks a tier-1 postcondition (and must cascade to the three functions
#     that COMPOSE it), one breaks a tier-2 safety obligation.
#
# The Summary line alone can read like a pass at exit 101 — measured on this
# very lane during development. Every assertion here is on the EXIT CODE and
# the `Gate:` line, never the Summary.
#
# Usage:  scripts/trust_ratio_strict_gate.sh          (~3 min, 3 verified runs)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-ratio/src/lib.rs"
TARGO="${TARGO:-$REPO_ROOT/build/aarch64-apple-darwin/stage1/bin/targo}"

[ -x "$TARGO" ] || { echo "REFUSE: no targo at $TARGO (set TARGO=...)"; exit 2; }
# Two behavioural discriminators; a stage whose targo was never rebuilt ships
# upstream cargo under the name `targo` and verifies NOTHING while succeeding.
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
run() { # run <label>; sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" trust check -p trust-ratio ) > "$LOG" 2>&1
  RC=$?
}
gate_line() { grep -oE 'Gate: [A-Z]+ \[strict lane, exit [0-9]+\]' "$LOG" | tail -1; }
fail() { echo "  FAIL $*"; fails=$((fails+1)); }

echo "trust-ratio strict gate:"

# ---------------------------------------------------------------------------
# 1. THE PASS, asserted on exit code, Gate, compile status, coverage AND the
#    kind split — never on the Summary alone.
# ---------------------------------------------------------------------------
run pristine
G="$(gate_line)"
[ -n "$G" ] || fail "pristine: no Gate: line — the lane did not run (vacuous)"
[ "$RC" -eq 0 ] || fail "pristine: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "pristine: Gate is '$G'";; esac
# (1) the crate actually compiled — a lowering abort emits no obligations
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 13/13 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 13/13 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 30 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(30 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# (2) NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert
#     the real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an `unreachable` row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=1 arithmetic_overflow_mul=3 arithmetic_overflow_sub=3 \
            division_by_zero=3 hardened_panic_boundary=9 postcondition=11; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
[ "$fails" -eq 0 ] && echo "  ok   pristine  $G  [10 safety + 9 hardened-twin + 11 postcondition, 0 unreachable]"
rm -f "$LOG"

# ---------------------------------------------------------------------------
# 2. MUTATION A — a tier-1 postcondition made FALSE.
#    `clamp_upper` is the primitive every other tier-1 bound is COMPOSED from,
#    so breaking it must refute four functions, not one. If it ever refutes only
#    `clamp_upper`, the composition stopped carrying and the other three bounds
#    are being proved by something else.
# ---------------------------------------------------------------------------
python3 - "$SRC" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
old = "pub fn clamp_upper(v: u32, hi: u32) -> u32 ensures result <= hi {\n    if v > hi { hi } else { v }\n}"
new = "pub fn clamp_upper(v: u32, hi: u32) -> u32 ensures result <= hi {\n    v\n}"
assert s.count(old) == 1, f"mutation A no longer applies ({s.count(old)} matches)"
open(p, "w").write(s.replace(old, new))
PY
[ $? -eq 0 ] || fail "mutation A could not be applied — the source moved under the gate"
run mutA
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a FALSE postcondition still passed  $G"; else echo "  ok   mutation A (clamp_upper returns v unclamped)  rc=$RC  $G"; fi
for f in clamp_upper span_width saturating_diff capped_sum; do
  grep -q "verification failed for \`trust_ratio::$f\`" "$LOG" \
    || fail "mutation A: $f was NOT refuted — composition is not carrying the bound"
done
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 3. MUTATION B — a tier-2 SAFETY obligation made false: drop the zero-divisor
#    guard. This must produce a hard `failed` row, not merely an `unknown`; an
#    unknown would mean the gate is only detecting coverage gaps.
# ---------------------------------------------------------------------------
python3 - "$SRC" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
old = "pub fn percent(num: u32, den: u32) -> u32 {\n    if den == 0 {\n        return 0;\n    }\n"
new = "pub fn percent(num: u32, den: u32) -> u32 {\n"
assert s.count(old) == 1, f"mutation B no longer applies ({s.count(old)} matches)"
open(p, "w").write(s.replace(old, new))
PY
[ $? -eq 0 ] || fail "mutation B could not be applied — the source moved under the gate"
run mutB
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an unguarded division still passed  $G"; else echo "  ok   mutation B (percent loses its den==0 guard)  rc=$RC  $G"; fi
grep -qE '^\s*\[FAILED\] \[divzero\]' "$LOG" \
  || fail "mutation B: no [FAILED] [divzero] row — the gate saw a coverage gap, not a refutation"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 4. The restore actually restored. A gate that leaves a mutation behind turns
#    the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
