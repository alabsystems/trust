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
# 2026-08-28 at stage1 `8d4210bcf`, and re-measured IDENTICALLY 2026-08-29 at
# stage1 `47aecd73e6` + the `collect_supported_atoms` duplicate-conjunct fix,
# under BOTH the default policy and `-Ztrust-policy=certify`:
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
# WHAT THIS GATE DID NOT SEE, and now does
# ----------------------------------------
# Between 2026-08-27 and 2026-08-29 this lane went red without a single line of
# `trust-ratio` changing: the `first-party/ay` pin crossed `2aaefaa808`, after
# which a DUPLICATED top-level assertion makes ay revoke an UNSAT proof it has
# already computed (ay's own `docs/ay-asks/2026-08-28-authored-assume-duplicate-
# root-suppresses-proof`). Every `ensures` here is PARAMETER-bounded, so its
# per-branch VC closes through ay's Farkas lane and carries the duplicated
# return-slot pin; `trust-hex`'s clauses are CONSTANT-bounded and close before
# ay is reached, so the sibling gate stayed green throughout. That asymmetry is
# why this gate must also run the certify lane — which is the lane the withheld
# rows were failing — and why the kind split above is asserted exactly.
#
# Usage:  scripts/trust_ratio_strict_gate.sh          (~4 min, 5 verified runs)
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
run() { # run [policy]; sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-ratio ) > "$LOG" 2>&1
  RC=$?
}
gate_line() { grep -oE 'Gate: [A-Z]+ \[strict lane, exit [0-9]+\]' "$LOG" | tail -1; }
fail() { echo "  FAIL $*"; fails=$((fails+1)); }

echo "trust-ratio strict gate:"

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
# 2. THE SAME PASS UNDER `-Ztrust-policy=certify`.
#    This is the lane the 2026-08-29 regression actually failed: the four
#    parameter-bounded per-branch postcondition VCs kept a favorable COMPILER
#    verdict and lost only their clean-kernel certificate, so nothing but a
#    certificate-demanding lane could see it.
#
#    A misspelled TRUSTFLAGS is silently dropped, so first prove the flag path
#    reaches the compiler by requiring a bogus policy to be REJECTED BY NAME.
#    Without this control, "certify passed" is indistinguishable from "certify
#    never ran".
# ---------------------------------------------------------------------------
run "-Ztrust-policy=bogus_not_a_policy"
grep -q "incorrect value \`bogus_not_a_policy\` for unstable option \`trust-policy\`" "$LOG" \
  || fail "TRUSTFLAGS control: a bogus policy was NOT rejected — the flag never reaches the compiler, so the certify run below proves nothing"
rm -f "$LOG"

run "-Ztrust-policy=certify"
G="$(gate_line)"
[ "$RC" -eq 0 ] || fail "certify: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "certify: Gate is '$G'";; esac
grep -qE 'Summary: 30 proved, 0 failed, .*0 inconclusive \(30 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# The publication boundary is the seam that broke. Assert that NOTHING is
# relabelled: a withheld favorable row reads `relabelled unknown`, and the four
# postcondition rows this gate exists for were exactly that for a day.
grep -qE 'Publication boundary: [0-9]+ obligation\(s\) passed the compiler, 30 published, [0-9]+ WITHHELD .*\(0 relabelled unknown' "$LOG" \
  || fail "certify: a favorable compiler row was RELABELLED at the publication boundary — $(grep -oE '^Publication boundary: .*' "$LOG" | tail -1)"
[ "$fails" -eq 0 ] && echo "  ok   certify   $G  [0 relabelled at the publication boundary]"
rm -f "$LOG"

# ---------------------------------------------------------------------------
# 3. MUTATION A — a tier-1 postcondition made FALSE.
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
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a FALSE postcondition still passed  $G"; else echo "  ok   mutation A (clamp_upper returns v unclamped)  rc=$RC  $G"; fi
for f in clamp_upper span_width saturating_diff capped_sum; do
  grep -q "verification failed for \`trust_ratio::$f\`" "$LOG" \
    || fail "mutation A: $f was NOT refuted — composition is not carrying the bound"
done
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 4. MUTATION B — a tier-2 SAFETY obligation made false: drop the zero-divisor
#    guard. The gate must see a REFUTATION, not a coverage gap.
#
#    This assertion used to read `[FAILED] [divzero]`, on the premise that "an
#    unknown would mean the gate is only detecting coverage gaps". That premise
#    is no longer sound and the assertion was measured stale on 2026-08-29: an
#    unattested CHC refutation is now deliberately DEMOTED to `unknown`
#    (`crates/trust-bmc/src/verifier_api.rs:3050-3055` — "a refutation of an
#    over-approximating encoding is a refutation of the ENCODING, not of the
#    program"), so a real counterexample can legitimately surface as `[UNKNOWN]`.
#    Asserting the label alone therefore fails on a correctly-refuted mutation.
#
#    Asserting merely "not proved" would be the opposite error — it passes on
#    the coverage gap the original assertion existed to exclude. So assert the
#    three facts that separate the two, all of which are ABSENT from the
#    pristine and `trust-hex` runs (measured 2026-08-29: 0 occurrences in each):
#      (a) an unfavorable `[divzero]` row exists at all — a coverage gap emits none;
#      (b) the solver REFUTED the encoded VC;
#      (c) the violation is genuinely SAT, i.e. a real counterexample exists.
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
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an unguarded division still passed  $G"; else echo "  ok   mutation B (percent loses its den==0 guard)  rc=$RC  $G"; fi
grep -qE '^\s*\[(FAILED|UNKNOWN)\] \[divzero\]' "$LOG" \
  || fail "mutation B: no unfavorable [divzero] row at all — the obligation was not even emitted"
grep -q 'solver refuted the encoded VC' "$LOG" \
  || fail "mutation B: no refutation recorded — the gate saw a coverage gap, not a refutation"
grep -q 'direct SMT confirmed a satisfiable typed query fact' "$LOG" \
  || fail "mutation B: the violation was never confirmed satisfiable — no counterexample exists, so this is a capability gap, not a caught bug"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 5. The restore actually restored. A gate that leaves a mutation behind turns
#    the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
