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
#  3. A pass never seen to fail is not evidence. So three mutations run: one
#     breaks a tier-1 postcondition (and must cascade to the three functions
#     that COMPOSE it), one breaks a tier-2 safety obligation, and one leaves
#     every obligation TRUE while making the crate return wrong answers.
#  4. Proofs here cover overflow, underflow, zero divisors and discharged
#     contracts — NOT whether the answer is right. So the crate's 7 unit tests
#     are RUN by this gate, and they are asserted to fail BY NAME under a
#     mutation the strict lane accepts at exit 0.
#
# The Summary line alone can read like a pass at exit 101 — measured on this
# very lane during development. Every assertion here is on the EXIT CODE and
# the `Gate:` line, never the Summary.
#
# MUTATION C IS WHY THE TESTS ARE HERE
# ------------------------------------
# `span_width(lo, hi)` is TIER 1: `ensures result <= hi` is discharged by the
# compiler, inherited from `clamp_upper`'s postcondition. Swapping its call to
# `raw_span(lo, hi)` for `raw_span(hi, lo)` cannot break that contract — the
# clamp's second argument is untouched, so `result <= hi` remains TRUE over
# whatever the helper returns. Measured 2026-08-29: the strict lane returns
# EXIT 0 with the row count, the coverage AND the kind split (`postcondition=11`)
# byte-identical to pristine, while `span_width(3, 9)` returns 0 instead of 6
# and `span_width(9, 3)` returns 3 instead of 0.
#
# A discharged `ensures` is therefore not a proved specification, and this gate
# says so with a measurement rather than a comment. This crate has already paid
# for the same lesson once at the value level: a `percent` reshaped to please
# the encoder proved every obligation it had and returned `4` for
# `percent(42_949_673, 1)`.
#
# The mutation is asserted in BOTH directions: one named test must go red, and
# `clamps_are_total_and_bounded` (the composition CARRIER) and
# `capped_sum_saturates_then_caps` (its untouched sibling) must stay GREEN — so
# it cannot degrade into "everything broke", which is the state in which a
# wrong-value control proves nothing.
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
# Usage:  scripts/trust_ratio_strict_gate.sh   (~2 min, 6 verified runs + 2 test runs)
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
  require_env "${STEP:-run}"
  no_rustc_error "${STEP:-run}"
}
# `--lib` is load-bearing. A concurrent `x.py check` can rebuild
# `librustc_driver-<hash>.dylib` while stage1 `trustdoc` still references the old
# hash; the doctest stage then dies with `dyld: Library not loaded` / SIGABRT and
# a bare `targo test` exits 101 with every unit test passing. That is what turned
# `trust-utf`'s gate red while its strict lane was green, and — worse — it
# DISARMS a wrong-value control, whose whole assertion is "the tests go red"
# when they were already red for an unrelated reason. This crate has no doctests
# (its examples are ```text). Scope to the unit tests, and keep asserting the
# exact result line so the scoping cannot hide a real red.
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-ratio --lib ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-tests}"
}
gate_line() { grep -oE 'Gate: [A-Z]+ \[strict lane, exit [0-9]+\]' "$LOG" | tail -1; }
fail() { echo "  FAIL $*"; fails=$((fails+1)); }

# ---------------------------------------------------------------------------
# G1. AN ENVIRONMENT FAILURE IS NOT A RESULT, AND IT SATISFIES EVERY
#     PRESENCE-ONLY ASSERTION. THIS IS DEMONSTRATED, NOT HYPOTHESISED.
#
# A transient `trustd` outage refuses EVERY obligation in the crate BEFORE
# solver dispatch: each row becomes `UnsupportedMir/MemoryAdmission` with
# outcome `unknown`, and the run emits a nonzero rc, `Gate: FAIL`, and one
# ``verification failed for `<crate>::<fn>``` line for EVERY function in the
# crate. That is a byte-perfect imitation of "the mutation refuted exactly what
# it was supposed to refute" — including the composition cascade.
#
# The archived run
#   crates/target/debug/.fingerprint/trust-ratio-461ba1c0b354a13d/output-lib-trust_ratio
# (2026-08-29 05:08 — `could not connect to selected endpoint
# /private/tmp/trustd-runtime-locks-501/trust-memory-jobserver.sock: Connection
# refused (os error 61)`; all 18 trust-ratio functions `UnsupportedMir/
# MemoryAdmission`, every outcome `unknown`, 0 proved) satisfies ALL FOUR of
# `trust_ratio` mutation A's assertions verbatim while proving nothing at all.
#
# An outage therefore ABORTS the gate as INCONCLUSIVE (exit 3). It is never
# scored as a pass and never scored as a refutation.
env_broken() {
  grep -qE 'MemoryAdmission|memory admission failed|could not connect to selected endpoint|Connection refused' "$LOG"
}
require_env() { # require_env <label>
  if env_broken; then
    echo "  ENV  $1: trustd memory admission was unavailable — every obligation was"
    echo "       refused BEFORE solver dispatch, so this run is not a fact about the"
    echo "       crate under test. Refusing to score it as a pass OR as a refutation."
    ENVD="$(grep -oE 'could not connect to selected endpoint [^\\"]*' "$LOG" | head -1)"
    [ -n "$ENVD" ] && echo "       $ENVD"
    echo "INCONCLUSIVE (environment): trustd admission unavailable — re-run when it is up."
    echo "       log kept at $LOG"
    exit 3
  fi
}

# A mutation meant to break the PROOF must not have broken the BUILD instead. A
# crate that fails to compile emits NO obligations for what did not lower, so a
# refutation-shaped verdict can be manufactured by a type error that has nothing
# to do with the property under test. Trust's own verification failures are bare
# `error:` lines carrying no code, so keying on `error[E####]` isolates the
# rustc diagnostic without colliding with the §9.1 bundling refusals that some
# mutations are SUPPOSED to provoke.
no_rustc_error() { # no_rustc_error <label>
  if grep -qE '^error\[E[0-9]{4}\]' "$LOG"; then
    fail "$1: rustc reported $(grep -oE '^error\[E[0-9]{4}\]' "$LOG" | head -1) — this run is supposed to exercise the PROOF, not the BUILD; obligations for code that did not lower are ABSENT, not refuted"
  fi
  return 0
}

# ---------------------------------------------------------------------------
# G2. `ok` MUST MEAN "THIS SECTION'S OWN CONTENT ASSERTIONS HELD".
#
# `ok   mutation X` used to be printed on `[ "$RC" -eq 0 ]` ALONE, so the
# transcript printed `ok` for a plain rustc type error, a missing driver, or an
# unrelated regression. The gate's EXIT CODE stayed right — the greps after each
# `ok` move `fails` separately — but the line a human reads was not evidence.
#
# Every ok-print is therefore QUEUED by `mut_ok` and flushed by `mut_end` at the
# END of the section, once every assertion in that section has had its chance to
# move `fails`. A section may queue more than one line (the wrong-value sections
# report both the pristine test result and the mutated one), so the queue is an
# array: if anything in the section failed, NONE of its ok lines are evidence.
__OKS__=()
mut_begin() { MUT_FAILS_AT="$fails"; __OKS__=(); }
mut_ok() { __OKS__+=("$1"); }
mut_end() {
  [ "${#__OKS__[@]}" -gt 0 ] || return 0
  local t
  for t in "${__OKS__[@]}"; do
    if [ "$fails" -eq "${MUT_FAILS_AT:-0}" ]; then
      printf '  ok   %s\n' "$t"
    else
      printf '  ---- %s\n' "$t"
      printf '       ^ NOT ok: see the FAIL line(s) above; this line is not evidence.\n'
    fi
  done
  __OKS__=()
}

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

echo "trust-ratio strict gate:"

# ---------------------------------------------------------------------------
# 1. THE PASS, asserted on exit code, Gate, compile status, coverage AND the
#    kind split — never on the Summary alone.
# ---------------------------------------------------------------------------
STEP="THE PASS"; mut_begin
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
mut_ok "pristine  $G  [10 safety + 9 hardened-twin + 11 postcondition, 0 unreachable]"
rm -f "$LOG"

mut_end
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
STEP="THE SAME PASS UNDER '-Ztrust-policy=certify'"; mut_begin
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
mut_ok "certify   $G  [0 relabelled at the publication boundary]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — a tier-1 postcondition made FALSE.
#    `clamp_upper` is the primitive every other tier-1 bound is COMPOSED from,
#    so breaking it must refute four functions, not one. If it ever refutes only
#    `clamp_upper`, the composition stopped carrying and the other three bounds
#    are being proved by something else.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
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
if [ "$RC" -eq 0 ]; then fail "mutation A: a FALSE postcondition still passed  $G"; else mut_ok "mutation A (clamp_upper returns v unclamped)  rc=$RC  $G"; fi
for f in clamp_upper span_width saturating_diff capped_sum; do
  grep -q "verification failed for \`trust_ratio::$f\`" "$LOG" \
    || fail "mutation A: $f was NOT refuted — composition is not carrying the bound"
done
# SPECIFICITY, the other half of the control. The four presence assertions above
# cannot tell "the break propagated to exactly its intended composers" apart
# from "the entire crate went red" — and an environment failure produces exactly
# the latter while satisfying all four verbatim (see the G1 block above). These
# nine functions are the complete complement: none of them reaches `clamp_upper`
# directly or transitively.
#
# Established two ways. (1) Call graph: the ONLY non-test callers of
# `clamp_upper` are `span_width` (lib.rs:144), `saturating_diff` (:155) and
# `capped_sum` (:163); none of those three has an in-crate caller, so the
# closure stops there and the remaining nine are call-free or call only the
# uncontracted `raw_*` helpers. (2) MEASUREMENT — this exact mutation was run
# standalone on 2026-08-29 and the full log named EXACTLY four subjects and no
# others.
#
# §11.5 NOTE, settled by that same measurement rather than by inference. All
# four subjects appeared in the `Trust strict verification failed for` form and
# the run contained NO `refused Assert-bearing member` note at all. So although
# `clamp_upper` IS bundled (it has three non-test callers), the three wrappers
# are named here because each independently lost its own postcondition row —
# not because a bundled callee's failure was attributed one level up. The
# composition claim this mutation makes is therefore about composition.
for f in clamp_lower clamp_range last_index percent permille scaled_ratio \
         raw_span raw_diff raw_sum; do
  grep -q "verification failed for \`trust_ratio::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a clamp_upper-only break — it does not depend on clamp_upper, so either this run went red for an unrelated reason (and is not evidence about composition at all) or the tier-1 bounds are not independent"
done
rm -f "$LOG"; restore

mut_end
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
STEP="MUTATION B"; mut_begin
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
if [ "$RC" -eq 0 ]; then fail "mutation B: an unguarded division still passed  $G"; else mut_ok "mutation B (percent loses its den==0 guard)  rc=$RC  $G"; fi
grep -qE '^\s*\[(FAILED|UNKNOWN)\] \[divzero\]' "$LOG" \
  || fail "mutation B: no unfavorable [divzero] row at all — the obligation was not even emitted"
grep -q 'solver refuted the encoded VC' "$LOG" \
  || fail "mutation B: no refutation recorded — the gate saw a coverage gap, not a refutation"
grep -q 'direct SMT confirmed a satisfiable typed query fact' "$LOG" \
  || fail "mutation B: the violation was never confirmed satisfiable — no counterexample exists, so this is a capability gap, not a caught bug"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. THE TESTS, AND THE MUTATION THEY ALONE CAN CATCH.
#    Everything above this point is a statement about obligations. Mutation C
#    changes the crate's ANSWERS while leaving every obligation — including the
#    discharged `ensures result <= hi` — true, so the strict lane accepts it at
#    exit 0 and only the unit tests refuse it. They are therefore asserted to
#    pass, and asserted to fail.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then
  fail "pristine: unit tests failed (rc=$RC) — $(grep -oE '^test result: .*' "$LOG" | head -1)"
else
  grep -qE '^test result: ok\. 7 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 7 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# MUTATION C — a WRONG ANSWER under a contract that stays TRUE.
# `clamp_upper`'s second argument is untouched, so `ensures result <= hi` holds
# over whatever `raw_span` returns; only the argument ORDER of the uncontracted
# helper moves. Measured 2026-08-29: exit 0, identical rows, identical kind
# split — and `span_width(3, 9) == 0` instead of 6.
mutate 'pub fn span_width(lo: u32, hi: u32) -> u32 ensures result <= hi {
    clamp_upper(raw_span(lo, hi), hi)
}' 'pub fn span_width(lo: u32, hi: u32) -> u32 ensures result <= hi {
    clamp_upper(raw_span(hi, lo), hi)
}'
run
VRC="$RC"
VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation C: the strict lane REFUTED an argument swap under a discharged contract (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged \`ensures\` cannot see the difference is now stale and must be re-measured, not deleted"
fi
case "$VG" in *"PASS [strict lane, exit 0]"*) ;; *) fail "mutation C: Gate is '$VG', expected PASS — the swap was supposed to change no obligation at all";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "mutation C: rustc reported errors, so the lane did not actually accept the swap"; fi
grep -qE 'Summary: 30 proved, 0 failed, .*0 inconclusive \(30 total\)' "$LOG" \
  || fail "mutation C: the row count moved — the swap was supposed to change no obligation at all. $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# The discharged contracts specifically, read off the same run: all 11
# postconditions — `span_width`'s among them — still prove over the wrong
# answer. That is the claim this mutation exists to make.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *postcondition=11*) ;; *) fail "mutation C: a postcondition stopped proving — $KINDS";; esac
rm -f "$LOG"

runtests
if [ "$RC" -eq 0 ]; then
  fail "mutation C: a swapped argument order passed the unit tests — the tests are not sensitive to the crate's own subject"
else
  mut_ok "mutation C (span_width: raw_span(lo,hi) -> raw_span(hi,lo))  tests rc=$RC, strict lane rc=$VRC  $VG"
fi
grep -q "span_and_diff_cannot_underflow ... FAILED" "$LOG" \
  || fail "mutation C: span_and_diff_cannot_underflow did not catch a swapped argument order"
# ... and the mutation must NOT degrade into "everything broke", or the red
# above would say nothing about this defect in particular. The composition
# CARRIER and its untouched sibling wrapper must both still pass.
for t in clamps_are_total_and_bounded capped_sum_saturates_then_caps; do
  grep -q "$t ... ok" "$LOG" \
    || fail "mutation C: $t also failed, so this is not a demonstration that a TRUE contract can sit over a wrong answer"
done
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — the"
  echo "        clamp keeps \`ensures result <= hi\` TRUE over the wrong value.)"
fi
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. The restore actually restored. A gate that leaves a mutation behind turns
#    the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
STEP="The restore actually restored"; mut_begin
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

mut_end
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
