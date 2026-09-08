#!/usr/bin/env bash
# trust_modular_strict_gate.sh — pin `crates/trust-modular` at a NON-VACUOUS
# pass of the authenticated strict lane, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-modular` is the fourteenth `crates/`-resident component written to
# PASS the authenticated strict lane rather than to be retrofitted onto it. It
# is the first whose subject is division and remainder, which is the part of
# the fragment every earlier crate routed AROUND: `%` and `/` cannot be
# bundled into a caller (fragment map §2.4/§7.2), so a modular library is
# almost entirely terminal by construction.
#
# Measured 2026-08-29, under BOTH the default policy and
# `-Ztrust-policy=certify` (see the PRISTINE_* constants below for the exact
# figures this gate asserts).
#
# A pass is worth nothing on its own, for four separate reasons this repo has
# paid for, and every assertion below exists for one of them:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not
#     lower, and reports `0 failed` with `Coverage: complete`. So the compile
#     status is asserted, not inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`; a pass whose
#     rows are mostly `unreachable` deletes no runtime check. So the kind split
#     is asserted and `unreachable` is asserted ABSENT.
#  3. A pass never seen to fail is not evidence. EIGHT mutations run (A-H) and
#     every one of them was WATCHED firing while this gate was written, on
#     2026-08-30 against stage1 driver `ae2a9e2924594153`.
#  4. Proofs here cover overflow, underflow and zero divisors — NOT whether the
#     answer is right, and in this crate NOT the modular value at all (no
#     tier-2 function carries a contract). So the crate's unit tests are RUN,
#     and they are asserted to fail BY NAME under a mutation the strict lane
#     accepts at exit 0.
#
# THE TIER-1 CONTRACT IS TWO-SIDED AND STILL NOT A SPECIFICATION
# --------------------------------------------------------------
# `residue_clamp(v, last)` carries TWO clauses — `result <= last` and
# `result <= v` — which together pin the result to `<= min(v, last)`, exactly
# the value it returns. That is a materially stronger contract than the
# one-sided clamps of `trust-ratio` and `trust-index`, and it is STILL true of
# a function that returns 0. Mutation D makes the clamping arm return 0: the
# strict lane stays at exit 0 with a byte-identical kind split, both
# postconditions still prove, and only the unit tests refuse it.
#
# Usage:  scripts/trust_modular_strict_gate.sh   (~35 min, 11 verified runs + 2 test runs)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-modular/src/lib.rs"
# Trust: `build/host` is a symlink to `build/<host-triple>`, so this resolves on
# every platform. It used to name `aarch64-apple-darwin` literally, which meant
# that on any non-Apple host this gate could only ever print
#   REFUSE: no targo at .../build/aarch64-apple-darwin/stage1/bin/targo
# and exit 2 — measured 2026-08-31 on aarch64-unknown-linux-gnu, where that
# directory does not exist at all, for all 19 strict gates at once. A soundness
# gate that cannot run on the host it is invoked from is not a strict gate.
TARGO="${TARGO:-$REPO_ROOT/build/host/stage1/bin/targo}"

# ---------------------------------------------------------------------------
# The pristine verdict, in one place. Every number here was MEASURED on this
# crate; none was transplanted from a sibling gate.
# ---------------------------------------------------------------------------
PRISTINE_COVERAGE='Coverage: 28/28 eligible function bodies verified (complete)'
PRISTINE_SUMMARY='Summary: 118 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(118 total\)'
PRISTINE_KINDS='proved by kind: arithmetic_overflow_add=4, arithmetic_overflow_mul=14, arithmetic_overflow_sub=6, division_by_zero=1, hardened_panic_boundary=50, postcondition=17, remainder_by_zero=26'
PRISTINE_TESTS='test result: ok. 16 passed; 0 failed'

[ -x "$TARGO" ] || { echo "REFUSE: no targo at $TARGO (set TARGO=...)"; exit 2; }
# A stage whose targo was never rebuilt ships upstream cargo under the name
# `targo` and verifies NOTHING while succeeding. `--unverified` is the only
# discriminator that has held under every measurement in this repo:
# `targo trust --help` PASSES on cargo-in-disguise (cargo execs the sibling
# `targo-trust` binary it finds beside itself), and the inode and
# version-string tests were both measured wrong against a real targo.
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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-modular ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-run}"
  no_rustc_error "${STEP:-run}"
}
# `--lib` is load-bearing. A concurrent `x.py check` can rebuild
# `librustc_driver-<hash>.dylib` while stage1 `trustdoc` still references the
# old hash; the doctest stage then dies with SIGABRT and a bare `targo test`
# exits 101 with every unit test passing. That is what turned `trust-utf`'s
# gate red while its strict lane was green, and — worse — it DISARMS a
# wrong-value control, whose whole assertion is "the tests go red" when they
# were already red for an unrelated reason.
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-modular --lib ) > "$LOG" 2>&1
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
# ``verification failed for `<crate>::<fn>``` line for EVERY function. That is
# a byte-perfect imitation of "the mutation refuted exactly what it was
# supposed to refute" — including a composition cascade. An archived
# `trust-ratio` outage log satisfied all four assertions of that crate's
# mutation A verbatim while proving nothing at all, and its gate printed `ok`.
#
# A second, independent environment failure was measured WHILE THIS CRATE WAS
# BEING WRITTEN and is checked here too: a concurrent `x.py build --stage 1`
# replaced `stage1/bin/targo-trust` mid-run, and the lane exited 2 with
# `protected Trust subcommand ... changed while it was running`. Everything
# before that point in the log is a fact about a DIFFERENT binary than the one
# the run started with.
#
# Either one ABORTS the gate as INCONCLUSIVE (exit 3). Never scored as a pass,
# never scored as a refutation.
env_broken() {
  grep -qE 'MemoryAdmission|memory admission failed|could not connect to selected endpoint|Connection refused|changed while it was running|cannot inspect protected Trust path' "$LOG"
}
require_env() { # require_env <label>
  if env_broken; then
    echo "  ENV  $1: the toolchain or its memory broker was unavailable or moved"
    echo "       under the run, so every obligation was refused before solver"
    echo "       dispatch (or adjudicated by a binary that no longer exists)."
    echo "       This run is not a fact about the crate under test. Refusing to"
    echo "       score it as a pass OR as a refutation."
    ENVD="$(grep -oE '(could not connect to selected endpoint [^\"]*|changed while it was running[^\"]*)' "$LOG" | head -1)"
    [ -n "$ENVD" ] && echo "       $ENVD"
    echo "INCONCLUSIVE (environment): re-run when the toolchain is stable."
    echo "       log kept at $LOG"
    exit 3
  fi
}

# A mutation meant to break the PROOF must not have broken the BUILD instead. A
# crate that fails to compile emits NO obligations for what did not lower, so a
# refutation-shaped verdict can be manufactured by a type error that has nothing
# to do with the property under test. Trust's own verification failures are bare
# `error:` lines carrying no code, so keying on `error[E####]` isolates the
# rustc diagnostic without colliding with the §7.2 bundling refusals that
# mutations C and E are SUPPOSED to provoke.
no_rustc_error() { # no_rustc_error <label>
  if grep -qE '^error\[E[0-9]{4}\]' "$LOG"; then
    fail "$1: rustc reported $(grep -oE '^error\[E[0-9]{4}\]' "$LOG" | head -1) — this run is supposed to exercise the PROOF, not the BUILD; obligations for code that did not lower are ABSENT, not refuted"
  fi
  return 0
}

# ---------------------------------------------------------------------------
# G2. `ok` MUST MEAN "THIS SECTION'S OWN CONTENT ASSERTIONS HELD".
#
# `ok   mutation X` printed on `[ "$RC" -eq 0 ]` ALONE would print `ok` for a
# plain rustc type error, a missing driver, or an unrelated regression. Every
# ok-print is therefore QUEUED by `mut_ok` and flushed by `mut_end` at the END
# of the section, once every assertion in that section has had its chance to
# move `fails`.
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

# The kind split, normalised for comparison against PRISTINE_KINDS.
kinds() { grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1; }

echo "trust-modular strict gate:"

# ---------------------------------------------------------------------------
# 1. THE PASS, asserted on exit code, Gate, compile status, coverage AND the
#    kind split — never on the Summary alone.
# ---------------------------------------------------------------------------
STEP="THE PASS"; mut_begin
run
G="$(gate_line)"
# §9.2: a crate can VERIFY completely and fail to SEAL, printing `could not
# seal the final compiler rows ...` at exit 2 and NOTHING else — no `error:`,
# no `Summary:`, no `Gate:`. Assert the Gate line is PRESENT before reading
# anything else, or that failure reads as a pass to every other check here.
[ -n "$G" ] || fail "pristine: no Gate: line — the lane did not run, or the report could not be sealed (§9.2). Everything below is vacuous."
[ "$RC" -eq 0 ] || fail "pristine: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "pristine: Gate is '$G'";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q "$PRISTINE_COVERAGE" "$LOG" \
  || fail "pristine: coverage moved — expected '$PRISTINE_COVERAGE', got '$(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)'"
grep -qE "$PRISTINE_SUMMARY" "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it ABSENT, and assert the
# real safety and functional counts by kind.
KINDS="$(kinds)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
[ "$KINDS" = "$PRISTINE_KINDS" ] \
  || fail "pristine: kind split moved
       expected: $PRISTINE_KINDS
       got:      $KINDS"
mut_ok "pristine  $G  [$PRISTINE_KINDS]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 2. THE SAME PASS UNDER `-Ztrust-policy=certify`.
#    A misspelled TRUSTFLAGS is silently dropped, so first prove the flag path
#    reaches the compiler by requiring a bogus policy to be REJECTED BY NAME.
#    Without this control, "certify passed" is indistinguishable from "certify
#    never ran".
# ---------------------------------------------------------------------------
STEP="CERTIFY"; mut_begin
run "-Ztrust-policy=bogus_not_a_policy"
grep -q "incorrect value \`bogus_not_a_policy\` for unstable option \`trust-policy\`" "$LOG" \
  || fail "TRUSTFLAGS control: a bogus policy was NOT rejected — the flag never reaches the compiler, so the certify run below proves nothing"
rm -f "$LOG"

run "-Ztrust-policy=certify"
G="$(gate_line)"
[ -n "$G" ] || fail "certify: no Gate: line"
[ "$RC" -eq 0 ] || fail "certify: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "certify: Gate is '$G'";; esac
grep -qE "$PRISTINE_SUMMARY" "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
CK="$(kinds)"
[ "$CK" = "$PRISTINE_KINDS" ] || fail "certify: kind split differs from the default policy
       default: $PRISTINE_KINDS
       certify: $CK"
grep -qE 'Publication boundary: [0-9]+ obligation\(s\) passed the compiler, [0-9]+ published, [0-9]+ WITHHELD .*\(0 relabelled unknown' "$LOG" \
  || fail "certify: a favorable compiler row was RELABELLED at the publication boundary — $(grep -oE '^Publication boundary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G  [identical kind split, 0 relabelled at the publication boundary]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — a tier-1 postcondition made FALSE.
#    `residue_clamp` returns `v` unclamped, so `ensures result <= last` is false
#    whenever `v > last`. Measured: the three postcondition rows collapse to two
#    UNKNOWN plus one trusted, `postcondition` drops 17 -> 14, and the refutation
#    is confirmed satisfiable.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate 'pub fn residue_clamp(v: u32, last: u32) -> u32 ensures result <= last ensures result <= v {
    if v > last {
        return last;
    }
    v
}' 'pub fn residue_clamp(v: u32, last: u32) -> u32 ensures result <= last ensures result <= v {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a FALSE postcondition still passed  $G"; else mut_ok "mutation A (residue_clamp returns v unclamped)  rc=$RC  $G"; fi
grep -q "verification failed for \`trust_modular::residue_clamp\`" "$LOG" \
  || fail "mutation A: residue_clamp was NOT refuted"
grep -oE 'unknown by kind: [a-z_=0-9, ]+' "$LOG" | grep -q 'postcondition=2' \
  || fail "mutation A: the two per-branch postcondition rows did not go UNKNOWN — $(grep -oE 'unknown by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
kinds | grep -q 'postcondition=14' \
  || fail "mutation A: the proved postcondition count is not 17-3=14 — $(kinds)"
grep -q 'direct SMT confirmed a satisfiable typed query fact' "$LOG" \
  || fail "mutation A: the violation was never confirmed satisfiable — this is a capability gap, not a caught bug"
# SPECIFICITY. The four presence assertions above cannot tell "the break hit
# exactly its subject" apart from "the whole crate went red", and an
# environment failure produces the latter while satisfying them verbatim (G1).
# `residue_clamp` has NO in-crate caller — established two ways: (1) call
# graph, `grep -n 'residue_clamp(' crates/trust-modular/src/lib.rs` matches
# only its own definition and the tests; (2) MEASUREMENT — this exact mutation
# was run standalone on 2026-08-30 and the log named EXACTLY one subject.
for f in modulus_floor is_zero_modulus is_residue is_reduced_pair reduce reduce_wide \
         add_mod sub_mod mul_mod neg_mod double_mod sqr_mod pow_mod pow_mod_step \
         add_reduced sub_reduced neg_reduced double_reduced reduce_once mod_last \
         quotient gcd_step bezout_step inv_check is_divisible congruent pow_factor; do
  grep -q "verification failed for \`trust_modular::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a residue_clamp-only break — it does not depend on residue_clamp, so this run went red for an unrelated reason and says nothing about the tier-1 contract"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — a tier-2 SAFETY obligation made false: `reduce` loses its
#    `m == 0` guard, so `% m` can divide by zero. The gate must see a
#    REFUTATION, not a coverage gap — assert the three facts that separate
#    them, all ABSENT from the pristine run.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate 'pub fn reduce(x: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    ((x as u64) % mm) as u32
}' 'pub fn reduce(x: u32, m: u32) -> u32 {
    let mm: u64 = m as u64;
    ((x as u64) % mm) as u32
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an unguarded remainder still passed  $G"; else mut_ok "mutation B (reduce loses its m==0 guard)  rc=$RC  $G"; fi
grep -q 'Verdict: HAS VIOLATIONS' "$LOG" \
  || fail "mutation B: the verdict is not HAS VIOLATIONS — $(grep -oE '^\s*Verdict: .*' "$LOG" | tail -1)"
grep -qE '^\s*\[(FAILED|UNKNOWN)\] \[remzero\]' "$LOG" \
  || fail "mutation B: no unfavourable [remzero] row at all — the obligation was not even emitted"
grep -qE '^\s*\[FAILED\] \[hardened_panic_boundary\]' "$LOG" \
  || fail "mutation B: the hardened twin was not FAILED — a division-by-zero with no runtime fallback must refute outright"
grep -q 'solver refuted the encoded VC' "$LOG" \
  || fail "mutation B: no refutation recorded — the gate saw a coverage gap, not a refutation"
grep -q 'direct SMT confirmed a satisfiable typed query fact' "$LOG" \
  || fail "mutation B: the violation was never confirmed satisfiable — no counterexample exists, so this is a capability gap, not a caught bug"
grep -q "verification failed for \`trust_modular::reduce\`" "$LOG" \
  || fail "mutation B: reduce was not named"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — a bundled MEMBER broken, and the ATTRIBUTION that follows.
#    `sub_reduced` loses the `m < y` guard that discharges its borrow. Its own
#    rows then go unproven, which is exactly what makes it unbundlable, so the
#    run raises a SECOND and THIRD error against its two callers with §11.5's
#    `refused Assert-bearing member` note.
#
#    §11.5 records (from `trust-interval`) that the member itself can be
#    SILENT in this situation. Here it is not: `sub_reduced` gets a `Trust
#    strict verification failed` line of its own and the callers get `Trust
#    FULL verification failed ... lowering did not complete`. Both forms are
#    asserted, because the difference between them is the whole content of the
#    §11.5 rule and a gate that asserted only one would be stale in one
#    direction or the other.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    if m < y {
        return NOT_A_RESIDUE;
    }
    let d: u32 = m - y;' '    let d: u32 = m - y;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an unguarded borrow still passed  $G"; else mut_ok "mutation C (sub_reduced loses its m<y guard)  rc=$RC  $G"; fi
grep -q 'refused Assert-bearing member `trust_modular::sub_reduced`' "$LOG" \
  || fail "mutation C: no 'refused Assert-bearing member' note naming sub_reduced — the bundling refusal §11.5 describes did not happen"
for f in sub_mod bezout_step; do
  grep -q "Trust full verification failed for \`trust_modular::$f\`" "$LOG" \
    || fail "mutation C: $f did not report the caller-side lowering refusal — §11.5's attribution rule has changed"
done
grep -q "Trust strict verification failed for \`trust_modular::sub_reduced\`" "$LOG" \
  || fail "mutation C: the MEMBER itself was silent. That is the shape §11.5 recorded for trust-interval; here it was measured LOUD. Re-measure §14.4 before assuming either."
# SPECIFICITY: the complement of sub_reduced's callers. `grep -n
# 'sub_reduced(' crates/trust-modular/src/lib.rs` matches its definition,
# `sub_mod` and `bezout_step` and nothing else; `add_reduced` is the sibling
# helper with the same shape and a different caller.
for f in add_reduced double_reduced neg_reduced reduce_once add_mod mul_mod pow_mod; do
  grep -q "verification failed for \`trust_modular::$f\`" "$LOG" \
    && fail "mutation C: $f was refuted although it never calls sub_reduced — this run went red for an unrelated reason"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. THE TESTS, AND THE MUTATION THEY ALONE CAN CATCH.
#    Everything above is a statement about obligations. Mutation D changes the
#    crate's ANSWERS while leaving BOTH discharged clauses true, so the strict
#    lane accepts it at exit 0 with a byte-identical kind split and only the
#    unit tests refuse it. They are therefore asserted to pass, and asserted to
#    fail.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then
  fail "pristine: unit tests failed (rc=$RC) — $(grep -oE '^test result: .*' "$LOG" | head -1)"
else
  grep -qE "^$PRISTINE_TESTS" "$LOG" \
    || fail "pristine tests: expected '$PRISTINE_TESTS' — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# MUTATION D — a WRONG ANSWER under two contracts that both stay TRUE.
# `residue_clamp`'s clamping arm returns 0. `0 <= last` and `0 <= v` both hold,
# so the pair of clauses that pins the result to `<= min(v, last)` is untouched;
# the return-site count is unchanged, so `postcondition=17` is unchanged.
# Measured 2026-08-30: exit 0, identical Summary, identical coverage, identical
# kind split — and `residue_clamp(9, 3) == 0` instead of 3.
mutate '    if v > last {
        return last;
    }
    v
}' '    if v > last {
        return 0;
    }
    v
}'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation D: the strict lane REFUTED a wrong clamp value under two TRUE clauses (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged two-clause \`ensures\` cannot see the difference is now stale and must be re-measured, not deleted"
fi
case "$VG" in *"PASS [strict lane, exit 0]"*) ;; *) fail "mutation D: Gate is '$VG', expected PASS — the change was supposed to alter no obligation at all";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "mutation D: rustc reported errors, so the lane did not actually accept the change"; fi
grep -qE "$PRISTINE_SUMMARY" "$LOG" \
  || fail "mutation D: the row count moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
DK="$(kinds)"
[ "$DK" = "$PRISTINE_KINDS" ] || fail "mutation D: the kind split moved
       pristine: $PRISTINE_KINDS
       mutated:  $DK"
rm -f "$LOG"

runtests
if [ "$RC" -eq 0 ]; then
  fail "mutation D: a clamp that returns 0 passed the unit tests — the tests are not sensitive to the crate's own subject"
else
  mut_ok "mutation D (residue_clamp's clamping arm returns 0)  tests rc=$RC, strict lane rc=$VRC  $VG"
  mut_ok "          (both \`ensures\` clauses stayed TRUE, all 17 postcondition rows still proved, and the strict lane PASSED at rc=0)"
fi
grep -q "residue_clamp_is_min_of_v_and_last ... FAILED" "$LOG" \
  || fail "mutation D: residue_clamp_is_min_of_v_and_last did not catch a clamp that returns 0"
# ... and the mutation must NOT degrade into "everything broke", or the red
# above would say nothing about THIS defect. The CARRIER — the test that
# asserts every discharged clause directly — must stay green, along with the
# two ring-value tests that do not touch the clamp.
for t in tier1_bounds_hold_everywhere add_sub_neg_double_match_u128 mul_mod_matches_repeated_addition; do
  grep -q "$t ... ok" "$LOG" \
    || fail "mutation D: $t also failed, so this is not a demonstration that a TRUE two-clause contract can sit over a wrong answer"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION E — §14.4's boundary, pinned. `bezout_step` inlines
#    `sub_reduced`'s body instead of calling it. Every operator, guard and
#    value is identical; only the call boundary is gone, and
#    `arithmetic_overflow_sub` stops proving.
#
#    This refusal is the QUIETEST class in §4.5: no `error:` line, no
#    per-function `verification failed` note. The exit code, the `Gate:` line
#    and `unknown by kind` are the only signals, and the Gate word is
#    INCONCLUSIVE rather than FAIL. If the compiler ever learns to carry a
#    `%`-derived range across a subtraction in one body, this goes RED and says
#    so, rather than §14.4 going stale.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate '    let t0r: u32 = ((t0 as u64) % mm) as u32;
    sub_reduced(t0r, pr, m)
}' '    let t0r: u32 = ((t0 as u64) % mm) as u32;
    if t0r >= pr {
        return t0r - pr;
    }
    if m < pr {
        return NOT_A_RESIDUE;
    }
    let d: u32 = m - pr;
    let s: u64 = (d as u64) + (t0r as u64);
    if s > 4294967295 {
        return NOT_A_RESIDUE;
    }
    s as u32
}'
run
G="$(gate_line)"
[ -n "$G" ] || fail "mutation E: no Gate: line"
if [ "$RC" -eq 0 ]; then
  fail "mutation E: inlining sub_reduced into bezout_step now PASSES. That is good news for the compiler and it makes §14.4 of docs/STRICT_VERIFICATION_FRAGMENT.md stale — re-measure it and rewrite the entry; do not delete this mutation."
else
  mut_ok "mutation E (bezout_step inlines sub_reduced)  rc=$RC  $G"
fi
case "$G" in *"PASS [strict lane, exit 0]"*) fail "mutation E: Gate says PASS at rc=$RC";; esac
grep -oE 'unknown by kind: [a-z_=0-9, ]+' "$LOG" | grep -q 'arithmetic_overflow_sub=1' \
  || fail "mutation E: the guarded subtraction did not go UNKNOWN — $(grep -oE 'unknown by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
grep -qE '^error: ' "$LOG" \
  && fail "mutation E: an 'error:' line appeared. Measured 2026-08-30 this refusal is SILENT (§4.5's quietest class) — if it is now loud, §14.4's note about how to detect it is stale."
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 8. MUTATION F — §14.2's boundary, pinned, and §14.6 demonstrated in the same
#    run. The four `pow_factor` calls become inline selects. Nothing else
#    changes: same constants, same widening casts, same multiplies.
#
#    Two things must hold. (1) The compiler must FAIL `pow_mod` with
#    `8 unknown out of 32` — two rows per step, exactly the select's multiply
#    and its hardened twin. (2) The published `Summary:` must still read
#    `0 inconclusive`, because those eight rows are ABSENT from the published
#    view rather than reported as unknown. That second assertion is the point:
#    it is what makes a gate keyed on the Summary read this as a pass.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate '    let f3: u32 = pow_factor(base, exp & 8);
    let f2: u32 = pow_factor(base, exp & 4);
    let f1: u32 = pow_factor(base, exp & 2);
    let f0: u32 = pow_factor(base, exp & 1);
    let mm: u64 = m as u64;' '    let f3: u32 = if exp & 8 == 0 { 1 } else { base };
    let f2: u32 = if exp & 4 == 0 { 1 } else { base };
    let f1: u32 = if exp & 2 == 0 { 1 } else { base };
    let f0: u32 = if exp & 1 == 0 { 1 } else { base };
    let mm: u64 = m as u64;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation F: an INLINE select now proves. §14.2 of docs/STRICT_VERIFICATION_FRAGMENT.md is stale — re-measure it, and consider deleting pow_factor; do not delete this mutation."
else
  mut_ok "mutation F (pow_mod's four pow_factor calls become inline selects)  rc=$RC  $G"
fi
grep -q "verification failed for \`trust_modular::pow_mod\`" "$LOG" \
  || fail "mutation F: pow_mod was not refuted"
grep -q 'note: summary: 0 trusted, 24 certified, 0 failed, 8 unknown, 0 runtime-checked, 0 skipped out of 32' "$LOG" \
  || fail "mutation F: the compiler's own per-function summary is not '24 certified / 8 unknown out of 32' — $(grep -oE 'note: summary: [0-9]+ trusted[^\"]*out of [0-9]+' "$LOG" | head -1)"
# §14.6, demonstrated rather than asserted in prose: the PUBLISHED view of this
# same run is clean. If this ever stops holding, the transport has been fixed
# and §14.6 must be re-measured — which is why the failure message says so.
grep -qE '^Summary: [0-9]+ proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive' "$LOG" \
  || fail "mutation F: the published Summary now reports the unknown rows. That is a FIX to the transport and §14.6/§4.3 must be re-measured — this assertion is the demonstration, not a requirement."
mut_ok "          (§14.6: the published Summary of that same run reads '$(grep -oE '^Summary: [^(]*' "$LOG" | tail -1)' — the 8 unknown rows are ABSENT from it, not reported)"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 9. MUTATION G — §14.3's step ceiling, pinned. `pow_mod` grows from FOUR
#    square-and-multiply steps to SIX. Measured 2026-08-30: four steps is
#    32/32; five is a solver TIMEOUT (20 unknown, 20 timeouts of 40); six and
#    seven fail to lower outright. Six is chosen because its failure mode is
#    the structural one, not the budget-dependent one.
# ---------------------------------------------------------------------------
STEP="MUTATION G"; mut_begin
mutate '    let f3: u32 = pow_factor(base, exp & 8);
    let f2: u32 = pow_factor(base, exp & 4);
    let f1: u32 = pow_factor(base, exp & 2);
    let f0: u32 = pow_factor(base, exp & 1);
    let mm: u64 = m as u64;

    let a3: u64 = 1;' '    let f5: u32 = pow_factor(base, exp & 32);
    let f4: u32 = pow_factor(base, exp & 16);
    let f3: u32 = pow_factor(base, exp & 8);
    let f2: u32 = pow_factor(base, exp & 4);
    let f1: u32 = pow_factor(base, exp & 2);
    let f0: u32 = pow_factor(base, exp & 1);
    let mm: u64 = m as u64;

    let a5: u64 = 1;
    let s5: u64 = a5 * a5;
    let t5: u32 = (s5 % mm) as u32;
    let w5: u64 = t5 as u64;
    let p5: u64 = w5 * (f5 as u64);
    let c5: u32 = (p5 % mm) as u32;

    let a4: u64 = c5 as u64;
    let s4: u64 = a4 * a4;
    let t4: u32 = (s4 % mm) as u32;
    let w4: u64 = t4 as u64;
    let p4: u64 = w4 * (f4 as u64);
    let c4: u32 = (p4 % mm) as u32;

    let a3: u64 = c4 as u64;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation G: a SIX-step square-and-multiply now verifies. §14.3's ceiling has moved — re-measure it and widen pow_mod's exponent; do not delete this mutation."
else
  mut_ok "mutation G (pow_mod widened from four steps to six)  rc=$RC  $G"
fi
grep -q "native typed-TrustIr lowering did not complete" "$LOG" \
  || fail "mutation G: six steps did not produce the LOWERING refusal — §14.3 records the failure MODE, not just the fact, and the mode has changed: $(grep -oE '^error: .{0,120}' "$LOG" | head -1)"
grep -oE 'unknown by kind: [a-z_=0-9, ]+' "$LOG" | grep -q 'unsupported_mir=' \
  || fail "mutation G: no unsupported_mir rows — the body lowered after all"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 10. MUTATION H — the peak, RECOMPUTED FOR THIS CRATE and bisected against the
#     compiler rather than derived and shipped (§8.8, §10.6, §12.2, §13.7).
#
#     `mul_mod`'s product peaks at `(2^32-1)^2 == 18446744065119617025`, so the
#     slack under `u64::MAX` is exactly `8589934590`. Unlike `trust-bits`'
#     §12.2 case, the engine here knows exactly the type peak and nothing more:
#     all four bisect points were measured on 2026-08-30 —
#
#       + 4294967294  PASS      + 8589934590  PASS   (peak exactly u64::MAX)
#       + 4294967295  PASS      + 8589934591  FAIL
#
#     Every transplantable coefficient in this file would have been a DEAD
#     control here: `trust-fixed`'s `* 3`, `trust-radix64`'s `16842753` and
#     `trust-timearith`'s `4294967297` are all multipliers, and this row is an
#     addend.
#
#     Note WHICH row fails: the Add, while all 14 Mul rows still prove. §13.7
#     records the same asymmetry, and a gate that asserted the Mul would report
#     a false green.
# ---------------------------------------------------------------------------
STEP="MUTATION H"; mut_begin
mutate '    let p: u64 = (a as u64) * (b as u64);
    (p % mm) as u32
}

/// `(a * a) mod m`.' '    let p: u64 = (a as u64) * (b as u64) + 8589934591;
    (p % mm) as u32
}

/// `(a * a) mod m`.'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation H: a product one past u64::MAX still proved. The peak has moved — bisect it again (the neighbour +8589934590 must still PASS) and rewrite this section; do not widen the coefficient blindly."
else
  mut_ok "mutation H (mul_mod's product + 8589934591, one past the type slack)  rc=$RC  $G"
fi
grep -q "verification failed for \`trust_modular::mul_mod\`" "$LOG" \
  || fail "mutation H: mul_mod was not refuted"
grep -oE 'unknown by kind: [a-z_=0-9, ]+' "$LOG" | grep -q 'arithmetic_overflow_add=1' \
  || fail "mutation H: the ADD did not go unknown — $(grep -oE 'unknown by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
kinds | grep -q 'arithmetic_overflow_mul=14' \
  || fail "mutation H: a Mul row stopped proving. The failure is supposed to be the ADD carrying the sum past the type, exactly as §13.7 records — if the Mul moved, this control is measuring something else: $(kinds)"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 11. The restore actually restored. A gate that leaves a mutation behind turns
#     the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
STEP="RESTORE"; mut_begin
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"
mut_ok "restore   source is byte-identical to the pristine tree"

mut_end
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
