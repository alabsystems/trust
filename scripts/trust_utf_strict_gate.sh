#!/usr/bin/env bash
# trust_utf_strict_gate.sh — pin `crates/trust-utf` at a NON-VACUOUS pass of the
# authenticated strict lane, on BOTH policies, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-utf` is the third `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it. Measured
# 2026-08-29, identically under the default `unix_hardened` policy and under
# `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 70 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive (70 total)
#   Coverage: 22/22 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=10, arithmetic_overflow_mul=7,
#                   arithmetic_overflow_sub=3, hardened_panic_boundary=21,
#                   postcondition=29
#
# A pass is worth nothing on its own, for five reasons this repo has paid for,
# and every assertion below exists for one of them:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower,
#     and reports `0 failed` with `Coverage: complete`. So the compile status is
#     asserted, not inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`; a pass whose
#     rows are mostly `unreachable` deletes no runtime check. So the kind split
#     is asserted and `unreachable` is asserted ABSENT. All 70 rows here are
#     29 postconditions + 20 primary safety + 21 hardened twins.
#  3. A pass never seen to fail is not evidence. Four mutations run, each
#     refuting a DIFFERENT mechanism: a direct contract, the composition that
#     carries the tier-1 bounds, the SECOND clause of the two-clause contract
#     (which nothing else in the tree exercises), and a real safety obligation.
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it by name.
#  5. Proofs cover overflow, underflow and discharged contracts — NOT whether
#     the answer is right. Two `u32 -> u16` casts in this crate are outside
#     every obligation it has (a truncating cast is neither an overflow nor a
#     zero divisor — the hole that let a fully-proved `percent` return 4). The
#     unit tests are therefore part of this gate, and are themselves mutated to
#     prove they can fail.
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit — the trap
#     `trust_strict_pass_frontier.sh` was written for.
#   * A per-function `[VERIFIED] (1 obligations: 1 proved ...)` transport row
#     can be published for a function the compiler HARD-ERRORED on. Measured
#     four times while building this crate.
# So every assertion here is on the EXIT CODE, the `Gate:` line, and the absence
# of `error:` lines — never on the Summary alone and never on a per-function row.
#
# Usage:  scripts/trust_utf_strict_gate.sh          (~3 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-utf/src/lib.rs"
# Trust: `build/host` is a symlink to `build/<host-triple>`, so this resolves on
# every platform. It used to name `aarch64-apple-darwin` literally, which meant
# that on any non-Apple host this gate could only ever print
#   REFUSE: no targo at .../build/aarch64-apple-darwin/stage1/bin/targo
# and exit 2 — measured 2026-08-31 on aarch64-unknown-linux-gnu, where that
# directory does not exist at all, for all 19 strict gates at once. A soundness
# gate that cannot run on the host it is invoked from is not a strict gate.
TARGO="${TARGO:-$REPO_ROOT/build/host/stage1/bin/targo}"

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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-utf ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-run}"
  no_rustc_error "${STEP:-run}"
}
# `--lib` is load-bearing. Measured 2026-08-29 while re-verifying the strict
# frontier: a stage1 `trustdoc` inconsistent with a freshly rebuilt
# `librustc_driver-<hash>.dylib` aborts the doctest stage with
# `(signal: 6, SIGABRT)`, so a bare `targo test` exits 101 with every unit test
# passing on a crate that has NO doctests (all its fences are ```text). That
# turned this gate red and, worse, made the wrong-value mutation control
# VACUOUS — it asserts the tests go red, and they were already red. Scope to
# the unit tests and assert the exact result line. See
# docs/STRICT_VERIFICATION_FRAGMENT.md §5, "Scope the test lane with --lib".
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-utf --lib ) > "$LOG" 2>&1
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

echo "trust-utf strict gate:"

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
# (1) the crate actually compiled — a lowering abort emits no obligations, and a
#     per-function [VERIFIED] row can be published for a hard-errored function.
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 22/22 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 22/22 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 70 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(70 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# (2) NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert
#     the real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=10 arithmetic_overflow_mul=7 arithmetic_overflow_sub=3 \
            hardened_panic_boundary=21 postcondition=29; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
mut_ok "pristine  $G  [29 postcondition + 20 safety + 21 hardened-twin, 0 unreachable]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 2. THE SAME PASS UNDER `-Ztrust-policy=certify`.
#    A misspelled TRUSTFLAGS is dropped, so first prove the flag path reaches
#    the compiler by requiring a bogus policy to be REJECTED BY NAME. Without
#    this control, "certify passed" is indistinguishable from "certify never ran".
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
grep -qE 'Summary: 70 proved, 0 failed, .*0 inconclusive \(70 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — a tier-1 contract made FALSE at its own body.
#    `utf8_head_len` is contracted DIRECTLY (a comparison chain against
#    constants, no clamp wrapper), so it is the control for that mechanism on
#    its own, independent of composition.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate '    if b0 < 245 {
        return 4;
    }
    0
}' '    if b0 < 245 {
        return b0;
    }
    0
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a FALSE postcondition still passed  $G"; else mut_ok "mutation A (utf8_head_len returns the byte)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_utf::utf8_head_len`' "$LOG" \
  || fail "mutation A: utf8_head_len was NOT refuted"
# SPECIFICITY. A presence-only control cannot tell "the break stayed where it
# was put" apart from "the whole crate went red" — and an environment failure
# produces the latter while satisfying the line above verbatim (see G1).
#
# `utf8_head_len` is a LEAF WITH NO NON-TEST CALLERS, so its break must reach
# nothing at all and the complement is the entire rest of the crate. §11.5 does
# not apply for the same reason: with no callers it cannot be bundled, which is
# precisely why it is this gate's direct-contract control.
#
# MEASURED 2026-08-29 by running this mutation standalone: the full log named
# EXACTLY one subject, and none of the twenty-one below.
for f in clamp_scalar clamp_supplementary clamp_low_surrogate \
         is_high_surrogate is_low_surrogate is_surrogate is_scalar_value \
         is_supplementary is_continuation_byte combine_surrogates \
         high_surrogate low_surrogate utf8_len utf8_decode2 utf8_decode3 \
         utf8_decode4 raw_combine_surrogates raw_low_surrogate \
         raw_utf8_decode2 raw_utf8_decode3 raw_utf8_decode4; do
  grep -q "verification failed for \`trust_utf::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a break in the caller-less leaf utf8_head_len — nothing depends on it, so this run went red for an unrelated reason and is not evidence about the direct-contract mechanism"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — the COMPOSITION CARRIER broken.
#    Every tier-1 bound on the decode side is inherited from `clamp_scalar`'s
#    postcondition. Breaking it must refute the three `utf8_decode*` wrappers as
#    well as `clamp_scalar` itself. If it ever refutes only `clamp_scalar`, the
#    composition stopped carrying and those bounds are being proved by something
#    else — the exact shape that lets a wrapper keep a green row after its
#    evidence went away.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate 'fn clamp_scalar(v: u32) -> u32 ensures result <= 1114112 {
    if v > 1114112 { 1114112 } else { v }
}' 'fn clamp_scalar(v: u32) -> u32 ensures result <= 1114112 {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: a broken composition carrier still passed  $G"; else mut_ok "mutation B (clamp_scalar stops clamping)  rc=$RC  $G"; fi
for f in clamp_scalar utf8_decode2 utf8_decode3 utf8_decode4; do
  grep -q "verification failed for \`trust_utf::$f\`" "$LOG" \
    || fail "mutation B: $f was NOT refuted — composition is not carrying the bound"
done
# SPECIFICITY. `clamp_scalar` carries the bound for the three `utf8_decode*`
# wrappers and NOTHING else: the surrogate side goes through
# `clamp_supplementary` and `clamp_low_surrogate`, and the eight predicates plus
# `high_surrogate`, `utf8_head_len` and `utf8_len` carry their own bounds with
# no clamp at all. So a `clamp_scalar`-only break must leave all eighteen alone.
#
# MEASURED 2026-08-29 standalone: EXACTLY four subjects, all four in the `Trust
# strict verification failed for` form and with no `refused Assert-bearing
# member` note in the run — so the three wrappers are named because each
# independently lost its own postcondition row, not by §11.5 attribution.
for f in clamp_supplementary clamp_low_surrogate is_high_surrogate \
         is_low_surrogate is_surrogate is_scalar_value is_supplementary \
         is_continuation_byte combine_surrogates high_surrogate low_surrogate \
         utf8_head_len utf8_len raw_combine_surrogates raw_low_surrogate \
         raw_utf8_decode2 raw_utf8_decode3 raw_utf8_decode4; do
  grep -q "verification failed for \`trust_utf::$f\`" "$LOG" \
    && fail "mutation B: $f was refuted by a clamp_scalar-only break — it is not on the decode clamp chain, so either this run went red for an unrelated reason (not evidence about composition) or the tier-1 bounds are not independent"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — the SECOND clause of the two-clause contract.
#    `combine_surrogates` carries `ensures result <= 1114112` AND
#    `ensures result >= 65536`. Nothing else in this tree uses two clauses, so
#    without this control the lower bound could silently stop being checked
#    while the upper one kept the row green. Breaking ONLY the lower half of
#    `clamp_supplementary` must still refute both it and `combine_surrogates`.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    if v < 65536 {
        return 65536;
    }
    v
}' '    if v < 65536 {
        return v;
    }
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: a FALSE second ensures clause still passed — the lower bound is not being checked  $G"; else mut_ok "mutation C (clamp_supplementary drops its lower bound)  rc=$RC  $G"; fi
for f in clamp_supplementary combine_surrogates; do
  grep -q "verification failed for \`trust_utf::$f\`" "$LOG" \
    || fail "mutation C: $f was NOT refuted — the second clause is not load-bearing"
done
# SPECIFICITY, and it is what makes this a control on the SECOND CLAUSE rather
# than on the crate. Only the lower half of `clamp_supplementary` moves, and
# `combine_surrogates` is its only caller. If the twenty below also went red,
# the run would say nothing about which clause is load-bearing.
#
# MEASURED 2026-08-29 standalone: EXACTLY two subjects, both `Trust strict`,
# no `refused Assert-bearing member` note. Note in particular that
# `clamp_scalar` and the three `utf8_decode*` wrappers stay GREEN in the same
# run — the upper-bound chain is untouched, which is the discrimination this
# mutation exists to make.
for f in clamp_scalar clamp_low_surrogate is_high_surrogate is_low_surrogate \
         is_surrogate is_scalar_value is_supplementary is_continuation_byte \
         high_surrogate low_surrogate utf8_head_len utf8_len utf8_decode2 \
         utf8_decode3 utf8_decode4 raw_combine_surrogates raw_low_surrogate \
         raw_utf8_decode2 raw_utf8_decode3 raw_utf8_decode4; do
  grep -q "verification failed for \`trust_utf::$f\`" "$LOG" \
    && fail "mutation C: $f was refuted by a lower-bound-only break in clamp_supplementary — it does not depend on that clause, so this run went red for an unrelated reason and is not evidence that the second clause is checked"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION D — a real SAFETY obligation made false: drop the guard that keeps
#    `hi - 55296` from underflowing. This is the obligation `trust-json`'s
#    `parse_escape` discharges by a range pattern, on untrusted input.
#
#    MEASURED ASYMMETRY, and the reason this assertion differs from the one in
#    `trust_hex_strict_gate.sh`. That gate demands a hard `[FAILED]` row and
#    gets one, because its subtraction is on a `u8`. The same defect on a `u32`
#    is only ever reported `[UNKNOWN]` — measured twice here, once by deleting
#    the guard (`overflow:sub`) and once by widening it from 1023 to 8388607 so
#    the multiply genuinely overflows (`overflow:mul`). Neither produced a
#    witnessed refutation. So a `[FAILED]` assertion here would fail against a
#    correctly-behaving compiler; what IS assertable is that the row at that
#    exact site stops being PROVED and the crate stops compiling. Both are
#    fail-closed, which is the property that matters — but do not read this
#    mutation as evidence that the verifier can REFUTE u32 arithmetic. It
#    cannot, and the three contract mutations above are where this gate's
#    witnessed refutations come from.
# ---------------------------------------------------------------------------
STEP="MUTATION D"; mut_begin
mutate '    if hi < 55296 {
        return 1114112;
    }
    let h: u32 = hi - 55296;' '    let h: u32 = hi - 55296;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation D: an unguarded subtraction still passed  $G"; else mut_ok "mutation D (raw_combine_surrogates loses its hi<55296 guard)  rc=$RC  $G"; fi
grep -qE '^\s*\[UNKNOWN\] \[overflow:sub\]' "$LOG" \
  || fail "mutation D: the subtraction row did not go UNKNOWN — $(grep -oE '\[[A-Z]+\] \[overflow:sub\]' "$LOG" | head -3 | tr '\n' ' ')"
grep -q 'strict verification failed for `trust_utf::raw_combine_surrogates`' "$LOG" \
  || fail "mutation D: raw_combine_surrogates did not hard-error"
# §11.5 IS LIVE HERE, AND THIS IS THE ONE PLACE IN THIS GATE WHERE IT IS.
# `raw_combine_surrogates` IS bundled — `combine_surrogates` (lib.rs:295) is its
# caller — so the audit flagged the by-name assertion above as the shape §11.5
# warns about: a callee whose rows go unproven stops being bundlable, and the
# error is then raised against its CALLER.
#
# MEASURED 2026-08-29 by running this mutation standalone, both halves happen:
#   Trust strict verification failed for `trust_utf::raw_combine_surrogates`
#   Trust full   verification failed for `trust_utf::combine_surrogates`
#     = note: … refused Assert-bearing member `trust_utf::raw_combine_surrogates`
#             member has a guarded or non-entry-prefix Assert
# The callee IS still named in its own right (the `strict` line), which is why
# the assertion above holds; but the `full`/member-note pair is the §11.5 shape
# and is the part that does not depend on the attribution level. Assert BOTH, so
# that if the diagnostic ever moves wholly to the caller this gate keeps its
# evidence instead of going red for a reason nobody can read.
grep -q 'verification failed for `trust_utf::combine_surrogates`' "$LOG" \
  || fail "mutation D: the CALLER combine_surrogates was not refused — per §11.5 an unbundlable member's error is raised against its caller, so this is where the refusal must surface"
grep -q 'refused Assert-bearing member `trust_utf::raw_combine_surrogates`' "$LOG" \
  || fail "mutation D: no 'refused Assert-bearing member' note naming raw_combine_surrogates — the unproven-rows refusal §11.5 describes is not what happened, so re-read the member's own row before trusting this mutation's meaning"
# SPECIFICITY. Only the surrogate-combine chain may move; the decode chain, the
# predicates and the low-surrogate side are all independent of it.
for f in clamp_scalar clamp_supplementary clamp_low_surrogate \
         is_high_surrogate is_low_surrogate is_surrogate is_scalar_value \
         is_supplementary is_continuation_byte high_surrogate low_surrogate \
         utf8_head_len utf8_len utf8_decode2 utf8_decode3 utf8_decode4 \
         raw_low_surrogate raw_utf8_decode2 raw_utf8_decode3 \
         raw_utf8_decode4; do
  grep -q "verification failed for \`trust_utf::$f\`" "$LOG" \
    && fail "mutation D: $f was refuted by an underflow confined to raw_combine_surrogates — it does not reach that helper, so this run went red for an unrelated reason and its UNKNOWN row is not evidence about the guard"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. THE TESTS, AND A MUTATION THEY MUST CATCH.
#    A truncating `as` cast is neither an overflow nor a zero divisor, so no
#    obligation above can see one. `raw_low_surrogate`'s mask is exactly such a
#    site: narrow it and every proof in the crate stays green while the value is
#    wrong. Only the tests can refuse this, so they are asserted to pass AND
#    asserted to fail.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)"; else
  grep -qE '^test result: ok\. 17 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 17 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

mutate '    let v: u32 = (cp & 1023) + 56320;' '    let v: u32 = (cp & 511) + 56320;'
# The verifier must NOT notice — that is the point of this control. If this ever
# starts failing the strict lane, the note below is out of date in a GOOD way
# and should be re-measured rather than deleted.
run
VRC="$RC"; rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation E: a wrong-value mask passed the unit tests — the tests are not sensitive to it"; else
  mut_ok "mutation E (raw_low_surrogate mask 1023 -> 511)  tests rc=$RC, strict lane rc=$VRC"
fi
grep -q 'surrogate_split_agrees_with_core_encode_utf16 ... FAILED' "$LOG" \
  || fail "mutation E: the core::encode_utf16 differential did not catch a wrong low surrogate"
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — a"
  echo "        truncating/narrowing mask is neither an overflow nor a zero divisor.)"
fi
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 8. The restore actually restored. A gate that leaves a mutation behind turns
#    the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
STEP="The restore actually restored"; mut_begin
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

mut_end
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
