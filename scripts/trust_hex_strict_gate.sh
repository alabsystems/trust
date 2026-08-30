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
#  3. A pass never seen to fail is not evidence. Four mutations run, each
#     refuting a DIFFERENT mechanism: a direct contract, the composition that
#     carries every other contract, a real safety obligation, and a WRONG ANSWER
#     that every obligation in the crate proves (mutation D, below).
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it by name.
#  5. Proofs here cover overflow, underflow and discharged contracts — NOT
#     whether the answer is right. So the crate's 10 unit tests are RUN by this
#     gate, and they are asserted to fail BY NAME under a mutation the strict
#     lane accepts at exit 0.
#
# The Summary line alone can read like a pass at a nonzero exit. Every assertion
# here is on the EXIT CODE and the `Gate:` line, never the Summary.
#
# MUTATION D IS WHY THE TESTS ARE HERE
# ------------------------------------
# `raw_hex_pair_value` computes `(h as u16) * 16 + (l as u16)` behind two
# `> 15` guards. Swapping the coefficient 16 for 15 leaves EVERY obligation in
# the crate true: the peak becomes `15 * 15 + 15 == 240`, nowhere near
# `u16::MAX`, so the multiplication and addition rows still prove; 240 is still
# `<= 256`, so `clamp256` still never fires and `hex_pair_value`'s discharged
# `ensures result <= 256` is still TRUE; and `raw_hex_quad_value` peaks at
# `240 * 256 + 240 == 61680 <= 65536`, so the quad contract survives too.
# Measured 2026-08-29: the strict lane returns EXIT 0 with the row count, the
# coverage and the kind split byte-identical to pristine — while
# `hex_pair_value(b'a', b'5')` returns 155 instead of 165.
#
# The coefficient was RECOMPUTED for this crate rather than transplanted. A
# sibling gate (`trust_varint_strict_gate.sh`) copied `trust-endian`'s 2^56
# constant into a crate with ~127x more slack and the control never overflowed;
# it had to be strengthened to 2^57. A control whose peak was not recomputed is
# a control that cannot fire.
#
# The mutation is asserted in BOTH directions: two named tests must go red, and
# `clamps_never_fire_on_a_real_input` and `the_contracted_bounds_hold_at_runtime_too`
# must stay GREEN — so it cannot degrade into "everything broke", which is the
# state in which a wrong-value control proves nothing.
#
# Usage:  scripts/trust_hex_strict_gate.sh     (~1 min, 7 verified runs + 2 test runs)
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
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-hex --lib ) > "$LOG" 2>&1
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

echo "trust-hex strict gate:"

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
mut_ok "pristine  $G  [16 postcondition + 13 safety + 12 hardened-twin, 0 unreachable]"
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
grep -qE 'Summary: 41 proved, 0 failed, .*0 inconclusive \(41 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — a tier-1 contract made FALSE at its own body.
#    `low_nibble` is the one contract proved directly (arithmetic-free body,
#    constant bound) rather than by composition, so it is the control for that
#    mechanism on its own.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate 'pub fn low_nibble(byte: u8) -> u8 ensures result <= 15 {
    byte & 15
}' 'pub fn low_nibble(byte: u8) -> u8 ensures result <= 15 {
    byte
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a FALSE postcondition still passed  $G"; else mut_ok "mutation A (low_nibble drops its mask)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_hex::low_nibble`' "$LOG" \
  || fail "mutation A: low_nibble was NOT refuted"
# SPECIFICITY. A presence-only control cannot tell "the break stayed where it
# was put" apart from "the whole crate went red" — and an environment failure
# produces the latter while satisfying the line above verbatim (see G1).
#
# `low_nibble` is a LEAF WITH NO CALLERS AT ALL: `low_nibble(high_nibble(byte))`
# appears only in a doc comment (lib.rs:212) and a test (:378), never in
# non-test code. So its break must reach nothing whatsoever, and the complement
# is the entire rest of the crate — the sharpest specificity control available
# in this gate. §11.5 does not apply: with no callers, `low_nibble` cannot be
# bundled, which is exactly why this mutation is the direct-contract control.
#
# MEASURED 2026-08-29 by running this mutation standalone: the full log named
# EXACTLY one subject, `trust_hex::low_nibble`, and none of the seventeen below.
for f in clamp16 clamp70 clamp102 clamp256 clamp65536 high_nibble \
         lower_hex_digit upper_hex_digit hex_digit_value is_hex_digit \
         hex_pair_value hex_quad_value raw_lower_hex_digit \
         raw_upper_hex_digit raw_hex_digit_value raw_hex_pair_value \
         raw_hex_quad_value; do
  grep -q "verification failed for \`trust_hex::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a break in the caller-less leaf low_nibble — nothing depends on it, so this run went red for an unrelated reason and is not evidence about the direct-contract mechanism"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — the COMPOSITION CARRIER broken.
#    Every tier-1 bound except `low_nibble`'s is inherited from a private
#    `clamp*` postcondition. Breaking `clamp102` must refute `lower_hex_digit`
#    as well as `clamp102` itself. If it ever refutes only `clamp102`, the
#    composition stopped carrying and `lower_hex_digit`'s bound is being proved
#    by something else — which is the exact shape that would let a wrapper keep
#    a green row after its evidence went away.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate 'fn clamp102(v: u8) -> u8 ensures result <= 102 {
    if v > 102 { 102 } else { v }
}' 'fn clamp102(v: u8) -> u8 ensures result <= 102 {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: a broken composition carrier still passed  $G"; else mut_ok "mutation B (clamp102 stops clamping)  rc=$RC  $G"; fi
for f in clamp102 lower_hex_digit; do
  grep -q "verification failed for \`trust_hex::$f\`" "$LOG" \
    || fail "mutation B: $f was NOT refuted — composition is not carrying the bound"
done
# SPECIFICITY. `clamp102` is used by exactly ONE function, `lower_hex_digit`
# (lib.rs:232). The other four clamps and every other wrapper are on independent
# chains — `upper_hex_digit` goes through `clamp70`, `hex_digit_value` through
# `clamp16`, `hex_pair_value` through `clamp256`, `hex_quad_value` through
# `clamp65536` — so a `clamp102`-only break must leave all sixteen alone.
#
# MEASURED 2026-08-29 standalone: EXACTLY two subjects, both in the `Trust
# strict verification failed for` form with no `refused Assert-bearing member`
# note in the run. §11.5 NOTE: `clamp102` IS bundled (`lower_hex_digit` calls
# it), so the audit flagged the by-name assertion above as the shape §11.5
# warns about. The measurement settles it — the callee gets its OWN `strict`
# line here because its postcondition is refuted outright rather than merely
# left unproven, which is the case §11.5 does not cover. Note also that a §11.5
# attribution shift would make the presence assertion FAIL, not silently pass:
# it is a false-red risk, never a false-green one.
for f in clamp16 clamp70 clamp256 clamp65536 low_nibble high_nibble \
         upper_hex_digit hex_digit_value is_hex_digit hex_pair_value \
         hex_quad_value raw_lower_hex_digit raw_upper_hex_digit \
         raw_hex_digit_value raw_hex_pair_value raw_hex_quad_value; do
  grep -q "verification failed for \`trust_hex::$f\`" "$LOG" \
    && fail "mutation B: $f was refuted by a clamp102-only break — it is on an independent clamp chain, so either this run went red for an unrelated reason (not evidence about composition) or the tier-1 bounds are not independent"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — a real SAFETY obligation made false: drop the guard that keeps
#    `ascii - 48` from underflowing. This must produce a hard `[FAILED]` row,
#    not merely an `unknown`; an unknown would mean the gate is only detecting
#    coverage gaps. This is the obligation `trust-json`'s `decode_hex_escape`
#    discharges by inspection, on untrusted input.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    if ascii < 48 {
        return 16;
    }
    if ascii < 58 {' '    if ascii < 58 {'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an unguarded subtraction still passed  $G"; else mut_ok "mutation C (raw_hex_digit_value loses its ascii<48 guard)  rc=$RC  $G"; fi
grep -qE '^\s*\[FAILED\] \[overflow:sub\]' "$LOG" \
  || fail "mutation C: no [FAILED] [overflow:sub] row — the gate saw a coverage gap, not a refutation"
# SPECIFICITY, and this is the one mutation in this gate where §11.5 is LIVE.
# MEASURED 2026-08-29 standalone: seven subjects, of which SIX are in the
# `Trust full verification failed for` form and the run carries
# ``refused Assert-bearing member `trust_hex::raw_hex_digit_value``` — i.e. the
# broken callee's rows became unproven, it therefore stopped being bundlable,
# and the error was raised against its callers exactly as §11.5 describes.
# Asserting `verification failed for raw_hex_digit_value` alone would have been
# the fragile form; the row-shape assertion above plus this complement do not
# depend on which level the diagnostic is attributed to.
#
# The eleven below are the decode chain's complement: the five clamps, the two
# nibble accessors, and the ENCODE side (`lower_hex_digit`/`upper_hex_digit`
# and their `raw_*` helpers), none of which reaches `raw_hex_digit_value`.
for f in clamp16 clamp70 clamp102 clamp256 clamp65536 low_nibble high_nibble \
         lower_hex_digit upper_hex_digit raw_lower_hex_digit \
         raw_upper_hex_digit; do
  grep -q "verification failed for \`trust_hex::$f\`" "$LOG" \
    && fail "mutation C: $f was refuted by a decode-side underflow — the encode side and the clamps do not reach raw_hex_digit_value, so this run went red for an unrelated reason and its [FAILED] row is not evidence about the guard"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. THE TESTS, AND THE MUTATION THEY ALONE CAN CATCH.
#    Everything above this point is a statement about obligations. Mutation D
#    changes the crate's ANSWERS while leaving every obligation true, so the
#    strict lane accepts it at exit 0 and only the unit tests refuse it. They
#    are therefore asserted to pass, and asserted to fail.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then
  fail "pristine: unit tests failed (rc=$RC) — $(grep -oE '^test result: .*' "$LOG" | head -1)"
else
  grep -qE '^test result: ok\. 10 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 10 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# MUTATION D — a WRONG ANSWER that every obligation in the crate proves.
# `15 * 15 + 15 == 240` still fits `u16` and is still `<= 256`, so `clamp256`
# never fires and `hex_pair_value`'s discharged `ensures result <= 256` stays
# TRUE; `raw_hex_quad_value` then peaks at `240 * 256 + 240 == 61680 <= 65536`,
# so the quad contract survives as well. Measured 2026-08-29: the row count, the
# coverage and the kind split come back byte-identical to pristine at exit 0,
# while `hex_pair_value(b'a', b'5')` returns 155 instead of 165.
mutate '    (h as u16) * 16 + (l as u16)' '    (h as u16) * 15 + (l as u16)'
run
VRC="$RC"
VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation D: the strict lane REFUTED a coefficient swap inside a contracted composition (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged \`ensures\` cannot see the difference is now stale and must be re-measured, not deleted"
fi
case "$VG" in *"PASS [strict lane, exit 0]"*) ;; *) fail "mutation D: Gate is '$VG', expected PASS — the swap was supposed to change no obligation at all";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "mutation D: rustc reported errors, so the lane did not actually accept the swap"; fi
grep -qE 'Summary: 41 proved, 0 failed, .*0 inconclusive \(41 total\)' "$LOG" \
  || fail "mutation D: the row count moved — the swap was supposed to change no obligation at all. $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# The discharged contracts specifically, read off the same run: all 16
# postconditions still prove over the wrong answer. That is the claim.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *postcondition=16*) ;; *) fail "mutation D: a postcondition stopped proving — $KINDS";; esac
rm -f "$LOG"

runtests
if [ "$RC" -eq 0 ]; then
  fail "mutation D: a swapped coefficient passed the unit tests — the tests are not sensitive to the crate's own subject"
else
  mut_ok "mutation D (raw_hex_pair_value: *16 -> *15)  tests rc=$RC, strict lane rc=$VRC  $VG"
fi
for t in hex_pair_covers_every_pair_of_bytes hex_quad_reproduces_the_json_unicode_escape; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation D: $t did not catch a swapped coefficient"
done
# ... and the mutation must NOT degrade into "everything broke", or the two reds
# above would say nothing about this defect in particular. The clamp no-op test
# and the runtime bound tripwire must both still pass — which is also the
# runtime half of "the contract is still true over the wrong value".
for t in clamps_never_fire_on_a_real_input the_contracted_bounds_hold_at_runtime_too; do
  grep -q "$t ... ok" "$LOG" \
    || fail "mutation D: $t also failed, so this is not a demonstration that a TRUE contract can sit over a wrong answer"
done
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — the"
  echo "        peak 15*15+15=240 keeps every overflow row and every \`ensures\` TRUE.)"
fi
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. The restore actually restored. A gate that leaves a mutation behind turns
#    the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
STEP="The restore actually restored"; mut_begin
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

mut_end
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
