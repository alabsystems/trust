#!/usr/bin/env bash
# trust_endian_strict_gate.sh — pin `crates/trust-endian` at a NON-VACUOUS pass
# of the authenticated strict lane, on BOTH policies, with live mutation
# controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-endian` is the fourth `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it, after
# `trust-ratio`, `trust-hex` and `trust-utf`. Measured 2026-08-29, identically
# under the default `unix_hardened` policy and under `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 106 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 16/16 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=24, arithmetic_overflow_mul=24,
#                   hardened_panic_boundary=48, postcondition=10
#
# A pass is worth nothing on its own, and every assertion below exists for one
# of the five reasons this repo has paid for:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower
#     and reports `0 failed` with `Coverage: complete`. The compile status is
#     asserted, never inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`. The kind split
#     is asserted and `unreachable` is asserted ABSENT. All 106 rows here are
#     10 postconditions + 48 primary safety + 48 hardened twins.
#  3. A pass never seen to fail is not evidence. Four mutations run, three
#     refuting a different mechanism and one that must NOT be refuted (below).
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it BY NAME.
#  5. Proofs cover overflow and discharged contracts — NOT whether the answer is
#     right.
#
# MUTATION D IS THE POINT OF THIS GATE
# ------------------------------------
# This crate's entire subject is which byte carries which coefficient, and NO
# obligation it has can see that. Swapping two coefficients in `u32_le` leaves
# every product and every partial sum in range, so the strict lane still returns
# EXIT 0 with all 106 rows proved while `u32_le(0,0,1,0)` returns 16777216
# instead of 65536. Mutation D performs that swap and asserts BOTH halves: the
# lane passes, and the unit tests go red. That demonstrates, rather than
# asserts, that a proved safety obligation is not a proved specification.
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit.
#   * A per-function `[VERIFIED] (n obligations: n proved ...)` transport row
#     can be published for a function the compiler HARD-ERRORED on.
# So every assertion is on the EXIT CODE, the `Gate:` line, and the absence of
# `error:` lines — never on the Summary alone and never on a per-function row.
#
# Usage:  scripts/trust_endian_strict_gate.sh          (~3 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-endian/src/lib.rs"
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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-endian ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-run}"
  no_rustc_error "${STEP:-run}"
}
# `--lib` is load-bearing, and was added after this gate went red for a reason
# that had nothing to do with the crate. A concurrent `x.py check` rebuilt
# `librustc_driver-<hash>.dylib`; stage1 `trustdoc` still referenced the old
# hash and died with `dyld: Library not loaded` / SIGABRT. The crate has NO
# doctests (its examples are ```text), all 11 unit tests passed, and `targo
# test` still exited 101 — so a bare rc assertion reports a crate failure when
# the sysroot is transiently inconsistent. Scope to the unit tests, which are
# what this gate is evidence about, and keep asserting the exact result line
# below so the scoping cannot hide a real red.
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-endian --lib ) > "$LOG" 2>&1
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

echo "trust-endian strict gate:"

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
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 16/16 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 16/16 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 106 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(106 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=24 arithmetic_overflow_mul=24 \
            hardened_panic_boundary=48 postcondition=10; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
mut_ok "pristine  $G  [10 postcondition + 48 safety + 48 hardened-twin, 0 unreachable]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 2. THE SAME PASS UNDER `-Ztrust-policy=certify`.
#    A misspelled TRUSTFLAGS is dropped, so first prove the flag path reaches
#    the compiler by requiring a bogus policy to be REJECTED BY NAME. Without
#    this control, "certify passed" is indistinguishable from "certify never
#    ran".
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
grep -qE 'Summary: 106 proved, 0 failed, .*0 inconclusive \(106 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — the u32 COMPOSITION CARRIER broken.
#    Every tier-1 bound on the 16- and 32-bit reads is inherited from
#    `clamp_u32`'s postcondition. Breaking it must refute all four of those
#    wrappers as well as `clamp_u32` itself. If it ever refutes only
#    `clamp_u32`, the composition stopped carrying and those bounds are being
#    proved by something else — the shape that lets a wrapper keep a green row
#    after its evidence went away.
#
#    `clamp_u64` is deliberately NOT touched, so the two `len64_*` wrappers must
#    stay green in the same run. That makes this a specificity assertion as well
#    as a sensitivity one.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate 'fn clamp_u32(v: u32, hi: u32) -> u32 ensures result <= hi {
    if v > hi { hi } else { v }
}' 'fn clamp_u32(v: u32, hi: u32) -> u32 ensures result <= hi {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a broken composition carrier still passed  $G"; else mut_ok "mutation A (clamp_u32 stops clamping)  rc=$RC  $G"; fi
for f in clamp_u32 len16_le len16_be len32_le len32_be; do
  grep -q "verification failed for \`trust_endian::$f\`" "$LOG" \
    || fail "mutation A: $f was NOT refuted — composition is not carrying the bound"
done
for f in len64_le len64_be; do
  grep -q "verification failed for \`trust_endian::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted, but it composes from clamp_u64 which was not touched"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — the u64 COMPOSITION CARRIER broken.
#    The 64-bit contract lane is exercised by nothing else in this tree, so
#    without this control `len64_le`/`len64_be` could silently stop being
#    checked while the u32 lane kept the crate green. The complement of
#    mutation A: exactly the two 64-bit wrappers must fall, and the four
#    32-bit ones must not.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate 'fn clamp_u64(v: u64, hi: u64) -> u64 ensures result <= hi {
    if v > hi { hi } else { v }
}' 'fn clamp_u64(v: u64, hi: u64) -> u64 ensures result <= hi {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: a broken 64-bit composition carrier still passed  $G"; else mut_ok "mutation B (clamp_u64 stops clamping)  rc=$RC  $G"; fi
for f in clamp_u64 len64_le len64_be; do
  grep -q "verification failed for \`trust_endian::$f\`" "$LOG" \
    || fail "mutation B: $f was NOT refuted — the 64-bit contract lane is not load-bearing"
done
for f in len16_le len32_le; do
  grep -q "verification failed for \`trust_endian::$f\`" "$LOG" \
    && fail "mutation B: $f was refuted, but it composes from clamp_u32 which was not touched"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — a real SAFETY obligation made false.
#    `u16_le`'s peak is `255 + 255 * 256 == 65535`, exactly `u16::MAX`. The
#    proof has NO slack, so raising the coefficient by one overflows `u16` on
#    the top input and the multiply can no longer be proved.
#
#    MEASURED ASYMMETRY (see §4.6 of the fragment map): an unguarded `u8`
#    subtraction is hard-`[FAILED]`, but the same class of defect on wider types
#    is only ever `[UNKNOWN]`. So this asserts what IS assertable — the crate
#    stops compiling and the site stops being proved — and does not demand a
#    witnessed refutation the verifier does not produce at this width.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    b0 as u16 + (b1 as u16) * 256
}' '    b0 as u16 + (b1 as u16) * 257
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an overflowing multiply still passed  $G"; else mut_ok "mutation C (u16_le coefficient 256 -> 257, overflows u16)  rc=$RC  $G"; fi
grep -qE '^\s*\[(FAILED|UNKNOWN)\] \[overflow:(mul|add)\]' "$LOG" \
  || fail "mutation C: no overflow row went FAILED or UNKNOWN — $(grep -oE '\[[A-Z]+\] \[overflow:[a-z]+\]' "$LOG" | head -3 | tr '\n' ' ')"
grep -q 'verification failed for `trust_endian::u16_le`' "$LOG" \
  || fail "mutation C: u16_le did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. THE TESTS, AND THE MUTATION THEY ALONE CAN CATCH.
#    Byte order is outside every obligation this crate has. Swapping the b2 and
#    b3 coefficients in `u32_le` keeps the peak at exactly `u32::MAX`, so every
#    product and every partial sum still proves and the strict lane still exits
#    0 — while the function returns the wrong number for every input in which
#    those two bytes differ. Only the tests can refuse this, so they are
#    asserted to pass AND asserted to fail.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)"; else
  grep -qE '^test result: ok\. 11 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 11 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

mutate '    b0 as u32 + (b1 as u32) * 256 + (b2 as u32) * 65536 + (b3 as u32) * 16777216' \
       '    b0 as u32 + (b1 as u32) * 256 + (b2 as u32) * 16777216 + (b3 as u32) * 65536'
# The verifier must NOT notice — that is the point of this control. If this ever
# starts failing the strict lane, the note below is out of date in a GOOD way
# and should be re-measured rather than deleted.
run
VRC="$RC"
VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation D: the strict lane REFUTED a byte-order swap (rc=$VRC $VG) — welcome news, but this gate's claim that byte order is outside every obligation is now stale and must be re-measured"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation D: a swapped byte order passed the unit tests — the tests are not sensitive to the crate's own subject"; else
  mut_ok "mutation D (u32_le b2/b3 coefficients swapped)  tests rc=$RC, strict lane rc=$VRC"
fi
for t in u32_assembly_agrees_with_core big_endian_is_little_endian_reversed; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation D: $t did not catch a swapped byte order"
done
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — a"
  echo "        coefficient swap changes no product's range and no sum's peak.)"
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
