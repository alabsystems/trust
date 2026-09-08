#!/usr/bin/env bash
# trust_varint_strict_gate.sh — pin `crates/trust-varint` at a NON-VACUOUS pass
# of the authenticated strict lane, on BOTH policies, with live mutation
# controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-varint` is the sixth `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it, after
# `trust-ratio`, `trust-hex`, `trust-utf`, `trust-endian` and `trust-index`.
# Measured
# 2026-08-29, identically under the default `unix_hardened` policy and under
# `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 67 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 15/15 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=9, arithmetic_overflow_mul=8,
#                   arithmetic_overflow_sub=1, hardened_panic_boundary=18,
#                   postcondition=31
#
# A pass is worth nothing on its own, and every assertion below exists for one
# of the five reasons this repo has paid for:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower
#     and reports `0 failed` with `Coverage: complete`. The compile status is
#     asserted, never inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`. The kind split
#     is asserted and `unreachable` is asserted ABSENT. All 67 rows here are
#     31 postconditions + 18 primary safety + 18 hardened twins.
#  3. A pass never seen to fail is not evidence. Five mutations run, four
#     refuting a different mechanism and one that must NOT be refuted (below).
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it BY NAME.
#  5. Proofs cover overflow and discharged contracts — NOT whether the answer is
#     right.
#
# MUTATION D IS THE POINT OF THIS GATE
# ------------------------------------
# This crate's subject is which byte of a LEB128 encoding carries which power of
# 2^7, and NO obligation it has can see that. Swapping the 2^7 and 2^14
# coefficients in `uleb_value` permutes the multiset of coefficients, so every
# product and every partial sum keeps exactly the range it had — the strict lane
# still returns EXIT 0 with all 67 rows proved, while `uleb_value(0x80,0x01,..)`
# returns 16384 instead of 128. Mutation D performs that swap and asserts BOTH
# halves: the lane passes, and NAMED unit tests go red.
#
# Note which test does NOT catch it: `uleb_value_reaches_exactly_2_pow_56_minus_1`
# stays green, because an all-`0xff` input is symmetric under any permutation of
# the coefficients. A gate that pinned only the extremes would have missed this
# entirely, which is why the sweeps are the evidence and the extremes are not.
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit.
#   * A per-function `[VERIFIED] (n obligations: n proved ...)` transport row
#     can be published for a function the compiler HARD-ERRORED on.
# So every assertion is on the EXIT CODE, the `Gate:` line, and the absence of
# `error:` lines — never on the Summary alone and never on a per-function row.
#
# Usage:  scripts/trust_varint_strict_gate.sh          (~3 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-varint/src/lib.rs"
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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-varint ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-run}"
  no_rustc_error "${STEP:-run}"
}
# `--lib` is load-bearing. Measured 2026-08-29 on `trust-endian`: a concurrent
# `x.py check` rebuilt `librustc_driver-<hash>.dylib`, stage1 `trustdoc` still
# referenced the old hash, and the doctest stage died with SIGABRT — `targo
# test` exited 101 with every unit test passing, on a crate with no doctests.
# A bare rc is not a fact about the crate; scope to the unit tests and assert
# the exact result line so the scoping cannot hide a real red.
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-varint --lib ) > "$LOG" 2>&1
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

echo "trust-varint strict gate:"

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
grep -q 'Coverage: 15/15 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 15/15 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 67 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(67 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=9 arithmetic_overflow_mul=8 \
            arithmetic_overflow_sub=1 hardened_panic_boundary=18 postcondition=31; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
mut_ok "pristine  $G  [31 postcondition + 18 safety + 18 hardened-twin, 0 unreachable]"
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
grep -qE 'Summary: 67 proved, 0 failed, .*0 inconclusive \(67 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — the u64 COMPOSITION CARRIER broken.
#    `uleb_clamp_u64`, `table_end` and `prefix_end` all inherit their bound from
#    `clamp_u64`'s postcondition. Breaking it must refute those three wrappers
#    as well as `clamp_u64` itself. If it ever refutes only `clamp_u64`, the
#    composition stopped carrying and those bounds are being proved by something
#    else — the shape that lets a wrapper keep a green row after its evidence
#    went away.
#
#    `clamp_u32` and `clamp_u16` are deliberately NOT touched, so
#    `uleb_clamp_u32` and `special_opcode_clamped` must stay green in the same
#    run. That makes this a specificity assertion as well as a sensitivity one.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate 'fn clamp_u64(v: u64, hi: u64) -> u64 ensures result <= hi {
    if v > hi { hi } else { v }
}' 'fn clamp_u64(v: u64, hi: u64) -> u64 ensures result <= hi {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a broken u64 clamp still passed  $G"; else mut_ok "mutation A (clamp_u64 returns v unclamped)  rc=$RC  $G"; fi
for f in clamp_u64 uleb_clamp_u64 table_end prefix_end; do
  grep -q "verification failed for \`trust_varint::$f\`" "$LOG" \
    || fail "mutation A: $f did not lose its bound — the composition is not carrying it"
done
for f in uleb_clamp_u32 special_opcode_clamped; do
  grep -q "verification failed for \`trust_varint::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a u64-only break — the carriers are not independent"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — an arithmetic OVERFLOW in the decoder.
#    Raising the top coefficient from 2^49 to 2^57 makes the final multiply
#    exceed `u64::MAX` on the engine's own range for the operand. Per the
#    fragment map §4.6 a `u64` overflow is UNKNOWN rather than FAILED, which is
#    fail-closed and is what must be asserted — never `[FAILED]` on u64.
#
#    2^57 and not 2^56: this crate's proofs are NOT tight, and the first draft
#    of this mutation used 2^56 and PASSED. Because the mask is invisible to the
#    interval engine (module docs, "THE CEILING"), the operands are read as
#    [0,255] rather than [0,127], so the pristine eight-term peak is
#    255*(2^56-1)/127 = 1.447e17 against a u64::MAX of 1.845e19 — a factor of
#    ~127 of slack. At 2^56 the peak is 1.837e19, still inside. Only at 2^57
#    does the multiply alone (255 * 2^57 = 3.67e19) cross. `trust-endian`'s
#    sums are exactly tight and this one is not; a mutation copied from that
#    gate without recomputing the peak is a control that cannot fire.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate '    a6 + ((b7 & 127) as u64) * 562949953421312' \
       '    a6 + ((b7 & 127) as u64) * 144115188075855872'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an overflowing decoder still passed  $G"; else mut_ok "mutation B (uleb_value top coefficient 2^49 -> 2^57, multiply overflows u64)  rc=$RC  $G"; fi
grep -qE '^\s*\[(FAILED|UNKNOWN)\] \[overflow:(mul|add)\]|arithmetic overflow \((Mul|Add)\) (RUNTIME CHECKED|UNKNOWN)' "$LOG" \
  || fail "mutation B: no overflow row went FAILED, UNKNOWN or RUNTIME CHECKED — $(grep -oE 'arithmetic overflow \([A-Za-z]+\) [A-Z ]+' "$LOG" | head -3 | tr '\n' ' ')"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — the u8 SUBTRACTION GUARD removed.
#    This is the `dwarf/line.rs:470` defect reintroduced: `opcode -
#    opcode_base` with the guard deleted. Per the fragment map §4.6 an
#    unguarded `u8` subtraction is REFUTED outright — a hard `[FAILED]` row —
#    unlike the `u64` case in mutation B. Asserting the stronger verdict here is
#    correct precisely because the type is narrow.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    if opcode < opcode_base { return 256; }
    (opcode - opcode_base) as u16' \
       '    (opcode - opcode_base) as u16'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an unguarded u8 subtraction still passed  $G"; else mut_ok "mutation C (special_opcode_adjusted underflow guard deleted)  rc=$RC  $G"; fi
grep -qE '\[(FAILED|UNKNOWN)\] \[overflow:sub\]|arithmetic overflow \(Sub\) (FAILED|UNKNOWN|RUNTIME CHECKED)' "$LOG" \
  || fail "mutation C: no subtraction row was refuted — $(grep -oE 'arithmetic overflow \(Sub\) [A-Z ]+' "$LOG" | head -3 | tr '\n' ' ')"
# §11.5 BUNDLING RECORD — `docs/STRICT_VERIFICATION_FRAGMENT.md` §11.5 says a
# callee whose rows go UNPROVEN stops being bundlable, so the compiler raises
# the error against its CALLER and not against the callee. An assertion naming
# the function the mutation broke is therefore wrong whenever that function is
# bundled. Recorded here per site so it is not rediscovered:
# `special_opcode_adjusted` IS bundled — one non-test caller,
# `special_opcode_clamped` (lib.rs:421). Measured green on the 2026-08-29
# baseline run of this gate.
#
# Direction of the risk, which decides how much this matters: if the attribution
# ever moves, `grep -q … || fail` stops matching and this gate goes RED. It is a
# false-RED (fragility) risk, never a false-GREEN one — the opposite of the
# environment defect the G1 block above repairs. Do not "fix" a red here by
# deleting the assertion; read the member's own row first, because
# `member has a guarded or non-entry-prefix Assert` is emitted BOTH for §9.1's
# position refusal and for this unproven-rows refusal, with nothing in the text
# telling them apart.
grep -q 'verification failed for `trust_varint::special_opcode_adjusted`' "$LOG" \
  || fail "mutation C: special_opcode_adjusted did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION E — a CONTRACT that is simply false.
#    `uleb_len` claims `result <= 10`; returning 11 on the last arm makes the
#    clause false on a reachable path. This is distinct from mutation A: there
#    the carrier's body stopped implying its clause, here a leaf's own returned
#    value violates its own clause directly.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate '    if b9 < 128 { return 10; }' '    if b9 < 128 { return 11; }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation E: a false ensures clause still passed  $G"; else mut_ok "mutation E (uleb_len returns 11 against 'ensures result <= 10')  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_varint::uleb_len`' "$LOG" \
  || fail "mutation E: uleb_len kept its bound while returning a value outside it"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. THE TESTS, AND THE MUTATION THEY ALONE CAN CATCH.
#    Which power of 2^7 a byte carries is outside every obligation this crate
#    has. Swapping the 2^7 and 2^14 coefficients in `uleb_value` permutes the
#    coefficient multiset, so no product's range and no sum's peak changes at
#    all — the strict lane still exits 0 while the decoder returns the wrong
#    value for every input whose second and third bytes differ. Only the tests
#    can refuse this, so they are asserted to pass AND asserted to fail.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)"; else
  grep -qE '^test result: ok\. 16 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 16 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

mutate '    let a1 = a0 + ((b1 & 127) as u64) * 128;
    if b1 < 128 { return a1; }
    let a2 = a1 + ((b2 & 127) as u64) * 16384;' \
       '    let a1 = a0 + ((b1 & 127) as u64) * 16384;
    if b1 < 128 { return a1; }
    let a2 = a1 + ((b2 & 127) as u64) * 128;'
# The verifier must NOT notice — that is the point of this control. If this ever
# starts failing the strict lane, the note below is out of date in a GOOD way
# and should be re-measured rather than deleted.
run
VRC="$RC"
VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation D: the strict lane REFUTED a coefficient swap (rc=$VRC $VG) — welcome news, but this gate's claim that the coefficient assignment is outside every obligation is now stale and must be re-measured"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation D: a swapped coefficient passed the unit tests — the tests are not sensitive to the crate's own subject"; else
  mut_ok "mutation D (uleb_value 2^7/2^14 coefficients swapped)  tests rc=$RC, strict lane rc=$VRC"
fi
# Assert WHICH tests fail, by name. A bare rc would be satisfied by a broken
# doctest stage or a compile error, and the control would silently stop testing.
for t in uleb_value_agrees_with_shift_oracle_over_every_two_byte_prefix \
         uleb_value_agrees_with_shift_oracle_per_position \
         uleb_value_agrees_with_shift_oracle_over_random_and_saturated_inputs \
         canonical_encodings_round_trip_through_uleb_value_and_len \
         uleb_clamp_u64_agrees_with_u128_oracle; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation D: $t did not catch a swapped coefficient"
done
# ...and assert the one that CANNOT catch it still passes, so the gate records
# why the sweeps are the evidence: an all-0xff input is symmetric under any
# permutation of the coefficients.
grep -q 'uleb_value_reaches_exactly_2_pow_56_minus_1 ... ok' "$LOG" \
  || echo "       (note: the all-0xff extreme now also catches this; it did not when written)"
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — a"
  echo "        coefficient swap permutes the multiset, changing no range at all.)"
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
