#!/usr/bin/env bash
# trust_radix64_strict_gate.sh — pin `crates/trust-radix64` at a NON-VACUOUS
# pass of the authenticated strict lane, on BOTH policies, with live mutation
# controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-radix64` is the eighth `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it, after
# `trust-ratio`, `trust-hex`, `trust-utf`, `trust-endian`, `trust-index`,
# `trust-varint` and `trust-checksum`. Measured 2026-08-29 on stage1 driver
# `ee3408608ee41ca2`, identically under the default `unix_hardened` policy and
# under `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 181 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 48/48 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=24, arithmetic_overflow_mul=22,
#                   arithmetic_overflow_sub=6, hardened_panic_boundary=104,
#                   postcondition=25
#
# A pass is worth nothing on its own, and every assertion below exists for one
# of the five reasons this repo has paid for:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower
#     and reports `0 failed` with `Coverage: complete`. The compile status is
#     asserted, never inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`. The kind split
#     is asserted and `unreachable` is asserted ABSENT. All 181 rows here are
#     25 postconditions + 52 primary safety + 104 hardened twins.
#  3. A pass never seen to fail is not evidence. Eight mutations run: six that
#     must refute, and TWO that must NOT (G and H below).
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it BY NAME.
#  5. Proofs cover overflow, division and the tier-1 bounds — NOT whether the
#     answer is right. No obligation in this crate can see which byte got which
#     coefficient or which index got which symbol.
#
# MUTATIONS G AND H ARE THE POINT OF THIS GATE
# --------------------------------------------
# Both are wrong-VALUE changes the strict lane PASSES at exit 0.
#
#   G mutates a TIER-1 function. `raw_b64_symbol`'s `x + 65` becomes `x + 64`,
#     so the whole A-Z run of the RFC 4648 alphabet shifts down one and every
#     base64 string this crate can produce is wrong. `b64_symbol`'s
#     `ensures result <= 123` stays TRUE — the mutated peak is 64+25 == 89 —
#     so the discharged POSTCONDITION survives intact alongside every safety
#     row: a proved *contract*, not merely a proved *safety obligation*,
#     sitting over a wrong answer.
#
#     Note which test does NOT catch it: `b64_alphabet_is_injective` derives
#     its expectation FROM the function under test, and a constant shift keeps
#     the map injective, so it stays green. Only
#     `b64_alphabet_matches_the_rfc4648_table_exhaustively`, which spells the
#     RFC table out as a literal, can refuse it. The gate asserts that
#     injectivity test still PASSES, so the asymmetry is pinned rather than
#     rediscovered — and so the demonstration cannot degrade into "the mutation
#     broke everything".
#
#   H mutates arithmetic whose peak does not move. `b64_group` is
#     `(b0 as u32)*65536 + (b1 as u32)*256 + (b2 as u32)`; swapping `b0` and
#     `b2` leaves the peak at exactly 16777215, because all three operands are
#     `u8` widened to `u32`. No range moves, all 181 rows still prove, and
#     every base64 quantum is byte-reversed. This is `trust-endian` mutation
#     D's demonstration in a second domain: the crate's entire subject is which
#     byte gets which coefficient, and *no* obligation it has can see that.
#
# MUTATION B PINS THE PROOF'S OWN TIGHTNESS, AND THE COEFFICIENT WAS
# RECOMPUTED FOR THIS ARITHMETIC RATHER THAN TRANSPLANTED
# ------------------------------------------------------------------
# `b64_group`'s engine peak is `255*c + 65535` for top coefficient `c`.
# Measured, not assumed: `c == 16842752` gives `4294967295` — exactly
# `u32::MAX` — and still PROVES; `c == 16842753` gives `4294967550` and is
# refused. B uses the second. If B ever stops firing, the peak arithmetic has
# changed and mutation H's claim (that a swap moves no range) needs
# re-measuring.
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit.
#   * A per-function `[VERIFIED] (n obligations: n proved ...)` transport row
#     can be published for a function the compiler HARD-ERRORED on.
# And a third, quieter than either: a refusal can carry NO `error:` line at all
# (a bounds gap keeps its runtime check and downgrades to a warning). So every
# assertion is on the EXIT CODE, the `Gate:` line, and the absence of `error:`
# lines — never on the Summary alone and never on a per-function row.
#
# Usage:  scripts/trust_radix64_strict_gate.sh          (~6 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-radix64/src/lib.rs"
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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-radix64 ) > "$LOG" 2>&1
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
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-radix64 --lib ) > "$LOG" 2>&1
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

echo "trust-radix64 strict gate:"

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
grep -q 'Coverage: 48/48 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 48/48 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 181 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(181 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=24 arithmetic_overflow_mul=22 arithmetic_overflow_sub=6 \
            hardened_panic_boundary=104 postcondition=25; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
mut_ok "pristine  $G  [25 postcondition + 52 safety + 104 hardened-twin, 0 unreachable]"
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
grep -qE 'Summary: 181 proved, 0 failed, .*0 inconclusive \(181 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — the COMPOSITION CARRIER broken.
#    All four alphabet functions inherit their bound from `clamp_u32`'s
#    postcondition. Breaking `clamp_u32` must refute all four as well as
#    `clamp_u32` itself. If it ever refutes only `clamp_u32`, the composition
#    stopped carrying and the wrappers' bounds are being proved by something
#    else — the shape that lets a wrapper keep a green row after its evidence
#    went away.
#
#    The four arithmetic-free tier-1 counters and `output_fits` (which rides
#    `clamp_u64`) are deliberately NOT touched, so they must stay green in the
#    same run. That makes this a specificity assertion as well as a
#    sensitivity one.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate 'fn clamp_u32(v: u32, hi: u32) -> u32 ensures result <= hi {
    if v > hi { hi } else { v }
}' 'fn clamp_u32(v: u32, hi: u32) -> u32 ensures result <= hi {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a broken clamp still passed  $G"; else mut_ok "mutation A (clamp_u32 returns v unclamped)  rc=$RC  $G"; fi
for f in clamp_u32 b64_symbol b64_value b32_symbol b32_value; do
  grep -q "verification failed for \`trust_radix64::$f\`" "$LOG" \
    || fail "mutation A: $f did not lose its bound — the composition is not carrying it"
done
for f in b64_padding_count b64_tail_symbols b32_padding_count b32_tail_symbols output_fits clamp_u64; do
  grep -q "verification failed for \`trust_radix64::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a clamp_u32-only break — the tier-1 bounds are not independent"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — the 24-bit group's peak pushed one past u32::MAX.
#    See the header: 16842752 is the exact largest coefficient that still
#    proves (peak == u32::MAX); this is that value plus one.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate 'pub fn b64_group(b0: u8, b1: u8, b2: u8) -> u32 {
    (b0 as u32) * 65536 + (b1 as u32) * 256 + (b2 as u32)
}' 'pub fn b64_group(b0: u8, b1: u8, b2: u8) -> u32 {
    (b0 as u32) * 16842753 + (b1 as u32) * 256 + (b2 as u32)
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an overflowing group coefficient still passed — the peak is no longer exact  $G"; else mut_ok "mutation B (b64_group 65536 -> 16842753, peak exceeds u32::MAX by 255)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_radix64::b64_group`' "$LOG" \
  || fail "mutation B: b64_group did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — the same at the 40-bit base32 group, at u64.
#    Recomputed for THIS arithmetic: 255*2^56 + 4294967295 fits u64 and 2^57
#    does not, so the coefficient had to be strengthened to 2^57. A
#    transplanted power of two would not have fired.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    (b0 as u64) * 4294967296' '    (b0 as u64) * 144115188075855872'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an overflowing u64 group coefficient still passed  $G"; else mut_ok "mutation C (b32_group 2^32 -> 2^57, peak exceeds u64::MAX)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_radix64::b32_group`' "$LOG" \
  || fail "mutation C: b32_group did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION D — a CONTRACT that is simply false.
#    `b64_padding_count` claims `result <= 2`; returning 3 makes the clause
#    false on a reachable path. Distinct from mutation A: there the carrier's
#    body stopped implying its clause, here a leaf's own returned value
#    violates its own clause directly.
# ---------------------------------------------------------------------------
STEP="MUTATION D"; mut_begin
mutate 'pub fn b64_padding_count(tail: u32) -> u32 ensures result <= 2 {
    if tail == 1 { return 2; }' 'pub fn b64_padding_count(tail: u32) -> u32 ensures result <= 2 {
    if tail == 1 { return 3; }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation D: a false ensures clause still passed  $G"; else mut_ok "mutation D (b64_padding_count returns 3 against 'ensures result <= 2')  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_radix64::b64_padding_count`' "$LOG" \
  || fail "mutation D: b64_padding_count kept its bound while returning a value outside it"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION E — an alphabet guard deleted, so a subtraction can underflow.
#    `raw_b64_value` reaches `x - 65` only after `if x < 65 { return 255; }`.
#    Per fragment map §4.7 a `u32` underflow is UNKNOWN rather than FAILED,
#    which is fail-closed and is what must be asserted — never `[FAILED]` on
#    u32 arithmetic.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate '    if x < 58 { return x + 4; }
    if x < 65 { return 255; }
    if x < 91 { return x - 65; }' '    if x < 58 { return x + 4; }
    if x < 91 { return x - 65; }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation E: an unguarded alphabet subtraction still passed  $G"; else mut_ok "mutation E (raw_b64_value 'x < 65' guard deleted)  rc=$RC  $G"; fi
grep -qE '\[(FAILED|UNKNOWN)\] \[overflow:sub\]|arithmetic overflow \(Sub\) (FAILED|UNKNOWN|RUNTIME CHECKED)' "$LOG" \
  || fail "mutation E: no subtraction row went FAILED, UNKNOWN or RUNTIME CHECKED — $(grep -oE 'arithmetic overflow \([A-Za-z]+\) [A-Z ]+' "$LOG" | head -3 | tr '\n' ' ')"
# §11.5 BUNDLING RECORD — `docs/STRICT_VERIFICATION_FRAGMENT.md` §11.5 says a
# callee whose rows go UNPROVEN stops being bundlable, so the compiler raises
# the error against its CALLER and not against the callee. An assertion naming
# the function the mutation broke is therefore wrong whenever that function is
# bundled. Recorded here per site so it is not rediscovered:
# `raw_b64_value` IS bundled — one non-test caller, `b64_value`
# (lib.rs:273). Measured green on the 2026-08-29 baseline run of this gate.
#
# Direction of the risk, which decides how much this matters: if the attribution
# ever moves, `grep -q … || fail` stops matching and this gate goes RED. It is a
# false-RED (fragility) risk, never a false-GREEN one — the opposite of the
# environment defect the G1 block above repairs. Do not "fix" a red here by
# deleting the assertion; read the member's own row first, because
# `member has a guarded or non-entry-prefix Assert` is emitted BOTH for §9.1's
# position refusal and for this unproven-rows refusal, with nothing in the text
# telling them apart.
grep -q 'verification failed for `trust_radix64::raw_b64_value`' "$LOG" \
  || fail "mutation E: raw_b64_value did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 8. MUTATION F — the decoded-length guard deleted.
#    `if t < p { return 0; }` is mathematically dead for any `pad <= 2` and
#    structurally required: it is the only thing that gives the interval engine
#    a range for the subtraction. A dead guard is fine; a dead CLAMP under a
#    tier-1 `ensures` would not be.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate '    let p: u64 = pad as u64;
    if t < p { return 0; }
    t - p' '    let p: u64 = pad as u64;
    t - p'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation F: an unguarded decoded-length subtraction still passed  $G"; else mut_ok "mutation F (b64_decoded_len 't < p' guard deleted)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_radix64::b64_decoded_len`' "$LOG" \
  || fail "mutation F: b64_decoded_len did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 9. THE TESTS, AND THE TWO MUTATIONS THEY ALONE CAN CATCH.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)"; else
  grep -qE '^test result: ok\. 17 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 17 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# --- MUTATION G — wrong value, TIER-1 POSTCONDITION SURVIVES ----------------
mutate 'fn raw_b64_symbol(i: u8) -> u32 {
    let x: u32 = i as u32;
    if x < 26 { return x + 65; }' 'fn raw_b64_symbol(i: u8) -> u32 {
    let x: u32 = i as u32;
    if x < 26 { return x + 64; }'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation G: the strict lane REFUTED a shifted alphabet (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged postcondition cannot see the answer is now stale and must be re-measured"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation G: a shifted base64 alphabet passed the unit tests"; else
  mut_ok "mutation G (raw_b64_symbol A-Z shifted down one; 'ensures result <= 123' still TRUE)  tests rc=$RC, strict lane rc=$VRC"
fi
# Assert WHICH tests fail, by name. A bare rc would be satisfied by a broken
# doctest stage or a compile error, and the control would silently stop testing.
for t in b64_alphabet_matches_the_rfc4648_table_exhaustively \
         base64_reproduces_the_rfc4648_published_vectors \
         base64_agrees_with_the_shift_and_table_oracle_over_a_byte_sweep; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation G: $t did not catch a shifted alphabet"
done
# The test that CANNOT catch it — it derives its expectation from the mutated
# function, and a constant shift preserves injectivity. Recorded so the
# asymmetry is not rediscovered. The tier-1 bound test and the untouched base32
# side must also stay green, so the demonstration cannot degrade into "the
# mutation broke everything".
for t in b64_alphabet_is_injective \
         no_tier1_result_ever_exceeds_its_bound \
         b32_alphabet_matches_the_rfc4648_table_exhaustively \
         every_non_symbol_byte_decodes_to_the_sentinel_exhaustively; do
  grep -q "$t ... ok" "$LOG" \
    || fail "mutation G: $t went red — G no longer isolates 'proved contract over a wrong answer'"
done
rm -f "$LOG"; restore

# --- MUTATION H — wrong value, PEAK DOES NOT MOVE --------------------------
mutate '    (b0 as u32) * 65536 + (b1 as u32) * 256 + (b2 as u32)
}' '    (b2 as u32) * 65536 + (b1 as u32) * 256 + (b0 as u32)
}'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation H: the strict lane REFUTED a byte swap (rc=$VRC $VG) — welcome news, but this gate's claim that the group's byte order is outside every obligation is now stale and must be re-measured"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation H: a byte-swapped 24-bit group passed the unit tests — the tests are not sensitive to the crate's own subject"; else
  mut_ok "mutation H (b64_group b0/b2 swapped; peak still exactly 16777215)  tests rc=$RC, strict lane rc=$VRC"
fi
for t in b64_group_slices_back_to_its_three_bytes_exhaustively_per_position \
         base64_reproduces_the_rfc4648_published_vectors \
         base64_agrees_with_the_shift_and_table_oracle_over_a_byte_sweep; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation H: $t did not catch a byte-swapped group"
done
# Specificity: the decode direction, the alphabet and base32 are untouched.
for t in b64_regroup_inverts_the_four_six_bit_slices_exhaustively_per_position \
         b64_alphabet_matches_the_rfc4648_table_exhaustively \
         base32_reproduces_the_rfc4648_published_vectors \
         no_tier1_result_ever_exceeds_its_bound; do
  grep -q "$t ... ok" "$LOG" \
    || fail "mutation H: $t went red — a b64_group byte swap must not disturb it"
done
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — all"
  echo "        three operands are u8, so the peak is 16777215 either way.)"
fi
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 10. The restore actually restored. A gate that leaves a mutation behind turns
#     the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
STEP="The restore actually restored"; mut_begin
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

mut_end
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
