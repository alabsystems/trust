#!/usr/bin/env bash
# trust_checksum_strict_gate.sh — pin `crates/trust-checksum` at a NON-VACUOUS
# pass of the authenticated strict lane, on BOTH policies, with live mutation
# controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-checksum` is the seventh `crates/`-resident component written to PASS
# the authenticated strict lane rather than to be retrofitted onto it, after
# `trust-ratio`, `trust-hex`, `trust-utf`, `trust-endian`, `trust-index` and
# `trust-varint`. Measured 2026-08-29 on stage1 driver `515d8d1d5d9d0018`,
# identically under the default `unix_hardened` policy and under
# `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 189 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 24/24 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=48, arithmetic_overflow_mul=5,
#                   arithmetic_overflow_shr=8, hardened_panic_boundary=101,
#                   postcondition=19, shift_overflow_shr=8
#
# A pass is worth nothing on its own, and every assertion below exists for one
# of the five reasons this repo has paid for:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower
#     and reports `0 failed` with `Coverage: complete`. The compile status is
#     asserted, never inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`. The kind split
#     is asserted and `unreachable` is asserted ABSENT. All 189 rows here are
#     19 postconditions + 69 primary safety + 101 hardened twins.
#  3. A pass never seen to fail is not evidence. Seven mutations run: five that
#     must refute, and TWO that must NOT (D and E below).
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it BY NAME.
#  5. Proofs cover overflow and discharged contracts — NOT whether the answer is
#     right.
#
# MUTATIONS D AND E ARE THE POINT OF THIS GATE
# --------------------------------------------
# Both are wrong-VALUE changes the strict lane PASSES at exit 0.
#
#   D mutates a TIER-1 function. `crc_width_bytes(16)` returns `1` instead of
#     `2`. `ensures result <= 8` stays TRUE, and so does
#     `checksum_bytes_clamped`'s `ensures result <= cap`, so the discharged
#     POSTCONDITION survives intact alongside every safety row — a proved
#     *contract*, not merely a proved *safety obligation*, sitting over a wrong
#     answer. The gate additionally asserts that
#     `no_tier1_result_ever_exceeds_its_bound` still PASSES under D, so the
#     demonstration cannot degrade into "the mutation broke everything".
#
#     Note which test does NOT catch it:
#     `checksum_bytes_clamped_is_the_min_of_the_width_and_the_cap` computes its
#     expectation FROM `crc_width_bytes`, so it is a consistency test and moves
#     with the mutation. Only the test that spells the widths out can refuse it.
#
#   E mutates arithmetic whose proof is EXACTLY TIGHT and stays tight under the
#     mutation. `fletcher_pack` is `(b as u16) * 256 + (a as u16)`, peaking at
#     exactly `u16::MAX`; swapping `a` and `b` leaves the peak at exactly
#     `u16::MAX`, because both are `u8`. No range moves, all 189 rows still
#     prove, and every Fletcher-16 checksum is wrong. The independent oracle
#     test `the_fletcher_oracle_reproduces_the_published_abcde_vector` still
#     passes under E — the oracle is a loop with `<<`, written by a different
#     method — which is what makes the sweeps evidence rather than a tautology.
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit.
#   * A per-function `[VERIFIED] (n obligations: n proved ...)` transport row
#     can be published for a function the compiler HARD-ERRORED on. Measured
#     twice while building THIS crate: `r2_shr_compose` and `s7_pack` each
#     published `[VERIFIED] (1 obligations: 1 proved)` in a run whose only
#     diagnostic for them was `error: Trust full verification failed`.
# So every assertion is on the EXIT CODE, the `Gate:` line, and the absence of
# `error:` lines — never on the Summary alone and never on a per-function row.
#
# Usage:  scripts/trust_checksum_strict_gate.sh          (~5 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-checksum/src/lib.rs"
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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-checksum ) > "$LOG" 2>&1
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
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-checksum --lib ) > "$LOG" 2>&1
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

echo "trust-checksum strict gate:"

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
grep -q 'Coverage: 24/24 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 24/24 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 189 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(189 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=48 arithmetic_overflow_mul=5 arithmetic_overflow_shr=8 \
            hardened_panic_boundary=101 postcondition=19 shift_overflow_shr=8; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
mut_ok "pristine  $G  [19 postcondition + 69 safety + 101 hardened-twin, 0 unreachable]"
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
grep -qE 'Summary: 189 proved, 0 failed, .*0 inconclusive \(189 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — the COMPOSITION CARRIER broken.
#    `checksum_bytes_clamped` inherits its bound from `clamp_u8`'s
#    postcondition. Breaking `clamp_u8` must refute the wrapper as well as
#    `clamp_u8` itself. If it ever refutes only `clamp_u8`, the composition
#    stopped carrying and the wrapper's bound is being proved by something
#    else — the shape that lets a wrapper keep a green row after its evidence
#    went away.
#
#    The five arithmetic-free tier-1 functions carry their own bounds and are
#    deliberately NOT touched, so they must stay green in the same run. That
#    makes this a specificity assertion as well as a sensitivity one.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate 'fn clamp_u8(v: u8, hi: u8) -> u8 ensures result <= hi {
    if v > hi { hi } else { v }
}' 'fn clamp_u8(v: u8, hi: u8) -> u8 ensures result <= hi {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a broken clamp still passed  $G"; else mut_ok "mutation A (clamp_u8 returns v unclamped)  rc=$RC  $G"; fi
# §11.5 BUNDLING RECORD — `docs/STRICT_VERIFICATION_FRAGMENT.md` §11.5 says a
# callee whose rows go UNPROVEN stops being bundlable, so the compiler raises
# the error against its CALLER and not against the callee. An assertion naming
# the function the mutation broke is therefore wrong whenever that function is
# bundled. Recorded here per site so it is not rediscovered:
# `clamp_u8` IS bundled — one non-test caller, `checksum_bytes_clamped`
# (lib.rs:151). This site already asserts BOTH the callee and that caller, so
# it is §11.5-robust as written: whichever level the diagnostic attaches to,
# one of the two names must appear. Keep both.
#
# Direction of the risk, which decides how much this matters: if the attribution
# ever moves, `grep -q … || fail` stops matching and this gate goes RED. It is a
# false-RED (fragility) risk, never a false-GREEN one — the opposite of the
# environment defect the G1 block above repairs. Do not "fix" a red here by
# deleting the assertion; read the member's own row first, because
# `member has a guarded or non-entry-prefix Assert` is emitted BOTH for §9.1's
# position refusal and for this unproven-rows refusal, with nothing in the text
# telling them apart.
for f in clamp_u8 checksum_bytes_clamped; do
  grep -q "verification failed for \`trust_checksum::$f\`" "$LOG" \
    || fail "mutation A: $f did not lose its bound — the composition is not carrying it"
done
for f in crc_width_bytes message_len_ok fletcher_state_ok adler_state_ok checksum_agrees; do
  grep -q "verification failed for \`trust_checksum::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a clamp-only break — the tier-1 bounds are not independent"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — the SHA-2 length bound removed.
#    This is `trust-sha2/src/sha256.rs:189`'s defect reintroduced: `bytes * 8`
#    with nothing bounding `bytes`. Per fragment map §4.7 a `u64` overflow is
#    UNKNOWN rather than FAILED, which is fail-closed and is what must be
#    asserted — never `[FAILED]` on u64.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate '    if bytes > 2305843009213693951 { return 18446744073709551615; }
    bytes * 8' \
       '    bytes * 8'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an unbounded bit-length multiply still passed  $G"; else mut_ok "mutation B (message_bit_len 2^61 guard deleted)  rc=$RC  $G"; fi
grep -qE '\[(FAILED|UNKNOWN)\] \[overflow:mul\]|arithmetic overflow \(Mul\) (FAILED|UNKNOWN|RUNTIME CHECKED)' "$LOG" \
  || fail "mutation B: no multiply row went FAILED, UNKNOWN or RUNTIME CHECKED — $(grep -oE 'arithmetic overflow \([A-Za-z]+\) [A-Z ]+' "$LOG" | head -3 | tr '\n' ' ')"
grep -q 'verification failed for `trust_checksum::message_bit_len`' "$LOG" \
  || fail "mutation B: message_bit_len did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — the CRC doubling guard removed.
#    `c * 2` at `u16` with `c` unbounded. The guard is mathematically dead when
#    `crc8_bit` is called from `crc8` and structurally required: it is the only
#    thing that gives the interval engine a range for the multiply.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    if c > 255 { return 0; }
    let d: u16 = c * 2;' \
       '    let d: u16 = c * 2;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an unbounded u16 doubling still passed  $G"; else mut_ok "mutation C (crc8_bit entry guard deleted)  rc=$RC  $G"; fi
# §11.5 BUNDLING RECORD — `docs/STRICT_VERIFICATION_FRAGMENT.md` §11.5 says a
# callee whose rows go UNPROVEN stops being bundlable, so the compiler raises
# the error against its CALLER and not against the callee. An assertion naming
# the function the mutation broke is therefore wrong whenever that function is
# bundled. Recorded here per site so it is not rediscovered:
# `crc8_bit` IS bundled — eight non-test call sites, all inside `crc8`
# (lib.rs:313-320), and `crc8` itself has no in-crate caller. Measured green on
# the 2026-08-29 baseline run: the callee is named in its own right here.
#
# Direction of the risk, which decides how much this matters: if the attribution
# ever moves, `grep -q … || fail` stops matching and this gate goes RED. It is a
# false-RED (fragility) risk, never a false-GREEN one — the opposite of the
# environment defect the G1 block above repairs. Do not "fix" a red here by
# deleting the assertion; read the member's own row first, because
# `member has a guarded or non-entry-prefix Assert` is emitted BOTH for §9.1's
# position refusal and for this unproven-rows refusal, with nothing in the text
# telling them apart.
grep -q 'verification failed for `trust_checksum::crc8_bit`' "$LOG" \
  || fail "mutation C: crc8_bit did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION F — the Fletcher pack coefficient raised, so the proof's own
#    TIGHTNESS is pinned.
#    `(b as u16) * 256 + (a as u16)` peaks at exactly `u16::MAX`. At `* 257`
#    the product still fits (255*257 == 65535 exactly) and the ADD does not.
#    If this ever stops firing, the pack's peak is no longer exact and mutation
#    E's claim — that a swap changes no range — needs re-measuring.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate 'fn fletcher_pack(a: u8, b: u8) -> u16 { (b as u16) * 256 + (a as u16) }' \
       'fn fletcher_pack(a: u8, b: u8) -> u16 { (b as u16) * 257 + (a as u16) }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation F: an overflowing pack still passed — the peak is no longer exact  $G"; else mut_ok "mutation F (fletcher_pack 256 -> 257, the add overflows u16)  rc=$RC  $G"; fi
# §11.5 BUNDLING RECORD — `docs/STRICT_VERIFICATION_FRAGMENT.md` §11.5 says a
# callee whose rows go UNPROVEN stops being bundlable, so the compiler raises
# the error against its CALLER and not against the callee. An assertion naming
# the function the mutation broke is therefore wrong whenever that function is
# bundled. Recorded here per site so it is not rediscovered:
# `fletcher_pack` IS bundled — one non-test caller, `fletcher16_4`
# (lib.rs:351). Measured green on the 2026-08-29 baseline run of this gate.
#
# Direction of the risk, which decides how much this matters: if the attribution
# ever moves, `grep -q … || fail` stops matching and this gate goes RED. It is a
# false-RED (fragility) risk, never a false-GREEN one — the opposite of the
# environment defect the G1 block above repairs. Do not "fix" a red here by
# deleting the assertion; read the member's own row first, because
# `member has a guarded or non-entry-prefix Assert` is emitted BOTH for §9.1's
# position refusal and for this unproven-rows refusal, with nothing in the text
# telling them apart.
grep -q 'verification failed for `trust_checksum::fletcher_pack`' "$LOG" \
  || fail "mutation F: fletcher_pack did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION G — a CONTRACT that is simply false.
#    `crc_width_bytes` claims `result <= 8`; returning 9 makes the clause false
#    on a reachable path. Distinct from mutation A: there the carrier's body
#    stopped implying its clause, here a leaf's own returned value violates its
#    own clause directly.
# ---------------------------------------------------------------------------
STEP="MUTATION G"; mut_begin
mutate '    if width_bits == 64 { return 8; }' '    if width_bits == 64 { return 9; }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation G: a false ensures clause still passed  $G"; else mut_ok "mutation G (crc_width_bytes returns 9 against 'ensures result <= 8')  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_checksum::crc_width_bytes`' "$LOG" \
  || fail "mutation G: crc_width_bytes kept its bound while returning a value outside it"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 8. THE TESTS, AND THE TWO MUTATIONS THEY ALONE CAN CATCH.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)"; else
  grep -qE '^test result: ok\. 25 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 25 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# --- MUTATION D — wrong value, TIER-1 POSTCONDITION SURVIVES ----------------
mutate '    if width_bits == 16 { return 2; }' '    if width_bits == 16 { return 1; }'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation D: the strict lane REFUTED a wrong width (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged postcondition cannot see the answer is now stale and must be re-measured"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation D: a wrong CRC width passed the unit tests"; else
  mut_ok "mutation D (crc_width_bytes(16) -> 1; 'ensures result <= 8' still TRUE)  tests rc=$RC, strict lane rc=$VRC"
fi
grep -q 'crc_width_bytes_matches_the_standard_widths ... FAILED' "$LOG" \
  || fail "mutation D: crc_width_bytes_matches_the_standard_widths did not catch a wrong width"
# The CONTRACT test must still pass — otherwise the demonstration degrades into
# "the mutation broke everything" and says nothing about proofs-vs-answers.
grep -q 'no_tier1_result_ever_exceeds_its_bound ... ok' "$LOG" \
  || fail "mutation D: the tier-1 bound test also went red — D no longer isolates 'proved contract over a wrong answer'"
# ...and the consistency test CANNOT catch it, because it computes its
# expectation from the mutated function. Recorded so the asymmetry is not
# rediscovered.
grep -q 'checksum_bytes_clamped_is_the_min_of_the_width_and_the_cap ... ok' "$LOG" \
  || echo "       (note: the min/cap consistency test now also catches this; it did not when written)"
rm -f "$LOG"; restore

# --- MUTATION E — wrong value, PEAK STAYS EXACTLY u16::MAX ------------------
mutate 'fn fletcher_pack(a: u8, b: u8) -> u16 { (b as u16) * 256 + (a as u16) }' \
       'fn fletcher_pack(a: u8, b: u8) -> u16 { (a as u16) * 256 + (b as u16) }'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation E: the strict lane REFUTED a residue swap (rc=$VRC $VG) — welcome news, but this gate's claim that the pack order is outside every obligation is now stale and must be re-measured"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation E: a swapped Fletcher pack passed the unit tests — the tests are not sensitive to the crate's own subject"; else
  mut_ok "mutation E (fletcher_pack residues swapped; peak still exactly u16::MAX)  tests rc=$RC, strict lane rc=$VRC"
fi
# Assert WHICH tests fail, by name. A bare rc would be satisfied by a broken
# doctest stage or a compile error, and the control would silently stop testing.
for t in fletcher16_4_matches_the_loop_oracle_over_a_byte_sweep \
         fletcher16_4_agrees_per_byte_position \
         fletcher16_4_chains_across_two_blocks; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation E: $t did not catch a swapped Fletcher pack"
done
# The INDEPENDENT oracle is unaffected — it is a loop with `<<`, written by a
# different method — which is what makes the sweeps evidence and not a
# tautology. Adler and the tier-1 bounds are untouched: specificity.
for t in the_fletcher_oracle_reproduces_the_published_abcde_vector \
         adler32_4_reproduces_the_published_abcd_vector \
         no_tier1_result_ever_exceeds_its_bound; do
  grep -q "$t ... ok" "$LOG" \
    || fail "mutation E: $t went red — a Fletcher-pack swap must not disturb it"
done
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — both"
  echo "        operands are u8, so the peak is 255*256+255 == u16::MAX either way.)"
fi
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 9. The restore actually restored. A gate that leaves a mutation behind turns
#    the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
STEP="The restore actually restored"; mut_begin
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

mut_end
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
