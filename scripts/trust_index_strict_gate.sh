#!/usr/bin/env bash
# trust_index_strict_gate.sh — pin `crates/trust-index` at a NON-VACUOUS pass of
# the authenticated strict lane, on BOTH policies, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-index` is the fifth `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it, after
# `trust-ratio`, `trust-hex`, `trust-utf` and `trust-endian`. Measured
# 2026-08-29, identically under the default `unix_hardened` policy and under
# `-Ztrust-policy=certify`, at stage1 driver `ba5e2cace25b69a8`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 35 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 18/18 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=3, arithmetic_overflow_sub=6,
#                   hardened_panic_boundary=11, postcondition=7,
#                   remainder_by_zero=3, slice_bounds_check=5
#
# A pass is worth nothing on its own, and every assertion below exists for one
# of the five reasons this repo has paid for:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower
#     and reports `0 failed` with `Coverage: complete`. The compile status is
#     asserted, never inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`. The kind split
#     is asserted and `unreachable` is asserted ABSENT. All 35 rows here are
#     7 postconditions + 17 primary safety + 11 hardened twins.
#  3. A pass never seen to fail is not evidence. Five mutations run, four
#     refuting a different mechanism and one that must NOT be refuted (below).
#  4. The certify lane must be seen to run, not assumed. `--certify` selects
#     it (TRUSTFLAGS is not read since T7a), and the Gate line names the lane
#     that graded the run, so the certify step requires `[certify lane`.
#  5. Proofs cover overflow, bounds and discharged contracts — NOT whether the
#     answer is right.
#
# MUTATION D IS THE POINT OF THIS GATE
# ------------------------------------
# `window_end` is a TIER-1 function: `ensures result <= len` is checked by the
# compiler. Swapping its `raw_sat_add` for `raw_sat_sub` keeps every operand in
# range, keeps the clamp live, and keeps that contract TRUE — so the strict lane
# still returns EXIT 0 with all 35 rows proved while `window_end(2, 3, 100)`
# returns 0 instead of 5. Mutation D performs that swap and asserts BOTH halves:
# the lane passes, and named unit tests go red. A proved CONTRACT is not a
# proved specification, which is a sharper statement than the tier-2 version of
# the same control in `trust_endian_strict_gate.sh`.
#
# MUTATION E IS THE CRATE'S HEADLINE CLAIM
# ----------------------------------------
# `subslice` clamps BOTH ends. A range slice mints a SINGLE `[slice]`
# obligation, so it is not obvious from the row count that the obligation
# encodes non-inversion (`start <= end`) and not merely `end <= len`. Mutation E
# deletes the `start > end` guard and requires the lane to refuse. Without it,
# the module docs' claim about `crates/trust-ts-strip/src/erase.rs:39` would be
# unsupported by anything.
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit.
#   * A per-function `[VERIFIED] (n obligations: n proved ...)` transport row
#     can be published for a function the compiler HARD-ERRORED on. This crate
#     hit that live during development: `ring_distance` published
#     `[VERIFIED] (7 obligations: 7 proved)` in the same run in which the
#     compiler emitted `error: Trust strict verification failed for
#     trust_index::ring_distance: 9 obligation(s) were not fully verified`, and
#     the Summary read `32 proved, 0 failed, 0 inconclusive`.
# So every assertion is on the EXIT CODE, the `Gate:` line, and the absence of
# `error:` lines — never on the Summary alone and never on a per-function row.
#
# Usage:  scripts/trust_index_strict_gate.sh          (~4 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-index/src/lib.rs"
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
run() { # run [lane flag]; sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" trust check --all-rows ${1:+"$1"} -p trust-index ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-run}"
  no_rustc_error "${STEP:-run}"
}
# `--lib` is load-bearing. A concurrent `x.py check` can rebuild
# `librustc_driver-<hash>.dylib` while stage1 `trustdoc` still references the
# old hash; the doctest stage then dies with `dyld: Library not loaded` /
# SIGABRT and `targo test` exits 101 with every unit test passing. This crate
# has no doctests (its examples are ```text). Scope to the unit tests, and keep
# asserting the exact result line so the scoping cannot hide a real red.
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-index --lib ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-tests}"
}
gate_line() { grep -oE 'Gate: [A-Z-]+ \[[a-z-]+ lane, exit [0-9]+\]' "$LOG" | tail -1; }
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

echo "trust-index strict gate:"

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
grep -q 'Coverage: 18/18 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 18/18 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 35 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(35 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=3 arithmetic_overflow_sub=6 \
            hardened_panic_boundary=11 postcondition=7 \
            remainder_by_zero=3 slice_bounds_check=5; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
mut_ok "pristine  $G  [7 postcondition + 17 safety + 11 hardened-twin, 0 unreachable]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 2. THE SAME PASS UNDER `--certify` (the compiler's `certify` policy).
#    The lane flag selects the compiler's `certify` policy, and the Gate line
#    names the lane that graded the run, so `[certify lane, exit 0]` is the
#    evidence that certify ran. (A bogus-policy control proved the TRUSTFLAGS
#    route reached the compiler; it went with that channel, DECISION_QUEUE T7a.)
# ---------------------------------------------------------------------------
STEP="THE SAME PASS UNDER '--certify'"; mut_begin
run "--certify"
G="$(gate_line)"
[ "$RC" -eq 0 ] || fail "certify: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [certify lane, exit 0]"*) ;; *) fail "certify: Gate is '$G'";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "certify: rustc reported errors"; fi
grep -qE 'Summary: 35 proved, 0 failed, .*0 inconclusive \(35 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — the COMPOSITION CARRIER broken.
#    Every tier-1 bound in the crate is inherited from `clamp_upper`'s
#    postcondition. Breaking it must refute all five wrappers as well as
#    `clamp_upper` itself. If it ever refutes only `clamp_upper`, the
#    composition stopped carrying and those bounds are being proved by
#    something else — the shape that lets a wrapper keep a green row after its
#    evidence went away.
#
#    The tier-2 functions are deliberately untouched and must stay green in the
#    same run, which makes this a specificity assertion as well as a
#    sensitivity one.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate 'fn clamp_upper(v: usize, hi: usize) -> usize ensures result <= hi {
    if v > hi { hi } else { v }
}' 'fn clamp_upper(v: usize, hi: usize) -> usize ensures result <= hi {
    v
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a broken composition carrier still passed  $G"; else mut_ok "mutation A (clamp_upper stops clamping)  rc=$RC  $G"; fi
for f in clamp_upper clamp_index window_start window_end span_len capped_len; do
  grep -q "verification failed for \`trust_index::$f\`" "$LOG" \
    || fail "mutation A: $f was NOT refuted — composition is not carrying the bound"
done
for f in ring_offset subslice at head tail last_index; do
  grep -q "verification failed for \`trust_index::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted, but it carries no contract and composes from nothing"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — a real SAFETY obligation made false: the underflow guard.
#    `raw_sat_sub` is the only subtraction on the tier-1 path. Deleting its
#    guard makes `end - start` underflow for every `end < start`, which is the
#    exact defect at `crates/trust-backprop/src/validation/cargo_exec.rs:500`.
#
#    MEASURED ASYMMETRY (fragment map §4.6): an unguarded `u8` subtraction is
#    hard-`[FAILED]`, but the same defect on wider types is only ever
#    `[UNKNOWN]`. So this asserts what IS assertable — the crate stops
#    compiling and the site stops being proved — and does not demand a
#    witnessed refutation the verifier does not produce at `usize` width.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate 'fn raw_sat_sub(a: usize, b: usize) -> usize {
    if a < b { return 0; }
    a - b
}' 'fn raw_sat_sub(a: usize, b: usize) -> usize {
    a - b
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an unguarded subtraction still passed  $G"; else mut_ok "mutation B (raw_sat_sub loses its underflow guard)  rc=$RC  $G"; fi
grep -qE '^\s*\[(FAILED|UNKNOWN)\] \[overflow:sub\]' "$LOG" \
  || fail "mutation B: no overflow:sub row went FAILED or UNKNOWN — $(grep -oE '\[[A-Z]+\] \[overflow:[a-z]+\]' "$LOG" | head -3 | tr '\n' ' ')"
# §11.5 BUNDLING RECORD — `docs/STRICT_VERIFICATION_FRAGMENT.md` §11.5 says a
# callee whose rows go UNPROVEN stops being bundlable, so the compiler raises
# the error against its CALLER and not against the callee. An assertion naming
# the function the mutation broke is therefore wrong whenever that function is
# bundled. Recorded here per site so it is not rediscovered:
# `raw_sat_sub` IS bundled — one non-test caller, `span_len` (lib.rs:314).
# Measured green on the 2026-08-29 baseline run of this gate.
#
# Direction of the risk, which decides how much this matters: if the attribution
# ever moves, `grep -q … || fail` stops matching and this gate goes RED. It is a
# false-RED (fragility) risk, never a false-GREEN one — the opposite of the
# environment defect the G1 block above repairs. Do not "fix" a red here by
# deleting the assertion; read the member's own row first, because
# `member has a guarded or non-entry-prefix Assert` is emitted BOTH for §9.1's
# position refusal and for this unproven-rows refusal, with nothing in the text
# telling them apart.
grep -q 'verification failed for `trust_index::raw_sat_sub`' "$LOG" \
  || fail "mutation B: raw_sat_sub did not hard-error"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — the divisor-nonzero guard deleted.
#    `ring_offset`'s `cap == 0` early return is the entire discharge for its
#    `%`. This is the fact `crates/trust-clean/src/cfg_family/emit.rs:697`
#    checks only in a `debug_assert`, and only AFTER the division.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate 'pub fn ring_offset(i: usize, k: usize, cap: usize) -> usize {
    if cap == 0 { return 0; }' 'pub fn ring_offset(i: usize, k: usize, cap: usize) -> usize {'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: a modulo with no nonzero guard still passed  $G"; else mut_ok "mutation C (ring_offset loses its cap==0 guard)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_index::ring_offset`' "$LOG" \
  || fail "mutation C: ring_offset did not hard-error"
grep -qE '^\s*\[(FAILED|UNKNOWN)\] \[(divzero|remzero|rem_zero)\]' "$LOG" \
  || fail "mutation C: no zero-divisor row went FAILED or UNKNOWN — $(grep -oE '\[[A-Z]+\] \[[a-z_]+\]' "$LOG" | sort -u | tr '\n' ' ')"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION E — the RANGE-INVERSION guard deleted. The headline claim.
#    A range slice mints ONE `[slice]` obligation, so the row count alone does
#    not say whether that obligation encodes `start <= end` or only
#    `end <= s.len()`. Deleting the `start > end` guard is the only thing that
#    distinguishes them. If this ever passes, `subslice`'s doc claim about
#    `crates/trust-ts-strip/src/erase.rs:39` is unsupported and must be
#    rewritten, not left standing.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate '    if start > end { return &[]; }
    &s[start..end]' '    &s[start..end]'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation E: an UN-INVERTED range guard still passed — the [slice] obligation does not encode start <= end, and subslice's doc claim is unsupported  $G"; else mut_ok "mutation E (subslice loses its start>end guard)  rc=$RC  $G"; fi
case "$G" in *"PASS"*) fail "mutation E: Gate still says PASS — $G";; esac
# A BOUNDS gap keeps its runtime check, so the default policy DOWNGRADES it to
# an advisory: this run emits NO `error:` line at all and still exits 1. A gate
# that grepped only for `error:` would read this mutation as a pass. Assert the
# advisory by name and the inconclusive count, and never `error:` here.
# The REFUSAL MUST NAME THE FUNCTION -- that is the assertion. Which SHAPE the
# refusal takes is not: measured 2026-09-01, this mutation now yields
#   Trust Level 0 safety verification incomplete for `trust_index::subslice`
#   Trust strict verification failed  for `trust_index::subslice`
# where it used to yield an advisory. FAILED is STRICTLY STRONGER evidence than
# an advisory -- the row is refuted rather than merely not established -- so
# demanding the weaker word would fail the gate for getting a better answer.
# The primary controls above (rc != 0, Gate not PASS) are untouched, so a
# verifier that wrongly PASSED this mutation is still caught.
grep -qE 'Trust (verification advisory|strict verification failed|Level 0 safety verification incomplete) for `trust_index::subslice`' "$LOG" \
  || fail "mutation E: subslice was not even named in a refusal — $(grep -oE 'Trust [a-zA-Z0-9 ]*for `trust_index::[a-z_]+`' "$LOG" | head -3 | tr '\n' ' ')"
# Same reasoning: the row must be REFUSED, in either shape. `1 failed` and
# `1 inconclusive` are both refusals of the mutated obligation; only `35 proved`
# would be the bug this asserts against, and that is excluded either way.
grep -qE 'Summary: 34 proved, ([1-9][0-9]* failed|.*[1-9][0-9]* inconclusive).*\(35 total\)' "$LOG" \
  || fail "mutation E: no row was refused — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
grep -qE '^\s*\[(FAILED|UNKNOWN)\] \[slice\]' "$LOG" \
  || fail "mutation E: no slice row went FAILED or UNKNOWN — $(grep -oE '\[[A-Z]+\] \[slice\]' "$LOG" | head -3 | tr '\n' ' ')"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION F — the parameter-vs-local respelling in `at`.
#    Measured 2026-08-29 against four variants in one run: returning the
#    PARAMETER `default` directly from the guard's arm leaves the bounds row
#    AND its hardened twin UNKNOWN, while binding it to a local first proves
#    both. Arity is ruled out (a three-parameter body with a literal fallback
#    proves) and so is guard polarity. This control exists so a future
#    "cleanup" that inlines the local is a loud red rather than a silent loss
#    of two rows, and so the fragment-map entry cannot go stale unobserved.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate '    let d: u8 = default;
    if i >= s.len() { return d; }' '    if i >= s.len() { return default; }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation F: inlining the local PASSED — the parameter-vs-local boundary has moved. That is welcome news, but docs/STRICT_VERIFICATION_FRAGMENT.md §2.6 and this crate's module docs are now stale and must be re-measured, not deleted"
else
  mut_ok "mutation F (at returns the parameter directly)  rc=$RC  $G"
fi
case "$G" in *"PASS"*) fail "mutation F: Gate still says PASS — $G";; esac
# MEASURED, and the quietest refusal in the four sibling gates: this mutation
# emits NO `error:` line AND no per-function warning either — not even the
# `Trust verification advisory` that mutation E gets. The ONLY things that say
# so are the exit code, the `Gate:` line and the inconclusive count. A gate
# built on diagnostics rather than on those three would read it as a pass.
if grep -qE '^error(\[|:)' "$LOG"; then fail "mutation F: an error: line appeared — the recorded quiet-refusal shape has changed, re-measure"; fi
grep -qE 'Summary: 33 proved, .*2 inconclusive \(35 total\)' "$LOG" \
  || fail "mutation F: expected exactly 2 inconclusive rows (the bounds row and its hardened twin) — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 8. THE TESTS, AND THE MUTATION THEY ALONE CAN CATCH.
#    `window_end` is TIER 1: `ensures result <= len` is checked. Swapping its
#    `raw_sat_add` for `raw_sat_sub` keeps that contract TRUE — a saturating
#    difference is still <= len once clamped — so every one of the 35 rows,
#    including the postcondition, still proves and the strict lane still exits
#    0, while `window_end(2, 3, 100)` returns 0 instead of 5. Only the tests can
#    refuse this, so they are asserted to pass AND asserted to fail.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)"; else
  grep -qE '^test result: ok\. 18 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 18 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

mutate 'pub fn window_end(start: usize, count: usize, len: usize) -> usize ensures result <= len {
    clamp_upper(raw_sat_add(start, count), len)
}' 'pub fn window_end(start: usize, count: usize, len: usize) -> usize ensures result <= len {
    clamp_upper(raw_sat_sub(start, count), len)
}'
# The verifier must NOT notice — that is the point of this control. If this ever
# starts failing the strict lane, the note below is out of date in a GOOD way
# and should be re-measured rather than deleted.
run
VRC="$RC"
VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation D: the strict lane REFUTED an add/sub swap inside a contracted function (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged \`ensures\` cannot see the difference is now stale and must be re-measured"
fi
if grep -qE '^error(\[|:)' "$LOG"; then fail "mutation D: rustc reported errors, so the lane did not actually accept the swap"; fi
grep -qE 'Summary: 35 proved, 0 failed, .*0 inconclusive \(35 total\)' "$LOG" \
  || fail "mutation D: the row count moved — the swap was supposed to change no obligation at all. $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation D: a swapped add/sub passed the unit tests — the tests are not sensitive to the crate's own subject"; else
  mut_ok "mutation D (window_end: raw_sat_add -> raw_sat_sub)  tests rc=$RC, strict lane rc=$VRC"
fi
for t in window_end_agrees_with_core_saturating_add_then_min a_window_never_ends_before_it_starts; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation D: $t did not catch a swapped add/sub"
done
# ... and the contract itself must still hold, which is the whole point.
grep -q "no_tier1_result_ever_exceeds_its_bound ... ok" "$LOG" \
  || fail "mutation D: the tier-1 bound test also failed, so this is not a demonstration that a TRUE contract can sit over a wrong answer"
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — the"
  echo "        clamp keeps \`ensures result <= len\` TRUE over the wrong value.)"
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
