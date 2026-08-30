#!/usr/bin/env bash
# trust_align_strict_gate.sh — pin `crates/trust-align` at a NON-VACUOUS pass of
# the authenticated strict lane, on BOTH policies, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-align` is the ninth `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it, after
# `trust-ratio`, `trust-hex`, `trust-utf`, `trust-endian`, `trust-index`,
# `trust-varint`, `trust-checksum` and `trust-radix64`. Measured 2026-08-29 on
# stage1 driver `40767a74521230d6`, identically under the default
# `unix_hardened` policy and under `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 84 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 34/34 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=3, arithmetic_overflow_mul=2,
#                   arithmetic_overflow_sub=3, hardened_panic_boundary=7,
#                   postcondition=69
#
# A pass is worth nothing on its own, and every assertion below exists for one
# of the five reasons this repo has paid for:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower
#     and reports `0 failed` with `Coverage: complete`. The compile status is
#     asserted, never inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`. The kind split
#     is asserted and `unreachable` is asserted ABSENT. All 84 rows here are
#     69 postconditions + 8 primary safety + 7 hardened twins.
#  3. A pass never seen to fail is not evidence. Seven mutations run: five that
#     must refute, and TWO that must NOT (D and G below).
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it BY NAME.
#  5. Proofs cover overflow and discharged contracts — NOT whether the answer is
#     right.
#
# MUTATIONS D AND G ARE THE POINT OF THIS GATE
# --------------------------------------------
# Both are wrong-VALUE changes the strict lane PASSES at exit 0, with the kind
# split BYTE-IDENTICAL to the pristine run.
#
#   D mutates a TIER-1 function. `align_mask(16)` returns `7` instead of `15`,
#     so every 16-byte alignment in the crate rounds to a multiple of 8.
#     `ensures result <= 4095` stays TRUE — 7 is well inside it — and so does
#     `align_up_within`'s `ensures result <= cap`, so the discharged
#     POSTCONDITION survives intact alongside every safety row. A proved
#     *contract*, not merely a proved *safety obligation*, sits over an answer
#     that is wrong for the crate's entire subject. The gate additionally
#     asserts that `every_tier1_clamp_is_live_and_no_result_ever_exceeds_its_bound`
#     still PASSES under D, so the demonstration cannot degrade into "the
#     mutation broke everything".
#
#     Note which test does NOT catch it:
#     `align_up_agrees_with_the_mask_identity_it_is_built_from` computes its
#     expectation FROM `align_mask`, so it is a consistency test and moves with
#     the mutation. Only the tests that spell the alignments out, or that ask
#     `core`, can refuse it. A test that derives its oracle from the code under
#     test is not a test, and this gate asserts that it still passes so the
#     asymmetry is not rediscovered.
#
#   G deletes the SATURATION and leaves a truncating cast. `raw_sat_mul`'s
#     `if p > 4294967295 { return 4294967295; }` is removed, so `p as u32`
#     silently truncates — and a truncating `as` cast is neither an overflow nor
#     a zero divisor, so it mints NO obligation at all
#     (`docs/STRICT_VERIFICATION_FRAGMENT.md` §2.5). The multiply's own row and
#     its hardened twin still prove, the row count does not move, and
#     `array_bytes(0x10000, 0x10000)` returns 0 instead of `u32::MAX`. This is
#     the §4.6 hole in operator form: the mutation makes the crate WORSE by
#     DELETING a check, and the proof count goes UP-or-equal, never down.
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit.
#   * A per-function `[VERIFIED] (n obligations: n proved …)` transport row can
#     be published for a function the compiler HARD-ERRORED on. Measured twice
#     while probing THIS crate: `t4` and `t5` each published
#     `[VERIFIED] (… proved)` in a run whose only diagnostic for them was
#     `error: Trust full verification failed`.
# So every assertion is on the EXIT CODE, the `Gate:` line, and the absence of
# `error:` lines — never on the Summary alone and never on a per-function row.
#
# AND A THIRD, FOUND WHILE BUILDING THIS CRATE
# --------------------------------------------
#   * `targo trust check` can exit 2 having printed NO `Gate:` line, NO
#     `Summary:`, NO `Coverage:` and NO `error:` — only
#     `could not seal the final compiler rows, …`. The crate compiled and
#     verified; the report could not be published. It is reproducible from row
#     COUNT alone (see `docs/STRICT_VERIFICATION_FRAGMENT.md` §9.2), so a gate
#     that greps for `error:` reads it as a pass. The `Gate:` line is asserted
#     PRESENT before anything else is read.
#
# Usage:  scripts/trust_align_strict_gate.sh          (~10 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-align/src/lib.rs"
TARGO="${TARGO:-$REPO_ROOT/build/aarch64-apple-darwin/stage1/bin/targo}"

[ -x "$TARGO" ] || { echo "REFUSE: no targo at $TARGO (set TARGO=...)"; exit 2; }
# Two behavioural discriminators; a stage whose targo was never rebuilt ships
# upstream cargo under the name `targo` and verifies NOTHING while succeeding.
"$TARGO" --unverified --version >/dev/null 2>&1 \
  || { echo "REFUSE: $TARGO rejects --unverified — it is cargo-in-disguise, not targo"; exit 2; }
[ -x "$(dirname "$TARGO")/trustc" ] \
  || { echo "REFUSE: no sibling trustc beside $TARGO — the stage1 sysroot is not assembled"; exit 2; }

# PREFLIGHT: `crates/Cargo.toml` must LOAD. A workspace member listed without a
# manifest on disk makes every `targo trust check` in this workspace exit 2 with
# no `Gate:` line — indistinguishable, to every assertion below, from the §9.2
# seal failure and from a real crate regression. Measured 2026-08-29: a
# concurrent lane added its member row minutes before creating the crate, and
# this gate reported 26 failures about `trust-align`, none of which were about
# `trust-align`. Name the real cause instead.
MISSING_MEMBERS="$(python3 - "$REPO_ROOT/crates" <<'PY'
import os, re, sys
root = sys.argv[1]
s = open(os.path.join(root, "Cargo.toml")).read()
m = re.search(r'^members\s*=\s*\[(.*?)^\]', s, re.S | re.M)
if m:
    for name in re.findall(r'^\s*"([^"]+)",\s*$', m.group(1), re.M):
        if not os.path.exists(os.path.join(root, name, "Cargo.toml")):
            print(name)
PY
)"
[ -z "$MISSING_MEMBERS" ] || {
  echo "REFUSE: crates/Cargo.toml lists member(s) with no manifest on disk:"
  echo "$MISSING_MEMBERS" | sed 's/^/          /'
  echo "        Every targo run in this workspace exits 2 with no Gate: line until"
  echo "        that is fixed. This is NOT a trust-align result."
  exit 2
}

BACKUP="$(mktemp)"; cp "$SRC" "$BACKUP"
PRISTINE_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
restore() { cp "$BACKUP" "$SRC"; }
trap 'restore; rm -f "$BACKUP"' EXIT INT TERM

fails=0
LOG=""
run() { # run [policy]; sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-align ) > "$LOG" 2>&1
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
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-align --lib ) > "$LOG" 2>&1
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

echo "trust-align strict gate:"

# ---------------------------------------------------------------------------
# 1. THE PASS, asserted on exit code, Gate, compile status, coverage AND the
#    kind split — never on the Summary alone, and with the Gate line asserted
#    PRESENT so a seal failure cannot read as a pass.
# ---------------------------------------------------------------------------
STEP="THE PASS"; mut_begin
run
require_env "pristine"
G="$(gate_line)"
[ -n "$G" ] || fail "pristine: no Gate: line — the lane did not run, or the report did not seal (vacuous)"
[ "$RC" -eq 0 ] || fail "pristine: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "pristine: Gate is '$G'";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 34/34 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 34/34 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 84 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(84 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=3 arithmetic_overflow_mul=2 arithmetic_overflow_sub=3 \
            hardened_panic_boundary=7 postcondition=69; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
PRISTINE_KINDS="$KINDS"
mut_ok "pristine  $G  [69 postcondition + 8 safety + 7 hardened-twin, 0 unreachable]"
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
require_env "certify"
G="$(gate_line)"
[ -n "$G" ] || fail "certify: no Gate: line"
[ "$RC" -eq 0 ] || fail "certify: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "certify: Gate is '$G'";; esac
grep -qE 'Summary: 84 proved, 0 failed, .*0 inconclusive \(84 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
[ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
  || fail "certify: the kind split differs from the default policy"
mut_ok "certify   $G"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — the COMPOSITION CARRIER broken.
#    All four `*_within` wrappers inherit their bound from `clamp_u32`'s
#    postcondition. Breaking `clamp_u32` must refute every one of them as well
#    as `clamp_u32` itself. If it ever refutes only `clamp_u32`, the
#    composition stopped carrying and the wrappers' bounds are being proved by
#    something else — the shape that lets a wrapper keep a green row after its
#    evidence went away.
#
#    The eight arithmetic-free tier-1 lattice functions carry their own bounds
#    and are deliberately NOT touched, so they must stay green in the same run.
#    That makes this a specificity assertion as well as a sensitivity one.
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
for f in clamp_u32 align_up_within array_bytes_within view_end_within record_size2_within; do
  grep -q "verification failed for \`trust_align::$f\`" "$LOG" \
    || fail "mutation A: $f did not lose its bound — the composition is not carrying it"
done
for f in align_mask align_norm align_shift align_from_shift align_is_supported \
         is_power_of_two is_aligned align_max; do
  grep -q "verification failed for \`trust_align::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a clamp-only break — the lattice bounds are not independent"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — the WIDENING deleted.
#    `(value as u64) + m` becomes `(value + mask) as u64`: the same value on
#    every non-overflowing input, computed at `u32` where nothing bounds it.
#    This is `module_to_lir.rs:1116`'s defect reintroduced. Per fragment map
#    §4.7 a `u32` overflow is UNKNOWN rather than FAILED, which is fail-closed
#    and is what must be asserted — never `[FAILED]` on `u32` arithmetic.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate '    let s: u64 = (value as u64) + m;' \
       '    let s: u64 = (value + mask) as u64;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an unwidened round-up add still passed  $G"; else mut_ok "mutation B (raw_up_from_mask adds at u32)  rc=$RC  $G"; fi
grep -qE '\[(FAILED|UNKNOWN)\] \[overflow:add\]|arithmetic overflow \(Add\) (FAILED|UNKNOWN|RUNTIME CHECKED)' "$LOG" \
  || fail "mutation B: no add row went FAILED, UNKNOWN or RUNTIME CHECKED — $(grep -oE 'arithmetic overflow \([A-Za-z]+\) [A-Z ]+' "$LOG" | head -3 | tr '\n' ' ')"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — the ENTRY-PREFIX BUNDLING RULE.
#    `raw_up_from_mask` takes the MASK rather than the alignment so that its
#    arithmetic Assert sits at the entry prefix. Folding the `align_mask`
#    lookup back into the body puts a CALL before the Assert, and every caller
#    then fails to lower. This pins the load-bearing measurement behind the
#    crate's whole shape (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.1): if the
#    compiler ever admits it, this gate goes red and says so, rather than the
#    entry going stale.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    let m: u64 = mask as u64;' \
       '    let m: u64 = align_mask(mask) as u64;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an Assert behind a CALL bundled — §9.1 is stale and must be re-measured  $G"; else mut_ok "mutation C (align_mask folded into raw_up_from_mask)  rc=$RC  $G"; fi
grep -q 'member has a guarded or non-entry-prefix Assert' "$LOG" \
  || fail "mutation C: the bundle did not refuse a non-entry-prefix Assert — $(grep -oE 'native TrustIr bundle for .*' "$LOG" | head -1)"
grep -q 'refused Assert-bearing member `trust_align::raw_up_from_mask`' "$LOG" \
  || fail "mutation C: raw_up_from_mask was not the refused member"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION E — a CONTRACT that is simply false.
#    `align_shift` claims `result <= 32`; returning 33 makes the clause false
#    on a reachable path. Distinct from mutation A: there the carrier's body
#    stopped implying its clause, here a leaf's own returned value violates its
#    own clause directly.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate '    if align == 4096 {
        return 12;
    }' '    if align == 4096 {
        return 33;
    }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation E: a false ensures clause still passed  $G"; else mut_ok "mutation E (align_shift(4096) -> 33 against 'ensures result <= 32')  rc=$RC  $G"; fi
# §11.5 BUNDLING RECORD — `docs/STRICT_VERIFICATION_FRAGMENT.md` §11.5 says a
# callee whose rows go UNPROVEN stops being bundlable, so the compiler raises
# the error against its CALLER and not against the callee. An assertion naming
# the function the mutation broke is therefore wrong whenever that function is
# bundled. Recorded here per site so it is not rediscovered:
# `align_shift` has NO non-test caller at all (its only other mention in the
# non-test region is a doc reference at lib.rs:304). Nothing can bundle it, so
# §11.5 cannot apply and asserting its own name is the correct form here.
#
# Direction of the risk, which decides how much this matters: if the attribution
# ever moves, `grep -q … || fail` stops matching and this gate goes RED. It is a
# false-RED (fragility) risk, never a false-GREEN one — the opposite of the
# environment defect the G1 block above repairs. Do not "fix" a red here by
# deleting the assertion; read the member's own row first, because
# `member has a guarded or non-entry-prefix Assert` is emitted BOTH for §9.1's
# position refusal and for this unproven-rows refusal, with nothing in the text
# telling them apart.
grep -q 'verification failed for `trust_align::align_shift`' "$LOG" \
  || fail "mutation E: align_shift kept its bound while returning a value outside it"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION F — the view-end peak, so the proof's own TIGHTNESS is pinned.
#    `(byte_offset as u64) + (count as u64) * (elem_bytes as u64)` peaks at
#    exactly `2^64 - 2^32`, which is inside `u64` with almost no slack. Scaling
#    the offset term by `2^32` pushes the peak past `u64::MAX`. If this ever
#    stops firing, the view arithmetic is no longer proved at the full `u32`
#    domain and the crate's claim about `typedarray.rs:339` needs re-measuring.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate '    let e: u64 = (byte_offset as u64) + (count as u64) * (elem_bytes as u64);' \
       '    let e: u64 = (byte_offset as u64) * 4294967296 + (count as u64) * (elem_bytes as u64);'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation F: an overflowing view end still passed — the peak is no longer tight  $G"; else mut_ok "mutation F (view end offset scaled by 2^32, the u64 sum overflows)  rc=$RC  $G"; fi
# §11.5 BUNDLING RECORD — `docs/STRICT_VERIFICATION_FRAGMENT.md` §11.5 says a
# callee whose rows go UNPROVEN stops being bundlable, so the compiler raises
# the error against its CALLER and not against the callee. An assertion naming
# the function the mutation broke is therefore wrong whenever that function is
# bundled. Recorded here per site so it is not rediscovered:
# `raw_view_end` IS bundled — four non-test callers: `view_end` (lib.rs:593),
# `view_elem_offset` (:609), `raw_view_fits` (:624) and `view_end_within`
# (:655), plus `view_fits` transitively through `raw_view_fits` (:620). So this
# is the shape §11.5 warns about. Measured green on the 2026-08-29 baseline
# run of this gate: the callee IS still named in its own right, because an
# overflowing `u64` sum REFUTES its row rather than merely leaving it
# unproven, and only the latter is the case §11.5 describes.
#
# Direction of the risk, which decides how much this matters: if the attribution
# ever moves, `grep -q … || fail` stops matching and this gate goes RED. It is a
# false-RED (fragility) risk, never a false-GREEN one — the opposite of the
# environment defect the G1 block above repairs. Do not "fix" a red here by
# deleting the assertion; read the member's own row first, because
# `member has a guarded or non-entry-prefix Assert` is emitted BOTH for §9.1's
# position refusal and for this unproven-rows refusal, with nothing in the text
# telling them apart.
grep -q 'verification failed for `trust_align::raw_view_end`' "$LOG" \
  || fail "mutation F: raw_view_end did not lose a row"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 8. THE TESTS, AND THE TWO MUTATIONS THEY ALONE CAN CATCH.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)  $(grep -oE '^test result: .*' "$LOG" | head -1)"; else
  grep -qE '^test result: ok\. 19 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 19 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# --- MUTATION D — wrong value, TIER-1 POSTCONDITION SURVIVES ----------------
mutate '    if align == 16 {
        return 15;
    }' '    if align == 16 {
        return 7;
    }'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation D: the strict lane REFUTED a wrong mask (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged postcondition cannot see the answer is now stale and must be re-measured"
else
  [ "$(gate_line)" = "$G" ] 2>/dev/null || true
  grep -qE 'Summary: 84 proved, 0 failed, .*0 inconclusive \(84 total\)' "$LOG" \
    || fail "mutation D: the row count moved — the demonstration needs the split to be IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
    || fail "mutation D: the kind split moved under a wrong-value mutation"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation D: a wrong 16-byte mask passed the unit tests"; else
  mut_ok "mutation D (align_mask(16) -> 7; 'ensures result <= 4095' still TRUE)  tests rc=$RC, strict lane rc=$VRC"
fi
# Assert WHICH tests fail, by name. A bare rc would be satisfied by a broken
# doctest stage or a compile error, and the control would silently stop testing.
for t in the_lattice_chains_agree_with_each_other_and_with_core \
         align_up_matches_core_checked_next_multiple_of \
         the_published_layout_check_values_are_reproduced_exactly \
         align_up_wide_matches_the_counting_oracle_over_every_supported_alignment; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation D: $t did not catch a wrong 16-byte mask"
done
# The tier-1 BOUND test must still PASS — otherwise the demonstration degrades
# into "the mutation broke everything" and says nothing about proofs-vs-answers.
grep -q 'every_tier1_clamp_is_live_and_no_result_ever_exceeds_its_bound ... ok' "$LOG" \
  || fail "mutation D: the tier-1 bound test also went red — D no longer isolates 'proved contract over a wrong answer'"
# ...and the CONSISTENCY test CANNOT catch it, because it computes its
# expectation from the mutated function. Asserted, not merely noted: a test that
# derives its oracle from the code under test is not a test, and this is the
# in-tree demonstration.
grep -q 'align_up_agrees_with_the_mask_identity_it_is_built_from ... ok' "$LOG" \
  || echo "       (note: the mask-identity consistency test now also catches this; it did not when written)"
rm -f "$LOG"; restore

# --- MUTATION G — wrong value, a SATURATION DELETED, no obligation minted ---
mutate '    let p: u64 = (a as u64) * (b as u64);
    if p > 4294967295 {
        return 4294967295;
    }
    p as u32' \
       '    let p: u64 = (a as u64) * (b as u64);
    p as u32'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation G: the strict lane REFUTED a deleted saturation (rc=$VRC $VG) — welcome news, but §2.5's 'a truncating cast mints no obligation' is now stale and must be re-measured"
else
  grep -qE 'Summary: 84 proved, 0 failed, .*0 inconclusive \(84 total\)' "$LOG" \
    || fail "mutation G: the row count moved — deleting a saturating clamp must leave the split IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
    || fail "mutation G: the kind split moved when a runtime check was DELETED"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation G: a truncating array-size multiply passed the unit tests"; else
  mut_ok "mutation G (raw_sat_mul saturation deleted; truncating cast mints NO row)  tests rc=$RC, strict lane rc=$VRC"
fi
grep -q 'array_bytes_saturates_where_the_unguarded_multiply_wraps ... FAILED' "$LOG" \
  || fail "mutation G: array_bytes_saturates_where_the_unguarded_multiply_wraps did not catch a truncating multiply"
# Specificity: the tier-1 clamp is untouched, so its bound test must still pass.
grep -q 'every_tier1_clamp_is_live_and_no_result_ever_exceeds_its_bound ... ok' "$LOG" \
  || fail "mutation G: the tier-1 bound test also went red — G no longer isolates the deleted saturation"
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — a"
  echo "        truncating \`as\` cast is neither an overflow nor a zero divisor,"
  echo "        so DELETING the check removes no obligation.)"
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
