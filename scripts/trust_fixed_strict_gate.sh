#!/usr/bin/env bash
# trust_fixed_strict_gate.sh — pin `crates/trust-fixed` at a NON-VACUOUS pass of
# the authenticated strict lane, on BOTH policies, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-fixed` is the tenth `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it, after
# `trust-ratio`, `trust-hex`, `trust-utf`, `trust-endian`, `trust-index`,
# `trust-varint`, `trust-checksum`, `trust-radix64` and `trust-align`. Measured
# 2026-08-29 on stage1 driver `803f47350d324d26`, identically under the default
# `unix_hardened` policy and under `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 127 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 32/32 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=9, arithmetic_overflow_mul=8,
#                   arithmetic_overflow_sub=1, division_by_zero=10,
#                   hardened_panic_boundary=41, postcondition=54,
#                   remainder_by_zero=4
#
# A pass is worth nothing on its own, and every assertion below exists for one
# of the five reasons this repo has paid for:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower
#     and reports `0 failed` with `Coverage: complete`. The compile status is
#     asserted, never inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`. The kind split
#     is asserted and `unreachable` is asserted ABSENT. All 127 rows here are
#     54 postconditions + 32 primary safety + 41 hardened twins.
#  3. A pass never seen to fail is not evidence. Seven mutations run: five that
#     must refute, and TWO that must NOT (D and G below).
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it BY NAME.
#  5. Proofs cover overflow, zero divisors and discharged contracts — NOT
#     whether the answer is right. A ROUNDING THRESHOLD is invisible to every
#     obligation this crate has, which is what mutations D and G demonstrate.
#
# MUTATIONS D AND G ARE THE POINT OF THIS GATE
# --------------------------------------------
# Both are wrong-VALUE changes the strict lane PASSES at exit 0, with the kind
# split BYTE-IDENTICAL to the pristine run.
#
#   D mutates a TIER-1 function. `binary_scale(16)` returns `32768` instead of
#     `65536`, so every Q16.16 computation in the crate runs at Q17.15.
#     `ensures result <= 65536` stays TRUE — 32768 is well inside it — so the
#     discharged POSTCONDITION survives intact alongside every safety row. A
#     proved *contract*, not merely a proved *safety obligation*, sits over an
#     answer that is wrong for the crate's headline format.
#
#     Note which test does NOT catch it:
#     `a_whole_unit_converts_back_to_one_at_every_binary_scale` computes its
#     expectation FROM `binary_scale`, so it is a consistency test and moves
#     with the mutation. Only the tests that spell `65536` out, or that ask
#     `core` for `1 << b`, can refuse it. A test that derives its oracle from
#     the code under test is not a test, and this gate asserts that it still
#     passes so the asymmetry is not rediscovered.
#
#   G mutates a ROUNDING THRESHOLD. `mul_div_round`'s increment becomes `d / 4`
#     instead of `d / 2`, so the function rounds at the quarter point and is no
#     longer round-half-away-from-zero at all. Every operator is unchanged, so
#     the row count and the kind split do not move by a single entry, and the
#     lane stays at exit 0 — the entire subject of this crate is which way a
#     division rounds, and NO obligation it has can see it. This is the sharpest
#     available demonstration for this domain, on the same terms as
#     `trust-endian`'s byte-order swap.
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit.
#   * A per-function `[VERIFIED] (n obligations: n proved …)` transport row can
#     be published for a function the compiler HARD-ERRORED on.
# So every assertion is on the EXIT CODE, the `Gate:` line, and the absence of
# `error:` lines — never on the Summary alone and never on a per-function row.
#
# AND A THIRD
# -----------
#   * `targo trust check` can exit 2 having printed NO `Gate:` line, NO
#     `Summary:`, NO `Coverage:` and NO `error:` — only
#     `could not seal the final compiler rows, …`. The crate compiled and
#     verified; the report could not be published. It is reproducible from row
#     COUNT alone (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.2), so a gate that
#     greps for `error:` reads it as a pass. The `Gate:` line is asserted
#     PRESENT before anything else is read. This crate's 54 postconditions are
#     deliberately inside that bracket.
#
# Usage:  scripts/trust_fixed_strict_gate.sh          (~12 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-fixed/src/lib.rs"
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
# seal failure and from a real crate regression. Name the real cause instead.
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
  echo "        that is fixed. This is NOT a trust-fixed result."
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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-fixed ) > "$LOG" 2>&1
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
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-fixed --lib ) > "$LOG" 2>&1
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

echo "trust-fixed strict gate:"

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
grep -q 'Coverage: 32/32 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 32/32 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 127 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(127 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=9 arithmetic_overflow_mul=8 arithmetic_overflow_sub=1 \
            division_by_zero=10 hardened_panic_boundary=41 postcondition=54 \
            remainder_by_zero=4; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
PRISTINE_KINDS="$KINDS"
mut_ok "pristine  $G  [54 postcondition + 32 safety + 41 hardened-twin, 0 unreachable]"
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
grep -qE 'Summary: 127 proved, 0 failed, .*0 inconclusive \(127 total\)' "$LOG" \
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
#    The five arithmetic-free tier-1 lattice functions carry their own bounds
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
for f in clamp_u32 scaled_add_within to_fixed_within from_parts_within binary_frac_within; do
  grep -q "verification failed for \`trust_fixed::$f\`" "$LOG" \
    || fail "mutation A: $f did not lose its bound — the composition is not carrying it"
done
for f in decimal_scale decimal_scale_is_exact binary_scale binary_scale_is_exact binary_frac_mask; do
  grep -q "verification failed for \`trust_fixed::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a clamp-only break — the lattice bounds are not independent"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — the WIDENING deleted.
#    `(a as u64) * (b as u64)` becomes `(a * b) as u64`: the same value on every
#    non-overflowing input, computed at `u32` where nothing bounds it. Per
#    fragment map §4.7 a `u32` overflow is UNKNOWN rather than FAILED, which is
#    fail-closed and is what must be asserted — never `[FAILED]` on `u32`
#    arithmetic.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate 'fn raw_sat_mul(a: u32, b: u32) -> u32 {
    let p: u64 = (a as u64) * (b as u64);' \
       'fn raw_sat_mul(a: u32, b: u32) -> u32 {
    let p: u64 = (a * b) as u64;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an unwidened saturating multiply still passed  $G"; else mut_ok "mutation B (raw_sat_mul multiplies at u32)  rc=$RC  $G"; fi
grep -qE '\[(FAILED|UNKNOWN)\] \[overflow:mul\]|arithmetic overflow \(Mul\) (FAILED|UNKNOWN|RUNTIME CHECKED)' "$LOG" \
  || fail "mutation B: no mul row went FAILED, UNKNOWN or RUNTIME CHECKED — $(grep -oE 'arithmetic overflow \([A-Za-z]+\) [A-Z ]+' "$LOG" | head -3 | tr '\n' ' ')"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — the ENTRY-PREFIX BUNDLING RULE.
#    Every arithmetic function here takes the SCALE, never the format code, so
#    that its arithmetic Assert sits at the entry prefix. Folding the
#    `binary_scale` lookup back into `raw_from_parts` puts a CALL before the
#    Assert, and every caller then fails to lower. This pins the load-bearing
#    measurement behind the crate's whole shape
#    (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.1): if the compiler ever admits
#    it, this gate goes red and says so, rather than the entry going stale.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    let p: u64 = (int_part as u64) * (scale as u64);' \
       '    let p: u64 = (int_part as u64) * (binary_scale(scale) as u64);'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an Assert behind a CALL bundled — §9.1 is stale and must be re-measured  $G"; else mut_ok "mutation C (binary_scale folded into raw_from_parts)  rc=$RC  $G"; fi
grep -q 'member has a guarded or non-entry-prefix Assert' "$LOG" \
  || fail "mutation C: the bundle did not refuse a non-entry-prefix Assert — $(grep -oE 'native TrustIr bundle for .*' "$LOG" | head -1)"
grep -q 'refused Assert-bearing member `trust_fixed::raw_from_parts`' "$LOG" \
  || fail "mutation C: raw_from_parts was not the refused member"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION E — a CONTRACT that is simply false.
#    `binary_scale` claims `result <= 65536`; returning 131072 makes the clause
#    false on a reachable path. Distinct from mutation A: there the carrier's
#    body stopped implying its clause, here a leaf's own returned value violates
#    its own clause directly.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate '    if frac_bits == 15 {
        return 32768;
    }
    65536
}' '    if frac_bits == 15 {
        return 32768;
    }
    131072
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation E: a false ensures clause still passed  $G"; else mut_ok "mutation E (binary_scale(16) -> 131072 against 'ensures result <= 65536')  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_fixed::binary_scale`' "$LOG" \
  || fail "mutation E: binary_scale kept its bound while returning a value outside it"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION F — the from-parts peak, so the proof's own TIGHTNESS is pinned.
#    `(int_part as u64) * (scale as u64) + (frac as u64)` peaks at exactly
#    `(2^32-1)^2 + (2^32-1) == 18446744069414584320`, leaving `2^32-1` of slack
#    under `u64::MAX`.
#
#    THE COEFFICIENT WAS RECOMPUTED FOR THIS ARITHMETIC, NOT TRANSPLANTED.
#    Measured in one run: `* 2` puts the peak at EXACTLY `u64::MAX
#    == 18446744073709551615` and still proves 6/6; `* 3` is the first that
#    fires. A coefficient copied from another crate's mutation would have been
#    a silently dead control.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate '    let s: u64 = p + (frac as u64);' \
       '    let s: u64 = p + (frac as u64) * 3;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation F: an overflowing from-parts sum still passed — the peak is no longer tight  $G"; else mut_ok "mutation F (from-parts fractional term scaled by 3; the u64 sum overflows)  rc=$RC  $G"; fi
# §11.5 BUNDLING RECORD — `docs/STRICT_VERIFICATION_FRAGMENT.md` §11.5 says a
# callee whose rows go UNPROVEN stops being bundlable, so the compiler raises
# the error against its CALLER and not against the callee. An assertion naming
# the function the mutation broke is therefore wrong whenever that function is
# bundled. Recorded here per site so it is not rediscovered:
# `raw_from_parts` IS bundled — two non-test callers, `from_parts`
# (lib.rs:450) and `from_parts_within` (:496). Measured green on the
# 2026-08-29 baseline run of this gate.
#
# Direction of the risk, which decides how much this matters: if the attribution
# ever moves, `grep -q … || fail` stops matching and this gate goes RED. It is a
# false-RED (fragility) risk, never a false-GREEN one — the opposite of the
# environment defect the G1 block above repairs. Do not "fix" a red here by
# deleting the assertion; read the member's own row first, because
# `member has a guarded or non-entry-prefix Assert` is emitted BOTH for §9.1's
# position refusal and for this unproven-rows refusal, with nothing in the text
# telling them apart.
grep -q 'verification failed for `trust_fixed::raw_from_parts`' "$LOG" \
  || fail "mutation F: raw_from_parts did not lose a row"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 8. THE TESTS, AND THE TWO MUTATIONS THEY ALONE CAN CATCH.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)  $(grep -oE '^test result: .*' "$LOG" | head -1)"; else
  grep -qE '^test result: ok\. 23 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 23 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# --- MUTATION D — wrong value, TIER-1 POSTCONDITION SURVIVES ----------------
mutate '    if frac_bits == 15 {
        return 32768;
    }
    65536
}' '    if frac_bits == 15 {
        return 32768;
    }
    32768
}'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation D: the strict lane REFUTED a wrong scale (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged postcondition cannot see the answer is now stale and must be re-measured"
else
  grep -qE 'Summary: 127 proved, 0 failed, .*0 inconclusive \(127 total\)' "$LOG" \
    || fail "mutation D: the row count moved — the demonstration needs the split to be IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
    || fail "mutation D: the kind split moved under a wrong-value mutation"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation D: a wrong Q16.16 scale passed the unit tests"; else
  mut_ok "mutation D (binary_scale(16) -> 32768; 'ensures result <= 65536' still TRUE)  tests rc=$RC, strict lane rc=$VRC"
fi
# Assert WHICH tests fail, by name. A bare rc would be satisfied by a broken
# doctest stage or a compile error, and the control would silently stop testing.
for t in binary_scale_matches_two_to_the_power_and_saturates_past_it \
         binary_frac_part_matches_modulo_at_every_supported_binary_scale \
         q16_16_arithmetic_reproduces_hand_computed_values; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation D: $t did not catch a wrong Q16.16 scale"
done
# The tier-1 BOUND test must still PASS — otherwise the demonstration degrades
# into "the mutation broke everything" and says nothing about proofs-vs-answers.
grep -q 'every_tier1_clamp_is_live_and_no_result_ever_exceeds_its_bound ... ok' "$LOG" \
  || fail "mutation D: the tier-1 bound test also went red — D no longer isolates 'proved contract over a wrong answer'"
# ...and the CONSISTENCY test CANNOT catch it, because it computes its
# expectation from the mutated function. Asserted, not merely noted: a test that
# derives its oracle from the code under test is not a test, and this is the
# in-tree demonstration.
grep -q 'a_whole_unit_converts_back_to_one_at_every_binary_scale ... ok' "$LOG" \
  || fail "mutation D: the self-oracle consistency test went red — it is in this crate precisely to demonstrate that it CANNOT catch D; if it now can, the demonstration must be rebuilt"
rm -f "$LOG"; restore

# --- MUTATION G — wrong value, a ROUNDING THRESHOLD, split IDENTICAL --------
#     `mul_div_round` rounds at the QUARTER point instead of the half. Every
#     operator is unchanged — a `/` by a different literal — so not one row
#     moves, and the lane stays at exit 0 while the function stops being
#     round-half-away-from-zero. Which way a division rounds is this crate's
#     entire subject and no obligation it has can see it.
mutate '    let h: u64 = dd / 2;' \
       '    let h: u64 = dd / 4;'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation G: the strict lane REFUTED a changed rounding threshold (rc=$VRC $VG) — welcome news, but the claim that a proof cannot see a rounding mode is now stale and must be re-measured"
else
  grep -qE 'Summary: 127 proved, 0 failed, .*0 inconclusive \(127 total\)' "$LOG" \
    || fail "mutation G: the row count moved — changing a literal divisor must leave the split IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
    || fail "mutation G: the kind split moved when only a rounding threshold changed"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation G: a quarter-point rounding threshold passed the unit tests"; else
  mut_ok "mutation G (mul_div_round increments by d/4, not d/2)  tests rc=$RC, strict lane rc=$VRC"
fi
for t in mul_div_matches_the_u128_oracle_in_all_three_modes \
         mul_div_round_turns_over_at_exactly_half_the_divisor \
         rescale_is_mul_div_with_its_arguments_reordered; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation G: $t did not catch a changed rounding threshold"
done
# Specificity: `to_int_round` is a SEPARATE body with its own `s / 2`, untouched
# by this mutation, so the rounding-mode ordering test must still pass. If it
# goes red, the mutation reached further than intended and G stops isolating
# "the proofs cannot see which way it rounds".
grep -q 'the_rounding_modes_are_ordered_on_every_input ... ok' "$LOG" \
  || fail "mutation G: the rounding-order test also went red — G no longer isolates mul_div_round"
grep -q 'every_tier1_clamp_is_live_and_no_result_ever_exceeds_its_bound ... ok' "$LOG" \
  || fail "mutation G: the tier-1 bound test also went red — G no longer isolates the rounding threshold"
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — a"
  echo "        rounding threshold is a literal divisor, not an obligation, so"
  echo "        changing it removes and adds no row.)"
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
