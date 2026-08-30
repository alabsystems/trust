#!/usr/bin/env bash
# trust_interval_strict_gate.sh — pin `crates/trust-interval` at a NON-VACUOUS
# pass of the authenticated strict lane, on BOTH policies, with live mutation
# controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-interval` is the eleventh `crates/`-resident component written to PASS
# the authenticated strict lane rather than to be retrofitted onto it, after
# `trust-ratio`, `trust-hex`, `trust-utf`, `trust-endian`, `trust-index`,
# `trust-varint`, `trust-checksum`, `trust-radix64`, `trust-align` and
# `trust-fixed`. Measured
# 2026-08-29 on stage1 driver `b46cd4dbccec1967`, identically under the default
# `unix_hardened` policy and under `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 70 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 29/29 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=4, arithmetic_overflow_sub=5,
#                   hardened_panic_boundary=8, postcondition=53
#
# A pass is worth nothing on its own, and every assertion below exists for one
# of the reasons this repo has paid for:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower
#     and reports `0 failed` with `Coverage: complete`. The compile status is
#     asserted, never inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`. The kind split
#     is asserted and `unreachable` is asserted ABSENT.
#  3. A pass never seen to fail is not evidence. Nine mutations run: seven that
#     must refute, and TWO that must NOT (H and I below).
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it BY NAME.
#  5. Proofs cover overflow and discharged contracts — NOT whether the answer is
#     right.
#
# MUTATIONS H AND I ARE THE POINT OF THIS GATE
# --------------------------------------------
# Both are wrong-VALUE changes the strict lane PASSES at exit 0, with the kind
# split BYTE-IDENTICAL to the pristine run.
#
#   H mutates a TIER-1 function. `clamp_hi_into(v, blo, bhi)` returns the TOP of
#     the target instead of the bottom when `v` is below it, so projecting a low
#     endpoint into a range lands at the wrong end of that range.
#     `ensures result <= bhi` stays TRUE — `bhi` is trivially inside it — so the
#     discharged POSTCONDITION survives intact alongside every safety row. A
#     proved *contract*, not merely a proved *safety obligation*, sits over an
#     answer that is wrong for one of the crate's two headline operations. The
#     gate additionally asserts that
#     `every_tier1_bound_holds_and_every_clamp_can_fire` still PASSES under H,
#     so the demonstration cannot degrade into "the mutation broke everything".
#
#   I mutates a TIER-2 arithmetic function. `span_len` returns `hi - lo + 2`.
#     The add's peak moves from `2^32` to `2^32 + 1`, which is still four
#     billion times inside `u64`, so the overflow row and its hardened twin both
#     still prove and the row count does not move. Every length the crate
#     reports is off by one.
#
#     I is ALSO this crate's demonstration of the asymmetry `trust-align` found:
#     `overlap_len_agrees_with_span_len_of_the_meet_consistency_only` computes
#     its expectation by CALLING `span_len`, so both sides of its assertion move
#     together and it passes under I. The gate asserts that it still passes.
#     A test that derives its oracle from the code under test is not a test, and
#     that test is named for it so the asymmetry is not rediscovered.
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit.
#   * A per-function `[VERIFIED] (n obligations: n proved …)` transport row can
#     be published for a function the compiler HARD-ERRORED on. Measured twice
#     while probing THIS crate: `p5_overlap_len` published
#     `[VERIFIED] (3 obligations: 3 proved, 0 failed, 0 unknown)` in a run whose
#     diagnostic for it was `error: Trust strict verification failed … 4
#     obligation(s) were not fully verified`, and `r9_distance` published
#     `[VERIFIED] (6 obligations: 6 proved …)` against `8 obligation(s) were not
#     fully verified`.
# So every assertion is on the EXIT CODE, the `Gate:` line, and the absence of
# `error:` lines — never on the Summary alone and never on a per-function row.
#
# AND A THIRD
#   * `targo trust check` can exit 2 having printed NO `Gate:` line, NO
#     `Summary:`, NO `Coverage:` and NO `error:` — only `could not seal the
#     final compiler rows, …`. It is reproducible from row COUNT alone
#     (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.2), so a gate that greps for
#     `error:` reads it as a pass. The `Gate:` line is asserted PRESENT first.
#
# Usage:  scripts/trust_interval_strict_gate.sh          (~25 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-interval/src/lib.rs"
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
  echo "        that is fixed. This is NOT a trust-interval result."
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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-interval ) > "$LOG" 2>&1
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
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-interval --lib ) > "$LOG" 2>&1
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

echo "trust-interval strict gate:"

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
grep -q 'Coverage: 29/29 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 29/29 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 70 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(70 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=4 arithmetic_overflow_sub=5 \
            hardened_panic_boundary=8 postcondition=53; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
PRISTINE_KINDS="$KINDS"
mut_ok "pristine  $G  [53 postcondition + 9 safety + 8 hardened-twin, 0 unreachable]"
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
grep -qE 'Summary: 70 proved, 0 failed, .*0 inconclusive \(70 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
[ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
  || fail "certify: the kind split differs from the default policy"
mut_ok "certify   $G"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — the COMPOSITION CARRIER broken.
#    `touches` is the crate's only shape-(B) wrapper: it has no body of its own
#    beyond a call to `raw_touches`, and inherits its bound from the fact that
#    the helper returns only 0 or 1
#    (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.3). Returning 2 from the helper
#    must refute `touches`, not merely `raw_touches`. If it ever refutes only
#    the helper, the wrapper's bound is being proved by something other than the
#    callee — the shape that lets a wrapper keep a green row after its evidence
#    went away.
#
#    The nine arithmetic-free tier-1 predicates carry their own bounds and are
#    deliberately NOT touched, so they must stay green in the same run. That
#    makes this a specificity assertion as well as a sensitivity one.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate '    if b == a + 1 {
        return 1;
    }
    0
}' '    if b == a + 1 {
        return 2;
    }
    0
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a helper returning 2 still passed  $G"; else mut_ok "mutation A (raw_touches returns 2)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_interval::touches`' "$LOG" \
  || fail "mutation A: touches did not lose its bound — the composition is not carrying it"
for f in is_empty is_nonempty is_degenerate contains_point contains_range \
         overlaps is_disjoint is_before is_equal; do
  grep -q "verification failed for \`trust_interval::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a touches-only break — the predicate bounds are not independent"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — a tier-1 CONTRACT that is simply false.
#    `intersect_hi` claims `result <= ahi` — the lattice law that a meet never
#    raises a high end. Returning `bhi` from the `ahi < bhi` arm makes the
#    clause false on a reachable path. Distinct from A: there the carrier
#    stopped supplying the bound, here a leaf's own returned value violates its
#    own clause directly.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate 'pub fn intersect_hi(ahi: u32, bhi: u32) -> u32 ensures result <= ahi {
    if ahi < bhi {
        return ahi;
    }' 'pub fn intersect_hi(ahi: u32, bhi: u32) -> u32 ensures result <= ahi {
    if ahi < bhi {
        return bhi;
    }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: a false lattice law still passed  $G"; else mut_ok "mutation B (intersect_hi(3,9) -> 9 against 'ensures result <= ahi')  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_interval::intersect_hi`' "$LOG" \
  || fail "mutation B: intersect_hi kept its bound while returning a value outside it"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — the WIDENING deleted, which pins the proof's TIGHTNESS.
#    `span_len`'s `(d as u64) + 1` peaks at exactly `2^32`, one past everything
#    a `u32` holds. Computing the `+ 1` at `u32` before widening is the same
#    value on every input except `span_len(0, u32::MAX)` — and that one input is
#    the whole reason the return type is `u64`. Per §4.7 a `u32` overflow is
#    UNKNOWN rather than FAILED, which is fail-closed and is what must be
#    asserted; never `[FAILED]` on `u32` arithmetic.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate '    (d as u64) + 1
}' '    (d + 1) as u64
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an unwidened +1 still passed — the peak is no longer tight  $G"; else mut_ok "mutation C (span_len adds at u32 before widening)  rc=$RC  $G"; fi
grep -qE '\[(FAILED|UNKNOWN)\] \[overflow:add\]|arithmetic overflow \(Add\) (FAILED|UNKNOWN|RUNTIME CHECKED)' "$LOG" \
  || fail "mutation C: no add row went FAILED, UNKNOWN or RUNTIME CHECKED — $(grep -oE 'arithmetic overflow \([A-Za-z]+\) [A-Z ]+' "$LOG" | head -3 | tr '\n' ' ')"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION D — the ENTRY-PREFIX BUNDLING RULE.
#    `span_len`'s arithmetic Assert sits at its entry prefix, which is why
#    `overlap_len`, `cover_len` and `clamped_len` can all bundle it. Putting any
#    CALL before that Assert must make every one of those callers fail to lower
#    (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.1). This pins the rule behind
#    the crate's whole shape: if the compiler ever admits it, this gate goes red
#    and says so, rather than the map entry going stale.
# ---------------------------------------------------------------------------
STEP="MUTATION D"; mut_begin
mutate '    let d: u32 = hi - lo;
    (d as u64) + 1' '    let _e: u8 = is_empty(lo, hi);
    let d: u32 = hi - lo;
    (d as u64) + 1'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation D: an Assert behind a CALL bundled — §9.1 is stale and must be re-measured  $G"; else mut_ok "mutation D (is_empty call folded into span_len)  rc=$RC  $G"; fi
grep -q 'member has a guarded or non-entry-prefix Assert' "$LOG" \
  || fail "mutation D: the bundle did not refuse a non-entry-prefix Assert — $(grep -oE 'native TrustIr bundle for .*' "$LOG" | head -1)"
grep -q 'refused Assert-bearing member `trust_interval::span_len`' "$LOG" \
  || fail "mutation D: span_len was not the refused member"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION E — the SELECT-DERIVED SUBTRACTION.
#    This is the boundary this crate measured and the reason `overlap_len`
#    delegates instead of computing: a subtraction whose operands are
#    select-derived locals does not prove, however it is guarded
#    (`docs/STRICT_VERIFICATION_FRAGMENT.md` §11.1). Inlining `span_len`'s body
#    into `overlap_len` — same values, same guard, same subtraction, one fewer
#    call — must fail. If it ever passes, §11.1 is stale and the delegation
#    throughout this crate is unnecessary.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate '    let hi: u32 = if ahi < bhi { ahi } else { bhi };
    span_len(lo, hi)
}' '    let hi: u32 = if ahi < bhi { ahi } else { bhi };
    if lo > hi {
        return 0;
    }
    let d: u32 = hi - lo;
    (d as u64) + 1
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation E: a select-derived subtraction PROVED — §11.1 is stale; re-measure and simplify this crate  $G"; else mut_ok "mutation E (span_len inlined into overlap_len over two selects)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_interval::overlap_len`' "$LOG" \
  || fail "mutation E: overlap_len did not lose a row"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 8. MUTATION F — the midpoint WIDENING deleted.
#    `(lo as u64) + (hi as u64)` is what makes `midpoint` overflow-free;
#    `(lo + hi) as u64` is the textbook bug, computed at `u32` where the sum of
#    two large endpoints wraps. The narrowing cast at the end mints no
#    obligation (§2.5), so this row is the only thing standing between the
#    crate and a silently wrong bisection.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate '    let s: u64 = (lo as u64) + (hi as u64);' \
       '    let s: u64 = (lo + hi) as u64;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation F: an unwidened midpoint sum still passed  $G"; else mut_ok "mutation F (midpoint adds at u32)  rc=$RC  $G"; fi
grep -qE '\[(FAILED|UNKNOWN)\] \[overflow:add\]|arithmetic overflow \(Add\) (FAILED|UNKNOWN|RUNTIME CHECKED)' "$LOG" \
  || fail "mutation F: no add row went FAILED, UNKNOWN or RUNTIME CHECKED"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 9. MUTATION G — the DEAD guard deleted.
#    `gap`'s `if d == 0 { return 0; }` is mathematically dead: `blo > ahi`
#    already gives `d >= 1`. It is structurally required, because the interval
#    engine does not carry `blo > ahi` into a bound on `d - 1` (§2.5). Deleting
#    it must refute. This is the assertion that keeps the comment above that
#    guard honest — if the engine ever learns the chain, this goes red and the
#    dead guard can be deleted for real.
#
#    NOTE THE ATTRIBUTION, which is why this gate does not assert
#    `verification failed for `trust_interval::gap``: there is no such line.
#    `gap` goes `[INCONCLUSIVE] (4 obligations: 2 proved, 2 unknown)`, and
#    because its own rows are now unproven it stops being BUNDLABLE — so the
#    single `error:` in the run is raised against its CALLER:
#
#      error: Trust full verification failed for `trust_interval::distance`: …
#        = note: … bundle for `trust_interval::distance` refused Assert-bearing
#                member `trust_interval::gap`: member has a guarded or
#                non-entry-prefix Assert
#
#    This is §7.2's observation run backwards ("fix the callee's rows and the
#    bundle appears"): break the callee's rows and the bundle disappears, and
#    the diagnostic surfaces one level UP. Both halves are asserted below, so a
#    change in the attribution direction is a red gate rather than a silent
#    weakening. Measured 2026-08-29.
# ---------------------------------------------------------------------------
STEP="MUTATION G"; mut_begin
mutate '    let d: u32 = blo - ahi;
    if d == 0 {
        return 0;
    }
    d - 1' '    let d: u32 = blo - ahi;
    d - 1'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation G: gap proved without its structurally-required guard — §2.5 is stale, delete the dead guard  $G"; else mut_ok "mutation G (gap's dead-but-required d==0 guard deleted)  rc=$RC  $G"; fi
grep -qE 'trust_interval::gap \[INCONCLUSIVE\].*[1-9][0-9]* unknown' "$LOG" \
  || fail "mutation G: gap did not lose a row — $(grep -oE 'trust_interval::gap \[[A-Z]+\] \([^;]*' "$LOG" | head -1)"
grep -q 'refused Assert-bearing member `trust_interval::gap`' "$LOG" \
  || fail "mutation G: gap was not named as the refused bundle member"
grep -q 'verification failed for `trust_interval::distance`' "$LOG" \
  || fail "mutation G: the refusal was not raised against the CALLER — the attribution direction changed and the note above is stale"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 10. THE TESTS, AND THE TWO MUTATIONS THEY ALONE CAN CATCH.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)  $(grep -oE '^test result: .*' "$LOG" | head -1)"; else
  grep -qE '^test result: ok\. 17 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 17 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# --- MUTATION H — wrong value, TIER-1 POSTCONDITION SURVIVES ----------------
mutate 'pub fn clamp_hi_into(v: u32, blo: u32, bhi: u32) -> u32 ensures result <= bhi {
    if bhi < blo {
        return bhi;
    }
    if v > bhi {
        return bhi;
    }
    if v < blo {
        return blo;
    }' 'pub fn clamp_hi_into(v: u32, blo: u32, bhi: u32) -> u32 ensures result <= bhi {
    if bhi < blo {
        return bhi;
    }
    if v > bhi {
        return bhi;
    }
    if v < blo {
        return bhi;
    }'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation H: the strict lane REFUTED a wrong projection (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged postcondition cannot see the answer is now stale and must be re-measured"
else
  grep -qE 'Summary: 70 proved, 0 failed, .*0 inconclusive \(70 total\)' "$LOG" \
    || fail "mutation H: the row count moved — the demonstration needs the split to be IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
    || fail "mutation H: the kind split moved under a wrong-value mutation"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation H: a wrong projection passed the unit tests"; else
  mut_ok "mutation H (clamp_hi_into lands at the TOP of the target; 'ensures result <= bhi' still TRUE)  tests rc=$RC, strict lane rc=$VRC"
fi
# Assert WHICH tests fail, by name. A bare rc would be satisfied by a broken
# doctest stage or a compile error, and the control would silently stop testing.
grep -q 'projection_moves_each_endpoint_to_the_nearest_point_of_the_target ... FAILED' "$LOG" \
  || fail "mutation H: the nearest-point oracle did not catch a wrong projection"
# The tier-1 BOUND test must still PASS — otherwise the demonstration degrades
# into "the mutation broke everything" and says nothing about proofs-vs-answers.
grep -q 'every_tier1_bound_holds_and_every_clamp_can_fire ... ok' "$LOG" \
  || fail "mutation H: the tier-1 bound test also went red — H no longer isolates 'proved contract over a wrong answer'"
rm -f "$LOG"; restore

# --- MUTATION I — wrong value, and the CONSISTENCY test cannot see it -------
mutate '    (d as u64) + 1
}' '    (d as u64) + 2
}'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation I: the strict lane REFUTED an off-by-one length (rc=$VRC $VG) — welcome news, but the peak is nowhere near u64::MAX and this must be re-measured"
else
  grep -qE 'Summary: 70 proved, 0 failed, .*0 inconclusive \(70 total\)' "$LOG" \
    || fail "mutation I: the row count moved — an in-range coefficient change must leave the split IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
    || fail "mutation I: the kind split moved under a wrong-value mutation"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation I: an off-by-one span_len passed the unit tests"; else
  mut_ok "mutation I (span_len returns hi-lo+2; the Add row still proves)  tests rc=$RC, strict lane rc=$VRC"
fi
for t in span_len_counts_the_inclusive_range \
         the_predicates_agree_with_brute_force_membership \
         the_half_open_and_closed_forms_round_trip \
         projection_and_intersection_differ_and_neither_is_the_other; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation I: $t did not catch an off-by-one length"
done
# ...and the CONSISTENCY test CANNOT catch it, because it computes its
# expectation by calling the mutated function. Asserted, not merely noted: a
# test that derives its oracle from the code under test is not a test, and this
# is the in-tree demonstration.
grep -q 'overlap_len_agrees_with_span_len_of_the_meet_consistency_only ... ok' "$LOG" \
  || fail "mutation I: the consistency test now catches this too — it did not when written, and the gate's demonstration of oracle-derivation is stale"
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — the"
  echo "        add's peak moved from 2^32 to 2^32+1, both far inside u64, so the"
  echo "        overflow row and its hardened twin still prove.)"
fi
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 11. The restore actually restored. A gate that leaves a mutation behind turns
#     the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
STEP="The restore actually restored"; mut_begin
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

mut_end
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
