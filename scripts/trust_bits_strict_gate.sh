#!/usr/bin/env bash
# trust_bits_strict_gate.sh — pin `crates/trust-bits` at a NON-VACUOUS pass of
# the authenticated strict lane, on BOTH policies, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-bits` is the twelfth `crates/`-resident component written to PASS the
# authenticated strict lane rather than to be retrofitted onto it, after
# `trust-ratio`, `trust-hex`, `trust-utf`, `trust-endian`, `trust-index`,
# `trust-varint`, `trust-checksum`, `trust-radix64`, `trust-align`,
# `trust-fixed` and `trust-interval`. Measured 2026-08-29 on stage1 driver
# `67b7f9b330b75a8f`, identically under the default `unix_hardened` policy and
# under `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 114 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 41/41 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=21, arithmetic_overflow_mul=12,
#                   arithmetic_overflow_sub=1, division_by_zero=1,
#                   hardened_panic_boundary=35, postcondition=43,
#                   remainder_by_zero=1
#
# A pass is worth nothing on its own, and every assertion below exists for one
# of the reasons this repo has paid for:
#
#  1. A crate that FAILS TO COMPILE emits no obligations for what did not lower
#     and reports `0 failed` with `Coverage: complete`. The compile status is
#     asserted, never inferred from the Summary.
#  2. `VcKind::Unreachable`'s formula is literally `Bool(true)`. The kind split
#     is asserted and `unreachable` is asserted ABSENT.
#  3. A pass never seen to fail is not evidence. Twelve mutations run: ten that
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
#   H swaps two coefficients in `rev8`'s weighted sum. Bit reversal is this
#     crate's `trust-endian` moment: NO obligation it has can see which bit got
#     which weight, and swapping two of them leaves the coefficient MULTISET
#     unchanged — so the engine's peak stays at exactly `255 * 255` and all 28
#     of `rev8`'s rows still prove while every reversal the crate computes is
#     wrong. The peak was recomputed for this crate and not transplanted; see
#     mutation L for the coefficient boundary that WAS tight here.
#
#   I mutates a TIER-1 function. `leading_zeros_u8` returns `3` where it should
#     return `4`. `ensures result <= 8` stays TRUE — 3 is trivially inside it —
#     so the nine discharged POSTCONDITION rows survive intact alongside every
#     safety row. A proved *contract*, not merely a proved *safety obligation*,
#     sits over an answer that is wrong for sixteen of the 256 inputs. The gate
#     additionally asserts that `every_tier1_bound_holds_and_every_clamp_can_fire`
#     still PASSES under I, so the demonstration cannot degrade into "the
#     mutation broke everything".
#
# TWO TRAPS, IN OPPOSITE DIRECTIONS, AND NEITHER CHECK SUBSUMES THE OTHER
# -----------------------------------------------------------------------
#   * The `Summary:` line can read like a pass at a NONZERO exit.
#   * A per-function `[VERIFIED] (n obligations: n proved …)` transport row can
#     be published for a function the compiler HARD-ERRORED on. Measured while
#     probing THIS crate: `r5_reverse32` published
#     `[VERIFIED] (4 obligations: 4 proved, 0 failed, 0 unknown)` in a run whose
#     only diagnostic for it was `error: Trust full verification failed`.
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
# ATTRIBUTION (§11.5) — READ BEFORE ADDING AN ASSERTION
#   A broken callee reports its error against its CALLER. Five of the ten
#   refuting mutations below break a BUNDLED member, and for those the gate
#   asserts the `refused Assert-bearing member` note plus the caller's name —
#   never `verification failed for <the function that was mutated>`, because
#   for `sum8` and `field` there is no such line at all. Mutation D asserts the
#   ABSENCE of one, so a change in the attribution direction is a red gate
#   rather than a silent weakening.
#
# Usage:  scripts/trust_bits_strict_gate.sh          (~25 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-bits/src/lib.rs"
TARGO="${TARGO:-$REPO_ROOT/build/aarch64-apple-darwin/stage1/bin/targo}"

[ -x "$TARGO" ] || { echo "REFUSE: no targo at $TARGO (set TARGO=...)"; exit 2; }
# The ONLY discriminator that has held under every measurement: a stage whose
# targo was never rebuilt ships upstream cargo under the name `targo` and
# verifies NOTHING while succeeding. `targo trust --help` passes on
# cargo-in-disguise (cargo execs the sibling `targo-trust` binary), so it is not
# a test; `--unverified` is a flag only targo has.
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
  echo "        that is fixed. This is NOT a trust-bits result."
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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-bits ) > "$LOG" 2>&1
  RC=$?
}
# `--lib` is load-bearing. Measured 2026-08-29 on `trust-endian`: a concurrent
# `x.py check` rebuilt `librustc_driver-<hash>.dylib`, stage1 `trustdoc` still
# referenced the old hash, and the doctest stage died with SIGABRT — `targo
# test` exited 101 with every unit test passing, on a crate with no doctests.
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-bits --lib ) > "$LOG" 2>&1
  RC=$?
}
gate_line() { grep -oE 'Gate: [A-Z]+ \[strict lane, exit [0-9]+\]' "$LOG" | tail -1; }
kinds() { grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1; }
fail() { echo "  FAIL $*"; fails=$((fails+1)); }

# ENVIRONMENT, NOT A RESULT. A transient `trustd` outage makes EVERY obligation
# report `unsupported MIR MemoryAdmission: … trust-memory-jobserver.sock:
# Connection refused`, so the run publishes `0 proved / N inconclusive`,
# `Gate: FAIL`, and many `error:` lines — a perfect imitation of a total crate
# regression, on source that passed minutes earlier. Name it, do not count it.
env_broken() { grep -q 'MemoryAdmission\|trust-memory-jobserver.sock' "$LOG"; }
check_env() { # check_env <label>
  if env_broken; then
    echo "  ENV  $1: trustd memory admission was unavailable — every obligation went UNKNOWN"
    echo "       before solver dispatch. This is NOT a trust-bits result. Re-run."
    fails=$((fails+1))
    return 1
  fi
  return 0
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

echo "trust-bits strict gate:"

# ---------------------------------------------------------------------------
# 1. THE PASS, asserted on exit code, Gate, compile status, coverage AND the
#    kind split — never on the Summary alone, and with the Gate line asserted
#    PRESENT so a seal failure cannot read as a pass.
# ---------------------------------------------------------------------------
run
check_env "pristine"
G="$(gate_line)"
[ -n "$G" ] || fail "pristine: no Gate: line — the lane did not run, or the report did not seal (vacuous)"
[ "$RC" -eq 0 ] || fail "pristine: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "pristine: Gate is '$G'";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 41/41 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 41/41 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 114 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(114 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(kinds)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=21 arithmetic_overflow_mul=12 arithmetic_overflow_sub=1 \
            division_by_zero=1 hardened_panic_boundary=35 postcondition=43 remainder_by_zero=1; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
PRISTINE_KINDS="$KINDS"
[ "$fails" -eq 0 ] && echo "  ok   pristine  $G  [43 postcondition + 36 safety + 35 hardened-twin, 0 unreachable]"
rm -f "$LOG"

# ---------------------------------------------------------------------------
# 2. THE SAME PASS UNDER `-Ztrust-policy=certify`.
#    A misspelled TRUSTFLAGS is dropped, so first prove the flag path reaches
#    the compiler by requiring a bogus policy to be REJECTED BY NAME. Without
#    this control, "certify passed" is indistinguishable from "certify never
#    ran".
# ---------------------------------------------------------------------------
run "-Ztrust-policy=bogus_not_a_policy"
grep -q "incorrect value \`bogus_not_a_policy\` for unstable option \`trust-policy\`" "$LOG" \
  || fail "TRUSTFLAGS control: a bogus policy was NOT rejected — the flag never reaches the compiler, so the certify run below proves nothing"
rm -f "$LOG"

run "-Ztrust-policy=certify"
check_env "certify"
G="$(gate_line)"
[ -n "$G" ] || fail "certify: no Gate: line"
[ "$RC" -eq 0 ] || fail "certify: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "certify: Gate is '$G'";; esac
grep -qE 'Summary: 114 proved, 0 failed, .*0 inconclusive \(114 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
[ "$(kinds)" = "$PRISTINE_KINDS" ] || fail "certify: the kind split differs from the default policy"
[ "$fails" -eq 0 ] && echo "  ok   certify   $G"
rm -f "$LOG"

# ---------------------------------------------------------------------------
# 3. MUTATION A — a tier-1 CONTRACT that is simply false.
#    `nibble_ones` claims `ensures result <= 4`, which is the one bound in this
#    crate that is NOT the width of its argument type: a nibble has four bits,
#    but the parameter is a `u32`. Returning 5 from the all-ones arm makes the
#    clause false on a reachable path.
# ---------------------------------------------------------------------------
mutate '    if v & 15 == 15 {
        return 4;
    }' '    if v & 15 == 15 {
        return 5;
    }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: nibble_ones(15) -> 5 still satisfied 'ensures result <= 4'  $G"; else echo "  ok   mutation A (nibble_ones(15) -> 5 against 'ensures result <= 4')  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_bits::nibble_ones`' "$LOG" \
  || fail "mutation A: nibble_ones kept its bound while returning a value outside it"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 4. MUTATION B — the COMPOSITION CARRIER broken.
#    The four tier-1 predicates have no body of their own beyond one call, and
#    inherit `ensures result <= 1` from the fact that the helper's body PINS its
#    return to `0` or `1` (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.3).
#    Returning 2 from `raw_is_power_of_two` must refute `is_power_of_two`, not
#    merely the helper. If it ever refutes only the helper, the wrapper's bound
#    is being proved by something other than the callee — the shape that lets a
#    wrapper keep a green row after its evidence went away.
#
#    The other three predicates carry their own pinned helpers and are
#    deliberately NOT touched, so they must stay green in the same run. That
#    makes this a specificity assertion as well as a sensitivity one.
# ---------------------------------------------------------------------------
mutate '    if x & (x - 1) == 0 {
        return 1;
    }' '    if x & (x - 1) == 0 {
        return 2;
    }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: a helper returning 2 still passed  $G"; else echo "  ok   mutation B (raw_is_power_of_two returns 2)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_bits::is_power_of_two`' "$LOG" \
  || fail "mutation B: is_power_of_two did not lose its bound — the composition is not carrying it"
for f in is_mask_low parity bit nibble_ones clamp_width clamp_index; do
  grep -q "verification failed for \`trust_bits::$f\`" "$LOG" \
    && fail "mutation B: $f was refuted by an is_power_of_two-only break — the tier-1 bounds are not independent"
done
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 5. MUTATION C — the underflow guard deleted.
#    `raw_is_power_of_two`'s `if x == 0` is what makes `x - 1` total. Unlike
#    most `u32` arithmetic in this tree (§4.7 warns that a `u32` defect is
#    usually only UNKNOWN), this one is genuinely REFUTED — measured, the
#    Summary reports `2 failed` — because `x == 0` is a counterexample the
#    engine can exhibit. Both halves of the attribution are asserted: the
#    helper's own rows fail, AND the caller stops being able to bundle it.
# ---------------------------------------------------------------------------
mutate '    if x == 0 {
        return 0;
    }
    if x & (x - 1) == 0 {' '    if x & (x - 1) == 0 {'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an unguarded x - 1 still passed  $G"; else echo "  ok   mutation C (raw_is_power_of_two's x == 0 guard deleted)  rc=$RC  $G"; fi
grep -qE 'Summary: [0-9]+ proved, [1-9][0-9]* failed' "$LOG" \
  || fail "mutation C: no row went FAILED — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
grep -q 'verification failed for `trust_bits::raw_is_power_of_two`' "$LOG" \
  || fail "mutation C: raw_is_power_of_two did not lose a row"
grep -q 'refused Assert-bearing member `trust_bits::raw_is_power_of_two`' "$LOG" \
  || fail "mutation C: the unproven helper was still bundled by its caller"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 6. MUTATION D — the ENTRY-PREFIX BUNDLING RULE, and its ATTRIBUTION.
#    `sum8`'s arithmetic Assert sits at its entry prefix, which is why every
#    counting function in the crate can bundle it. Putting any CALL before that
#    Assert must make each of those callers fail to lower (§9.1).
#
#    Note what is asserted and what is NOT. There is no
#    `verification failed for `trust_bits::sum8`` line in this run at all —
#    `sum8` still proves its own 14 rows, and the six functions that bundle it
#    are what go INCONCLUSIVE. Asserting the mutated function's own name here
#    would be the §11.5 mistake; the gate asserts its ABSENCE instead, so a
#    change in the attribution direction is a red gate.
# ---------------------------------------------------------------------------
mutate 'fn sum8(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u32 {
    (b0 as u32)' 'fn sum8(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u32 {
    let _p: u32 = weight(b0 as u32);
    (b0 as u32)'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation D: an Assert behind a CALL bundled — §9.1 is stale and must be re-measured  $G"; else echo "  ok   mutation D (weight() call folded into sum8's entry prefix)  rc=$RC  $G"; fi
grep -q 'member has a guarded or non-entry-prefix Assert' "$LOG" \
  || fail "mutation D: the bundle did not refuse a non-entry-prefix Assert — $(grep -oE 'native TrustIr bundle for .*' "$LOG" | head -1)"
grep -q 'refused Assert-bearing member `trust_bits::sum8`' "$LOG" \
  || fail "mutation D: sum8 was not the refused member"
grep -q 'verification failed for `trust_bits::ones_u32`' "$LOG" \
  || fail "mutation D: the refusal was not raised against a CALLER"
grep -q 'verification failed for `trust_bits::sum8`' "$LOG" \
  && fail "mutation D: the mutated function was named directly — §11.5's attribution direction changed and this gate's note is stale"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 7. MUTATION E — the NINE-TERM SUM WALL (§12.1).
#    This is the boundary this crate measured and the reason its population
#    count is four groups of eight rather than one 32-term sum: a chain of
#    widened `u8 -> u32` additions proves for at most NINE terms, and every add
#    past the eighth is RUNTIME-CHECKED with an UNKNOWN hardened twin. Widening
#    `sum4` from four terms to ten must produce exactly that — 16 proved (the
#    eight adds that fit), 1 runtime-checked and 1 unknown (the ninth) — and
#    nothing about the peak explains it: 10 * 255 == 2550, four million times
#    inside `u32::MAX`.
#
#    If this ever proves 18/18, §12.1 is stale, the whole grouping structure of
#    this crate is unnecessary, and this gate says so rather than the map entry
#    going quietly wrong.
# ---------------------------------------------------------------------------
mutate '    (b0 as u32) + (b1 as u32) + (b2 as u32) + (b3 as u32)
}' '    (b0 as u32) + (b1 as u32) + (b2 as u32) + (b3 as u32) + (b0 as u32) + (b1 as u32)
        + (b2 as u32) + (b3 as u32) + (b0 as u32) + (b1 as u32)
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation E: a TEN-term widened sum PROVED — §12.1 is stale; re-measure the wall and simplify this crate  $G"; else echo "  ok   mutation E (sum4 widened from 4 terms to 10)  rc=$RC  $G"; fi
grep -qE 'trust_bits::sum4 \[INCONCLUSIVE\] \(18 obligations: 16 proved, 1 runtime-checked, 0 failed, 1 unknown' "$LOG" \
  || fail "mutation E: the wall did not land at the ninth add — $(grep -oE 'trust_bits::sum4 \[[A-Z]+\] \([^;]*' "$LOG" | head -1)"
grep -q 'refused Assert-bearing member `trust_bits::sum4`' "$LOG" \
  || fail "mutation E: sum4's unproven rows did not stop it being bundled"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 8. MUTATION F — `/` IS OPAQUE TO BUNDLING (§2.4, §7.2), at a new site.
#    `field` divides, so no verified function in this crate may call it — which
#    is why there is no `field_at_index` convenience wrapper and why `field`
#    inlines its own weight lookups. Making `select_u8` call it must fail to
#    lower. If it ever succeeds, the tier-2 shape of `field`/`deposit` is
#    unnecessary and a composition API becomes available.
# ---------------------------------------------------------------------------
mutate '    if rank_u8(b, 1) > n {' '    if field(b as u32, 0, 1) > n {'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation F: a caller of a '/'-bearing callee lowered — §2.4/§7.2 is stale  $G"; else echo "  ok   mutation F (select_u8 made to call the dividing 'field')  rc=$RC  $G"; fi
grep -q 'refused Assert-bearing member `trust_bits::field`' "$LOG" \
  || fail "mutation F: field was not the refused member — $(grep -oE 'refused Assert-bearing member .*' "$LOG" | head -1)"
grep -q 'verification failed for `trust_bits::select_u8`' "$LOG" \
  || fail "mutation F: the refusal was not raised against the caller"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 9. MUTATION G — the WIDENING deleted in `deposit`.
#    `((value & m) as u64) * (d as u64)` is what makes the field placement
#    overflow-free; `((value & m) * d) as u64` is the same value on every input
#    that fits and a `u32` multiply that wraps on every input that does not.
#    Per §4.7 a `u32` defect is fail-closed as UNKNOWN rather than FAILED, which
#    is what must be asserted; never `[FAILED]` on `u32` arithmetic.
# ---------------------------------------------------------------------------
mutate '    let placed: u64 = ((value & m) as u64) * (d as u64);' \
       '    let placed: u64 = ((value & m) * d) as u64;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation G: an unwidened field placement still passed  $G"; else echo "  ok   mutation G (deposit multiplies at u32 before widening)  rc=$RC  $G"; fi
grep -qE '\[(FAILED|UNKNOWN)\] \[overflow:mul\]|arithmetic overflow \(Mul\) (FAILED|UNKNOWN|RUNTIME CHECKED)' "$LOG" \
  || fail "mutation G: no mul row went FAILED, UNKNOWN or RUNTIME CHECKED — $(grep -oE 'arithmetic overflow \([A-Za-z]+\) [A-Z ]+' "$LOG" | head -3 | tr '\n' ' ')"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 10. MUTATION J — PINNING DOES NOT COMPOSE THROUGH A CALL (§12.4).
#    `raw_bit` spells its two constants out instead of delegating to `bit_set`,
#    which returns exactly the same two constants from a body that pins them.
#    That one extra statement is the difference between `bit`'s clause
#    discharging and not — it cost this crate its only failing row on first
#    submission. Restoring the delegating form must refute.
# ---------------------------------------------------------------------------
mutate '    if x & weight(k) == 0 {
        return 0;
    }
    1
}

// ---' '    bit_set(x, weight(k))
}

// ---'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation J: a bare-call helper PINNED its return — §12.4 is stale and raw_bit can be simplified  $G"; else echo "  ok   mutation J (raw_bit delegates instead of pinning)  rc=$RC  $G"; fi
grep -qE 'trust_bits::bit \[INCONCLUSIVE\] \(2 obligations: 0 proved, 0 runtime-checked, 0 failed, 2 unknown' "$LOG" \
  || fail "mutation J: bit did not go UNKNOWN x2 — $(grep -oE 'trust_bits::bit \[[A-Z]+\] \([^;]*' "$LOG" | head -1)"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 11. MUTATION K — A GUARD MUST BE AN INEQUALITY (§12.3).
#    `raw_is_mask_low`'s `if x > 4294967294` and `if x == 4294967295` select the
#    SAME single value. Only the first supplies the interval engine a bound on
#    the fall-through path, so only the first discharges the `x + 1` below it.
#    Nothing else in the body changes. Pinned here so that if the engine ever
#    learns the equality form, this goes red rather than the map entry going
#    stale.
# ---------------------------------------------------------------------------
mutate '    if x > 4294967294 {
        return 1;
    }
    let y: u32 = x + 1;' '    if x == 4294967295 {
        return 1;
    }
    let y: u32 = x + 1;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation K: an EQUALITY guard bounded the add — §12.3 is stale, respell the guard  $G"; else echo "  ok   mutation K (x > 4294967294 respelled as x == 4294967295)  rc=$RC  $G"; fi
grep -qE 'trust_bits::raw_is_mask_low \[INCONCLUSIVE\] \(2 obligations: 0 proved, 0 runtime-checked, 0 failed, 2 unknown' "$LOG" \
  || fail "mutation K: raw_is_mask_low did not go UNKNOWN x2 — $(grep -oE 'trust_bits::raw_is_mask_low \[[A-Z]+\] \([^;]*' "$LOG" | head -1)"
grep -q 'verification failed for `trust_bits::is_mask_low`' "$LOG" \
  || fail "mutation K: the refusal was not raised against the caller"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 12. MUTATION L — the PEAK, recomputed for THIS crate and not transplanted.
#    `deposit`'s `(m as u64) * (d as u64)` is this crate's only tight peak, and
#    the arithmetic that looks obvious is WRONG: computing it from the TYPES
#    gives `(2^32-1)^2` and a slack of 8589934590, and BOTH `+ 8589934590` and
#    `+ 8589934591` were measured to PASS. The engine's real peak is
#    `(2^32-1) * 2^31 == 9223372034707292160`, because it reads `d <= 2^31`
#    from `weight`'s BUNDLED constant-returning chain rather than from `u32`
#    (§12.2). The exact boundary was then measured in adjacent runs:
#
#      + 9223372039002259455  (peak exactly u64::MAX)  -> 6/6 PROVED
#      + 9223372039002259456  (one past it)            -> 4 proved, 2 UNKNOWN
#
#    A coefficient copied from another crate's gate would have been a silently
#    dead control that never fired, twice over.
# ---------------------------------------------------------------------------
mutate '    let hole: u64 = (m as u64) * (d as u64);' \
       '    let hole: u64 = (m as u64) * (d as u64) + 9223372039002259456;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation L: one past the measured peak still proved — §12.2's range source is stale  $G"; else echo "  ok   mutation L (deposit peak + 9223372039002259456, one past u64::MAX)  rc=$RC  $G"; fi
grep -qE 'trust_bits::deposit \[INCONCLUSIVE\] \(6 obligations: 4 proved, 0 runtime-checked, 0 failed, 2 unknown' "$LOG" \
  || fail "mutation L: deposit did not lose exactly the add row and its twin — $(grep -oE 'trust_bits::deposit \[[A-Z]+\] \([^;]*' "$LOG" | head -1)"
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 13. THE TESTS, AND THE TWO MUTATIONS THEY ALONE CAN CATCH.
# ---------------------------------------------------------------------------
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)  $(grep -oE '^test result: .*' "$LOG" | head -1)"; else
  grep -qE '^test result: ok\. 17 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 17 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  echo "  ok   tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# --- MUTATION H — wrong value, the KIND SPLIT CANNOT SEE IT -----------------
mutate '    (b0 as u32) * 128
        + (b1 as u32) * 64' '    (b0 as u32) * 64
        + (b1 as u32) * 128'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation H: the strict lane REFUTED a swapped coefficient (rc=$VRC $VG) — welcome news, but this gate's claim that no obligation can see which bit got which weight is now stale and must be re-measured"
else
  grep -qE 'Summary: 114 proved, 0 failed, .*0 inconclusive \(114 total\)' "$LOG" \
    || fail "mutation H: the row count moved — the demonstration needs the split to be IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(kinds)" = "$PRISTINE_KINDS" ] \
    || fail "mutation H: the kind split moved under a wrong-value mutation"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation H: a swapped bit weight passed the unit tests"; else
  echo "  ok   mutation H (rev8 swaps the 128 and 64 weights; the coefficient MULTISET, so the peak, is unchanged)  tests rc=$RC, strict lane rc=$VRC"
fi
# Assert WHICH tests fail, by name. A bare rc would be satisfied by a broken
# doctest stage or a compile error, and the control would silently stop testing.
grep -q 'reverse_agrees_with_core_reverse_bits ... FAILED' "$LOG" \
  || fail "mutation H: the core::reverse_bits oracle did not catch a swapped bit weight"
# Everything that is not about bit ORDER must still PASS — otherwise the
# demonstration degrades into "the mutation broke everything".
for t in ones_agrees_with_count_ones \
         rank_and_select_are_inverse_on_every_byte \
         the_byte_and_word_zero_runs_are_two_independent_chains \
         every_tier1_bound_holds_and_every_clamp_can_fire; do
  grep -q "$t ... ok" "$LOG" \
    || fail "mutation H: $t also went red — H no longer isolates 'a wrong answer at exit 0'"
done
# ...and the CROSS-WIDTH test CANNOT catch it, because both of its sides call
# the mutated `rev8`. Asserted, not merely noted: a test that derives its
# expectation from the code under test is not a test, and this is the in-tree
# demonstration. Measured 2026-08-29 — this assertion was written the other way
# round first, and the gate went red saying so.
grep -q 'the_byte_and_word_lanes_agree_consistency_only ... ok' "$LOG" \
  || fail "mutation H: the consistency test now catches this too — it did not when written, and the gate's demonstration of oracle-derivation is stale"
rm -f "$LOG"; restore

# --- MUTATION I — wrong value, TIER-1 POSTCONDITION SURVIVES ----------------
mutate '    if b < 16 {
        return 4;
    }' '    if b < 16 {
        return 3;
    }'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation I: the strict lane REFUTED a wrong leading-zero count (rc=$VRC $VG) — welcome news, but the returned value is still inside 'ensures result <= 8' and this must be re-measured"
else
  grep -qE 'Summary: 114 proved, 0 failed, .*0 inconclusive \(114 total\)' "$LOG" \
    || fail "mutation I: the row count moved — an in-bound constant change must leave the split IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(kinds)" = "$PRISTINE_KINDS" ] \
    || fail "mutation I: the kind split moved under a wrong-value mutation"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation I: a wrong leading-zero count passed the unit tests"; else
  echo "  ok   mutation I (leading_zeros_u8 returns 3 for b in 16..=31; 'ensures result <= 8' still TRUE)  tests rc=$RC, strict lane rc=$VRC"
fi
for t in zero_runs_agree_with_core \
         the_byte_and_word_zero_runs_are_two_independent_chains; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation I: $t did not catch a wrong leading-zero count"
done
# The tier-1 BOUND test must still PASS: the mutated value is inside the clause,
# which is the entire point of this control.
grep -q 'every_tier1_bound_holds_and_every_clamp_can_fire ... ok' "$LOG" \
  || fail "mutation I: the tier-1 bound test also went red — I no longer isolates 'proved contract over a wrong answer'"
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — the"
  echo "        clause is 'result <= 8' and 3 is inside it, so all nine of"
  echo "        leading_zeros_u8's postcondition rows still discharge.)"
fi
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 14. The restore actually restored. A gate that leaves a mutation behind turns
#     the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
