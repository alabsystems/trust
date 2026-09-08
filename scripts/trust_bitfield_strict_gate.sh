#!/usr/bin/env bash
# trust_bitfield_strict_gate.sh — pin `crates/trust-bitfield` at a NON-VACUOUS
# pass of the authenticated strict lane, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS GATE IS DIFFERENT FROM THE OTHER FOURTEEN
# --------------------------------------------------
# `trust-bitfield` is the FIRST Trust component that DEPENDS on another verified
# Trust crate. Until 850147d402 that edge was verdict-NEGATIVE — a one-line
# passthrough to `trust_bits::clamp_index` took a crate from `PASS 2 proved` to
# `FAIL 0 proved / 1 unknown`, the sole row being
# `[trust-absent-callee-assumption] call to absent callee ... may panic`. The
# fourteen strict-lane crates were fourteen isolated leaves for exactly that
# reason.
#
# So this gate asserts, on top of everything the other fourteen assert:
#
#   * that `trust-absent-callee-assumption` occurs ZERO times (section 1);
#   * that the `trust-bits` unit is in the report's dependency trust base, i.e.
#     the edge is in the proof graph and not merely in the manifest (section 1);
#   * that DELETING the dependency breaks the BUILD (mutation H) — the edge is
#     load-bearing, not decorative;
#   * and that the three cross-crate boundaries §15 of
#     `docs/STRICT_VERIFICATION_FRAGMENT.md` records are still where §15 says
#     they are (mutations C, D and E). Those three are the reason this file
#     exists: a measured boundary with no live assertion goes STALE SILENTLY,
#     and §10.1 set the precedent — its pin fired correctly the week §13.1 was
#     fixed. If the compiler closes any of the three, this gate goes RED and
#     names the section to correct.
#
# Measured 2026-08-30 against stage1 driver `de5b5cd009ba47efe` (shasum read
# before the first run and again after the last — unchanged), from a tree at
# 850147d402, under BOTH the default `unix_hardened` policy and
# `-Ztrust-policy=certify`, byte-identically:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 41 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive (41 total)
#   Coverage: 26/26 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=3, arithmetic_overflow_mul=3,
#                   arithmetic_overflow_sub=1, division_by_zero=1,
#                   hardened_panic_boundary=9, postcondition=23,
#                   remainder_by_zero=1
#
# THE CONTROL THAT MAKES THE PASS MEAN SOMETHING
# ----------------------------------------------
# An INLINE TWIN — the same 26 bodies with the five `trust-bits` functions
# copied in verbatim and every `trust_bits::` prefix deleted — was measured in
# the same session and reports `41 proved / 0 failed`, the SAME kind split, at
# `Coverage: 31/31` (the five copied guard chains report `[NO OBLIGATIONS]`).
# The composition penalty on this crate's bodies is therefore measured ZERO,
# and the pass above is not a smaller claim than a self-contained crate's.
#
# Usage:  scripts/trust_bitfield_strict_gate.sh   (~12 verified runs + 4 test runs)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-bitfield/src/lib.rs"
MANIFEST="$REPO_ROOT/crates/trust-bitfield/Cargo.toml"
# Trust: `build/host` is a symlink to `build/<host-triple>`, so this resolves on
# every platform. It used to name `aarch64-apple-darwin` literally, which meant
# that on any non-Apple host this gate could only ever print
#   REFUSE: no targo at .../build/aarch64-apple-darwin/stage1/bin/targo
# and exit 2 — measured 2026-08-31 on aarch64-unknown-linux-gnu, where that
# directory does not exist at all, for all 19 strict gates at once. A soundness
# gate that cannot run on the host it is invoked from is not a strict gate.
TARGO="${TARGO:-$REPO_ROOT/build/host/stage1/bin/targo}"

[ -x "$TARGO" ] || { echo "REFUSE: no targo at $TARGO (set TARGO=...)"; exit 2; }
# The ONLY discriminator that has held under every measurement. A stage whose
# targo was never rebuilt ships upstream cargo under the name `targo`, verifies
# NOTHING, and succeeds. `targo trust --help` is NOT a discriminator: cargo
# resolves the unknown subcommand to the real `targo-trust` beside it.
"$TARGO" --unverified --version >/dev/null 2>&1 \
  || { echo "REFUSE: $TARGO rejects --unverified — it is cargo-in-disguise, not targo"; exit 2; }
[ -x "$(dirname "$TARGO")/trustc" ] \
  || { echo "REFUSE: no sibling trustc beside $TARGO — the stage1 sysroot is not assembled"; exit 2; }

BACKUP="$(mktemp)"; cp "$SRC" "$BACKUP"
MBACKUP="$(mktemp)"; cp "$MANIFEST" "$MBACKUP"
PRISTINE_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
PRISTINE_MSHA="$(shasum -a 256 "$MANIFEST" | cut -d' ' -f1)"
restore() { cp "$BACKUP" "$SRC"; cp "$MBACKUP" "$MANIFEST"; }
trap 'restore; rm -f "$BACKUP" "$MBACKUP"' EXIT INT TERM

fails=0
LOG=""

# ---------------------------------------------------------------------------
# G1. AN ENVIRONMENT FAILURE IS NOT A RESULT, AND IT SATISFIES EVERY
#     PRESENCE-ONLY ASSERTION.
#
# A transient `trustd` outage refuses EVERY obligation BEFORE solver dispatch:
# each row becomes `UnsupportedMir/MemoryAdmission` with outcome `unknown`, and
# the run emits a nonzero rc, `Gate: FAIL`, and one `verification failed for
# `<crate>::<fn>`` line for every function. That is a byte-perfect imitation of
# "the mutation refuted exactly what it was supposed to refute", INCLUDING the
# specificity checks. An outage therefore ABORTS as INCONCLUSIVE (exit 3); it is
# never scored as a pass and never as a refutation. (§9.6.)
env_broken() {
  grep -qE 'MemoryAdmission|memory admission failed|could not connect to selected endpoint|Connection refused' "$LOG"
}
require_env() { # require_env <label>
  if env_broken; then
    echo "  ENV  $1: trustd memory admission was unavailable — every obligation was"
    echo "       refused BEFORE solver dispatch, so this run is not a fact about the"
    echo "       crate under test. Refusing to score it as a pass OR as a refutation."
    ENVD="$(grep -oE 'could not connect to selected endpoint [^\"]*' "$LOG" | head -1)"
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
# rustc diagnostic without colliding with the bundling refusals that mutations
# C and D are SUPPOSED to provoke.
no_rustc_error() { # no_rustc_error <label>
  if grep -qE '^error\[E[0-9]{4}\]' "$LOG"; then
    fail "$1: rustc reported $(grep -oE '^error\[E[0-9]{4}\]' "$LOG" | head -1) — this run is supposed to exercise the PROOF, not the BUILD; obligations for code that did not lower are ABSENT, not refuted"
  fi
  return 0
}

fail() { echo "  FAIL $*"; fails=$((fails+1)); }

run() { # run [policy]; sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-bitfield ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-run}"
  no_rustc_error "${STEP:-run}"
}
# The BUILD-breaking mutation (H) must not be run through `no_rustc_error`,
# whose whole job is to refuse the state H creates on purpose.
run_raw() {
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" trust check -p trust-bitfield ) > "$LOG" 2>&1
  RC=$?
}
# `--lib` is load-bearing. A concurrent `x.py check` can rebuild
# `librustc_driver-<hash>.dylib` while stage1 `trustdoc` still references the old
# hash; the doctest stage then dies with SIGABRT and a bare `targo test` exits
# 101 with every unit test passing. That turned `trust-utf`'s gate red while its
# strict lane was green — and, worse, it DISARMS a wrong-value control, whose
# whole assertion is "the tests go red" when they were already red for an
# unrelated reason. This crate has no doctests (its examples are ```text).
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-bitfield --lib ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-tests}"
}
gate_line() { grep -oE 'Gate: [A-Z]+ \[strict lane, exit [0-9]+\]' "$LOG" | tail -1; }

# ---------------------------------------------------------------------------
# G2. `ok` MUST MEAN "THIS SECTION'S OWN CONTENT ASSERTIONS HELD".
#
# Every ok-print is QUEUED and flushed at the END of its section, once every
# assertion in it has had its chance to move `fails`. If anything in a section
# failed, NONE of its ok lines are printed as evidence.
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

# `mutate <file> <old> <new>` — refuses if the anchor is not unique, so a source
# edit that moves a mutation out from under this gate is a loud failure, never a
# silently-skipped control.
mutate() {
  python3 - "$1" "$2" "$3" <<'PY' || exit 3
import sys
p, old, new = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(p).read()
if s.count(old) != 1:
    sys.exit(f"anchor matched {s.count(old)} times, expected 1:\n{old}")
open(p, "w").write(s.replace(old, new))
PY
}

echo "trust-bitfield strict gate:"

# ---------------------------------------------------------------------------
# 1. THE PASS — asserted on exit code, Gate, compile status, coverage, the kind
#    split, AND the two facts that are specific to a COMPOSED crate.
# ---------------------------------------------------------------------------
STEP="THE PASS"; mut_begin
run
G="$(gate_line)"
# §9.2: a crate can verify completely and fail to SEAL, and that failure prints
# no `Gate:` line, no `Summary:` and no diagnostic at all. Assert presence first.
[ -n "$G" ] || fail "pristine: no Gate: line — the report did not seal (§9.2), so nothing below is readable"
[ "$RC" -eq 0 ] || fail "pristine: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "pristine: Gate is '$G'";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 26/26 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 26/26 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 41 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(41 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `VcKind::Unreachable`'s formula is literally `Bool(true)`; an
# audit once found 53% of published proofs were exactly that.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=3 arithmetic_overflow_mul=3 arithmetic_overflow_sub=1 \
            division_by_zero=1 hardened_panic_boundary=9 postcondition=23 remainder_by_zero=1; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
# --- THE COMPOSITION ASSERTIONS ---------------------------------------------
# (a) The row that used to be this crate's ENTIRE obligation content.
N_ABSENT="$(grep -c 'trust-absent-callee-assumption' "$LOG")"
[ "$N_ABSENT" -eq 0 ] \
  || fail "pristine: $N_ABSENT trust-absent-callee-assumption row(s) — the foreign bundling lane is shut, and this crate's calls into trust-bits are being fail-closed rather than verified"
# (b) The edge is in the PROOF GRAPH, not merely in the manifest. If this line
#     disappears, the dependency stopped being compiled as part of the session
#     and the pass above is about a different program.
grep -q 'package="trust-bits"' "$LOG" \
  || fail "pristine: the trust-bits unit does not appear in the report's dependency trust base — the edge is not in the proof graph"
# (c) The pristine ABSENCE of the diagnostics mutations C and D are asserted to
#     produce. Without this, those two mutations cannot distinguish "the
#     boundary is still there" from "that string is always present".
for absent in 'refused Assert-bearing member' 'trust_bits::deposit' 'counterexample:' 'UnmodeledCalleeReturn'; do
  grep -q "$absent" "$LOG" \
    && fail "pristine: '$absent' is ALREADY present — the mutation that asserts it cannot discriminate"
done
mut_ok "pristine  $G  [9 safety + 9 hardened-twin + 23 postcondition, 0 unreachable, 0 absent-callee]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 2. THE SAME PASS UNDER `-Ztrust-policy=certify`.
#    A misspelled TRUSTFLAGS is silently dropped, so first prove the flag path
#    reaches the compiler by requiring a bogus policy to be REJECTED BY NAME.
#    Without this control, "certify passed" is indistinguishable from "certify
#    never ran".
# ---------------------------------------------------------------------------
STEP="CERTIFY"; mut_begin
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
grep -qE 'Publication boundary: [0-9]+ obligation\(s\) passed the compiler, 41 published, [0-9]+ WITHHELD .*\(0 relabelled unknown' "$LOG" \
  || fail "certify: a favorable compiler row was RELABELLED at the publication boundary — $(grep -oE '^Publication boundary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G  [0 relabelled at the publication boundary]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — a tier-1 postcondition made FALSE.
#    `fit_width` returns `width` unclamped, so `ensures result <= room` is false
#    at `width > room`. It must be REFUTED, and — the other half of the control
#    — the other eight contracted functions must NOT be, or this run went red
#    for an unrelated reason and says nothing about `fit_width`.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate "$SRC" 'pub fn fit_width(width: u32, room: u32) -> u32 ensures result <= width ensures result <= room {
    if width > room {
        return room;
    }
    width
}' 'pub fn fit_width(width: u32, room: u32) -> u32 ensures result <= width ensures result <= room {
    width
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a FALSE postcondition still passed  $G"; else mut_ok "mutation A (fit_width returns width unclamped)  rc=$RC  $G"; fi
grep -q "verification failed for \`trust_bitfield::fit_width\`" "$LOG" \
  || fail "mutation A: fit_width was NOT refuted"
for f in clamp_to_mask hull_lo hull_end next_lo clamp_word_index field_fits value_fits mask_is_field fields_overlap; do
  grep -q "verification failed for \`trust_bitfield::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a fit_width-only break — it does not depend on fit_width, so this run went red for an unrelated reason and is not evidence"
done
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — a tier-2 SAFETY obligation made false: `extract` loses its
#    zero-divisor guard. `raw_field_fits(32, 0)` is 1 and `weight(32)` is 0, so
#    a zero divisor is REACHABLE and this is a refutation, not a coverage gap.
#
#    THE ROW IS NOT LABELLED `[divzero]`, AND THE FIRST VERSION OF THIS GATE
#    ASSERTED THAT IT WAS. Measured: the unfavorable row is
#    `[hardened_panic_boundary] ... mir_assert::DivisionByZero ... FAILED`, with
#    an explicit `counterexample: ... d = 0, lo = 0, width = 0, x = 0`, while the
#    `division_by_zero` row itself is not emitted at all — a
#    `[spine:unchecked-obligation]` row says trust-vcgen never minted it. So a
#    gate keyed on the label reads a REFUTED division as "no row at all". Assert
#    the counterexample instead: a coverage gap cannot produce one.
#
#    §4.7 also rules out asserting `[FAILED]` on its own (an unattested CHC
#    refutation is deliberately demoted to `unknown`), and asserting merely "not
#    proved" would pass on exactly the coverage gap this exists to exclude. The
#    three facts below separate them, and all three are asserted ABSENT from the
#    pristine run in section 1.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate "$SRC" '    let m: u32 = trust_bits::weight(width);
    if d == 0 {
        return 0;
    }
    let q: u32 = x / d;' '    let m: u32 = trust_bits::weight(width);
    let q: u32 = x / d;'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an unguarded division still passed  $G"; else mut_ok "mutation B (extract loses its d==0 guard)  rc=$RC  $G"; fi
# (a) an unfavorable row for the division exists at all — a coverage gap emits none
grep -qE '^\s*\[hardened_panic_boundary\].*mir_assert::DivisionByZero.*FAILED' "$LOG" \
  || fail "mutation B: no FAILED mir_assert::DivisionByZero row — the obligation was not even emitted, so the gate saw a coverage gap rather than a refutation"
# (b) a real WITNESS, which is what a coverage gap structurally cannot produce
grep -qE 'counterexample:.*\bd = 0\b' "$LOG" \
  || fail "mutation B: the refutation carries no counterexample naming d = 0 — $(grep -oE 'counterexample:.*' "$LOG" | head -1)"
# (c) the crate Summary counts it as FAILED rather than merely inconclusive
grep -qE 'Summary: [0-9]+ proved, 1 failed,' "$LOG" \
  || fail "mutation B: the Summary does not report exactly 1 failed — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# (d) §15.1's characterisation of `UnmodeledCalleeReturn`, pinned. The pristine
#     run has ZERO of these; deleting the guard on the FOREIGN value `d` mints
#     them. That is the whole content of §15.1: the row is not a general ceiling
#     on consuming a foreign return, it fires exactly where the obligation's
#     truth depends on a foreign value the caller's own body does not constrain.
grep -q "UnmodeledCalleeReturn.*unmodelled call (\`d\`)" "$LOG" \
  || fail "mutation B: no UnmodeledCalleeReturn row naming the foreign value \`d\`. If the compiler now constrains a foreign return value, that is welcome news and §15.1 must be re-measured and rewritten — do not delete this assertion."
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — §15.2, THE CONTRACT BOUNDARY.
#    `next_lo`'s clamp is spelled LOCALLY even though `trust_bits::clamp_width`
#    carries the byte-identical `ensures result <= 32`. §15.2 measures that a
#    shape-(B) wrapper over a FOREIGN contracted callee does NOT discharge:
#    0 proved / 2 unknown, against the local twin's 1 proved. This mutation
#    makes that substitution and asserts the failure is still there.
#
#    IF THIS MUTATION EVER PASSES, THE COMPILER CLOSED THE BOUNDARY. That is
#    good news and it makes §15.2 WRONG — correct the section, do not delete
#    this control.
# ---------------------------------------------------------------------------
STEP="MUTATION C (§15.2)"; mut_begin
mutate "$SRC" '    clamp_word_index(raw_next_lo(lo, width))' '    trust_bits::clamp_width(raw_next_lo(lo, width))'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation C: a shape-(B) wrapper over the FOREIGN contracted callee \`trust_bits::clamp_width\` now DISCHARGES ($G). Welcome news — and §15.2 of docs/STRICT_VERIFICATION_FRAGMENT.md is now stale and must be re-measured and rewritten, not deleted. next_lo's local clamp can then be replaced by the foreign one."
else
  mut_ok "mutation C (§15.2: next_lo's local clamp -> trust_bits::clamp_width)  rc=$RC  $G"
fi
grep -q "verification failed for \`trust_bitfield::next_lo\`" "$LOG" \
  || fail "mutation C: next_lo was not refuted — the failure §15.2 records did not occur, and it did not pass either; re-read the log at $LOG"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION D — §15.3, THE TERMINAL-CALLEE BOUNDARY.
#    `trust_bits::deposit` is the closest function in the tree to `insert` and
#    it is un-callable: a `*`-after-a-call body is TERMINAL, and §15.3 measures
#    that the rule crosses the crate boundary unchanged. That is the entire
#    reason `insert`/`place`/`extract` re-derive their arithmetic here. Assert
#    the refusal BY NAME, and assert the diagnostic names the FOREIGN member —
#    if it ever names only the local caller, the attribution changed and §11.5's
#    reading of these refusals needs re-checking.
# ---------------------------------------------------------------------------
STEP="MUTATION D (§15.3)"; mut_begin
mutate "$SRC" '    let hole: u32 = field_mask(lo, width);
    let placed: u32 = place(value, lo, width);
    (x & !hole) | placed' '    trust_bits::deposit(x, value, lo, width)'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation D: calling the TERMINAL foreign callee \`trust_bits::deposit\` now verifies ($G). Welcome news — §15.3 is stale; re-measure it, and reconsider whether extract/place/insert still need to re-derive their arithmetic."
else
  mut_ok "mutation D (§15.3: insert -> trust_bits::deposit)  rc=$RC  $G"
fi
grep -q 'refused Assert-bearing member `trust_bits::deposit`' "$LOG" \
  || fail "mutation D: the refusal does not name \`trust_bits::deposit\` as the refused member — $(grep -oE 'refused Assert-bearing member [^:]*: [a-zA-Z /-]*' "$LOG" | head -1)"
grep -q 'member has a guarded or non-entry-prefix Assert' "$LOG" \
  || fail "mutation D: the refusal reason is not the non-entry-prefix one §15.3 records"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION E — §15.4, THE RANGE BOUNDARY, BISECTED FOR THIS CRATE.
#
#    §12.2 measured that a bundled constant guard chain is a range source
#    TIGHTER than the type: inside `trust-bits`, `mask_below(w) * weight(lo)`
#    admits an addend of `9223372039002259455` because the engine reads
#    `weight <= 2^31` from the bundled body. §15.4 measures that this does NOT
#    cross the crate boundary — the engine falls back to the TYPE peak
#    `(2^32-1)^2`, whose slack to `u64::MAX` is exactly `8589934590`.
#
#    THE COEFFICIENT BELOW WAS BISECTED AGAINST THIS COMPILER FOR THIS CRATE,
#    not transplanted and not derived. §12.2 is precisely the case where
#    computing the boundary from the types was ALSO wrong, in the other
#    direction. Both sides are asserted, in two runs, because a one-sided
#    assertion cannot tell "the boundary is here" from "everything fails":
#
#      + 8589934590  (type peak exactly u64::MAX) -> PASSES, 41 proved
#      + 8589934591  (one past it)                -> FAILS
#
#    Measured foreign-vs-local in ONE run on 2026-08-30: the local twin proves
#    ALL THREE of 8589934590 / 8589934591 / 9223372039002259455.
# ---------------------------------------------------------------------------
STEP="MUTATION E (§15.4) — at the peak"; mut_begin
mutate "$SRC" '    let hole: u64 = (m as u64) * (d as u64);
    if hole > 4294967295 {
        return 0;
    }
    hole as u32
}' '    let hole: u64 = (m as u64) * (d as u64) + 8589934590;
    if hole > 4294967295 {
        return 0;
    }
    hole as u32
}'
run
G="$(gate_line)"
if [ "$RC" -ne 0 ]; then
  fail "mutation E-lo: an addend of 8589934590 — the TYPE peak exactly at u64::MAX — did NOT prove (rc=$RC $G). The boundary moved DOWN; §15.4's coefficient is stale and E-hi below proves nothing."
else
  mut_ok "mutation E-lo (field_mask hole + 8589934590, type peak exactly u64::MAX)  rc=0  $G"
fi
rm -f "$LOG"; restore

STEP="MUTATION E (§15.4) — one past it"
mutate "$SRC" '    let hole: u64 = (m as u64) * (d as u64);
    if hole > 4294967295 {
        return 0;
    }
    hole as u32
}' '    let hole: u64 = (m as u64) * (d as u64) + 8589934591;
    if hole > 4294967295 {
        return 0;
    }
    hole as u32
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation E-hi: an addend ONE PAST the type peak still proved ($G) — the engine is now reading a range TIGHTER than the type across the crate boundary, i.e. §12.2's chain range composes after all. §15.4 is stale; re-bisect it."
else
  mut_ok "mutation E-hi (field_mask hole + 8589934591, one past the type peak)  rc=$RC  $G"
fi
grep -q "verification failed for \`trust_bitfield::field_mask\`" "$LOG" \
  || fail "mutation E-hi: field_mask was not the refuted subject"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 8. THE TESTS, AND THE TWO MUTATIONS THEY ALONE CAN CATCH.
#    Everything above is a statement about obligations. Mutations F and G change
#    the crate's ANSWERS while leaving every obligation — G's including a
#    DISCHARGED `ensures` — true, so the strict lane accepts both at exit 0 and
#    only the unit tests refuse them.
# ---------------------------------------------------------------------------
STEP="THE TESTS"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then
  fail "pristine: unit tests failed (rc=$RC) — $(grep -oE '^test result: .*' "$LOG" | head -1)"
else
  grep -qE '^test result: ok\. 17 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 17 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"

# MUTATION F — a WRONG ANSWER with every obligation still in range.
# `place` swaps which `trust-bits` lookup gets which argument. The peak is
# unchanged in BOTH factors — `mask_below` still returns at most `2^32-1` and
# `weight` at most `2^31`, they have merely traded places — so every row still
# proves, at exit 0, with a byte-identical kind split, while `place(1, 4, 3)`
# returns 8 instead of 16. This is `trust-endian`'s demonstration in a new
# domain: no obligation this crate has can see which lookup got which number.
STEP="MUTATION F"
mutate "$SRC" '    let d: u32 = trust_bits::weight(lo);
    let m: u32 = trust_bits::mask_below(width);
    if d == 0 {
        return 0;
    }
    let hole: u64 = (m as u64) * (d as u64);
    if hole > 4294967295 {
        return 0;
    }
    // `value & m <= m`' '    let d: u32 = trust_bits::weight(width);
    let m: u32 = trust_bits::mask_below(lo);
    if d == 0 {
        return 0;
    }
    let hole: u64 = (m as u64) * (d as u64);
    if hole > 4294967295 {
        return 0;
    }
    // `value & m <= m`'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation F: the strict lane REFUTED a swap of two lookup arguments (rc=$VRC $VG) — welcome news, but this gate's claim that no obligation can see which lookup got which number is now stale and must be re-measured, not deleted"
fi
case "$VG" in *"PASS [strict lane, exit 0]"*) ;; *) fail "mutation F: Gate is '$VG', expected PASS — the swap was supposed to change no obligation at all";; esac
grep -qE 'Summary: 41 proved, 0 failed, .*0 inconclusive \(41 total\)' "$LOG" \
  || fail "mutation F: the row count moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *arithmetic_overflow_mul=3*) ;; *) fail "mutation F: the multiply rows moved — $KINDS";; esac
rm -f "$LOG"

runtests
if [ "$RC" -eq 0 ]; then
  fail "mutation F: a swapped pair of trust-bits lookups passed the unit tests — the tests are not sensitive to the crate's own subject"
else
  mut_ok "mutation F (place: weight(lo)/mask_below(width) -> weight(width)/mask_below(lo))  tests rc=$RC, strict lane rc=$VRC  $VG"
fi
for t in place_and_extract_are_inverse insert_replaces_exactly_the_field_and_nothing_else pack2_lays_two_fields_end_to_end; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation F: $t did not catch a swapped pair of lookups"
done
# ... and it must NOT degrade into "everything broke", or the red above would
# say nothing about this defect in particular. The tier-1 carrier and the two
# functions the mutation does not touch must stay GREEN.
for t in no_tier1_result_ever_exceeds_its_bound fit_width_is_exactly_min field_mask_agrees_with_a_bit_loop; do
  grep -q "$t ... ok" "$LOG" \
    || fail "mutation F: $t also failed, so this is not a demonstration that a PROVED crate can return a wrong answer"
done
rm -f "$LOG"; restore

# MUTATION G — a WRONG ANSWER under a contract that stays TRUE.
# `fit_width` returns 0 on its clamping arm. BOTH `ensures` clauses remain true
# (`0 <= width` and `0 <= room`), so all 23 postcondition rows still prove, at
# exit 0 — and `fit_width(3, 9)` returns 3 while `fit_width(9, 3)` returns 0
# instead of 3. This is the §14.1 two-sided pin shown to be a bound and not a
# specification: the only wrong implementations a same-direction pair admits are
# the ones that return something too SMALL, and here is one.
STEP="MUTATION G"
mutate "$SRC" '    if width > room {
        return room;
    }
    width
}' '    if width > room {
        return 0;
    }
    width
}'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation G: the strict lane REFUTED a too-small return under a two-sided ensures (rc=$VRC $VG) — welcome news, and §14.1's reading that a same-direction pair admits every too-small implementation is now stale here; re-measure, do not delete"
fi
case "$VG" in *"PASS [strict lane, exit 0]"*) ;; *) fail "mutation G: Gate is '$VG', expected PASS";; esac
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *postcondition=23*) ;; *) fail "mutation G: a postcondition stopped proving, so the contract did NOT stay true — $KINDS";; esac
rm -f "$LOG"

runtests
if [ "$RC" -eq 0 ]; then
  fail "mutation G: a too-small fit_width passed the unit tests"
else
  mut_ok "mutation G (fit_width returns 0 on the clamping arm; both ensures stay TRUE)  tests rc=$RC, strict lane rc=$VRC  $VG"
fi
grep -q "fit_width_is_exactly_min ... FAILED" "$LOG" \
  || fail "mutation G: fit_width_is_exactly_min did not catch a too-small min"
grep -q "no_tier1_result_ever_exceeds_its_bound ... ok" "$LOG" \
  || fail "mutation G: the tier-1 carrier ALSO failed, so this is not a demonstration that a DISCHARGED contract can sit over a wrong answer"
rm -f "$LOG"; restore
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED mutations F and G, as expected —"
  echo "        proofs cover panic-freedom and the stated bounds, not the answer.)"
fi

mut_end
# ---------------------------------------------------------------------------
# 9. MUTATION H — THE DEPENDENCY IS LOAD-BEARING.
#    The single assertion that separates this crate from one that inlined
#    `trust-bits` and kept a decorative `[dependencies]` entry: delete the edge
#    and the crate must not COMPILE. There is nothing to fall back on, because
#    every power of two and every mask in the file is a `trust_bits::` call.
# ---------------------------------------------------------------------------
STEP="MUTATION H"; mut_begin
python3 - "$MANIFEST" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
old = 'trust-bits = { workspace = true }'
assert s.count(old) == 1, f"mutation H no longer applies ({s.count(old)} matches)"
open(p, "w").write(s.replace(old, ""))
PY
[ $? -eq 0 ] || fail "mutation H could not be applied — the manifest moved under the gate"
run_raw
if [ "$RC" -eq 0 ]; then
  fail "mutation H: the crate still built and PASSED with no trust-bits dependency — the edge is DECORATIVE, and every composition claim in this file and in §15 is void"
else
  mut_ok "mutation H (delete trust-bits from the manifest)  rc=$RC"
fi
grep -qE '^error\[E0433\]' "$LOG" \
  || fail "mutation H: the build did not fail with E0433 (unresolved crate) — it failed for some other reason, so this run does not show the edge is load-bearing. $(grep -oE '^error(\[E[0-9]{4}\])?: .*' "$LOG" | head -1)"
N="$(grep -cE '^error\[E0433\]' "$LOG")"
[ "$N" -ge 8 ] \
  || fail "mutation H: only $N unresolved-crate errors — a load-bearing edge should break every call site (expected >= 8)"
mut_ok "          $N call sites went unresolved — the dependency carries the crate"
rm -f "$LOG"; restore

mut_end
# ---------------------------------------------------------------------------
# 10. The restore actually restored — BOTH files. A gate that leaves a mutation
#     behind turns the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
STEP="RESTORE"; mut_begin
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "src was NOT restored ($NOW_SHA != $PRISTINE_SHA)"
NOW_MSHA="$(shasum -a 256 "$MANIFEST" | cut -d' ' -f1)"
[ "$NOW_MSHA" = "$PRISTINE_MSHA" ] || fail "manifest was NOT restored ($NOW_MSHA != $PRISTINE_MSHA)"

mut_end
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
