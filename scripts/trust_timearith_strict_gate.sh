#!/usr/bin/env bash
# trust_timearith_strict_gate.sh — pin `crates/trust-timearith` at a NON-VACUOUS
# pass of the authenticated strict lane, on BOTH policies, with live mutation
# controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# `trust-timearith` is the thirteenth `crates/`-resident component written to
# PASS the authenticated strict lane rather than to be retrofitted onto it.
# Measured 2026-08-29 on stage1 driver `67b7f9b330b75a8f`, identically under the
# default `unix_hardened` policy and under `-Ztrust-policy=certify`:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 127 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
#   Coverage: 51/51 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=15, arithmetic_overflow_mul=18,
#                   arithmetic_overflow_sub=4, division_by_zero=1,
#                   hardened_panic_boundary=53, postcondition=35,
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
#  3. A pass never seen to fail is not evidence. Nine mutations run: seven that
#     must refute, and TWO that must NOT (H and I below).
#  4. `TRUSTFLAGS` is silently dropped if misspelled, so the certify lane can
#     look like it ran when it did not. The flag path is proved by feeding it a
#     bogus policy and requiring the compiler to reject it BY NAME.
#  5. Proofs cover overflow and discharged contracts — NOT whether the answer is
#     right.
#
# THREE MUTATIONS PIN FRAGMENT BOUNDARIES THIS CRATE MEASURED
# -----------------------------------------------------------
# `docs/STRICT_VERIFICATION_FRAGMENT.md` §13 records three boundaries that no
# earlier section predicts. Each is pinned by a mutation here, so that the day
# the compiler learns one, this gate goes RED and says so, rather than the map
# entry going quietly stale (the §10.1 precedent).
#
#   F pins §13.1 — a DIGIT SEPARATOR in an `ensures` literal (`999_999_999`)
#     makes the whole clause `SpecEnsuresUnparseable`. The body is unaffected:
#     the identical separator inside the body proves. Bare decimal digits are
#     the entire literal language of the predicate.
#   G pins §13.5 — a subtraction whose MINUEND is a literal (`1000000000 - r`)
#     does not prove at any width and NO guard repairs it, not even on a bare
#     parameter. `var - var` and `var - CONST` both prove.
#   E pins §13.3 — a guarded subtraction of two MULTIPLY-DERIVED locals leaves
#     its `arithmetic_overflow_sub` row unproven; crossing a call boundary
#     re-supplies the range. This is §11.1 reaching subtraction.
#
# MUTATIONS H AND I ARE THE POINT OF THIS GATE
# --------------------------------------------
# Both are wrong-VALUE changes the strict lane PASSES at exit 0, with the kind
# split BYTE-IDENTICAL to the pristine run.
#
#   H mutates a TIER-1 function. `raw_nanos_field_sum` subtracts 1000000 instead
#     of 1000000000 when folding the carry out, so every nanosecond sum that
#     crosses a second is wrong by 999 milliseconds. `nanos_field_sum`'s
#     `ensures result <= 999999999` stays TRUE — `clamp_nanos` above it squashes
#     the wrong value back into range — so a discharged POSTCONDITION sits over
#     an answer that is wrong for the crate's headline operation. This is
#     exactly the trap the crate header names: a range declaration is not a
#     conservation law. The gate additionally asserts that
#     `every_tier1_bound_holds_and_every_clamp_can_fire` still PASSES under H,
#     so the demonstration cannot degrade into "the mutation broke everything".
#
#   I mutates a TIER-2 unit conversion. `hours_to_secs` multiplies by 360
#     instead of 3600. The peak MOVES DOWN, so the multiply row and its hardened
#     twin still prove and the row count does not move; every hour this crate
#     converts is off by a factor of ten. No obligation in the crate can see a
#     unit factor, which is `trust-endian`'s byte-order demonstration in the
#     time domain.
#
# THE MUTATION COEFFICIENT WAS COMPUTED FOR THIS CRATE, NOT TRANSPLANTED
# ---------------------------------------------------------------------
# `total_nanos`'s engine peak is `4294967295 * C + 4294967295`, i.e.
# `4294967295 * (C + 1)`, and `u64::MAX` is exactly `4294967295 * 4294967297`.
# So the largest coefficient that proves is `4294967296` (peak exactly
# `u64::MAX`) and the first that fails is `4294967297`. Both were measured in
# one run. A transplanted `* 2` — `trust-fixed`'s coefficient — would have been
# `2000000000` here, peak `8589934598589934590`, comfortably inside `u64` and a
# silently dead control. Mutation C uses `4294967297`.
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
#   * `targo trust check` can exit 2 having printed NO `Gate:` line, NO
#     `Summary:`, NO `Coverage:` and NO `error:` — only `could not seal the
#     final compiler rows, …`. The `Gate:` line is asserted PRESENT first.
#
# WHAT THIS GATE DID NOT SEE, and now does (2026-08-29)
# -----------------------------------------------------
# A mutation control that asserts only "function X was REFUSED" is satisfied by
# ANY SUPERSET FAILURE, and one such failure is routine: a transient `trustd`
# outage refuses EVERY obligation in the crate BEFORE solver dispatch, so the
# run emits a nonzero rc, `Gate: FAIL`, and one `verification failed for
# `<crate>::<fn>`` line for every function — a byte-perfect imitation of "the
# mutation refuted exactly what it was supposed to refute". Demonstrated, not
# hypothesised: replaying an archived outage log through the UNREPAIRED
# `trust_ratio` gate printed `ok mutation A` with no FAIL line at all.
#
# Commit deed5041441baf44b90455d633f28b3a41bc5f9b repaired the eleven gates that
# existed then; this one landed after that scope and carried none of it. It now
# has all three parts, verbatim from `scripts/trust_ratio_strict_gate.sh`:
#
#   * `require_env` INSIDE `run`/`runtests`, so every present and future run
#     inherits it and an outage ABORTS the gate as INCONCLUSIVE (exit 3) rather
#     than being scored as a pass OR as a refutation. The old `check_env` was
#     hand-called at two of this file's seventeen run sites.
#   * `no_rustc_error`, keyed on `error[E####]`: a mutation meant to break the
#     PROOF must not have broken the BUILD, because obligations for code that
#     did not lower are ABSENT, not refuted. Trust's own verification failures
#     are bare `error:` lines carrying no code, so this cannot collide with the
#     §9.1 bundling refusals mutations D and E are SUPPOSED to provoke.
#   * a QUEUED `mut_ok`/`mut_end` pair. `ok mutation X` used to print the
#     instant `rc != 0`, BEFORE the assertions that say what was refuted had
#     run; the exit code stayed right but the line a human reads was not
#     evidence. Nothing prints `ok` until its whole section has had its chance
#     to fail.
#
# SPECIFICITY. `require_env` closes the outage class; a complement list closes
# the rest, by naming functions that must stay GREEN in the same run. Mutations
# A, C, F, H and I already had one. B, E and G did not, and their claims were
# bare enough to be satisfied by a general regression — B asserted only that
# `clamp_nanos` was refuted, E and G only that one function went INCONCLUSIVE,
# which is what EVERY function does when the crate stops verifying. Each new
# list is the set of functions that do not reach the mutated one, read off this
# crate's call graph (every call site is a direct, non-generic, same-module
# call, so the graph is exactly the `fn` names appearing in each body):
#   B  clamp_nanos      <- nanos_field_sum, nanos_field_diff   (only these two)
#   E  diff_total_nanos <- nobody                              (a leaf)
#   G  raw_nanos_field_diff <- nanos_field_diff                (only this one)
#
# Usage:  scripts/trust_timearith_strict_gate.sh          (~12 min)
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-timearith/src/lib.rs"
# Trust: `build/host` is a symlink to `build/<host-triple>`, so this resolves on
# every platform. It used to name `aarch64-apple-darwin` literally, which meant
# that on any non-Apple host this gate could only ever print
#   REFUSE: no targo at .../build/aarch64-apple-darwin/stage1/bin/targo
# and exit 2 — measured 2026-08-31 on aarch64-unknown-linux-gnu, where that
# directory does not exist at all, for all 19 strict gates at once. A soundness
# gate that cannot run on the host it is invoked from is not a strict gate.
TARGO="${TARGO:-$REPO_ROOT/build/host/stage1/bin/targo}"

[ -x "$TARGO" ] || { echo "REFUSE: no targo at $TARGO (set TARGO=...)"; exit 2; }
# A stage whose targo was never rebuilt ships upstream cargo under the name
# `targo` and verifies NOTHING while succeeding. `--unverified` is the only
# discriminator that has held under every measurement; `targo trust --help`
# passes on cargo-in-disguise (cargo execs the sibling `targo-trust` binary).
"$TARGO" --unverified --version >/dev/null 2>&1 \
  || { echo "REFUSE: $TARGO rejects --unverified — it is cargo-in-disguise, not targo"; exit 2; }
[ -x "$(dirname "$TARGO")/trustc" ] \
  || { echo "REFUSE: no sibling trustc beside $TARGO — the stage1 sysroot is not assembled"; exit 2; }

# PREFLIGHT: `crates/Cargo.toml` must LOAD. A workspace member listed without a
# manifest — or with a manifest but no `src/lib.rs` yet — makes every `targo
# trust check` in this workspace exit 2 with no `Gate:` line, indistinguishable
# from the seal failure and from a real crate regression. This is not
# hypothetical: it blocked this crate's first measurement while a sibling agent
# was mid-way through adding `trust-bits`.
MISSING_MEMBERS="$(python3 - "$REPO_ROOT/crates" <<'PY'
import os, re, sys
root = sys.argv[1]
s = open(os.path.join(root, "Cargo.toml")).read()
m = re.search(r'^members\s*=\s*\[(.*?)^\]', s, re.S | re.M)
if m:
    for name in re.findall(r'^\s*"([^"]+)",\s*$', m.group(1), re.M):
        d = os.path.join(root, name)
        if not os.path.exists(os.path.join(d, "Cargo.toml")):
            print(f"{name} (no Cargo.toml)")
        elif not any(os.path.exists(os.path.join(d, p))
                     for p in ("src/lib.rs", "src/main.rs")):
            print(f"{name} (manifest with no target)")
PY
)"
[ -z "$MISSING_MEMBERS" ] || {
  echo "REFUSE: crates/Cargo.toml lists member(s) cargo cannot load:"
  echo "$MISSING_MEMBERS" | sed 's/^/          /'
  echo "        Every targo run in this workspace exits 2 with no Gate: line until"
  echo "        that is fixed. This is NOT a trust-timearith result."
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
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-timearith ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-run}"
  no_rustc_error "${STEP:-run}"
}
# `--lib` is load-bearing. Measured 2026-08-29 on `trust-endian`: a concurrent
# `x.py check` rebuilt `librustc_driver-<hash>.dylib`, stage1 `trustdoc` still
# referenced the old hash, and the doctest stage died with SIGABRT — `targo
# test` exited 101 with every unit test passing, on a crate with no doctests.
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-timearith --lib ) > "$LOG" 2>&1
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
# An outage therefore ABORTS the gate as INCONCLUSIVE (exit 3). It is never
# scored as a pass and never scored as a refutation. The previous `check_env`
# recorded a FAIL and continued, which is not the same thing: a red gate says
# "trust-timearith regressed", and that would have been a false statement about
# the crate.
env_broken() {
  grep -qE 'MemoryAdmission|memory admission failed|trust-memory-jobserver\.sock|could not connect to selected endpoint|Connection refused' "$LOG"
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
# rustc diagnostic without colliding with the §9.1 bundling refusals that
# mutations D and E are SUPPOSED to provoke.
no_rustc_error() { # no_rustc_error <label>
  if grep -qE '^error\[E[0-9]{4}\]' "$LOG"; then
    fail "$1: rustc reported $(grep -oE '^error\[E[0-9]{4}\]' "$LOG" | head -1) — this run is supposed to exercise the PROOF, not the BUILD; obligations for code that did not lower are ABSENT, not refuted"
  fi
  return 0
}

# ---------------------------------------------------------------------------
# G2. `ok` MUST MEAN "THIS SECTION'S OWN CONTENT ASSERTIONS HELD".
#
# `ok   mutation X` used to be printed on `[ "$RC" -ne 0 ]` ALONE, so the
# transcript printed `ok` for a plain rustc type error, a missing driver, or an
# unrelated regression. The gate's EXIT CODE stayed right — the greps after each
# `ok` move `fails` separately — but the line a human reads was not evidence.
#
# Every ok-print is therefore QUEUED by `mut_ok` and flushed by `mut_end` at the
# END of the section, once every assertion in that section has had its chance to
# move `fails`. A section may queue more than one line, so the queue is an
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

echo "trust-timearith strict gate:"

# ---------------------------------------------------------------------------
# 1. THE PASS, asserted on exit code, Gate, compile status, coverage AND the
#    kind split — never on the Summary alone, and with the Gate line asserted
#    PRESENT so a seal failure cannot read as a pass.
# ---------------------------------------------------------------------------
STEP="THE PASS"; mut_begin
run
G="$(gate_line)"
[ -n "$G" ] || fail "pristine: no Gate: line — the lane did not run, or the report did not seal (vacuous)"
[ "$RC" -eq 0 ] || fail "pristine: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "pristine: Gate is '$G'";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 51/51 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 51/51 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 127 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(127 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `unreachable` proves nothing; assert it is absent, and assert the
# real safety and functional counts by kind.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
for want in arithmetic_overflow_add=15 arithmetic_overflow_mul=18 \
            arithmetic_overflow_sub=4 division_by_zero=1 \
            hardened_panic_boundary=53 postcondition=35 remainder_by_zero=1; do
  case "$KINDS" in *"$want"*) ;; *) fail "pristine: expected $want in kind split — got: $KINDS";; esac
done
PRISTINE_KINDS="$KINDS"
mut_ok "pristine  $G  [35 postcondition + 39 safety + 53 hardened-twin, 0 unreachable]"
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
#    `nanos_field_carry` has no body of its own beyond a call to
#    `raw_nanos_field_carry`, and inherits `ensures result <= 1` from the fact
#    that the helper returns only 0 or 1 (§9.3's pinned-return rule). Returning
#    2 from the helper must refute the WRAPPER, not merely the helper. If it
#    ever refutes only the helper, the wrapper's bound is being proved by
#    something other than the callee — the shape that lets a wrapper keep a
#    green row after its evidence went away.
#
#    The arithmetic-free tier-1 predicates carry their own bounds and are
#    deliberately NOT touched, so they must stay green in the same run. That
#    makes this a specificity assertion as well as a sensitivity one.
# ---------------------------------------------------------------------------
STEP="mutation A"; mut_begin
mutate 'fn raw_nanos_field_carry(a: u32, b: u32) -> u32 {
    let s: u64 = (a as u64) + (b as u64);
    if s < 1000000000 {
        return 0;
    }
    1
}' 'fn raw_nanos_field_carry(a: u32, b: u32) -> u32 {
    let s: u64 = (a as u64) + (b as u64);
    if s < 1000000000 {
        return 0;
    }
    2
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: a carry helper returning 2 still passed  $G"; else mut_ok "mutation A (raw_nanos_field_carry returns 2)  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_timearith::nanos_field_carry`' "$LOG" \
  || fail "mutation A: nanos_field_carry did not lose its bound — the composition is not carrying it"
for f in is_canonical_nanos fits_secs_field is_zero duration_cmp nonzero_period; do
  grep -q "verification failed for \`trust_timearith::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a carry-only break — the predicate bounds are not independent"
done
rm -f "$LOG"; restore
mut_end

# ---------------------------------------------------------------------------
# 4. MUTATION B — a tier-1 CONTRACT that is simply false.
#    `clamp_nanos` claims `result <= 999999999`. Returning `v` from the arm that
#    exists to clamp it makes the clause false on a reachable path. Distinct
#    from A: there the carrier stopped supplying the bound, here a leaf's own
#    returned value violates its own clause directly.
# ---------------------------------------------------------------------------
STEP="mutation B"; mut_begin
mutate 'pub fn clamp_nanos(v: u32) -> u32 ensures result <= 999999999 {
    if v > 999999999 {
        return 999999999;
    }' 'pub fn clamp_nanos(v: u32) -> u32 ensures result <= 999999999 {
    if v > 999999999 {
        return v;
    }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: a false canonicalization still passed  $G"; else mut_ok "mutation B (clamp_nanos(2000000000) -> 2000000000 against 'ensures result <= 999999999')  rc=$RC  $G"; fi
grep -q 'verification failed for `trust_timearith::clamp_nanos`' "$LOG" \
  || fail "mutation B: clamp_nanos kept its bound while returning a value outside it"
# SPECIFICITY. Refuting `clamp_nanos` is also what a general regression does, so
# name what must stay GREEN. `clamp_nanos` is called by exactly `nanos_field_sum`
# and `nanos_field_diff` (read off the call graph: every call in this crate is a
# direct, non-generic, same-module call, so a function's callees are exactly the
# `fn` names appearing in its body). Nothing below reaches it by any path.
for f in nanos_field_carry nanos_field_borrow total_nanos duration_cmp is_canonical_nanos; do
  grep -q "verification failed for \`trust_timearith::$f\`" "$LOG" \
    && fail "mutation B: $f was refuted by a clamp_nanos-only break — it does not call clamp_nanos, so either this run went red for an unrelated reason (and is not evidence about the clause at all) or the tier-1 bounds are not independent"
done
rm -f "$LOG"; restore
mut_end

# ---------------------------------------------------------------------------
# 5. MUTATION C — the PEAK, at the exact boundary computed for THIS crate.
#    `total_nanos`'s peak is `4294967295 * (C + 1)` and `u64::MAX` is exactly
#    `4294967295 * 4294967297`, so `C = 4294967296` proves (peak exactly
#    `u64::MAX`) and `C = 4294967297` is the first that does not. Measured in
#    one run before this gate was written. Per §4.7 a `u64` overflow is UNKNOWN
#    rather than FAILED, which is fail-closed and is what must be asserted.
#
#    THE ROW THAT FAILS IS THE **ADD**, NOT THE MUL, and this gate asserted the
#    wrong one on its first run. At `C = 4294967297` the multiply's own peak is
#    `4294967295 * 4294967297`, which is exactly `u64::MAX` — so the Mul row
#    still PROVES, and it is `+ (nanos as u64)` that carries the sum past the
#    type. Asserting on the Mul reported a false FAIL against a mutation that
#    had refuted correctly.
# ---------------------------------------------------------------------------
STEP="mutation C"; mut_begin
mutate '    (secs as u64) * 1000000000 + (nanos as u64)
}' '    (secs as u64) * 4294967297 + (nanos as u64)
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: a coefficient one past the computed boundary still passed — the peak is no longer tight, re-measure  $G"; else mut_ok "mutation C (total_nanos coefficient 4294967297, one past the exact boundary)  rc=$RC  $G"; fi
grep -qE 'trust_timearith::total_nanos \[INCONCLUSIVE\]' "$LOG" \
  || fail "mutation C: total_nanos did not lose a row — $(grep -oE 'trust_timearith::total_nanos \[[A-Z]+\] \([^;]*' "$LOG" | head -1)"
grep -qE 'arithmetic overflow \(Add\) (FAILED|UNKNOWN|RUNTIME CHECKED)' "$LOG" \
  || fail "mutation C: no add row went FAILED, UNKNOWN or RUNTIME CHECKED — $(grep -oE 'arithmetic overflow \([A-Za-z]+\) [A-Z ]+' "$LOG" | sort -u | tr '\n' ' ')"
# The Mul must still PROVE. If it ever stops, the coefficient is no longer
# sitting exactly on the boundary and §13.7's arithmetic needs re-deriving.
grep -q 'arithmetic overflow (Mul) PROVED' "$LOG" \
  || fail "mutation C: the Mul row stopped proving — 4294967295 * 4294967297 is exactly u64::MAX, so this coefficient should break the ADD only"
rm -f "$LOG"; restore
mut_end

# ---------------------------------------------------------------------------
# 6. MUTATION D — the ENTRY-PREFIX BUNDLING RULE (§9.1).
#    `raw_nanos_field_sum`'s arithmetic Assert sits at its entry prefix, which
#    is why `nanos_field_sum` can bundle it. Putting any CALL before that Assert
#    must make the caller fail to lower. If the compiler ever admits it, this
#    gate goes red and says so, rather than the map entry going stale.
#
#    NOTE THE ATTRIBUTION (§11.5): the error is raised against the CALLER, not
#    against the function that was mutated, so this gate asserts the
#    `refused Assert-bearing member` note and the caller separately. An
#    assertion of the form `verification failed for <the mutated function>`
#    would be wrong here and would silently never fire.
# ---------------------------------------------------------------------------
STEP="mutation D"; mut_begin
mutate 'fn raw_nanos_field_sum(a: u32, b: u32) -> u32 {
    let s: u64 = (a as u64) + (b as u64);' 'fn raw_nanos_field_sum(a: u32, b: u32) -> u32 {
    let _c: u32 = is_canonical_nanos(a);
    let s: u64 = (a as u64) + (b as u64);'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation D: an Assert behind a CALL bundled — §9.1 is stale and must be re-measured  $G"; else mut_ok "mutation D (is_canonical_nanos call folded into raw_nanos_field_sum)  rc=$RC  $G"; fi
grep -q 'member has a guarded or non-entry-prefix Assert' "$LOG" \
  || fail "mutation D: the bundle did not refuse a non-entry-prefix Assert — $(grep -oE 'native TrustIr bundle for .*' "$LOG" | head -1)"
grep -q 'refused Assert-bearing member `trust_timearith::raw_nanos_field_sum`' "$LOG" \
  || fail "mutation D: raw_nanos_field_sum was not the refused member"
grep -q 'verification failed for `trust_timearith::nanos_field_sum`' "$LOG" \
  || fail "mutation D: the refusal was not raised against the CALLER — the §11.5 attribution direction changed"
rm -f "$LOG"; restore
mut_end

# ---------------------------------------------------------------------------
# 7. MUTATION E — pins §13.3, the MULTIPLY-DERIVED SUBTRACTION.
#    This is the boundary this crate measured and the reason `diff_total_nanos`
#    delegates instead of computing: a guarded subtraction whose operands are
#    MULTIPLY-DERIVED locals leaves its `arithmetic_overflow_sub` row unproven,
#    and crossing a call boundary is what re-supplies the range (§11.1 reaching
#    subtraction). Inlining `sat_sub_u64`'s body into `diff_total_nanos` — same
#    values, same guard, same subtraction, one fewer call — must fail. If it
#    ever passes, §13.3 is stale and the delegation is unnecessary.
# ---------------------------------------------------------------------------
STEP="mutation E"; mut_begin
mutate '    let tb: u64 = (b_secs as u64) * 1000000000 + (b_nanos as u64);
    sat_sub_u64(ta, tb)
}' '    let tb: u64 = (b_secs as u64) * 1000000000 + (b_nanos as u64);
    if ta < tb {
        return 0;
    }
    ta - tb
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation E: a multiply-derived subtraction PROVED — §13.3 is stale; re-measure and simplify this crate  $G"; else mut_ok "mutation E (sat_sub_u64 inlined into diff_total_nanos)  rc=$RC  $G"; fi
grep -qE 'trust_timearith::diff_total_nanos \[INCONCLUSIVE\]' "$LOG" \
  || fail "mutation E: diff_total_nanos did not lose a row — $(grep -oE 'trust_timearith::diff_total_nanos \[[A-Z]+\] \([^;]*' "$LOG" | head -1)"
# SPECIFICITY. "one function went INCONCLUSIVE" is what EVERY function does when
# the crate stops verifying, so name what must stay VERIFIED. `diff_total_nanos`
# is a LEAF of the call graph — no function in this crate calls it — so no other
# row can be downstream of this mutation.
for f in sum_total_nanos total_nanos nanos_field_sum is_canonical_nanos; do
  grep -qE "trust_timearith::$f \[(INCONCLUSIVE|FAILED)\]" "$LOG" \
    && fail "mutation E: $f also stopped verifying — nothing calls diff_total_nanos, so this run is a general regression and says nothing about §13.3"
done
rm -f "$LOG"; restore
mut_end

# ---------------------------------------------------------------------------
# 8. MUTATION F — pins §13.1, the DIGIT SEPARATOR in an `ensures` LITERAL.
#    `ensures result <= 999_999_999` is the same number, written the way Rust
#    style writes it, and it makes the entire clause unparseable. The body is
#    unaffected — the identical separator inside a body proves — so this is a
#    property of the PREDICATE language alone, and it is silent apart from the
#    generic strict-verification error. Every `ensures` literal in this crate is
#    spelled in bare decimal digits because of this measurement; the mutation
#    exists so that the constraint is a live assertion rather than a comment.
# ---------------------------------------------------------------------------
STEP="mutation F"; mut_begin
mutate 'pub fn clamp_nanos(v: u32) -> u32 ensures result <= 999999999 {' \
       'pub fn clamp_nanos(v: u32) -> u32 ensures result <= 999_999_999 {'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation F: a digit-separated ensures literal PARSED — §13.1 is stale; re-measure and the whole map's 'bare decimal only' rule can be relaxed  $G"; else mut_ok "mutation F (ensures literal respelled 999_999_999)  rc=$RC  $G"; fi
grep -q 'SpecEnsuresUnparseable' "$LOG" \
  || fail "mutation F: the clause was not reported unparseable — the failure mode changed"
grep -q 'unsupported contract predicate expression `result <= 999_999_999`' "$LOG" \
  || fail "mutation F: the predicate was not named in the diagnostic"
rm -f "$LOG"; restore
mut_end

# ---------------------------------------------------------------------------
# 9. MUTATION G — pins §13.5, a LITERAL MINUEND.
#    `1000000000 - r` is the textbook way to spell "borrow a second", it is the
#    way this crate was first written, and it does not prove at any width with
#    any guard — including on a bare parameter, which is what makes it a rule
#    about the MINUEND rather than about the operand's provenance. The shipped
#    spelling widens and subtracts variable-from-variable instead.
# ---------------------------------------------------------------------------
STEP="mutation G"; mut_begin
mutate '    let s: u64 = (a as u64) + 1000000000;
    let t: u64 = b as u64;
    if s < t {
        return 0;
    }
    let d: u64 = s - t;
    d as u32
}' '    let r: u32 = b - a;
    if r > 1000000000 {
        return 0;
    }
    1000000000 - r
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation G: a literal minuend PROVED — §13.5 is stale; re-measure, the borrow arm can be spelled the textbook way  $G"; else mut_ok "mutation G (borrow arm respelled 1000000000 - (b - a))  rc=$RC  $G"; fi
grep -qE 'trust_timearith::raw_nanos_field_diff \[INCONCLUSIVE\]' "$LOG" \
  || fail "mutation G: raw_nanos_field_diff did not lose a row — $(grep -oE 'trust_timearith::raw_nanos_field_diff \[[A-Z]+\] \([^;]*' "$LOG" | head -1)"
# SPECIFICITY, as for E. `raw_nanos_field_diff` has exactly one caller,
# `nanos_field_diff`, which is therefore excluded from this list; every function
# below is on an independent chain.
for f in raw_nanos_field_sum raw_nanos_field_carry raw_nanos_field_borrow total_nanos; do
  grep -qE "trust_timearith::$f \[(INCONCLUSIVE|FAILED)\]" "$LOG" \
    && fail "mutation G: $f also stopped verifying — it does not reach raw_nanos_field_diff, so this run is a general regression and says nothing about §13.5"
done
rm -f "$LOG"; restore
mut_end

# ---------------------------------------------------------------------------
# 10. THE TESTS, AND THE TWO MUTATIONS THEY ALONE CAN CATCH.
# ---------------------------------------------------------------------------
STEP="tests"; mut_begin
runtests
if [ "$RC" -ne 0 ]; then fail "pristine: unit tests failed (rc=$RC)  $(grep -oE '^test result: .*' "$LOG" | head -1)"; else
  grep -qE '^test result: ok\. 20 passed; 0 failed' "$LOG" \
    || fail "pristine tests: expected 20 passed — $(grep -oE '^test result: .*' "$LOG" | head -1)"
  mut_ok "tests     $(grep -oE '^test result: ok\. [0-9]+ passed[^;]*; [0-9]+ failed' "$LOG" | head -1)"
fi
rm -f "$LOG"
mut_end

# --- MUTATION H — wrong value, TIER-1 POSTCONDITION SURVIVES ----------------
STEP="mutation H"; mut_begin
mutate '    let d: u64 = s - 1000000000;
    if d > 4294967295 {' '    let d: u64 = s - 1000000;
    if d > 4294967295 {'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation H: the strict lane REFUTED a wrong carry constant (rc=$VRC $VG) — welcome news, but this gate's claim that a discharged postcondition cannot see the answer is now stale and must be re-measured"
else
  grep -qE 'Summary: 127 proved, 0 failed, .*0 inconclusive \(127 total\)' "$LOG" \
    || fail "mutation H: the row count moved — the demonstration needs the split to be IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
    || fail "mutation H: the kind split moved under a wrong-value mutation"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation H: a wrong carry constant passed the unit tests"; else
  mut_ok "mutation H (nanosecond carry folds out 1000000 instead of 1000000000; 'ensures result <= 999999999' still TRUE)  tests rc=$RC, strict lane rc=$VRC"
fi
# Assert WHICH tests fail, by name. A bare rc would be satisfied by a broken
# doctest stage or a compile error, and the control would silently stop testing.
for t in carry_and_field_conserve_the_whole_sum \
         the_carry_is_exactly_the_one_second_boundary; do
  grep -q "$t ... FAILED" "$LOG" \
    || fail "mutation H: $t did not catch a wrong carry constant"
done
# The tier-1 BOUND test must still PASS — otherwise the demonstration degrades
# into "the mutation broke everything" and says nothing about proofs-vs-answers.
grep -q 'every_tier1_bound_holds_and_every_clamp_can_fire ... ok' "$LOG" \
  || fail "mutation H: the tier-1 bound test also went red — H no longer isolates 'proved contract over a wrong answer'"
rm -f "$LOG"; restore
mut_end

# --- MUTATION I — wrong value, a TIER-2 UNIT FACTOR -------------------------
STEP="mutation I"; mut_begin
mutate '    (hours as u64) * 3600
}' '    (hours as u64) * 360
}'
run
VRC="$RC"; VG="$(gate_line)"
if [ "$VRC" -ne 0 ]; then
  fail "mutation I: the strict lane REFUTED a wrong unit factor (rc=$VRC $VG) — welcome news, but the peak MOVED DOWN and this must be re-measured"
else
  grep -qE 'Summary: 127 proved, 0 failed, .*0 inconclusive \(127 total\)' "$LOG" \
    || fail "mutation I: the row count moved — a smaller coefficient must leave the split IDENTICAL, got $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
  [ "$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)" = "$PRISTINE_KINDS" ] \
    || fail "mutation I: the kind split moved under a wrong-value mutation"
fi
rm -f "$LOG"
runtests
if [ "$RC" -eq 0 ]; then fail "mutation I: an hours_to_secs off by a factor of ten passed the unit tests"; else
  mut_ok "mutation I (hours_to_secs multiplies by 360; the Mul row still proves)  tests rc=$RC, strict lane rc=$VRC"
fi
grep -q 'the_up_conversion_ladder_is_exact_at_the_top_of_u32 ... FAILED' "$LOG" \
  || fail "mutation I: the up-conversion ladder test did not catch a wrong unit factor"
# ...and the carry/conservation tests must still PASS, so I isolates the unit
# factor rather than breaking the crate.
grep -q 'carry_and_field_conserve_the_whole_sum ... ok' "$LOG" \
  || fail "mutation I: the conservation test also went red — I no longer isolates the unit factor"
mut_end
if [ "$VRC" -eq 0 ]; then
  echo "       (note: the strict lane still PASSED this mutation, as expected — a"
  echo "        SMALLER coefficient moves the peak down, so the mul row and its"
  echo "        hardened twin both still prove. No obligation in this crate can"
  echo "        see a unit factor.)"
fi
rm -f "$LOG"; restore

# ---------------------------------------------------------------------------
# 11. The restore actually restored. A gate that leaves a mutation behind turns
#     the next run into a false red and, worse, could be committed.
# ---------------------------------------------------------------------------
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "source was NOT restored ($NOW_SHA != $PRISTINE_SHA)"

[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
