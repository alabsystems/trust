#!/usr/bin/env bash
# trust_widthconv_strict_gate.sh — pin `crates/trust-widthconv` at a NON-VACUOUS
# pass of the authenticated strict lane, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHAT THIS ONE PINS THAT THE SEVENTEEN BEFORE IT DO NOT
# -----------------------------------------------------
# `trust-widthconv` is the second crate EXTRACTED FROM Trust's own verification
# stack (after `trust-intbound`), and the first whose subject is a
# FALSE-HYPOTHESIS site rather than a range bound. Its consumer,
# `trust_vcgen::machine_domain`, opens with:
#
#   "A truncating conversion lowered as the identity is this tree's canonical
#    false-proof bug."
#
# The rule table that decides it now lives here. So the load-bearing assertions
# are (a) that the table's narrowing row is really refused — mutation A and the
# exhaustive oracle — and (b) that the CONSUMER genuinely depends on this crate,
# which is mutation G on `trust-vcgen`'s manifest, not on this crate's.
#
# It also records the SENTINEL DIRECTION reversing from `trust-intbound`'s
# (mutation F): there the unsound direction was a bound too NARROW, here it is a
# decision too WIDE, and the lane cannot see either.
#
# Measured 2026-08-30 against the stage1 driver from a tree at 850147d402, under
# BOTH the default `unix_hardened` policy and `-Ztrust-policy=certify`,
# byte-identically:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 48 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive (48 total)
#   Coverage: 7/7 eligible function bodies verified (complete)
#   proved by kind: postcondition=48
#   unreachable: 0     absent-callee rows: 0     relabelled at publication: 0
#
# EVERY NUMBER ABOVE WAS RECOMPUTED FOR THIS CRATE. None is transplanted from
# `trust_intbound_strict_gate.sh`; the two crates share no peak.
#
# Usage:  scripts/trust_widthconv_strict_gate.sh
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-widthconv/src/lib.rs"
CONSUMER_MANIFEST="$REPO_ROOT/crates/trust-vcgen/Cargo.toml"
CONSUMER_PACKAGE="trust-vcgen"
CONSUMER_DEP_LINE='trust-widthconv = { workspace = true }'
WORKSPACE_LOCK="$REPO_ROOT/crates/Cargo.lock"
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

python3 "$REPO_ROOT/scripts/trust_floatbits_twin_parity.py" \
  "$SRC" "$(dirname "$SRC")/contracts.rs" \
  || { echo "REFUSE: single-source contract preflight failed"; exit 3; }

BACKUP="$(mktemp)" \
  || { echo "REFUSE: cannot allocate source backup" >&2; exit 3; }
if ! cp "$SRC" "$BACKUP" || ! cmp -s "$SRC" "$BACKUP"; then
  echo "REFUSE: could not create byte-exact source backup" >&2
  rm -f "$BACKUP"
  exit 3
fi

# Every exit path restores the mutated source byte-for-byte. Mutation G uses an
# inode-independent candidate workspace, so the live consumer and Cargo.lock
# are compare-only inputs and are never restored over concurrent work.
RESTORE_FAILED=0
CANDIDATE_ROOT=""
CANDIDATE_MANIFEST=""
restore() {
  local rc=0
  if ! cp "$BACKUP" "$SRC"; then
    echo "REFUSE: failed to restore $SRC from $BACKUP" >&2
    rc=1
  elif ! cmp -s "$BACKUP" "$SRC"; then
    echo "REFUSE: restored $SRC is not byte-exact; backup: $BACKUP" >&2
    rc=1
  fi
  if [ "$rc" -ne 0 ]; then RESTORE_FAILED=1; return 1; fi
  return 0
}
restore_or_refuse() {
  restore || { echo "REFUSE: restoration failed; backup retained at $BACKUP" >&2; exit 3; }
}
cleanup_candidate() {
  [ -n "$CANDIDATE_ROOT" ] || return 0
  python3 - "$CANDIDATE_ROOT" <<'PY'
import pathlib
import shutil
import sys

root = pathlib.Path(sys.argv[1])
marker = root / ".trust-mutation-candidate"
if root.is_symlink() or marker.is_symlink() or not marker.is_file():
    raise SystemExit(f"refusing unsafe candidate cleanup: {root}")
shutil.rmtree(root)
PY
  local rc=$?
  [ "$rc" -eq 0 ] && CANDIDATE_ROOT=""
  return "$rc"
}
on_exit() {
  local status=$?
  trap - EXIT HUP INT QUIT TERM
  if ! restore || [ "$RESTORE_FAILED" -ne 0 ]; then
    echo "REFUSE: restoration failed; backup retained at $BACKUP" >&2
    [ "$status" -ne 0 ] || status=3
  elif ! cleanup_candidate; then
    echo "REFUSE: could not remove mutation candidate: $CANDIDATE_ROOT" >&2
    [ "$status" -ne 0 ] || status=3
  elif ! rm -f "$BACKUP"; then
    echo "REFUSE: restored source, but could not remove backup: $BACKUP" >&2
    [ "$status" -ne 0 ] || status=3
  fi
  exit "$status"
}
trap on_exit EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 131' QUIT
trap 'exit 143' TERM

PRISTINE_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)" \
  || { echo "REFUSE: could not hash $SRC"; exit 2; }
PRISTINE_CSHA="$(shasum -a 256 "$CONSUMER_MANIFEST" | cut -d' ' -f1)" \
  || { echo "REFUSE: could not hash $CONSUMER_MANIFEST"; exit 2; }
PRISTINE_LOCK_SHA="$(shasum -a 256 "$WORKSPACE_LOCK" | cut -d' ' -f1)" \
  || { echo "REFUSE: could not hash $WORKSPACE_LOCK"; exit 2; }

fails=0
LOG=""

# ---------------------------------------------------------------------------
# G1. AN ENVIRONMENT FAILURE IS NOT A RESULT, AND IT SATISFIES EVERY
#     PRESENCE-ONLY ASSERTION.  (§9.6, §16.5)
# ---------------------------------------------------------------------------
env_broken() {
  grep -qE 'MemoryAdmission|memory admission failed|could not connect to selected endpoint|Connection refused|could not establish the selected same-sysroot trustd memory authority' "${1:-$LOG}"
}
require_env() { # require_env <label>
  if env_broken "$LOG"; then
    echo "  ENV  $1: trustd memory admission was unavailable — every obligation was"
    echo "       refused BEFORE solver dispatch, so this run is not a fact about the"
    echo "       crate under test. Refusing to score it as a pass OR as a refutation."
    echo "INCONCLUSIVE (environment): trustd admission unavailable — re-run when it is up."
    echo "       log kept at $LOG"
    exit 3
  fi
  # §16.5: a stage1 sysroot with no `trustdoc` makes verified Targo refuse the
  # whole run and print NO Gate line — byte-compatible with "this crate is a
  # long way from verifying".
  if grep -q 'requires the authenticated sibling documentation generator' "$LOG"; then
    echo "  ENV  $1: the stage1 sysroot has no \`trustdoc\` beside \`targo\`, which"
    echo "       verified Targo requires before it will run at all. Not a fact about"
    echo "       the crate. Install one and re-run."
    exit 3
  fi
}

# Pin the exact pre-admission diagnostic independently of any proof summary it
# may precede. The close negative deliberately mentions trustd and authority.
selftest_env_classifier() {
  local positive negative output positive_rc negative_rc
  positive="$(mktemp)" || return 1
  negative="$(mktemp)" || { rm -f "$positive"; return 1; }
  printf '%s\n' \
    'error: could not establish the selected same-sysroot trustd memory authority' \
    'Gate: PASS [strict lane, exit 0]' > "$positive"
  printf '%s\n' \
    'note: selected same-sysroot trustd memory authority remained available after solver dispatch' \
    > "$negative"
  output="$(LOG="$positive"; require_env "classifier positive control" 2>&1)"
  positive_rc=$?
  ( LOG="$negative"; require_env "classifier close-negative control" ) >/dev/null 2>&1
  negative_rc=$?
  rm -f "$positive" "$negative"
  [ "$positive_rc" -eq 3 ] \
    && printf '%s\n' "$output" | grep -qF 'INCONCLUSIVE (environment)' \
    && [ "$negative_rc" -eq 0 ]
}
selftest_env_classifier \
  || { echo "REFUSE: trustd environmental classifier controls failed" >&2; exit 3; }

# A mutation meant to break the PROOF must not have broken the BUILD instead.
no_rustc_error() { # no_rustc_error <label>
  if grep -qE '^error\[E[0-9]{4}\]' "$LOG"; then
    fail "$1: rustc reported $(grep -oE '^error\[E[0-9]{4}\]' "$LOG" | head -1) — this run is supposed to exercise the PROOF, not the BUILD; obligations for code that did not lower are ABSENT, not refuted"
  fi
  return 0
}

fail() { echo "  FAIL $*"; fails=$((fails+1)); }

run() { # run [policy]; sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-widthconv ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-run}"
  no_rustc_error "${STEP:-run}"
}
# The BUILD-breaking mutation (G) must not be run through `no_rustc_error`,
# whose whole job is to refuse the state G creates on purpose. It also targets
# the CONSUMER, not this crate.
prepare_consumer_candidate() {
  CANDIDATE_ROOT="$(mktemp -d)" \
    || { echo "REFUSE: cannot allocate mutation-G candidate" >&2; exit 3; }
  CANDIDATE_MANIFEST="$CANDIDATE_ROOT/crates/$CONSUMER_PACKAGE/Cargo.toml"
  python3 "$REPO_ROOT/scripts/trust_floatbits_twin_parity.py" \
    --materialize-consumer-candidate \
    "$REPO_ROOT" "$CANDIDATE_ROOT" "$CONSUMER_PACKAGE"
  [ "$?" -eq 0 ] || { echo "REFUSE: could not materialize mutation-G candidate" >&2; exit 3; }
  cmp -s "$WORKSPACE_LOCK" "$CANDIDATE_ROOT/crates/Cargo.lock" \
    || { echo "REFUSE: candidate lock does not start byte-identical" >&2; exit 3; }
  [ ! "$WORKSPACE_LOCK" -ef "$CANDIDATE_ROOT/crates/Cargo.lock" ] \
    || { echo "REFUSE: candidate lock is not inode-independent" >&2; exit 3; }
  [ ! "$CONSUMER_MANIFEST" -ef "$CANDIDATE_MANIFEST" ] \
    || { echo "REFUSE: candidate consumer manifest is not inode-independent" >&2; exit 3; }
}
assert_live_candidate_inputs() {
  local lock_sha consumer_sha
  lock_sha="$(shasum -a 256 "$WORKSPACE_LOCK" | cut -d' ' -f1)" || return 1
  consumer_sha="$(shasum -a 256 "$CONSUMER_MANIFEST" | cut -d' ' -f1)" || return 1
  [ "$lock_sha" = "$PRISTINE_LOCK_SHA" ] \
    && [ "$consumer_sha" = "$PRISTINE_CSHA" ] \
    && grep -qF "$CONSUMER_DEP_LINE" "$CONSUMER_MANIFEST" \
    && ! grep -qF "$CONSUMER_DEP_LINE" "$CANDIDATE_MANIFEST"
}
run_consumer_raw() {
  assert_live_candidate_inputs \
    || { echo "REFUSE: live lock/consumer changed or candidate mutation is not isolated" >&2; exit 3; }
  LOG="$(mktemp)"
  ( cd "$CANDIDATE_ROOT/crates" \
    && CARGO_TARGET_DIR="$CANDIDATE_ROOT/target" \
      "$TARGO" --unverified check --manifest-path "$CANDIDATE_ROOT/crates/Cargo.toml" \
        -p "$CONSUMER_PACKAGE" ) > "$LOG" 2>&1
  RC=$?
  assert_live_candidate_inputs \
    || { echo "REFUSE: mutation G touched or raced the live lock/consumer" >&2; exit 3; }
  cleanup_candidate \
    || { echo "REFUSE: could not remove mutation-G candidate: $CANDIDATE_ROOT" >&2; exit 3; }
}
# `--lib` is load-bearing: a concurrent `x.py check` can leave stage1 `trustdoc`
# referencing a stale `librustc_driver` hash, and the doctest stage then dies
# with SIGABRT while every unit test passes — which DISARMS the wrong-value
# controls, whose whole assertion is "the tests go red".
runtests() { # sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-widthconv --lib ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-tests}"
}
gate_line() { grep -oE 'Gate: [A-Z]+ \[strict lane, exit [0-9]+\]' "$LOG" | tail -1; }

# ---------------------------------------------------------------------------
# G2. `ok` MUST MEAN "THIS SECTION'S OWN CONTENT ASSERTIONS HELD".
# ---------------------------------------------------------------------------
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

echo "trust-widthconv strict gate:"

# ---------------------------------------------------------------------------
# 1. THE PASS — exit code, Gate, compile status, coverage, the kind split, and
#    the ABSENCE of every string a later mutation asserts (without which those
#    mutations cannot discriminate "the boundary is still there" from "that
#    string is always present").
# ---------------------------------------------------------------------------
STEP="THE PASS"; mut_begin
run
G="$(gate_line)"
# §9.2: a crate can verify completely and fail to SEAL, printing no `Gate:`
# line, no `Summary:` and no diagnostic at all. Assert presence first.
[ -n "$G" ] || fail "pristine: no Gate: line — the report did not seal (§9.2), so nothing below is readable"
[ "$RC" -eq 0 ] || fail "pristine: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "pristine: Gate is '$G'";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 7/7 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 7/7 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 48 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(48 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `VcKind::Unreachable`'s formula is literally `Bool(true)`; an
# audit once found 53% of published proofs were exactly that.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
case "$KINDS" in *"postcondition=48"*) ;; *) fail "pristine: expected postcondition=48 — got: $KINDS";; esac
# §14.6: the published view is LOSSY. A function the compiler FAILED can be
# absent from the transport while the crate `Summary:` still reads 0
# inconclusive. The compiler's own per-function note is the authority.
grep -q 'verification failed for' "$LOG" \
  && fail "pristine: the compiler reported a per-function verification failure that the published Summary does not show (§14.6)"
N_ABSENT="$(grep -c 'trust-absent-callee-assumption' "$LOG")"
[ "$N_ABSENT" -eq 0 ] || fail "pristine: $N_ABSENT trust-absent-callee-assumption row(s)"
# Absence controls for mutations A, B, C, E.
for absent in 'verification failed for `trust_widthconv::conversion_code`' \
              'verification failed for `trust_widthconv::shift_mask`' \
              'verification failed for `trust_widthconv::join_width`' \
              'counterexample:'; do
  grep -qF "$absent" "$LOG" \
    && fail "pristine: '$absent' is ALREADY present — the mutation that asserts it cannot discriminate"
done
mut_ok "pristine  $G  [48 postcondition rows, 0 unreachable, 0 absent-callee]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 2. THE SAME PASS UNDER `-Ztrust-policy=certify`.
#    A misspelled TRUSTFLAGS is silently dropped, so first prove the flag path
#    reaches the compiler by requiring a bogus policy to be REJECTED BY NAME.
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
grep -qE 'Summary: 48 proved, 0 failed, .*0 inconclusive \(48 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
grep -qE 'Publication boundary: [0-9]+ obligation\(s\) passed the compiler, 48 published, [0-9]+ WITHHELD .*\(0 relabelled unknown' "$LOG" \
  || fail "certify: a favorable compiler row was RELABELLED at the publication boundary — $(grep -oE '^Publication boundary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G  [0 relabelled at the publication boundary]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — A CODE OUTSIDE THE FOUR THE CONSUMER'S `match` HANDLES.
#    `conversion_code`'s only clause is `result <= 3`. Return `4`: the consumer
#    would read it as REFUSED (its `_` arm), so this is the fail-closed
#    direction and NOT a false proof — but it is the one wrong answer the
#    clause can see, and if it stops being refuted the clause has stopped
#    checking anything at all.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate "$SRC" '    // Rows 2 and 4: an unsigned source widens by zero extension into either
    // signedness.
    2
}' '    // Rows 2 and 4: an unsigned source widens by zero extension into either
    // signedness.
    4
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: conversion_code returning 4 still passed  $G"; else mut_ok "mutation A (conversion_code returns an out-of-range code)  rc=$RC  $G"; fi
grep -qF 'verification failed for `trust_widthconv::conversion_code`' "$LOG" \
  || fail "mutation A: conversion_code was NOT refuted — its only clause is doing no work"
for f in width_supported extension_bits shift_mask join_width; do
  grep -qF "verification failed for \`trust_widthconv::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a conversion_code-only break — this run went red for an unrelated reason and is not evidence"
done
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — `shift_mask` breaks the LITERAL half of its clause pair.
#    `shift_mask(128)` returns 128, violating `ensures result <= 127` while
#    satisfying `ensures result <= target_width` (128 <= 128). Only a mutation
#    that breaks exactly one bound shows that bound is carried on its own.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate "$SRC" '    if target_width == 128 {
        return 127;
    }' '    if target_width == 128 {
        return 128;
    }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: shift_mask(128) = 128 still passed  $G"; else mut_ok "mutation B (shift_mask breaks the LITERAL bound)  rc=$RC  $G"; fi
grep -qF 'verification failed for `trust_widthconv::shift_mask`' "$LOG" \
  || fail "mutation B: shift_mask was NOT refuted by a value above the literal bound"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — `shift_mask` breaks the PARAMETER half.
#    `shift_mask(8)` returns 15: still under the literal 127, but ABOVE its own
#    width, which is the unsound direction (it admits a shift count >= the
#    width, which is Rust UB, as a defined operation). Mutation B and this one
#    together are what show the pair is doing work at each end.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate "$SRC" '    if target_width == 8 {
        return 7;
    }' '    if target_width == 8 {
        return 15;
    }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: shift_mask(8) = 15 still passed — a mask WIDER than its own width is exactly the UB-admitting direction  $G"; else mut_ok "mutation C (shift_mask breaks the PARAMETER bound)  rc=$RC  $G"; fi
grep -qF 'verification failed for `trust_widthconv::shift_mask`' "$LOG" \
  || fail "mutation C: shift_mask was NOT refuted — a bound against a PARAMETER is not being checked"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION D — THE WRONG-VALUE CONTROL. §4.6 in one run: a proof covers
#    overflow, bounds and contracts, and says NOTHING about whether the answer
#    is right. `extension_bits(8, 32)` is made 25 instead of 24 — inside both
#    clauses (25 <= 120, 25 <= 32), so the strict lane must still PASS at exit 0
#    while the NAMED tests go red.
#
#    This is the assertion that makes the exhaustive oracle tests load-bearing
#    rather than decorative. If it ever stops passing the lane, the crate has
#    acquired a real clause on that value and this comment is the thing to fix.
# ---------------------------------------------------------------------------
STEP="MUTATION D"; mut_begin
mutate "$SRC" '    if dst_width == 32 {
        if src_width == 8 {
            return 24;
        }' '    if dst_width == 32 {
        if src_width == 8 {
            return 25;
        }'
run
G="$(gate_line)"
[ "$RC" -eq 0 ] \
  && mut_ok "mutation D (extension_bits(8,32) off by one)  the strict lane still PASSES  $G" \
  || fail "mutation D: the lane FAILED on a wrong VALUE (rc=$RC) — §4.6 no longer holds and the tests are no longer the only thing checking values; re-read this section"
grep -qE 'Summary: 48 proved, 0 failed' "$LOG" \
  || fail "mutation D: the row count moved on a value-only change — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
rm -f "$LOG"
runtests
[ "$RC" -eq 0 ] \
  && fail "mutation D: extension_bits(8,32) is off by one and every test still PASSED — the oracle tests cannot see a wrong value, which is the only thing they exist for" \
  || mut_ok "          and the tests go RED  rc=$RC"
grep -q 'extension_bits_is_the_width_difference' "$LOG" \
  || fail "mutation D: the exhaustive difference oracle did not name itself in the failure output — it may not have run"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION E — THE §14.1 MIRRORED PAIR IS DOING WORK.
#    `join_width` returns `right_width` unconditionally. `ensures result >=
#    right_width` still holds; `ensures result >= left_width` does not. Two
#    VARIABLE bounds in the SAME direction are the shape §14.1 measured as
#    discharging, and this is the control that shows both ends are checked.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate "$SRC" '    if left_width > right_width {
        return left_width;
    }
    right_width
}' '    right_width
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation E: join_width ignoring left_width still passed — the mirrored §14.1 pair is not being checked at both ends  $G"; else mut_ok "mutation E (join_width returns right_width unconditionally)  rc=$RC  $G"; fi
grep -qF 'verification failed for `trust_widthconv::join_width`' "$LOG" \
  || fail "mutation E: join_width was NOT refuted"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 8. MUTATION F — THE SENTINEL DIRECTION (§15.5, §16.1, and the module doc's
#    central decision). `conversion_code`'s out-of-domain answer is flipped from
#    REFUSED (0) to IDENTITY (1). That is the UNSOUND direction — an unmodelled
#    width would be converted as the identity, which is one step from the
#    truncation-as-identity bug the consumer's header names — and the clause
#    `result <= 3` cannot see it, because 1 is a perfectly legal code.
#
#    NOTE THE REVERSAL FROM `trust-intbound`, whose mutation E flips a sentinel
#    the OTHER way for the same reason: there the answer is a range BOUND and
#    the unsound direction is too narrow; here it is a DECISION and the unsound
#    direction is too wide. Both are the §16.1 argument, and the lane sees
#    neither.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate "$SRC" '    if raw_width_supported(src_width) == 0 {
        return 0;
    }' '    if raw_width_supported(src_width) == 0 {
        return 1;
    }'
run
G="$(gate_line)"
[ "$RC" -eq 0 ] \
  && mut_ok "mutation F (unsupported width -> IDENTITY instead of REFUSED)  lane still PASSES  $G" \
  || fail "mutation F: the lane FAILED on the sentinel direction (rc=$RC) — if the verifier can now see this, §16.1 and the module doc need correcting"
rm -f "$LOG"
runtests
[ "$RC" -eq 0 ] \
  && fail "mutation F: the sentinel was flipped to the UNSOUND direction and every test passed — conversion_code_fails_closed_off_the_domain is not doing its job" \
  || mut_ok "          and the tests go RED  rc=$RC"
grep -q 'conversion_code_fails_closed_off_the_domain' "$LOG" \
  || fail "mutation F: the fail-closed test did not name itself — it may not have run"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 9. MUTATION G — THE DEPENDENCY EDGE IS LOAD-BEARING.
#    The assertion that separates a real extraction from one that copied the
#    code and kept a decorative `[dependencies]` entry. `trust-vcgen`'s width
#    set (five copies), its conversion rule table and its shift mask were
#    DELETED and rebuilt on this crate; remove the edge and the consumer must
#    not COMPILE. Note the direction: the mutation is on the CONSUMER's
#    manifest, because here the verified crate is the dependency.
# ---------------------------------------------------------------------------
STEP="MUTATION G"; mut_begin
prepare_consumer_candidate
python3 - "$CANDIDATE_MANIFEST" "$CONSUMER_DEP_LINE" <<'PY'
import sys
p = sys.argv[1]; old = sys.argv[2]; s = open(p).read()
assert s.count(old) == 1, f"mutation G no longer applies ({s.count(old)} matches)"
open(p, "w").write(s.replace(old, ""))
PY
[ $? -eq 0 ] || fail "mutation G could not be applied — the consumer manifest moved under the gate"
run_consumer_raw
if [ "$RC" -eq 0 ]; then
  fail "mutation G: trust-vcgen still built with no trust-widthconv dependency — the edge is DECORATIVE and the extraction claim is void"
else
  mut_ok "mutation G (delete trust-widthconv from trust-vcgen)  rc=$RC"
fi
grep -qE '^error\[E0433\]' "$LOG" \
  || fail "mutation G: the build did not fail with E0433 (unresolved crate) — it failed for some other reason, so this run does not show the edge is load-bearing. $(grep -oE '^error(\[E[0-9]{4}\])?: .*' "$LOG" | head -1)"
N="$(grep -cE '^error\[E0433\]' "$LOG")"
[ "$N" -ge 8 ] \
  || fail "mutation G: only $N unresolved-crate errors — a load-bearing edge should break every call site (expected >= 8)"
mut_ok "          $N call sites went unresolved — the consumer genuinely depends on this crate"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 10. The restore actually restored — BOTH files.
# ---------------------------------------------------------------------------
STEP="RESTORE"; mut_begin
NOW_SHA="$(shasum -a 256 "$SRC" | cut -d' ' -f1)"
[ "$NOW_SHA" = "$PRISTINE_SHA" ] || fail "src was NOT restored ($NOW_SHA != $PRISTINE_SHA)"
NOW_CSHA="$(shasum -a 256 "$CONSUMER_MANIFEST" | cut -d' ' -f1)"
[ "$NOW_CSHA" = "$PRISTINE_CSHA" ] || fail "consumer manifest was NOT restored ($NOW_CSHA != $PRISTINE_CSHA)"
NOW_LOCK_SHA="$(shasum -a 256 "$WORKSPACE_LOCK" | cut -d' ' -f1)"
[ "$NOW_LOCK_SHA" = "$PRISTINE_LOCK_SHA" ] || fail "workspace lock changed ($NOW_LOCK_SHA != $PRISTINE_LOCK_SHA)"

mut_end
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
