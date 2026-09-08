#!/usr/bin/env bash
# trust_intbound_strict_gate.sh — pin `crates/trust-intbound` at a NON-VACUOUS
# pass of the authenticated strict lane, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS GATE IS DIFFERENT FROM THE SIXTEEN BEFORE IT
# -----------------------------------------------------
# `trust-intbound` is the first strict-lane crate EXTRACTED FROM Trust's own
# verification stack rather than written beside it. Its consumer,
# `trust-ir-bridge`, is an ordinary unverified compiler-side crate, and the
# direction of the edge is the opposite of `trust-bitfield`'s: there a verified
# crate depended on a verified crate; here an UNVERIFIED crate depends on a
# verified one. So the load-bearing assertion is not on this crate's manifest
# but on the CONSUMER's (mutation G).
#
# It also pins a defect this crate found and could not route around: a
# parameter named `max` or `min` is SILENTLY UNREADABLE from an `ensures`
# clause (mutation F, §16.2).
#
# Measured 2026-08-30 against stage1 driver from a tree at 850147d402, under
# BOTH the default `unix_hardened` policy and `-Ztrust-policy=certify`,
# byte-identically:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 15 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive (15 total)
#   Coverage: 17/17 eligible function bodies verified (complete)
#   proved by kind: postcondition=15
#   unreachable: 0     absent-callee rows: 0     relabelled at publication: 0
#
# Usage:  scripts/trust_intbound_strict_gate.sh
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-intbound/src/lib.rs"
# Contract tokens and their single authored bodies live together in cfg-selected
# declarative macro invocations in SRC. Stock/bootstrap rustc expands away only
# the clauses; Trust restores the native tokens for every mutation below.
CONSUMER_MANIFEST="$REPO_ROOT/crates/trust-ir-bridge/Cargo.toml"
CONSUMER_SRC="$REPO_ROOT/crates/trust-ir-bridge/src/lower.rs"
CONSUMER_PACKAGE="trust-ir-bridge"
CONSUMER_DEP_LINE='trust-intbound = { workspace = true }'
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
#     PRESENCE-ONLY ASSERTION.  (§9.6)
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
  # This crate's consumer measurement needs `trustdoc` beside `targo`; verified
  # Targo refuses the whole run without it and prints NO Gate line. That refusal
  # is byte-compatible with "the crate failed", so it aborts rather than scores.
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
# Trust's own verification failures are bare `error:` lines carrying no code, so
# keying on `error[E####]` isolates the rustc diagnostic.
no_rustc_error() { # no_rustc_error <label>
  if grep -qE '^error\[E[0-9]{4}\]' "$LOG"; then
    fail "$1: rustc reported $(grep -oE '^error\[E[0-9]{4}\]' "$LOG" | head -1) — this run is supposed to exercise the PROOF, not the BUILD; obligations for code that did not lower are ABSENT, not refuted"
  fi
  return 0
}

fail() { echo "  FAIL $*"; fails=$((fails+1)); }

run() { # run [policy]; sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && TRUSTFLAGS="${1:-}" "$TARGO" trust check -p trust-intbound ) > "$LOG" 2>&1
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
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-intbound --lib ) > "$LOG" 2>&1
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

echo "trust-intbound strict gate:"

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
grep -q 'Coverage: 17/17 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 17/17 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 15 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(15 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `VcKind::Unreachable`'s formula is literally `Bool(true)`; an
# audit once found 53% of published proofs were exactly that.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
case "$KINDS" in *"postcondition=15"*) ;; *) fail "pristine: expected postcondition=15 — got: $KINDS";; esac
# §14.6: the published view is LOSSY. A function the compiler FAILED can be
# absent from the transport while the crate `Summary:` still reads 0
# inconclusive. The compiler's own per-function note is the authority.
grep -q 'verification failed for' "$LOG" \
  && fail "pristine: the compiler reported a per-function verification failure that the published Summary does not show (§14.6)"
N_ABSENT="$(grep -c 'trust-absent-callee-assumption' "$LOG")"
[ "$N_ABSENT" -eq 0 ] || fail "pristine: $N_ABSENT trust-absent-callee-assumption row(s)"
# Absence controls for mutations A, B, C, F.
for absent in 'verification failed for `trust_intbound::signed_max`' \
              'verification failed for `trust_intbound::clamp_width`' \
              'verification failed for `trust_intbound::clamp_to_max`' \
              'counterexample:'; do
  grep -qF "$absent" "$LOG" \
    && fail "pristine: '$absent' is ALREADY present — the mutation that asserts it cannot discriminate"
done
mut_ok "pristine  $G  [15 postcondition rows, 0 unreachable, 0 absent-callee]"
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
grep -qE 'Summary: 15 proved, 0 failed, .*0 inconclusive \(15 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
grep -qE 'Publication boundary: [0-9]+ obligation\(s\) passed the compiler, 15 published, [0-9]+ WITHHELD .*\(0 relabelled unknown' "$LOG" \
  || fail "certify: a favorable compiler row was RELABELLED at the publication boundary — $(grep -oE '^Publication boundary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G  [0 relabelled at the publication boundary]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — THE SIGNED/UNSIGNED CONFUSION, which is the exact wrong
#    implementation `signed_max`'s clause exists to rule out. Return the
#    UNSIGNED maximum instead: at w = 64 that is `u64::MAX`, which violates
#    `ensures result <= 9223372036854775807`. It must be REFUTED — and the
#    other eight contracted functions must NOT be, or this run went red for an
#    unrelated reason and says nothing about `signed_max`.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate "$SRC" 'pub fn signed_max(w: u32) -> u64
clauses [ensures result <= 9223372036854775807]
{
    raw_signed_max(w)
}' 'pub fn signed_max(w: u32) -> u64
clauses [ensures result <= 9223372036854775807]
{
    unsigned_max_raw(w)
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation A: signed_max returning the UNSIGNED maximum still passed  $G"; else mut_ok "mutation A (signed_max returns the unsigned max)  rc=$RC  $G"; fi
grep -qF 'verification failed for `trust_intbound::signed_max`' "$LOG" \
  || fail "mutation A: signed_max was NOT refuted — the clause does not rule out the signed/unsigned confusion it is documented to rule out"
for f in width_is_supported signed_min_magnitude clamp_width clamp_to_max clamp_unsigned_to_width unsigned_fits signed_fits_nonneg signed_fits_magnitude; do
  grep -qF "verification failed for \`trust_intbound::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by a signed_max-only break — this run went red for an unrelated reason and is not evidence"
done
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — `clamp_width` loses its guard, so `ensures result <= 64` is
#    false at w > 64. The LITERAL half of the two-clause pair.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate "$SRC" 'pub fn clamp_width(w: u32) -> u32
clauses [ensures result <= 64 ensures result <= w]
{
    if w > 64 {
        return 64;
    }
    w
}' 'pub fn clamp_width(w: u32) -> u32
clauses [ensures result <= 64 ensures result <= w]
{
    w
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation B: an unclamped clamp_width still passed  $G"; else mut_ok "mutation B (clamp_width returns w unclamped)  rc=$RC  $G"; fi
grep -qF 'verification failed for `trust_intbound::clamp_width`' "$LOG" \
  || fail "mutation B: clamp_width was NOT refuted"
for f in signed_max clamp_to_max unsigned_fits; do
  grep -qF "verification failed for \`trust_intbound::$f\`" "$LOG" \
    && fail "mutation B: $f was refuted by a clamp_width-only break — not evidence"
done
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — `clamp_to_max` loses its guard, so `ensures result <= limit`
#    is false. The PARAMETER half of the two-clause pair: mutation B pins a
#    bound against a literal, this one pins a bound against a variable, and
#    only both together show the pair is doing work at each end.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate "$SRC" 'pub fn clamp_to_max(value: u64, limit: u64) -> u64
clauses [ensures result <= value ensures result <= limit]
{
    if value > limit {
        return limit;
    }
    value
}' 'pub fn clamp_to_max(value: u64, limit: u64) -> u64
clauses [ensures result <= value ensures result <= limit]
{
    value
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: an unclamped clamp_to_max still passed  $G"; else mut_ok "mutation C (clamp_to_max returns value unclamped)  rc=$RC  $G"; fi
grep -qF 'verification failed for `trust_intbound::clamp_to_max`' "$LOG" \
  || fail "mutation C: clamp_to_max was NOT refuted — a bound against a PARAMETER is not being checked"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION D — THE WRONG-VALUE CONTROL. §4.6 in one run: a proof covers
#    overflow, bounds and contracts, and says NOTHING about whether the answer
#    is right. One arm of the unsigned bound table is made wrong by one. The
#    strict lane must still PASS at exit 0 — the value is uncontracted, because
#    the only literal bound available is the `u64` type maximum and therefore
#    vacuous — while the NAMED tests go red.
#
#    This is the assertion that makes the exhaustive oracle tests load-bearing
#    rather than decorative. If it ever stops passing the lane, the crate has
#    acquired a real clause on that value and this comment is the thing to fix.
# ---------------------------------------------------------------------------
STEP="MUTATION D"; mut_begin
mutate "$SRC" '    if w == 32 {
        return 4294967295;
    }' '    if w == 32 {
        return 4294967294;
    }'
run
G="$(gate_line)"
[ "$RC" -eq 0 ] \
  && mut_ok "mutation D (unsigned_max(32) off by one)  the strict lane still PASSES  $G" \
  || fail "mutation D: the lane FAILED on a wrong VALUE (rc=$RC) — §4.6 no longer holds and the tests are no longer the only thing checking values; re-read this section"
grep -qE 'Summary: 15 proved, 0 failed' "$LOG" \
  || fail "mutation D: the row count moved on a value-only change — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
rm -f "$LOG"
runtests
[ "$RC" -eq 0 ] \
  && fail "mutation D: unsigned_max(32) is off by one and every test still PASSED — the oracle tests cannot see a wrong value, which is the only thing they exist for" \
  || mut_ok "          and the tests go RED  rc=$RC"
grep -q 'unsigned_max_matches_a_u128_oracle' "$LOG" \
  || fail "mutation D: the u128 oracle test did not name itself in the failure output — it may not have run"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION E — THE SENTINEL DIRECTION (§15.5, and the module doc's central
#    decision). Point the out-of-domain sentinel at ZERO instead of the widest
#    value. A too-NARROW bound is a false hypothesis handed to the solver; a
#    too-WIDE one only loses precision. The lane cannot see the difference —
#    that is the finding — so the test must.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate "$SRC" '    if w == 64 {
        return 18446744073709551615;
    }
    18446744073709551615
}' '    if w == 64 {
        return 18446744073709551615;
    }
    0
}'
run
G="$(gate_line)"
[ "$RC" -eq 0 ] \
  && mut_ok "mutation E (unsigned_max sentinel 0 instead of u64::MAX)  lane still PASSES  $G" \
  || fail "mutation E: the lane FAILED on the sentinel direction (rc=$RC) — if the verifier can now see this, §15.5 and the module doc need correcting"
rm -f "$LOG"
runtests
[ "$RC" -eq 0 ] \
  && fail "mutation E: the sentinel was flipped to the UNSOUND direction and every test passed — sentinel_is_the_wide_end_not_zero is not doing its job" \
  || mut_ok "          and the tests go RED  rc=$RC"
grep -q 'sentinel_is_the_wide_end_not_zero' "$LOG" \
  || fail "mutation E: the sentinel-direction test did not name itself — it may not have run"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 8. MUTATION F — THE `max` IDENTIFIER TRAP (§16.2).
#    Rename `clamp_to_max`'s second parameter back to the natural spelling.
#    A parameter named `max` (or `min`) is SILENTLY UNREADABLE from an `ensures`
#    clause: the byte-identical body proves 4/4 as `limit` and goes to 4 UNKNOWN
#    rows as `max`, with NO diagnostic naming the identifier and NO rustc error.
#
#    The day the compiler learns to read it, this mutation stops failing and the
#    gate goes RED, which is the signal to delete §16.2 and rename the parameter
#    back. That is the whole reason this is a gate assertion and not a comment.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate "$SRC" 'pub fn clamp_to_max(value: u64, limit: u64) -> u64
clauses [ensures result <= value ensures result <= limit]
{
    if value > limit {
        return limit;
    }
    value
}' 'pub fn clamp_to_max(value: u64, max: u64) -> u64
clauses [ensures result <= value ensures result <= max]
{
    if value > max {
        return max;
    }
    value
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation F: a parameter named \`max\` now READS correctly from its own ensures clause — §16.2 is CLOSED. Delete that section, rename clamp_to_max's parameter back to \`max\`, and delete this mutation."
else
  mut_ok "mutation F (rename \`limit\` -> \`max\`)  rc=$RC  $G"
fi
# It must fail as a SILENT UNKNOWN, not as a build error and not as a
# refutation. That distinction is the entire content of §16.2.
case "$G" in *"INCONCLUSIVE [strict lane, exit 1]"*) ;; *) fail "mutation F: expected Gate INCONCLUSIVE (a silent unknown), got '$G' — the failure mode changed, so §16.2's description is stale";; esac
grep -qE 'unknown by kind: postcondition=4' "$LOG" \
  || fail "mutation F: expected exactly 4 unknown postcondition rows — $(grep -oE 'unknown by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
grep -q 'counterexample:' "$LOG" \
  && fail "mutation F: a counterexample was printed — this is a REFUTATION, not the silent unknown §16.2 describes"
mut_ok "          silent: Gate INCONCLUSIVE, 4 unknown postcondition rows, no counterexample, no rustc error"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 9. MUTATION G — THE DEPENDENCY EDGE IS LOAD-BEARING.
#    The assertion that separates a real extraction from one that copied the
#    code and kept a decorative `[dependencies]` entry. `trust-ir-bridge`'s
#    `native_int_min_max` was DELETED and rebuilt on this crate; remove the
#    edge and the consumer must not COMPILE. Note the direction: the mutation
#    is on the CONSUMER's manifest, because here the verified crate is the
#    dependency rather than the dependent.
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
  fail "mutation G: trust-ir-bridge still built with no trust-intbound dependency — the edge is DECORATIVE and the extraction claim is void"
else
  mut_ok "mutation G (delete trust-intbound from trust-ir-bridge)  rc=$RC"
fi
grep -qE '^error\[E0433\]' "$LOG" \
  || fail "mutation G: the build did not fail with E0433 (unresolved crate) — it failed for some other reason, so this run does not show the edge is load-bearing. $(grep -oE '^error(\[E[0-9]{4}\])?: .*' "$LOG" | head -1)"
N="$(grep -cE '^error\[E0433\]' "$LOG")"
[ "$N" -ge 4 ] \
  || fail "mutation G: only $N unresolved-crate errors — a load-bearing edge should break every call site (expected >= 4)"
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
