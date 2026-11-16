#!/usr/bin/env bash
# trust_floatbits_strict_gate.sh — pin `crates/trust-floatbits` at a NON-VACUOUS
# pass of the authenticated strict lane, with live mutation controls.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHAT THIS ONE PINS THAT THE EIGHTEEN BEFORE IT DO NOT
# -----------------------------------------------------
# `trust-floatbits` is the fourth crate EXTRACTED FROM Trust's own verification
# stack (after `trust-intbound` and wave two's `trust-widthconv`/`trust-budget`),
# and the first whose subject is a bound that is handed to the SOLVER AS A FACT
# in a direction where being wrong is a false PROVE. Its consumer,
# `trust_vcgen::generate::float_range`, does
#
#   Some(Ty::Int { width, .. }) => { let bound = exp2i(*width)?;
#                                    finite_outward(-bound, bound) }
#
# and conjoins that interval onto float-overflow obligations. A bound BELOW the
# true `2^w` discharges a real overflow.
#
# So the load-bearing assertions are:
#   (a) mutation A — the catastrophic sentinel (`0`, i.e. a bound of `0.0`) is
#       REFUTED by the clause, not merely untested. This is the first extraction
#       whose false-hypothesis direction the strict lane can actually SEE.
#   (b) mutation B — the residue the clauses still admit (a constant `1.0`)
#       passes the lane at exit 0 while the named oracle tests go red. Both
#       halves are asserted, because a clause that catches everything and a
#       clause that catches nothing are equally suspicious.
#   (c) mutation E — `u64::from(w)` for `w as u64`. Measured while building this
#       crate: the `From` spelling makes the addend an UNMODELLED CALLEE RETURN
#       and REFUTES the overflow row. `clippy::cast_lossless` recommends the
#       spelling that breaks the proof.
#   (d) mutation G — the CONSUMER genuinely depends on this crate.
#   (e) SINGLE AUTHORED BODY — cfg-selected declarative-macro definitions emit
#       either the native clause tokens or a stock-Rust signature around the
#       same invocation body. There is no verification/plain twin to drift.
#
# Measured 2026-08-30 against the stage1 driver from a tree at 850147d402
# (trustc blob sha256 6bf8876323cc9e4e…), under BOTH the default `unix_hardened`
# policy and `-Ztrust-policy=certify`, byte-identically:
#
#   exit 0 · Gate: PASS [strict lane, exit 0]
#   Summary: 39 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive (39 total)
#   Coverage: 12/12 eligible function bodies verified (complete)
#   proved by kind: arithmetic_overflow_add=1, arithmetic_overflow_shl=1,
#                   arithmetic_overflow_shr=1, hardened_panic_boundary=3,
#                   postcondition=31, shift_overflow_shl=1, shift_overflow_shr=1
#   unreachable: 0     absent-callee rows: 0     relabelled at publication: 0
#
# EVERY NUMBER ABOVE WAS RECOMPUTED FOR THIS CRATE. None is transplanted from
# `trust_budget_strict_gate.sh`; the crates share no peak.
#
# Usage:  scripts/trust_floatbits_strict_gate.sh
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
SRC="$REPO_ROOT/crates/trust-floatbits/src/lib.rs"
# Contract tokens and their single authored bodies live together in cfg-selected
# declarative macro invocations in SRC. Stock/bootstrap rustc expands away only
# the clauses; Trust restores the native tokens for every mutation below.
CONSUMER_MANIFEST="$REPO_ROOT/crates/trust-vcgen/Cargo.toml"
CONSUMER_PACKAGE="trust-vcgen"
CONSUMER_DEP_LINE='trust-floatbits = { workspace = true }'
WORKSPACE_LOCK="$REPO_ROOT/Cargo.lock"
# `build/host` resolves to the configured host triple on every supported
# platform; keeping a literal Apple target here made the gate unrunnable on
# Linux even when the authenticated stage was present.
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
# G1. AN ENVIRONMENT FAILURE IS NOT A RESULT.  (§9.6, §16.5)
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

run() { # run [lane flag]; sets RC and LOG
  LOG="$(mktemp)"
  ( cd "$REPO_ROOT/crates" && "$TARGO" trust check --all-rows ${1:+"$1"} -p trust-floatbits ) > "$LOG" 2>&1
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
  cmp -s "$WORKSPACE_LOCK" "$CANDIDATE_ROOT/Cargo.lock" \
    || { echo "REFUSE: candidate lock does not start byte-identical" >&2; exit 3; }
  [ ! "$WORKSPACE_LOCK" -ef "$CANDIDATE_ROOT/Cargo.lock" ] \
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
      "$TARGO" --unverified check --manifest-path "$CANDIDATE_ROOT/Cargo.toml" \
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
  ( cd "$REPO_ROOT/crates" && "$TARGO" --unverified test -p trust-floatbits --lib ) > "$LOG" 2>&1
  RC=$?
  require_env "${STEP:-tests}"
}
gate_line() { grep -oE 'Gate: [A-Z-]+ \[[a-z-]+ lane, exit [0-9]+\]' "$LOG" | tail -1; }

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

echo "trust-floatbits strict gate:"
# ---------------------------------------------------------------------------
# 1. THE PASS — exit code, Gate, compile status, coverage, the kind split, and
#    the ABSENCE of every string a later mutation asserts.
# ---------------------------------------------------------------------------
STEP="THE PASS"; mut_begin
run
G="$(gate_line)"
[ -n "$G" ] || fail "pristine: no Gate: line — the report did not seal (§9.2), so nothing below is readable"
[ "$RC" -eq 0 ] || fail "pristine: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [strict lane, exit 0]"*) ;; *) fail "pristine: Gate is '$G'";; esac
if grep -qE '^error(\[|:)' "$LOG"; then fail "pristine: rustc reported errors; obligations for unlowered code are ABSENT, not proved"; fi
grep -q 'Coverage: 12/12 eligible function bodies verified (complete)' "$LOG" \
  || fail "pristine: coverage is not 12/12 complete — $(grep -oE 'Coverage: [^)]*\)' "$LOG" | tail -1)"
grep -qE 'Summary: 39 proved, 0 failed, 0 runtime-checked, 0 assumed, .*0 inconclusive \(39 total\)' "$LOG" \
  || fail "pristine: summary moved — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
# NON-VACUITY. `VcKind::Unreachable`'s formula is literally `Bool(true)`.
KINDS="$(grep -oE 'proved by kind: [a-z_=0-9, ]+' "$LOG" | tail -1)"
case "$KINDS" in *unreachable*) fail "pristine: an 'unreachable' row appeared — $KINDS";; esac
case "$KINDS" in *"postcondition=31"*) ;; *) fail "pristine: expected postcondition=31 — got: $KINDS";; esac
# The SAFETY rows. `raw_exp2_bits`'s add and shift are what mutation E refutes;
# without them that mutation would be measuring nothing.
for k in "arithmetic_overflow_add=1" "arithmetic_overflow_shl=1" "arithmetic_overflow_shr=1" "shift_overflow_shl=1" "shift_overflow_shr=1"; do
  case "$KINDS" in *"$k"*) ;; *) fail "pristine: the $k row is gone — a mutation below cannot discriminate. $KINDS";; esac
done
grep -q 'verification failed for' "$LOG" \
  && fail "pristine: the compiler reported a per-function verification failure that the published Summary does not show (§14.6)"
N_ABSENT="$(grep -c 'trust-absent-callee-assumption' "$LOG")"
[ "$N_ABSENT" -eq 0 ] || fail "pristine: $N_ABSENT trust-absent-callee-assumption row(s)"
# Absence controls for mutations A, C, D, E.
for absent in 'verification failed for `trust_floatbits::exp2_binary64_bits`' \
              'verification failed for `trust_floatbits::magnitude_mask`' \
              'verification failed for `trust_floatbits::magnitude_field_width`' \
              'verification failed for `trust_floatbits::raw_exp2_bits`' \
              'UnmodeledCalleeReturn' \
              'INCONCLUSIVE [strict lane, exit 1]'; do
  grep -qF "$absent" "$LOG" \
    && fail "pristine: '$absent' is ALREADY present — the mutation that asserts it cannot discriminate"
done
mut_ok "pristine  $G  [31 postcondition + 5 safety + 3 hardened_panic_boundary, 0 unreachable]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 2. THE SAME PASS UNDER `--certify` (the compiler's `certify` policy).
#    The lane flag selects the compiler's `certify` policy, and the Gate line
#    names the lane that graded the run, so `[certify lane, exit 0]` is the
#    evidence that certify ran. (A bogus-policy control proved the TRUSTFLAGS
#    route reached the compiler; it went with that channel, DECISION_QUEUE T7a.)
# ---------------------------------------------------------------------------
STEP="CERTIFY"; mut_begin
run "--certify"
G="$(gate_line)"
[ "$RC" -eq 0 ] || fail "certify: rc=$RC (expected 0)  $G"
case "$G" in *"PASS [certify lane, exit 0]"*) ;; *) fail "certify: Gate is '$G'";; esac
grep -qE 'Summary: 39 proved, 0 failed, .*0 inconclusive \(39 total\)' "$LOG" \
  || fail "certify: summary differs from the default policy — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
grep -qE 'Publication boundary: [0-9]+ obligation\(s\) passed the compiler, 39 published, [0-9]+ WITHHELD .*\(0 relabelled unknown' "$LOG" \
  || fail "certify: a favorable compiler row was RELABELLED at the publication boundary — $(grep -oE '^Publication boundary: .*' "$LOG" | tail -1)"
mut_ok "certify   $G  [0 relabelled at the publication boundary]"
rm -f "$LOG"

mut_end
# ---------------------------------------------------------------------------
# 3. MUTATION A — THE CATASTROPHIC SENTINEL, AND THE CLAUSE THAT SEES IT.
#    `exp2_binary64_bits` saturates DOWN to `0` instead of up to `+inf`. `0` is
#    the bit pattern of `+0.0`, so the consumer's int->f64 cast bound becomes the
#    interval `[-0.0, 0.0]` and EVERY cast is claimed non-overflowing — a false
#    hypothesis conjoined onto real obligations.
#
#    This is the direction §16.1 and §17.4 say the lane CANNOT normally see, and
#    here it can: `ensures result >= 4607182418800017408` excludes the whole
#    zero-and-subnormal region. That is the reason for the second clause, and
#    this mutation is the proof that it is not decoration.
# ---------------------------------------------------------------------------
STEP="MUTATION A"; mut_begin
mutate "$SRC" '    if w > 1023 {
        return 9218868437227405312;
    }' '    if w > 1023 {
        return 0;
    }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation A: a magnitude bound of 0.0 for every unsupported width still PASSED — the `result >= 1.0` clause is not doing its work, and the false-hypothesis direction is unguarded  $G"
else
  mut_ok "mutation A (exp2 sentinel flipped DOWN to 0.0 — the false-PROVE direction)  rc=$RC  $G"
fi
grep -qF 'verification failed for `trust_floatbits::exp2_binary64_bits`' "$LOG" \
  || fail "mutation A: exp2_binary64_bits was NOT refuted — the crate went red for some other reason"
grep -qE 'Gate: FAIL \[strict lane, exit 1\]' "$LOG" \
  || fail "mutation A: expected Gate FAIL (a refutation), got '$G' — this boundary is supposed to be LOUD"
for f in magnitude_mask nonfinite_exponent format_supported; do
  grep -qF "verification failed for \`trust_floatbits::$f\`" "$LOG" \
    && fail "mutation A: $f was refuted by an exp2-only break — this run went red for an unrelated reason and is not evidence"
done
mut_ok "          the lower clause REFUTES it: this is the first extraction whose unsound direction the lane can see"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 4. MUTATION B — THE WRONG-VALUE CONTROL, AND THE RESIDUE THE CLAUSES ADMIT.
#    `raw_exp2_bits` drops the bias, so `2^w` becomes `2^(w-1023)` — every bound
#    is 2^1023 times too small, which is the unsound direction. BOTH clauses
#    still hold for w >= 1023 and the clamp fail-closes the rest to +inf, so the
#    strict lane must PASS at exit 0 while the NAMED oracle tests go red.
#
#    A and B together are the whole honest claim of this crate: the clause sees
#    the catastrophic wrong answer and cannot see the merely-wrong one.
# ---------------------------------------------------------------------------
STEP="MUTATION B"; mut_begin
mutate "$SRC" '    ((w as u64) + 1023) << 52' '    ((w as u64) + 0) << 52'
run
G="$(gate_line)"
[ "$RC" -eq 0 ] \
  && mut_ok "mutation B (the exponent BIAS deleted; every bound 2^1023 too small)  the strict lane still PASSES  $G" \
  || fail "mutation B: the lane FAILED on a wrong VALUE (rc=$RC) — §4.6 no longer holds and the tests are no longer the only thing checking values; re-read this section"
grep -qE 'Summary: 39 proved, 0 failed' "$LOG" \
  || fail "mutation B: the row count moved on a value-only change — $(grep -oE '^Summary: .*' "$LOG" | tail -1)"
rm -f "$LOG"
runtests
[ "$RC" -eq 0 ] \
  && fail "mutation B: the exponent bias is gone and every test still PASSED — the oracle tests cannot see a wrong value, which is the only thing they exist for" \
  || mut_ok "          and the tests go RED  rc=$RC"
grep -q 'exp2_binary64_bits_matches_a_libm_powers_oracle' "$LOG" \
  || fail "mutation B: the doubling-oracle test did not name itself in the failure output — it may not have run"
grep -q 'replaced_consumer_body_is_reproduced_exactly' "$LOG" \
  || fail "mutation B: the pre-extraction-body equivalence test did not name itself — it may not have run"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 5. MUTATION C — THE MAGNITUDE MASK KEEPS THE SIGN BIT.
#    `magnitude_mask(64)` returns `u64::MAX`. The consumer uses this as the mask
#    on an operand's bit pattern before an unsigned magnitude comparison, so a
#    kept sign bit makes every NEGATIVE float compare as enormous and the
#    overflow witness silently stops firing — the under-approximating direction
#    `float_overflow.rs`'s own soundness note forbids.
#
#    `ensures result <= 9223372036854775807` IS "the sign bit is clear", so this
#    must be a REFUTATION.
# ---------------------------------------------------------------------------
STEP="MUTATION C"; mut_begin
mutate "$SRC" '    if width == 64 {
        return 9223372036854775807;
    }
    0
}' '    if width == 64 {
        return 18446744073709551615;
    }
    0
}'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation C: a magnitude mask that keeps the SIGN BIT still passed  $G"; else mut_ok "mutation C (magnitude_mask keeps the sign bit)  rc=$RC  $G"; fi
grep -qF 'verification failed for `trust_floatbits::magnitude_mask`' "$LOG" \
  || fail "mutation C: magnitude_mask was NOT refuted"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 6. MUTATION D — A WIDER MAGNITUDE FIELD.
#    `magnitude_field_width(64)` returns 64, which puts the sign bit INSIDE the
#    magnitude bitvector the consumer builds. Same soundness direction as C, at
#    the other end of the same pair — C is the mask, D is the WIDTH, and a
#    reader who fixes only one has fixed nothing.
# ---------------------------------------------------------------------------
STEP="MUTATION D"; mut_begin
mutate "$SRC" '    if width == 64 {
        return 63;
    }' '    if width == 64 {
        return 64;
    }'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then fail "mutation D: a magnitude field width that swallows the sign bit still passed  $G"; else mut_ok "mutation D (magnitude_field_width includes the sign bit)  rc=$RC  $G"; fi
grep -qF 'verification failed for `trust_floatbits::magnitude_field_width`' "$LOG" \
  || fail "mutation D: magnitude_field_width was NOT refuted"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 7. MUTATION E — `u64::from(w)` IS NOT `w as u64`, AND THE DIFFERENCE IS A
#    REFUTATION.  Measured while building this crate, and the reason the source
#    carries a comment where a reader would otherwise "simplify" it back:
#    `u64::from` is a CALL, its body is not in the bundle, so the widened addend
#    becomes an UNMODELLED CALLEE RETURN with no range at all and the `+`
#    overflow row is refuted.
#
#    `clippy::cast_lossless` recommends exactly the spelling that breaks it.
#    The day the encoder models `<u64 as From<u32>>::from`, this mutation stops
#    failing, the gate goes RED, and the correct response is to record that in
#    the fragment map and delete this mutation.
# ---------------------------------------------------------------------------
STEP="MUTATION E"; mut_begin
mutate "$SRC" '    ((w as u64) + 1023) << 52' '    (u64::from(w) + 1023) << 52'
run
G="$(gate_line)"
if [ "$RC" -eq 0 ]; then
  fail "mutation E: `u64::from(w)` now verifies identically to `w as u64` — the encoder learned the From impl. Record it in the fragment map, drop the comment in raw_exp2_bits, and delete this mutation."
else
  mut_ok "mutation E (u64::from(w) for w as u64)  rc=$RC  $G"
fi
grep -qF 'verification failed for `trust_floatbits::raw_exp2_bits`' "$LOG" \
  || fail "mutation E: raw_exp2_bits was NOT refuted — the failure moved somewhere else"
grep -qF 'UnmodeledCalleeReturn' "$LOG" \
  || fail "mutation E: the log does not carry 'UnmodeledCalleeReturn' — this run went red for some other reason, so it is not evidence for the recorded mechanism"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 8. MUTATION F — THE SUPPORTED-PREDICATE ABSENCE CONTROL.
#    `format_supported` accepts every width. The clause `result <= 1` still
#    holds, so the lane must PASS — and the exhaustive test must go red. This
#    is the §16.1 mitigation itself under test: the accessors saturate to `0`,
#    so the ONLY thing separating "unsupported" from an answer is this
#    predicate, and nothing in the proof can check what it decides.
# ---------------------------------------------------------------------------
STEP="MUTATION F"; mut_begin
mutate "$SRC" 'pub fn format_supported(width: u32) -> u32
clauses [ensures result <= 1]
{
    if width == 32 {
        return 1;
    }
    if width == 64 {
        return 1;
    }
    0
}' 'pub fn format_supported(width: u32) -> u32
clauses [ensures result <= 1]
{
    if width == 32 {
        return 1;
    }
    if width == 64 {
        return 1;
    }
    1
}'
run
G="$(gate_line)"
[ "$RC" -eq 0 ] \
  && mut_ok "mutation F (format_supported accepts f16/f128, whose field rows are all 0)  lane still PASSES  $G" \
  || fail "mutation F: the lane FAILED on the supported predicate (rc=$RC) — if the verifier can now see this, §16.1's mitigation note needs correcting"
rm -f "$LOG"
runtests
[ "$RC" -eq 0 ] \
  && fail "mutation F: an accept-everything predicate passed every test — format_supported_accepts_exactly_binary32_and_binary64 is not doing its job" \
  || mut_ok "          and the tests go RED  rc=$RC"
grep -q 'format_supported_accepts_exactly_binary32_and_binary64' "$LOG" \
  || fail "mutation F: the exhaustive predicate test did not name itself — it may not have run"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 9. MUTATION G — THE DEPENDENCY EDGE IS LOAD-BEARING.
#    `trust-vcgen`'s int->f64 cast bound, its float-overflow field table (three
#    ad-hoc tuple spellings) and its witness-width predicate were DELETED from
#    two files and rebuilt on this crate; remove the edge and the consumer must
#    not COMPILE.
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
  fail "mutation G: trust-vcgen still built with no trust-floatbits dependency — the edge is DECORATIVE and the extraction claim is void"
else
  mut_ok "mutation G (delete trust-floatbits from trust-vcgen)  rc=$RC"
fi
grep -qE '^error\[E0433\]' "$LOG" \
  || fail "mutation G: the build did not fail with E0433 (unresolved crate) — it failed for some other reason, so this run does not show the edge is load-bearing. $(grep -oE '^error(\[E[0-9]{4}\])?: .*' "$LOG" | head -1)"
N="$(grep -cE '^error\[E0433\]' "$LOG")"
[ "$N" -ge 8 ] \
  || fail "mutation G: only $N unresolved-crate errors — a load-bearing edge should break every call site (expected >= 8, across two files)"
mut_ok "          $N call sites went unresolved — the consumer genuinely depends on this crate"
rm -f "$LOG"; restore_or_refuse

mut_end
# ---------------------------------------------------------------------------
# 10. The restore actually restored — source and consumer manifest.
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
