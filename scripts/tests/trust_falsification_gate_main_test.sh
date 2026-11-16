#!/bin/bash
# Trust: end-to-end test of `trust_falsification_gate.sh`'s main() with a fake
# compiler, so the gate's ROW LOGIC is exercised without a stage2 `trustc`.
#
# `tests/trust-falsification/classify_verdict_test.sh` pins the classifier on
# text; `trust_falsification_gate_test.sh` pins the helpers. Neither runs main(),
# which is where the lanes turn verdicts into PASS/FAIL rows. This test copies
# the REAL gate into a throwaway Git repository with a fake
# build/<host>/stage2/bin/trustc whose output is the fixture's own text, so each
# fixture says exactly what the "compiler" prints and exits with.
#
# Rows pinned (2026-10-06):
#   * FALSIF-ARMOR-ASSUMED — a proved fixture whose certify summary carries the
#     `, N assumed (requires)` column is `proved` (it was a false red), and a
#     conditional (`conditionally discharged (NOT proved)`) exit-0 line is not.
#   * FALSIF-OD1-VOCAB — an OD-1 certify refusal on the mutant lane is an
#     UNCAUGHT (incomplete) row, never a refutation and never a tool error.
#   * A proved lane in which no fixture printed a summary is a FAIL, not a run of
#     zero-obligation acceptances.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

GATE_SOURCE=${1:-"$(cd -P "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)/scripts/trust_falsification_gate.sh"}
QUICK_SOURCE="$(cd -P "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)/falsification_corpus_quick.sh"
[[ -r $GATE_SOURCE ]] || {
  printf 'trust_falsification_gate_main_test: cannot read %s\n' "$GATE_SOURCE" >&2
  exit 2
}

TEST_ROOT=$(mktemp -d /tmp/trust-falsification-main-test.XXXXXXXXXX) || exit 2
TEST_ROOT=$(cd -P "$TEST_ROOT" && pwd -P) || exit 2
trap 'rm -rf -- "$TEST_ROOT"' EXIT

failures=0
fail() {
  printf '  FAIL  %s\n' "$*"
  failures=$((failures + 1))
}
ok() {
  printf '  ok    %s\n' "$*"
}

REPO="$TEST_ROOT/repo"
BIN="$REPO/build/test-host/stage2/bin"
FAKE_TRUSTC="$BIN/trustc"
mkdir -p "$REPO/scripts" "$REPO/tests/trust-falsification/proved" \
  "$REPO/tests/trust-falsification/mutant" "$BIN" || exit 2
cp "$GATE_SOURCE" "$REPO/scripts/trust_falsification_gate.sh" || exit 2
cp "$QUICK_SOURCE" "$REPO/scripts/falsification_corpus_quick.sh" || exit 2
chmod 755 "$REPO/scripts/trust_falsification_gate.sh"
printf 'build/\n' > "$REPO/.gitignore"

# The fake compiler: `-Vv` answers the commit recorded beside it; a compile
# prints the fixture's lines after the first to stderr and exits with the code
# its first line (`//rc=N`) names.
cat > "$FAKE_TRUSTC" <<'FAKE'
#!/bin/sh
fixture=
for arg do
  case $arg in
    -Vv)
      printf 'rustc 0.0.0-fake\ncommit-hash: %s\n' "$(cat "$0.head")"
      exit 0
      ;;
    *.rs) fixture=$arg ;;
  esac
done
[ -n "$fixture" ] || exit 2
rc=$(sed -n '1s,^//rc=,,p' "$fixture")
sed -n '2,$p' "$fixture" >&2
exit "${rc:-2}"
FAKE
chmod 700 "$FAKE_TRUSTC"

git_fake() {
  env -i PATH=/usr/bin:/bin HOME="$TEST_ROOT" GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null \
    git -C "$REPO" -c user.name=gate-test -c user.email=gate-test@invalid -c commit.gpgsign=false "$@"
}
git_fake init -q || exit 2

fixture() {
  local lane=$1 name=$2 rc=$3 text=$4
  printf '//rc=%s\n%s\n' "$rc" "$text" > "$REPO/tests/trust-falsification/$lane/$name.rs"
}

run_gate() {
  git_fake add -A && git_fake commit -q -m fixtures || return 2
  git_fake rev-parse HEAD > "$FAKE_TRUSTC.head" || return 2
  env -i PATH=/usr/bin:/bin HOME="$TEST_ROOT" TRUSTC="$FAKE_TRUSTC" \
    bash "$REPO/scripts/trust_falsification_gate.sh" > "$TEST_ROOT/gate.out" 2>&1
}

expect_line() {
  local label=$1 pattern=$2
  if grep -Fq -- "$pattern" "$TEST_ROOT/gate.out"; then
    ok "$label"
  else
    fail "$label: no line containing [$pattern]"
    sed 's/^/        | /' "$TEST_ROOT/gate.out"
  fi
}

STATIC='note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)'
# The exact two lines w17 prints for proved/contract_caller_precondition_met under certify.
REQUIRES='note: Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 1 obligation(s)
note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 2 obligation(s)'
REFUTED='error: Trust verification found 1 guaranteed Level 0 safety violation(s) in `m::f`'
OD1='error: Trust certify verification failed for `m::r3_t_default`: 1 instance hypothesis row(s) — panic-freedom of open generic dispatch is assumed, not proved
  = note: under -Ztrust-policy=certify an assumption:instance-hypothesis row is fatal; the default lane records it and passes CONDITIONALLY'
CONDITIONAL='note: Trust verification: 1 conditionally discharged (NOT proved), 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 4 skipped out of 5 obligation(s)'

printf 'case 1: assumed (requires) is proved, OD-1 refusal is an uncaught mutant\n'
fixture proved a_static 0 "$STATIC"
fixture proved b_requires 0 "$REQUIRES"
fixture proved c_cast_acceptance 0 ''
fixture mutant m_refuted 1 "$REFUTED"
fixture mutant m_od1 1 "$OD1"
run_gate
rc=$?
[[ $rc == 1 ]] && ok 'gate is RED on the uncaught OD-1 mutant (rc=1)' || fail "gate rc=$rc, expected 1"
expect_line 'static proved row' 'PASS  proved   a_static.rs  — verified'
expect_line 'assumed (requires) proved row' 'PASS  proved   b_requires.rs  — verified'
expect_line 'zero-headline acceptance row' 'PASS  proved   c_cast_acceptance.rs  — verified'
expect_line 'refuted mutant row' 'PASS  mutant   m_refuted.rs  — rejected by an explicit Trust verification verdict'
expect_line 'OD-1 certify refusal is incomplete, not refuted' \
  'FAIL  mutant   m_od1.rs  — UNCAUGHT MUTANT: verification was incomplete, not refuting'

printf 'case 2: without the OD-1 row the lanes are green\n'
rm -f "$REPO/tests/trust-falsification/mutant/m_od1.rs"
run_gate
rc=$?
[[ $rc == 0 ]] && ok 'gate is GREEN (rc=0)' || fail "gate rc=$rc, expected 0"
expect_line 'green headline' 'FALSIFICATION GATE: GREEN — 3 proofs verified and 1 mutants explicitly refuted'

printf 'case 3: a conditional exit-0 summary is not a proof\n'
fixture proved d_conditional 0 "$CONDITIONAL"
run_gate
rc=$?
[[ $rc == 1 ]] && ok 'gate is RED (rc=1)' || fail "gate rc=$rc, expected 1"
expect_line 'conditional row is runtime-checked' \
  'FAIL  proved   d_conditional.rs  — non-proof result: runtime-checked'

printf 'case 4: a proved lane with no summary at all measured nothing\n'
rm -f "$REPO/tests/trust-falsification/proved/"*.rs
fixture proved c_cast_acceptance 0 ''
fixture proved e_cast_acceptance 0 'warning: unused variable: `x`'
run_gate
rc=$?
[[ $rc == 1 ]] && ok 'gate is RED (rc=1)' || fail "gate rc=$rc, expected 1"
expect_line 'no-summary lane row' 'FAIL  proved   (lane)  — no proved fixture printed a `Trust verification:` summary'

# Trust: exercise the advisory owner through its real subprocess/TSV path too.
# These are fake-compiler harness controls, never native proof qualification.
TIMEOUT_BIN=$(command -v timeout) || exit 2
QUICK_OUT="$TEST_ROOT/quick"
run_quick() {
  env -i PATH="${TIMEOUT_BIN%/*}:/usr/bin:/bin" HOME="$TEST_ROOT" \
    bash "$REPO/scripts/falsification_corpus_quick.sh" "$FAKE_TRUSTC" "$QUICK_OUT" \
    > "$TEST_ROOT/quick.out" 2>&1
}
expect_quick_row() {
  local expected
  expected=$(printf '%s\t%s\t%s\t%s' "$1" "$2" "$3" "$4")
  if grep -Fxq -- "$expected" "$QUICK_OUT/results.tsv"; then
    ok "advisory TSV: $1/$2 $3 $4"
  else
    fail "advisory TSV missing [$expected]"
    cat "$TEST_ROOT/quick.out" "$QUICK_OUT/results.tsv"
  fi
}

printf 'case 5: advisory certify refusal is recorded without granting release refutation\n'
rm -f -- "${REPO:?}/tests/trust-falsification/proved/"*.rs \
  "${REPO:?}/tests/trust-falsification/mutant/"*.rs
fixture proved a_static 0 "$STATIC"
fixture proved b_incomplete 1 "$OD1"
fixture mutant m_refuted 1 "$REFUTED"
fixture mutant m_od1 1 "$OD1"
run_quick
rc=$?
[[ $rc == 0 ]] && ok 'advisory accepts the measured refusals (rc=0)' || fail "advisory rc=$rc, expected 0"
expect_quick_row proved a_static 0 other
expect_quick_row proved b_incomplete 1 trust
expect_quick_row mutant m_refuted 1 trust
expect_quick_row mutant m_od1 1 trust
grep -Fq 'proved fixtures: 2, not verifying: 1' "$TEST_ROOT/quick.out" \
  && ok 'advisory keeps the incomplete positive visible' || fail 'advisory lost the incomplete positive'

printf 'case 6: ordinary Rust error takes priority over verifier text\n'
fixture mutant m_od1 1 "error[E0308]: mismatched types
$OD1
error: Trust strict verification failed for \`m::r3_t_default\`"
run_quick
rc=$?
[[ $rc == 1 ]] && ok 'advisory rejects a Rust tool error (rc=1)' || fail "advisory rc=$rc, expected 1"
expect_quick_row mutant m_od1 1 other

printf 'case 7: abnormal exit carrying refutation text is a tool failure\n'
fixture mutant m_od1 134 "$REFUTED
Level 0 summary: 1 failed"
run_quick
rc=$?
[[ $rc == 1 ]] && ok 'advisory rejects an abnormal exit (rc=1)' || fail "advisory rc=$rc, expected 1"
expect_quick_row mutant m_od1 134 other

printf 'case 8: an accepted mutant remains a survivor\n'
fixture mutant m_od1 0 "$STATIC"
run_quick
rc=$?
[[ $rc == 1 ]] && ok 'advisory rejects a surviving mutant (rc=1)' || fail "advisory rc=$rc, expected 1"
expect_quick_row mutant m_od1 0 other

if ((failures)); then
  printf 'trust_falsification_gate_main_test: %d FAILED\n' "$failures"
  exit 1
fi
printf 'trust_falsification_gate_main_test: all cases pass\n'
