#!/bin/bash
# Trust: drive `trust_superiority_gate.sh` and `trust_clean_certification_gate.sh`
# against a FAKE compiler, so their row logic is tested without a stage2 trustc.
#
# WHY (SUPERIORITY-GATE-DEAD, 2026-10-06). Both gates ran `export AY_PATH=…`,
# which a verifying trustc has refused since 80a35e2c7e (2026-07-14): every
# compile died with "environment variable `AY_PATH` is an untracked Trust
# semantic/codegen control", the release rows `verify.superiority` and
# `verify.clean-certification` measured nothing for three months, and the
# clean-certification gate printed four `PASS  mutant` rows over the dead
# compiles. The fake trustc here refuses exactly like the real one when AY_PATH
# (or another refused name) reaches it, and otherwise prints the fixture's own
# text — human summary lines (`H ` lines) or JSON rows (`J ` lines, when the
# gate asks for `-Ztrust-verify-output=json`) — and exits with its `//rc=N`.
#
# Each gate is copied into a throwaway repo layout (its REPO_ROOT is its own
# parent directory), so the fixtures are the test's, not the tree's.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

SRC_ROOT=${1:-"$(cd -P "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"}
SUP_GATE="$SRC_ROOT/scripts/trust_superiority_gate.sh"
CERT_GATE="$SRC_ROOT/scripts/trust_clean_certification_gate.sh"
for g in "$SUP_GATE" "$CERT_GATE"; do
  [[ -r $g ]] || { printf 'superiority_gates_stub_test: cannot read %s\n' "$g" >&2; exit 2; }
done

TEST_ROOT=$(mktemp -d) || exit 2
TEST_ROOT=$(cd -P "$TEST_ROOT" && pwd -P) || exit 2
trap 'rm -rf -- "$TEST_ROOT"' EXIT

failures=0
fail() { printf '  FAIL  %s\n' "$*"; failures=$((failures + 1)); }
ok() { printf '  ok    %s\n' "$*"; }

REPO="$TEST_ROOT/repo"
BIN="$TEST_ROOT/toolchain/bin"
FIX="$REPO/tests/trust-falsification/superiority"
mkdir -p "$REPO/scripts/lib" "$FIX/proved" "$FIX/mutant" "$BIN" || exit 2
cp "$SUP_GATE" "$CERT_GATE" "$REPO/scripts/" || exit 2
cp "$SRC_ROOT/scripts/lib/trust_program_wire.py" "$REPO/scripts/lib/" || exit 2

cat > "$BIN/trustc" <<'FAKE'
#!/bin/sh
# Refuse like trustc's forbidden_trust_environment_key (a verifying compile).
for name in AY_PATH TY_PATH TRUST_SOLVER TRUST_VERIFY_POLICY; do
  if env | grep -q "^$name="; then
    echo "error: environment variable \`$name\` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option" >&2
    exit 1
  fi
done
if [ -e "$0.dead" ]; then
  echo 'error: environment variable `AY_PATH` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option' >&2
  exit 1
fi
fixture= json=0 prev=
for arg do
  case $arg in
    *.rs) fixture=$arg ;;
    -Ztrust-verify-output=json) json=1 ;;
    trust-verify-output=json) [ "$prev" = -Z ] && json=1 ;;
  esac
  prev=$arg
done
[ -n "$fixture" ] || exit 2
rc=$(sed -n 's,^//rc=,,p' "$fixture")
if [ "$json" -eq 1 ]; then
  sed -n 's/^J //p' "$fixture" >&2
else
  sed -n 's/^H //p' "$fixture" >&2
fi
exit "${rc:-0}"
FAKE
printf '#!/bin/sh\nexit 0\n' > "$BIN/ay"
chmod 755 "$BIN/trustc" "$BIN/ay"

fixture() { # lane name rc lines...
  local lane=$1 name=$2 rc=$3
  shift 3
  { printf '//rc=%s\n' "$rc"; printf '%s\n' "$@"; } > "$FIX/$lane/$name.rs"
}
clear_fixtures() { rm -f "$FIX"/proved/*.rs "$FIX"/mutant/*.rs; }

run() { # gate-script-name [extra env assignments...]
  local gate=$1
  shift
  env -i PATH=/usr/bin:/bin HOME="$TEST_ROOT" TMPDIR="$TEST_ROOT" TRUSTC="$BIN/trustc" "$@" \
    bash "$REPO/scripts/$gate" > "$TEST_ROOT/gate.out" 2>&1
}
expect_rc() {
  if [[ $1 == "$2" ]]; then ok "$3 (rc=$1)"; else fail "$3: rc=$1, expected $2"; dump; fi
}
expect_line() {
  if grep -Fq -- "$2" "$TEST_ROOT/gate.out"; then ok "$1"; else fail "$1: no line containing [$2]"; dump; fi
}
expect_no_line() {
  if grep -Eq -- "$2" "$TEST_ROOT/gate.out"; then fail "$1: unexpected line matching [$2]"; dump; else ok "$1"; fi
}
dump() { sed 's/^/        | /' "$TEST_ROOT/gate.out"; }

H_CLEAN='H note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)'
H_RETAINED='H note: Trust verification: 1 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)'

printf '== superiority gate ==\n'

printf 'S1: the gate hands trustc no refused variable (root cause)\n'
clear_fixtures
fixture proved p_clean 0 "$H_CLEAN"
fixture proved p_requires 0 'H note: Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 4 obligation(s)'
fixture mutant m_retained 0 "$H_RETAINED"
run trust_superiority_gate.sh
rc=$?
expect_rc "$rc" 0 'GREEN from a clean caller environment'
expect_line 'proved row' 'PASS  proved   p_clean.rs  — SUPERIOR: 2 proved'
expect_line 'assumed (requires) is static' 'PASS  proved   p_requires.rs  — SUPERIOR: 3 proved'
expect_line 'mutant row' 'PASS  mutant   m_retained.rs  — sound: not fully discharged (1 failed'
run trust_superiority_gate.sh AY_PATH=/nonexistent/ay TRUST_SOLVER=z3
rc=$?
expect_rc "$rc" 0 'GREEN although the caller exports AY_PATH and TRUST_SOLVER'

printf 'S2: a compiler that refuses every compile cannot produce a verdict\n'
touch "$BIN/trustc.dead"
run trust_superiority_gate.sh
rc=$?
rm -f "$BIN/trustc.dead"
expect_rc "$rc" 2 'exit 2'
expect_line 'cannot-run line names the refusal' 'GATE CANNOT RUN: no proved fixture printed a `Trust verification:` summary; first: p_clean.rs: error: environment variable `AY_PATH`'
expect_no_line 'no PASS row over dead compiles' '^PASS'

printf 'S3: no ay beside trustc\n'
mv "$BIN/ay" "$BIN/ay.off"
run trust_superiority_gate.sh
rc=$?
mv "$BIN/ay.off" "$BIN/ay"
expect_rc "$rc" 2 'exit 2'
expect_line 'cannot-run line names the solver' 'GATE CANNOT RUN: no executable ay solver beside trustc'

printf 'S4: the summary line is read whole\n'
clear_fixtures
fixture proved p_clean 0 "$H_CLEAN"
fixture proved p_skipped 0 'H note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 3 obligation(s)'
fixture proved p_conditional 0 "$H_CLEAN" 'H note: Trust verification: 1 conditionally discharged (NOT proved), 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)'
fixture proved p_future 0 'H note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 frobnicated out of 3 obligation(s)'
fixture proved p_short 0 'H note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)'
fixture proved p_rc1 1 "$H_CLEAN" 'H error: native typed-TrustIr lowering did not complete'
fixture mutant m_retained 0 "$H_RETAINED"
fixture mutant m_only_skipped 0 'H note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 3 obligation(s)'
fixture mutant m_silent 1 'H error[E0425]: cannot find value `x` in this scope'
run trust_superiority_gate.sh
rc=$?
expect_rc "$rc" 1 'RED'
expect_line 'clean proved row still passes' 'PASS  proved   p_clean.rs  — SUPERIOR'
expect_line 'skipped row is not superior' 'FAIL  proved   p_skipped.rs  — NOT superior: 2 proved / 0 failed / 0 unknown / 0 timed / 0 runtime-checked / 1 skipped-or-conditional / rc=0'
expect_line 'conditional line beside a clean one is not superior' 'FAIL  proved   p_conditional.rs  — NOT superior: 2 proved / 0 failed / 0 unknown / 0 timed / 0 runtime-checked / 1 skipped-or-conditional / rc=0'
expect_line 'unknown column is unparseable' 'FAIL  proved   p_future.rs  — unparseable verification summary'
expect_line 'counts short of the total are unparseable' 'FAIL  proved   p_short.rs  — unparseable verification summary'
expect_line 'clean line with rc=1 is not superior' 'FAIL  proved   p_rc1.rs  — NOT superior: 2 proved / 0 failed / 0 unknown / 0 timed / 0 runtime-checked / 0 skipped-or-conditional / rc=1'
expect_line 'skipped rows are not a retained check' 'FAIL  mutant   m_only_skipped.rs  — VACUOUS PROOF'
expect_line 'a mutant with no summary fails' 'FAIL  mutant   m_silent.rs  — no verification summary'

printf '== clean-certification gate ==\n'

# JSON rows in the compiler's shape (-Ztrust-verify-output=json).
row() { # id kind typed outcome [assurance]
  local ev=''
  [[ -n ${5-} ]] && ev=',"proof_evidence":{"suite":"trust-certify","status":"'"$4"'","strength":{"reasoning":"Constructive","assurance":"'"$5"'"}}'
  printf '{"obligation_id":"vc:f__f:%s","kind":"%s","typed_kind":"%s","outcome":"%s"%s}' "$1" "$2" "$3" "$4" "$ev"
}
fn_result() { # fixture-name rows...
  python3 -I - "$@" <<'PY'
from collections import Counter
import json
import sys

crate, *rows = sys.argv[1:]
functions = {f"{crate}::{crate}": []}
for raw in rows:
    row = json.loads(raw)
    function = f"{crate}::{row.pop('_test_function', crate)}"
    functions.setdefault(function, []).append(row)

def counts(results):
    outcomes = Counter(row["outcome"] for row in results)
    return dict(proved=outcomes["proved"], failed=outcomes["failed"],
                unknown=sum(outcomes[kind] for kind in (
                    "unknown", "timeout", "skipped", "unsupported", "canceled", "rejected")),
                timed_out=outcomes["timeout"], skipped=outcomes["skipped"],
                runtime_checked=outcomes["runtime_checked"], total=len(results))

messages = [dict(type="function_result", function=function, results=results, **counts(results))
            for function, results in functions.items()]
summary_counts = {"total_" + key: value for key, value in counts(
    [row for results in functions.values() for row in results]).items() if key != "total"}
identities = dict(schema="trustc.coverage-function-identities.v1",
                  eligible_functions=sorted(functions), processed_functions=sorted(functions))
messages.extend((
    dict(type="coverage_summary", eligible=len(functions), processed=len(functions), function_identities=identities,
         memory=dict(schema="trust-memory-summary/v1", counters={})),
    dict(type="crate_summary", functions_analyzed=len(functions), total_obligations=len(rows),
         functions_verified=sum(bool(results) and all(row["outcome"] == "proved" for row in results)
                                for results in functions.values()),
         **summary_counts),
))
for message in messages:
    print("J TRUST_JSON:" + json.dumps(dict(crate_name=crate, **message)))
PY
}
BOUNDS_CERT=$(row bounds_check:0 slice SliceBoundsCheck proved Certified)
BOUNDS_TRUSTED=$(row bounds_check:0 slice SliceBoundsCheck proved Trusted)
BOUNDS_FAILED=$(row bounds_check:1 slice SliceBoundsCheck failed)
UNREACH_CERT=$(row assertion:0 unreach Unreachable proved Certified)
ADD_CERT=$(row arithmetic_safety:1 overflow:add ArithmeticOverflow proved Certified)
# The human note the OLD gate counted (w17 printed it on the for/while/rev mutants).
H_NOTE='H note: of which 1 kernel-certified by the clean CIC kernel (zero-trust re-check)'

certifiable_fixtures() { # rev-mutant-row
  clear_fixtures
  for n in guarded_slice_bound for_range_index_bound while_range_index_bound rev_range_index_bound; do
    fixture proved "$n" 0 "$(fn_result "$n" "$BOUNDS_CERT")" "$H_NOTE"
  done
  fixture mutant guarded_slice_bound 0 "$(fn_result guarded_slice_bound "$BOUNDS_FAILED")"
  # The measured w17 shapes: a TRUE row Certified beside the refuted bounds row.
  fixture mutant for_range_index_bound 0 "$(fn_result for_range_index_bound "$UNREACH_CERT" "$BOUNDS_FAILED")" "$H_NOTE"
  fixture mutant while_range_index_bound 0 "$(fn_result while_range_index_bound "$BOUNDS_FAILED" "$ADD_CERT")" "$H_NOTE"
  fixture mutant rev_range_index_bound 0 "$(fn_result rev_range_index_bound "$UNREACH_CERT" "$1")" "$H_NOTE"
}

printf 'C1: per-obligation judgment, and no refused variable reaches trustc (root cause)\n'
certifiable_fixtures "$BOUNDS_FAILED"
run trust_clean_certification_gate.sh AY_PATH=/nonexistent/ay
rc=$?
expect_rc "$rc" 0 'GREEN although the caller exports AY_PATH'
run trust_clean_certification_gate.sh
rc=$?
expect_rc "$rc" 0 'GREEN from a clean caller environment'
expect_line 'proved row certified' 'PASS  proved   for_range_index_bound  — CLEAN-CERTIFIED: 1 bounds obligation(s)'
expect_line 'a true Certified row does not fail the mutant' \
  'PASS  mutant   for_range_index_bound  — sound: clean refused to certify the buggy bounds obligation(s) bounds_check:1(failed) (1 other row(s) Certified)'
expect_line 'a true Certified add does not fail the mutant' 'PASS  mutant   while_range_index_bound  — sound'

printf 'C2: a Certified bounds row on a mutant is a false certification\n'
certifiable_fixtures "$(row bounds_check:1 slice SliceBoundsCheck proved Certified)"
run trust_clean_certification_gate.sh
rc=$?
expect_rc "$rc" 1 'RED'
expect_line 'false certified row' 'FAIL  mutant   rev_range_index_bound  — FALSE CERTIFIED: clean certified the unsafe bounds obligation(s) bounds_check:1(proved)'

printf 'C3: a compiler that refuses every compile cannot produce a verdict\n'
certifiable_fixtures "$BOUNDS_FAILED"
touch "$BIN/trustc.dead"
run trust_clean_certification_gate.sh
rc=$?
rm -f "$BIN/trustc.dead"
expect_rc "$rc" 2 'exit 2'
expect_line 'cannot-run line names the refusal' 'GATE CANNOT RUN: no proved fixture produced a verification row; first: guarded_slice_bound: error: environment variable `AY_PATH`'
expect_no_line 'no PASS mutant row over dead compiles' '^PASS  mutant'

printf 'C4: rows that are missing, uncertified or unjudgeable fail\n'
certifiable_fixtures "$BOUNDS_FAILED"
fixture proved guarded_slice_bound 0 "$(fn_result guarded_slice_bound "$BOUNDS_TRUSTED")"
fixture proved rev_range_index_bound 0 "$(fn_result rev_range_index_bound "$BOUNDS_CERT" "$(row bounds_check:2 slice SliceBoundsCheck proved Trusted)")"
fixture mutant guarded_slice_bound 1 'J error[E0425]: cannot find value `x` in this scope'
fixture mutant while_range_index_bound 0 "$(fn_result while_range_index_bound "$ADD_CERT")"
fixture mutant for_range_index_bound 0 "$(fn_result for_range_index_bound "$(row bounds_check:1 slice SliceBoundsCheck proved Trusted)")"
run trust_clean_certification_gate.sh
rc=$?
expect_rc "$rc" 1 'RED'
expect_line 'Trusted-only bounds row is not certified' 'FAIL  proved   guarded_slice_bound  — NOT clean-certified: bounds row(s) bounds_check:0(proved) lack Certified assurance'
expect_line 'every bounds row must be certified' 'FAIL  proved   rev_range_index_bound  — NOT clean-certified: bounds row(s) bounds_check:2(proved) lack Certified assurance'
expect_line 'a mutant with no rows fails' 'FAIL  mutant   guarded_slice_bound  — compile exited 1'
expect_line 'a mutant without its bounds row fails' 'FAIL  mutant   while_range_index_bound  — no slice bounds obligation in the fixture function'
expect_line 'a mutant whose bounds row is proved fails' 'FAIL  mutant   for_range_index_bound  — fixture bounds obligation(s) bounds_check:1(proved) proved without certification'

printf 'C5: a missing mutant fixture is a failure, not a skip\n'
certifiable_fixtures "$BOUNDS_FAILED"
rm -f "$FIX/mutant/rev_range_index_bound.rs"
run trust_clean_certification_gate.sh
rc=$?
expect_rc "$rc" 1 'RED'
expect_line 'missing mutant row' 'FAIL  mutant   rev_range_index_bound  — fixture missing'

printf 'C6: an emitted mutant row cannot turn a refused compile green\n'
certifiable_fixtures "$BOUNDS_FAILED"
rev_rows=$(fn_result rev_range_index_bound "$BOUNDS_FAILED")
for failed_exit in 75 101 137; do
  fixture mutant rev_range_index_bound "$failed_exit" "$rev_rows"
  run trust_clean_certification_gate.sh
  rc=$?
  expect_rc "$rc" 1 'RED'
  expect_line 'refused or crashed mutant compile fails' "FAIL  mutant   rev_range_index_bound  — compile exited $failed_exit"
  expect_no_line 'no PASS over the refused mutant' '^PASS  mutant   rev_range_index_bound'
done

printf 'C7: mutant evidence requires its complete, reconciled wire\n'
for wire in "$(printf '%s\n' "$rev_rows" | sed '$d')" \
            "$(fn_result for_range_index_bound "$BOUNDS_FAILED")" \
            "$(printf '%s\n' "$rev_rows" | sed 's/"total_failed": 1/"total_failed": 0/')"; do
  fixture mutant rev_range_index_bound 0 "$wire"
  run trust_clean_certification_gate.sh
  rc=$?
  expect_rc "$rc" 1 'RED'
  expect_line 'bad wire refuses' 'FAIL  mutant   rev_range_index_bound  — invalid verification wire:'
  expect_no_line 'no PASS over incomplete or mismatched evidence' '^PASS  mutant   rev_range_index_bound'
done

printf 'C8: evidence belongs to the fixture body and the reported obligation\n'
certifiable_fixtures "$BOUNDS_FAILED"
nested_cert="${BOUNDS_TRUSTED%?}"',"diagnostic":{"assurance":"Certified"}}'
helper_cert="${BOUNDS_CERT%?}"',"_test_function":"helper"}'
helper_failed="${BOUNDS_FAILED%?}"',"_test_function":"helper"}'
conflicting_status=$(printf '%s\n' "$BOUNDS_CERT" | sed 's/"status":"proved"/"status":"failed"/')
fixture proved guarded_slice_bound 0 "$(fn_result guarded_slice_bound "$nested_cert")"
fixture proved for_range_index_bound 0 "$(fn_result for_range_index_bound "$helper_cert")"
fixture proved while_range_index_bound 0 "$(fn_result while_range_index_bound "$conflicting_status")"
fixture mutant rev_range_index_bound 0 "$(fn_result rev_range_index_bound "$BOUNDS_TRUSTED" "$helper_failed")"
run trust_clean_certification_gate.sh
rc=$?
expect_rc "$rc" 1 'RED for body and assurance mismatches'
expect_line 'nested assurance cannot certify its containing row' 'FAIL  proved   guarded_slice_bound  — NOT clean-certified'
expect_line 'a helper cannot replace the fixture bounds obligation' 'FAIL  proved   for_range_index_bound  — no slice bounds obligation in the fixture function'
expect_line 'conflicting proof status refuses certification' 'FAIL  proved   while_range_index_bound  — inconsistent Certified outcome or proof status'
expect_line 'a helper cannot refute the mutant fixture' 'FAIL  mutant   rev_range_index_bound  — fixture bounds obligation'
expect_no_line 'mismatched rows cannot pass' '^PASS  (proved   (guarded_slice_bound|for_range_index_bound|while_range_index_bound)|mutant   rev_range_index_bound)'

if ((failures)); then
  printf 'superiority_gates_stub_test: %d FAILED\n' "$failures"
  exit 1
fi
printf 'superiority_gates_stub_test: all cases pass\n'
