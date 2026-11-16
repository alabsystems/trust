#!/usr/bin/env bash
# trust_kernel_derivation_lane.sh — the Clean-kernel re-derivation SLOW LANE.
#
# `crates/trust-certify` carries dozens of `#[ignore]`d tests that each build a whole
# `clean_verify::spec::Specification`, FULLY kernel-type-check it, then
# re-derive and kernel-check a proof term — plus the tamper/relineage twins that
# prove the re-check is discriminating. They are the strongest evidence in the
# repo that the Certified tier is real (the SMT solver is outside the trusted
# base; the CIC kernel re-checks), and they are the most expensive tests here by
# two orders of magnitude. (The exact set is enumerated at run time from the test
# binary, not listed here — `--list` prints it. A hard-coded count in this header
# said 88 while the tree held 93, which is what a number in a steering comment
# does.)
#
# Measured 2026-07-24 on this host (release, one test per process):
#
#   checker_core::lift_instantiate_swap_checker_core_closes                753 s
#   checker_core::relineaged_sorry_beta_proof_..._are_rejected             484 s
#   reducer_universal_composition::beta_iota_gating_reflection_kernel_...  1105 s
#   checker_core_is_whnf::whnf_identity_public_api_is_consumer_indep.       555 s
#   checker_core_lemma::all_pinned_checker_core_authority_closures...       159 s
#
# and `reducer_universal_composition`'s full composite is self-documented at
# ~3.5 h. The lane is therefore an overnight-to-multi-day run — it CANNOT live
# in `targo trust gate scripts` or `check_all.sh`, which must stay minutes long,
# and un-ignoring these would wedge `targo test --workspace --lib`. Naming the
# lane is the honest alternative to both: the tests stay ignored by default, and
# this script is the thing that actually runs them.
#
# What does NOT belong here: a test that only reads a sealed MIR fixture and
# asserts a structural property costs microseconds. Nineteen such tests carried
# the same blanket `#[ignore]` and so ran nowhere at all; they are inline again.
# Before adding `#[ignore]` to anything, measure it.
#
# THE MIDDLE RUNG — `scripts/trust_control_canary.sh` (~210 s of test). Between
# "microseconds, inline" and "hours, overnight" sits one question that must not
# wait for an overnight run: are the anti-masquerade controls the `is_whnf` mint
# is GATED on still DEMONSTRABLE, so a certificate still issues at all? Control 3
# pinned a positionally generated reflected-env constant, that constant drifted,
# and every `is_whnf` certificate was withheld from July until 2026-08-23 with
# nothing reporting it — every test on the path was ignored into THIS lane, which
# is exactly as often as this lane runs. The canary pays one `Specification::new()`
# (99.5% of its cost) and answers that one question. It is not a substitute for
# the derivations below: it never re-checks a serialized certificate through an
# independently rebuilt spec and never exercises tamper/relineage rejection. This
# lane also selects it, since it is `#[ignore]`d in the same crate.
# Write-up: reports/2026-08-23-is-whnf-mint-blocked-by-control-3.md.
#
# RELEASE is not an optimization here. The kernel derivations are compute-bound;
# a debug build makes the same lane multiples longer, which is the difference
# between "runs overnight" and "never runs".
#
# Usage:
#   scripts/trust_kernel_derivation_lane.sh              # the whole lane
#   scripts/trust_kernel_derivation_lane.sh checker_core_is_whnf   # one group
#   scripts/trust_kernel_derivation_lane.sh --list       # what would run
#
# A bare substring argument is a libtest filter, which is how you shard this by
# hand across machines or re-run a single failure. Parallelism defaults to 4
# processes (each derivation is single-threaded and memory-hungry); override
# with TRUST_KERNEL_LANE_JOBS.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

JOBS="${TRUST_KERNEL_LANE_JOBS:-4}"
FILTER=""
LIST_ONLY=0
case "${1:-}" in
  --list) LIST_ONLY=1 ;;
  -h|--help|help)
    awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "${BASH_SOURCE[0]}"
    exit 0
    ;;
  -*) echo "Unknown option: $1 (use --list, --help, or a test-name filter)" >&2; exit 2 ;;
  "") ;;
  *) FILTER="$1" ;;
esac

# `targo --unverified`, not `cargo`: under the `trust` toolchain stock cargo has
# no per-unit verification policy, so it verifies every dependency as its own
# primary crate and dies on obligations unrelated to this lane. The workspace's
# nightly features no longer need RUSTC_BOOTSTRAP either — the toolchain targo
# pins is `channel = "trust"`, which opens them natively. An unbounded job count
# still gets this host's build OOM-killed. Converted 2026-09-12 with the gate
# manifest.
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-6}"

echo "=== Clean-kernel re-derivation lane ==="
echo "Building trust-certify test binary (release) …"
if ! targo --unverified test --release --manifest-path Cargo.toml -p trust-certify --lib --no-run; then
  echo "FAIL: could not build the trust-certify test binary." >&2
  exit 1
fi

# `targo test --no-run` prints the binary path, but parsing its human output is
# brittle; ask for the machine-readable artifact instead. targo IS upstream cargo
# renamed, so `--message-format=json` emits the identical `"executable"` field.
TEST_BIN="$(targo --unverified test --release --manifest-path Cargo.toml -p trust-certify --lib \
  --no-run --message-format=json 2>/dev/null \
  | sed -n 's/.*"executable":"\([^"]*\)".*/\1/p' | tail -1)"
if [ -z "$TEST_BIN" ] || [ ! -x "$TEST_BIN" ]; then
  echo "FAIL: could not locate the built trust-certify test binary." >&2
  exit 1
fi
echo "Test binary: $TEST_BIN"

# Portable to bash 3.2, which is the only `bash` on a stock macOS host and the
# one the manifest row's `bash scripts/...` resolves to there. `mapfile` is
# bash 4+: under 3.2 it is "command not found", TESTS stays unset, and `set -u`
# killed the lane before it ran a single test — measured 2026-09-27, which is
# why `slow.kernel-derivation` had never recorded a green run.
#
# Selected by the REASON a test is ignored, not merely by being ignored. The
# crate ignores tests for other reasons too — measured 2026-09-27: 77 multi-minute
# kernel re-derivations and 11 multi-hour composites belong here, but an opt-in
# mint-gate CANARY and a test that needs a retained compiler artifact
# (TRUST_SCALAR_ACTUAL_IR_BINARY) were swept in as well, and the latter fails with
# `NotPresent` on every run, so selecting "all ignored" could never be green even
# with every kernel re-check closing. libtest's JSON listing carries each test's
# ignore message; that is read, and anything else is printed, never silently run.
KERNEL_REASONS_PY='("multi-minute clean-verify kernel-recheck derivation", "multi-hour kernel-composite derivation")'
LISTING="$("$TEST_BIN" --list --ignored --format json -Z unstable-options 2>/dev/null)" || LISTING=""
if [ -z "$LISTING" ]; then
  echo "FAIL: could not list the ignored tests with their reasons (libtest --format json)." >&2
  echo "      Refusing to guess the selection: running every ignored test sweeps in tests" >&2
  echo "      that need artifacts this lane does not provide." >&2
  exit 1
fi
select_by_reason() {  # $1 = "in" or "out"
  printf '%s\n' "$LISTING" | python3 -c '
import json, sys
wanted = sys.argv[1] == "in"
prefixes = '"$KERNEL_REASONS_PY"'
for line in sys.stdin:
    try:
        event = json.loads(line)
    except ValueError:
        continue
    if event.get("type") != "test":
        continue
    reason = event.get("ignore_message") or ""
    if reason.startswith(prefixes) == wanted:
        print(event["name"] if wanted else event["name"] + "  -- " + reason[:90])
' "$1"
}
OTHER_IGNORED="$(select_by_reason out)"
if [ -n "$OTHER_IGNORED" ]; then
  echo "Not this lane's (ignored for another reason, not run here):"
  printf '%s\n' "$OTHER_IGNORED" | sed 's/^/  /'
fi
TESTS=()
while IFS= read -r test_name; do
  [ -n "$test_name" ] && TESTS+=("$test_name")
done < <(select_by_reason in \
  | { if [ -n "$FILTER" ]; then grep -F -- "$FILTER"; else cat; fi } \
  | LC_ALL=C sort)

if [ "${#TESTS[@]}" -eq 0 ]; then
  echo "FAIL: no ignored kernel-derivation tests matched${FILTER:+ filter '$FILTER'}." >&2
  echo "DETAIL: this lane exists to run them; an empty selection means the lane is" >&2
  echo "        silently covering nothing, which is the failure it guards against." >&2
  exit 1
fi

if [ "$LIST_ONLY" -eq 1 ]; then
  printf '%s\n' "${TESTS[@]}"
  echo "----------------"
  echo "${#TESTS[@]} kernel-derivation test(s) would run at $JOBS at a time."
  exit 0
fi

echo "Running ${#TESTS[@]} kernel-derivation test(s), $JOBS at a time."
echo "Expect HOURS: ~12 min each, and the reducer_universal_composition"
echo "composites ~3.5 h each. Results stream below as each finishes."
echo ""

RESULTS="$(mktemp "${TMPDIR:-/tmp}/kernel-lane-results.XXXXXX")"
LOGDIR="$(mktemp -d "${TMPDIR:-/tmp}/kernel-lane-logs.XXXXXX")"
trap 'rm -f "$RESULTS"' EXIT
LANE_START=$(date +%s)

run_one() {
  local test_name="$1" start rc elapsed log
  log="$LOGDIR/${test_name//:/_}.log"
  start=$(date +%s)
  "$TEST_BIN" --ignored --exact "$test_name" --test-threads=1 > "$log" 2>&1
  rc=$?
  elapsed=$(( $(date +%s) - start ))
  # libtest exits 0 when its filter selected NOTHING, so a green exit code alone
  # would let a renamed test report PASS forever. Demand the one result.
  # One line per test, appended atomically enough for a status log: short writes
  # to a pipe-free file under PIPE_BUF are not interleaved on Linux.
  if [ "$rc" -eq 0 ] && grep -q '^test result: ok\. 1 passed' "$log"; then
    printf 'PASS %6ss  %s\n' "$elapsed" "$test_name" | tee -a "$RESULTS"
  elif [ "$rc" -eq 0 ]; then
    printf 'FAIL %6ss  %s  (ran no test — filter selected nothing, log: %s)\n' \
      "$elapsed" "$test_name" "$log" | tee -a "$RESULTS"
  else
    printf 'FAIL %6ss  %s  (rc=%s, log: %s)\n' "$elapsed" "$test_name" "$rc" "$log" | tee -a "$RESULTS"
  fi
}

# A rolling window of $JOBS, portable to bash 3.2. The old limiter used
# `wait -n` (bash 4.3+) with a `|| wait` fallback; under 3.2 that fallback waits
# for EVERY job yet the counter only drops by one, so after the first batch the
# lane ran one test at a time — roughly $JOBS times slower on a lane measured in
# hours. Counting live jobs directly is correct on every bash.
for test_name in "${TESTS[@]}"; do
  while [ "$(jobs -rp | wc -l | tr -d ' ')" -ge "$JOBS" ]; do
    sleep 2
  done
  run_one "$test_name" &
done
wait

LANE_ELAPSED=$(( $(date +%s) - LANE_START ))
passed=$(grep -c '^PASS' "$RESULTS" || true)
failed=$(grep -c '^FAIL' "$RESULTS" || true)

echo ""
echo "=== Clean-kernel re-derivation lane: $passed passed, $failed failed in ${LANE_ELAPSED}s ==="
if [ "$failed" -ne 0 ]; then
  echo ""
  grep '^FAIL' "$RESULTS"
  echo ""
  echo "FAIL: a kernel re-derivation did not close. Logs: $LOGDIR"
  echo "      Treat this as soundness-critical: these tests are the evidence that"
  echo "      the Certified tier's kernel re-check is real and discriminating."
  exit 1
fi
if [ "$passed" -ne "${#TESTS[@]}" ]; then
  echo "FAIL: expected ${#TESTS[@]} results, recorded $passed. The lane did not run to completion." >&2
  exit 1
fi
rm -rf "$LOGDIR"
echo "PASS: every selected kernel re-derivation closed."
exit 0
