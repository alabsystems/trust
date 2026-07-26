#!/usr/bin/env bash
# trust_kernel_derivation_lane.sh — the Clean-kernel re-derivation SLOW LANE.
#
# `crates/trust-certify` carries 88 `#[ignore]`d tests that each build a whole
# `clean_verify::spec::Specification`, FULLY kernel-type-check it, then
# re-derive and kernel-check a proof term — plus the tamper/relineage twins that
# prove the re-check is discriminating. They are the strongest evidence in the
# repo that the Certified tier is real (the SMT solver is outside the trusted
# base; the CIC kernel re-checks), and they are the most expensive tests here by
# two orders of magnitude.
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

# The workspace needs RUSTC_BOOTSTRAP for its nightly features, and an unbounded
# cargo job count gets this host's build OOM-killed.
export RUSTC_BOOTSTRAP=1
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-6}"

echo "=== Clean-kernel re-derivation lane ==="
echo "Building trust-certify test binary (release) …"
if ! cargo test --release --manifest-path crates/Cargo.toml -p trust-certify --lib --no-run; then
  echo "FAIL: could not build the trust-certify test binary." >&2
  exit 1
fi

# `cargo test --no-run` prints the binary path, but parsing its human output is
# brittle; ask cargo for the machine-readable artifact instead.
TEST_BIN="$(cargo test --release --manifest-path crates/Cargo.toml -p trust-certify --lib \
  --no-run --message-format=json 2>/dev/null \
  | sed -n 's/.*"executable":"\([^"]*\)".*/\1/p' | tail -1)"
if [ -z "$TEST_BIN" ] || [ ! -x "$TEST_BIN" ]; then
  echo "FAIL: could not locate the built trust-certify test binary." >&2
  exit 1
fi
echo "Test binary: $TEST_BIN"

mapfile -t TESTS < <("$TEST_BIN" --list --ignored 2>/dev/null \
  | sed -n 's/: test$//p' \
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

running=0
for test_name in "${TESTS[@]}"; do
  run_one "$test_name" &
  running=$((running + 1))
  if [ "$running" -ge "$JOBS" ]; then
    wait -n 2>/dev/null || wait
    running=$((running - 1))
  fi
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
