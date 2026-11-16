#!/usr/bin/env bash
# The `scripts/tests/` suite as one gate.
#
# These are the self-tests of the build/bootstrap/gate scripts themselves — the
# only thing standing between a silently broken `recreate_bootstrap.py` or
# `check_seed_freshness.py` and a build that fails for a reason nobody can read.
# The suite is the DIRECTORY, not a hand-maintained list, so a new test is
# picked up by existing; a list here would be one more thing to forget.
#
# A zero-test run is a failure: an empty directory must not read as green.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

PYTHON_BIN=""
for candidate in python3.14 python3.13 python3.12 python3.11 python3 python; do
  if command -v "$candidate" >/dev/null 2>&1; then PYTHON_BIN="$candidate"; break; fi
done
if [ -z "$PYTHON_BIN" ]; then
  echo "script tests: no python3 on PATH" >&2
  exit 2
fi

# Several tests import their siblings as `from scripts.tests import ...` (the
# completion-gate suite does, and more will), which needs the REPO ROOT on
# sys.path. Running `python3 scripts/tests/<name>.py` puts only scripts/tests/
# there, so those tests died with `ModuleNotFoundError: No module named
# 'scripts'` — a harness defect that read as a test defect (2026-09-27,
# docs/KNOWN_HAZARDS.md). Prepend the root, keeping any caller's PYTHONPATH; the
# working directory is already the root. -B: a test run writes no bytecode into
# the tree.
export PYTHONPATH="$REPO_ROOT${PYTHONPATH:+:$PYTHONPATH}"

TOTAL=0
PASSED=0
FAILED_TESTS=()

# The Trust core checkers' tests read pinned external sources (MiniRust, the Reference, the
# FLS, a-mir-formality, the RFCs, rust-lang/rust's library) from a durable cache and never
# fetch themselves. Fill the cache first; it is idempotent and costs nothing once filled. A
# failed fetch is not hidden: the tests that need the sources then fail naming the command.
if [ -f scripts/trust_core/fetch_sources.py ]; then
  "$PYTHON_BIN" scripts/trust_core/fetch_sources.py \
    || echo "script tests: fetch_sources.py failed; the Trust core tests will report the missing sources" >&2
fi

for test in scripts/tests/*_test.py scripts/tests/*_test.sh; do
  [ -f "$test" ] || continue
  TOTAL=$((TOTAL + 1))
  echo "=== $test ==="
  case "$test" in
    *.py) runner=("$PYTHON_BIN" -B "$test") ;;
    *)    runner=(bash "$test") ;;
  esac
  if "${runner[@]}" </dev/null; then
    PASSED=$((PASSED + 1))
    echo "--- $test PASS"
  else
    status=$?
    FAILED_TESTS+=("$test(exit=$status)")
    echo "--- $test FAIL exit=$status"
  fi
done

if [ "$TOTAL" -eq 0 ]; then
  echo "script tests: none found under scripts/tests — an empty suite is not a pass" >&2
  exit 2
fi

# `*_live.py` files are DRIVERS of a real, built compiler, named on their own
# command line (--trustc, --sysroot, ...); this suite has none to give them, so
# it does not run them. Two such drivers were named `*_test.py` until
# 2026-09-27 and exited 2 here on every run (argparse), which kept this
# aggregate red by construction. Not running them is printed, never silent;
# scripts/check_gate_lane_coverage.py:MANUAL_ONLY records each one's reason.
echo
for driver in scripts/tests/*_live.py; do
  [ -f "$driver" ] || continue
  echo "script tests: NOT RUN (live driver, needs an explicit compiler): $driver"
done

echo
echo "script tests: $PASSED/$TOTAL passed"
if [ "${#FAILED_TESTS[@]}" -ne 0 ]; then
  printf 'script tests FAIL: %s\n' "${FAILED_TESTS[*]}" >&2
  exit 1
fi
echo "script tests: PASS"
