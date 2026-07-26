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

TOTAL=0
PASSED=0
FAILED_TESTS=()

for test in scripts/tests/*_test.py scripts/tests/*_test.sh; do
  [ -f "$test" ] || continue
  TOTAL=$((TOTAL + 1))
  echo "=== $test ==="
  case "$test" in
    *.py) runner=("$PYTHON_BIN" "$test") ;;
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

echo
echo "script tests: $PASSED/$TOTAL passed"
if [ "${#FAILED_TESTS[@]}" -ne 0 ]; then
  printf 'script tests FAIL: %s\n' "${FAILED_TESTS[*]}" >&2
  exit 1
fi
echo "script tests: PASS"
