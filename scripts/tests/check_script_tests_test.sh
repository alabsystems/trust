#!/usr/bin/env bash
# The import-path proof for `scripts/check_script_tests.sh`.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# `scripts/` is a package (it has an `__init__.py`), and script tests import
# their subjects as `from scripts import X` / `from scripts.tests import Y`.
# The runner invokes each test as `python scripts/tests/<x>.py`, which puts
# `scripts/tests/` — not the repository root — at sys.path[0]; unless the
# runner supplies the root, every such import dies with
# `ModuleNotFoundError: No module named 'scripts'` and the suite cannot be
# green however correct the code under test is (measured 2026-09-24: three
# tests, one at import time and two inside test methods).
#
# The runner is exercised on a throwaway repository laid out like this one, so
# the assertion is about the runner, not about which real tests happen to
# insert the path themselves.
set -euo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
RUNNER="$REPO_ROOT/scripts/check_script_tests.sh"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

PASSED=0
fail() { printf 'check_script_tests_test: %s\n' "$*" >&2; exit 1; }
ok()   { PASSED=$((PASSED + 1)); printf '  ok  %s\n' "$*"; }

[ -f "$RUNNER" ] || fail "runner is missing: $RUNNER"

R="$TMP/repo"
mkdir -p "$R/scripts/tests"
cp "$RUNNER" "$R/scripts/check_script_tests.sh"
: >"$R/scripts/__init__.py"
printf 'VALUE = 42\n' >"$R/scripts/subject.py"
printf 'HELPER = "shared"\n' >"$R/scripts/tests/shared_fixture.py"

# A module-level package import, as completion_gate_malformed_input_test does.
cat >"$R/scripts/tests/top_level_import_test.py" <<'EOF'
import unittest
from scripts import subject

class T(unittest.TestCase):
    def test_value(self):
        self.assertEqual(subject.VALUE, 42)

if __name__ == "__main__":
    unittest.main()
EOF
# A lazy import of a sibling test module, as completion_gates_g1_test does.
cat >"$R/scripts/tests/lazy_import_test.py" <<'EOF'
import unittest

class T(unittest.TestCase):
    def test_sibling(self):
        from scripts.tests import shared_fixture
        self.assertEqual(shared_fixture.HELPER, "shared")

if __name__ == "__main__":
    unittest.main()
EOF

# Run from an unrelated directory with no inherited PYTHONPATH: the runner, not
# the caller's environment, must make the package importable.
set +e
(cd "$TMP" && env -u PYTHONPATH bash "$R/scripts/check_script_tests.sh") \
  >"$TMP/run.out" 2>&1
rc=$?
set -e
if grep -q "No module named 'scripts'" "$TMP/run.out"; then
  fail "the runner does not put the repository root on the import path:
$(cat "$TMP/run.out")"
fi
ok "no test fails to import the scripts package"
[ "$rc" -eq 0 ] || fail "the runner must pass a suite whose tests pass, got $rc:
$(cat "$TMP/run.out")"
grep -q 'script tests: 2/2 passed' "$TMP/run.out" \
  || fail "expected 2/2 passed:
$(cat "$TMP/run.out")"
ok "both package-importing tests pass under the runner"

# Negative control: a genuinely failing test must still fail the suite, so the
# fix above cannot have been bought by swallowing failures.
cat >"$R/scripts/tests/red_test.py" <<'EOF'
import sys
sys.exit(3)
EOF
set +e
(cd "$TMP" && env -u PYTHONPATH bash "$R/scripts/check_script_tests.sh") \
  >"$TMP/red.out" 2>&1
rc=$?
set -e
[ "$rc" -eq 1 ] || fail "a failing test must fail the suite with 1, got $rc"
grep -q 'script tests: 2/3 passed' "$TMP/red.out" || fail "expected 2/3 passed:
$(cat "$TMP/red.out")"
ok "a failing test still fails the suite"

printf 'check_script_tests_test: %d checks passed\n' "$PASSED"
