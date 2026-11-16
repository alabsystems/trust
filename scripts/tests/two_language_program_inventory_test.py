#!/usr/bin/env python3
"""Coverage regressions need no compiler, submodule build or network."""

import importlib.util
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check_two_language_program_inventory.py"
SPEC = importlib.util.spec_from_file_location("battery_inventory", CHECKER)
I = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(I)


class BatteryInventory(unittest.TestCase):
    def test_full_run_requires_every_fixture(self):
        expected = {"r01_positive", "r02_negative", "ir-one"}
        self.assertEqual(I.coverage_errors(expected, sorted(expected)), [])
        errors = I.coverage_errors(expected, ["r01_positive", "ir-one"])
        self.assertTrue(any("unexecuted fixtures: r02_negative" in e for e in errors))

    def test_duplicate_cannot_replace_missing_fixture(self):
        errors = I.coverage_errors({"r01_positive", "r02_negative"},
                                  ["r01_positive", "r01_positive"])
        self.assertTrue(any("duplicate rows" in e for e in errors))
        self.assertTrue(any("unexecuted fixtures" in e for e in errors))

    def test_unknown_row_and_empty_runs_refuse(self):
        self.assertTrue(I.coverage_errors({"r01_positive"}, ["r99_invented"]))
        self.assertTrue(I.coverage_errors(set(), []))
        self.assertTrue(I.coverage_errors({"r01_positive"}, [], lane="typo"))

    def test_filtered_run_is_partial_and_not_vacuous(self):
        expected = {"r01_positive", "r02_negative", "ir-one", "ir-two"}
        self.assertEqual(I.coverage_errors(expected, ["r01_positive"], only="r01_positive"), [])
        self.assertTrue(I.coverage_errors(expected, [], only="r01_positive"))
        self.assertTrue(I.coverage_errors(expected, ["r01_positive"], only="r99_typo"))
        self.assertTrue(I.coverage_errors(expected, ["ir-one"], lane="trustc-ir"))
        self.assertEqual(I.coverage_errors(expected, ["ir-one", "ir-two"], lane="trustc-ir"), [])

    def test_fixture_discovery_does_not_depend_on_registration_or_expected_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ["r01_positive", "r36_joint_cited_lean_theorem", "ir-new", "ir-audit", "__pycache__"]:
                (root / name).mkdir()
            self.assertEqual(I.fixture_names(root),
                             {"r01_positive", "r36_joint_cited_lean_theorem", "ir-new"})

    def test_real_registration_covers_all_ordinary_fixtures(self):
        harness = (ROOT / "tests/e2e_two_language_programs.sh").read_text()
        registered = re.findall(r"^row_\w+\s+(?:--\S+\s+)*(r\d+_\S+)", harness, re.M)
        expected = {name for name in I.fixture_names(ROOT / "tests/two-language-programs")
                    if name.startswith("r")}
        self.assertEqual(I.coverage_errors(expected, registered), [])
        omitted = [name for name in registered if name != "r36_joint_cited_lean_theorem"]
        self.assertTrue(any("r36_joint_cited_lean_theorem" in e
                            for e in I.coverage_errors(expected, omitted)))
        self.assertRegex(harness, r"(?m)^row_trustc_run\s+r36_joint_cited_lean_theorem\s*$")

    def test_cli_refuses_missing_fixture_and_identifies_filtered_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "r01_positive").mkdir()
            (root / "r02_negative").mkdir()
            command = [sys.executable, str(CHECKER), "--rows-dir", str(root)]
            failed = subprocess.run(command, input="r01_positive\n", text=True, capture_output=True)
            self.assertEqual(failed.returncode, 1)
            self.assertIn("unexecuted fixtures: r02_negative", failed.stderr)
            partial = subprocess.run(command + ["--only", "r01_positive"],
                                     input="r01_positive\n", text=True, capture_output=True)
            self.assertEqual(partial.returncode, 0, partial.stderr)
            self.assertIn("partial (filtered), 1/2", partial.stdout)

    def test_real_battery_footer_propagates_inventory_failure(self):
        harness = (ROOT / "tests/e2e_two_language_programs.sh").read_text()
        bookkeeping = harness[harness.index("declare -a RESULT_ROWS=()"):
                              harness.index("# Turn a raw outcome")]
        footer = harness[harness.index('echo "PASS=$PASSES RED(expected)='):]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "r01_positive").mkdir()
            (root / "r02_negative").mkdir()
            # Execute the maintained bookkeeping and footer, including their
            # real checker invocation, without running a compiler or replacing
            # either side's coverage logic with a test double.
            program = '''set -uo pipefail
TRUST_ROOT=$1
ROWS_DIR=$2
ONLY=$3
LANE=""
IDENTITY_LINE="fixture-only regression"
OUT_FILE=""
''' + bookkeeping + '''
record r01_positive trustc-run PASS "synthetic row outcome"
if [ "$4" = complete ]; then
    record r02_negative trustc-lib PASS "synthetic negative outcome"
fi
''' + footer
            command = ["bash", "-c", program, "battery-footer-test", str(ROOT), str(root)]
            missing = subprocess.run(command + ["", "missing"], text=True, capture_output=True)
            self.assertEqual(missing.returncode, 1, missing.stdout + missing.stderr)
            self.assertIn("unexecuted fixtures: r02_negative", missing.stdout)
            complete = subprocess.run(command + ["", "complete"], text=True, capture_output=True)
            self.assertEqual(complete.returncode, 0, complete.stdout + complete.stderr)
            self.assertIn("full, 2/2 fixtures executed", complete.stdout)
            filtered = subprocess.run(command + ["r01_positive", "missing"], text=True, capture_output=True)
            self.assertEqual(filtered.returncode, 0, filtered.stdout + filtered.stderr)
            self.assertIn("partial (filtered), 1/2", filtered.stdout)


if __name__ == "__main__":
    unittest.main()
