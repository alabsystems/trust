#!/usr/bin/env python3
"""A fatal Git ancestry read must refuse even when both endpoint commits exist."""

from pathlib import Path
import re
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check_pin_regression.sh"
FIXED_BRANCH = '''        ancestry_rc=0
        git -C "$path" merge-base --is-ancestor "$new" "$old" 2>/dev/null || ancestry_rc=$?
        if [ "$ancestry_rc" -gt 1 ]; then
          problems+=("UNJUDGEABLE  $shown  (Git ancestry read failed with exit $ancestry_rc; restore its real commit history)$tag")
          fail=1
          continue
        fi
        if [ "$ancestry_rc" -eq 0 ]; then'''
ORIGINAL_BRANCH = '''        if git -C "$path" merge-base --is-ancestor "$new" "$old" 2>/dev/null; then'''


class PinRegressionAncestryTests(unittest.TestCase):
    def test_real_missing_parent_control_and_all_existing_selftests(self):
        source = SCRIPT.read_text()
        self.assertEqual(source.count(FIXED_BRANCH), 1)
        syntax = subprocess.run(
            ["bash", "-n", str(SCRIPT)], cwd=ROOT, capture_output=True, text=True, timeout=30
        )
        self.assertEqual(syntax.returncode, 0, syntax.stderr)

        # Change only the production decision back to its original form. Both
        # executions retain the same real Git fixtures and existing controls.
        original = source.replace(FIXED_BRANCH, ORIGINAL_BRANCH)
        with tempfile.TemporaryDirectory(prefix="pin-regression-ancestry-") as directory:
            mutant = Path(directory) / "original-ancestry-decision.sh"
            mutant.write_text(original)
            red = subprocess.run(
                ["bash", str(mutant), "--selftest"], cwd=ROOT,
                capture_output=True, text=True, timeout=120,
            )
            green = subprocess.run(
                ["bash", str(SCRIPT), "--selftest"], cwd=ROOT,
                capture_output=True, text=True, timeout=120,
            )
        self.assertEqual(red.returncode, 1, red.stdout + red.stderr)
        self.assertEqual(green.returncode, 0, green.stdout + green.stderr)
        summary = r"PIN-REGRESSION SELFTEST: (\d+) passed, (\d+) failed"
        bad = re.search(summary, red.stdout)
        good = re.search(summary, green.stdout)
        self.assertIsNotNone(bad, red.stdout + red.stderr)
        self.assertIsNotNone(good, green.stdout + green.stderr)
        self.assertEqual(int(bad[2]), 1, red.stdout)
        self.assertEqual(int(good[2]), 0, green.stdout)
        self.assertEqual(int(bad[1]) + 1, int(good[1]))
        self.assertIn("present endpoints with a missing intermediate commit", red.stdout)
        self.assertEqual(SCRIPT.read_text(), source)
        print(f"PIN-ANCESTRY causal original: {bad[1]} passed/{bad[2]} failed; "
              f"fixed: {good[1]} passed/{good[2]} failed", flush=True)


if __name__ == "__main__":
    unittest.main()
