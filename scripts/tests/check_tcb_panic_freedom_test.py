"""Run the real panic-counter mutation suite in landing validation."""

import pathlib
import subprocess
import unittest


class PanicRatchetTests(unittest.TestCase):
    def test_counter_and_baseline_mutations(self):
        root = pathlib.Path(__file__).resolve().parents[2]
        result = subprocess.run(
            ["bash", str(root / "scripts/tests/check_tcb_panic_freedom_test.sh")],
            cwd=root, capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r"check_tcb_panic_freedom_test: [1-9][0-9]* checks passed\n\Z")


if __name__ == "__main__":
    unittest.main()
