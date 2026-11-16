"""Exercise the real self-proof driver with controlled compiler output."""

from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
GOOD_LOG = """    = note: summary: 0 trusted, 7 certified, 0 failed, 0 unknown, 0 runtime-checked, 0 skipped out of 7
  Summary: 29 proved, 0 failed, 0 runtime-checked, 6 assumed, 0 mandated, 0 contract-panic, 0 inconclusive (35 total)
  Coverage: 24/24 eligible function bodies verified (complete)
"""
BASELINE = "certified_min = 7\nproved_min = 29\nassumed_max = 6\n"


class SelfProofDriverTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="self-proof-driver-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        (self.root / "scripts").mkdir()
        (self.root / "crates").mkdir()
        (self.root / "tests/self-proof").mkdir(parents=True)
        self.script = self.root / "scripts/trust_self_verify_crate.sh"
        shutil.copyfile(ROOT / "scripts/trust_self_verify_crate.sh", self.script)
        self.baseline = self.root / "tests/self-proof/trust-semantics.baseline"
        self.baseline.write_text(BASELINE)
        self.log = self.root / "output.log"
        self.log.write_text(GOOD_LOG)
        self.calls = self.root / "calls"
        self.targo = self.root / "targo"
        self.targo.write_text("""#!/bin/sh
if [ "$1" = --unverified ] && [ "$2" = --version ]; then
    echo 'targo test fixture'; exit 0
fi
echo called >> "$SELF_PROOF_CALLS"
if [ -n "${SELF_PROOF_REPLACEMENT:-}" ]; then
    cat "$SELF_PROOF_REPLACEMENT" > "$SELF_PROOF_BASELINE"
fi
cat "$SELF_PROOF_OUTPUT"
exit "${SELF_PROOF_EXIT:-1}"
""")
        self.targo.chmod(0o755)
        self.env = dict(os.environ, TARGO=str(self.targo),
                        SELF_PROOF_OUTPUT=str(self.log), SELF_PROOF_CALLS=str(self.calls),
                        SELF_PROOF_BASELINE=str(self.baseline))
        self.env.pop("TRUST_SELF_VERIFY_CRATE", None)

    def run_driver(self, *args):
        return subprocess.run(["bash", str(self.script), *args], cwd=self.root,
                              env=self.env, text=True, capture_output=True)

    def test_complete_observation_holds_existing_ratchet(self):
        result = self.run_driver()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("RATCHET, not a strict-lane pass", result.stdout)

    def test_builtin_mutation_controls_remain_live(self):
        result = self.run_driver("--selftest")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("every assertion mutation-proved", result.stdout)
        self.assertFalse(self.calls.exists())

    def test_bad_baseline_is_refused_before_compiling(self):
        for baseline in ("", "certified_min = 7\nproved_min = 29\n",
                         BASELINE.replace("7", "oops"), BASELINE + "proved_min = 1\n",
                         BASELINE.replace("= ", "= invalid="),
                         BASELINE.replace("29", "-1"),
                         BASELINE.replace("29", "9" * 80)):
            with self.subTest(baseline=baseline):
                self.baseline.write_text(baseline)
                self.calls.unlink(missing_ok=True)
                result = self.run_driver()
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertFalse(self.calls.exists(), "invalid baseline wasted a verified compile")

    def test_missing_or_invalid_observation_is_refused(self):
        for output in (GOOD_LOG.replace("  Summary:", "  Unknown:"),
                       GOOD_LOG.replace("29 proved", "many proved"),
                       GOOD_LOG.replace("29 proved", "-29 proved"),
                       GOOD_LOG.replace("6 assumed", "-6 assumed"),
                       GOOD_LOG.replace("7 certified", "-7 certified"),
                       GOOD_LOG.replace("6 assumed", "many assumed"),
                       GOOD_LOG.replace("0 failed", "many failed")):
            with self.subTest(output=output):
                self.log.write_text(output)
                result = self.run_driver()
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)

    def test_zero_bodies_is_not_self_verification(self):
        self.baseline.write_text("certified_min = 0\nproved_min = 0\nassumed_max = 0\n")
        self.log.write_text(GOOD_LOG.replace("7 certified", "0 certified")
                            .replace("29 proved", "0 proved").replace("6 assumed", "0 assumed")
                            .replace("24/24", "0/0"))
        result = self.run_driver()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)

    def test_update_uses_complete_observation_and_does_not_weaken_ratchet(self):
        self.baseline.write_text("# Keep historical evidence.\n" + BASELINE)
        self.log.write_text(GOOD_LOG.replace("7 certified", "8 certified").replace("29 proved", "30 proved"))
        result = self.run_driver("--update")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("certified_min = 8", self.baseline.read_text())
        self.assertRegex(self.baseline.read_text(), r"proved_min\s*= 30")
        self.assertIn("# Keep historical evidence.", self.baseline.read_text())
        before = self.baseline.read_bytes()
        for output in (GOOD_LOG, GOOD_LOG.replace("6 assumed", "7 assumed"),
                       GOOD_LOG.replace("24/24", "23/24").replace("(complete)", "(incomplete)")):
            with self.subTest(output=output):
                self.log.write_text(output)
                result = self.run_driver("--update")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(self.baseline.read_bytes(), before)

    def test_update_can_create_first_baseline_after_nonvacuous_measurement(self):
        self.baseline.unlink()
        result = self.run_driver("--update")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("certified_min = 7", self.baseline.read_text())

    def test_abnormal_compiler_exit_is_not_a_ratchet_pass(self):
        for code in (2, 137):
            with self.subTest(code=code):
                self.env["SELF_PROOF_EXIT"] = str(code)
                result = self.run_driver()
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)

    def test_update_preserves_a_baseline_changed_during_compilation(self):
        replacement = self.root / "replacement"
        stronger = "certified_min = 100\nproved_min = 1000\nassumed_max = 0\n"
        replacement.write_text(stronger)
        self.env["SELF_PROOF_REPLACEMENT"] = str(replacement)
        for initially_present in (True, False):
            with self.subTest(initially_present=initially_present):
                if initially_present:
                    self.baseline.write_text(BASELINE)
                else:
                    self.baseline.unlink()
                result = self.run_driver("--update")
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertEqual(self.baseline.read_text(), stronger)

    def test_parallel_update_lock_refuses_before_compiling(self):
        lock = Path(str(self.baseline) + ".lock")
        lock.mkdir()
        result = self.run_driver("--update")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertTrue(lock.is_dir(), "another update's lock must be preserved")
        self.assertFalse(self.calls.exists())

    def test_normal_run_refuses_a_changed_baseline(self):
        replacement = self.root / "replacement"
        replacement.write_text(BASELINE.replace("29", "1000"))
        self.env["SELF_PROOF_REPLACEMENT"] = str(replacement)
        result = self.run_driver()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(self.baseline.read_bytes(), replacement.read_bytes())

    def test_unknown_arguments_are_refused_without_compiling(self):
        for args in (("--unknown",), ("--update", "extra")):
            result = self.run_driver(*args)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertFalse(self.calls.exists())


if __name__ == "__main__":
    unittest.main()
