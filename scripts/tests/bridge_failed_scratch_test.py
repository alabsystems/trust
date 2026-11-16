#!/usr/bin/env python3
"""Execute the producer's actual EXIT handler on successful and failed work."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "regen-trustir-oleans.sh"


class BridgeScratch(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="bridge scratch ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        text = SCRIPT.read_text()
        # The handler reads KEEP_WORK, which the script binds (and validates)
        # from TRUST_REGEN_KEEP_WORK before any work: run that actual binding too.
        keep = text.index('KEEP_WORK="${TRUST_REGEN_KEEP_WORK:-0}"\n')
        keep_end = text.index("\nesac\n", keep) + len("\nesac\n")
        start = text.index("cleanup_bridge_work() {")
        end = text.index("\ntrap cleanup_bridge_work EXIT", start)
        self.actual = text[keep:keep_end] + text[start:end]

    def execute(self, status, env=None, keep=None, label=None):
        env = {k: v for k, v in (os.environ if env is None else env).items() if k != "TRUST_REGEN_KEEP_WORK"}
        if keep is not None:
            env["TRUST_REGEN_KEEP_WORK"] = keep
        work = self.root / ("run with spaces " + (label or str(status)))
        work.mkdir()
        (work / "actual-source-witness").write_bytes(b"preserve this failed input")
        command = 'set -euo pipefail\nWORK="$1"\n' + self.actual + '\ntrap cleanup_bridge_work EXIT\nexit "$2"\n'
        result = subprocess.run(["bash", "-c", command, "bridge-handler-probe", str(work), str(status)],
                                text=True, capture_output=True, env=env)
        return work, result

    def test_success_retires_only_owned_scratch(self):
        work, result = self.execute(0)
        self.assertEqual(result.returncode, 0)
        self.assertFalse(work.exists())
        self.assertEqual(result.stderr, "")

    def test_requested_keep_retains_successful_scratch(self):
        work, result = self.execute(0, keep="1")
        self.assertEqual(result.returncode, 0)
        self.assertTrue((work / "actual-source-witness").exists())
        self.assertIn("retained by TRUST_REGEN_KEEP_WORK=1", result.stderr)

    def test_keep_work_outside_zero_or_one_is_refused_before_any_work(self):
        for value in ("2", "yes", ""):
            with self.subTest(value=value):
                work, result = self.execute(0, keep=value, label="keep " + repr(value))
                if value == "":
                    # An empty value is the documented default, 0: cleanup runs.
                    self.assertEqual(result.returncode, 0)
                    self.assertFalse(work.exists())
                    continue
                self.assertEqual(result.returncode, 2)
                self.assertIn("TRUST_REGEN_KEEP_WORK must be 0 or 1", result.stderr)
                self.assertTrue((work / "actual-source-witness").exists())

    def test_failure_retains_exact_inputs_and_original_nonzero_status(self):
        for status in (1, 73, 130):
            with self.subTest(status=status):
                work, result = self.execute(status)
                self.assertEqual(result.returncode, status)
                self.assertEqual((work / "actual-source-witness").read_bytes(), b"preserve this failed input")
                self.assertIn(str(work), result.stderr)
                self.assertIn("failed scratch retained", result.stderr)

    def test_cleanup_io_failure_does_not_change_successful_producer_verdict(self):
        tools = self.root / "tools"
        tools.mkdir()
        rm = tools / "rm"
        rm.write_text("#!/bin/sh\nexit 9\n")
        rm.chmod(0o755)
        work, result = self.execute(0, dict(os.environ, PATH=str(tools) + ":" + os.environ["PATH"]))
        self.assertEqual(result.returncode, 0)
        self.assertTrue((work / "actual-source-witness").exists())
        self.assertIn("cleanup failed; scratch retained", result.stderr)


if __name__ == "__main__":
    unittest.main()
