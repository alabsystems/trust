#!/usr/bin/env python3
"""Exercise the real mint exit handlers with inert, owned lifecycle helpers."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class FailedMintEvidenceTests(unittest.TestCase):
    def run_handler(self, ending: str, expected_status: int, retained: bool, at_provenance: bool = False):
        bash = shutil.which("bash")
        if bash is None:
            self.skipTest("mint entrypoint requires Bash")
        script = (ROOT / "scripts/mint_and_prove_seed.sh").read_text()
        # Execute the production handlers, with no bootstrap, Git or compiler.
        handlers = script[script.index("drop_repin() {"):script.index("trap cleanup EXIT")]
        with tempfile.TemporaryDirectory(prefix="mint-exit-evidence-") as temporary:
            root = Path(temporary)
            work = root / "build/.mint-and-prove.fixture"
            work.mkdir(parents=True)
            evidence = work / "stage2-ddc-seed.json"
            evidence.write_bytes(b"original-independent-observation\n")
            sentinel = root / "product-source"
            sentinel.write_bytes(b"untouched-source\n")
            calls = root / "calls.jsonl"
            helper = root / "helper.py"
            helper.write_text(
                "import json, pathlib, shutil, sys\n"
                f"with pathlib.Path({str(calls)!r}).open('a') as f: "
                "f.write(json.dumps(sys.argv[1:])+'\\n')\n"
                "if sys.argv[1] == 'cleanup-work': shutil.rmtree(sys.argv[3])\n"
            )
            bindings = {"ROOT": root, "WORK": work, "MINT_BUILD": root / "build/mint",
                        "HELPER": helper, "PYTHON_BIN": sys.executable,
                        "CHILD_PID": "", "REPIN_COMMIT": "", "RESUME_AT_PROVENANCE": int(at_provenance)}
            prefix = "\n".join(f"{key}={shlex.quote(str(value))}" for key, value in bindings.items())
            completed = subprocess.run(
                [bash, "-c", "set -euo pipefail\n" + prefix + "\n" + handlers + "\n" + ending],
                env={"PATH": os.defpath}, capture_output=True, text=True, timeout=30,
            )
            self.assertEqual(completed.returncode, expected_status, completed.stderr)
            self.assertEqual(work.exists(), retained)
            self.assertEqual(sentinel.read_bytes(), b"untouched-source\n")
            actual = [json.loads(line) for line in calls.read_text().splitlines()]
            self.assertEqual(actual[0], ["ddc-restore", "--root", str(root), "--build", str(root / "build/mint")])
            self.assertEqual([row[0] for row in actual],
                             ["ddc-restore"] if retained else ["ddc-restore", "cleanup-work"])
            if retained:
                self.assertEqual(evidence.read_bytes(), b"original-independent-observation\n")
                self.assertIn(str(work), completed.stderr)

    def test_failed_exit_keeps_original_evidence_and_exit_status(self):
        self.run_handler("trap cleanup EXIT\nexit 1", 1, True)

    def test_signal_exit_keeps_original_evidence_and_signal_status(self):
        self.run_handler("signal_exit TERM 143", 143, True)

    def test_success_still_cleans_owned_temporary_work(self):
        self.run_handler("trap cleanup EXIT\nexit 0", 0, False)

    def test_recovered_success_preserves_the_genuine_original_work(self):
        self.run_handler("trap cleanup EXIT\nexit 0", 0, True, at_provenance=True)


if __name__ == "__main__":
    unittest.main()
