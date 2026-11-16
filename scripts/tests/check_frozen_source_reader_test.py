#!/usr/bin/env python3
"""The source citation reader keeps real committed-tree freeze refusals."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


GATE = Path(__file__).resolve().parents[1] / "check_frozen_files.sh"


class SourceReaderTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="freeze source reader ")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.env = dict(os.environ)
        self.env.pop("TRUST_PUSHED_REFS", None)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.name", "Freeze reader fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "core.hooksPath", "/dev/null")
        (self.root / "scripts").mkdir()
        (self.root / "src").mkdir()
        shutil.copyfile(GATE, self.root / "scripts/check_frozen_files.sh")
        # A real fallback invocation is observable without starting any compiler.
        (self.root / "scripts/oracle_freeze_facts.sh").write_text(
            '#!/bin/sh\nprintf "called\\n" >> "$(dirname "$0")/reader-called"\nexit 91\n'
        )
        (self.root / "src/frozen.rs").write_text("pub fn value() -> u8 { 1 }\n")
        self.git("add", ".")
        self.git("commit", "-qm", "pin the original source")
        pin = self.git("rev-parse", "HEAD:src/frozen.rs").strip()
        (self.root / "src/frozen.rs").write_text("pub fn value() -> u8 { 2 }\n")
        moved = self.git("hash-object", "-w", "src/frozen.rs").strip()
        (self.root / "src/frozen_tests.rs").write_text(
            "#[test]\nfn the_pin_holds() {}\n"
        )
        (self.root / "scripts/frozen-files.txt").write_text(
            f"src/frozen.rs|{pin}|BYTE-IDENTICAL|fixture\n"
        )
        (self.root / "scripts/frozen-waivers.txt").write_text(
            "# prose-only-max: 0\n# prose-residual-max: 0\n"
            f"src/frozen.rs|{moved}|2026-01-01|fixture|refuses more. "
            "PIN-DELTA: +1/-1. ENFORCED-BY: src/frozen_tests.rs::the_pin_holds\n"
        )
        self.commit("record the exact moved source and its actual test")

    def git(self, *args):
        result = subprocess.run(
            ["git", *args], cwd=self.root, env=self.env,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=True,
        )
        return result.stdout

    def commit(self, message):
        self.git("add", ".")
        self.git("commit", "-qm", message)

    def compare_readers(self, expected, finding, pushed_refs=None):
        marker = self.root / "scripts/reader-called"
        results = []
        for mode in ["--check-source", "--check"]:
            marker.unlink(missing_ok=True)
            env = dict(self.env)
            if pushed_refs is not None:
                env["TRUST_PUSHED_REFS"] = pushed_refs
            result = subprocess.run(
                ["bash", "scripts/check_frozen_files.sh", mode],
                cwd=self.root, env=env, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
            self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
            self.assertIn(finding, result.stdout)
            if mode == "--check-source":
                self.assertFalse(marker.exists(), "source mode launched the compiled reader")
            elif pushed_refs is None:
                self.assertTrue(marker.exists(), "control never exercised the real fallback")
            results.append(result.stdout)
        self.assertEqual(results[0], results[1], "reader choice changed the gate's findings")

    def test_real_cited_waiver_passes_without_launching_compiled_reader(self):
        self.compare_readers(0, "FREEZE GATE: GREEN")

    def test_committed_missing_test_still_refuses(self):
        (self.root / "src/frozen_tests.rs").write_text("fn the_pin_holds() {}\n")
        self.commit("remove the test attribute but keep the claimed citation")
        self.compare_readers(1, "UNRESOLVED")

    def test_unpeelable_push_subject_still_refuses(self):
        refs = "refs/heads/main " + "1" * 40 + " refs/heads/main " + "0" * 40
        self.compare_readers(2, "FREEZE GATE: RED", refs)


if __name__ == "__main__":
    unittest.main()
