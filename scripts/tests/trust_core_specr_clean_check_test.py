#!/usr/bin/env python3
"""The specr → Clean translator's committed output, kernel-checked by Clean, with every sibling copy
compared at the revision Trust pins (RM1, scripts/trust_core/specr/regen.py `check --clean
--require-siblings`).

scripts/tests/trust_core_specr_regen_test.py judges the driver on copies and fake reports and never
runs a kernel. This module runs the real one once on the real tree: `regen.py check --clean
<clean on PATH> --require-siblings` regenerates every output, compares the copies Clean and trust-ir
hold at Trust's HEAD gitlinks, and has `clean check --json` accept every declaration of the prelude,
its vectors, the slice, the slice's vectors and every conformance theorem (each present in the report
and free of errors), with no sorry, no kernel failure and no assumption.

What it cannot run is NOT RUN, never a pass: with no `clean` on PATH, or with a sibling comparison
NOT RUN (first-party/NAME not checked out, or its object store lacks the pinned commit), the test is
skipped, so `land_gate.py validation-tests` reports the module NOT JUDGED (exit 2). A runner whose
siblings live elsewhere names their object stores in TRUST_SPECR_SIBLING_GIT
(`clean=DIR trust-ir=DIR`, passed as `--sibling-git`; the gitlinks still choose the revisions).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import os
import re
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_core" / "specr" / "regen.py"
LAST = re.compile(r"clean check: (\d+)/(\d+) declarations accepted, (\d+)/(\d+) conformance theorems "
                  r"\([^)]*\), sorry 0/0, kernel failures 0, assumptions 0 -> ok\Z")


class SpecrCleanCheckTest(unittest.TestCase):
    def test_the_committed_slice_and_its_theorems_pass_clean_at_the_pinned_siblings(self):
        clean = shutil.which("clean")
        if clean is None:
            self.skipTest("NOT RUN: no `clean` on PATH")
        stores = []
        for spec in os.environ.get("TRUST_SPECR_SIBLING_GIT", "").split():
            stores += ["--sibling-git", spec]
        proc = subprocess.run([sys.executable, "-B", str(SCRIPT), "check", "--clean", clean, "--require-siblings",
                               *stores], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                              check=False)
        out = proc.stdout + proc.stderr
        # exit 2 is also argparse's usage error: only regen's own NOT RUN verdict is a skip
        if proc.returncode == 2 and "regen: a sibling comparison was NOT RUN under --require-siblings" in proc.stdout:
            self.skipTest("NOT RUN: a sibling comparison was not run\n" + proc.stdout)
        self.assertEqual(proc.returncode, 0, out)
        lines = proc.stdout.splitlines()
        self.assertIn("regen: byte-identical", lines, out)
        siblings = [line for line in lines if re.match(r"\S+(?: RUN)?\s+(?:clean|trust-ir)@", line)]
        self.assertTrue(siblings and all(line.startswith("identical  ") for line in siblings), out)
        m = LAST.match(lines[-1])
        self.assertIsNotNone(m, out)
        self.assertEqual(m.group(1), m.group(2), out)
        self.assertEqual(m.group(3), m.group(4), out)


if __name__ == "__main__":
    unittest.main()
