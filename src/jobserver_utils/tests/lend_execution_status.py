#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Process regressions for a built lender under real build-slot protocol 1.

Run: build-slot --exclusive --cpus 1 -- python3 this-file ABSOLUTE-LENDER
The lender independently checks its inherited admission; this test creates none.
"""
import os
from pathlib import Path
import signal
import subprocess
import sys
import unittest

LENDER = None

class StatusTests(unittest.TestCase):
    def child(self, source, **kwargs):
        return subprocess.run([LENDER, sys.executable, "-I", "-S", "-c", source],
                              capture_output=True, check=False, **kwargs)

    def test_ordinary_exits_including_signal_number_twins(self):
        for code in (0, 7, 139, 143):
            with self.subTest(code=code):
                result = self.child(f"raise SystemExit({code})")
                self.assertEqual(result.returncode, code, result.stderr)

    def test_actual_child_signals(self):
        for number in (signal.SIGTERM, signal.SIGUSR1, signal.SIGKILL):
            with self.subTest(signal=number):
                result = self.child(f"import os; os.kill(os.getpid(), {int(number)})")
                self.assertEqual(result.returncode, -number, result.stderr)

    def test_inherited_ignored_disposition_cannot_hide_child_signal(self):
        previous = signal.signal(signal.SIGTERM, signal.SIG_IGN)
        try:
            result = self.child("import os,signal; signal.signal(signal.SIGTERM,signal.SIG_DFL); "
                                "os.kill(os.getpid(),signal.SIGTERM)")
        finally:
            signal.signal(signal.SIGTERM, previous)
        self.assertEqual(result.returncode, -signal.SIGTERM, result.stderr)

    def test_inherited_blocked_mask_cannot_hide_child_signal(self):
        previous = signal.pthread_sigmask(signal.SIG_BLOCK, [signal.SIGTERM])
        try:
            result = self.child("import os,signal; signal.pthread_sigmask(signal.SIG_UNBLOCK,[signal.SIGTERM]); "
                                "os.kill(os.getpid(),signal.SIGTERM)")
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous)
        self.assertEqual(result.returncode, -signal.SIGTERM, result.stderr)

    def test_unsupported_admission_refuses_before_child(self):
        env = dict(os.environ, BUILD_SLOT_CPU_PROTOCOL="2")
        result = self.child("print('child must not run'); raise SystemExit(99)", env=env)
        self.assertEqual(result.returncode, 75, result.stderr)
        self.assertEqual(result.stdout, b"")
        self.assertIn(b"a loan requires bare build-slot protocol 1", result.stderr)

if __name__ == "__main__":
    if len(sys.argv) != 2 or not Path(sys.argv[1]).is_absolute():
        raise SystemExit("usage: lend_execution_status.py ABSOLUTE-LENDER")
    LENDER = sys.argv.pop()
    unittest.main(verbosity=2)
