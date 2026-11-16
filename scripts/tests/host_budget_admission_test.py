#!/usr/bin/env python3
"""Host measurements obey the same managed admission as execution planning."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch


SOURCE = Path(__file__).resolve().parents[1] / "lib" / "host_budget.py"
SPEC = importlib.util.spec_from_file_location("measured_host_budget", SOURCE)
assert SPEC is not None and SPEC.loader is not None
budget = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(budget)


class MeasuredAdmissionTests(unittest.TestCase):
    def test_explicit_environment_is_independent_of_process_admission(self):
        with patch.dict(os.environ, {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "7"}, clear=True):
            self.assertIsNone(budget.admitted_jobs({}))
            self.assertEqual(budget.admitted_jobs({"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "2"}), 2)
            self.assertEqual(budget.admitted_jobs(), 7)

    def test_explicit_environment_uses_the_same_refusal(self):
        with patch.dict(os.environ, {}, clear=True):
            for share in (None, "0", "-1", "\u0662"):
                env = {"BUILD_SLOT_HELD": "1"}
                if share is not None:
                    env["CARGO_BUILD_JOBS"] = share
                with self.subTest(share=share), self.assertRaises(budget.AdmissionInvalid):
                    budget.admitted_jobs(env)

    def measure(self, env):
        readings = {
            ("sysctl", "-n", "hw.ncpu"): "32\n",
            ("sysctl", "-n", "hw.memsize"): str(128 * budget.GIB),
            ("vm_stat",): (
                "Mach Virtual Memory Statistics: (page size of 16384 bytes)\n"
                "Pages free: 65536.\nPages speculative: 65536.\n"
                "Pages inactive: 65536.\nPages purgeable: 65536.\n"
            ),
        }
        with patch.dict(os.environ, env, clear=True), \
             patch.object(budget.platform, "system", return_value="Darwin"), \
             patch.object(budget, "_run", side_effect=lambda argv: readings[tuple(argv)]):
            return budget.measure()

    def test_valid_share_caps_observed_cpus_and_records_the_cap(self):
        for share, expected in (("2", 2), ("64", 32)):
            with self.subTest(share=share):
                measured = self.measure({"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": share})
                self.assertEqual(measured.cpus, expected)
                self.assertIn(f"build-slot CPU share {expected}/32", measured.avail_source)

    def test_unmanaged_caller_keeps_the_actual_cpu_reading(self):
        for env in ({}, {"CARGO_BUILD_JOBS": "2"}, {"BUILD_SLOT_HELD": "0"}):
            with self.subTest(env=env):
                measured = self.measure(env)
                self.assertEqual(measured.cpus, 32)
                self.assertNotIn("build-slot CPU share", measured.avail_source)

    def test_invalid_share_has_the_canonical_admission_refusal(self):
        for share in (None, "", "0", "-1", "2x", " 2", "2\n", "\u0662", "\uff12"):
            with self.subTest(share=share):
                env = {"BUILD_SLOT_HELD": "1"}
                if share is not None:
                    env["CARGO_BUILD_JOBS"] = share
                with self.assertRaises(budget.AdmissionInvalid):
                    self.measure(env)

    @unittest.skipUnless(getattr(sys, "get_int_max_str_digits", lambda: 0)() > 0,
                         "interpreter has no integer-string limit")
    def test_unparseable_large_share_is_an_admission_refusal(self):
        share = "9" * (sys.get_int_max_str_digits() + 1)
        with self.assertRaises(budget.AdmissionInvalid):
            self.measure({"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": share})


if __name__ == "__main__":
    unittest.main()
