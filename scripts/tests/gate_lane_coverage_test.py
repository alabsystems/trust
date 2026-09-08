#!/usr/bin/env python3
"""Mutation controls for exact versus intentional-prefix tooling roles."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "check_gate_lane_coverage.py"
SPEC = importlib.util.spec_from_file_location("check_gate_lane_coverage", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
coverage = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = coverage
SPEC.loader.exec_module(coverage)


class ToolingRoleControls(unittest.TestCase):
    def test_exact_tooling_role_does_not_hide_suffix_twin(self) -> None:
        for exact in (
            "scripts/toolchain-provenance-probe.sh",
            "scripts/trust_ir_scorecard_diff.py",
        ):
            with self.subTest(exact=exact):
                self.assertTrue(coverage._is_tooling(exact))
                self.assertFalse(coverage._is_tooling(f"{exact}.evil.py"))

    def test_declared_directory_and_stem_roles_remain_prefixes(self) -> None:
        self.assertTrue(coverage._is_tooling("scripts/lib/process_tree.sh"))
        self.assertTrue(coverage._is_tooling("scripts/install-example.sh"))


if __name__ == "__main__":
    unittest.main()
