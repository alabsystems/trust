#!/usr/bin/env python3
"""Focused regression controls for the retired compatibility WP native API."""

import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "manifest_alignment", ROOT / "scripts" / "check_cargo_manifest_alignment.py"
)
POLICY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(POLICY)


class NativeFacadeRetirement(unittest.TestCase):
    def test_current_sources_and_reintroduction_controls(self):
        self.assertEqual(POLICY.wp_retirement_self_check(), [])


if __name__ == "__main__":
    unittest.main()
