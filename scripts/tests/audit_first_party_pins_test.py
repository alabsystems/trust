#!/usr/bin/env python3
"""Focused regressions for historical first-party pin classification."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "audit_first_party_pins.py"
SPEC = importlib.util.spec_from_file_location("audit_first_party_pins", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
audit = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = audit
SPEC.loader.exec_module(audit)


class ProbeClassificationTests(unittest.TestCase):
    def test_remote_refusal_leaves_local_object_anchorable(self) -> None:
        sha = "1" * 40
        missing, orphan, unknown = audit.classify_probe_results(
            {sha: True}, {sha: audit.REFUSED}
        )

        self.assertEqual(missing, [])
        self.assertEqual(orphan, [sha])
        self.assertEqual(unknown, [])

    def test_remote_refusal_is_missing_without_local_object(self) -> None:
        sha = "2" * 40
        missing, orphan, unknown = audit.classify_probe_results(
            {sha: False}, {sha: audit.REFUSED}
        )

        self.assertEqual(missing, [sha])
        self.assertEqual(orphan, [])
        self.assertEqual(unknown, [])

    def test_served_remote_object_is_orphan_without_local_object(self) -> None:
        sha = "3" * 40
        missing, orphan, unknown = audit.classify_probe_results(
            {sha: False}, {sha: audit.SERVED}
        )

        self.assertEqual(missing, [])
        self.assertEqual(orphan, [sha])
        self.assertEqual(unknown, [])

    def test_unknown_remote_object_is_indeterminate_without_local_object(self) -> None:
        sha = "4" * 40
        missing, orphan, unknown = audit.classify_probe_results(
            {sha: False}, {sha: audit.UNKNOWN}
        )

        self.assertEqual(missing, [])
        self.assertEqual(orphan, [])
        self.assertEqual(unknown, [sha])


if __name__ == "__main__":
    unittest.main()
