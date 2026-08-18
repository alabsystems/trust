#!/usr/bin/env python3
"""Focused regressions for historical first-party pin classification."""

from __future__ import annotations

import importlib.util
import subprocess
import sys
import tempfile
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


class SubmoduleGitDirTests(unittest.TestCase):
    def test_linked_worktree_uses_git_resolved_modules_directory(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "root"
            linked = Path(tmp) / "linked"
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(
                ["git", "-C", str(root), "config", "user.name", "Pin Audit Test"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(root), "config", "user.email", "pin-audit@example.invalid"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(root), "commit", "--allow-empty", "-qm", "seed"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(root), "worktree", "add", "-q", str(linked)],
                check=True,
            )

            resolved = audit.submodule_git_dir(linked, "first-party/example")

            self.assertIsNotNone(resolved)
            assert resolved is not None
            self.assertTrue(resolved.is_absolute())
            self.assertNotEqual(resolved, linked / ".git" / "modules/first-party/example")
            self.assertIn("worktrees", resolved.parts)


if __name__ == "__main__":
    unittest.main()
