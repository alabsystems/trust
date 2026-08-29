#!/usr/bin/env python3
"""Focused regressions for the executable stage0 identity probe."""

from __future__ import annotations

import importlib.util
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "check_seed_freshness.py"
SPEC = importlib.util.spec_from_file_location("check_seed_freshness", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
freshness = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = freshness
SPEC.loader.exec_module(freshness)


@unittest.skipUnless(os.name == "posix", "executable seed fixture requires POSIX")
class MaterializedStage0IdentityTests(unittest.TestCase):
    def test_identity_mismatch_never_emits_identity_match_note(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = root / "build/test-host/stage0/bin/rustc"
            binary.parent.mkdir(parents=True)
            binary.write_text(
                """#!/usr/bin/env python3
import pathlib
import sys

if "-vV" in sys.argv:
    print("rustc 1.99.0-trust")
    print("commit-hash: 2222222222222222222222222222222222222222")
    print("commit-date: 2026-07-13")
    print("release: 1.99.0-trust")
else:
    output = pathlib.Path(sys.argv[sys.argv.index("-o") + 1])
    output.write_bytes(b"rmeta")
""",
                encoding="utf-8",
            )
            binary.chmod(0o755)
            stage0 = {
                "compiler_git_commit_hash": "1" * 40,
                "compiler_date": "2026-07-13",
                "compiler_version": "1.99.0-trust",
            }

            with mock.patch.object(freshness, "ROOT", root):
                errors, notes = freshness.probe_materialized_stage0(stage0)

            self.assertTrue(any("commit-hash" in error for error in errors))
            self.assertFalse(any("identity matches the pin" in note for note in notes))


if __name__ == "__main__":
    unittest.main()
