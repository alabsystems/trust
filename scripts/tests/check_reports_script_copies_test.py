#!/usr/bin/env python3
"""Tests for scripts/check_reports_script_copies.py.

The fixture tests build a real git repository in a temp dir: the check reads the
index, so a stand-in file list would not test what the check actually reads.
`test_live_repository_has_no_copies` is the regression test for the reports/
session-residue deletion. It runs the check against this checkout, and it
failed while the three `native-rustdoc-alias01/source/scripts/` copies were
still tracked.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "check_reports_script_copies.py"
SPEC = importlib.util.spec_from_file_location("check_reports_script_copies", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
check = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(check)


def git(repo: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True)


class FixtureRepo:
    def __init__(self, root: Path) -> None:
        self.root = root
        git(root, "init", "-q")

    def write(self, rel: str, content: str, executable: bool = False) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        if executable:
            path.chmod(0o755)
        git(self.root, "add", rel)

    def run(self) -> tuple[int, str]:
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = check.main(["--repo", str(self.root)])
        return rc, buf.getvalue()


class CheckReportsScriptCopiesTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.repo = FixtureRepo(Path(self._tmp.name))

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def test_identical_copy_of_executable_script_is_refused(self) -> None:
        self.repo.write("scripts/hooks/pre-push", "#!/bin/sh\necho gate\n", executable=True)
        self.repo.write("reports/x/source/scripts/hooks/pre-push", "#!/bin/sh\necho gate\n")
        rc, out = self.repo.run()
        self.assertEqual(rc, 1)
        self.assertIn(
            "reports/x/source/scripts/hooks/pre-push is byte-identical to scripts/hooks/pre-push",
            out,
        )

    def test_identical_copy_of_suffixed_script_is_refused_whatever_its_name(self) -> None:
        self.repo.write("tools/probe.py", "print('probe')\n")
        self.repo.write("reports/y/renamed-copy.txt", "print('probe')\n")
        rc, out = self.repo.run()
        self.assertEqual(rc, 1)
        self.assertIn("reports/y/renamed-copy.txt is byte-identical to tools/probe.py", out)

    def test_a_modified_copy_is_allowed(self) -> None:
        self.repo.write("scripts/gate.sh", "#!/bin/sh\necho live\n", executable=True)
        self.repo.write("reports/z/gate.sh", "#!/bin/sh\necho frozen\n")
        rc, out = self.repo.run()
        self.assertEqual(rc, 0, out)

    def test_copy_of_a_data_file_is_not_a_script_copy(self) -> None:
        self.repo.write("scripts/pins.txt", "a\nb\n")
        self.repo.write("reports/w/manifest.candidate", "a\nb\n")
        rc, out = self.repo.run()
        self.assertEqual(rc, 0, out)

    def test_empty_files_never_match(self) -> None:
        self.repo.write("scripts/empty.sh", "", executable=True)
        self.repo.write("reports/v/stderr", "")
        rc, out = self.repo.run()
        self.assertEqual(rc, 0, out)

    def test_copies_between_reports_are_not_live_scripts(self) -> None:
        self.repo.write("reports/a/run.sh", "#!/bin/sh\n", executable=True)
        self.repo.write("reports/b/run.sh", "#!/bin/sh\n", executable=True)
        rc, out = self.repo.run()
        self.assertEqual(rc, 0, out)

    def test_live_repository_has_no_copies(self) -> None:
        if not (REPO_ROOT / ".git").exists():
            self.skipTest("not a git checkout")
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = check.main(["--repo", str(REPO_ROOT)])
        self.assertEqual(rc, 0, buf.getvalue())


if __name__ == "__main__":
    os.environ.setdefault("GIT_CONFIG_NOSYSTEM", "1")
    unittest.main()
