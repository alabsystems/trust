#!/usr/bin/env python3
"""Mutation proofs for the fleet pin-drift sweep.

Every test builds a real fleet on disk --- superprojects, siblings, and bare
remotes --- and asserts on the shipped script's own output. The sweep exists
because four distinct pin failures in one day were each caught only when an
unrelated lane tried to push, so the properties worth pinning are: an
unpublished gitlink is HARD, a lag is REPORTED but not refused, an anchor is
recognised as durable, an upstream mirror is not swept for lag, and --- the one
that closes the audit's own historical defect --- a stale remote-tracking ref
cannot vouch for anything.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "sweep_pin_drift.py"


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], capture_output=True, text=True, check=check)


def identity(repo: Path) -> None:
    git("-C", str(repo), "config", "user.name", "Pin Sweep Test")
    git("-C", str(repo), "config", "user.email", "pin-sweep@example.invalid")


class Fleet:
    """One superproject, one sibling, one bare remote for each, on disk."""

    def __init__(self, root: Path, *, owner: str = "alabsystems") -> None:
        self.root = root
        self.sibling = root / "sibling"
        self.sibling_remote = root / f"{owner}" / "sibling.git"
        self.super = root / "fleet" / "super"
        self.super_remote = root / f"{owner}" / "super.git"
        self.super_remote.parent.mkdir(parents=True, exist_ok=True)
        self.super.parent.mkdir(parents=True, exist_ok=True)

        git("init", "-q", "--bare", "--initial-branch=main", str(self.sibling_remote))
        git("init", "-q", "-b", "main", str(self.sibling))
        identity(self.sibling)
        self.commit(self.sibling, "one")
        git("-C", str(self.sibling), "remote", "add", "origin", str(self.sibling_remote))
        git("-C", str(self.sibling), "push", "-qu", "origin", "main")
        self.first = self.head(self.sibling)

        git("init", "-q", "--bare", "--initial-branch=main", str(self.super_remote))
        git("init", "-q", "-b", "main", str(self.super))
        identity(self.super)
        git("-C", str(self.super), "remote", "add", "origin", str(self.super_remote))

    def commit(self, repo: Path, text: str) -> str:
        (repo / "value").write_text(f"{text}\n")
        git("-C", str(repo), "add", "value")
        git("-C", str(repo), "commit", "-qm", text)
        return self.head(repo)

    def head(self, repo: Path) -> str:
        return git("-C", str(repo), "rev-parse", "HEAD").stdout.strip()

    def pin(self, sha: str, *, url: str | None = None, path: str = "sib") -> None:
        (self.super / ".gitmodules").write_text(
            f'[submodule "{path}"]\n\tpath = {path}\n'
            f"\turl = {url or self.sibling_remote}\n"
        )
        git("-C", str(self.super), "add", ".gitmodules")
        git("-C", str(self.super), "update-index", "--add", "--info-only",
            "--cacheinfo", "160000", sha, path)
        git("-C", str(self.super), "commit", "-qm", f"pin {sha[:12]}")
        git("-C", str(self.super), "push", "-q", "origin", "main")

    def materialize(self) -> None:
        git("-c", "protocol.file.allow=always", "-C", str(self.super),
            "submodule", "update", "--init", "--checkout", check=False)


def sweep(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        capture_output=True, text=True, check=False,
    )


def rows(done: subprocess.CompletedProcess[str]) -> list[dict[str, str]]:
    return json.loads(done.stdout)["gitlinks"]


class SweepTests(unittest.TestCase):
    def test_unpublished_gitlink_is_a_hard_finding(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fleet = Fleet(Path(tmp))
            # A commit made locally and never pushed: failure (a), the shape
            # that produced 22 unrecoverable pins and 169 unreproducible
            # superproject commits.
            unpushed = fleet.commit(fleet.sibling, "never pushed")
            fleet.pin(unpushed)
            fleet.materialize()

            done = sweep("--repo", str(fleet.super), "--json")
            self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
            [row] = rows(done)
            self.assertEqual(row["status"], "UNPUBLISHED")
            self.assertIn("cannot be reproduced by anyone else", row["detail"])

            text = sweep("--repo", str(fleet.super))
            self.assertIn("HARD: 1", text.stdout)

    def test_lag_is_reported_and_not_refused(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fleet = Fleet(Path(tmp))
            fleet.pin(fleet.first)
            for n in range(3):
                fleet.commit(fleet.sibling, f"later {n}")
            git("-C", str(fleet.sibling), "push", "-q", "origin", "main")
            fleet.materialize()

            done = sweep("--repo", str(fleet.super), "--json")
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
            [row] = rows(done)
            self.assertEqual(row["status"], "PUBLISHED")
            self.assertEqual(row["lag"], "BEHIND")
            self.assertIn("3 commits behind", row["detail"])

            text = sweep("--repo", str(fleet.super))
            self.assertIn("DRIFT (reported, not refused): 1", text.stdout)
            self.assertNotIn("HARD:", text.stdout)

    def test_an_anchor_is_durable_and_a_deleted_branch_is_not(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fleet = Fleet(Path(tmp))
            git("-C", str(fleet.sibling), "switch", "-qc", "topic")
            topic = fleet.commit(fleet.sibling, "topic")
            git("-C", str(fleet.sibling), "push", "-qu", "origin", "topic")
            fleet.pin(topic)
            fleet.materialize()

            # On a branch: durable, and merely divergent from main.
            done = sweep("--repo", str(fleet.super), "--json")
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
            self.assertEqual(rows(done)[0]["status"], "PUBLISHED")

            # The forge prunes the branch. THIS CLONE IS NEVER TOLD, and
            # refs/remotes/origin/topic survives. A sweep that read
            # remote-tracking refs would still call this reachable --- which is
            # precisely the false all-clear that motivated the whole tool.
            git("--git-dir", str(fleet.sibling_remote), "update-ref", "-d",
                "refs/heads/topic")
            submodule_git_dir = fleet.super / ".git" / "modules" / "sib"
            self.assertEqual(
                git("--git-dir", str(submodule_git_dir), "rev-parse",
                    "refs/remotes/origin/topic").stdout.strip(),
                topic,
                "fixture is not exercising the defect: the stale remote-tracking "
                "ref is already gone",
            )

            done = sweep("--repo", str(fleet.super), "--json")
            self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
            self.assertEqual(rows(done)[0]["status"], "UNPUBLISHED")

            # Anchoring it restores durability without moving any branch.
            git("-C", str(fleet.sibling), "push", "-q", str(fleet.sibling_remote),
                f"{topic}:refs/pins/{topic}")
            done = sweep("--repo", str(fleet.super), "--json")
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
            self.assertEqual(rows(done)[0]["status"], "ANCHORED")

    def test_upstream_mirrors_are_not_swept_for_lag(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fleet = Fleet(Path(tmp), owner="upstream-project")
            fleet.pin(fleet.first, url="https://github.com/upstream-project/thing.git")
            fleet.materialize()

            done = sweep("--repo", str(fleet.super), "--json")
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
            [row] = rows(done)
            self.assertEqual(row["status"], "THIRD-PARTY")
            self.assertEqual(row["lag"], "-")

    def test_a_dead_remote_is_an_error_not_a_pass(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fleet = Fleet(Path(tmp))
            fleet.pin(fleet.first)
            fleet.materialize()
            git("-C", str(fleet.super), "remote", "set-url", "origin",
                str(Path(tmp) / "absent.git"))

            done = sweep("--repo", str(fleet.super), "--json")
            self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
            self.assertEqual(rows(done)[0]["status"], "ERROR")

    def test_the_subject_is_the_published_revision_not_this_checkout(self) -> None:
        """A local commit nobody has seen must not become a fleet finding."""
        with tempfile.TemporaryDirectory() as tmp:
            fleet = Fleet(Path(tmp))
            fleet.pin(fleet.first)
            fleet.materialize()

            unpushed = fleet.commit(fleet.sibling, "local only")
            git("-C", str(fleet.super), "update-index", "--info-only",
                "--cacheinfo", "160000", unpushed, "sib")
            git("-C", str(fleet.super), "commit", "-qm", "local pin bump")

            done = sweep("--repo", str(fleet.super), "--json")
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
            [row] = rows(done)
            self.assertEqual(row["sha"], fleet.first)
            self.assertEqual(row["status"], "PUBLISHED")


class DefaultBranchTests(unittest.TestCase):
    def test_master_is_a_default_branch_too(self) -> None:
        import importlib.util

        spec = importlib.util.spec_from_file_location("sweep_pin_drift", SCRIPT)
        assert spec is not None and spec.loader is not None
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)

        self.assertEqual(
            module.default_head({"refs/heads/master": "a" * 40}),
            ("refs/heads/master", "a" * 40),
        )
        self.assertEqual(
            module.default_head({"refs/heads/main": "b" * 40,
                                 "refs/heads/master": "a" * 40}),
            ("refs/heads/main", "b" * 40),
        )
        self.assertEqual(
            module.default_head({"refs/heads/only-one": "c" * 40}),
            ("refs/heads/only-one", "c" * 40),
        )
        self.assertEqual(
            module.default_head({"refs/heads/a": "c" * 40, "refs/heads/b": "d" * 40}),
            ("", ""),
        )


if __name__ == "__main__":
    unittest.main()
