#!/usr/bin/env python3
"""Shallow-store containment regressions for scripts/lib/remote_tips.py.

The cohort shell suite pins scope="main" through the gate; this pins the
shared library itself, including scope="durable" (the reach lane) and bare
stores. The defect (2026-10-26): a by-sha fetch into a shallow store brings
the pinned commit and the remote tip but not the history between them, so
`merge-base --is-ancestor` answered 1 for contained pins --- twelve false
OFF-MAIN rows on the real tree. A 1 from a shallow store must earn one
--unshallow fetch and a retest; a fork must still read NOT_CONTAINED.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lib"))
import remote_tips as rt  # noqa: E402


def git(*args: str, cwd: Path) -> str:
    done = subprocess.run(
        ["git", *args], cwd=cwd, text=True, capture_output=True, check=True
    )
    return done.stdout.strip()


def refstate(store: Path) -> str:
    refs = git("-C", str(store), "for-each-ref", "--format=%(objectname) %(refname)", cwd=store)
    fh = Path(git("-C", str(store), "rev-parse", "--path-format=absolute", "--git-path", "FETCH_HEAD", cwd=store))
    return refs + "\n" + (fh.read_text() if fh.exists() else "<no FETCH_HEAD>")


class StoreDiscoveryTests(unittest.TestCase):
    def test_a_worktree_is_found_from_its_git_not_from_stray_files(self) -> None:
        # Round 6 of LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (the IR reader audit):
        # _resolve asked a worktree first as a bare store, and two untracked
        # files there (HEAD, commondir) answered with another repository's
        # store and remote, so a pin only that repository held read as
        # contained. A bare store is still asked as one.
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        wt = root / "wt"
        git("init", "-q", "-b", "main", str(wt), cwd=root)
        git("remote", "add", "origin", "https://example.invalid/real.git", cwd=wt)
        other = root / "other.git"
        git("init", "-q", "--bare", "-b", "main", str(other), cwd=root)
        git("--git-dir", str(other), "remote", "add", "origin", "https://example.invalid/other.git", cwd=root)
        (wt / "HEAD").write_text("ref: refs/heads/main\n")
        (wt / "commondir").write_text(str(other) + "\n")
        found = rt.RemoteTips._resolve(wt)
        self.assertEqual(found.url, "https://example.invalid/real.git", found.error)
        self.assertEqual(Path(found.git_dir).resolve(), (wt / ".git").resolve())
        bare = rt.RemoteTips._resolve(other)
        self.assertEqual(bare.url, "https://example.invalid/other.git", bare.error)

    def test_a_worktree_whose_git_is_a_file_is_found_from_it(self) -> None:
        # Round 7 of LAND-GATE-EW1-FOLLOWUP-REVIEW-4: a submodule worktree's
        # .git is a gitfile naming its store; the test above used a .git
        # directory only, and a check of `.git` being a directory passed it.
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        wt = root / "wt"
        git("init", "-q", "-b", "main", "--separate-git-dir", str(root / "store"), str(wt), cwd=root)
        self.assertTrue((wt / ".git").is_file())
        git("remote", "add", "origin", "https://example.invalid/real.git", cwd=wt)
        other = root / "other.git"
        git("init", "-q", "--bare", "-b", "main", str(other), cwd=root)
        git("--git-dir", str(other), "remote", "add", "origin", "https://example.invalid/other.git", cwd=root)
        (wt / "HEAD").write_text("ref: refs/heads/main\n")
        (wt / "commondir").write_text(str(other) + "\n")
        found = rt.RemoteTips._resolve(wt)
        self.assertEqual(found.url, "https://example.invalid/real.git", found.error)
        self.assertEqual(Path(found.git_dir).resolve(), (root / "store").resolve())


class ShallowStoreTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        src = self.root / "src"
        git("init", "-q", "-b", "main", str(src), cwd=self.root)
        git("config", "user.email", "t@example.invalid", cwd=src)
        git("config", "user.name", "T", cwd=src)
        self.revs = []
        for i in range(5):
            (src / "f").write_text(f"{i}\n")
            git("add", "-A", cwd=src)
            git("commit", "-qm", f"c{i}", cwd=src)
            self.revs.append(git("rev-parse", "HEAD", cwd=src))
        self.pin = self.revs[0]  # oldest: contained, far below a depth-1 tip
        # A fork off the pin, published on its own branch: fetchable, and
        # contained in durable scope, never in main scope.
        git("checkout", "-q", "-b", "fork", self.pin, cwd=src)
        (src / "f").write_text("fork\n")
        git("add", "-A", cwd=src)
        git("commit", "-qm", "fork", cwd=src)
        self.fork = git("rev-parse", "HEAD", cwd=src)
        git("checkout", "-q", "main", cwd=src)
        self.remote = self.root / "remote.git"
        git("clone", "-q", "--bare", str(src), str(self.remote), cwd=self.root)

    def shallow_clone(self, name: str, *, bare: bool = False) -> Path:
        dst = self.root / name
        args = ["clone", "-q", "--depth", "1"]
        if bare:
            args.append("--bare")
        git(*args, f"file://{self.remote}", str(dst), cwd=self.root)
        return dst

    def test_main_scope_contained_pin_in_shallow_worktree(self) -> None:
        # Main scope, not durable: the pin is also the fork's parent, so a
        # durable verdict could arrive via the fork branch's direct parent
        # edge without ever testing main containment across the graft.
        store = self.shallow_clone("wt")
        before = refstate(store)
        verdict = rt.RemoteTips().judge(store, self.pin, scope="main")
        self.assertEqual(verdict.state, rt.CONTAINED, verdict.detail)
        self.assertEqual(refstate(store), before, "judge moved a ref")

    def test_main_scope_contained_pin_in_shallow_bare_store(self) -> None:
        store = self.shallow_clone("bare.git", bare=True)
        verdict = rt.RemoteTips().judge(store, self.pin, scope="main")
        self.assertEqual(verdict.state, rt.CONTAINED, verdict.detail)

    def test_fork_still_not_contained_in_main_scope(self) -> None:
        store = self.shallow_clone("wt-fork")
        verdict = rt.RemoteTips().judge(store, self.fork, scope="main")
        self.assertEqual(verdict.state, rt.NOT_CONTAINED, verdict.detail)

    def test_deepen_refusal_falls_through_to_unshallow(self) -> None:
        # A server may refuse `--deepen` for by-sha wants while still
        # serving `--unshallow`. The deepen ladder must fall through to
        # the unshallow step instead of giving up as unread.
        class DeepenRefusingTips(rt.RemoteTips):
            def _fetch(self, remote, shas, *, unshallow=False, deepen=None):  # type: ignore[override]
                if deepen:
                    return subprocess.CompletedProcess(
                        [], 128, "", "fatal: deepen refused by fake server"
                    )
                return super()._fetch(remote, shas, unshallow=unshallow, deepen=deepen)

        store = self.shallow_clone("wt-deepen-refused")
        verdict = DeepenRefusingTips().judge(store, self.pin, scope="main")
        self.assertEqual(verdict.state, rt.CONTAINED, verdict.detail)
        store2 = self.shallow_clone("wt-deepen-refused-fork")
        verdict2 = DeepenRefusingTips().judge(store2, self.fork, scope="main")
        self.assertEqual(verdict2.state, rt.NOT_CONTAINED, verdict2.detail)

    def test_fork_contained_in_durable_scope_via_its_branch(self) -> None:
        store = self.shallow_clone("wt-fork-durable")
        verdict = rt.RemoteTips().judge(store, self.fork, scope="durable")
        self.assertEqual(verdict.state, rt.CONTAINED, verdict.detail)


if __name__ == "__main__":
    unittest.main()
