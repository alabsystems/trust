#!/usr/bin/env python3
"""Focused regressions for historical first-party pin classification."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


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


class HeadPruneClassificationTests(unittest.TestCase):
    def test_only_explicitly_retained_closures_are_safe(self) -> None:
        main = "1" * 40
        pin = "2" * 40
        tag = "3" * 40
        side_head_only = "4" * 40
        reachable = audit.DurableReachability({main}, {pin}, {tag})

        self.assertEqual(audit.head_prune_status(main, reachable), audit.SAFE_MAIN)
        self.assertEqual(audit.head_prune_status(pin, reachable), audit.SAFE_PIN)
        self.assertEqual(audit.head_prune_status(tag, reachable), audit.SAFE_TAG)
        self.assertEqual(
            audit.head_prune_status(side_head_only, reachable), audit.NEEDS_ANCHOR
        )

    def test_exact_remote_pin_verification_rejects_wrong_target(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            work = root / "work"
            remote = root / "remote.git"
            _git("init", "-q", "-b", "main", str(work))
            _identity(work)
            (work / "value").write_text("one\n")
            _git("-C", str(work), "add", "value")
            _git("-C", str(work), "commit", "-qm", "one")
            first = _git("-C", str(work), "rev-parse", "HEAD").stdout.strip()
            (work / "value").write_text("two\n")
            _git("-C", str(work), "commit", "-qam", "two")
            second = _git("-C", str(work), "rev-parse", "HEAD").stdout.strip()
            _git("clone", "-q", "--bare", str(work), str(remote))

            ref = f"refs/pins/{first}"
            _git("--git-dir", str(remote), "update-ref", ref, second)
            ok, detail = audit.remote_pin_is_exact(work / ".git", str(remote), first)
            self.assertFalse(ok)
            self.assertIn("mismatch", detail)

            _git("--git-dir", str(remote), "update-ref", ref, first)
            ok, detail = audit.remote_pin_is_exact(work / ".git", str(remote), first)
            self.assertTrue(ok, detail)


def _git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        capture_output=True,
        text=True,
        check=check,
    )


def _identity(repo: Path) -> None:
    _git("-C", str(repo), "config", "user.name", "Pin Audit Test")
    _git("-C", str(repo), "config", "user.email", "pin-audit@example.invalid")


class HeadPruneIntegrationTests(unittest.TestCase):
    def test_side_head_is_anchored_before_prune_and_failures_are_nonzero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sibling = root / "sibling"
            remote = root / "sibling.git"
            superproject = root / "super"

            _git("init", "-q", "-b", "main", str(sibling))
            _identity(sibling)
            (sibling / "value").write_text("main\n")
            _git("-C", str(sibling), "add", "value")
            _git("-C", str(sibling), "commit", "-qm", "main")
            _git("init", "-q", "--bare", "--initial-branch=main", str(remote))
            _git("-C", str(sibling), "remote", "add", "origin", str(remote))
            _git("-C", str(sibling), "push", "-qu", "origin", "main")
            _git("-C", str(sibling), "switch", "-qc", "topic")
            (sibling / "value").write_text("topic\n")
            _git("-C", str(sibling), "commit", "-qam", "topic")
            topic = _git("-C", str(sibling), "rev-parse", "HEAD").stdout.strip()
            _git("-C", str(sibling), "push", "-qu", "origin", "topic")

            _git("init", "-q", "-b", "main", str(superproject))
            _identity(superproject)
            (superproject / ".gitmodules").write_text(
                "[submodule \"first-party/example\"]\n"
                "\tpath = first-party/example\n"
                f"\turl = {remote}\n"
            )
            _git("-C", str(superproject), "add", ".gitmodules")
            _git(
                "-C",
                str(superproject),
                "update-index",
                "--add",
                "--cacheinfo",
                "160000",
                topic,
                "first-party/example",
            )
            _git("-C", str(superproject), "commit", "-qm", "pin topic")
            _git(
                "-c",
                "protocol.file.allow=always",
                "-C",
                str(superproject),
                "submodule",
                "update",
                "--init",
                "--checkout",
            )

            command = [
                sys.executable,
                str(SCRIPT),
                "--repo",
                str(superproject),
                "--prepare-head-prune",
            ]
            before = subprocess.run(command, capture_output=True, text=True, check=False)
            self.assertEqual(before.returncode, 1, before.stdout + before.stderr)
            self.assertIn("NEEDS_ANCHOR", before.stdout)

            # Even a pin initially safe through main must be reclassified if
            # the durable namespace changes before the final verdict.
            output = io.StringIO()
            durable_snapshots = [
                (audit.DurableReachability({topic}, set(), set()), ""),
                (audit.DurableReachability(set(), set(), set()), ""),
            ]
            with (
                mock.patch.object(sys, "argv", [str(SCRIPT), *command[2:]]),
                mock.patch.object(
                    audit,
                    "prepare_head_prune_reachability",
                    side_effect=durable_snapshots,
                ) as snapshots,
                contextlib.redirect_stdout(output),
            ):
                self.assertEqual(audit.main(), 1)
            self.assertEqual(snapshots.call_count, 2)
            self.assertIn("NEEDS_ANCHOR", output.getvalue())

            # A failed push/verification must keep the mode red.
            output = io.StringIO()
            with (
                mock.patch.object(sys, "argv", [str(SCRIPT), *command[2:], "--anchor"]),
                mock.patch.object(audit, "anchor", return_value=(False, "push failed: test")),
                contextlib.redirect_stdout(output),
            ):
                self.assertEqual(audit.main(), 1)
            self.assertIn("ANCHOR FAILURES", output.getvalue())

            anchored = subprocess.run(
                [*command, "--anchor"], capture_output=True, text=True, check=False
            )
            self.assertEqual(anchored.returncode, 0, anchored.stdout + anchored.stderr)
            self.assertIn("exact remote ref verified", anchored.stdout)
            self.assertEqual(
                _git(
                    "--git-dir", str(remote), "rev-parse", f"refs/pins/{topic}"
                ).stdout.strip(),
                topic,
            )

            _git("--git-dir", str(remote), "update-ref", "-d", "refs/heads/topic")
            after = subprocess.run(command, capture_output=True, text=True, check=False)
            self.assertEqual(after.returncode, 0, after.stdout + after.stderr)
            self.assertIn("HEAD-PRUNE READY", after.stdout)

            # An absent pin plus an inconclusive direct-SHA probe is not a
            # successful audit.  --info-only lets the superproject record the
            # deliberately missing gitlink without adding an object locally.
            absent_pin = "f" * 40
            _git(
                "-C",
                str(superproject),
                "update-index",
                "--info-only",
                "--cacheinfo",
                "160000",
                absent_pin,
                "first-party/example",
            )
            _git("-C", str(superproject), "commit", "-qm", "pin absent object")
            output = io.StringIO()
            with (
                mock.patch.object(sys, "argv", [str(SCRIPT), *command[2:]]),
                mock.patch.object(audit, "probe", return_value=audit.UNKNOWN),
                mock.patch.object(audit.time, "sleep"),
                contextlib.redirect_stdout(output),
            ):
                self.assertEqual(audit.main(), 1)
            self.assertIn("INDETERMINATE pins: 1", output.getvalue())

            # A successful direct-SHA probe is exact evidence that an absent
            # object can be anchored; do not relabel it UNKNOWN merely because
            # a no-write audit intentionally did not fetch it.
            output = io.StringIO()
            with (
                mock.patch.object(sys, "argv", [str(SCRIPT), *command[2:]]),
                mock.patch.object(audit, "probe", return_value=audit.SERVED),
                mock.patch.object(audit.time, "sleep"),
                contextlib.redirect_stdout(output),
            ):
                self.assertEqual(audit.main(), 1)
            self.assertIn("NEEDS_ANCHOR=1", output.getvalue())
            self.assertIn(f"NEEDS_ANCHOR {absent_pin}", output.getvalue())
            self.assertNotIn("UNKNOWN=1", output.getvalue())

            # The mode cannot make a safety claim from stale local refs.
            (superproject / ".gitmodules").write_text(
                "[submodule \"first-party/example\"]\n"
                "\tpath = first-party/example\n"
                f"\turl = {root / 'absent.git'}\n"
            )
            failed_fetch = subprocess.run(
                command, capture_output=True, text=True, check=False
            )
            self.assertEqual(failed_fetch.returncode, 1)
            self.assertIn("remote-head fetch failed", failed_fetch.stdout)


class OrdinaryAuditRemoteEvidenceTests(unittest.TestCase):
    """End-to-end runs of the shipped script, one real sibling and one real remote.

    Measured 2026-08-26 against the nine live first-party siblings: the audit
    called 58 pins UNRECOVERABLE, and 33 of them were held by an exact
    refs/pins/<sha> on the canonical remote --- absent only from this clone.
    """

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        self.superproject = root / "super"
        sibling = root / "sibling"
        donor = root / "donor"
        self.remote = root / "sibling.git"

        _git("init", "-q", "-b", "main", str(sibling))
        _identity(sibling)
        (sibling / "value").write_text("main\n")
        _git("-C", str(sibling), "add", "value")
        _git("-C", str(sibling), "commit", "-qm", "main")
        _git("init", "-q", "--bare", "--initial-branch=main", str(self.remote))
        _git("-C", str(sibling), "remote", "add", "origin", str(self.remote))
        _git("-C", str(sibling), "push", "-qu", "origin", "main")
        main_tip = _git("-C", str(sibling), "rev-parse", "HEAD").stdout.strip()

        _git("init", "-q", "-b", "main", str(self.superproject))
        _identity(self.superproject)
        (self.superproject / ".gitmodules").write_text(
            "[submodule \"first-party/example\"]\n"
            "\tpath = first-party/example\n"
            f"\turl = {self.remote}\n"
        )
        _git("-C", str(self.superproject), "add", ".gitmodules")
        _git(
            "-C", str(self.superproject), "update-index", "--add", "--cacheinfo",
            "160000", main_tip, "first-party/example",
        )
        _git("-C", str(self.superproject), "commit", "-qm", "pin main")
        _git(
            "-c", "protocol.file.allow=always", "-C", str(self.superproject),
            "submodule", "update", "--init", "--checkout",
        )

        # A commit reachable ONLY from refs/pins/<sha> on the canonical remote.
        # Built in a donor clone *after* the sibling exists: a local clone
        # hardlinks the whole object store, so an earlier push would have
        # handed the sibling the very object these tests need it to lack.
        _git("clone", "-q", str(self.remote), str(donor))
        _identity(donor)
        (donor / "value").write_text("anchored\n")
        _git("-C", str(donor), "commit", "-qam", "anchored")
        self.anchored = _git("-C", str(donor), "rev-parse", "HEAD").stdout.strip()
        _git(
            "-C", str(donor), "push", "-q", str(self.remote),
            f"{self.anchored}:refs/pins/{self.anchored}",
        )

    def _record_pin(self, sha: str) -> None:
        """Pin a sha the superproject holds no object for, as history really does."""
        _git(
            "-C", str(self.superproject), "update-index", "--info-only",
            "--cacheinfo", "160000", sha, "first-party/example",
        )
        _git("-C", str(self.superproject), "commit", "-qm", f"pin {sha}")

    def _audit(self, *flags: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--repo", str(self.superproject), *flags],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_planted_lost_pin_fails_the_audit(self) -> None:
        lost = "f" * 40  # in no object store and refused by the remote
        self._record_pin(lost)

        done = self._audit("--probe")

        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn(f"MISSING {lost}", done.stdout)
        self.assertIn("UNRECOVERABLE pins: 1", done.stdout)

    def test_remotely_anchored_pin_is_durable_not_lost(self) -> None:
        self._record_pin(self.anchored)

        done = self._audit("--probe")

        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("REMOTE_PIN=1", done.stdout)
        self.assertIn("ORPHAN=0", done.stdout)
        self.assertNotIn("UNRECOVERABLE", done.stdout)

    def test_local_absence_without_a_probe_is_unknown_not_unrecoverable(self) -> None:
        self._record_pin(self.anchored)

        done = self._audit()

        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn(f"UNKNOWN {self.anchored}", done.stdout)
        self.assertIn("no remote verdict", done.stdout)
        self.assertNotIn("UNRECOVERABLE", done.stdout)

    def test_probe_without_a_canonical_url_fails_closed(self) -> None:
        (self.superproject / ".gitmodules").write_text(
            "[submodule \"first-party/example\"]\n"
            "\tpath = first-party/example\n"
        )
        _git("-C", str(self.superproject), "commit", "-qam", "drop url")
        self._record_pin(self.anchored)

        done = self._audit("--probe")

        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("canonical submodule URL is missing", done.stdout)


if __name__ == "__main__":
    unittest.main()
