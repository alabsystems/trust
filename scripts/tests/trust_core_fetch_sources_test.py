#!/usr/bin/env python3
"""Exercise source fetching against real local Git remotes, including a renamed branch.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
"""
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

if __name__ == "__main__" and sys.version_info < (3, 11):
    for candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        executable = shutil.which(candidate)
        if executable:
            os.execv(executable, [executable, os.path.abspath(__file__), *sys.argv[1:]])
    sys.exit("trust_core_fetch_sources_test.py requires Python 3.11+; none found on PATH")

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "trust_core"))
import fetch_sources as F  # noqa: E402


class BranchHistory(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="trust-core-fetch.")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.remote = self.root / "upstream"
        self.clone = self.root / "cache" / "upstream"
        self.git(self.root, "init", "-q", "-b", "main", str(self.remote))
        self.git(self.remote, "config", "user.name", "Source fetch test")
        self.git(self.remote, "config", "user.email", "source-fetch@example.invalid")
        self.pin = self.commit("2026-01-01T00:00:00Z")
        self.source = F.C.Source("fixture", str(self.remote), self.pin, "2026-01-01T00:00:00Z",
                                 "objects", "refs/remotes/origin/master")
        self.pins = F.C.Pins("a" * 40, "2026-01-02T00:00:00Z", {"fixture": self.source})

    def git(self, repo, *args, stamp=None):
        env = F.C.git_environment()
        if stamp is not None:
            env.update(GIT_AUTHOR_DATE=stamp, GIT_COMMITTER_DATE=stamp)
        return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                              text=True, env=env).stdout.strip()

    def commit(self, stamp):
        (self.remote / "source").write_text(stamp, encoding="utf-8")
        self.git(self.remote, "add", "source")
        self.git(self.remote, "commit", "-q", "-m", stamp, stamp=stamp)
        return self.git(self.remote, "rev-parse", "HEAD")

    def alias_exists(self):
        return F.C.git(self.clone, "rev-parse", "--verify", self.source.branch) is not None

    def test_renamed_default_preserves_the_pin_and_full_history(self):
        tip = self.commit("2026-01-03T00:00:00Z")
        F.fetch_branch_history(self.clone, self.source, self.pins)
        self.assertNotEqual(tip, self.pin)
        self.assertEqual(self.git(self.clone, "rev-parse", self.source.branch), tip)
        self.assertEqual(self.git(self.clone, "rev-parse", "--is-shallow-repository"), "false")
        self.assertTrue(F.branch_ready(self.clone, self.source, self.pins))
        # A second preparation needs neither the network nor a ref rewrite.
        with mock.patch.object(F.C, "load_pins", return_value=self.pins), \
                mock.patch.object(F.C, "sources_root", return_value=self.clone.parent), \
                mock.patch.object(F, "rust_ready", return_value=True), \
                mock.patch.object(F, "run", side_effect=AssertionError("unexpected fetch")):
            self.assertEqual(F.main([]), 0)

    def test_requested_branch_still_works_without_a_rename(self):
        tip = self.commit("2026-01-03T00:00:00Z")
        self.git(self.remote, "branch", "master")
        F.fetch_branch_history(self.clone, self.source, self.pins)
        self.assertEqual(self.git(self.clone, "rev-parse", self.source.branch), tip)
        self.assertTrue(F.branch_ready(self.clone, self.source, self.pins))

    def test_a_pin_object_without_its_required_branch_is_not_ready(self):
        self.commit("2026-01-03T00:00:00Z")
        F.run(["git", "clone", "-q", "--no-checkout", str(self.remote), str(self.clone)])
        self.assertTrue(F.holds(self.clone, self.pin))
        self.assertFalse(self.alias_exists())
        self.assertFalse(F.branch_ready(self.clone, self.source, self.pins))
        with mock.patch.object(F.C, "load_pins", return_value=self.pins), \
                mock.patch.object(F.C, "sources_root", return_value=self.clone.parent), \
                mock.patch.object(F, "rust_ready", return_value=True):
            self.assertEqual(F.main(["--check"]), 1)

    def test_changed_first_parent_selection_refuses_without_publishing_alias(self):
        self.commit("2026-01-01T12:00:00Z")
        self.commit("2026-01-03T00:00:00Z")
        with self.assertRaisesRegex(RuntimeError, "first-parent commit"):
            F.fetch_branch_history(self.clone, self.source, self.pins)
        self.assertTrue(F.holds(self.clone, self.pin))
        self.assertFalse(self.alias_exists())

    def test_detached_remote_head_cannot_supply_an_implicit_replacement(self):
        tip = self.commit("2026-01-03T00:00:00Z")
        self.git(self.remote, "update-ref", "--no-deref", "HEAD", tip)
        with self.assertRaisesRegex(RuntimeError, "no distinct symbolic default branch"):
            F.fetch_branch_history(self.clone, self.source, self.pins)
        self.assertFalse(self.alias_exists())

    def test_shallow_history_cannot_publish_the_historical_alias(self):
        self.commit("2026-01-03T00:00:00Z")
        F.run(["git", "clone", "-q", "--depth=1", "--no-checkout",
               self.remote.as_uri(), str(self.clone)])
        with self.assertRaisesRegex(RuntimeError, "shallow"):
            F.fetch_branch_history(self.clone, self.source, self.pins)
        self.assertFalse(self.alias_exists())

    def test_transport_failure_never_takes_the_renamed_branch_path(self):
        self.commit("2026-01-03T00:00:00Z")
        F.run(["git", "clone", "-q", "--no-checkout", str(self.remote), str(self.clone)])
        failure = subprocess.CompletedProcess(["git", "ls-remote"], 128, "", "transport refused")
        with mock.patch.object(F.subprocess, "run", return_value=failure) as run:
            with self.assertRaises(subprocess.CalledProcessError):
                F.fetch_branch_history(self.clone, self.source, self.pins)
            run.assert_called_once()
        self.assertFalse(self.alias_exists())


class CheckoutSource(unittest.TestCase):
    """A `read = "checkout"` source is fetched at its pin and checked out there."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="trust-core-checkout.")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.remote = self.root / "upstream"
        self.cache = self.root / "cache"
        self.git(self.root, "init", "-q", "-b", "main", str(self.remote))
        self.git(self.remote, "config", "user.name", "Checkout source test")
        self.git(self.remote, "config", "user.email", "checkout-source@example.invalid")
        (self.remote / "spec.md").write_text("pinned\n", encoding="utf-8")
        self.git(self.remote, "add", "spec.md")
        self.git(self.remote, "commit", "-q", "-m", "pinned")
        self.pin = self.git(self.remote, "rev-parse", "HEAD")
        (self.remote / "spec.md").write_text("newer\n", encoding="utf-8")
        self.git(self.remote, "commit", "-q", "-am", "newer")
        self.source = F.C.Source("fixture", self.remote.as_uri(), self.pin, "2026-01-01T00:00:00Z")
        self.pins = F.C.Pins("a" * 40, "2026-01-02T00:00:00Z", {"fixture": self.source})

    def git(self, repo, *args):
        return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                              text=True, env=F.C.git_environment()).stdout.strip()

    def main(self, argv):
        with mock.patch.object(F.C, "load_pins", return_value=self.pins), \
                mock.patch.object(F.C, "sources_root", return_value=self.cache), \
                mock.patch.object(F, "rust_ready", return_value=True):
            return F.main(argv)

    def test_preparation_checks_out_the_pin_and_is_then_idempotent(self):
        clone = self.cache / self.source.directory
        self.assertEqual(self.main(["--check"]), 1)
        self.assertEqual(self.main([]), 0)
        self.assertTrue(F.head_is(clone, self.pin))
        self.assertEqual((clone / "spec.md").read_text(encoding="utf-8"), "pinned\n")
        with mock.patch.object(F, "run", side_effect=AssertionError("unexpected fetch")):
            self.assertEqual(self.main([]), 0)


class RustAvailability(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="trust-core-rust-availability.")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.cache = self.root / "rust"
        self.cache.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Rust source availability test")
        self.git("config", "user.email", "source-availability@example.invalid")
        self.libraries = tuple(f"library/{crate}/src/lib.rs"
                               for crate in ("core", "alloc", "std", "proc_macro"))
        for rel in (*F.RUST_UPSTREAM_FILES, *self.libraries, "README.md"):
            path = self.cache / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"source: {rel}\n", encoding="utf-8")
        self.commit()

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.cache), *args], check=True,
                              capture_output=True, text=True, env=F.C.git_environment()).stdout.strip()

    def commit(self):
        self.git("add", "--all")
        self.git("commit", "-q", "-m", "source availability fixture")
        self.pin = self.git("rev-parse", "HEAD")

    def remove_blob(self, rel):
        oid = self.git("rev-parse", f"{self.pin}:{rel}")
        (self.cache / ".git" / "objects" / oid[:2] / oid[2:]).unlink()

    def test_a_pin_and_compiler_blob_do_not_hide_a_missing_library_blob(self):
        self.assertTrue(F.rust_ready(self.cache, self.pin))
        # Model an incomplete partial-clone object store. The commit, tree and
        # explicit upstream compiler input remain readable, but a required
        # standard-library source cannot be read offline.
        self.remove_blob(self.libraries[0])
        self.assertTrue(F.holds(self.cache, self.pin))
        for rel in F.RUST_UPSTREAM_FILES:
            self.assertIsNotNone(F.C.git(self.cache, "cat-file", "-e", f"{self.pin}:{rel}"))
        self.assertFalse(F.rust_ready(self.cache, self.pin))
        pins = F.C.Pins(self.pin, "2999-01-01T00:00:00Z", {})
        with mock.patch.object(F.C, "load_pins", return_value=pins), \
                mock.patch.object(F.C, "sources_root", return_value=self.root):
            self.assertEqual(F.main(["--check"]), 1)

    def test_every_declared_standard_library_root_must_exist(self):
        self.assertTrue(F.rust_ready(self.cache, self.pin))
        self.git("rm", "-q", self.libraries[-1])
        self.commit()
        self.assertFalse(F.rust_ready(self.cache, self.pin))

    def test_missing_compiler_input_still_refuses(self):
        self.assertTrue(F.rust_ready(self.cache, self.pin))
        self.remove_blob(F.RUST_UPSTREAM_FILES[0])
        self.assertFalse(F.rust_ready(self.cache, self.pin))

    def test_an_upstream_file_absent_from_the_pin_refuses(self):
        self.assertTrue(F.rust_ready(self.cache, self.pin))
        self.git("rm", "-q", F.RUST_UPSTREAM_FILES[0])
        self.commit()
        self.assertIsNone(F.rust_missing_blobs(self.cache, self.pin))
        self.assertFalse(F.rust_ready(self.cache, self.pin))

    def promisor_origin(self):
        remote = self.root / "upstream.git"
        self.git("clone", "-q", "--bare", "--no-hardlinks", str(self.cache), str(remote))
        self.git("remote", "add", "origin", str(remote))
        self.git("config", "remote.origin.promisor", "true")
        self.git("config", "remote.origin.partialclonefilter", "blob:none")

    def test_explicit_preparation_restores_a_missing_local_library_blob(self):
        self.promisor_origin()
        self.remove_blob(self.libraries[0])
        self.assertFalse(F.rust_ready(self.cache, self.pin))
        F.fetch_rust(self.cache, self.pin)
        self.assertTrue(F.rust_ready(self.cache, self.pin))

    def test_explicit_preparation_restores_every_missing_required_blob(self):
        # A checkout behind an unchanged working tree reads no blob, so each absent
        # library and compiler input must be fetched by oid, in one request.
        self.promisor_origin()
        lost = (*self.libraries, *F.RUST_UPSTREAM_FILES)
        oids = sorted(self.git("rev-parse", f"{self.pin}:{rel}") for rel in lost)
        for rel in lost:
            self.remove_blob(rel)
        self.assertEqual(F.rust_missing_blobs(self.cache, self.pin), oids)
        F.fetch_rust(self.cache, self.pin)
        self.assertEqual(F.rust_missing_blobs(self.cache, self.pin), [])

    def test_unread_corpus_and_gitlink_objects_are_not_required_library_blobs(self):
        self.git("update-index", "--add", "--cacheinfo",
                 "160000," + "f" * 40 + ",library/stdarch")
        self.git("commit", "-q", "-m", "opaque library gitlink")
        self.pin = self.git("rev-parse", "HEAD")
        self.remove_blob("README.md")
        self.assertTrue(F.rust_ready(self.cache, self.pin))


if __name__ == "__main__":
    unittest.main(verbosity=2)
