#!/usr/bin/env python3
"""Actual operation lifetime controls; no remote or ancestry verdict is mocked."""
import contextlib
import errno
import hashlib
import io
import json
import os
import random
import shutil
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
import zlib
from unittest.mock import patch

LIB = Path(__file__).resolve().parents[1] / "lib"
sys.path.insert(0, str(LIB))
import remote_tips as rt


@unittest.skipUnless(os.name == "posix" and rt._process_owner.exit_observation_available(),
                     "requires the supported local POSIX publication profile")
class SourcePublicationViewTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="source-publication-view-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.root = self.directory / "original checkout"
        self.root.mkdir()
        self.env = dict(os.environ, HOME=str(self.directory / "home"), XDG_CONFIG_HOME=str(self.directory / "xdg"))
        Path(self.env["HOME"]).mkdir()
        self.git(self.root, "init", "-q", "-b", "main")
        self.git(self.root, "config", "user.email", "fixture@example.invalid")
        self.git(self.root, "config", "user.name", "Source fixture")
        (self.root / "source.txt").write_text("before\n")
        self.git(self.root, "add", ".")
        self.git(self.root, "commit", "-qm", "before")
        self.before = self.git(self.root, "rev-parse", "HEAD")
        (self.root / "source.txt").write_text("qualified\n")
        self.git(self.root, "commit", "-qam", "qualified source")
        self.after = self.git(self.root, "rev-parse", "HEAD")
        self.git(self.root, "config", "core.hooksPath", "scripts/hooks")
        self.config = (self.root / ".git/config").read_bytes()
        self.keep = self.directory / ".ubd/keep.noindex"
        self.keep.mkdir(parents=True)
        (self.keep / "sentinel").write_text("unrelated owned data\n")

    def git(self, directory, *arguments, check=True):
        result = subprocess.run(["git", "-C", str(directory), *arguments], env=self.env,
                                capture_output=True, text=True, check=check)
        return result.stdout.strip() if check else result

    def publication(self, provider, *, root=None, before=None, after=None, after_clone=None):
        actual_run = rt._run
        self.views = []
        self.prepared = []
        def run(arguments, **kwargs):
            if arguments[:3] == ["agh", "repo", "push"]:
                view = Path(arguments[4])
                self.views.append(view)
                self.assertEqual(arguments[3], "example/source")
                self.assertIn("--no-anonymous-api", arguments)
                self.assertEqual(kwargs["cwd"], (root or self.root).resolve())
                self.assertNotIn("isolate_git_config", kwargs)
                change = json.loads(Path(arguments[arguments.index("--input") + 1]).read_text())
                self.assertEqual(change, [{"ref": rt.MAIN_REF, "before": before or self.before,
                                           "after": after or self.after}])
                return provider(arguments, view)
            result = actual_run(arguments, **kwargs)
            if arguments[:2] == ["git", "clone"]:
                self.prepared.append(Path(arguments[-1]))
                self.assertTrue(kwargs["isolate_git_config"])
                for flag in ("--local", "--no-checkout", "--single-branch", "--no-tags", "--template="):
                    self.assertIn(flag, arguments)
                if after_clone:
                    after_clone(Path(arguments[-1]))
            return result
        with patch.object(rt, "_run", side_effect=run):
            return rt.push_exact_source("https://github.com/example/source.git", root or self.root,
                                        before or self.before, after or self.after, env=self.env)

    def assert_cleaned_only_view(self):
        self.assertEqual((self.root / ".git/config").read_bytes(), self.config)
        self.assertEqual((self.root / "source.txt").read_text(), "qualified\n")
        self.assertTrue(all(not view.parents[1].exists() for view in self.prepared))
        self.assertEqual(list((self.directory / ".ubd").iterdir()), [self.keep])
        self.assertEqual((self.keep / "sentinel").read_text(), "unrelated owned data\n")

    def test_original_and_linked_checkout_use_identical_clean_nondense_transport(self):
        linked = self.directory / "linked checkout"
        self.git(self.root, "worktree", "add", "-q", "--detach", str(linked), self.after)
        def provider(arguments, view):
            self.assertTrue((view / ".git").is_dir())
            self.assertEqual(list(view.iterdir()), [view / ".git"])
            self.assertEqual(self.git(view, "rev-parse", "HEAD"), self.after)
            self.assertEqual(self.git(view, "rev-parse", "HEAD^{tree}"), self.git(self.root, "rev-parse", "HEAD^{tree}"))
            self.assertEqual(self.git(view, "cat-file", "-t", self.before), "commit")
            self.assertEqual(self.git(view, "config", "--local", "--get", "core.hooksPath", check=False).returncode, 1)
            self.assertFalse((view / ".git/objects/info/alternates").exists())
            return subprocess.CompletedProcess(arguments, 0, "native-created\n", "")
        for root in (self.root, linked):
            with self.subTest(root=root):
                result = self.publication(provider, root=root)
                self.assertEqual((result.returncode, result.stdout), (0, "native-created\n"))
                self.assertEqual(len(self.views), 1)
                self.assert_cleaned_only_view()

    def test_native_view_reads_qualified_blob_without_source_object_directory(self):
        blob = self.git(self.root, "rev-parse", self.after + ":source.txt")
        objects = self.root / ".git/objects"
        retained = self.root / ".git/retained-object-data"

        def provider(arguments, view):
            # The native transport receives its own directory, not authority to
            # open the caller's object directory. Exercise an actual Git read
            # with that pathname unavailable, then restore the source before
            # its existing post-operation bookend.
            objects.rename(retained)
            try:
                self.assertEqual(self.git(view, "cat-file", "blob", blob), "qualified")
            finally:
                retained.rename(objects)
            return subprocess.CompletedProcess(arguments, 0, "native-created\n", "")

        result = self.publication(provider)
        self.assertEqual(result.returncode, 0)
        self.assert_cleaned_only_view()

    def test_borrowed_caller_retains_packed_and_loose_history_without_any_provider(self):
        # Packed history, nested relative alternates, spaces, and a local loose
        # commit exercise Git's resolved object graph without a repack/copy.
        self.git(self.root, "repack", "-ad")
        middle = self.directory / "middle provider"
        borrowed = self.directory / "borrowed caller"
        self.git(self.directory, "clone", "--quiet", "--shared", str(self.root), str(middle))
        self.git(self.directory, "clone", "--quiet", "--shared", str(middle), str(borrowed))
        for caller, upstream in ((middle, self.root), (borrowed, middle)):
            objects = caller / ".git/objects"
            (objects / "info/alternates").write_text(
                os.path.relpath(upstream / ".git/objects", objects) + "\n")
        (borrowed / "source.txt").write_text("caller-local\n")
        self.git(borrowed, "-c", "user.email=fixture@example.invalid", "-c",
                 "user.name=Source fixture", "commit", "-qam", "caller local source")
        selected = self.git(borrowed, "rev-parse", "HEAD")
        blob = self.git(borrowed, "rev-parse", selected + ":source.txt")
        namespaces = [self.root / ".git/objects", middle / ".git/objects", borrowed / ".git/objects"]
        saved = {caller: ((caller / ".git/config").read_bytes(),
                         (caller / ".git/objects/info/alternates").read_bytes())
                 for caller in (middle, borrowed)}
        retained_files = list((namespaces[0] / "pack").glob("*.pack"))
        retained_files += list((namespaces[0] / "pack").glob("*.idx"))
        self.assertTrue(retained_files)
        retained_files.append(namespaces[-1] / blob[:2] / blob[2:])

        def provider(arguments, view):
            self.assertFalse((view / ".git/objects/info/alternates").exists())
            self.assertNotIn("alternate: ", self.git(view, "count-objects", "-v"))
            for original in retained_files:
                origin = namespaces[-1] if original.is_relative_to(namespaces[-1]) else namespaces[0]
                owned = view / ".git/objects" / original.relative_to(origin)
                old_stat, new_stat = original.stat(), owned.stat()
                self.assertEqual((new_stat.st_dev, new_stat.st_ino),
                                 (old_stat.st_dev, old_stat.st_ino),
                                 "publication must retain existing object DATA without recompression")
            retained = []
            try:
                for objects in namespaces:
                    moved = objects.with_name("held-object-data")
                    objects.rename(moved)
                    retained.append((objects, moved))
                self.assertEqual(self.git(view, "show", self.before + ":source.txt"), "before")
                self.assertEqual(self.git(view, "show", selected + ":source.txt"), "caller-local")
                self.git(view, "rev-list", "--quiet", "--objects", "--missing=error", selected)
            finally:
                for objects, moved in reversed(retained):
                    moved.rename(objects)
            return subprocess.CompletedProcess(arguments, 0, "native-created\n", "")

        result = self.publication(provider, root=borrowed, after=selected)
        self.assertEqual((result.returncode, result.stdout), (0, "native-created\n"), result.stderr)
        for caller, (config, alternate) in saved.items():
            self.assertEqual((caller / ".git/config").read_bytes(), config)
            self.assertEqual((caller / ".git/objects/info/alternates").read_bytes(), alternate)
        self.assertEqual(self.git(borrowed, "rev-parse", "HEAD"), selected)
        self.assertEqual((borrowed / "source.txt").read_text(), "caller-local\n")
        self.assert_cleaned_only_view()

    def test_borrowed_data_symlink_or_collision_refuses_before_native_publication(self):
        blob = self.git(self.root, "rev-parse", self.before + ":source.txt")
        original = self.root / ".git/objects" / blob[:2] / blob[2:]
        for hazard in ("symlink", "collision"):
            with self.subTest(hazard=hazard):
                borrowed = self.directory / ("borrowed " + hazard)
                self.git(self.directory, "clone", "--quiet", "--shared", str(self.root), str(borrowed))
                held = self.directory / "held-historical-object"
                def mutate(view):
                    if hazard == "symlink":
                        original.rename(held)
                        original.symlink_to(held)
                    else:
                        collision = view / ".git/objects" / blob[:2] / blob[2:]
                        collision.parent.mkdir(exist_ok=True)
                        collision.write_bytes(b"unrelated object data")
                def forbidden(*_):
                    self.fail("unsafe borrowed object reached native publication")
                try:
                    result = self.publication(forbidden, root=borrowed, after_clone=mutate)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("regular data file" if hazard == "symlink" else "object data collision",
                                  result.stderr)
                    self.assertFalse(self.views)
                finally:
                    if hazard == "symlink" and held.exists():
                        original.unlink()
                        held.rename(original)
                self.assertEqual(self.git(self.root, "cat-file", "blob", blob), "before")
                self.assert_cleaned_only_view()

    def test_borrowed_data_exdev_copy_preserves_history_without_any_provider(self):
        self.git(self.root, "repack", "-ad")
        borrowed = self.directory / "borrowed other volume"
        self.git(self.directory, "clone", "--quiet", "--shared", str(self.root), str(borrowed))
        namespaces = [self.root / ".git/objects", borrowed / ".git/objects"]
        pack = next((namespaces[0] / "pack").glob("*.pack"))
        def provider(arguments, view):
            self.assertFalse((view / ".git/objects/info/alternates").exists())
            owned = view / ".git/objects/pack" / pack.name
            self.assertEqual(owned.read_bytes(), pack.read_bytes())
            self.assertNotEqual((owned.stat().st_dev, owned.stat().st_ino),
                                (pack.stat().st_dev, pack.stat().st_ino))
            retained = []
            try:
                for objects in namespaces:
                    moved = objects.with_name("held-object-data")
                    objects.rename(moved)
                    retained.append((objects, moved))
                self.assertEqual(self.git(view, "show", self.before + ":source.txt"), "before")
                self.assertEqual(self.git(view, "show", self.after + ":source.txt"), "qualified")
                self.git(view, "rev-list", "--quiet", "--objects", "--missing=error", self.after)
            finally:
                for objects, moved in reversed(retained):
                    moved.rename(objects)
            return subprocess.CompletedProcess(arguments, 0, "native-created\n", "")
        # Exercise only the EXDEV result of the OS link operation; all copy,
        # comparison, history, ownership and provider-loss reads are actual.
        with patch.object(rt.os, "link", side_effect=OSError(errno.EXDEV, "cross-device link")):
            result = self.publication(provider, root=borrowed)
        self.assertEqual((result.returncode, result.stdout), (0, "native-created\n"), result.stderr)
        self.assert_cleaned_only_view()

    def test_borrowed_data_link_failure_refuses_without_copy_or_native_publication(self):
        borrowed = self.directory / "borrowed link failure"
        self.git(self.directory, "clone", "--quiet", "--shared", str(self.root), str(borrowed))
        def forbidden(*_):
            self.fail("failed object retention reached native publication")
        with patch.object(rt.os, "link", side_effect=PermissionError(13, "permission denied")):
            result = self.publication(forbidden, root=borrowed)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("permission denied", result.stderr)
        self.assertFalse(self.views)
        self.assert_cleaned_only_view()

    def test_missing_historical_blob_refuses_before_native_publication(self):
        old_blob = self.git(self.root, "rev-parse", self.before + ":source.txt")
        path = self.root / ".git/objects" / old_blob[:2] / old_blob[2:]
        retained = self.directory / "historical-blob-data"
        path.rename(retained)
        try:
            # The complete selected checkout does not establish complete
            # historical object availability for native strict packing.
            self.assertEqual(self.git(self.root, "show", "HEAD:source.txt"), "qualified")

            def forbidden(*_):
                self.fail("incomplete source history reached native publication")

            result = self.publication(forbidden)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("publication history", result.stderr)
            self.assertIn(old_blob, result.stderr)
            self.assertFalse(self.views)
            self.assertFalse(self.prepared)
        finally:
            retained.rename(path)
        self.assert_cleaned_only_view()

    def test_transport_missing_historical_blob_refuses_before_native_publication(self):
        old_blob = self.git(self.root, "rev-parse", self.before + ":source.txt")

        def remove_old_blob(view):
            (view / ".git/objects" / old_blob[:2] / old_blob[2:]).unlink()

        def forbidden(*_):
            self.fail("incomplete transport history reached native publication")

        result = self.publication(forbidden, after_clone=remove_old_blob)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("publication history", result.stderr)
        self.assertIn(old_blob, result.stderr)
        self.assertFalse(self.views)
        self.assertEqual(len(self.prepared), 1)
        self.assertEqual(self.git(self.root, "cat-file", "blob", old_blob), "before")
        self.assert_cleaned_only_view()

    def test_wrong_head_and_nonancestor_never_reach_native_publication(self):
        tree = self.git(self.root, "rev-parse", "HEAD^{tree}")
        orphan = subprocess.run(["git", "-C", str(self.root), "commit-tree", tree], input="orphan\n",
                                env=self.env, capture_output=True, text=True, check=True).stdout.strip()
        def forbidden(*_):
            self.fail("invalid source reached Agh")
        for before, after in ((orphan, self.after), (self.after, self.before)):
            with self.subTest(before=before, after=after):
                self.assertNotEqual(self.publication(forbidden, before=before, after=after).returncode, 0)
                self.assertFalse(self.views)
                self.assert_cleaned_only_view()

    def test_source_or_view_change_during_clone_refuses_before_native_publication(self):
        for changed in ("source", "transport"):
            with self.subTest(changed=changed):
                def mutate(view):
                    target = self.root if changed == "source" else view
                    self.git(target, "update-ref", "HEAD", self.before, self.after)
                def forbidden(*_):
                    self.fail("changed source reached Agh")
                result = self.publication(forbidden, after_clone=mutate)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("qualified commit", result.stderr)
                self.assertFalse(self.views)
                if changed == "source":
                    self.git(self.root, "update-ref", "HEAD", self.after, self.before)
                self.assert_cleaned_only_view()

    def test_native_refusal_is_exact_and_post_operation_mutation_preserves_native_answer(self):
        refused = self.publication(lambda args, view: subprocess.CompletedProcess(args, 17, "native-data\n", "native-refusal\n"))
        self.assertEqual((refused.returncode, refused.stdout, refused.stderr), (17, "native-data\n", "native-refusal\n"))
        self.assert_cleaned_only_view()
        def changed(arguments, view):
            self.git(view, "update-ref", "HEAD", self.before, self.after)
            return subprocess.CompletedProcess(arguments, 0, "native-created\n", "native-diagnostic\n")
        result = self.publication(changed)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "native-created\n")
        self.assertIn("native-diagnostic", result.stderr)
        self.assertIn("qualified commit", result.stderr)
        self.assert_cleaned_only_view()

    def test_global_config_isolation_is_fixed_and_does_not_change_default_operations(self):
        global_config = Path(self.env["HOME"]) / ".gitconfig"
        global_config.write_text('[core]\n hooksPath = /not-a-publication-hook\n[include]\n path = /missing-source-config\n')
        original = global_config.read_bytes()
        command = ["git", "config", "--global", "--get", "core.hooksPath"]
        ordinary = rt._run(command, env=self.env, timeout=5)
        isolated = rt._run(command, env=self.env, timeout=5, isolate_git_config=True)
        self.assertEqual((ordinary.returncode, ordinary.stdout.strip()), (0, "/not-a-publication-hook"))
        self.assertEqual(isolated.returncode, 1)
        result = self.publication(lambda args, view: subprocess.CompletedProcess(args, 0, "native-created\n", ""))
        self.assertEqual(result.returncode, 0)
        self.assertEqual(global_config.read_bytes(), original)
        self.assertEqual(rt._run([sys.executable, "-c", "raise SystemExit(99)"],
                                 isolate_git_config=True).returncode, 2)
        self.assert_cleaned_only_view()

    def test_unsafe_existing_parent_refuses_before_clone_or_foreign_writes(self):
        victim = self.directory / "foreign victim"
        victim.mkdir()
        (victim / "sentinel").write_text("preserve\n")
        symlink = self.directory / "unsafe parent"
        symlink.symlink_to(victim, target_is_directory=True)
        validate = rt._publication_parent
        for parent in (symlink, victim):
            with self.subTest(parent=parent), \
                    patch.object(rt, "_publication_parent", side_effect=lambda _fixed: validate(parent)):
                def forbidden(*_):
                    self.fail("unsafe parent reached Agh")
                result = self.publication(forbidden)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("system temporary", result.stderr)
                self.assertFalse(self.views)
                self.assertEqual(list(victim.iterdir()), [victim / "sentinel"])
                self.assertEqual((victim / "sentinel").read_text(), "preserve\n")
                self.assert_cleaned_only_view()


@unittest.skipUnless(os.name == "posix" and rt._process_owner.exit_observation_available(),
                     "requires the supported local POSIX source transport profile")
class SourceIntakeViewTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="source-intake-view-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.root = self.directory / "original checkout"
        self.root.mkdir()
        self.env = dict(os.environ, HOME=str(self.directory / "home"), XDG_CONFIG_HOME=str(self.directory / "xdg"))
        Path(self.env["HOME"]).mkdir()
        self.git(self.root, "init", "-q", "-b", "main")
        self.git(self.root, "config", "user.email", "fixture@example.invalid")
        self.git(self.root, "config", "user.name", "Source fixture")
        (self.root / "source.txt").write_text("before\n")
        self.git(self.root, "add", ".")
        self.git(self.root, "commit", "-qm", "before")
        self.before = self.git(self.root, "rev-parse", "HEAD")
        self.source = self.directory / "provider checkout"
        self.git(self.directory, "clone", "-q", str(self.root), str(self.source))
        self.git(self.source, "config", "user.email", "fixture@example.invalid")
        self.git(self.source, "config", "user.name", "Source fixture")
        (self.source / "source.txt").write_text("native fetched source\n")
        self.git(self.source, "commit", "-qam", "new source")
        self.oid = self.git(self.source, "rev-parse", "HEAD")
        self.assertNotEqual(self.git(self.root, "cat-file", "-e", self.oid, check=False).returncode, 0)
        self.git(self.root, "config", "core.hooksPath", "scripts/hooks")
        self.git(self.root, "config", "url.file:///not-a-source/.insteadOf", "/")
        self.marker = self.directory / "unexpected-hook"
        self.git(self.root, "config", "hook.ref-transaction.command", "touch " + str(self.marker))
        self.git(self.root, "config", "hook.ref-transaction.event", "reference-transaction")
        self.config = (self.root / ".git/config").read_bytes()
        (self.root / ".git/FETCH_HEAD").write_text("preserve fetch head\n")
        (self.root / "source.txt").write_text("original dirty source\n")
        (self.root / "untracked").write_text("preserve untracked\n")
        self.refs = self.git(self.root, "show-ref")
        self.views = []
        self.intakes = []

    def git(self, directory, *arguments, check=True):
        result = subprocess.run(["git", "-C", str(directory), *arguments], env=self.env,
                                capture_output=True, text=True, check=check)
        return result.stdout.strip() if check else result

    def intake(self, *, root=None, provider=None, after_local=None, call_env=None,
               timeout=rt.FETCH_TIMEOUT_S):
        actual_run = rt._run
        def agh(repository, arguments, **kwargs):
            self.assertEqual(repository, "example/source")
            self.assertEqual(arguments[:3], ["repo", "fetch", repository])
            self.assertEqual(arguments[4:], ["--ref", self.oid, "--into", "refs/agh/land-discovery",
                                             "--checkout-closure"])
            self.assertGreater(kwargs["timeout"], 0)
            self.assertLessEqual(kwargs["timeout"], timeout)
            view = Path(arguments[3])
            self.views.append(view)
            self.assertEqual(list(view.iterdir()), [view / ".git"])
            self.assertEqual(self.git(view, "config", "--local", "--get", "core.hooksPath", check=False).returncode, 1)
            if provider is not None:
                return provider(arguments, view)
            # Native intake receives independently of the caller's partial
            # object store. A direct fetch through the borrowed source view
            # would incorrectly advertise its incomplete history as complete.
            received = view.parent / "native-received.git"
            done = actual_run(["git", "clone", "--quiet", "--bare", "--no-hardlinks",
                               "--template=", "--", str(self.source), str(received)],
                              env=self.env, cwd=view, timeout=10, isolate_git_config=True)
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertFalse((received / "objects/info/alternates").exists())
            shutil.copytree(received / "objects", view / ".git/objects", dirs_exist_ok=True)
            done = actual_run(["git", "-C", str(view), "update-ref", "refs/agh/land-discovery", self.oid],
                              env=self.env, cwd=view, timeout=10, isolate_git_config=True)
            self.assertEqual(done.returncode, 0, done.stderr)
            return subprocess.CompletedProcess(arguments, 0, "native-acquired\n", "native-diagnostic\n")
        def run(arguments, **kwargs):
            if kwargs.get("git_object_directory") is not None:
                self.intakes.append(arguments)
                destination = Path(arguments[arguments.index("--git-dir") + 1])
                self.assertTrue((destination / "config").is_file())
                self.assertEqual(self.git(destination, "for-each-ref"), "")
                self.assertEqual(self.git(destination, "config", "--local", "--get", "core.hooksPath", check=False).returncode, 1)
                self.assertTrue(kwargs["isolate_git_config"])
                self.assertEqual(kwargs["git_object_directory"], (self.root / ".git/objects").resolve())
                self.assertEqual(arguments[-2:], ["index-pack", "--stdin"])
                self.assertIsNotNone(kwargs.get("input_file"))
                self.assertIsNone(kwargs.get("input_text"))
                stream = kwargs["input_file"]
                class DescriptorOnly:
                    def fileno(self):
                        return stream.fileno()
                    def read(self, *args):
                        raise AssertionError("pack payload must not be read into Python memory")
                kwargs["input_file"] = DescriptorOnly()
                self.assertNotIn("-C", arguments)
            done = actual_run(arguments, **kwargs)
            if after_local is not None:
                after_local(arguments, kwargs, done)
            return done
        with patch.object(rt, "_agh", side_effect=agh), patch.object(rt, "_run", side_effect=run):
            return rt.fetch_exact_source("https://github.com/example/source.git", root or self.root,
                                         self.oid, env=call_env or self.env, timeout=timeout)

    def assert_original_unchanged(self):
        self.assertEqual((self.root / ".git/config").read_bytes(), self.config)
        self.assertEqual(self.git(self.root, "rev-parse", "HEAD"), self.before)
        self.assertEqual(self.git(self.root, "show-ref"), self.refs)
        self.assertEqual((self.root / ".git/FETCH_HEAD").read_text(), "preserve fetch head\n")
        self.assertEqual((self.root / "source.txt").read_text(), "original dirty source\n")
        self.assertEqual((self.root / "untracked").read_text(), "preserve untracked\n")
        self.assertFalse(self.marker.exists())
        self.assertTrue(all(not view.parents[1].exists() for view in self.views))

    def shared_payload(self, payload):
        (self.root / "retained.bin").write_bytes(payload)
        self.git(self.root, "add", "retained.bin")
        self.git(self.root, "-c", "hook.ref-transaction.command=true", "commit", "-qm", "shared payload")
        self.before = self.git(self.root, "rev-parse", "HEAD")
        self.refs = self.git(self.root, "show-ref")
        self.git(self.source, "fetch", "-q", str(self.root), "main")
        self.git(self.source, "reset", "--hard", self.before)
        (self.source / "source.txt").write_text("native fetched source\n")
        self.git(self.source, "commit", "-qam", "new selected source")
        self.oid = self.git(self.source, "rev-parse", "HEAD")
        return self.git(self.root, "rev-parse", "HEAD:retained.bin")

    def test_unchanged_large_blob_is_hashed_but_absent_from_actual_import_pack(self):
        shared = self.shared_payload(random.Random(4321).randbytes(4 * 1024 * 1024))
        packs = []
        def inspect(arguments, kwargs, done):
            if "pack-objects" not in arguments or done.returncode:
                return
            ids = set(kwargs["input_text"].splitlines())
            self.assertNotIn(shared, ids)
            prefix = str(arguments[-1]) + "-" + done.stdout.strip()
            with Path(prefix + ".idx").open("rb") as index:
                shown = subprocess.run(["git", "show-index"], stdin=index, env=self.env,
                                       capture_output=True, text=True, check=True)
            actual = {row.split()[1] for row in shown.stdout.splitlines()}
            self.assertEqual(actual, ids)
            self.assertNotIn(shared, actual)
            packs.append(Path(prefix + ".pack").stat().st_size)
        result = self.intake(after_local=inspect)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(packs), 1)
        self.assertLess(packs[0], 128 * 1024)
        self.assertEqual(self.git(self.root, "cat-file", "-s", shared), str(4 * 1024 * 1024))
        self.assert_original_unchanged()

    def test_present_blob_with_valid_zlib_but_wrong_raw_hash_refuses_before_import(self):
        shared = self.shared_payload(b"retained selected body\n")
        path = self.root / ".git/objects" / shared[:2] / shared[2:]
        path.chmod(0o644)
        wrong = b"X" * len(b"retained selected body\n")
        corrupted = zlib.compress(b"blob " + str(len(wrong)).encode() + b"\0" + wrong)
        path.write_bytes(corrupted)
        result = self.intake()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("framing/hash differs", result.stderr)
        self.assertIn("native-diagnostic", result.stderr)
        self.assertFalse(self.intakes)
        self.assertEqual(path.read_bytes(), corrupted)
        self.assert_original_unchanged()

    def test_corrupt_present_blob_is_not_accepted_as_a_missing_object(self):
        shared = self.shared_payload(b"retained selected body\n")
        path = self.root / ".git/objects" / shared[:2] / shared[2:]
        path.chmod(0o644)
        path.write_bytes(b"not a compressed Git object")
        result = self.intake()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("native-diagnostic", result.stderr)
        self.assertFalse(self.intakes)
        self.assertEqual(path.read_bytes(), b"not a compressed Git object")
        self.assert_original_unchanged()

    def test_missing_ancestor_commit_header_is_imported_without_moving_original_head(self):
        ancestor = self.before
        raw = subprocess.check_output(["git", "-C", str(self.root), "cat-file", "commit", ancestor], env=self.env)
        tree = self.git(self.root, "rev-parse", "HEAD^{tree}")
        descendant = subprocess.run(["git", "-C", str(self.root), "commit-tree", tree, "-p", ancestor],
                                    input="retained current head\n", text=True, env=self.env,
                                    capture_output=True, check=True).stdout.strip()
        self.git(self.root, "-c", "hook.ref-transaction.command=true", "update-ref", "HEAD", descendant)
        self.before, self.refs = descendant, self.git(self.root, "show-ref")
        (self.root / ".git/objects" / ancestor[:2] / ancestor[2:]).unlink()
        result = self.intake()
        self.assertEqual(result.returncode, 0, result.stderr)
        restored = subprocess.check_output(["git", "-C", str(self.root), "cat-file", "commit", ancestor], env=self.env)
        self.assertEqual(restored, raw)
        self.assertEqual(hashlib.sha1(b"commit " + str(len(raw)).encode() + b"\0" + restored).hexdigest(), ancestor)
        self.assert_original_unchanged()

    def test_zero_new_objects_skips_pack_and_import_but_rechecks_original_selected_closure(self):
        first = self.intake()
        self.assertEqual(first.returncode, 0, first.stderr)
        self.intakes.clear()
        packed, checked = [], []
        def inspect(arguments, kwargs, done):
            if "pack-objects" in arguments:
                packed.append(arguments)
            if (arguments[:3] == ["git", "-C", str(self.root.resolve())]
                    and "rev-list" in arguments and "--objects" in arguments and "--missing=error" in arguments):
                checked.append(done.returncode)
        second = self.intake(after_local=inspect)
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertFalse(packed)
        self.assertFalse(self.intakes)
        self.assertEqual(checked, [0])
        self.assert_original_unchanged()

    def test_source_stream_budgets_are_exact_and_independent_of_metadata_limit(self):
        bodies = [b"a" * 1024, b"b" * 1024]
        ids = [hashlib.sha1(b"blob 1024\0" + body).hexdigest() for body in bodies]
        raw = b"".join(oid.encode() + b" blob 1024\n" + body + b"\n" for oid, body in zip(ids, bodies))
        expected = {oid: ("blob", 1024) for oid in ids}
        with patch.object(rt, "MAX_OBJECT_READ_BYTES", 1):
            rows = list(rt._verified_original_rows(io.BytesIO(raw), ids, expected=expected,
                        retain_body=False, byte_budget=2048, object_limit=1024))
        self.assertEqual([kind for _oid, kind, _body in rows], [b"blob", b"blob"])
        self.assertTrue(all(body is None for _oid, _kind, body in rows))
        for budget, maximum, message in ((2047, 1024, "source byte budget"),
                                          (2048, 1023, "source object budget")):
            with self.subTest(budget=budget, maximum=maximum), self.assertRaisesRegex(ValueError, message):
                list(rt._verified_original_rows(io.BytesIO(raw), ids, expected=expected,
                     retain_body=False, byte_budget=budget, object_limit=maximum))

    def test_source_reader_deadline_stops_and_reaps_its_blocked_owned_child(self):
        actual = subprocess.Popen
        children = []
        def blocked(arguments, **kwargs):
            if arguments != ["git", "-C", str(self.root), "cat-file", "--batch"]:
                return actual(arguments, **kwargs)
            child = actual([sys.executable, "-c", "import time; time.sleep(30)"], **kwargs)
            children.append(child)
            return child
        start = time.monotonic()
        with patch.object(rt.subprocess, "Popen", side_effect=blocked):
            result, held = rt._verified_present_objects(self.root,
                {"1" * 40: ("blob", 4)}, env=self.env, timeout=0.1)
        self.assertEqual(result.returncode, 124)
        self.assertIsNone(held)
        self.assertLess(time.monotonic() - start, 5)
        self.assertEqual(len(children), 1)
        self.assertIsNotNone(children[0].returncode)
        with self.assertRaises(ChildProcessError):
            os.waitpid(children[0].pid, os.WNOHANG)
        self.assert_original_unchanged()

    def test_new_objects_survive_private_cleanup_without_original_config_refs_or_checkout_changes(self):
        result = self.intake(call_env=dict(self.env, GIT_OBJECT_DIRECTORY="/not-the-object-output"))
        self.assertEqual((result.returncode, result.stdout, result.stderr),
                         (0, "native-acquired\n", "native-diagnostic\n"))
        self.assertEqual(len(self.intakes), 1)
        self.assertEqual(self.git(self.root, "show", self.oid + ":source.txt"), "native fetched source")
        self.assertFalse((self.root / ".git/objects/info/alternates").exists())
        self.assert_original_unchanged()

    def test_caller_source_deadline_is_preserved_through_native_and_local_intake(self):
        result = self.intake(timeout=180)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.git(self.root, "show", self.oid + ":source.txt"), "native fetched source")
        self.assert_original_unchanged()

    def test_original_commit_without_its_tree_is_repaired_without_changing_caller_state(self):
        body = subprocess.check_output(["git", "-C", str(self.source), "cat-file", "commit", self.oid], env=self.env)
        imported = subprocess.run(["git", "-C", str(self.root), "hash-object", "-t", "commit", "-w", "--stdin"],
                                  input=body, capture_output=True, env=self.env, check=True).stdout.decode().strip()
        self.assertEqual(imported, self.oid)
        self.assertEqual(self.git(self.root, "cat-file", "-t", self.oid), "commit")
        self.assertNotEqual(self.git(self.root, "cat-file", "-e", self.oid + "^{tree}", check=False).returncode, 0)
        # Model original-commit ancestry intake: the missing tree belongs to
        # an already-held ancestor, so ordinary fetch negotiation omits it.
        tree = self.git(self.root, "rev-parse", "HEAD^{tree}")
        descendant = subprocess.run(["git", "-C", str(self.root), "commit-tree", tree, "-p", self.oid],
                                    input="descendant with retained current tree\n", capture_output=True,
                                    text=True, env=self.env, check=True).stdout.strip()
        # This ref write constructs the fixture before intake. Suppress only
        # its poison-hook command; the unchanged saved caller configuration
        # still detects any hook execution by the actual intake below.
        self.git(self.root, "-c", "hook.ref-transaction.command=true",
                 "update-ref", "refs/heads/main", descendant)
        self.before = descendant
        self.refs = self.git(self.root, "show-ref")
        self.assertFalse(self.marker.exists())
        result = self.intake()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.git(self.root, "show", self.oid + ":source.txt"), "native fetched source")
        self.assertFalse((self.root / ".git/shallow").exists())
        self.assert_original_unchanged()

    def test_local_source_route_preserves_explicit_and_default_deadlines(self):
        oid = "1" * 40
        done = subprocess.CompletedProcess([], 0, "", "")
        for timeout in (180, rt.FETCH_TIMEOUT_S):
            with self.subTest(timeout=timeout), patch.object(rt, "_run", return_value=done) as run:
                result = rt.fetch_exact_source("file:///literal-source.git", self.root, oid,
                                               env=self.env, timeout=timeout)
                self.assertIs(result, done)
                self.assertEqual(run.call_args.kwargs["timeout"], timeout)
        with patch.object(rt, "_run", return_value=done) as run:
            rt.fetch_exact_source("file:///literal-source.git", self.root, oid, env=self.env)
            self.assertEqual(run.call_args.kwargs["timeout"], rt.FETCH_TIMEOUT_S)

    def test_checkout_intake_does_not_require_unselected_historical_blobs(self):
        historical = self.root / "historical.bin"
        historical.write_bytes(b"old historical payload\x00\xff\r\n")
        self.git(self.root, "add", "historical.bin")
        self.git(self.root, "commit", "-qm", "historical payload")
        missing = self.git(self.root, "rev-parse", "HEAD:historical.bin")
        missing_tree = self.git(self.root, "rev-parse", "HEAD^{tree}")
        historical.unlink()
        self.git(self.root, "add", "historical.bin")
        self.git(self.root, "commit", "-qm", "selected checkout excludes history payload")
        self.before = self.git(self.root, "rev-parse", "HEAD")
        self.refs = self.git(self.root, "show-ref")
        self.marker.unlink(missing_ok=True)
        self.git(self.source, "fetch", "-q", str(self.root), "main")
        self.git(self.source, "reset", "--hard", self.before)
        (self.source / "source.txt").write_text("native fetched source\n")
        binary = b"current snapshot\x00\xff\r\nexact bytes\r"
        (self.source / "binary.bin").write_bytes(binary)
        self.git(self.source, "add", ".")
        self.git(self.source, "commit", "-qm", "selected binary snapshot")
        self.oid = self.git(self.source, "rev-parse", "HEAD")
        for item in (missing, missing_tree):
            (self.root / ".git/objects" / item[:2] / item[2:]).unlink()
            self.assertNotEqual(self.git(self.root, "cat-file", "-e", item, check=False).returncode, 0)

        result = self.intake()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(subprocess.check_output(
            ["git", "-C", str(self.root), "cat-file", "blob", self.oid + ":binary.bin"],
            env=self.env), binary)
        self.assertEqual(self.git(self.root, "merge-base", self.before, self.oid), self.before)
        for item in (missing, missing_tree):
            self.assertNotEqual(self.git(self.root, "cat-file", "-e", item, check=False).returncode, 0)
        self.assert_original_unchanged()

    def test_sparse_oversized_pack_refuses_before_object_import(self):
        oversized = []
        def expand_pack(arguments, kwargs, done):
            if "pack-objects" not in arguments or done.returncode:
                return
            pack = Path(str(arguments[-1]) + "-" + done.stdout.strip() + ".pack")
            mode = pack.stat().st_mode & 0o777
            pack.chmod(mode | 0o200)
            try:
                with pack.open("r+b") as stream:
                    stream.truncate(2 * 1024 ** 3 + 1)
            finally:
                pack.chmod(mode)
            observed = pack.stat()
            self.assertEqual(observed.st_size, 2 * 1024 ** 3 + 1)
            self.assertLess(observed.st_blocks * 512, 1024 * 1024)
            oversized.append(pack)
        result = self.intake(after_local=expand_pack)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("snapshot pack exceeds 2 GiB", result.stderr)
        self.assertIn("native-diagnostic", result.stderr)
        self.assertEqual(len(oversized), 1)
        self.assertFalse(self.intakes)
        self.assert_original_unchanged()

    def test_snapshot_gitlinks_do_not_require_unowned_submodule_objects(self):
        foreign = "d" * 40
        self.git(self.source, "update-index", "--add", "--cacheinfo", "160000," + foreign + ",module")
        self.git(self.source, "commit", "-qm", "snapshot with external submodule")
        self.oid = self.git(self.source, "rev-parse", "HEAD")
        result = self.intake()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.git(self.root, "ls-tree", self.oid, "module"),
                         "160000 commit " + foreign + "\tmodule")
        self.assertNotEqual(self.git(self.root, "cat-file", "-e", foreign, check=False).returncode, 0)
        self.assert_original_unchanged()

    def test_linked_checkout_intake_targets_original_common_objects(self):
        linked = self.directory / "linked checkout"
        self.git(self.root, "worktree", "add", "-q", "--detach", str(linked), self.before)
        # The deliberate original hook is expected to run for this fixture's
        # own worktree registration, before the intake operation under test.
        self.marker.unlink(missing_ok=True)
        self.refs = self.git(self.root, "show-ref")
        result = self.intake(root=linked)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.git(linked, "show", self.oid + ":source.txt"), "native fetched source")
        self.assertEqual((linked / "source.txt").read_text(), "before\n")
        self.assert_original_unchanged()

    def test_unborn_original_repository_is_supported_without_creating_its_head(self):
        empty = self.directory / "unborn checkout"
        self.git(self.directory, "init", "-q", "-b", "main", str(empty))
        original_config = (empty / ".git/config").read_bytes()
        # This assertion concerns the same fixed intake profile with another
        # actual original object directory, not the helper's primary fixture.
        self.root = empty
        result = self.intake()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.git(empty, "show", self.oid + ":source.txt"), "native fetched source")
        self.assertEqual(self.git(empty, "symbolic-ref", "HEAD"), "refs/heads/main")
        self.assertEqual(self.git(empty, "show-ref", check=False).returncode, 1)
        self.assertEqual((empty / ".git/config").read_bytes(), original_config)
        self.assertFalse((empty / ".git/FETCH_HEAD").exists())
        self.assertTrue(all(not view.parents[1].exists() for view in self.views))

    def test_native_refusal_is_exact_and_does_not_start_local_intake(self):
        result = self.intake(provider=lambda args, view: subprocess.CompletedProcess(args, 17, "native-data\n", "native-refusal\n"))
        self.assertEqual((result.returncode, result.stdout, result.stderr), (17, "native-data\n", "native-refusal\n"))
        self.assertFalse(self.intakes)
        self.assertNotEqual(self.git(self.root, "cat-file", "-e", self.oid, check=False).returncode, 0)
        self.assert_original_unchanged()

    def test_success_without_exact_materialized_private_ref_refuses_before_intake(self):
        def wrong(arguments, view):
            self.git(view, "fetch", "--quiet", "--no-write-fetch-head", "--no-tags",
                     str(self.source), self.before)
            self.git(view, "update-ref", "refs/agh/land-discovery", self.before)
            return subprocess.CompletedProcess(arguments, 0, "native-data\n", "native-diagnostic\n")
        for provider in (lambda args, view: subprocess.CompletedProcess(args, 0, "native-data\n", "native-diagnostic\n"), wrong):
            with self.subTest(provider=provider):
                result = self.intake(provider=provider)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "native-data\n")
                self.assertIn("native-diagnostic", result.stderr)
                self.assertFalse(self.intakes)
                self.assert_original_unchanged()

    def test_shallow_original_with_complete_selected_tree_needs_no_historical_blob(self):
        # Deliberately retain a valid shallow ancestry boundary while omitting
        # an unrelated old body. The current checkout's own body is complete.
        ancestor = self.before
        historical = self.git(self.root, "rev-parse", ancestor + ":source.txt")
        (self.root / "source.txt").write_text("new original selected body\n")
        self.git(self.root, "commit", "-qam", "original selected body")
        self.before = self.git(self.root, "rev-parse", "HEAD")
        self.refs = self.git(self.root, "show-ref")
        (self.root / "source.txt").write_text("original dirty source\n")
        (self.root / ".git/shallow").write_text(ancestor + "\n")
        (self.root / ".git/objects" / historical[:2] / historical[2:]).unlink()
        # The fixture's own commit above intentionally exercised the hook.
        self.marker.unlink(missing_ok=True)
        result = self.intake()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.git(self.root, "show", self.oid + ":source.txt"), "native fetched source")
        self.assertNotEqual(self.git(self.root, "cat-file", "-e", historical, check=False).returncode, 0)
        self.assertEqual((self.root / ".git/shallow").read_text(), ancestor + "\n")
        self.assert_original_unchanged()

    def test_native_selected_closure_without_historical_body_survives_private_cleanup(self):
        self.selected_closure_control(missing_selected=False)

    def test_missing_selected_body_refuses_even_after_native_success(self):
        self.selected_closure_control(missing_selected=True)

    def test_preexisting_selected_tree_with_missing_body_is_completed(self):
        self.selected_closure_control(missing_selected=False, preseed_selected_tree=True)

    def selected_closure_control(self, *, missing_selected, preseed_selected_tree=False):
        empty = self.directory / "empty recipient"
        self.git(self.directory, "init", "-q", "-b", "main", str(empty))
        original_config = (empty / ".git/config").read_bytes()
        historical = self.git(self.source, "rev-parse", self.before + ":source.txt")
        selected = self.git(self.source, "rev-parse", self.oid + ":source.txt")
        if preseed_selected_tree:
            shutil.copytree(self.source / ".git/objects", empty / ".git/objects", dirs_exist_ok=True)
            for oid in [historical, selected]:
                (empty / ".git/objects" / oid[:2] / oid[2:]).unlink()
            self.git(empty, "cat-file", "-e", self.oid + "^{tree}")
            self.assertNotEqual(self.git(empty, "cat-file", "-e", selected, check=False).returncode, 0)
        self.root = empty
        def selected_provider(arguments, view):
            # Model the native API's actual selected checkout + ancestry shape
            # with real Git objects, rather than an unfiltered historical fetch.
            shutil.copytree(self.source / ".git/objects", view / ".git/objects", dirs_exist_ok=True)
            for oid in [historical] + ([selected] if missing_selected else []):
                (view / ".git/objects" / oid[:2] / oid[2:]).unlink()
            self.git(view, "update-ref", "refs/agh/land-discovery", self.oid)
            return subprocess.CompletedProcess(arguments, 0, "native-selected\n", "native-diagnostic\n")
        result = self.intake(provider=selected_provider)
        self.assertEqual(result.stdout, "native-selected\n")
        if missing_selected:
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("native-diagnostic", result.stderr)
            self.assertNotEqual(self.git(empty, "cat-file", "-e", selected, check=False).returncode, 0)
        else:
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(self.git(empty, "show", self.oid + ":source.txt"), "native fetched source")
            self.assertIn(self.before, self.git(empty, "rev-list", "--parents", self.oid))
        self.assertNotEqual(self.git(empty, "cat-file", "-e", historical, check=False).returncode, 0)
        self.assertEqual((empty / ".git/config").read_bytes(), original_config)
        self.assertEqual(self.git(empty, "symbolic-ref", "HEAD"), "refs/heads/main")
        self.assertEqual(self.git(empty, "show-ref", check=False).returncode, 1)
        self.assertEqual(self.git(empty, "remote"), "")
        self.assertFalse((empty / ".git/FETCH_HEAD").exists())
        self.assertFalse((empty / ".git/objects/info/alternates").exists())
        self.assertTrue(all(not view.parents[1].exists() for view in self.views))

    def test_original_change_after_acquisition_preserves_native_answer_and_refuses_intake(self):
        def changed(arguments, kwargs, done):
            if "refs/agh/land-discovery" in arguments and "rev-parse" in arguments:
                tree = self.git(self.root, "rev-parse", "HEAD^{tree}")
                orphan = subprocess.run(["git", "-C", str(self.root), "commit-tree", tree], input="changed\n",
                                        env=self.env, capture_output=True, text=True, check=True).stdout.strip()
                self.git(self.root, "update-ref", "HEAD", orphan, self.before)
        result = self.intake(after_local=changed)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "native-acquired\n")
        self.assertIn("original HEAD changed", result.stderr)
        self.assertFalse(self.intakes)
        self.assertTrue(all(not view.parents[1].exists() for view in self.views))

    def test_original_object_directory_replacement_refuses_before_local_intake(self):
        def replace(arguments, kwargs, done):
            if "refs/agh/land-discovery" in arguments and "rev-parse" in arguments:
                objects = self.root / ".git/objects"
                objects.rename(self.root / ".git/original-objects")
                objects.mkdir()
        result = self.intake(after_local=replace)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "native-acquired\n")
        self.assertIn("original object directory changed", result.stderr)
        self.assertFalse(self.intakes)
        self.assertEqual(list((self.root / ".git/objects").iterdir()), [])
        self.assertTrue(all(not view.parents[1].exists() for view in self.views))

    def test_local_intake_failure_keeps_native_streams_and_original_state(self):
        actual_run = rt._run
        def refused(arguments, **kwargs):
            if kwargs.get("git_object_directory") is not None:
                return subprocess.CompletedProcess(arguments, 19, "", "local object write refused\n")
            return actual_run(arguments, **kwargs)
        with patch.object(rt, "_run", side_effect=refused):
            result = self.intake()
        self.assertEqual((result.returncode, result.stdout), (19, "native-acquired\n"))
        self.assertIn("native-diagnostic", result.stderr)
        self.assertIn("local object write refused", result.stderr)
        self.assertNotEqual(self.git(self.root, "cat-file", "-e", self.oid, check=False).returncode, 0)
        self.assert_original_unchanged()

    def test_object_output_profile_requires_isolated_constructed_local_git(self):
        objects = (self.root / ".git/objects").resolve()
        for command, options in ((["git", "version"], {}), ([sys.executable, "-c", "raise SystemExit(99)"], {"isolate_git_config": True})):
            with self.subTest(command=command):
                self.assertEqual(rt._run(command, git_object_directory=objects, **options).returncode, 2)
        self.assertEqual(rt._run(["git", "version"], isolate_git_config=True,
                                 git_object_directory=Path("relative")).returncode, 2)


@unittest.skipUnless(os.name == "posix" and rt._process_owner.exit_observation_available(),
                     "requires POSIX nonreaping process ownership")
class OperationLifetimeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def no_live_process(self, pid):
        result = subprocess.run(["/bin/ps", "-p", str(pid), "-o", "stat="], capture_output=True, text=True)
        self.assertTrue(result.returncode != 0 or result.stdout.strip().startswith("Z"), result.stdout)

    def await_not_live(self, pid):
        deadline = time.monotonic() + 5
        while True:
            result = subprocess.run(["/bin/ps", "-p", str(pid), "-o", "stat="], capture_output=True, text=True)
            if result.returncode != 0 or result.stdout.strip().startswith("Z"):
                return
            self.assertLess(time.monotonic(), deadline, f"owned process {pid} remains live")
            time.sleep(0.02)

    def run_owner(self, source, timeout=0.4):
        with patch.object(rt, "STOP_GRACE_S", 0.15), patch.object(rt, "KILL_GRACE_S", 2):
            return rt._run([sys.executable, "-c", source, str(self.root)], timeout=timeout)

    def test_status_stdin_and_output_remain_exact_and_refusal_is_not_timeout(self):
        code = "import sys;sys.stdout.buffer.write(sys.stdin.buffer.read()+b'\\r\\n');sys.stderr.write('not our ref\\n');sys.exit(7)"
        result = rt._run([sys.executable, "-c", code], input_text="payload", timeout=2)
        self.assertEqual((result.returncode, result.stdout, result.stderr), (7, "payload\n", "not our ref\n"))

    def test_timeout_first_allows_native_owner_to_reap_its_separate_child_group(self):
        source = """import os,signal,subprocess,sys,time
from pathlib import Path
root=Path(sys.argv[1]);child=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)'],preexec_fn=lambda:os.setpgid(0,0))
(root/'child').write_text(str(child.pid))
def stop(*_):
 os.killpg(child.pid,signal.SIGTERM);child.wait();(root/'cooperative').write_text('reaped');raise SystemExit(0)
signal.signal(signal.SIGTERM,stop)
time.sleep(60)
"""
        result = self.run_owner(source)
        self.assertEqual(result.returncode, 124)
        self.assertEqual((self.root / "cooperative").read_text(), "reaped")
        self.no_live_process(int((self.root / "child").read_text()))

    def test_timeout_escalates_and_stops_ignored_term_descendants_in_owned_group(self):
        source = """import signal,subprocess,sys,time
from pathlib import Path
signal.signal(signal.SIGTERM,signal.SIG_IGN)
child=subprocess.Popen([sys.executable,'-c','import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)'])
Path(sys.argv[1],'child').write_text(str(child.pid));time.sleep(60)
"""
        result = self.run_owner(source)
        self.assertEqual(result.returncode, 124)
        self.no_live_process(int((self.root / "child").read_text()))

    def test_old_owner_exit_cleans_different_group_without_touching_other_session(self):
        bystander = subprocess.Popen([sys.executable, "-c", "import time;time.sleep(60)"], start_new_session=True)
        source = """import os,subprocess,sys,time
from pathlib import Path
child=subprocess.Popen([sys.executable,'-c','import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)'],preexec_fn=lambda:os.setpgid(0,0))
Path(sys.argv[1],'child').write_text(str(child.pid));time.sleep(60)
"""
        try:
            self.assertEqual(self.run_owner(source).returncode, 124)
            self.no_live_process(int((self.root / "child").read_text()))
            self.assertIsNone(bystander.poll(), "unrelated operation session was signaled")
        finally:
            bystander.terminate()
            bystander.wait()

    def test_foreign_or_reused_group_cannot_be_anchored_in_operation_session(self):
        bystander = subprocess.Popen([sys.executable, "-c", "import time;time.sleep(60)"], start_new_session=True)
        source = ("import sys;sys.path.insert(0,sys.argv[1]);import remote_operation as op;"
                  "assert op.anchor_group(int(sys.argv[2])) is None;print('foreign-group-refused')")
        try:
            result = subprocess.run([sys.executable, "-c", source, str(LIB), str(bystander.pid)],
                                    capture_output=True, text=True, start_new_session=True, timeout=5)
            self.assertEqual((result.returncode, result.stdout), (0, "foreign-group-refused\n"))
            self.assertIsNone(bystander.poll())
        finally:
            bystander.terminate()
            bystander.wait()

    def test_successful_leader_cannot_leave_same_group_background_work(self):
        source = """import subprocess,sys
from pathlib import Path
child=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
Path(sys.argv[1],'child').write_text(str(child.pid));print('complete')
"""
        result = self.run_owner(source, timeout=2)
        self.assertEqual((result.returncode, result.stdout), (0, "complete\n"))
        self.no_live_process(int((self.root / "child").read_text()))

    def test_signal_during_launch_is_deferred_through_owned_cleanup(self):
        original = rt.subprocess.Popen
        child = []
        def launch(*args, **kwargs):
            process = original(*args, **kwargs)
            if args[0][0] == sys.executable:
                child.append(process)
                os.kill(os.getpid(), signal.SIGTERM)
            return process
        with patch.object(rt.subprocess, "Popen", side_effect=launch):
            with self.assertRaises(KeyboardInterrupt):
                self.run_owner("import time;time.sleep(60)", timeout=2)
        self.assertEqual(len(child), 1)
        self.assertIsNotNone(child[0].returncode)

    def test_parallel_operation_interrupt_stops_workers_before_return(self):
        source = """import sys,time
from pathlib import Path
sys.path.insert(0,sys.argv[1]);import remote_tips as rt
root=Path(sys.argv[2]);rt.STOP_GRACE_S=.15;rt.KILL_GRACE_S=2
def work(index):
 code='import os,sys,time;from pathlib import Path;Path(sys.argv[1]).write_text(str(os.getpid()));time.sleep(60)'
 return rt._run([sys.executable,'-c',code,str(root/str(index))],timeout=60)
rt.parallel_map(work,[0,1],workers=2)
"""
        process = subprocess.Popen([sys.executable, "-c", source, str(LIB), str(self.root)],
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
        try:
            deadline = time.monotonic() + 5
            while not all((self.root / str(i)).exists() for i in (0, 1)):
                self.assertLess(time.monotonic(), deadline, "worker launch did not complete")
                time.sleep(0.02)
            process.send_signal(signal.SIGTERM)
            self.assertNotEqual(process.wait(timeout=5), 0)
            for index in (0, 1):
                self.no_live_process(int((self.root / str(index)).read_text()))
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()

    def test_caller_death_closes_custody_and_stops_separate_group(self):
        source = """import sys
from pathlib import Path
sys.path.insert(0,sys.argv[1]);import remote_tips as rt
rt.STOP_GRACE_S=.15;rt.KILL_GRACE_S=2
code='import os,subprocess,sys,time;from pathlib import Path;child=subprocess.Popen([sys.executable,"-c","import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)"],preexec_fn=lambda:os.setpgid(0,0));Path(sys.argv[1],"child").write_text(str(child.pid));time.sleep(60)'
rt._run([sys.executable,'-c',code,sys.argv[2]],timeout=60)
"""
        caller = subprocess.Popen([sys.executable, "-c", source, str(LIB), str(self.root)],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
        try:
            deadline = time.monotonic() + 5
            while not (self.root / "child").exists():
                self.assertLess(time.monotonic(), deadline)
                time.sleep(0.02)
            caller.kill()
            caller.wait()
            self.await_not_live(int((self.root / "child").read_text()))
        finally:
            if caller.poll() is None:
                caller.kill()
                caller.wait()

    def census_failure(self, persistent):
        # Exercise the actual session owner, with real differently grouped
        # children. Only the census operation fails; fixture cleanup also
        # runs on the old implementation's exception, so RED leaves no work.
        source = """import os,signal,subprocess,sys,time
from pathlib import Path
sys.path.insert(0,sys.argv[1]);import remote_operation as op
root=Path(sys.argv[2]);persistent=sys.argv[3]=='True';pins={};native=None
code='import os,signal,subprocess,sys,time;from pathlib import Path;child=subprocess.Popen([sys.executable,"-c","import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)"],preexec_fn=lambda:os.setpgid(0,0));Path(sys.argv[1],"child").write_text(str(child.pid));time.sleep(60)'
try:
 native=subprocess.Popen([sys.executable,'-c',code,str(root)],preexec_fn=lambda:os.setpgid(0,0))
 pins[native.pid]=op.anchor_group(native.pid)
 deadline=time.monotonic()+5
 while not (root/'child').exists():
  assert time.monotonic()<deadline;time.sleep(.01)
 child=int((root/'child').read_text())
 if persistent:pins[child]=op.anchor_group(child)
 original=op.session_members;calls=[0]
 def census(session):
  calls[0]+=1
  if persistent or calls[0]==1:raise RuntimeError('forced census failure')
  return original(session)
 op.session_members=census
 if persistent:
  try:op.stop_session(os.getpid(),native,pins,.1,.2)
  except RuntimeError:pass
  else:raise AssertionError('unknown cleanup was accepted')
 else:op.stop_session(os.getpid(),native,pins,.1,2)
 # Observe before fixture cleanup: the implementation must have stopped both.
 for pid in (native.pid,child):
  state=subprocess.run(['/bin/ps','-p',str(pid),'-o','stat='],capture_output=True,text=True)
  assert state.returncode or state.stdout.strip().startswith('Z'),(pid,state.stdout)
 print('owned work stopped')
finally:
 # Known groups are atomically pinned before signals even on the old RED.
 if (root/'child').exists():
  child=int((root/'child').read_text())
  if child not in pins:
   pin=op.anchor_group(child)
   if pin is not None:pins[child]=pin
 for group,pin in pins.items():
  if pin is not None:
   try:os.killpg(group,signal.SIGKILL)
   except ProcessLookupError:pass
 if native is not None:native.wait(timeout=2)
 for pin in pins.values():
  if pin is not None:
   try:os.waitpid(pin,0)
   except ChildProcessError:pass
# Completed cleanup must withdraw every pin before returning it to callers.
assert pins and all(pin is None for pin in pins.values()), pins
retired=dict(pins);owner=op.owner_logic();original_signal=owner.signal_owned_group
def no_retired_signal(group,sig):
 raise AssertionError(('retired group signalled',group,sig))
owner.signal_owned_group=no_retired_signal
try:
 if persistent:
  try:op.stop_session(os.getpid(),native,pins,.1,.2)
  except RuntimeError:pass
  else:raise AssertionError('persistent unknown cleanup was accepted')
 else:assert op.stop_session(os.getpid(),native,pins,.1,.2)==native.returncode
finally:owner.signal_owned_group=original_signal
assert pins==retired
"""
        result = subprocess.run([sys.executable, "-c", source, str(LIB), str(self.root), str(persistent)],
                                capture_output=True, text=True, start_new_session=True, timeout=10)
        self.assertEqual((result.returncode, result.stdout), (0, "owned work stopped\n"), result.stderr)

    def test_transient_census_failure_retries_after_stopping_known_groups(self):
        self.census_failure(False)

    def test_persistent_census_failure_refuses_and_stops_every_known_group(self):
        self.census_failure(True)


@unittest.skipUnless(os.name == "posix" and rt._process_owner.exit_observation_available(),
                     "requires the supported local POSIX operation profile")
class InheritedRepositoryEnvironmentTests(unittest.TestCase):
    """A hook's exported repository-local variables never choose what
    RemoteTips reads (the inherited-environment half of IR-COHORT-LOCAL-REMOTE-1): _env
    removes every GIT_* name, inherited or passed, before its fixed profile."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="remote-tips-env-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name).resolve()
        self.clean = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        self.store = self.repository("store", "/remotes/declared.git")
        self.other = self.repository("other", "/remotes/elsewhere.git")

    def git(self, *arguments):
        return subprocess.run(["git", *arguments], env=self.clean, capture_output=True, text=True,
                              check=True).stdout.strip()

    def repository(self, name, url):
        path = self.directory / name
        self.git("init", "-q", "-b", "main", str(path))
        self.git("-C", str(path), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "-q", "--allow-empty", "-m", name)
        self.git("-C", str(path), "remote", "add", "origin", url)
        return path

    def reported(self):
        return subprocess.run(["git", "rev-parse", "--local-env-vars"], cwd=os.path.abspath(os.sep), env=self.clean,
                              capture_output=True, text=True, check=True).stdout.split()

    def test_resolve_answers_for_the_named_store_whatever_a_hook_exports(self):
        other_git = str(self.other / ".git")
        exports = {
            "GIT_DIR": {"GIT_DIR": other_git},
            "GIT_DIR and GIT_WORK_TREE": {"GIT_DIR": other_git, "GIT_WORK_TREE": str(self.other)},
            "GIT_COMMON_DIR": {"GIT_COMMON_DIR": other_git},
            "GIT_OBJECT_DIRECTORY": {"GIT_OBJECT_DIRECTORY": str(self.other / ".git/objects")},
            "GIT_INDEX_FILE": {"GIT_INDEX_FILE": str(self.other / ".git/index")},
            "GIT_CONFIG_PARAMETERS": {"GIT_CONFIG_PARAMETERS": "'remote.origin.url'='/remotes/elsewhere.git'"},
            "GIT_CONFIG_COUNT": {"GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "remote.origin.url",
                                 "GIT_CONFIG_VALUE_0": "/remotes/elsewhere.git"},
        }
        expected = rt.Remote(self.store / ".git", "origin", "/remotes/declared.git")
        self.assertEqual(rt.RemoteTips._resolve(self.store), expected)
        for name, exported in exports.items():
            with self.subTest(name), patch.dict(os.environ, exported):
                self.assertEqual(rt.RemoteTips._resolve(self.store), expected)
                self.assertEqual(rt.RemoteTips._resolve(self.store / ".git"), expected)
                self.assertEqual(rt.RemoteTips().remote(self.store), expected)

    def test_env_drops_every_name_git_reports_inherited_or_passed(self):
        reported = self.reported()
        self.assertTrue({"GIT_DIR", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY", "GIT_COMMON_DIR"} <= set(reported))
        hostile = {name: "/nonexistent/hook-export" for name in reported}
        hostile.update(GIT_CONFIG_PARAMETERS="'core.bare'='true'", GIT_CONFIG_COUNT="1",
                       GIT_CONFIG_KEY_0="core.bare", GIT_CONFIG_VALUE_0="true", GIT_CONFIG_GLOBAL="/nonexistent",
                       # Global pathspec switches git exports to a hook, and a
                       # transport profile the fixed one must replace.
                       GIT_GLOB_PATHSPECS="1", GIT_ICASE_PATHSPECS="1", GIT_TERMINAL_PROMPT="1",
                       GIT_NO_LAZY_FETCH="0", GIT_ALLOW_PROTOCOL="https:ssh")
        # The fixed profile, which _env sets after removing every GIT_* name.
        fixed = {"GIT_TERMINAL_PROMPT": "0", "GIT_NO_REPLACE_OBJECTS": "1", "GIT_GRAFT_FILE": os.devnull,
                 "GIT_ALLOW_PROTOCOL": "file", "GIT_NO_LAZY_FETCH": "1"}
        objects = self.directory / "intake-objects"
        with patch.dict(os.environ, hostile):
            profiles = {
                "inherited": (rt._env(), fixed),
                "passed": (rt._env(dict(os.environ)), fixed),
                "isolated": (rt._env(isolate_git_config=True), dict(
                    fixed, GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_SYSTEM=os.devnull, GIT_CONFIG_GLOBAL=os.devnull)),
                # Isolated object intake names its own object directory, deliberately.
                "object intake": (rt._env(isolate_git_config=True, git_object_directory=objects), dict(
                    fixed, GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_SYSTEM=os.devnull, GIT_CONFIG_GLOBAL=os.devnull,
                    GIT_OBJECT_DIRECTORY=str(objects))),
            }
        for name, (env, profile) in profiles.items():
            with self.subTest(name):
                self.assertEqual({key: value for key, value in env.items() if key.startswith("GIT_")}, profile)
                self.assertEqual(env.get("PATH"), os.environ.get("PATH"))


if __name__ == "__main__":
    unittest.main()
