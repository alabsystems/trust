#!/usr/bin/env python3
"""Real-Git controls for complete cohort manifest inventory, and for the
batched, remembered, bounded containment judgment and the judged date.

Run: python3 -m unittest scripts.tests.check_ir_cohort_inventory_test
"""
from pathlib import Path
import contextlib
import base64
import copy
import datetime
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_ir_cohort as gate

DECL = 'trust-ir = { git = "https://github.com/alabsystems/trust-ir", rev = "' + 'a' * 40 + '" }\n'


class ManifestInventoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="ir-inventory.")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve() / "root"
        self.repo(self.root, {"README": "root\n"})

    def git(self, root, *args):
        return subprocess.check_output(["git", "-C", str(root), *args], text=True, stderr=subprocess.PIPE).strip()

    def repo(self, root, files):
        root.mkdir(parents=True, exist_ok=True)
        self.git(root, "init", "-q", "-b", "main")
        self.git(root, "config", "user.email", "test@example.invalid")
        self.git(root, "config", "user.name", "Test")
        for name, text in files.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        self.git(root, "add", "-A")
        self.git(root, "commit", "-qm", "fixture")

    def child(self, parent, relative, files=None):
        child = parent / relative
        self.repo(child, files or {"Cargo.toml": '[dependencies]\n' + DECL})
        head = self.git(child, "rev-parse", "HEAD")
        self.git(parent, "update-index", "--add", "--cacheinfo", f"160000,{head},{relative}")
        self.git(parent, "commit", "-qm", "tracked child")
        return child

    def test_unregistered_inactive_and_uninitialized_metadata_do_not_hide_a_populated_child(self):
        self.child(self.root, "first-party/dep")
        self.assertEqual(self.git(self.root, "ls-files", "--recurse-submodules", "*Cargo.toml"), "")
        for settings in ((), ("submodule.first-party/dep.active", "false"), ("submodule.active", ":!first-party/dep")):
            with self.subTest(settings=settings):
                if settings:
                    self.git(self.root, "config", *settings)
                rows = gate.find_declarations(self.root)
                self.assertEqual([row.where for row in rows], ["first-party/dep/Cargo.toml"])

    def test_nested_gitlinks_are_complete_and_sorted_without_activation(self):
        a = self.child(self.root, "first-party/a")
        self.child(a, "nested/leaf")
        self.child(self.root, "first-party/b with spaces")
        self.git(self.root, "config", "submodule.active", ":!first-party/*")
        self.git(a, "config", "submodule.nested/leaf.active", "false")
        self.assertEqual([row.where for row in gate.find_declarations(self.root)], [
            "first-party/a/Cargo.toml", "first-party/a/nested/leaf/Cargo.toml", "first-party/b with spaces/Cargo.toml",
        ])

    def test_untracked_nested_repository_is_not_a_consumer(self):
        self.repo(self.root / "untracked", {"Cargo.toml": '[dependencies]\n' + DECL})
        self.assertEqual(gate.find_declarations(self.root), [])

    def test_missing_or_nonrepository_gitlink_refuses_instead_of_returning_empty(self):
        child = self.child(self.root, "first-party/dep")
        shutil.rmtree(child / ".git")
        with self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)
        shutil.rmtree(child)
        with self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)

    def test_unreadable_index_and_missing_tracked_manifest_refuse(self):
        child = self.child(self.root, "first-party/dep")
        original = gate.run
        def failed(args, cwd, **kwargs):
            return (128, "") if args[1:2] == ["ls-files"] else original(args, cwd, **kwargs)
        with mock.patch.object(gate, "run", side_effect=failed), self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)
        (child / "Cargo.toml").unlink()
        with self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)
        error_output = io.StringIO()
        with mock.patch.object(sys, "argv", ["check_ir_cohort.py", "--root", str(self.root), "--report"]), contextlib.redirect_stderr(error_output):
            self.assertEqual(gate.main(), 2)
        self.assertIn("IR COHORT COULD NOT RUN", error_output.getvalue())

    def test_staged_manifest_is_inventoried_but_unmerged_index_refuses(self):
        manifest = self.root / "Cargo.toml"
        manifest.write_text('[dependencies]\n' + DECL)
        self.git(self.root, "add", "Cargo.toml")
        self.assertEqual([row.where for row in gate.find_declarations(self.root)], ["Cargo.toml"])
        oid = self.git(self.root, "hash-object", "Cargo.toml")
        subprocess.run(["git", "-C", str(self.root), "update-index", "--index-info"],
                       input=f"0 {'0' * 40}\tCargo.toml\n100644 {oid} 1\tCargo.toml\n100644 {oid} 2\tCargo.toml\n",
                       text=True, check=True)
        with self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)

    def test_hook_environment_cannot_substitute_a_partial_index_or_repository(self):
        child = self.child(self.root, "first-party/dep")
        (self.root / "Cargo.toml").write_text('[dependencies]\n' + DECL)
        self.git(self.root, "add", "Cargo.toml")
        self.git(self.root, "commit", "-qm", "root manifest")
        alternate = Path(self.tmp.name) / "alternate-index"
        env = dict(os.environ, GIT_INDEX_FILE=str(alternate))
        subprocess.run(["git", "-C", str(self.root), "read-tree", "--empty"], env=env, check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "Cargo.toml"], env=env, check=True)
        for overrides in ({"GIT_INDEX_FILE": str(alternate)},
                          {"GIT_DIR": str(child / ".git"), "GIT_WORK_TREE": str(child)}):
            with self.subTest(overrides=overrides), mock.patch.dict(os.environ, overrides):
                rows = gate.find_declarations(self.root)
                self.assertEqual([row.where for row in rows], ["Cargo.toml", "first-party/dep/Cargo.toml"])

    def other_repository(self, gitlink="first-party/trust-ir", recorded="b" * 40):
        """A second repository a hook's environment could name: its HEAD
        records `recorded` at `gitlink`, and it holds none of self.root's
        objects."""
        other = Path(self.tmp.name).resolve() / "other"
        self.repo(other, {"README": "other\n", "surface.rs": "pub const SURFACE: u8 = 2;\n"})
        self.git(other, "update-index", "--add", "--cacheinfo", f"160000,{recorded},{gitlink}")
        self.git(other, "commit", "-qm", "another repository's gitlink")
        return other

    def hook_exports(self, other):
        """Each repository-local variable a hook can export, alone, naming
        `other` (the inherited-environment half of IR-COHORT-LOCAL-REMOTE-1),
        and each global pathspec switch git exports to a hook
        (`git --glob-pathspecs push` sets GIT_GLOB_PATHSPECS=1)."""
        git_dir = str(other / ".git")
        return {
            "GIT_DIR": {"GIT_DIR": git_dir},
            "GIT_DIR and GIT_WORK_TREE": {"GIT_DIR": git_dir, "GIT_WORK_TREE": str(other)},
            "GIT_COMMON_DIR": {"GIT_COMMON_DIR": git_dir},
            "GIT_OBJECT_DIRECTORY": {"GIT_OBJECT_DIRECTORY": str(other / ".git/objects")},
            "GIT_INDEX_FILE": {"GIT_INDEX_FILE": str(other / ".git/index")},
            # With either one, `--literal-pathspecs ls-tree` and ls-tree on a
            # directory die (exit 128): gitlink_rev raised RATIFIED ANCHOR
            # UNREADABLE and semantic_digest returned None on fb4059f5abb6.
            "GIT_GLOB_PATHSPECS": {"GIT_GLOB_PATHSPECS": "1"},
            "GIT_ICASE_PATHSPECS": {"GIT_ICASE_PATHSPECS": "1"},
            "GIT_NOGLOB_PATHSPECS": {"GIT_NOGLOB_PATHSPECS": "1"},
            "GIT_LITERAL_PATHSPECS": {"GIT_LITERAL_PATHSPECS": "1"},
        }

    def test_an_exported_repository_cannot_answer_for_the_recorded_gitlink(self):
        # Formerly IR-COHORT-LOCAL-REMOTE-1: gitlink_rev ran git with the inherited
        # environment. On d0c36e78984c an exported GIT_DIR or GIT_COMMON_DIR
        # read the other repository's HEAD (its gitlink, 'b' * 40) and an
        # exported GIT_OBJECT_DIRECTORY could not read HEAD's tree at all.
        recorded = self.child(self.root, "first-party/trust-ir")
        recorded = self.git(recorded, "rev-parse", "HEAD")
        other = self.other_repository()
        self.assertEqual(gate.gitlink_rev(self.root, "first-party/trust-ir"), recorded)
        for name, exported in self.hook_exports(other).items():
            with self.subTest(name), mock.patch.dict(os.environ, exported):
                self.assertEqual(gate.gitlink_rev(self.root, "first-party/trust-ir"), recorded)
                self.assertIsNone(gate.gitlink_rev(self.root, "first-party/absent"))
                self.assertEqual(gate.ancestry_memory_dir(self.root),
                                 (self.root / ".git/trust-land/commit-ancestry").resolve())

    def test_an_exported_repository_cannot_answer_for_a_store_semantic_digest(self):
        # Formerly IR-COHORT-LOCAL-REMOTE-1: semantic_digest ran git (ls-tree and
        # cat-file) with the inherited environment. On d0c36e78984c an
        # exported GIT_DIR, GIT_COMMON_DIR or GIT_OBJECT_DIRECTORY naming a
        # repository without the store's revision made it unreadable (None),
        # and an exported GIT_DIR holding a revision the store lacks read it.
        (self.root / "surface.rs").write_text("pub const SURFACE: u8 = 1;\n")
        self.git(self.root, "add", "surface.rs")
        self.git(self.root, "commit", "-qm", "semantic source")
        held = self.git(self.root, "rev-parse", "HEAD")
        expected = gate.semantic_digest(self.root, held, ("surface.rs",))
        self.assertIsNotNone(expected)
        other = self.other_repository()
        elsewhere = self.git(other, "rev-parse", "HEAD")
        self.assertIsNone(gate.semantic_digest(self.root, elsewhere, ("surface.rs",)))
        for name, exported in self.hook_exports(other).items():
            with self.subTest(name), mock.patch.dict(os.environ, exported):
                self.assertEqual(gate.semantic_digest(self.root, held, ("surface.rs",)), expected)
                self.assertIsNone(gate.semantic_digest(self.root, elsewhere, ("surface.rs",)))

    def test_a_partial_clone_store_never_fetches_lazily_from_its_remote(self):
        # On fb4059f5abb6 git_environment did not set GIT_NO_LAZY_FETCH, so
        # semantic_digest's local cat-file in a blob-less partial clone fetched
        # the blob from the store's configured remote: unbounded, outside Agh,
        # with the inherited transport environment. The read must fail
        # (None) and leave the store as it was; semantic_digest_with_source
        # then acquires the bytes through materialize_semantic_objects.
        base = Path(self.tmp.name).resolve()
        source = base / "partial-source"
        self.repo(source, {"surface.rs": "pub const SURFACE: u8 = 3;\n"})
        origin = base / "partial-origin.git"
        self.git(base, "clone", "-q", "--bare", str(source), str(origin))
        self.git(origin, "config", "uploadpack.allowFilter", "true")
        store = base / "partial-store"
        self.git(base, "clone", "-q", "--filter=blob:none", "--no-checkout", origin.as_uri(), str(store))
        held = self.git(store, "rev-parse", "HEAD")
        blob = self.git(source, "rev-parse", "HEAD:surface.rs")
        expected = gate.semantic_digest(source, held, ("surface.rs",))
        self.assertIsNotNone(expected)

        def present():
            return subprocess.run(["git", "-C", str(store), "cat-file", "-e", blob],
                                  env=dict(os.environ, GIT_NO_LAZY_FETCH="1"),
                                  capture_output=True).returncode == 0

        self.assertFalse(present())
        for name, exported in {"inherited": {}, "lazy fetch allowed": {"GIT_NO_LAZY_FETCH": "0"}}.items():
            with self.subTest(name), mock.patch.dict(os.environ, exported):
                self.assertIsNone(gate.semantic_digest(store, held, ("surface.rs",)))
                self.assertFalse(present())
        # The fixture's partial clone does serve the blob when asked for it.
        subprocess.run(["git", "-C", str(store), "cat-file", "blob", blob], check=True, capture_output=True)
        self.assertTrue(present())
        self.assertEqual(gate.semantic_digest(store, held, ("surface.rs",)), expected)

    def test_an_exported_repository_cannot_move_the_whole_gate(self):
        # The same reads end to end: on d0c36e78984c an exported GIT_DIR
        # naming another repository made gitlink_rev answer for it.
        self.coherent_semantic_cohort()
        other = self.other_repository()
        self.assertEqual(self.semantic_gate_result()[0], 0)
        for name, exported in self.hook_exports(other).items():
            with self.subTest(name), mock.patch.dict(os.environ, exported):
                status, output = self.semantic_gate_result()
                self.assertEqual(status, 0, output)
                self.assertIn("IR COHORT COHERENT", output)

    def test_missing_index_and_unborn_repository_are_not_empty_inventories(self):
        for state in ("missing-index", "unborn"):
            with self.subTest(state=state):
                child = self.child(self.root, "first-party/" + state)
                if state == "missing-index":
                    (child / ".git/index").unlink()
                else:
                    self.git(child, "update-ref", "-d", "refs/heads/main")
                with self.assertRaises(gate.InventoryError):
                    gate.find_declarations(self.root)
                if state == "missing-index":
                    self.git(child, "reset", "--mixed", "HEAD")

    def test_linked_worktree_index_is_read_from_its_own_administrative_directory(self):
        source = Path(self.tmp.name) / "store"
        self.repo(source, {"Cargo.toml": '[dependencies]\n' + DECL})
        linked = self.root / "first-party/linked"
        linked.parent.mkdir()
        self.git(source, "worktree", "add", "-q", "--detach", str(linked), "HEAD")
        head = self.git(linked, "rev-parse", "HEAD")
        self.git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{head},first-party/linked")
        self.git(self.root, "commit", "-qm", "linked worktree")
        self.assertTrue((linked / ".git").is_file())
        self.assertEqual([row.where for row in gate.find_declarations(self.root)], ["first-party/linked/Cargo.toml"])

    def test_semantic_digest_retains_genuine_absence_and_distinguishes_present_source(self):
        absent = self.git(self.root, "rev-parse", "HEAD")
        absent_digest = gate.semantic_digest(self.root, absent, ("surface.rs",))
        self.assertIsNotNone(absent_digest)
        (self.root / "surface.rs").write_text("pub const SURFACE: u8 = 1;\n")
        self.git(self.root, "add", "surface.rs")
        self.git(self.root, "commit", "-qm", "present semantic source")
        present = self.git(self.root, "rev-parse", "HEAD")
        self.assertNotEqual(gate.semantic_digest(self.root, present, ("surface.rs",)), absent_digest)
        self.assertEqual(gate.semantic_digest(self.root, absent, ("surface.rs",)), absent_digest)

    def test_missing_semantic_blobs_refuse_until_their_exact_bytes_are_restored(self):
        for relative in ("surface.rs", "surface/extension.rs"):
            with self.subTest(relative=relative):
                source = self.root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("pub const SURFACE: u8 = 1;\n// " + relative + "\n")
                self.git(self.root, "add", relative)
                self.git(self.root, "commit", "-qm", "tracked semantic source")
                revision = self.git(self.root, "rev-parse", "HEAD")
                complete = gate.semantic_digest(self.root, revision, ("surface.rs",))
                self.assertIsNotNone(complete)
                blob = self.git(self.root, "rev-parse", "HEAD:" + relative)
                obj = self.root / ".git/objects" / blob[:2] / blob[2:]
                saved = obj.read_bytes()
                obj.unlink()
                try:
                    self.assertEqual(self.git(self.root, "cat-file", "-t", revision), "commit")
                    self.assertEqual(self.git(self.root, "cat-file", "-t", revision + "^{tree}"), "tree")
                    self.assertIsNone(gate.semantic_digest(self.root, revision, ("surface.rs",)))
                finally:
                    obj.write_bytes(saved)
                self.assertEqual(gate.semantic_digest(self.root, revision, ("surface.rs",)), complete)

    def test_missing_semantic_tree_refuses_until_restored(self):
        revision = self.git(self.root, "rev-parse", "HEAD")
        complete = gate.semantic_digest(self.root, revision, ("surface.rs",))
        tree = self.git(self.root, "rev-parse", "HEAD^{tree}")
        obj = self.root / ".git/objects" / tree[:2] / tree[2:]
        saved = obj.read_bytes()
        obj.unlink()
        try:
            self.assertEqual(self.git(self.root, "cat-file", "-t", revision), "commit")
            self.assertIsNone(gate.semantic_digest(self.root, revision, ("surface.rs",)))
        finally:
            obj.write_bytes(saved)
        self.assertEqual(gate.semantic_digest(self.root, revision, ("surface.rs",)), complete)

    def test_unreadable_ratified_surface_never_uses_the_consumer_group_as_authority(self):
        relative = "crates/trust-ir/src/ty.rs"
        store = self.child(self.root, "first-party/trust-ir", {
            "Cargo.toml": '[package]\nname = "trust-ir"\nversion = "0.1.0"\n',
            relative: "pub const SURFACE: u8 = 1;\n",
        })
        anchor_blob = self.git(store, "rev-parse", "HEAD:" + relative)
        (store / relative).write_text("pub const SURFACE: u8 = 2;\n")
        self.git(store, "add", relative)
        self.git(store, "commit", "-qm", "different consumer source")
        consumer = self.git(store, "rev-parse", "HEAD")
        remote = Path(self.tmp.name) / "remote.git"
        self.git(store, "init", "-q", "--bare", "-b", "main", str(remote))
        self.git(store, "remote", "add", "origin", str(remote))
        self.git(store, "push", "-q", "origin", "main")
        (self.root / "Cargo.toml").write_text('[dependencies]\n' + DECL.replace("a" * 40, consumer))
        self.git(self.root, "add", "Cargo.toml")
        self.git(self.root, "commit", "-qm", "consume a published descendant without moving the anchor")
        obj = store / ".git/objects" / anchor_blob[:2] / anchor_blob[2:]
        saved = obj.read_bytes()
        obj.unlink()
        output = io.StringIO()
        try:
            with mock.patch.object(sys, "argv", ["check_ir_cohort.py", "--root", str(self.root)]), \
                    contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
                self.assertEqual(gate.main(), 1)
            self.assertIn("RATIFIED SURFACE UNREADABLE", output.getvalue())
            self.assertNotIn("   COHERENT:", output.getvalue())
        finally:
            obj.write_bytes(saved)

    def coherent_semantic_cohort(self):
        store = self.child(self.root, "first-party/trust-ir", {
            "Cargo.toml": '[package]\nname = "trust-ir"\nversion = "0.1.0"\n',
            "crates/trust-ir/src/ty.rs": "pub const SURFACE: u8 = 1;\n",
        })
        revision = self.git(store, "rev-parse", "HEAD")
        remote = Path(self.tmp.name) / "remote.git"
        self.git(store, "init", "-q", "--bare", "-b", "main", str(remote))
        self.git(store, "remote", "add", "origin", str(remote))
        self.git(store, "push", "-q", "origin", "main")
        (self.root / "Cargo.toml").write_text('[dependencies]\n' + DECL.replace("a" * 40, revision))
        self.git(self.root, "add", "Cargo.toml")
        self.git(self.root, "commit", "-qm", "consume the recorded published anchor")
        return revision

    def semantic_gate_result(self):
        output = io.StringIO()
        with mock.patch.object(sys, "argv", ["check_ir_cohort.py", "--root", str(self.root)]), \
                contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            status = gate.main()
        return status, output.getvalue()

    def test_unreadable_superproject_tree_refuses_and_exact_restoration_passes(self):
        self.coherent_semantic_cohort()
        self.assertEqual(self.semantic_gate_result()[0], 0)
        revision = self.git(self.root, "rev-parse", "HEAD")
        tree = self.git(self.root, "rev-parse", "HEAD^{tree}")
        obj = self.root / ".git/objects" / tree[:2] / tree[2:]
        saved = obj.read_bytes()
        obj.unlink()
        try:
            self.assertEqual(self.git(self.root, "cat-file", "-t", revision), "commit")
            status, output = self.semantic_gate_result()
            self.assertEqual(status, 2)
            self.assertIn("RATIFIED ANCHOR UNREADABLE", output)
            self.assertNotIn("COHERENT", output)
        finally:
            obj.write_bytes(saved)
        self.assertEqual(self.semantic_gate_result()[0], 0)

    def test_missing_ratified_gitlink_refuses_instead_of_electing_a_consumer(self):
        revision = self.coherent_semantic_cohort()
        self.git(self.root, "update-index", "--force-remove", "first-party/trust-ir")
        self.git(self.root, "commit", "-qm", "remove only the recorded anchor")
        status, output = self.semantic_gate_result()
        self.assertEqual(status, 2)
        self.assertIn("RATIFIED ANCHOR MISSING", output)
        self.assertNotIn("COHERENT", output)
        self.git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{revision},first-party/trust-ir")
        self.git(self.root, "commit", "-qm", "restore the exact recorded anchor")
        self.assertEqual(self.semantic_gate_result()[0], 0)

    def test_a_store_counts_only_as_a_populated_checkout_at_a_recorded_gitlink(self):
        # LAND-IR-READER-GAPS-1: has_store took any path holding a `.git` or
        # a `HEAD` for the dependency's object store. Git started there then
        # found another repository: with a gitfile naming the superproject's
        # Git directory, whose objects hold the pin and whose remote publishes
        # it, the gate judged the pins there and said COHERENT (exit 0 on
        # 46a6408ff56f). What ties the store's remote to the dependency is
        # store_identity_problem (the next test).
        self.coherent_semantic_cohort()
        rel = "first-party/trust-ir"
        self.assertTrue(gate.has_store(self.root, rel))
        self.assertEqual(self.semantic_gate_result()[0], 0)
        self.git(self.root, "remote", "add", "origin", str(Path(self.tmp.name) / "remote.git"))
        self.git(self.root, "fetch", "-q", "origin", "main:refs/dependency/main")
        self.git(self.root, "rm", "-q", "--cached", rel)  # HEAD still records the gitlink
        store = self.root / rel
        store.rename(Path(self.tmp.name) / "populated")
        own = self.git(self.root, "rev-parse", "--path-format=absolute", "--git-common-dir")
        cases = {
            "an empty directory": lambda: None,
            "a stray HEAD": lambda: (store / "HEAD").write_text("ref: refs/heads/main\n"),
            "a gitfile naming the superproject's Git directory":
                lambda: (store / ".git").write_text(f"gitdir: {own}\n"),
            "a bare repository": lambda: self.git(store, "init", "-q", "--bare"),
        }
        for name, make in cases.items():
            with self.subTest(name):
                shutil.rmtree(store, ignore_errors=True)
                store.mkdir()
                make()
                status, output = self.semantic_gate_result()
                self.assertEqual(status, 1, output)
                self.assertIn("trust-ir: object store first-party/trust-ir is not checked out", output)
                self.assertNotIn("IR COHORT COHERENT", output)
                self.assertFalse(gate.has_store(self.root, rel))
        with self.subTest("a populated checkout HEAD records no gitlink at"):
            self.child(self.root, "first-party/ay")
            self.git(self.root, "rm", "-q", "--cached", "first-party/ay")
            self.git(self.root, "commit", "-qm", "untrack the ay checkout")
            self.assertFalse(gate.has_store(self.root, "first-party/ay"))

    def test_a_github_remote_must_name_the_declared_repository(self):
        # Review of d034e8e620dd: whatever repository the store's origin
        # named judged the pins, so a store whose origin is a fork, whose main
        # contains a pin the dependency's does not, read as contained (exit 0,
        # IR COHORT COHERENT there with the same stubbed answer). The remote's
        # answer is stubbed (every revision contained): no network is read.
        self.coherent_semantic_cohort()
        store = self.root / "first-party/trust-ir"
        asked = []

        def contained(tips, path, shas, *, scope="durable"):
            asked.append(Path(path))
            return {sha.lower(): gate.rt.Verdict(gate.rt.CONTAINED, (gate.rt.MAIN_REF,)) for sha in shas}

        with mock.patch.object(gate.rt.RemoteTips, "warm", lambda *args, **kwargs: None), \
                mock.patch.object(gate.rt.RemoteTips, "judge_many", contained):
            for url, want in (("https://github.com/someone-else/trust-ir.git", 1),
                              ("git@github.com:alabsystems/trust-ir-fork.git", 1),
                              ("https://example.invalid/alabsystems/trust-ir.git", 1),
                              ("git@github.com:alabsystems/trust-ir.git", 0),
                              ("https://github.com/alabsystems/trust-ir", 0)):
                with self.subTest(url):
                    asked.clear()
                    self.git(store, "remote", "set-url", "origin", url)
                    status, output = self.semantic_gate_result()
                    self.assertEqual(status, want, output)
                    if want:
                        self.assertIn("trust-ir: STORE IDENTITY --- object store first-party/trust-ir", output)
                        self.assertNotIn("IR COHORT COHERENT", output)
                        self.assertEqual(asked, [], "a misidentified store's remote judges nothing")
                    else:
                        self.assertIn("IR COHORT COHERENT", output)
                        self.assertEqual(set(asked), {store})

    def test_report_and_audited_exclusion_rules_are_preserved(self):
        child = self.child(self.root, "first-party/dep", {
            "Cargo.toml": '[dependencies]\n' + DECL,
            "reports/old/Cargo.toml": '[dependencies]\n' + DECL,
            "spikes/old/Cargo.toml": '[dependencies]\n' + DECL,
        })
        config = self.root / gate.EXCLUSIONS_PATH
        config.parent.mkdir(parents=True)
        config.write_text(json.dumps({"schema": gate.EXCLUSIONS_SCHEMA, "exclusions": [
            {"repository": "dep", "path": "spikes/old"},
        ]}))
        # Excluded snapshots are not read, even when absent on disk.
        (child / "reports/old/Cargo.toml").unlink()
        (child / "spikes/old/Cargo.toml").unlink()
        with contextlib.redirect_stdout(io.StringIO()):
            rows = gate.find_declarations(self.root)
        self.assertEqual([row.where for row in rows], ["first-party/dep/Cargo.toml"])
        self.assertEqual(gate.EXCLUDED_MANIFESTS, ["first-party/dep/spikes/old/Cargo.toml"])


    def surface_commit(self, files):
        for name, content in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        self.git(self.root, "add", "-A")
        self.git(self.root, "commit", "-qm", "surface fixture")
        return self.git(self.root, "rev-parse", "HEAD")

    def remove_fixture_object(self, oid):
        objects = self.root / ".git/objects"
        (objects / oid[:2] / oid[2:]).unlink()

    def test_a_missing_surface_blob_is_unreadable_not_absence(self):
        rev = self.surface_commit({"value.rs": "pub struct Value;\n"})
        self.remove_fixture_object(self.git(self.root, "rev-parse", rev + ":value.rs"))
        self.git(self.root, "cat-file", "-e", rev + "^{commit}")
        self.assertIsNone(gate.semantic_digest(self.root, rev, ("value.rs",)))

    def test_a_missing_surface_tree_is_unreadable_not_an_empty_split_directory(self):
        rev = self.surface_commit({
            "value.rs": "mod split;\n", "value/split.rs": "pub struct Value;\n",
        })
        self.remove_fixture_object(self.git(self.root, "rev-parse", rev + ":value"))
        self.assertIsNone(gate.semantic_digest(self.root, rev, ("value.rs",)))

    def test_proven_surface_absence_is_still_a_distinct_digest(self):
        absent = self.git(self.root, "rev-parse", "HEAD")
        empty = self.surface_commit({"value.rs": ""})
        missing = gate.semantic_digest(self.root, absent, ("value.rs",))
        present = gate.semantic_digest(self.root, empty, ("value.rs",))
        self.assertIsNotNone(missing)
        self.assertIsNotNone(present)
        self.assertNotEqual(missing, present)


    def test_semantic_source_intake_binds_the_exact_commit_and_rereads_original_bytes(self):
        content = b"pub struct Value;\n"
        rev = self.surface_commit({"value.rs": content.decode()})
        expected = gate.semantic_digest(self.root, rev, ("value.rs",))
        blob = self.git(self.root, "rev-parse", rev + ":value.rs")
        self.remove_fixture_object(blob)
        self.git(self.root, "remote", "add", "origin", "https://github.com/example/ir.git")
        def restore(root, oid, surface, tips):
            self.assertEqual((root, oid, surface), (self.root, rev, ("value.rs",)))
            self.assertEqual(tips.remote(root).url, "https://github.com/example/ir.git")
            written = subprocess.check_output(
                ["git", "-C", str(root), "hash-object", "-w", "--stdin"], input=content,
            ).decode().strip()
            self.assertEqual(written, blob)
            return None
        with mock.patch.object(gate, "materialize_semantic_objects", side_effect=restore) as intake:
            digest, error = gate.semantic_digest_with_source(
                self.root, rev[:12], ("value.rs",), gate.rt.RemoteTips(),
            )
        intake.assert_called_once()
        self.assertEqual((digest, error), (expected, None))
        self.assertEqual(self.git(self.root, "rev-parse", "HEAD"), rev)

    def test_semantic_source_intake_failure_or_unreadable_success_is_not_a_digest(self):
        rev = self.surface_commit({"value.rs": "pub struct Value;\n"})
        self.remove_fixture_object(self.git(self.root, "rev-parse", rev + ":value.rs"))
        self.git(self.root, "remote", "add", "origin", "https://github.com/example/ir.git")
        for status in (3, 0):
            with self.subTest(status=status), mock.patch.object(
                gate, "materialize_semantic_objects",
                side_effect=gate.SurfaceUnavailable("fixture unavailable") if status else None,
            ):
                digest, error = gate.semantic_digest_with_source(
                    self.root, rev, ("value.rs",), gate.rt.RemoteTips(),
                )
                self.assertIsNone(digest)
                self.assertIsNotNone(error)

    def test_readable_semantic_source_needs_no_source_intake(self):
        rev = self.surface_commit({"value.rs": "pub struct Value;\n"})
        with mock.patch.object(
            gate, "materialize_semantic_objects", side_effect=AssertionError("unexpected intake"),
        ):
            digest, error = gate.semantic_digest_with_source(
                self.root, rev, ("value.rs",), gate.rt.RemoteTips(),
            )
        self.assertEqual(
            (digest, error), (gate.semantic_digest(self.root, rev, ("value.rs",)), None),
        )


    def source_object_fixture(self, name, missing_parent=False):
        root = Path(self.tmp.name) / name
        self.repo(root, {"value.rs": "mod split;\n", "value/split.rs": "pub struct Value;\n"})
        (root / "value/data.bin").write_bytes(b"\x00\xff\x01")
        self.git(root, "add", "-A")
        self.git(root, "commit", "-qm", "binary split data")
        self.git(root, "remote", "add", "origin", "https://github.com/example/ir.git")
        rev = self.git(root, "rev-parse", "HEAD")
        expected = gate.semantic_digest(root, rev, ("value.rs",))
        root_tree = self.git(root, "rev-parse", rev + "^{tree}")
        rows = [
            line.split("\t", 1)[0].split()
            for line in self.git(root, "ls-tree", "-r", "-t", rev).splitlines()
        ]
        trees = {root_tree} | {oid for _, kind, oid in rows if kind == "tree"}
        blobs = {oid for _, kind, oid in rows if kind == "blob"}
        payloads = {}
        for oid in trees:
            entries = []
            for line in self.git(root, "ls-tree", oid).splitlines():
                header, path = line.split("\t", 1)
                mode, kind, target = header.split()
                entries.append({"mode": mode, "type": kind, "sha": target, "path": path})
            # API ordering is not authority: Git's canonical tree must still
            # hash to the commit's original identity after reconstruction.
            payloads[f"repos/example/ir/git/trees/{oid}"] = {
                "sha": oid, "truncated": False, "tree": list(reversed(entries)),
            }
        for oid in blobs:
            raw = subprocess.check_output(["git", "-C", str(root), "cat-file", "blob", oid])
            payloads[f"repos/example/ir/git/blobs/{oid}"] = {
                "sha": oid, "size": len(raw), "encoding": "base64",
                "content": base64.b64encode(raw).decode(),
            }
        for oid in trees | blobs:
            (root / ".git/objects" / oid[:2] / oid[2:]).unlink()
        if missing_parent:
            parent = self.git(root, "rev-parse", rev + "^")
            (root / ".git/objects" / parent[:2] / parent[2:]).unlink()
        self.assertIsNone(gate.semantic_digest(root, rev, ("value.rs",)))
        return root, rev, root_tree, expected, payloads

    def test_exact_api_objects_restore_surface_without_fetching_parent_history(self):
        root, rev, _, expected, payloads = self.source_object_fixture(
            "objects", missing_parent=True,
        )
        called = []
        def api(repository, args, *, timeout):
            self.assertEqual(repository, "example/ir")
            self.assertEqual(args[0], "api")
            self.assertGreater(timeout, 0)
            called.append(args[1])
            return subprocess.CompletedProcess([], 0, json.dumps(payloads[args[1]]), "")
        with mock.patch.object(gate.rt, "_agh", side_effect=api):
            digest, error = gate.semantic_digest_with_source(
                root, rev, ("value.rs",), gate.rt.RemoteTips(),
            )
        self.assertEqual((digest, error), (expected, None))
        self.assertTrue(any("/blobs/" in path for path in called))
        self.assertTrue(any("/trees/" in path for path in called))
        self.assertEqual(self.git(root, "rev-parse", "HEAD"), rev)

    def test_incomplete_or_changed_api_objects_cannot_supply_a_surface_digest(self):
        for case in (
            "truncated", "identity", "tree-bytes", "duplicate",
            "blob-bytes", "blob-size", "unavailable",
        ):
            with self.subTest(case=case):
                root, rev, tree, _, payloads = self.source_object_fixture(case)
                tree_endpoint = f"repos/example/ir/git/trees/{tree}"
                blob_endpoint = next(path for path in payloads if "/blobs/" in path)
                changed = []
                def api(repository, args, *, timeout):
                    payload = copy.deepcopy(payloads[args[1]])
                    if args[1] == tree_endpoint and case in {
                        "truncated", "identity", "tree-bytes", "duplicate", "unavailable",
                    }:
                        changed.append(case)
                        if case == "truncated":
                            payload["truncated"] = True
                        elif case == "identity":
                            payload["sha"] = "0" * 40
                        elif case == "tree-bytes":
                            payload["tree"][0]["sha"] = "f" * 40
                        elif case == "duplicate":
                            payload["tree"].append(payload["tree"][0])
                        else:
                            return subprocess.CompletedProcess([], 3, "", "fixture unavailable")
                    elif args[1] == blob_endpoint and case in {"blob-bytes", "blob-size"}:
                        changed.append(case)
                        if case == "blob-bytes":
                            payload["content"] = base64.b64encode(b"different source").decode()
                            payload["size"] = len(b"different source")
                        else:
                            payload["size"] += 1
                    return subprocess.CompletedProcess([], 0, json.dumps(payload), "")
                with mock.patch.object(gate.rt, "_agh", side_effect=api):
                    digest, error = gate.semantic_digest_with_source(
                root, rev, ("value.rs",), gate.rt.RemoteTips(),
            )
                self.assertTrue(changed, "the mutation must reach an actual requested object")
                self.assertIsNone(digest)
                self.assertIsNotNone(error)


    def test_a_partial_semantic_population_is_not_reported_coherent(self):
        child = self.child(self.root, "first-party/trust-ir", {"value.rs": "pub struct Value;\n"})
        good = self.git(child, "rev-parse", "HEAD")
        (child / "value.rs").write_text("pub struct Other;\n")
        self.git(child, "add", "value.rs")
        self.git(child, "commit", "-qm", "second semantic input")
        unreadable = self.git(child, "rev-parse", "HEAD")
        self.git(child, "checkout", "-q", "--detach", good)
        rows = [
            gate.Decl("trust-ir", good, "a/Cargo.toml"),
            gate.Decl("trust-ir", unreadable, "b/Cargo.toml"),
        ]
        def read(store, rev, surface, tips):
            return ("0123456789ab", None) if rev == good else (None, "fixture unreadable")
        output = io.StringIO()
        with mock.patch.object(sys, "argv", ["check_ir_cohort.py", "--root", str(self.root)]), \
             mock.patch.object(gate, "find_declarations", return_value=rows), \
             mock.patch.object(gate.rt.RemoteTips, "warm"), \
             mock.patch.object(gate, "on_main", return_value=True), \
             mock.patch.object(gate, "semantic_digest_with_source", side_effect=read), \
             contextlib.redirect_stdout(output):
            status = gate.main()
        self.assertEqual(status, 2)
        self.assertIn("INCOMPLETE: 1/2", output.getvalue())
        self.assertNotIn("COHERENT:", output.getvalue())
class GitEnvironmentTests(unittest.TestCase):
    """git_environment, the environment of every git process the gate runs
    (the inherited-environment half of IR-COHORT-LOCAL-REMOTE-1): no
    inherited GIT_* variable, then remote_tips' fixed profile."""

    PROFILE = {"GIT_TERMINAL_PROMPT": "0", "GIT_NO_REPLACE_OBJECTS": "1", "GIT_GRAFT_FILE": os.devnull,
               "GIT_ALLOW_PROTOCOL": "file", "GIT_NO_LAZY_FETCH": "1"}

    def reported(self):
        clean = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        return subprocess.run(["git", "rev-parse", "--local-env-vars"], cwd=os.path.abspath(os.sep), env=clean,
                              capture_output=True, text=True, check=True).stdout.split()

    def test_the_git_environment_keeps_no_inherited_git_variable(self):
        reported = self.reported()
        self.assertLessEqual({"GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY",
                              "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_COMMON_DIR"}, set(reported))
        hostile = {name: "/nonexistent/hook-export" for name in reported}
        hostile.update(GIT_CONFIG_PARAMETERS="malformed", GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="core.bare",
                       GIT_CONFIG_VALUE_0="true", GIT_CONFIG_GLOBAL="/nonexistent/config",
                       GIT_CONFIG_NOSYSTEM="1", GIT_GLOB_PATHSPECS="1", GIT_ICASE_PATHSPECS="1",
                       GIT_NOGLOB_PATHSPECS="1", GIT_LITERAL_PATHSPECS="1", GIT_TERMINAL_PROMPT="1",
                       GIT_NO_LAZY_FETCH="0", GIT_ALLOW_PROTOCOL="https:ssh", GIT_SSH_COMMAND="false",
                       GIT_ASKPASS="false", GIT_NO_REPLACE_OBJECTS="0", GIT_REPLACE_REF_BASE="refs/x/",
                       GIT_GRAFT_FILE="/nonexistent/grafts", TRUST_GIT_ENVIRONMENT_PROBE="kept")
        with mock.patch.dict(os.environ, hostile):
            env = gate.git_environment()
            self.assertEqual(env, gate.rt._env())
        self.assertEqual({key: value for key, value in env.items() if key.startswith("GIT_")}, self.PROFILE)
        self.assertEqual(env["TRUST_GIT_ENVIRONMENT_PROBE"], "kept")
        self.assertEqual(env.get("PATH"), os.environ.get("PATH"))

    def test_every_git_process_runs_under_it_and_others_inherit(self):
        seen = []
        actual = subprocess.run
        def record(args, **kwargs):
            seen.append((args[0], kwargs.get("env")))
            return actual(args, **kwargs)
        with mock.patch.dict(os.environ, {"GIT_DIR": "/nonexistent/hook-export", "GIT_GLOB_PATHSPECS": "1"}), \
                mock.patch.object(gate.subprocess, "run", side_effect=record):
            gate.run(["git", "--version"], Path(os.path.abspath(os.sep)))
            gate.run([sys.executable, "-c", "pass"], Path(os.path.abspath(os.sep)))
        self.assertEqual(len(seen), 2)
        program, env = seen[0]
        self.assertEqual(program, "git")
        self.assertEqual({key: value for key, value in env.items() if key.startswith("GIT_")}, self.PROFILE)
        self.assertEqual(seen[1], (sys.executable, None))


class BatchedJudgmentTests(unittest.TestCase):
    """Every store's revisions are judged in one batch, stores in parallel,
    with remembered ancestry and one bound; the verdicts and the report are
    those of the one-at-a-time loop (2026-11-15). The date waivers are judged
    on is max(--date, the UTC date), never the local date or an environment
    variable."""

    git = ManifestInventoryTests.git
    repo = ManifestInventoryTests.repo
    child = ManifestInventoryTests.child

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="ir-judgment.")
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name).resolve()
        self.root = self.base / "root"
        self.repo(self.root, {"README": "root\n"})

    def bare(self, name):
        remote = self.base / f"{name}.git"
        subprocess.run(["git", "init", "-q", "--bare", "-b", "main", str(remote)], check=True)
        return remote

    def declare(self, rel, repo, rev):
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f'[dependencies]\nx = {{ git = "https://github.com/alabsystems/{repo}", rev = "{rev}" }}\n')
        self.git(self.root, "add", rel)
        self.git(self.root, "commit", "-qm", "declare " + rel)

    def undeclare(self, *rels):
        for rel in rels:
            self.git(self.root, "rm", "-q", f"{rel}/Cargo.toml")
        self.git(self.root, "commit", "-qm", "undeclare " + " ".join(rels))

    def commit(self, store, rel, text, message):
        (store / rel).parent.mkdir(parents=True, exist_ok=True)
        (store / rel).write_text(text)
        self.git(store, "add", rel)
        self.git(store, "commit", "-qm", message)
        return self.git(store, "rev-parse", "HEAD")

    def cohort(self, *, waiver=True, no_main=True):
        """A ratified anchor A, a waived divergence B, C (same surface as B,
        the remote's main), OFF-MAIN, ABSENT, and an ungated store whose remote
        publishes no main (NO_MAIN)."""
        surface = "crates/trust-ir/src/ty.rs"
        self.store = self.child(self.root, "first-party/trust-ir", {
            "Cargo.toml": '[package]\nname = "trust-ir"\nversion = "0.1.0"\n',
            surface: "pub const SURFACE: u8 = 1;\n",
        })
        a = self.git(self.store, "rev-parse", "HEAD")
        b = self.commit(self.store, surface, "pub const SURFACE: u8 = 2;\n", "B")
        c = self.commit(self.store, "README", "not surface\n", "C")
        self.remote = self.bare("trust-ir")
        self.git(self.store, "remote", "add", "origin", str(self.remote))
        self.git(self.store, "push", "-q", "origin", "main")
        self.git(self.store, "checkout", "-q", "-b", "fork", a)
        fork = self.commit(self.store, surface, "pub const SURFACE: u8 = 99;\n", "FORK")
        self.git(self.store, "checkout", "-q", "main")
        self.revs = {"A": a, "B": b, "C": c, "FORK": fork, "ABSENT": "0123456789abcdef" * 2 + "01234567"}
        self.declare("a/Cargo.toml", "trust-ir", a)
        self.declare("b/Cargo.toml", "trust-ir", b)
        self.declare("c/Cargo.toml", "trust-ir", c)
        self.declare("f/Cargo.toml", "trust-ir", fork)
        self.declare("u/Cargo.toml", "trust-ir", self.revs["ABSENT"])
        if no_main:
            clean = self.child(self.root, "first-party/clean", {"README": "clean\n"})
            clean_remote = self.bare("clean")
            self.git(clean, "remote", "add", "origin", str(clean_remote))
            self.git(clean, "push", "-q", "origin", "main:dev")
            self.declare("k/Cargo.toml", "clean", self.git(clean, "rev-parse", "HEAD"))
        if waiver:
            self.write_waiver(self.digest("B"), datetime.date(2099, 1, 1))
        return self.revs

    def digest(self, name):
        return gate.semantic_digest(self.store, self.revs[name], gate.SEMANTIC_SURFACE["trust-ir"])

    def write_waiver(self, digest, expires):
        path = self.root / gate.WAIVER_PATH
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"trust-ir | {digest} | {expires.isoformat()} | test | fixture\n")

    def run_gate(self, *argv, env=None):
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(sys, "argv", ["check_ir_cohort.py", "--root", str(self.root), *argv]), \
                mock.patch.dict(os.environ, env or {}), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = gate.main()
        return status, out.getvalue(), err.getvalue()

    def test_batched_judgment_matches_one_at_a_time_and_asks_each_store_once(self):
        revs = self.cohort()
        rt = gate.rt
        original_batch, original_one = rt.RemoteTips.judge_many, rt.RemoteTips._judge_many
        asked = []

        def counting(tips, path, shas, scope):
            asked.append((str(path), tuple(shas), scope))
            return original_one(tips, path, shas, scope)

        def one_at_a_time(tips, path, shas, *, scope="durable"):
            verdicts = {}
            for sha in shas:
                verdicts.update(original_batch(tips, path, [sha], scope=scope))
            return verdicts

        original_inventory = rt.RemoteTips.inventory
        scopes = []

        def recording(tips, path, **kwargs):
            scopes.append(kwargs.get("scope", "durable"))
            return original_inventory(tips, path, **kwargs)

        with mock.patch.object(gate, "ancestry_memory_dir", return_value=None), \
                mock.patch.object(rt.RemoteTips, "_judge_many", counting), \
                mock.patch.object(rt.RemoteTips, "inventory", recording):
            batched = self.run_gate()
        # warm and judge_many ask one main-scope inventory (witnessing main
        # alone for a GitHub remote; IR-COHORT-MAIN-WITNESS-1).
        self.assertEqual(set(scopes), {"main"}, scopes)
        stores = [path for path, _shas, _scope in asked]
        self.assertEqual(len(stores), 2, asked)
        self.assertEqual(len(set(stores)), 2, "one batch per store")
        self.assertTrue(all(scope == "main" for _p, _s, scope in asked))
        trust_ir = next(shas for path, shas, _ in asked if path.endswith("trust-ir"))
        self.assertEqual(set(trust_ir), set(revs.values()))  # the anchor A rides in the same batch
        with mock.patch.object(gate, "ancestry_memory_dir", return_value=None), \
                mock.patch.object(rt.RemoteTips, "judge_many", one_at_a_time):
            serial = self.run_gate()
        self.assertEqual(batched[:2], serial[:2])
        status, output, _ = batched
        self.assertEqual(status, 1, output)
        self.assertIn(f"trust-ir@{revs['FORK'][:8]}: OFF-MAIN", output)
        self.assertIn(f"trust-ir@{revs['ABSENT'][:8]}: UNRESOLVABLE", output)
        self.assertIn("CONTAINMENT UNRESOLVED", output)
        self.assertIn("   waived  ", output)
        self.assertNotIn(f"trust-ir@{revs['C'][:8]}", output.split("IR COHORT INCOHERENT")[1])
        self.assertIn("IR COHORT PHASES: inventory ", batched[2])
        # The one commit fetch is ABSENT's. These literal local remotes'
        # `git ls-remote` witnesses no tip, natively or otherwise.
        self.assertIn(" 1 commit fetch(es); ", batched[2])
        self.assertIn(" witnessing 0 tip(s) as commits (0 of them by 0 native read(s)), ", batched[2])
        self.assertIn("; 0 revision(s) UNJUDGED; ", batched[2])

    def test_parallel_stores_with_one_revision_and_different_mains_keep_their_own_verdicts(self):
        revs = self.cohort(waiver=False, no_main=False)
        twin = self.root / "first-party/ty"
        subprocess.run(["git", "clone", "-q", str(self.store), str(twin)], check=True)
        self.git(twin, "checkout", "-q", revs["C"])
        self.git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{revs['C']},first-party/ty")
        self.git(self.root, "commit", "-qm", "twin store")
        twin_remote = self.bare("ty")
        self.git(twin, "remote", "set-url", "origin", str(twin_remote))
        self.git(twin, "push", "-q", "origin", revs["A"] + ":refs/heads/main")
        self.undeclare("a", "b", "f", "u")
        self.declare("t/Cargo.toml", "ty", revs["C"])
        status, output, _ = self.run_gate()
        self.assertEqual(status, 1, output)
        self.assertIn(f"ty@{revs['C'][:8]}: OFF-MAIN", output)
        self.assertNotIn(f"trust-ir@{revs['C'][:8]}: OFF-MAIN", output)

    def test_a_second_run_remembers_and_a_rewound_main_is_asked_afresh(self):
        revs = self.cohort(no_main=False)  # C shares B's waived surface
        self.undeclare("b", "f", "u")
        memory = self.root / ".git/trust-land/commit-ancestry"
        self.assertEqual(gate.ancestry_memory_dir(self.root), memory)
        first = self.run_gate()
        second = self.run_gate()
        self.assertEqual((first[0], second[0]), (0, 0), first[1])
        self.assertEqual(first[1], second[1])
        self.assertIn(" 0 remembered answer(s)", first[2])
        self.assertRegex(second[2], r" [1-9][0-9]* remembered answer\(s\)")
        self.assertTrue((memory / gate.rt.AncestryMemory.FORMAT).is_dir())
        # A rewound main: C was remembered as contained in the old tip only.
        self.git(self.remote, "update-ref", "refs/heads/main", revs["A"])
        status, output, _ = self.run_gate()
        self.assertEqual(status, 1, output)
        self.assertIn(f"trust-ir@{revs['C'][:8]}: OFF-MAIN", output)

    def test_a_memo_under_another_format_is_ignored(self):
        revs = self.cohort(waiver=False, no_main=False)
        self.undeclare("b", "c", "u")
        tip, fork = revs["C"], revs["FORK"]
        memory = self.root / ".git/trust-land/commit-ancestry"
        # Answers written under an older or other contract (the bare `v1` of
        # 2026-11-13, another Agh schema or scope) never answer for this one.
        for other in ("v1", "v1-agh2-commit-parent-ancestry-only-v1", "v1-agh1-another-scope"):
            self.assertNotEqual(other, gate.rt.AncestryMemory.FORMAT)
            forged = memory / other / fork[:2] / f"{fork}-{tip}"
            forged.parent.mkdir(parents=True, exist_ok=True)
            forged.write_text("contained\n")
        status, output, _ = self.run_gate()
        self.assertEqual(status, 1, output)
        self.assertIn(f"trust-ir@{fork[:8]}: OFF-MAIN", output)
        # Control: the same file under the current FORMAT is read (the trusted
        # class docs/DECISION_QUEUE.md REACH-MEMO-1 names), so the files above
        # sat where a memo would be found.
        current = memory / gate.rt.AncestryMemory.FORMAT / fork[:2] / f"{fork}-{tip}"
        self.assertEqual(current.read_text(), "not-contained\n")
        current.write_text("contained\n")
        status, output, _ = self.run_gate()
        self.assertNotIn("OFF-MAIN", output)
        self.assertIn(f"schema {self.digest('FORK')} diverges", output)

    def test_the_native_reply_contract_names_the_memory_format(self):
        rt = gate.rt
        self.assertEqual(rt.AncestryMemory.FORMAT,
                         f"v1-agh{rt.NATIVE_ANCESTRY_SCHEMA}-{rt.NATIVE_ANCESTRY_SCOPE}")
        self.assertEqual((rt.NATIVE_ANCESTRY_SCHEMA, rt.NATIVE_ANCESTRY_SCOPE),
                         (1, "commit-parent-ancestry-only-v1"))

    def test_a_spent_time_bound_leaves_every_revision_unjudged(self):
        revs = self.cohort(waiver=False)
        # Isolate remote/source uncertainty from the fixture's deliberately
        # readable local schema divergences. Keep a readable anchor, ABSENT,
        # and the ungated Clean store; none licenses a containment verdict.
        self.undeclare("b", "c", "f")
        status, output, err = self.run_gate("--time-bound", "0")
        self.assertEqual(status, 2, output + err)
        self.assertNotRegex(output, r"OFF-MAIN|UNRESOLVABLE|CONTAINMENT UNRESOLVED|COHERENT|waived")
        rows = re.findall(r"^  \* (\S+)@([0-9a-f]{8}): (?:RATIFIED ANCHOR )?COULD NOT RUN", output, re.M)
        expected = {("trust-ir", revs[name][:8]) for name in ("A", "ABSENT")}
        self.assertTrue(expected <= set(rows), rows)
        self.assertEqual(rows.count(("trust-ir", revs["A"][:8])), 2, rows)  # declaration + anchor
        self.assertEqual(len(rows), len(expected) + 2, rows)  # Clean and the separate anchor
        self.assertIn("time bound", output)
        self.assertIn(f"; {len(rows)} revision(s) UNJUDGED; ", err)

    def test_a_spent_remote_bound_preserves_actual_local_schema_findings(self):
        revs = self.cohort(waiver=False)
        status, output, err = self.run_gate("--time-bound", "0")
        self.assertEqual(status, 1, output + err)
        self.assertIn("IR COHORT INCOHERENT --- 2 problem(s)", output)
        self.assertIn(f"schema {self.digest('B')} diverges", output)
        self.assertIn(f"schema {self.digest('FORK')} diverges", output)
        self.assertNotRegex(output, r"OFF-MAIN|UNRESOLVABLE|CONTAINMENT UNRESOLVED|waived")
        self.assertNotIn("IR COHORT COHERENT", output)
        rows = re.findall(r"^  \* (\S+)@([0-9a-f]{8}): (?:RATIFIED ANCHOR )?COULD NOT RUN", output, re.M)
        expected = {("trust-ir", rev[:8]) for rev in revs.values()}
        self.assertTrue(expected <= set(rows), rows)
        self.assertEqual(rows.count(("trust-ir", revs["A"][:8])), 2, rows)
        self.assertEqual(len(rows), len(expected) + 2, rows)
        # A proven local problem is exit1 while every unavailable remote
        # judgment remains explicit. Neither report erases the other.
        self.assertIn(f"; {len(rows)} revision(s) UNJUDGED; ", err)

    def test_waivers_are_judged_on_max_of_argv_and_utc_date_never_the_environment(self):
        self.cohort(no_main=False)
        self.undeclare("f", "u")
        today = gate.utc_today()
        day = datetime.timedelta(days=1)
        self.write_waiver(self.digest("B"), today - day)
        past = (today - 3 * day).isoformat()
        for argv, env in (((), {"TRUST_GATE_DATE": past}), (("--date", past), {"TRUST_GATE_DATE": past})):
            with self.subTest(argv=argv, env=env):
                status, output, _ = self.run_gate(*argv, env=env)
                self.assertEqual(status, 1, output)
                self.assertIn("EXPIRED", output)
        self.write_waiver(self.digest("B"), today + 2 * day)
        self.assertEqual(self.run_gate()[0], 0)
        status, output, _ = self.run_gate("--date", (today + 5 * day).isoformat())
        self.assertEqual(status, 1, output)
        self.assertIn("EXPIRED", output)
        with mock.patch.object(gate, "utc_today", return_value=today + 3 * day):
            status, output, _ = self.run_gate("--date", today.isoformat())
        self.assertEqual(status, 1, output)
        self.assertIn("EXPIRED", output)
        self.assertEqual(gate.judged_date(None), gate.utc_today())
        for bad in ("2026-1-5", "tomorrow", "2026-02-30"):
            with self.subTest(bad=bad), self.assertRaises(SystemExit):
                self.run_gate("--date", bad)

    def test_a_waiver_is_judged_on_the_date_after_the_remote_phase(self):
        # Review 1: the date was read at the run's start, before up to the
        # time bound of remote work, so a run crossing midnight still honoured
        # a waiver that expired at midnight. The clock here turns over once
        # the remote phase has judged anything.
        self.cohort(no_main=False)
        self.undeclare("f", "u")
        today = gate.utc_today()
        self.write_waiver(self.digest("B"), today)
        self.assertEqual(self.run_gate()[0], 0, "a waiver expiring today still holds today")
        judged = {"remote": False}
        original = gate.rt.RemoteTips.judge_many

        def judge_many(tips, *args, **kwargs):
            judged["remote"] = True
            return original(tips, *args, **kwargs)
        with mock.patch.object(gate.rt.RemoteTips, "judge_many", judge_many), \
                mock.patch.object(gate, "utc_today",
                                  lambda: today + datetime.timedelta(days=1) if judged["remote"] else today):
            status, output, _ = self.run_gate("--date", today.isoformat())
        self.assertTrue(judged["remote"])
        self.assertEqual(status, 1, output)
        self.assertIn("EXPIRED", output)

    def test_a_time_bound_that_bounds_nothing_is_refused(self):
        self.cohort(waiver=False)
        for bad in ("nan", "inf", "-inf", "-1", "soon"):
            with self.subTest(bad=bad), self.assertRaises(SystemExit):
                self.run_gate("--time-bound", bad)
        self.assertEqual(gate.time_bound_seconds("0"), 0.0)
        self.assertEqual(gate.time_bound_seconds("900"), 900.0)

    def test_the_local_time_zone_never_moves_the_judged_date(self):
        self.cohort(no_main=False)
        self.undeclare("f", "u")
        saved = os.environ.get("TZ")

        def restore():
            if saved is None:
                os.environ.pop("TZ", None)
            else:
                os.environ["TZ"] = saved
            time.tzset()
        self.addCleanup(restore)
        # UTC-12 and UTC+14: at every hour one of them names another local
        # date than UTC's, so a local-date judgment fails one case below.
        for zone in ("Etc/GMT+12", "Etc/GMT-14"):
            os.environ["TZ"] = zone
            time.tzset()
            today = gate.utc_today()
            for expires, want in ((today, 0), (today - datetime.timedelta(days=1), 1)):
                with self.subTest(zone=zone, expires=expires):
                    self.write_waiver(self.digest("B"), expires)
                    self.assertEqual(self.run_gate()[0], want)


if __name__ == "__main__":
    unittest.main()
