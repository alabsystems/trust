#!/usr/bin/env python3
"""Native Git/CoW fixtures; no compiler, remote source or SDK qualification."""
import errno
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1]

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    sys.modules[name] = value
    spec.loader.exec_module(value)
    return value

cache = load("source_working_cache", SCRIPT / "source_working_cache.py")
owner = load("source_working_cache_bootstrap", SCRIPT / "recreate_bootstrap.py")


class NativeWorkingCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.source = self.root / "source"
        self.source.mkdir()
        self.git(self.source, "init", "-q", "--template=", "--initial-branch=main")
        self.git(self.source, "config", "user.name", "Source cache fixture")
        self.git(self.source, "config", "user.email", "source@example.invalid")
        (self.source / "nested").mkdir()
        (self.source / "a").write_bytes(b"actual exact regular source\n")
        (self.source / "nested/b").write_bytes(b"same sized content\n")
        (self.source / "executable").write_bytes(b"#!/bin/sh\nexit 0\n")
        (self.source / "executable").chmod(0o755)
        (self.source / "symbolic").symlink_to("a")
        (self.source / ".gitmodules").write_text('[submodule "child"]\npath=child\nurl=https://github.com/example/child.git\n')
        self.git(self.source, "add", ".")
        self.git(self.source, "commit", "-qm", "source")
        self.git(self.source, "update-index", "--add", "--cacheinfo", "160000", self.oid(), "child")
        self.git(self.source, "commit", "-qm", "gitlink")
        self.commit = self.oid()

    def git(self, path, *args):
        return subprocess.run([*owner._controlled_git_command([]), "-C", str(path), *args],
            env=owner._provenance_git_environment(), check=True, capture_output=True).stdout

    def oid(self):
        return self.git(self.source, "rev-parse", "HEAD").decode().strip()

    def destination(self, name):
        dest = self.root / name
        dest.mkdir()
        self.git(dest, "init", "-q", "--template=", "--initial-branch=main")
        # Native local fixture transfer is object authority here, not production Agh.
        self.git(dest, "-c", "protocol.file.allow=always", "fetch", "-q", "--no-tags",
                 str(self.source), self.commit + ":refs/fixture/target")
        return dest

    def prepare(self, dest, donor=None):
        return cache.prepare_checkout(dest, self.commit, donor,
            git_command=owner._controlled_git_command([]), environment=owner._provenance_git_environment(),
            verify_physical=owner._source_working_cache_physical)

    def finish(self, dest, prepared):
        self.git(dest, "checkout", "--quiet", "--detach", "--no-recurse-submodules", self.commit, "--")
        return {**prepared.verify(), "clones": prepared.clones}

    def inventory(self, dest):
        result = {}
        for path in ("a", "nested/b", "executable", "symbolic", ".gitmodules"):
            p = dest / path
            info = p.lstat()
            result[path] = (stat.S_IMODE(info.st_mode), os.readlink(p) if p.is_symlink() else p.read_bytes())
        return result

    def require_native(self):
        if cache._native() is None:
            self.skipTest("native Darwin clone API unavailable; normal fallback tested separately")

    def test_complete_cold_warm_and_original_head_transition_keeps_clone_inodes(self):
        self.require_native()
        cold = self.destination("cold")
        self.finish(cold, self.prepare(cold))
        warm = self.destination("warm")
        prepared = self.prepare(warm, self.source)
        before = {r["path"]: (warm / r["path"]).stat().st_ino for r in prepared.clones}
        self.assertGreaterEqual(len(before), 4)
        result = self.finish(warm, prepared)
        self.assertTrue(result["complete_checkout_verified"])
        self.assertEqual(self.inventory(cold), self.inventory(warm))
        self.assertTrue((warm / "child").is_dir())
        self.assertEqual(self.git(warm, "ls-files", "--stage"), self.git(cold, "ls-files", "--stage"))
        for path, inode in before.items():
            self.assertEqual((warm / path).stat().st_ino, inode)
            self.assertNotEqual(inode, (self.source / path).stat().st_ino)
            self.assertEqual((warm / path).stat().st_nlink, 1)
        self.assertEqual(self.git(warm, "status", "--porcelain"), b"")
        self.assertFalse((warm / ".git/info/alternates").exists())
        self.assertTrue(all(row.startswith(b"H ") for row in self.git(warm, "ls-files", "-v").splitlines()))
        self.assertEqual(json.loads((warm / ".git/trust-source-working-cache.json").read_text())["cloned"], len(before))

    def test_same_size_corrupt_missing_and_dirty_donor_fall_back_without_mutation(self):
        self.require_native()
        (self.source / "nested/b").write_bytes(b"x" * len((self.source / "nested/b").read_bytes()))
        (self.source / "a").unlink()
        (self.source / "untracked-compiled-artifact").write_bytes(b"not source")
        before = (self.source / "nested/b").read_bytes()
        dest = self.destination("corrupt")
        result = self.finish(dest, self.prepare(dest, self.source))
        self.assertEqual((dest / "nested/b").read_bytes(), b"same sized content\n")
        self.assertEqual((dest / "a").read_bytes(), b"actual exact regular source\n")
        self.assertEqual((self.source / "nested/b").read_bytes(), before)
        self.assertFalse((dest / "untracked-compiled-artifact").exists())
        self.assertGreaterEqual(result["fallback"], 4)

    def test_unsupported_cross_volume_partial_clone_and_one_failure_keep_complete_fallback(self):
        for failure in ("unsupported", "cross-volume", "partial", "one"):
            with self.subTest(failure=failure):
                dest = self.destination(failure)
                native = cache._native()
                if failure != "unsupported" and native is None:
                    continue
                count = 0
                def clone(fd, directory, name):
                    nonlocal count
                    count += 1
                    if failure == "one" and count > 1:
                        return native[0](fd, directory, name)
                    if failure == "partial":
                        p = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600, dir_fd=directory)
                        os.write(p, b"partial")
                        os.close(p)
                        return  # Returned candidate has bad/partial bytes: normal fallback.
                    raise OSError(errno.EXDEV, "controlled clone miss")
                with mock.patch.object(cache, "_native", return_value=None if failure == "unsupported" else (clone, *native[1:])):
                    result = self.finish(dest, self.prepare(dest, self.source))
                self.assertEqual((dest / "a").read_bytes(), b"actual exact regular source\n")
                self.assertEqual(self.git(dest, "status", "--porcelain"), b"")
                self.assertEqual(list((dest / ".git").glob("trust-working-data-*")), [])
                if failure in ("cross-volume", "partial"):
                    self.assertEqual(result["cloned"], 0)

    def test_racy_donor_and_fifo_symlink_parent_hardlink_are_only_data_misses(self):
        self.require_native()
        native = cache._native()
        changed = False
        def race(fd, directory, name):
            nonlocal changed
            native[0](fd, directory, name)
            if not changed and os.fstat(fd).st_ino == (self.source / "a").stat().st_ino:
                changed = True
                (self.source / "a").write_bytes(b"after-clone donor mutation\n")
        dest = self.destination("racy")
        with mock.patch.object(cache, "_native", return_value=(race, *native[1:])):
            result = self.finish(dest, self.prepare(dest, self.source))
        self.assertTrue(changed)
        self.assertNotIn("a", {r["path"] for r in result["clones"]})
        self.assertEqual((dest / "a").read_bytes(), b"actual exact regular source\n")
        (self.source / "a").unlink()
        os.mkfifo(self.source / "a")
        (self.source / "nested/b").unlink()
        (self.source / "nested").rmdir()
        (self.source / "nested").symlink_to(dest / "nested", target_is_directory=True)
        os.link(self.source / "executable", self.source / "hardlink")
        dest2 = self.destination("special")
        result = self.finish(dest2, self.prepare(dest2, self.source))
        self.assertEqual((dest2 / "a").read_bytes(), b"actual exact regular source\n")
        self.assertEqual({r["path"] for r in result["clones"]}, {".gitmodules"})

    def test_git_attributes_are_normal_checkout_not_raw_blob_substitution(self):
        self.require_native()
        (self.source / ".gitattributes").write_text("a text eol=crlf\nnested/b ident\n")
        self.git(self.source, "add", ".gitattributes")
        self.git(self.source, "commit", "-qm", "conversion")
        self.commit = self.oid()
        cold = self.destination("converted-cold")
        self.finish(cold, self.prepare(cold))
        warm = self.destination("converted-warm")
        result = self.finish(warm, self.prepare(warm, self.source))
        self.assertEqual(self.inventory(cold), self.inventory(warm))
        self.assertEqual((warm / "a").read_bytes(), b"actual exact regular source\r\n")
        self.assertNotIn("a", {r["path"] for r in result["clones"]})
        self.assertNotIn("nested/b", {r["path"] for r in result["clones"]})

    def test_donor_execution_metadata_never_imported_or_executed(self):
        self.require_native()
        metadata = self.source / ".git"
        (metadata / "hooks").mkdir()
        (metadata / "hooks/post-checkout").write_text("must not execute")
        (metadata / "objects/info/alternates").write_text("/unowned-object-store\n")
        with (metadata / "config").open("a") as f:
            f.write("\n[core]\n hooksPath=/unowned\n sparseCheckout=true\n[include]\n path=/unowned-config\n")
        before = {str(p.relative_to(metadata)): p.read_bytes() for p in metadata.rglob("*") if p.is_file()}
        # Fixture-only object DATA transfer; no donor execution config is used.
        dest = self.root / "independent"
        clean = self.destination_from_copy(dest)
        result = self.finish(clean, self.prepare(clean, self.source))
        self.assertGreater(result["cloned"], 0)
        self.assertEqual({str(p.relative_to(metadata)): p.read_bytes() for p in metadata.rglob("*") if p.is_file()}, before)
        self.assertFalse((clean / ".git/hooks").exists())
        self.assertNotIn(b"/unowned", (clean / ".git/config").read_bytes())

    def destination_from_copy(self, dest):
        # This fixture manually copies loose object DATA after poisoning donor
        # config; native Git resolves the preknown commit from independent files.
        # It is not production Agh acquisition evidence. No donor .git metadata
        # is passed to the working DATA cache API.
        dest.mkdir()
        self.git(dest, "init", "-q", "--template=")
        objects = self.source / ".git/objects"
        for path in objects.glob("??/*"):
            if path.is_file():
                target = dest / ".git/objects" / path.relative_to(objects)
                target.parent.mkdir(exist_ok=True)
                target.write_bytes(path.read_bytes())
        self.git(dest, "update-ref", "refs/fixture/target", self.commit)
        return dest

    def test_path_traversal_rejected_and_existing_trees_never_prepared(self):
        for path in (b"../a", b"/a", b"a/.GIT/config", b"a//b", b"./a"):
            with self.subTest(path=path), self.assertRaises(RuntimeError):
                cache._parts(path)
        dest = self.destination("existing")
        (dest / "unowned").write_bytes(b"retain")
        self.assertEqual(self.prepare(dest, self.source).record["method"], "normal-checkout")
        self.assertEqual((dest / "unowned").read_bytes(), b"retain")

    def test_final_clone_change_and_sparse_index_refuse(self):
        self.require_native()
        dest = self.destination("changed")
        prepared = self.prepare(dest, self.source)
        self.git(dest, "checkout", "--quiet", "--detach", self.commit, "--")
        (dest / "a").write_bytes(b"edited final clone\n")
        with self.assertRaises(RuntimeError):
            prepared.verify()
        dest2 = self.destination("skip")
        prepared2 = self.prepare(dest2, self.source)
        self.git(dest2, "checkout", "--quiet", "--detach", self.commit, "--")
        self.git(dest2, "update-index", "--skip-worktree", "a")
        with self.assertRaisesRegex(RuntimeError, "sparse/assume"):
            prepared2.verify()

    def test_native_api_loss_after_preparation_retains_the_complete_owned_tree(self):
        self.require_native()
        dest = self.destination("native-api-lost")
        prepared = self.prepare(dest, self.source)
        self.assertTrue(prepared.clones)
        self.git(dest, "checkout", "--quiet", "--detach", self.commit, "--")
        before = self.inventory(dest)
        inodes = {row["path"]: (dest / row["path"]).stat().st_ino for row in prepared.clones}
        with mock.patch.object(cache, "_native", return_value=None):
            with self.assertRaises(cache.CustodyRefused) as refused:
                prepared.verify()
        self.assertTrue(refused.exception.retain_source_working_cache)
        self.assertEqual(self.inventory(dest), before)
        self.assertEqual(self.git(dest, "rev-parse", "HEAD").decode().strip(), self.commit)
        for path, inode in inodes.items():
            self.assertEqual((dest / path).stat().st_ino, inode)

    def test_native_acl_and_xattrs_are_bookended_and_never_donor_authority(self):
        self.require_native()
        import ctypes
        lib = ctypes.CDLL(None, use_errno=True)
        set_attr = lib.fsetxattr
        set_attr.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_uint, ctypes.c_int]
        fd = os.open(self.source / "a", os.O_RDONLY)
        try:
            value = ctypes.create_string_buffer(b"donor-only-data")
            self.assertEqual(set_attr(fd, b"org.trust.fixture", value, 15, 0, 0), 0)
        finally:
            os.close(fd)
        import pwd
        subprocess.run(["/bin/chmod", "+a", f"user:{pwd.getpwuid(os.getuid()).pw_name} allow read", str(self.source / "a")], check=True)
        dest = self.destination("metadata")
        result = self.finish(dest, self.prepare(dest, self.source))
        a = next(r for r in result["clones"] if r["path"] == "a")
        self.assertIsNotNone(a["source_metadata"]["extended_acl_sha256"])
        self.assertIsNone(a["normal_metadata"]["extended_acl_sha256"])
        self.assertNotEqual(a["source_metadata"], a["normal_metadata"])
        self.assertNotIn(b"org.trust.fixture".hex(), [r[0] for r in a["normal_metadata"]["xattrs"]])
        self.assertTrue((self.source / "a").exists())

    def test_unsafe_mode_donor_and_foreign_destination_data_are_not_clobbered(self):
        self.require_native()
        (self.source / "a").chmod(0o666)
        dest = self.destination("mode")
        result = self.finish(dest, self.prepare(dest, self.source))
        self.assertNotIn("a", {r["path"] for r in result["clones"]})
        self.assertEqual(stat.S_IMODE((dest / "a").stat().st_mode), 0o644)
        dest2 = self.destination("conflict")
        native = cache._native()
        conflicts = []
        def conflict(src, name, parent, leaf):
            fd = os.open(leaf, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600, dir_fd=parent)
            os.write(fd, b"appeared independent data")
            os.close(fd)
            conflicts.append((os.fstat(parent).st_ino, os.fsdecode(leaf)))
            native[1](src, name, parent, leaf)
        with mock.patch.object(cache, "_native", return_value=(native[0], conflict, native[2])):
            with self.assertRaises(RuntimeError):
                self.prepare(dest2, self.source)
        appeared = [p for p in dest2.rglob("*") if p.is_file() and '.git' not in p.parts]
        self.assertTrue(appeared)
        self.assertEqual(len(conflicts), len([p for p in appeared if p.read_bytes() == b"appeared independent data"]))

    def parent_fixture(self, name):
        parent = self.root / name
        parent.mkdir()
        self.git(parent, "init", "-q", "--template=")
        self.git(parent, "config", "user.name", "Fixture")
        self.git(parent, "config", "user.email", "fixture@example.invalid")
        (parent / ".gitmodules").write_text('[submodule "clean"]\npath=first-party/clean\nurl=https://github.com/example/clean.git\n')
        self.git(parent, "add", ".gitmodules")
        self.git(parent, "update-index", "--add", "--cacheinfo", "160000", self.commit, "first-party/clean")
        self.git(parent, "commit", "-qm", "parent pin")
        indexed = owner._indexed_submodules(parent)[0]
        return parent, indexed

    def test_production_pinned_child_installs_complete_tree_with_independent_git(self):
        self.require_native()
        parent, indexed = self.parent_fixture("parent")
        calls = []
        def acquire(url, stage, source_ref, private_ref, **kwargs):
            calls.append((url, source_ref, private_ref, kwargs))
            self.git(stage, "-c", "protocol.file.allow=always", "fetch", "-q", "--no-tags",
                     str(self.source), source_ref + ":" + private_ref)
        with mock.patch.object(owner, "_agh_source_fetch", side_effect=acquire):
            owner._install_missing_submodule(parent, indexed, checkout_cache=self.source)
        child = parent / "first-party/clean"
        self.assertEqual(self.inventory(child), self.inventory(self.source))
        self.assertEqual(self.git(child, "rev-parse", "HEAD").decode().strip(), self.commit)
        receipt = json.loads((child / ".git/trust-source-working-cache.json").read_text())
        self.assertGreater(receipt["cloned"], 0)
        self.assertEqual(calls[0][1], self.commit)
        self.assertEqual(calls[0][3]["checkout_cache"], self.source)
        for p in (child / ".git").rglob("*"):
            if p.is_file():
                self.assertEqual(p.stat().st_nlink, 1)
                self.assertFalse(p.is_symlink())
        self.assertFalse((child / ".git/objects/info/alternates").exists())

    def test_separate_plain_data_donor_never_selects_git_or_agh_authority(self):
        self.require_native()
        parent, indexed = self.parent_fixture("separate-parent")
        donor = self.root / "plain-working-data"
        (donor / "nested").mkdir(parents=True)
        (donor / "a").write_bytes((self.source / "a").read_bytes())
        (donor / "nested/b").write_bytes(b"x" * len((self.source / "nested/b").read_bytes()))
        # A locator is DATA, including any fake Git configuration beside it.
        # The owner must not load it or execute a donor hook/filter.
        (donor / ".git").mkdir()
        (donor / ".git/config").write_text("invalid donor Git configuration; never parse me\n")
        before = {str(p.relative_to(donor)): p.read_bytes() for p in donor.rglob("*") if p.is_file()}
        calls = []
        def acquire(url, stage, source_ref, private_ref, **kwargs):
            calls.append(kwargs)
            self.assertEqual(kwargs, {"checkout_cache": self.source})
            self.git(stage, "-c", "protocol.file.allow=always", "fetch", "-q", "--no-tags",
                     str(self.source), source_ref + ":" + private_ref)
        with mock.patch.object(owner, "_agh_source_fetch", side_effect=acquire):
            owner._install_missing_submodule(parent, indexed,
                checkout_cache=self.source, working_cache=donor)
        child = parent / "first-party/clean"
        receipt = json.loads((child / ".git/trust-source-working-cache.json").read_text())
        self.assertEqual(receipt["donor_data_only"], str(donor))
        self.assertGreater(receipt["cloned"], 0)
        self.assertTrue(receipt["complete_checkout_verified"])
        self.assertEqual((child / "a").read_bytes(), (self.source / "a").read_bytes())
        self.assertEqual((child / "nested/b").read_bytes(), (self.source / "nested/b").read_bytes())
        self.assertEqual(self.git(child, "rev-parse", "HEAD").decode().strip(), self.commit)
        self.assertEqual(self.git(child, "status", "--porcelain"), b"")
        self.assertEqual(before, {str(p.relative_to(donor)): p.read_bytes()
                                 for p in donor.rglob("*") if p.is_file()})
        self.assertEqual(len(calls), 1)

    def test_working_donor_declared_path_is_independent_and_disjoint(self):
        parent, _ = self.parent_fixture("declarations-parent")
        donor = self.root / "working-only"
        donor.mkdir()
        declaration = f"first-party/clean={donor}"
        self.assertEqual(owner._first_party_checkout_caches(parent, [declaration], working=True),
                         {"first-party/clean": donor})
        alias = self.root / "donor-alias"
        alias.symlink_to(donor, target_is_directory=True)
        for declarations in ([declaration, declaration],
                             [f"first-party/other={donor}"],
                             ["first-party/clean=relative"],
                             [f"first-party/clean={parent}"],
                             [f"first-party/clean={self.root}"],
                             [f"first-party/clean={alias}"]):
            with self.subTest(declarations=declarations), self.assertRaises(RuntimeError):
                owner._first_party_checkout_caches(parent, declarations, working=True)

    def test_normal_preparation_forwards_both_cache_roles_without_inventing_authority(self):
        parent, _ = self.parent_fixture("forwarding-parent")
        data = self.root / "working-forward-data"
        data.mkdir()
        objects = {"first-party/clean": self.source}
        working = {"first-party/clean": data}
        with mock.patch.object(owner, "ensure_submodules") as ensure:
            owner.prepare_first_party_sources(parent, no_build=True,
                checkout_caches=objects, working_caches=working)
        ensure.assert_called_once_with(parent, checkout_caches=objects, working_caches=working)
        with mock.patch.object(owner, "ensure_submodules") as ensure:
            owner.prepare_first_party_sources(parent, no_build=True, checkout_caches=objects)
        ensure.assert_called_once_with(parent, checkout_caches=objects)

    def test_cli_working_data_is_not_a_check_or_provenance_override(self):
        for mode in ("--check", "--verify-stage-provenance"):
            with self.subTest(mode=mode), \
                    mock.patch.object(owner, "resolve_stage0_selection") as stage0:
                self.assertEqual(owner.main([mode, "--source-working-cache", "first-party/clean=/r"]), 2)
                stage0.assert_not_called()

    def test_working_donor_alias_and_nested_paths_refuse_before_source_writes(self):
        dest = self.destination("overlap")
        nested = dest / ".git/working-data"
        nested.mkdir()
        alias = self.root / "target-alias"
        alias.symlink_to(dest, target_is_directory=True)
        for donor in (dest, nested, self.root, alias):
            with self.subTest(donor=donor), self.assertRaisesRegex(cache.CustodyRefused, "overlap"):
                self.prepare(dest, donor)
        self.assertEqual(self.git(dest, "ls-files"), b"")
        self.assertEqual(list(dest.glob(".git/trust-working-data-*")), [])

    def test_physical_directory_alias_refuses_before_clone(self):
        self.require_native()
        dest = self.destination("physical-overlap")
        real_directory = cache._directory
        @cache.contextlib.contextmanager
        def physical_alias(path):
            # Exercise physical inode-ancestry protection independently of
            # lexical spelling (as with alternate mounted namespace paths).
            actual = self.source if Path(path) == dest else path
            with real_directory(actual) as held:
                yield held
        with mock.patch.object(cache, "_directory", side_effect=physical_alias), \
                self.assertRaisesRegex(cache.CustodyRefused, "physically overlap"):
            self.prepare(dest, self.source)
        self.assertEqual(self.git(dest, "ls-files"), b"")

    def test_pinned_child_cleanup_retains_ambiguous_candidate_and_registration(self):
        self.require_native()
        parent, indexed = self.parent_fixture("refused-parent")
        original_config = (parent / ".git/config").read_bytes()
        native = cache._native()
        def acquire(url, stage, source_ref, private_ref, **kwargs):
            self.git(stage, "-c", "protocol.file.allow=always", "fetch", "-q", "--no-tags",
                     str(self.source), source_ref + ":" + private_ref)
        def failure(fd, directory, name):
            foreign = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600, dir_fd=directory)
            os.write(foreign, b"retain through owner cleanup")
            os.close(foreign)
            raise OSError(errno.EIO, "unknown failed-clone candidate")
        with mock.patch.object(owner, "_agh_source_fetch", side_effect=acquire), mock.patch.object(
                owner, "_prepare_source_working_cache", side_effect=lambda stage, commit, donor: self.prepare(stage, donor)), mock.patch.object(
                cache, "_native", return_value=(failure, *native[1:])):
            with self.assertRaises(cache.CustodyRefused):
                owner._install_missing_submodule(parent, indexed, checkout_cache=self.source)
        candidates = list((parent / "first-party").glob(".trust-submodule-*/source/.git/trust-working-data-*/candidate"))
        self.assertEqual(len(candidates), 1)
        self.assertEqual(candidates[0].read_bytes(), b"retain through owner cleanup")
        self.assertFalse((parent / "first-party/clean").exists())
        self.assertEqual((parent / ".git/config").read_bytes(), original_config)

    def test_pinned_child_retains_lost_installation_and_final_audit_custody(self):
        self.require_native()
        native = cache._native()
        for variant in ("replace", "missing", "move-error", "conflict", "final-audit"):
            with self.subTest(variant=variant):
                parent, indexed = self.parent_fixture("lost-" + variant)
                config_before = (parent / ".git/config").read_bytes()
                index_before = (parent / ".git/index").read_bytes()
                payload = b"independent installed replacement: retain"
                affected = []
                prepared = []

                def acquire(url, stage, source_ref, private_ref, **kwargs):
                    self.git(stage, "-c", "protocol.file.allow=always", "fetch", "-q", "--no-tags",
                             str(self.source), source_ref + ":" + private_ref)

                def replace(directory, leaf):
                    fd = os.open(leaf, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600, dir_fd=directory)
                    try:
                        os.write(fd, payload)
                    finally:
                        os.close(fd)

                def move(source, name, destination, leaf):
                    if variant == "final-audit":
                        return native[1](source, name, destination, leaf)
                    affected.append(os.fsdecode(leaf))
                    if variant == "conflict":
                        replace(destination, leaf)
                        return native[1](source, name, destination, leaf)
                    native[1](source, name, destination, leaf)
                    os.unlink(leaf, dir_fd=destination)
                    if variant != "missing":
                        replace(destination, leaf)
                    if variant == "move-error":
                        raise OSError(errno.EIO, "move returned after an uncertain installation")

                def prepare(stage, commit, donor):
                    value = self.prepare(stage, donor)
                    prepared.append((stage, value))
                    return value

                actual_git = owner._local_submodule_git
                def git(arguments, **kwargs):
                    result = actual_git(arguments, **kwargs)
                    if variant == "final-audit" and "checkout" in arguments and prepared:
                        stage, value = prepared[0]
                        leaf = stage / value.clones[0]["path"]
                        affected.append(str(leaf.relative_to(stage)))
                        leaf.unlink()
                        leaf.write_bytes(payload)
                    return result

                with mock.patch.object(owner, "_agh_source_fetch", side_effect=acquire), mock.patch.object(
                        owner, "_prepare_source_working_cache", side_effect=prepare), mock.patch.object(
                        owner, "_local_submodule_git", side_effect=git), mock.patch.object(
                        cache, "_native", return_value=(native[0], move, native[2])):
                    with self.assertRaises(cache.CustodyRefused):
                        owner._install_missing_submodule(parent, indexed, checkout_cache=self.source)
                self.assertEqual(len(affected), 1)
                stages = list((parent / "first-party").glob(".trust-submodule-*/source"))
                self.assertEqual(len(stages), 1, "outer cleanup deleted ambiguous installed source")
                leaf = stages[0] / affected[0]
                if variant == "missing":
                    self.assertFalse(leaf.exists(), "lost custody was silently reconstructed")
                else:
                    self.assertEqual(leaf.read_bytes(), payload)
                self.assertFalse((parent / "first-party/clean").exists())
                self.assertEqual((parent / ".git/config").read_bytes(), config_before)
                self.assertEqual((parent / ".git/index").read_bytes(), index_before)

    def test_actual_captured_loader_cold_and_warm_routes(self):
        loader_owner = load("working_cache_source_loader", SCRIPT / "seed_custody_source.py")
        repo = SCRIPT.parent
        names = ("scripts/recreate_bootstrap.py", "src/bootstrap/stage0_identity.py", "scripts/source_working_cache.py")
        expected = {name: hashlib.sha256((repo / name).read_bytes()).hexdigest() for name in names}
        cold_loader = loader_owner.BoundSourceLoader(repo, {n: expected[n] for n in names[:2]})
        cold_api = cold_loader.module("working_cache_bound_cold_bootstrap", repo / names[0])
        cold = self.destination("bound-cold")
        normal = cold_api._prepare_source_working_cache(cold, self.commit, None)
        self.git(cold, "checkout", "--quiet", "--detach", self.commit, "--")
        self.assertEqual(normal.verify()["method"], "normal-checkout")
        cold_loader.recheck()
        self.require_native()
        loader = loader_owner.BoundSourceLoader(repo, expected)
        api = loader.module("working_cache_bound_bootstrap", repo / names[0])
        warm = self.destination("bound-warm")
        prepared = api._prepare_source_working_cache(warm, self.commit, self.source)
        self.git(warm, "checkout", "--quiet", "--detach", self.commit, "--")
        result = prepared.verify()
        self.assertGreater(result["cloned"], 0)
        self.assertEqual(self.inventory(cold), self.inventory(warm))
        loader.recheck()

    def test_replaced_private_controls_are_preserved_on_refusal(self):
        self.require_native()
        native = cache._native()
        for error in (errno.EEXIST, errno.EXDEV, errno.EIO):
            with self.subTest(error=error):
                dest = self.destination("unknown-candidate-" + str(error))
                def existing(fd, directory, name):
                    foreign = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600, dir_fd=directory)
                    os.write(foreign, b"preserve unexpected candidate")
                    os.close(foreign)
                    raise OSError(error, "unexpected candidate after failed clone")
                with mock.patch.object(cache, "_native", return_value=(existing, *native[1:])):
                    with self.assertRaisesRegex(RuntimeError, "unknown custody"):
                        self.prepare(dest, self.source)
                candidates = list((dest / ".git").glob("trust-working-data-*/candidate"))
                self.assertEqual(len(candidates), 1)
                self.assertEqual(candidates[0].read_bytes(), b"preserve unexpected candidate")

    def test_native_destination_group_is_normal_policy_or_complete_fallback(self):
        self.require_native()
        groups = [g for g in os.getgroups() if g != os.getgid()]
        if not groups:
            self.skipTest("no supplementary group available for native group-policy control")
        dest = self.destination("different-group")
        os.chown(dest, -1, groups[0])
        os.chmod(dest, 0o2755)
        prepared = self.prepare(dest, self.source)
        result = self.finish(dest, prepared)
        for path in ("a", ".gitmodules", "executable"):
            self.assertEqual((dest / path).stat().st_gid, groups[0])
        self.assertEqual(self.git(dest, "status", "--porcelain"), b"")
        # On systems whose clone API honors this policy directly these can be
        # valid hits; otherwise exact metadata mismatch must take normal Git.
        for row in result["clones"]:
            self.assertEqual(row["destination"][5], (dest / row["path"]).stat().st_gid)

    def test_complete_audit_refuses_changed_fallback_missing_symlink_and_gitlink(self):
        self.require_native()
        (self.source / "nested/b").write_bytes(b"corrupt donor")
        for corruption in ("fallback", "missing", "symlink", "gitlink"):
            with self.subTest(corruption=corruption):
                dest = self.destination("final-" + corruption)
                prepared = self.prepare(dest, self.source)
                self.git(dest, "checkout", "--quiet", "--detach", self.commit, "--")
                if corruption == "fallback":
                    info = (dest / "nested/b").stat()
                    (dest / "nested/b").write_bytes(b"x" * info.st_size)
                    os.utime(dest / "nested/b", ns=(info.st_atime_ns, info.st_mtime_ns))
                    with self.assertRaisesRegex(RuntimeError, "physical source audit"):
                        owner._source_working_cache_physical(dest)
                elif corruption == "missing":
                    (dest / "nested/b").unlink()
                elif corruption == "symlink":
                    (dest / "symbolic").unlink()
                    (dest / "symbolic").write_bytes(b"a")
                else:
                    (dest / "child").rmdir()
                    (dest / "child").symlink_to(self.source, target_is_directory=True)
                with self.assertRaises(RuntimeError):
                    prepared.verify()

    def test_cold_warm_permissions_and_directories_match_under_actual_umask(self):
        self.require_native()
        for mask in (0o077, 0o027, 0o002):
            with self.subTest(mask=oct(mask)):
                # This test process has no threads. Production never reads or
                # resets process-global umask; actual creation applies it.
                previous = os.umask(mask)
                try:
                    cold = self.destination("umask-cold-" + str(mask))
                    self.finish(cold, self.prepare(cold))
                    warm = self.destination("umask-warm-" + str(mask))
                    result = self.finish(warm, self.prepare(warm, self.source))
                    self.assertGreater(result["cloned"], 0)
                    self.assertEqual(self.inventory(cold), self.inventory(warm))
                    for directory in ("nested", "child"):
                        self.assertEqual(stat.S_IMODE((cold / directory).stat().st_mode),
                                         stat.S_IMODE((warm / directory).stat().st_mode))
                    self.assertEqual(stat.S_IMODE((warm / "a").stat().st_mode), 0o666 & ~mask)
                    self.assertEqual(stat.S_IMODE((warm / "executable").stat().st_mode), 0o777 & ~mask)
                    native = cache._native()
                    for path in ("a", "nested/b", "executable"):
                        left, right = (cold / path).stat(), (warm / path).stat()
                        self.assertEqual((left.st_uid, left.st_gid, left.st_flags),
                                         (right.st_uid, right.st_gid, right.st_flags))
                        with (cold / path).open("rb") as a, (warm / path).open("rb") as b:
                            self.assertEqual({k: v for k, v in native[2](a.fileno()).items() if k != "birthtime_ns"},
                                             {k: v for k, v in native[2](b.fileno()).items() if k != "birthtime_ns"})
                finally:
                    os.umask(previous)

    def test_destination_inherited_acl_matches_cold_git_or_falls_back(self):
        self.require_native()
        import pwd
        cold, warm = self.destination("acl-cold"), self.destination("acl-warm")
        for dest in (cold, warm):
            subprocess.run(["/bin/chmod", "+a", f"user:{pwd.getpwuid(os.getuid()).pw_name} allow read,write,file_inherit,directory_inherit", str(dest)], check=True)
        self.finish(cold, self.prepare(cold))
        result = self.finish(warm, self.prepare(warm, self.source))
        self.assertEqual(self.inventory(cold), self.inventory(warm))
        native = cache._native()
        for path in ("a", "nested/b", "executable"):
            with (cold / path).open("rb") as a, (warm / path).open("rb") as b:
                self.assertEqual({k: v for k, v in native[2](a.fileno()).items() if k != "birthtime_ns"},
                                 {k: v for k, v in native[2](b.fileno()).items() if k != "birthtime_ns"})
        self.assertTrue(result["complete_checkout_verified"])

    def test_replaced_empty_or_symlink_temporary_directory_is_never_cleaned(self):
        self.require_native()
        native = cache._native()
        for replacement in ("empty", "symlink"):
            with self.subTest(replacement=replacement):
                dest = self.destination("temp-" + replacement)
                external = self.root / ("outside-" + replacement)
                external.mkdir()
                (external / "foreign").write_bytes(b"outside retained")
                replaced = []
                def replace(fd, directory, name):
                    if not replaced:
                        temp = next((dest / ".git").glob("trust-working-data-*"))
                        original = dest / ".git/original-private-temp"
                        temp.rename(original)
                        if replacement == "empty":
                            temp.mkdir()
                        else:
                            temp.symlink_to(external, target_is_directory=True)
                        replaced.append((temp, temp.lstat().st_ino, original))
                    raise OSError(errno.EXDEV, "cache miss after directory replacement")
                with mock.patch.object(cache, "_native", return_value=(replace, *native[1:])):
                    with self.assertRaises(cache.CustodyRefused):
                        self.prepare(dest, self.source)
                temp, inode, original = replaced[0]
                self.assertEqual(temp.lstat().st_ino, inode)
                self.assertTrue(original.is_dir())
                self.assertEqual((external / "foreign").read_bytes(), b"outside retained")
                if replacement == "symlink":
                    self.assertTrue(temp.is_symlink())
                else:
                    self.assertEqual(list(temp.iterdir()), [])

    def test_old_and_future_donor_times_never_supply_working_freshness(self):
        self.require_native()
        regular = ("a", "nested/b", "executable", ".gitmodules")
        ages = (946684800000000000, time.time_ns() + 10 * 366 * 24 * 3600 * 10**9)
        native = cache._native()
        for index, age in enumerate(ages):
            with self.subTest(age=age):
                for name in regular:
                    os.utime(self.source / name, ns=(age, age))
                    with (self.source / name).open("rb") as file:
                        self.assertEqual(native[2].birthtime(file.fileno(), age), age)
                source_before = {name: ((self.source / name).stat().st_ino,
                                        (self.source / name).stat().st_mtime_ns,
                                        (self.source / name).read_bytes()) for name in regular}
                cold, warm = self.destination("time-cold-" + str(index)), self.destination("time-warm-" + str(index))
                start = time.time_ns()
                self.finish(cold, self.prepare(cold))
                prepared = self.prepare(warm, self.source)
                inodes = {r["path"]: (warm / r["path"]).stat().st_ino for r in prepared.clones}
                result = self.finish(warm, prepared)
                end = time.time_ns()
                self.assertEqual(len(inodes), len(regular))
                self.assertEqual(self.inventory(cold), self.inventory(warm))
                for row in result["clones"]:
                    name = row["path"]
                    info = (warm / name).stat()
                    self.assertEqual(info.st_ino, inodes[name])
                    self.assertEqual(info.st_mtime_ns, row["normal_times_ns"]["mtime"])
                    self.assertTrue(start <= info.st_mtime_ns <= end)
                    self.assertTrue(start <= info.st_atime_ns <= end)
                    self.assertTrue(start <= row["normal_times_ns"]["atime"] <= end)
                    self.assertTrue(start <= (cold / name).stat().st_mtime_ns <= end)
                    self.assertNotEqual(info.st_mtime_ns, age)
                    self.assertTrue(start <= row["normal_metadata"]["birthtime_ns"] <= end)
                    with (warm / name).open("rb") as file:
                        self.assertEqual(native[2].birthtime(file.fileno()), row["normal_metadata"]["birthtime_ns"])
                    with (self.source / name).open("rb") as file:
                        self.assertEqual(native[2].birthtime(file.fileno()), age)
                    self.assertEqual(((self.source / name).stat().st_ino,
                                      (self.source / name).stat().st_mtime_ns,
                                      (self.source / name).read_bytes()), source_before[name])

    def test_unsupported_timestamp_normalization_keeps_complete_fallback_under_umask(self):
        self.require_native()
        native = cache._native()
        for mask in (0o077, 0o027):
            for unsupported in ("utime", "birthtime"):
                with self.subTest(mask=oct(mask), unsupported=unsupported):
                    previous = os.umask(mask)
                    try:
                        dest = self.destination("unsupported-" + unsupported + str(mask))
                        if unsupported == "utime":
                            with mock.patch.object(cache.os, "utime", side_effect=OSError(errno.ENOTSUP, "unsupported fd timestamp normalization")):
                                prepared = self.prepare(dest, self.source)
                        else:
                            metadata = cache._native()[2]
                            normal = metadata.birthtime
                            def unavailable(fd, value=None):
                                if value is not None:
                                    raise OSError(errno.ENOTSUP, "unsupported creation-time normalization")
                                return normal(fd)
                            metadata.birthtime = unavailable
                            with mock.patch.object(cache, "_native", return_value=(native[0], native[1], metadata)):
                                prepared = self.prepare(dest, self.source)
                        result = self.finish(dest, prepared)
                        self.assertEqual(result["cloned"], 0)
                        self.assertEqual((dest / "a").read_bytes(), b"actual exact regular source\n")
                        self.assertEqual(stat.S_IMODE((dest / "a").stat().st_mode), 0o666 & ~mask)
                        self.assertEqual(self.git(dest, "status", "--porcelain"), b"")
                        self.assertEqual(list((dest / ".git").glob("trust-working-data-*")), [])
                    finally:
                        os.umask(previous)


if __name__ == "__main__":
    unittest.main()
