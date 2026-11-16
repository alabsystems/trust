"""Archive-derived Darwin linker roles; fixtures grant no SDK/proof claim."""
import hashlib
import importlib.util
import io
import os
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src/bootstrap"))
import bootstrap
import bootstrap_test

SPEC = importlib.util.spec_from_file_location("paired_linker_recreator", ROOT / "scripts/recreate_bootstrap.py")
recreator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = recreator
SPEC.loader.exec_module(recreator)

HOST = "aarch64-apple-darwin"
owner = bootstrap._identity_owner


class PairedLinkerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "bin").mkdir()
        self.source = self.root / f"lib/rustlib/{HOST}/bin/rust-lld"
        self.source.parent.mkdir(parents=True)
        self.source.write_bytes(b"archive-bound host linker")
        self.source.chmod(0o755)
        self.selected = self.root / "bin/rust-lld"

    def test_materializes_exact_bytes_mode_and_distinct_inode(self):
        role = owner.paired_linker(self.root, HOST, materialize=True)
        self.assertEqual(self.selected.read_bytes(), self.source.read_bytes())
        self.assertFalse(os.path.samefile(self.selected, self.source))
        self.assertEqual(role["sha256"], hashlib.sha256(self.source.read_bytes()).hexdigest())
        self.assertEqual(owner.paired_linker(self.root, HOST), role)
        self.assertEqual(owner.paired_linker(self.root, HOST, materialize=True), role)

    def test_reader_cannot_repair_missing_role(self):
        with self.assertRaises(FileNotFoundError):
            owner.paired_linker(self.root, HOST)
        self.assertFalse(self.selected.exists())

    def test_refuses_substituted_root_linker_bytes_or_mode(self):
        self.selected.write_bytes(b"foreign linker")
        self.selected.chmod(0o755)
        with self.assertRaisesRegex(ValueError, "differs"):
            owner.paired_linker(self.root, HOST, materialize=True)
        self.selected.write_bytes(self.source.read_bytes())
        self.selected.chmod(0o700)
        with self.assertRaisesRegex(ValueError, "modes differ"):
            owner.paired_linker(self.root, HOST, materialize=True)

    def test_refuses_root_symlink_and_hardlink(self):
        self.selected.symlink_to(self.source)
        with self.assertRaisesRegex(ValueError, "confined and regular"):
            owner.paired_linker(self.root, HOST, materialize=True)
        self.selected.unlink()
        os.link(self.source, self.selected)
        with self.assertRaisesRegex(ValueError, "distinct executable inodes"):
            owner.paired_linker(self.root, HOST, materialize=True)

    def test_refuses_inner_directory_symlink(self):
        real = self.source.parent
        real.rename(real.with_name("actual-bin"))
        real.symlink_to("actual-bin")
        with self.assertRaises((ValueError, OSError)):
            owner.paired_linker(self.root, HOST, materialize=True)
        self.assertFalse(self.selected.exists())

    def test_refuses_nonexecutable_host_image(self):
        self.source.chmod(0o644)
        with self.assertRaisesRegex(ValueError, "not executable"):
            owner.paired_linker(self.root, HOST, materialize=True)

    def test_refuses_same_target_directory_alias_introduced_during_hash(self):
        owner.paired_linker(self.root, HOST, materialize=True)
        original = owner.hashlib.sha256
        calls = 0
        def substituted(*args, **kwargs):
            nonlocal calls
            calls += 1
            if calls == 2:
                (self.root / "bin").rename(self.root / "saved-bin")
                (self.root / "bin").symlink_to("saved-bin")
            return original(*args, **kwargs)
        with mock.patch.object(owner.hashlib, "sha256", substituted):
            with self.assertRaisesRegex(ValueError, "directory"):
                owner.paired_linker(self.root, HOST)

    def test_creation_cannot_follow_directory_replaced_with_outside_alias(self):
        outside = self.root / "outside-seed"
        outside.mkdir()
        original = owner.os.open
        def substituted(path, flags, *args, **kwargs):
            if flags & os.O_CREAT:
                (self.root / "bin").rename(self.root / "saved-bin")
                (self.root / "bin").symlink_to(outside)
            return original(path, flags, *args, **kwargs)
        with mock.patch.object(owner.os, "open", substituted):
            with self.assertRaisesRegex(ValueError, "directory"):
                owner.paired_linker(self.root, HOST, materialize=True)
        self.assertFalse((outside / "rust-lld").exists())
        self.assertEqual((self.root / "saved-bin/rust-lld").read_bytes(), self.source.read_bytes())

    def test_legacy_and_other_host_have_no_invented_capability(self):
        self.source.unlink()
        self.assertIsNone(owner.paired_linker(self.root, HOST, materialize=True))
        self.assertIsNone(owner.paired_linker(self.root, "x86_64-unknown-linux-gnu", materialize=True))
        self.selected.write_bytes(b"unbound root role")
        with self.assertRaisesRegex(ValueError, "lacks its archived host image"):
            owner.paired_linker(self.root, HOST, materialize=True)


class ExtractionTests(unittest.TestCase):
    def fixture(self, conflicting=False):
        fixture = bootstrap_test.Stage0FailClosedRefresh()
        fixture.setUp()
        self.addCleanup(fixture.tearDown)
        fixture.BUILD = HOST
        build = fixture.make_build()
        plan = fixture.component_plan(build)
        plan["trustc"][1].append(f"lib/rustlib/{HOST}/bin/rust-lld")
        if conflicting:
            plan["trustc"][1].append("bin/rust-lld")
        fixture.component_plan = lambda _: plan
        fixture.make_archives(build)
        # The existing generic fixture writes data files. This profile's
        # archived linker is a genuine regular executable role.
        archive = next((Path(fixture.dist_root) / "dist" / fixture.DATE).glob("trustc-*.tar.xz"))
        with tarfile.open(archive, "r:xz") as tar:
            entries = [(member, tar.extractfile(member).read()) for member in tar]
        with tarfile.open(archive, "w:xz") as tar:
            for member, data in entries:
                member.mode = 0o755
                if conflicting and member.name.endswith("/trustc/bin/rust-lld"):
                    data = b"substituted root executable"
                member.size = len(data)
                tar.addfile(member, io.BytesIO(data))
        build.stage0_data[f"dist/{fixture.DATE}/{archive.name}"] = hashlib.sha256(archive.read_bytes()).hexdigest()
        return fixture, build

    def test_real_authenticated_extraction_materializes_before_atomic_swap(self):
        fixture, build = self.fixture()
        build.download_toolchain()
        role = owner.paired_linker(Path(build.bin_root()), HOST)
        self.assertTrue(role["distinct_inodes"])
        fixture.assert_no_refresh_residue(build)
        self.assertTrue(Path(build.rustc_stamp()).read_text().startswith("trust-stage0-extraction-v3:"))

    def test_bad_archived_root_role_cannot_displace_existing_seed(self):
        fixture, build = self.fixture(conflicting=True)
        old = fixture.write_seed(build)
        before = fixture.snapshot(old)
        with self.assertRaisesRegex(ValueError, "differs"):
            build.download_toolchain()
        self.assertEqual(fixture.snapshot(old), before)
        fixture.assert_no_refresh_residue(build)


class ArchiveBindingTests(unittest.TestCase):
    def capture(self, root_kind=None, root_payload=b"archived linker"):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        date, version = "2026-11-07", "0.13.0-trust"
        archive = root / f"bootstrap/trust-stage0/dist/{date}/trustc-{version}-{HOST}.tar.xz"
        archive.parent.mkdir(parents=True)
        prefix = f"trustc-{version}-{HOST}/trustc/"
        with tarfile.open(archive, "w:xz") as tar:
            for relative in ("bin/trustc", "bin/rustc", "bin/trustdoc", "libexec/trust-analyzer-proc-macro-srv",
                             f"lib/rustlib/{HOST}/bin/rust-lld"):
                member = tarfile.TarInfo(prefix + relative)
                member.mode = 0o755
                member.size = len(b"archived linker")
                tar.addfile(member, io.BytesIO(b"archived linker"))
            if root_kind:
                member = tarfile.TarInfo(prefix + "bin/rust-lld")
                member.mode = 0o755
                member.type = root_kind
                member.linkname = f"../lib/rustlib/{HOST}/bin/rust-lld"
                member.size = len(root_payload) if member.isfile() else 0
                tar.addfile(member, io.BytesIO(root_payload) if member.isfile() else None)
        errors = []
        records, bindings = recreator._capture_seed_archive_members(root, HOST,
            {"compiler_version": version, "rustfmt_version": version, "compiler_date": date},
            [{"path": archive.relative_to(root).as_posix()}], errors)
        # This fixture intentionally contains only the compiler component.
        errors = [error for error in errors if "does not declare the exact required archive" not in error]
        return root, records, bindings, errors

    def test_old_archive_root_role_has_explicit_exact_member_provenance(self):
        root, records, bindings, errors = self.capture()
        self.assertEqual(errors, [])
        role = bindings["bin/rust-lld"]
        self.assertEqual(role["materialization"], "paired-linker-copy-v1")
        self.assertEqual(role["derived_from"], f"lib/rustlib/{HOST}/bin/rust-lld")
        self.assertEqual(role["member_sha256"], hashlib.sha256(b"archived linker").hexdigest())
        self.assertEqual(len(records), 6)

    def test_new_archive_roles_must_match_and_be_regular(self):
        _, _, bindings, errors = self.capture(tarfile.REGTYPE)
        self.assertEqual(errors, [])
        self.assertNotIn("materialization", bindings["bin/rust-lld"])
        _, _, _, errors = self.capture(tarfile.REGTYPE, b"foreign root linker")
        self.assertTrue(any("differ in bytes or mode" in error for error in errors))
        _, _, _, errors = self.capture(tarfile.SYMTYPE)
        self.assertTrue(any("not regular executable" in error for error in errors))

    def test_hydrated_role_is_checked_against_archive_not_only_tree_hash(self):
        root, _, bindings, errors = self.capture()
        stage0 = root / "build" / HOST / "stage0"
        source = stage0 / f"lib/rustlib/{HOST}/bin/rust-lld"
        source.parent.mkdir(parents=True)
        (stage0 / "bin").mkdir()
        source.write_bytes(b"foreign but internally consistent linker")
        source.chmod(0o755)
        owner.paired_linker(stage0, HOST, materialize=True)
        captured = recreator._capture_seed_compiler_identity(root, HOST, {}, bindings, {})
        self.assertIn("hydrated paired linker differs from its pinned archive member", captured["errors"])
        self.assertEqual(captured["status"], "rejected")


if __name__ == "__main__":
    unittest.main()
