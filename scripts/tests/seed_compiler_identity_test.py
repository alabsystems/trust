"""Real archive bytes and fake compiler fixtures; no native admission claim."""

from __future__ import annotations

import hashlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS / "lib"))
identity = importlib.import_module("seed_compiler_identity")

SPEC = importlib.util.spec_from_file_location(
    "identity_fixture_freshness", SCRIPTS / "check_seed_freshness.py"
)
freshness = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = freshness
SPEC.loader.exec_module(freshness)

PIN = "1" * 40
SEED = """#!/usr/bin/env python3
import os,pathlib,sys
ledger=os.environ.get('IDENTITY_FIXTURE_LEDGER')
if ledger:
 with open(ledger,'a') as log: log.write('identity\\n' if '-vV' in sys.argv else 'produce\\n')
if '-vV' in sys.argv:
 print('commit-hash: {commit}')
 print('commit-date: 2026-07-13')
 print('release: 1.99.0-trust')
 {mutation}
 raise SystemExit(0)
{production}
"""


def archive_fixture(root, payload=b"exact launcher", *, members=None):
    compiler = root / "build/test-host/stage0/bin/rustc"
    compiler.parent.mkdir(parents=True)
    compiler.write_bytes(payload)
    compiler.chmod(0o755)
    relative = "dist/2026-07-13/trustc-1.99.0-trust-test-host.tar.xz"
    archive = root / "bootstrap/trust-stage0" / relative
    archive.parent.mkdir(parents=True)
    member = "trustc-1.99.0-trust-test-host/trustc/bin/trustc"
    with tarfile.open(archive, "w:xz") as image:
        for name, content, kind in members or [(member, payload, tarfile.REGTYPE)]:
            item = tarfile.TarInfo(name)
            item.type = kind
            item.size = len(content) if kind == tarfile.REGTYPE else 0
            item.linkname = "other" if kind == tarfile.SYMTYPE else ""
            image.addfile(item, io.BytesIO(content) if item.size else None)
    stage0 = {
        "compiler_git_commit_hash": PIN,
        "compiler_date": "2026-07-13",
        "compiler_version": "1.99.0-trust",
        relative: hashlib.sha256(archive.read_bytes()).hexdigest(),
    }
    (root / "src").mkdir()
    (root / "src/stage0").write_text(
        "\n".join(f"{k}={v}" for k, v in stage0.items()) + "\n"
    )
    return compiler, archive, stage0


class CompilerIdentityTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="seed identity ü ")
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)

    def test_actual_archive_member_binds_literal_invocation_and_snapshot(self):
        compiler, _, stage0 = archive_fixture(self.root)
        bound = identity.authenticate_compiler(self.root, compiler, stage0)
        identity.check_compiler_snapshot(compiler, bound)
        self.assertEqual(bound[1], hashlib.sha256(compiler.read_bytes()).hexdigest())
        self.assertIsNotNone(
            identity.pinned_compiler_binding(self.root, compiler, timeout=10)
        )

    def test_layout_policy_remains_inside_the_authenticated_transitive_source_graph(self):
        root = SCRIPTS.parent.resolve()
        paths = ("scripts/lib/seed_compiler_identity.py", "scripts/mint_seed_support.py",
                 "src/bootstrap/stage0_identity.py")
        expected = {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                    for name in paths}
        spec = importlib.util.spec_from_file_location(
            "identity_bound_source_control", SCRIPTS / "seed_custody_source.py")
        source = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(source)
        with mock.patch.dict(sys.modules):
            owner = source.BoundSourceLoader(root, expected)
            bound = owner.module("identity_bound_positive", root / paths[0])
            bound._layout_owner()
            self.assertEqual(owner.executed, expected)
            owner.recheck()
            for bad_manifest in ({name: value for name, value in expected.items()
                                  if name != paths[1]}, {**expected, paths[1]: "0" * 64}):
                with self.subTest(manifest=bad_manifest.get(paths[1], "missing")):
                    refused = source.BoundSourceLoader(root, bad_manifest)
                    bound = refused.module("identity_bound_negative", root / paths[0])
                    with self.assertRaisesRegex(ValueError, "live owner manifest"):
                        bound._layout_owner()

    def test_sanctioned_default_build_alias_binds_both_literal_spellings(self):
        compiler, _, _ = archive_fixture(self.root)
        (self.root / "build").rename(self.root / "build.noindex")
        (self.root / "build").symlink_to("build.noindex", target_is_directory=True)
        physical = self.root / "build.noindex/test-host/stage0/bin/rustc"
        for selected in (compiler, physical):
            with self.subTest(selected=selected):
                bound = identity.pinned_compiler_binding(self.root, selected, timeout=10)
                self.assertIsNotNone(bound)
                identity.check_compiler_snapshot(selected, bound)
        physical.write_bytes(b"changed physical compiler")
        with self.assertRaisesRegex(identity.SeedIdentityError, "pinned archive member"):
            identity.pinned_compiler_binding(self.root, physical, timeout=10)

    def test_reserved_physical_spelling_never_skips_binding_for_invalid_layout(self):
        compiler, _, _ = archive_fixture(self.root)
        (self.root / "build").rename(self.root / "build.noindex")
        physical = self.root / "build.noindex/test-host/stage0/bin/rustc"
        lexical = self.root / "build"
        other = self.root / "other-build"
        other.mkdir()
        outside = self.root.parent / (self.root.name + "-physical-outside")
        outside.mkdir()
        self.addCleanup(outside.rmdir)
        physical.write_bytes(b"different physical bytes")
        for shape in ("absent", "wrong", "outside", "real", "file"):
            with self.subTest(shape=shape):
                if shape == "wrong": lexical.symlink_to(other, target_is_directory=True)
                elif shape == "outside": lexical.symlink_to(outside, target_is_directory=True)
                elif shape == "real":
                    # Another valid lexical compiler must never substitute for
                    # the different physical invocation selected by the caller.
                    real = lexical / "test-host/stage0/bin/rustc"
                    real.parent.mkdir(parents=True)
                    real.write_bytes(b"exact launcher")
                    real.chmod(0o755)
                elif shape == "file": lexical.write_bytes(b"not a directory")
                try:
                    with self.assertRaisesRegex(identity.SeedIdentityError, "sanctioned"):
                        identity.pinned_compiler_binding(self.root, physical, timeout=10)
                finally:
                    if lexical.is_symlink() or lexical.is_file(): lexical.unlink()
                    elif lexical.is_dir():
                        if shape == "real":
                            real.unlink()
                            real.parent.rmdir()
                            real.parent.parent.rmdir()
                            real.parent.parent.parent.rmdir()
                        lexical.rmdir()
        # Nonreserved explicit external/custom roots retain their old boundary.
        self.assertIsNone(identity.pinned_compiler_binding(
            self.root, other / "test-host/stage0/bin/rustc", timeout=10))

    def test_generated_host_alias_authenticates_the_canonical_host_archive(self):
        for noindex in (False, True):
            root = self.root / str(noindex)
            root.mkdir()
            compiler, _, stage0 = archive_fixture(root)
            if noindex:
                (root / "build").rename(root / "build.noindex")
                (root / "build").symlink_to("build.noindex", target_is_directory=True)
            alias = root / "build/host"
            for target in (Path("test-host"), compiler.parents[2]):
                with self.subTest(noindex=noindex, target=target):
                    alias.symlink_to(target, target_is_directory=True)
                    selected = alias / "stage0/bin/rustc"
                    binding = identity.authenticate_compiler(root, selected, stage0)
                    identity.check_compiler_snapshot(selected, binding)
                    self.assertEqual(binding[1], hashlib.sha256(compiler.read_bytes()).hexdigest())
                    alias.unlink()
            alias.symlink_to(compiler.parents[2], target_is_directory=True)
            compiler.write_bytes(b"substituted compiler")
            with self.assertRaisesRegex(identity.SeedIdentityError, "pinned archive member"):
                identity.authenticate_compiler(root, alias / "stage0/bin/rustc", stage0)

    def test_absolute_host_alias_can_retain_the_source_checkout_alias(self):
        compiler, _, stage0 = archive_fixture(self.root)
        source_alias = self.root.parent / (self.root.name + "-source-alias")
        source_alias.symlink_to(self.root, target_is_directory=True)
        self.addCleanup(source_alias.unlink)
        alias = self.root / "build/host"
        alias.symlink_to(source_alias / "build/test-host", target_is_directory=True)
        selected = alias / "stage0/bin/rustc"
        binding = identity.authenticate_compiler(self.root, selected, stage0)
        identity.check_compiler_snapshot(selected, binding)

    def test_host_alias_rejects_outside_traversal_chains_loops_and_wrong_owner(self):
        compiler, _, stage0 = archive_fixture(self.root)
        alias = self.root / "build/host"
        (self.root / "build/chain").symlink_to("test-host", target_is_directory=True)
        outside = self.root / "outside/test-host"
        outside.mkdir(parents=True)
        for target in ("../outside/test-host", outside, "chain", "host", "missing-host"):
            with self.subTest(target=target):
                alias.symlink_to(target, target_is_directory=True)
                with self.assertRaises(identity.SeedIdentityError):
                    identity.authenticate_compiler(self.root, alias / "stage0/bin/rustc", stage0)
                alias.unlink()
        alias.symlink_to("test-host", target_is_directory=True)
        with mock.patch.object(identity.os, "geteuid", return_value=os.geteuid() + 1):
            with self.assertRaisesRegex(identity.SeedIdentityError, "owned symlink"):
                identity.authenticate_compiler(self.root, alias / "stage0/bin/rustc", stage0)

    def test_host_alias_substitution_cannot_reuse_an_identical_file_snapshot(self):
        compiler, _, stage0 = archive_fixture(self.root)
        alias = self.root / "build/host"
        alias.symlink_to("test-host", target_is_directory=True)
        selected = alias / "stage0/bin/rustc"
        binding = identity.authenticate_compiler(self.root, selected, stage0)
        other = self.root / "build/other-host/stage0/bin/rustc"
        other.parent.mkdir(parents=True)
        os.link(compiler, other)
        alias.unlink()
        alias.symlink_to("other-host", target_is_directory=True)
        self.assertEqual(selected.stat().st_ino, compiler.stat().st_ino)
        with self.assertRaisesRegex(identity.SeedIdentityError, "path changed"):
            identity.check_compiler_snapshot(selected, binding)
        alias.unlink()
        alias.symlink_to("test-host", target_is_directory=True)
        binding = identity.authenticate_compiler(self.root, selected, stage0)
        alias.unlink()
        alias.symlink_to("test-host", target_is_directory=True)
        with self.assertRaisesRegex(identity.SeedIdentityError, "path changed"):
            identity.check_compiler_snapshot(selected, binding)

    def test_default_build_alias_does_not_admit_outside_or_inner_links(self):
        compiler, _, stage0 = archive_fixture(self.root)
        physical = self.root / "build.noindex"
        (self.root / "build").rename(physical)
        # Another real directory is not the maintained build.noindex target.
        (self.root / "build").symlink_to("elsewhere", target_is_directory=True)
        (self.root / "elsewhere").mkdir()
        with self.assertRaisesRegex(identity.SeedIdentityError, "sanctioned"):
            identity.authenticate_compiler(self.root, compiler, stage0)
        (self.root / "build").unlink()
        outside = self.root.parent / (self.root.name + "-outside")
        outside.mkdir()
        self.addCleanup(outside.rmdir)
        (self.root / "build").symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(identity.SeedIdentityError, "sanctioned"):
            identity.authenticate_compiler(self.root, compiler, stage0)
        (self.root / "build").unlink()
        (self.root / "build").symlink_to("build.noindex", target_is_directory=True)
        host = physical / "test-host"
        moved = physical / "real-host"
        host.rename(moved)
        host.symlink_to("real-host", target_is_directory=True)
        with self.assertRaisesRegex(identity.SeedIdentityError, "symlink or wrong-type"):
            identity.authenticate_compiler(self.root, compiler, stage0)

    def test_wrong_archive_hash_or_extracted_member_refuses(self):
        compiler, archive, stage0 = archive_fixture(self.root)
        stage0[next(k for k in stage0 if k.startswith("dist/"))] = "0" * 64
        with self.assertRaisesRegex(identity.SeedIdentityError, "SHA-256"):
            identity.authenticate_compiler(self.root, compiler, stage0)
        stage0[next(k for k in stage0 if k.startswith("dist/"))] = hashlib.sha256(
            archive.read_bytes()
        ).hexdigest()
        compiler.write_bytes(b"another launcher")
        with self.assertRaisesRegex(
            identity.SeedIdentityError, "pinned archive member"
        ):
            identity.authenticate_compiler(self.root, compiler, stage0)

    def test_missing_duplicate_or_link_members_refuse(self):
        member = "trustc-1.99.0-trust-test-host/trustc/bin/trustc"
        for label, members in [
            ("missing", [("other", b"x", tarfile.REGTYPE)]),
            ("duplicate", [(member, b"x", tarfile.REGTYPE)] * 2),
            ("link", [(member, b"", tarfile.SYMTYPE)]),
        ]:
            with self.subTest(label=label):
                child = self.root / label
                child.mkdir()
                compiler, _, stage0 = archive_fixture(child, b"x", members=members)
                with self.assertRaisesRegex(identity.SeedIdentityError, "one regular"):
                    identity.authenticate_compiler(child, compiler, stage0)

    def test_compiler_or_archive_alias_and_nonexecutable_refuse(self):
        compiler, archive, stage0 = archive_fixture(self.root)
        payload = compiler.read_bytes()
        compiler.unlink()
        target = compiler.with_name("alias-target")
        target.write_bytes(payload)
        target.chmod(0o755)
        compiler.symlink_to(target)
        with self.assertRaises(identity.SeedIdentityError):
            identity.authenticate_compiler(self.root, compiler, stage0)
        compiler.unlink()
        compiler.write_bytes(payload)
        compiler.chmod(0o644)
        with self.assertRaises(identity.SeedIdentityError):
            identity.authenticate_compiler(self.root, compiler, stage0)
        compiler.chmod(0o755)
        moved = archive.with_suffix(".original")
        archive.rename(moved)
        archive.symlink_to(moved)
        with self.assertRaises(identity.SeedIdentityError):
            identity.authenticate_compiler(self.root, compiler, stage0)

    def test_changed_or_lost_compiler_cannot_reuse_snapshot(self):
        compiler, _, stage0 = archive_fixture(self.root)
        bound = identity.authenticate_compiler(self.root, compiler, stage0)
        compiler.write_bytes(b"changed")
        with self.assertRaises(identity.SeedIdentityError):
            identity.check_compiler_snapshot(compiler, bound)
        compiler.unlink()
        with self.assertRaises(identity.SeedIdentityError):
            identity.check_compiler_snapshot(compiler, bound)

    def test_nonapplicable_is_distinct_from_applicable_pin_failure(self):
        self.assertIsNone(
            identity.pinned_compiler_binding(
                self.root, self.root / "stock/rustc", timeout=10
            )
        )
        compiler, _, _ = archive_fixture(self.root)
        (self.root / "src/stage0").write_text(
            "compiler_date=2026-07-13\ncompiler_version=1.99.0-trust\n"
        )
        with self.assertRaises(identity.SeedIdentityError):
            identity.pinned_compiler_binding(self.root, compiler, timeout=10)

    def test_deadline_and_malformed_record_refuse_without_query(self):
        compiler, _, stage0 = archive_fixture(self.root)
        with self.assertRaises(subprocess.TimeoutExpired):
            identity.authenticate_compiler(
                self.root, compiler, stage0, deadline=time.monotonic() - 1
            )
        (self.root / "src/stage0").write_text("duplicate=x\nduplicate=y\n")
        with self.assertRaises(identity.SeedIdentityError):
            identity.pinned_compiler_binding(self.root, compiler, timeout=10)

    def test_deadline_reaches_selected_executable_after_real_archive_parsing(self):
        compiler, archive, stage0 = archive_fixture(self.root)
        real_open = identity._open_regular
        observed = []

        def open_input(path):
            observed.append(path)
            return real_open(path)

        # Both archive hashing and the actual tar member are parsed while the
        # clock is zero. It expires only when the selected executable opens.
        with mock.patch.object(
            identity, "_open_regular", side_effect=open_input
        ), mock.patch.object(
            identity.time,
            "monotonic",
            side_effect=lambda: 2 if compiler in observed else 0,
        ):
            with self.assertRaises(subprocess.TimeoutExpired):
                identity.authenticate_compiler(self.root, compiler, stage0, deadline=1)
        self.assertEqual(observed, [archive, compiler])


class CompilerCallerIdentityTests(unittest.TestCase):
    def probe(
        self,
        *,
        commit=PIN,
        mutation="pass",
        production=None,
        archive_change=None,
        owner_error=None,
        host_alias=False,
        materialized=False,
    ):
        tmp = tempfile.TemporaryDirectory(prefix="compiler caller ü ")
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        payload = SEED.format(
            commit=commit,
            mutation=mutation,
            production=production
            or "pathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'rmeta')",
        ).encode()
        compiler, archive, stage0 = archive_fixture(root, payload)
        if archive_change is not None:
            archive_change(compiler, archive, stage0)
        if host_alias:
            alias = root / "build/host"
            alias.symlink_to(compiler.parents[2], target_is_directory=True)
            compiler = alias / "stage0/bin/rustc"
        bridge = root / "unit fixture bridge"
        bridge.write_text('#!/bin/sh\nshift\nexec "$@"\n')
        bridge.chmod(0o700)
        ledger = root / "ledger"
        with mock.patch.object(freshness, "ROOT", root), mock.patch.dict(
            os.environ, {"IDENTITY_FIXTURE_LEDGER": str(ledger)}
        ), mock.patch.object(
            freshness.native_serial,
            "managed_serial_executor",
            return_value=bridge,
            side_effect=owner_error,
        ) as owner:
            result = (
                freshness.probe_materialized_stage0(stage0)
                if materialized
                else freshness.probe_seed_binary(compiler, "fake archive fixture", stage0)
            )
        return (
            result,
            ledger.read_text().splitlines() if ledger.exists() else [],
            owner.call_count,
        )

    def test_real_member_guard_then_exact_fake_producing_query(self):
        (errors, notes), events, owners = self.probe()
        self.assertEqual(errors, [])
        self.assertTrue(notes)
        self.assertEqual((events, owners), (["identity", "produce"], 1))

    def test_generated_host_alias_reaches_the_exact_producing_query(self):
        (errors, notes), events, owners = self.probe(host_alias=True)
        self.assertEqual(errors, [])
        self.assertTrue(notes)
        self.assertEqual((events, owners), (["identity", "produce"], 1))

    def test_host_alias_replaced_after_banner_never_reaches_producing(self):
        (errors, notes), events, owners = self.probe(
            host_alias=True,
            mutation="alias=pathlib.Path(sys.argv[0]).parents[2]; alias.unlink(); alias.symlink_to('test-host', target_is_directory=True)",
        )
        self.assertTrue(any("path changed" in error for error in errors), errors)
        self.assertEqual((events, owners, notes), (["identity"], 0, []))
    def test_materialized_census_probes_concrete_seed_once_beside_bootstrap_host_alias(self):
        def alias(compiler, _archive, stage0):
            (compiler.parent.parent / ".rustc-stamp").write_text(
                freshness.stage0_extraction_stamp(stage0)
            )
            # This is Bootstrap Session's real layout. The fake executable and
            # native-transport stub remain unit fixtures, never a real SDK.
            (compiler.parents[3] / "host").symlink_to(
                compiler.parents[2], target_is_directory=True
            )

        (errors, notes), events, owners = self.probe(
            archive_change=alias, materialized=True
        )
        self.assertEqual(errors, [])
        self.assertEqual(sum("identity matches the pin" in note for note in notes), 1)
        self.assertEqual((events, owners), (["identity", "produce"], 1))

    def test_materialized_census_still_refuses_concrete_target_symlink(self):
        def replace(compiler, _archive, stage0):
            (compiler.parent.parent / ".rustc-stamp").write_text(
                freshness.stage0_extraction_stamp(stage0)
            )
            target = compiler.parents[2]
            moved = target.with_name("other-target")
            target.rename(moved)
            target.symlink_to(moved, target_is_directory=True)

        (errors, _notes), events, owners = self.probe(
            archive_change=replace, materialized=True
        )
        self.assertTrue(any("symlink or wrong-type seed component" in error for error in errors))
        self.assertEqual((events, owners), ([], 0))

    def test_bootstrap_host_alias_never_launders_changed_concrete_seed(self):
        def replace(compiler, _archive, stage0):
            (compiler.parent.parent / ".rustc-stamp").write_text(
                freshness.stage0_extraction_stamp(stage0)
            )
            (compiler.parents[3] / "host").symlink_to(
                compiler.parents[2], target_is_directory=True
            )
            compiler.write_bytes(b"not the original archive member")

        (errors, _notes), events, owners = self.probe(
            archive_change=replace, materialized=True
        )
        self.assertTrue(any("pinned archive member" in error for error in errors))
        self.assertEqual((events, owners), ([], 0))

    def test_banner_mismatch_stops_before_owner_or_producing(self):
        (errors, notes), events, owners = self.probe(commit="2" * 40)
        self.assertTrue(any("commit-hash" in e for e in errors))
        self.assertEqual((events, owners, notes), (["identity"], 0, []))

    def test_wrong_archive_stops_before_any_compiler_or_owner(self):
        def corrupt_pin(_compiler, _archive, stage0):
            stage0[next(k for k in stage0 if k.startswith("dist/"))] = "0" * 64

        (errors, notes), events, owners = self.probe(archive_change=corrupt_pin)
        self.assertTrue(any("SHA-256" in error for error in errors))
        self.assertEqual((events, owners, notes), ([], 0, []))

    def test_native_admission_refusal_has_no_direct_producing_fallback(self):
        (errors, notes), events, owners = self.probe(
            owner_error=RuntimeError("fixture admission refused")
        )
        self.assertEqual(len(errors), 1)
        self.assertIsInstance(errors[0], freshness.ProbeUnavailable)
        self.assertEqual((events, owners, notes), (["identity"], 1, []))

    def test_mutation_after_banner_and_after_producing_refuses(self):
        for mutation, production in [
            ("pathlib.Path(sys.argv[0]).write_bytes(b'changed')", None),
            (
                "pass",
                "pathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'rmeta'); pathlib.Path(sys.argv[0]).write_bytes(b'changed')",
            ),
        ]:
            with self.subTest(mutation=mutation):
                (errors, notes), _, _ = self.probe(
                    mutation=mutation, production=production
                )
                self.assertTrue(any("changed" in e for e in errors))
                self.assertEqual(notes, [])

    def test_empty_missing_or_symlink_metadata_is_not_a_success(self):
        for production in [
            "pass",
            "pathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'')",
            "out=pathlib.Path(sys.argv[sys.argv.index('-o')+1]); target=out.with_name('other'); target.write_bytes(b'rmeta'); out.symlink_to(target)",
        ]:
            with self.subTest(production=production):
                (errors, notes), _, _ = self.probe(production=production)
                self.assertTrue(errors)
                self.assertEqual(notes, [])

    def test_raw_status75_is_unavailable_without_fallback(self):
        (errors, notes), events, owners = self.probe(production="raise SystemExit(75)")
        self.assertEqual(len(errors), 1)
        self.assertIsInstance(errors[0], freshness.ProbeUnavailable)
        self.assertEqual((events, owners, notes), (["identity", "produce"], 1, []))


if __name__ == "__main__":
    unittest.main()
