#!/usr/bin/env python3
"""An archive-only history rewrite cannot silently replace a declared Git pin."""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "fabric_manifest_alignment", ROOT / "scripts/check_cargo_manifest_alignment.py"
)
POLICY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(POLICY)
URL = "https://github.com/alabsystems/trust-ir.git"


class TemporalFabricSourceIdentity(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fabric-source-identity-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.source = self.root / "source"
        self.source.mkdir()
        self.environment = {key: value for key, value in os.environ.items()
                            if not key.startswith("GIT_")}
        self.environment.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                                GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1")
        self.git("init", "-q", "--template=")
        self.code = b"pub fn original() -> bool { true }\n"
        self.manifest = b'[package]\nname="trust-ir"\nversion="0.14.0"\n'
        (self.source / "Cargo.toml").write_bytes(self.manifest)
        (self.source / "src").mkdir()
        (self.source / "src/lib.rs").write_bytes(self.code)
        (self.source / "reports").mkdir()
        (self.source / "reports/archive.tar").write_bytes(b"historical report data\n")
        self.git("add", ".")
        self.git("commit", "-qm", "original source and report")
        self.original = self.git("rev-parse", "HEAD")
        self.git("rm", "-q", "reports/archive.tar")
        self.git("commit", "-qm", "retire the report payload")
        self.replacement = self.git("rev-parse", "HEAD")
        self.assertNotEqual(self.git("rev-parse", self.original + "^{tree}"),
                            self.git("rev-parse", self.replacement + "^{tree}"))
        for name in ("Cargo.toml", "src/lib.rs"):
            self.assertEqual(self.git("rev-parse", self.original + ":" + name),
                             self.git("rev-parse", self.replacement + ":" + name))

        (self.root / "Cargo.toml").write_text(
            '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
            'trust-ir={git="' + URL + '",rev="' + self.original + '"}\n'
        )
        temporal = self.root / "crates/trust-spec-temporal/Cargo.toml"
        temporal.parent.mkdir(parents=True)
        temporal.write_text('[package]\nname="trust-spec-temporal"\nversion="0.1.0"\n'
                            '[dependencies]\ntrust-ir={workspace=true,optional=true}\n')
        fixture = self.root / "targo-trust/tests/fixtures/fabric/Cargo.toml"
        fixture.parent.mkdir(parents=True)
        fixture.write_text('[package]\nname="fabric"\nversion="0.0.0"\n'
                           '[workspace]\n[dependencies]\n'
                           'trust-spec-temporal={path="../../../../crates/trust-spec-temporal"}\n')
        for name, value in (("REPO_ROOT", self.root),
                            ("TEMPORAL_MANIFEST", temporal),
                            ("TEMPORAL_FABRIC_MANIFEST", fixture)):
            context = patch.object(POLICY, name, value)
            context.start()
            self.addCleanup(context.stop)

    def git(self, *arguments):
        return subprocess.check_output(
            ["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
             "-c", "maintenance.auto=false", "-C", str(self.source), *arguments],
            env=self.environment, text=True,
        ).strip()

    def lock(self, requested, resolved):
        return ('version = 4\n[[package]]\nname="trust-ir"\nversion="0.14.0"\n'
                'source = "git+' + URL + '?rev=' + requested + '#' + resolved + '"\n')

    def test_original_declared_identity_and_unpatched_boundary_remain_accepted(self):
        self.assertEqual(POLICY.check_temporal_fabric_boundary(
            POLICY.load_manifest(POLICY.TEMPORAL_FABRIC_MANIFEST)), [])
        self.assertEqual(POLICY.check_temporal_fabric_lock_source_revs(
            self.lock(self.original, self.original)), [])

    def test_equal_code_after_report_retirement_does_not_authorize_a_lock_only_repin(self):
        errors = POLICY.check_temporal_fabric_lock_source_revs(
            self.lock(self.replacement, self.replacement))
        self.assertTrue(any("not declared by its reachable manifest closure" in error
                            for error in errors), errors)

    def test_a_real_manifest_pin_move_requires_the_matching_lock_source(self):
        # Unlike a lock-only archive substitution, a new literal declaration
        # makes the previous lock identity stale. No revision exemption is used.
        root = self.root / "Cargo.toml"
        root.write_text(root.read_text().replace(self.original, self.replacement))
        errors = POLICY.check_temporal_fabric_lock_source_revs(
            self.lock(self.original, self.original))
        self.assertTrue(any("not declared by its reachable manifest closure" in error
                            for error in errors), errors)
        self.assertEqual(POLICY.check_temporal_fabric_lock_source_revs(
            self.lock(self.replacement, self.replacement)), [])

    def test_declared_request_cannot_hide_a_different_resolved_commit(self):
        errors = POLICY.check_temporal_fabric_lock_source_revs(
            self.lock(self.original, self.replacement))
        self.assertTrue(any("resolved commit does not match its requested rev" in error
                            for error in errors), errors)


if __name__ == "__main__":
    unittest.main()
