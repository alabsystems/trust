#!/usr/bin/env python3
"""Git-object regressions for immutable evidence versus live pin consumers."""

import contextlib
import hashlib
import io
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import unicodedata
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "check_first_party_pin_lattice.py"
SPEC = importlib.util.spec_from_file_location("sealed_pin_lattice", SCRIPT)
lattice = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = lattice
SPEC.loader.exec_module(lattice)


class SealedSourceSnapshotTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="sealed source pins ")
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.ir, self.root = self.base / "ir", self.base / "root"
        self.env = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                        GIT_AUTHOR_NAME="Fixture", GIT_AUTHOR_EMAIL="fixture@example.invalid",
                        GIT_COMMITTER_NAME="Fixture", GIT_COMMITTER_EMAIL="fixture@example.invalid")
        for repo in (self.ir, self.root):
            self.git(self.base, "init", "-q", str(repo))
        self.packet = "reports/snapshot"
        self.manifest = "crates/trust-ir-build/Cargo.toml"
        self.old = "0" * 40
        self.new = "1" * 40
        self.write(self.ir, "Cargo.toml", '[workspace]\nmembers=["crates/trust-ir-build"]\n')
        self.write(self.ir, self.manifest,
                   '[package]\nname="trust-ir-build"\nversion="0.14.0"\n[dependencies]\n'
                   'clean-kernel={git="https://github.com/alabsystems/clean.git",rev="' + self.old + '"}\n')
        self.write(self.ir, "Cargo.lock", 'version=4\n[[package]]\nname="clean-kernel"\nversion="0.9.0"\n'
                   'source="git+https://github.com/alabsystems/clean.git?rev=' + self.old + '#' + self.old + '"\n')
        self.subject = self.commit(self.ir)
        payload = {"source/" + p: (self.ir / p).read_bytes()
                   for p in ("Cargo.toml", "Cargo.lock", self.manifest)}
        payload["handoff.json"] = json.dumps({"code": self.subject}).encode()
        rows = []
        for path, body in payload.items():
            self.write(self.ir, self.packet + "/" + path, body)
            rows.append({"path": path, "bytes": len(body), "mode": 0o644,
                         "sha256": hashlib.sha256(body).hexdigest()})
        seal = json.dumps({"schema": "compact-handoff-v2", "subject": self.subject,
                           "files": rows, "payload_count": len(rows),
                           "payload_bytes": sum(len(v) for v in payload.values())}, sort_keys=True)
        self.write(self.ir, self.packet + "/artifact-manifest.json", seal)
        self.rev = self.commit(self.ir)
        self.write(self.root, "Cargo.toml", "[workspace]\nmembers=[]\n")
        self.root_rev = self.commit(self.root)
        self.snapshot = lattice.SealedSourceSnapshot(
            lattice.TRUST_IR, self.packet, self.subject, hashlib.sha256(seal.encode()).hexdigest(),
            ("source/Cargo.lock", "source/" + self.manifest))
        self.ir_store = lattice.Store(lattice.TRUST_IR, [self.ir / ".git"])
        self.root_store = lattice.Store("trust", [self.root / ".git"])
        self.addCleanup(self.close_stores)

    def close_stores(self):
        for store in (self.ir_store, self.root_store):
            for batch in store._batches.values():
                batch.close()

    def git(self, repo, *args):
        result = subprocess.run(["git", "-C", str(repo), *args], env=self.env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout.strip()

    def write(self, repo, name, content):
        path = repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content.encode() if isinstance(content, str) else content)

    def commit(self, repo):
        self.git(repo, "add", "-A")
        self.git(repo, "commit", "-qm", "fixture")
        return self.git(repo, "rev-parse", "HEAD")

    def judge(self, path=None):
        path = path or self.packet + "/source/" + self.manifest
        report = lattice.Report()
        report.archive_root = self.root
        report.archive_scope = [("", self.root_rev, self.root_store),
                                ("first-party/trust-ir", self.rev, self.ir_store)]
        holder = lattice.Holder(lattice.TRUST_IR, self.rev, self.ir_store)
        with mock.patch.object(lattice, "SEALED_SOURCE_SNAPSHOTS", (self.snapshot,)):
            lattice.judge_file(holder, path, "lock" if path.endswith(".lock") else "manifest",
                               lattice.CLEAN, self.new, "L3", "fix current source", report)
        return report

    def assertArchiveRefusal(self):
        report = self.judge()
        self.assertTrue(report.violations)
        self.assertIn("LATTICE-ARCHIVE", "\n".join(report.violations))

    def test_pushed_root_adoption_is_rejudged_with_unchanged_child_gitlinks(self):
        for path in lattice.GITLINKS.values():
            self.git(self.root, "update-index", "--add", "--cacheinfo", "160000," + self.subject + "," + path)
        self.git(self.root, "commit", "-qm", "identical selected child pins")
        good = self.git(self.root, "rev-parse", "HEAD")
        target = "first-party/trust-ir/" + self.packet + "/source/crates/trust-ir-build"
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="' + target + '"}\n')
        self.git(self.root, "add", "Cargo.toml")
        self.git(self.root, "commit", "-qm", "activate archive without moving child pins")
        bad = self.git(self.root, "rev-parse", "HEAD")
        def committed_archive_check(_root, rev, _overrides):
            # Production creates fresh stores per root subject and reaps their
            # cat-file processes after each. Match that lifetime in the seam.
            self.ir_store = lattice.Store(lattice.TRUST_IR, [self.ir / ".git"])
            self.root_store = lattice.Store("trust", [self.root / ".git"])
            self.root_rev = rev
            return self.judge()
        output = io.StringIO()
        with mock.patch.object(lattice, "check", side_effect=committed_archive_check) as checked, contextlib.redirect_stdout(output):
            result = lattice.judge_pushed(self.root, [("refs/heads/good", good), ("refs/heads/bad", bad)], {})
        self.assertEqual(result, 1, output.getvalue())
        self.assertEqual(checked.call_count, 2)
        self.assertIn("activates archived source", output.getvalue())
        self.assertNotIn("PIN LATTICE OK", output.getvalue())

    def test_exact_seal_and_original_git_endpoints_are_historical_data(self):
        for endpoint in self.snapshot.endpoints:
            report = self.judge(self.packet + "/" + endpoint)
            self.assertEqual(report.violations, [])
            self.assertTrue(any("SEALED HISTORICAL SOURCE" in n for n in report.notes))

    def test_altered_snapshot_cannot_hide_by_using_the_current_pin(self):
        path = self.ir / self.packet / "source" / self.manifest
        path.write_text(path.read_text().replace(self.old, self.new))
        self.rev = self.commit(self.ir)
        self.assertArchiveRefusal()

    def test_absent_or_changed_outer_seal_refuses(self):
        path = self.ir / self.packet / "artifact-manifest.json"
        original = path.read_bytes()
        for changed in (None, original + b"\n"):
            if changed is None:
                path.unlink()
            else:
                path.write_bytes(changed)
            self.rev = self.commit(self.ir)
            self.assertArchiveRefusal()

    def test_unsealed_neighbor_voids_the_exact_packet(self):
        self.write(self.ir, self.packet + "/source/neighbor/Cargo.toml", "[package]\nname='extra'\n")
        self.rev = self.commit(self.ir)
        self.assertArchiveRefusal()

    def test_neighboring_copy_and_current_operational_manifest_never_exempt(self):
        for path in ("reports/neighbor/source/Cargo.toml", self.manifest):
            self.write(self.ir, path, (self.ir / self.manifest).read_bytes())
            self.rev = self.commit(self.ir) if path != self.manifest else self.rev
            report = self.judge(path)
            self.assertTrue(any("LATTICE-L3" in v for v in report.violations))

    def test_root_path_dependency_activates_archive_even_if_workspace_excludes_it(self):
        path = "first-party/trust-ir/" + self.packet + "/source/crates/trust-ir-build"
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\nexclude=["' + path + '"]\n'
                   '[workspace.dependencies]\narchived={path="' + path + '"}\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()

    def test_holder_path_dependency_activates_archive(self):
        self.write(self.ir, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="' + self.packet + '/source/crates/trust-ir-build"}\n')
        self.rev = self.commit(self.ir)
        self.assertArchiveRefusal()

    def test_absolute_dotdot_path_activates_archive(self):
        path = str(self.root) + "/first-party/clean/../trust-ir/" + self.packet + "/source/crates/trust-ir-build"
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="' + path + '"}\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()

    def test_committed_symlink_alias_activates_archive(self):
        target = "first-party/trust-ir/" + self.packet + "/source/crates/trust-ir-build"
        (self.root / "archive-alias").symlink_to(target)
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="archive-alias"}\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()

    def test_link_parent_traversal_uses_git_target_before_dotdot(self):
        target = "first-party/trust-ir/" + self.packet + "/source/crates"
        (self.root / "archive-alias").symlink_to(target)
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="archive-alias/../crates/trust-ir-build"}\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()

    def test_workspace_glob_through_committed_alias_activates_archive(self):
        target = "first-party/trust-ir/" + self.packet + "/source/crates/trust-ir-build"
        (self.root / "archive-alias").symlink_to(target)
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=["archive-*"]\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()

    def test_symlink_cycle_is_not_an_inactivity_proof(self):
        (self.root / "loop-a").symlink_to("loop-b")
        (self.root / "loop-b").symlink_to("loop-a")
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="loop-a"}\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()

    def test_recursive_workspace_glob_cannot_hide_a_deep_alias(self):
        (self.root / "archive-parent").symlink_to("first-party/trust-ir")
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=["archive-*/**"]\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()

    def test_case_alias_is_conservatively_treated_as_activation(self):
        path = "FIRST-PARTY/TRUST-IR/" + self.packet.upper() + "/SOURCE/CRATES/TRUST-IR-BUILD"
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="' + path + '"}\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()

    def test_distinct_git_links_colliding_under_casefold_cannot_hide_activation(self):
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="Archive-Alias"}\n')
        self.root_rev = self.commit(self.root)
        for name, target in [("Archive-Alias", "first-party/trust-ir/" + self.packet + "/source"),
                             ("archive-alias", "not-the-archive")]:
            payload = self.base / "link-target"
            payload.write_text(target)
            blob = self.git(self.root, "hash-object", "-w", str(payload))
            self.git(self.root, "update-index", "--add", "--cacheinfo", "120000," + blob + "," + name)
        self.git(self.root, "commit", "-qm", "case-distinct committed links")
        self.root_rev = self.git(self.root, "rev-parse", "HEAD")
        self.assertArchiveRefusal()

    def test_casefold_link_cannot_redirect_a_distinct_committed_directory(self):
        self.write(self.root, "Real/data", "committed directory")
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="Real"}\n')
        self.root_rev = self.commit(self.root)
        payload = self.base / "link-target"
        payload.write_text("not-the-archive")
        blob = self.git(self.root, "hash-object", "-w", str(payload))
        self.git(self.root, "update-index", "--add", "--cacheinfo", "120000," + blob + ",real")
        self.git(self.root, "commit", "-qm", "link differs from directory only by case")
        self.root_rev = self.git(self.root, "rev-parse", "HEAD")
        self.assertArchiveRefusal()

    def test_unicode_normalization_alias_cannot_hide_activation(self):
        target = "first-party/trust-ir/" + self.packet + "/source/crates/trust-ir-build"
        (self.root / "archive-\u00e9").symlink_to(target)
        decomposed = "archive-e\u0301"
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="' + decomposed + '"}\n')
        self.root_rev = self.commit(self.root)
        if sys.platform == "darwin":
            self.assertEqual((self.root / "archive-\u00e9").lstat().st_ino,
                             (self.root / decomposed).lstat().st_ino)
        self.assertArchiveRefusal()

    def test_absolute_decomposed_root_uses_normalized_prefix_offsets(self):
        renamed = self.base / "r\u00e9po"
        self.root.rename(renamed)
        self.root = renamed
        self.root_store = lattice.Store("trust", [self.root / ".git"])
        target = unicodedata.normalize("NFD", str(self.root)) + "/first-party/trust-ir/" + self.packet + "/source/crates/trust-ir-build"
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=[]\n[workspace.dependencies]\n'
                   'archived={path="' + target + '"}\n')
        self.root_rev = self.commit(self.root)
        if sys.platform == "darwin":
            self.assertEqual(self.root.stat().st_ino, Path(unicodedata.normalize("NFD", str(self.root))).stat().st_ino)
        self.assertArchiveRefusal()

    def test_explicit_workspace_owner_cannot_activate_archive(self):
        path = "first-party/trust-ir/" + self.packet + "/source"
        self.write(self.root, "Cargo.toml", '[package]\nname="live"\nversion="0.1.0"\nworkspace="' + path + '"\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()

    def test_workspace_glob_activation_and_explicit_exclusion(self):
        pattern = "first-party/trust-ir/reports/*/source"
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=["' + pattern + '"]\n')
        self.root_rev = self.commit(self.root)
        self.assertArchiveRefusal()
        self.write(self.root, "Cargo.toml", '[workspace]\nmembers=["' + pattern + '"]\n'
                   'exclude=["first-party/trust-ir/' + self.packet + '/source"]\n')
        self.root_rev = self.commit(self.root)
        self.assertEqual(self.judge().violations, [])


if __name__ == "__main__":
    unittest.main()
