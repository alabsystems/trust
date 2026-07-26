#!/usr/bin/env python3
"""Focused tests for durable end-to-end receipt publication and binding."""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parents[2]
MODULE_PATH = REPO_ROOT / "scripts" / "lib" / "trust_e2e_receipt.py"
SPEC = importlib.util.spec_from_file_location("trust_e2e_receipt", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
receipt = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(receipt)


class AtomicReceiptTests(unittest.TestCase):
    def passing_document(self) -> dict[str, object]:
        digest = "0" * 64
        doctor_report = {
            "ready": True,
            "status": "ready",
            "compiler": {"check_report_mode": "native_compiler"},
        }
        runtime_output = {
            "sender": "Sanny",
            "body": "Trust installed-toolchain fixture",
            "priority": 2,
        }
        return {
            "schema": "trust.e2e.installed-toolchain-receipt.v1",
            "status": "passed",
            "source": {
                "repository_head": "a" * 40,
                "repository_clean_before_and_after": True,
                "inputs_stable_before_and_after": True,
                "gate_script_sha256": digest,
                "receipt_helper_sha256": digest,
            },
            "stage_provenance": {
                "schema": "trust.stage-tool-provenance.v2",
                "status": "internal-release-ready",
                "stage": 2,
                "sha256": digest,
                "source_commit": "a" * 40,
                "verified_before_and_after": True,
            },
            "sysroots": {
                "source": {
                    "manifest_schema": "trust.filesystem-content-manifest.ndjson.v1",
                    "manifest_scope": (
                        "entry-kind-mode-symlink-target-file-bytes;"
                        "excludes-owner-xattrs-flags-hardlink-topology"
                    ),
                    "manifest_sha256": digest,
                    "stable_before_and_after": True,
                    "copy_content_manifest_schema": (
                        "trust.filesystem-content-manifest.ndjson.v1"
                    ),
                    "copy_content_manifest_scope": (
                        "entry-kind-symlink-target-file-bytes;"
                        "excludes-mode-owner-xattrs-flags-hardlink-topology"
                    ),
                    "copy_content_manifest_sha256": digest,
                    "copied_sysroot_content_manifest_sha256": digest,
                    "copied_sysroot_matches_source_content_manifest": True,
                    "materialized_link_inputs_manifest_schema": (
                        "trust.materialized-source-input-manifest.ndjson.v1"
                    ),
                    "materialized_link_inputs_manifest_scope": (
                        "entry-kind-symlink-target-file-bytes;"
                        "excludes-mode-owner-xattrs-flags-hardlink-topology"
                    ),
                    "materialized_link_inputs_manifest_sha256": digest,
                    "materialized_link_inputs_stable_before_and_after": True,
                    "materialized_link_input_content_copied_exactly": True,
                    "materialized_link_input_files_git_tracked_only": True,
                },
                "installed": {
                    "manifest_schema": "trust.filesystem-content-manifest.ndjson.v1",
                    "manifest_scope": (
                        "entry-kind-mode-symlink-target-file-bytes;"
                        "excludes-owner-xattrs-flags-hardlink-topology"
                    ),
                    "manifest_sha256": digest,
                    "read_only": True,
                    "no_escaping_symlinks": True,
                    "no_source_hardlinks": True,
                    "unchanged_after_behavior_checks": True,
                },
            },
            "compiler": {
                "sha256": digest,
                "source_sha256": digest,
                "provenance_digest_match": True,
            },
            "doctor": {
                "report_sha256": receipt.canonical_embedded_json_sha256(doctor_report),
                "report": doctor_report,
                "ready": True,
                "daily_driver_ready": True,
                "required_verifier_suites": ["trust-mc", "trust-wp", "trust-vc"],
            },
            "serde_fixture": {
                "tree_manifest_sha256": digest,
                "cargo_lock_sha256": digest,
                "runtime_output_sha256": receipt.canonical_embedded_json_sha256(
                    runtime_output
                ),
                "runtime_output": runtime_output,
                "native_proc_macro_lane": "explicitly-unverified",
                "verified_proc_macro_boundary": "rejected-fail-closed",
            },
            "checks": {name: "passed" for name in receipt._INSTALLED_CHECKS},
            "claim_scope": {
                "kind": "local-installed-toolchain-rehearsal",
                "public_rustup_channel": False,
                "notarized_macos_application": False,
                "ecosystem_superiority": False,
            },
            "evidence": {"value": 1},
        }

    def dist_document(self) -> dict[str, object]:
        digest = "0" * 64
        host = "aarch64-apple-darwin"
        version = "1.99.0-trust"
        dist_directory = "/var/empty/trust-dist-fixture"
        child = self.passing_document()
        child.pop("evidence")
        child_sha256 = hashlib.sha256(receipt._serialized_receipt(child)).hexdigest()
        archives = []
        for component in sorted(receipt.REQUIRED_ARCHIVE_COMPONENTS):
            archive_root = (
                f"{component}-{version}"
                if component == "trust-src"
                else f"{component}-{version}-{host}"
            )
            archive_filename = f"{archive_root}.tar.xz"
            archives.append(
                {
                    "component": component,
                    "archive_path": f"{dist_directory}/{archive_filename}",
                    "archive_filename": archive_filename,
                    "size_bytes": 1,
                    "extension": "tar.xz",
                    "archive_root": archive_root,
                    "sha256": digest,
                    "selected": True,
                }
            )
        archive_manifest_sha256 = hashlib.sha256(
            "".join(
                json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
                for row in archives
            ).encode()
        ).hexdigest()
        return {
            "schema": "trust.e2e.dist-artifact-receipt.v1",
            "status": "passed",
            "source": copy.deepcopy(child["source"]),
            "stage_provenance": copy.deepcopy(child["stage_provenance"]),
            "compiler": {
                "trustc_sha256": digest,
                "identity_matches_installed_archives": True,
            },
            "distribution": {
                "directory": dist_directory,
                "host": host,
                "version": version,
                "archive_manifest_schema": "trust.dist-archive-manifest.ndjson.v1",
                "archive_manifest_sha256": archive_manifest_sha256,
                "archives": archives,
                "archives_rehashed_after_install": True,
                "umbrella_trust_archive_required": True,
            },
            "channel_manifest": {
                "path": "/var/empty/channel-rust-trust.toml",
                "sha256": digest,
                "manifest_version": "2",
                "host": host,
                "archive_rows_validated": len(archives),
                "targo_trust_available": True,
                "umbrella_targo_trust_extension": True,
                "hosting_claim": "none-local-rehearsal-only",
                "required_archive_components": sorted(receipt.REQUIRED_ARCHIVE_COMPONENTS),
                "default_profile": sorted(receipt.REQUIRED_DEFAULT_PROFILE),
            },
            "installed_toolchain_gate": {
                "receipt_sha256": child_sha256,
                "receipt": child,
                "exact_document_embedded": True,
            },
            "checks": {name: "passed" for name in receipt._DIST_CHECKS},
            "claim_scope": {
                "kind": "local-pre-publication-dist-rehearsal",
                "public_download_channel": False,
                "hosted_urls_exercised": False,
                "signatures_or_notarization": False,
                "multi_host_availability": False,
            },
        }

    def test_atomic_publish_replaces_regular_file(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary).resolve() / "evidence" / "receipt.json"
            receipt.write_receipt(output, self.passing_document())
            parsed = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(parsed["status"], "passed")
            self.assertEqual(output.stat().st_mode & 0o777, 0o644)
            self.assertEqual(list(output.parent.glob(f".{output.name}.*.tmp")), [])

            replacement = self.passing_document()
            replacement["evidence"] = {"value": 2}
            receipt.write_receipt(output, replacement)
            self.assertEqual(json.loads(output.read_text())["evidence"]["value"], 2)

    def test_no_replace_publish_refuses_existing_file_and_racing_creator(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            existing = root / "existing.json"
            existing.write_text("do not overwrite\n", encoding="utf-8")
            with self.assertRaisesRegex(receipt.ReceiptError, "refusing to overwrite"):
                receipt.write_receipt(
                    existing,
                    self.passing_document(),
                    replace_existing=False,
                )
            self.assertEqual(existing.read_text(encoding="utf-8"), "do not overwrite\n")

            output = root / "raced.json"
            real_create = receipt._create_unique_temporary

            def create_then_race(directory_fd: int, filename: str) -> tuple[str, int]:
                temporary_name, descriptor = real_create(directory_fd, filename)
                output.write_text("racer wins creation\n", encoding="utf-8")
                return temporary_name, descriptor

            with mock.patch.object(
                receipt,
                "_create_unique_temporary",
                side_effect=create_then_race,
            ), self.assertRaisesRegex(receipt.ReceiptError, "refusing to overwrite"):
                receipt.write_receipt(
                    output,
                    self.passing_document(),
                    replace_existing=False,
                )
            self.assertEqual(output.read_text(encoding="utf-8"), "racer wins creation\n")
            self.assertEqual(list(root.glob(".raced.json.*.tmp")), [])

            fresh = root / "fresh.json"
            receipt.write_receipt(
                fresh,
                self.passing_document(),
                replace_existing=False,
            )
            self.assertEqual(json.loads(fresh.read_text())["status"], "passed")

    def test_prepare_new_destination_anchors_cwd_and_rejects_ambiguity(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            caller = root / "caller"
            caller.mkdir()
            expected = caller / "nested" / "receipt.json"
            self.assertEqual(
                receipt.prepare_new_receipt_destination(
                    Path("nested/../nested/receipt.json"),
                    caller_directory=caller,
                ),
                expected,
            )

            existing = caller / "existing.json"
            existing.write_text("preserve\n", encoding="utf-8")
            with self.assertRaisesRegex(receipt.ReceiptError, "already exists"):
                receipt.prepare_new_receipt_destination(
                    Path("existing.json"),
                    caller_directory=caller,
                )

            real_parent = root / "real-parent"
            real_parent.mkdir()
            linked_parent = caller / "linked-parent"
            linked_parent.symlink_to(real_parent, target_is_directory=True)
            with self.assertRaisesRegex(receipt.ReceiptError, "parent component"):
                receipt.prepare_new_receipt_destination(
                    Path("linked-parent/receipt.json"),
                    caller_directory=caller,
                )

    def test_atomic_publish_uses_unique_nofollow_temp_and_fsyncs_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            output = root / "evidence" / "receipt.json"
            output.parent.mkdir()
            collision = output.parent / f".{output.name}.collision.tmp"
            collision_target = output.parent / "collision-target"
            collision_target.write_text("do not overwrite\n", encoding="utf-8")
            collision.symlink_to(collision_target)
            real_fsync = receipt.os.fsync
            with mock.patch.object(
                receipt.secrets,
                "token_hex",
                side_effect=["collision", "unique"],
            ), mock.patch.object(receipt.os, "fsync", wraps=real_fsync) as fsync:
                receipt.write_receipt(output, self.passing_document())
            self.assertEqual(json.loads(output.read_text(encoding="utf-8"))["status"], "passed")
            self.assertTrue(collision.is_symlink())
            self.assertEqual(collision_target.read_text(encoding="utf-8"), "do not overwrite\n")
            self.assertFalse((output.parent / f".{output.name}.unique.tmp").exists())
            self.assertGreaterEqual(fsync.call_count, 2)

    def test_created_parent_chain_is_private_and_each_entry_is_synced(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            output = root / "private" / "nested" / "receipt.json"
            real_fsync = receipt.os.fsync
            with mock.patch.object(receipt.os, "fsync", wraps=real_fsync) as fsync:
                receipt.write_receipt(
                    output,
                    self.passing_document(),
                    replace_existing=False,
                )

            self.assertEqual(output.stat().st_mode & 0o777, 0o644)
            self.assertEqual(output.parent.stat().st_mode & 0o077, 0)
            self.assertEqual(output.parent.parent.stat().st_mode & 0o077, 0)
            # Payload, both newly created parent entries, and final directory.
            self.assertGreaterEqual(fsync.call_count, 4)

    def test_invalid_candidate_preserves_existing_receipt_and_parent_state(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            output = root / "receipt.json"
            output.write_text("previous\n", encoding="utf-8")
            invalid = self.passing_document()
            invalid["status"] = "failed"
            with self.assertRaises(receipt.ReceiptError):
                receipt.write_receipt(output, invalid)
            self.assertEqual(output.read_text(encoding="utf-8"), "previous\n")

            nested = root / "not-created" / "receipt.json"
            unserializable = self.passing_document()
            unserializable["bad"] = object()
            with self.assertRaises(receipt.ReceiptError):
                receipt.write_receipt(nested, unserializable)
            self.assertFalse(nested.parent.exists())

    def test_rejects_unknown_schema_symlink_and_non_regular_destination(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            unknown = self.passing_document()
            unknown["schema"] = "trust.e2e.made-up.v1"
            with self.assertRaises(receipt.ReceiptError):
                receipt.write_receipt(root / "unknown.json", unknown)

            target = root / "target.json"
            target.write_text("unchanged\n", encoding="utf-8")
            symlink = root / "symlink.json"
            symlink.symlink_to(target)
            with self.assertRaises(receipt.ReceiptError):
                receipt.write_receipt(symlink, self.passing_document())
            self.assertEqual(target.read_text(encoding="utf-8"), "unchanged\n")

            directory = root / "directory.json"
            directory.mkdir()
            with self.assertRaises(receipt.ReceiptError):
                receipt.write_receipt(directory, self.passing_document())

    def test_rejects_symlink_and_non_directory_parent_components(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            real_parent = root / "real-parent"
            real_parent.mkdir()
            linked_parent = root / "linked-parent"
            linked_parent.symlink_to(real_parent, target_is_directory=True)
            with self.assertRaisesRegex(receipt.ReceiptError, "parent component is a symlink"):
                receipt.write_receipt(
                    linked_parent / "receipt.json", self.passing_document()
                )
            self.assertFalse((real_parent / "receipt.json").exists())

            file_parent = root / "not-a-directory"
            file_parent.write_text("file\n", encoding="utf-8")
            with self.assertRaisesRegex(receipt.ReceiptError, "not a directory"):
                receipt.write_receipt(
                    file_parent / "receipt.json", self.passing_document()
                )

    def test_rejects_mismatched_embedded_output_digests(self) -> None:
        cases = (
            ("doctor", "report", "doctor report digest"),
            ("serde_fixture", "runtime_output", "serde runtime output digest"),
        )
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary).resolve() / "receipt.json"
            for section, embedded_field, expected_error in cases:
                with self.subTest(section=section):
                    document = self.passing_document()
                    embedded = document[section][embedded_field]
                    embedded["tampered_after_digest"] = True
                    with self.assertRaisesRegex(receipt.ReceiptError, expected_error):
                        receipt.write_receipt(output, document)
                    self.assertFalse(output.exists())

    def test_installed_receipt_requires_exact_manifest_schemas(self) -> None:
        cases = (
            (("source", "manifest_schema"), "source sysroot manifest schema"),
            (("installed", "manifest_schema"), "installed sysroot manifest schema"),
            (
                ("source", "copy_content_manifest_schema"),
                "sysroot copy-content manifest schema",
            ),
            (
                ("source", "materialized_link_inputs_manifest_schema"),
                "materialized source-input manifest schema",
            ),
        )
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary).resolve() / "receipt.json"
            for (section, field), expected_error in cases:
                with self.subTest(section=section, field=field):
                    document = self.passing_document()
                    document["sysroots"][section][field] = "trust.unknown-manifest.v1"
                    with self.assertRaisesRegex(receipt.ReceiptError, expected_error):
                        receipt.write_receipt(output, document)
                    self.assertFalse(output.exists())

    def test_installed_receipt_requires_scoped_copy_and_tracked_input_claims(self) -> None:
        mutations = (
            (("source", "manifest_scope"), "unknown", "source sysroot manifest scope"),
            (
                ("installed", "manifest_scope"),
                "unknown",
                "installed sysroot manifest scope",
            ),
            (
                ("source", "materialized_link_inputs_manifest_scope"),
                "unknown",
                "materialized source-input manifest scope",
            ),
            (
                ("source", "copy_content_manifest_scope"),
                "unknown",
                "sysroot copy-content manifest scope",
            ),
            (
                ("source", "copied_sysroot_content_manifest_sha256"),
                "1" * 64,
                "copied sysroot content manifest differs",
            ),
            (
                ("source", "copied_sysroot_matches_source_content_manifest"),
                False,
                "copied sysroot did not match",
            ),
            (
                ("source", "materialized_link_input_content_copied_exactly"),
                False,
                "source-link content was not copied exactly",
            ),
            (
                ("source", "materialized_link_input_files_git_tracked_only"),
                False,
                "source-link files were not Git-tracked only",
            ),
        )
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary).resolve() / "receipt.json"
            for (section, field), replacement, expected_error in mutations:
                with self.subTest(section=section, field=field):
                    document = self.passing_document()
                    document["sysroots"][section][field] = replacement
                    with self.assertRaisesRegex(receipt.ReceiptError, expected_error):
                        receipt.write_receipt(output, document)
                    self.assertFalse(output.exists())

    def test_dist_receipt_requires_and_hashes_exact_installed_child(self) -> None:
        document = self.dist_document()
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary).resolve() / "dist.json"
            receipt.write_receipt(output, document)
            self.assertEqual(json.loads(output.read_text())["status"], "passed")
            document["installed_toolchain_gate"]["receipt_sha256"] = "1" * 64
            with self.assertRaisesRegex(receipt.ReceiptError, "receipt digest"):
                receipt.write_receipt(output, document)

    def test_dist_receipt_closes_archive_and_channel_binding_schemas(self) -> None:
        mutations = (
            (
                lambda document: document["distribution"].__setitem__(
                    "archive_manifest_schema", "trust.unknown.v1"
                ),
                "archive-manifest schema",
            ),
            (
                lambda document: document["distribution"]["archives"][0].__setitem__(
                    "unexpected", True
                ),
                "open schema",
            ),
            (
                lambda document: document["distribution"].__setitem__(
                    "version", "2.0.0-trust"
                ),
                "root does not match host/version",
            ),
            (
                lambda document: document["channel_manifest"].__setitem__(
                    "host", "x86_64-apple-darwin"
                ),
                "channel host differs",
            ),
            (
                lambda document: document["channel_manifest"].__setitem__(
                    "archive_rows_validated", 0
                ),
                "archive-row count differs",
            ),
        )
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary).resolve() / "dist.json"
            for mutate, expected_error in mutations:
                with self.subTest(expected_error=expected_error):
                    document = self.dist_document()
                    mutate(document)
                    with self.assertRaisesRegex(receipt.ReceiptError, expected_error):
                        receipt.write_receipt(output, document)
                    self.assertFalse(output.exists())

    def test_receipt_claim_scopes_are_closed_and_local_only(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary).resolve() / "receipt.json"
            for document, invalid_kind, expected_error in (
                (
                    self.passing_document(),
                    "public-installed-toolchain-release",
                    "installed claim_scope kind",
                ),
                (
                    self.dist_document(),
                    "public-distribution-release",
                    "dist claim_scope kind",
                ),
            ):
                with self.subTest(invalid_kind=invalid_kind):
                    document["claim_scope"]["kind"] = invalid_kind
                    with self.assertRaisesRegex(receipt.ReceiptError, expected_error):
                        receipt.write_receipt(output, document)
                    self.assertFalse(output.exists())
                    document["claim_scope"]["kind"] = (
                        "local-pre-publication-dist-rehearsal"
                        if document["schema"] == "trust.e2e.dist-artifact-receipt.v1"
                        else "local-installed-toolchain-rehearsal"
                    )
                    document["claim_scope"]["unvalidated_public_claim"] = True
                    with self.assertRaisesRegex(receipt.ReceiptError, "claim_scope schema"):
                        receipt.write_receipt(output, document)
                    self.assertFalse(output.exists())

    def test_dist_receipt_cross_binds_every_child_authority_field(self) -> None:
        contradictions = (
            ("source_head", ("source", "repository_head"), "b" * 40, "source HEAD"),
            (
                "stage_digest",
                ("stage_provenance", "sha256"),
                "1" * 64,
                "provenance digest",
            ),
            (
                "stage_source",
                ("stage_provenance", "source_commit"),
                "b" * 40,
                "provenance source commit",
            ),
            (
                "stage_status",
                ("stage_provenance", "status"),
                "release-ready",
                "provenance status",
            ),
            ("stage_number", ("stage_provenance", "stage"), 1, "provenance stage"),
            ("compiler", ("compiler", "sha256"), "1" * 64, "compiler digest"),
        )
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary).resolve() / "dist.json"
            for name, (section, field), contradictory, expected_error in contradictions:
                with self.subTest(binding=name):
                    document = self.dist_document()
                    child = document["installed_toolchain_gate"]["receipt"]
                    child[section][field] = contradictory
                    with self.assertRaisesRegex(receipt.ReceiptError, expected_error):
                        receipt.write_receipt(output, document)
                    self.assertFalse(output.exists())

    def test_stage_provenance_validation_binds_seed_head_and_compiler(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            trustc = root / "trustc"
            trustc.write_bytes(b"trustc-stage2")
            head = "a" * 40
            report = {
                "schema": "trust.stage-tool-provenance.v2",
                "status": "internal-release-ready",
                "stage": 2,
                "host": "aarch64-apple-darwin",
                "errors": [],
                "tool_binding_status": "ready",
                "source_tree_clean": True,
                "trust_from_trust": True,
                "source_lineage": {"status": "immutable_release"},
                "bootstrap_lineage": {
                    "status": "trust_from_trust",
                    "validated_seed": {
                        "status": "validated",
                        "materialization_status": "fresh-from-validated-archives",
                        "admission_status": "internal-admitted",
                    },
                },
                "build_authority": {"status": "ready"},
                "compiler": {
                    "source_commit": head,
                    "compiler_sha256": receipt.sha256_file(trustc),
                    "sysroot_matches": True,
                },
            }
            provenance = root / "tool-provenance.json"
            provenance.write_text(json.dumps(report), encoding="utf-8")
            binding = receipt.validate_stage_provenance(
                provenance,
                repository_head=head,
                trustc_path=trustc,
            )
            self.assertEqual(binding["compiler_sha256"], receipt.sha256_file(trustc))
            report["bootstrap_lineage"]["validated_seed"]["materialization_status"] = "reused"
            provenance.write_text(json.dumps(report), encoding="utf-8")
            with self.assertRaisesRegex(receipt.ReceiptError, "freshly materialized"):
                receipt.validate_stage_provenance(
                    provenance,
                    repository_head=head,
                    trustc_path=trustc,
                )


class PrivateTempCleanupTests(unittest.TestCase):
    prefix = "trust-installed-e2e."
    system_parent = Path("/tmp").resolve(strict=True)

    @staticmethod
    def identity(path: Path) -> str:
        info = path.lstat()
        return f"{info.st_dev}:{info.st_ino}"

    @staticmethod
    def force_remove(path: Path) -> None:
        if not path.exists() and not path.is_symlink():
            return
        if path.is_symlink():
            path.unlink()
            return
        for child in path.rglob("*"):
            if child.is_dir() and not child.is_symlink():
                child.chmod(0o700)
        path.chmod(0o700)
        shutil.rmtree(path)

    def new_root(self) -> Path:
        return Path(
            tempfile.mkdtemp(prefix=self.prefix, dir=self.system_parent)
        ).resolve(strict=True)

    def test_descriptor_cleanup_removes_read_only_tree_without_following_symlink(self) -> None:
        root = self.new_root()
        with tempfile.TemporaryDirectory() as external_temporary:
            external = Path(external_temporary).resolve()
            sentinel = external / "must-survive.txt"
            sentinel.write_text("outside the cleanup root\n", encoding="utf-8")
            nested = root / "read-only" / "child"
            nested.mkdir(parents=True)
            (nested / "payload.txt").write_text("remove me\n", encoding="utf-8")
            (root / "external-link").symlink_to(external, target_is_directory=True)
            nested.chmod(0o500)
            nested.parent.chmod(0o500)
            try:
                receipt.remove_private_temp_tree(
                    root,
                    system_parent=self.system_parent,
                    expected_prefix=self.prefix,
                    expected_identity=self.identity(root),
                )
                self.assertFalse(root.exists())
                self.assertEqual(
                    sentinel.read_text(encoding="utf-8"),
                    "outside the cleanup root\n",
                )
            finally:
                self.force_remove(root)

    def test_descriptor_cleanup_refuses_replaced_root_identity(self) -> None:
        root = self.new_root()
        displaced = root.with_name(f"{root.name}-displaced")
        identity = self.identity(root)
        root.rename(displaced)
        root.mkdir(mode=0o700)
        (root / "replacement.txt").write_text("preserve replacement\n", encoding="utf-8")
        (displaced / "original.txt").write_text("preserve original on refusal\n", encoding="utf-8")
        try:
            with self.assertRaisesRegex(receipt.ReceiptError, "identity changed"):
                receipt.remove_private_temp_tree(
                    root,
                    system_parent=self.system_parent,
                    expected_prefix=self.prefix,
                    expected_identity=identity,
                )
            self.assertTrue((root / "replacement.txt").is_file())
            self.assertTrue((displaced / "original.txt").is_file())
        finally:
            self.force_remove(root)
            self.force_remove(displaced)

    def test_publish_after_cleanup_commits_only_after_temp_root_is_absent(self) -> None:
        root = self.new_root()
        candidate = root / "candidate.json"
        candidate.write_text(
            json.dumps(AtomicReceiptTests().passing_document()),
            encoding="utf-8",
        )
        with tempfile.TemporaryDirectory() as output_temporary:
            output = Path(output_temporary).resolve() / "receipt.json"
            real_write = receipt.write_receipt

            def assert_cleaned_before_write(*args, **kwargs) -> None:
                self.assertFalse(root.exists(), "temp root must be gone before publication")
                real_write(*args, **kwargs)

            try:
                with mock.patch.object(
                    receipt,
                    "write_receipt",
                    side_effect=assert_cleaned_before_write,
                ):
                    receipt._publish_after_cleanup_command(
                        argparse.Namespace(
                            input=candidate,
                            output=output,
                            cleanup_path=root,
                            system_parent=self.system_parent,
                            expected_prefix=self.prefix,
                            expected_identity=self.identity(root),
                        )
                    )
                self.assertEqual(json.loads(output.read_text())["status"], "passed")
            finally:
                self.force_remove(root)


class GateScriptOutputSafetyTests(unittest.TestCase):
    scripts = (
        REPO_ROOT / "tests" / "e2e_trust_local_rustup_install.sh",
        REPO_ROOT / "tests" / "e2e_trust_dist_artifacts.sh",
    )

    def test_relative_existing_output_is_anchored_to_invocation_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            caller = Path(temporary).resolve()
            output = caller / "receipt.json"
            output.write_text("customer file; preserve exactly\n", encoding="utf-8")
            for script in self.scripts:
                with self.subTest(script=script.name):
                    completed = subprocess.run(
                        ["bash", str(script), "--receipt", "receipt.json"],
                        cwd=caller,
                        env={
                            **dict(os.environ),
                            "TRUST_E2E_PYTHON3": sys.executable,
                        },
                        text=True,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        check=False,
                    )
                    self.assertNotEqual(completed.returncode, 0)
                    self.assertIn("already exists", completed.stderr)
                    self.assertEqual(
                        output.read_text(encoding="utf-8"),
                        "customer file; preserve exactly\n",
                    )

    def test_unignored_checkout_destination_is_rejected_before_publication(self) -> None:
        output = REPO_ROOT / ".trust-receipt-output-safety-test.json"
        self.assertFalse(output.exists())
        for script in self.scripts:
            with self.subTest(script=script.name):
                completed = subprocess.run(
                    ["bash", str(script), "--receipt", str(output)],
                    cwd=REPO_ROOT,
                    env={
                        **dict(os.environ),
                        "TRUST_E2E_PYTHON3": sys.executable,
                    },
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    check=False,
                )
                self.assertNotEqual(completed.returncode, 0)
                self.assertIn("inside the repository must be ignored", completed.stderr)
                self.assertFalse(output.exists())

    def test_scripts_recheck_authority_before_no_replace_publication(self) -> None:
        for script in self.scripts:
            with self.subTest(script=script.name):
                source = script.read_text(encoding="utf-8")
                publish = source.rfind('"$RECEIPT_HELPER" publish-after-cleanup')
                pre_publish = source.rfind("\n    verify_repository_before_publication\n")
                self.assertGreaterEqual(publish, 0)
                self.assertGreater(pre_publish, source.rfind('RECEIPT_CANDIDATE="$TMP_ROOT/'))
                self.assertLess(pre_publish, publish)
                publication_block = source[publish:]
                self.assertIn("--cleanup-path", publication_block)
                self.assertIn("--expected-identity", publication_block)
                self.assertIn('exec "$PYTHON3_BIN"', source[publish - 80 : publish])
                self.assertIn("trap - EXIT HUP INT TERM", source[publish - 200 : publish])
                self.assertIn("status --porcelain=v1", source)
                self.assertNotIn("verify_repository_after_publication", source)
                self.assertNotIn('cmp -s "$RECEIPT_CANDIDATE" "$RECEIPT_OUT"', source)
                self.assertIn("ls-files --error-unmatch", source)
                self.assertIn("check-ignore --quiet --no-index", source)
                self.assertGreaterEqual(
                    source.count('"$RECEIPT_HELPER" validate-stage'),
                    2,
                    "Stage2 provenance must be revalidated after the rehearsal",
                )
                verification_definition = source[
                    source.index("verify_repository_before_publication() {") :
                    source.index("\n}\n", source.index("verify_repository_before_publication() {"))
                ]
                self.assertIn('"$RECEIPT_HELPER" validate-stage', verification_definition)
                self.assertNotRegex(publication_block, r"\n\s+(?:verify|require|check)[A-Za-z0-9_]*")

    def test_installed_source_baseline_precedes_scan_copy_and_materialization(self) -> None:
        script = self.scripts[0].read_text(encoding="utf-8")
        baseline = script.index(
            'write_content_manifest "$SOURCE_SYSROOT" "$SOURCE_MANIFEST" 0'
        )
        link_inputs = script.index("write_materialized_source_inputs_manifest", baseline)
        self.assertIn(
            '"$SOURCE_LINK_INPUT_MANIFEST"',
            script[link_inputs : link_inputs + 200],
        )
        self.assertLess(baseline, script.index('root.rglob("*")', baseline))
        self.assertLess(baseline, script.index('cp -R "$SOURCE_SYSROOT/."'))
        self.assertLess(baseline, script.index("materialize_source_link()"))
        self.assertLess(link_inputs, script.index('root.rglob("*")', baseline))
        self.assertLess(link_inputs, script.index('cp -R "$SOURCE_SYSROOT/."'))
        self.assertIn("materialized-source-inputs-final.ndjson", script)
        self.assertIn("materialized-installed-inputs.ndjson", script)
        self.assertIn("source-sysroot-copy-content.ndjson", script)
        self.assertIn(
            'write_content_manifest "$SOURCE_SYSROOT" "$SOURCE_COPY_CONTENT_MANIFEST" 0 0',
            script,
        )
        self.assertIn(
            'cmp -s "$SOURCE_COPY_CONTENT_MANIFEST" "$COPIED_SYSROOT_CONTENT_MANIFEST"',
            script,
        )
        self.assertIn(
            'cmp -s "$SOURCE_LINK_INPUT_MANIFEST" "$INSTALLED_LINK_INPUT_MANIFEST"',
            script,
        )
        self.assertIn("--ignored=matching", script)
        self.assertIn("materialized_link_input_files_git_tracked_only", script)
        self.assertIn("target != repository", script)
        self.assertIn(
            'cmp -s "$SOURCE_LINK_INPUT_MANIFEST" "$SOURCE_LINK_INPUT_MANIFEST_FINAL"',
            script,
        )

    def test_gate_scripts_label_results_as_non_authoritative_diagnostics(self) -> None:
        forbidden = (
            "local release evidence",
            "local pre-publication evidence",
            "gate: PASS",
            "durable receipt",
            "Canonical entrypoint for the immutable installed-toolchain acceptance gate",
        )
        scripts = (*self.scripts, REPO_ROOT / "tests" / "e2e_trust_installed_toolchain.sh")
        for script in scripts:
            with self.subTest(script=script.name):
                source = script.read_text(encoding="utf-8")
                for stale_claim in forbidden:
                    self.assertNotIn(stale_claim, source)
                self.assertRegex(source, r"(?i)(local diagnostic|local rehearsal|non-authoritative)")

    def test_scripts_create_and_revalidate_private_owned_temp_roots(self) -> None:
        prefixes = {
            "e2e_trust_local_rustup_install.sh": "trust-installed-e2e.",
            "e2e_trust_dist_artifacts.sh": "trust-dist-e2e.",
        }
        validation_call = re.compile(
            r"(?m)^[^\n]*(?:validate|verify|require|check)[A-Za-z0-9_]*"
            r"[^\n]*\"\$TMP_ROOT\""
        )

        for script in self.scripts:
            with self.subTest(script=script.name):
                source = script.read_text(encoding="utf-8")
                prefix = prefixes[script.name]

                self.assertRegex(source, r"(?m)^umask 077$")
                self.assertNotRegex(
                    source,
                    r"\$(?:TMPDIR\b|\{TMPDIR[^}]*\})",
                    "ambient TMPDIR must not select the gate's cleanup root",
                )
                self.assertNotRegex(source, r"\$\(\s*mktemp(?:\s|$)")
                self.assertRegex(
                    source,
                    rf'/usr/bin/mktemp\s+-d\s+["\']?/tmp/{re.escape(prefix)}XXXXXX',
                )

                # The creation result is checked as an absolute, canonical
                # direct child of /tmp with the exact per-gate basename prefix.
                self.assertRegex(
                    source,
                    r'(?:canonical|realpath)[A-Za-z0-9_]*\s+["\']?/tmp["\']?',
                )
                self.assertIn("pwd -P", source)
                self.assertRegex(
                    source,
                    r'case\s+"\$[A-Za-z_][A-Za-z0-9_]*"\s+in\s*\n\s*/\*\)',
                )
                self.assertRegex(
                    source,
                    r'\[\s+"\$[a-z_]*parent"\s+=\s+"\$SYSTEM_TEMP_PARENT"\s+\]',
                )
                self.assertGreaterEqual(source.count(prefix), 2)
                self.assertRegex(source, r"\[\s+!?\s*-d\s+")
                self.assertRegex(source, r"\[\s+!?\s*-L\s+")
                self.assertRegex(source, r"\[\s+!?\s*-O\s+")
                self.assertIn("/usr/bin/stat", source)
                self.assertIn("700", source)
                self.assertIn("%d", source)
                self.assertIn("%i", source)
                self.assertRegex(
                    source,
                    r"TMP_ROOT_(?:ID|[A-Z_]*(?:IDENTITY|DEVICE_INODE))\b",
                )

                trap_at = source.index("trap cleanup")
                creation_at = source.index("/usr/bin/mktemp")
                self.assertIsNotNone(
                    validation_call.search(source, creation_at, trap_at),
                    "new temp root must be validated before its EXIT trap is armed",
                )

                cleanup_at = source.index("cleanup() {")
                cleanup_end = source.index("\n}\n", cleanup_at) + 3
                cleanup = source[cleanup_at:cleanup_end]
                self.assertRegex(
                    cleanup,
                    r"TMP_ROOT_(?:ID|[A-Z_]*(?:IDENTITY|DEVICE_INODE))\b",
                )
                self.assertIn('"$RECEIPT_HELPER" remove-private-temp', cleanup)
                self.assertIn('--path "$TMP_ROOT"', cleanup)
                self.assertIn('--system-parent "$SYSTEM_TEMP_PARENT"', cleanup)
                self.assertIn(f'--expected-prefix "{prefix}"', cleanup)
                self.assertIn('--expected-identity "$TMP_ROOT_ID"', cleanup)
                self.assertNotIn("/bin/chmod -R", cleanup)
                self.assertNotIn("/bin/rm -rf", cleanup)
                self.assertIn('[ -e "$TMP_ROOT" ] || [ -L "$TMP_ROOT" ]', cleanup)

    def test_hostile_path_mktemp_and_ambient_tmpdir_cannot_select_cleanup_target(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            for script in self.scripts:
                with self.subTest(script=script.name):
                    case_root = root / script.stem
                    fake_bin = case_root / "hostile-bin"
                    victim = case_root / "victim"
                    ambient_tmp = case_root / "ambient-tmp"
                    source_sysroot = case_root / "source-sysroot"
                    dist_dir = case_root / "dist"
                    for directory in (
                        fake_bin,
                        victim,
                        ambient_tmp,
                        source_sysroot,
                        dist_dir,
                    ):
                        directory.mkdir(parents=True)
                    ambient_tmp.chmod(0o777)
                    victim.chmod(0o755)
                    sentinel = victim / "must-survive.txt"
                    sentinel.write_text("never a cleanup target\n", encoding="utf-8")
                    marker = case_root / "path-mktemp-was-run"

                    fake_mktemp = fake_bin / "mktemp"
                    fake_mktemp.write_text(
                        "#!/bin/sh\n"
                        ': >"$FAKE_MKTEMP_MARKER"\n'
                        'printf \'%s\\n\' "$FAKE_MKTEMP_VICTIM"\n',
                        encoding="utf-8",
                    )
                    fake_mktemp.chmod(0o755)
                    fake_rustup = fake_bin / "rustup"
                    fake_rustup.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
                    fake_rustup.chmod(0o755)
                    python_shim = fake_bin / "test-python"
                    python_shim.write_text(
                        "#!/bin/sh\n"
                        'if [ "$1" = "-c" ] && [ "$2" = "import tomllib" ]; then\n'
                        "    exit 0\n"
                        "fi\n"
                        'exec "$REAL_TEST_PYTHON" "$@"\n',
                        encoding="utf-8",
                    )
                    python_shim.chmod(0o755)

                    environment = {
                        "PATH": f"{fake_bin}:{os.environ.get('PATH', '/usr/bin:/bin')}",
                        "TMPDIR": str(ambient_tmp),
                        "TRUST_E2E_PYTHON3": str(python_shim),
                        "REAL_TEST_PYTHON": sys.executable,
                        "FAKE_MKTEMP_MARKER": str(marker),
                        "FAKE_MKTEMP_VICTIM": str(victim),
                        "LC_ALL": "C",
                    }
                    if script.name == "e2e_trust_local_rustup_install.sh":
                        arguments = ["--source-sysroot", str(source_sysroot)]
                    else:
                        channel_manifest = case_root / "channel-rust-trust.toml"
                        channel_manifest.write_text("", encoding="utf-8")
                        arguments = [
                            "--dist-dir",
                            str(dist_dir),
                            "--channel-manifest",
                            str(channel_manifest),
                            "--host",
                            "aarch64-apple-darwin",
                            "--version",
                            "1.99.0-trust",
                        ]

                    completed = subprocess.run(
                        ["/bin/bash", str(script), *arguments],
                        cwd=case_root,
                        env=environment,
                        text=True,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        check=False,
                        timeout=30,
                    )
                    self.assertNotEqual(completed.returncode, 0)
                    self.assertFalse(
                        marker.exists(),
                        f"{script.name} executed attacker-controlled PATH mktemp",
                    )
                    self.assertEqual(
                        sentinel.read_text(encoding="utf-8"),
                        "never a cleanup target\n",
                    )
                    self.assertEqual(
                        list(ambient_tmp.iterdir()),
                        [],
                        f"{script.name} used attacker-controlled ambient TMPDIR",
                    )


class LegacyHarnessReleaseBoundaryTests(unittest.TestCase):
    canonical_modes = (
        "quick",
        "trust-added-compiletest",
        "trustc-native",
        "native-contracts-pipeline-v2",
        "trust-extra",
        "binary-decompilation-golden",
        "launch",
        "public-distribution",
        "prepublish",
        "installed",
        "installed-default",
        "stage0-lineage",
    )

    def run_shell(self, script: str, *arguments: str, release: bool = False):
        environment = dict(os.environ)
        if release:
            environment["TRUST_RELEASE_GATE"] = "1"
        return subprocess.run(
            ["/bin/bash", str(REPO_ROOT / "tests" / script), *arguments],
            cwd=REPO_ROOT,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=10,
        )

    def test_robust_and_superset_entrypoints_block_all_canonical_release_ids(self) -> None:
        for script in ("run_trust_robust_suite.sh", "run_trust_superset_suite.sh"):
            for mode in self.canonical_modes:
                with self.subTest(script=script, mode=mode):
                    completed = self.run_shell(script, mode, release=True)
                    self.assertEqual(completed.returncode, 2)
                    output = completed.stdout + completed.stderr
                    self.assertIn(
                        f"targo trust domination trust-added --release {mode}", output
                    )
                    self.assertNotIn(": PASS ===", output)

    def test_comprehensive_release_inventory_marks_all_twelve_ids_blocked(self) -> None:
        completed = self.run_shell(
            "run_trust_comprehensive_harness.sh", "list", "release"
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        blocked = [
            line
            for line in completed.stdout.splitlines()
            if "\tblocked-release-inventory\t" in line
        ]
        self.assertEqual(len(blocked), len(self.canonical_modes))
        for mode in self.canonical_modes:
            self.assertTrue(
                any(
                    "TRUST_RELEASE_GATE=1" in line
                    and line.rstrip().endswith(f" {mode}")
                    for line in blocked
                ),
                f"comprehensive release inventory does not fail closed for {mode}",
            )

    def test_comprehensive_example_diagnostic_cannot_be_promoted_to_evidence(self) -> None:
        completed = self.run_shell(
            "run_trust_comprehensive_harness.sh", "list", "release"
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        rows = [
            line.split("\t")
            for line in completed.stdout.splitlines()
            if line.startswith("trust.examples.complete-corpus-diagnostic\t")
        ]
        self.assertEqual(len(rows), 1)
        gate_id, category, required, last_green, command = rows[0]
        self.assertEqual(gate_id, "trust.examples.complete-corpus-diagnostic")
        self.assertEqual(category, "non-evidence-regression-diagnostic")
        self.assertEqual(required, "true")
        self.assertRegex(last_green, r"^(never|\d{4}-\d{2}-\d{2})$")
        self.assertIn("env -u TRUST_RELEASE_GATE", command)
        self.assertIn("TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1", command)

        source = (
            REPO_ROOT / "tests" / "run_trust_comprehensive_harness.sh"
        ).read_text(encoding="utf-8")
        self.assertIn('row["proof_evidence"] = False', source)
        self.assertIn('row["release_evidence"] = False', source)
        self.assertIn('"diagnostic_passed"', source)
        self.assertIn(
            '"non_evidence_success_can_block_but_never_satisfies_evidence": True',
            source,
        )

    def test_superset_release_and_status_report_cannot_promote_diagnostics(self) -> None:
        completed = self.run_shell("run_trust_superset_suite.sh", "release")
        self.assertEqual(completed.returncode, 2)
        output = completed.stdout + completed.stderr
        self.assertIn(
            "targo trust domination trust-added --release prepublish", output
        )
        self.assertNotIn("Superset Test Suite (release): PASS", output)

        report_source = (
            REPO_ROOT / "tests" / "report_trust_gate_status.sh"
        ).read_text(encoding="utf-8")
        start = report_source.index("canonical_trust_added_release_mode()")
        end = report_source.index("\n}\n", start)
        guard = report_source[start:end]
        for mode in self.canonical_modes:
            self.assertIn(mode, guard)
        core_start = report_source.index("CORE_GATES=(")
        core_end = report_source.index("\n)", core_start)
        core_inventory = report_source[core_start:core_end]
        for mode in self.canonical_modes:
            self.assertIn(
                mode,
                core_inventory,
                f"status report omits required canonical mode {mode}",
            )
        self.assertIn("record_gate \"$gate\" 2", report_source)
        self.assertIn("Direct shell diagnostics are intentionally not run", report_source)

    def test_legacy_harness_scratch_paths_ignore_path_and_tmpdir(self) -> None:
        harnesses = (
            "run_trust_robust_suite.sh",
            "run_trust_superset_suite.sh",
            "report_trust_gate_status.sh",
        )
        for script in harnesses:
            with self.subTest(script=script):
                source = (REPO_ROOT / "tests" / script).read_text(encoding="utf-8")
                self.assertRegex(source, r"(?m)^umask 077$")
                self.assertNotRegex(source, r"\$(?:TMPDIR\b|\{TMPDIR[^}]*\})")
                self.assertNotRegex(source, r"\$\(\s*mktemp(?:\s|$)")
                self.assertIn("/usr/bin/mktemp", source)
                self.assertIn("/tmp/trust-", source)


@unittest.skipIf(receipt.tomllib is None, "Python 3.11+ tomllib required")
class ChannelManifestTests(unittest.TestCase):
    host = "aarch64-apple-darwin"

    def test_required_default_profile_matches_checked_in_build_manifest_shape(self) -> None:
        manifest_path = REPO_ROOT / "bootstrap" / "trust-stage0" / "dist" / "channel-rust-trust.toml"
        manifest = receipt.tomllib.loads(manifest_path.read_text(encoding="utf-8"))
        default_profile = manifest["profiles"]["default"]
        self.assertEqual(len(default_profile), len(set(default_profile)))
        self.assertEqual(set(default_profile), receipt.REQUIRED_DEFAULT_PROFILE)

    def create_fixture(self, root: Path) -> tuple[Path, Path, Path]:
        dist = root / "dist"
        dist.mkdir()
        rows = []
        package_sections = []
        for component in sorted(receipt.REQUIRED_ARCHIVE_COMPONENTS):
            target = "*" if component == "trust-src" else self.host
            manifest_component = (
                f"{component}-preview"
                if component in receipt._PREVIEW_COMPONENTS
                else component
            )
            archive = dist / f"{component}-1.99.0-trust-{target}.tar.xz"
            archive.write_bytes(f"archive:{component}\n".encode())
            digest = receipt.sha256_file(archive)
            rows.append(
                {
                    "component": component,
                    "archive_path": str(archive.resolve()),
                    "archive_filename": archive.name,
                    "size_bytes": archive.stat().st_size,
                    "extension": "tar.xz",
                    "archive_root": archive.name.removesuffix(".tar.xz"),
                    "sha256": digest,
                    "selected": True,
                }
            )
            extensions = ""
            if component == "trust":
                extensions = (
                    f'extensions = [{{ pkg = "targo-trust", target = "{self.host}" }}]\n'
                )
            package_sections.append(
                f'''[pkg."{manifest_component}"]
version = "1.99.0-trust"
[pkg."{manifest_component}".target."{target}"]
available = true
xz_url = "https://static.example.test/dist/{archive.name}"
xz_hash = "{digest}"
{extensions}'''
            )

        archive_manifest = root / "archives.ndjson"
        archive_manifest.write_text(
            "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
            encoding="utf-8",
        )
        default_profile = ", ".join(
            json.dumps(item) for item in sorted(receipt.REQUIRED_DEFAULT_PROFILE)
        )
        manifest = root / "channel-rust-trust.toml"
        manifest.write_text(
            f'''manifest-version = "2"
date = "2026-07-20"
[profiles]
default = [{default_profile}]
{''.join(package_sections)}''',
            encoding="utf-8",
        )
        return manifest, archive_manifest, dist

    def test_channel_manifest_binds_profile_extension_urls_and_hashes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            manifest, archives, dist = self.create_fixture(Path(temporary))
            result = receipt.validate_channel_manifest(
                manifest,
                archives,
                dist_dir=dist,
                host=self.host,
            )
            self.assertEqual(result["archive_rows_validated"], 12)
            self.assertTrue(result["targo_trust_available"])
            self.assertTrue(result["umbrella_targo_trust_extension"])
            self.assertEqual(result["hosting_claim"], "none-local-rehearsal-only")

    def test_channel_manifest_rejects_an_archive_hash_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            manifest, archives, dist = self.create_fixture(Path(temporary))
            rows = archives.read_text(encoding="utf-8").splitlines()
            row = json.loads(rows[0])
            row["sha256"] = "0" * 64
            rows[0] = json.dumps(row)
            archives.write_text("\n".join(rows) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(receipt.ReceiptError, "digest changed"):
                receipt.validate_channel_manifest(
                    manifest,
                    archives,
                    dist_dir=dist,
                    host=self.host,
                )

    def test_channel_manifest_rejects_missing_daily_driver_profile_entry(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            manifest, archives, dist = self.create_fixture(Path(temporary))
            contents = manifest.read_text(encoding="utf-8")
            contents = contents.replace('"targo-trust", ', "", 1)
            manifest.write_text(contents, encoding="utf-8")
            with self.assertRaisesRegex(receipt.ReceiptError, "default profile is missing"):
                receipt.validate_channel_manifest(
                    manifest,
                    archives,
                    dist_dir=dist,
                    host=self.host,
                )


if __name__ == "__main__":
    unittest.main()
