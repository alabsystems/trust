#!/usr/bin/env python3
"""Inert phase-two selector and disclosure controls; no compiler executes."""
from __future__ import annotations

from contextlib import ExitStack
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("continuation_inert_fixture", ROOT / "scripts/tests/mint_seed_recovery_test.py")
fixture = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(fixture)
recovery, support = fixture.recovery, fixture.REAL


class ContinuationContextTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="continuation-context-inert-")
        self.addCleanup(temp.cleanup)
        self.f = fixture.Fixture(Path(temp.name))
        self.stack = ExitStack()
        self.addCleanup(self.stack.close)
        self.engine_commit = "e" * 40
        self.source_commit = fixture.COMMIT

        def git(_root, *args):
            if args == ("rev-parse", "HEAD"):
                return SimpleNamespace(returncode=0, stdout=self.engine_commit + "\n", stderr="")
            if args[0] == "status":
                return SimpleNamespace(returncode=0, stdout="", stderr="")
            raise AssertionError(f"unexpected Git operation: {args}")

        def repository(root, expected_commit=None):
            if root != self.f.root or (expected_commit is not None and expected_commit != self.source_commit):
                support.fail("source HEAD changed during the workflow")
            return {**self.f.source, "commit": self.source_commit}

        self.stack.enter_context(mock.patch.object(support, "git_command", side_effect=git))
        self.stack.enter_context(mock.patch.object(support, "repository_state", side_effect=repository))
        self.stack.enter_context(mock.patch.object(support, "canonical_version", return_value=fixture.VERSION))
        self.stack.enter_context(mock.patch.object(subprocess, "Popen", side_effect=AssertionError("no native process in inert controls")))
        self.f.engine = recovery.engine_identity(support)
        self.record = self.f.inspect()
        recovery.prepare(self.record, support=self.f.support, owner=self.f.owner)
        self.record_path = self.f.evidence / "prepared-record.json"
        self.save()
        Path(self.record["cargo_source"]).mkdir()
        self.selectors = {"config": self.f.config, "host": fixture.HOST,
                          "clean_lean_lib": self.f.lean_file.parent, "library_path": "", "seed_dylib_path": "",
                          "ddc_seed": self.f.oracle, "cargo_source": Path(self.record["cargo_source"]),
                          "python": self.f.helper}

    def save(self):
        fixture.write(self.record_path, self.record)
        self.record_sha = recovery.digest(self.record_path)

    def context(self, **changes):
        return support.continuation_context(self.f.root, self.record_path, self.record_sha,
                                             **{**self.selectors, **changes})

    def refuses(self, text, **changes):
        with self.assertRaisesRegex(support.WorkflowError, text):
            self.context(**changes)

    def prepare_elan_alias(self):
        # Capture an original alias selection through the real recovery path;
        # later context checks must preserve both this literal and its target.
        self.f = fixture.Fixture(self.f.base / "alias-world")
        toolchain = self.f.base / "elan/toolchains/leanprover--lean4---v4.30.0-rc2"
        toolchain.parent.mkdir(parents=True)
        toolchain.symlink_to(self.f.lean_file.parents[2], target_is_directory=True)
        library = toolchain / "lib/lean"
        lean = {**self.f.lean(), "library_path": str(library),
                "environment": {**self.f.lean()["environment"], "CLEAN_OLEAN_PINNED_LEAN_LIB": str(library)}}
        self.f.support.clean_lean_inputs = lambda *args: lean
        self.f.provenance["bootstrap_lineage"]["mint_configuration"]["clean_lean_inputs"] = lean
        self.f.provenance["build_authority"]["clean_lean_inputs"] = lean
        self.f.provenance["build_authority"]["declared_environment_sha256"]["CLEAN_OLEAN_PINNED_LEAN_LIB"] = hashlib.sha256(str(library).encode()).hexdigest()
        terminal_path = self.f.evidence / "mint-result.json"
        terminal = recovery.document(terminal_path)
        terminal["command"][terminal["command"].index("--clean-lean-lib") + 1] = str(library)
        fixture.write(terminal_path, terminal)
        self.f.save_provenance()
        self.f.engine = recovery.engine_identity(support)
        self.record = self.f.inspect()
        recovery.prepare(self.record, support=self.f.support, owner=self.f.owner)
        self.record_path = self.f.evidence / "prepared-record.json"
        self.save()
        Path(self.record["cargo_source"]).mkdir()
        self.selectors.update(config=self.f.config, clean_lean_lib=library, ddc_seed=self.f.oracle,
                              cargo_source=Path(self.record["cargo_source"]), python=self.f.helper)
        return toolchain, library

    def test_original_elan_intermediate_toolchain_alias_is_accepted(self):
        toolchain, library = self.prepare_elan_alias()
        self.assertTrue(toolchain.is_symlink())
        self.assertFalse(library.is_symlink())
        self.assertEqual(library.resolve(), self.f.lean_file.parent)
        actual = self.context()
        self.assertEqual(actual["declared_environment"]["CLEAN_OLEAN_PINNED_LEAN_LIB"], str(library))
        self.assertFalse(actual["qualification"])

    def test_different_elan_alias_to_same_physical_lean_refuses(self):
        _, library = self.prepare_elan_alias()
        other = self.f.base / "other-elan/toolchains/leanprover--lean4---v4.30.0-rc2"
        other.parent.mkdir(parents=True)
        other.symlink_to(self.f.lean_file.parents[2], target_is_directory=True)
        self.assertEqual((other / "lib/lean").resolve(), library.resolve())
        self.refuses("clean_lean_lib selection differs", clean_lean_lib=other / "lib/lean")

    def test_original_elan_alias_retargeted_to_other_physical_lean_refuses(self):
        toolchain, library = self.prepare_elan_alias()
        original_receipt = (self.f.stage / "tool-provenance.json").read_bytes()
        other = self.f.base / "other-physical-lean"
        fixture.put(other / "lib/lean/fixture", self.f.lean_file.read_bytes())
        toolchain.unlink()
        toolchain.symlink_to(other, target_is_directory=True)
        self.assertNotEqual(library.resolve(), self.f.lean_file.parent)
        self.refuses("clean_lean_lib selection differs.*physical installation changed")
        self.assertEqual((self.f.stage / "tool-provenance.json").read_bytes(), original_receipt)

    def test_prepared_context_matches_every_selector_without_granting_selfhost(self):
        actual = self.context()
        self.assertFalse(actual["qualification"])
        self.assertEqual(actual["state"], "prepared")
        self.assertEqual(actual["original_terminal_exit"], 1)
        self.assertEqual(actual["original_jobs"], 12)
        self.assertNotIn("fresh_selfhost_jobs", actual)

    def test_work_only_does_not_require_final_selectors_but_requires_prepared_record(self):
        actual = support.continuation_context(self.f.root, self.record_path, self.record_sha, work_only=True)
        self.assertEqual(actual["work"], str(self.f.work))
        self.record["state"] = "inspected"
        self.save()
        with self.assertRaisesRegex(support.WorkflowError, "prepared, unqualified"):
            support.continuation_context(self.f.root, self.record_path, self.record_sha, work_only=True)

    def test_record_hash_duplicate_key_and_claim_upgrade_refuse(self):
        with self.assertRaisesRegex(support.WorkflowError, "JSON input changed"):
            support.continuation_context(self.f.root, self.record_path, "f" * 64, work_only=True)
        self.record["qualification"] = True
        self.save()
        self.refuses("prepared, unqualified")
        fixture.put(self.record_path, '{"state":"prepared","state":"prepared"}')
        self.record_sha = recovery.digest(self.record_path)
        self.refuses("duplicate JSON key")

    def test_product_and_engine_drift_refuse_independently(self):
        self.source_commit = "f" * 40
        self.refuses("source HEAD changed")
        self.source_commit = fixture.COMMIT
        self.engine_commit = "f" * 40
        self.refuses("orchestration source changed")

    def test_config_host_and_lean_selectors_cannot_be_silently_substituted(self):
        other_config = fixture.put(self.f.root / "other.toml", "[build]\n")
        other_lean = self.f.base / "other-lean"
        other_lean.mkdir()
        for name, value in (("config", other_config), ("host", "x86_64-apple-darwin"),
                            ("clean_lean_lib", other_lean)):
            with self.subTest(selector=name):
                self.refuses(name + " selection differs", **{name: value})

    def test_cargo_python_oracle_and_library_selectors_are_exact(self):
        other_dir = self.f.base / "other-input"
        other_dir.mkdir()
        other_python = fixture.put(self.f.base / "other-python", "inert second Python")
        for name, value in (("cargo_source", other_dir), ("python", other_python),
                            ("ddc_seed", other_dir), ("library_path", str(other_dir)),
                            ("seed_dylib_path", str(other_dir))):
            with self.subTest(selector=name):
                self.refuses(name + " selection differs", **{name: value})

    def test_missing_python_or_cargo_source_does_not_mean_reuse(self):
        for selector in ("python", "cargo_source"):
            with self.subTest(selector=selector):
                self.refuses(selector + " selection differs", **{selector: None})

    def test_saved_alias_manifest_and_physical_helper_identity_remain_live(self):
        manifest = Path(self.record["path_manifest"])
        original = manifest.read_bytes()
        fixture.put(manifest, original + b" ")
        self.refuses("JSON input changed")
        fixture.put(manifest, original)
        fixture.put(self.f.helper, "changed physical helper")
        self.refuses("sanitized PATH target changed")

    def test_workspace_path_alias_or_escape_refuses_even_with_new_record_hash(self):
        original = self.record["safe_bin"]
        self.record["safe_bin"] = str(self.f.base / "foreign-safe-bin")
        self.save()
        self.refuses("safe_bin differs")
        self.record["safe_bin"] = original
        self.record["work"] = str(self.f.base)
        self.save()
        self.refuses("workspace escapes")

    def test_product_build_and_declared_namespace_cannot_cross_associate(self):
        original = json.loads(json.dumps(self.record))
        for name, value, message in (("root", str(self.f.base), "product root differs"),
                                     ("version", "0.1.0", "retained build differs"),
                                     ("build", str(self.f.root / "build/foreign-mint"), "retained build differs")):
            with self.subTest(field=name):
                self.record = {**original, name: value}
                self.save()
                self.refuses(message)
        for name in ("CARGO_HOME", "RUSTUP_HOME"):
            with self.subTest(environment=name):
                self.record = {**original, "declared_environment": {**original["declared_environment"], name: str(self.f.base)}}
                self.save()
                self.refuses("declared environment differs")

    def test_retained_stage_receipt_must_stay_bound_until_final_disclosure(self):
        p = self.f.stage / "tool-provenance.json"
        fixture.put(p, p.read_bytes() + b" ")
        self.refuses("retained stage provenance changed")

    def test_final_disclosure_binds_original_record_and_fresh_jobs_without_relabelling(self):
        args = self.finalize_args()
        with mock.patch.object(support, "verify_clean_lean_inputs", return_value=self.f.lean()), \
             mock.patch.object(sys, "executable", str(self.f.helper)):
            support.finalize_manifest(**args, continuation_record=self.record_path,
                                      continuation_record_sha256=self.record_sha, continuation_build_jobs=20)
        result = recovery.document(args["output"])
        disclosure = result["continuation"]
        self.assertEqual(disclosure["record_sha256"], self.record_sha)
        self.assertEqual(disclosure["record"]["original_jobs"], 12)
        self.assertEqual(disclosure["fresh_selfhost_jobs"], 20)
        self.assertFalse(disclosure["record"]["qualification"])
        self.assertFalse(disclosure["record"]["original_private_cargo_retained"])
        self.assertEqual(result["environment"]["cargo_home_inputs_scope"], "fresh continuation phase")

    def test_final_disclosure_cannot_omit_hash_or_fresh_job_grant(self):
        for changes in ({"continuation_build_jobs": None}, {"continuation_record_sha256": None},
                        {"continuation_build_jobs": 0}, {"continuation_build_jobs": True}):
            with self.subTest(changes=changes):
                args = self.finalize_args()
                options = {"continuation_record": self.record_path,
                           "continuation_record_sha256": self.record_sha, "continuation_build_jobs": 20, **changes}
                with mock.patch.object(support, "verify_clean_lean_inputs", return_value=self.f.lean()), \
                     self.assertRaisesRegex(support.WorkflowError, "positive fresh job count"):
                    support.finalize_manifest(**args, **options)
                self.assertFalse(args["output"].exists())

    def finalize_args(self):
        base = self.f.work / "fresh-phase"
        input_manifest = fixture.write(base / "seed-inputs.json", {"schema": "inert-selfhost-input", "host": fixture.HOST})
        generated_config = fixture.put(base / "bootstrap.seed.toml", "inert generated seed config")
        stage2 = fixture.put(self.f.root / "build/inert-proof/bin/trustc", "inert proof compiler; never executed")
        paths = {}
        for key in ("surface_manifest", "config_manifest", "library_manifest", "mint_tools_manifest", "seed_dylib_manifest"):
            paths[key] = fixture.write(base / (key + ".json"), {})
        cargo = fixture.write(base / "cargo-home-inputs.json", {"source": self.record["cargo_source"]})
        lean = fixture.write(base / "lean-inputs.json", self.f.lean())
        receipt = fixture.put(base / "seed-mint", "schema=inert-unit-fixture\n")
        return {"root": self.f.root, "input_manifest": input_manifest, "output": base / "final.json",
                "config": generated_config, "source_config": self.f.config, "stage2": stage2,
                "source_date_epoch": 1000, "path_manifest": Path(self.record["path_manifest"]),
                "library_path": "", "seed_dylib_path": "", "mint_receipt": receipt,
                "cargo_home_manifest": cargo, "clean_lean_manifest": lean,
                "clean_lean_lib": self.f.lean_file.parent, "clean_lean_manifest_sha256": recovery.digest(lean), **paths}


class RetainedAuditContextTests(unittest.TestCase):
    """The common tail accepts retained inputs only with a separately audited receipt."""
    def setUp(self):
        ContinuationContextTests.setUp(self)
        self.f = fixture.AuditFixture(self.f.base / "retained")
        self.f.engine = recovery.engine_identity(support)
        record = self.f.inspect_audit()
        output = self.f.evidence / "mint-continuation-context-stage-provenance.json"
        def finish(*args, **kwargs):
            fixture.write(kwargs["receipt_path"], {**self.f.provenance, "status": "internal-release-ready", "errors": []})
        self.f.support.finish_mint_stage_evidence = finish
        self.record = recovery.prepare_at_provenance(record, output, support=self.f.support, owner=self.f.owner)
        self.record_path = self.f.evidence / "prepared-record.json"
        self.save()
        self.selectors.update(config=self.f.config, clean_lean_lib=self.f.lean_file.parent,
                              ddc_seed=self.f.oracle, cargo_source=self.f.base / "immutable-cargo", python=self.f.helper)

    save = ContinuationContextTests.save
    context = ContinuationContextTests.context
    refuses = ContinuationContextTests.refuses

    def test_retained_mode_binds_external_acceptance_without_rewriting_rejection(self):
        record = self.context()
        self.assertTrue(record["original_work_retained"])
        self.assertTrue(record["original_private_cargo_retained"])
        self.assertFalse(record["qualification"])
        self.assertEqual(recovery.document(self.f.stage / "tool-provenance.json")["status"], "rejected")

    def test_changed_external_audit_and_original_capture_refuse(self):
        path = Path(self.record["stage_provenance_path"])
        path.write_bytes(path.read_bytes() + b" ")
        self.refuses("JSON input changed")

    def test_coherently_rehashed_rejected_external_audit_is_not_accepted(self):
        path = Path(self.record["stage_provenance_path"])
        doc = recovery.document(path); doc.update(status="rejected", errors=["audit failed"])
        fixture.write(path, doc)
        self.record["evidence_sha256"]["stage_provenance"] = recovery.digest(path)
        self.save()
        self.refuses("not an accepted mint of this product")

    def test_retained_mode_cannot_claim_a_fresh_absent_cargo_namespace(self):
        self.record["cargo_home_absent_for_fresh_inputs"] = True
        self.save()
        self.refuses("prepared, unqualified phase-split")


if __name__ == "__main__":
    unittest.main()
