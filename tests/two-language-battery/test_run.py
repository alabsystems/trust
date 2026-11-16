#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0 OR MIT

"""Fail-closed regression tests for the two-language battery runner."""

from __future__ import annotations

import importlib.util
import contextlib
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


RUNNER_PATH = Path(__file__).with_name("run.py")
SPEC = importlib.util.spec_from_file_location("two_language_battery_run", RUNNER_PATH)
assert SPEC is not None and SPEC.loader is not None
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


def sealed_stamp() -> dict:
    return {
        "rustc_vV_exit_code": 0,
        "toolchain_binary": "trustc",
        "trust_brand_present": True,
        "trustc_sha256": "a" * 64,
        "tippy_version_exit_code": 0,
        "tippy_driver_sha256": "b" * 64,
        "toolchain_matches_head": True,
        "repo_clean": True,
        "submodules_clean": True,
    }


class IrArtifactEvidenceTests(unittest.TestCase):
    """Exercise the real artifact reader using synthetic compiler publications."""

    BOTH = "rustcc fn @trust_battery_rust_fn() {}\nrustcc fn @trust_battery_island_def() {}\n"
    RUST_ONLY = "rustcc fn @trust_battery_rust_fn() {}\n"

    def artifacts(self, fixture: str, files: dict[str, str | bytes]) -> dict:
        source = runner.BATTERY_DIR / "lane-e-ir-spine" / fixture

        def publish(argv: list[str], **_kwargs) -> subprocess.CompletedProcess:
            crate = argv[argv.index("--crate-name") + 1]
            target = Path(next(arg.removeprefix("-Ztrust-dump=ir:")
                               for arg in argv if arg.startswith("-Ztrust-dump=ir:")))
            for name, contents in files.items():
                path = target / name.replace("CRATE", crate)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(contents.encode() if isinstance(contents, str) else contents)
            return subprocess.CompletedProcess(argv, 0, stdout="", stderr="")

        with (
            mock.patch.object(runner, "_trustc_cmd", return_value=["synthetic-compiler"]),
            mock.patch.object(runner.subprocess, "run", side_effect=publish),
        ):
            return runner.run_one(source, 1)

    @staticmethod
    def coverage() -> str:
        return json.dumps({"clean_origin": {
            "recorded": True,
            "emitted": [{"def_path": "m::trust_battery_linked_def", "func_id": 7, "def_index": 31}],
            "linked": [{"target_func_id": 7, "source_def_index": 31,
                        "decl_func_id": 2, "edges_repointed": 1}],
        }})

    def test_noncanonical_artifacts_cannot_supply_language_markers(self) -> None:
        for name in ("CRATE.trust-ir.bin", "CRATE.trust-ir.coverage.json",
                     "CRATE.trust-ir.txt.tmp", "unrelated.trust-ir.txt",
                     "nested/CRATE.trust-ir.txt"):
            with self.subTest(artifact=name):
                result = self.artifacts("e1_both_languages_in_ir.rs", {name: self.BOTH})
                self.assertEqual(result["verdict"], "ir-no-artifact")
                self.assertEqual(result["ir_artifact_count"], 0)
                self.assertFalse(result["battery_ok"])

    def test_sidecar_marker_does_not_fill_missing_lean_body(self) -> None:
        result = self.artifacts("e1_both_languages_in_ir.rs", {
            "CRATE.trust-ir.txt": self.RUST_ONLY,
            "CRATE.trust-ir.coverage.json": json.dumps({"def_path": "trust_battery_island_def"}),
        })
        self.assertEqual(result["verdict"], "ir-rust-only")
        self.assertFalse(result["lean_in_ir"])
        self.assertFalse(result["battery_ok"])

    def test_canonical_text_is_the_single_marker_artifact(self) -> None:
        result = self.artifacts("e1_both_languages_in_ir.rs", {
            "CRATE.trust-ir.txt": self.BOTH,
            "CRATE.trust-ir.bin": self.BOTH.encode(),
            "CRATE.coverage.json": "{}",
        })
        self.assertEqual(result["verdict"], "ir-carries-both-languages")
        self.assertEqual(result["ir_module_artifacts"], ["e1_both_languages_in_ir.trust-ir.txt"])
        self.assertEqual(result["ir_artifact_count"], 1)
        self.assertTrue(result["battery_ok"])
        self.assertEqual(len(result["ir_artifacts"]), 3)

    def test_binary_or_sidecar_cannot_supply_call_spelling(self) -> None:
        for name in ("CRATE.trust-ir.bin", "CRATE.trust-ir.coverage.json"):
            with self.subTest(artifact=name):
                result = self.artifacts("e2_rust_calls_clean_in_ir.rs", {
                    "CRATE.trust-ir.txt": "rustcc fn @caller() {}\n",
                    "CRATE.coverage.json": self.coverage(),
                    name: 'call @func.7(',
                })
                self.assertEqual(result["verdict"], "ir-clean-declared-only")
                self.assertFalse(result["clean_call_in_text"])
                self.assertFalse(result["battery_ok"])

    def test_unrelated_coverage_cannot_supply_linkage(self) -> None:
        for name in ("unrelated.coverage.json", "nested/CRATE.coverage.json"):
            with self.subTest(artifact=name):
                result = self.artifacts("e2_rust_calls_clean_in_ir.rs", {
                    "CRATE.trust-ir.txt": "rustcc fn @caller() { call @func.7(%0) }\n",
                    name: self.coverage(),
                })
                self.assertEqual(result["verdict"], "ir-no-clean-row")
                self.assertFalse(result["battery_ok"])

    def test_canonical_text_and_same_crate_coverage_still_supply_linkage(self) -> None:
        result = self.artifacts("e2_rust_calls_clean_in_ir.rs", {
            "CRATE.trust-ir.txt": "rustcc fn @caller() { call @func.7(%0) }\n",
            "CRATE.trust-ir.bin": b"binary call data",
            "CRATE.coverage.json": self.coverage(),
        })
        self.assertEqual(result["verdict"], "ir-links-clean-origin")
        self.assertEqual(result["ir_artifact_count"], 1)
        self.assertTrue(result["battery_ok"])


class BatteryRunnerTests(unittest.TestCase):
    def test_complete_diagnostics_survive_storage_without_changing_verdicts(self) -> None:
        source = runner.BATTERY_DIR / "lane-a-rust" / "a3_NEG_false_ensures.rs"
        stdout = "first stdout line\n" + "output detail\n" * 1000 + "last stdout line\n"
        for prefix, verdict, battery_ok in (
            ("Trust verification: 0 proved, 1 failed, 0 unknown", "reject-correct", True),
            ("error: [postcondition] UNKNOWN (trust-mc): unsupported", "reject-by-frontier", False),
        ):
            stderr = prefix + f"\n --> {source}:1:1\n" + "engine detail\n" * 1000 + "last diagnostic\n"
            with self.subTest(verdict=verdict):
                process = subprocess.CompletedProcess(["fake-trustc"], 1, stdout=stdout, stderr=stderr)
                with (
                    mock.patch.object(runner, "_trustc_cmd", return_value=["fake-trustc"]),
                    mock.patch.object(runner.subprocess, "run", return_value=process),
                ):
                    result = runner.run_one(source, 1, source)
                self.assertEqual(result["stdout"], stdout)
                self.assertEqual(result["stderr"], stderr.replace(str(runner.REPO_ROOT), "<repo>"))
                self.assertGreater(len(result["stderr"]), 8000)
                self.assertFalse(result["stdout_truncated"])
                self.assertFalse(result["stderr_truncated"])
                self.assertTrue(result["streams_complete"])
                self.assertEqual(result["verdict"], verdict)
                self.assertEqual(result["battery_ok"], battery_ok)
                self.assertNotIn("_full_stderr", result)

    def test_timeout_retains_observed_text_without_crediting_partial_proofs(self) -> None:
        source = runner.BATTERY_DIR / "lane-a-rust" / "a3_NEG_false_ensures.rs"
        stdout = "observed λ output\n"
        stderr = f"Trust verification: 0 proved, 1 failed, 0 unknown\n --> {source}:1:1\n"
        for binary in (False, True):
            with self.subTest(binary=binary):
                timeout = subprocess.TimeoutExpired(
                    ["fake-trustc"], 1,
                    output=stdout.encode() if binary else stdout,
                    stderr=stderr.encode() if binary else stderr,
                )
                with (
                    mock.patch.object(runner, "_trustc_cmd", return_value=["fake-trustc"]),
                    mock.patch.object(runner.subprocess, "run", side_effect=timeout),
                ):
                    result = runner.run_one(source, 1, source)
                self.assertEqual(result["stdout"], stdout)
                self.assertEqual(result["stderr"], stderr.replace(str(runner.REPO_ROOT), "<repo>"))
                self.assertIsNone(result["exit_code"])
                self.assertEqual(result["error"], "TIMEOUT after 1s")
                self.assertEqual(result["verdict"], "timeout")
                self.assertFalse(result["battery_ok"])
                self.assertFalse(result["streams_complete"])

    def test_aggregate_refusal_is_not_a_successful_negative_control(self) -> None:
        for diagnostic in (
            "error: strict verification failed",
            "error: safety verification incomplete",
            "error: 2 obligation(s) were not discharged",
            "error: obligations were not fully verified",
            "error: obligations were not proved",
            "error: undischarged obligation",
        ):
            with self.subTest(diagnostic=diagnostic):
                self.assertEqual(runner.classify_failure(diagnostic), "unclassified")

    def test_missing_authority_unknown_and_timeout_are_not_refutations(self) -> None:
        for diagnostic in (
            "error: [hardened_panic_boundary] UNKNOWN (trust-mc): "
            "Proved label lacked exact kernel/native proof authority",
            "error: [arithmetic_overflow_add] TIMED_OUT (interval): timeout",
            "error: certification audit failed: native proof evidence unavailable",
            "error: proof failed the strict Clean certification audit",
            "Trust verification: 1 proved, 0 failed, 0 unknown, 1 timed out",
            "Trust verification: 0 proved, 0 failed, 2 unknown, 0 timed out",
        ):
            with self.subTest(diagnostic=diagnostic):
                self.assertEqual(
                    runner.classify_failure(diagnostic + "\nerror: strict verification failed"),
                    "frontier",
                )

    def test_actual_refutations_and_kernel_term_rejections_still_count(self) -> None:
        for diagnostic in (
            "Trust verification: 1 proved, 1 failed, 2 unknown, 3 timed out",
            "error: [arithmetic_overflow_add] FAILED (ay): counterexample value = 255",
            'error: Clean island declaration rejected: TypeMismatch { expected: "Nat.le 1 0", actual: "Nat.le 0 0" }',
            'error: citation `bad` failed the strict Clean statement/certification audit: '
            'strict certification audit failed: [TermRejected { error: "TypeMismatch { expected: Pi(...), inferred: Pi(...) }" }]',
            # cb1/B2 (2026-09-28): the refuted postcondition goal leads the head.
            'error: citation `bad` failed the strict Clean statement/certification audit against '
            'this postcondition with `result` bound to the imported definition of `f`: '
            'strict certification audit failed: [TermRejected { error: "TypeMismatch { expected: Pi(...), inferred: Pi(...) }" }]',
            "  = note: [postcondition] FAILED (ay): counterexample value = 255",
            "  = note: [overflow:add] FAILED (ay-in-process); counterexample: _0 = 0, value = 255",
        ):
            with self.subTest(diagnostic=diagnostic):
                self.assertEqual(runner.classify_failure(diagnostic), "refutation")
        self.assertEqual(
            runner.obligation_counts(
                "Trust verification: 2 proved, 1 failed, 3 unknown, 4 timed out\n"
                "Trust verification: 0 proved, 5 failed, 6 unknown"
            ),
            (6, 9, 4),
        )

    def test_echoed_verdict_words_do_not_supply_refutation_evidence(self) -> None:
        self.assertEqual(
            runner.classify_failure(
                "error: strict verification failed\n"
                " --> /tmp/counterexample/fixture.rs:1:1\n"
                "1 | // counterexample: kernel rejected, [FAILED]\n"
            ),
            "unclassified",
        )

    def test_elaboration_rejection_is_not_a_terminal_kernel_verdict(self) -> None:
        source = runner.BATTERY_DIR / "lane-b-lean" / "b2_NEG_bad_proof.rs"
        diagnostic = (
            'error: Clean island declaration rejected: ElaborationTypeMismatch '
            '{ expected: "Nat.le 1 0", actual: "Nat.le 0 0" }'
        )
        for note in (
            "",
            "\n  = note: the island was parsed by the Clean parser and checked by the "
            "Clean CIC kernel during this build (two-language design E10)",
        ):
            with self.subTest(legacy_note=bool(note)):
                process = subprocess.CompletedProcess(
                    ["fake-trustc"], 1, stdout="", stderr=diagnostic + note,
                )
                with (
                    mock.patch.object(runner, "_trustc_cmd", return_value=["fake-trustc"]),
                    mock.patch.object(runner.subprocess, "run", return_value=process),
                ):
                    result = runner.run_one(source, 1, source)
                self.assertNotEqual(result["verdict"], "reject-correct")
                self.assertFalse(result["battery_ok"])

    def test_unknown_compiler_exit_cannot_pass_the_negative_fixture(self) -> None:
        source = runner.BATTERY_DIR / "lane-a-rust" / "a3_NEG_false_ensures.rs"
        process = subprocess.CompletedProcess(
            ["fake-trustc"], 1, stdout="",
            stderr="error: [postcondition] UNKNOWN (trust-mc): proof unavailable\n"
                   "error: strict verification failed",
        )
        with (
            mock.patch.object(runner, "_trustc_cmd", return_value=["fake-trustc"]),
            mock.patch.object(runner.subprocess, "run", return_value=process),
        ):
            result = runner.run_one(source, 1, source)
        self.assertEqual(result["verdict"], "reject-by-frontier")
        self.assertFalse(result["battery_ok"])

    def test_crashing_driver_cannot_reuse_an_earlier_refutation(self) -> None:
        source = runner.BATTERY_DIR / "lane-a-rust" / "a3_NEG_false_ensures.rs"
        for code in (101, 134, 137, -9, 2):
            with self.subTest(code=code):
                process = subprocess.CompletedProcess(
                    ["fake-trustc"], code, stdout="",
                    stderr="Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out",
                )
                with (
                    mock.patch.object(runner, "_trustc_cmd", return_value=["fake-trustc"]),
                    mock.patch.object(runner.subprocess, "run", return_value=process),
                ):
                    result = runner.run_one(source, 1, source)
                self.assertEqual(result["verdict"], "driver-failed")
                self.assertFalse(result["battery_ok"])
        self.assertEqual(
            runner.classify_failure(
                "Trust verification: 0 proved, 1 failed, 0 unknown\n"
                "error: internal compiler error: compiler panicked"
            ),
            "compiler-failure",
        )

    def test_generic_kernel_wrappers_and_counterexample_nouns_are_not_verdicts(self) -> None:
        source = runner.BATTERY_DIR / "lane-a-rust" / "a3_NEG_false_ensures.rs"
        for diagnostic in (
            'citation p failed the strict Clean statement/certification audit: '
            '[TermRejected { error: "HeartbeatExceeded { limit:100 }" }]',
            "Clean island declaration rejected: InternalInvariant(broken elaboration)",
            "Clean island declaration rejected: UnknownIdent(x)",
            "Clean island declaration rejected: UnknownConstant(x)",
            "error: declaration rejected: heartbeat limit exceeded while checking TypeMismatch",
            "error: declaration rejected: DeclarationBudgetExhausted",
            "error: declaration rejected: declaration budget exhausted",
            "error: declaration rejected: ExcessiveMemory",
            "error: declaration rejected: excessive memory consumption detected",
            "error: declaration rejected: DeepRecursion",
            "error: declaration rejected: deep recursion detected during type checking",
            "error: declaration rejected: type checking interrupted",
            "error: declaration rejected: CrossValidationFailure(TypeMismatch)",
            "error: declaration rejected: Cross-validation failure: type mismatch",
            "error: TermRejected: resource limit reached",
            "error: counterexample replay evidence is missing",
            "error: counterexample: candidate model rejected by independent validation",
            "error: kernel rejected the proof request without checking the term",
            "warning: unexpected cfg condition value: `TypeMismatch`\nerror: strict verification failed",
            "warning: use of deprecated function `demo`: [FAILED]\nerror: strict verification failed",
            "warning: use of deprecated function `demo`: Trust verification: 0 proved, 1 failed, 0 unknown\nerror: strict verification failed",
            "warning: use of deprecated function `demo`: [postcondition] FAILED (ay): fake\nerror: strict verification failed",
            "error: Clean island declaration rejected: TypeMismatch { expected: \"Bool (option 'trace.compiler')\", actual: \"Nat\" }",
        ):
            with self.subTest(diagnostic=diagnostic):
                process = subprocess.CompletedProcess(
                    ["fake-trustc"], 1, stdout="", stderr=diagnostic,
                )
                with (
                    mock.patch.object(runner, "_trustc_cmd", return_value=["fake-trustc"]),
                    mock.patch.object(runner.subprocess, "run", return_value=process),
                ):
                    result = runner.run_one(source, 1, source)
                self.assertNotEqual(result["verdict"], "reject-correct")
                self.assertFalse(result["battery_ok"])

    def test_current_canonical_inventory_is_exact(self) -> None:
        files = runner.discover(None)
        captured = runner.capture_fixture_inventory(files, canonical=True)
        # Derived, not hardcoded — this literal read 25 while the manifest
        # held 26, and only stayed unnoticed because the inventory check
        # above RAISES before this line is reached.
        self.assertEqual(len(captured), len(runner.CANONICAL_FIXTURES))
        self.assertEqual(len(runner.fixture_snapshot(captured)), 64)

    def test_deleted_fixture_cannot_shrink_canonical_inventory(self) -> None:
        files = runner.discover(None)
        with self.assertRaisesRegex(RuntimeError, r"reviewed \d+-fixture manifest"):
            runner.capture_fixture_inventory(files[:-1], canonical=True)

    def test_duplicate_required_directive_is_rejected(self) -> None:
        text = """\
//@ battery-lane: A-rust
//@ battery-lane: B-lean
//@ battery-expect: pass
//@ battery-flags: --crate-type=lib
"""
        with self.assertRaisesRegex(RuntimeError, "exactly one battery-lane"):
            runner.validate_fixture_directives(Path("duplicate.rs"), text)

    def test_fixture_snapshot_changes_with_exact_bytes(self) -> None:
        path = runner.discover(None)[0]
        original = {path: path.read_bytes()}
        changed = {path: original[path] + b"\n"}
        self.assertNotEqual(
            runner.fixture_snapshot(original),
            runner.fixture_snapshot(changed),
        )

    def test_relative_explicit_trustc_and_tippy_share_one_stage2(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            bindir = root / "stage2" / "bin"
            bindir.mkdir(parents=True)
            trustc = bindir / "trustc"
            tippy = bindir / "tippy-driver"
            trustc.write_text("#!/bin/sh\n", encoding="utf-8")
            tippy.write_text("#!/bin/sh\n", encoding="utf-8")
            trustc.chmod(0o755)
            tippy.chmod(0o755)

            runner._trustc_path.cache_clear()
            try:
                with (
                    mock.patch.object(runner, "REPO_ROOT", root),
                    mock.patch.dict(
                        os.environ,
                        {"TRUST_PROBE_TRUSTC": "stage2/bin/trustc"},
                    ),
                ):
                    self.assertEqual(runner._trustc_path(), trustc.resolve())
                    self.assertEqual(runner._tippy_path(), tippy.resolve())
            finally:
                runner._trustc_path.cache_clear()

    def test_nonzero_or_unbranded_toolchain_never_seals(self) -> None:
        for field, value in (
            ("rustc_vV_exit_code", 1),
            ("toolchain_binary", "rustc"),
            ("trust_brand_present", False),
            ("tippy_version_exit_code", 134),
            ("repo_clean", False),
            ("submodules_clean", False),
        ):
            with self.subTest(field=field):
                stamp = sealed_stamp()
                stamp[field] = value
                self.assertFalse(runner.is_toolchain_sealed(stamp))
        self.assertTrue(runner.is_toolchain_sealed(sealed_stamp()))

    def test_every_submodule_drift_prefix_is_rejected(self) -> None:
        for prefix in ("+", "-", "U"):
            with self.subTest(prefix=prefix):
                line = f"{prefix}{'a' * 40} first-party/example"
                self.assertEqual(runner.submodule_drift_lines(line), [line])
        clean = f" {'a' * 40} first-party/example"
        self.assertEqual(runner.submodule_drift_lines(clean), [])

    def test_postflight_identity_detects_binary_and_checkout_drift(self) -> None:
        before = {
            "rustc_vV_exit_code": 0,
            "rustc_vV": "version",
            "trustc_sha256": "a",
            "toolchain_commit": "head",
            "toolchain_binary": "trustc",
            "trust_brand_present": True,
            "tippy_version_exit_code": 0,
            "tippy_version": "version",
            "tippy_driver_sha256": "b",
            "repo_head": "head",
            "repo_clean": True,
            "submodules_clean": True,
            "toolchain_matches_head": True,
            "toolchain_sealed": True,
        }
        self.assertTrue(runner.same_measurement_identity(before, dict(before)))
        for field in ("trustc_sha256", "tippy_driver_sha256", "repo_head"):
            with self.subTest(field=field):
                after = dict(before)
                after[field] = "changed"
                self.assertFalse(runner.same_measurement_identity(before, after))

    def test_tippy_nonzero_cannot_impersonate_known_target_verdict(self) -> None:
        source = runner.BATTERY_DIR / "lane-d-legacy" / "d1_kani_contracts.rs"
        with tempfile.TemporaryDirectory() as td:
            snapshot = Path(td) / source.name
            snapshot.write_bytes(source.read_bytes())
            process = subprocess.CompletedProcess(
                ["fake-tippy"],
                1,
                stdout="legacy spec_sugar clean {",
                stderr="driver crashed",
            )
            with (
                mock.patch.object(runner, "_tippy_cmd", return_value=["fake-tippy"]),
                mock.patch.object(runner.subprocess, "run", return_value=process),
            ):
                result = runner.run_one(source, 1, snapshot)
        self.assertEqual(result["verdict"], "tippy-compile-failed")
        self.assertFalse(result["battery_ok"])

    def test_symlink_alias_resolves_to_canonical_output(self) -> None:
        canonical = (runner.BATTERY_DIR / "results.json").resolve()
        with tempfile.TemporaryDirectory() as td:
            alias = Path(td) / "alias.json"
            alias.symlink_to(canonical)
            self.assertEqual(alias.resolve(), canonical)
            with self.assertRaisesRegex(ValueError, "--filter requires"):
                runner.validate_output_policy(
                    "lane-c",
                    alias.resolve(),
                    canonical,
                    explicit_trustc=True,
                )

    def test_atomic_write_failure_preserves_existing_scorecard(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "results.json"
            output.write_text("old scorecard\n", encoding="utf-8")
            with (
                mock.patch.object(
                    runner.json,
                    "dump",
                    side_effect=RuntimeError("serialization failed"),
                ),
                self.assertRaisesRegex(RuntimeError, "serialization failed"),
            ):
                runner.write_scorecard_atomic(output, {"new": True})
            self.assertEqual(output.read_text(encoding="utf-8"), "old scorecard\n")
            self.assertEqual(list(Path(td).iterdir()), [output])

    def test_external_canonical_mode_keeps_filter_and_explicit_tool_guards(self) -> None:
        canonical = (runner.BATTERY_DIR / "results.json").resolve()
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "fresh.json"
            runner.validate_output_policy(None, output, canonical, True, canonical=True)
            for filter_pat, explicit_tool in [("lane-c", True), (None, False)]:
                with self.subTest(filter=filter_pat, explicit_tool=explicit_tool):
                    with self.assertRaises(ValueError):
                        runner.validate_output_policy(
                            filter_pat, output, canonical, explicit_tool, canonical=True
                        )

    def test_external_canonical_output_refuses_source_and_source_aliases(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "source"
            root.mkdir()
            alias = Path(td) / "alias"
            alias.symlink_to(root, target_is_directory=True)
            for output in [root / "new.json", alias / "new.json"]:
                with self.subTest(output=output), self.assertRaisesRegex(ValueError, "outside"):
                    runner.validate_external_canonical_output(output, root)
            runner.validate_external_canonical_output(Path(td) / "new.json", root)

    def test_external_canonical_output_requires_new_file_and_existing_parent(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "source"
            root.mkdir()
            existing = Path(td) / "existing.json"
            existing.write_text("retained")
            dangling = Path(td) / "dangling.json"
            dangling.symlink_to(Path(td) / "absent.json")
            for output in [existing, dangling]:
                with self.subTest(output=output), self.assertRaisesRegex(ValueError, "new file"):
                    runner.validate_external_canonical_output(output, root)
            with self.assertRaisesRegex(ValueError, "existing output directory"):
                runner.validate_external_canonical_output(Path(td) / "missing/new.json", root)
            self.assertEqual(existing.read_text(), "retained")

    def test_create_only_publication_cannot_overwrite_a_racing_file_or_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            old = Path(td) / "old.json"
            old.write_text("retained")
            alias = Path(td) / "alias.json"
            alias.symlink_to(old)
            for output in [old, alias]:
                with self.subTest(output=output), self.assertRaises(FileExistsError):
                    runner.write_scorecard_atomic(output, {"new": True}, create_only=True)
            self.assertEqual(old.read_text(), "retained")
            self.assertTrue(alias.is_symlink())
            self.assertEqual(set(Path(td).iterdir()), {old, alias})
            fresh = Path(td) / "fresh.json"
            runner.write_scorecard_atomic(fresh, {"new": True}, create_only=True)
            self.assertEqual(json.loads(fresh.read_text()), {"new": True})

    def test_canonical_cli_refuses_missing_output_and_unsealed_escape_before_tools(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            cases = [
                ["--canonical"],
                ["--canonical", "--output", str(Path(td) / "fresh.json"),
                 "--allow-unsealed-toolchain"],
                ["--allow-unsealed-toolchain"],
            ]
            for arguments in cases:
                with self.subTest(arguments=arguments), mock.patch.object(
                    sys, "argv", [str(RUNNER_PATH), *arguments]
                ), mock.patch.object(runner, "toolchain_stamp") as stamp, contextlib.redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit) as failure:
                        runner.main()
                    self.assertEqual(failure.exception.code, 2)
                    stamp.assert_not_called()

    def run_external_canonical(self, output: Path, **patches) -> tuple[int, dict]:
        """Real runner orchestration/publication; mocked compiler outcomes only."""
        def measured_row(path, _timeout, _snapshot):
            return {"file": str(path), "lane": "A-rust", "verdict": "pass", "battery_ok": True}

        physical_trustc = (runner.REPO_ROOT / "build/host/stage2/bin/trustc").resolve()
        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.object(sys, "argv", [str(RUNNER_PATH),
                "--canonical", "--output", str(output)]))
            stack.enter_context(mock.patch.dict(os.environ, {"TRUST_PROBE_TRUSTC": str(physical_trustc)}))
            stack.enter_context(mock.patch.object(runner, "_trustc_path", return_value=physical_trustc))
            stack.enter_context(mock.patch.object(runner, "toolchain_stamp",
                return_value=dict(sealed_stamp(), toolchain_sealed=True)))
            stack.enter_context(mock.patch.object(runner, "run_one", side_effect=measured_row))
            inventory = stack.enter_context(mock.patch.object(runner, "capture_fixture_inventory",
                wraps=runner.capture_fixture_inventory))
            for name, value in patches.items():
                stack.enter_context(mock.patch.object(runner, name, **value))
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            stack.enter_context(contextlib.redirect_stderr(io.StringIO()))
            code = runner.main()
            return code, {"inventory_calls": inventory.call_args_list}

    def test_external_canonical_runs_the_exact_reviewed_population_twice_without_source_writes(self) -> None:
        canonical = runner.BATTERY_DIR / "results.json"
        original = canonical.read_bytes()
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "fresh.json"
            code, observations = self.run_external_canonical(output)
            self.assertEqual(code, 0)
            document = json.loads(output.read_text())
            self.assertEqual(document["measurement_scope"], "canonical-reviewed-battery")
            self.assertEqual(document["summary"]["total"], len(runner.CANONICAL_FIXTURES))
            self.assertEqual(len(observations["inventory_calls"]), 2)
            self.assertTrue(all(call.args[1] is True for call in observations["inventory_calls"]))
            self.assertTrue(document["toolchain"]["end_identity_revalidated"])
            self.assertEqual(canonical.read_bytes(), original)

    def test_external_canonical_rejects_foreign_physical_stage2_without_output(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "fresh.json"
            code, _ = self.run_external_canonical(output,
                _trustc_path={"return_value": Path(td) / "other/stage2/bin/trustc"})
            self.assertEqual(code, 2)
            self.assertFalse(output.exists())

    def test_external_canonical_rejects_stale_toolchain_without_output(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "fresh.json"
            stale = dict(sealed_stamp(), toolchain_sealed=False, toolchain_matches_head=False)
            code, _ = self.run_external_canonical(output, toolchain_stamp={"return_value": stale})
            self.assertEqual(code, 2)
            self.assertFalse(output.exists())

    def test_external_canonical_rejects_missing_fixture_without_output(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "fresh.json"
            code, _ = self.run_external_canonical(output,
                discover={"return_value": runner.discover(None)[:-1]})
            self.assertEqual(code, 2)
            self.assertFalse(output.exists())

    def test_external_canonical_rechecks_identity_before_publication(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "fresh.json"
            before = dict(sealed_stamp(), toolchain_sealed=True)
            after = dict(before, trustc_sha256="changed")
            code, _ = self.run_external_canonical(output,
                toolchain_stamp={"side_effect": [before, after]})
            self.assertEqual(code, 2)
            self.assertFalse(output.exists())

    def test_external_canonical_cli_does_not_follow_an_existing_dangling_output(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            target = Path(td) / "absent.json"
            alias = Path(td) / "alias.json"
            alias.symlink_to(target)
            with mock.patch.object(sys, "argv", [str(RUNNER_PATH), "--canonical",
                "--output", str(alias)]), mock.patch.object(runner, "toolchain_stamp") as stamp, \
                    contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as failure:
                    runner.main()
                self.assertEqual(failure.exception.code, 2)
                stamp.assert_not_called()
            self.assertFalse(target.exists())
            self.assertTrue(alias.is_symlink())


class LaneDLeanSuggestionTests(unittest.TestCase):
    """Lane D credits a SUGGESTED Lean artifact, never prose that names Lean."""

    # d1's complete tippy stderr, verbatim from the canonical run on stage2
    # `5ab8dcccfcb` (2026-09-27; reports/2026-09-27-new-pack-5ab8dcccfcb-measured/
    # results.json). Every suggestion is a Rust clause; the only `clean {` is the
    # `#[kani::proof]` NOTE, which the old marker list scored as Lean emission.
    MEASURED_D1_STDERR = """warning: legacy contracts attribute; Trust supports first-class signature clauses
  --> <repo>/tests/two-language-battery/lane-d-legacy/d1_kani_contracts.rs:42:1
   |
42 | #[kani::requires(x < 1000)]
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^ help: move the predicate into the signature: `fn f(..) requires x < 1000 { .. }`
   |
   = help: for further information visit https://rust-lang.github.io/rust-clippy/master/index.html#trust_legacy_spec_sugar
   = note: `#[warn(clippy::trust_legacy_spec_sugar)]` on by default

warning: legacy contracts attribute; Trust supports first-class signature clauses
  --> <repo>/tests/two-language-battery/lane-d-legacy/d1_kani_contracts.rs:43:1
   |
43 | #[kani::ensures(|r| *r >= x)]
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ help: move the predicate into the signature: `fn f(..) ensures |r| *r >= x { .. }`
   |
   = help: for further information visit https://rust-lang.github.io/rust-clippy/master/index.html#trust_legacy_spec_sugar

warning: legacy contracts attribute; Trust supports first-class signature clauses
  --> <repo>/tests/two-language-battery/lane-d-legacy/d1_kani_contracts.rs:48:1
   |
48 | #[kani::requires(n > 0)]
   | ^^^^^^^^^^^^^^^^^^^^^^^^ help: move the predicate into the signature: `fn f(..) requires n > 0 { .. }`
   |
   = help: for further information visit https://rust-lang.github.io/rust-clippy/master/index.html#trust_legacy_spec_sugar

warning: legacy contracts attribute; Trust supports first-class signature clauses
  --> <repo>/tests/two-language-battery/lane-d-legacy/d1_kani_contracts.rs:49:1
   |
49 | #[kani::ensures(|r| *r <= n)]
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ help: move the predicate into the signature: `fn f(..) ensures |r| *r <= n { .. }`
   |
   = help: for further information visit https://rust-lang.github.io/rust-clippy/master/index.html#trust_legacy_spec_sugar

warning: legacy kani proof attribute; use `#[kani::harness]`
  --> <repo>/tests/two-language-battery/lane-d-legacy/d1_kani_contracts.rs:54:1
   |
54 | #[kani::proof]
   | ^^-----------^
   |   |
   |   help: use the native harness attribute: `kani::harness`
   |
   = note: `kani::harness` is an ingestion-lane spelling and carries no proof authority; Trust's authoritative surfaces are `requires`/`ensures` signature clauses and `clean { .. }` Lean islands
   = help: for further information visit https://rust-lang.github.io/rust-clippy/master/index.html#trust_legacy_spec_sugar

warning: 5 warnings emitted

"""

    INLINE_ISLAND_HELP = (
        "warning: legacy contracts attribute; Trust supports first-class signature clauses\n"
        "  --> <repo>/tests/two-language-battery/lane-d-legacy/d1_kani_contracts.rs:42:1\n"
        "   |\n"
        "42 | #[kani::requires(x < 1000)]\n"
        "   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^ help: state the predicate as a Lean island: "
        "`clean { def bump_pre (x : Nat) : Prop := x < 1000 }`\n"
    )

    MULTILINE_DECLARATION_HELP = (
        "warning: legacy contracts attribute; Trust supports first-class signature clauses\n"
        "  --> <repo>/tests/two-language-battery/lane-d-legacy/d1_kani_contracts.rs:43:1\n"
        "   |\n"
        "help: state the postcondition in Lean\n"
        "   |\n"
        "43 ~ clean {\n"
        "44 +   theorem bump_ge (x : Nat) : x <= x + 1 := Nat.le_succ x\n"
        "45 + }\n"
        "   |\n"
    )

    def run_tippy(self, stderr: str) -> dict:
        source = runner.BATTERY_DIR / "lane-d-legacy" / "d1_kani_contracts.rs"
        process = subprocess.CompletedProcess(["fake-tippy"], 0, stdout="", stderr=stderr)
        with (
            mock.patch.object(runner, "_tippy_cmd", return_value=["fake-tippy"]),
            mock.patch.object(runner.subprocess, "run", return_value=process),
        ):
            return runner.run_one(source, 1, source)

    def test_measured_d1_note_prose_is_not_lean_emission(self) -> None:
        self.assertIn("`clean { .. }` Lean islands", self.MEASURED_D1_STDERR)
        self.assertEqual(runner.suggested_lean_artifacts(self.MEASURED_D1_STDERR), [])
        result = self.run_tippy(self.MEASURED_D1_STDERR)
        self.assertFalse(result["emits_lean"])
        self.assertEqual(result["lean_suggestions"], [])
        self.assertEqual(result["verdict"], "tippy-fires-but-no-lean")
        self.assertFalse(result["battery_ok"])

    def test_placeholder_island_source_echo_and_notes_are_not_lean_emission(self) -> None:
        for text in (
            "   | ^^^ help: use a Lean island: `clean { .. }`\n",
            "   = help: write the contract as a `clean { … }` island\n",
            "12 | clean { theorem echoed (n : Nat) : n = n := rfl }\n",
            "   = note: suggested: `theorem t (n : Nat) : n = n := rfl`\n",
            "warning: consider `def f (x : Nat) : Nat := x`\n",
            "   | ^^^ help: move the predicate into the signature: "
            "`fn f(..) requires x < 1000 { .. }`\n",
        ):
            with self.subTest(text=text):
                self.assertEqual(runner.suggested_lean_artifacts(text), [])

    def test_suggested_island_or_declaration_is_lean_emission(self) -> None:
        self.assertEqual(
            runner.suggested_lean_artifacts(self.INLINE_ISLAND_HELP),
            ["clean { def bump_pre (x : Nat) : Prop := x < 1000 }"],
        )
        self.assertEqual(
            runner.suggested_lean_artifacts(self.MULTILINE_DECLARATION_HELP),
            ["theorem bump_ge (x : Nat) : x <= x + 1 := Nat.le_succ x"],
        )
        for stderr in (self.INLINE_ISLAND_HELP, self.MULTILINE_DECLARATION_HELP):
            with self.subTest(stderr=stderr):
                result = self.run_tippy(stderr)
                self.assertTrue(result["emits_lean"])
                self.assertEqual(result["verdict"], "tippy-emits-lean")
                self.assertTrue(result["battery_ok"])


if __name__ == "__main__":
    unittest.main()
