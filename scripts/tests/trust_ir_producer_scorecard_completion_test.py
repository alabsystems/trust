#!/usr/bin/env python3
"""Focused, self-executing controls for the Rust producer completion gate."""

from __future__ import annotations

import copy
import importlib.util
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "trust_ir_producer_scorecard.py"


def load_scorecard_module():
    spec = importlib.util.spec_from_file_location("trust_ir_producer_scorecard_completion", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


scorecard = load_scorecard_module()


def complete_aggregate() -> dict:
    """A small internally consistent aggregate satisfying every W0 producer conjunct."""
    return {
        "file_outcomes": {"ok": 2, "compile_fail": 1},
        "validation": {
            "modules_measured": 2,
            "modules_unmeasured": 0,
            "modules_invalid": 0,
            "error_occurrences": 0,
            "class_histogram": {},
        },
        "bodies": {
            "total": 3,
            "lowered_clean": 3,
            "lowered_clean_pct": 100.0,
            "bodies_out_of_fragment": 0,
            "lowered_clean_in_fragment_pct": 100.0,
            "lowered_clean_modelled": 3,
            "lowered_clean_modelled_agreed": 3,
            "lowered_clean_symbolic": 0,
            "lowered_clean_symbolic_agreed": 0,
            "lowered_clean_opaque": 0,
            "lowered_clean_opaque_agreed": 0,
            "opaque_collapse_all": 0,
            "opaque_collapse_all_agreed": 0,
            "lowered_clean_class_unmeasured": 0,
            "agreed": 3,
            "agreed_uninterpreted_callee": 0,
            "divergences": [],
            "divergence_note_histogram": {},
            "by_kind": {"named": 3},
            "clean_by_kind": {"named": 3},
            "note_class_histogram": {"agreed": 3},
            "seam_declaration_blockers": {},
            "reason_tag_histogram": {},
            "single_missing_shape_tag_histogram": {},
            "unsupported_count_per_body_histogram": {"0": 3},
        },
        "partial_bodies_from_flag_induced_failures": {
            "total": 0,
            "lowered_clean": 0,
        },
        "bodies_including_partial": {
            "total": 3,
            "lowered_clean": 3,
            "lowered_clean_pct": 100.0,
        },
        "flag_induced_ice_signatures": {},
        "parse_anomalies": {
            "duplicate_differential_events": 0,
            "duplicate_unsupported_events": 0,
            "unsupported_event_without_differential_event": 0,
        },
    }


def artifact(aggregate: dict | None = None) -> dict:
    return {
        "schema": "trust.trust-ir.producer-scorecard.v1",
        "provenance": {
            "date_utc": "2026-08-31T00:00:00+00:00",
            "repo_head": "a" * 40,
            "repo_describe": "test",
            "trustc_version_verbose": "trustc fixture",
            "rustc_log_filter": scorecard.RUSTC_LOG_FILTER,
            "compile_flags": ["-Z trust-ir-lower"],
            "seed": 1,
        },
        "corpora": {
            "fixture": {
                "sample_meta": None,
                "aggregate": aggregate if aggregate is not None else complete_aggregate(),
                "files": [],
            },
        },
    }


def fixture_subject_stderr() -> str:
    lines = []
    for index in range(3):
        identity = f"DefId(0:{index + 1} ~ fixture::f{index})"
        lines.append(f"trust-ir-lower: body class, def={identity}, symbolic=false, opaque=false, clean=true")
        lines.append(f'trust-ir-lower: differential, def={identity}, equal=true, samples=1, mode=Agreed, note=""')
    lines.append("trust-ir-lower: module validation summary, total=0")
    return "\n".join(lines) + "\n"


def complete_raw_files() -> list[dict]:
    stderr = fixture_subject_stderr()
    bodies, anomalies = scorecard.parse_bodies(stderr)
    return [
        {
            "file": "fixture.rs",
            "outcome": "ok",
            "bodies": bodies,
            "anomalies": anomalies,
            "validation": scorecard.parse_validation(stderr),
        },
        {"file": "excluded.rs", "outcome": "compile_fail", "bodies": []},
    ]


def raw_artifact() -> dict:
    data = artifact(complete_aggregate())
    corpus = data["corpora"]["fixture"]
    corpus["files"] = complete_raw_files()
    corpus["input_census"] = {
        "schema": "trust.trust-ir.producer-input-census.v1",
        "source": "precompile-content-manifest/v1",
        "files": [
            {"file": "fixture.rs", "sha256": "1" * 64, "expected_outcome": "ok"},
            {
                "file": "excluded.rs",
                "sha256": "2" * 64,
                "expected_outcome": "compile_fail",
            },
        ],
    }
    corpus["body_census"] = {
        "schema": "trust.trust-ir.producer-body-census.v1",
        "source": scorecard.BODY_CENSUS_SOURCE,
        "bodies": [
            {"file": "fixture.rs", "def": f"fixture::f{index}", "kind": "named"}
            for index in range(3)
        ],
    }
    add_census_evidence(corpus)
    return data


def compiler_census(input_path, rows, digest, lowering, *, complete=True, edition="2021"):
    header = {"schema": scorecard.CENSUS_SCHEMA, "event": "begin", "input": input_path,
              "compiler_version": "fixture-compiler", "target": "fixture-target",
              "edition": edition, "crate_types": ["Rlib"],
              "direct_lowering": lowering, "verification_enabled": False,
              "scope": "local-hir-body-owners-after-typeck", "reachable_instances": "unmeasured"}
    header["generated_scope"] = "local-typeck-synthetic-coroutine-bodies"
    snapshot = {"schema": scorecard.CENSUS_SCHEMA, "event": "hir_snapshot",
                "body_count": len(rows), "sources": [{"file": input_path, "sha256": digest}],
                "generated_body_count": 0, "generated_bodies": [],
                "bodies": [{"def": row["def"], "kind": row["kind"], "def_kind": "Fn",
                            "def_index": index, "def_path_hash": f"fixture-identity-{index}"}
                           for index, row in enumerate(rows)]}
    lines = [json.dumps(header) + "\n", json.dumps(snapshot) + "\n"]
    if complete:
        footer = {"schema": scorecard.CENSUS_SCHEMA, "event": "complete", "status": "complete",
                  "body_count": len(rows), "sources": snapshot["sources"],
                  "generated_body_count": 0,
                  "other_inputs": {"tracked_files": [], "environment_variables": [],
                                   "proc_macro_io": "unmeasured", "build_environment": "unmeasured",
                                   "external_dependency_closure": "unmeasured"},
                  "snapshot_sha256": hashlib.sha256(lines[1].encode()).hexdigest()}
        lines.append(json.dumps(footer) + "\n")
    return "".join(lines)


def mono_census(input_path, rows, digest, lowering, *, complete=True, edition="2021"):
    census = scorecard.rust_instance_census
    schema = census.SCHEMA_V3
    header = {
        "schema": schema, "event": "begin", "scope": census.SCOPE, "input": input_path,
        "compiler_version": "fixture-compiler", "target": "fixture-target", "edition": edition,
        "direct_lowering": lowering, "verification_enabled": False,
        "collection_strategy": "lazy", "optimization": "No", "incremental": False,
        "codegen_requested": True,
        "identity_scheme": "rustc-stable-mono-item-fingerprint-128-diagnostic-only",
        "dependency_identity_scheme": census.DEPENDENCY_IDENTITY,
        "dependency_scope": census.DEPENDENCY_SCOPE,
        "eager_const_root_scope": census.EAGER_CONST_ROOT_SCOPE,
        "eager_const_root_identity_scheme": census.EAGER_CONST_ROOT_IDENTITY,
        "unmeasured": list(census.UNMEASURED_V2),
    }
    if not complete:
        return json.dumps(header) + "\n"
    items = [
        {"id": f"{index + 1:032x}", "kind": "item", "instance_detail": "Item(fixture)",
         "generic_args": "[]", "def": row["def"], "def_path_hash": f"fixture-identity-{index}",
         "def_kind": "Fn", "definition_is_local": True, "symbol": f"fixture_symbol_{index}"}
        for index, row in enumerate(rows)
    ]
    ids = [item["id"] for item in items]
    nodes = [
        {"id": "item:" + item["id"], "kind": "item", "mono_item_kind": item["kind"],
         "collected": True, **{key: item[key] for key in (
             "instance_detail", "generic_args", "def", "def_path_hash", "def_kind",
             "definition_is_local")}}
        for item in items
    ]
    owners = [{"id": node["id"] + ":used", "item": node["id"],
               "collection_mode": "used", "collected": True} for node in nodes]
    snapshot = {
        "schema": schema, "event": "mono_snapshot", "item_count": len(items),
        "items": items, "roots": ids, "usage_edges": [],
        "codegen_units": {"fixture-cgu.0": [
            {"id": identity, "linkage": "Internal", "visibility": "Default", "inlined": False}
            for identity in ids]},
        "unplaced_items": [], "dependency_node_count": len(nodes),
        "dependency_owner_count": len(owners), "dependency_occurrence_count": 0,
        "dependency_nodes": nodes, "dependency_owners": owners, "dependency_occurrences": [],
        "eager_const_root_owner_count": 0, "eager_const_root_occurrence_count": 0,
        "eager_const_root_owners": [], "eager_const_root_occurrences": [],
    }
    snapshot_line = json.dumps(snapshot) + "\n"
    footer = {
        "schema": schema, "event": "complete", "status": "collector_observed",
        "item_count": len(items), "snapshot_sha256": hashlib.sha256(snapshot_line.encode()).hexdigest(),
        "sources": {input_path: "sha256=" + digest},
        "unmeasured": list(census.UNMEASURED_V2), "whole_program_complete": False,
    }
    return json.dumps(header) + "\n" + snapshot_line + json.dumps(footer) + "\n"


def add_census_evidence(corpus, repo="/fixture"):
    inputs = corpus["input_census"]["files"]
    hashes = {row["file"]: row["sha256"] for row in inputs}
    stage_root = str(Path(repo) / "stage")
    compiler = str(Path(stage_root) / "bin" / "trustc")
    closure = {
        "schema": scorecard.STAGE_CLOSURE_SCHEMA, "stage_root": stage_root,
        "compiler": compiler, "compiler_sha256": "a" * 64,
        "files": [{"path": "lib/librustc_driver-fixture.dylib",
                   "target": "lib/librustc_driver-fixture.dylib", "sha256": "b" * 64}],
    }
    closure["sha256"] = scorecard.stage_closure_digest(closure)
    corpus["census_evidence"] = {
        "schema": "trust.rust.producer-census-evidence.v2", "repo": repo,
        "target": "fixture-target", "edition": "2021",
        "compiler_sha256_before": "a" * 64, "compiler_sha256_after": "a" * 64,
        "stage_closure_before": copy.deepcopy(closure),
        "stage_closure_after": copy.deepcopy(closure),
        "precompile_errors": [], "postcompile_errors": [],
        "input_manifest": {"schema": scorecard.INPUT_MANIFEST_SCHEMA, "corpora": {"corpus": {
            "files": copy.deepcopy(inputs),
            "sources": [{"file": row["file"], "sha256": row["sha256"]} for row in inputs],
        }}},
    }
    for row in corpus["files"]:
        input_path = str(Path(repo) / row["file"])
        complete = row["outcome"] == "ok"
        row["measurement"] = {}
        for role, lowering, codegen in (("control", False, False), ("subject", True, False),
                                        ("codegen_control", False, True),
                                        ("codegen_subject", True, True)):
            argv = [compiler, "-Z", "trust-ir-lower=" + ("on" if lowering else "off"),
                    "-Z", "trust-verify=off", "-Z", "checksum-hash-algorithm=sha256",
                    "-Z", "trust-body-census=fixture.jsonl"]
            if codegen:
                argv += ["-Z", "trust-instance-census=mono-fixture.jsonl"]
            argv += ["--edition", "2021", "--crate-type", "lib",
                     "--emit=link" if codegen else "--emit=metadata", "--out-dir", "/fixture-output",
                     "--cap-lints", "allow", input_path]
            run = {
                "input": input_path, "error": None,
                "stderr": fixture_subject_stderr() if complete and lowering and not codegen else "",
                "exit_code": 0 if complete else 1,
                "argv": argv,
                "census_raw": compiler_census(input_path, row["bodies"], hashes[row["file"]],
                                              lowering, complete=complete),
                "compiler_sha256_before": "a" * 64,
                "compiler_sha256_after": "a" * 64,
            }
            if codegen:
                run["mono_raw"] = mono_census(input_path, row["bodies"], hashes[row["file"]],
                                               lowering, complete=complete)
            row["measurement"][role] = run


def check_by_id(result: dict, check_id: str) -> dict:
    return next(check for check in result["checks"] if check["id"] == check_id)


def delete_path(value: dict, path: str) -> None:
    parts = path.split(".")
    target = value
    for part in parts[:-1]:
        target = target[part]
    del target[parts[-1]]


class ProducerCompletionEvaluatorTests(unittest.TestCase):
    def test_complete_aggregate_passes_every_conjunct(self) -> None:
        result = scorecard.evaluate_producer_completion(complete_aggregate())
        self.assertTrue(result["complete"])
        self.assertTrue(result["checks"])
        self.assertTrue(all(check["passed"] for check in result["checks"]))
        self.assertFalse(
            result["non_acceptance_metrics"]["lowered_clean"]["acceptance_condition"]
        )

    def test_each_required_residue_fails_its_named_conjunct(self) -> None:
        mutations = {
            "modelled_equals_total": ("bodies.lowered_clean_modelled", 2),
            "symbolic_zero": ("bodies.lowered_clean_symbolic", 1),
            "opaque_collapse_all_zero": ("bodies.opaque_collapse_all", 1),
            "opaque_collapse_clean_zero": ("bodies.lowered_clean_opaque", 1),
            "class_unmeasured_zero": ("bodies.lowered_clean_class_unmeasured", 1),
            "validation_unmeasured_zero": ("validation.modules_unmeasured", 1),
            "validation_invalid_zero": ("validation.modules_invalid", 1),
            "validation_errors_zero": ("validation.error_occurrences", 1),
            "agreed_uninterpreted_callee_zero": (
                "bodies.agreed_uninterpreted_callee",
                1,
            ),
            "divergences_zero": ("bodies.divergences", ["fixture::bad"]),
            "parse_anomalies_zero": (
                "parse_anomalies.duplicate_differential_events",
                1,
            ),
            "partial_bodies_zero": (
                "partial_bodies_from_flag_induced_failures.total",
                1,
            ),
            "flag_induced_ice_signatures_zero": (
                "flag_induced_ice_signatures.fixture-panic",
                1,
            ),
        }
        for check_id, (path, residue) in mutations.items():
            with self.subTest(check=check_id):
                aggregate = complete_aggregate()
                target = aggregate
                parts = path.split(".")
                for part in parts[:-1]:
                    target = target[part]
                target[parts[-1]] = residue
                result = scorecard.evaluate_producer_completion(aggregate)
                self.assertFalse(result["complete"])
                self.assertFalse(check_by_id(result, check_id)["passed"])

    def test_flag_induced_and_timeout_outcomes_cannot_shrink_denominator(self) -> None:
        aggregate = complete_aggregate()
        aggregate["file_outcomes"]["flag_induced_fail"] = 1
        result = scorecard.evaluate_producer_completion(aggregate)
        self.assertFalse(check_by_id(result, "flag_induced_outcomes_zero")["passed"])

        aggregate = complete_aggregate()
        aggregate["file_outcomes"]["timeout"] = 1
        result = scorecard.evaluate_producer_completion(aggregate)
        self.assertFalse(check_by_id(result, "unresolved_file_outcomes_zero")["passed"])

    def test_empty_denominator_is_not_vacuously_complete(self) -> None:
        aggregate = complete_aggregate()
        aggregate["bodies"]["total"] = 0
        aggregate["bodies"]["lowered_clean_modelled"] = 0
        aggregate["bodies"]["lowered_clean_modelled_agreed"] = 0
        result = scorecard.evaluate_producer_completion(aggregate)
        self.assertFalse(result["complete"])
        self.assertFalse(check_by_id(result, "admitted_body_denominator_nonzero")["passed"])

    def test_lowered_clean_100_percent_does_not_mask_unmodelled_bodies(self) -> None:
        aggregate = complete_aggregate()
        aggregate["bodies"]["lowered_clean_modelled"] = 2
        aggregate["bodies"]["lowered_clean_modelled_agreed"] = 2
        self.assertEqual(aggregate["bodies"]["lowered_clean_pct"], 100.0)
        result = scorecard.evaluate_producer_completion(aggregate)
        self.assertFalse(result["complete"])
        self.assertFalse(check_by_id(result, "modelled_equals_total")["passed"])

    def test_missing_acceptance_fields_fail_closed_without_crashing(self) -> None:
        required_paths = [
            "bodies.total",
            "bodies.lowered_clean_modelled",
            "bodies.lowered_clean_symbolic",
            "bodies.opaque_collapse_all",
            "bodies.lowered_clean_opaque",
            "bodies.lowered_clean_class_unmeasured",
            "validation.modules_measured",
            "validation.modules_unmeasured",
            "validation.modules_invalid",
            "validation.error_occurrences",
            "file_outcomes.ok",
            "flag_induced_ice_signatures",
            "bodies.agreed_uninterpreted_callee",
            "bodies.divergences",
            "parse_anomalies",
            "partial_bodies_from_flag_induced_failures.total",
        ]
        for path in required_paths:
            with self.subTest(path=path):
                aggregate = complete_aggregate()
                delete_path(aggregate, path)
                result = scorecard.evaluate_producer_completion(aggregate)
                self.assertFalse(result["complete"])
                self.assertTrue(
                    any(path in check.get("missing_fields", []) for check in result["checks"]),
                    result,
                )

    def test_artifact_conjoins_all_corpora_and_rejects_empty_artifact(self) -> None:
        data = artifact()
        data["corpora"]["incomplete"] = {
            "aggregate": copy.deepcopy(complete_aggregate()),
            "files": [],
        }
        data["corpora"]["incomplete"]["aggregate"]["bodies"][
            "lowered_clean_symbolic"
        ] = 1
        result = scorecard.evaluate_scorecard_completion(data)
        self.assertFalse(result["complete"])
        self.assertTrue(result["corpora"]["fixture"]["complete"])
        self.assertFalse(result["corpora"]["incomplete"]["complete"])
        self.assertFalse(scorecard.evaluate_scorecard_completion({"corpora": {}})["complete"])

    def test_markdown_calls_it_a_gate_and_lowered_clean_non_acceptance(self) -> None:
        rendered = scorecard.render_markdown(artifact())
        self.assertIn("corpus-local instrumented-row zero-residue gate: **PASS**", rendered)
        self.assertIn("does not establish G1", rendered)
        self.assertIn("G1/G3 **RED**", rendered)
        self.assertIn("not a proof", rendered)
        self.assertIn("lowered clean (diagnostic only; **NOT an acceptance metric**", rendered)


class ProducerCompletionCliTests(unittest.TestCase):
    def run_gate(self, data: dict) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "data.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            return subprocess.run(
                [sys.executable, str(SCRIPT), "--check-completion", str(path)],
                check=False,
                capture_output=True,
                text=True,
            )

    def test_cli_exit_code_is_opt_in_and_reflects_completion(self) -> None:
        passed = self.run_gate(raw_artifact())
        self.assertEqual(passed.returncode, 0, passed.stderr)
        passed_result = json.loads(passed.stdout)
        self.assertTrue(passed_result["complete"])
        self.assertEqual(passed_result["aggregate_source"], "recomputed_from_files")
        self.assertIn("instrumented-row", passed_result["scope"])
        self.assertIn("G3", passed_result["does_not_establish"])

        incomplete = raw_artifact()
        # Leave the stored aggregate green and mutate only the raw evidence: CLI mode must not
        # trust an author-edited summary over the rows from which that summary was derived.
        incomplete["corpora"]["fixture"]["files"][0]["bodies"][0]["mode"] = "NotRun"
        failed = self.run_gate(incomplete)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        self.assertFalse(json.loads(failed.stdout)["complete"])

    def test_cli_fails_closed_when_raw_rows_are_missing(self) -> None:
        data = raw_artifact()
        del data["corpora"]["fixture"]["files"]
        failed = self.run_gate(data)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        result = json.loads(failed.stdout)
        self.assertFalse(result["complete"])
        self.assertTrue(result["artifact_errors"])

    def test_cli_requires_independent_file_and_body_censuses(self) -> None:
        data = raw_artifact()
        del data["corpora"]["fixture"]["body_census"]
        failed = self.run_gate(data)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        self.assertIn("reachable-body census", failed.stdout)

        data = raw_artifact()
        data["corpora"]["fixture"]["body_census"]["bodies"].pop()
        failed = self.run_gate(data)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        self.assertIn("do not equal", failed.stdout)

    def test_cli_rejects_legacy_artifact_without_codegen_observations(self) -> None:
        data = raw_artifact()
        for row in data["corpora"]["fixture"]["files"]:
            del row["measurement"]["codegen_control"]
            del row["measurement"]["codegen_subject"]
        failed = self.run_gate(data)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        result = json.loads(failed.stdout)
        self.assertFalse(result["complete"])
        self.assertIn("codegen control/subject", " ".join(result["artifact_errors"]))

    def test_sampled_agreed_requires_real_equal_samples_and_provenance(self) -> None:
        for field, value in (("equal", False), ("samples", 0)):
            with self.subTest(field=field):
                data = raw_artifact()
                data["corpora"]["fixture"]["files"][0]["bodies"][0][field] = value
                failed = self.run_gate(data)
                self.assertEqual(failed.returncode, 1, failed.stderr)
                self.assertIn("malformed", failed.stdout)

        data = raw_artifact()
        data["provenance"] = None
        failed = self.run_gate(data)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        self.assertIn("provenance identity", failed.stdout)

    def test_raw_body_cannot_hide_unsupported_events_behind_zero_count(self) -> None:
        data = raw_artifact()
        body = data["corpora"]["fixture"]["files"][0]["bodies"][0]
        body["unsupported"] = 0
        body["reasons"] = ["unsupported expression: fixture"]
        failed = self.run_gate(data)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        self.assertIn("malformed", failed.stdout)

    def test_cli_rejects_bodies_smuggled_through_compile_fail_rows(self) -> None:
        data = raw_artifact()
        ok_row = data["corpora"]["fixture"]["files"].pop(0)
        forged = data["corpora"]["fixture"]["files"][0]
        forged["bodies"] = ok_row["bodies"]
        # With no ok file, a permissive recomputation would observe three perfect bodies and
        # vacuously agree that zero of zero modules were invalid.
        failed = self.run_gate(data)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        result = json.loads(failed.stdout)
        self.assertFalse(result["complete"])
        self.assertTrue(
            any("carries completed bodies" in error for error in result["artifact_errors"]),
            result,
        )

    def test_cli_rejects_inconsistent_validation_and_wrong_schema(self) -> None:
        data = raw_artifact()
        data["corpora"]["fixture"]["files"][0]["validation"] = {
            "total": 0,
            "classes": {"ReturnTypeMismatch": 1},
        }
        failed = self.run_gate(data)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        self.assertIn("producer validation differs from saved subject stderr", failed.stdout)

        data = raw_artifact()
        data["schema"] = "forged.v1"
        failed = self.run_gate(data)
        self.assertEqual(failed.returncode, 1, failed.stderr)
        self.assertIn("unsupported producer scorecard schema", failed.stdout)


if __name__ == "__main__":
    unittest.main()
