#!/usr/bin/env python3
"""Independent Rust census controls. Live compiler tests require explicit Trust.

Run `TRUST_CENSUS_TEST_TRUSTC=/.../stage2/bin/trustc python3 -B ...` after
building this compiler revision. No stock rustc fallback is permitted.
"""

from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from trust_ir_producer_scorecard_completion_test import (
    compiler_census, mono_census, raw_artifact, scorecard,
)

ROOT = Path(__file__).resolve().parents[2]
LIVE_TRUSTC = os.environ.get("TRUST_CENSUS_TEST_TRUSTC")


def mutate_census(raw, change, *, rehash=True):
    records = [json.loads(line) for line in raw.splitlines()]
    change(records)
    lines = [json.dumps(record) + "\n" for record in records]
    if rehash and len(records) == 3:
        records[2]["snapshot_sha256"] = hashlib.sha256(lines[1].encode()).hexdigest()
        lines[2] = json.dumps(records[2]) + "\n"
    return "".join(lines)


def mutate_mono(raw, change):
    records = [json.loads(line) for line in raw.splitlines()]
    change(records)
    snapshot_line = json.dumps(records[1]) + "\n"
    records[2]["snapshot_sha256"] = hashlib.sha256(snapshot_line.encode()).hexdigest()
    return json.dumps(records[0]) + "\n" + snapshot_line + json.dumps(records[2]) + "\n"


def append_mono_item(raw, item):
    def change(records):
        snapshot, footer = records[1:]
        snapshot["items"].append(item)
        snapshot["roots"].append(item["id"])
        snapshot["codegen_units"]["fixture-cgu.0"].append(
            {"id": item["id"], "linkage": "Internal", "visibility": "Default", "inlined": False})
        node = {"id": "item:" + item["id"], "kind": "item", "mono_item_kind": item["kind"],
                "collected": True, **{key: item[key] for key in (
                    "instance_detail", "generic_args", "def", "def_path_hash", "def_kind",
                    "definition_is_local")}}
        snapshot["dependency_nodes"].append(node)
        snapshot["dependency_owners"].append(
            {"id": node["id"] + ":used", "item": node["id"],
             "collection_mode": "used", "collected": True})
        snapshot["item_count"] = footer["item_count"] = len(snapshot["items"])
        snapshot["dependency_node_count"] += 1
        snapshot["dependency_owner_count"] += 1
    return mutate_mono(raw, change)


class CompilerCensusParsing(unittest.TestCase):
    def setUp(self):
        self.corpus = raw_artifact()["corpora"]["fixture"]
        self.run = self.corpus["files"][0]["measurement"]["control"]

    def parse(self, raw, code=0):
        return scorecard.parse_compiler_census(raw, input_path=self.run["input"],
                                              lowering=False, exit_code=code)

    def test_complete_roster_has_no_reachable_instance_authority(self):
        result = self.parse(self.run["census_raw"])
        self.assertEqual(result["status"], "complete", result)
        self.assertEqual(len(result["bodies"]), 3)
        self.assertEqual(result["header"]["reachable_instances"], "unmeasured")

    def test_explicit_crate_type_contract_keeps_the_rlib_default_strict(self):
        for kinds in [("Executable",), ("Dylib",), ("StaticLib",), ("Cdylib",),
                      ("ProcMacro",), ("Sdylib",), ("Rlib", "Cdylib")]:
            with self.subTest(kinds=kinds):
                raw = mutate_census(self.run["census_raw"],
                                    lambda rows: rows[0].update(crate_types=list(kinds)))
                self.assertEqual(self.parse(raw)["status"], "malformed")
                result = scorecard.parse_compiler_census(
                    raw, input_path=self.run["input"], lowering=False, exit_code=0,
                    expected_crate_types=kinds)
                self.assertEqual(result["status"], "complete", result)
                self.assertEqual(len(result["bodies"]), 3)
                self.assertEqual(result["header"]["reachable_instances"], "unmeasured")
                failed = scorecard.parse_compiler_census(
                    raw, input_path=self.run["input"], lowering=False, exit_code=1,
                    expected_crate_types=kinds)
                self.assertEqual(failed["status"], "compiler_failed")
        wrong = scorecard.parse_compiler_census(
            self.run["census_raw"], input_path=self.run["input"], lowering=False,
            exit_code=0, expected_crate_types=("Executable",))
        self.assertEqual(wrong["status"], "malformed")

    def test_untyped_empty_duplicate_or_unknown_expected_crate_types_refuse(self):
        for expected in [None, "Rlib", [], (), ["Rlib", "Rlib"], ["unknown"],
                         [True], [["Rlib"]], {"Rlib"}]:
            with self.subTest(expected=expected):
                result = scorecard.parse_compiler_census(
                    self.run["census_raw"], input_path=self.run["input"],
                    lowering=False, exit_code=0, expected_crate_types=expected)
                self.assertEqual(result["status"], "malformed")

    def test_genuinely_empty_hir_roster_is_explicitly_complete(self):
        raw = compiler_census(self.run["input"], [], "1" * 64, False)
        self.assertEqual(self.parse(raw)["status"], "complete")

    def test_missing_partial_and_truncated_records_do_not_mean_zero(self):
        for raw, status in ((None, "missing"), ("", "missing"),
                            (self.run["census_raw"].splitlines(True)[0], "incomplete"),
                            (self.run["census_raw"][:-1], "malformed")):
            with self.subTest(status=status):
                self.assertEqual(self.parse(raw)["status"], status)

    def test_analysis_footer_does_not_override_failed_process(self):
        for code in (1, 101, -9, None):
            with self.subTest(code=code):
                self.assertEqual(self.parse(self.run["census_raw"], code)["status"], "compiler_failed")
        self.assertEqual(self.parse(self.run["census_raw"], False)["status"], "malformed")

    def test_wrong_input_lane_count_digest_and_unknown_class_are_rejected(self):
        mutations = [
            lambda r: r[0].update(input="/swapped.rs"),
            lambda r: r[0].update(direct_lowering=True),
            lambda r: r[0].update(verification_enabled=True),
            lambda r: r[0].update(reachable_instances="complete"),
            lambda r: r[1].update(body_count=4),
            lambda r: r[2].update(body_count=4),
            lambda r: r[1]["bodies"][0].update(def_kind="UnknownGeneratedKind"),
            lambda r: r[1]["bodies"][0].update(kind="closure"),
            lambda r: r[2].update(sources=[]),
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                raw = mutate_census(self.run["census_raw"], mutation)
                self.assertEqual(self.parse(raw)["status"], "malformed")
        raw = mutate_census(self.run["census_raw"], lambda r: r[2].update(snapshot_sha256="0" * 64), rehash=False)
        self.assertEqual(self.parse(raw)["status"], "malformed")

    def test_duplicate_identities_cannot_be_hidden_by_set_conversion(self):
        for field in ("def", "def_index", "def_path_hash"):
            raw = mutate_census(self.run["census_raw"],
                                lambda r: r[1]["bodies"][1].update({field: r[1]["bodies"][0][field]}))
            self.assertEqual(self.parse(raw)["status"], "malformed", field)

    def test_duplicate_json_keys_and_deep_json_fail_closed(self):
        raw = self.run["census_raw"].replace('"event": "begin"', '"event": "begin", "event": "begin"')
        self.assertEqual(self.parse(raw)["status"], "malformed")
        self.assertEqual(self.parse("[" * 2000 + "0" + "]" * 2000 + "\n")["status"], "malformed")

    def test_tracked_file_and_environment_inputs_are_explicitly_unmeasured(self):
        for key, value in (("tracked_files", "/fixture/payload.bin"),
                           ("environment_variables", "FIXTURE_CONFIG")):
            raw = mutate_census(self.run["census_raw"], lambda r: r[2]["other_inputs"][key].append(value))
            result = self.parse(raw)
            self.assertEqual(result["status"], "input_closure_incomplete", result)
            self.assertIn(value, " ".join(result["errors"]))

    def test_generated_closure_coroutine_const_and_static_rows_are_retained(self):
        kinds = ("Closure", "SyntheticCoroutineBody", "Const", "AnonConst", "InlineConst", "Static { safety: Safe }")
        rows = [{"def": f"fixture::f{index}", "kind": "named"} for index in range(len(kinds))]
        raw = compiler_census(self.run["input"], rows, "1" * 64, False)
        def change(records):
            for body, kind in zip(records[1]["bodies"], kinds):
                body["def_kind"] = kind
            generated = records[1]["bodies"].pop(1)
            records[1].update(body_count=len(kinds) - 1, generated_body_count=1, generated_bodies=[generated])
            records[2].update(body_count=len(kinds) - 1, generated_body_count=1)
        parsed = self.parse(mutate_census(raw, change))
        self.assertEqual(parsed["status"], "complete", parsed)
        self.assertEqual(sorted(row["def_kind"] for row in parsed["bodies"]), sorted(kinds))
        self.assertEqual(len(parsed["generated_bodies"]), 1)


def census_v2(raw, *, source=None):
    """Re-emit a v1 fixture census as v2: crate-disambiguated defs plus the
    compiler-independent identity fields rustc_interface now writes."""
    def change(records):
        for record in records:
            record["schema"] = scorecard.CENSUS_SCHEMA_V2
        for index, body in enumerate(records[1]["bodies"] + records[1]["generated_bodies"]):
            crate, _, rest = body["def"].partition("::")
            body.update({"def": f"{crate}[1a2b]::{rest}", "crate_name": crate,
                         "def_path_no_crate": f"::{rest}",
                         "source": copy.deepcopy(source) if source is not None else {
                             "file": "/fixture/src/lib.rs", "sha256": "2" * 64,
                             "lo": [index + 1, 0], "hi": [index + 1, 9]}})
    return mutate_census(raw, change)


class CompilerCensusV2Identity(unittest.TestCase):
    """v2 rows carry identity independent of the StableCrateId; v1 stays readable."""

    def setUp(self):
        self.corpus = raw_artifact()["corpora"]["fixture"]
        self.run = self.corpus["files"][0]["measurement"]["control"]

    def parse(self, raw):
        return scorecard.parse_compiler_census(raw, input_path=self.run["input"],
                                              lowering=False, exit_code=0)

    def test_v2_identity_rows_are_accepted_and_retained(self):
        result = self.parse(census_v2(self.run["census_raw"]))
        self.assertEqual(result["status"], "complete", result)
        self.assertEqual(result["schema"], scorecard.CENSUS_SCHEMA_V2)
        self.assertEqual({body["crate_name"] for body in result["bodies"]}, {"fixture"})
        self.assertTrue(all(body["source"]["sha256"] == "2" * 64 for body in result["bodies"]))

    def test_v1_census_still_parses_as_v1(self):
        result = self.parse(self.run["census_raw"])
        self.assertEqual((result["status"], result["schema"]), ("complete", scorecard.CENSUS_SCHEMA))

    def test_all_null_source_is_disclosed_unmeasured_not_malformed(self):
        empty = {"file": None, "sha256": None, "lo": None, "hi": None}
        self.assertEqual(self.parse(census_v2(self.run["census_raw"], source=empty))["status"], "complete")

    def test_v2_identity_mutations_refuse(self):
        v2 = census_v2(self.run["census_raw"])
        mutations = {
            "mixed schemas": lambda r: r[2].update(schema=scorecard.CENSUS_SCHEMA),
            "v1 row under v2": lambda r: [r[1]["bodies"][0].pop(key)
                                          for key in ("crate_name", "def_path_no_crate", "source")],
            "v2 row under v1": lambda r: [record.update(schema=scorecard.CENSUS_SCHEMA) for record in r],
            "def disagrees with crate-free path": lambda r: r[1]["bodies"][0].update(def_path_no_crate="::other"),
            "def disagrees with crate name": lambda r: r[1]["bodies"][0].update(crate_name="other"),
            "partially measured source": lambda r: r[1]["bodies"][0]["source"].update(sha256=None),
            "relative source file": lambda r: r[1]["bodies"][0]["source"].update(file="src/lib.rs"),
            "uppercase source hash": lambda r: r[1]["bodies"][0]["source"].update(sha256="A" * 64),
            "inverted span": lambda r: r[1]["bodies"][0]["source"].update(lo=[9, 0], hi=[1, 0]),
            "zero line": lambda r: r[1]["bodies"][0]["source"].update(lo=[0, 0]),
            "extra source key": lambda r: r[1]["bodies"][0]["source"].update(offset=0),
            "crate-free path lacks separator": lambda r: r[1]["bodies"][0].update(def_path_no_crate="f0"),
        }
        self.assertEqual(self.parse(v2)["status"], "complete")
        for name, mutation in mutations.items():
            with self.subTest(mutation=name):
                result = self.parse(mutate_census(v2, mutation))
                self.assertEqual(result["status"], "malformed", result)


class CensusReconciliation(unittest.TestCase):
    def setUp(self):
        self.data = raw_artifact()
        self.corpus = self.data["corpora"]["fixture"]

    def result(self):
        return scorecard.reconcile_compiler_censuses(self.corpus)

    def test_positive_with_explicit_expected_compile_failure(self):
        result = self.result()
        self.assertEqual(result["status"], "bounded_mono_reconciled", result)
        self.assertEqual(len(result["bodies"]), 3)
        self.assertEqual(result["mono_item_count"], 3)
        self.assertEqual(result["mono_matched_count"], 3)
        self.assertEqual(result["mono_unrepresented"], {})
        self.assertEqual(result["g1_g3_status"], "red")
        self.assertFalse(result["whole_program_complete"])
        self.assertIn("external-linked-and-foreign-bodies", result["unmeasured"])
        self.assertTrue(any(state["status"] == "expected_compile_failure" for state in result["files"]))
        self.assertEqual(result["runtime_roots"], "unmeasured")

    def test_lost_file_or_producer_body_is_incomplete(self):
        original = copy.deepcopy(self.corpus)
        self.corpus["files"].pop()
        self.assertEqual(self.result()["status"], "incomplete")
        self.corpus = original
        self.corpus["files"][0]["bodies"].pop()
        self.assertIn("producer body rows differ", " ".join(self.result()["errors"]))

    def test_missing_control_or_missing_census_is_not_inferred_from_subject(self):
        for mutation in ("control", "census"):
            self.setUp()
            run = self.corpus["files"][0]["measurement"]
            if mutation == "control":
                del run["control"]
            else:
                run["control"]["census_raw"] = None
            self.assertEqual(self.result()["status"], "incomplete")

    def test_subject_cannot_replace_independent_roster(self):
        run = self.corpus["files"][0]["measurement"]["subject"]
        def change(records):
            records[1]["bodies"][0]["def"] = "fixture::replacement"
        run["census_raw"] = mutate_census(run["census_raw"], change)
        self.assertIn("subject HIR census differs", " ".join(self.result()["errors"]))

    def test_codegen_pair_cannot_claim_a_different_compiler_version(self):
        for role in ("codegen_control", "codegen_subject"):
            run = self.corpus["files"][0]["measurement"][role]
            run["census_raw"] = mutate_census(
                run["census_raw"], lambda records: records[0].update(compiler_version="other-compiler"))
            run["mono_raw"] = mutate_mono(
                run["mono_raw"], lambda records: records[0].update(compiler_version="other-compiler"))
        result = self.result()
        self.assertEqual(result["status"], "incomplete", result)
        self.assertIn("compiler versions differ across metadata/codegen runs", " ".join(result["errors"]))
        self.assertFalse(scorecard.evaluate_scorecard_completion(
            self.data, recompute_from_files=True)["complete"])

    def test_late_flag_override_is_not_a_lowering_disabled_control(self):
        self.corpus["files"][0]["measurement"]["control"]["argv"] += ["-Z", "trust-ir-lower=on"]
        self.assertIn("argv", " ".join(self.result()["errors"]))

    def test_input_edition_and_target_must_match_the_exact_measurement(self):
        for mutation in ("input", "edition", "target", "header-edition"):
            self.setUp()
            run = self.corpus["files"][0]["measurement"]["control"]
            if mutation == "input":
                run["argv"][-1] = "/fixture/swapped.rs"
            elif mutation == "edition":
                run["argv"][10] = "2024"
            else:
                field = "edition" if mutation == "header-edition" else "target"
                value = "2024" if field == "edition" else "other-target"
                run["census_raw"] = mutate_census(run["census_raw"], lambda r: r[0].update({field: value}))
            self.assertEqual(self.result()["status"], "incomplete", mutation)

    def test_source_or_compiler_identity_drift_is_incomplete(self):
        for field in ("compiler_sha256_after", "precompile_errors", "postcompile_errors"):
            self.setUp()
            self.corpus["census_evidence"][field] = "b" * 64 if field.startswith("compiler") else ["source changed"]
            self.assertEqual(self.result()["status"], "incomplete")
        self.setUp()
        self.corpus["census_evidence"]["input_manifest"]["corpora"]["corpus"]["sources"][0]["sha256"] = "b" * 64
        self.assertEqual(self.result()["status"], "incomplete")

    def test_each_run_requires_matching_executable_checkpoints(self):
        for role in ("control", "subject", "codegen_control", "codegen_subject"):
            for field in ("compiler_sha256_before", "compiler_sha256_after"):
                with self.subTest(role=role, field=field):
                    self.setUp()
                    self.corpus["files"][0]["measurement"][role][field] = "b" * 64
                    result = self.result()
                    self.assertEqual(result["status"], "incomplete", result)
                    self.assertIn("compiler executable changed or unmeasured around compiler run",
                                  " ".join(result["errors"]))

    def test_stage_library_drift_or_missing_closure_is_incomplete(self):
        for mutation in ("missing", "changed_library", "wrong_compiler"):
            with self.subTest(mutation=mutation):
                self.setUp()
                evidence = self.corpus["census_evidence"]
                if mutation == "missing":
                    evidence["stage_closure_after"] = None
                elif mutation == "changed_library":
                    after = evidence["stage_closure_after"]
                    after["files"][0]["sha256"] = "c" * 64
                    after["sha256"] = scorecard.stage_closure_digest(after)
                else:
                    self.corpus["files"][0]["measurement"]["codegen_subject"]["argv"][0] = "/other/bin/trustc"
                self.assertEqual(self.result()["status"], "incomplete")

    def test_loaded_auxiliary_source_requires_precompile_manifest(self):
        run = self.corpus["files"][0]["measurement"]["control"]
        raw = mutate_census(run["census_raw"], lambda r: r[2]["sources"].append({"file": "/fixture/module.rs", "sha256": "c" * 64}))
        run["census_raw"] = raw
        self.assertIn("declare auxiliary inputs", " ".join(self.result()["errors"]))
        self.corpus["census_evidence"]["input_manifest"]["corpora"]["corpus"]["sources"].append({"file": "module.rs", "sha256": "c" * 64})
        self.assertIn("HIR sources differs", " ".join(self.result()["errors"]))
        for role in ("control", "subject", "codegen_control", "codegen_subject"):
            run = self.corpus["files"][0]["measurement"][role]
            def add_source(records):
                source = {"file": "/fixture/module.rs", "sha256": "c" * 64}
                for record in records[1:]:
                    if source not in record["sources"]:
                        record["sources"].append(source)
            run["census_raw"] = mutate_census(run["census_raw"], add_source)
            if role.startswith("codegen_"):
                run["mono_raw"] = mutate_mono(run["mono_raw"], lambda records:
                    records[2]["sources"].update({"/fixture/module.rs": "sha256=" + "c" * 64}))
        self.assertEqual(self.result()["status"], "bounded_mono_reconciled")

    def test_subject_stderr_verdict_cannot_disagree_with_saved_producer_row(self):
        run = self.corpus["files"][0]["measurement"]["subject"]
        run["stderr"] = run["stderr"].replace(
            "equal=true, samples=1, mode=Agreed",
            "equal=false, samples=1, mode=MirOracle", 1)
        parsed, _ = scorecard.parse_bodies(run["stderr"])
        self.assertEqual(parsed[0]["mode"], "MirOracle")
        self.assertEqual(self.corpus["files"][0]["bodies"][0]["mode"], "Agreed")
        result = self.result()
        self.assertEqual(result["status"], "incomplete", result)
        self.assertIn("saved subject stderr", " ".join(result["errors"]))
        self.assertFalse(scorecard.evaluate_scorecard_completion(
            self.data, recompute_from_files=True)["complete"])

    def test_predeclared_compile_failure_cannot_succeed_in_codegen(self):
        row = self.corpus["files"][1]
        bodies = self.corpus["files"][0]["bodies"]
        for role, lowering in (("codegen_control", False), ("codegen_subject", True)):
            run = row["measurement"][role]
            run["exit_code"] = 0
            run["census_raw"] = compiler_census(run["input"], bodies, "2" * 64, lowering)
            run["mono_raw"] = mono_census(run["input"], bodies, "2" * 64, lowering)
        result = self.result()
        self.assertEqual(result["status"], "incomplete", result)
        self.assertIn("predeclared compile-failure codegen_control run succeeded",
                      " ".join(result["errors"]))
        self.assertEqual(result["mono_item_count"], 3)
        self.assertFalse(scorecard.evaluate_scorecard_completion(
            self.data, recompute_from_files=True)["complete"])

    def test_one_lane_extra_loaded_source_cannot_pass(self):
        for role in ("control", "subject", "codegen_control", "codegen_subject"):
            with self.subTest(role=role):
                self.setUp()
                run = self.corpus["files"][0]["measurement"][role]
                def add_source(records):
                    source = {"file": "/fixture/extra.rs", "sha256": "c" * 64}
                    records[1]["sources"].append(source)
                    records[2]["sources"].append(source)
                run["census_raw"] = mutate_census(run["census_raw"], add_source)
                if role.startswith("codegen_"):
                    run["mono_raw"] = mutate_mono(run["mono_raw"], lambda records:
                        records[2]["sources"].update({"/fixture/extra.rs": "sha256=" + "c" * 64}))
                self.corpus["census_evidence"]["input_manifest"]["corpora"]["corpus"]["sources"].append(
                    {"file": "extra.rs", "sha256": "c" * 64})
                result = self.result()
                self.assertEqual(result["status"], "incomplete", result)
                self.assertIn("HIR snapshot_sources differs", " ".join(result["errors"]))
                self.assertFalse(scorecard.evaluate_scorecard_completion(
                    self.data, recompute_from_files=True)["complete"])

    def test_reconciliation_never_resolves_retained_compiler_argv(self):
        with mock.patch.object(scorecard.os.path, "realpath", side_effect=AssertionError("offline filesystem access")):
            result = self.result()
        self.assertEqual(result["status"], "bounded_mono_reconciled", result)
        self.assertEqual(result["g1_g3_status"], "red")

    def test_repointing_retained_argv_symlink_never_changes_result(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            stage = Path(os.path.realpath(root / "stage"))
            (stage / "bin").mkdir(parents=True)
            compiler = stage / "bin" / "trustc"
            compiler.write_text("first")
            alternate = root / "alternate"
            alternate.write_text("second")
            alias = root / "compiler-alias"
            alias.symlink_to(compiler)
            self.assertEqual(os.path.realpath(alias), str(compiler))
            closure = self.corpus["census_evidence"]["stage_closure_before"]
            closure.update(stage_root=str(stage), compiler=str(compiler))
            closure["sha256"] = scorecard.stage_closure_digest(closure)
            self.corpus["census_evidence"]["stage_closure_after"] = copy.deepcopy(closure)
            for row in self.corpus["files"]:
                for run in row["measurement"].values():
                    run["argv"][0] = str(alias)
            before = self.result()
            alias.unlink()
            alias.symlink_to(alternate)
            self.assertNotEqual(os.path.realpath(alias), str(compiler))
            after = self.result()
        self.assertEqual(before, after)
        self.assertEqual(after["status"], "incomplete")
        self.assertIn("not bound to the stage closure", " ".join(after["errors"]))
        self.assertFalse(scorecard.evaluate_scorecard_completion(
            self.data, recompute_from_files=True)["complete"])

    def test_missing_or_downgraded_codegen_capture_is_red(self):
        for mutation in ("missing_run", "metadata_emit", "missing_mono", "truncated_mono",
                         "unmeasured_footer"):
            with self.subTest(mutation=mutation):
                self.setUp()
                row = self.corpus["files"][0]
                if mutation == "missing_run":
                    del row["measurement"]["codegen_control"]
                elif mutation == "metadata_emit":
                    row["measurement"]["codegen_control"]["argv"][15] = "--emit=metadata"
                elif mutation == "missing_mono":
                    row["measurement"]["codegen_control"]["mono_raw"] = None
                elif mutation == "truncated_mono":
                    row["measurement"]["codegen_control"]["mono_raw"] = (
                        row["measurement"]["codegen_control"]["mono_raw"].splitlines(True)[0])
                else:
                    raw = row["measurement"]["codegen_control"]["mono_raw"]
                    records = [json.loads(line) for line in raw.splitlines()]
                    records[0]["codegen_requested"] = False
                    records[2].update(status="unmeasured", item_count=None, snapshot_sha256=None)
                    row["measurement"]["codegen_control"]["mono_raw"] = "".join(
                        json.dumps(record) + "\n" for record in (records[0], records[2]))
                self.assertEqual(self.result()["status"], "incomplete")

    def test_subject_mono_omission_or_duplicate_identity_is_red(self):
        for mutation in ("omit", "duplicate"):
            with self.subTest(mutation=mutation):
                self.setUp()
                run = self.corpus["files"][0]["measurement"]["codegen_subject"]
                records = [json.loads(line) for line in run["mono_raw"].splitlines()]
                snapshot = records[1]
                if mutation == "omit":
                    removed = snapshot["items"].pop()
                    snapshot["roots"].remove(removed["id"])
                    snapshot["codegen_units"]["fixture-cgu.0"].pop()
                    snapshot["dependency_nodes"].pop()
                    snapshot["dependency_owners"].pop()
                    for key in ("item_count", "dependency_node_count", "dependency_owner_count"):
                        snapshot[key] -= 1
                    records[2]["item_count"] -= 1
                else:
                    snapshot["items"][1]["id"] = snapshot["items"][0]["id"]
                line = json.dumps(snapshot) + "\n"
                records[2]["snapshot_sha256"] = hashlib.sha256(line.encode()).hexdigest()
                run["mono_raw"] = json.dumps(records[0]) + "\n" + line + json.dumps(records[2]) + "\n"
                if mutation == "omit":
                    parsed = scorecard.rust_instance_census.parse_census(
                        run["mono_raw"].encode(), input_path=run["input"], exit_code=0,
                        lowering=True)
                    self.assertEqual(parsed["status"], "collector_observed", parsed)
                result = self.result()
                self.assertEqual(result["status"], "incomplete", result)
                self.assertIn("mono items differs" if mutation == "omit" else "mono",
                              " ".join(result["errors"]))

    def test_dependency_only_subject_change_is_rejected_after_valid_parse(self):
        run = self.corpus["files"][0]["measurement"]["codegen_subject"]
        def extra_dependency(records):
            snapshot = records[1]
            identity = "item:" + snapshot["items"][0]["id"]
            snapshot["dependency_occurrences"].append({
                "owner": identity + ":used", "ordinal": 0, "mode": "used", "origin": "mir",
                "kind": "instance-use", "target": identity, "site": "instance-use",
                "collector_direct_call": True, "local_codegen": True})
            snapshot["dependency_occurrence_count"] += 1
        run["mono_raw"] = mutate_mono(run["mono_raw"], extra_dependency)
        parsed = scorecard.rust_instance_census.parse_census(
            run["mono_raw"].encode(), input_path=run["input"], exit_code=0, lowering=True)
        self.assertEqual(parsed["status"], "collector_observed", parsed)
        self.assertIn("mono dependency_occurrences differs", " ".join(self.result()["errors"]))

    def test_multiple_mono_instances_of_one_hir_body_remain_distinct(self):
        row = self.corpus["files"][0]
        item = {"id": f"{4:032x}", "kind": "item", "instance_detail": "Item(fixture)",
                "generic_args": "[u32]", "def": "fixture::f0",
                "def_path_hash": "fixture-identity-0", "def_kind": "Fn",
                "definition_is_local": True, "symbol": "fixture_symbol_0_u32"}
        for role in ("codegen_control", "codegen_subject"):
            run = row["measurement"][role]
            run["mono_raw"] = append_mono_item(run["mono_raw"], item)
        result = self.result()
        self.assertEqual(result["status"], "bounded_mono_reconciled", result)
        self.assertEqual(result["mono_item_count"], 4)
        self.assertEqual(result["mono_matched_count"], 4)
        self.assertEqual(len(result["bodies"]), 3)

    def test_external_and_shim_items_remain_unrepresented_and_gates_red(self):
        row = self.corpus["files"][0]
        item = {"id": f"{4:032x}", "kind": "shim-drop-glue", "instance_detail": "Shim(DropGlue)",
                "generic_args": "[Owner]", "def": "core::drop_in_place",
                "def_path_hash": "external-drop-definition", "def_kind": "Fn",
                "definition_is_local": False, "symbol": "drop_owner"}
        for role in ("codegen_control", "codegen_subject"):
            run = row["measurement"][role]
            run["mono_raw"] = append_mono_item(run["mono_raw"], item)
        result = self.result()
        self.assertEqual(result["status"], "bounded_mono_reconciled", result)
        self.assertEqual(result["mono_unrepresented"], {"external-shim-drop-glue": 1})
        self.assertEqual(result["g1_g3_status"], "red")

    def test_typeck_generated_body_identity_is_joined_to_mono_and_producer(self):
        row = self.corpus["files"][0]
        for role in ("control", "subject", "codegen_control", "codegen_subject"):
            run = row["measurement"][role]
            def generate(records):
                generated = records[1]["bodies"].pop(1)
                generated["def_kind"] = "SyntheticCoroutineBody"
                records[1]["generated_bodies"] = [generated]
                records[1]["body_count"] -= 1
                records[1]["generated_body_count"] = 1
                records[2]["body_count"] -= 1
                records[2]["generated_body_count"] = 1
            run["census_raw"] = mutate_census(run["census_raw"], generate)
        for role in ("codegen_control", "codegen_subject"):
            run = row["measurement"][role]
            def generated_kind(records):
                records[1]["items"][1]["def_kind"] = "SyntheticCoroutineBody"
                records[1]["dependency_nodes"][1]["def_kind"] = "SyntheticCoroutineBody"
            run["mono_raw"] = mutate_mono(run["mono_raw"], generated_kind)
        result = self.result()
        self.assertEqual(result["status"], "bounded_mono_reconciled", result)
        self.assertEqual(result["mono_matched_count"], 3)

    def test_local_mono_identity_must_exist_in_hir_and_producer(self):
        for mutation in ("hir_hash", "producer_def"):
            with self.subTest(mutation=mutation):
                self.setUp()
                row = self.corpus["files"][0]
                if mutation == "hir_hash":
                    for role in ("control", "subject", "codegen_control", "codegen_subject"):
                        run = row["measurement"][role]
                        run["census_raw"] = mutate_census(
                            run["census_raw"],
                            lambda records: records[1]["bodies"][0].update(def_path_hash="swapped"))
                else:
                    row["bodies"][0]["def"] = "fixture::replacement"
                result = self.result()
                self.assertEqual(result["status"], "incomplete", result)
                self.assertIn("local mono item", " ".join(result["errors"]))

    def test_aborted_codegen_run_cannot_reuse_a_complete_report(self):
        for exit_code in (None, 101, -9):
            with self.subTest(exit_code=exit_code):
                self.setUp()
                run = self.corpus["files"][0]["measurement"]["codegen_control"]
                run["exit_code"] = exit_code
                self.assertEqual(self.result()["status"], "incomplete")

    def test_duplicate_producer_row_and_changed_mono_source_are_red(self):
        row = self.corpus["files"][0]
        row["bodies"].append(copy.deepcopy(row["bodies"][0]))
        self.assertIn("producer body rows differ", " ".join(self.result()["errors"]))
        self.setUp()
        run = self.corpus["files"][0]["measurement"]["codegen_control"]
        run["mono_raw"] = mutate_mono(run["mono_raw"], lambda records:
            records[2]["sources"].update({run["input"]: "sha256=" + "f" * 64}))
        self.assertIn("mono loaded source absent or changed", " ".join(self.result()["errors"]))

    def test_expected_outcome_is_not_fitted_to_control_failure(self):
        row = self.corpus["files"][0]
        row["outcome"], row["bodies"] = "compile_fail", []
        for run in row["measurement"].values():
            run["exit_code"] = 1
        result = self.result()
        self.assertEqual(result["status"], "incomplete")
        self.assertEqual(self.corpus["input_census"]["files"][0]["expected_outcome"], "ok")

    def test_deleting_compiler_evidence_does_not_restore_a_green_row_gate(self):
        data = raw_artifact()
        del data["corpora"]["fixture"]["census_evidence"]
        self.assertFalse(scorecard.evaluate_scorecard_completion(data, recompute_from_files=True)["complete"])


class MeasurementProduction(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="trust-rust-census-test-")
        self.addCleanup(temporary.cleanup)
        self.repo = Path(temporary.name)
        self.source = self.repo / "fixture.rs"
        self.source.write_text("pub fn value() -> u32 { 1 }\n")
        stage = self.repo / "stage"
        (stage / "bin").mkdir(parents=True)
        (stage / "lib").mkdir()
        (stage / "lib" / "librustc_driver-fixture.dylib").write_bytes(b"driver fixture")
        self.compiler = stage / "bin" / "trustc"
        self.compiler.write_text("mock boundary only; never executed as a compiler\n")
        self.rows = [{"def": "fixture::value", "kind": "named"}]

    @unittest.skipUnless(os.name == "posix", "direct compiler process-group descriptor transport")
    def test_guarded_direct_child_preserves_advertised_descriptors_and_its_own_group(self):
        # This actor observes transport only: file descriptors and GNU locators
        # do not authenticate native resource admission or a compiler result.
        read, write = os.pipe()
        try:
            with (self.repo / "original-description").open("w+b") as original:
                descriptors = [original.fileno(), read, write]
                expected = [[os.fstat(fd).st_dev, os.fstat(fd).st_ino] for fd in descriptors]
                environment = dict(os.environ,
                                   TRUST_CPU_IMPLICIT_FD=str(original.fileno()),
                                   MAKEFLAGS=f"--jobserver-auth={read},{write}")
                actor = (
                    "import json,os,sys; "
                    "fds=[int(os.environ['TRUST_CPU_IMPLICIT_FD'])]+"
                    "[int(fd) for fd in os.environ['MAKEFLAGS'].split('=')[1].split(',')]; "
                    "sys.stderr.write(json.dumps([sys.argv[1:],"
                    "[[os.fstat(fd).st_dev,os.fstat(fd).st_ino] for fd in fds],"
                    "os.getsid(0)==os.getpid()]))"
                )
                code, output = scorecard.guarded_compile(
                    [sys.executable, "-c", actor, "exact-argument"],
                    str(self.repo), environment, 60)
        finally:
            os.close(read)
            os.close(write)
        # Assertions follow the guarded child's actual wait and descriptor cleanup.
        self.assertEqual(code, 0, output)
        self.assertEqual(json.loads(output), [["exact-argument"], expected, True])

    def compile_control(self, argv, cwd, env, timeout):
        path = argv[-1]
        lowering = "trust-ir-lower=on" in argv
        census_path = Path(next(arg.split("=", 1)[1] for arg in argv if arg.startswith("trust-body-census=")))
        edition = argv[argv.index("--edition") + 1]
        digest = scorecard.file_sha256(path)
        census_path.write_text(compiler_census(path, self.rows, digest, lowering, edition=edition))
        if "--emit=link" in argv:
            mono_path = Path(next(arg.split("=", 1)[1] for arg in argv if arg.startswith("trust-instance-census=")))
            mono_path.write_text(mono_census(path, self.rows, digest, lowering, edition=edition))
        stderr = ("trust-ir-lower: differential, def=DefId(0:1 ~ fixture::value), equal=true, samples=1, "
                  'mode=Agreed, note=""\n') if lowering else ""
        return 0, stderr.encode()

    def test_every_success_and_failure_runs_control_then_subject(self):
        for status in (0, 1, 101, None):
            with self.subTest(status=status):
                def compile_run(argv, cwd, env, timeout):
                    code, stderr = self.compile_control(argv, cwd, env, timeout)
                    return (status, stderr) if "trust-ir-lower=on" in argv else (code, stderr)
                with mock.patch.object(scorecard, "guarded_compile", side_effect=compile_run) as compiler:
                    row = scorecard.measure_file(str(self.compiler), str(self.source), "2024", 2, str(self.repo))
                self.assertEqual(compiler.call_count, 4)
                self.assertIn("trust-ir-lower=off", compiler.call_args_list[0].args[0])
                self.assertIn("trust-ir-lower=on", compiler.call_args_list[1].args[0])
                self.assertIn("--emit=link", compiler.call_args_list[2].args[0])
                self.assertIn("--emit=link", compiler.call_args_list[3].args[0])
                self.assertIsNotNone(row["measurement"]["control"]["census_raw"])
                self.assertIsNotNone(row["measurement"]["codegen_control"]["mono_raw"])

    def test_codegen_only_flag_failure_has_first_class_outcome(self):
        def compile_run(argv, cwd, env, timeout):
            code, stderr = self.compile_control(argv, cwd, env, timeout)
            if "--emit=link" in argv and "trust-ir-lower=on" in argv:
                return 101, b"internal compiler error: codegen fixture\n"
            return code, stderr
        with mock.patch.object(scorecard, "guarded_compile", side_effect=compile_run):
            row = scorecard.measure_file(str(self.compiler), str(self.source), "2024", 2, str(self.repo))
        self.assertEqual(row["outcome"], "flag_induced_codegen_ice")
        self.assertEqual(row["bodies"], [])
        self.assertEqual(len(row["partial_bodies"]), 1)
        aggregated = scorecard.aggregate([row])
        self.assertEqual(aggregated["file_outcomes"], {"flag_induced_codegen_ice": 1})
        self.assertFalse(scorecard.evaluate_producer_completion(aggregated)["complete"])

    def test_compiler_stage_closure_detects_library_drift(self):
        before = scorecard.compiler_stage_closure(str(self.compiler))
        self.assertEqual(scorecard.validate_stage_closure(before), before)
        driver = self.compiler.parent.parent / "lib" / "librustc_driver-fixture.dylib"
        driver.write_bytes(b"different driver fixture")
        after = scorecard.compiler_stage_closure(str(self.compiler))
        self.assertNotEqual(before, after)
        driver.unlink()
        closure, errors = scorecard.capture_stage_closure(str(self.compiler))
        self.assertIsNone(closure)
        self.assertTrue(errors)

    def test_compiler_mutation_between_runs_cannot_hide_behind_corpus_hashes(self):
        output = self.repo / "report"
        original = self.compiler.read_bytes()

        def compile_run(argv, cwd, env, timeout):
            result = self.compile_control(argv, cwd, env, timeout)
            if "--emit=metadata" in argv and "trust-ir-lower=on" in argv:
                self.compiler.write_bytes(b"different compiler during measurement")
            elif "--emit=link" in argv and "trust-ir-lower=on" in argv:
                self.compiler.write_bytes(original)
            return result

        provenance = {"date_utc": "fixture", "repo_describe": "fixture", "seed": 1,
                      "target": "fixture-target", "trustc_sha256": scorecard.file_sha256(self.compiler)}
        argv = ["scorecard", "--trustc", str(self.compiler), "--repo", str(self.repo),
                "--out-dir", str(output), "--no-ui-sample", "--corpus", "fixture=" + str(self.source)]
        with mock.patch.object(sys, "argv", argv), mock.patch.object(scorecard, "provenance", return_value=provenance), \
                mock.patch.object(scorecard, "guarded_compile", side_effect=compile_run) as compiler:
            scorecard.main()

        self.assertEqual(compiler.call_count, 4)
        corpus = json.loads((output / "data.json").read_text())["corpora"]["fixture"]
        evidence = corpus["census_evidence"]
        self.assertEqual(evidence["compiler_sha256_before"], evidence["compiler_sha256_after"])
        self.assertEqual(evidence["stage_closure_before"], evidence["stage_closure_after"])
        self.assertEqual(corpus["census_status"]["status"], "incomplete")
        self.assertIn("compiler executable changed or unmeasured around compiler run",
                      " ".join(corpus["census_status"]["errors"]))

    def test_run_one_retains_resolved_compiler_identity(self):
        alias = self.repo / "trustc-alias"
        alias.symlink_to(self.compiler)
        with mock.patch.object(scorecard, "guarded_compile", side_effect=self.compile_control):
            run = scorecard.run_one(str(alias), str(self.source), "2024", 2,
                                    False, str(self.repo))
        self.assertEqual(run["argv"][0], os.path.realpath(self.compiler))
        alias.unlink()
        alternate = self.repo / "alternate-compiler"
        alternate.write_text("different compiler")
        alias.symlink_to(alternate)
        self.assertEqual(run["argv"][0], os.path.realpath(self.compiler))

    def test_timeout_keeps_partial_census_and_diagnostics(self):
        def compile_run(argv, cwd, env, timeout):
            self.compile_control(argv, cwd, env, timeout)
            return None, b"partial compiler diagnostics"
        with mock.patch.object(scorecard, "guarded_compile", side_effect=compile_run):
            run = scorecard.run_one(str(self.compiler), str(self.source), "2024", 2, False, str(self.repo))
        self.assertIn("partial compiler diagnostics", run["stderr"])
        self.assertIsNotNone(run["census_raw"])
        self.assertFalse(Path(run["argv"][15]).exists(), "temporary compiler outputs were not cleaned")

    def test_mono_capture_is_bounded_before_retention(self):
        def oversized_report(argv, cwd, env, timeout):
            mono_path = Path(next(arg.split("=", 1)[1] for arg in argv if arg.startswith("trust-instance-census=")))
            mono_path.write_text("x" * 512)
            return 0, b""
        with mock.patch.object(scorecard, "guarded_compile", side_effect=oversized_report), \
                mock.patch.object(scorecard.rust_instance_census, "MAX_BYTES", 64):
            run = scorecard.run_one(str(self.compiler), str(self.source), "2024", 2,
                                    False, str(self.repo), codegen=True)
        self.assertEqual(len(run["mono_raw"]), 65)
        self.assertFalse(Path(run["argv"][17]).exists(), "temporary codegen outputs were not cleaned")

    def test_hir_capture_and_stderr_are_bounded(self):
        def oversized_hir(argv, cwd, env, timeout):
            path = Path(next(arg.split("=", 1)[1] for arg in argv if arg.startswith("trust-body-census=")))
            path.write_text("x" * 512)
            return 0, b"diagnostic"
        with mock.patch.object(scorecard, "guarded_compile", side_effect=oversized_hir), \
                mock.patch.object(scorecard, "MAX_HIR_CENSUS_BYTES", 64):
            run = scorecard.run_one(str(self.compiler), str(self.source), "2024", 2,
                                    False, str(self.repo))
        self.assertIsNone(run["census_raw"])
        self.assertIn("bounded capture", run["error"])
        with mock.patch.object(scorecard, "MAX_HIR_CENSUS_BYTES", 64):
            parsed = scorecard.parse_compiler_census(
                compiler_census(str(self.source), self.rows, scorecard.file_sha256(self.source), False),
                input_path=str(self.source), lowering=False, exit_code=0)
        self.assertEqual(parsed["status"], "malformed")
        with mock.patch.object(scorecard, "MAX_STDERR_BYTES", 128):
            code, stderr = scorecard.guarded_compile(
                [sys.executable, "-c", "import sys; sys.stderr.write('x' * 10000)"],
                str(self.repo), dict(os.environ), 5)
        self.assertIsNone(code)
        self.assertLessEqual(len(stderr), 128)
        self.assertTrue(stderr.endswith(scorecard.STDERR_OVERFLOW_MARKER))

    def test_snapshot_precedes_compilation_and_failed_run_does_not_rewrite_it(self):
        output = self.repo / "report"
        scratch = self.repo / "scratch"
        scratch.mkdir()
        sentinel = scratch / "existing-user-file"
        sentinel.write_text("preserve")
        observed = []
        def compile_run(argv, cwd, env, timeout):
            manifest = json.loads((output / "input-manifest.json").read_text())
            observed.append(manifest["corpora"]["fixture"]["files"][0]["expected_outcome"])
            self.compile_control(argv, cwd, env, timeout)
            return 1, b"fixture compile failed"
        provenance = {"date_utc": "fixture", "repo_describe": "fixture", "seed": 1, "target": "fixture-target",
                      "trustc_sha256": scorecard.file_sha256(self.compiler)}
        argv = [str(ROOT / "scripts/trust_ir_producer_scorecard.py"), "--trustc", str(self.compiler),
                "--repo", str(self.repo), "--out-dir", str(output), "--scratch", str(scratch),
                "--no-ui-sample", "--corpus", "fixture=" + str(self.source)]
        with mock.patch.object(sys, "argv", argv), mock.patch.object(scorecard, "provenance", return_value=provenance), \
                mock.patch.object(scorecard, "guarded_compile", side_effect=compile_run):
            self.assertIsNone(scorecard.main())
        self.assertEqual(observed, ["ok"] * 4)
        data = json.loads((output / "data.json").read_text())
        corpus = data["corpora"]["fixture"]
        self.assertEqual(corpus["files"][0]["outcome"], "compile_fail")
        self.assertEqual(corpus["census_status"]["status"], "incomplete")
        evidence = corpus["census_evidence"]
        self.assertEqual(evidence["stage_closure_before"], evidence["stage_closure_after"])
        self.assertEqual(evidence["stage_closure_before"]["compiler_sha256"],
                         scorecard.file_sha256(self.compiler))
        self.assertEqual(sentinel.read_text(), "preserve")

    def test_duplicate_inputs_and_missing_or_changed_sources_fail_closed(self):
        with self.assertRaises(ValueError):
            scorecard.prepare_input_manifest([("fixture", [str(self.source)] * 2, None)], str(self.repo))
        manifest = scorecard.prepare_input_manifest([("fixture", [str(self.source)], None)], str(self.repo))
        sources = manifest["corpora"]["fixture"]["sources"]
        self.source.write_text("changed")
        self.assertIn("hash mismatch", " ".join(scorecard.current_source_errors(sources, str(self.repo))))
        self.source.unlink()
        self.assertIn("input unavailable", " ".join(scorecard.current_source_errors(sources, str(self.repo))))

    def test_disappeared_admitted_input_still_has_both_runs_and_a_failed_file_row(self):
        manifest = scorecard.prepare_input_manifest([("fixture", [str(self.source)], None)], str(self.repo))
        digest = manifest["corpora"]["fixture"]["files"][0]["sha256"]
        manifest_path = self.repo / "admitted-inputs.json"
        manifest_path.write_text(json.dumps(manifest))
        self.source.unlink()
        output = self.repo / "report"
        def missing_input(argv, cwd, env, timeout):
            raw = compiler_census(str(self.source), [], digest, "trust-ir-lower=on" in argv)
            census_path = Path(argv[8].split("=", 1)[1])
            census_path.write_text(raw.splitlines(True)[0])
            return 1, b"could not read input"
        provenance = {"date_utc": "fixture", "repo_describe": "fixture", "seed": 1,
                      "target": "fixture-target", "trustc_sha256": scorecard.file_sha256(self.compiler)}
        argv = ["scorecard", "--trustc", str(self.compiler), "--repo", str(self.repo),
                "--out-dir", str(output), "--input-manifest", str(manifest_path)]
        with mock.patch.object(sys, "argv", argv), mock.patch.object(scorecard, "provenance", return_value=provenance), \
                mock.patch.object(scorecard, "guarded_compile", side_effect=missing_input) as compiler:
            scorecard.main()
        self.assertEqual(compiler.call_count, 4)
        corpus = json.loads((output / "data.json").read_text())["corpora"]["fixture"]
        self.assertEqual(len(corpus["files"]), 1)
        self.assertEqual(corpus["files"][0]["outcome"], "compile_fail")
        self.assertEqual(corpus["input_census"]["files"][0]["expected_outcome"], "ok")
        self.assertEqual(corpus["input_census"]["files"][0]["sha256"], digest)
        self.assertEqual(corpus["census_status"]["status"], "incomplete")

    def test_nonempty_measurement_output_is_preserved(self):
        output = self.repo / "report"
        output.mkdir()
        artifact = output / "previous.json"
        artifact.write_text("previous evidence")
        argv = ["scorecard", "--trustc", str(self.compiler), "--repo", str(self.repo),
                "--out-dir", str(output), "--no-ui-sample", "--corpus", "fixture=" + str(self.source)]
        with mock.patch.object(sys, "argv", argv), self.assertRaises(SystemExit) as raised:
            scorecard.main()
        self.assertEqual(raised.exception.code, 2)
        self.assertEqual(artifact.read_text(), "previous evidence")


@unittest.skipUnless(LIVE_TRUSTC, "set TRUST_CENSUS_TEST_TRUSTC to the freshly built Trust compiler; no stock fallback")
class LiveTrustCompilerCensus(unittest.TestCase):
    def test_typechecked_call_observations_keep_raw_origins_and_unknown_dispatch(self):
        fixture = ROOT / "scripts/tests/fixtures/rust-hir-census/calls.rs"
        source_bytes = b"\xef\xbb\xbf" + fixture.read_bytes().replace(b"\n", b"\r\n")
        with tempfile.TemporaryDirectory(prefix="trust-live-hir-calls-") as scratch:
            source = Path(scratch) / "input.rs"
            source.write_bytes(source_bytes)
            report = Path(scratch) / "calls.jsonl"
            code, stderr = scorecard.guarded_compile(
                [LIVE_TRUSTC, str(source), "--crate-name=call_observations", "--crate-type=lib",
                 "--edition=2024", "--emit=metadata", "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
                 "-Zchecksum-hash-algorithm=sha256", "-Ztrust-body-census-calls",
                 "-Ztrust-body-census=" + str(report)], scratch, dict(os.environ), 60)
            self.assertIsNotNone(code, stderr)
            self.assertEqual(code, 0, stderr)
            raw = report.read_bytes()
        lines = raw.splitlines(keepends=True)
        records = [json.loads(line) for line in lines]
        self.assertEqual(len(records), 3)
        self.assertTrue(all(r["schema"] == "trust.rust.hir-body-census.v3" for r in records))
        self.assertEqual(records[2]["event"], "complete")
        self.assertEqual(records[2]["snapshot_sha256"], hashlib.sha256(lines[1]).hexdigest())
        self.assertEqual(records[2]["other_inputs"]["external_dependency_closure"], "unmeasured")
        observations = records[1]["call_observations"]
        self.assertFalse(observations["input_binding_complete"])
        self.assertEqual(observations["expanded_body_acquisition_completeness"], "unmeasured")
        self.assertEqual(observations["synthetic_coroutine_bodies_without_hir"], "not-visited")
        bodies = observations["bodies"]
        self.assertEqual(observations["body_count"], len(bodies))
        calls = [call for body in bodies for call in body["calls"]]

        def named(name):
            return [call for call in calls if call["caller"]["def_path"].endswith("::" + name)]

        for name in ("direct", "method", "through_alias"):
            with self.subTest(name=name):
                rows = named(name)
                self.assertEqual(len(rows), 1, rows)
                self.assertEqual(rows[0]["resolution"], "static_definition")
                self.assertIsNotNone(rows[0]["target"]["raw_span"])
        for name in ("generic", "dynamic", "trait_method", "pointer", "closure"):
            with self.subTest(name=name):
                rows = named(name)
                self.assertEqual(len(rows), 1, rows)
                self.assertEqual(rows[0]["resolution"], "unknown")
                self.assertIsNone(rows[0]["target"])
                self.assertEqual(rows[0]["declaration"] is None, name in ("pointer", "closure"))
        nested = [call for call in calls if "nested::{closure" in call["caller"]["def_path"]
                  and call["target"] is not None and call["target"]["def_path"].endswith("leaf")]
        self.assertEqual(len(nested), 1, nested)
        self.assertTrue(any(b["owner"]["def_path"].endswith("empty")
                            and b["explicit_hir_call_count"] == 0 for b in bodies))
        self.assertFalse(any(b["owner"]["def_path"].endswith("excluded") for b in bodies))
        direct = named("direct")[0]
        span, callee = direct["raw_span"], direct["callee_raw_span"]
        self.assertEqual(source_bytes[span["lo"]:span["hi"]], b"leaf()")
        self.assertEqual(source_bytes[callee["lo"]:callee["hi"]], b"leaf")
        loaded = next(s for s in records[1]["sources"] if s["file"] == span["file"])
        self.assertEqual(span["sha256"], loaded["sha256"])
        self.assertEqual(loaded["sha256"], hashlib.sha256(source_bytes).hexdigest())
        expanded = named("expanded")
        self.assertEqual(len(expanded), 2)
        self.assertTrue(all(c["from_expansion"] for c in expanded))
        self.assertNotEqual(expanded[0]["hir_local_id"], expanded[1]["hir_local_id"])

    def test_call_observation_failures_preserve_existing_output_and_omit_completion(self):
        with tempfile.TemporaryDirectory(prefix="trust-live-hir-call-failures-") as scratch:
            source = Path(scratch) / "input.rs"
            source.write_text("pub fn leaf() {}\n", encoding="utf-8")
            report = Path(scratch) / "existing.jsonl"
            sentinel = b"previous user artifact\n"
            report.write_bytes(sentinel)
            common = [LIVE_TRUSTC, str(source), "--crate-type=lib", "--emit=metadata",
                      "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
                      "-Zchecksum-hash-algorithm=sha256", "-Ztrust-body-census-calls"]
            code, stderr = scorecard.guarded_compile(
                common + ["-Ztrust-body-census=" + str(report)], scratch, dict(os.environ), 60)
            self.assertIsNotNone(code, stderr)
            self.assertNotEqual(code, 0, stderr)
            self.assertEqual(report.read_bytes(), sentinel)
            code, stderr = scorecard.guarded_compile(common, scratch, dict(os.environ), 60)
            self.assertIsNotNone(code, stderr)
            self.assertNotEqual(code, 0, stderr)
            self.assertIn(b"requires -Ztrust-body-census", stderr)
            source.write_text("pub fn broken() { let _: u32 = false; }\n", encoding="utf-8")
            failed = Path(scratch) / "error.jsonl"
            code, stderr = scorecard.guarded_compile(
                common + ["-Ztrust-body-census=" + str(failed)], scratch, dict(os.environ), 60)
            self.assertIsNotNone(code, stderr)
            self.assertNotEqual(code, 0, stderr)
            records = [json.loads(line) for line in failed.read_bytes().splitlines()]
            self.assertFalse(any(row["event"] == "complete" for row in records))

    def test_include_bytes_and_include_str_are_not_credited_as_source_hashes(self):
        with tempfile.TemporaryDirectory(prefix="trust-live-hir-includes-") as scratch:
            source = Path(scratch) / "includes.rs"
            binary, text = Path(scratch) / "payload.bin", Path(scratch) / "payload.txt"
            binary.write_bytes(b"\xff\x00\x80")
            text.write_text("UTF-8 macro input\n")
            source.write_text('pub const BYTES: &[u8] = include_bytes!("payload.bin");\n'
                              'pub const TEXT: &str = include_str!("payload.txt");\n')
            run = scorecard.run_one(LIVE_TRUSTC, str(source), "2024", 90, False, scratch)
        self.assertEqual(run["exit_code"], 0, run["stderr"])
        parsed = scorecard.parse_compiler_census(run["census_raw"], input_path=str(source),
                                               lowering=False, exit_code=run["exit_code"])
        self.assertEqual(parsed["status"], "input_closure_incomplete", parsed)
        self.assertEqual(set(parsed["other_inputs"]["tracked_files"]), {str(binary), str(text)})

    def test_full_hir_fixture_and_loaded_module_hashes(self):
        fixture = ROOT / "scripts/tests/fixtures/rust-hir-census/owners.rs"
        with tempfile.TemporaryDirectory(prefix="trust-live-hir-census-") as scratch:
            run = scorecard.run_one(LIVE_TRUSTC, str(fixture), "2024", 90, False, scratch)
        self.assertEqual(run["exit_code"], 0, run["stderr"])
        default_records = [json.loads(line) for line in run["census_raw"].splitlines()]
        self.assertTrue(all(row["schema"] == "trust.rust.hir-body-census.v2"
                            and "call_observations" not in row for row in default_records))
        parsed = scorecard.parse_compiler_census(run["census_raw"], input_path=str(fixture),
                                               lowering=False, exit_code=run["exit_code"])
        self.assertEqual(parsed["status"], "complete", parsed)
        names = [body["def"] for body in parsed["bodies"]]
        self.assertTrue(any("{closure" in name for name in names), names)
        self.assertTrue(any("{constant#" in name for name in names), names)
        self.assertTrue(any("NAMED" in name for name in names), names)
        self.assertTrue(any("STORED" in name for name in names), names)
        self.assertTrue(any("λ" in name for name in names), names)
        self.assertTrue(any(body["def_kind"] == "SyntheticCoroutineBody" for body in parsed["bodies"]), parsed)
        hashes = {source["file"]: source["sha256"] for source in parsed["sources"]}
        self.assertEqual(hashes[str(fixture)], scorecard.file_sha256(fixture))
        auxiliary = fixture.with_name("auxiliary.rs")
        self.assertEqual(hashes[str(auxiliary)], scorecard.file_sha256(auxiliary))
        self.assertNotIn("trust-ir-lower: differential", run["stderr"])

    def test_parse_failure_has_begin_without_complete_and_existing_file_is_preserved(self):
        with tempfile.TemporaryDirectory(prefix="trust-live-hir-failure-") as scratch:
            source = Path(scratch) / "broken.rs"
            source.write_text("pub fn broken( {\n")
            run = scorecard.run_one(LIVE_TRUSTC, str(source), "2024", 60, False, scratch)
            self.assertNotEqual(run["exit_code"], 0)
            parsed = scorecard.parse_compiler_census(run["census_raw"], input_path=str(source),
                                                   lowering=False, exit_code=run["exit_code"])
            self.assertEqual(parsed["status"], "incomplete", parsed)
            existing = Path(scratch) / "existing.jsonl"
            existing.write_text("user artifact\n")
            code, stderr = scorecard.guarded_compile([LIVE_TRUSTC, "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
                                     "-Zchecksum-hash-algorithm=sha256", "-Ztrust-body-census=" + str(existing),
                                     "--emit=metadata", "--crate-type=lib", str(source)],
                                    scratch, dict(os.environ), 60)
            self.assertIsNotNone(code, stderr)
            self.assertNotEqual(code, 0, stderr)
            self.assertEqual(existing.read_text(), "user artifact\n")


if __name__ == "__main__":
    unittest.main()
