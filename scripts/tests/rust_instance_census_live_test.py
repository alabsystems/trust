#!/usr/bin/env python3
"""Mock orchestration controls, not compiler observations or acceptance evidence.

Every subprocess entry point is mocked. Temporary fake binaries are data files,
never executable compiler substitutes; the real JSON census consumer is used.
"""

from contextlib import ExitStack, redirect_stderr, redirect_stdout
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "instance_census_live_under_test", ROOT / "scripts/tests/rust_instance_census_live.py")
live = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(live)
EXPECTED = {"baseline", "control", "subject", "metadata", "optimized-roots", "eager-roots",
            "existing-output", "missing-checksum", "invalid-source"}


class LiveOrchestration(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-mono-live-mocks-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.root = self.directory / "source"
        self.fixtures = self.root / "scripts/tests/fixtures/rust-instance-census"
        self.fixtures.mkdir(parents=True)
        for name in ("instances.rs", "invalid.rs", "unplaced.rs"):
            (self.fixtures / name).write_text("// mock source, never compiled: " + name + "\n")
        (self.root / "scripts/rust_instance_census.py").write_text("# mock pinned consumer bytes\n")
        self.compiler = self.directory / "toolchain/bin/trustc"
        self.compiler.parent.mkdir(parents=True)
        self.compiler.write_bytes(b"non-executable fake launcher\n")
        self.driver = self.compiler.parent.parent / "lib/librustc_driver-mock.dylib"
        self.driver.parent.mkdir()
        self.driver.write_bytes(b"non-executable fake driver\n")
        self.output = self.directory / "evidence"
        self.calls = []
        self.faults = {}

    def records(self, source, command):
        census = live.census
        identities = [f"{index:032x}" for index in range(1, 5)]
        kinds = ("item", "item", "shim-drop-glue", "static")
        definitions = ("mock::identity", "mock::identity", "core::drop_in_place", "mock::VALUE")
        items = [dict(id=identity, kind=kind, instance_detail=kind,
                      generic_args=("[u8]", "[u16]", "[Owner]", "")[index],
                      **{"def": definition}, def_path_hash="diagnostic-definition",
                      def_kind="Static" if kind == "static" else "Fn",
                      definition_is_local=kind != "shim-drop-glue", symbol=f"symbol{index}")
                 for index, (identity, kind, definition) in enumerate(zip(identities, kinds, definitions))]
        metadata = "--emit=metadata" in command
        unplaced = [identities[2]] if source.name == "unplaced.rs" else []
        header = dict(schema=census.SCHEMA, event="begin", scope=census.SCOPE, input=str(source),
                      compiler_version="rustc mock (trustc mock)", target="aarch64-apple-darwin",
                      edition="2024", direct_lowering="-Ztrust-ir-lower=on" in command,
                      verification_enabled=False,
                      collection_strategy="eager" if any(c.startswith("-Clink-dead-code") for c in command) else "lazy",
                      optimization="No" if "-Copt-level=0" in command else "Aggressive",
                      incremental=False, codegen_requested=not metadata,
                      identity_scheme="rustc-stable-mono-item-fingerprint-128-diagnostic-only",
                      unmeasured=list(census.UNMEASURED))
        snapshot = dict(schema=census.SCHEMA, event="mono_snapshot", item_count=len(items),
                        items=items, roots=identities, usage_edges=[], unplaced_items=unplaced,
                        codegen_units={"mock-cgu": [dict(id=identity, linkage="Internal",
                            visibility="Default", inlined=False) for identity in identities if identity not in unplaced]})
        footer = dict(schema=census.SCHEMA, event="complete",
                      status="unmeasured" if metadata else "collector_observed",
                      item_count=None if metadata else len(items), snapshot_sha256=None,
                      sources={str(source): "sha256=" + hashlib.sha256(source.read_bytes()).hexdigest()},
                      unmeasured=list(census.UNMEASURED), whole_program_complete=False)
        return [header, footer] if metadata else [header, snapshot, footer]

    @staticmethod
    def encode(records):
        lines = [json.dumps(row, sort_keys=True).encode() + b"\n" for row in records]
        if len(records) == 3:
            records[-1]["snapshot_sha256"] = hashlib.sha256(lines[1]).hexdigest()
            lines[-1] = json.dumps(records[-1], sort_keys=True).encode() + b"\n"
        return b"".join(lines)

    def fake_process(self, command, **kwargs):
        command = [str(value) for value in command]
        self.calls.append(command)
        self.assertEqual(command[0], str(self.compiler))
        if command[1:] == ["-vV"]:
            if self.faults.get("interrupt") == "version":
                raise KeyboardInterrupt()
            return subprocess.CompletedProcess(command, 0, "rustc mock (trustc mock)\ncommit-hash: " + "a" * 40 + "\n", "")
        folder = Path(kwargs["cwd"])
        label = folder.name
        source = Path(command[1])
        if self.faults.get("interrupt") == label:
            raise KeyboardInterrupt()
        if self.faults.get("exception") == label:
            raise OSError("mock process could not launch")
        if self.faults.get("timeout") == label:
            raise subprocess.TimeoutExpired(command, kwargs["timeout"])
        report_args = [arg for arg in command if arg.startswith("-Ztrust-instance-census=")]
        report = Path(report_args[0].split("=", 1)[1]) if report_args else None
        if label == "existing-output":
            self.assertTrue(report.is_file(), "collision control needs a real preexisting sentinel")
            kwargs["stderr"].write(b"error: Rust instance census: cannot create NEW output: already exists\n")
            if self.faults.get("overwrite_collision"):
                report.write_bytes(b"overwritten\n")
            return subprocess.CompletedProcess(command, 1)
        if label == "missing-checksum":
            kwargs["stderr"].write(b"error: -Ztrust-instance-census requires -Zchecksum-hash-algorithm=sha256\n")
            if self.faults.get("missing_checksum_report"):
                report.write_bytes(b"unexpected publication\n")
            return subprocess.CompletedProcess(command, 1)
        if report is not None and self.faults.get("missing_report") != label:
            records = self.records(source, command)
            if label == "invalid-source":
                records = records[:1]
                if self.faults.get("invalid_report") == "empty":
                    report.write_bytes(b"")
                elif self.faults.get("invalid_report") == "foreign":
                    report.write_bytes(b'{"event":"unrelated"}\n')
                elif self.faults.get("invalid_report") == "wrong-input":
                    records[0]["input"] = str(self.fixtures / "instances.rs")
                    report.write_bytes(self.encode(records))
                elif self.faults.get("invalid_report") == "complete":
                    report.write_bytes(self.encode(self.records(source, command)))
                else:
                    report.write_bytes(self.encode(records))
            else:
                report.write_bytes(self.encode(records))
        if label != "invalid-source" and self.faults.get("missing_outputs") != label:
            suffixes = ("rmeta",) if "--emit=metadata" in command else ("mir", "o")
            for suffix in suffixes:
                if self.faults.get("drop_suffix") == (label, suffix):
                    continue
                data = b"mock deterministic " + suffix.encode()
                if self.faults.get("changed_output") == label:
                    data += b" changed"
                (folder / ("instance_probe." + suffix)).write_bytes(data)
        if self.faults.get("source_drift") == label:
            source.write_bytes(source.read_bytes() + b"// changed during invocation\n")
        if self.faults.get("remove_driver") == label:
            self.driver.unlink()
        return subprocess.CompletedProcess(command, self.faults.get("failed", {}).get(label, 1 if label == "invalid-source" else 0))

    def invoke(self, output=None):
        real_digest = live.digest

        def checked_digest(path):
            if self.faults.get("interrupt_final_snapshot") and path == self.driver and self.calls:
                raise KeyboardInterrupt()
            return real_digest(path)

        with ExitStack() as stack:
            stack.enter_context(patch.object(live, "ROOT", self.root))
            stack.enter_context(patch.object(live, "FIXTURES", self.fixtures))
            stack.enter_context(patch.dict(live.os.environ, {}, clear=True))
            stack.enter_context(patch.object(live, "digest", side_effect=checked_digest))
            stack.enter_context(patch.object(live.subprocess, "run", side_effect=self.fake_process))
            stack.enter_context(patch.object(live.subprocess, "check_output", side_effect=lambda command, **_: "a" * 40 + "\n" if command[1] == "rev-parse" else ""))
            stack.enter_context(redirect_stdout(io.StringIO()))
            stack.enter_context(redirect_stderr(io.StringIO()))
            return live.main(["--trustc", str(self.compiler), "--out", str(output or self.output)])

    def result(self):
        return json.loads((self.output / "result.json").read_text())

    def assert_failed(self):
        self.assertEqual(self.invoke(), 1)
        result = self.result()
        self.assertEqual(result["status"], "failed", result)
        self.assertTrue(result["errors"])
        self.assertFalse(result["whole_program_complete"])
        return result

    def test_complete_mock_population_is_only_development_success(self):
        self.assertEqual(self.invoke(), 0, self.result() if (self.output / "result.json").is_file() else None)
        result = self.result()
        self.assertEqual(result["status"], "passed", result)
        self.assertEqual(set(result["runs"]), EXPECTED)
        self.assertFalse(result["whole_program_complete"])
        self.assertFalse(result["complete_toolchain_closure_bound"])
        self.assertTrue(result["inputs_stable"])
        self.assertEqual(len(self.calls), len(EXPECTED) + 1)

    def test_interrupt_before_any_case_is_not_empty_success(self):
        self.faults["interrupt"] = "version"
        result = self.assert_failed()
        self.assertEqual(result["runs"], {})
        self.assertTrue(any("KeyboardInterrupt" in error for error in result["errors"]))

    def test_interrupt_mid_population_retains_partial_failure(self):
        self.faults["interrupt"] = "subject"
        result = self.assert_failed()
        self.assertEqual(set(result["runs"]), {"baseline", "control"})
        self.assertTrue((self.output / "control/result.json").is_file())

    def test_failed_subject_cannot_borrow_its_complete_report(self):
        self.faults["failed"] = {"subject": 101}
        result = self.assert_failed()
        self.assertTrue(result["inputs_stable"])
        self.assertEqual(result["runs"]["subject"]["exit_code"], 101)
        self.assertEqual(result["runs"]["subject"]["census"]["status"], "compiler_failed")

    def test_timeout_and_missing_case_are_retained_failures(self):
        self.faults["timeout"] = "control"
        result = self.assert_failed()
        self.assertIsNone(result["runs"]["control"]["exit_code"])
        self.assertEqual(result["runs"]["control"]["census"]["status"], "compiler_failed")

    def test_process_launch_error_cannot_skip_required_cases(self):
        self.faults["exception"] = "metadata"
        result = self.assert_failed()
        self.assertNotEqual(set(result["runs"]), EXPECTED)

    def test_missing_report_is_not_an_empty_observed_population(self):
        self.faults["missing_report"] = "control"
        result = self.assert_failed()
        self.assertEqual(result["runs"]["control"]["census"]["status"], "missing")
        self.assertFalse((self.output / "control/census.jsonl").exists())
        self.assertEqual((self.output / "existing-census.jsonl").read_bytes(), b"existing-output-sentinel\n")

    def test_all_six_positive_cases_require_actual_artifacts(self):
        for label in ("baseline", "control", "subject", "metadata", "optimized-roots", "eager-roots"):
            with self.subTest(label=label):
                self.output = self.directory / ("no-artifacts-" + label)
                self.faults["missing_outputs"] = label
                result = self.assert_failed()
                self.assertEqual(result["runs"][label]["outputs"], {})

    def test_single_missing_requested_suffix_is_not_hidden_by_other_artifacts(self):
        for label in ("baseline", "control", "subject", "optimized-roots", "eager-roots"):
            for suffix in ("mir", "o"):
                with self.subTest(label=label, suffix=suffix):
                    self.output = self.directory / ("missing-" + label + "-" + suffix)
                    self.faults["drop_suffix"] = (label, suffix)
                    result = self.assert_failed()
                    self.assertTrue(result["runs"][label]["outputs"], "the other requested artifact really exists")

    def test_changed_observer_artifact_bytes_are_not_success(self):
        self.faults["changed_output"] = "control"
        self.assert_failed()

    def test_overwritten_collision_sentinel_is_rejected_even_with_exit_one(self):
        self.faults["overwrite_collision"] = True
        self.assert_failed()

    def test_checksum_refusal_cannot_publish_a_report(self):
        self.faults["missing_checksum_report"] = True
        self.assert_failed()

    def test_invalid_source_requires_a_real_exact_incomplete_begin(self):
        for index, mode in enumerate(("empty", "foreign", "wrong-input", "complete")):
            with self.subTest(mode=mode):
                self.output = self.directory / ("invalid-report-" + str(index))
                self.faults["invalid_report"] = mode
                self.assert_failed()

    def test_source_drift_cannot_pass_even_when_compiler_cases_do(self):
        self.faults["source_drift"] = "invalid-source"
        result = self.assert_failed()
        self.assertFalse(result["inputs_stable"])

    def test_missing_initial_fixture_does_not_produce_success(self):
        (self.fixtures / "instances.rs").unlink()
        result = self.assert_failed()
        self.assertEqual(self.calls, [])
        self.assertFalse(result["inputs_stable"])

    def test_disappearing_final_input_is_a_retained_failure(self):
        self.faults["remove_driver"] = "invalid-source"
        result = self.assert_failed()
        self.assertFalse(result["inputs_stable"])

    def test_final_snapshot_interrupt_is_not_a_complete_population_success(self):
        self.faults["interrupt_final_snapshot"] = True
        result = self.assert_failed()
        self.assertEqual(set(result["runs"]), EXPECTED)
        self.assertFalse(result["inputs_stable"])
        self.assertIn("KeyboardInterrupt", json.loads((self.output / "after.json").read_text())["snapshot_failed"])

    def test_existing_or_internal_output_is_refused_without_touching_sources(self):
        existing = self.directory / "existing"
        existing.mkdir()
        sentinel = existing / "keep.txt"
        sentinel.write_bytes(b"retain me")
        dangling = self.directory / "dangling"
        dangling.symlink_to(self.directory / "absent")
        alias = self.directory / "source-alias"
        alias.symlink_to(self.root, target_is_directory=True)
        for output in (existing, dangling, self.root / "new-output", alias / "new-output"):
            with self.subTest(output=output), self.assertRaises(SystemExit) as error:
                self.invoke(output)
            self.assertNotEqual(error.exception.code, 0)
            self.assertEqual(sentinel.read_bytes(), b"retain me")
        self.assertEqual(self.calls, [])
        self.assertFalse((self.root / "new-output").exists())


class AllocationComparison(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location(
            "instance_census_comparison_fixtures", ROOT / "scripts/tests/rust_instance_census_test.py")
        self.fixtures = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.fixtures)

    def valid_snapshot(self, records):
        result = live.census.parse_census(self.fixtures.encode(records),
                                         input_path="/fixture/instances.rs", exit_code=0)
        self.assertEqual(result["status"], "collector_observed", result)
        return result["snapshot"]

    def test_run_local_ids_are_renamed_without_mutating_reports(self):
        original = self.fixtures.fixture_v2()
        renamed = copy.deepcopy(original)
        for row in renamed[1]["dependency_nodes"] + renamed[1]["dependency_occurrences"]:
            for key, value in list(row.items()):
                if type(value) is str and value.startswith("alloc:"):
                    row[key] = "alloc:" + str(1000 - int(value.split(":")[1]))
        renamed[1]["dependency_nodes"].sort(key=lambda row: row["id"])
        a, b = self.valid_snapshot(original), self.valid_snapshot(renamed)
        before = copy.deepcopy((a, b))
        self.assertNotEqual(a, b)
        self.assertEqual(live.comparable_snapshot(a), live.comparable_snapshot(b))
        self.assertEqual((a, b), before)

    def test_equal_metadata_does_not_hide_changed_aliasing(self):
        original = self.fixtures.fixture_v2()
        changed = copy.deepcopy(original)
        rows = changed[1]["dependency_occurrences"]
        start = next(i for i, row in enumerate(rows)
                     if row["kind"] == "allocation-root" and row["form"] == "indirect")
        end = next(i for i in range(start + 1, len(rows)) if rows[i]["kind"] == "allocation-root")
        # Rename the complete encountered value, preserving its paired calls.
        # Other references still distinguish the two same-metadata allocations.
        for row in rows[start:end]:
            for key in ("source", "target"):
                if row.get(key) == "alloc:1":
                    row[key] = "alloc:2"
        self.assertNotEqual(live.comparable_snapshot(self.valid_snapshot(original)),
                            live.comparable_snapshot(self.valid_snapshot(changed)))

    def test_merging_distinct_same_metadata_allocations_is_detected(self):
        original = self.fixtures.fixture_v2()
        changed = copy.deepcopy(original)
        changed[1]["dependency_nodes"] = [row for row in changed[1]["dependency_nodes"] if row["id"] != "alloc:2"]
        for row in changed[1]["dependency_occurrences"]:
            for key in ("source", "target"):
                if row.get(key) == "alloc:2":
                    row[key] = "alloc:1"
        self.fixtures.recount_dependencies(changed)
        self.assertNotEqual(live.comparable_snapshot(self.valid_snapshot(original)),
                            live.comparable_snapshot(self.valid_snapshot(changed)))

    def test_v1_keeps_exact_comparison(self):
        snapshot = self.valid_snapshot(self.fixtures.fixture())
        self.assertEqual(live.comparable_snapshot(snapshot), snapshot)
        self.assertIsNone(live.comparable_snapshot(None))

    def test_v3_root_only_allocations_and_shared_aliases_are_renamed(self):
        original = self.fixtures.fixture_v3()
        renamed = copy.deepcopy(original)
        for table in ("dependency_nodes", "dependency_occurrences", "eager_const_root_occurrences"):
            for row in renamed[1][table]:
                for key, value in list(row.items()):
                    if type(value) is str and value.startswith("alloc:"):
                        row[key] = "alloc:" + str(1000 - int(value.split(":")[1]))
        renamed[1]["dependency_nodes"].sort(key=lambda row: row["id"])
        a, b = self.valid_snapshot(original), self.valid_snapshot(renamed)
        before = copy.deepcopy((a, b))
        self.assertNotEqual(a, b)
        self.assertEqual(live.comparable_snapshot(a), live.comparable_snapshot(b))
        self.assertEqual((a, b), before)

    def test_v3_root_alias_change_is_not_content_deduplicated(self):
        original = self.fixtures.fixture_v3()
        changed = copy.deepcopy(original)
        node = next(row for row in changed[1]["dependency_nodes"] if row["id"] == "alloc:78")
        changed[1]["dependency_nodes"].append(dict(node, id="alloc:79"))
        changed[1]["dependency_nodes"].sort(key=lambda row: row["id"])
        owner = changed[1]["eager_const_root_owners"][1]["id"]
        for row in changed[1]["eager_const_root_occurrences"]:
            if row["owner"] == owner and row.get("target") == "alloc:78":
                row["target"] = "alloc:79"
        self.fixtures.recount_dependencies(changed)
        self.assertNotEqual(live.comparable_snapshot(self.valid_snapshot(original)),
                            live.comparable_snapshot(self.valid_snapshot(changed)))

    def test_v3_empty_root_owner_is_retained_in_comparison(self):
        original = self.fixtures.fixture_v3()
        changed = copy.deepcopy(original)
        changed[1]["eager_const_root_owners"].pop()
        self.fixtures.recount_eager_roots(changed)
        self.assertNotEqual(live.comparable_snapshot(self.valid_snapshot(original)),
                            live.comparable_snapshot(self.valid_snapshot(changed)))


if __name__ == "__main__":
    unittest.main()
