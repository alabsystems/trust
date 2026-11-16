#!/usr/bin/env python3
"""Adversarial, runner-protocol tests for the actual fail-closed G7 checker."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/completion_gates/check_g7_codegen_authority.py"
CHECKER_ID = "trust.two-language.g7.codegen-authority/v3"
CONTRACT_ID = "trust.two-language.contract.codegen-surface"
REQUIRED = (
    "exact_linked_module_is_codegen_input",
    "full_admitted_codegen_surface",
    "zero_unproved_fallbacks",
    "machine_equivalence_evidence",
    "objects_biject_admitted_modules",
    "authorized_codegen_matrix_complete",
    "typed_module_object_executable_lineage",
    "linked_executable_composition_validated",
    "runtime_startup_syslib_closure_bound",
)
FIELDS = (
    "target_id", "abi_id", "crate_type", "runtime_id", "startup_id",
    "linker_id", "unwind_mode", "debug_mode", "opt_level", "profile_id",
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def tagged_digest(tag: str) -> str:
    return digest(tag.encode("utf-8"))


def write_json(path: Path, doc: dict) -> dict[str, str]:
    data = json.dumps(doc, sort_keys=True).encode("utf-8")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return {"path": str(path), "sha256": digest(data)}


class G7Fixture:
    def __init__(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="trust-g7-failclosed-")
        self.root = Path(self.tmp.name).resolve()
        self.evidence = self.root / "evidence"
        self.evidence.mkdir()
        self.linked = self.root / "linked.trust-ir.bin"
        self.linked.write_bytes(b"TRUST_IR\x00linked")
        self.policy = self.root / "policy.json"
        self.contract = self.root / "codegen-contract.json"
        self.artifacts: dict[str, dict[str, str]] = {}
        for name in ("toolchain", "corpus", "subject-graph", "release", "policy-auth"):
            (self.root / f"{name}.json").write_text("{}", encoding="utf-8")

        self.cells = [
            {
                "id": f"cell-{crate_type}", "target_id": "aarch64-apple-darwin",
                "abi_id": "rust", "crate_type": crate_type, "runtime_id": "std",
                "startup_id": "rustc-entry", "linker_id": "ld64",
                "unwind_mode": "abort", "debug_mode": "none", "opt_level": "0",
                "profile_id": "dev",
            }
            for crate_type in ("rlib", "bin")
        ]
        contract_ref = write_json(self.contract, {
            "schema": "trust.two-language.codegen-surface-contract/v2",
            "goal_id": "TRUST-TWO-LANGUAGE-100",
            "repository_id": "https://github.com/alabsystems/trust",
            "translation_relation": {"id": "machine", "sha256": tagged_digest("relation")},
            "targets": [{
                "id": "aarch64-apple-darwin", "triple": "aarch64-apple-darwin",
                "abis": ["rust"], "crate_types": ["rlib", "bin"],
                "runtimes": ["std"], "startups": ["rustc-entry"],
                "linkers": ["ld64"], "unwind_modes": ["abort"],
                "debug_modes": ["none"], "opt_levels": ["0"],
                "profiles": ["dev"],
            }],
            "matrix_cells": self.cells,
        })
        self.policy_doc = {
            "contracts": {"codegen_surface": {
                "id": CONTRACT_ID,
                "path": self.contract.name,
                "sha256": contract_ref["sha256"],
            }}
        }
        self.save_policy()

        self.receipt = {
            "schema": "trust.two-language.codegen-receipt/v1",
            "frontend": "trust-ir",
            "linked_module_sha256": digest(self.linked.read_bytes()),
            "admitted_functions": ["main", "m::cleanWsum"],
            "objects": [{
                "path": "out/nonexistent.o", "sha256": tagged_digest("object"),
                "module_id": "crate-a", "functions": ["main", "m::cleanWsum"],
            }],
            "refusals": [], "fallbacks": 0, "output_gate": "on",
        }
        receipt_ref = self.write("exact_linked_module_is_codegen_input", self.receipt)
        self.artifacts["full_admitted_codegen_surface"] = dict(receipt_ref)
        self.artifacts["zero_unproved_fallbacks"] = dict(receipt_ref)
        self.write("machine_equivalence_evidence", {
            "schema": "trust.two-language.machine-equivalence/v1",
            "functions": [
                {"name": name, "object_sha256": tagged_digest("object"),
                 "verdict": "preserved", "method": "translation-validation"}
                for name in ("main", "m::cleanWsum")
            ],
        })
        self.write("objects_biject_admitted_modules", {
            "schema": "trust.two-language.object-module-bijection/v1",
            "pairs": [{"module_id": "crate-a", "object_sha256": tagged_digest("object")}],
        })
        self.write("authorized_codegen_matrix_complete", {
            "schema": "trust.two-language.codegen-matrix-observation/v1",
            "rows": [
                {"codegen_cell_id": cell["id"],
                 **{field: cell[field] for field in FIELDS},
                 "object_sha256": tagged_digest(cell["id"])}
                for cell in self.cells
            ],
        })
        self.write("typed_module_object_executable_lineage", {
            "schema": "trust.two-language.executable-lineage/v1",
            "chain": [{
                "module_sha256": digest(self.linked.read_bytes()),
                "object_sha256": tagged_digest("object"),
                "executable_sha256": tagged_digest("exe"), "module_typed": True,
            }],
        })
        self.write("linked_executable_composition_validated", {
            "schema": "trust.two-language.executable-composition/v1",
            "executables": [{
                "executable_sha256": tagged_digest("exe"),
                "composition_verdict": "validated",
                "components": [{"name": "object", "sha256": tagged_digest("object")}],
            }],
        })
        self.write("runtime_startup_syslib_closure_bound", {
            "schema": "trust.two-language.runtime-closure/v1",
            "runtime_id": "std", "startup_id": "rustc-entry", "closure": "bound",
            "syslibs": [{"name": "libSystem", "sha256": tagged_digest("libSystem")}],
        })

    def save_policy(self) -> None:
        write_json(self.policy, self.policy_doc)

    def save_contract(self, contract: dict) -> None:
        self.policy_doc["contracts"]["codegen_surface"]["sha256"] = write_json(self.contract, contract)["sha256"]
        self.save_policy()

    def write_receipt(self, receipt: dict) -> None:
        """Bind the same receipt bytes to all three codegen-receipt checks."""
        ref = self.write("exact_linked_module_is_codegen_input", receipt)
        self.artifacts["full_admitted_codegen_surface"] = dict(ref)
        self.artifacts["zero_unproved_fallbacks"] = dict(ref)

    def write(self, check_id: str, doc: dict) -> dict[str, str]:
        ref = write_json(self.evidence / f"{check_id}.json", doc)
        ref["path"] = str(Path(ref["path"]).relative_to(self.root))
        self.artifacts[check_id] = ref
        return ref

    def document(self, check_id: str) -> dict:
        return json.loads((self.root / self.artifacts[check_id]["path"]).read_text())

    def run(self, *, policy_digest: str | None = None, evidence_digest: str | None = None,
            linked_digest: str | None = None, bundle_bytes: bytes | None = None,
            timeout: float = 30) -> tuple[int, dict, str]:
        bundle = self.root / "bundle.json"
        if bundle_bytes is None:
            write_json(bundle, {
                "schema": "trust.two-language.gate-evidence/v1",
                "gate": "G7", "checker": CHECKER_ID,
                "artifacts": self.artifacts,
            })
        else:
            bundle.write_bytes(bundle_bytes)
        paths = {
            "toolchain-manifest": self.root / "toolchain.json",
            "corpus-manifest": self.root / "corpus.json",
            "subject-graph": self.root / "subject-graph.json",
            "linked-module": self.linked,
            "release-artifact": self.root / "release.json",
            "authority-policy": self.policy,
            "policy-authorization": self.root / "policy-auth.json",
        }
        command = [
            sys.executable, "-I", str(CHECKER),
            "--verify-evidence", str(bundle), "--root", str(self.root),
        ]
        for flag, path in paths.items():
            command.extend((f"--{flag}", str(path)))
        command.extend((
            "--acceptance-run-id", "run-1", "--source-revision", "a" * 40,
            "--checker-sha256", digest(CHECKER.read_bytes()),
            "--evidence-sha256", evidence_digest or digest(bundle.read_bytes()),
            "--toolchain-sha256", digest(paths["toolchain-manifest"].read_bytes()),
            "--corpus-manifest-sha256", digest(paths["corpus-manifest"].read_bytes()),
            "--subject-graph-sha256", digest(paths["subject-graph"].read_bytes()),
            "--linked-module-sha256", linked_digest or digest(self.linked.read_bytes()),
            "--release-artifact-sha256", digest(paths["release-artifact"].read_bytes()),
            "--authority-policy-sha256", policy_digest or digest(self.policy.read_bytes()),
            "--policy-authorization-sha256", digest(paths["policy-authorization"].read_bytes()),
        ))
        process = subprocess.run(
            command, cwd=self.root, check=False, capture_output=True, text=True,
            timeout=timeout,
        )
        return process.returncode, json.loads(process.stdout), process.stderr


class G7FailClosedTests(unittest.TestCase):
    def fixture(self) -> G7Fixture:
        fixture = G7Fixture()
        self.addCleanup(fixture.tmp.cleanup)
        return fixture

    def assert_red(self, fixture: G7Fixture) -> tuple[dict, str]:
        code, verdict, stderr = fixture.run()
        self.assertEqual(code, 1, stderr)
        self.assertIs(verdict["passed"], False)
        self.assertEqual([row["id"] for row in verdict["checks"]], list(REQUIRED))
        self.assertTrue(all(row["passed"] is False for row in verdict["checks"]))
        return verdict, stderr

    def test_authored_complete_bundle_cannot_mint_any_g7_conjunct(self) -> None:
        fixture = self.fixture()
        self.assertFalse((fixture.root / "out/nonexistent.o").exists())
        receipt_digest = fixture.receipt["objects"][0]["sha256"]
        matrix_digests = {
            row["object_sha256"]
            for row in fixture.document("authorized_codegen_matrix_complete")["rows"]
        }
        self.assertNotIn(receipt_digest, matrix_digests)
        verdict, stderr = self.assert_red(fixture)
        for row in verdict["checks"]:
            self.assertTrue(row["artifacts"], row["id"])
            self.assertIn(f"G7: {row['id']}:", stderr)
        self.assertIn("no independent replay checks a translation proof", stderr)
        self.assertIn("signed cells and authored observations do not prove", stderr)

    def test_runner_shaped_named_contract_is_resolved(self) -> None:
        _verdict, stderr = self.assert_red(self.fixture())
        self.assertIn("authorized_codegen_matrix_complete: signed cells", stderr)
        self.assertNotIn("artifact schema must be", stderr)

    def test_wrong_contract_id_is_diagnosed(self) -> None:
        fixture = self.fixture()
        fixture.policy_doc["contracts"]["codegen_surface"]["id"] = "wrong-id"
        fixture.save_policy()
        _verdict, stderr = self.assert_red(fixture)
        self.assertIn(f"codegen_surface contract id must be {CONTRACT_ID!r}", stderr)

    def test_wrong_contract_digest_is_diagnosed(self) -> None:
        fixture = self.fixture()
        fixture.policy_doc["contracts"]["codegen_surface"]["sha256"] = "0" * 64
        fixture.save_policy()
        _verdict, stderr = self.assert_red(fixture)
        self.assertIn("codegen_surface contract reference is not bound: artifact hash mismatch", stderr)

    def test_runner_bound_policy_digest_is_rechecked(self) -> None:
        fixture = self.fixture()
        code, verdict, stderr = fixture.run(policy_digest="0" * 64)
        self.assertEqual(code, 1)
        self.assertIs(verdict["passed"], False)
        self.assertIn("authority policy digest differs from --authority-policy-sha256", stderr)

    def test_missing_translation_row_is_named(self) -> None:
        fixture = self.fixture()
        doc = fixture.document("machine_equivalence_evidence")
        doc["functions"] = doc["functions"][:1]
        fixture.write("machine_equivalence_evidence", doc)
        _verdict, stderr = self.assert_red(fixture)
        self.assertIn("missing translation rows for admitted functions: ['m::cleanWsum']", stderr)

    def test_duplicate_translation_row_is_named(self) -> None:
        fixture = self.fixture()
        doc = fixture.document("machine_equivalence_evidence")
        doc["functions"].append(dict(doc["functions"][0]))
        fixture.write("machine_equivalence_evidence", doc)
        _verdict, stderr = self.assert_red(fixture)
        self.assertIn("duplicate translation row for function 'main'", stderr)

    def test_missing_matrix_row_is_named(self) -> None:
        fixture = self.fixture()
        doc = fixture.document("authorized_codegen_matrix_complete")
        doc["rows"] = doc["rows"][:1]
        fixture.write("authorized_codegen_matrix_complete", doc)
        _verdict, stderr = self.assert_red(fixture)
        self.assertIn("missing matrix observations for signed cells: ['cell-bin']", stderr)

    def test_duplicate_matrix_row_is_named(self) -> None:
        fixture = self.fixture()
        doc = fixture.document("authorized_codegen_matrix_complete")
        doc["rows"].append(dict(doc["rows"][0]))
        fixture.write("authorized_codegen_matrix_complete", doc)
        _verdict, stderr = self.assert_red(fixture)
        self.assertIn("duplicate matrix observation for signed cell 'cell-rlib'", stderr)

    def check_line(self, fixture: G7Fixture, check_id: str) -> str:
        _verdict, stderr = self.assert_red(fixture)
        lines = [line for line in stderr.splitlines() if line.startswith(f"G7: {check_id}:")]
        self.assertEqual(len(lines), 1, stderr)
        return lines[0]

    def test_fallbacks_must_be_the_integer_zero(self) -> None:
        # `doc.get("fallbacks") != 0` accepted `false`, `0.0` and `-0.0`.
        for value in (False, 0.0, -0.0):
            with self.subTest(fallbacks=value):
                fixture = self.fixture()
                fixture.write_receipt(dict(fixture.receipt, fallbacks=value))
                line = self.check_line(fixture, "zero_unproved_fallbacks")
                self.assertIn(f"unproved fallbacks recorded: {value!r}", line)
                self.assertNotIn("no authenticated compiler trace", line)

    def test_receipt_objects_are_one_module_per_object_and_one_object_per_function(self) -> None:
        def second_object(**fields):
            obj = {"path": "out/b.o", "sha256": tagged_digest("object-b"),
                   "module_id": "crate-b", "functions": ["main"]}
            obj.update(fields)
            return obj

        missing_module = dict(second_object())
        missing_module.pop("module_id")
        cases = (
            (second_object(), "function 'main' is emitted by both module 'crate-a' and module 'crate-b'"),
            (second_object(module_id="crate-a", functions=[]), "module 'crate-a' is emitted as more than one object"),
            (dict(missing_module, functions=[]), "every object must name its module_id as a non-empty string"),
            (second_object(module_id=True, functions=[]), "every object must name its module_id as a non-empty string"),
        )
        for obj, diagnostic in cases:
            with self.subTest(expect=diagnostic):
                fixture = self.fixture()
                receipt = json.loads(json.dumps(fixture.receipt))
                receipt["objects"].append(obj)
                fixture.write_receipt(receipt)
                line = self.check_line(fixture, "full_admitted_codegen_surface")
                self.assertIn(diagnostic, line)
                self.assertNotIn("no producer-bound census", line)

    def test_syslib_name_must_be_a_string(self) -> None:
        fixture = self.fixture()
        doc = fixture.document("runtime_startup_syslib_closure_bound")
        doc["syslibs"][0]["name"] = True
        fixture.write("runtime_startup_syslib_closure_bound", doc)
        line = self.check_line(fixture, "runtime_startup_syslib_closure_bound")
        self.assertIn("every syslib must be named", line)

    def test_lineage_starts_from_the_linked_module(self) -> None:
        fixture = self.fixture()
        doc = fixture.document("typed_module_object_executable_lineage")
        doc["chain"][0]["module_sha256"] = tagged_digest("some-other-module")
        fixture.write("typed_module_object_executable_lineage", doc)
        line = self.check_line(fixture, "typed_module_object_executable_lineage")
        self.assertIn("not the acceptance run's linked module", line)
        self.assertNotIn("no independently checked typed-module", line)

    def test_equivalence_rows_name_the_receipt_object_that_emits_the_function(self) -> None:
        fixture = self.fixture()
        doc = fixture.document("machine_equivalence_evidence")
        doc["functions"][1]["object_sha256"] = tagged_digest("unrelated-object")
        fixture.write("machine_equivalence_evidence", doc)
        line = self.check_line(fixture, "machine_equivalence_evidence")
        self.assertIn("function 'm::cleanWsum' translation row names object", line)
        self.assertIn("but the codegen receipt emits it in object", line)

    def test_bijection_pairs_are_the_receipt_objects(self) -> None:
        for pair in ({"module_id": "crate-z", "object_sha256": tagged_digest("object")},
                     {"module_id": "crate-a", "object_sha256": tagged_digest("unrelated")}):
            with self.subTest(pair=pair):
                fixture = self.fixture()
                fixture.write("objects_biject_admitted_modules", {
                    "schema": "trust.two-language.object-module-bijection/v1", "pairs": [pair]})
                line = self.check_line(fixture, "objects_biject_admitted_modules")
                self.assertIn("bijection pairs are not the codegen receipt's objects", line)

    def test_signed_cell_fields_are_strings_matched_exactly(self) -> None:
        # `row.get(field) != cell.get(field)` let a field absent from both the signed
        # cell and the observation match (None == None), and 0 match `false`.
        contract = json.loads(self.fixture().contract.read_text())

        def drop(cell, row):
            cell.pop("debug_mode"); row.pop("debug_mode")

        def falsy(cell, row):
            cell["opt_level"] = 0; row["opt_level"] = False

        for mutate, field in ((drop, "debug_mode"), (falsy, "opt_level")):
            with self.subTest(field=field):
                fixture = self.fixture()
                signed = json.loads(json.dumps(contract))
                doc = fixture.document("authorized_codegen_matrix_complete")
                mutate(signed["matrix_cells"][0], doc["rows"][0])
                fixture.save_contract(signed)
                fixture.write("authorized_codegen_matrix_complete", doc)
                line = self.check_line(fixture, "authorized_codegen_matrix_complete")
                self.assertIn(f"signed matrix cell 'cell-rlib' must name `{field}` as a non-empty string", line)

    def test_bundle_bytes_must_hash_to_the_bound_evidence_digest(self) -> None:
        fixture = self.fixture()
        code, verdict, stderr = fixture.run(evidence_digest="e" * 64)
        self.assertEqual(code, 1)
        self.assertIs(verdict["passed"], False)
        self.assertIn("G7: evidence bundle digest differs from --evidence-sha256", stderr)
        self.assertTrue(all(row["passed"] is False and not row["artifacts"] for row in verdict["checks"]))

    def test_linked_module_bytes_must_hash_to_the_bound_digest(self) -> None:
        # The receipt, the lineage and --linked-module-sha256 all agree; only the
        # --linked-module FILE differs.  The checker never hashed that file.
        fixture = self.fixture()
        bound = digest(fixture.linked.read_bytes())
        fixture.linked.write_bytes(b"TRUST_IR\x00a-different-module")
        code, verdict, stderr = fixture.run(linked_digest=bound)
        self.assertEqual(code, 1)
        self.assertIs(verdict["passed"], False)
        self.assertIn("G7: --linked-module bytes differ from --linked-module-sha256", stderr)
        for check_id in ("exact_linked_module_is_codegen_input", "typed_module_object_executable_lineage"):
            self.assertIn(f"G7: {check_id}: --linked-module bytes differ", stderr)

    def test_nesting_is_bounded_by_the_checker_not_the_interpreter(self) -> None:
        # A newer json decoder accepts nesting far deeper than `repr` can print, so
        # quoting a deep `refusals` value died with no verdict.
        for depth in (100, 100_000):
            with self.subTest(depth=depth):
                fixture = self.fixture()
                text = json.dumps(fixture.receipt, sort_keys=True)
                marker = '"refusals": []'
                self.assertEqual(text.count(marker), 1)
                data = text.replace(marker, '"refusals": ' + "[" * depth + "]" * depth).encode()
                path = fixture.evidence / "deep.receipt.json"
                path.write_bytes(data)
                ref = {"path": str(path.relative_to(fixture.root)), "sha256": digest(data)}
                for check_id in ("exact_linked_module_is_codegen_input", "full_admitted_codegen_surface",
                                 "zero_unproved_fallbacks"):
                    fixture.artifacts[check_id] = dict(ref)
                line = self.check_line(fixture, "full_admitted_codegen_surface")
                self.assertIn("artifact is not a JSON document: JSON nests deeper than 64", line)

    def test_nesting_scan_is_linear_on_unterminated_strings(self) -> None:
        # A nesting pre-scan that re-scanned an unterminated string from each
        # escaped quote was quadratic: ~0.5 MB outlived the runner's timeout and
        # the checker printed no verdict.  The shared depth scan must stay linear
        # on authored text the decoder refuses in well under a millisecond.
        data = ('{"schema": "' + '\\"' * 200_000).encode()
        with self.subTest(where="artifact"):
            fixture = self.fixture()
            path = fixture.evidence / "unterminated.json"
            path.write_bytes(data)
            ref = {"path": str(path.relative_to(fixture.root)), "sha256": digest(data)}
            for check_id in ("exact_linked_module_is_codegen_input", "full_admitted_codegen_surface",
                             "zero_unproved_fallbacks"):
                fixture.artifacts[check_id] = dict(ref)
            code, verdict, stderr = fixture.run(timeout=20)
            self.assertEqual(code, 1, stderr)
            self.assertIs(verdict["passed"], False)
            self.assertTrue(all(row["passed"] is False for row in verdict["checks"]))
            lines = [l for l in stderr.splitlines() if l.startswith("G7: full_admitted_codegen_surface:")]
            self.assertEqual(len(lines), 1, stderr)
            self.assertIn("artifact is not a JSON document", lines[0])
        with self.subTest(where="bundle"):
            fixture = self.fixture()
            code, verdict, stderr = fixture.run(bundle_bytes=data, timeout=20)
            self.assertEqual(code, 1, stderr)
            self.assertIs(verdict["passed"], False)
            self.assertTrue(all(row["passed"] is False for row in verdict["checks"]))
            self.assertIn("G7: evidence bundle unreadable:", stderr)

    def test_unstatable_artifact_path_still_yields_one_verdict(self) -> None:
        # Python 3.9's `Path.is_file` re-raises ENAMETOOLONG: the checker died with
        # a traceback and an empty stdout instead of refusing the row.
        fixture = self.fixture()
        fixture.artifacts["runtime_startup_syslib_closure_bound"]["path"] = "evidence/" + "a" * 300 + ".json"
        line = self.check_line(fixture, "runtime_startup_syslib_closure_bound")
        self.assertTrue("artifact path cannot be inspected" in line
                        or "artifact file does not exist" in line, line)

    def test_conflicting_codegen_receipts_are_diagnosed(self) -> None:
        fixture = self.fixture()
        other = dict(fixture.receipt, fallbacks=1)
        fixture.write("zero_unproved_fallbacks", other)
        _verdict, stderr = self.assert_red(fixture)
        self.assertIn("the three codegen-receipt checks must bind identical receipt bytes", stderr)


if __name__ == "__main__":
    unittest.main()
