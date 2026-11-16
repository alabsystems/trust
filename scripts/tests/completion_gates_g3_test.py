#!/usr/bin/env python3
"""Focused mutation controls for the schema-owned G3 checker."""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import os
import py_compile
import runpy
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/completion_gates/check_g3_producer_totality.py"
GATE_SCRIPT = ROOT / "scripts/two_language_completion_gate.py"


def load_gate():
    spec = importlib.util.spec_from_file_location("g3_test_completion_gate", GATE_SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


# The runner that executes this checker.
GATE = load_gate()

ZERO = "0" * 64
ONE = "1" * 64
TWO = "2" * 64
REV = "a" * 40
RUN = "g3-test-run"
REQUIRED = (
    "admitted_file_manifest_exact", "reachable_body_census_exact",
    "rust_zero_producer_residue", "lean_zero_producer_residue",
    "all_joined_modules_valid", "no_denominator_exclusions",
    "subject_index_roots_match",
)


def hash_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value: object, *, ascii: bool = True) -> str:
    return hash_bytes(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                 ensure_ascii=ascii).encode("utf-8"))


def plant_bytecode(module: Path, source: str) -> Path:
    """Plant an unchecked-hash .pyc of ``source`` where CPython caches ``module``.

    CPython loads an unchecked hash-based .pyc without comparing it to the
    source it claims to cache.
    """
    cache = module.parent / "__pycache__" / f"{module.stem}.{sys.implementation.cache_tag}.pyc"
    cache.parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="forged-bytecode-") as scratch:
        forged = Path(scratch) / module.name
        forged.write_text(source, encoding="utf-8")
        py_compile.compile(str(forged), cfile=str(cache), dfile=str(module), doraise=True,
                           invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH)
    return cache


def bytecode_in(root: Path) -> set[Path]:
    """Every bytecode file and __pycache__ directory under ``root``."""
    return {path for path in root.rglob("*") if path.suffix == ".pyc" or path.name == "__pycache__"}


# Every anomaly field the producer's parse_bodies measures, at zero.
ZERO_ANOMALIES = {"duplicate_differential_events": 0, "duplicate_unsupported_events": 0,
                  "unsupported_event_without_differential_event": []}


# A census that reports the replay complete, as a substituted one could.
FORGED_CENSUS = """\
import json, os, pathlib, sys
pathlib.Path({marker!r}).write_text("ran")
sys.stdout.write(json.dumps({{"complete": True, "aggregate_source": "recomputed_from_files",
                              "artifact_errors": [], "result": "pass"}}))
sys.stdout.flush()
os._exit(0)
"""


class GateRoot:
    def __init__(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="trust-g3-checker-")
        self.root = Path(self.temp.name)
        (self.root / "inputs").mkdir()
        (self.root / "evidence").mkdir()
        self.sources = {
            "rust": ("r", "inputs/r.rs", b"fn f() {}\n"),
            "lean": ("l", "inputs/l.lean", b"def f := 1\n"),
            "mixed": ("m", "inputs/m.rs", b"fn mixed() {}\n"),
        }
        for _, path, data in self.sources.values():
            (self.root / path).write_bytes(data)
        # An auxiliary (mod/include!) source the Rust precompile manifest pins.
        self.auxiliary = ("inputs/r_aux.rs", b"pub fn g() {}\n")
        (self.root / self.auxiliary[0]).write_bytes(self.auxiliary[1])
        self.docs: dict[str, dict] = {}
        self.refs: dict[str, dict] = {}
        self.make_metadata()
        self.make_artifacts()

    def close(self) -> None:
        self.temp.cleanup()

    def write(self, relative: str, value: dict | bytes) -> dict[str, str]:
        data = value if isinstance(value, bytes) else json.dumps(value, sort_keys=True).encode()
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return {"path": relative, "sha256": hash_bytes(data)}

    def artifact(self, name: str, document: dict) -> None:
        self.docs[name] = document
        self.refs[name] = self.write(f"evidence/{name}.json", document)

    def make_metadata(self) -> None:
        lanes = {}
        corpus_lanes = {}
        for lane, (entry_id, path, data) in self.sources.items():
            entry = {"id": entry_id, "kind": "program", "admitted": True,
                     "source": {"path": path, "sha256": hash_bytes(data)},
                     "expected_outcome": "ok"}
            lanes[lane] = {"upstream_repository": "https://example.test/upstream",
                           "upstream_revision": REV, "upstream_tree_sha256": ZERO,
                           "feature_manifest": {}, "suite_manifest": {},
                           "exception_ledger": {}, "entries": [entry]}
        contract = {"schema": "trust.two-language.admission-contract/v1",
                    "goal_id": "TRUST-TWO-LANGUAGE-100",
                    "repository_id": "https://github.com/alabsystems/trust",
                    "lanes": lanes}
        contract_ref = self.write("admission.json", contract)
        self.contract = contract
        for lane, owner_lane in lanes.items():
            corpus_lanes[lane] = {"upstream_revision": REV,
                "admission_policy_sha256": contract_ref["sha256"],
                "entries": copy.deepcopy(owner_lane["entries"])}
        self.corpus = {"schema": "trust.two-language.corpus-manifest/v1",
            "goal_id": "TRUST-TWO-LANGUAGE-100", "repository_id": "https://github.com/alabsystems/trust",
            "acceptance_run_id": RUN, "source_revision": REV, **corpus_lanes}
        self.write("corpus.json", self.corpus)
        self.policy = {"schema": "trust.two-language.authority-policy/v2",
            "contracts": {name: {} for name in ("admission", "semantics", "obligations",
                "proof_authority", "compatibility_surfaces", "codegen_surface",
                "acceptance_environment")}}
        self.policy["contracts"]["admission"] = {
            "id": "trust.two-language.contract.admission", **contract_ref}
        self.write("policy.json", self.policy)
        for name in ("toolchain", "release", "authorization"):
            self.write(f"{name}.json", {})
        self.module_ref = self.write("linked.trust-ir", b"validity still unmeasured")
        def body(body_id: str, language: str) -> dict:
            return {"id": body_id, "language": language,
                "function_identity_sha256": ONE, "source_language_semantics_id": "sem",
                "source_language_semantics_sha256": ONE, "source_semantics_sha256": ONE,
                "trust_ir_semantics_id": "ir", "trust_ir_semantics_sha256": ONE,
                "trust_ir_sha256": ONE, "ssa_epoch_sha256": ONE,
                "effect_summary_sha256": ONE}
        module = {"id": "module", "artifact": self.module_ref,
                  "body_ids": ["rb", "lb"], "call_edge_ids": [], "obligation_ids": [],
                  "refinement_certificate_body_ids": [], "proof_certificate_ids": [],
                  "assumption_closure_sha256": ONE,
                  "contextual_refinement_evidence": self.module_ref}
        program = {"id": "program", "entrypoints": ["rb"],
            "admitted_file_ids": ["r", "l", "m"], "bodies": [body("rb", "rust"), body("lb", "lean")],
            "refinement_certificates": [], "obligations": [], "proof_certificates": [],
            "modules": [module], "objects": [], "translation_evidence": [],
            "executables": [], "call_edges": [], "contextual_refinement": {}}
        self.subject = {"schema": "trust.two-language.subject-index/v3",
            "goal_id": "TRUST-TWO-LANGUAGE-100", "acceptance_run_id": RUN,
            "source_revision": REV, "programs": [program], "release_executable": {},
            "roots": {name: canonical([]) for name in (
                "admitted_files", "reachable_bodies", "refinement_certificates",
                "obligations", "proof_certificates", "modules", "codegen_matrix_cells",
                "objects", "translation_evidence", "call_edges", "executables")}}
        self.rehash_subject_roots()

    def rehash_subject_roots(self) -> None:
        program = self.subject["programs"][0]
        for name, values in (
            ("admitted_files", [{"program_id": "program", "file_id": fid}
                                for fid in program["admitted_file_ids"]]),
            ("reachable_bodies", [{"program_id": "program", **body} for body in program["bodies"]]),
            ("modules", [{"program_id": "program", **module} for module in program["modules"]]),
        ):
            ordered = sorted(values, key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")))
            self.subject["roots"][name] = canonical(ordered)
        self.write("subject.json", self.subject)

    def make_artifacts(self) -> None:
        rust_path = self.sources["rust"][1]
        lean_path = self.sources["lean"][1]
        rust_body = {"def": "crate::f", "kind": "Fn", "unsupported": 0, "reasons": [],
                     "symbolic": False, "opaque_collapse": False}
        rust_inputs = [{"file": rust_path, "sha256": hash_bytes(self.sources["rust"][2]),
                        "expected_outcome": "ok"}]
        rust_sources = sorted([{"file": rust_path, "sha256": hash_bytes(self.sources["rust"][2])},
                               {"file": self.auxiliary[0], "sha256": hash_bytes(self.auxiliary[1])}],
                              key=lambda row: row["file"])
        self.artifact("rust_scorecard", {"schema": "trust.trust-ir.producer-scorecard.v1",
            "corpora": {"full": {"input_census": {
                "schema": "trust.trust-ir.producer-input-census.v1",
                "source": "precompile-content-manifest/v1",
                "files": copy.deepcopy(rust_inputs)},
                "census_evidence": {"schema": "trust.rust.producer-census-evidence.v2",
                    "input_manifest": {"schema": "trust.rust.measurement-input-manifest.v1",
                        "corpora": {"corpus": {"files": copy.deepcopy(rust_inputs),
                                               "sources": rust_sources}}}},
                "body_census": {"schema": "trust.trust-ir.producer-body-census.v1",
                    "source": "independent-hir-and-typeck-generated-body-census/v1",
                    "bodies": [{"file": rust_path, "def": "crate::f", "kind": "Fn"}]},
                "files": [{"file": rust_path, "outcome": "ok", "bodies": [rust_body],
                           "validation": {"total": 0, "classes": {}},
                           "anomalies": copy.deepcopy(ZERO_ANOMALIES)}],
                "sample_meta": {}}}})
        lean_manifest = {"schema": "trust.clean-corpus.input-manifest/v1",
            "files": [{"file": lean_path, "sha256": hash_bytes(self.sources["lean"][2]),
                       "expected_outcome": "ok", "auxiliary_inputs": []}]}
        self.artifact("lean_input_manifest", lean_manifest)
        self.artifact("lean_body_census", {"schema": "trust.clean-corpus.body-census/v1",
            "input_manifest_sha256": canonical(lean_manifest, ascii=False),
            "files": [lean_path], "declarations": [
                {"file": lean_path, "name": "A.f", "kind": "computational"}]})
        self.artifact("lean_scorecard", {"schema": "trust.clean-corpus.scorecard/v2",
            "per_file": [[lean_path, "ok", ""]],
            "file_records": [{"file": lean_path, "outcome": "ok", "returncode": 0,
                              "sha256": hash_bytes(self.sources["lean"][2]),
                              "auxiliary_inputs": []}],
            "rows": [[lean_path, "A.f", "emitted:gate", "constant", ""]],
            "summary": {"carrier_gate_observed": 999}})
        self.artifact("lean_inventory", {"schema": "trust.lean.check-kernel-roster/v1",
            "authority": "diagnostic-only", "kernel_roster": {
                "schema": "trust.lean.kernel-roster/v1", "authority": "diagnostic-only",
                "denominator_status": "denominator_unverified",
                "runtime_body_universe": "unmeasured"}})
        self.artifact("body_join", {"schema": "trust.two-language.g3.producer-body-join/v1",
            "rows": [
                {"program_id": "program", "file_id": "r", "language": "rust",
                 "source_body": "crate::f", "source_kind": "Fn", "body_id": "rb", "module_id": "module"},
                {"program_id": "program", "file_id": "l", "language": "lean",
                 "source_body": "A.f", "source_kind": "computational", "body_id": "lb", "module_id": "module"}]})

    def rewrite_admission(self) -> None:
        """Re-bind the owner contract, the policy naming it, and the corpus
        mirroring its entries after an edit to ``self.contract``."""
        contract_ref = self.write("admission.json", self.contract)
        self.policy["contracts"]["admission"]["sha256"] = contract_ref["sha256"]
        self.write("policy.json", self.policy)
        for lane in ("rust", "lean", "mixed"):
            self.corpus[lane]["admission_policy_sha256"] = contract_ref["sha256"]
            self.corpus[lane]["entries"] = copy.deepcopy(self.contract["lanes"][lane]["entries"])
        self.write("corpus.json", self.corpus)

    def add_rust_alias(self, alias_path: str) -> None:
        """Admit a second Rust ID ``r2`` whose source is ``alias_path`` (already
        on disk), with a scorecard that claims its own compilation of it."""
        alias = copy.deepcopy(self.contract["lanes"]["rust"]["entries"][0])
        alias["id"] = "r2"
        alias["source"]["path"] = alias_path
        self.contract["lanes"]["rust"]["entries"].append(alias)
        self.rewrite_admission()
        self.subject["programs"][0]["admitted_file_ids"].append("r2")
        self.rehash_subject_roots()
        full = self.docs["rust_scorecard"]["corpora"]["full"]
        source = alias["source"]["sha256"]
        precompile = full["census_evidence"]["input_manifest"]["corpora"]["corpus"]
        for files in (full["input_census"]["files"], precompile["files"]):
            files.append({"file": alias_path, "sha256": source, "expected_outcome": "ok"})
        precompile["sources"].append({"file": alias_path, "sha256": source})
        full["body_census"]["bodies"].append({"file": alias_path, "def": "crate::f", "kind": "Fn"})
        compiled = copy.deepcopy(full["files"][0])
        compiled["file"] = alias_path
        full["files"].append(compiled)
        self.artifact("rust_scorecard", self.docs["rust_scorecard"])

    def write_bundle(self) -> dict[str, str]:
        bundle = {"schema": "trust.two-language.gate-evidence/v1", "gate": "G3",
                  "checker": "trust.two-language.g3.producer-totality/v2",
                  "artifacts": self.refs}
        return self.write("bundle.json", bundle)

    def add_scorecard_replay(self) -> None:
        """Reach the Rust scorecard replay: the tree's pinned scorecard and
        census, a receipt-bound trustc, and a sweep at the accepted revision."""
        # The scorecard loads each of these by file path: the census parser,
        # and (e232684bfd) the resource-descriptor transport in lib/.
        (self.root / "scripts" / "lib").mkdir(parents=True, exist_ok=True)
        for name in ("trust_ir_producer_scorecard.py", "rust_instance_census.py", "lib/landing_targo.py"):
            shutil.copyfile(ROOT / "scripts" / name, self.root / "scripts" / name)
        self.write("toolchain.json", {"components": [{"role": "trustc", "artifact": {"sha256": ONE}}]})
        rust = self.docs["rust_scorecard"]
        rust["provenance"] = {"repo_head": REV, "trustc_sha256": ONE}
        self.artifact("rust_scorecard", rust)

    def plant_forged_bytecode(self, outside: Path) -> tuple[list[Path], set[Path]]:
        """Forge the cached bytecode of every module under scripts/, lib/ included.

        Each forgery records under ``outside`` that it ran; the census's also
        reports the replay complete.  Returns the records and what was planted.
        """
        markers: list[Path] = []
        planted: set[Path] = set()
        for module in sorted((self.root / "scripts").rglob("*.py")):
            marker = outside / f"{module.stem}-bytecode-ran"
            source = (FORGED_CENSUS.format(marker=str(marker)) if module.stem == "rust_instance_census"
                      else f"import pathlib\npathlib.Path({str(marker)!r}).write_text('ran')\n")
            cache = plant_bytecode(module, source)
            markers.append(marker)
            planted |= {cache, cache.parent}
        return markers, planted

    def run(self, *, receipt: bool = False, source_revision: str = REV) -> tuple[int, dict, str]:
        """Run the checker as the gate's run_checker does, interpreter flags included."""
        bundle_ref = self.write_bundle()
        checker_bytes = CHECKER.read_bytes()
        snapshot = self.root / "checker.py"
        if snapshot.exists():
            snapshot.chmod(0o644)
        snapshot.write_bytes(checker_bytes)
        snapshot.chmod(0o444)
        bytecode = tempfile.TemporaryDirectory(prefix="trust-g3-test-bytecode-")
        command = [sys.executable, "-I", "-B", "-X", f"pycache_prefix={bytecode.name}", str(snapshot),
            "--verify-evidence", str(self.root / bundle_ref["path"]), "--root", str(self.root),
            "--toolchain-manifest", str(self.root / "toolchain.json"),
            "--corpus-manifest", str(self.root / "corpus.json"),
            "--subject-graph", str(self.root / "subject.json"),
            "--linked-module", str(self.root / self.module_ref["path"]),
            "--release-artifact", str(self.root / "release.json"),
            "--authority-policy", str(self.root / "policy.json"),
            "--policy-authorization", str(self.root / "authorization.json"),
            "--acceptance-run-id", RUN, "--source-revision", source_revision,
            "--checker-sha256", hash_bytes(checker_bytes),
            "--evidence-sha256", bundle_ref["sha256"],
            "--toolchain-sha256", ZERO,
            "--corpus-manifest-sha256", hash_bytes((self.root / "corpus.json").read_bytes()),
            "--subject-graph-sha256", hash_bytes((self.root / "subject.json").read_bytes()),
            "--linked-module-sha256", self.module_ref["sha256"],
            "--release-artifact-sha256", ZERO,
            "--authority-policy-sha256", hash_bytes((self.root / "policy.json").read_bytes()),
            "--policy-authorization-sha256", ZERO]
        if receipt:
            command += ["--receipt", str(self.root / "receipt.json"), "--prior-gates-root", ZERO]
        env = {"HOME": self.temp.name, "PATH": "/usr/bin:/bin", "LANG": "C.UTF-8",
               "LC_ALL": "C.UTF-8", "PYTHONHASHSEED": "0", "TZ": "UTC"}
        with bytecode:
            process = subprocess.run(command, cwd=self.root, env=env,
                                     capture_output=True, text=True, timeout=60, check=False)
        return process.returncode, json.loads(process.stdout), process.stderr


class G3Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.g = GateRoot()

    def tearDown(self) -> None:
        self.g.close()

    def checks(self) -> tuple[dict[str, bool], str]:
        rc, verdict, stderr = self.g.run()
        self.assertEqual(rc, 1)
        self.assertFalse(verdict["passed"])
        self.assertEqual(tuple(row["id"] for row in verdict["checks"]), REQUIRED)
        self.assertEqual(verdict["prior_gates_root"], None)
        self.assertEqual(set(verdict), {"schema", "goal_id", "gate", "checker", "repository_id",
            "acceptance_run_id", "checker_sha256", "evidence_sha256", "source_revision",
            "toolchain_sha256", "corpus_manifest_sha256", "subject_graph_sha256",
            "linked_module_sha256", "release_artifact_sha256", "authority_policy_sha256",
            "policy_authorization_sha256", "prior_gates_root", "passed", "checks"})
        return {row["id"]: row["passed"] for row in verdict["checks"]}, stderr

    def test_matches_schema_owned_runner_contract(self) -> None:
        runner = runpy.run_path(str(ROOT / "scripts/two_language_completion_gate.py"))
        self.assertEqual(tuple(runner["REQUIRED_CHECKS"]["G3"]), REQUIRED)
        self.assertEqual(runner["CHECKER_PATHS"]["G3"],
                         "scripts/completion_gates/check_g3_producer_totality.py")
        self.assertEqual(runner["CHECKER_IDS"]["G3"],
                         "trust.two-language.g3.producer-totality/v2")

    def test_measurable_joins_pass_but_unavailable_authority_stays_red(self) -> None:
        checks, stderr = self.checks()
        self.assertTrue(checks["admitted_file_manifest_exact"], stderr)
        self.assertFalse(checks["no_denominator_exclusions"])
        self.assertFalse(checks["subject_index_roots_match"])
        self.assertFalse(checks["reachable_body_census_exact"])
        self.assertFalse(checks["rust_zero_producer_residue"])
        self.assertFalse(checks["lean_zero_producer_residue"])
        self.assertFalse(checks["all_joined_modules_valid"])
        self.assertIn("diagnostic-only", stderr)
        self.assertIn("per-ID/config", stderr)
        self.assertIn("other 8/11", stderr)

    def test_corpus_local_rust_complete_never_grants_totality(self) -> None:
        checker = runpy.run_path(str(CHECKER))
        refusal = checker["Refusal"]
        census = {"mono_unrepresented": {"shim": 1}, "unmeasured": ["runtime_roots"]}
        fake = SimpleNamespace(rust_replay=lambda: None,
                               document=lambda _name, _schema: {"corpora": {"full": {"census_status": census}}})
        fake.require_rust_totality_authority = lambda: checker["Context"].require_rust_totality_authority(fake)
        with self.assertRaisesRegex(refusal, "unrepresented monomorphized/runtime"):
            checker["verify"]("rust_zero_producer_residue", fake)
        census["mono_unrepresented"] = {}
        with self.assertRaisesRegex(refusal, "unmeasured instance/runtime"):
            checker["verify"]("rust_zero_producer_residue", fake)
        census["unmeasured"] = []
        census.update({name: "complete" for name in (
            "reachable_instances", "runtime_roots", "external_dependency_closure",
            "proc_macro_io", "build_environment")})
        with self.assertRaisesRegex(refusal, "authored artifacts"):
            checker["verify"]("rust_zero_producer_residue", fake)

    def test_mixed_file_unlisted_body_cannot_pass_no_exclusions(self) -> None:
        program = self.g.subject["programs"][0]
        extra = copy.deepcopy(program["bodies"][0])
        extra["id"] = "mixed-rust-body"
        program["bodies"].append(extra)
        program["modules"][0]["body_ids"].append(extra["id"])
        self.g.rehash_subject_roots()
        checks, stderr = self.checks()
        self.assertFalse(checks["no_denominator_exclusions"])
        self.assertFalse(checks["reachable_body_census_exact"])
        self.assertIn("not an exact duplicate-free bijection", stderr)

    def test_two_admitted_ids_one_source_one_compilation_refused(self) -> None:
        alias = copy.deepcopy(self.g.contract["lanes"]["rust"]["entries"][0])
        alias["id"] = "r2"
        self.g.contract["lanes"]["rust"]["entries"].append(alias)
        contract_ref = self.g.write("admission.json", self.g.contract)
        self.g.policy["contracts"]["admission"]["sha256"] = contract_ref["sha256"]
        self.g.write("policy.json", self.g.policy)
        for lane in ("rust", "lean", "mixed"):
            self.g.corpus[lane]["admission_policy_sha256"] = contract_ref["sha256"]
        self.g.corpus["rust"]["entries"].append(copy.deepcopy(alias))
        self.g.write("corpus.json", self.g.corpus)
        self.g.subject["programs"][0]["admitted_file_ids"].append("r2")
        self.g.rehash_subject_roots()
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertFalse(checks["no_denominator_exclusions"])
        self.assertIn("share one source", stderr)

    def test_authored_body_digests_cannot_make_join_checks_green(self) -> None:
        body = self.g.subject["programs"][0]["bodies"][0]
        body["function_identity_sha256"] = TWO
        body["trust_ir_sha256"] = TWO
        self.g.rehash_subject_roots()
        checks, stderr = self.checks()
        self.assertFalse(checks["reachable_body_census_exact"])
        self.assertFalse(checks["no_denominator_exclusions"])
        self.assertFalse(checks["subject_index_roots_match"])
        self.assertIn("authored labels", stderr)

    def test_non_g3_subject_root_mutation_is_not_ignored(self) -> None:
        self.g.subject["roots"]["proof_certificates"] = TWO
        self.g.write("subject.json", self.g.subject)
        checks, stderr = self.checks()
        self.assertFalse(checks["subject_index_roots_match"])
        self.assertIn("other 8/11", stderr)

    def test_source_revision_format_is_checked_standalone(self) -> None:
        for revision in ("short", "A" * 40, "a" * 39, "a" * 41, "a" * 63, "a" * 65):
            with self.subTest(revision=revision):
                rc, verdict, stderr = self.g.run(source_revision=revision)
                self.assertEqual(rc, 1)
                self.assertFalse(verdict["passed"])
                self.assertFalse(any(row["passed"] for row in verdict["checks"]))
                self.assertIn("lowercase 40- or 64-hex", stderr)
        long_revision = "b" * 64
        self.g.corpus["source_revision"] = long_revision
        self.g.write("corpus.json", self.g.corpus)
        self.g.subject["source_revision"] = long_revision
        self.g.write("subject.json", self.g.subject)
        rc, verdict, stderr = self.g.run(source_revision=long_revision)
        self.assertEqual(rc, 1)
        self.assertTrue(next(row["passed"] for row in verdict["checks"]
                             if row["id"] == "admitted_file_manifest_exact"), stderr)
        self.assertNotIn("lowercase 40- or 64-hex", stderr)

    def test_owner_admission_cannot_be_shrunk_by_corpus(self) -> None:
        self.g.corpus["rust"]["entries"] = []
        self.g.write("corpus.json", self.g.corpus)
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertIn("owner admission contract", stderr)

    def test_subject_cannot_omit_admitted_zero_body_file(self) -> None:
        self.g.subject["programs"][0]["admitted_file_ids"].remove("m")
        self.g.rehash_subject_roots()
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertIn("exact partition", stderr)

    def test_symbolic_body_not_laundered_by_summary(self) -> None:
        rust = self.g.docs["rust_scorecard"]
        rust["corpora"]["full"]["files"][0]["bodies"][0]["symbolic"] = True
        rust["corpora"]["full"]["aggregate"] = {"complete": True, "modelled": 1}
        self.g.artifact("rust_scorecard", rust)
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertFalse(checks["no_denominator_exclusions"])
        self.assertIn("symbolic", stderr)

    def test_flag_induced_file_failure_cannot_shrink_rust_denominator(self) -> None:
        rust = self.g.docs["rust_scorecard"]
        result = rust["corpora"]["full"]["files"][0]
        result["outcome"] = "flag_induced_fail"
        result["bodies"] = []
        rust["corpora"]["full"]["aggregate"] = {"file_outcomes": {"ok": 1},
                                                "bodies": {"lowered_clean_modelled": 1}}
        self.g.artifact("rust_scorecard", rust)
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertFalse(checks["rust_zero_producer_residue"])
        self.assertIn("flag_induced_fail", stderr)

    def test_unmeasured_rust_body_class_refused(self) -> None:
        rust = self.g.docs["rust_scorecard"]
        rust["corpora"]["full"]["files"][0]["bodies"][0]["symbolic"] = None
        self.g.artifact("rust_scorecard", rust)
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertIn("unmeasured", stderr)

    def test_rust_sweep_cannot_be_reused_at_another_revision(self) -> None:
        rust = self.g.docs["rust_scorecard"]
        rust["provenance"] = {"repo_head": "b" * 40, "trustc_sha256": ZERO}
        self.g.artifact("rust_scorecard", rust)
        checks, stderr = self.checks()
        self.assertFalse(checks["rust_zero_producer_residue"])
        self.assertIn("accepted source revision", stderr)

    def rust_precompile_sources(self) -> list:
        corpus = self.g.docs["rust_scorecard"]["corpora"]["full"]
        return corpus["census_evidence"]["input_manifest"]["corpora"]["corpus"]["sources"]

    def assert_rust_manifest_refused(self, needle: str) -> None:
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertFalse(checks["no_denominator_exclusions"])
        self.assertIn(needle, stderr)

    def test_rust_auxiliary_source_is_bound_to_the_tree(self) -> None:
        # The fixture's auxiliary source is on the green path above; drifted
        # bytes mean the sweep measured other mod/include! content.
        (self.g.root / self.g.auxiliary[0]).write_bytes(b"pub fn g() { loop {} }\n")
        self.assert_rust_manifest_refused("r_aux.rs: precompile source hash drift")

    def test_rust_missing_auxiliary_source_refused(self) -> None:
        (self.g.root / self.g.auxiliary[0]).unlink()
        self.assert_rust_manifest_refused("missing file or path escapes root: inputs/r_aux.rs")

    def test_rust_auxiliary_source_rows_are_well_formed(self) -> None:
        pristine = copy.deepcopy(self.g.docs["rust_scorecard"])
        for mutate, needle in (
            (lambda sources: sources.append({"file": "../outside.rs", "sha256": ZERO}), "root-relative"),
            (lambda sources: sources.append(copy.deepcopy(sources[-1])), "duplicate precompile source"),
            (lambda sources: sources[-1].pop("sha256"), "precompile source row"),
            (lambda sources: sources[-1].__setitem__("sha256", "A" * 64), "lowercase SHA-256"),
            (lambda sources: sources.remove(next(row for row in sources
                                                 if row["file"] == "inputs/r.rs")), "input root"),
        ):
            with self.subTest(needle=needle):
                self.g.artifact("rust_scorecard", copy.deepcopy(pristine))
                mutate(self.rust_precompile_sources())
                self.g.artifact("rust_scorecard", self.g.docs["rust_scorecard"])
                self.assert_rust_manifest_refused(needle)

    def test_rust_scorecard_without_precompile_manifest_refused(self) -> None:
        rust = self.g.docs["rust_scorecard"]
        corpus = rust["corpora"]["full"]
        manifest = corpus["census_evidence"]["input_manifest"]
        manifest["corpora"]["corpus"]["files"][0]["expected_outcome"] = "compile_fail"
        self.g.artifact("rust_scorecard", rust)
        self.assert_rust_manifest_refused("input census differs from retained precompile manifest")
        corpus.pop("census_evidence")
        self.g.artifact("rust_scorecard", rust)
        self.assert_rust_manifest_refused("precompile input manifest")

    def test_lean_missing_body_census_refused(self) -> None:
        census = self.g.docs["lean_body_census"]
        census["declarations"] = []
        self.g.artifact("lean_body_census", census)
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertIn("Lean census declarations", stderr)

    def test_lean_weaker_tier_and_favorable_summary_refused(self) -> None:
        lean = self.g.docs["lean_scorecard"]
        lean["rows"][0][2] = "emitted:structural"
        lean["summary"] = {"carrier_gate_observed": 1, "measurement_errors": []}
        self.g.artifact("lean_scorecard", lean)
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertFalse(checks["lean_zero_producer_residue"])
        self.assertIn("carrier-gate", stderr)

    def test_favorable_lean_inventory_label_is_not_body_authority(self) -> None:
        inventory = self.g.docs["lean_inventory"]
        inventory["authority"] = "post-lowering-inventory"
        roster = inventory["kernel_roster"]
        roster["authority"] = "post-lowering-inventory"
        roster["denominator_status"] = "denominator_verified"
        roster["runtime_body_universe"] = "measured"
        self.g.artifact("lean_inventory", inventory)
        checks, stderr = self.checks()
        self.assertFalse(checks["lean_zero_producer_residue"])
        self.assertFalse(checks["reachable_body_census_exact"])
        self.assertIn("no authenticated identity join", stderr)

    def test_duplicate_body_join_refused(self) -> None:
        join = self.g.docs["body_join"]
        join["rows"].append(copy.deepcopy(join["rows"][0]))
        self.g.artifact("body_join", join)
        checks, stderr = self.checks()
        self.assertFalse(checks["no_denominator_exclusions"])
        self.assertFalse(checks["subject_index_roots_match"])
        self.assertIn("duplicate", stderr)

    def test_module_partition_and_root_mutations_refused(self) -> None:
        self.g.subject["programs"][0]["modules"][0]["body_ids"] = ["rb"]
        self.g.rehash_subject_roots()
        checks, stderr = self.checks()
        self.assertFalse(checks["subject_index_roots_match"])
        self.assertIn("partition", stderr)
        self.g.subject["programs"][0]["modules"][0]["body_ids"] = ["rb", "lb"]
        self.g.rehash_subject_roots()
        self.g.subject["roots"]["reachable_bodies"] = TWO
        self.g.write("subject.json", self.g.subject)
        checks, stderr = self.checks()
        self.assertFalse(checks["subject_index_roots_match"])
        self.assertIn("root differs", stderr)

    def test_unknown_artifact_and_path_escape_refused(self) -> None:
        self.g.refs["unknown"] = self.g.refs["body_join"]
        checks, stderr = self.checks()
        self.assertFalse(any(checks.values()))
        self.assertIn("evidence artifacts", stderr)
        self.g.refs.pop("unknown")
        self.g.refs["body_join"] = {"path": "../outside.json", "sha256": ZERO}
        checks, stderr = self.checks()
        self.assertFalse(checks["subject_index_roots_match"])
        self.assertIn("root-relative", stderr)

    def assert_one_verdict_refusing(self, needle: str) -> str:
        """The checker printed ONE JSON verdict (``run`` parses stdout) that
        refuses, and a diagnostic line matches ``needle``."""
        rc, verdict, stderr = self.g.run()
        self.assertEqual(rc, 1, stderr)
        self.assertFalse(verdict["passed"])
        self.assertEqual(tuple(row["id"] for row in verdict["checks"]), REQUIRED)
        self.assertRegex(stderr, needle)
        self.assertNotIn("Traceback", stderr)
        return stderr

    def test_symlink_loop_in_bundle_artifact_path_is_a_structured_refusal(self) -> None:
        # Python 3.9's Path.resolve raises RuntimeError on a symlink loop;
        # later interpreters resolve it and find no file.  Either way the
        # checker prints its verdict instead of dying with a traceback.
        (self.g.root / "loop").symlink_to("loop")
        self.g.refs["lean_inventory"] = {"path": "loop/x.json", "sha256": ZERO}
        self.assert_one_verdict_refusing(
            r"artifacts\.lean_inventory: (path cannot be resolved|missing file or path escapes root)")

    def test_symlink_loop_in_admission_source_is_a_structured_refusal(self) -> None:
        (self.g.root / "loop").symlink_to("loop")
        self.g.contract["lanes"]["mixed"]["entries"][0]["source"]["path"] = "loop/m.rs"
        self.g.rewrite_admission()
        self.assert_one_verdict_refusing(
            r"admitted_file_manifest_exact: owner mixed m\.source: "
            r"(path cannot be resolved|missing file or path escapes root)")

    def test_over_long_bundle_artifact_path_is_a_structured_refusal(self) -> None:
        # Python 3.9's Path.is_file re-raises ENAMETOOLONG instead of
        # answering False.
        self.g.refs["lean_inventory"] = {"path": "evidence/" + "a" * 300 + ".json", "sha256": ZERO}
        self.assert_one_verdict_refusing(
            r"artifacts\.lean_inventory: (path cannot be inspected|missing file or path escapes root)")

    @unittest.skipIf(hasattr(os, "geteuid") and os.geteuid() == 0, "root reads a mode-000 file")
    def test_unreadable_bundle_artifact_is_a_structured_refusal(self) -> None:
        unreadable = self.g.root / self.g.refs["lean_inventory"]["path"]
        unreadable.chmod(0)
        try:
            self.assert_one_verdict_refusing(r"artifacts\.lean_inventory: cannot read: .*Permission denied")
        finally:
            unreadable.chmod(0o644)

    def test_rust_anomaly_fields_must_all_be_measured_at_zero(self) -> None:
        # The producer's parse_bodies emits exactly these three fields; a
        # missing one is unmeasured, not clean.
        pristine = copy.deepcopy(self.g.docs["rust_scorecard"])
        missing = [{key: value for key, value in ZERO_ANOMALIES.items() if key != dropped}
                   for dropped in ZERO_ANOMALIES]
        for anomalies in ({}, *missing, {**ZERO_ANOMALIES, "extra": 0},
                          {**ZERO_ANOMALIES, "duplicate_differential_events": False},
                          {**ZERO_ANOMALIES, "duplicate_unsupported_events": 1},
                          {**ZERO_ANOMALIES, "duplicate_unsupported_events": 0.0},
                          {**ZERO_ANOMALIES, "unsupported_event_without_differential_event": ["x"]},
                          {**ZERO_ANOMALIES, "unsupported_event_without_differential_event": None},
                          None):
            with self.subTest(anomalies=anomalies):
                rust = copy.deepcopy(pristine)
                rust["corpora"]["full"]["files"][0]["anomalies"] = anomalies
                self.g.artifact("rust_scorecard", rust)
                checks, stderr = self.checks()
                self.assertFalse(checks["admitted_file_manifest_exact"])
                self.assertRegex(stderr, r"Rust inputs/r\.rs(: parse anomalies or unmeasured anomaly "
                                         r"fields| anomalies: expected exactly)")
        self.g.artifact("rust_scorecard", pristine)
        checks, stderr = self.checks()
        self.assertTrue(checks["admitted_file_manifest_exact"], stderr)

    def test_hardlinked_admitted_sources_are_one_source(self) -> None:
        # Two admitted IDs naming one file under two directory entries are the
        # same-source alias refused above, whatever the listed compilations.
        os.link(self.g.root / "inputs/r.rs", self.g.root / "inputs/r_alias.rs")
        self.g.add_rust_alias("inputs/r_alias.rs")
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertFalse(checks["no_denominator_exclusions"])
        self.assertIn("admitted IDs ['r', 'r2'] share one source", stderr)

    def test_case_variant_admitted_sources_are_one_source(self) -> None:
        if not (self.g.root / "inputs/R.rs").exists():
            self.skipTest("case-sensitive volume: inputs/R.rs names no file")
        self.g.add_rust_alias("inputs/R.rs")
        checks, stderr = self.checks()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertIn("admitted IDs ['r', 'r2'] share one source", stderr)

    def test_distinct_admitted_sources_are_not_aliases(self) -> None:
        # Control: a byte-identical copy at its own path is a separate file.
        shutil.copyfile(self.g.root / "inputs/r.rs", self.g.root / "inputs/r_copy.rs")
        self.g.add_rust_alias("inputs/r_copy.rs")
        checks, stderr = self.checks()
        self.assertTrue(checks["admitted_file_manifest_exact"], stderr)

    def test_each_row_declares_exactly_the_artifacts_it_reads(self) -> None:
        # The runner binds each row's declared artifacts; a row whose verdict
        # reads an undeclared one under-discloses its evidence.
        self.g.add_scorecard_replay()
        bundle = self.g.write_bundle()
        root = self.g.root
        checker = runpy.run_path(str(CHECKER))
        args = SimpleNamespace(
            verify_evidence=str(root / bundle["path"]), root=str(root),
            authority_policy=str(root / "policy.json"), corpus_manifest=str(root / "corpus.json"),
            subject_graph=str(root / "subject.json"), linked_module_sha256=self.g.module_ref["sha256"],
            acceptance_run_id=RUN, source_revision=REV, toolchain_manifest=str(root / "toolchain.json"))
        complete = json.dumps({"complete": True, "aggregate_source": "recomputed_from_files",
                               "artifact_errors": []})
        for check_id in REQUIRED:
            with self.subTest(check=check_id):
                context = checker["Context"](args)
                self.assertEqual(context.errors, [])
                read: set[str] = set()
                document = context.document

                def recording(name, schema, document=document, read=read):
                    read.add(name)
                    return document(name, schema)

                context.document = recording
                with patch.object(subprocess, "run", side_effect=lambda argv, **_: (
                        subprocess.CompletedProcess(argv, 0, complete, ""))):
                    try:
                        checker["verify"](check_id, context)
                        refusal = None
                    except checker["Refusal"] as exc:
                        refusal = str(exc)
                # Only the one measurable row passes; the rest reach their
                # standing refusal, having read everything on the way.
                self.assertEqual(refusal is None, check_id == "admitted_file_manifest_exact", refusal)
                self.assertEqual(read, set(checker["CHECK_ARTIFACTS"][check_id]))

    def test_unhashable_schema_values_refuse_with_the_schema_reason(self) -> None:
        subject = copy.deepcopy(self.g.subject)
        census = copy.deepcopy(self.g.docs["lean_body_census"])

        def body_language() -> None:
            self.g.subject["programs"][0]["bodies"][0]["language"] = ["rust"]
            self.g.rehash_subject_roots()

        def module_body_id() -> None:
            self.g.subject["programs"][0]["modules"][0]["body_ids"] = ["rb", ["lb"]]
            self.g.rehash_subject_roots()

        def census_file() -> None:
            lean = copy.deepcopy(census)
            lean["files"] = [lean["files"][0], ["inputs/l.lean"]]
            self.g.artifact("lean_body_census", lean)

        for mutate, needle in (
            (body_language, "duplicate body or unknown language rb"),
            (module_body_id, "program.module.body_ids: expected non-empty string"),
            (census_file, "Lean body census file roster differs from admitted files"),
        ):
            with self.subTest(needle=needle):
                self.g.subject = copy.deepcopy(subject)
                self.g.rehash_subject_roots()
                self.g.artifact("lean_body_census", copy.deepcopy(census))
                mutate()
                checks, stderr = self.checks()
                self.assertFalse(checks["admitted_file_manifest_exact"])
                self.assertIn(needle, stderr)
                self.assertNotIn("unhashable", stderr)

    def test_preseal_protocol_refuses_receipt(self) -> None:
        rc, verdict, stderr = self.g.run(receipt=True)
        self.assertEqual(rc, 1)
        self.assertFalse(verdict["passed"])
        self.assertIn("pre-seal", stderr)

    def outside(self) -> Path:
        temporary = tempfile.TemporaryDirectory(prefix="trust-g3-outside-")
        self.addCleanup(temporary.cleanup)
        return Path(temporary.name)

    def test_scorecard_replay_runs_no_bytecode_from_the_tree(self) -> None:
        # The replayed scorecard imports rust_instance_census by file path,
        # which CPython loads from the __pycache__ beside it: the clean-tree
        # gate permits that ignored directory, and an unchecked-hash .pyc there
        # runs without being compared to the pinned source -- here one that
        # reports the replay complete.
        self.g.add_scorecard_replay()
        checks, stderr = self.checks()
        self.assertFalse(checks["rust_zero_producer_residue"])
        self.assertIn("raw compiler-census replay is incomplete", stderr)
        self.assertEqual(bytecode_in(self.g.root), set())

        markers, planted = self.g.plant_forged_bytecode(self.outside())
        checks, stderr = self.checks()
        self.assertEqual([marker.name for marker in markers if marker.exists()], [])
        self.assertIn("raw compiler-census replay is incomplete", stderr)
        self.assertEqual(bytecode_in(self.g.root), planted)

    def test_gate_run_of_the_replay_chain_runs_no_tree_bytecode(self) -> None:
        # The whole chain as the gate runs it: run_checker starts this checker,
        # which starts the tree's scorecard, which loads the tree's census.
        self.g.add_scorecard_replay()
        markers, planted = self.g.plant_forged_bytecode(self.outside())
        bundle = self.g.write_bundle()
        root = self.g.root
        validator = GATE.ReceiptValidator(root, root / "receipt.json", None)
        verdict = validator.run_checker(
            gate="G3", checker_bytes=CHECKER.read_bytes(), evidence_path=root / bundle["path"],
            toolchain_path=root / "toolchain.json", corpus_path=root / "corpus.json",
            subject_graph_path=root / "subject.json", linked_module_path=root / self.g.module_ref["path"],
            release_artifact_path=root / "release.json", policy_path=root / "policy.json",
            policy_authorization_path=root / "authorization.json", acceptance_run_id=RUN,
            subject_graph_digest=hash_bytes((root / "subject.json").read_bytes()),
            linked_module_digest=self.g.module_ref["sha256"], release_artifact_digest=ZERO,
            policy_digest=hash_bytes((root / "policy.json").read_bytes()),
            policy_authorization_digest=ZERO, source_revision=REV,
            checker_digest=hash_bytes(CHECKER.read_bytes()), evidence_digest=bundle["sha256"],
            toolchain_digest=ZERO, corpus_digest=hash_bytes((root / "corpus.json").read_bytes()),
            prior_gates_root=None,
        )
        self.assertIsNotNone(verdict)
        self.assertFalse(verdict["passed"])
        # G3 reached the replay, and the pinned census judged it incomplete:
        # a fixture that failed G3 earlier would start no scorecard at all.
        self.assertTrue(any(
            "G3.checker_run: checker exited 1" in error
            and "raw compiler-census replay is incomplete" in error
            for error in validator.errors
        ), validator.errors)
        self.assertEqual([marker.name for marker in markers if marker.exists()], [])
        self.assertEqual(bytecode_in(root), planted)

    def test_scorecard_replay_interpreter_reads_bytecode_only_from_a_fresh_prefix(self) -> None:
        # -I alone still reads the tree's __pycache__ for an import by path,
        # and a child interpreter does not inherit this one's -X options.
        self.g.add_scorecard_replay()
        bundle = self.g.write_bundle()
        root = self.g.root
        checker = runpy.run_path(str(CHECKER))
        context = checker["Context"](SimpleNamespace(
            verify_evidence=str(root / bundle["path"]), root=str(root),
            authority_policy=str(root / "policy.json"), corpus_manifest=str(root / "corpus.json"),
            acceptance_run_id=RUN, source_revision=REV,
            toolchain_manifest=str(root / "toolchain.json")))
        self.assertEqual(context.errors, [])
        spawned = []

        def replay(argv, **kwargs):
            prefix = Path(argv[4].partition("pycache_prefix=")[2]) if len(argv) > 4 else None
            contents = sorted(prefix.iterdir()) if prefix is not None and prefix.is_dir() else None
            spawned.append((list(argv), kwargs.get("cwd"), prefix, contents))
            verdict = {"complete": True, "aggregate_source": "recomputed_from_files",
                       "artifact_errors": []}
            return subprocess.CompletedProcess(argv, 0, json.dumps(verdict), "")

        with patch.object(subprocess, "run", side_effect=replay):
            context.rust_replay()
        [(argv, cwd, prefix, contents)] = spawned
        resolved = root.resolve()
        self.assertEqual(argv[:4], [sys.executable, "-I", "-B", "-X"])
        self.assertEqual(argv[4], f"pycache_prefix={prefix}")
        self.assertEqual(argv[5:], [str(resolved / "scripts/trust_ir_producer_scorecard.py"),
                                    "--check-completion",
                                    str(resolved / self.g.refs["rust_scorecard"]["path"])])
        # The prefix was a fresh empty directory outside the tree, removed after.
        self.assertEqual(contents, [])
        self.assertTrue(prefix.is_absolute())
        self.assertFalse(prefix.resolve().is_relative_to(resolved))
        self.assertFalse(prefix.exists())
        self.assertEqual(Path(cwd), resolved)


if __name__ == "__main__":
    unittest.main()
