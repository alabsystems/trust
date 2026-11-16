#!/usr/bin/env python3
"""Focused fail-closed and mutation controls for the G4 completion checker."""

from __future__ import annotations

import copy
import hashlib
import json
import os
import runpy
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/completion_gates/check_g4_semantic_faithfulness.py"
REV = "a" * 40
RUN = "b" * 64
ZERO = "0" * 64
ONE = "1" * 64
TWO = "2" * 64
GOAL = "TRUST-TWO-LANGUAGE-100"
REPO = "https://github.com/alabsystems/trust"
REQUIRED = (
    "every_body_universally_refined",
    "finite_domain_exhaustiveness_certificates_checked",
    "sampled_agreement_not_used_as_proof",
    "refinement_certificates_biject_reachable_bodies",
    "all_lean_rows_carrier_faithful_gate",
    "no_weak_or_uninterpreted_verdict_classes",
    "owner_pinned_semantics_relation_observation_model",
    "certificates_bind_authorized_relation",
    "whole_program_contextual_refinement",
    "assumption_closure_checked",
)


def hash_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_root(rows: list[dict]) -> str:
    ordered = sorted(rows, key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")))
    return hash_bytes(json.dumps(ordered, sort_keys=True, separators=(",", ":"),
                                 ensure_ascii=True).encode())


class GateRoot:
    def __init__(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="trust-g4-checker-")
        self.root = Path(self.temp.name)
        (self.root / "evidence").mkdir()
        self.refs: dict[str, dict[str, str]] = {}
        self.make_policy()
        self.make_subject()
        self.make_scorecards()

    def close(self) -> None:
        self.temp.cleanup()

    def write(self, path: str, value: dict | bytes) -> dict[str, str]:
        data = value if isinstance(value, bytes) else json.dumps(value, sort_keys=True).encode()
        dest = self.root / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        return {"path": path, "sha256": hash_bytes(data)}

    def artifact(self, name: str, value: dict) -> None:
        self.refs[name] = self.write(f"evidence/{name}.json", value)

    def make_policy(self) -> None:
        self.definitions = {}
        for role in (
            "rust_language", "lean_language", "trust_ir",
            "rust_to_trust_ir_refinement", "lean_to_trust_ir_refinement",
            "observation_model", "undefined_behavior", "abi_memory_model",
        ):
            ref = self.write(f"semantic/{role}.txt", f"formal {role}\n".encode())
            self.definitions[role] = {"id": f"fixture.{role}", **ref}
        semantics = {"schema": "trust.two-language.semantics-contract/v1",
                     "goal_id": GOAL, "repository_id": REPO,
                     "definitions": self.definitions}
        self.artifact("semantics_contract", semantics)
        kernel_ref = self.write("kernel.bin", b"kernel fixture, not an acceptance kernel\n")
        proof = {"schema": "trust.two-language.proof-authority-contract/v1",
                 "goal_id": GOAL, "repository_id": REPO,
                 "canonical_proposition_encoder": {}, "axiom_policy": {},
                 "external_olean_policy": {}, "denied_axioms": ["sorryAx"],
                 "kernels": [{"id": "fixture.kernel", "environment_sha256": ONE,
                              "artifact": kernel_ref, "proof_grades": ["kernel-checked"],
                              "axiom_allowlist_root_sha256": ZERO}]}
        self.artifact("proof_authority_contract", proof)
        self.sources = {
            "rust": ("rust:fixture", "inputs/r.rs", b"fn rust_main() {}\n"),
            "lean": ("lean:fixture", "inputs/l.lean", b"def answer := 1\n"),
            "mixed": ("mixed:fixture", "inputs/m.rs", b"fn mixed() {}\n"),
        }
        lanes = {}
        corpus_lanes = {}
        for lane, (fid, path, source) in self.sources.items():
            source_ref = self.write(path, source)
            entry = {"id": fid, "kind": "program", "admitted": True,
                     "source": source_ref, "expected_outcome": "ok"}
            lanes[lane] = {"upstream_repository": "https://example.test/upstream",
                           "upstream_revision": REV, "upstream_tree_sha256": ZERO,
                           "feature_manifest": {}, "suite_manifest": {},
                           "exception_ledger": {}, "entries": [entry]}
            corpus_lanes[lane] = {"upstream_revision": REV,
                                  "admission_policy_sha256": "pending", "entries": [entry]}
        admission = {"schema": "trust.two-language.admission-contract/v1",
                     "goal_id": GOAL, "repository_id": REPO, "lanes": lanes}
        admission_ref = self.write("admission.json", admission)
        for lane in corpus_lanes.values():
            lane["admission_policy_sha256"] = admission_ref["sha256"]
        self.corpus_ref = self.write("corpus.json", {
            "schema": "trust.two-language.corpus-manifest/v1", "goal_id": GOAL,
            "repository_id": REPO, "acceptance_run_id": RUN, "source_revision": REV,
            **corpus_lanes,
        })
        contracts = {key: {} for key in (
            "admission", "semantics", "obligations", "proof_authority",
            "compatibility_surfaces", "codegen_surface", "acceptance_environment",
        )}
        contracts["admission"] = {"id": "trust.two-language.contract.admission", **admission_ref}
        contracts["semantics"] = {"id": "trust.two-language.contract.semantics",
                                  **self.refs["semantics_contract"]}
        contracts["proof_authority"] = {"id": "trust.two-language.contract.proof-authority",
                                        **self.refs["proof_authority_contract"]}
        self.policy_ref = self.write("policy.json", {
            "schema": "trust.two-language.authority-policy/v2", "goal_id": GOAL,
            "repository_id": REPO, "contracts": contracts,
        })
        self.toolchain_ref = self.write("toolchain.json", {})
        self.release_ref = self.write("release.bin", b"diagnostic release fixture\n")
        self.authorization_ref = self.write("authorization.json", {})
        self.module_ref = self.write("linked.trust-ir", b"linked module, not a real validator\n")
        self.contextual_ref = self.write("context.cert", b"authored contextual label\n")
        self.rust_cert_ref = self.write("rust.cert", b"authored universal label\n")
        self.lean_cert_ref = self.write("lean.cert", b"authored universal label\n")

    def rebind_semantics(self) -> None:
        """Re-emit the semantics contract and owner policy from ``definitions``."""
        self.artifact("semantics_contract", {
            "schema": "trust.two-language.semantics-contract/v1", "goal_id": GOAL,
            "repository_id": REPO, "definitions": self.definitions})
        policy = json.loads((self.root / self.policy_ref["path"]).read_bytes())
        policy["contracts"]["semantics"] = {"id": "trust.two-language.contract.semantics",
                                            **self.refs["semantics_contract"]}
        self.policy_ref = self.write("policy.json", policy)

    def make_subject(self) -> None:
        def body(ident: str, language: str, source: str, ir: str) -> dict:
            role = self.definitions[f"{language}_language"]
            return {"id": ident, "language": language,
                    "function_identity_sha256": ONE,
                    "source_language_semantics_id": role["id"],
                    "source_language_semantics_sha256": role["sha256"],
                    "source_semantics_sha256": source,
                    "trust_ir_semantics_id": self.definitions["trust_ir"]["id"],
                    "trust_ir_semantics_sha256": self.definitions["trust_ir"]["sha256"],
                    "trust_ir_sha256": ir, "ssa_epoch_sha256": ONE,
                    "effect_summary_sha256": ONE}
        bodies = [body("rust-main", "rust", ONE, TWO),
                  body("lean-answer", "lean", TWO, ONE)]
        certs = []
        for item, evidence in zip(bodies, (self.rust_cert_ref, self.lean_cert_ref)):
            relation = self.definitions[f"{item['language']}_to_trust_ir_refinement"]
            certs.append({"body_id": item["id"],
                          "source_semantics_sha256": item["source_semantics_sha256"],
                          "trust_ir_sha256": item["trust_ir_sha256"],
                          "relation_id": relation["id"], "relation_sha256": relation["sha256"],
                          "certificate_kind": "universal", "finite_domain_sha256": None,
                          "exhaustiveness_evidence": None,
                          "all_elements_agreement_root_sha256": None,
                          "kernel_environment_id": "fixture.kernel",
                          "kernel_environment_sha256": ONE, "evidence": evidence})
        closure = ZERO
        module = {"id": "module", "artifact": self.module_ref,
                  "body_ids": ["rust-main", "lean-answer"], "call_edge_ids": [],
                  "obligation_ids": [], "refinement_certificate_body_ids": ["rust-main", "lean-answer"],
                  "proof_certificate_ids": [], "assumption_closure_sha256": closure,
                  "contextual_refinement_evidence": self.contextual_ref}
        program = {"id": "program", "entrypoints": ["rust-main"],
                   "admitted_file_ids": [value[0] for value in self.sources.values()],
                   "bodies": bodies, "refinement_certificates": certs,
                   "obligations": [], "proof_certificates": [], "modules": [module],
                   "objects": [], "translation_evidence": [], "executables": [], "call_edges": [],
                   "contextual_refinement": {"assumption_closure_sha256": closure,
                                             "evidence": self.contextual_ref}}
        self.subject = {"schema": "trust.two-language.subject-index/v3", "goal_id": GOAL,
                        "acceptance_run_id": RUN, "source_revision": REV,
                        "programs": [program], "release_executable": {},
                        "roots": {key: canonical_root([]) for key in (
                            "admitted_files", "reachable_bodies", "refinement_certificates",
                            "obligations", "proof_certificates", "modules", "codegen_matrix_cells",
                            "objects", "translation_evidence", "call_edges", "executables")}}
        self.refresh_subject()

    def refresh_subject(self, *, roots: bool = True) -> None:
        if roots:
            self.subject["roots"]["reachable_bodies"] = canonical_root([
                {"program_id": p["id"], **row}
                for p in self.subject["programs"] for row in p["bodies"]])
            self.subject["roots"]["refinement_certificates"] = canonical_root([
                {"program_id": p["id"], **row}
                for p in self.subject["programs"] for row in p["refinement_certificates"]])
        self.artifact("subject_graph", self.subject)

    def make_scorecards(self) -> None:
        rust_path = self.sources["rust"][1]
        lean_path = self.sources["lean"][1]
        self.rust_scorecard = {"schema": "trust.trust-ir.producer-scorecard.v1",
                               "corpora": {"full": {"files": [{"file": rust_path, "outcome": "ok",
                                  "bodies": [{"def": "crate::rust_main", "kind": "Fn",
                                              "mode": "Agreed", "samples": 3, "equal": True,
                                              "unsupported": 0, "symbolic": False,
                                              "opaque_collapse": False, "reasons": []}]}]}}}
        self.lean_scorecard = {"schema": "trust.clean-corpus.scorecard/v2",
                               "rows": [[lean_path, "A.answer", "emitted:gate", "constant", ""]]}
        self.join = {"schema": "trust.two-language.g3.producer-body-join/v1", "rows": [
            {"program_id": "program", "file_id": "rust:fixture", "language": "rust",
             "source_body": "crate::rust_main", "source_kind": "Fn",
             "body_id": "rust-main", "module_id": "module"},
            {"program_id": "program", "file_id": "lean:fixture", "language": "lean",
             "source_body": "A.answer", "source_kind": "computational",
             "body_id": "lean-answer", "module_id": "module"},
        ]}
        self.artifact("rust_scorecard", self.rust_scorecard)
        self.artifact("lean_scorecard", self.lean_scorecard)
        self.artifact("body_join", self.join)

    def run(self, *, receipt: bool = False, roots: bool = True,
            bundle_override: dict | None = None, checker_hash: str | None = None,
            raw_artifacts: dict[str, bytes] | None = None,
            root_override: Path | None = None) -> tuple[int, dict, str]:
        self.refresh_subject(roots=roots)
        self.artifact("rust_scorecard", self.rust_scorecard)
        self.artifact("lean_scorecard", self.lean_scorecard)
        self.artifact("body_join", self.join)
        for name, data in (raw_artifacts or {}).items():
            self.refs[name] = self.write(f"evidence/{name}.json", data)
        bundle = {"schema": "trust.two-language.gate-evidence/v1", "gate": "G4",
                  "checker": "trust.two-language.g4.semantic-faithfulness/v2",
                  "artifacts": copy.deepcopy(self.refs)}
        if bundle_override is not None:
            bundle.update(bundle_override)
        bundle_ref = self.write("bundle.json", bundle)
        checker_bytes = CHECKER.read_bytes()
        snapshot = self.root / "checker.py"
        snapshot.write_bytes(checker_bytes)
        command = [sys.executable, "-I", str(snapshot),
            "--verify-evidence", str(self.root / bundle_ref["path"]),
            "--root", str(root_override or self.root),
            "--toolchain-manifest", str(self.root / self.toolchain_ref["path"]),
            "--corpus-manifest", str(self.root / self.corpus_ref["path"]),
            "--subject-graph", str(self.root / self.refs["subject_graph"]["path"]),
            "--linked-module", str(self.root / self.module_ref["path"]),
            "--release-artifact", str(self.root / self.release_ref["path"]),
            "--authority-policy", str(self.root / self.policy_ref["path"]),
            "--policy-authorization", str(self.root / self.authorization_ref["path"]),
            "--acceptance-run-id", RUN, "--source-revision", REV,
            "--checker-sha256", checker_hash or hash_bytes(checker_bytes),
            "--evidence-sha256", bundle_ref["sha256"],
            "--toolchain-sha256", self.toolchain_ref["sha256"],
            "--corpus-manifest-sha256", self.corpus_ref["sha256"],
            "--subject-graph-sha256", self.refs["subject_graph"]["sha256"],
            "--linked-module-sha256", self.module_ref["sha256"],
            "--release-artifact-sha256", self.release_ref["sha256"],
            "--authority-policy-sha256", self.policy_ref["sha256"],
            "--policy-authorization-sha256", self.authorization_ref["sha256"]]
        if receipt:
            command += ["--receipt", str(self.root / "receipt.json"), "--prior-gates-root", ZERO]
        env = {"HOME": self.temp.name, "PATH": "/usr/bin:/bin", "LANG": "C.UTF-8",
               "LC_ALL": "C.UTF-8", "PYTHONHASHSEED": "0", "TZ": "UTC"}
        process = subprocess.run(command, cwd=self.root, env=env,
                                 capture_output=True, text=True, timeout=60, check=False)
        lines = process.stdout.splitlines()
        if len(lines) != 1:
            raise AssertionError(f"expected exactly one verdict line, got {lines!r}; "
                                 f"stderr: {process.stderr}")
        return process.returncode, json.loads(lines[0]), process.stderr


class G4Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.g = GateRoot()

    def tearDown(self) -> None:
        self.g.close()

    def checks(self, **kwargs: object) -> tuple[dict[str, bool], str]:
        rc, verdict, stderr = self.g.run(**kwargs)
        self.assertEqual(rc, 1, stderr)
        self.assertFalse(verdict["passed"])
        self.assertEqual(tuple(row["id"] for row in verdict["checks"]), REQUIRED)
        self.assertEqual(set(verdict), {"schema", "goal_id", "gate", "checker", "repository_id",
            "acceptance_run_id", "checker_sha256", "evidence_sha256", "source_revision",
            "toolchain_sha256", "corpus_manifest_sha256", "subject_graph_sha256",
            "linked_module_sha256", "release_artifact_sha256", "authority_policy_sha256",
            "policy_authorization_sha256", "prior_gates_root", "passed", "checks"})
        self.assertTrue(all(set(row) == {"id", "passed", "artifacts"} for row in verdict["checks"]))
        return {row["id"]: row["passed"] for row in verdict["checks"]}, stderr

    def test_matches_schema_owned_runner_contract(self) -> None:
        runner = runpy.run_path(str(ROOT / "scripts/two_language_completion_gate.py"))
        self.assertEqual(tuple(runner["REQUIRED_CHECKS"]["G4"]), REQUIRED)
        self.assertEqual(runner["CHECKER_PATHS"]["G4"],
                         "scripts/completion_gates/check_g4_semantic_faithfulness.py")
        self.assertEqual(runner["CHECKER_IDS"]["G4"],
                         "trust.two-language.g4.semantic-faithfulness/v2")

    def test_structural_owner_pin_only_and_concrete_red_blockers(self) -> None:
        checks, stderr = self.checks()
        self.assertTrue(checks["owner_pinned_semantics_relation_observation_model"], stderr)
        self.assertEqual(sum(checks.values()), 1)
        self.assertIn("observed 2 body/certificate labels", stderr)
        self.assertIn("observed 1 Rust Agreed rows/3 samples", stderr)
        self.assertIn("observed 1 Lean emitted:gate labels", stderr)
        self.assertIn("no checked linked-program refinement replay", stderr)
        self.assertIn("no independently checked assumption/theorem closure", stderr)

    def test_authored_certificate_claim_and_sample_never_green(self) -> None:
        self.g.rust_cert_ref = self.g.write("rust.cert", b"kernel-checked universal refinement: yes\n")
        self.g.subject["programs"][0]["refinement_certificates"][0]["evidence"] = self.g.rust_cert_ref
        checks, stderr = self.checks()
        self.assertFalse(checks["every_body_universally_refined"])
        self.assertFalse(checks["sampled_agreement_not_used_as_proof"])
        self.assertIn("no independent universal refinement replay", stderr)

    def test_finite_exhaustive_labels_and_complete_domain_text_still_red(self) -> None:
        cert = self.g.subject["programs"][0]["refinement_certificates"][0]
        cert["certificate_kind"] = "finite-exhaustive"
        cert["finite_domain_sha256"] = ONE
        cert["all_elements_agreement_root_sha256"] = TWO
        cert["exhaustiveness_evidence"] = self.g.write("finite.cert", b"all elements checked\n")
        checks, stderr = self.checks()
        self.assertFalse(checks["finite_domain_exhaustiveness_certificates_checked"])
        self.assertIn("observed 1 finite-exhaustive labels", stderr)
        self.assertIn("no checked domain enumeration", stderr)

    def test_finite_certificate_missing_exhaustiveness_ref_rejected(self) -> None:
        cert = self.g.subject["programs"][0]["refinement_certificates"][0]
        cert["certificate_kind"] = "finite-exhaustive"
        cert["finite_domain_sha256"] = ONE
        cert["all_elements_agreement_root_sha256"] = TWO
        _, stderr = self.checks()
        self.assertIn("exhaustiveness", stderr)

    def test_duplicate_or_missing_certificate_rejected(self) -> None:
        certs = self.g.subject["programs"][0]["refinement_certificates"]
        certs.append(copy.deepcopy(certs[0]))
        checks, stderr = self.checks()
        self.assertFalse(checks["refinement_certificates_biject_reachable_bodies"])
        self.assertIn("duplicate or unknown refinement body", stderr)
        certs.pop()
        certs.pop()
        _, stderr = self.checks()
        self.assertIn("bijection fails", stderr)

    def test_refinement_root_mutation_rejected(self) -> None:
        self.g.subject["roots"]["refinement_certificates"] = ZERO
        _, stderr = self.checks(roots=False)
        self.assertIn("refinement_certificates root differs", stderr)

    def test_mutated_owner_relation_and_kernel_ref_rejected(self) -> None:
        cert = self.g.subject["programs"][0]["refinement_certificates"][0]
        cert["relation_sha256"] = ZERO
        _, stderr = self.checks()
        self.assertIn("certificate does not bind body and owner relation", stderr)
        cert["relation_sha256"] = self.g.definitions["rust_to_trust_ir_refinement"]["sha256"]
        cert["kernel_environment_sha256"] = TWO
        _, stderr = self.checks()
        self.assertIn("non-owner/non-kernel-checked environment", stderr)

    def test_sampled_uninterpreted_and_not_run_modes_rejected(self) -> None:
        body = self.g.rust_scorecard["corpora"]["full"]["files"][0]["bodies"][0]
        for mode in ("AgreedUninterpretedCallee", "NotRun", "MirOracle"):
            with self.subTest(mode=mode):
                body["mode"] = mode
                body["equal"] = False
                _, stderr = self.checks()
                self.assertIn("weak or uninterpreted differential mode", stderr)

    def test_structural_and_ungated_lean_rows_rejected(self) -> None:
        row = self.g.lean_scorecard["rows"][0]
        for disposition in ("structural", "kernel-tv", "general:compiled", "emitted:ungated"):
            with self.subTest(disposition=disposition):
                row[2] = disposition
                _, stderr = self.checks()
                self.assertIn("non-gate or weak disposition", stderr) if disposition != "general:compiled" else self.assertIn("below carrier gate", stderr)

    def test_body_join_duplicate_and_wrong_source_id_rejected(self) -> None:
        self.g.join["rows"].append(copy.deepcopy(self.g.join["rows"][0]))
        _, stderr = self.checks()
        self.assertIn("duplicates or mismatches", stderr)
        self.g.join["rows"].pop()
        self.g.join["rows"][0]["file_id"] = "lean:fixture"
        _, stderr = self.checks()
        self.assertIn("unknown or wrong-language admitted ID", stderr)

    def test_proof_only_lean_rows_are_not_computational_gate_rows(self) -> None:
        self.g.lean_scorecard["rows"].extend([
            ["inputs/l.lean", "A.theorem", "general:not-computational", "theorem", ""],
            ["inputs/l.lean", "A.theorem", "planner-skipped", "theorem", ""],
        ])
        checks, stderr = self.checks()
        self.assertTrue(checks["owner_pinned_semantics_relation_observation_model"])
        self.assertIn("observed 1 Lean emitted:gate labels", stderr)
        self.g.lean_scorecard["rows"].append(
            ["inputs/l.lean", "A.theorem", "emitted:gate", "theorem", ""])
        _, stderr = self.checks()
        self.assertIn("proof-only and computational dispositions overlap", stderr)

    def test_admission_corpus_mismatch_and_missing_join_rejected(self) -> None:
        self.g.join["rows"].pop()
        _, stderr = self.checks()
        self.assertIn("exact duplicate-free population", stderr)
        corpus = json.loads((self.g.root / "corpus.json").read_text())
        corpus["rust"]["entries"][0]["id"] = "forged"
        self.g.corpus_ref = self.g.write("corpus.json", corpus)
        _, stderr = self.checks()
        self.assertIn("corpus entries differ from owner admission", stderr)

    def test_contextual_and_assumption_labels_cannot_fake_replay(self) -> None:
        program = self.g.subject["programs"][0]
        program["modules"][0]["assumption_closure_sha256"] = TWO
        _, stderr = self.checks()
        self.assertIn("module assumption closure differs", stderr)
        program["modules"][0]["assumption_closure_sha256"] = ZERO
        program["modules"][0]["contextual_refinement_evidence"] = self.g.rust_cert_ref
        _, stderr = self.checks()
        self.assertIn("contextual evidence differs", stderr)

    def test_bundle_passed_flag_cannot_flip_verdict(self) -> None:
        _, stderr = self.checks(bundle_override={"passed": True})
        self.assertIn("evidence bundle: expected exactly", stderr)

    def alias_observation_model(self, path: str) -> None:
        """Bind observation_model to ``path``, a second spelling of undefined_behavior."""
        undefined = self.g.definitions["undefined_behavior"]
        self.g.definitions["observation_model"].update(path=path, sha256=undefined["sha256"])
        self.g.rebind_semantics()

    def test_semantic_roles_aliasing_one_file_by_symlink_rejected(self) -> None:
        os.symlink("undefined_behavior.txt", self.g.root / "semantic/alias.txt")
        self.alias_observation_model("semantic/alias.txt")
        checks, stderr = self.checks()
        self.assertFalse(checks["owner_pinned_semantics_relation_observation_model"])
        self.assertIn("semantic definitions have duplicate identity or path", stderr)

    def test_semantic_roles_aliasing_one_file_by_hard_link_rejected(self) -> None:
        os.link(self.g.root / "semantic/undefined_behavior.txt", self.g.root / "semantic/alias.txt")
        self.alias_observation_model("semantic/alias.txt")
        checks, stderr = self.checks()
        self.assertFalse(checks["owner_pinned_semantics_relation_observation_model"])
        self.assertIn("semantic definitions have duplicate identity or path", stderr)

    def test_semantic_roles_aliasing_one_file_by_case_rejected(self) -> None:
        alias = "semantic/UNDEFINED_BEHAVIOR.TXT"
        if not (self.g.root / alias).is_file():
            self.skipTest("file system is case-sensitive; a case alias names no file")
        self.alias_observation_model(alias)
        checks, stderr = self.checks()
        self.assertFalse(checks["owner_pinned_semantics_relation_observation_model"])
        self.assertIn("semantic definitions have duplicate identity or path", stderr)

    def test_distinct_semantic_files_still_pass_owner_pin(self) -> None:
        # Control for the alias tests: a fresh, distinct file under the same
        # role keeps the structural owner pin green.
        ref = self.g.write("semantic/observation_model_v2.txt", b"formal observation v2\n")
        self.g.definitions["observation_model"].update(ref)
        self.g.rebind_semantics()
        checks, stderr = self.checks()
        self.assertTrue(checks["owner_pinned_semantics_relation_observation_model"], stderr)

    def test_symlink_loop_root_yields_one_refusing_verdict(self) -> None:
        loop = self.g.root / "loop"
        loop.symlink_to("loop")
        checks, stderr = self.checks(root_override=loop)
        self.assertFalse(any(checks.values()))
        self.assertIn("G4: common binding: ", stderr)
        try:
            loop.resolve()
        except (OSError, RuntimeError):  # Python < 3.13 raises on a loop.
            self.assertIn("--root cannot be resolved", stderr)
        self.assertNotIn("Traceback", stderr)

    def test_duplicate_json_key_diagnostic_names_its_document(self) -> None:
        _, stderr = self.checks(raw_artifacts={
            "lean_scorecard": b'{"schema": "a", "schema": "b"}'})
        self.assertIn("common binding: lean_scorecard: duplicate JSON key 'schema'", stderr)

    def test_binding_mutations_rejected(self) -> None:
        _, stderr = self.checks(checker_hash=ZERO)
        self.assertIn("checker snapshot SHA-256 differs", stderr)
        _, stderr = self.checks(receipt=True)
        self.assertIn("G4 is pre-seal", stderr)


if __name__ == "__main__":
    unittest.main()
