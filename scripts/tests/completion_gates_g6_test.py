#!/usr/bin/env python3
"""Hostile favorable-input controls for the fail-closed G6 checker."""

from __future__ import annotations

import copy
import hashlib
import json
import runpy
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TOP = ROOT / "scripts/two_language_completion_gate.py"
TOP_SCHEMA = runpy.run_path(str(TOP))
CHECKER = ROOT / TOP_SCHEMA["CHECKER_PATHS"]["G6"]
ZERO = "0" * 64
ONE = "1" * 64
TWO = "2" * 64
THREE = "3" * 64
REV = "a" * 40
RUN = "6" * 64
GOAL = "TRUST-TWO-LANGUAGE-100"
REPO = "https://github.com/alabsystems/trust"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def root_of(rows: list[dict]) -> str:
    ordered = sorted(rows, key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")))
    return sha(json.dumps(ordered, sort_keys=True, separators=(",", ":")).encode())


class GateRoot:
    def __init__(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="trust-g6-hostile-")
        self.root = Path(self.tmp.name)
        self.artifact_schemas = runpy.run_path(str(CHECKER))["ARTIFACT_SCHEMAS"]
        self.docs: dict[str, dict] = {}
        self.refs: dict[str, dict] = {}
        self.make_policy()
        self.make_subject()
        self.make_artifacts()
        self.write("toolchain.json", {"schema": "trust.two-language.toolchain-manifest/v1"})
        self.write("corpus.json", {"schema": "trust.two-language.corpus-manifest/v1"})
        self.write("release.json", {"schema": "test-release"})
        self.write("authorization.json", {"schema": "test-owner-authorization"})
        self.module = self.write("linked.trust-ir", b"authored fake module; not decoded")

    def close(self) -> None:
        self.tmp.cleanup()

    def write(self, path: str, value: dict | bytes) -> dict[str, str]:
        data = value if isinstance(value, bytes) else json.dumps(value, sort_keys=True).encode()
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        return {"path": path, "sha256": sha(data)}

    def make_policy(self) -> None:
        rules = [
            {"id": f"rule-{kind}", "class": kind,
             "applicability": {}, "formula_schema": {}}
            for kind in ("safety", "functional", "termination", "ownership",
                         "unsafe_memory", "temporal")
        ]
        obligation = {
            "schema": "trust.two-language.obligation-contract/v1",
            "goal_id": GOAL, "repository_id": REPO, "rules": rules,
            "formula_encoder": {"id": "formula", **self.write("encoders/formula", b"encoder")},
        }
        proof = {
            "schema": "trust.two-language.proof-authority-contract/v1",
            "goal_id": GOAL, "repository_id": REPO,
            "canonical_proposition_encoder": {
                "id": "proposition", **self.write("encoders/proposition", b"proposition")},
            "kernels": [{"id": "clean", "environment_sha256": TWO,
                         "artifact": {}, "proof_grades": ["Certified"],
                         "axiom_allowlist_root_sha256": THREE}],
            "axiom_policy": {}, "external_olean_policy": {},
            "denied_axioms": ["sorryAx"],
        }
        capabilities = {
            "kani": ["nondeterminism", "assume", "harnesses"],
            "verus": ["ghost", "tracked", "triggers", "fuel", "broadcast", "calculations"],
            "creusot": ["prophecy", "mutable_borrows", "machine_integers", "contracts"],
            "tla_plus": ["fairness", "stuttering", "infinite_behaviors", "temporal_operators"],
        }
        compatibility = {
            "schema": "trust.two-language.compatibility-surfaces-contract/v2",
            "goal_id": GOAL, "repository_id": REPO,
            "surfaces": {key: {"required": True, "semantic_capabilities": values}
                         for key, values in capabilities.items()},
        }
        obligation_ref = self.write("policy/obligation.json", obligation)
        proof_ref = self.write("policy/proof.json", proof)
        compatibility_ref = self.write("policy/compatibility.json", compatibility)
        self.policy = {
            "schema": "trust.two-language.authority-policy/v2", "goal_id": GOAL,
            "repository_id": REPO, "authorized_source_revision": REV,
            "authorized_acceptance_run_id": RUN,
            "contracts": {name: {} for name in (
                "admission", "semantics", "obligations", "proof_authority",
                "compatibility_surfaces", "codegen_surface", "acceptance_environment")},
        }
        self.policy["contracts"]["obligations"] = {
            "id": "trust.two-language.contract.obligations", **obligation_ref}
        self.policy["contracts"]["proof_authority"] = {
            "id": "trust.two-language.contract.proof-authority", **proof_ref}
        self.policy["contracts"]["compatibility_surfaces"] = {
            "id": "trust.two-language.contract.compatibility-surfaces", **compatibility_ref}
        self.write("policy.json", self.policy)

    def make_subject(self) -> None:
        self.proof_bytes = self.write("evidence/proof-term.bin", b"not a proof term")
        self.bridge_bytes = self.write("evidence/formula-bridge.bin", b"not a checked bridge")
        self.body = {"id": "body", "language": "rust", "function_identity_sha256": ONE,
                     "ssa_epoch_sha256": ONE, "effect_summary_sha256": ONE}
        self.obligation = {"id": "obligation", "body_id": "body", "module_id": "module",
                           "function_identity_sha256": ONE, "ssa_epoch_sha256": ONE,
                           "effect_summary_sha256": ONE, "formula_sha256": ONE,
                           "canonical_proposition_sha256": ONE,
                           "policy_rule_id": "rule-functional",
                           "formula_encoder_id": "formula",
                           "formula_encoder_sha256": self.policy_encoder("formula"),
                           "proposition_encoder_id": "proposition",
                           "proposition_encoder_sha256": self.policy_encoder("proposition"),
                           "formula_to_proposition_evidence": self.bridge_bytes}
        self.certificate = {"id": "certificate", "obligation_id": "obligation",
                            "body_id": "body", "module_id": "module",
                            "function_identity_sha256": ONE, "ssa_epoch_sha256": ONE,
                            "effect_summary_sha256": ONE, "proposition_sha256": ONE,
                            "kernel_environment_id": "clean", "kernel_environment_sha256": TWO,
                            "proof_grade": "Certified", "axiom_allowlist_root_sha256": THREE,
                            "evidence": self.proof_bytes}
        self.program = {
            "id": "program", "entrypoints": ["body"], "admitted_file_ids": ["file"],
            "bodies": [self.body], "obligations": [self.obligation],
            "proof_certificates": [self.certificate],
            "modules": [{"id": "module", "body_ids": ["body"],
                         "obligation_ids": ["obligation"],
                         "proof_certificate_ids": ["certificate"]}],
        }
        self.subject = {
            "schema": "trust.two-language.subject-index/v3", "goal_id": GOAL,
            "acceptance_run_id": RUN, "source_revision": REV,
            "programs": [self.program], "roots": {},
        }
        self.rehash_subject()

    def policy_encoder(self, name: str) -> str:
        return sha((self.root / "encoders" / name).read_bytes())

    def rehash_subject(self) -> None:
        self.subject["roots"] = {
            "obligations": root_of([{"program_id": "program", **row}
                                    for row in self.program["obligations"]]),
            "proof_certificates": root_of([{"program_id": "program", **row}
                                           for row in self.program["proof_certificates"]]),
        }
        self.write("subject.json", self.subject)

    def make_artifacts(self) -> None:
        for key, schema in self.artifact_schemas.items():
            self.docs[key] = {"schema": schema, "complete": True, "passed": True,
                              "source_revision": REV, "rows": [{"status": "Certified",
                                  "solver": "UNSAT", "kernel_replayed": True,
                                  "obligation_id": "obligation"}]}
            self.refs[key] = self.write(f"evidence/{key}.json", self.docs[key])

    def run(self, *, extra: list[str] | None = None,
            revision: str = REV, checker_digest: str | None = None,
            bundle_bytes: bytes | None = None, run_id: str = RUN,
            root_arg: str | None = None) -> tuple[int, dict, str]:
        for key, doc in self.docs.items():
            self.refs[key] = self.write(f"evidence/{key}.json", doc)
        bundle = {"schema": "trust.two-language.gate-evidence/v1", "gate": "G6",
                  "checker": "trust.two-language.g6.proof-authority/v2",
                  "artifacts": copy.deepcopy(self.refs)}
        bundle_ref = self.write("bundle.json", bundle if bundle_bytes is None else bundle_bytes)
        checker_bytes = CHECKER.read_bytes()
        snapshot = self.root / "checker.py"
        if snapshot.exists():
            snapshot.chmod(0o644)
        snapshot.write_bytes(checker_bytes)
        snapshot.chmod(0o444)
        paths = {"toolchain_manifest": "toolchain.json", "corpus_manifest": "corpus.json",
                 "subject_graph": "subject.json", "linked_module": "linked.trust-ir",
                 "release_artifact": "release.json", "authority_policy": "policy.json",
                 "policy_authorization": "authorization.json"}
        hashes = {"toolchain_sha256": sha((self.root / "toolchain.json").read_bytes()),
                  "corpus_manifest_sha256": sha((self.root / "corpus.json").read_bytes()),
                  "subject_graph_sha256": sha((self.root / "subject.json").read_bytes()),
                  "linked_module_sha256": sha((self.root / "linked.trust-ir").read_bytes()),
                  "release_artifact_sha256": sha((self.root / "release.json").read_bytes()),
                  "authority_policy_sha256": sha((self.root / "policy.json").read_bytes()),
                  "policy_authorization_sha256": sha((self.root / "authorization.json").read_bytes())}
        command = [sys.executable, "-I", str(snapshot),
                   "--verify-evidence", str(self.root / bundle_ref["path"]),
                   "--root", root_arg or str(self.root),
                   "--acceptance-run-id", run_id, "--source-revision", revision,
                   "--checker-sha256", checker_digest or sha(checker_bytes),
                   "--evidence-sha256", bundle_ref["sha256"]]
        for key, path in paths.items():
            command += ["--" + key.replace("_", "-"), str(self.root / path)]
        for key, value in hashes.items():
            command += ["--" + key.replace("_", "-"), value]
        command += extra or []
        process = subprocess.run(command, cwd=self.root,
                                 env={"HOME": str(self.root), "PATH": "/usr/bin:/bin",
                                      "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
                                      "PYTHONHASHSEED": "0", "TZ": "UTC"},
                                 text=True, capture_output=True, timeout=30, check=False)
        lines = process.stdout.splitlines()
        if len(lines) != 1:
            raise AssertionError(
                f"checker must print exactly one JSON verdict line; stdout={process.stdout!r} "
                f"stderr tail={process.stderr[-400:]!r}")
        return process.returncode, json.loads(lines[0]), process.stderr


class G6Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.g = GateRoot()

    def tearDown(self) -> None:
        self.g.close()

    def check(self) -> tuple[dict[str, bool], str]:
        rc, verdict, stderr = self.g.run()
        self.assertEqual(rc, 1)
        self.assertFalse(verdict["passed"])
        self.assertEqual(verdict["schema"], TOP_SCHEMA["CHECKER_VERDICT_SCHEMA"])
        self.assertEqual(verdict["gate"], "G6")
        self.assertEqual(verdict["prior_gates_root"], None)
        self.assertEqual(tuple(row["id"] for row in verdict["checks"]),
                         tuple(runpy.run_path(str(CHECKER))["REQUIRED"]))
        self.assertTrue(all(set(row) == {"id", "passed", "artifacts"}
                            and len(row["artifacts"]) == len(self.g.refs)
                            for row in verdict["checks"]))
        return {row["id"]: row["passed"] for row in verdict["checks"]}, stderr

    def test_exact_top_level_check_set_and_protocol(self) -> None:
        own = runpy.run_path(str(CHECKER))
        top = TOP_SCHEMA
        self.assertEqual(top["CHECKER_PATHS"]["G6"],
                         "scripts/completion_gates/check_g6_proof_authority.py")
        self.assertTrue(CHECKER.is_file())
        self.assertEqual(CHECKER.relative_to(ROOT).as_posix(), top["CHECKER_PATHS"]["G6"])
        self.assertEqual(own["SCHEMA"], top["CHECKER_VERDICT_SCHEMA"])
        self.assertEqual(own["GOAL"], top["GOAL_ID"])
        self.assertEqual(own["REQUIRED"], top["REQUIRED_CHECKS"]["G6"])
        self.assertEqual(own["CHECKER"], top["CHECKER_IDS"]["G6"])
        checks, _ = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])

    def test_authored_certified_unsat_replayed_and_complete_stay_red(self) -> None:
        checks, stderr = self.check()
        self.assertFalse(any(checks.values()))
        self.assertIn("no independent kernel execution", stderr)
        self.assertIn("source operations and policy instances", stderr)
        self.assertIn("external .olean loading/closure remains unsupported", stderr)
        self.assertIn("authored subject-index obligation/proof rows", stderr)

    def test_self_consistent_forged_subject_population_stays_diagnostic_only(self) -> None:
        forged_obligation = copy.deepcopy(self.g.obligation)
        forged_obligation.update({"id": "forged-obligation", "formula_sha256": ZERO,
                                  "canonical_proposition_sha256": ZERO})
        forged_certificate = copy.deepcopy(self.g.certificate)
        forged_certificate.update({"id": "forged-certificate",
                                   "obligation_id": "forged-obligation",
                                   "proposition_sha256": ZERO,
                                   "evidence": self.g.write("evidence/forged-proof-term.bin",
                                                            b"authored proof claim")})
        self.g.program["obligations"].append(forged_obligation)
        self.g.program["proof_certificates"].append(forged_certificate)
        self.g.program["modules"][0]["obligation_ids"].append("forged-obligation")
        self.g.program["modules"][0]["proof_certificate_ids"].append("forged-certificate")
        self.g.rehash_subject()
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn("authored subject-index obligation/proof rows", stderr)
        self.assertIn("independent complete source-policy", stderr)

    def test_forged_policy_olean_and_contract_claims_remain_red(self) -> None:
        self.g.docs["source_policy_census"].update(
            {"complete": True, "instances": ["obligation"], "missing": []})
        self.g.docs["native_obligation_census"].update(
            {"complete": True, "obligations": ["obligation"], "vacuous": 0})
        self.g.docs["rust_contracts"].update(
            {"all_typed": True, "design_only": 0, "ssa_epochs_bound": True})
        self.g.docs["external_olean"].update(
            {"transitive": True, "all_attested": True, "sorryAx": False})
        self.g.docs["kernel_replay"].update(
            {"replayed": True, "grade": "Certified", "axioms_policy_clean": True})
        checks, _ = self.check()
        for check_id in (
            "source_policy_obligation_bijection", "zero_vacuous_weakened_or_tautological_obligations",
            "rust_contracts_typed_ssa_epoch_effect_identity_bound", "zero_design_only_contracts",
            "external_olean_transitive_trust_attested", "proof_dependency_closure_policy_clean",
            "every_favorable_verdict_kernel_rechecked", "proof_grade_kernel_axiom_policy_exact",
        ):
            self.assertFalse(checks[check_id], check_id)

    def test_zero_obligations_cannot_satisfy_the_bijection_vacuously(self) -> None:
        self.g.program["obligations"] = []
        self.g.program["proof_certificates"] = []
        self.g.program["modules"][0]["obligation_ids"] = []
        self.g.program["modules"][0]["proof_certificate_ids"] = []
        self.g.rehash_subject()
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn("expected non-empty array", stderr)

    def test_duplicate_proof_cannot_launder_missing_or_extra_obligation(self) -> None:
        self.g.program["proof_certificates"].append(copy.deepcopy(self.g.certificate))
        self.g.program["modules"][0]["proof_certificate_ids"].append("certificate")
        self.g.rehash_subject()
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn("duplicate certificate", stderr)

    def test_mismatched_proposition_refuses_structural_relation(self) -> None:
        self.g.certificate["proposition_sha256"] = ZERO
        self.g.rehash_subject()
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn("proposition differs", stderr)

    def test_dropped_module_partition_refused(self) -> None:
        self.g.program["modules"][0]["obligation_ids"] = []
        self.g.rehash_subject()
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn("modules do not exactly partition", stderr)

    def test_cross_module_certificate_partition_refused(self) -> None:
        self.g.program["modules"].append({"id": "other", "body_ids": [],
                                          "obligation_ids": [],
                                          "proof_certificate_ids": ["certificate"]})
        self.g.program["modules"][0]["proof_certificate_ids"] = []
        self.g.rehash_subject()
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn("certificate's module differs from its partition", stderr)

    def test_owner_formula_encoder_splice_refused(self) -> None:
        self.g.obligation["formula_encoder_sha256"] = ZERO
        self.g.rehash_subject()
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn("formula encoder differs from owner", stderr)

    def test_unknown_policy_rule_refused(self) -> None:
        self.g.obligation["policy_rule_id"] = "unreviewed"
        self.g.rehash_subject()
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn("unknown owner policy rule", stderr)

    def test_wrong_root_refused(self) -> None:
        self.g.subject["roots"]["obligations"] = ZERO
        self.g.write("subject.json", self.g.subject)
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn("subject root obligations", stderr)

    def test_artifact_digest_mismatch_refuses_all_checks(self) -> None:
        bundle = {"schema": "trust.two-language.gate-evidence/v1", "gate": "G6",
                  "checker": "trust.two-language.g6.proof-authority/v2",
                  "artifacts": copy.deepcopy(self.g.refs)}
        bundle["artifacts"]["kernel_replay"]["sha256"] = ZERO
        rc, verdict, stderr = self.g.run(bundle_bytes=json.dumps(bundle).encode())
        self.assertEqual(rc, 1)
        self.assertFalse(any(row["passed"] for row in verdict["checks"]))
        self.assertIn("artifact kernel_replay: content hash mismatch", stderr)

    def test_traversal_and_symlink_refs_refused(self) -> None:
        bundle = {"schema": "trust.two-language.gate-evidence/v1", "gate": "G6",
                  "checker": "trust.two-language.g6.proof-authority/v2",
                  "artifacts": copy.deepcopy(self.g.refs)}
        bundle["artifacts"]["source_policy_census"]["path"] = "../outside.json"
        rc, verdict, stderr = self.g.run(bundle_bytes=json.dumps(bundle).encode())
        self.assertEqual(rc, 1)
        self.assertFalse(any(row["passed"] for row in verdict["checks"]))
        self.assertIn("canonical and root-relative", stderr)
        self.g.refs["source_policy_census"] = self.g.write(
            "evidence/source_policy_census.json", self.g.docs["source_policy_census"])
        (self.g.root / "evidence/source-policy-link.json").symlink_to("source_policy_census.json")
        bundle["artifacts"]["source_policy_census"] = {
            "path": "evidence/source-policy-link.json",
            "sha256": self.g.refs["source_policy_census"]["sha256"],
        }
        rc, verdict, stderr = self.g.run(bundle_bytes=json.dumps(bundle).encode())
        self.assertEqual(rc, 1)
        self.assertFalse(any(row["passed"] for row in verdict["checks"]))
        self.assertIn("symlink path component", stderr)

    def test_duplicate_json_keys_are_not_last_wins(self) -> None:
        bundle = b'{"schema":"trust.two-language.gate-evidence/v1","gate":"G6","gate":"G6"}'
        rc, verdict, stderr = self.g.run(bundle_bytes=bundle)
        self.assertEqual(rc, 1)
        self.assertFalse(any(row["passed"] for row in verdict["checks"]))
        self.assertIn("duplicate JSON key", stderr)

    def test_wrong_checker_hash_and_g8_only_arguments_refuse(self) -> None:
        rc, verdict, stderr = self.g.run(checker_digest=ZERO,
                                          extra=["--receipt", str(self.g.root / "receipt.json"),
                                                 "--prior-gates-root", ZERO])
        self.assertEqual(rc, 1)
        self.assertFalse(any(row["passed"] for row in verdict["checks"]))
        self.assertIn("checker snapshot does not match", stderr)
        self.assertIn("pre-seal", stderr)

    def test_non_git_revision_refused(self) -> None:
        rc, verdict, stderr = self.g.run(revision="not-a-revision")
        self.assertEqual(rc, 1)
        self.assertFalse(any(row["passed"] for row in verdict["checks"]))
        self.assertIn("source_revision must be", stderr)

    def assert_bijection_refused(self, wanted: str) -> str:
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertIn(wanted, stderr)
        self.assertNotIn("structurally consistent", stderr)
        self.assertNotIn("unhashable", stderr)
        return stderr

    def test_symlink_loop_root_still_emits_one_refusing_verdict(self) -> None:
        # Python 3.9 raises RuntimeError resolving a looping --root; that must
        # become a located refusal, never a traceback with no verdict.
        loop = self.g.root / "loop"
        loop.symlink_to("loop")
        rc, verdict, stderr = self.g.run(root_arg=str(loop))
        self.assertEqual(rc, 1)
        self.assertFalse(verdict["passed"])
        self.assertEqual(len(verdict["checks"]), len(runpy.run_path(str(CHECKER))["REQUIRED"]))
        self.assertFalse(any(row["passed"] for row in verdict["checks"]))
        self.assertIn("invalid bound G6 input", stderr)
        self.assertTrue("--root cannot be resolved" in stderr
                        or "--root must be an existing directory" in stderr, stderr)

    def test_non_string_body_ids_cannot_alias_through_bool_int_float(self) -> None:
        # True == 1 == 1.0 in Python; ids must be strings before any lookup.
        self.g.body["id"] = True
        self.g.obligation["body_id"] = 1
        self.g.certificate["body_id"] = 1.0
        self.g.program["modules"][0]["body_ids"] = [True]
        self.g.program["entrypoints"] = [True]
        self.g.rehash_subject()
        self.assert_bijection_refused("program body id: expected non-empty trimmed string")

    def test_non_string_obligation_body_id_refused(self) -> None:
        self.g.obligation["body_id"] = ["body"]
        self.g.rehash_subject()
        self.assert_bijection_refused(
            "program obligation obligation body_id: expected non-empty trimmed string")

    def test_row_program_id_cannot_rebind_rows_to_another_program(self) -> None:
        # Roots computed the way the pre-fix checker did, where a row-supplied
        # program_id shadowed the real one: the row must be refused outright.
        self.g.obligation.update({"program_id": "some-other-program",
                                  "unreviewed_extra_claim": {"kernel_replayed": True}})
        self.g.rehash_subject()
        self.g.subject["roots"]["obligations"] = root_of(
            [{"program_id": "program", **row} for row in self.g.program["obligations"]])
        self.g.write("subject.json", self.g.subject)
        self.assert_bijection_refused("program obligations[0]: expected exactly")

    def test_certificate_row_extra_keys_refused(self) -> None:
        self.g.certificate["program_id"] = "some-other-program"
        self.g.rehash_subject()
        self.g.subject["roots"]["proof_certificates"] = root_of(
            [{"program_id": "program", **row} for row in self.g.program["proof_certificates"]])
        self.g.write("subject.json", self.g.subject)
        self.assert_bijection_refused("program proof_certificates[0]: expected exactly")

    def test_foreign_policy_identity_refused(self) -> None:
        for field, value in (("goal_id", "SOME-OTHER-GOAL"),
                             ("repository_id", "https://example.invalid/fork"),
                             ("authorized_source_revision", "b" * 40),
                             ("authorized_acceptance_run_id", ZERO)):
            with self.subTest(field=field):
                policy = copy.deepcopy(self.g.policy)
                policy[field] = value
                self.g.write("policy.json", policy)
                self.assert_bijection_refused(
                    "owner policy: wrong schema, goal, repository, source, or run identity")
        del self.g.policy["authorized_acceptance_run_id"]
        self.g.write("policy.json", self.g.policy)
        self.assert_bijection_refused("owner policy: wrong schema, goal, repository")

    def test_non_hex_acceptance_run_id_refused(self) -> None:
        # Policy and subject both bind the same non-hex id, so only the
        # run-id format itself can refuse.
        run_id = "g6-hostile-test"
        self.g.policy["authorized_acceptance_run_id"] = run_id
        self.g.write("policy.json", self.g.policy)
        self.g.subject["acceptance_run_id"] = run_id
        self.g.write("subject.json", self.g.subject)
        rc, verdict, stderr = self.g.run(run_id=run_id)
        self.assertEqual(rc, 1)
        self.assertFalse(any(row["passed"] for row in verdict["checks"]))
        self.assertIn("--acceptance-run-id: expected lowercase SHA-256", stderr)
        self.assertNotIn("structurally consistent", stderr)

    def test_unhashable_ids_report_located_refusal(self) -> None:
        cases = (
            ("obligation", "policy_rule_id", ["rule-functional"],
             "program obligation obligation policy_rule_id: expected non-empty trimmed string"),
            ("certificate", "kernel_environment_id", ["clean"],
             "program certificate certificate kernel_environment_id: expected non-empty trimmed string"),
            ("certificate", "obligation_id", ["obligation"],
             "program certificate certificate obligation_id: expected non-empty trimmed string"),
            ("body", "id", ["body"], "program body id: expected non-empty trimmed string"),
        )
        for row_name, field, value, wanted in cases:
            with self.subTest(field=field):
                row = getattr(self.g, row_name)
                original = copy.deepcopy(row[field])
                row[field] = value
                self.g.rehash_subject()
                self.assert_bijection_refused(wanted)
                row[field] = original
                self.g.rehash_subject()

    def test_uninspectable_artifact_path_component_is_located(self) -> None:
        bundle = {"schema": "trust.two-language.gate-evidence/v1", "gate": "G6",
                  "checker": "trust.two-language.g6.proof-authority/v2",
                  "artifacts": copy.deepcopy(self.g.refs)}
        bundle["artifacts"]["kernel_replay"]["path"] = "evidence/" + "a" * 300
        rc, verdict, stderr = self.g.run(bundle_bytes=json.dumps(bundle).encode())
        self.assertEqual(rc, 1)
        self.assertFalse(any(row["passed"] for row in verdict["checks"]))
        # Python 3.9's is_symlink raises ENAMETOOLONG (now a located refusal);
        # later versions report the component as absent. Either way the
        # diagnostic names the artifact, never a bare errno.
        self.assertRegex(stderr, r"(?m)^G6: artifact kernel_replay: "
                                 r"(path cannot be inspected|file is absent)")
        self.assertNotRegex(stderr, r"(?m)^G6: \[Errno")

    def test_uninspectable_certificate_evidence_path_is_located(self) -> None:
        self.g.certificate["evidence"] = {"path": "evidence/" + "a" * 300, "sha256": ZERO}
        self.g.rehash_subject()
        checks, stderr = self.check()
        self.assertFalse(checks["obligation_certificate_bijection_matches_subject_index"])
        self.assertRegex(stderr, r"(?m)^G6: obligation_certificate_bijection_matches_subject_index: "
                                 r"program certificate certificate evidence: "
                                 r"(path cannot be inspected|file is absent)")
        self.assertNotRegex(stderr, r"(?m)^G6: [a-z_]+: \[Errno")


if __name__ == "__main__":
    unittest.main()
