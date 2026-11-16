"""Fail-closed controls for the standalone G8 product-acceptance checker."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
CHECKER = REPO / "scripts/completion_gates/check_g8_release_reproducibility.py"
TOP_VERIFIER = REPO / "scripts/two_language_completion_gate.py"


def load_gate_module():
    spec = importlib.util.spec_from_file_location("two_language_completion_gate_g8_test", TOP_VERIFIER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def load_checker_module():
    spec = importlib.util.spec_from_file_location("check_g8_release_reproducibility_g8_test", CHECKER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


gate = load_gate_module()
checker = load_checker_module()
GATE_ID = "trust.two-language.g8.release-reproducibility/v3"
CHECKS = (
    "g1_through_g7_same_source_revision",
    "g1_through_g7_same_run_and_subject_graph",
    "detached_release_seal_binds_prior_root_and_artifact",
    "owner_authorized_policy_and_repository_identity",
    "pinned_reproducible_environment",
    "cold_warm_cross_crate_release_reproducible",
    "release_artifact_binds_all_evidence",
    "authorized_toolchain_roster_exact",
    "acceptance_run_matrix_exact",
    "externally_pinned_top_verifier",
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, sort_keys=True, separators=(",", ":")), encoding="utf-8")


class Fixture:
    def __init__(self, outer: Path):
        self.outer = outer
        self.root = outer / "candidate"
        self.root.mkdir()
        self.run_id = "b" * 64
        self.revision = "a" * 40
        self.prior_root = "c" * 64
        self.toolchain = self.root / "toolchain.json"
        self.corpus = self.root / "corpus.json"
        self.subject = self.root / "subject.json"
        self.linked = self.root / "linked.bin"
        self.executable = self.root / "executable.bin"
        self.policy = self.root / "policy.json"
        self.authorization = self.root / "authorization.json"
        self.seal = self.root / "seal.json"
        self.bundle = self.root / "g8-evidence.json"
        self.receipt = self.root / "receipt.json"
        self.generic = self.root / "generic.json"
        self.owner = outer / "owner"
        self.external_verifier = outer / "top-verifier.py"
        write_json(self.toolchain, {"schema": "trust.two-language.toolchain-manifest/v1",
                                    "goal_id": "TRUST-TWO-LANGUAGE-100",
                                    "acceptance_run_id": self.run_id,
                                    "source_revision": self.revision, "components": []})
        write_json(self.corpus, {"schema": "trust.two-language.corpus-manifest/v1"})
        write_json(self.subject, {"schema": "trust.two-language.subject-index/v3",
                                  "acceptance_run_id": self.run_id,
                                  "source_revision": self.revision, "roots": {"bodies": "d" * 64}})
        self.linked.write_bytes(b"linked module")
        self.executable.write_bytes(b"executable")
        write_json(self.policy, {})
        write_json(self.authorization, {})
        write_json(self.seal, {"passed": True})
        write_json(self.generic, {"passed": True, "complete": True,
                                  "reproducible": True, "signed": True})
        self.artifacts = {check: self.ref(self.generic) for check in CHECKS}
        self.artifacts["detached_release_seal_binds_prior_root_and_artifact"] = self.ref(self.seal)
        # Each structural row cites exactly the input its predicate checks.
        self.artifacts["owner_authorized_policy_and_repository_identity"] = self.ref(self.authorization)
        self.write_bundle()
        gates = {}
        for number in range(1, 8):
            path = self.root / f"g{number}-evidence.json"
            write_json(path, {"schema": "trust.two-language.gate-evidence/v1",
                              "gate": f"G{number}", "checker": f"fixture.g{number}",
                              "artifacts": {}})
            gates[f"G{number}"] = {"checker": f"fixture.g{number}",
                                    "checker_sha256": "e" * 64, "evidence": self.ref(path)}
        gates["G8"] = {"checker": GATE_ID, "checker_sha256": sha(CHECKER),
                       "evidence": self.ref(self.bundle)}
        self.receipt_value = {
            "schema": "trust.two-language.completion/v2", "goal_id": "TRUST-TWO-LANGUAGE-100",
            "repository_id": "https://github.com/alabsystems/trust",
            "acceptance_run_id": self.run_id, "source_revision": self.revision,
            "toolchain_manifest": self.ref(self.toolchain), "corpus_manifest": self.ref(self.corpus),
            "subject_graph": self.ref(self.subject), "linked_module": self.ref(self.linked),
            "release_artifact": self.ref(self.executable), "authority_policy": self.ref(self.policy),
            "policy_authorization": self.ref(self.authorization), "gates": gates,
        }
        self.write_receipt()

    def ref(self, path: Path) -> dict[str, str]:
        return {"path": path.relative_to(self.root).as_posix(), "sha256": sha(path)}

    def write_bundle(self) -> None:
        write_json(self.bundle, {"schema": "trust.two-language.gate-evidence/v1",
                                 "gate": "G8", "checker": GATE_ID, "artifacts": self.artifacts})

    def write_receipt(self) -> None:
        write_json(self.receipt, self.receipt_value)

    def refresh_refs(self) -> None:
        for name, path in (
            ("toolchain_manifest", self.toolchain), ("corpus_manifest", self.corpus),
            ("subject_graph", self.subject), ("linked_module", self.linked),
            ("release_artifact", self.executable), ("authority_policy", self.policy),
            ("policy_authorization", self.authorization),
        ):
            self.receipt_value[name] = self.ref(path)
        self.write_bundle()
        self.receipt_value["gates"]["G8"]["evidence"] = self.ref(self.bundle)
        self.write_receipt()

    def args(self, *extra: str) -> list[str]:
        values = {
            "verify-evidence": self.bundle, "root": self.root, "receipt": self.receipt,
            "toolchain-manifest": self.toolchain, "corpus-manifest": self.corpus,
            "subject-graph": self.subject, "linked-module": self.linked,
            "release-artifact": self.executable, "authority-policy": self.policy,
            "policy-authorization": self.authorization, "acceptance-run-id": self.run_id,
            "source-revision": self.revision, "checker-sha256": sha(CHECKER),
            "evidence-sha256": sha(self.bundle), "toolchain-sha256": sha(self.toolchain),
            "corpus-manifest-sha256": sha(self.corpus), "subject-graph-sha256": sha(self.subject),
            "linked-module-sha256": sha(self.linked), "release-artifact-sha256": sha(self.executable),
            "authority-policy-sha256": sha(self.policy),
            "policy-authorization-sha256": sha(self.authorization),
            "prior-gates-root": self.prior_root,
        }
        return [part for name, value in values.items() for part in (f"--{name}", str(value))] + list(extra)

    def run(self, *extra: str) -> tuple[subprocess.CompletedProcess[str], dict]:
        result = subprocess.run([sys.executable, "-I", str(CHECKER), *self.args(*extra)],
                                cwd=self.root, capture_output=True, text=True, check=False)
        return result, json.loads(result.stdout)

    def sign_file(self, source: Path, namespace: str) -> Path:
        # ssh-keygen will not overwrite an existing signature (it asks on stdin),
        # so a re-sign would silently keep the stale one.
        signature = Path(f"{source}.sig")
        if signature.exists():
            signature.unlink()
        subprocess.run(["/usr/bin/ssh-keygen", "-Y", "sign", "-f", str(self.owner),
                        "-n", namespace, str(source)], capture_output=True, check=True,
                       stdin=subprocess.DEVNULL)
        return signature

    def signed_policy(self, *, with_roster: bool = False, claimed_fingerprint: str | None = None) -> None:
        contracts = {}
        if with_roster:
            roles = (
                "trustc", "rust_frontend", "lean_frontend", "clean_kernel", "trust_ir_producer",
                "trust_ir_linker", "trust_codegen", "trust_router", "proof_reconstructor",
                "runtime", "linker", "top_verifier", "python", "ssh_keygen",
            )
            components = []
            roster = []
            for role in roles:
                artifact = self.root / f"component-{role}.bin"
                artifact.write_bytes(role.encode("ascii"))
                components.append({"role": role, "name": role, "version": "1",
                                   "artifact": self.ref(artifact)})
                roster.append({"role": role, "name": role, "version": "1",
                               "artifact_sha256": sha(artifact)})
            write_json(self.toolchain, {"schema": "trust.two-language.toolchain-manifest/v1",
                                        "goal_id": "TRUST-TWO-LANGUAGE-100",
                                        "acceptance_run_id": self.run_id,
                                        "source_revision": self.revision, "components": components})
            environment = self.root / "acceptance-environment.json"
            write_json(environment, {
                "schema": "trust.two-language.acceptance-environment-contract/v1",
                "goal_id": "TRUST-TWO-LANGUAGE-100",
                "repository_id": "https://github.com/alabsystems/trust",
                "component_roster": roster,
                "run_modes": ["cold_build", "warm_build", "cross_crate", "mixed_language", "tests", "release"],
            })
            contracts["acceptance_environment"] = {
                "id": "trust.two-language.contract.acceptance-environment", **self.ref(environment)}
            self.artifacts["authorized_toolchain_roster_exact"] = self.ref(environment)
        if not self.owner.exists():
            subprocess.run(["/usr/bin/ssh-keygen", "-q", "-t", "ed25519", "-N", "",
                            "-f", str(self.owner)], capture_output=True, check=True,
                           stdin=subprocess.DEVNULL)
        fingerprint = subprocess.run(
            ["/usr/bin/ssh-keygen", "-lf", f"{self.owner}.pub", "-E", "sha256"],
            capture_output=True, text=True, check=True,
        ).stdout.split()[1]
        if claimed_fingerprint is not None:
            fingerprint = claimed_fingerprint
        write_json(self.policy, {
            "schema": "trust.two-language.authority-policy/v2",
            "goal_id": "TRUST-TWO-LANGUAGE-100",
            "repository_id": "https://github.com/alabsystems/trust",
            "completion_schema": "trust.two-language.completion/v2",
            "authorized_source_revision": self.revision,
            "authorized_acceptance_run_id": self.run_id,
            "owner_key_fingerprint": fingerprint,
            "authorized_inputs": {
                "toolchain_manifest_sha256": sha(self.toolchain),
                "corpus_manifest_sha256": sha(self.corpus),
                "subject_graph_sha256": sha(self.subject),
                "linked_module_sha256": sha(self.linked),
                "release_artifact_sha256": sha(self.executable),
            },
            "contracts": contracts,
            "authorized_checkers": {
                gate: {
                    "id": descriptor["checker"],
                    "path": ("scripts/completion_gates/check_g8_release_reproducibility.py"
                             if gate == "G8" else f"scripts/completion_gates/check_{gate.lower()}.py"),
                    "sha256": descriptor["checker_sha256"],
                }
                for gate, descriptor in self.receipt_value["gates"].items()
            },
        })
        signature = self.sign_file(self.policy, "trust-two-language-policy")
        write_json(self.authorization, {
            "schema": "trust.two-language.policy-authorization/v1",
            "algorithm": "ssh-ed25519", "namespace": "trust-two-language-policy",
            "signer_fingerprint": fingerprint, "policy_sha256": sha(self.policy),
            "signature": self.ref(signature),
        })
        self.artifacts["owner_authorized_policy_and_repository_identity"] = self.ref(self.authorization)
        self.refresh_refs()

    def install_top_verifier(self, candidate_bytes: bytes) -> Path:
        """Pin the real top verifier externally and cite the candidate copy."""
        self.external_verifier.write_bytes(TOP_VERIFIER.read_bytes())
        candidate = self.root / "scripts/two_language_completion_gate.py"
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_bytes(candidate_bytes)
        self.artifacts["externally_pinned_top_verifier"] = self.ref(candidate)
        self.refresh_refs()
        return candidate

    def signed_seal(self) -> None:
        payload = {"schema": "trust.two-language.detached-release-seal/v1",
                   "prior_gates_root": self.prior_root,
                   "release_artifact_sha256": sha(self.executable)}
        source = self.root / "seal-payload.json"
        write_json(source, payload)
        signature = self.sign_file(source, "trust-two-language-g8-release")
        write_json(self.seal, {**payload, "signature": self.ref(signature)})
        self.artifacts["detached_release_seal_binds_prior_root_and_artifact"] = self.ref(self.seal)
        self.write_bundle()
        self.refresh_refs()


@unittest.skipUnless(Path("/usr/bin/ssh-keygen").is_file(), "needs ssh-keygen")
class G8CheckerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="trust-g8-test-")
        self.addCleanup(self.temp.cleanup)
        self.fixture = Fixture(Path(self.temp.name))

    def row(self, verdict: dict, check: str) -> dict:
        return next(row for row in verdict["checks"] if row["id"] == check)

    def test_schema_owned_path_and_exact_runner_protocol(self) -> None:
        self.assertEqual(gate.CHECKER_PATHS["G8"], CHECKER.relative_to(REPO).as_posix())
        self.assertEqual(gate.CHECKER_IDS["G8"], GATE_ID)
        self.assertEqual(gate.REQUIRED_CHECKS["G8"], CHECKS)

        self.fixture.signed_policy(with_roster=True)
        self.fixture.signed_seal()
        self.fixture.install_top_verifier(TOP_VERIFIER.read_bytes())

        candidate = self.fixture.root / gate.CHECKER_PATHS["G8"]
        candidate.parent.mkdir(parents=True)
        candidate.write_bytes(CHECKER.read_bytes())
        subprocess.run(["git", "init", "-q", str(self.fixture.root)], check=True)
        subprocess.run(["git", "-C", str(self.fixture.root), "add", gate.CHECKER_PATHS["G8"]], check=True)
        subprocess.run(
            ["git", "-C", str(self.fixture.root), "-c", "user.name=G8 Fixture",
             "-c", "user.email=g8@example.invalid", "commit", "-q", "-m", "checker fixture"],
            check=True,
        )
        revision = subprocess.run(
            ["git", "-C", str(self.fixture.root), "rev-parse", "HEAD"],
            check=True, capture_output=True, text=True,
        ).stdout.strip()
        runner = gate.ReceiptValidator(
            self.fixture.root, self.fixture.receipt, Path(f"{self.fixture.owner}.pub"),
            self.fixture.external_verifier, sha(self.fixture.external_verifier),
        )
        resolved = runner.resolve_checker("G8", revision, sha(CHECKER), "G8.checker")
        self.assertIsNotNone(resolved)
        self.assertEqual(resolved[2], CHECKER.read_bytes())
        self.assertEqual(runner.errors, [])

        verdict = runner.run_checker(
            gate="G8", checker_bytes=resolved[2], evidence_path=self.fixture.bundle,
            toolchain_path=self.fixture.toolchain, corpus_path=self.fixture.corpus,
            subject_graph_path=self.fixture.subject, linked_module_path=self.fixture.linked,
            release_artifact_path=self.fixture.executable, policy_path=self.fixture.policy,
            policy_authorization_path=self.fixture.authorization,
            acceptance_run_id=self.fixture.run_id, subject_graph_digest=sha(self.fixture.subject),
            linked_module_digest=sha(self.fixture.linked), release_artifact_digest=sha(self.fixture.executable),
            policy_digest=sha(self.fixture.policy), policy_authorization_digest=sha(self.fixture.authorization),
            source_revision=self.fixture.revision, checker_digest=sha(CHECKER),
            evidence_digest=sha(self.fixture.bundle), toolchain_digest=sha(self.fixture.toolchain),
            corpus_digest=sha(self.fixture.corpus), prior_gates_root=self.fixture.prior_root,
        )
        self.assertIsNotNone(verdict)
        self.assertEqual(verdict["schema"], gate.CHECKER_VERDICT_SCHEMA)
        self.assertEqual(verdict["checker"], gate.CHECKER_IDS["G8"])
        self.assertEqual(verdict["prior_gates_root"], self.fixture.prior_root)
        self.assertEqual(tuple(row["id"] for row in verdict["checks"]), gate.REQUIRED_CHECKS["G8"])
        self.assertFalse(verdict["passed"])
        self.assertTrue(all(not row["passed"] for row in verdict["checks"]))
        self.assertTrue(any("checker exited 1" in error for error in runner.errors))
        self.assertIn("independently configured owner-key authorization anchor", " ".join(runner.errors))

    def test_favorable_authored_metadata_never_mints_g8(self) -> None:
        result, verdict = self.fixture.run()
        self.assertEqual(result.returncode, 1)
        self.assertFalse(verdict["passed"])
        self.assertEqual(tuple(row["id"] for row in verdict["checks"]), CHECKS)
        self.assertTrue(all(row["passed"] is False for row in verdict["checks"]))
        self.assertIn("independently executed", result.stderr)

    def test_bare_forged_seal_cannot_pass(self) -> None:
        self.fixture.signed_policy()
        write_json(self.fixture.seal, {"schema": "trust.two-language.detached-release-seal/v1",
                                       "prior_gates_root": self.fixture.prior_root,
                                       "release_artifact_sha256": sha(self.fixture.executable),
                                       "signature": self.fixture.ref(self.fixture.generic)})
        self.fixture.artifacts["detached_release_seal_binds_prior_root_and_artifact"] = self.fixture.ref(self.fixture.seal)
        self.fixture.write_bundle()
        self.fixture.refresh_refs()
        result, verdict = self.fixture.run("--trusted-owner-key", f"{self.fixture.owner}.pub")
        self.assertFalse(self.row(verdict, "detached_release_seal_binds_prior_root_and_artifact")["passed"])
        self.assertIn("external owner signature does not verify", result.stderr)

    def test_signed_policy_and_detached_seal_are_bounded_progress_only(self) -> None:
        self.fixture.signed_policy()
        self.fixture.signed_seal()
        result, verdict = self.fixture.run("--trusted-owner-key", f"{self.fixture.owner}.pub")
        self.assertEqual(result.returncode, 1)
        self.assertFalse(self.row(verdict, "owner_authorized_policy_and_repository_identity")["passed"])
        self.assertFalse(self.row(verdict, "detached_release_seal_binds_prior_root_and_artifact")["passed"])
        self.assertIn("policy signature verifies under the caller-supplied key", result.stderr)
        self.assertIn("detached seal signature verifies under the caller-supplied key", result.stderr)
        self.assertFalse(self.row(verdict, "g1_through_g7_same_run_and_subject_graph")["passed"])
        self.assertFalse(verdict["passed"])

    def test_signed_roster_matches_every_component_but_does_not_prove_replay(self) -> None:
        self.fixture.signed_policy(with_roster=True)
        result, verdict = self.fixture.run("--trusted-owner-key", f"{self.fixture.owner}.pub")
        self.assertFalse(self.row(verdict, "authorized_toolchain_roster_exact")["passed"])
        self.assertIn("roster matches the contract signed by the caller-supplied key", result.stderr)
        self.assertFalse(self.row(verdict, "acceptance_run_matrix_exact")["passed"])
        self.assertFalse(verdict["passed"])
        (self.fixture.root / "component-linker.bin").write_bytes(b"forged linker")
        result, verdict = self.fixture.run("--trusted-owner-key", f"{self.fixture.owner}.pub")
        self.assertFalse(self.row(verdict, "authorized_toolchain_roster_exact")["passed"])
        self.assertNotIn("roster matches the contract signed", result.stderr)

    def test_hostile_self_key_and_self_pin_leave_every_conjunct_red(self) -> None:
        self.fixture.signed_policy(with_roster=True)
        self.fixture.signed_seal()
        self.fixture.install_top_verifier(TOP_VERIFIER.read_bytes())
        result, verdict = self.fixture.run(
            "--trusted-owner-key", f"{self.fixture.owner}.pub",
            "--external-verifier", str(self.fixture.external_verifier),
            "--external-verifier-sha256", sha(self.fixture.external_verifier),
        )
        self.assertEqual(result.returncode, 1)
        self.assertFalse(verdict["passed"])
        self.assertTrue(all(not row["passed"] for row in verdict["checks"]))
        self.assertIn("independently configured owner-key authorization anchor", result.stderr)
        self.assertIn("no independently configured owner verifier pin exists", result.stderr)

    def test_spliced_prior_root_rejects_detached_seal(self) -> None:
        self.fixture.signed_policy()
        self.fixture.signed_seal()
        self.fixture.prior_root = "f" * 64
        _, verdict = self.fixture.run("--trusted-owner-key", f"{self.fixture.owner}.pub")
        self.assertFalse(self.row(verdict, "detached_release_seal_binds_prior_root_and_artifact")["passed"])

    def test_spliced_executable_rejects_signed_policy_and_seal(self) -> None:
        self.fixture.signed_policy()
        self.fixture.signed_seal()
        self.fixture.executable.write_bytes(b"other executable")
        self.fixture.refresh_refs()
        _, verdict = self.fixture.run("--trusted-owner-key", f"{self.fixture.owner}.pub")
        self.assertFalse(self.row(verdict, "owner_authorized_policy_and_repository_identity")["passed"])
        self.assertFalse(self.row(verdict, "detached_release_seal_binds_prior_root_and_artifact")["passed"])

    def test_external_key_is_required_and_must_be_outside_candidate(self) -> None:
        self.fixture.signed_policy()
        _, verdict = self.fixture.run()
        self.assertFalse(self.row(verdict, "owner_authorized_policy_and_repository_identity")["passed"])
        copied = self.fixture.root / "copied-owner.pub"
        shutil.copyfile(f"{self.fixture.owner}.pub", copied)
        _, verdict = self.fixture.run("--trusted-owner-key", str(copied))
        self.assertFalse(self.row(verdict, "owner_authorized_policy_and_repository_identity")["passed"])

    def test_aliased_spelling_of_candidate_is_not_outside_root(self) -> None:
        # "Outside --root" is filesystem identity: a case-aliased spelling on a
        # case-insensitive volume, or a symlinked alias of the root directory,
        # names the candidate tree however differently it is written.
        self.fixture.signed_policy()
        root = self.fixture.root.resolve()
        copied = root / "copied-owner.pub"
        shutil.copyfile(f"{self.fixture.owner}.pub", copied)
        link = self.fixture.outer / "root-link"
        link.symlink_to(root, target_is_directory=True)
        with self.assertRaisesRegex(checker.Refusal, "must be outside --root"):
            checker.external_path(root, str(link / copied.name), "--trusted-owner-key")
        alias = root.with_name(root.name.upper())
        if not alias.exists() or not alias.samefile(root):
            self.skipTest("temporary filesystem is case-sensitive: no case alias of --root exists")
        with self.assertRaisesRegex(checker.Refusal, "must be outside --root"):
            checker.external_path(root, str(alias / copied.name), "--trusted-owner-key")
        with self.assertRaisesRegex(checker.Refusal, "must be outside --root"):
            checker.external_path(alias, str(copied), "--trusted-owner-key")
        result, verdict = self.fixture.run("--trusted-owner-key", str(alias / copied.name))
        self.assertFalse(self.row(verdict, "owner_authorized_policy_and_repository_identity")["passed"])
        self.assertIn("--trusted-owner-key must be outside --root", result.stderr)
        self.assertNotIn("policy signature verifies under the caller-supplied key", result.stderr)

    def test_uninspectable_ancestor_refuses_rather_than_reads_outside(self) -> None:
        # A component whose identity cannot be read is not evidence that the
        # path lies outside --root; the guard refuses instead of skipping it.
        root = self.fixture.root.resolve()
        with self.assertRaisesRegex(checker.Refusal, "cannot inspect"):
            checker.inside_root(root, self.fixture.outer.resolve() / "missing" / "key.pub")

    def test_spliced_subject_index_run_refuses_all_structural_positives(self) -> None:
        self.fixture.signed_policy()
        write_json(self.fixture.subject, {"schema": "trust.two-language.subject-index/v3",
                                          "acceptance_run_id": "0" * 64,
                                          "source_revision": self.fixture.revision,
                                          "roots": {"bodies": "d" * 64}})
        self.fixture.refresh_refs()
        _, verdict = self.fixture.run("--trusted-owner-key", f"{self.fixture.owner}.pub")
        self.assertFalse(verdict["passed"])
        self.assertTrue(all(not row["passed"] for row in verdict["checks"]))

    def test_signed_wrong_completion_schema_does_not_authorize_policy(self) -> None:
        self.fixture.signed_policy()
        policy = json.loads(self.fixture.policy.read_text(encoding="utf-8"))
        policy["completion_schema"] = "attacker.accept-all/v1"
        write_json(self.fixture.policy, policy)
        signature = self.fixture.sign_file(self.fixture.policy, "trust-two-language-policy")
        authorization = json.loads(self.fixture.authorization.read_text(encoding="utf-8"))
        authorization["policy_sha256"] = sha(self.fixture.policy)
        authorization["signature"] = self.fixture.ref(signature)
        write_json(self.fixture.authorization, authorization)
        self.fixture.artifacts["owner_authorized_policy_and_repository_identity"] = (
            self.fixture.ref(self.fixture.authorization))
        self.fixture.refresh_refs()
        result, verdict = self.fixture.run("--trusted-owner-key", f"{self.fixture.owner}.pub")
        self.assertFalse(self.row(verdict, "owner_authorized_policy_and_repository_identity")["passed"])
        self.assertIn("authority policy completion_schema differs", result.stderr)

    def test_preseal_evidence_cannot_reference_detached_seal(self) -> None:
        self.fixture.signed_policy()
        self.fixture.signed_seal()
        g3_path = self.fixture.root / "g3-evidence.json"
        g3 = json.loads(g3_path.read_text(encoding="utf-8"))
        g3["artifacts"]["forged-preseal-dependency"] = self.fixture.ref(self.fixture.seal)
        write_json(g3_path, g3)
        self.fixture.receipt_value["gates"]["G3"]["evidence"] = self.fixture.ref(g3_path)
        self.fixture.write_receipt()
        _, verdict = self.fixture.run("--trusted-owner-key", f"{self.fixture.owner}.pub")
        self.assertFalse(self.row(verdict, "detached_release_seal_binds_prior_root_and_artifact")["passed"])

    def test_g8_descriptor_splice_refuses_all_rows(self) -> None:
        self.fixture.receipt_value["gates"]["G8"]["checker_sha256"] = "0" * 64
        self.fixture.write_receipt()
        _, verdict = self.fixture.run()
        self.assertTrue(all(not row["passed"] for row in verdict["checks"]))

    def test_spliced_gate_evidence_does_not_establish_cross_gate_identity(self) -> None:
        other = self.fixture.root / "foreign-g4.json"
        write_json(other, {"passed": True, "source_revision": "0" * 40,
                           "acceptance_run_id": "0" * 64})
        self.fixture.receipt_value["gates"]["G4"]["evidence"] = self.fixture.ref(other)
        self.fixture.write_receipt()
        _, verdict = self.fixture.run()
        self.assertFalse(self.row(verdict, "g1_through_g7_same_source_revision")["passed"])
        self.assertFalse(self.row(verdict, "g1_through_g7_same_run_and_subject_graph")["passed"])

    def test_external_verifier_must_be_pinned_and_match_candidate_bytes(self) -> None:
        self.fixture.install_top_verifier(TOP_VERIFIER.read_bytes())
        result, verdict = self.fixture.run("--external-verifier", str(self.fixture.external_verifier),
                                          "--external-verifier-sha256", sha(self.fixture.external_verifier))
        self.assertFalse(self.row(verdict, "externally_pinned_top_verifier")["passed"])
        self.assertIn("no independently configured owner verifier pin exists", result.stderr)
        self.fixture.install_top_verifier(b"print('accept anything')\n")
        result, verdict = self.fixture.run("--external-verifier", str(self.fixture.external_verifier),
                                          "--external-verifier-sha256", sha(self.fixture.external_verifier))
        self.assertFalse(self.row(verdict, "externally_pinned_top_verifier")["passed"])
        self.assertIn("candidate-tree top verifier differs", result.stderr)

    def split_owner_key(self) -> tuple[Path, str]:
        """A key file whose first parseable line is key B, while its first two
        whitespace tokens, spanning lines, are signing key A."""
        signer_public = Path(f"{self.fixture.owner}.pub").read_text(encoding="utf-8").split()
        other = self.fixture.outer / "other-owner"
        subprocess.run(["/usr/bin/ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", "other",
                        "-f", str(other)], capture_output=True, check=True, stdin=subprocess.DEVNULL)
        other_line = Path(f"{other}.pub").read_text(encoding="utf-8").strip()
        other_fingerprint = subprocess.run(
            ["/usr/bin/ssh-keygen", "-lf", f"{other}.pub", "-E", "sha256"],
            capture_output=True, text=True, check=True,
        ).stdout.split()[1]
        split = self.fixture.outer / "split-owner.pub"
        split.write_text(f"ssh-ed25519\n{signer_public[1]}\n{other_line}\n", encoding="utf-8")
        return split, other_fingerprint

    def test_split_line_owner_key_cannot_bind_one_fingerprint_to_another_signer(self) -> None:
        # Signed by the fixture owner (key A), but claiming key B, which is what
        # `ssh-keygen -lf` reports for the split file.  The fingerprint and the
        # verifying material must come from the same bytes, so this refuses.
        self.fixture.signed_policy()
        split, claimed = self.split_owner_key()
        self.fixture.signed_policy(claimed_fingerprint=claimed)
        self.fixture.signed_seal()
        result, verdict = self.fixture.run("--trusted-owner-key", str(split))
        self.assertFalse(self.row(verdict, "owner_authorized_policy_and_repository_identity")["passed"])
        self.assertFalse(self.row(verdict, "detached_release_seal_binds_prior_root_and_artifact")["passed"])
        self.assertIn("external owner key must contain exactly one ssh-ed25519 key", result.stderr)
        self.assertNotIn("policy signature verifies under the caller-supplied key", result.stderr)
        self.assertNotIn("detached seal signature verifies under the caller-supplied key", result.stderr)

    def test_owner_key_file_must_be_exactly_one_ed25519_line(self) -> None:
        self.fixture.signed_policy()
        root = self.fixture.root.resolve()
        split, _ = self.split_owner_key()
        public_line = Path(f"{self.fixture.owner}.pub").read_text(encoding="utf-8").strip()
        two = self.fixture.outer / "two-keys.pub"
        two.write_text(f"{public_line}\n{public_line}\n", encoding="utf-8")
        bad_b64 = self.fixture.outer / "bad-b64.pub"
        bad_b64.write_text("ssh-ed25519 not*base64 c\n", encoding="utf-8")
        for path in (split, two, bad_b64):
            with self.subTest(path.name), self.assertRaisesRegex(
                    checker.Refusal, "external owner key must contain exactly one ssh-ed25519 key"):
                checker.owner_key(root, str(path))
        # Control: an ordinary one-line key with a comment, surrounded by blank
        # lines, fingerprints exactly as ssh-keygen reports the original file.
        padded = self.fixture.outer / "padded.pub"
        padded.write_text(f"\n{public_line}\n\n", encoding="utf-8")
        expected = subprocess.run(
            ["/usr/bin/ssh-keygen", "-lf", f"{self.fixture.owner}.pub", "-E", "sha256"],
            capture_output=True, text=True, check=True,
        ).stdout.split()[1]
        _, fingerprint, material = checker.owner_key(root, str(padded))
        self.assertEqual(fingerprint, expected)
        self.assertEqual(material, " ".join(public_line.split()[:2]))

    def test_structural_rows_must_cite_the_input_their_predicate_checks(self) -> None:
        self.fixture.signed_policy(with_roster=True)
        self.fixture.signed_seal()
        self.fixture.install_top_verifier(TOP_VERIFIER.read_bytes())
        external = ("--trusted-owner-key", f"{self.fixture.owner}.pub",
                    "--external-verifier", str(self.fixture.external_verifier),
                    "--external-verifier-sha256", sha(self.fixture.external_verifier))
        rows = {
            "owner_authorized_policy_and_repository_identity":
                "policy signature verifies under the caller-supplied key",
            "authorized_toolchain_roster_exact":
                "roster matches the contract signed by the caller-supplied key",
            "externally_pinned_top_verifier":
                "verifier bytes match the caller-supplied path and digest",
        }
        # Control: correctly cited inputs reach each row's structural-only reason.
        result, verdict = self.fixture.run(*external)
        for check, structural in rows.items():
            self.assertIn(f"{check}: {structural}", result.stderr)
            self.assertEqual(self.row(verdict, check)["artifacts"], [self.fixture.artifacts[check]])
        for check, structural in rows.items():
            with self.subTest(check):
                cited = self.fixture.artifacts[check]
                self.fixture.artifacts[check] = self.fixture.ref(self.fixture.generic)
                self.fixture.write_bundle()
                self.fixture.refresh_refs()
                result, verdict = self.fixture.run(*external)
                self.assertFalse(self.row(verdict, check)["passed"])
                self.assertIn(f"{check}: {check} artifact must be the input its predicate checks",
                              result.stderr)
                self.assertNotIn(f"{check}: {structural}", result.stderr)
                self.fixture.artifacts[check] = cited
                self.fixture.write_bundle()
                self.fixture.refresh_refs()

    def test_missing_and_malformed_evidence_refuses(self) -> None:
        self.fixture.artifacts.pop("acceptance_run_matrix_exact")
        self.fixture.write_bundle()
        self.fixture.refresh_refs()
        result, verdict = self.fixture.run()
        self.assertEqual(result.returncode, 1)
        self.assertFalse(verdict["passed"])
        self.assertIn("G8 evidence artifacts", result.stderr)


if __name__ == "__main__":
    unittest.main()
