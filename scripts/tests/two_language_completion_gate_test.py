#!/usr/bin/env python3
"""Self-executing adversarial controls for the two-language completion receipt."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "two_language_completion_gate.py"


def load_gate_module():
    spec = importlib.util.spec_from_file_location("two_language_completion_gate", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


gate = load_gate_module()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def checker_source(gate_id: str) -> str:
    """A fixture checker that independently validates each referenced artifact."""
    checker_id = gate.CHECKER_IDS[gate_id]
    required = list(gate.REQUIRED_CHECKS[gate_id])
    return f'''#!/usr/bin/env python3
import argparse
import hashlib
import json
import sys
from pathlib import Path

GATE = {gate_id!r}
CHECKER = {checker_id!r}
REQUIRED = {required!r}
SCHEMA = {gate.CHECKER_VERDICT_SCHEMA!r}
GOAL = {gate.GOAL_ID!r}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

ap = argparse.ArgumentParser()
ap.add_argument("--verify-evidence", required=True)
ap.add_argument("--root", required=True)
ap.add_argument("--receipt")
ap.add_argument("--toolchain-manifest", required=True)
ap.add_argument("--corpus-manifest", required=True)
ap.add_argument("--subject-graph", required=True)
ap.add_argument("--linked-module", required=True)
ap.add_argument("--release-artifact", required=True)
ap.add_argument("--authority-policy", required=True)
ap.add_argument("--policy-authorization", required=True)
ap.add_argument("--acceptance-run-id", required=True)
ap.add_argument("--source-revision", required=True)
ap.add_argument("--checker-sha256", required=True)
ap.add_argument("--evidence-sha256", required=True)
ap.add_argument("--toolchain-sha256", required=True)
ap.add_argument("--corpus-manifest-sha256", required=True)
ap.add_argument("--subject-graph-sha256", required=True)
ap.add_argument("--linked-module-sha256", required=True)
ap.add_argument("--release-artifact-sha256", required=True)
ap.add_argument("--authority-policy-sha256", required=True)
ap.add_argument("--policy-authorization-sha256", required=True)
ap.add_argument("--prior-gates-root")
args = ap.parse_args()
root = Path(args.root).resolve()
try:
    bundle = json.loads(Path(args.verify_evidence).read_text(encoding="utf-8"))
except Exception:
    bundle = {{}}
passed = (
    set(bundle) == {{"schema", "gate", "checker", "artifacts"}}
    and bundle.get("schema") == "fixture.gate-input/v1"
    and bundle.get("gate") == GATE
    and bundle.get("checker") == CHECKER
    and isinstance(bundle.get("artifacts"), dict)
    and set(bundle.get("artifacts", {{}})) == set(REQUIRED)
    and (
        (GATE == "G8" and args.receipt is not None and args.prior_gates_root is not None)
        or (GATE != "G8" and args.receipt is None and args.prior_gates_root is None)
    )
)
checks = []
for check_id in REQUIRED:
    ref = bundle.get("artifacts", {{}}).get(check_id)
    row_ok = isinstance(ref, dict) and set(ref) == {{"path", "sha256"}}
    artifacts = [ref] if row_ok else []
    if row_ok:
        path = (root / ref["path"]).resolve()
        row_ok = (
            path.is_relative_to(root)
            and path.is_file()
            and digest(path) == ref["sha256"]
        )
        if row_ok:
            try:
                value = json.loads(path.read_text(encoding="utf-8"))
            except Exception:
                row_ok = False
            else:
                row_ok = value == {{"gate": GATE, "check": check_id, "result": "pass"}}
    passed = passed and row_ok
    checks.append({{"id": check_id, "passed": row_ok, "artifacts": artifacts}})
verdict = {{
    "schema": SCHEMA,
    "goal_id": GOAL,
    "gate": GATE,
    "checker": CHECKER,
    "repository_id": {gate.REPOSITORY_ID!r},
    "acceptance_run_id": args.acceptance_run_id,
    "checker_sha256": args.checker_sha256,
    "evidence_sha256": args.evidence_sha256,
    "source_revision": args.source_revision,
    "toolchain_sha256": args.toolchain_sha256,
    "corpus_manifest_sha256": args.corpus_manifest_sha256,
    "subject_graph_sha256": args.subject_graph_sha256,
    "linked_module_sha256": args.linked_module_sha256,
    "release_artifact_sha256": args.release_artifact_sha256,
    "authority_policy_sha256": args.authority_policy_sha256,
    "policy_authorization_sha256": args.policy_authorization_sha256,
    "prior_gates_root": args.prior_gates_root,
    "passed": passed,
    "checks": checks,
}}
print(json.dumps(verdict))
sys.exit(0 if passed else 1)
'''


class GreenReceipt:
    """A clean Git root with tracked checkers and ignored generated evidence."""

    def __init__(self, base: Path):
        self.root = base / "repo"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(
            ["git", "-C", str(self.root), "config", "user.email", "gate@test.invalid"],
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(self.root), "config", "user.name", "gate-test"],
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(self.root), "remote", "add", "origin", gate.REPOSITORY_ID],
            check=True,
        )
        (self.root / ".gitignore").write_text("evidence/\n", encoding="utf-8")
        (self.root / "source.txt").write_text("pinned source\n", encoding="utf-8")
        (self.root / "fixture.rs").write_text("fn main() {}\n", encoding="utf-8")
        (self.root / "Fixture.lean").write_text("def answer : Nat := 42\n", encoding="utf-8")
        (self.root / "mixed.fixture").write_text("rust -> lean -> rust\n", encoding="utf-8")
        candidate_top = self.root / "scripts" / "two_language_completion_gate.py"
        candidate_top.parent.mkdir(parents=True, exist_ok=True)
        candidate_top.write_bytes(SCRIPT.read_bytes())
        self.candidate_top = candidate_top
        for gate_id, relative in gate.CHECKER_PATHS.items():
            checker = self.root / relative
            checker.parent.mkdir(parents=True, exist_ok=True)
            checker.write_text(checker_source(gate_id), encoding="utf-8")
        subprocess.run(["git", "-C", str(self.root), "add", "."], check=True)
        subprocess.run(
            ["git", "-C", str(self.root), "commit", "-q", "-m", "fixture source"],
            check=True,
        )
        self.source_revision = subprocess.run(
            ["git", "-C", str(self.root), "rev-parse", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()

        self.evidence_dir = self.root / "evidence"
        self.evidence_dir.mkdir()
        self.acceptance_run_id = hashlib.sha256(b"fixture acceptance run").hexdigest()
        self.linked_module = self.evidence_dir / "linked.trustir"
        self.linked_module.write_text("fixture linked Trust-IR module\n", encoding="utf-8")
        self.release_artifact = self.evidence_dir / "fixture.bin"
        self.release_artifact.write_bytes(b"fixture executable\n")

        def text_artifact(name: str, contents: str) -> Path:
            path = self.evidence_dir / name
            path.write_text(contents, encoding="utf-8")
            return path

        def named_ref(path: Path, ref_id: str) -> dict[str, str]:
            return {"id": ref_id, **self.ref(path)}

        semantics_refs: dict[str, dict[str, str]] = {}
        for role in sorted(gate.SEMANTICS_DEFINITIONS):
            semantics_refs[role] = named_ref(
                text_artifact(f"semantics-{role}.def", f"formal {role} definition\n"),
                f"fixture.semantics.{role}",
            )
        semantics_contract = self.evidence_dir / "semantics-contract.json"
        write_json(
            semantics_contract,
            {
                "schema": gate.AUTHORITY_CONTRACTS["semantics"][1],
                "goal_id": gate.GOAL_ID,
                "repository_id": gate.REPOSITORY_ID,
                "definitions": semantics_refs,
            },
        )

        applicability = named_ref(
            text_artifact("obligation-applicability.def", "typed applicability relation\n"),
            "fixture.obligations.applicability",
        )
        formula_schema = named_ref(
            text_artifact("obligation-formula.def", "typed Trust-IR formula schema\n"),
            "fixture.obligations.formula-schema",
        )
        formula_encoder = named_ref(
            text_artifact("formula-encoder.def", "Trust-IR formula encoder\n"),
            "fixture.obligations.formula-encoder",
        )
        obligation_rules = [
            {
                "id": f"fixture.rule.{rule_class.replace('_', '-')}",
                "class": rule_class,
                "applicability": applicability,
                "formula_schema": formula_schema,
            }
            for rule_class in sorted(gate.OBLIGATION_CLASSES)
        ]
        obligations_contract = self.evidence_dir / "obligations-contract.json"
        write_json(
            obligations_contract,
            {
                "schema": gate.AUTHORITY_CONTRACTS["obligations"][1],
                "goal_id": gate.GOAL_ID,
                "repository_id": gate.REPOSITORY_ID,
                "rules": obligation_rules,
                "formula_encoder": formula_encoder,
            },
        )

        proposition_encoder = named_ref(
            text_artifact("proposition-encoder.def", "canonical Lean proposition encoder\n"),
            "fixture.proof.canonical-proposition-encoder",
        )
        kernel_artifact = named_ref(
            text_artifact("clean-kernel.bin", "fixture Clean kernel\n"),
            "fixture.kernel.clean",
        )
        axiom_policy = named_ref(
            text_artifact("axiom-policy.json", '{"deny":["sorryAx"]}\n'),
            "fixture.proof.axiom-policy",
        )
        olean_policy = named_ref(
            text_artifact("olean-policy.json", '{"transitive":true}\n'),
            "fixture.proof.olean-policy",
        )
        kernel_environment_sha256 = "8" * 64
        axiom_root_sha256 = "b" * 64
        proof_contract = self.evidence_dir / "proof-authority-contract.json"
        write_json(
            proof_contract,
            {
                "schema": gate.AUTHORITY_CONTRACTS["proof_authority"][1],
                "goal_id": gate.GOAL_ID,
                "repository_id": gate.REPOSITORY_ID,
                "canonical_proposition_encoder": proposition_encoder,
                "kernels": [
                    {
                        "id": "fixture.kernel.environment",
                        "environment_sha256": kernel_environment_sha256,
                        "artifact": kernel_artifact,
                        "proof_grades": ["kernel-checked"],
                        "axiom_allowlist_root_sha256": axiom_root_sha256,
                    }
                ],
                "axiom_policy": axiom_policy,
                "external_olean_policy": olean_policy,
                "denied_axioms": ["sorryAx"],
            },
        )

        compatibility_surfaces = {}
        for surface, capabilities in gate.COMPATIBILITY_CAPABILITIES.items():
            feature_path = self.evidence_dir / f"compat-{surface}-features.json"
            write_json(
                feature_path,
                {
                    "schema": "trust.two-language.compatibility-feature-manifest/v1",
                    "surface": surface,
                    "features": sorted(capabilities),
                },
            )
            compatibility_surfaces[surface] = {
                "required": True,
                "upstream_repository": f"https://example.invalid/{surface}",
                "upstream_version": "fixture-v1",
                "feature_manifest": self.ref(feature_path),
                "corpus_root_sha256": hashlib.sha256(
                    f"{surface} fixture corpus".encode()
                ).hexdigest(),
                "elaborator": named_ref(
                    text_artifact(f"{surface}-elaborator.bin", f"{surface} elaborator\n"),
                    f"fixture.compat.{surface}.elaborator",
                ),
                "ingestion_authority": "zero-authority",
                "computational_destinations": gate.COMPATIBILITY_IMAGE_DESTINATIONS[surface][
                    "computational"
                ],
                "computational_image": (
                    named_ref(
                        text_artifact(
                            f"{surface}-computational-image.def",
                            f"{surface} canonical computational image\n",
                        ),
                        f"fixture.compat.{surface}.computational-image",
                    )
                    if gate.COMPATIBILITY_IMAGE_DESTINATIONS[surface]["computational"]
                    else None
                ),
                "proposition_destinations": gate.COMPATIBILITY_IMAGE_DESTINATIONS[surface][
                    "proposition"
                ],
                "proposition_image": named_ref(
                    text_artifact(
                        f"{surface}-proposition-image.def",
                        f"{surface} canonical Lean proposition image\n",
                    ),
                    f"fixture.compat.{surface}.proposition-image",
                ),
                "semantic_capabilities": sorted(capabilities),
            }
        self.compatibility_contract = self.evidence_dir / "compatibility-contract.json"
        write_json(
            self.compatibility_contract,
            {
                "schema": gate.AUTHORITY_CONTRACTS["compatibility_surfaces"][1],
                "goal_id": gate.GOAL_ID,
                "repository_id": gate.REPOSITORY_ID,
                "surfaces": compatibility_surfaces,
            },
        )

        translation_relation = named_ref(
            text_artifact("machine-translation-relation.def", "Trust-IR to machine refinement\n"),
            "fixture.codegen.translation-relation",
        )
        self.codegen_cells = [
            {
                "id": "fixture.cell.release",
                "target_id": "fixture.target",
                "abi_id": "fixture-abi-release",
                "crate_type": "bin",
                "runtime_id": "fixture-runtime-release",
                "startup_id": "fixture-startup-release",
                "linker_id": "fixture-linker-release",
                "unwind_mode": "abort",
                "debug_mode": "none",
                "opt_level": "3",
                "profile_id": "release",
            },
            {
                "id": "fixture.cell.debug",
                "target_id": "fixture.target",
                "abi_id": "fixture-abi-debug",
                "crate_type": "staticlib",
                "runtime_id": "fixture-runtime-debug",
                "startup_id": "fixture-startup-debug",
                "linker_id": "fixture-linker-debug",
                "unwind_mode": "unwind",
                "debug_mode": "full",
                "opt_level": "0",
                "profile_id": "dev",
            },
        ]
        self.codegen_contract = self.evidence_dir / "codegen-contract.json"
        write_json(
            self.codegen_contract,
            {
                "schema": gate.AUTHORITY_CONTRACTS["codegen_surface"][1],
                "goal_id": gate.GOAL_ID,
                "repository_id": gate.REPOSITORY_ID,
                "translation_relation": translation_relation,
                "targets": [
                    {
                        "id": "fixture.target",
                        "triple": "fixture-unknown-none",
                        "abis": ["fixture-abi-release", "fixture-abi-debug"],
                        "crate_types": ["bin", "staticlib"],
                        "runtimes": ["fixture-runtime-release", "fixture-runtime-debug"],
                        "startups": ["fixture-startup-release", "fixture-startup-debug"],
                        "linkers": ["fixture-linker-release", "fixture-linker-debug"],
                        "unwind_modes": ["abort", "unwind"],
                        "debug_modes": ["none", "full"],
                        "opt_levels": ["3", "0"],
                        "profiles": ["release", "dev"],
                    }
                ],
                "matrix_cells": self.codegen_cells,
            },
        )

        source_artifact_digest = sha256(self.root / "source.txt")
        component_roster = [
            {
                "role": role,
                "name": f"fixture-{role.replace('_', '-')}",
                "version": "1.0",
                "artifact_sha256": source_artifact_digest,
            }
            for role in sorted(gate.TOOLCHAIN_ROLES)
        ]
        acceptance_contract = self.evidence_dir / "acceptance-environment-contract.json"
        write_json(
            acceptance_contract,
            {
                "schema": gate.AUTHORITY_CONTRACTS["acceptance_environment"][1],
                "goal_id": gate.GOAL_ID,
                "repository_id": gate.REPOSITORY_ID,
                "component_roster": component_roster,
                "run_modes": sorted(gate.ACCEPTANCE_RUN_MODES),
            },
        )

        admission_entries = {
            "rust": [
                {
                    "id": "rust:fixture",
                    "kind": "run-pass",
                    "admitted": True,
                    "source": self.ref(self.root / "fixture.rs"),
                    "expected_outcome": "run-pass",
                }
            ],
            "lean": [
                {
                    "id": "lean:fixture",
                    "kind": "build-pass",
                    "admitted": True,
                    "source": self.ref(self.root / "Fixture.lean"),
                    "expected_outcome": "build-pass",
                }
            ],
            "mixed": [
                {
                    "id": "mixed:fixture",
                    "kind": "run-pass",
                    "admitted": True,
                    "source": self.ref(self.root / "mixed.fixture"),
                    "expected_outcome": "run-pass",
                }
            ],
        }
        admission_lanes = {}
        for lane, entries in admission_entries.items():
            feature_path = self.evidence_dir / f"{lane}-features.json"
            write_json(
                feature_path,
                {
                    "schema": "trust.two-language.language-feature-manifest/v1",
                    "lane": lane,
                    "features": [f"fixture-{lane}-surface"],
                },
            )
            suite_path = self.evidence_dir / f"{lane}-suite.json"
            write_json(
                suite_path,
                {
                    "schema": "trust.two-language.suite-manifest/v1",
                    "lane": lane,
                    "cases": [entry["id"] for entry in entries],
                },
            )
            ledger_path = self.evidence_dir / f"{lane}-exceptions.json"
            write_json(
                ledger_path,
                {
                    "schema": "trust.two-language.exception-ledger/v1",
                    "lane": lane,
                    "rows": [],
                },
            )
            admission_lanes[lane] = {
                "upstream_repository": f"https://example.invalid/{lane}",
                "upstream_revision": self.source_revision,
                "upstream_tree_sha256": hashlib.sha256(
                    f"{lane} fixture tree".encode()
                ).hexdigest(),
                "feature_manifest": self.ref(feature_path),
                "suite_manifest": self.ref(suite_path),
                "exception_ledger": self.ref(ledger_path),
                "entries": entries,
            }
        admission_contract = self.evidence_dir / "admission-contract.json"
        write_json(
            admission_contract,
            {
                "schema": gate.AUTHORITY_CONTRACTS["admission"][1],
                "goal_id": gate.GOAL_ID,
                "repository_id": gate.REPOSITORY_ID,
                "lanes": admission_lanes,
            },
        )
        self.contract_refs = {
            "admission": named_ref(
                admission_contract,
                gate.AUTHORITY_CONTRACTS["admission"][0],
            ),
            "semantics": named_ref(
                semantics_contract,
                gate.AUTHORITY_CONTRACTS["semantics"][0],
            ),
            "obligations": named_ref(
                obligations_contract,
                gate.AUTHORITY_CONTRACTS["obligations"][0],
            ),
            "proof_authority": named_ref(
                proof_contract,
                gate.AUTHORITY_CONTRACTS["proof_authority"][0],
            ),
            "compatibility_surfaces": named_ref(
                self.compatibility_contract,
                gate.AUTHORITY_CONTRACTS["compatibility_surfaces"][0],
            ),
            "codegen_surface": named_ref(
                self.codegen_contract,
                gate.AUTHORITY_CONTRACTS["codegen_surface"][0],
            ),
            "acceptance_environment": named_ref(
                acceptance_contract,
                gate.AUTHORITY_CONTRACTS["acceptance_environment"][0],
            ),
        }
        self.toolchain = self.evidence_dir / "toolchain.json"
        write_json(
            self.toolchain,
            {
                "schema": gate.TOOLCHAIN_SCHEMA,
                "goal_id": gate.GOAL_ID,
                "acceptance_run_id": self.acceptance_run_id,
                "source_revision": self.source_revision,
                "components": [
                    {
                        "role": component["role"],
                        "name": component["name"],
                        "version": component["version"],
                        "artifact": self.ref(self.root / "source.txt"),
                    }
                    for component in component_roster
                ],
            },
        )
        self.corpus = self.evidence_dir / "corpus.manifest"
        write_json(
            self.corpus,
            {
                "schema": gate.CORPUS_SCHEMA,
                "goal_id": gate.GOAL_ID,
                "acceptance_run_id": self.acceptance_run_id,
                "source_revision": self.source_revision,
                "repository_id": gate.REPOSITORY_ID,
                "rust": {
                    "upstream_revision": self.source_revision,
                    "admission_policy_sha256": sha256(admission_contract),
                    "entries": admission_entries["rust"],
                },
                "lean": {
                    "upstream_revision": self.source_revision,
                    "admission_policy_sha256": sha256(admission_contract),
                    "entries": admission_entries["lean"],
                },
                "mixed": {
                    "upstream_revision": self.source_revision,
                    "admission_policy_sha256": sha256(admission_contract),
                    "entries": admission_entries["mixed"],
                },
            },
        )
        self.subject_graph = self.evidence_dir / "subject-graph.json"
        refinement_rust = self.evidence_dir / "refinement-rust.cert"
        refinement_rust.write_text("universal Rust refinement\n", encoding="utf-8")
        refinement_lean = self.evidence_dir / "refinement-lean.cert"
        refinement_lean.write_text("universal Lean refinement\n", encoding="utf-8")
        proof_rust = self.evidence_dir / "proof-rust.cert"
        proof_rust.write_text("kernel proof Rust\n", encoding="utf-8")
        proof_lean = self.evidence_dir / "proof-lean.cert"
        proof_lean.write_text("kernel proof Lean\n", encoding="utf-8")
        contextual = text_artifact("contextual-refinement.cert", "whole-program refinement\n")
        bridge = text_artifact("formula-proposition-bridge.cert", "formula to Lean term\n")
        codegen_artifacts: dict[str, dict[str, Path]] = {}
        for cell in self.codegen_cells:
            suffix = cell["id"].rsplit(".", 1)[-1]
            executable = (
                self.release_artifact
                if suffix == "release"
                else text_artifact(f"fixture-{suffix}.bin", f"fixture {suffix} executable\n")
            )
            codegen_artifacts[cell["id"]] = {
                "object": text_artifact(
                    f"fixture-{suffix}.o", f"fixture {suffix} object\n"
                ),
                "translation": text_artifact(
                    f"translation-{suffix}.cert",
                    f"{suffix} object translation proof\n",
                ),
                "executable": executable,
                "composition": text_artifact(
                    f"link-composition-{suffix}.cert",
                    f"{suffix} linked composition proof\n",
                ),
                "binary_semantics": text_artifact(
                    f"binary-semantics-{suffix}.cert",
                    f"{suffix} binary refinement proof\n",
                ),
            }
        closure_sha256 = "c" * 64
        rust_body = {
            "id": "rust-main",
            "language": "rust",
            "function_identity_sha256": "d" * 64,
            "source_language_semantics_id": semantics_refs["rust_language"]["id"],
            "source_language_semantics_sha256": semantics_refs["rust_language"]["sha256"],
            "source_semantics_sha256": "4" * 64,
            "trust_ir_semantics_id": semantics_refs["trust_ir"]["id"],
            "trust_ir_semantics_sha256": semantics_refs["trust_ir"]["sha256"],
            "trust_ir_sha256": "5" * 64,
            "ssa_epoch_sha256": "e" * 64,
            "effect_summary_sha256": "f" * 64,
        }
        lean_body = {
            "id": "lean-answer",
            "language": "lean",
            "function_identity_sha256": "a" * 64,
            "source_language_semantics_id": semantics_refs["lean_language"]["id"],
            "source_language_semantics_sha256": semantics_refs["lean_language"]["sha256"],
            "source_semantics_sha256": "6" * 64,
            "trust_ir_semantics_id": semantics_refs["trust_ir"]["id"],
            "trust_ir_semantics_sha256": semantics_refs["trust_ir"]["sha256"],
            "trust_ir_sha256": "7" * 64,
            "ssa_epoch_sha256": "1" * 64,
            "effect_summary_sha256": "2" * 64,
        }
        bodies = [rust_body, lean_body]
        value_categories = ["value", "aggregate", "reference", "error", "callback", "result"]
        call_edges = []
        for caller, callee in ((rust_body, lean_body), (lean_body, rust_body)):
            direction = f"{caller['language']}_to_{callee['language']}"
            for category in value_categories:
                call_edges.append(
                    {
                        "id": f"edge-{direction}-{category}",
                        "caller_body_id": caller["id"],
                        "callee_body_id": callee["id"],
                        "direction": direction,
                        "value_category": category,
                        "canonical_type_sha256": hashlib.sha256(
                            f"{direction}:{category}".encode()
                        ).hexdigest(),
                        "abi_id": semantics_refs["abi_memory_model"]["id"],
                        "abi_sha256": semantics_refs["abi_memory_model"]["sha256"],
                        "memory_model_id": semantics_refs["abi_memory_model"]["id"],
                        "memory_model_sha256": semantics_refs["abi_memory_model"]["sha256"],
                        "import_assumption_closure_sha256": closure_sha256,
                        "visibility": "call",
                    }
                )
        refinement_certificates = []
        for body in bodies:
            relation = semantics_refs[f"{body['language']}_to_trust_ir_refinement"]
            evidence = refinement_rust if body["language"] == "rust" else refinement_lean
            refinement_certificates.append(
                {
                    "body_id": body["id"],
                    "source_semantics_sha256": body["source_semantics_sha256"],
                    "trust_ir_sha256": body["trust_ir_sha256"],
                    "relation_id": relation["id"],
                    "relation_sha256": relation["sha256"],
                    "certificate_kind": "universal",
                    "finite_domain_sha256": None,
                    "exhaustiveness_evidence": None,
                    "all_elements_agreement_root_sha256": None,
                    "kernel_environment_id": "fixture.kernel.environment",
                    "kernel_environment_sha256": kernel_environment_sha256,
                    "evidence": self.ref(evidence),
                }
            )
        obligations = []
        proof_certificates = []
        formula_digits = "012345"
        proposition_digits = "9abcde"
        for index, rule in enumerate(obligation_rules):
            body = bodies[index % len(bodies)]
            obligation_id = f"obligation-{index}"
            proof_id = f"proof-{index}"
            obligation = {
                "id": obligation_id,
                "body_id": body["id"],
                "function_identity_sha256": body["function_identity_sha256"],
                "formula_sha256": formula_digits[index] * 64,
                "canonical_proposition_sha256": proposition_digits[index] * 64,
                "formula_encoder_id": formula_encoder["id"],
                "formula_encoder_sha256": formula_encoder["sha256"],
                "proposition_encoder_id": proposition_encoder["id"],
                "proposition_encoder_sha256": proposition_encoder["sha256"],
                "formula_to_proposition_evidence": self.ref(bridge),
                "policy_rule_id": rule["id"],
                "ssa_epoch_sha256": body["ssa_epoch_sha256"],
                "effect_summary_sha256": body["effect_summary_sha256"],
                "module_id": "linked-module",
            }
            obligations.append(obligation)
            proof_certificates.append(
                {
                    "id": proof_id,
                    "obligation_id": obligation_id,
                    "body_id": body["id"],
                    "function_identity_sha256": body["function_identity_sha256"],
                    "proposition_sha256": obligation["canonical_proposition_sha256"],
                    "ssa_epoch_sha256": body["ssa_epoch_sha256"],
                    "effect_summary_sha256": body["effect_summary_sha256"],
                    "module_id": "linked-module",
                    "kernel_environment_id": "fixture.kernel.environment",
                    "kernel_environment_sha256": kernel_environment_sha256,
                    "proof_grade": "kernel-checked",
                    "axiom_allowlist_root_sha256": axiom_root_sha256,
                    "evidence": self.ref(proof_rust if body["language"] == "rust" else proof_lean),
                }
            )
        objects = []
        translation_evidence_rows = []
        executables = []
        for cell in self.codegen_cells:
            suffix = cell["id"].rsplit(".", 1)[-1]
            configuration = {
                field: cell[field] for field in gate.CODEGEN_CELL_FIELDS
            }
            object_id = f"object-{suffix}"
            object_artifact = codegen_artifacts[cell["id"]]["object"]
            objects.append(
                {
                    "id": object_id,
                    "module_id": "linked-module",
                    "codegen_cell_id": cell["id"],
                    **configuration,
                    "artifact": self.ref(object_artifact),
                }
            )
            translation_evidence_rows.append(
                {
                    "id": f"translation-evidence-{suffix}",
                    "object_id": object_id,
                    "module_id": "linked-module",
                    "codegen_cell_id": cell["id"],
                    **configuration,
                    "translation_relation_id": translation_relation["id"],
                    "translation_relation_sha256": translation_relation["sha256"],
                    "module_sha256": sha256(self.linked_module),
                    "object_sha256": sha256(object_artifact),
                    "evidence": self.ref(codegen_artifacts[cell["id"]]["translation"]),
                }
            )
            executables.append(
                {
                    "id": f"executable-{suffix}",
                    "codegen_cell_id": cell["id"],
                    **configuration,
                    "object_ids": [object_id],
                    "artifact": self.ref(codegen_artifacts[cell["id"]]["executable"]),
                    "system_library_closure_sha256": "3" * 64,
                    "composition_evidence": self.ref(
                        codegen_artifacts[cell["id"]]["composition"]
                    ),
                    "binary_semantics_evidence": self.ref(
                        codegen_artifacts[cell["id"]]["binary_semantics"]
                    ),
                }
            )
        program = {
            "id": "mixed-program",
            "entrypoints": ["rust-main"],
            "admitted_file_ids": ["rust:fixture", "lean:fixture", "mixed:fixture"],
            "bodies": bodies,
            "call_edges": call_edges,
            "contextual_refinement": {
                "assumption_closure_sha256": closure_sha256,
                "evidence": self.ref(contextual),
            },
            "refinement_certificates": refinement_certificates,
            "obligations": obligations,
            "proof_certificates": proof_certificates,
            "modules": [
                {
                    "id": "linked-module",
                    "artifact": self.ref(self.linked_module),
                    "body_ids": ["rust-main", "lean-answer"],
                    "call_edge_ids": [edge["id"] for edge in call_edges],
                    "obligation_ids": [row["id"] for row in obligations],
                    "refinement_certificate_body_ids": ["rust-main", "lean-answer"],
                    "proof_certificate_ids": [row["id"] for row in proof_certificates],
                    "assumption_closure_sha256": closure_sha256,
                    "contextual_refinement_evidence": self.ref(contextual),
                }
            ],
            "objects": objects,
            "translation_evidence": translation_evidence_rows,
            "executables": executables,
        }
        root_rows = {
            "admitted_files": [
                {"program_id": program["id"], "file_id": file_id}
                for file_id in program["admitted_file_ids"]
            ],
            "reachable_bodies": [
                {"program_id": program["id"], **row} for row in program["bodies"]
            ],
            **{
                field: [
                    {"program_id": program["id"], **row} for row in program[field]
                ]
                for field in (
                    "call_edges",
                    "refinement_certificates",
                    "obligations",
                    "proof_certificates",
                    "modules",
                    "objects",
                    "translation_evidence",
                    "executables",
                )
            },
            "codegen_matrix_cells": [
                {"program_id": program["id"], **cell}
                for cell in self.codegen_cells
            ],
        }
        roots = {
            name: gate._canonical_json_sha256(
                sorted(
                    rows,
                    key=lambda row: json.dumps(
                        row,
                        sort_keys=True,
                        separators=(",", ":"),
                    ),
                )
            )
            for name, rows in root_rows.items()
        }
        write_json(
            self.subject_graph,
            {
                "schema": gate.SUBJECT_GRAPH_SCHEMA,
                "goal_id": gate.GOAL_ID,
                "acceptance_run_id": self.acceptance_run_id,
                "source_revision": self.source_revision,
                "programs": [program],
                "roots": roots,
                "release_executable": {
                    "program_id": "mixed-program",
                    "executable_id": "executable-release",
                },
            },
        )
        self.policy = self.evidence_dir / "authority-policy.json"
        self.owner_private = base / "fixture-owner"
        subprocess.run(
            [
                str(gate.SSH_KEYGEN),
                "-q",
                "-t",
                "ed25519",
                "-N",
                "",
                "-f",
                str(self.owner_private),
            ],
            check=True,
        )
        self.owner_public = Path(f"{self.owner_private}.pub")
        fingerprint = subprocess.run(
            [str(gate.SSH_KEYGEN), "-lf", str(self.owner_public), "-E", "sha256"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.split()[1]
        write_json(
            self.policy,
            {
                "schema": gate.POLICY_SCHEMA,
                "goal_id": gate.GOAL_ID,
                "repository_id": gate.REPOSITORY_ID,
                "completion_schema": gate.SCHEMA,
                "authorized_source_revision": self.source_revision,
                "authorized_acceptance_run_id": self.acceptance_run_id,
                "owner_key_fingerprint": fingerprint,
                "authorized_inputs": {
                    "toolchain_manifest_sha256": sha256(self.toolchain),
                    "corpus_manifest_sha256": sha256(self.corpus),
                    "subject_graph_sha256": sha256(self.subject_graph),
                    "linked_module_sha256": sha256(self.linked_module),
                    "release_artifact_sha256": sha256(self.release_artifact),
                },
                "contracts": self.contract_refs,
                "authorized_checkers": {
                    gate_id: {
                        "id": gate.CHECKER_IDS[gate_id],
                        "path": gate.CHECKER_PATHS[gate_id],
                        "sha256": sha256(self.root / gate.CHECKER_PATHS[gate_id]),
                    }
                    for gate_id in gate.GATES
                },
            },
        )
        subprocess.run(
            [
                str(gate.SSH_KEYGEN),
                "-Y",
                "sign",
                "-f",
                str(self.owner_private),
                "-n",
                gate.POLICY_SIGNATURE_NAMESPACE,
                str(self.policy),
            ],
            check=True,
            capture_output=True,
        )
        policy_signature = Path(f"{self.policy}.sig")
        self.policy_authorization = self.evidence_dir / "authority-policy-authorization.json"
        write_json(
            self.policy_authorization,
            {
                "schema": gate.POLICY_AUTH_SCHEMA,
                "algorithm": "ssh-ed25519",
                "namespace": gate.POLICY_SIGNATURE_NAMESPACE,
                "signer_fingerprint": fingerprint,
                "policy_sha256": sha256(self.policy),
                "signature": self.ref(policy_signature),
            },
        )

        self.receipt: dict = {
            "schema": gate.SCHEMA,
            "goal_id": gate.GOAL_ID,
            "repository_id": gate.REPOSITORY_ID,
            "acceptance_run_id": self.acceptance_run_id,
            "source_revision": self.source_revision,
            "toolchain_manifest": self.ref(self.toolchain),
            "corpus_manifest": self.ref(self.corpus),
            "subject_graph": self.ref(self.subject_graph),
            "linked_module": self.ref(self.linked_module),
            "release_artifact": self.ref(self.release_artifact),
            "authority_policy": self.ref(self.policy),
            "policy_authorization": self.ref(self.policy_authorization),
            "gates": {},
        }
        for gate_id in gate.GATES:
            artifacts = {}
            for check_id in gate.REQUIRED_CHECKS[gate_id]:
                artifact = self.evidence_dir / f"{gate_id}-{check_id}.json"
                write_json(artifact, {"gate": gate_id, "check": check_id, "result": "pass"})
                artifacts[check_id] = self.ref(artifact)
            evidence_path = self.evidence_dir / f"{gate_id}.json"
            write_json(
                evidence_path,
                {
                    "schema": "fixture.gate-input/v1",
                    "gate": gate_id,
                    "checker": gate.CHECKER_IDS[gate_id],
                    "artifacts": artifacts,
                },
            )
            checker_path = self.root / gate.CHECKER_PATHS[gate_id]
            self.receipt["gates"][gate_id] = {
                "checker": gate.CHECKER_IDS[gate_id],
                "checker_sha256": sha256(checker_path),
                "evidence": self.ref(evidence_path),
            }
        self.path = self.evidence_dir / "receipt.json"
        self.write_receipt()

    def ref(self, path: Path) -> dict[str, str]:
        return {"path": path.relative_to(self.root).as_posix(), "sha256": sha256(path)}

    def write_receipt(self) -> None:
        write_json(self.path, self.receipt)

    def evidence_path(self, gate_id: str) -> Path:
        return self.root / self.receipt["gates"][gate_id]["evidence"]["path"]

    def rewrite_evidence(self, gate_id: str, evidence: dict) -> None:
        path = self.evidence_path(gate_id)
        write_json(path, evidence)
        self.receipt["gates"][gate_id]["evidence"] = self.ref(path)
        self.write_receipt()


class CompletionReceiptTests(unittest.TestCase):
    def make_fixture(self) -> GreenReceipt:
        temporary = tempfile.TemporaryDirectory(prefix="two-language-gate-")
        self.addCleanup(temporary.cleanup)
        return GreenReceipt(Path(temporary.name))

    def test_exact_checker_backed_receipt_is_structurally_complete(self) -> None:
        fixture = self.make_fixture()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertTrue(verdict["accepted"], verdict["errors"])
        self.assertEqual(verdict["result"], "checker-verified-structurally-complete")
        self.assertEqual(set(verdict["gate_results"]), set(gate.GATES))
        self.assertTrue(all(verdict["gate_results"].values()))
        self.assertIn("does_not_establish", verdict)

    def test_missing_gate_and_author_completion_bit_fail_closed(self) -> None:
        fixture = self.make_fixture()
        del fixture.receipt["gates"]["G8"]
        fixture.receipt["vision_complete"] = True
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(any("unknown keys" in error for error in verdict["errors"]))
        self.assertTrue(any("missing gates" in error for error in verdict["errors"]))

    def test_required_check_cannot_be_false(self) -> None:
        fixture = self.make_fixture()
        evidence = json.loads(fixture.evidence_path("G6").read_text(encoding="utf-8"))
        first = gate.REQUIRED_CHECKS["G6"][0]
        artifact = fixture.root / evidence["artifacts"][first]["path"]
        write_json(artifact, {"gate": "G6", "check": first, "result": "fail"})
        fixture.rewrite_evidence("G6", evidence)
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertFalse(verdict["gate_results"]["G6"])
        self.assertTrue(any("checker exited" in error for error in verdict["errors"]))
        self.assertTrue(any("boolean true" in error for error in verdict["errors"]))

    def test_mutated_underlying_artifact_breaks_fresh_checker_run(self) -> None:
        fixture = self.make_fixture()
        evidence = json.loads(fixture.evidence_path("G4").read_text(encoding="utf-8"))
        artifact = fixture.root / next(iter(evidence["artifacts"].values()))["path"]
        artifact.write_text("mutated after receipt\n", encoding="utf-8")
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertFalse(verdict["gate_results"]["G4"])
        self.assertTrue(any("checker exited" in error for error in verdict["errors"]))

    def test_missing_schema_owned_checker_is_rejected(self) -> None:
        fixture = self.make_fixture()
        checker = fixture.root / gate.CHECKER_PATHS["G2"]
        checker.unlink()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(any("checker is not implemented" in error for error in verdict["errors"]))

    def test_candidate_cannot_supply_its_own_policy_trust_root(self) -> None:
        fixture = self.make_fixture()
        verdict = gate.validate_receipt(fixture.path, fixture.root)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any("--trusted-owner-key is required" in error for error in verdict["errors"]),
            verdict,
        )
        self.assertTrue(all(not passed for passed in verdict["gate_results"].values()))

    def test_subject_index_requires_body_refinement_module_object_bijections(self) -> None:
        fixture = self.make_fixture()
        subject = json.loads(fixture.subject_graph.read_text(encoding="utf-8"))
        subject["programs"][0]["refinement_certificates"].pop()
        write_json(fixture.subject_graph, subject)
        fixture.receipt["subject_graph"] = fixture.ref(fixture.subject_graph)
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any(
                "exactly one universal refinement certificate per body" in error
                for error in verdict["errors"]
            ),
            verdict,
        )
        self.assertTrue(any("canonical root mismatch" in error for error in verdict["errors"]))

    def test_proof_must_bind_canonical_proposition_not_formula_bytes(self) -> None:
        fixture = self.make_fixture()
        subject = json.loads(fixture.subject_graph.read_text(encoding="utf-8"))
        obligation = subject["programs"][0]["obligations"][0]
        certificate = subject["programs"][0]["proof_certificates"][0]
        certificate["proposition_sha256"] = obligation["formula_sha256"]
        write_json(fixture.subject_graph, subject)
        fixture.receipt["subject_graph"] = fixture.ref(fixture.subject_graph)
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any("exact canonical Lean proposition digest" in error for error in verdict["errors"]),
            verdict,
        )

    def test_malformed_object_module_identity_fails_without_crashing(self) -> None:
        fixture = self.make_fixture()
        subject = json.loads(fixture.subject_graph.read_text(encoding="utf-8"))
        subject["programs"][0]["objects"][0]["module_id"] = []
        write_json(fixture.subject_graph, subject)
        fixture.receipt["subject_graph"] = fixture.ref(fixture.subject_graph)
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(any("must name an admitted module" in error for error in verdict["errors"]))

    def test_codegen_matrix_requires_every_module_cell_object(self) -> None:
        fixture = self.make_fixture()
        subject = json.loads(fixture.subject_graph.read_text(encoding="utf-8"))
        subject["programs"][0]["objects"].pop()
        write_json(fixture.subject_graph, subject)
        fixture.receipt["subject_graph"] = fixture.ref(fixture.subject_graph)
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any(
                "every admitted module/codegen-cell pair" in error
                for error in verdict["errors"]
            ),
            verdict,
        )

    def test_codegen_matrix_rejects_cross_mixed_object_configuration(self) -> None:
        fixture = self.make_fixture()
        subject = json.loads(fixture.subject_graph.read_text(encoding="utf-8"))
        objects = subject["programs"][0]["objects"]
        self.assertNotEqual(objects[0]["debug_mode"], objects[1]["debug_mode"])
        objects[0]["debug_mode"] = objects[1]["debug_mode"]
        write_json(fixture.subject_graph, subject)
        fixture.receipt["subject_graph"] = fixture.ref(fixture.subject_graph)
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any(
                "objects[0].debug_mode" in error
                and "owner-signed codegen cell value" in error
                for error in verdict["errors"]
            ),
            verdict,
        )

    def test_cross_language_matrix_requires_each_category_in_both_directions(self) -> None:
        fixture = self.make_fixture()
        subject = json.loads(fixture.subject_graph.read_text(encoding="utf-8"))
        edges = subject["programs"][0]["call_edges"]
        edges[:] = [
            edge
            for edge in edges
            if not (
                edge["direction"] == "lean_to_rust"
                and edge["value_category"] == "callback"
            )
        ]
        write_json(fixture.subject_graph, subject)
        fixture.receipt["subject_graph"] = fixture.ref(fixture.subject_graph)
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any("every direction/value-category pair" in error for error in verdict["errors"]),
            verdict,
        )

    def test_kani_proposition_only_translation_cannot_satisfy_compatibility_contract(self) -> None:
        fixture = self.make_fixture()
        contract = json.loads(
            fixture.compatibility_contract.read_text(encoding="utf-8")
        )
        contract["surfaces"]["kani"]["computational_image"] = None
        write_json(fixture.compatibility_contract, contract)
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any(
                "surfaces.kani.computational_image" in error
                for error in verdict["errors"]
            ),
            verdict,
        )

    def test_candidate_cannot_remove_the_admitted_lean_population(self) -> None:
        fixture = self.make_fixture()
        corpus = json.loads(fixture.corpus.read_text(encoding="utf-8"))
        corpus["lean"]["entries"][0]["admitted"] = False
        write_json(fixture.corpus, corpus)
        fixture.receipt["corpus_manifest"] = fixture.ref(fixture.corpus)
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any("must contain at least one admitted program" in error for error in verdict["errors"]),
            verdict,
        )
        self.assertTrue(
            any("owner-signed admission population" in error for error in verdict["errors"]),
            verdict,
        )

    def test_finite_refinement_requires_domain_and_exhaustiveness_evidence(self) -> None:
        fixture = self.make_fixture()
        subject = json.loads(fixture.subject_graph.read_text(encoding="utf-8"))
        subject["programs"][0]["refinement_certificates"][0][
            "certificate_kind"
        ] = "finite-exhaustive"
        write_json(fixture.subject_graph, subject)
        fixture.receipt["subject_graph"] = fixture.ref(fixture.subject_graph)
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any("finite_domain_sha256" in error for error in verdict["errors"]),
            verdict,
        )
        self.assertTrue(
            any("exhaustiveness_evidence" in error for error in verdict["errors"]),
            verdict,
        )

    def test_path_escape_is_rejected(self) -> None:
        fixture = self.make_fixture()
        fixture.receipt["gates"]["G2"]["evidence"]["path"] = "../outside.json"
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(any("escapes --root" in error for error in verdict["errors"]))

    def test_source_revision_and_clean_worktree_are_enforced(self) -> None:
        fixture = self.make_fixture()
        fixture.receipt["source_revision"] = "0" * 40
        fixture.write_receipt()
        (fixture.root / "dirty.txt").write_text("not committed\n", encoding="utf-8")
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(any("does not match --root HEAD" in error for error in verdict["errors"]))
        self.assertTrue(any("worktree is not clean" in error for error in verdict["errors"]))

    def test_cli_exit_codes_follow_computed_verdict(self) -> None:
        fixture = self.make_fixture()
        passed = subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--receipt",
                fixture.path.relative_to(fixture.root).as_posix(),
                "--root",
                str(fixture.root),
                "--candidate-verifier",
                fixture.candidate_top.relative_to(fixture.root).as_posix(),
                "--trusted-owner-key",
                str(fixture.owner_public),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(passed.returncode, 0, passed.stderr)
        self.assertTrue(json.loads(passed.stdout)["accepted"])

        fixture.receipt["gates"]["G1"]["checker"] = "trust.two-language.fake/v1"
        fixture.write_receipt()
        failed = subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--receipt",
                str(fixture.path),
                "--root",
                str(fixture.root),
                "--trusted-owner-key",
                str(fixture.owner_public),
                "--text",
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(failed.returncode, 1, failed.stderr)
        self.assertIn("INCOMPLETE", failed.stdout)

    def test_external_verifier_rejects_mutated_candidate_top_gate(self) -> None:
        fixture = self.make_fixture()
        fixture.candidate_top.write_text(
            "#!/usr/bin/env python3\nraise SystemExit(0)\n",
            encoding="utf-8",
        )
        process = subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--candidate-verifier",
                fixture.candidate_top.relative_to(fixture.root).as_posix(),
                "--receipt",
                fixture.path.relative_to(fixture.root).as_posix(),
                "--root",
                str(fixture.root),
                "--trusted-owner-key",
                str(fixture.owner_public),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(process.returncode, 2, process)
        self.assertIn("do not equal the externally pinned verifier", process.stderr)

    def test_candidate_tree_verifier_cannot_verify_itself(self) -> None:
        fixture = self.make_fixture()
        process = subprocess.run(
            [
                sys.executable,
                str(fixture.candidate_top),
                "--candidate-verifier",
                fixture.candidate_top.relative_to(fixture.root).as_posix(),
                "--receipt",
                fixture.path.relative_to(fixture.root).as_posix(),
                "--root",
                str(fixture.root),
                "--trusted-owner-key",
                str(fixture.owner_public),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(process.returncode, 2, process)
        self.assertIn("running verifier must be outside --root", process.stderr)

    def test_verifier_symlink_paths_are_rejected(self) -> None:
        fixture = self.make_fixture()
        candidate_link = fixture.candidate_top.with_name("candidate-link.py")
        candidate_link.symlink_to(fixture.candidate_top)
        candidate_process = subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--candidate-verifier",
                candidate_link.relative_to(fixture.root).as_posix(),
                "--receipt",
                fixture.path.relative_to(fixture.root).as_posix(),
                "--root",
                str(fixture.root),
                "--trusted-owner-key",
                str(fixture.owner_public),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(candidate_process.returncode, 2, candidate_process)
        self.assertIn("--candidate-verifier must not be a symlink", candidate_process.stderr)

        running_link = fixture.root.parent / "external-verifier-link.py"
        running_link.symlink_to(SCRIPT)
        running_process = subprocess.run(
            [
                sys.executable,
                str(running_link),
                "--candidate-verifier",
                fixture.candidate_top.relative_to(fixture.root).as_posix(),
                "--receipt",
                fixture.path.relative_to(fixture.root).as_posix(),
                "--root",
                str(fixture.root),
                "--trusted-owner-key",
                str(fixture.owner_public),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(running_process.returncode, 2, running_process)
        self.assertIn("running verifier must not be a symlink", running_process.stderr)


if __name__ == "__main__":
    unittest.main()
