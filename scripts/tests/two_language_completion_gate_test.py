#!/usr/bin/env python3
"""Self-executing adversarial controls for the two-language completion receipt."""

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import os
import py_compile
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from types import SimpleNamespace
from typing import Callable
from unittest.mock import patch


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
G8_CHECKER = REPO_ROOT / gate.CHECKER_PATHS["G8"]


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
if GATE == "G8":
    ap.add_argument("--trusted-owner-key")
    ap.add_argument("--external-verifier")
    ap.add_argument("--external-verifier-sha256")
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
    """A clean Git root with tracked checkers and ignored generated evidence.

    ``before_commit`` may add tracked content (files, submodules) to the root
    before the single fixture commit that the receipt and policy then bind.
    """

    def __init__(
        self,
        base: Path,
        *,
        g8_checker_bytes: bytes | None = None,
        before_commit: Callable[[Path], None] | None = None,
    ):
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
            if gate_id == "G8" and g8_checker_bytes is not None:
                checker.write_bytes(g8_checker_bytes)
            else:
                checker.write_text(checker_source(gate_id), encoding="utf-8")
        if before_commit is not None:
            before_commit(self.root)
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
        policy_signature = self.sign_file(self.policy, gate.POLICY_SIGNATURE_NAMESPACE)
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
                    "schema": (
                        "trust.two-language.gate-evidence/v1"
                        if gate_id == "G8" and g8_checker_bytes is not None
                        else "fixture.gate-input/v1"
                    ),
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

    def sign_file(self, source: Path, namespace: str) -> Path:
        subprocess.run(
            [str(gate.SSH_KEYGEN), "-Y", "sign", "-f", str(self.owner_private),
             "-n", namespace, str(source)],
            check=True,
            capture_output=True,
        )
        return Path(f"{source}.sig")

    def sign_detached_seal(self, prior_gates_root: str) -> None:
        payload = {
            "schema": "trust.two-language.detached-release-seal/v1",
            "prior_gates_root": prior_gates_root,
            "release_artifact_sha256": sha256(self.release_artifact),
        }
        message_path = self.evidence_dir / "g8-seal-message.json"
        message_path.write_bytes(
            json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
        )
        signature = self.sign_file(message_path, "trust-two-language-g8-release")
        seal = self.evidence_dir / "g8-detached-seal.json"
        write_json(seal, {**payload, "signature": self.ref(signature)})
        evidence = json.loads(self.evidence_path("G8").read_text(encoding="utf-8"))
        evidence["artifacts"]["detached_release_seal_binds_prior_root_and_artifact"] = self.ref(seal)
        self.rewrite_evidence("G8", evidence)

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


# The same length, so a rewrite keeps the size cached in the index and Git
# re-checks its content only when the rest of the stat data says to.
PINNED_TEXT = "pinned upstream source\n"
FORGED_TEXT = "forged upstream source\n"
assert len(PINNED_TEXT) == len(FORGED_TEXT)
ENGINE = "first-party/engine"


# The index and pack layouts the helpers below rewrite by hand, whatever the
# operator's global configuration (feature.manyFiles, core.splitIndex, ...)
# would otherwise choose.
PLAIN_VERSION_2_INDEX = (
    "-c", "index.version=2", "-c", "core.splitIndex=false", "-c", "index.skipHash=false",
)
VERSION_2_PACK = ("-c", "pack.indexVersion=2")


def git(root: Path, *args: str) -> str:
    """The test's own Git, run as an attacker or operator would run it."""
    return subprocess.run(
        ["git", "-C", str(root), *args], check=True, capture_output=True, text=True
    ).stdout


def plain_status(root: Path) -> str:
    """Exactly the status the gate used to accept as the clean-tree predicate."""
    return git(root, "status", "--porcelain", "--untracked-files=all")


def git_version() -> tuple[int, int]:
    """The major and minor version of the Git on PATH."""
    words = subprocess.run(
        ["git", "--version"], check=True, capture_output=True, text=True
    ).stdout.split()
    major, minor = words[2].split(".")[:2]
    return int(major), int(minor)


def add_pinned_file(root: Path) -> None:
    """A tracked file no receipt reference binds, as first-party sources are."""
    (root / "pinned.txt").write_text(PINNED_TEXT, encoding="utf-8")


def serve_object_as(root: Path, pinned: str, forged: str) -> None:
    """Make the object store answer the id ``pinned`` with ``forged``'s content.

    Packs ``forged`` alone and rewrites the version-2 pack index so its one
    entry claims ``pinned``: Git searches packs before loose objects, and does
    not re-verify the index or re-hash that object when serving it.  The
    genuine loose object is deleted too, so the id has no other source.
    """
    pack_dir = root / ".git" / "objects" / "pack"
    name = subprocess.run(
        ["git", "-C", str(root), *VERSION_2_PACK, "pack-objects", str(pack_dir / "forged")],
        input=f"{forged}\n", check=True, capture_output=True, text=True,
    ).stdout.strip()
    index = pack_dir / f"forged-{name}.idx"
    data = bytearray(index.read_bytes())
    ids = 8 + 256 * 4  # after the magic, the version and the fan-out table
    assert data[:8] == b"\xfftOc\x00\x00\x00\x02"
    assert data[ids:ids + 20] == bytes.fromhex(forged)
    data[ids:ids + 20] = bytes.fromhex(pinned)
    for first_byte in range(256):
        struct.pack_into(">I", data, 8 + 4 * first_byte, int(first_byte >= data[ids]))
    index.chmod(0o644)
    index.write_bytes(bytes(data))
    loose = root / ".git" / "objects" / pinned[:2] / pinned[2:]
    loose.chmod(0o644)
    loose.unlink()


def add_engine_submodule(root: Path, path: str = ENGINE) -> tuple[str, str]:
    """Pin ``path`` (``first-party/engine``) to the first of two upstream commits."""
    upstream = root.parent / "engine-upstream"
    subprocess.run(["git", "init", "-q", str(upstream)], check=True)
    git(upstream, "config", "user.email", "engine@test.invalid")
    git(upstream, "config", "user.name", "engine-test")
    (upstream / "engine.txt").write_text("engine v1\n", encoding="utf-8")
    git(upstream, "add", "engine.txt")
    git(upstream, "commit", "-q", "-m", "engine v1")
    pinned = git(upstream, "rev-parse", "HEAD").strip()
    (upstream / "engine.txt").write_text("engine v2\n", encoding="utf-8")
    git(upstream, "commit", "-q", "-am", "engine v2")
    later = git(upstream, "rev-parse", "HEAD").strip()
    git(root, "-c", "protocol.file.allow=always", "submodule", "add", "-q", str(upstream), path)
    git(root / path, "checkout", "-q", pinned)
    git(root, "add", path)
    return pinned, later


# The submodule G2 binds its Lean inputs to, and runs `git status` in.
CLEAN = "first-party/clean"
# Every hook githooks(5) documents.
GIT_HOOKS = (
    "applypatch-msg", "pre-applypatch", "post-applypatch", "pre-commit", "pre-merge-commit",
    "prepare-commit-msg", "commit-msg", "post-commit", "pre-rebase", "post-checkout",
    "post-merge", "pre-push", "pre-receive", "update", "proc-receive", "post-receive",
    "post-update", "reference-transaction", "push-to-checkout", "pre-auto-gc", "post-rewrite",
    "sendemail-validate", "fsmonitor-watchman", "p4-changelist", "p4-prepare-changelist",
    "p4-post-changelist", "p4-pre-submit", "post-index-change",
)
# What the real checkers run, reproduced inside fixture checkers: G2 reads the
# clean submodule's state with `git status`, and G1 reads a tracked file's blob.
G2_CLEAN_STATUS = (
    "import os, subprocess\n"
    "subprocess.run(\n"
    "    ['git', '--no-optional-locks', 'status', '--porcelain', '--untracked-files=all'],\n"
    "    cwd=str(root / 'first-party' / 'clean'), capture_output=True,\n"
    "    env={k: v for k, v in os.environ.items() if not k.startswith('GIT_')},\n"
    ")\n"
)
G1_TRACKED_READ = (
    "import os, subprocess\n"
    "subprocess.run(\n"
    "    ['git', '--no-replace-objects', '--no-optional-locks', 'show',\n"
    "     args.source_revision + ':pinned.txt'],\n"
    "    cwd=str(root), capture_output=True,\n"
    "    env={k: v for k, v in os.environ.items() if not k.startswith('GIT_')},\n"
    ")\n"
)


def inject_into_checker(root: Path, gate_id: str, code: str) -> None:
    """Make the fixture checker for ``gate_id`` run ``code`` before its verdict."""
    anchor = "verdict = {\n"
    source = checker_source(gate_id)
    assert source.count(anchor) == 1
    (root / gate.CHECKER_PATHS[gate_id]).write_text(
        source.replace(anchor, code + anchor), encoding="utf-8"
    )


def recording_program(path: Path, ran: Path) -> Path:
    """An executable at ``path`` that appends its command line to ``ran`` and fails."""
    path.write_text(f"#!/bin/sh\necho \"$0 $*\" >> '{ran}'\nexit 1\n", encoding="utf-8")
    path.chmod(0o755)
    return path


def arm_promisor(
    repository: Path,
    scratch: Path,
    ran: Path,
    naming: tuple[str, str] = ("remote.cache.promisor", "true"),
) -> None:
    """Name a promisor remote ``cache`` whose transport records that it ran.

    ``naming`` is the setting that makes ``cache`` a promisor remote.  A lazy
    fetch runs `git fetch cache`, and for a local remote Git starts the
    program its uploadpack setting names.
    """
    served = scratch / f"{repository.name}-promisor.git"
    subprocess.run(["git", "init", "-q", "--bare", str(served)], check=True)
    program = recording_program(scratch / f"{repository.name}-uploadpack", ran)
    git(repository, "config", "remote.cache.url", str(served))
    git(repository, "config", *naming)
    git(repository, "config", "remote.cache.uploadpack", str(program))


def arm_unnamed_promisor(
    repository: Path, scratch: Path, ran: Path, naming: tuple[str, str]
) -> None:
    """Name the promisor remote "" with a remote.* key that has no subsection.

    A lazy fetch then runs `git fetch ""`.  No remote has that name, so Git
    uses the name as the URL, and a url.<base>.insteadOf of "" rewrites it to
    <base>: here an ext:: command that records that it ran.
    """
    program = recording_program(scratch / f"{repository.name}-ext-transport", ran)
    git(repository, "config", *naming)
    git(repository, "config", f"url.ext::sh -c {program}% ext.insteadOf", "")
    git(repository, "config", "protocol.ext.allow", "always")


def drop_object(repository: Path, oid: str) -> None:
    """Remove ``oid`` from ``repository``'s object store, unpacking packs first."""
    objects = Path(
        git(repository, "rev-parse", "--path-format=absolute", "--git-path", "objects").strip()
    )
    for pack in list((objects / "pack").glob("*.pack")):
        data = pack.read_bytes()
        for part in (objects / "pack").glob(f"{pack.stem}.*"):
            part.unlink()
        subprocess.run(
            ["git", "-C", str(repository), "unpack-objects", "-q"], input=data, check=True
        )
    (objects / oid[:2] / oid[2:]).unlink()


REAL_GIT_ENV = gate._git_env


def git_without_lazy_fetch_guard() -> dict[str, str]:
    """The gate's Git environment as a Git that ignores GIT_NO_LAZY_FETCH sees it.

    Releases 2.41 to 2.44 older than the May 2024 security fixes (2.41.1,
    2.42.2, 2.43.4, 2.44.1) ignore the variable; dropping it shows what the
    gate's own Git then does.
    """
    return {
        key: value for key, value in REAL_GIT_ENV().items() if key != "GIT_NO_LAZY_FETCH"
    }


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
        py_compile.compile(
            str(forged), cfile=str(cache), dfile=str(module), doraise=True,
            invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH,
        )
    return cache


def bytecode_in(root: Path) -> set[Path]:
    """Every bytecode file and __pycache__ directory under ``root``."""
    return {
        path for path in root.rglob("*") if path.suffix == ".pyc" or path.name == "__pycache__"
    }


def load_real_checker(gate_id: str):
    """The schema-owned checker module for ``gate_id`` in this tree."""
    path = REPO_ROOT / gate.CHECKER_PATHS[gate_id]
    spec = importlib.util.spec_from_file_location(f"real_checker_{gate_id.lower()}", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def hash_object(root: Path, text: str) -> str:
    """Write ``text`` as a loose blob and return its id."""
    return subprocess.run(
        ["git", "-C", str(root), "hash-object", "-w", "--stdin"],
        input=text, check=True, capture_output=True, text=True,
    ).stdout.strip()


def pack_objects(
    root: Path, name: str, oids: list[str], alias: tuple[str, str] | None = None
) -> Path:
    """Pack ``oids`` (without deltas) and return the pack's path minus its suffix.

    With ``alias=(forged, pinned)`` the version-2 pack index then claims the
    packed object ``forged`` is ``pinned``: its entries are re-sorted and the
    fan-out table rebuilt, and the reverse index that ordered them is dropped.
    """
    pack_dir = root / ".git" / "objects" / "pack"
    digest = subprocess.run(
        [
            "git", "-C", str(root), *VERSION_2_PACK, "pack-objects", "--window=0",
            str(pack_dir / name),
        ],
        input="".join(f"{oid}\n" for oid in oids), check=True, capture_output=True, text=True,
    ).stdout.strip()
    pack = pack_dir / f"{name}-{digest}"
    if alias is None:
        return pack
    forged, pinned = (bytes.fromhex(oid) for oid in alias)
    index = pack.with_suffix(".idx")
    data = bytearray(index.read_bytes())
    assert data[:8] == b"\xfftOc\x00\x00\x00\x02"
    count = struct.unpack_from(">I", data, 8 + 255 * 4)[0]
    # After the fan-out table: every id, then every CRC32, then every offset.
    ids = 8 + 256 * 4
    crcs, offsets = ids + 20 * count, ids + 24 * count
    rows = sorted(
        (
            pinned if data[ids + 20 * i:ids + 20 * i + 20] == forged
            else bytes(data[ids + 20 * i:ids + 20 * i + 20]),
            bytes(data[crcs + 4 * i:crcs + 4 * i + 4]),
            bytes(data[offsets + 4 * i:offsets + 4 * i + 4]),
        )
        for i in range(count)
    )
    assert pinned in (oid for oid, _crc, _offset in rows)
    for i, (oid, crc, offset) in enumerate(rows):
        data[ids + 20 * i:ids + 20 * i + 20] = oid
        data[crcs + 4 * i:crcs + 4 * i + 4] = crc
        data[offsets + 4 * i:offsets + 4 * i + 4] = offset
    for first_byte in range(256):
        below = sum(oid[0] <= first_byte for oid, _crc, _offset in rows)
        struct.pack_into(">I", data, 8 + 4 * first_byte, below)
    index.chmod(0o644)
    index.write_bytes(bytes(data))
    pack.with_suffix(".rev").unlink(missing_ok=True)
    return pack


def split_index(data: bytes) -> tuple[bytes, list[tuple[bytes, bytes]]]:
    """A version-2 index as (header and entries, [(signature, extension)])."""
    assert data[:8] == b"DIRC\x00\x00\x00\x02"
    position = 12
    for _entry in range(struct.unpack_from(">I", data, 8)[0]):
        # 62 bytes of stat data, id and flags, then the path, NUL-padded to a
        # multiple of eight.
        end = data.index(b"\0", position + 62)
        position += (end - position + 8) & ~7
    entries_end = position
    extensions = []
    while position < len(data) - 20:
        size = struct.unpack_from(">I", data, position + 4)[0]
        extensions.append((data[position:position + 4], data[position + 8:position + 8 + size]))
        position += 8 + size
    return data[:entries_end], extensions


def grow_cache_tree(extension: bytes, grown: set[bytes]) -> bytes:
    """A TREE extension with one more entry counted in each node of ``grown``.

    Nodes come in pre-order as "<name>\\0<entries> <subtrees>\\n<id>", the id
    present only for a valid node; the root's name is empty.
    """
    output = b""
    position = 0
    stack: list[list] = []  # [path, subtrees still to come]
    while position < len(extension):
        nul = extension.index(b"\0", position)
        newline = extension.index(b"\n", nul)
        name = extension[position:nul]
        count, subtrees = (int(field) for field in extension[nul + 1:newline].split(b" "))
        position = newline + 1
        oid = extension[position:position + 20] if count >= 0 else b""
        position += len(oid)
        while stack and stack[-1][1] == 0:
            stack.pop()
        path = b""
        if stack:
            stack[-1][1] -= 1
            path = stack[-1][0] + b"/" + name if stack[-1][0] else name
        stack.append([path, subtrees])
        output += name + b"\0%d %d\n" % (count + (path in grown), subtrees) + oid
    return output


def index_file_under_cached_trees(root: Path, path: str) -> None:
    """Index ``path`` while the index's cache-tree still claims HEAD's trees.

    `git status` compares HEAD with the index through the index's cache-tree
    extension: a directory whose cached tree id equals HEAD's is skipped
    whole, and its cached entry count says how many index entries to skip.
    This indexes ``path`` (in a directory HEAD has), puts back the cache-tree
    of HEAD's own index with one more entry counted along ``path``, and
    re-seals the index checksum.
    """
    index = root / ".git" / "index"
    git(root, *PLAIN_VERSION_2_INDEX, "read-tree", "HEAD")
    pinned = dict(split_index(index.read_bytes())[1])[b"TREE"]
    git(root, *PLAIN_VERSION_2_INDEX, "update-index", "--add", path)
    entries, extensions = split_index(index.read_bytes())
    parts = path.encode().split(b"/")[:-1]
    grown = {b""} | {b"/".join(parts[:depth]) for depth in range(1, len(parts) + 1)}
    data = entries
    for signature, extension in extensions:
        if signature != b"TREE":
            data += signature + struct.pack(">I", len(extension)) + extension
    tree = grow_cache_tree(pinned, grown)
    data += b"TREE" + struct.pack(">I", len(tree)) + tree
    index.write_bytes(data + hashlib.sha1(data).digest())


class CompletionReceiptTests(unittest.TestCase):
    def make_fixture(self, *, g8_checker_bytes: bytes | None = None) -> GreenReceipt:
        temporary = tempfile.TemporaryDirectory(prefix="two-language-gate-")
        self.addCleanup(temporary.cleanup)
        return GreenReceipt(Path(temporary.name), g8_checker_bytes=g8_checker_bytes)

    def test_exact_checker_backed_receipt_is_structurally_complete(self) -> None:
        fixture = self.make_fixture()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertTrue(verdict["accepted"], verdict["errors"])
        self.assertEqual(verdict["result"], "checker-verified-structurally-complete")
        self.assertEqual(set(verdict["gate_results"]), set(gate.GATES))
        self.assertTrue(all(verdict["gate_results"].values()))
        self.assertIn("does_not_establish", verdict)

    def test_cli_forwards_external_inputs_to_g8_only(self) -> None:
        fixture = self.make_fixture()
        external = fixture.root.parent / "caller-supplied-verifier.py"
        external.write_bytes(SCRIPT.read_bytes())
        commands: list[list[str]] = []
        real_run = subprocess.run

        def record(command, *args, **kwargs):
            if (
                isinstance(command, list)
                and len(command) > 5
                and command[:4] == [sys.executable, "-I", "-B", "-X"]
                and command[4].startswith("pycache_prefix=")
                and Path(command[5]).name == "checker.py"
            ):
                commands.append(command)
            return real_run(command, *args, **kwargs)

        with patch.object(gate.subprocess, "run", side_effect=record):
            with contextlib.redirect_stdout(io.StringIO()):
                result = gate.main([
                    "--receipt", str(fixture.path), "--root", str(fixture.root),
                    "--trusted-owner-key", str(fixture.owner_public),
                    "--external-verifier", str(external),
                    "--external-verifier-sha256", sha256(external),
                ])
        self.assertEqual(result, 0)
        self.assertEqual(len(commands), 8)
        for command in commands[:7]:
            self.assertNotIn("--trusted-owner-key", command)
            self.assertNotIn("--external-verifier", command)
            self.assertNotIn("--external-verifier-sha256", command)
        g8 = commands[7]
        self.assertEqual(g8[g8.index("--trusted-owner-key") + 1], str(fixture.owner_public.resolve()))
        self.assertEqual(g8[g8.index("--external-verifier") + 1], str(external.resolve()))
        self.assertEqual(g8[g8.index("--external-verifier-sha256") + 1], sha256(external))

    def test_signed_receipt_loads_real_g8_and_refuses_self_key_and_self_pin(self) -> None:
        fixture = self.make_fixture(g8_checker_bytes=G8_CHECKER.read_bytes())
        external = fixture.root.parent / "caller-verifier-copy.py"
        external.write_bytes(SCRIPT.read_bytes())
        verdict = gate.validate_receipt(
            fixture.path, fixture.root, fixture.owner_public, external, sha256(external),
        )
        self.assertFalse(verdict["accepted"])
        self.assertTrue(all(verdict["gate_results"][gate_id] for gate_id in gate.GATES[:-1]),
                        verdict["errors"])
        self.assertFalse(verdict["gate_results"]["G8"])
        self.assertIsNotNone(verdict["prior_gates_root"])
        prior_gates_root = verdict["prior_gates_root"]
        fixture.sign_detached_seal(prior_gates_root)
        verdict = gate.validate_receipt(
            fixture.path, fixture.root, fixture.owner_public, external, sha256(external),
        )
        self.assertEqual(verdict["prior_gates_root"], prior_gates_root)
        self.assertFalse(verdict["gate_results"]["G8"])
        self.assertTrue(any("G8.checker_run: checker exited 1" in error for error in verdict["errors"]))
        self.assertTrue(any(
            "detached_release_seal_binds_prior_root_and_artifact: "
            "detached seal signature verifies under the caller-supplied key, "
            "but no independently configured owner-key authorization anchor exists" in error
                            for error in verdict["errors"]))

        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            exit_code = gate.main([
                "--receipt", str(fixture.path), "--root", str(fixture.root),
                "--trusted-owner-key", str(fixture.owner_public),
                "--candidate-verifier", fixture.candidate_top.relative_to(fixture.root).as_posix(),
                "--external-verifier", str(external),
                "--external-verifier-sha256", sha256(external),
            ])
        cli_verdict = json.loads(output.getvalue())
        self.assertEqual(exit_code, 1)
        self.assertFalse(cli_verdict["gate_results"]["G8"])
        self.assertEqual(cli_verdict["prior_gates_root"], prior_gates_root)
        self.assertTrue(any(
            "detached_release_seal_binds_prior_root_and_artifact: "
            "detached seal signature verifies under the caller-supplied key" in error
            for error in cli_verdict["errors"]
        ))
        self.assertTrue(all(cli_verdict["gate_results"][gate_id]
                            for gate_id in gate.GATES[:-1]))

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

    def test_schema_owned_checker_symlink_is_rejected_before_resolution(self) -> None:
        fixture = self.make_fixture()
        checker = fixture.root / gate.CHECKER_PATHS["G1"]
        target = fixture.root / "checker-target.py"
        target.write_bytes(checker.read_bytes())
        checker.unlink()
        checker.symlink_to(target)
        validator = gate.ReceiptValidator(fixture.root, fixture.path, fixture.owner_public)
        resolved = validator.resolve_checker(
            "G1", fixture.source_revision, sha256(target), "G1.checker_sha256"
        )
        self.assertIsNone(resolved)
        self.assertTrue(any("not a symlink" in error for error in validator.errors))

        checker.unlink()
        checker.symlink_to(checker.name)
        validator = gate.ReceiptValidator(fixture.root, fixture.path, fixture.owner_public)
        resolved = validator.resolve_checker(
            "G1", fixture.source_revision, sha256(target), "G1.checker_sha256"
        )
        self.assertIsNone(resolved)
        self.assertTrue(any("not a symlink" in error for error in validator.errors))

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

    def test_git_environment_cannot_spoof_clean_worktree(self) -> None:
        fixture = self.make_fixture()
        clean = fixture.root.parent / "clean-copy"
        subprocess.run(["git", "clone", "-q", str(fixture.root), str(clean)], check=True)
        subprocess.run(
            ["git", "-C", str(clean), "remote", "set-url", "origin", gate.REPOSITORY_ID],
            check=True,
        )
        (fixture.root / "dirty.txt").write_text("not committed\n", encoding="utf-8")
        git_calls: list[tuple[list[str], dict[str, str] | None]] = []
        real_run = subprocess.run

        def record(command, *args, **kwargs):
            if isinstance(command, list) and command and command[0] == "git":
                git_calls.append((command, kwargs.get("env")))
            return real_run(command, *args, **kwargs)

        with patch.dict(os.environ, {"GIT_DIR": str(clean / ".git"), "GIT_WORK_TREE": str(clean)}):
            with patch.object(gate.subprocess, "run", side_effect=record):
                verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(any("worktree is not clean" in error for error in verdict["errors"]), verdict)
        self.assertTrue(any("status" in command for command, _env in git_calls))
        # Every caller GIT_* variable is gone; the only ones left are those the
        # gate sets itself to neutralize system and global configuration and
        # lazy fetching.
        gate_owned = {
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_ATTR_NOSYSTEM": "1",
            "GIT_NO_LAZY_FETCH": "1",
        }
        git_keys = [
            (command, None if env is None else sorted(key for key in env if key.startswith("GIT_")))
            for command, env in git_calls
        ]
        self.assertTrue(
            all(
                env is not None
                and {key: value for key, value in env.items() if key.startswith("GIT_")}
                == gate_owned
                and env.get("XDG_CONFIG_HOME") == os.devnull
                for _command, env in git_calls
            ),
            git_keys,
        )
        cli = subprocess.run(
            [
                sys.executable, str(SCRIPT), "--receipt", str(fixture.path),
                "--root", str(fixture.root), "--candidate-verifier",
                str(fixture.candidate_top), "--trusted-owner-key", str(fixture.owner_public),
            ],
            env={**os.environ, "GIT_DIR": str(clean / ".git"), "GIT_WORK_TREE": str(clean)},
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(cli.returncode, 1, cli.stderr)
        self.assertFalse(json.loads(cli.stdout)["accepted"])

    def test_malformed_toolchain_roles_produce_verdict(self) -> None:
        fixture = self.make_fixture()
        toolchain = json.loads(fixture.toolchain.read_text(encoding="utf-8"))
        toolchain["components"][0]["role"] = []
        write_json(fixture.toolchain, toolchain)
        fixture.receipt["toolchain_manifest"] = fixture.ref(fixture.toolchain)
        fixture.write_receipt()
        verdict = gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)
        self.assertFalse(verdict["accepted"])
        self.assertTrue(
            any("toolchain_manifest.components[0].role" in error for error in verdict["errors"]),
            verdict,
        )
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            rc = gate.main([
                "--receipt", str(fixture.path), "--root", str(fixture.root),
                "--trusted-owner-key", str(fixture.owner_public),
            ])
        self.assertEqual(rc, 1)
        self.assertFalse(json.loads(output.getvalue())["accepted"])

        roster = json.loads(
            (fixture.evidence_dir / "acceptance-environment-contract.json").read_text(encoding="utf-8")
        )
        roster["component_roster"][0]["role"] = []
        validator = gate.ReceiptValidator(fixture.root, fixture.path, fixture.owner_public)
        validator.validate_acceptance_environment_contract(roster)
        self.assertTrue(
            any("acceptance_environment.component_roster[0].role" in error for error in validator.errors),
            validator.errors,
        )

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


class CleanTreePredicateTests(unittest.TestCase):
    """Attacks on the clean-tree predicate and the other --root identity checks.

    Each tree attack leaves `git status --porcelain` empty -- the old predicate,
    asserted as the attack's precondition -- while the checkers would read bytes
    the source revision does not pin; each must be refused.  The fsmonitor and
    promisor attacks instead configure a program that a checker's read-only Git
    would start; each must be refused by name, with neither a checker nor the
    gate's own Git having started it.  The case-alias, symlink-loop,
    deleted-directory and missing-key tests cover the identity and resolve()
    sites; the Git-version, failed-conversion, false-setting and newline-path
    tests keep a genuine checkout from being refused, or refused for the wrong
    reason; and the last test is the positive control: a genuinely clean
    checkout stays accepted.
    """

    def make_fixture(
        self, before_commit: Callable[[Path], None] | None = add_pinned_file
    ) -> GreenReceipt:
        temporary = tempfile.TemporaryDirectory(prefix="two-language-gate-")
        self.addCleanup(temporary.cleanup)
        return GreenReceipt(Path(temporary.name), before_commit=before_commit)

    def validate(self, fixture: GreenReceipt, owner_key: Path | None = None) -> dict:
        return gate.validate_receipt(
            fixture.path, fixture.root, owner_key or fixture.owner_public
        )

    def assert_refused(self, verdict: dict, *fragments: str) -> None:
        self.assertFalse(verdict["accepted"], verdict["errors"])
        for fragment in fragments:
            self.assertTrue(
                any(fragment in error for error in verdict["errors"]),
                f"{fragment!r} not in {verdict['errors']}",
            )

    def case_alias(self, fixture: GreenReceipt) -> Path:
        alias = fixture.root.parent / fixture.root.name.upper()
        if not alias.exists() or not os.path.samefile(alias, fixture.root):
            self.skipTest(
                "TMPDIR is case-sensitive, so no case-aliased spelling of --root exists"
            )
        return alias

    def test_clean_filter_cannot_hide_a_rewritten_tracked_file(self) -> None:
        fixture = self.make_fixture()
        original = fixture.root.parent / "pinned-original.txt"
        original.write_text(PINNED_TEXT, encoding="utf-8")
        ran = fixture.root.parent / "filter-ran"
        (fixture.root / "pinned.txt").write_text(FORGED_TEXT, encoding="utf-8")
        (fixture.root / ".git" / "info" / "attributes").write_text(
            "pinned.txt filter=hide\n", encoding="utf-8"
        )
        git(
            fixture.root, "config", "filter.hide.clean",
            f"touch '{ran}'; cat >/dev/null; cat '{original}'",
        )
        self.assertEqual(plain_status(fixture.root), "")
        self.assertTrue(ran.exists())
        ran.unlink()
        self.assert_refused(
            self.validate(fixture),
            "filter drivers in the repository configuration",
            "filter.hide.clean",
            "info/attributes adds repository-local attributes",
            "raw worktree bytes differ from HEAD's checkout: pinned.txt",
        )
        # Neither status nor the conversion check (in its own sandbox
        # repository) ran the candidate's filter.
        self.assertFalse(ran.exists())

    def test_skip_worktree_cannot_hide_a_rewritten_tracked_file(self) -> None:
        fixture = self.make_fixture()
        (fixture.root / "pinned.txt").write_text(FORGED_TEXT, encoding="utf-8")
        git(fixture.root, "update-index", "--skip-worktree", "pinned.txt")
        self.assertEqual(plain_status(fixture.root), "")
        self.assert_refused(
            self.validate(fixture),
            "skip-worktree index entries hide their worktree files: pinned.txt",
            "raw worktree bytes differ from HEAD's checkout: pinned.txt",
        )

    def test_assume_unchanged_cannot_hide_a_rewritten_tracked_file(self) -> None:
        fixture = self.make_fixture()
        (fixture.root / "pinned.txt").write_text(FORGED_TEXT, encoding="utf-8")
        git(fixture.root, "update-index", "--assume-unchanged", "pinned.txt")
        self.assertEqual(plain_status(fixture.root), "")
        self.assert_refused(
            self.validate(fixture),
            "assume-unchanged index entries hide their worktree files: pinned.txt",
            "raw worktree bytes differ from HEAD's checkout: pinned.txt",
        )

    def test_forged_stat_data_cannot_hide_a_same_size_rewrite(self) -> None:
        fixture = self.make_fixture()
        pinned = fixture.root / "pinned.txt"
        then = time.time_ns() - 1000 * 10**9
        os.utime(pinned, ns=(then, then))
        git(fixture.root, "update-index", "-q", "--refresh")
        git(fixture.root, "config", "core.trustctime", "false")
        git(fixture.root, "config", "core.checkStat", "minimal")
        with pinned.open("r+b") as handle:
            handle.write(FORGED_TEXT.encode())
        os.utime(pinned, ns=(then, then))
        self.assertEqual(plain_status(fixture.root), "")
        self.assert_refused(
            self.validate(fixture),
            "raw worktree bytes differ from HEAD's checkout: pinned.txt",
        )

    def test_eol_conversion_recorded_in_the_index_cannot_hide_raw_bytes(self) -> None:
        # One `git -c core.autocrlf=true add` records the CRLF rewrite's stat
        # data against the pinned blob; no configuration is left behind and
        # even the hardened status reads clean.  Only raw bytes show it.
        fixture = self.make_fixture()
        pinned = fixture.root / "pinned.txt"
        pinned.write_bytes(PINNED_TEXT.replace("\n", "\r\n").encode())
        then = time.time_ns() - 1000 * 10**9
        os.utime(pinned, ns=(then, then))
        git(fixture.root, "-c", "core.autocrlf=true", "add", "pinned.txt")
        self.assertEqual(plain_status(fixture.root), "")
        self.assertEqual(
            git(fixture.root, "rev-parse", ":pinned.txt"),
            git(fixture.root, "rev-parse", "HEAD:pinned.txt"),
        )
        self.assert_refused(
            self.validate(fixture),
            "raw worktree bytes differ from HEAD's checkout: pinned.txt",
        )
        hardened_status = git(
            fixture.root, *gate.HARDENED_STATUS_OPTIONS, "status", "--porcelain",
            "--untracked-files=all", "--ignore-submodules=none",
        )
        self.assertEqual(hardened_status, "")

    def test_conversion_that_depends_on_core_ignorecase_is_not_the_pinned_checkout(self) -> None:
        # The committed pattern matches notes.txt only case-insensitively, and
        # core.ignoreCase is the candidate's own setting: CRLF bytes there are
        # not what the pinned revision checks out, whatever that setting says.
        def setup(root: Path) -> None:
            add_pinned_file(root)
            (root / ".gitattributes").write_text("NOTES.TXT text eol=crlf\n", encoding="utf-8")
            (root / "notes.txt").write_text("case\nfolded\n", encoding="utf-8")
            earlier = time.time_ns() - 2000 * 10**9
            os.utime(root / "notes.txt", ns=(earlier, earlier))
            git(root, "-c", "core.safecrlf=false", "add", ".gitattributes", "notes.txt")

        fixture = self.make_fixture(setup)
        notes = fixture.root / "notes.txt"
        notes.write_bytes(b"case\r\nfolded\r\n")
        then = time.time_ns() - 1000 * 10**9
        os.utime(notes, ns=(then, then))
        git(fixture.root, "config", "core.ignoreCase", "true")
        git(fixture.root, "-c", "core.safecrlf=false", "add", "notes.txt")
        self.assertEqual(plain_status(fixture.root), "")
        self.assertEqual(
            git(fixture.root, "rev-parse", ":notes.txt"),
            git(fixture.root, "rev-parse", "HEAD:notes.txt"),
        )
        self.assert_refused(
            self.validate(fixture),
            "raw worktree bytes differ from HEAD's checkout: notes.txt",
        )

    def test_replacement_refs_cannot_substitute_the_pinned_tree(self) -> None:
        fixture = self.make_fixture()
        (fixture.root / "pinned.txt").write_text(FORGED_TEXT, encoding="utf-8")
        git(fixture.root, "add", "pinned.txt")
        forged_tree = git(fixture.root, "write-tree").strip()
        forged = git(fixture.root, "commit-tree", forged_tree, "-m", "forged").strip()
        git(fixture.root, "replace", fixture.source_revision, forged)
        self.assertEqual(plain_status(fixture.root), "")
        self.assertEqual(git(fixture.root, "rev-parse", "HEAD").strip(), fixture.source_revision)
        self.assert_refused(
            self.validate(fixture),
            f"replacement refs substitute object content for every other Git reader: "
            f"refs/replace/{fixture.source_revision}",
            "raw worktree bytes differ from HEAD's checkout: pinned.txt",
        )

    def test_substituted_subtree_object_cannot_list_forged_files(self) -> None:
        # The commit id is untouched; only the pack index lies about what the
        # pinned vendor/ tree contains, and `ls-tree -r` and status believe it.
        def setup(root: Path) -> None:
            add_pinned_file(root)
            (root / "vendor").mkdir()
            (root / "vendor" / "pinned.txt").write_text(PINNED_TEXT, encoding="utf-8")

        fixture = self.make_fixture(setup)
        pinned_tree = git(fixture.root, "rev-parse", "HEAD:vendor").strip()
        (fixture.root / "vendor" / "pinned.txt").write_text(FORGED_TEXT, encoding="utf-8")
        git(fixture.root, "add", "vendor/pinned.txt")
        forged_tree = git(fixture.root, "write-tree", "--prefix=vendor/").strip()
        serve_object_as(fixture.root, pinned_tree, forged_tree)
        self.assertEqual(plain_status(fixture.root), "")
        self.assertEqual(git(fixture.root, "rev-parse", "HEAD").strip(), fixture.source_revision)
        self.assertEqual(
            git(fixture.root, "rev-parse", ":vendor/pinned.txt").strip(),
            git(fixture.root, "ls-tree", "-r", "HEAD", "vendor/pinned.txt").split()[2],
        )
        self.assert_refused(
            self.validate(fixture),
            f"object {pinned_tree} does not hash to its id (a substituted object)",
        )

    def test_substituted_blob_cannot_pass_as_a_checkout_conversion(self) -> None:
        # The pinned blob's id is answered with the forged bytes, so the
        # checkout-conversion comparison must re-hash the blob it converts.
        fixture = self.make_fixture()
        pinned = fixture.root / "pinned.txt"
        pinned_blob = git(fixture.root, "rev-parse", "HEAD:pinned.txt").strip()
        original = fixture.root.parent / "pinned-original.txt"
        original.write_text(PINNED_TEXT, encoding="utf-8")
        attributes = fixture.root.parent / "one-shot-attributes"
        attributes.write_text("pinned.txt filter=hide\n", encoding="utf-8")
        pinned.write_text(FORGED_TEXT, encoding="utf-8")
        then = time.time_ns() - 1000 * 10**9
        os.utime(pinned, ns=(then, then))
        # Record the forged file's stat data against the pinned blob, leaving
        # no filter or attributes configuration behind.
        git(
            fixture.root, "-c", f"core.attributesFile={attributes}",
            "-c", f"filter.hide.clean=cat >/dev/null; cat '{original}'", "add", "pinned.txt",
        )
        forged_blob = hash_object(fixture.root, FORGED_TEXT)
        serve_object_as(fixture.root, pinned_blob, forged_blob)
        self.assertEqual(plain_status(fixture.root), "")
        self.assertEqual(git(fixture.root, "cat-file", "blob", pinned_blob), FORGED_TEXT)
        self.assert_refused(
            self.validate(fixture),
            f"cannot compute HEAD's checkout conversion for pinned.txt: object {pinned_blob} "
            "does not hash to its id (a substituted object)",
        )

    def rewrite_as_utf16_under(self, fixture: GreenReceipt, attributes: str) -> None:
        # pinned.txt becomes its UTF-16LE encoding, and its index entry records
        # that file's stat data against the pinned blob, as a one-shot `git add`
        # under ``attributes`` leaves it: no configuration stays behind.
        pinned = fixture.root / "pinned.txt"
        pinned.write_bytes(PINNED_TEXT.encode("utf-16le"))
        then = time.time_ns() - 1000 * 10**9
        os.utime(pinned, ns=(then, then))
        one_shot = fixture.root.parent / "one-shot-attributes"
        one_shot.write_text(attributes, encoding="utf-8")
        git(fixture.root, "-c", f"core.attributesFile={one_shot}", "add", "pinned.txt")
        self.assertEqual(plain_status(fixture.root), "")

    @staticmethod
    def commit_binary_attributes(root: Path) -> None:
        add_pinned_file(root)
        (root / ".gitattributes").write_text("*.bin binary\n", encoding="utf-8")

    def test_substituted_gitattributes_cannot_license_a_conversion(self) -> None:
        # The worktree .gitattributes is genuine, but the object store answers
        # its pinned id with attributes that re-encode pinned.txt as UTF-16LE,
        # and Git converts with the attributes it reads from the store.
        fixture = self.make_fixture(self.commit_binary_attributes)
        forged_attributes = "pinned.txt working-tree-encoding=UTF-16LE\n"
        pinned_attributes = git(fixture.root, "rev-parse", "HEAD:.gitattributes").strip()
        serve_object_as(
            fixture.root, pinned_attributes, hash_object(fixture.root, forged_attributes)
        )
        self.rewrite_as_utf16_under(fixture, forged_attributes)
        self.assertEqual((fixture.root / ".gitattributes").read_text(), "*.bin binary\n")
        self.assert_refused(
            self.validate(fixture),
            f"cannot compute HEAD's checkout conversion for pinned.txt: object "
            f"{pinned_attributes} does not hash to its id (a substituted object)",
        )

    def test_attributes_a_converting_git_reads_later_cannot_license_a_conversion(self) -> None:
        # Two packs claim the pinned .gitattributes id: the newer one holds the
        # genuine blob, the older one -- which also holds pinned.txt's blob --
        # forged attributes.  Git searches packs most recently used first, so
        # a process that reads only the attributes id re-hashes the genuine
        # blob, while one that converts pinned.txt reads its blob first, from
        # the older pack, and then takes the forged attributes from that pack.
        # Re-hashing the attributes in one Git process and converting in
        # another therefore proves nothing; the conversion must not read the
        # candidate's object store at all.
        fixture = self.make_fixture(self.commit_binary_attributes)
        root = fixture.root
        forged_attributes = "pinned.txt working-tree-encoding=UTF-16LE\n"
        pinned_attributes = git(root, "rev-parse", "HEAD:.gitattributes").strip()
        pinned_blob = git(root, "rev-parse", "HEAD:pinned.txt").strip()
        forged = hash_object(root, forged_attributes)
        genuine_pack = pack_objects(root, "genuine", [pinned_attributes])
        forged_pack = pack_objects(
            root, "forged", [pinned_blob, forged], alias=(forged, pinned_attributes)
        )
        now = time.time()
        for pack, when in ((forged_pack, now - 1000), (genuine_pack, now)):
            for suffix in (".pack", ".idx"):
                os.utime(pack.with_suffix(suffix), (when, when))
        self.rewrite_as_utf16_under(fixture, forged_attributes)
        self.assertIn(
            git(root, "cat-file", "blob", pinned_attributes),
            ("*.bin binary\n", forged_attributes),
        )
        candidate_conversion = subprocess.run(
            [
                "git", "-C", str(root), "--attr-source=HEAD", "cat-file", "--filters",
                "--path=pinned.txt", pinned_blob,
            ],
            check=True, capture_output=True,
        ).stdout
        self.assertEqual(candidate_conversion, (root / "pinned.txt").read_bytes())
        # Which refusal comes first depends on the order in which the running
        # Git searches the two packs: one that serves the forged pack for the
        # pinned attributes id finds that object truncated or its content
        # substituted before any conversion runs; one that serves the genuine pack converts from
        # verified bytes and finds pinned.txt differs.  Either way the forged
        # attributes license nothing.
        verdict = self.validate(fixture)
        self.assertFalse(verdict["accepted"], verdict["errors"])
        self.assertTrue(
            any(
                "raw worktree bytes differ from HEAD's checkout: pinned.txt" in error
                or (
                    "cannot compute HEAD's checkout conversion for pinned.txt" in error
                    and (
                        "is truncated" in error
                        or (
                            f"object {pinned_attributes}" in error
                            and "does not hash to its id (a substituted object)" in error
                        )
                    )
                )
                for error in verdict["errors"]
            ),
            verdict["errors"],
        )

    @staticmethod
    def commit_crlf_checkout(root: Path) -> None:
        add_pinned_file(root)
        (root / ".gitattributes").write_text("crlf.txt text eol=crlf\n", encoding="utf-8")
        (root / "crlf.txt").write_bytes(b"checked out\r\nwith CRLF\r\n")

    def checked_out_crlf_fixture(self) -> GreenReceipt:
        fixture = self.make_fixture(self.commit_crlf_checkout)
        (fixture.root / "crlf.txt").unlink()
        git(fixture.root, "checkout", "--", "crlf.txt")
        self.assertEqual(
            (fixture.root / "crlf.txt").read_bytes(), b"checked out\r\nwith CRLF\r\n"
        )
        self.assertEqual(plain_status(fixture.root), "")
        return fixture

    def test_failed_conversion_is_reported_as_such_not_as_tampering(self) -> None:
        # A Git that cannot compute the conversion (2.40 and older exit 129 on
        # --attr-source) must not blame the genuine file it could not check.
        fixture = self.checked_out_crlf_fixture()
        real_git_run = gate._git_run

        def git_without_attr_source(
            root: Path, *args: str, **kwargs: object
        ) -> subprocess.CompletedProcess:
            if any(arg.startswith("--attr-source=") for arg in args):
                return subprocess.CompletedProcess(
                    ["git", *args], 129, b"", b"unknown option: --attr-source\nusage: git ..."
                )
            return real_git_run(root, *args, **kwargs)

        with patch.object(gate, "_git_run", side_effect=git_without_attr_source):
            verdict = self.validate(fixture)
        self.assert_refused(
            verdict,
            "cannot compute HEAD's checkout conversion for crlf.txt: git exited 129: "
            "unknown option: --attr-source",
        )
        self.assertFalse(
            any("raw worktree bytes differ" in error for error in verdict["errors"]),
            verdict["errors"],
        )
        self.assertTrue(self.validate(fixture)["accepted"])

    def test_git_older_than_2_41_is_refused_with_the_reason(self) -> None:
        fixture = self.make_fixture()
        real_run = subprocess.run
        answers: dict[str, bytes] = {}

        def reported_git(command, *args, **kwargs):
            if command == ["git", "--version"]:
                return subprocess.CompletedProcess(command, 0, answers["version"], b"")
            return real_run(command, *args, **kwargs)

        with patch.object(gate.subprocess, "run", side_effect=reported_git):
            answers["version"] = b"git version 2.40.1 (Apple Git-143)\n"
            too_old = gate.worktree_refusals(fixture.root)
            verdict = self.validate(fixture)
            answers["version"] = b"git version 2.41.0\n"
            recent = gate.worktree_refusals(fixture.root)
        self.assertEqual(len(too_old), 1, too_old)
        self.assertIn("git 2.40 is too old for this gate", too_old[0])
        self.assertIn("--attr-source (2.41)", too_old[0])
        self.assertIn("2.41+ is required", too_old[0])
        self.assert_refused(verdict, "repository: worktree is not clean: git 2.40 is too old")
        self.assertEqual(recent, [])

    def test_graft_file_is_refused_by_name(self) -> None:
        fixture = self.make_fixture()
        tree = git(fixture.root, "rev-parse", "HEAD^{tree}").strip()
        ancestor = git(fixture.root, "commit-tree", tree, "-m", "forged ancestor").strip()
        grafts = fixture.root / ".git" / "info" / "grafts"
        grafts.write_text(f"{fixture.source_revision} {ancestor}\n", encoding="utf-8")
        self.assertEqual(plain_status(fixture.root), "")
        self.assert_refused(
            self.validate(fixture),
            "info/grafts rewrites commit ancestry (a graft file)",
        )

    def test_submodule_off_its_pin_is_refused_despite_ignore_all(self) -> None:
        revisions: dict[str, tuple[str, str]] = {}

        def setup(root: Path) -> None:
            add_pinned_file(root)
            revisions["engine"] = add_engine_submodule(root)

        fixture = self.make_fixture(setup)
        pinned, later = revisions["engine"]
        engine = fixture.root / ENGINE
        git(engine, "checkout", "-q", later)
        git(fixture.root, "config", f"submodule.{ENGINE}.ignore", "all")
        self.assertEqual(plain_status(fixture.root), "")
        self.assert_refused(
            self.validate(fixture),
            f"submodule {ENGINE}: HEAD {later} is not the pinned commit {pinned}",
        )

        # At its pin but with rewritten content the index is told to ignore.
        git(engine, "checkout", "-q", pinned)
        (engine / "engine.txt").write_text("forged engine\n", encoding="utf-8")
        git(engine, "update-index", "--assume-unchanged", "engine.txt")
        self.assertEqual(plain_status(fixture.root), "")
        self.assert_refused(
            self.validate(fixture),
            f"submodule {ENGINE}: assume-unchanged index entries hide their worktree files",
            f"submodule {ENGINE}: raw worktree bytes differ from HEAD's checkout: engine.txt",
        )

    def test_uninitialized_gitlink_directory_with_forged_content_is_refused(self) -> None:
        def setup(root: Path) -> None:
            add_pinned_file(root)
            add_engine_submodule(root)

        fixture = self.make_fixture(setup)
        git(fixture.root, "submodule", "deinit", "-q", "-f", ENGINE)
        engine = fixture.root / ENGINE
        self.assertEqual(list(engine.iterdir()), [])
        (engine / "engine.txt").write_text("forged engine\n", encoding="utf-8")
        self.assertEqual(plain_status(fixture.root), "")
        self.assert_refused(
            self.validate(fixture),
            f"gitlink directory holds content outside its pin (no .git): {ENGINE}",
        )

    def test_core_worktree_cannot_point_git_at_a_decoy_checkout(self) -> None:
        fixture = self.make_fixture()
        decoy = fixture.root.parent / "decoy"
        subprocess.run(["git", "clone", "-q", str(fixture.root), str(decoy)], check=True)
        shutil.rmtree(decoy / ".git")
        git(fixture.root, "config", "core.worktree", str(decoy))
        (fixture.root / "pinned.txt").write_text(FORGED_TEXT, encoding="utf-8")
        self.assertEqual(plain_status(fixture.root), "")
        self.assert_refused(
            self.validate(fixture),
            "(core.worktree or a .git file redirects it)",
        )

    def test_forged_cache_tree_cannot_hide_an_extra_indexed_file(self) -> None:
        # The index lists scripts/evil.py with fresh stat data and no flag, and
        # its cache-tree claims scripts/ is still HEAD's tree: status skips the
        # directory when comparing HEAD with the index, and the file is not
        # untracked because the index lists it.
        fixture = self.make_fixture()
        (fixture.root / "scripts" / "evil.py").write_text("print('unpinned')\n", encoding="utf-8")
        index_file_under_cached_trees(fixture.root, "scripts/evil.py")
        self.assertEqual(plain_status(fixture.root), "")
        self.assertEqual(
            git(fixture.root, "ls-files", "-v", "scripts/evil.py"), "H scripts/evil.py\n"
        )
        self.assert_refused(
            self.validate(fixture),
            "index entries differ from HEAD's tree: scripts/evil.py",
            "worktree entries neither in HEAD nor reported by git status: scripts/evil.py",
        )

    def test_untracked_gitignore_cannot_hide_untracked_files(self) -> None:
        # Git reads a .gitignore in every directory it walks, tracked or not; an
        # untracked one can ignore itself and anything beside it.
        fixture = self.make_fixture()
        scripts = fixture.root / "scripts"
        (scripts / ".gitignore").write_text(".gitignore\nevil.py\n", encoding="utf-8")
        (scripts / "evil.py").write_text("print('unpinned')\n", encoding="utf-8")
        self.assertEqual(plain_status(fixture.root), "")
        self.assert_refused(
            self.validate(fixture),
            "untracked .gitignore files hide untracked content from git status: "
            "scripts/.gitignore",
        )

    def test_entries_git_status_never_reports_are_refused(self) -> None:
        # Git's untracked-file walk skips every entry named .git and every
        # FIFO, socket or device, and does not report a directory holding
        # only such entries.
        def dot_git_directory(root: Path) -> str:
            (root / "scripts" / ".git").mkdir()
            (root / "scripts" / ".git" / "evil.py").write_text("unpinned\n", encoding="utf-8")
            return "scripts/.git"

        def directory_holding_only_dot_git(root: Path) -> str:
            (root / "extra" / "sub" / ".git").mkdir(parents=True)
            (root / "extra" / "sub" / ".git" / "evil.lean").write_text("x\n", encoding="utf-8")
            return "extra/sub/.git"

        def fifo(root: Path) -> str:
            os.mkfifo(root / "scripts" / "evil.fifo")
            return "scripts/evil.fifo"

        for plant in (dot_git_directory, directory_holding_only_dot_git, fifo):
            with self.subTest(plant.__name__):
                fixture = self.make_fixture()
                planted = plant(fixture.root)
                self.assertEqual(plain_status(fixture.root), "")
                self.assert_refused(
                    self.validate(fixture),
                    f"worktree entries neither in HEAD nor reported by git status: {planted}",
                )

    def test_filter_driver_in_any_repository_config_scope_is_refused(self) -> None:
        # Mounted variants: the driver comes from an included file, from a
        # conditional include, or from the worktree-scoped config file.
        def include_path(root: Path, driver: Path) -> None:
            git(root, "config", "include.path", str(driver))

        def include_if_gitdir(root: Path, driver: Path) -> None:
            git(root, "config", f"includeIf.gitdir:{os.path.realpath(root)}/.git.path", str(driver))

        def worktree_scope(root: Path, driver: Path) -> None:
            git(root, "config", "extensions.worktreeConfig", "true")
            shutil.copyfile(driver, root / ".git" / "config.worktree")

        for scope in (include_path, include_if_gitdir, worktree_scope):
            with self.subTest(scope.__name__):
                fixture = self.make_fixture()
                original = fixture.root.parent / "pinned-original.txt"
                original.write_text(PINNED_TEXT, encoding="utf-8")
                driver = fixture.root.parent / "driver.cfg"
                driver.write_text(
                    f'[filter "hide"]\n\tclean = "cat >/dev/null; cat \'{original}\'"\n',
                    encoding="utf-8",
                )
                scope(fixture.root, driver)
                attributes = fixture.root.parent / "attributes"
                attributes.write_text("pinned.txt filter=hide\n", encoding="utf-8")
                git(fixture.root, "config", "core.attributesFile", str(attributes))
                (fixture.root / "pinned.txt").write_text(FORGED_TEXT, encoding="utf-8")
                self.assertEqual(plain_status(fixture.root), "")
                self.assert_refused(
                    self.validate(fixture),
                    "filter drivers in the repository configuration rewrite content "
                    "between the index and the worktree: filter.hide.clean",
                    "raw worktree bytes differ from HEAD's checkout: pinned.txt",
                )

    def test_sparse_checkout_and_split_index_cannot_hide_a_rewrite(self) -> None:
        # Mounted variants: a sparse checkout told to expect files outside its
        # patterns keeps skip-worktree on a present file, and a split index
        # keeps the flag in its shared part.
        for variant in ("sparse checkout", "split index"):
            with self.subTest(variant):
                fixture = self.make_fixture()
                root = fixture.root
                if variant == "sparse checkout":
                    git(root, "config", "sparse.expectFilesOutsideOfPatterns", "true")
                    git(root, "sparse-checkout", "set", "--no-cone", "/*", "!/pinned.txt")
                else:
                    git(root, "update-index", "--split-index")
                    git(root, "update-index", "--skip-worktree", "pinned.txt")
                (root / "pinned.txt").write_text(FORGED_TEXT, encoding="utf-8")
                self.assertEqual(plain_status(root), "")
                self.assert_refused(
                    self.validate(fixture),
                    "skip-worktree index entries hide their worktree files: pinned.txt",
                    "raw worktree bytes differ from HEAD's checkout: pinned.txt",
                )

    def test_submodule_filter_replace_ref_and_worktree_redirect_are_refused(self) -> None:
        # Mounted variants inside a submodule whose HEAD is its pin: its own
        # filter driver hides a rewrite; a replacement makes the pinned commit
        # read as the later one, whose content the submodule then holds; or
        # its core.worktree points Git at a decoy while the checkout itself is
        # rewritten.
        for variant in ("filter driver", "replace ref", "core.worktree"):
            with self.subTest(variant):
                revisions: dict[str, tuple[str, str]] = {}

                def setup(root: Path) -> None:
                    add_pinned_file(root)
                    revisions["engine"] = add_engine_submodule(root)

                fixture = self.make_fixture(setup)
                pinned, later = revisions["engine"]
                engine = fixture.root / ENGINE
                if variant == "filter driver":
                    original = fixture.root.parent / "engine-original.txt"
                    original.write_text("engine v1\n", encoding="utf-8")
                    git_dir = Path(git(engine, "rev-parse", "--absolute-git-dir").strip())
                    (git_dir / "info").mkdir(exist_ok=True)
                    (git_dir / "info" / "attributes").write_text(
                        "engine.txt filter=hide\n", encoding="utf-8"
                    )
                    git(engine, "config", "filter.hide.clean", f"cat >/dev/null; cat '{original}'")
                    (engine / "engine.txt").write_text("forged v1\n", encoding="utf-8")
                    expected = (
                        f"submodule {ENGINE}: filter drivers in the repository configuration "
                        "rewrite content between the index and the worktree: filter.hide.clean"
                    )
                elif variant == "replace ref":
                    git(engine, "replace", pinned, later)
                    (engine / "engine.txt").write_text("engine v2\n", encoding="utf-8")
                    git(engine, "add", "engine.txt")
                    expected = (
                        f"submodule {ENGINE}: replacement refs substitute object content "
                        f"for every other Git reader: refs/replace/{pinned}"
                    )
                else:
                    decoy = fixture.root.parent / "decoy-engine"
                    decoy.mkdir()
                    (decoy / "engine.txt").write_text("engine v1\n", encoding="utf-8")
                    git(engine, "config", "core.worktree", str(decoy))
                    (engine / "engine.txt").write_text("forged engine\n", encoding="utf-8")
                    expected = f"submodule {ENGINE}: Git inspects "
                self.assertEqual(git(engine, "rev-parse", "HEAD").strip(), pinned)
                self.assertEqual(plain_status(fixture.root), "")
                self.assert_refused(self.validate(fixture), expected)

    def test_fsmonitor_in_any_repository_config_scope_is_refused_by_name(self) -> None:
        # The gate's own Git passes core.fsmonitor=false, but a checker's Git
        # reads the candidate's configuration: G2's `git status` in
        # first-party/clean (which the fixture G2 runs too) starts the hook
        # configured there.  Mounted variants: the root's config, an included
        # file, the worktree scope, the submodule's config, and true (the
        # built-in daemon) spelled as a value or as a key without one.
        def setup(root: Path) -> None:
            add_pinned_file(root)
            add_engine_submodule(root, CLEAN)
            inject_into_checker(root, "G2", G2_CLEAN_STATUS)

        refusal = "core.fsmonitor starts a program whenever a checker's Git reads the index: "
        for variant in (
            "root config", "include.path", "worktree config", "submodule config",
            "true", "no value",
        ):
            with self.subTest(variant):
                fixture = self.make_fixture(setup)
                root = fixture.root
                ran = root.parent / "fsmonitor-ran"
                hook = recording_program(root.parent / "fsmonitor-hook", ran)
                included = root.parent / "monitor.cfg"
                included.write_text(f"[core]\n\tfsmonitor = {hook}\n", encoding="utf-8")
                expected = f"{refusal}core.fsmonitor={hook}"
                if variant == "root config":
                    git(root, "config", "core.fsmonitor", str(hook))
                elif variant == "include.path":
                    git(root, "config", "include.path", str(included))
                elif variant == "worktree config":
                    git(root, "config", "extensions.worktreeConfig", "true")
                    shutil.copyfile(included, root / ".git" / "config.worktree")
                elif variant == "submodule config":
                    git(root / CLEAN, "config", "core.fsmonitor", str(hook))
                    expected = f"submodule {CLEAN}: {expected}"
                elif variant == "true":
                    git(root, "config", "core.fsmonitor", "true")
                    expected = f"{refusal}core.fsmonitor=true"
                else:
                    included.write_text("[core]\n\tfsmonitor\n", encoding="utf-8")
                    git(root, "config", "include.path", str(included))
                    expected = f"worktree is not clean: {refusal}core.fsmonitor"
                if variant not in ("true", "no value"):
                    # The hook is live: the old predicate's status ran it.
                    # (With true, that status would start the daemon.)
                    self.assertEqual(plain_status(root), "")
                    self.assertTrue(ran.exists())
                    ran.unlink()
                verdict = self.validate(fixture)
                self.assert_refused(verdict, expected)
                if variant == "no value":
                    self.assertIn(f"repository: {expected}", verdict["errors"])
                self.assertFalse(ran.exists(), ran.read_text() if ran.exists() else "")

    def test_promisor_remote_is_refused_before_any_object_is_read(self) -> None:
        # With a promisor remote configured, a Git command that needs an
        # object the store lacks starts a lazy `git fetch`, whose transport
        # runs what the remote's settings name: here a local remote's
        # uploadpack program, or an ext:: URL.  The raw-bytes comparison reads
        # no blob, so a store missing one passes it, and G1 reads its ledgers
        # with `git show <rev>:<path>` (the fixture G1 does too).  The gate
        # itself reads no object of such a repository -- on a Git that ignores
        # GIT_NO_LAZY_FETCH as well, simulated by dropping the variable.
        # Mounted variants: a missing blob of the root, a missing commit (the
        # partialClone extension), and a missing tree of a submodule.  The
        # last three name the promisor remote without a promisor key, and drop
        # only the blob the fixture G1 reads, so that nothing but the refusal
        # stops the gate accepting while G1's read runs the program: a
        # partialCloneFilter alone, which Git registers whatever its value,
        # and the remote "" that a remote.* key without a subsection names.
        def setup(root: Path) -> None:
            add_pinned_file(root)
            add_engine_submodule(root)
            inject_into_checker(root, "G1", G1_TRACKED_READ)

        refusal = (
            "a promisor remote makes a checker's Git fetch any object the store lacks, "
            "running the programs its transport settings name: "
        )
        for variant in (
            "missing blob", "missing commit", "submodule tree", "filter only",
            "unnamed remote", "unnamed filter",
        ):
            with self.subTest(variant):
                fixture = self.make_fixture(setup)
                root = fixture.root
                engine = root / ENGINE
                ran = root.parent / "fetch-ran"
                probe = ["git", "-C", str(root), "show", "HEAD:pinned.txt"]
                if variant == "missing blob":
                    arm_promisor(root, root.parent, ran)
                    for tracked in ("pinned.txt", gate.CHECKER_PATHS["G1"]):
                        drop_object(root, git(root, "rev-parse", f"HEAD:{tracked}").strip())
                    self.assertEqual(plain_status(root), "")
                    expected = f"{refusal}remote.cache.promisor=true"
                elif variant == "missing commit":
                    program = recording_program(root.parent / "ext-transport", ran)
                    git(root, "config", "extensions.partialClone", "cache")
                    git(root, "config", "remote.cache.url", f"ext::sh -c {program}% ext")
                    git(root, "config", "protocol.ext.allow", "always")
                    drop_object(root, fixture.source_revision)
                    probe = ["git", "-C", str(root), "cat-file", "-e", fixture.source_revision]
                    expected = f"{refusal}extensions.partialclone=cache"
                elif variant == "submodule tree":
                    arm_promisor(engine, root.parent, ran)
                    drop_object(engine, git(engine, "rev-parse", "HEAD^{tree}").strip())
                    probe = ["git", "-C", str(engine), "ls-tree", "HEAD"]
                    expected = f"submodule {ENGINE}: {refusal}remote.cache.promisor=true"
                else:
                    if variant == "filter only":
                        naming = ("remote.cache.partialCloneFilter", "blob:none")
                        arm_promisor(root, root.parent, ran, naming)
                        expected = f"{refusal}remote.cache.partialclonefilter=blob:none"
                    elif variant == "unnamed remote":
                        arm_unnamed_promisor(root, root.parent, ran, ("remote.promisor", "true"))
                        expected = f"{refusal}remote.promisor=true"
                    else:
                        naming = ("remote.partialCloneFilter", "false")
                        arm_unnamed_promisor(root, root.parent, ran, naming)
                        expected = f"{refusal}remote.partialclonefilter=false"
                    drop_object(root, git(root, "rev-parse", "HEAD:pinned.txt").strip())
                    self.assertEqual(plain_status(root), "")
                # The fetch is live: the candidate's own Git runs it.
                subprocess.run(
                    probe, check=False, capture_output=True,
                    env={k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
                )
                self.assertTrue(ran.exists())
                ran.unlink()
                with patch.object(gate, "_git_env", side_effect=git_without_lazy_fetch_guard):
                    verdict = self.validate(fixture)
                self.assert_refused(verdict, expected)
                self.assertFalse(ran.exists(), ran.read_text() if ran.exists() else "")
                if variant == "missing blob" and git_version() >= (2, 45):
                    # Git 2.45 honors GIT_NO_LAZY_FETCH, which the gate sets.
                    gate._git_run(root, "show", "HEAD:pinned.txt")
                    self.assertFalse(ran.exists())

    def test_false_fsmonitor_and_promisor_settings_are_not_refused(self) -> None:
        # Git reads each of these spellings as false, so none starts a program;
        # nor do the remote section's other keys, with or without a subsection.
        fixture = self.make_fixture()
        root = fixture.root
        for spelling in ("false", "No", "OFF", "0", ""):
            git(root, "config", "--add", "core.fsmonitor", spelling)
        git(root, "config", "remote.cache.url", str(root.parent / "absent"))
        git(root, "config", "remote.cache.promisor", "false")
        git(root, "config", "remote.pushDefault", "cache")
        self.assertEqual(gate.worktree_refusals(root), [])
        self.assertTrue(self.validate(fixture)["accepted"])

    def test_many_differing_files_stop_conversion_early(self) -> None:
        # Past the first batch that decides the refusal, differing files are
        # counted and named as not examined rather than converted one by one.
        count = gate.CONVERSION_BATCH + 6

        def setup(root: Path) -> None:
            add_pinned_file(root)
            (root / "bulk").mkdir()
            for number in range(count):
                (root / "bulk" / f"{number:03}.txt").write_text("pinned\n", encoding="utf-8")

        fixture = self.make_fixture(setup)
        for number in range(count):
            (fixture.root / "bulk" / f"{number:03}.txt").write_text("forged\n", encoding="utf-8")
        verdict = self.validate(fixture)
        self.assert_refused(
            verdict,
            "raw worktree bytes differ from HEAD's checkout: bulk/000.txt, bulk/001.txt, "
            f"bulk/002.txt (+{gate.CONVERSION_BATCH - 3} more)",
            "raw worktree bytes differ from HEAD's blob (not examined for a checkout "
            f"conversion once the refusal was decided): bulk/{gate.CONVERSION_BATCH:03}.txt",
        )

    def test_operator_global_and_xdg_git_config_cannot_hide_untracked_files(self) -> None:
        fixture = self.make_fixture()
        (fixture.root / "dirty.txt").write_text("untracked candidate input\n", encoding="utf-8")
        hide = fixture.root.parent / "hide-dirty"
        hide.write_text("dirty.txt\n", encoding="utf-8")
        home = fixture.root.parent / "operator-home"
        home.mkdir()
        (home / ".gitconfig").write_text(f"[core]\n\texcludesFile = {hide}\n", encoding="utf-8")
        xdg = fixture.root.parent / "operator-xdg"
        (xdg / "git").mkdir(parents=True)
        (xdg / "git" / "ignore").write_text("dirty.txt\n", encoding="utf-8")
        empty_home = fixture.root.parent / "empty-home"
        empty_home.mkdir()
        for environment in (
            {"HOME": str(home), "XDG_CONFIG_HOME": str(fixture.root.parent / "absent")},
            {"HOME": str(empty_home), "XDG_CONFIG_HOME": str(xdg)},
        ):
            with patch.dict(os.environ, environment):
                self.assertEqual(plain_status(fixture.root), "")
                verdict = self.validate(fixture)
            self.assert_refused(verdict, "git status reports changes: ?? dirty.txt")

    def test_post_run_check_applies_the_same_predicate(self) -> None:
        # A checker that rewrites a pinned file while it runs and hides the
        # rewrite from `git status` must still fail the post-run check.
        def setup(root: Path) -> None:
            add_pinned_file(root)
            tamper = (
                "import subprocess\n"
                "(root / 'pinned.txt').write_text('rewritten by a checker\\n', encoding='utf-8')\n"
                "subprocess.run(['git', '-C', str(root), 'update-index', '--skip-worktree',"
                " 'pinned.txt'], check=True)\n"
            )
            checker = root / gate.CHECKER_PATHS["G1"]
            source = checker_source("G1")
            anchor = "print(json.dumps(verdict))"
            self.assertIn(anchor, source)
            checker.write_text(source.replace(anchor, tamper + anchor), encoding="utf-8")

        fixture = self.make_fixture(setup)
        verdict = self.validate(fixture)
        self.assertEqual(plain_status(fixture.root), "")
        self.assertTrue(all(verdict["gate_results"].values()), verdict["errors"])
        self.assertFalse(any(error.startswith("repository:") for error in verdict["errors"]))
        self.assert_refused(
            verdict,
            "post_run_integrity: worktree became dirty during checker execution: "
            "skip-worktree index entries hide their worktree files: pinned.txt",
        )

    def test_case_aliased_owner_key_inside_root_is_refused(self) -> None:
        fixture = self.make_fixture()
        alias = self.case_alias(fixture)
        shutil.copyfile(fixture.owner_public, fixture.evidence_dir / "owner.pub")
        aliased_key = alias / fixture.evidence_dir.name / "owner.pub"
        self.assertTrue(self.validate(fixture)["accepted"])
        self.assert_refused(
            self.validate(fixture, aliased_key),
            "trusted owner key must be outside the candidate repository",
        )

    def test_case_aliased_running_verifier_inside_root_is_refused(self) -> None:
        fixture = self.make_fixture()
        alias = self.case_alias(fixture)
        process = subprocess.run(
            [
                sys.executable,
                str(alias / fixture.candidate_top.relative_to(fixture.root)),
                "--candidate-verifier",
                fixture.candidate_top.relative_to(fixture.root).as_posix(),
                "--receipt",
                str(fixture.path),
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

    def test_symlink_loop_paths_are_recorded_not_raised(self) -> None:
        fixture = self.make_fixture()
        loop = fixture.evidence_dir / "loop.json"
        loop.symlink_to(loop.name)
        fixture.receipt["toolchain_manifest"] = {
            "path": loop.relative_to(fixture.root).as_posix(),
            "sha256": "0" * 64,
        }
        fixture.write_receipt()
        # A real loop: Python 3.9's pathlib raises RuntimeError on it.
        self.assert_refused(self.validate(fixture), "receipt.toolchain_manifest.path")

        # The same RuntimeError on every interpreter, at every resolve() site.
        symlink_loop = RuntimeError(f"Symlink loop from {str(loop)!r}")
        validator = gate.ReceiptValidator(fixture.root, fixture.path, fixture.owner_public)
        with patch.object(gate.Path, "resolve", side_effect=symlink_loop):
            self.assertIsNone(validator.resolve_ref(
                {"path": "evidence/loop.json", "sha256": "0" * 64}, "artifact"
            ))
            constructed = gate.ReceiptValidator(fixture.root, fixture.path, fixture.owner_public)
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr), self.assertRaises(SystemExit) as exited:
                gate.main([
                    "--receipt", str(fixture.path), "--root", str(fixture.root),
                    "--candidate-verifier", "scripts/two_language_completion_gate.py",
                    "--trusted-owner-key", str(fixture.owner_public),
                ])
        self.assertTrue(
            any("artifact.path: cannot resolve path: Symlink loop" in error
                for error in validator.errors),
            validator.errors,
        )
        self.assertTrue(
            any("--root cannot be resolved: Symlink loop" in error
                for error in constructed.errors),
            constructed.errors,
        )
        self.assertEqual(exited.exception.code, 2)
        self.assertIn("--root cannot be resolved: Symlink loop", stderr.getvalue())

    def test_resolve_sites_survive_a_deleted_working_directory(self) -> None:
        here = os.getcwd()
        doomed = tempfile.mkdtemp(prefix="two-language-gate-cwd-")
        try:
            os.chdir(doomed)
            os.rmdir(doomed)
            resolved, problem = gate._resolved(Path("receipt.json"))
            validator = gate.ReceiptValidator(
                Path("repo"), Path("receipt.json"), Path("owner.pub")
            )
        finally:
            os.chdir(here)
        self.assertEqual(resolved, Path("receipt.json"))
        self.assertIsNotNone(problem)
        self.assertTrue(
            any(error.startswith("repository: --root cannot be resolved")
                for error in validator.errors),
            validator.errors,
        )

    def test_missing_owner_key_outside_root_is_reported_missing(self) -> None:
        fixture = self.make_fixture()
        missing = fixture.root.parent / "absent-owner.pub"
        verdict = self.validate(fixture, missing)
        self.assert_refused(verdict, f"trusted owner key does not exist: {missing.resolve()}")
        self.assertFalse(
            any("must be outside" in error for error in verdict["errors"]), verdict["errors"]
        )

    def test_root_path_holding_a_newline_is_inspected(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="two-language-gate-")
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name) / "new\nline"
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        git(root, "config", "user.email", "gate@test.invalid")
        git(root, "config", "user.name", "gate-test")
        add_pinned_file(root)
        git(root, "add", "pinned.txt")
        git(root, "commit", "-q", "-m", "pinned")
        self.assertEqual(gate.worktree_refusals(root), [])

    def test_clean_checkout_with_submodule_conversion_and_build_dir_is_accepted(self) -> None:
        # The measured shape of the real repository: an initialized submodule at
        # its pin, a file the committed .gitattributes checks out with CRLF, an
        # ignored build/ tree full of generated files, ignored files in an
        # otherwise untracked directory (listed one by one), an empty untracked
        # directory (nothing to report), and --root reached through a symlink.
        def setup(root: Path) -> None:
            self.commit_crlf_checkout(root)
            add_engine_submodule(root)
            with (root / ".gitignore").open("a", encoding="utf-8") as ignore:
                ignore.write("build/\n*.pyc\n")

        fixture = self.make_fixture(setup)
        (fixture.root / "crlf.txt").unlink()
        git(fixture.root, "checkout", "--", "crlf.txt")
        self.assertEqual((fixture.root / "crlf.txt").read_bytes(), b"checked out\r\nwith CRLF\r\n")
        self.assertTrue((fixture.root / ENGINE / ".git").is_file())
        build = fixture.root / "build" / "two-language-completion"
        build.mkdir(parents=True)
        (build / "artifact.bin").write_bytes(b"generated\n")
        (fixture.root / "scripts" / "__pycache__").mkdir()
        (fixture.root / "scripts" / "__pycache__" / "cached.pyc").write_bytes(b"\0cached\n")
        (fixture.root / "notes").mkdir()
        self.assertEqual(plain_status(fixture.root), "")
        verdict = self.validate(fixture)
        self.assertTrue(verdict["accepted"], verdict["errors"])
        linked_root = fixture.root.parent / "linked-root"
        linked_root.symlink_to(fixture.root)
        verdict = gate.validate_receipt(fixture.path, linked_root, fixture.owner_public)
        self.assertTrue(verdict["accepted"], verdict["errors"])


class CheckerProcessTests(unittest.TestCase):
    """A checker runs the pinned code and starts only what that code names.

    The clean-tree predicate permits ignored files, __pycache__ among them,
    and the checkers run Git with the candidate's own configuration (whose
    program-starting settings the predicate refuses; see the tests above).
    These tests cover the interpreter each checker runs in, and the Git
    commands the real checkers run.
    """

    def make_fixture(self, before_commit: Callable[[Path], None]) -> GreenReceipt:
        temporary = tempfile.TemporaryDirectory(prefix="two-language-gate-")
        self.addCleanup(temporary.cleanup)
        return GreenReceipt(Path(temporary.name), before_commit=before_commit)

    def test_checker_loads_no_bytecode_from_the_tree(self) -> None:
        # The G3 scorecard replay imports rust_instance_census by file path,
        # and CPython loads a module imported that way from the __pycache__
        # beside it: an unchecked-hash .pyc there runs without being compared
        # to the source, and the repository ignores __pycache__.  The fixture
        # G1 imports a tracked module the same way; the genuine module refuses,
        # the planted bytecode would accept (and record that it ran).
        def setup(root: Path) -> None:
            add_pinned_file(root)
            with (root / ".gitignore").open("a", encoding="utf-8") as ignore:
                ignore.write("__pycache__/\n")
            (root / "scripts" / "tree_helper.py").write_text("ACCEPT = False\n", encoding="utf-8")
            inject_into_checker(
                root,
                "G1",
                "import importlib.util\n"
                "_spec = importlib.util.spec_from_file_location(\n"
                "    'tree_helper', str(root / 'scripts' / 'tree_helper.py'))\n"
                "_helper = importlib.util.module_from_spec(_spec)\n"
                "_spec.loader.exec_module(_helper)\n"
                "passed = passed and _helper.ACCEPT is True\n",
            )

        fixture = self.make_fixture(setup)
        root = fixture.root
        genuine_refusal = "G1.checker_verdict.passed: fresh checker verdict must be the boolean true"
        # The genuine module runs, and nothing is cached into the tree.
        verdict = gate.validate_receipt(fixture.path, root, fixture.owner_public)
        self.assertFalse(verdict["gate_results"]["G1"], verdict["errors"])
        self.assertIn(genuine_refusal, verdict["errors"])
        self.assertEqual(bytecode_in(root), set())

        ran = root.parent / "forged-bytecode-ran"
        planted = plant_bytecode(
            root / "scripts" / "tree_helper.py",
            f"import pathlib\npathlib.Path({str(ran)!r}).write_text('ran')\nACCEPT = True\n",
        )
        planted_bytes = planted.read_bytes()
        self.assertEqual(plain_status(root), "")
        verdict = gate.validate_receipt(fixture.path, root, fixture.owner_public)
        self.assertFalse(ran.exists())
        self.assertFalse(verdict["accepted"])
        self.assertFalse(any(error.startswith("repository:") for error in verdict["errors"]))
        self.assertIn(genuine_refusal, verdict["errors"])
        self.assertEqual(bytecode_in(root), {planted, planted.parent})
        self.assertEqual(planted.read_bytes(), planted_bytes)

    def test_checker_git_reads_fire_no_hook_and_write_no_index(self) -> None:
        # Candidate hooks are not refused -- this checkout sets
        # core.hooksPath=scripts/hooks -- because no Git command the checkers
        # run fires one: none writes a ref, and each passes
        # --no-optional-locks, so none writes the index (post-index-change)
        # either, even over stat data that no longer matches it.  Measured
        # with the real G1 and G2 checkers' own Git calls, every documented
        # hook installed in both repositories.
        def setup(root: Path) -> None:
            add_pinned_file(root)
            (root / "tests").mkdir()
            (root / "tests" / "case.rs").write_text("fn main() {}\n", encoding="utf-8")
            add_engine_submodule(root, CLEAN)

        fixture = self.make_fixture(setup)
        root = fixture.root.resolve()
        clean = root / CLEAN
        fired = root.parent / "hooks-fired"
        hooks = root.parent / "hooks"
        hooks.mkdir()
        for name in GIT_HOOKS:
            (hooks / name).write_text(f"#!/bin/sh\necho {name} >> '{fired}'\n", encoding="utf-8")
            (hooks / name).chmod(0o755)
        then = time.time_ns() - 1000 * 10**9
        indexes = []
        for repository, tracked in ((root, "pinned.txt"), (clean, "engine.txt")):
            git(repository, "config", "core.hooksPath", str(hooks))
            os.utime(repository / tracked, ns=(then, then))
            indexes.append(Path(
                git(repository, "rev-parse", "--path-format=absolute", "--git-path", "index").strip()
            ))
        index_bytes = [index.read_bytes() for index in indexes]
        revision = fixture.source_revision
        home = root.parent / "checker-home"
        home.mkdir()
        g1 = load_real_checker("G1")
        g2 = load_real_checker("G2")
        # A checker runs with the gate's environment: no operator Git config.
        with patch.dict(os.environ, {"HOME": str(home), "XDG_CONFIG_HOME": str(home)}):
            rust = g1.Context(SimpleNamespace(root=str(root), source_revision=revision))
            rust.tracked("pinned.txt")
            self.assertEqual(rust.git("cat-file", "-t", revision).strip(), b"commit")
            tree = rust.git("rev-parse", f"{revision}^{{tree}}").decode().strip()
            rust.git("cat-file", "tree", tree)
            rust.git("ls-tree", "-rz", "--name-only", revision, "--", "tests")
            lean = g2.Context(root, root / "p", "0" * 64, root / "c", "0" * 64, "0" * 64, revision)
            lean.clean_pin()
            lean.tree_files(["pinned.txt", f"{CLEAN}/engine.txt"])
        self.assertFalse(fired.exists(), fired.read_text() if fired.exists() else "")
        self.assertEqual([index.read_bytes() for index in indexes], index_bytes)
        # The hooks are live: a status that may take the index lock rewrites
        # the index and fires post-index-change. Enable optional locks only
        # for this fixture's positive control, regardless of the caller's
        # setting; the real checker calls above must remain read-only.
        with patch.dict(os.environ, {"GIT_OPTIONAL_LOCKS": "1"}):
            git(root, "status", "--porcelain")
        self.assertIn("post-index-change", fired.read_text())
        self.assertNotEqual(indexes[0].read_bytes(), index_bytes[0])

    def test_checker_git_readonly_control_covers_caller_optional_lock_modes(self) -> None:
        for setting in (None, "0", "1"):
            with self.subTest(optional_locks=setting), patch.dict(os.environ):
                if setting is None:
                    os.environ.pop("GIT_OPTIONAL_LOCKS", None)
                else:
                    os.environ["GIT_OPTIONAL_LOCKS"] = setting
                self.test_checker_git_reads_fire_no_hook_and_write_no_index()


def release_fifo(path: Path) -> None:
    """Unblock a process stuck opening the FIFO at ``path`` for reading."""
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_NONBLOCK)
    except OSError:
        return  # no reader is waiting on it
    os.close(descriptor)


def validate_in_child(fixture: GreenReceipt, settings: dict, timeout: float) -> dict:
    """``validate_receipt`` in a fresh interpreter with ``settings`` set on the gate.

    A child, so that a gate which blocks fails the test when ``timeout``
    expires instead of stalling the suite.
    """
    code = (
        "import importlib.util, json\n"
        f"spec = importlib.util.spec_from_file_location('gate', {str(SCRIPT)!r})\n"
        "gate = importlib.util.module_from_spec(spec)\n"
        "spec.loader.exec_module(gate)\n"
        f"for name, value in {settings!r}.items():\n"
        "    setattr(gate, name, value)\n"
        "print(json.dumps(gate.validate_receipt(\n"
        f"    {str(fixture.path)!r}, {str(fixture.root)!r}, {str(fixture.owner_public)!r})))\n"
    )
    process = subprocess.run(
        [sys.executable, "-I", "-B", "-c", code],
        capture_output=True, text=True, timeout=timeout,
    )
    assert process.returncode == 0, process.stderr
    return json.loads(process.stdout)


# A G1 checker that reports, for every required conjunct, the artifact its
# evidence names in "alias_path" -- as a checker echoing refs from
# candidate-authored evidence into its verdict does.
ECHO_ALIAS_PATH = (
    "_alias = bundle.get('alias_path')\n"
    "if _alias is not None:\n"
    "    _ref = {'path': _alias, 'sha256': digest(root / _alias)}\n"
    "    checks = [{'id': check_id, 'passed': True, 'artifacts': [_ref]} for check_id in REQUIRED]\n"
    "    passed = True\n"
)


class RunnerRobustnessTests(unittest.TestCase):
    """The runner itself: how it starts, and inputs that must be refused, not crash.

    A traceback or a hang is no verdict: every malformed, unreadable or
    blocking input below must yield the JSON refusal, and no alias of receipt
    metadata may pass as a conjunct's underlying evidence.
    """

    def make_fixture(
        self, before_commit: Callable[[Path], None] | None = None
    ) -> GreenReceipt:
        temporary = tempfile.TemporaryDirectory(prefix="two-language-gate-")
        self.addCleanup(temporary.cleanup)
        return GreenReceipt(Path(temporary.name), before_commit=before_commit)

    def validate(self, fixture: GreenReceipt) -> dict:
        return gate.validate_receipt(fixture.path, fixture.root, fixture.owner_public)

    def assert_refused(self, verdict: dict, *fragments: str) -> None:
        self.assertFalse(verdict["accepted"], verdict["errors"])
        for fragment in fragments:
            self.assertTrue(
                any(fragment in error for error in verdict["errors"]),
                f"{fragment!r} not in {verdict['errors']}",
            )

    def lock(self, directory: Path) -> None:
        """Take every permission from ``directory`` until the test ends."""
        if os.geteuid() == 0:
            self.skipTest("root ignores directory permissions")
        directory.chmod(0)
        self.addCleanup(directory.chmod, 0o755)

    def test_runner_isolates_itself_before_any_import_searches_its_directory(self) -> None:
        # Without -I, sys.path[0] is the runner's own directory: for a copy in
        # the candidate its scripts/, where the repository ignores a sourceless
        # .pyc.  `from __future__ import annotations` was the first import
        # searched there, json the next.  Neither planted module may run, and
        # the re-executed runner keeps argv, output and exit status.
        temporary = tempfile.TemporaryDirectory(prefix="two-language-gate-")
        self.addCleanup(temporary.cleanup)
        base = Path(temporary.name)
        scripts = base / "scripts"
        scripts.mkdir()
        runner = scripts / SCRIPT.name
        runner.write_bytes(SCRIPT.read_bytes())
        ran = base / "planted-module-ran"
        for module in ("__future__", "json"):
            payload = base / f"{module}_payload.py"
            payload.write_text(
                f"with open({str(ran)!r}, 'a') as log:\n    log.write({module!r} + '\\n')\n",
                encoding="utf-8",
            )
            py_compile.compile(str(payload), cfile=str(scripts / f"{module}.pyc"), doraise=True)
        receipt = str(base.resolve() / "absent  receipt.json")
        outputs = []
        for argv, status in (
            (["--receipt", receipt, "--root", str(base), "--text"], 1),
            (["--receipt", receipt, "--root", str(base)], 1),
            (["--unknown-option"], 2),
        ):
            with self.subTest(argv=argv):
                plain, isolated = (
                    subprocess.run(
                        [sys.executable, *flags, str(runner), *argv],
                        cwd=scripts, capture_output=True, text=True, timeout=120,
                    )
                    for flags in ((), ("-I", "-B"))
                )
                self.assertFalse(ran.exists(), ran.read_text() if ran.exists() else "")
                self.assertEqual(isolated.returncode, status, isolated)
                self.assertEqual(
                    (plain.returncode, plain.stdout, plain.stderr),
                    (isolated.returncode, isolated.stdout, isolated.stderr),
                )
                outputs.append(plain.stdout)
        self.assertIn(f"No such file or directory: '{receipt}'", outputs[0])
        self.assertIn("G1: INCOMPLETE", outputs[0])
        self.assertFalse(json.loads(outputs[1])["accepted"])
        # One re-execution at most: an interpreter that did not honor -I -B
        # (here: the marker the re-execution sets, without them) is refused.
        refused = subprocess.run(
            [sys.executable, str(runner), "--receipt", receipt, "--root", str(base)],
            cwd=scripts, capture_output=True, text=True, timeout=120,
            env={**os.environ, "TRUST_COMPLETION_GATE_ISOLATED": "1"},
        )
        self.assertEqual(refused.returncode, 1, refused)
        self.assertIn("cannot start an isolated (-I -B) interpreter", refused.stderr)
        self.assertEqual(refused.stdout, "")
        self.assertFalse(ran.exists())

    def test_paths_that_cannot_be_stat_ed_are_refused_not_raised(self) -> None:
        # Python 3.9's pathlib is_file() and is_symlink() raise every OSError
        # but ENOENT, ENOTDIR, EBADF and ELOOP.
        fixture = self.make_fixture()
        fixture.receipt["toolchain_manifest"] = {
            "path": "evidence/" + "a" * 300, "sha256": "0" * 64,
        }
        fixture.write_receipt()
        self.assert_refused(
            self.validate(fixture),
            "receipt.toolchain_manifest.path: cannot stat evidence/aaaa",
            "File name too long",
        )

        fixture = self.make_fixture()
        locked = fixture.evidence_dir / "locked"
        locked.mkdir()
        write_json(locked / "toolchain.json", {})
        fixture.receipt["toolchain_manifest"] = {
            "path": "evidence/locked/toolchain.json", "sha256": "0" * 64,
        }
        fixture.write_receipt()
        self.lock(locked)
        self.assert_refused(
            self.validate(fixture),
            "receipt.toolchain_manifest.path: cannot stat evidence/locked/toolchain.json: "
            "[Errno 13] Permission denied",
        )

        fixture = self.make_fixture()
        self.lock(fixture.root / "scripts" / "completion_gates")
        self.assert_refused(
            self.validate(fixture),
            "repository: worktree is not clean",
            "receipt.gates.G1.checker_sha256: schema-owned checker cannot be stat'ed: "
            "[Errno 13] Permission denied",
        )

    def test_malformed_values_in_membership_tests_are_refused_not_raised(self) -> None:
        # A JSON list or object where a string belongs is unhashable, and a
        # number where a list belongs cannot be searched; a string where a
        # list belongs would be searched for a substring.
        def subject(mutate: Callable[[dict], None]) -> Callable[[GreenReceipt], None]:
            def apply(fixture: GreenReceipt) -> None:
                graph = json.loads(fixture.subject_graph.read_text(encoding="utf-8"))
                mutate(graph["programs"][0])
                write_json(fixture.subject_graph, graph)
                fixture.receipt["subject_graph"] = fixture.ref(fixture.subject_graph)
                fixture.write_receipt()
            return apply

        def contract(role: str, mutate: Callable[[dict], None]) -> Callable[[GreenReceipt], None]:
            def apply(fixture: GreenReceipt) -> None:
                path = fixture.root / fixture.contract_refs[role]["path"]
                value = json.loads(path.read_text(encoding="utf-8"))
                mutate(value)
                write_json(path, value)
            return apply

        def ledger(fixture: GreenReceipt) -> None:
            path = fixture.evidence_dir / "rust-exceptions.json"
            value = json.loads(path.read_text(encoding="utf-8"))
            value["rows"] = [
                {"entry_id": [], "classification": "non-applicable-harness", "reason": "x"}
            ]
            write_json(path, value)

        def receipt_digest(field: str, digest: object) -> Callable[[GreenReceipt], None]:
            def apply(fixture: GreenReceipt) -> None:
                fixture.receipt[field] = {"path": fixture.receipt[field]["path"], "sha256": digest}
                fixture.write_receipt()
            return apply

        def set_field(row: str, field: str, value: object) -> Callable[[dict], None]:
            return lambda program: program[row][0].__setitem__(field, value)

        def grades(value: object) -> Callable[[dict], None]:
            return lambda contract: contract["kernels"][0].__setitem__("proof_grades", value)

        cases = (
            (subject(set_field("bodies", "language", [])),
             ".bodies[0].language: must be 'rust' or 'lean'"),
            (subject(set_field("call_edges", "value_category", {})),
             ".call_edges[0].value_category: is not a supported category"),
            (subject(set_field("obligations", "module_id", [])),
             ".obligations[0].module_id: must name the owning admitted module"),
            (subject(set_field("proof_certificates", "module_id", {})),
             ".proof_certificates[0].module_id: must name the owning admitted module"),
            (contract("obligations", lambda value: value["rules"][0].__setitem__("class", [])),
             "authority_contracts.obligations.rules[0].class: is not a required obligation class"),
            (ledger, ".exception_ledger.rows[0].entry_id: must uniquely name"),
            (receipt_digest("linked_module", []),
             "receipt.linked_module: must name a typed module artifact"),
            (receipt_digest("release_artifact", {}),
             "receipt.release_artifact: must name a typed linked executable"),
            (contract("proof_authority", grades(7)),
             ".proof_certificates[0].proof_grade: must be an owner-authorized proof grade"),
            (contract("proof_authority", grades("kernel-checked")),
             ".proof_certificates[0].proof_grade: must be an owner-authorized proof grade"),
        )
        for mutate, fragment in cases:
            with self.subTest(fragment):
                fixture = self.make_fixture()
                mutate(fixture)
                self.assert_refused(self.validate(fixture), fragment)

    def test_git_blocked_on_a_candidate_fifo_is_timed_out(self) -> None:
        # Git opens an untracked .gitignore in every directory it walks, and
        # every included configuration file, with a blocking open.  Each case
        # shortens only the bound on the commands that block.
        def untracked_gitignore(fixture: GreenReceipt) -> Path:
            return fixture.root / "scripts" / ".gitignore"

        def included_config(fixture: GreenReceipt) -> Path:
            fifo = fixture.root.parent / "included.config"
            git(fixture.root, "config", "include.path", str(fifo))
            return fifo

        for plant, settings, fragment in (
            (untracked_gitignore, {"GIT_TIMEOUT": 3},
             "repository: worktree is not clean: cannot inspect worktree state: git exited "
             "124: timed out after 3 s"),
            (included_config, {"GIT_QUICK_TIMEOUT": 3},
             "repository: --root is not a readable Git worktree: git exited 124: "
             "timed out after 3 s"),
        ):
            with self.subTest(plant.__name__):
                fixture = self.make_fixture()
                fifo = plant(fixture)
                os.mkfifo(fifo)
                self.addCleanup(release_fifo, fifo)
                self.assert_refused(validate_in_child(fixture, settings, timeout=90), fragment)

    def test_receipt_that_is_not_a_regular_file_is_refused_without_blocking(self) -> None:
        fixture = self.make_fixture()
        fixture.path.unlink()
        os.mkfifo(fixture.path)
        self.addCleanup(release_fifo, fixture.path)
        process = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--receipt", str(fixture.path),
             "--root", str(fixture.root), "--trusted-owner-key", str(fixture.owner_public)],
            capture_output=True, text=True, timeout=60,
        )
        self.assertEqual(process.returncode, 1, process)
        self.assert_refused(
            json.loads(process.stdout), "receipt: cannot read JSON", "not a regular file"
        )

    def test_head_tree_of_any_depth_is_refused_not_raised(self) -> None:
        # HEAD's tree is the candidate's: a legal commit may hold one file
        # thousands of directories deep with nothing checked out, and every
        # directory on its path is looked up before the file.
        temporary = tempfile.TemporaryDirectory(prefix="two-language-gate-")
        self.addCleanup(temporary.cleanup)
        deep = b"/".join([b"deep", *[b"a"] * 5000, b"f"])
        refusals: list[str] = []
        submodules = gate._CheckoutInspection().compare_tree(
            Path(temporary.name), refusals.append, [(b"100644", "0" * 40, deep)], "0" * 40, {}
        )
        self.assertEqual(submodules, [])
        self.assertEqual(len(refusals), 1, refusals)
        self.assertTrue(
            refusals[0].startswith("HEAD entries are missing from the worktree: deep/a/a/"),
            refusals[0][:100],
        )

    def test_conjunct_artifact_cannot_alias_receipt_metadata(self) -> None:
        # The checker reports what its evidence names; only an artifact that is
        # neither a metadata path, nor the same file, nor the same bytes passes.
        def echoing_checker(root: Path) -> None:
            inject_into_checker(root, "G1", ECHO_ALIAS_PATH)

        def genuine(fixture: GreenReceipt) -> str:
            write_json(fixture.evidence_dir / "underlying.json", {"underlying": True})
            return "evidence/underlying.json"

        def exact(fixture: GreenReceipt) -> str:
            return "evidence/toolchain.json"

        def case_alias(fixture: GreenReceipt) -> str:
            alias = fixture.evidence_dir / "TOOLCHAIN.json"
            if not alias.exists():
                self.skipTest("TMPDIR is case-sensitive, so no case alias exists")
            return "evidence/TOOLCHAIN.json"

        def hard_link(fixture: GreenReceipt) -> str:
            os.link(fixture.toolchain, fixture.evidence_dir / "toolchain-link.json")
            return "evidence/toolchain-link.json"

        def copy(fixture: GreenReceipt) -> str:
            shutil.copyfile(fixture.toolchain, fixture.evidence_dir / "toolchain-copy.json")
            return "evidence/toolchain-copy.json"

        def copy_of_receipt(fixture: GreenReceipt) -> str:
            # The receipt is rewritten below, so this copy is of its final bytes.
            return "evidence/receipt-copy.json"

        for name in (genuine, exact, case_alias, hard_link, copy, copy_of_receipt):
            with self.subTest(name.__name__):
                fixture = self.make_fixture(echoing_checker)
                alias = name(fixture)
                evidence = json.loads(fixture.evidence_path("G1").read_text(encoding="utf-8"))
                evidence["alias_path"] = alias
                fixture.rewrite_evidence("G1", evidence)
                if name is copy_of_receipt:
                    shutil.copyfile(fixture.path, fixture.root / alias)
                verdict = self.validate(fixture)
                if name is genuine:
                    self.assertTrue(verdict["accepted"], verdict["errors"])
                    continue
                self.assert_refused(
                    verdict,
                    "G1.checker_verdict.checks[0].artifacts[0].path: "
                    "must bind underlying evidence, not receipt metadata",
                )
                self.assertFalse(verdict["gate_results"]["G1"])

    def test_common_artifacts_and_evidence_must_be_distinct_files(self) -> None:
        fixture = self.make_fixture()
        link = fixture.evidence_dir / "linked-alias.trustir"
        os.link(fixture.linked_module, link)
        fixture.receipt["release_artifact"] = fixture.ref(link)
        fixture.write_receipt()
        self.assert_refused(
            self.validate(fixture),
            "receipt: all common bound artifacts must use distinct paths",
        )

        fixture = self.make_fixture()
        link = fixture.evidence_dir / "G2-alias.json"
        os.link(fixture.evidence_path("G1"), link)
        fixture.receipt["gates"]["G2"]["evidence"] = fixture.ref(link)
        fixture.write_receipt()
        self.assert_refused(
            self.validate(fixture),
            "receipt.gates.G2.evidence.path: evidence receipts must be distinct",
        )

    def test_semantic_definitions_must_be_distinct_files(self) -> None:
        # resolve() canonicalizes a symlink but neither a hard link nor a case
        # alias on a case-insensitive volume: each would bind one definition
        # file under two semantic roles.  A copy is a distinct file.
        def hard_link(source: Path) -> Path:
            link = source.with_name("semantics-alias.def")
            os.link(source, link)
            return link

        def case_alias(source: Path) -> Path:
            alias = source.with_name(source.name.upper())
            if not alias.exists():
                self.skipTest("TMPDIR is case-sensitive, so no case alias exists")
            return alias

        def symlink(source: Path) -> Path:
            link = source.with_name("semantics-alias.def")
            link.symlink_to(source.name)
            return link

        def copy(source: Path) -> Path:
            duplicate = source.with_name("semantics-copy.def")
            shutil.copyfile(source, duplicate)
            return duplicate

        refusal = (
            "authority_contracts.semantics.definitions.rust_language.path: "
            "semantic paths must be distinct"
        )
        for spell in (hard_link, case_alias, symlink, copy):
            with self.subTest(spell.__name__):
                fixture = self.make_fixture()
                contract_path = fixture.root / fixture.contract_refs["semantics"]["path"]
                contract = json.loads(contract_path.read_text(encoding="utf-8"))
                definitions = contract["definitions"]
                source = fixture.root / definitions["rust_language"]["path"]
                # Roles are checked in sorted order, so lean_language binds the
                # file first and rust_language is refused as its duplicate.
                definitions["lean_language"] = {
                    "id": definitions["lean_language"]["id"],
                    **fixture.ref(spell(source)),
                }
                write_json(contract_path, contract)
                errors = self.validate(fixture)["errors"]
                if spell is copy:
                    self.assertNotIn(refusal, errors)
                else:
                    self.assertIn(refusal, errors)

    def test_refused_checkout_executes_no_checker(self) -> None:
        # A checker taken from a refused checkout is the working tree's, not
        # the accepted commit's: the receipt is refused already, so running it
        # would execute candidate code for no verdict.
        fixture = self.make_fixture()
        (fixture.root / "source.txt").write_text("rewritten\n", encoding="utf-8")
        with patch.object(
            gate.ReceiptValidator,
            "run_checker",
            side_effect=AssertionError("a checker ran for a refused checkout"),
        ) as run_checker:
            verdict = self.validate(fixture)
        run_checker.assert_not_called()
        self.assert_refused(
            verdict,
            "repository: worktree is not clean",
            *(
                f"{gate_id}.checker_run: checker not run: the checkout was refused"
                for gate_id in gate.GATES[:-1]
            ),
            "G8.checker_run: G1-G7 must pass before the G8 seal checker runs",
        )
        self.assertEqual(verdict["gate_results"], {gate_id: False for gate_id in gate.GATES})
        self.assertIsNone(verdict["prior_gates_root"])
        self.assertEqual(verdict["result"], "incomplete")

    def test_authority_policy_that_cannot_be_read_is_refused_not_raised(self) -> None:
        fixture = self.make_fixture()
        directory = fixture.evidence_dir / "policy-directory"
        directory.mkdir()
        fixture.receipt["authority_policy"] = {
            "path": "evidence/policy-directory", "sha256": "0" * 64,
        }
        fixture.write_receipt()
        self.assert_refused(
            self.validate(fixture),
            "receipt.authority_policy.path: file does not exist: evidence/policy-directory",
            "policy_authorization: cannot read the authority policy",
        )

        if os.geteuid() == 0:
            self.skipTest("root reads a file without read permission")
        fixture = self.make_fixture()
        fixture.policy.chmod(0)
        self.addCleanup(fixture.policy.chmod, 0o644)
        self.assert_refused(
            self.validate(fixture),
            "policy_authorization: cannot read the authority policy: "
            "[Errno 13] Permission denied",
        )


if __name__ == "__main__":
    unittest.main()
