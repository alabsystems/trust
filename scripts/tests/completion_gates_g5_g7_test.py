#!/usr/bin/env python3
"""Controls for the G5 and G7 schema-owned gate checkers.

Each checker is driven EXACTLY as ``scripts/two_language_completion_gate.py``
drives it — a read-only snapshot, ``python -I``, the sandbox environment, the
full argv — against a temp root.  The synthetic G5 bundle deliberately has
plausible, hash-bound but unauthenticated claims.  It must stay red on every
conjunct; independent mutations still exercise each structural diagnostic.
The Rust-to-Clean sidecar mirrors the real compiler's narrow same-crate shape.
The synthetic G7 bundle uses the runner's named signed-contract reference and
must also stay red; shape mutations remain independently observable.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GATES_DIR = ROOT / "scripts" / "completion_gates"
CHECKERS = {
    "G5": GATES_DIR / "check_g5_mixed_linking.py",
    "G7": GATES_DIR / "check_g7_codegen_authority.py",
}
CHECKER_IDS = {
    "G5": "trust.two-language.g5.mixed-linking/v2",
    "G7": "trust.two-language.g7.codegen-authority/v3",
}
REQUIRED = {
    "G5": (
        "rust_to_lean_typed_link",
        "lean_to_rust_typed_link",
        "cross_crate_digest_rechecked_link",
        "proof_call_firewall",
        "typed_bidirectional_call_graph",
        "cross_language_value_category_matrix",
        "shared_abi_and_memory_model",
        "cross_crate_import_assumption_closure",
    ),
    "G7": (
        "exact_linked_module_is_codegen_input",
        "full_admitted_codegen_surface",
        "zero_unproved_fallbacks",
        "machine_equivalence_evidence",
        "objects_biject_admitted_modules",
        "authorized_codegen_matrix_complete",
        "typed_module_object_executable_lineage",
        "linked_executable_composition_validated",
        "runtime_startup_syslib_closure_bound",
    ),
}
VERDICT_KEYS = {
    "schema", "goal_id", "gate", "checker", "repository_id", "acceptance_run_id",
    "checker_sha256", "evidence_sha256", "source_revision", "toolchain_sha256",
    "corpus_manifest_sha256", "subject_graph_sha256", "linked_module_sha256",
    "release_artifact_sha256", "authority_policy_sha256", "policy_authorization_sha256",
    "prior_gates_root", "passed", "checks",
}
ZERO = "0" * 64


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class GateRoot:
    """A temp root holding artifacts, a bundle, and the runner-side inputs."""

    def __init__(self, gate: str) -> None:
        self.gate = gate
        self.tmp = tempfile.TemporaryDirectory(prefix=f"trust-{gate.lower()}-gate-")
        self.root = Path(self.tmp.name).resolve()
        (self.root / "evidence").mkdir()
        self.linked_module = self.root / "linked.trust-ir.bin"
        self.linked_module.write_bytes(b"TRUST_IR\x00linked-module-bytes")
        self.policy = self.root / "policy.json"
        self.policy.write_text(json.dumps(DEFAULT_POLICY), encoding="utf-8")
        for name in ("toolchain", "corpus", "subject-graph", "release", "policy-auth"):
            (self.root / f"{name}.json").write_text("{}", encoding="utf-8")
        self.artifacts: dict[str, dict[str, str]] = {}

    def write(self, check_id: str, document: dict | bytes, name: str | None = None) -> Path:
        data = document if isinstance(document, bytes) else json.dumps(document, indent=1).encode()
        path = self.root / "evidence" / (name or f"{check_id}.json")
        path.write_bytes(data)
        self.artifacts[check_id] = {"path": str(path.relative_to(self.root)), "sha256": sha256_bytes(data)}
        return path

    def bundle(self, **overrides) -> Path:
        doc = {
            "schema": "trust.two-language.gate-evidence/v1",
            "gate": self.gate,
            "checker": CHECKER_IDS[self.gate],
            "artifacts": dict(self.artifacts),
        }
        doc.update(overrides)
        path = self.root / "bundle.json"
        path.write_text(json.dumps(doc), encoding="utf-8")
        return path

    def run(self, bundle: Path, *, receipt: bool = False,
            evidence_sha256: str | None = None, timeout: float = 120) -> tuple[int, dict, str]:
        checker_bytes = CHECKERS[self.gate].read_bytes()
        snapshot = self.root / "checker.py"
        if snapshot.exists():
            snapshot.chmod(0o644)
        snapshot.write_bytes(checker_bytes)
        snapshot.chmod(0o444)
        command = [
            sys.executable, "-I", str(snapshot),
            "--verify-evidence", str(bundle), "--root", str(self.root),
            "--toolchain-manifest", str(self.root / "toolchain.json"),
            "--corpus-manifest", str(self.root / "corpus.json"),
            "--subject-graph", str(self.root / "subject-graph.json"),
            "--linked-module", str(self.linked_module),
            "--release-artifact", str(self.root / "release.json"),
            "--authority-policy", str(self.policy),
            "--policy-authorization", str(self.root / "policy-auth.json"),
            "--acceptance-run-id", "run-1", "--source-revision", "a" * 40,
            "--checker-sha256", sha256_bytes(checker_bytes),
            "--evidence-sha256", evidence_sha256 or sha256_bytes(bundle.read_bytes()),
            "--toolchain-sha256", ZERO, "--corpus-manifest-sha256", ZERO,
            "--subject-graph-sha256", ZERO,
            "--linked-module-sha256", sha256_bytes(self.linked_module.read_bytes()),
            "--release-artifact-sha256", ZERO,
            "--authority-policy-sha256", sha256_bytes(self.policy.read_bytes()),
            "--policy-authorization-sha256", ZERO,
        ]
        if receipt:
            command += ["--receipt", str(self.root / "receipt.json"), "--prior-gates-root", ZERO]
        env = {"HOME": self.tmp.name, "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
               "PATH": "/usr/bin:/bin", "PYTHONHASHSEED": "0", "TZ": "UTC"}
        process = subprocess.run(command, cwd=self.root, env=env, check=False,
                                 capture_output=True, text=True, timeout=timeout)
        verdict = json.loads(process.stdout)
        return process.returncode, verdict, process.stderr


DEFAULT_POLICY = {
    "schema": "trust.two-language.authority-policy/v2",
    "authority_contracts": {
        "codegen_surface": {
            "schema": "trust.two-language.codegen-surface-contract/v2",
            "goal_id": "TRUST-TWO-LANGUAGE-100",
            "repository_id": "https://github.com/alabsystems/trust",
            "translation_relation": {"id": "trust.two-language.relation.machine", "sha256": "0" * 64},
            "targets": [{
                "id": "aarch64-apple-darwin", "triple": "aarch64-apple-darwin",
                "abis": ["rust"], "crate_types": ["rlib", "bin"], "runtimes": ["std"],
                "startups": ["rustc-entry"], "linkers": ["ld64"], "unwind_modes": ["abort"],
                "debug_modes": ["none"], "opt_levels": ["0"], "profiles": ["dev"],
            }],
            "matrix_cells": [
                {"id": "cell-rlib", "target_id": "aarch64-apple-darwin", "abi_id": "rust",
                 "crate_type": "rlib", "runtime_id": "std", "startup_id": "rustc-entry",
                 "linker_id": "ld64", "unwind_mode": "abort", "debug_mode": "none",
                 "opt_level": "0", "profile_id": "dev"},
                {"id": "cell-bin", "target_id": "aarch64-apple-darwin", "abi_id": "rust",
                 "crate_type": "bin", "runtime_id": "std", "startup_id": "rustc-entry",
                 "linker_id": "ld64", "unwind_mode": "abort", "debug_mode": "none",
                 "opt_level": "0", "profile_id": "dev"},
            ],
        }
    },
}


# ── G5 authored artifacts (the coverage sidecar mirrors the run-make pin) ───

def coverage_sidecar() -> dict:
    return {
        "direct_obligation_capability": "obligation-bearing-pending-v2",
        "clean_origin": {
            "recorded": True,
            "emitted": [{
                "def_index": 7, "def_path": "m::cleanWsum", "clean_name": "cleanWsum",
                "shape": "wrapping-binop", "tier": "gate",
                "judgment": "actual-TrustIR-Function-carrier-defeq",
                "carrier_faithfulness": "established", "body_gate": "carrier-faithful",
                "func_id": 3, "gate_subject_digest": "sha256:" + "b" * 64,
                "gate_carrier": "UInt64", "gate_method": "definitional-equality",
                "gate_scope": "same-crate Rust-to-Clean link only; not G5 cross-crate and not G7 codegen",
            }],
            "skipped": [],
            # `type_unchecked` is spelled as both emitters in `clean_origin_join` spell it
            # (3b30328c07): present and EMPTY is the only typed link.  A row without it
            # predates the seam type guard and is refused right after the per-row
            # `refusals` check, before the edge, identity and tier rules run.
            "linked": [{
                "decl_key": "local-unlowered:m::cleanWsum", "decl_func_id": 2,
                "source_def_index": 7, "target_func_id": 3, "def_path": "m::cleanWsum",
                "edges_repointed": 1, "refusals": [], "type_unchecked": [],
            }],
            "general": [], "general_renamed": [],
        },
    }


def g5_authored(gr: GateRoot) -> None:
    gr.write("rust_to_lean_typed_link", coverage_sidecar(), "foo.trust-ir.coverage.json")
    gr.write("lean_to_rust_typed_link", {
        "schema": "trust.two-language.lean-to-rust-link/v1",
        "links": [{"clean_name": "callsRust", "rust_def_index": 12,
                   "rust_definition_identity": "t::h::00ff", "func_ty": "(u64) -> u64",
                   "verdict": "typed"}]})
    gr.write("cross_crate_digest_rechecked_link", {
        "schema": "trust.two-language.cross-crate-link/v1",
        "links": [{"importer_crate": "b", "exporter_crate": "a", "lane": "trust-ir",
                   "exporter_digest": "c" * 64, "importer_recheck": "re-earned"}]})
    gr.write("proof_call_firewall", {
        "schema": "trust.two-language.proof-call-firewall/v1",
        "checked_items": 3, "transitive": True, "violations": []})
    gr.write("typed_bidirectional_call_graph", {
        "schema": "trust.two-language.typed-call-graph/v1",
        "edges": [{"direction": "rust_to_lean", "caller_identity": "r1", "callee_identity": "c1", "func_ty": "(u8)->u8"},
                  {"direction": "lean_to_rust", "caller_identity": "c2", "callee_identity": "r2", "func_ty": "(u8)->u8"}]})
    gr.write("cross_language_value_category_matrix", {
        "schema": "trust.two-language.value-category-matrix/v1",
        "cells": {f"{c}/{d}": {"status": "crosses", "evidence": f"ev-{c}-{d}"}
                  for c in ("scalar", "aggregate", "reference", "error", "callback", "result")
                  for d in ("rust_to_lean", "lean_to_rust")}})
    gr.write("shared_abi_and_memory_model", {
        "schema": "trust.two-language.shared-abi-memory-model/v1",
        "abi_id": "rustcc", "memory_model_id": "trust-ir-mm-v1",
        "conforming_producers": ["Trust", "Clean"], "divergences": []})
    gr.write("cross_crate_import_assumption_closure", {
        "schema": "trust.two-language.import-assumption-closure/v1",
        "assumptions": [{"id": "a1", "status": "discharged",
                         "discharged_by": {"path": "x", "sha256": "d" * 64}}]})


# One independent mutation per G5 conjunct: (check id, mutate(document) -> document).
def _drop_link_refusal(doc):
    doc["clean_origin"]["linked"][0]["refusals"] = ["arity skew"]; return doc
def _demote_target(doc):
    doc["clean_origin"]["emitted"][0]["tier"] = "kernel-tv"; doc["clean_origin"]["emitted"][0]["body_gate"] = "ungated"; return doc
def _link_by_name_only(doc):
    doc["clean_origin"]["linked"][0]["target_func_id"] = 99; return doc
def _predate_seam_type_guard(doc):
    doc["clean_origin"]["linked"][0].pop("type_unchecked"); return doc
def _leave_operand_undecided(doc):
    doc["clean_origin"]["linked"][0]["type_unchecked"] = [
        "function `main`: argument 0 (Refine(U64, p) vs U64) NOT type-checked — a refinement"
        " — trust-ir decides refine-involving call edges in `validate_refinements`; the edge"
        " was re-pointed on arity and identity alone"]
    return doc

# Each Rust-to-Clean mutation must be refused by ITS rule, not by whichever rule runs
# first: a fixture that trips an earlier refusal makes every later mutation pass
# vacuously (the pre-fix fixture lacked `type_unchecked`, so `_demote_target` and
# `_link_by_name_only` did: the seam guard runs after the `refusals` check but before
# the edge, identity and tier rules).
RUST_TO_LEAN_REFUSALS = (
    (_drop_link_refusal, "carries refusals: ['arity skew']"),
    (_demote_target, "is at tier 'kernel-tv'; G5 requires tier `gate`"),
    (_link_by_name_only, "which is not an emitted row"),
    (_predate_seam_type_guard, "carries no `type_unchecked` key: it predates the seam type guard"),
    (_leave_operand_undecided, "left 1 operand position(s) undecided at the seam"),
)

G5_MUTATIONS = {
    "rust_to_lean_typed_link": [mutate for mutate, _ in RUST_TO_LEAN_REFUSALS],
    "lean_to_rust_typed_link": [lambda d: (d["links"][0].__setitem__("verdict", "by-name"), d)[1],
                                lambda d: (d.__setitem__("links", []), d)[1]],
    "cross_crate_digest_rechecked_link": [lambda d: (d["links"][0].__setitem__("lane", "mir"), d)[1],
                                          lambda d: (d["links"][0].__setitem__("importer_recheck", "trusted"), d)[1],
                                          lambda d: (d["links"][0].__setitem__("exporter_crate", "b"), d)[1]],
    "proof_call_firewall": [lambda d: (d.__setitem__("violations", ["proof item reachable from CALL"]), d)[1],
                            lambda d: (d.__setitem__("transitive", False), d)[1]],
    "typed_bidirectional_call_graph": [lambda d: (d.__setitem__("edges", d["edges"][:1]), d)[1],
                                       lambda d: (d["edges"][0].pop("func_ty"), d)[1]],
    "cross_language_value_category_matrix": [lambda d: (d["cells"].pop("callback/lean_to_rust"), d)[1],
                                             lambda d: (d["cells"]["error/rust_to_lean"].__setitem__("status", "planned"), d)[1]],
    "shared_abi_and_memory_model": [lambda d: (d.__setitem__("conforming_producers", ["Trust"]), d)[1],
                                    lambda d: (d.__setitem__("divergences", ["Nat boxing"]), d)[1]],
    "cross_crate_import_assumption_closure": [lambda d: (d["assumptions"][0].__setitem__("status", "open"), d)[1],
                                              lambda d: (d["assumptions"][0].__setitem__("discharged_by", {"path": "x", "sha256": "nope"}), d)[1]],
}


def sha(tag: str) -> str:
    return hashlib.sha256(tag.encode()).hexdigest()


def bind_codegen_contract(gr: GateRoot, contract: dict) -> Path:
    path = gr.root / "codegen-contract.json"
    path.write_text(json.dumps(contract), encoding="utf-8")
    gr.policy.write_text(json.dumps({
        "schema": DEFAULT_POLICY["schema"],
        "contracts": {"codegen_surface": {
            "id": "trust.two-language.contract.codegen-surface",
            "path": path.name,
            "sha256": sha256_bytes(path.read_bytes()),
        }},
    }), encoding="utf-8")
    return path


def g7_authored(gr: GateRoot) -> None:
    bind_codegen_contract(gr, DEFAULT_POLICY["authority_contracts"]["codegen_surface"])
    linked = sha256_bytes(gr.linked_module.read_bytes())
    receipt = {
        "schema": "trust.two-language.codegen-receipt/v1", "frontend": "trust-ir",
        "linked_module_sha256": linked, "admitted_functions": ["main", "m::cleanWsum"],
        "objects": [{"path": "out/a.o", "sha256": sha("obj-a"), "module_id": "crate-a",
                     "functions": ["main", "m::cleanWsum"]}],
        "refusals": [], "fallbacks": 0, "output_gate": "on",
    }
    for check_id in ("exact_linked_module_is_codegen_input", "full_admitted_codegen_surface", "zero_unproved_fallbacks"):
        gr.write(check_id, receipt, f"{check_id}.receipt.json")
    gr.write("machine_equivalence_evidence", {
        "schema": "trust.two-language.machine-equivalence/v1",
        "functions": [{"name": "main", "object_sha256": sha("obj-a"), "verdict": "preserved", "method": "proven-output"},
                      {"name": "m::cleanWsum", "object_sha256": sha("obj-a"), "verdict": "preserved", "method": "translation-validation"}]})
    gr.write("objects_biject_admitted_modules", {
        "schema": "trust.two-language.object-module-bijection/v1",
        "pairs": [{"module_id": "crate-a", "object_sha256": sha("obj-a")}]})
    cells = DEFAULT_POLICY["authority_contracts"]["codegen_surface"]["matrix_cells"]
    gr.write("authorized_codegen_matrix_complete", {
        "schema": "trust.two-language.codegen-matrix-observation/v1",
        "rows": [dict({k: v for k, v in cell.items() if k != "id"}, codegen_cell_id=cell["id"], object_sha256=sha(cell["id"]))
                 for cell in cells]})
    gr.write("typed_module_object_executable_lineage", {
        "schema": "trust.two-language.executable-lineage/v1",
        "chain": [{"module_sha256": linked, "object_sha256": sha("obj-a"), "executable_sha256": sha("exe"), "module_typed": True}]})
    gr.write("linked_executable_composition_validated", {
        "schema": "trust.two-language.executable-composition/v1",
        "executables": [{"executable_sha256": sha("exe"), "composition_verdict": "validated",
                         "components": [{"name": "a.o", "sha256": sha("obj-a")}, {"name": "libSystem", "sha256": sha("libSystem")}]}]})
    gr.write("runtime_startup_syslib_closure_bound", {
        "schema": "trust.two-language.runtime-closure/v1", "runtime_id": "std", "startup_id": "rustc-entry",
        "syslibs": [{"name": "libSystem.B.dylib", "sha256": sha("libSystem")}], "closure": "bound"})


G7_MUTATIONS = {
    "exact_linked_module_is_codegen_input": [lambda d: (d.__setitem__("frontend", "mir"), d)[1],
                                             lambda d: (d.__setitem__("linked_module_sha256", "f" * 64), d)[1]],
    "full_admitted_codegen_surface": [lambda d: (d["admitted_functions"].append("helper"), d)[1],
                                      lambda d: (d.__setitem__("refusals", ["UnsupportedInst Call"]), d)[1]],
    "zero_unproved_fallbacks": [lambda d: (d.__setitem__("fallbacks", 1), d)[1],
                                lambda d: (d.__setitem__("output_gate", "off"), d)[1]],
    "machine_equivalence_evidence": [lambda d: (d["functions"][1].__setitem__("verdict", "unknown"), d)[1],
                                     lambda d: (d["functions"][0].__setitem__("method", "sampled"), d)[1]],
    "objects_biject_admitted_modules": [lambda d: (d["pairs"].append({"module_id": "crate-b", "object_sha256": d["pairs"][0]["object_sha256"]}), d)[1],
                                        lambda d: (d.__setitem__("pairs", []), d)[1]],
    "authorized_codegen_matrix_complete": [lambda d: (d.__setitem__("rows", d["rows"][:1]), d)[1],
                                           lambda d: (d["rows"][0].__setitem__("crate_type", "cdylib"), d)[1],
                                           lambda d: (d["rows"][0].__setitem__("codegen_cell_id", "cell-unsigned"), d)[1]],
    "typed_module_object_executable_lineage": [lambda d: (d["chain"][0].__setitem__("module_typed", False), d)[1],
                                               lambda d: (d["chain"][0].__setitem__("executable_sha256", "short"), d)[1]],
    "linked_executable_composition_validated": [lambda d: (d["executables"][0].__setitem__("composition_verdict", "assumed"), d)[1],
                                                lambda d: (d["executables"][0].__setitem__("components", []), d)[1]],
    "runtime_startup_syslib_closure_bound": [lambda d: (d.__setitem__("closure", "open"), d)[1],
                                             lambda d: (d["syslibs"][0].pop("sha256"), d)[1]],
}


class CheckerContractTests(unittest.TestCase):
    def root(self, gate: str) -> GateRoot:
        gr = GateRoot(gate)
        self.addCleanup(gr.tmp.cleanup)
        return gr

    def assert_verdict_shape(self, gate: str, verdict: dict) -> None:
        self.assertEqual(set(verdict), VERDICT_KEYS)
        self.assertEqual(verdict["schema"], "trust.two-language.gate-checker-verdict/v2")
        self.assertEqual(verdict["gate"], gate)
        self.assertEqual(verdict["checker"], CHECKER_IDS[gate])
        self.assertEqual([row["id"] for row in verdict["checks"]], list(REQUIRED[gate]))
        for row in verdict["checks"]:
            self.assertEqual(set(row), {"id", "passed", "artifacts"})

    def test_g5_authored_bundle_cannot_pass_any_conjunct(self) -> None:
        gr = self.root("G5"); g5_authored(gr)
        code, verdict, err = gr.run(gr.bundle())
        self.assert_verdict_shape("G5", verdict)
        self.assertFalse(verdict["passed"])
        self.assertEqual(code, 1)
        self.assertTrue(all(not row["passed"] and row["artifacts"] for row in verdict["checks"]))
        for check_id in REQUIRED["G5"]:
            self.assertIn(f"{check_id}: producer authority missing:", err)
        for reason in (
            "callee identity and signature witness",
            "importer replay over versioned exporter bytes",
            "transitive PROOF/CALL reachability check",
            "shared ABI and memory-model definition",
        ):
            self.assertIn(reason, err)
        self.assertEqual(verdict["linked_module_sha256"], sha256_bytes(gr.linked_module.read_bytes()))

    def test_g5_each_shape_rule_reports_its_mutation(self) -> None:
        for check_id, mutations in G5_MUTATIONS.items():
            for index, mutate in enumerate(mutations):
                with self.subTest(check=check_id, mutation=index):
                    gr = self.root("G5"); g5_authored(gr)
                    path = gr.root / gr.artifacts[check_id]["path"]
                    doc = mutate(json.loads(path.read_text()))
                    gr.write(check_id, doc, path.name)
                    code, verdict, err = gr.run(gr.bundle())
                    self.assertEqual(code, 1)
                    self.assertFalse(verdict["passed"])
                    rows = {row["id"]: row["passed"] for row in verdict["checks"]}
                    self.assertFalse(rows[check_id], err)
                    self.assertFalse(any(rows.values()))
                    target_lines = [line for line in err.splitlines() if line.startswith(f"G5: {check_id}:")]
                    self.assertEqual(len(target_lines), 1, err)
                    self.assertNotIn("producer authority missing", target_lines[0])

    def rust_to_lean_line(self, gr: GateRoot, mutate) -> str:
        path = gr.root / gr.artifacts["rust_to_lean_typed_link"]["path"]
        gr.write("rust_to_lean_typed_link", mutate(json.loads(path.read_text())), path.name)
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1)
        self.assertFalse({r["id"]: r["passed"] for r in verdict["checks"]}["rust_to_lean_typed_link"])
        lines = [line for line in err.splitlines() if line.startswith("G5: rust_to_lean_typed_link:")]
        self.assertEqual(len(lines), 1, err)
        return lines[0]

    def test_g5_rust_to_lean_mutations_hit_their_own_refusal(self) -> None:
        for index, (mutate, diagnostic) in enumerate(RUST_TO_LEAN_REFUSALS):
            with self.subTest(mutation=mutate.__name__, index=index):
                gr = self.root("G5"); g5_authored(gr)
                self.assertIn(diagnostic, self.rust_to_lean_line(gr, mutate))

    def test_g5_seam_type_guard_requires_type_unchecked_present_and_empty(self) -> None:
        # 3b30328c07: `refusals: []` no longer means "typed".  The unmutated fixture
        # carries the key empty, so the shape rule passes and only the source gap fires.
        gr = self.root("G5"); g5_authored(gr)
        line = self.rust_to_lean_line(gr, lambda doc: doc)
        self.assertIn("producer authority missing: same-crate coverage sidecar", line)
        # Absent: a pre-guard emitter's row is not a typed link, however clean it looks.
        gr = self.root("G5"); g5_authored(gr)
        line = self.rust_to_lean_line(gr, _predate_seam_type_guard)
        self.assertIn("'m::cleanWsum' carries no `type_unchecked` key: it predates the seam type guard", line)
        self.assertNotIn("producer authority missing", line)
        # Non-empty: the seam linked a position it could not decide; that is disclosed, not typed.
        gr = self.root("G5"); g5_authored(gr)
        line = self.rust_to_lean_line(gr, _leave_operand_undecided)
        self.assertIn("'m::cleanWsum' left 1 operand position(s) undecided at the seam", line)
        self.assertIn("Refine(U64, p) vs U64", line)
        self.assertNotIn("producer authority missing", line)

    def test_g5_seam_type_guard_refuses_a_type_unchecked_that_is_not_a_list(self) -> None:
        # Both emitters write `type_unchecked` as a JSON list.  A guard that tested
        # `is None` then truthiness let the falsy non-lists read as the empty list (the
        # row passed the shape rule and only the source gap fired), refused a PRESENT
        # `null` as if the key were absent, and counted a string's characters as
        # undecided operand positions.  Each must be refused as the wrong type instead.
        cases = (
            (False, "bool"), (0, "int"), ("", "str"), ({}, "dict"), (None, "NoneType"),
            ("Refine(U64, p) vs U64", "str"),
        )
        for value, type_name in cases:
            with self.subTest(type_unchecked=value):
                gr = self.root("G5"); g5_authored(gr)

                def mutate(doc, value=value):
                    doc["clean_origin"]["linked"][0]["type_unchecked"] = value
                    return doc

                line = self.rust_to_lean_line(gr, mutate)
                self.assertIn(
                    f"'m::cleanWsum' carries `type_unchecked` of type {type_name} ({value!r});"
                    f" the seam discloses undecided operand positions as a list", line)
                self.assertNotIn("carries no `type_unchecked` key", line)
                self.assertNotIn("operand position(s) undecided", line)
                self.assertNotIn("producer authority missing", line)

    def check_line(self, gr: GateRoot, check_id: str, mutate) -> str:
        path = gr.root / gr.artifacts[check_id]["path"]
        gr.write(check_id, mutate(json.loads(path.read_text())), path.name)
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1)
        self.assertFalse(verdict["passed"])
        self.assertFalse(any(row["passed"] for row in verdict["checks"]), err)
        lines = [line for line in err.splitlines() if line.startswith(f"G5: {check_id}:")]
        self.assertEqual(len(lines), 1, err)
        return lines[0]

    def test_g5_linked_refusals_must_be_a_present_list(self) -> None:
        # Both emitters write `refusals` as a JSON list.  A guard reading it by
        # truthiness let an absent key, `null`, `false`, `0`, `""` and `{}` read as
        # "no refusals": the row passed the shape rule and only the source gap fired.
        absent = object()
        cases = ((absent, None), (None, "NoneType"), (False, "bool"), (0, "int"),
                 ("", "str"), ({}, "dict"))
        for value, type_name in cases:
            with self.subTest(refusals="ABSENT" if value is absent else value):
                gr = self.root("G5"); g5_authored(gr)

                def mutate(doc, value=value):
                    row = doc["clean_origin"]["linked"][0]
                    if value is absent:
                        row.pop("refusals")
                    else:
                        row["refusals"] = value
                    return doc

                line = self.rust_to_lean_line(gr, mutate)
                if value is absent:
                    self.assertIn("'m::cleanWsum' carries no `refusals` key", line)
                else:
                    self.assertIn(
                        f"'m::cleanWsum' carries `refusals` of type {type_name} ({value!r});"
                        f" only an empty list is zero refusals", line)
                self.assertNotIn("producer authority missing", line)

    def test_g5_typed_fields_are_read_by_type_not_truthiness(self) -> None:
        # Each field the producers write as an integer, a string identity or a
        # digest must be refused by ITS rule when it carries a boolean, a bare
        # prefix, `null` or a non-string that happens to be truthy.
        def linked(key, value):
            def mutate(doc):
                doc["clean_origin"]["linked"][0][key] = value; return doc
            return mutate

        def emitted(key, value):
            def mutate(doc):
                doc["clean_origin"]["emitted"][0][key] = value; return doc
            return mutate

        def link(key, value):
            def mutate(doc):
                doc["links"][0][key] = value; return doc
            return mutate

        def drop_link(key):
            def mutate(doc):
                doc["links"][0].pop(key); return doc
            return mutate

        def edge(key, value):
            def mutate(doc):
                doc["edges"][0][key] = value; return doc
            return mutate

        def top(key, value):
            def mutate(doc):
                doc[key] = value; return doc
            return mutate

        def evidence(value):
            def mutate(doc):
                for cell in doc["cells"].values():
                    cell["evidence"] = value
                return doc
            return mutate

        def crates(importer, exporter):
            def mutate(doc):
                doc["links"][0]["importer_crate"] = importer
                doc["links"][0]["exporter_crate"] = exporter
                return doc
            return mutate

        cases = (
            ("rust_to_lean_typed_link", linked("edges_repointed", True),
             "re-pointed no edge: `edges_repointed` must be a positive integer, got True"),
            ("rust_to_lean_typed_link", emitted("gate_subject_digest", "sha256:"),
             "`gate_subject_digest` must be `sha256:` and 64 lowercase hex digits"),
            ("rust_to_lean_typed_link", emitted("gate_subject_digest", "sha256:" + "B" * 64),
             "`gate_subject_digest` must be `sha256:` and 64 lowercase hex digits"),
            ("lean_to_rust_typed_link", link("rust_def_index", True),
             "rust_def_index must be a non-negative integer identity"),
            ("lean_to_rust_typed_link", link("rust_def_index", -1),
             "rust_def_index must be a non-negative integer identity"),
            ("lean_to_rust_typed_link", link("func_ty", None),
             "link `func_ty` must be a non-empty string, got None"),
            ("lean_to_rust_typed_link", link("rust_definition_identity", True),
             "link `rust_definition_identity` must be a non-empty string, got True"),
            ("cross_crate_digest_rechecked_link", drop_link("exporter_crate"),
             "link `exporter_crate` must name a crate as a non-empty string, got None"),
            ("cross_crate_digest_rechecked_link", crates(2, True),
             "link `importer_crate` must name a crate as a non-empty string, got 2"),
            ("cross_crate_digest_rechecked_link", crates(1, True),
             "link `importer_crate` must name a crate as a non-empty string, got 1"),
            ("proof_call_firewall", top("checked_items", True),
             "checked_items must be a positive integer"),
            ("typed_bidirectional_call_graph", edge("caller_identity", True),
             "edge `caller_identity` must be a non-empty string, got True"),
            ("typed_bidirectional_call_graph", edge("callee_identity", 1),
             "edge `callee_identity` must be a non-empty string, got 1"),
            ("typed_bidirectional_call_graph", edge("func_ty", [0]),
             "edge `func_ty` must be a non-empty string, got [0]"),
            ("cross_language_value_category_matrix", evidence(True),
             "evidence must be a non-empty string reference, got True"),
        )
        for index, (check_id, mutate, diagnostic) in enumerate(cases):
            with self.subTest(check=check_id, case=index, expect=diagnostic):
                gr = self.root("G5"); g5_authored(gr)
                line = self.check_line(gr, check_id, mutate)
                self.assertIn(diagnostic, line)
                self.assertNotIn("producer authority missing", line)

    def test_g5_non_list_emitted_is_named_not_blamed_on_linked(self) -> None:
        gr = self.root("G5"); g5_authored(gr)

        def mutate(doc):
            doc["clean_origin"]["emitted"] = {}
            return doc

        line = self.rust_to_lean_line(gr, mutate)
        self.assertIn("`clean_origin.emitted` must be a list, got dict", line)
        self.assertNotIn("clean_origin.linked", line)

    def test_g5_nesting_is_bounded_by_the_checker_not_the_interpreter(self) -> None:
        # A newer json decoder accepts nesting far deeper than `repr` can print, so a
        # refusal quoting the value died with no verdict.  Depth 100 is within every
        # decoder's limit (HEAD quoted it back as "refusals"); 100000 is past 3.9's.
        for depth in (100, 100_000):
            with self.subTest(depth=depth):
                gr = self.root("G5"); g5_authored(gr)
                path = gr.root / gr.artifacts["rust_to_lean_typed_link"]["path"]
                marker = '"refusals": []'
                text = path.read_text()
                self.assertEqual(text.count(marker), 1)
                gr.write("rust_to_lean_typed_link",
                         text.replace(marker, '"refusals": ' + "[" * depth + "]" * depth).encode(),
                         path.name)
                code, verdict, err = gr.run(gr.bundle())
                self.assertEqual(code, 1)
                self.assertFalse(verdict["passed"])
                self.assertFalse(any(row["passed"] for row in verdict["checks"]))
                self.assertIn("G5: rust_to_lean_typed_link: artifact is not a JSON document: "
                              "JSON nests deeper than 64", err)

    def test_g5_nesting_scan_is_linear_on_unterminated_strings(self) -> None:
        # A nesting pre-scan that re-scanned an unterminated string from each
        # escaped quote was quadratic: ~0.5 MB outlived the runner's timeout and
        # the checker printed no verdict.  The shared depth scan must stay linear
        # on authored text the decoder refuses in well under a millisecond.
        text = ('{"schema": "' + '\\"' * 200_000).encode()
        with self.subTest(where="artifact"):
            gr = self.root("G5"); g5_authored(gr)
            gr.write("rust_to_lean_typed_link", text, "unterminated.json")
            code, verdict, err = gr.run(gr.bundle(), timeout=20)
            self.assertEqual(code, 1)
            self.assert_verdict_shape("G5", verdict)
            self.assertFalse(any(row["passed"] for row in verdict["checks"]))
            line = [l for l in err.splitlines() if l.startswith("G5: rust_to_lean_typed_link:")]
            self.assertEqual(len(line), 1, err)
            self.assertIn("artifact is not a JSON document", line[0])
        with self.subTest(where="bundle"):
            gr = self.root("G5"); g5_authored(gr)
            bundle = gr.root / "unterminated-bundle.json"
            bundle.write_bytes(text)
            code, verdict, err = gr.run(bundle, timeout=20)
            self.assertEqual(code, 1)
            self.assert_verdict_shape("G5", verdict)
            self.assertFalse(any(row["passed"] for row in verdict["checks"]))
            self.assertIn("G5: evidence bundle unreadable:", err)

    def test_g5_unstatable_artifact_path_still_yields_one_verdict(self) -> None:
        # Python 3.9's `Path.is_file` re-raises ENAMETOOLONG: the checker died with
        # a traceback and an empty stdout instead of refusing the row.
        gr = self.root("G5"); g5_authored(gr)
        gr.artifacts["proof_call_firewall"]["path"] = "evidence/" + "a" * 300 + ".json"
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1)
        self.assert_verdict_shape("G5", verdict)
        row = next(row for row in verdict["checks"] if row["id"] == "proof_call_firewall")
        self.assertFalse(row["passed"]); self.assertEqual(row["artifacts"], [])
        line = [l for l in err.splitlines() if l.startswith("G5: proof_call_firewall:")]
        self.assertEqual(len(line), 1, err)
        self.assertTrue("artifact path cannot be inspected" in line[0]
                        or "artifact file does not exist" in line[0], line[0])

    def test_g5_bundle_bytes_must_hash_to_the_bound_evidence_digest(self) -> None:
        gr = self.root("G5"); g5_authored(gr)
        bundle = gr.bundle()
        code, verdict, err = gr.run(bundle, evidence_sha256="e" * 64)
        self.assertEqual(code, 1)
        self.assertFalse(verdict["passed"])
        self.assertIn("G5: evidence bundle digest differs from --evidence-sha256", err)
        self.assertNotIn("producer authority missing", err)
        self.assertTrue(all(not row["passed"] and not row["artifacts"] for row in verdict["checks"]))

    def test_g5_forged_producer_and_exact_module_fields_do_not_authorize_reports(self) -> None:
        gr = self.root("G5"); g5_authored(gr)
        for check_id in REQUIRED["G5"]:
            path = gr.root / gr.artifacts[check_id]["path"]
            doc = json.loads(path.read_text())
            doc.update({
                "producer": "trustc", "source_revision": "a" * 40,
                "acceptance_run_id": "run-1",
                "linked_module_sha256": sha256_bytes(gr.linked_module.read_bytes()),
                "subject_graph_sha256": ZERO,
                "independent_recheck": "passed",
            })
            gr.write(check_id, doc, path.name)
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1)
        self.assertFalse(verdict["passed"])
        self.assertTrue(all(not row["passed"] for row in verdict["checks"]), err)

    def test_g5_same_crate_sidecar_cannot_follow_an_unrelated_linked_module(self) -> None:
        gr = self.root("G5"); g5_authored(gr)
        gr.linked_module.write_bytes(b"TRUST_IR\x00unrelated-linked-module")
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1)
        row = next(row for row in verdict["checks"] if row["id"] == "rust_to_lean_typed_link")
        self.assertFalse(row["passed"])
        self.assertIn("not bound to the exact linked module", err)

    def test_g5_evidence_binding_is_fail_closed(self) -> None:
        # Digest mismatch.
        gr = self.root("G5"); g5_authored(gr)
        gr.artifacts["proof_call_firewall"]["sha256"] = "e" * 64
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1); self.assertIn("hash mismatch", err)
        self.assertEqual([r["artifacts"] for r in verdict["checks"] if r["id"] == "proof_call_firewall"], [[]])
        # Absolute path / root escape.
        for bad in [str(gr.root / "evidence" / "proof_call_firewall.json"), "../outside.json"]:
            gr2 = self.root("G5"); g5_authored(gr2)
            gr2.artifacts["proof_call_firewall"]["path"] = bad
            code, verdict, err = gr2.run(gr2.bundle())
            self.assertEqual(code, 1, bad); self.assertFalse(verdict["passed"])
        # A hand-authored `passed` in the bundle is a header violation, not a verdict.
        gr3 = self.root("G5"); g5_authored(gr3)
        code, verdict, err = gr3.run(gr3.bundle(passed=True))
        self.assertEqual(code, 1); self.assertIn("header", err)
        # Unknown check ids are refused.
        gr4 = self.root("G5"); g5_authored(gr4)
        gr4.artifacts["made_up"] = dict(gr4.artifacts["proof_call_firewall"])
        code, verdict, err = gr4.run(gr4.bundle())
        self.assertEqual(code, 1); self.assertIn("unknown check ids", err)
        # G8-only inputs are a protocol violation for G5.
        gr5 = self.root("G5"); g5_authored(gr5)
        code, verdict, err = gr5.run(gr5.bundle(), receipt=True)
        self.assertEqual(code, 1); self.assertIn("G8-only", err)

    def test_g5_empty_bundle_names_every_missing_conjunct(self) -> None:
        gr = self.root("G5")
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1); self.assertFalse(verdict["passed"])
        for check_id in REQUIRED["G5"]:
            self.assertIn(f"{check_id}: no artifact bound", err)

    def test_g7_authored_bundle_cannot_pass_any_conjunct(self) -> None:
        gr = self.root("G7"); g7_authored(gr)
        code, verdict, err = gr.run(gr.bundle())
        self.assert_verdict_shape("G7", verdict)
        self.assertFalse(verdict["passed"])
        self.assertEqual(code, 1)
        self.assertTrue(all(not row["passed"] and row["artifacts"] for row in verdict["checks"]), err)
        for check_id in REQUIRED["G7"]:
            self.assertIn(f"{check_id}:", err)

    def test_g7_each_shape_mutation_is_diagnosed(self) -> None:
        for check_id, mutations in G7_MUTATIONS.items():
            for index, mutate in enumerate(mutations):
                with self.subTest(check=check_id, mutation=index):
                    gr = self.root("G7"); g7_authored(gr)
                    _, baseline, baseline_err = gr.run(gr.bundle())
                    self.assertFalse(baseline["passed"])
                    path = gr.root / gr.artifacts[check_id]["path"]
                    doc = mutate(json.loads(path.read_text()))
                    gr.write(check_id, doc, path.name)
                    code, verdict, err = gr.run(gr.bundle())
                    self.assertEqual(code, 1)
                    self.assertFalse(verdict["passed"])
                    rows = {row["id"]: row["passed"] for row in verdict["checks"]}
                    self.assertFalse(rows[check_id], err)
                    self.assertFalse(any(rows.values()))
                    target = [line for line in err.splitlines() if line.startswith(f"G7: {check_id}:")]
                    prior = [line for line in baseline_err.splitlines() if line.startswith(f"G7: {check_id}:")]
                    self.assertEqual(len(target), 1, err)
                    self.assertEqual(len(prior), 1, baseline_err)
                    self.assertNotEqual(target[0], prior[0], "mutation must change the target diagnostic")

    def test_g7_binds_the_receipt_linked_module_and_the_signed_matrix(self) -> None:
        # The receipt's consumed module must be the acceptance run's linked module.
        gr = self.root("G7"); g7_authored(gr)
        gr.linked_module.write_bytes(b"TRUST_IR\x00a-different-linked-module")
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1)
        rows = {row["id"]: row["passed"] for row in verdict["checks"]}
        self.assertFalse(rows["exact_linked_module_is_codegen_input"], err)
        self.assertIn("exact linked module", err)
        # A cell the owner signs but nobody built is named, not inferred away.
        gr = self.root("G7"); g7_authored(gr)
        contract_path = gr.root / "codegen-contract.json"
        contract = json.loads(contract_path.read_text())
        cells = contract["matrix_cells"]
        cells.append(dict(cells[0], id="cell-x86", target_id="aarch64-apple-darwin", crate_type="rlib", opt_level="0"))
        bind_codegen_contract(gr, contract)
        code, verdict, err = gr.run(gr.bundle())
        rows = {row["id"]: row["passed"] for row in verdict["checks"]}
        self.assertFalse(rows["authorized_codegen_matrix_complete"], err)
        self.assertIn("cell-x86", err)
        # The named contract reference is verified by digest.
        gr = self.root("G7"); g7_authored(gr)
        contract_path = gr.root / "codegen-contract.json"
        contract = json.loads(contract_path.read_text())
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1)
        self.assertFalse(verdict["passed"])
        self.assertIn("signed cells and authored observations", err)
        contract_path.write_text(json.dumps(dict(contract, matrix_cells=contract["matrix_cells"][:1])))
        code, verdict, err = gr.run(gr.bundle())
        self.assertFalse({r["id"]: r["passed"] for r in verdict["checks"]}["authorized_codegen_matrix_complete"])
        self.assertIn("artifact hash mismatch", err)

    def test_g7_empty_bundle_names_every_missing_conjunct(self) -> None:
        gr = self.root("G7")
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1); self.assertFalse(verdict["passed"])
        for check_id in REQUIRED["G7"]:
            self.assertIn(f"{check_id}: no artifact bound", err)


if __name__ == "__main__":
    unittest.main()
