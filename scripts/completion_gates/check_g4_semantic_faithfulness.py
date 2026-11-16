#!/usr/bin/env python3
"""Fail-closed G4 semantic-faithfulness completion checker.

The receipt runner authenticates the owner policy and executes this exact
source-revision blob in isolation. This checker recomputes structural joins and
content hashes, but no current artifact contains an independently replayable
source-to-Trust-IR refinement derivation or a checked finite-domain coverage
proof. A certificate-shaped file, an authored ``kernel-checked`` label, and a
sampled ``Agreed`` verdict cannot fill that gap. The gate therefore stays red.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

# Trust (2026-09-27): an EXPLICIT nesting bound, because the `RecursionError`
# caught at the parse sites below is NOT one. Python's recursion limit is not a
# property this gate controls. MEASURED 2026-09-27: `b"[" * 1100 + b"0" + b"]" * 1100`
# raises `RecursionError` on CPython 3.9 (so the reader refused it) and parses
# CLEANLY on CPython 3.14 (so it did not). `_isolated_python` runs every checker
# under `sys.executable` and NOTHING here pins an interpreter version, so on a
# newer Python the refusal of adversarially nested evidence silently disappeared.
# `scripts/tests/completion_gate_malformed_input_test.py` is the control and does
# fail on 3.14 — but no harness lane runs it, so nothing said so.
#
# 64 is chosen from measurement, not taste: the deepest legitimate JSON in the
# tree is depth 4. Refuse-only — this can reject input a reader previously
# accepted, never accept input it previously rejected.
TRUST_MAX_JSON_DEPTH = 64


def _trust_json_nesting_depth(text: str) -> int:
    """Maximum `[`/`{` nesting of `text`, ignoring brackets inside strings."""
    depth = 0
    deepest = 0
    in_string = False
    escaped = False
    for ch in text:
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
        elif ch == "[" or ch == "{":
            depth += 1
            deepest = max(deepest, depth)
        elif ch == "]" or ch == "}":
            depth -= 1
    return deepest


SCHEMA = "trust.two-language.gate-checker-verdict/v2"
EVIDENCE_SCHEMA = "trust.two-language.gate-evidence/v1"
GOAL = "TRUST-TWO-LANGUAGE-100"
GATE = "G4"
CHECKER = "trust.two-language.g4.semantic-faithfulness/v2"
REPOSITORY_ID = "https://github.com/alabsystems/trust"
HEX = re.compile(r"[0-9a-f]{64}\Z")
REVISION = re.compile(r"(?:[0-9a-f]{40}|[0-9a-f]{64})\Z")
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
ARTIFACTS = (
    "subject_graph", "semantics_contract", "proof_authority_contract",
    "rust_scorecard", "lean_scorecard", "body_join",
)
CHECK_ARTIFACTS = {
    "every_body_universally_refined": ("subject_graph", "semantics_contract", "proof_authority_contract"),
    "finite_domain_exhaustiveness_certificates_checked": ("subject_graph", "proof_authority_contract"),
    "sampled_agreement_not_used_as_proof": ("rust_scorecard", "lean_scorecard", "body_join"),
    "refinement_certificates_biject_reachable_bodies": ("subject_graph", "body_join"),
    "all_lean_rows_carrier_faithful_gate": ("lean_scorecard", "body_join"),
    "no_weak_or_uninterpreted_verdict_classes": ("rust_scorecard", "lean_scorecard", "body_join"),
    "owner_pinned_semantics_relation_observation_model": ("semantics_contract",),
    "certificates_bind_authorized_relation": ("subject_graph", "semantics_contract", "proof_authority_contract"),
    "whole_program_contextual_refinement": ("subject_graph",),
    "assumption_closure_checked": ("subject_graph",),
}
assert tuple(CHECK_ARTIFACTS) == REQUIRED
SEMANTICS_ROLES = {
    "rust_language", "lean_language", "trust_ir", "rust_to_trust_ir_refinement",
    "lean_to_trust_ir_refinement", "observation_model", "undefined_behavior",
    "abi_memory_model",
}
POLICY_CONTRACTS = {
    "admission", "semantics", "obligations", "proof_authority",
    "compatibility_surfaces", "codegen_surface", "acceptance_environment",
}
SUBJECT_ROOTS = {
    "admitted_files", "reachable_bodies", "refinement_certificates", "obligations",
    "proof_certificates", "modules", "codegen_matrix_cells", "objects",
    "translation_evidence", "call_edges", "executables",
}
BODY_FIELDS = {
    "id", "language", "function_identity_sha256", "source_language_semantics_id",
    "source_language_semantics_sha256", "source_semantics_sha256",
    "trust_ir_semantics_id", "trust_ir_semantics_sha256", "trust_ir_sha256",
    "ssa_epoch_sha256", "effect_summary_sha256",
}
CERT_FIELDS = {
    "body_id", "source_semantics_sha256", "trust_ir_sha256", "relation_id",
    "relation_sha256", "certificate_kind", "finite_domain_sha256",
    "exhaustiveness_evidence", "all_elements_agreement_root_sha256",
    "kernel_environment_id", "kernel_environment_sha256", "evidence",
}


class Refusal(Exception):
    pass


def exact(value: Any, keys: set[str], where: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != keys:
        raise Refusal(f"{where}: expected exactly {sorted(keys)}")
    return value


def rows(value: Any, where: str, *, nonempty: bool = True) -> list[Any]:
    if type(value) is not list or (nonempty and not value):
        raise Refusal(f"{where}: expected {'non-empty ' if nonempty else ''}array")
    return value


def string(value: Any, where: str) -> str:
    if type(value) is not str or not value:
        raise Refusal(f"{where}: expected non-empty string")
    return value


def digest(value: Any, where: str) -> str:
    if type(value) is not str or HEX.fullmatch(value) is None:
        raise Refusal(f"{where}: expected lowercase SHA-256")
    return value


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_root(value: list[dict[str, Any]]) -> str:
    ordered = sorted(value, key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")))
    return sha256(json.dumps(ordered, sort_keys=True, separators=(",", ":"),
                             ensure_ascii=True, allow_nan=False).encode("utf-8"))


def unique_pairs(pairs: list[tuple[str, Any]], where: str) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise Refusal(f"{where}: duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_json(data: bytes, where: str) -> dict[str, Any]:
    try:
        _trust_text = data.decode("utf-8")
        if _trust_json_nesting_depth(_trust_text) > TRUST_MAX_JSON_DEPTH:
            raise ValueError(f"JSON nests deeper than {TRUST_MAX_JSON_DEPTH}")
        value = json.loads(_trust_text,
                           object_pairs_hook=lambda pairs: unique_pairs(pairs, where),
                           parse_constant=lambda token: (_ for _ in ()).throw(Refusal(
                               f"{where}: non-finite JSON {token}")))
        json.dumps(value, allow_nan=False)
    except (UnicodeError, ValueError, RecursionError) as exc:
        raise Refusal(f"{where}: invalid strict JSON: {exc}") from exc
    if type(value) is not dict:
        raise Refusal(f"{where}: expected JSON object")
    return value


class Context:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        try:
            # Python 3.9 raises RuntimeError on a symlink loop; map it to a
            # refusal so main() still prints exactly one verdict.
            self.root = Path(args.root).resolve()
        except (OSError, RuntimeError, ValueError) as exc:
            raise Refusal(f"--root cannot be resolved: {exc}") from exc
        self.refs: dict[str, dict[str, str]] = {}
        self.docs: dict[str, dict[str, Any]] = {}
        self.cache: dict[str, Any] = {}
        self.bind_common()

    def path(self, raw: Any, where: str) -> Path:
        name = string(raw, where)
        parts = name.split("/")
        if Path(name).is_absolute() or "\\" in name or any(part in {"", ".", ".."} for part in parts):
            raise Refusal(f"{where}: path must be canonical and root-relative")
        try:
            candidate = (self.root / name).resolve()
        except (OSError, ValueError, RuntimeError) as exc:
            raise Refusal(f"{where}: path cannot be resolved: {exc}") from exc
        if not candidate.is_relative_to(self.root) or not candidate.is_file():
            raise Refusal(f"{where}: missing file or path escapes root")
        return candidate

    def relative(self, raw: str, where: str) -> str:
        try:
            candidate = Path(raw).resolve()
        except (OSError, ValueError, RuntimeError) as exc:
            raise Refusal(f"{where}: CLI path cannot be resolved: {exc}") from exc
        if not candidate.is_relative_to(self.root):
            raise Refusal(f"{where}: CLI path escapes root")
        return candidate.relative_to(self.root).as_posix()

    def ref(self, value: Any, where: str, *, nonempty: bool = False) -> tuple[dict[str, str], bytes]:
        ref = exact(value, {"path", "sha256"}, where)
        path = self.path(ref["path"], where)
        expected = digest(ref["sha256"], f"{where}.sha256")
        data = path.read_bytes()
        if sha256(data) != expected or (nonempty and not data):
            raise Refusal(f"{where}: content hash mismatch or empty evidence")
        return ref, data

    def bound(self, path: str, expected: str, where: str) -> tuple[dict[str, str], bytes]:
        return self.ref({"path": self.relative(path, where), "sha256": expected}, where)

    def bind_common(self) -> None:
        a = self.args
        if a.receipt is not None or a.prior_gates_root is not None:
            raise Refusal("G4 is pre-seal and must not receive receipt/prior-gates-root")
        if REVISION.fullmatch(a.source_revision) is None:
            raise Refusal("source_revision must be a lowercase Git OID")
        digest(a.acceptance_run_id, "acceptance run ID")
        if sha256(Path(__file__).read_bytes()) != digest(a.checker_sha256, "checker SHA-256"):
            raise Refusal("checker snapshot SHA-256 differs from runner binding")
        for path, expected, where in (
            (a.toolchain_manifest, a.toolchain_sha256, "toolchain manifest"),
            (a.corpus_manifest, a.corpus_manifest_sha256, "corpus manifest"),
            (a.subject_graph, a.subject_graph_sha256, "subject graph"),
            (a.linked_module, a.linked_module_sha256, "linked module"),
            (a.release_artifact, a.release_artifact_sha256, "release artifact"),
            (a.authority_policy, a.authority_policy_sha256, "authority policy"),
            (a.policy_authorization, a.policy_authorization_sha256, "policy authorization"),
        ):
            self.bound(path, expected, where)
        _, raw = self.bound(a.verify_evidence, a.evidence_sha256, "G4 evidence bundle")
        bundle = exact(load_json(raw, "G4 evidence bundle"),
                       {"schema", "gate", "checker", "artifacts"}, "G4 evidence bundle")
        if (bundle["schema"], bundle["gate"], bundle["checker"]) != (
            EVIDENCE_SCHEMA, GATE, CHECKER
        ):
            raise Refusal("G4 evidence bundle has wrong schema, gate, or checker")
        artifacts = exact(bundle["artifacts"], set(ARTIFACTS), "G4 evidence artifacts")
        for name in ARTIFACTS:
            ref, data = self.ref(artifacts[name], f"artifacts.{name}")
            self.refs[name] = ref
            self.docs[name] = load_json(data, name)
        if self.refs["subject_graph"] != {
            "path": self.relative(a.subject_graph, "subject graph"), "sha256": a.subject_graph_sha256
        }:
            raise Refusal("G4 subject graph artifact differs from receipt-bound subject graph")

    def memo(self, key: str, produce: Any) -> Any:
        if key not in self.cache:
            self.cache[key] = produce()
        return self.cache[key]

    def policy(self) -> tuple[dict[str, dict[str, str]], dict[str, tuple[str, set[str]]]]:
        def produce() -> tuple[dict[str, dict[str, str]], dict[str, tuple[str, set[str]]]]:
            _, raw = self.bound(self.args.authority_policy, self.args.authority_policy_sha256,
                                "authority policy")
            policy = load_json(raw, "authority policy")
            if (policy.get("schema"), policy.get("goal_id"), policy.get("repository_id")) != (
                "trust.two-language.authority-policy/v2", GOAL, REPOSITORY_ID
            ):
                raise Refusal("authority policy header mismatch")
            contracts = exact(policy.get("contracts"), POLICY_CONTRACTS, "authority contracts")
            def contract(name: str, schema: str) -> dict[str, Any]:
                named = exact(contracts[name], {"id", "path", "sha256"}, f"{name} contract ref")
                if named["id"] != f"trust.two-language.contract.{name.replace('_', '-')}":
                    raise Refusal(f"{name}: wrong owner contract identity")
                ref, data = self.ref({"path": named["path"], "sha256": named["sha256"]},
                                     f"{name} contract")
                if ref != self.refs[f"{name}_contract"]:
                    raise Refusal(f"{name}: evidence artifact differs from owner policy")
                doc = load_json(data, f"{name} contract")
                if (doc.get("schema"), doc.get("goal_id"), doc.get("repository_id")) != (
                    schema, GOAL, REPOSITORY_ID
                ):
                    raise Refusal(f"{name}: owner contract header mismatch")
                return doc
            semantics = exact(contract("semantics", "trust.two-language.semantics-contract/v1"),
                              {"schema", "goal_id", "repository_id", "definitions"},
                              "semantics contract")
            definitions = exact(semantics["definitions"], SEMANTICS_ROLES, "semantic definitions")
            roles: dict[str, dict[str, str]] = {}
            ids: set[str] = set()
            paths: set[str] = set()
            files: set[tuple[int, int]] = set()
            for role, named in definitions.items():
                named = exact(named, {"id", "path", "sha256"}, f"semantic {role}")
                ident = string(named["id"], f"semantic {role}.id")
                ref, _ = self.ref({"path": named["path"], "sha256": named["sha256"]},
                                  f"semantic {role}", nonempty=True)
                # A raw-string comparison misses two spellings of one file: a
                # symlink or hard link, or a case alias on a case-insensitive
                # file system. Compare the resolved file's (st_dev, st_ino) too.
                status = self.path(ref["path"], f"semantic {role}").stat()
                file = (status.st_dev, status.st_ino)
                if ident in ids or ref["path"] in paths or file in files:
                    raise Refusal("semantic definitions have duplicate identity or path")
                ids.add(ident)
                paths.add(ref["path"])
                files.add(file)
                roles[role] = {"id": ident, "sha256": ref["sha256"]}
            proof = exact(contract("proof_authority", "trust.two-language.proof-authority-contract/v1"),
                          {"schema", "goal_id", "repository_id", "canonical_proposition_encoder",
                           "kernels", "axiom_policy", "external_olean_policy", "denied_axioms"},
                          "proof authority contract")
            if proof["denied_axioms"] != ["sorryAx"]:
                raise Refusal("proof authority does not deny sorryAx")
            kernels: dict[str, tuple[str, set[str]]] = {}
            for row in rows(proof["kernels"], "owner kernels"):
                row = exact(row, {"id", "environment_sha256", "artifact", "proof_grades",
                                  "axiom_allowlist_root_sha256"}, "owner kernel")
                ident = string(row["id"], "kernel ID")
                if ident in kernels:
                    raise Refusal("duplicate owner kernel ID")
                digest(row["axiom_allowlist_root_sha256"], f"kernel {ident} axiom root")
                self.ref(row["artifact"], f"kernel {ident} artifact", nonempty=True)
                grades = rows(row["proof_grades"], f"kernel {ident} grades")
                if any(type(grade) is not str or not grade for grade in grades) or len(set(grades)) != len(grades):
                    raise Refusal(f"kernel {ident} has malformed or duplicate proof grades")
                kernels[ident] = (digest(row["environment_sha256"],
                                         f"kernel {ident} environment"), set(grades))
            return roles, kernels
        return self.memo("policy", produce)

    def admission(self) -> dict[str, tuple[str, str]]:
        def produce() -> dict[str, tuple[str, str]]:
            _, raw = self.bound(self.args.authority_policy, self.args.authority_policy_sha256,
                                "authority policy")
            contracts = exact(load_json(raw, "authority policy").get("contracts"),
                              POLICY_CONTRACTS, "authority contracts")
            named = exact(contracts["admission"], {"id", "path", "sha256"},
                          "admission contract ref")
            if named["id"] != "trust.two-language.contract.admission":
                raise Refusal("wrong owner admission contract identity")
            _, data = self.ref({"path": named["path"], "sha256": named["sha256"]},
                               "admission contract")
            contract = exact(load_json(data, "admission contract"),
                             {"schema", "goal_id", "repository_id", "lanes"},
                             "admission contract")
            if (contract["schema"], contract["goal_id"], contract["repository_id"]) != (
                "trust.two-language.admission-contract/v1", GOAL, REPOSITORY_ID
            ):
                raise Refusal("owner admission contract header mismatch")
            lanes = exact(contract["lanes"], {"rust", "lean", "mixed"}, "admission lanes")
            _, corpus_data = self.bound(self.args.corpus_manifest, self.args.corpus_manifest_sha256,
                                        "corpus manifest")
            corpus = exact(load_json(corpus_data, "corpus manifest"), {
                "schema", "goal_id", "repository_id", "acceptance_run_id",
                "source_revision", "rust", "lean", "mixed",
            }, "corpus manifest")
            if (corpus["schema"], corpus["goal_id"], corpus["repository_id"],
                corpus["acceptance_run_id"], corpus["source_revision"]) != (
                "trust.two-language.corpus-manifest/v1", GOAL, REPOSITORY_ID,
                self.args.acceptance_run_id, self.args.source_revision
            ):
                raise Refusal("corpus manifest header differs from receipt")
            entries: dict[str, tuple[str, str]] = {}
            for lane in ("rust", "lean", "mixed"):
                owner_lane = lanes[lane]
                if type(owner_lane) is not dict:
                    raise Refusal(f"owner {lane} lane malformed")
                observed = exact(corpus[lane], {"upstream_revision", "admission_policy_sha256",
                                                "entries"}, f"corpus {lane}")
                if (observed["upstream_revision"] != owner_lane.get("upstream_revision")
                    or observed["admission_policy_sha256"] != named["sha256"]
                    or observed["entries"] != owner_lane.get("entries")):
                    raise Refusal(f"{lane}: corpus entries differ from owner admission contract")
                for entry in rows(owner_lane.get("entries"), f"owner {lane} entries"):
                    entry = exact(entry, {"id", "kind", "admitted", "source", "expected_outcome"},
                                  f"owner {lane} entry")
                    fid = string(entry["id"], f"owner {lane} file ID")
                    if fid in entries:
                        raise Refusal(f"duplicate owner admission ID {fid}")
                    source, _ = self.ref(entry["source"], f"owner {fid} source")
                    if type(entry["admitted"]) is not bool:
                        raise Refusal(f"owner {fid}: admitted must be boolean")
                    if entry["admitted"] is True:
                        if entry["expected_outcome"] != "ok":
                            raise Refusal(f"admitted {fid} has non-ok expected outcome")
                        entries[fid] = (lane, source["path"])
            return entries
        return self.memo("admission", produce)

    def subject(self) -> dict[str, dict[str, Any]]:
        def produce() -> dict[str, dict[str, Any]]:
            roles, kernels = self.policy()
            doc = exact(self.docs["subject_graph"], {
                "schema", "goal_id", "acceptance_run_id", "source_revision", "programs",
                "roots", "release_executable",
            }, "subject index")
            if (doc["schema"], doc["goal_id"], doc["acceptance_run_id"], doc["source_revision"]) != (
                "trust.two-language.subject-index/v3", GOAL,
                self.args.acceptance_run_id, self.args.source_revision
            ):
                raise Refusal("subject index header differs from receipt")
            roots = exact(doc["roots"], SUBJECT_ROOTS, "subject roots")
            programs: dict[str, dict[str, Any]] = {}
            body_rows: list[dict[str, Any]] = []
            cert_rows: list[dict[str, Any]] = []
            languages: set[str] = set()
            linked = False
            for program in rows(doc["programs"], "subject programs"):
                program = exact(program, {"id", "entrypoints", "admitted_file_ids", "bodies",
                    "refinement_certificates", "obligations", "proof_certificates", "modules",
                    "objects", "translation_evidence", "executables", "call_edges",
                    "contextual_refinement"}, "subject program")
                pid = string(program["id"], "program ID")
                if pid in programs:
                    raise Refusal(f"duplicate subject program {pid}")
                bodies: dict[str, dict[str, Any]] = {}
                for body in rows(program["bodies"], f"{pid}.bodies"):
                    body = exact(body, BODY_FIELDS, f"{pid}.body")
                    bid = string(body["id"], f"{pid}.body.id")
                    language = body["language"]
                    if bid in bodies or language not in {"rust", "lean"}:
                        raise Refusal(f"{pid}: duplicate body or unknown language {bid}")
                    for key in BODY_FIELDS - {"id", "language", "source_language_semantics_id",
                                               "trust_ir_semantics_id"}:
                        digest(body[key], f"{pid}.{bid}.{key}")
                    source_role = roles[f"{language}_language"]
                    if (body["source_language_semantics_id"], body["source_language_semantics_sha256"]) != (
                        source_role["id"], source_role["sha256"]
                    ) or (body["trust_ir_semantics_id"], body["trust_ir_semantics_sha256"]) != (
                        roles["trust_ir"]["id"], roles["trust_ir"]["sha256"]
                    ):
                        raise Refusal(f"{pid}.{bid}: body uses non-owner semantic labels")
                    bodies[bid] = body
                    languages.add(language)
                    body_rows.append({"program_id": pid, **body})
                certs: dict[str, dict[str, Any]] = {}
                for cert in rows(program["refinement_certificates"], f"{pid}.refinements"):
                    cert = exact(cert, CERT_FIELDS, f"{pid}.refinement")
                    bid = string(cert["body_id"], f"{pid}.refinement.body_id")
                    if bid in certs or bid not in bodies:
                        raise Refusal(f"{pid}: duplicate or unknown refinement body {bid}")
                    body = bodies[bid]
                    relation = roles[f"{body['language']}_to_trust_ir_refinement"]
                    if (cert["source_semantics_sha256"] != body["source_semantics_sha256"]
                        or cert["trust_ir_sha256"] != body["trust_ir_sha256"]
                        or (cert["relation_id"], cert["relation_sha256"]) != (
                            relation["id"], relation["sha256"]
                        )):
                        raise Refusal(f"{pid}.{bid}: certificate does not bind body and owner relation")
                    kernel = kernels.get(cert["kernel_environment_id"])
                    if (kernel is None or cert["kernel_environment_sha256"] != kernel[0]
                        or "kernel-checked" not in kernel[1]):
                        raise Refusal(f"{pid}.{bid}: certificate names non-owner/non-kernel-checked environment")
                    kind = cert["certificate_kind"]
                    finite = (cert["finite_domain_sha256"], cert["exhaustiveness_evidence"],
                              cert["all_elements_agreement_root_sha256"])
                    if kind == "universal":
                        if finite != (None, None, None):
                            raise Refusal(f"{pid}.{bid}: universal certificate carries finite substitute")
                    elif kind == "finite-exhaustive":
                        digest(finite[0], f"{pid}.{bid}.finite_domain_sha256")
                        self.ref(finite[1], f"{pid}.{bid}.exhaustiveness", nonempty=True)
                        digest(finite[2], f"{pid}.{bid}.all_elements_agreement_root_sha256")
                    else:
                        raise Refusal(f"{pid}.{bid}: unsupported certificate kind {kind!r}")
                    self.ref(cert["evidence"], f"{pid}.{bid}.refinement evidence", nonempty=True)
                    certs[bid] = cert
                    cert_rows.append({"program_id": pid, **cert})
                if set(certs) != set(bodies):
                    raise Refusal(f"{pid}: refinement certificate/body bijection fails")
                contextual = exact(program["contextual_refinement"],
                    {"assumption_closure_sha256", "evidence"}, f"{pid}.contextual_refinement")
                closure = digest(contextual["assumption_closure_sha256"], f"{pid}.closure")
                self.ref(contextual["evidence"], f"{pid}.contextual evidence", nonempty=True)
                owned: set[str] = set()
                owner_module: dict[str, str] = {}
                module_ids: set[str] = set()
                for module in rows(program["modules"], f"{pid}.modules"):
                    module = exact(module, {"id", "artifact", "body_ids", "call_edge_ids",
                        "obligation_ids", "refinement_certificate_body_ids", "proof_certificate_ids",
                        "assumption_closure_sha256", "contextual_refinement_evidence"}, f"{pid}.module")
                    mid = string(module["id"], f"{pid}.module.id")
                    if mid in module_ids:
                        raise Refusal(f"{pid}: duplicate module ID {mid}")
                    module_ids.add(mid)
                    ref, _ = self.ref(module["artifact"], f"{pid}.{mid}.module", nonempty=True)
                    if ref["sha256"] == self.args.linked_module_sha256:
                        linked = True
                    if module["assumption_closure_sha256"] != closure:
                        raise Refusal(f"{pid}.{mid}: module assumption closure differs from program")
                    if module["contextual_refinement_evidence"] != contextual["evidence"]:
                        raise Refusal(f"{pid}.{mid}: contextual evidence differs from program")
                    self.ref(module["contextual_refinement_evidence"],
                             f"{pid}.{mid}.contextual evidence", nonempty=True)
                    ids = rows(module["body_ids"], f"{pid}.{mid}.body_ids")
                    if any(type(bid) is not str or bid not in bodies or bid in owned for bid in ids):
                        raise Refusal(f"{pid}.{mid}: module body partition is not unique and known")
                    owned.update(ids)
                    owner_module.update({bid: mid for bid in ids})
                    if sorted(module["refinement_certificate_body_ids"]) != sorted(ids):
                        raise Refusal(f"{pid}.{mid}: module refinement/body partition differs")
                if owned != set(bodies):
                    raise Refusal(f"{pid}: modules omit or duplicate reachable bodies")
                for edge in rows(program["call_edges"], f"{pid}.call_edges", nonempty=False):
                    if type(edge) is not dict or edge.get("import_assumption_closure_sha256") != closure:
                        raise Refusal(f"{pid}: call edge assumption closure differs from program")
                programs[pid] = {"bodies": bodies, "certs": certs, "closure": closure,
                                 "owner_module": owner_module,
                                 "files": set(rows(program["admitted_file_ids"],
                                                   f"{pid}.admitted_file_ids"))}
            if languages != {"rust", "lean"} or not linked:
                raise Refusal("subject index lacks both languages or the receipt linked module")
            for name, population in (("reachable_bodies", body_rows),
                                     ("refinement_certificates", cert_rows)):
                if roots[name] != canonical_root(population):
                    raise Refusal(f"subject {name} root differs from recomputed rows")
            return programs
        return self.memo("subject", produce)

    def scorecards(self) -> tuple[int, int, int]:
        def produce() -> tuple[int, int, int]:
            programs = self.subject()
            admitted = self.admission()
            join = exact(self.docs["body_join"], {"schema", "rows"}, "body join")
            if join["schema"] != "trust.two-language.g3.producer-body-join/v1":
                raise Refusal("body join has wrong schema")
            rust = self.docs["rust_scorecard"]
            lean = self.docs["lean_scorecard"]
            if rust.get("schema") != "trust.trust-ir.producer-scorecard.v1":
                raise Refusal("Rust producer scorecard has wrong schema")
            if lean.get("schema") != "trust.clean-corpus.scorecard/v2":
                raise Refusal("Lean producer scorecard has wrong schema")
            corpora = rust.get("corpora")
            if type(corpora) is not dict or not corpora:
                raise Refusal("Rust producer scorecard has no corpora")
            modes: dict[tuple[str, str, str], tuple[str, int]] = {}
            for corpus in corpora.values():
                if type(corpus) is not dict:
                    raise Refusal("malformed Rust corpus")
                for file in rows(corpus.get("files"), "Rust files"):
                    path = string(file.get("file") if type(file) is dict else None, "Rust file path")
                    if file.get("outcome") != "ok":
                        raise Refusal(f"Rust {path}: non-ok compiler outcome")
                    for body in rows(file.get("bodies"), f"Rust {path} bodies", nonempty=False):
                        if type(body) is not dict:
                            raise Refusal(f"Rust {path}: malformed body")
                        key = (path, string(body.get("def"), "Rust def"),
                               string(body.get("kind"), "Rust kind"))
                        if key in modes:
                            raise Refusal(f"duplicate Rust sampled body {key}")
                        mode = string(body.get("mode"), f"Rust {key}.mode")
                        samples = body.get("samples")
                        if mode != "Agreed" or type(samples) is not int or samples <= 0 or body.get("equal") is not True:
                            raise Refusal(f"Rust {key}: weak or uninterpreted differential mode {mode}")
                        if (type(body.get("unsupported")) is not int or body["unsupported"] != 0
                            or body.get("symbolic") is not False
                            or body.get("opaque_collapse") is not False or body.get("reasons") != []):
                            raise Refusal(f"Rust {key}: unsupported/symbolic/opaque body")
                        modes[key] = (mode, samples)
            lean_rows: dict[tuple[str, str], set[str]] = {}
            proof_only: set[tuple[str, str]] = set()
            for row in rows(lean.get("rows"), "Lean producer rows"):
                if type(row) is not list or len(row) != 5 or any(type(x) is not str for x in row):
                    raise Refusal("malformed Lean producer row")
                path, name, disposition, _, reason = row
                key = (string(path, "Lean path"), string(name, "Lean declaration"))
                allowed = {"emitted:gate", "general:compiled",
                           "general:not-computational", "planner-skipped"}
                if reason or disposition not in allowed:
                    raise Refusal(f"Lean {key}: non-gate or weak disposition {disposition!r}")
                dispositions = lean_rows.setdefault(key, set())
                if disposition in dispositions:
                    raise Refusal(f"Lean {key}: duplicate disposition {disposition}")
                dispositions.add(disposition)
            for key, values in lean_rows.items():
                if "general:not-computational" in values:
                    if not values <= {"general:not-computational", "planner-skipped"}:
                        raise Refusal(f"Lean {key}: proof-only and computational dispositions overlap")
                    proof_only.add(key)
                elif "emitted:gate" not in values:
                    raise Refusal("Lean scorecard has a computational row below carrier gate")
            for key in proof_only:
                del lean_rows[key]
            joined: set[tuple[str, str]] = set()
            rust_seen: set[tuple[str, str, str]] = set()
            lean_seen: set[tuple[str, str]] = set()
            samples_total = 0
            for row in rows(join["rows"], "body join rows"):
                row = exact(row, {"program_id", "file_id", "language", "source_body",
                    "source_kind", "body_id", "module_id"}, "body join row")
                pid = string(row["program_id"], "join program")
                bid = string(row["body_id"], "join body")
                language = row["language"]
                if ((pid, bid) in joined or pid not in programs or bid not in programs[pid]["bodies"]
                    or programs[pid]["bodies"][bid]["language"] != language):
                    raise Refusal(f"body join duplicates or mismatches {pid}/{bid}")
                joined.add((pid, bid))
                file_id = string(row["file_id"], "join admitted file ID")
                if (file_id not in admitted or admitted[file_id][0] != language
                    or file_id not in programs[pid]["files"]
                    or row["module_id"] != programs[pid]["owner_module"][bid]):
                    raise Refusal(f"body join has unknown or wrong-language admitted ID {file_id}")
                source_path = admitted[file_id][1]
                if language == "rust":
                    key = (source_path,
                           string(row["source_body"], "Rust join body"),
                           string(row["source_kind"], "Rust join kind"))
                    if key not in modes or key in rust_seen:
                        raise Refusal(f"Rust body join has missing or duplicate sampled body {key}")
                    rust_seen.add(key)
                    samples_total += modes[key][1]
                elif language == "lean":
                    key = (source_path,
                           string(row["source_body"], "Lean join body"))
                    if key not in lean_rows or key in lean_seen or row["source_kind"] != "computational":
                        raise Refusal(f"Lean body join has missing or duplicate carrier-gate row {key}")
                    lean_seen.add(key)
                else:
                    raise Refusal(f"unknown body join language {language!r}")
            expected = {(pid, bid) for pid, program in programs.items() for bid in program["bodies"]}
            if joined != expected or rust_seen != set(modes) or lean_seen != set(lean_rows):
                raise Refusal("scorecard/body join is not an exact duplicate-free population")
            return len(rust_seen), len(lean_seen), samples_total
        return self.memo("scorecards", produce)


def verify(check_id: str, cx: Context) -> None:
    if check_id == "owner_pinned_semantics_relation_observation_model":
        roles, _ = cx.policy()
        if set(roles) != SEMANTICS_ROLES:
            raise Refusal("owner semantics relation/observation role roster is incomplete")
        return  # Structural owner pin only; the receipt runner authenticates its signature.
    programs = cx.subject()
    bodies = sum(len(p["bodies"]) for p in programs.values())
    finite = sum(c["certificate_kind"] == "finite-exhaustive"
                 for p in programs.values() for c in p["certs"].values())
    if check_id == "every_body_universally_refined":
        raise Refusal(f"observed {bodies} body/certificate labels; no independent universal refinement replay")
    if check_id == "finite_domain_exhaustiveness_certificates_checked":
        raise Refusal(f"observed {finite} finite-exhaustive labels; no checked domain enumeration and per-element replay")
    if check_id == "refinement_certificates_biject_reachable_bodies":
        raise Refusal(f"observed {bodies}/{bodies} subject-index certificate/body pairs; no independent complete body census or authenticated certificate producer")
    if check_id == "certificates_bind_authorized_relation":
        raise Refusal(f"observed {bodies} owner-relation digest matches; certificate bytes have no independently checked derivation binding")
    if check_id == "whole_program_contextual_refinement":
        raise Refusal(f"observed {len(programs)} contextual evidence refs; no checked linked-program refinement replay")
    if check_id == "assumption_closure_checked":
        raise Refusal(f"observed {len(programs)} program closure labels; no independently checked assumption/theorem closure")
    rust_count, lean_count, samples = cx.scorecards()
    if check_id == "sampled_agreement_not_used_as_proof":
        raise Refusal(f"observed {rust_count} Rust Agreed rows/{samples} samples and {lean_count} Lean gate labels; no certificate-format checker excludes sampled evidence as proof")
    if check_id == "all_lean_rows_carrier_faithful_gate":
        raise Refusal(f"observed {lean_count} Lean emitted:gate labels; no independently checked carrier-faithfulness derivations")
    if check_id == "no_weak_or_uninterpreted_verdict_classes":
        raise Refusal(f"observed {rust_count} Rust Agreed and {lean_count} Lean gate labels; scorecards/body join are authored and cannot exclude unmeasured weak bodies")
    raise Refusal(f"unknown G4 check {check_id}")


def arguments() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--verify-evidence", required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--receipt")
    for flag in (
        "--toolchain-manifest", "--corpus-manifest", "--subject-graph", "--linked-module",
        "--release-artifact", "--authority-policy", "--policy-authorization",
        "--acceptance-run-id", "--source-revision", "--checker-sha256", "--evidence-sha256",
        "--toolchain-sha256", "--corpus-manifest-sha256", "--subject-graph-sha256",
        "--linked-module-sha256", "--release-artifact-sha256", "--authority-policy-sha256",
        "--policy-authorization-sha256",
    ):
        ap.add_argument(flag, required=True)
    ap.add_argument("--prior-gates-root")
    return ap.parse_args()


def main() -> int:
    args = arguments()
    diagnostics: list[str] = []
    cx: Context | None = None
    try:
        cx = Context(args)
    except (Refusal, OSError, UnicodeError, ValueError, TypeError, KeyError, RecursionError) as exc:
        diagnostics.append(f"common binding: {exc}")
    checks: list[dict[str, Any]] = []
    for check_id in REQUIRED:
        refs = [cx.refs[name] for name in CHECK_ARTIFACTS[check_id]] if cx else []
        passed = False
        try:
            if cx is None:
                raise Refusal("common G4 binding is invalid")
            verify(check_id, cx)
            passed = True
        except (Refusal, OSError, UnicodeError, ValueError, TypeError, KeyError, RecursionError) as exc:
            diagnostics.append(f"{check_id}: {exc}")
        checks.append({"id": check_id, "passed": passed, "artifacts": refs})
    verdict = {
        "schema": SCHEMA, "goal_id": GOAL, "gate": GATE, "checker": CHECKER,
        "repository_id": REPOSITORY_ID, "acceptance_run_id": args.acceptance_run_id,
        "checker_sha256": args.checker_sha256, "evidence_sha256": args.evidence_sha256,
        "source_revision": args.source_revision, "toolchain_sha256": args.toolchain_sha256,
        "corpus_manifest_sha256": args.corpus_manifest_sha256,
        "subject_graph_sha256": args.subject_graph_sha256,
        "linked_module_sha256": args.linked_module_sha256,
        "release_artifact_sha256": args.release_artifact_sha256,
        "authority_policy_sha256": args.authority_policy_sha256,
        "policy_authorization_sha256": args.policy_authorization_sha256,
        "prior_gates_root": args.prior_gates_root,
        "passed": not diagnostics and all(row["passed"] for row in checks), "checks": checks,
    }
    print(json.dumps(verdict, sort_keys=True))
    for line in diagnostics:
        print(f"G4: {line}", file=sys.stderr)
    return 0 if verdict["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
