#!/usr/bin/env python3
"""Schema-owned, fail-closed G6 obligation and proof-authority checker.

This is a diagnostic checker for the G6 conjuncts fixed by the top-level
completion schema. It accepts the receipt runner's isolated, standard-library
protocol and emits exactly one verdict. A content hash, a subject-index row,
``Certified``, or a solver's ``UNSAT`` is not independent proof authority.

The current compiler has typed Trust-IR obligation/certificate structures, but
no product-wide independent source-policy census, linked-module obligation
decoder, certificate replay, or external .olean closure attestation. Even a
structurally consistent subject-index relation is diagnostic-only: authored
rows cannot establish either population. Every conjunct remains red after
rejecting malformed evidence; no authored flag can enable one.
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
GATE = "G6"
CHECKER = "trust.two-language.g6.proof-authority/v2"
REPOSITORY_ID = "https://github.com/alabsystems/trust"
POLICY_SCHEMA = "trust.two-language.authority-policy/v2"
HEX = re.compile(r"^[0-9a-f]{64}$")
GIT_REVISION = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")

# Exactly REQUIRED_CHECKS["G6"] in scripts/two_language_completion_gate.py.
REQUIRED = (
    "source_policy_obligation_bijection",
    "zero_vacuous_weakened_or_tautological_obligations",
    "every_obligation_owned_and_typed",
    "trust_ir_native_verdict_authority",
    "every_favorable_verdict_kernel_rechecked",
    "proof_evidence_exact_digest_binding",
    "zero_open_dropped_or_unowned_obligations",
    "rust_contracts_typed_ssa_epoch_effect_identity_bound",
    "zero_design_only_contracts",
    "external_olean_transitive_trust_attested",
    "proof_dependency_closure_policy_clean",
    "obligation_certificate_bijection_matches_subject_index",
    "kani_parse_and_reject_surface",
    "kani_computational_image_exposed",
    "kani_canonical_proposition_image_exposed",
    "kani_computational_translation_validated_zero_authority",
    "kani_proposition_translation_validated_zero_authority",
    "verus_parse_and_reject_surface",
    "verus_computational_image_exposed",
    "verus_canonical_proposition_image_exposed",
    "verus_computational_translation_validated_zero_authority",
    "verus_proposition_translation_validated_zero_authority",
    "creusot_parse_and_reject_surface",
    "creusot_computational_image_exposed",
    "creusot_canonical_proposition_image_exposed",
    "creusot_computational_translation_validated_zero_authority",
    "creusot_proposition_translation_validated_zero_authority",
    "tla_parse_and_reject_surface",
    "tla_canonical_proposition_image_exposed",
    "tla_proposition_translation_validated_zero_authority",
    "required_policy_instances_biject_obligations",
    "formula_to_canonical_proposition_bridge_checked",
    "proof_grade_kernel_axiom_policy_exact",
    "compatibility_feature_manifests_exact",
    "compatibility_translations_universally_or_exhaustively_validated",
)

# These are evidence envelopes, not authority. No currently shipped producer
# emits an independently replayable G6 completion artifact under these schemas.
ARTIFACT_SCHEMAS = {
    "source_policy_census": "trust.two-language.g6.source-policy-census/v1",
    "native_obligation_census": "trust.two-language.g6.native-obligation-census/v1",
    "native_verdicts": "trust.two-language.g6.native-verdicts/v1",
    "kernel_replay": "trust.two-language.g6.kernel-replay/v1",
    "rust_contracts": "trust.two-language.g6.rust-contract-bindings/v1",
    "external_olean": "trust.two-language.g6.external-olean-closure/v1",
    "compatibility": "trust.two-language.g6.compatibility-translations/v1",
}
ARTIFACTS = tuple(ARTIFACT_SCHEMAS)
# Exactly the obligation and proof-certificate row keys the receipt runner
# admits (``typed_rows`` in scripts/two_language_completion_gate.py). A row
# carrying any other key -- ``program_id`` included, which would otherwise
# re-bind the row to another program inside the root -- is refused.
OBLIGATION_KEYS = {
    "id", "body_id", "function_identity_sha256", "formula_sha256",
    "canonical_proposition_sha256", "formula_encoder_id", "formula_encoder_sha256",
    "proposition_encoder_id", "proposition_encoder_sha256",
    "formula_to_proposition_evidence", "policy_rule_id", "ssa_epoch_sha256",
    "effect_summary_sha256", "module_id",
}
CERTIFICATE_KEYS = {
    "id", "obligation_id", "body_id", "function_identity_sha256", "proposition_sha256",
    "ssa_epoch_sha256", "effect_summary_sha256", "module_id", "kernel_environment_id",
    "kernel_environment_sha256", "proof_grade", "axiom_allowlist_root_sha256", "evidence",
}
OBLIGATION_CLASSES = {
    "safety", "functional", "termination", "ownership", "unsafe_memory", "temporal",
}
COMPATIBILITY_CAPABILITIES = {
    "kani": {"nondeterminism", "assume", "harnesses"},
    "verus": {"ghost", "tracked", "triggers", "fuel", "broadcast", "calculations"},
    "creusot": {"prophecy", "mutable_borrows", "machine_integers", "contracts"},
    "tla_plus": {"fairness", "stuttering", "infinite_behaviors", "temporal_operators"},
}


class Refusal(Exception):
    """Evidence does not establish a G6 conjunct."""


def exact(value: Any, keys: set[str], where: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        raise Refusal(f"{where}: expected exactly {sorted(keys)}")
    return value


def records(value: Any, where: str, *, nonempty: bool = True) -> list[dict[str, Any]]:
    if not isinstance(value, list) or (nonempty and not value):
        raise Refusal(f"{where}: expected {'non-empty ' if nonempty else ''}array")
    if not all(isinstance(row, dict) for row in value):
        raise Refusal(f"{where}: every row must be an object")
    return value


def name(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value or value.strip() != value:
        raise Refusal(f"{where}: expected non-empty trimmed string")
    return value


def digest(value: Any, where: str) -> str:
    if not isinstance(value, str) or not HEX.fullmatch(value):
        raise Refusal(f"{where}: expected lowercase SHA-256")
    return value


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_root(rows: list[dict[str, Any]]) -> str:
    ordered = sorted(rows, key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")))
    return sha256(json.dumps(ordered, sort_keys=True, separators=(",", ":")).encode("utf-8"))


def unique_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def json_object(data: bytes, where: str) -> dict[str, Any]:
    try:
        _trust_text = data.decode("utf-8")
        if _trust_json_nesting_depth(_trust_text) > TRUST_MAX_JSON_DEPTH:
            raise ValueError(f"JSON nests deeper than {TRUST_MAX_JSON_DEPTH}")
        value = json.loads(_trust_text, object_pairs_hook=unique_pairs,
                           parse_constant=lambda token: (_ for _ in ()).throw(ValueError(token)))
        json.dumps(value, allow_nan=False).encode("utf-8")
    except (UnicodeError, ValueError, RecursionError) as exc:
        raise Refusal(f"{where}: invalid strict JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise Refusal(f"{where}: expected JSON object")
    return value


class Context:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        # Resolved inside the try below: Python 3.9 raises RuntimeError on a
        # symlink loop, and an escaped exception would print no verdict.
        self.root = Path(args.root)
        self.errors: list[str] = []
        self.refs: dict[str, dict[str, str]] = {}
        self.docs: dict[str, dict[str, Any]] = {}
        self.common: dict[str, dict[str, Any]] = {}
        self._policy: dict[str, Any] | None = None
        self._subject_checked = False
        try:
            try:
                self.root = self.root.resolve()
            except (OSError, ValueError, RuntimeError) as exc:
                raise Refusal(f"--root cannot be resolved: {exc}") from exc
            if not self.root.is_dir():
                raise Refusal("--root must be an existing directory")
            digest(args.acceptance_run_id, "--acceptance-run-id")
            for key in (
                "checker_sha256", "evidence_sha256", "toolchain_sha256",
                "corpus_manifest_sha256", "subject_graph_sha256", "linked_module_sha256",
                "release_artifact_sha256", "authority_policy_sha256",
                "policy_authorization_sha256",
            ):
                digest(getattr(args, key), f"--{key.replace('_', '-')}")
            checker_bytes = Path(__file__).read_bytes()
            if sha256(checker_bytes) != args.checker_sha256:
                raise Refusal("checker snapshot does not match --checker-sha256")
            bound = (
                ("toolchain_manifest", "toolchain_sha256"),
                ("corpus_manifest", "corpus_manifest_sha256"),
                ("subject_graph", "subject_graph_sha256"),
                ("linked_module", "linked_module_sha256"),
                ("release_artifact", "release_artifact_sha256"),
                ("authority_policy", "authority_policy_sha256"),
                ("policy_authorization", "policy_authorization_sha256"),
            )
            for path_key, hash_key in bound:
                path = self.absolute_path(getattr(args, path_key), path_key)
                data = path.read_bytes()
                if sha256(data) != getattr(args, hash_key):
                    raise Refusal(f"{path_key}: receipt-bound content hash mismatch")
                if path_key in {"subject_graph", "authority_policy"}:
                    self.common[path_key] = json_object(data, path_key)
            evidence = self.absolute_path(args.verify_evidence, "evidence")
            data = evidence.read_bytes()
            if sha256(data) != args.evidence_sha256:
                raise Refusal("evidence: receipt-bound content hash mismatch")
            bundle = exact(json_object(data, "evidence"),
                           {"schema", "gate", "checker", "artifacts"}, "evidence")
            if (bundle["schema"], bundle["gate"], bundle["checker"]) != (
                EVIDENCE_SCHEMA, GATE, CHECKER
            ):
                raise Refusal("evidence: wrong schema, gate, or checker")
            artifact_rows = exact(bundle["artifacts"], set(ARTIFACTS), "evidence.artifacts")
            used_paths: set[Path] = set()
            for key in ARTIFACTS:
                row = exact(artifact_rows[key], {"path", "sha256"}, f"artifact {key}")
                path = self.relative_path(row["path"], f"artifact {key}")
                if path in used_paths:
                    raise Refusal(f"artifact {key}: duplicate artifact path")
                used_paths.add(path)
                expected = digest(row["sha256"], f"artifact {key}.sha256")
                content = path.read_bytes()
                if sha256(content) != expected:
                    raise Refusal(f"artifact {key}: content hash mismatch")
                self.refs[key] = {"path": row["path"], "sha256": expected}
                self.docs[key] = json_object(content, f"artifact {key}")
        except (Refusal, OSError) as exc:
            self.errors.append(str(exc))

    def absolute_path(self, value: Any, where: str) -> Path:
        raw = name(value, where)
        path = Path(raw)
        if not path.is_absolute():
            raise Refusal(f"{where}: expected absolute receipt-bound path")
        try:
            resolved = path.resolve()
        except (OSError, ValueError, RuntimeError) as exc:
            raise Refusal(f"{where}: path cannot be resolved: {exc}") from exc
        if not resolved.is_relative_to(self.root) or not path.is_file():
            raise Refusal(f"{where}: file is absent or escapes --root")
        return path

    def relative_path(self, value: Any, where: str) -> Path:
        raw = name(value, where)
        if "\0" in raw or raw.startswith("/") or "\\" in raw or any(
            part in {"", ".", ".."} for part in raw.split("/")
        ):
            raise Refusal(f"{where}: path must be canonical and root-relative")
        path = self.root
        for part in raw.split("/"):
            path = path / part
            try:
                is_link = path.is_symlink()
            except OSError as exc:
                raise Refusal(f"{where}: path cannot be inspected: {exc}") from exc
            if is_link:
                raise Refusal(f"{where}: symlink path component is not allowed")
        try:
            resolved = path.resolve()
        except (OSError, ValueError, RuntimeError) as exc:
            raise Refusal(f"{where}: path cannot be resolved: {exc}") from exc
        if not resolved.is_relative_to(self.root) or not path.is_file():
            raise Refusal(f"{where}: file is absent or escapes --root")
        return path

    def named_ref(self, value: Any, wanted: str, where: str) -> dict[str, Any]:
        row = exact(value, {"id", "path", "sha256"}, where)
        if row["id"] != wanted:
            raise Refusal(f"{where}: expected owner contract {wanted}")
        path = self.relative_path(row["path"], where)
        if sha256(data := path.read_bytes()) != digest(row["sha256"], f"{where}.sha256"):
            raise Refusal(f"{where}: owner contract hash mismatch")
        return json_object(data, where)

    def policy(self) -> dict[str, Any]:
        if self._policy is not None:
            return self._policy
        policy = self.common["authority_policy"]
        if (policy.get("schema"), policy.get("goal_id"), policy.get("repository_id"),
                policy.get("authorized_source_revision"),
                policy.get("authorized_acceptance_run_id")) != (
            POLICY_SCHEMA, GOAL, REPOSITORY_ID,
            self.args.source_revision, self.args.acceptance_run_id,
        ):
            raise Refusal("owner policy: wrong schema, goal, repository, source, or run identity")
        contracts = exact(policy.get("contracts"), {
            "admission", "semantics", "obligations", "proof_authority",
            "compatibility_surfaces", "codegen_surface", "acceptance_environment",
        }, "owner contracts")
        obligations = self.named_ref(contracts["obligations"],
                                     "trust.two-language.contract.obligations", "obligation contract")
        proof = self.named_ref(contracts["proof_authority"],
                               "trust.two-language.contract.proof-authority", "proof contract")
        compatibility = self.named_ref(contracts["compatibility_surfaces"],
                                       "trust.two-language.contract.compatibility-surfaces",
                                       "compatibility contract")
        for doc, schema, where in (
            (obligations, "trust.two-language.obligation-contract/v1", "obligation contract"),
            (proof, "trust.two-language.proof-authority-contract/v1", "proof contract"),
            (compatibility, "trust.two-language.compatibility-surfaces-contract/v2", "compatibility contract"),
        ):
            if (doc.get("schema"), doc.get("goal_id"), doc.get("repository_id")) != (
                schema, GOAL, REPOSITORY_ID
            ):
                raise Refusal(f"{where}: wrong schema or identity")
        formula_encoder = exact(obligations.get("formula_encoder"),
                                {"id", "path", "sha256"}, "owner formula encoder")
        proposition_encoder = exact(proof.get("canonical_proposition_encoder"),
                                    {"id", "path", "sha256"}, "owner proposition encoder")
        for label, row in (("formula", formula_encoder), ("proposition", proposition_encoder)):
            name(row["id"], f"owner {label} encoder id")
            path = self.relative_path(row["path"], f"owner {label} encoder")
            if sha256(path.read_bytes()) != digest(row["sha256"], f"owner {label} encoder"):
                raise Refusal(f"owner {label} encoder: content hash mismatch")
        rules: dict[str, str] = {}
        for row in records(obligations.get("rules"), "owner obligation rules"):
            exact(row, {"id", "class", "applicability", "formula_schema"}, "owner obligation rule")
            rule_id = name(row["id"], "owner obligation rule id")
            if rule_id in rules or row["class"] not in OBLIGATION_CLASSES:
                raise Refusal("owner obligation rules: duplicate or unknown class")
            rules[rule_id] = row["class"]
        if set(rules.values()) != OBLIGATION_CLASSES:
            raise Refusal("owner obligation rules: required classes are incomplete")
        if proof.get("denied_axioms") != ["sorryAx"]:
            raise Refusal("proof contract: sorryAx must be denied")
        kernels: dict[str, dict[str, Any]] = {}
        for row in records(proof.get("kernels"), "owner kernels"):
            exact(row, {"id", "environment_sha256", "artifact", "proof_grades",
                        "axiom_allowlist_root_sha256"}, "owner kernel")
            key = name(row["id"], "owner kernel id")
            if key in kernels:
                raise Refusal(f"owner kernel {key}: duplicate id")
            digest(row["environment_sha256"], f"owner kernel {key} environment")
            digest(row["axiom_allowlist_root_sha256"], f"owner kernel {key} axiom policy")
            grades = row["proof_grades"]
            if (not isinstance(grades, list) or not grades
                or any(not isinstance(g, str) or not g for g in grades)
                or len(grades) != len(set(grades))):
                raise Refusal(f"owner kernel {key}: invalid proof grades")
            kernels[key] = row
        surfaces = exact(compatibility.get("surfaces"), set(COMPATIBILITY_CAPABILITIES),
                         "owner compatibility surfaces")
        for surface, required in COMPATIBILITY_CAPABILITIES.items():
            row = surfaces[surface]
            if not isinstance(row, dict) or row.get("required") is not True:
                raise Refusal(f"owner compatibility surface {surface}: not required")
            capabilities = row.get("semantic_capabilities")
            if (not isinstance(capabilities, list)
                or not all(isinstance(item, str) for item in capabilities)
                or len(capabilities) != len(set(capabilities))
                or set(capabilities) != required):
                raise Refusal(f"owner compatibility surface {surface}: incomplete feature manifest")
        self._policy = {
            "rules": rules, "kernels": kernels, "compatibility": surfaces,
            "formula_encoder": formula_encoder,
            "proposition_encoder": proposition_encoder,
        }
        return self._policy

    def artifact(self, key: str) -> dict[str, Any]:
        doc = self.docs[key]
        if doc.get("schema") != ARTIFACT_SCHEMAS[key]:
            raise Refusal(f"{key}: wrong diagnostic artifact schema")
        return doc

    def subject_relation(self) -> None:
        """Check authored subject rows and roots only; never decode a module."""
        if self._subject_checked:
            return
        policy = self.policy()
        subject = self.common["subject_graph"]
        if (subject.get("schema"), subject.get("goal_id"),
            subject.get("acceptance_run_id"), subject.get("source_revision")) != (
            "trust.two-language.subject-index/v3", GOAL,
            self.args.acceptance_run_id, self.args.source_revision
        ):
            raise Refusal("subject index: wrong schema or run/source identity")
        roots = subject.get("roots")
        if not isinstance(roots, dict):
            raise Refusal("subject index: missing roots")
        observed_obligations: list[dict[str, Any]] = []
        observed_proofs: list[dict[str, Any]] = []
        program_ids: set[str] = set()
        for program in records(subject.get("programs"), "subject programs"):
            pid = name(program.get("id"), "program id")
            if pid in program_ids:
                raise Refusal(f"subject program {pid}: duplicate id")
            program_ids.add(pid)
            bodies: dict[str, dict[str, Any]] = {}
            for row in records(program.get("bodies"), f"{pid} bodies"):
                bid = name(row.get("id"), f"{pid} body id")
                if bid in bodies:
                    raise Refusal(f"{pid}: duplicate body {bid}")
                bodies[bid] = row
            obligations = records(program.get("obligations"), f"{pid} obligations")
            certificates = records(program.get("proof_certificates"), f"{pid} proof certificates")
            modules = records(program.get("modules"), f"{pid} modules")
            by_id: dict[str, dict[str, Any]] = {}
            for index, row in enumerate(obligations):
                exact(row, OBLIGATION_KEYS, f"{pid} obligations[{index}]")
                oid = name(row.get("id"), f"{pid} obligation id")
                if oid in by_id:
                    raise Refusal(f"{pid}: duplicate obligation {oid}")
                by_id[oid] = row
                body = bodies.get(name(row.get("body_id"), f"{pid} obligation {oid} body_id"))
                if body is None:
                    raise Refusal(f"{pid} obligation {oid}: body is missing")
                for field in ("function_identity_sha256", "ssa_epoch_sha256", "effect_summary_sha256"):
                    if digest(row.get(field), f"{pid} obligation {oid}.{field}") != body.get(field):
                        raise Refusal(f"{pid} obligation {oid}: {field} differs from body")
                for field in ("formula_sha256", "canonical_proposition_sha256"):
                    digest(row.get(field), f"{pid} obligation {oid}.{field}")
                for prefix in ("formula", "proposition"):
                    encoder = policy[f"{prefix}_encoder"]
                    if (row.get(f"{prefix}_encoder_id") != encoder["id"]
                        or row.get(f"{prefix}_encoder_sha256") != encoder["sha256"]):
                        raise Refusal(f"{pid} obligation {oid}: {prefix} encoder differs from owner")
                bridge = exact(row.get("formula_to_proposition_evidence"),
                               {"path", "sha256"}, f"{pid} obligation {oid} formula bridge")
                bridge_path = self.relative_path(bridge["path"], f"{pid} obligation {oid} formula bridge")
                if sha256(bridge_path.read_bytes()) != digest(
                    bridge["sha256"], f"{pid} obligation {oid} formula bridge"
                ):
                    raise Refusal(f"{pid} obligation {oid}: formula bridge hash mismatch")
                rule_id = name(row.get("policy_rule_id"), f"{pid} obligation {oid} policy_rule_id")
                if rule_id not in policy["rules"]:
                    raise Refusal(f"{pid} obligation {oid}: unknown owner policy rule")
                name(row.get("module_id"), f"{pid} obligation {oid} module")
                observed_obligations.append({**row, "program_id": pid})
            proof_ids: set[str] = set()
            certified: list[str] = []
            for index, row in enumerate(certificates):
                exact(row, CERTIFICATE_KEYS, f"{pid} proof_certificates[{index}]")
                cid = name(row.get("id"), f"{pid} certificate id")
                if cid in proof_ids:
                    raise Refusal(f"{pid}: duplicate certificate {cid}")
                proof_ids.add(cid)
                oid = name(row.get("obligation_id"), f"{pid} certificate {cid} obligation_id")
                name(row.get("body_id"), f"{pid} certificate {cid} body_id")
                obligation = by_id.get(oid)
                if obligation is None:
                    raise Refusal(f"{pid} certificate {cid}: unknown obligation")
                certified.append(oid)
                for field in ("body_id", "function_identity_sha256", "ssa_epoch_sha256",
                              "effect_summary_sha256", "module_id"):
                    if row.get(field) != obligation.get(field):
                        raise Refusal(f"{pid} certificate {cid}: {field} differs from obligation")
                if row.get("proposition_sha256") != obligation.get("canonical_proposition_sha256"):
                    raise Refusal(f"{pid} certificate {cid}: proposition differs from obligation")
                kernel = policy["kernels"].get(
                    name(row.get("kernel_environment_id"), f"{pid} certificate {cid} kernel_environment_id"))
                if not kernel or row.get("kernel_environment_sha256") != kernel["environment_sha256"]:
                    raise Refusal(f"{pid} certificate {cid}: unapproved kernel environment")
                if (row.get("proof_grade") not in kernel["proof_grades"]
                    or row.get("axiom_allowlist_root_sha256") != kernel["axiom_allowlist_root_sha256"]):
                    raise Refusal(f"{pid} certificate {cid}: grade or axiom policy differs from owner")
                evidence = exact(row.get("evidence"), {"path", "sha256"}, f"{pid} certificate {cid} evidence")
                path = self.relative_path(evidence["path"], f"{pid} certificate {cid} evidence")
                if sha256(path.read_bytes()) != digest(evidence["sha256"], f"{pid} certificate {cid} evidence"):
                    raise Refusal(f"{pid} certificate {cid}: evidence content hash mismatch")
                observed_proofs.append({**row, "program_id": pid})
            if sorted(certified) != sorted(by_id):
                raise Refusal(f"{pid}: obligation/certificate relation is not a bijection")
            obligation_partition: list[str] = []
            proof_partition: list[str] = []
            obligation_modules: dict[str, str] = {}
            proof_modules: dict[str, str] = {}
            module_ids: set[str] = set()
            for module in modules:
                mid = name(module.get("id"), f"{pid} module id")
                if mid in module_ids:
                    raise Refusal(f"{pid}: duplicate module {mid}")
                module_ids.add(mid)
                for field, destination in (("obligation_ids", obligation_partition),
                                           ("proof_certificate_ids", proof_partition)):
                    values = module.get(field)
                    if not isinstance(values, list) or any(not isinstance(x, str) for x in values):
                        raise Refusal(f"{pid} module {mid}: invalid {field}")
                    destination.extend(values)
                    destinations = obligation_modules if field == "obligation_ids" else proof_modules
                    for value in values:
                        if value in destinations:
                            raise Refusal(f"{pid}: duplicate {field} partition member {value}")
                        destinations[value] = mid
            if (sorted(obligation_partition) != sorted(by_id)
                or sorted(proof_partition) != sorted(proof_ids)):
                raise Refusal(f"{pid}: modules do not exactly partition obligation and proof IDs")
            for row in obligations:
                if row["module_id"] != obligation_modules.get(row["id"]):
                    raise Refusal(f"{pid}: obligation's module differs from its partition")
            for row in certificates:
                if row["module_id"] != proof_modules.get(row["id"]):
                    raise Refusal(f"{pid}: certificate's module differs from its partition")
        for key, rows in (("obligations", observed_obligations),
                          ("proof_certificates", observed_proofs)):
            if digest(roots.get(key), f"subject root {key}") != canonical_root(rows):
                raise Refusal(f"subject root {key}: does not match complete authored rows")
        self._subject_checked = True


def verify(check_id: str, cx: Context) -> None:
    # Validate the relevant diagnostic envelope, then explicitly refuse what
    # that envelope cannot establish. No authored result/status bit is read.
    if check_id == "obligation_certificate_bijection_matches_subject_index":
        cx.subject_relation()
        raise Refusal(
            "authored subject-index obligation/proof rows and roots are structurally consistent, "
            "but independent complete source-policy, decoded Trust-IR obligation, and replayed "
            "certificate populations are absent"
        )
    if check_id.startswith(("kani_", "verus_", "creusot_", "tla_")) or check_id in {
        "compatibility_feature_manifests_exact",
        "compatibility_translations_universally_or_exhaustively_validated",
    }:
        cx.policy()
        cx.artifact("compatibility")
        raise Refusal("compatibility declarations and supplied images are not independent parse, elaboration, or universal/exhaustive translation evidence")
    if check_id in {"external_olean_transitive_trust_attested", "proof_dependency_closure_policy_clean"}:
        cx.policy()
        cx.artifact("external_olean")
        raise Refusal("external .olean loading/closure remains unsupported; no independently attested transitive axiom policy or sorryAx audit exists")
    if check_id in {"rust_contracts_typed_ssa_epoch_effect_identity_bound", "zero_design_only_contracts"}:
        cx.subject_relation()
        cx.artifact("rust_contracts")
        raise Refusal("contract report is not a typed decode of every live Trust-IR clause; DesignOnly and SSA/epoch/effect binding cannot be excluded")
    if check_id in {"every_favorable_verdict_kernel_rechecked", "proof_evidence_exact_digest_binding",
                    "formula_to_canonical_proposition_bridge_checked", "proof_grade_kernel_axiom_policy_exact"}:
        cx.subject_relation()
        cx.artifact("kernel_replay")
        raise Refusal("no independent kernel execution replays each exact canonical proposition, certificate, environment, dependency, and module digest")
    if check_id == "trust_ir_native_verdict_authority":
        cx.subject_relation()
        cx.artifact("native_verdicts")
        raise Refusal("a native/compatibility verdict-parity run bound to the decoded linked Trust-IR module is not available")
    if check_id in {"source_policy_obligation_bijection", "required_policy_instances_biject_obligations"}:
        cx.subject_relation()
        cx.artifact("source_policy_census")
        cx.artifact("native_obligation_census")
        raise Refusal("source operations and policy instances lack an independent complete census joined to decoded Trust-IR obligations")
    if check_id in {"zero_vacuous_weakened_or_tautological_obligations",
                    "every_obligation_owned_and_typed", "zero_open_dropped_or_unowned_obligations"}:
        cx.subject_relation()
        cx.artifact("native_obligation_census")
        raise Refusal("authored obligation rows do not establish formula nonvacuity, ownership, complete birth, or absence of dropped/open native goals")
    raise Refusal(f"unknown G6 check {check_id}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-evidence", required=True)
    parser.add_argument("--root", required=True)
    parser.add_argument("--receipt")
    for flag in (
        "--toolchain-manifest", "--corpus-manifest", "--subject-graph", "--linked-module",
        "--release-artifact", "--authority-policy", "--policy-authorization",
        "--acceptance-run-id", "--source-revision", "--checker-sha256", "--evidence-sha256",
        "--toolchain-sha256", "--corpus-manifest-sha256", "--subject-graph-sha256",
        "--linked-module-sha256", "--release-artifact-sha256", "--authority-policy-sha256",
        "--policy-authorization-sha256",
    ):
        parser.add_argument(flag, required=True)
    parser.add_argument("--prior-gates-root")
    args = parser.parse_args()
    cx = Context(args)
    diagnostics = list(cx.errors)
    if not GIT_REVISION.fullmatch(args.source_revision):
        diagnostics.append("source_revision must be a lowercase 40- or 64-hex Git revision")
    if args.receipt is not None or args.prior_gates_root is not None:
        diagnostics.append("G6 is pre-seal and must not receive a receipt or prior-gates root")
    initial_invalid = bool(diagnostics)
    checks: list[dict[str, Any]] = []
    for check_id in REQUIRED:
        refs = list(cx.refs.values())
        passed = False
        try:
            if initial_invalid:
                raise Refusal("invalid bound G6 input")
            verify(check_id, cx)
            passed = True
        except (Refusal, OSError, UnicodeError, ValueError, TypeError, KeyError, RecursionError) as exc:
            diagnostics.append(f"{check_id}: {exc}")
        checks.append({"id": check_id, "passed": passed, "artifacts": refs})
    passed = not diagnostics and all(row["passed"] for row in checks)
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
        "prior_gates_root": args.prior_gates_root, "passed": passed, "checks": checks,
    }
    print(json.dumps(verdict, sort_keys=True))
    for line in diagnostics:
        print(f"G6: {line}", file=sys.stderr)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
