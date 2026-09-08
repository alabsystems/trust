#!/usr/bin/env python3
"""Structural release-receipt gate for TRUST-TWO-LANGUAGE-100.

This is the top-level conjunction for the goal recorded in
``docs/TWO_LANGUAGE_100_PERCENT_GOAL.md``.  It does not reinterpret a producer
percentage and it does not claim to prove the semantic facts recorded by a
specialized checker.  It verifies that:

* one clean source revision, toolchain identity, and corpus manifest are bound;
* exactly G1 through G8 have distinct, content-hashed checker evidence;
* every gate's schema-owned, source-controlled checker is content-bound and
  re-executed against that evidence;
* every required conjunct reported by the fresh checker run is affirmative;
* every conjunct binds at least one existing, content-hashed evidence artifact;
* no author-provided ``complete`` or ``vision_complete`` bit can mint success.

The evidence-producing checkers remain responsible for the semantics of their
artifacts.  This script is the fail-closed, checker-executing structural
conjunction over them.  An authored JSON ``passed`` bit is never sufficient.

Usage:
    python3 scripts/two_language_completion_gate.py \
        --receipt build/two-language-completion/receipt.json --root . \
        --trusted-owner-key /external/trust-owner.pub

Exit 0 means the structural receipt is complete.  Exit 1 means incomplete or
malformed evidence.  A structurally green receipt is necessary, not sufficient,
for believing a checker whose own implementation has not been reviewed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


SCHEMA = "trust.two-language.completion/v2"
CHECKER_VERDICT_SCHEMA = "trust.two-language.gate-checker-verdict/v2"
VERDICT_SCHEMA = "trust.two-language.completion-verdict/v2"
GOAL_ID = "TRUST-TWO-LANGUAGE-100"
GATES = tuple(f"G{i}" for i in range(1, 9))
CHECKER_IDS = {
    "G1": "trust.two-language.g1.rust-input/v2",
    "G2": "trust.two-language.g2.lean-input/v2",
    "G3": "trust.two-language.g3.producer-totality/v2",
    "G4": "trust.two-language.g4.semantic-faithfulness/v2",
    "G5": "trust.two-language.g5.mixed-linking/v2",
    "G6": "trust.two-language.g6.proof-authority/v2",
    "G7": "trust.two-language.g7.codegen-authority/v3",
    "G8": "trust.two-language.g8.release-reproducibility/v3",
}

REPOSITORY_ID = "https://github.com/alabsystems/trust"
TOOLCHAIN_SCHEMA = "trust.two-language.toolchain-manifest/v1"
CORPUS_SCHEMA = "trust.two-language.corpus-manifest/v1"
SUBJECT_GRAPH_SCHEMA = "trust.two-language.subject-index/v3"
POLICY_SCHEMA = "trust.two-language.authority-policy/v2"
POLICY_AUTH_SCHEMA = "trust.two-language.policy-authorization/v1"
POLICY_SIGNATURE_NAMESPACE = "trust-two-language-policy"
SSH_KEYGEN = Path("/usr/bin/ssh-keygen")

AUTHORITY_CONTRACTS = {
    "admission": (
        "trust.two-language.contract.admission",
        "trust.two-language.admission-contract/v1",
    ),
    "semantics": (
        "trust.two-language.contract.semantics",
        "trust.two-language.semantics-contract/v1",
    ),
    "obligations": (
        "trust.two-language.contract.obligations",
        "trust.two-language.obligation-contract/v1",
    ),
    "proof_authority": (
        "trust.two-language.contract.proof-authority",
        "trust.two-language.proof-authority-contract/v1",
    ),
    "compatibility_surfaces": (
        "trust.two-language.contract.compatibility-surfaces",
        "trust.two-language.compatibility-surfaces-contract/v2",
    ),
    "codegen_surface": (
        "trust.two-language.contract.codegen-surface",
        "trust.two-language.codegen-surface-contract/v2",
    ),
    "acceptance_environment": (
        "trust.two-language.contract.acceptance-environment",
        "trust.two-language.acceptance-environment-contract/v1",
    ),
}
SEMANTICS_DEFINITIONS = {
    "rust_language",
    "lean_language",
    "trust_ir",
    "rust_to_trust_ir_refinement",
    "lean_to_trust_ir_refinement",
    "observation_model",
    "undefined_behavior",
    "abi_memory_model",
}
OBLIGATION_CLASSES = {
    "safety",
    "functional",
    "termination",
    "ownership",
    "unsafe_memory",
    "temporal",
}
COMPATIBILITY_CAPABILITIES = {
    "kani": {"nondeterminism", "assume", "harnesses"},
    "verus": {"ghost", "tracked", "triggers", "fuel", "broadcast", "calculations"},
    "creusot": {"prophecy", "mutable_borrows", "machine_integers", "contracts"},
    "tla_plus": {"fairness", "stuttering", "infinite_behaviors", "temporal_operators"},
}
COMPATIBILITY_IMAGE_DESTINATIONS = {
    "kani": {
        "computational": [
            "rust:nondeterministic-program",
            "trust-ir:nondeterministic-program",
        ],
        "proposition": ["lean:canonical-obligation"],
    },
    "verus": {
        "computational": ["rust:canonical-clause"],
        "proposition": ["lean:canonical-term"],
    },
    "creusot": {
        "computational": ["rust:canonical-clause"],
        "proposition": ["lean:canonical-term"],
    },
    "tla_plus": {
        "computational": [],
        "proposition": ["lean:canonical-temporal-term"],
    },
}
ACCEPTANCE_RUN_MODES = {
    "cold_build",
    "warm_build",
    "cross_crate",
    "mixed_language",
    "tests",
    "release",
}
TOOLCHAIN_ROLES = {
    "trustc",
    "rust_frontend",
    "lean_frontend",
    "clean_kernel",
    "trust_ir_producer",
    "trust_ir_linker",
    "trust_codegen",
    "trust_router",
    "proof_reconstructor",
    "runtime",
    "linker",
    "top_verifier",
    "python",
    "ssh_keygen",
}

CODEGEN_CELL_FIELDS = (
    "target_id",
    "abi_id",
    "crate_type",
    "runtime_id",
    "startup_id",
    "linker_id",
    "unwind_mode",
    "debug_mode",
    "opt_level",
    "profile_id",
)
CODEGEN_TARGET_AXIS_BY_CELL_FIELD = {
    "abi_id": "abis",
    "crate_type": "crate_types",
    "runtime_id": "runtimes",
    "startup_id": "startups",
    "linker_id": "linkers",
    "unwind_mode": "unwind_modes",
    "debug_mode": "debug_modes",
    "opt_level": "opt_levels",
    "profile_id": "profiles",
}

# The receipt cannot choose the program that decides a gate.  Each checker is
# fixed by this schema and must be tracked at the exact source revision being
# accepted.  These checkers are intentionally absent until their corresponding
# gates are implemented; therefore the current product cannot manufacture a
# green top-level receipt from hand-authored JSON.
CHECKER_PATHS = {
    "G1": "scripts/completion_gates/check_g1_rust_input.py",
    "G2": "scripts/completion_gates/check_g2_lean_input.py",
    "G3": "scripts/completion_gates/check_g3_producer_totality.py",
    "G4": "scripts/completion_gates/check_g4_semantic_faithfulness.py",
    "G5": "scripts/completion_gates/check_g5_mixed_linking.py",
    "G6": "scripts/completion_gates/check_g6_proof_authority.py",
    "G7": "scripts/completion_gates/check_g7_codegen_authority.py",
    "G8": "scripts/completion_gates/check_g8_release_reproducibility.py",
}

# These are deliberately exact sets.  Adding a new meaning to a gate requires
# a schema revision rather than silently accepting a receipt produced under a
# different definition of "100%".
REQUIRED_CHECKS: dict[str, tuple[str, ...]] = {
    "G1": (
        "pinned_upstream_rust_revision",
        "full_upstream_rust_surface",
        "all_reachable_rust_bodies_inventoried",
        "zero_upstream_rust_semantic_regressions",
        "non_applicable_rust_harness_rows_only",
        "owner_pinned_rust_surface_and_accept_reject_parity",
        "rust_frontend_constructor_totality",
        "rust_macro_build_asm_ffi_dynamic_runtime_surface",
    ),
    "G2": (
        "pinned_upstream_lean_revision",
        "vanilla_lean_build",
        "external_olean_and_dependency_graphs",
        "all_lean_computational_declarations_inventoried",
        "zero_upstream_lean_semantic_regressions",
        "non_applicable_lean_harness_rows_only",
        "owner_pinned_lean_surface_and_accept_reject_parity",
        "lean_elaborator_constructor_totality",
        "lean_macro_io_unsafe_ffi_surface",
    ),
    "G3": (
        "admitted_file_manifest_exact",
        "reachable_body_census_exact",
        "rust_zero_producer_residue",
        "lean_zero_producer_residue",
        "all_joined_modules_valid",
        "no_denominator_exclusions",
        "subject_index_roots_match",
    ),
    "G4": (
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
    ),
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
    "G6": (
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
    "G8": (
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
    ),
}

HEX_DIGEST = re.compile(r"^[0-9a-f]{64}$")
GIT_REVISION = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
CHECKER_ID = re.compile(r"^[a-z0-9][a-z0-9._/-]*$")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _canonical_json_sha256(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _git(root: Path, *args: str) -> tuple[int, str]:
    process = subprocess.run(
        ["git", "-C", str(root), *args],
        check=False,
        capture_output=True,
        text=True,
    )
    return process.returncode, process.stdout.strip()


class ReceiptValidator:
    def __init__(
        self,
        root: Path,
        receipt_path: Path,
        trusted_owner_key: Path | None,
    ):
        self.root = root.resolve()
        self.receipt_path = receipt_path.resolve()
        self.trusted_owner_key = (
            trusted_owner_key.resolve() if trusted_owner_key is not None else None
        )
        self.trusted_owner_fingerprint: str | None = None
        self.errors: list[str] = []
        self.bound_files: dict[Path, str] = {}
        self.prior_gates_root: str | None = None

    def error(self, location: str, detail: str) -> None:
        self.errors.append(f"{location}: {detail}")

    def exact_keys(self, value: Any, expected: set[str], location: str) -> bool:
        if not isinstance(value, dict):
            self.error(location, "must be an object")
            return False
        actual = set(value)
        missing = sorted(expected - actual)
        unknown = sorted(actual - expected)
        if missing:
            self.error(location, f"missing keys {missing}")
        if unknown:
            self.error(location, f"unknown keys {unknown}")
        return not missing and not unknown

    def validate_codegen_cell_binding(
        self,
        row: dict[str, Any],
        location: str,
        cells: dict[str, dict[str, str]],
    ) -> dict[str, str] | None:
        """Join one observed codegen row to the exact owner-signed matrix cell."""
        cell_id = row.get("codegen_cell_id")
        if not isinstance(cell_id, str) or not cell_id:
            self.error(f"{location}.codegen_cell_id", "must be a non-empty string")
            return None
        cell = cells.get(cell_id)
        if cell is None:
            self.error(
                f"{location}.codegen_cell_id",
                "must name an owner-signed codegen matrix cell",
            )
            return None
        for field in CODEGEN_CELL_FIELDS:
            if row.get(field) != cell.get(field):
                self.error(
                    f"{location}.{field}",
                    "must exactly equal the owner-signed codegen cell value",
                )
        return cell

    def load_json(self, path: Path, location: str) -> dict[str, Any] | None:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as exc:
            self.error(location, f"cannot read JSON: {exc}")
            return None
        if not isinstance(value, dict):
            self.error(location, "must contain a JSON object")
            return None
        return value

    def resolve_ref(
        self,
        value: Any,
        location: str,
        *,
        forbidden: set[Path] | None = None,
    ) -> Path | None:
        if not self.exact_keys(value, {"path", "sha256"}, location):
            return None
        raw_path = value.get("path")
        digest = value.get("sha256")
        if not isinstance(raw_path, str) or not raw_path:
            self.error(f"{location}.path", "must be a non-empty relative path")
            return None
        if Path(raw_path).is_absolute():
            self.error(f"{location}.path", "absolute paths are forbidden")
            return None
        candidate = (self.root / raw_path).resolve()
        try:
            candidate.relative_to(self.root)
        except ValueError:
            self.error(f"{location}.path", "escapes --root")
            return None
        if forbidden and candidate in forbidden:
            self.error(f"{location}.path", "must bind underlying evidence, not receipt metadata")
        if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
            self.error(f"{location}.sha256", "must be a lowercase 64-hex digest")
            return candidate
        if not candidate.is_file():
            self.error(f"{location}.path", f"file does not exist: {raw_path}")
            return candidate
        actual = _sha256(candidate)
        if actual != digest:
            self.error(f"{location}.sha256", f"hash mismatch: recorded {digest}, actual {actual}")
        previous = self.bound_files.get(candidate)
        if previous is not None and previous != digest:
            self.error(location, "the same path is bound to conflicting digests")
        elif isinstance(digest, str) and HEX_DIGEST.fullmatch(digest):
            self.bound_files[candidate] = digest
        return candidate

    def resolve_named_ref(
        self,
        value: Any,
        location: str,
        *,
        expected_id: str | None = None,
        forbidden: set[Path] | None = None,
    ) -> tuple[str | None, Path | None, str | None]:
        """Resolve a content reference whose semantic identity is also explicit."""
        if not self.exact_keys(value, {"id", "path", "sha256"}, location):
            return None, None, None
        ref_id = value.get("id")
        if not isinstance(ref_id, str) or not CHECKER_ID.fullmatch(ref_id):
            self.error(f"{location}.id", "must be a non-empty typed identifier")
            ref_id = None
        elif expected_id is not None and ref_id != expected_id:
            self.error(f"{location}.id", f"must equal {expected_id!r}")
        path = self.resolve_ref(
            {"path": value.get("path"), "sha256": value.get("sha256")},
            location,
            forbidden=forbidden,
        )
        digest = value.get("sha256")
        if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
            digest = None
        return ref_id, path, digest

    def resolve_checker(
        self,
        gate: str,
        source_revision: Any,
        recorded_digest: Any,
        location: str,
    ) -> tuple[Path, str, bytes] | None:
        """Resolve the schema-owned checker and bind it to the accepted commit."""
        relative = CHECKER_PATHS[gate]
        candidate = (self.root / relative).resolve()
        try:
            candidate.relative_to(self.root)
        except ValueError:
            self.error(location, "schema-owned checker path escapes --root")
            return None
        if candidate.is_symlink():
            self.error(location, "checker must be a regular tracked file, not a symlink")
            return None
        if not candidate.is_file():
            self.error(location, f"schema-owned checker is not implemented: {relative}")
            return None
        actual_digest = _sha256(candidate)
        if not isinstance(recorded_digest, str) or not HEX_DIGEST.fullmatch(recorded_digest):
            self.error(location, "must be a lowercase 64-hex digest")
        elif recorded_digest != actual_digest:
            self.error(
                location,
                f"checker hash mismatch: recorded {recorded_digest}, actual {actual_digest}",
            )
        if not isinstance(source_revision, str) or not GIT_REVISION.fullmatch(source_revision):
            self.error(location, "cannot bind checker to an invalid source revision")
            return candidate, actual_digest, candidate.read_bytes()
        tracked = subprocess.run(
            ["git", "-C", str(self.root), "show", f"{source_revision}:{relative}"],
            check=False,
            capture_output=True,
        )
        if tracked.returncode != 0:
            self.error(location, f"checker is not tracked at source revision: {relative}")
            checker_bytes = candidate.read_bytes()
        else:
            checker_bytes = tracked.stdout
            tracked_digest = hashlib.sha256(tracked.stdout).hexdigest()
            if tracked_digest != actual_digest:
                self.error(
                    location,
                    "working checker bytes differ from the source-revision checker bytes",
                )
        previous = self.bound_files.get(candidate)
        if previous is not None and previous != actual_digest:
            self.error(location, "checker path is already bound to a conflicting digest")
        self.bound_files[candidate] = actual_digest
        return candidate, actual_digest, checker_bytes

    def run_checker(
        self,
        gate: str,
        checker_bytes: bytes,
        evidence_path: Path,
        toolchain_path: Path,
        corpus_path: Path,
        subject_graph_path: Path,
        linked_module_path: Path,
        release_artifact_path: Path,
        policy_path: Path,
        policy_authorization_path: Path,
        acceptance_run_id: Any,
        subject_graph_digest: Any,
        linked_module_digest: Any,
        release_artifact_digest: Any,
        policy_digest: Any,
        policy_authorization_digest: Any,
        source_revision: Any,
        checker_digest: str,
        evidence_digest: Any,
        toolchain_digest: Any,
        corpus_digest: Any,
        prior_gates_root: str | None,
    ) -> dict[str, Any] | None:
        """Re-run one schema-owned checker using the fixed verification protocol."""
        location = f"{gate}.checker_run"
        with tempfile.TemporaryDirectory(prefix=f"trust-{gate.lower()}-checker-") as tmp:
            checker_snapshot = Path(tmp) / "checker.py"
            checker_snapshot.write_bytes(checker_bytes)
            checker_snapshot.chmod(0o444)
            command = [
                sys.executable,
                "-I",
                str(checker_snapshot),
                "--verify-evidence",
                str(evidence_path),
                "--root",
                str(self.root),
                "--toolchain-manifest",
                str(toolchain_path),
                "--corpus-manifest",
                str(corpus_path),
                "--subject-graph",
                str(subject_graph_path),
                "--linked-module",
                str(linked_module_path),
                "--release-artifact",
                str(release_artifact_path),
                "--authority-policy",
                str(policy_path),
                "--policy-authorization",
                str(policy_authorization_path),
                "--acceptance-run-id",
                str(acceptance_run_id),
                "--source-revision",
                str(source_revision),
                "--checker-sha256",
                checker_digest,
                "--evidence-sha256",
                str(evidence_digest),
                "--toolchain-sha256",
                str(toolchain_digest),
                "--corpus-manifest-sha256",
                str(corpus_digest),
                "--subject-graph-sha256",
                str(subject_graph_digest),
                "--linked-module-sha256",
                str(linked_module_digest),
                "--release-artifact-sha256",
                str(release_artifact_digest),
                "--authority-policy-sha256",
                str(policy_digest),
                "--policy-authorization-sha256",
                str(policy_authorization_digest),
            ]
            # G1-G7 are the pre-seal facts.  They must not depend on the final
            # receipt (which includes the G8 seal), or the seal becomes a hash
            # fixed-point.  Only G8 inspects the final receipt after receiving
            # the already-computed G1-G7 root.
            if gate == "G8":
                command.extend(["--receipt", str(self.receipt_path)])
            if prior_gates_root is not None:
                command.extend(["--prior-gates-root", prior_gates_root])
            checker_env = {
                "HOME": tmp,
                "LANG": "C.UTF-8",
                "LC_ALL": "C.UTF-8",
                "PATH": "/usr/bin:/bin",
                "PYTHONHASHSEED": "0",
                "TZ": "UTC",
            }
            try:
                process = subprocess.run(
                    command,
                    cwd=self.root,
                    env=checker_env,
                    check=False,
                    capture_output=True,
                    text=True,
                    timeout=1800,
                )
            except (OSError, subprocess.TimeoutExpired) as exc:
                self.error(location, f"could not execute checker: {exc}")
                return None
        if process.returncode != 0:
            detail = process.stderr.strip() or process.stdout.strip() or "no diagnostic"
            self.error(location, f"checker exited {process.returncode}: {detail[:1000]}")
        try:
            verdict = json.loads(process.stdout)
        except json.JSONDecodeError as exc:
            self.error(location, f"checker stdout is not one JSON verdict: {exc}")
            return None
        if not isinstance(verdict, dict):
            self.error(location, "checker verdict must be a JSON object")
            return None
        return verdict

    def validate_manifest_header(
        self,
        value: dict[str, Any] | None,
        *,
        schema: str,
        location: str,
        acceptance_run_id: Any,
        source_revision: Any,
    ) -> bool:
        if value is None:
            return False
        expected = {
            "schema": schema,
            "goal_id": GOAL_ID,
            "acceptance_run_id": acceptance_run_id,
            "source_revision": source_revision,
        }
        ok = True
        for key, wanted in expected.items():
            if value.get(key) != wanted:
                self.error(f"{location}.{key}", f"must equal {wanted!r}")
                ok = False
        return ok

    def validate_contract_header(
        self,
        value: dict[str, Any] | None,
        *,
        schema: str,
        location: str,
    ) -> bool:
        if value is None:
            return False
        expected = {
            "schema": schema,
            "goal_id": GOAL_ID,
            "repository_id": REPOSITORY_ID,
        }
        ok = True
        for key, wanted in expected.items():
            if value.get(key) != wanted:
                self.error(f"{location}.{key}", f"must equal {wanted!r}")
                ok = False
        return ok

    def validate_admission_contract(
        self,
        value: dict[str, Any] | None,
    ) -> dict[str, dict[str, Any]]:
        location = "authority_contracts.admission"
        result: dict[str, dict[str, Any]] = {}
        if value is None:
            return result
        self.exact_keys(value, {"schema", "goal_id", "repository_id", "lanes"}, location)
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["admission"][1],
            location=location,
        )
        lanes = value.get("lanes")
        if not self.exact_keys(lanes, {"rust", "lean", "mixed"}, f"{location}.lanes"):
            return result
        for lane in ("rust", "lean", "mixed"):
            lane_value = lanes.get(lane)
            lane_location = f"{location}.lanes.{lane}"
            if not self.exact_keys(
                lane_value,
                {
                    "upstream_repository",
                    "upstream_revision",
                    "upstream_tree_sha256",
                    "feature_manifest",
                    "suite_manifest",
                    "exception_ledger",
                    "entries",
                },
                lane_location,
            ):
                continue
            repository = lane_value.get("upstream_repository")
            revision = lane_value.get("upstream_revision")
            tree_digest = lane_value.get("upstream_tree_sha256")
            if not isinstance(repository, str) or not repository:
                self.error(f"{lane_location}.upstream_repository", "must be non-empty")
            if not isinstance(revision, str) or not GIT_REVISION.fullmatch(revision):
                self.error(f"{lane_location}.upstream_revision", "must be a Git revision")
            if not isinstance(tree_digest, str) or not HEX_DIGEST.fullmatch(tree_digest):
                self.error(f"{lane_location}.upstream_tree_sha256", "must be 64-hex")

            support_docs: dict[str, dict[str, Any] | None] = {}
            for field in ("feature_manifest", "suite_manifest", "exception_ledger"):
                path = self.resolve_ref(lane_value.get(field), f"{lane_location}.{field}")
                support_docs[field] = (
                    self.load_json(path, f"{lane_location}.{field}")
                    if path is not None and path.is_file()
                    else None
                )

            entries = lane_value.get("entries")
            if not isinstance(entries, list) or not entries:
                self.error(f"{lane_location}.entries", "must be a non-empty list")
                continue
            entry_ids: set[str] = set()
            admitted_ids: set[str] = set()
            normalized_entries: list[dict[str, Any]] = []
            for index, entry in enumerate(entries):
                entry_location = f"{lane_location}.entries[{index}]"
                if not self.exact_keys(
                    entry,
                    {"id", "kind", "admitted", "source", "expected_outcome"},
                    entry_location,
                ):
                    continue
                entry_id = entry.get("id")
                if not isinstance(entry_id, str) or not entry_id or entry_id in entry_ids:
                    self.error(f"{entry_location}.id", "must be unique and non-empty")
                    continue
                entry_ids.add(entry_id)
                if type(entry.get("admitted")) is not bool:
                    self.error(f"{entry_location}.admitted", "must be a boolean")
                elif entry["admitted"]:
                    admitted_ids.add(entry_id)
                if not isinstance(entry.get("kind"), str) or not entry.get("kind"):
                    self.error(f"{entry_location}.kind", "must be non-empty")
                if not isinstance(entry.get("expected_outcome"), str) or not entry.get(
                    "expected_outcome"
                ):
                    self.error(f"{entry_location}.expected_outcome", "must be non-empty")
                self.resolve_ref(entry.get("source"), f"{entry_location}.source")
                normalized_entries.append(entry)
            if not admitted_ids:
                self.error(lane_location, "must owner-authorize at least one admitted entry")

            feature_manifest = support_docs["feature_manifest"]
            feature_location = f"{lane_location}.feature_manifest"
            if feature_manifest is not None:
                self.exact_keys(feature_manifest, {"schema", "lane", "features"}, feature_location)
                if feature_manifest.get("schema") != "trust.two-language.language-feature-manifest/v1":
                    self.error(f"{feature_location}.schema", "has the wrong schema")
                if feature_manifest.get("lane") != lane:
                    self.error(f"{feature_location}.lane", f"must equal {lane!r}")
                features = feature_manifest.get("features")
                if (
                    not isinstance(features, list)
                    or not features
                    or not all(isinstance(item, str) and item for item in features)
                    or len(features) != len(set(features))
                ):
                    self.error(f"{feature_location}.features", "must be non-empty and unique")

            suite_manifest = support_docs["suite_manifest"]
            suite_location = f"{lane_location}.suite_manifest"
            if suite_manifest is not None:
                self.exact_keys(suite_manifest, {"schema", "lane", "cases"}, suite_location)
                if suite_manifest.get("schema") != "trust.two-language.suite-manifest/v1":
                    self.error(f"{suite_location}.schema", "has the wrong schema")
                if suite_manifest.get("lane") != lane:
                    self.error(f"{suite_location}.lane", f"must equal {lane!r}")
                cases = suite_manifest.get("cases")
                if (
                    not isinstance(cases, list)
                    or not all(isinstance(case, str) for case in cases)
                    or sorted(cases) != sorted(entry_ids)
                ):
                    self.error(
                        f"{suite_location}.cases",
                        "must enumerate exactly the owner-authorized entry IDs",
                    )

            ledger = support_docs["exception_ledger"]
            ledger_location = f"{lane_location}.exception_ledger"
            if ledger is not None:
                self.exact_keys(ledger, {"schema", "lane", "rows"}, ledger_location)
                if ledger.get("schema") != "trust.two-language.exception-ledger/v1":
                    self.error(f"{ledger_location}.schema", "has the wrong schema")
                if ledger.get("lane") != lane:
                    self.error(f"{ledger_location}.lane", f"must equal {lane!r}")
                rows = ledger.get("rows")
                if not isinstance(rows, list):
                    self.error(f"{ledger_location}.rows", "must be a list")
                else:
                    ledger_ids: set[str] = set()
                    for index, row in enumerate(rows):
                        row_location = f"{ledger_location}.rows[{index}]"
                        if not self.exact_keys(
                            row,
                            {"entry_id", "classification", "reason"},
                            row_location,
                        ):
                            continue
                        entry_id = row.get("entry_id")
                        if (
                            not isinstance(entry_id, str)
                            or entry_id not in entry_ids
                            or entry_id in ledger_ids
                        ):
                            self.error(
                                f"{row_location}.entry_id",
                                "must uniquely name an owner-authorized entry",
                            )
                        else:
                            ledger_ids.add(entry_id)
                        if entry_id in admitted_ids:
                            self.error(
                                f"{row_location}.entry_id",
                                "an admitted program cannot be waived by the exception ledger",
                            )
                        if row.get("classification") != "non-applicable-harness":
                            self.error(
                                f"{row_location}.classification",
                                "only non-applicable-harness is authorized",
                            )
                        if not isinstance(row.get("reason"), str) or not row.get("reason"):
                            self.error(f"{row_location}.reason", "must be non-empty")
            result[lane] = {
                "upstream_revision": revision,
                "entries": normalized_entries,
            }
        return result

    def validate_semantics_contract(
        self,
        value: dict[str, Any] | None,
    ) -> dict[str, dict[str, str]]:
        location = "authority_contracts.semantics"
        result: dict[str, dict[str, str]] = {}
        if value is None:
            return result
        self.exact_keys(
            value,
            {"schema", "goal_id", "repository_id", "definitions"},
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["semantics"][1],
            location=location,
        )
        definitions = value.get("definitions")
        if not self.exact_keys(definitions, SEMANTICS_DEFINITIONS, f"{location}.definitions"):
            return result
        ids: set[str] = set()
        paths: set[Path] = set()
        for role in sorted(SEMANTICS_DEFINITIONS):
            ref_id, path, digest = self.resolve_named_ref(
                definitions.get(role),
                f"{location}.definitions.{role}",
            )
            if ref_id is not None and ref_id in ids:
                self.error(f"{location}.definitions.{role}.id", "semantic IDs must be distinct")
            elif ref_id is not None:
                ids.add(ref_id)
            if path is not None and path in paths:
                self.error(f"{location}.definitions.{role}.path", "semantic paths must be distinct")
            elif path is not None:
                paths.add(path)
            if ref_id is not None and digest is not None:
                result[role] = {"id": ref_id, "sha256": digest}
        return result

    def validate_obligation_contract(
        self,
        value: dict[str, Any] | None,
    ) -> dict[str, Any]:
        location = "authority_contracts.obligations"
        result: dict[str, Any] = {"rules": {}, "formula_encoder": {}}
        if value is None:
            return result
        self.exact_keys(
            value,
            {"schema", "goal_id", "repository_id", "rules", "formula_encoder"},
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["obligations"][1],
            location=location,
        )
        encoder_id, _encoder_path, encoder_digest = self.resolve_named_ref(
            value.get("formula_encoder"),
            f"{location}.formula_encoder",
        )
        if encoder_id is not None and encoder_digest is not None:
            result["formula_encoder"] = {"id": encoder_id, "sha256": encoder_digest}
        rules = value.get("rules")
        if not isinstance(rules, list) or not rules:
            self.error(f"{location}.rules", "must be a non-empty list")
            return result
        classes: set[str] = set()
        for index, rule in enumerate(rules):
            row_location = f"{location}.rules[{index}]"
            if not self.exact_keys(
                rule,
                {"id", "class", "applicability", "formula_schema"},
                row_location,
            ):
                continue
            rule_id = rule.get("id")
            rule_class = rule.get("class")
            if (
                not isinstance(rule_id, str)
                or not CHECKER_ID.fullmatch(rule_id)
                or rule_id in result["rules"]
            ):
                self.error(f"{row_location}.id", "must be a unique typed rule ID")
                continue
            if rule_class not in OBLIGATION_CLASSES:
                self.error(f"{row_location}.class", "is not a required obligation class")
            else:
                classes.add(rule_class)
            self.resolve_named_ref(rule.get("applicability"), f"{row_location}.applicability")
            self.resolve_named_ref(rule.get("formula_schema"), f"{row_location}.formula_schema")
            result["rules"][rule_id] = rule
        if classes != OBLIGATION_CLASSES:
            self.error(
                f"{location}.rules",
                f"must cover exactly the required obligation classes {sorted(OBLIGATION_CLASSES)}",
            )
        return result

    def validate_proof_authority_contract(
        self,
        value: dict[str, Any] | None,
    ) -> dict[str, Any]:
        location = "authority_contracts.proof_authority"
        result: dict[str, Any] = {"kernels": {}, "canonical_proposition_encoder": {}}
        if value is None:
            return result
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "repository_id",
                "canonical_proposition_encoder",
                "kernels",
                "axiom_policy",
                "external_olean_policy",
                "denied_axioms",
            },
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["proof_authority"][1],
            location=location,
        )
        encoder_id, _encoder_path, encoder_digest = self.resolve_named_ref(
            value.get("canonical_proposition_encoder"),
            f"{location}.canonical_proposition_encoder",
        )
        if encoder_id is not None and encoder_digest is not None:
            result["canonical_proposition_encoder"] = {
                "id": encoder_id,
                "sha256": encoder_digest,
            }
        self.resolve_named_ref(value.get("axiom_policy"), f"{location}.axiom_policy")
        self.resolve_named_ref(
            value.get("external_olean_policy"),
            f"{location}.external_olean_policy",
        )
        if value.get("denied_axioms") != ["sorryAx"]:
            self.error(f"{location}.denied_axioms", "must be exactly ['sorryAx']")
        kernels = value.get("kernels")
        if not isinstance(kernels, list) or not kernels:
            self.error(f"{location}.kernels", "must be a non-empty list")
            return result
        for index, kernel in enumerate(kernels):
            row_location = f"{location}.kernels[{index}]"
            if not self.exact_keys(
                kernel,
                {
                    "id",
                    "environment_sha256",
                    "artifact",
                    "proof_grades",
                    "axiom_allowlist_root_sha256",
                },
                row_location,
            ):
                continue
            kernel_id = kernel.get("id")
            if (
                not isinstance(kernel_id, str)
                or not CHECKER_ID.fullmatch(kernel_id)
                or kernel_id in result["kernels"]
            ):
                self.error(f"{row_location}.id", "must be a unique typed kernel ID")
                continue
            for field in ("environment_sha256", "axiom_allowlist_root_sha256"):
                digest = kernel.get(field)
                if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                    self.error(f"{row_location}.{field}", "must be 64-hex")
            self.resolve_named_ref(kernel.get("artifact"), f"{row_location}.artifact")
            grades = kernel.get("proof_grades")
            if (
                not isinstance(grades, list)
                or not grades
                or not all(isinstance(item, str) and item for item in grades)
                or len(grades) != len(set(grades))
            ):
                self.error(f"{row_location}.proof_grades", "must be non-empty and unique")
            result["kernels"][kernel_id] = kernel
        return result

    def validate_compatibility_contract(self, value: dict[str, Any] | None) -> None:
        location = "authority_contracts.compatibility_surfaces"
        if value is None:
            return
        self.exact_keys(
            value,
            {"schema", "goal_id", "repository_id", "surfaces"},
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["compatibility_surfaces"][1],
            location=location,
        )
        surfaces = value.get("surfaces")
        if not self.exact_keys(surfaces, set(COMPATIBILITY_CAPABILITIES), f"{location}.surfaces"):
            return
        for surface, required_capabilities in COMPATIBILITY_CAPABILITIES.items():
            row = surfaces.get(surface)
            row_location = f"{location}.surfaces.{surface}"
            if not self.exact_keys(
                row,
                {
                    "required",
                    "upstream_repository",
                    "upstream_version",
                    "feature_manifest",
                    "corpus_root_sha256",
                    "elaborator",
                    "ingestion_authority",
                    "computational_destinations",
                    "computational_image",
                    "proposition_destinations",
                    "proposition_image",
                    "semantic_capabilities",
                },
                row_location,
            ):
                continue
            if row.get("required") is not True:
                self.error(f"{row_location}.required", "must be the boolean true")
            for field in ("upstream_repository", "upstream_version"):
                if not isinstance(row.get(field), str) or not row.get(field):
                    self.error(f"{row_location}.{field}", "must be non-empty")
            corpus_root = row.get("corpus_root_sha256")
            if not isinstance(corpus_root, str) or not HEX_DIGEST.fullmatch(corpus_root):
                self.error(f"{row_location}.corpus_root_sha256", "must be 64-hex")
            if row.get("ingestion_authority") != "zero-authority":
                self.error(
                    f"{row_location}.ingestion_authority",
                    "must equal 'zero-authority'",
                )
            destinations = COMPATIBILITY_IMAGE_DESTINATIONS[surface]
            computational_destinations = row.get("computational_destinations")
            proposition_destinations = row.get("proposition_destinations")
            if computational_destinations != destinations["computational"]:
                self.error(
                    f"{row_location}.computational_destinations",
                    f"must equal {destinations['computational']!r}",
                )
            if proposition_destinations != destinations["proposition"]:
                self.error(
                    f"{row_location}.proposition_destinations",
                    f"must equal {destinations['proposition']!r}",
                )
            computational_ref: tuple[str | None, Path | None, str | None]
            if destinations["computational"]:
                computational_ref = self.resolve_named_ref(
                    row.get("computational_image"),
                    f"{row_location}.computational_image",
                )
            else:
                computational_ref = (None, None, None)
                if row.get("computational_image") is not None:
                    self.error(
                        f"{row_location}.computational_image",
                        "must be null because this surface has no computational image",
                    )
            proposition_ref = self.resolve_named_ref(
                row.get("proposition_image"),
                f"{row_location}.proposition_image",
            )
            if destinations["computational"]:
                for index, label in enumerate(("id", "path", "sha256")):
                    computational_value = computational_ref[index]
                    proposition_value = proposition_ref[index]
                    if (
                        computational_value is not None
                        and proposition_value is not None
                        and computational_value == proposition_value
                    ):
                        self.error(
                            f"{row_location}.computational_image.{label}",
                            "must not alias the distinct canonical proposition image",
                        )
            capabilities = row.get("semantic_capabilities")
            if (
                not isinstance(capabilities, list)
                or not all(isinstance(item, str) for item in capabilities)
                or set(capabilities) != required_capabilities
            ):
                self.error(
                    f"{row_location}.semantic_capabilities",
                    f"must equal {sorted(required_capabilities)}",
                )
            feature_path = self.resolve_ref(
                row.get("feature_manifest"),
                f"{row_location}.feature_manifest",
            )
            self.resolve_named_ref(row.get("elaborator"), f"{row_location}.elaborator")
            if feature_path is not None and feature_path.is_file():
                manifest = self.load_json(feature_path, f"{row_location}.feature_manifest")
                if manifest is not None:
                    self.exact_keys(
                        manifest,
                        {"schema", "surface", "features"},
                        f"{row_location}.feature_manifest",
                    )
                    if manifest.get("schema") != "trust.two-language.compatibility-feature-manifest/v1":
                        self.error(f"{row_location}.feature_manifest.schema", "has the wrong schema")
                    if manifest.get("surface") != surface:
                        self.error(f"{row_location}.feature_manifest.surface", "has the wrong surface")
                    features = manifest.get("features")
                    if not isinstance(features, list) or not features:
                        self.error(f"{row_location}.feature_manifest.features", "must be non-empty")

    def validate_codegen_contract(
        self,
        value: dict[str, Any] | None,
    ) -> dict[str, Any]:
        location = "authority_contracts.codegen_surface"
        result: dict[str, Any] = {
            "targets": {},
            "translation_relation": {},
            "cells": {},
            "matrix_root": None,
        }
        if value is None:
            return result
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "repository_id",
                "translation_relation",
                "targets",
                "matrix_cells",
            },
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["codegen_surface"][1],
            location=location,
        )
        relation_id, _relation_path, relation_digest = self.resolve_named_ref(
            value.get("translation_relation"),
            f"{location}.translation_relation",
        )
        if relation_id is not None and relation_digest is not None:
            result["translation_relation"] = {
                "id": relation_id,
                "sha256": relation_digest,
            }
        targets = value.get("targets")
        if not isinstance(targets, list) or not targets:
            self.error(f"{location}.targets", "must be a non-empty list")
            return result
        for index, target in enumerate(targets):
            row_location = f"{location}.targets[{index}]"
            if not self.exact_keys(
                target,
                {
                    "id",
                    "triple",
                    "abis",
                    "crate_types",
                    "runtimes",
                    "startups",
                    "linkers",
                    "unwind_modes",
                    "debug_modes",
                    "opt_levels",
                    "profiles",
                },
                row_location,
            ):
                continue
            target_id = target.get("id")
            if (
                not isinstance(target_id, str)
                or not CHECKER_ID.fullmatch(target_id)
                or target_id in result["targets"]
            ):
                self.error(f"{row_location}.id", "must be a unique typed target ID")
                continue
            target_valid = True
            if not isinstance(target.get("triple"), str) or not target.get("triple"):
                self.error(f"{row_location}.triple", "must be non-empty")
                target_valid = False
            for field in (
                "abis",
                "crate_types",
                "runtimes",
                "startups",
                "linkers",
                "unwind_modes",
                "debug_modes",
                "opt_levels",
                "profiles",
            ):
                items = target.get(field)
                if (
                    not isinstance(items, list)
                    or not items
                    or not all(isinstance(item, str) and item for item in items)
                    or len(items) != len(set(items))
                ):
                    self.error(f"{row_location}.{field}", "must be non-empty and unique")
                    target_valid = False
            if target_valid:
                result["targets"][target_id] = target

        matrix_cells = value.get("matrix_cells")
        if not isinstance(matrix_cells, list) or not matrix_cells:
            self.error(f"{location}.matrix_cells", "must be a non-empty list")
            return result
        seen_cell_ids: set[str] = set()
        seen_configurations: set[tuple[str, ...]] = set()
        projections: dict[str, dict[str, set[str]]] = {
            target_id: {
                axis: set() for axis in CODEGEN_TARGET_AXIS_BY_CELL_FIELD.values()
            }
            for target_id in result["targets"]
        }
        for index, cell in enumerate(matrix_cells):
            row_location = f"{location}.matrix_cells[{index}]"
            if not self.exact_keys(
                cell,
                {"id", *CODEGEN_CELL_FIELDS},
                row_location,
            ):
                continue
            cell_id = cell.get("id")
            if (
                not isinstance(cell_id, str)
                or not CHECKER_ID.fullmatch(cell_id)
                or cell_id in seen_cell_ids
            ):
                self.error(f"{row_location}.id", "must be a unique typed matrix-cell ID")
                continue
            seen_cell_ids.add(cell_id)
            cell_valid = True
            for field in CODEGEN_CELL_FIELDS:
                if not isinstance(cell.get(field), str) or not cell.get(field):
                    self.error(f"{row_location}.{field}", "must be a non-empty string")
                    cell_valid = False
            target_id = cell.get("target_id")
            target = (
                result["targets"].get(target_id)
                if isinstance(target_id, str)
                else None
            )
            if target is None:
                self.error(
                    f"{row_location}.target_id",
                    "must name an owner-authorized codegen target",
                )
                cell_valid = False
            else:
                for field, axis in CODEGEN_TARGET_AXIS_BY_CELL_FIELD.items():
                    if cell.get(field) not in target[axis]:
                        self.error(
                            f"{row_location}.{field}",
                            f"must select a value from target.{axis}",
                        )
                        cell_valid = False
            if not cell_valid:
                continue
            configuration = tuple(cell[field] for field in CODEGEN_CELL_FIELDS)
            if configuration in seen_configurations:
                self.error(
                    row_location,
                    "must not duplicate an authorized configuration under another cell ID",
                )
                continue
            seen_configurations.add(configuration)
            normalized_cell = {
                "id": cell_id,
                **{field: cell[field] for field in CODEGEN_CELL_FIELDS},
            }
            result["cells"][cell_id] = normalized_cell
            for field, axis in CODEGEN_TARGET_AXIS_BY_CELL_FIELD.items():
                projections[target_id][axis].add(cell[field])

        for target_id, target in result["targets"].items():
            for axis in CODEGEN_TARGET_AXIS_BY_CELL_FIELD.values():
                observed = projections[target_id][axis]
                expected = set(target[axis])
                if observed != expected:
                    self.error(
                        f"{location}.matrix_cells.{target_id}.{axis}",
                        "signed cells must cover every declared target-axis value exactly",
                    )
        if result["cells"]:
            result["matrix_root"] = _canonical_json_sha256(
                sorted(result["cells"].values(), key=lambda row: row["id"])
            )
        return result

    def validate_acceptance_environment_contract(
        self,
        value: dict[str, Any] | None,
    ) -> dict[str, Any]:
        location = "authority_contracts.acceptance_environment"
        result: dict[str, Any] = {"component_roster": []}
        if value is None:
            return result
        self.exact_keys(
            value,
            {"schema", "goal_id", "repository_id", "component_roster", "run_modes"},
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["acceptance_environment"][1],
            location=location,
        )
        roster = value.get("component_roster")
        if not isinstance(roster, list) or not roster:
            self.error(f"{location}.component_roster", "must be a non-empty list")
        else:
            roles: set[str] = set()
            names: set[str] = set()
            for index, component in enumerate(roster):
                row_location = f"{location}.component_roster[{index}]"
                if not self.exact_keys(
                    component,
                    {"role", "name", "version", "artifact_sha256"},
                    row_location,
                ):
                    continue
                role = component.get("role")
                name = component.get("name")
                if role not in TOOLCHAIN_ROLES or role in roles:
                    self.error(f"{row_location}.role", "must uniquely name a required role")
                else:
                    roles.add(role)
                if not isinstance(name, str) or not name or name in names:
                    self.error(f"{row_location}.name", "must be unique and non-empty")
                else:
                    names.add(name)
                if not isinstance(component.get("version"), str) or not component.get("version"):
                    self.error(f"{row_location}.version", "must be non-empty")
                digest = component.get("artifact_sha256")
                if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                    self.error(f"{row_location}.artifact_sha256", "must be 64-hex")
            if roles != TOOLCHAIN_ROLES:
                self.error(
                    f"{location}.component_roster",
                    f"must cover exactly the required roles {sorted(TOOLCHAIN_ROLES)}",
                )
            result["component_roster"] = roster
        run_modes = value.get("run_modes")
        if (
            not isinstance(run_modes, list)
            or not all(isinstance(item, str) for item in run_modes)
            or set(run_modes) != ACCEPTANCE_RUN_MODES
        ):
            self.error(
                f"{location}.run_modes",
                f"must equal {sorted(ACCEPTANCE_RUN_MODES)}",
            )
        return result

    def validate_authority_contracts(
        self,
        policy: dict[str, Any] | None,
    ) -> dict[str, Any]:
        result: dict[str, Any] = {}
        if policy is None:
            return result
        contracts = policy.get("contracts")
        location = "authority_policy.contracts"
        if not self.exact_keys(contracts, set(AUTHORITY_CONTRACTS), location):
            return result
        paths: set[Path] = set()
        digests: set[str] = set()
        loaded: dict[str, dict[str, Any] | None] = {}
        for role, (contract_id, _schema) in AUTHORITY_CONTRACTS.items():
            _ref_id, path, digest = self.resolve_named_ref(
                contracts.get(role),
                f"{location}.{role}",
                expected_id=contract_id,
            )
            if path is not None and path in paths:
                self.error(f"{location}.{role}.path", "contract paths must be distinct")
            elif path is not None:
                paths.add(path)
            if digest is not None and digest in digests:
                self.error(f"{location}.{role}.sha256", "contract digests must be distinct")
            elif digest is not None:
                digests.add(digest)
            loaded[role] = (
                self.load_json(path, f"authority_contracts.{role}")
                if path is not None and path.is_file()
                else None
            )
            result[f"{role}_sha256"] = digest
        result["admission"] = self.validate_admission_contract(loaded.get("admission"))
        result["semantics"] = self.validate_semantics_contract(loaded.get("semantics"))
        result["obligations"] = self.validate_obligation_contract(loaded.get("obligations"))
        result["proof_authority"] = self.validate_proof_authority_contract(
            loaded.get("proof_authority")
        )
        self.validate_compatibility_contract(loaded.get("compatibility_surfaces"))
        result["codegen_surface"] = self.validate_codegen_contract(
            loaded.get("codegen_surface")
        )
        result["acceptance_environment"] = self.validate_acceptance_environment_contract(
            loaded.get("acceptance_environment")
        )
        return result

    def validate_toolchain_manifest(
        self,
        value: dict[str, Any] | None,
        acceptance_run_id: Any,
        source_revision: Any,
        authority_contracts: dict[str, Any],
    ) -> None:
        location = "toolchain_manifest"
        if value is None:
            return
        self.exact_keys(
            value,
            {"schema", "goal_id", "acceptance_run_id", "source_revision", "components"},
            location,
        )
        self.validate_manifest_header(
            value,
            schema=TOOLCHAIN_SCHEMA,
            location=location,
            acceptance_run_id=acceptance_run_id,
            source_revision=source_revision,
        )
        components = value.get("components")
        if not isinstance(components, list) or not components:
            self.error(f"{location}.components", "must be a non-empty list")
            return
        names: set[str] = set()
        roles: set[str] = set()
        normalized: list[dict[str, Any]] = []
        for index, component in enumerate(components):
            row_location = f"{location}.components[{index}]"
            if not self.exact_keys(
                component,
                {"role", "name", "version", "artifact"},
                row_location,
            ):
                continue
            role = component.get("role")
            name = component.get("name")
            version = component.get("version")
            if role not in TOOLCHAIN_ROLES or role in roles:
                self.error(f"{row_location}.role", "must uniquely name a required role")
            else:
                roles.add(role)
            if not isinstance(name, str) or not name:
                self.error(f"{row_location}.name", "must be a non-empty string")
            elif name in names:
                self.error(f"{row_location}.name", f"duplicate component {name!r}")
            else:
                names.add(name)
            if not isinstance(version, str) or not version:
                self.error(f"{row_location}.version", "must be a non-empty string")
            self.resolve_ref(component.get("artifact"), f"{row_location}.artifact")
            artifact = component.get("artifact")
            normalized.append(
                {
                    "role": role,
                    "name": name,
                    "version": version,
                    "artifact_sha256": (
                        artifact.get("sha256") if isinstance(artifact, dict) else None
                    ),
                }
            )
        if roles != TOOLCHAIN_ROLES:
            self.error(
                f"{location}.components",
                f"must cover exactly the required roles {sorted(TOOLCHAIN_ROLES)}",
            )
        expected_roster = authority_contracts.get("acceptance_environment", {}).get(
            "component_roster",
            [],
        )
        if sorted(normalized, key=lambda row: str(row.get("role"))) != sorted(
            expected_roster,
            key=lambda row: str(row.get("role")) if isinstance(row, dict) else "",
        ):
            self.error(
                f"{location}.components",
                "must equal the owner-authorized component roster exactly",
            )

    def validate_corpus_manifest(
        self,
        value: dict[str, Any] | None,
        acceptance_run_id: Any,
        source_revision: Any,
        authority_contracts: dict[str, Any],
    ) -> set[str]:
        location = "corpus_manifest"
        admitted_ids: set[str] = set()
        if value is None:
            return admitted_ids
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "acceptance_run_id",
                "source_revision",
                "repository_id",
                "rust",
                "lean",
                "mixed",
            },
            location,
        )
        self.validate_manifest_header(
            value,
            schema=CORPUS_SCHEMA,
            location=location,
            acceptance_run_id=acceptance_run_id,
            source_revision=source_revision,
        )
        if value.get("repository_id") != REPOSITORY_ID:
            self.error(f"{location}.repository_id", f"must equal {REPOSITORY_ID!r}")
        ids: set[str] = set()
        authorized_lanes = authority_contracts.get("admission", {})
        admission_digest = authority_contracts.get("admission_sha256")
        for lane in ("rust", "lean", "mixed"):
            lane_value = value.get(lane)
            lane_location = f"{location}.{lane}"
            if not self.exact_keys(
                lane_value,
                {"upstream_revision", "admission_policy_sha256", "entries"},
                lane_location,
            ):
                continue
            upstream_revision = lane_value.get("upstream_revision")
            policy_digest = lane_value.get("admission_policy_sha256")
            if not isinstance(upstream_revision, str) or not upstream_revision:
                self.error(f"{lane_location}.upstream_revision", "must be a non-empty string")
            if not isinstance(policy_digest, str) or not HEX_DIGEST.fullmatch(policy_digest):
                self.error(
                    f"{lane_location}.admission_policy_sha256",
                    "must be a lowercase 64-hex digest",
                )
            elif policy_digest != admission_digest:
                self.error(
                    f"{lane_location}.admission_policy_sha256",
                    "must equal the owner-signed admission contract digest",
                )
            authorized_lane = authorized_lanes.get(lane, {})
            if upstream_revision != authorized_lane.get("upstream_revision"):
                self.error(
                    f"{lane_location}.upstream_revision",
                    "must equal the owner-authorized upstream revision",
                )
            entries = lane_value.get("entries")
            if not isinstance(entries, list) or not entries:
                self.error(f"{lane_location}.entries", "must be a non-empty list")
                continue
            lane_admitted = 0
            normalized_entries: list[dict[str, Any]] = []
            for index, entry in enumerate(entries):
                entry_location = f"{lane_location}.entries[{index}]"
                if not self.exact_keys(
                    entry,
                    {"id", "kind", "admitted", "source", "expected_outcome"},
                    entry_location,
                ):
                    continue
                entry_id = entry.get("id")
                kind = entry.get("kind")
                if not isinstance(entry_id, str) or not entry_id:
                    self.error(f"{entry_location}.id", "must be a non-empty string")
                elif entry_id in ids:
                    self.error(f"{entry_location}.id", f"duplicate corpus id {entry_id!r}")
                else:
                    ids.add(entry_id)
                    if entry.get("admitted") is True:
                        admitted_ids.add(entry_id)
                        lane_admitted += 1
                if not isinstance(kind, str) or not kind:
                    self.error(f"{entry_location}.kind", "must be a non-empty string")
                if type(entry.get("admitted")) is not bool:
                    self.error(f"{entry_location}.admitted", "must be a boolean")
                if not isinstance(entry.get("expected_outcome"), str) or not entry.get(
                    "expected_outcome"
                ):
                    self.error(f"{entry_location}.expected_outcome", "must be non-empty")
                self.resolve_ref(entry.get("source"), f"{entry_location}.source")
                normalized_entries.append(entry)
            if lane_admitted == 0:
                self.error(lane_location, "must contain at least one admitted program")
            if normalized_entries != authorized_lane.get("entries"):
                self.error(
                    f"{lane_location}.entries",
                    "must exactly equal the owner-signed admission population",
                )
        if not admitted_ids:
            self.error(location, "must contain at least one admitted program")
        return admitted_ids

    def validate_subject_graph(
        self,
        value: dict[str, Any] | None,
        acceptance_run_id: Any,
        source_revision: Any,
        admitted_corpus_ids: set[str],
        linked_module_digest: Any,
        release_artifact_digest: Any,
        authority_contracts: dict[str, Any],
    ) -> dict[str, set[str]]:
        location = "subject_graph"
        artifact_digests: dict[str, set[str]] = {
            "modules": set(),
            "objects": set(),
            "executables": set(),
            "translation_evidence": set(),
        }
        if value is None:
            return artifact_digests
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "acceptance_run_id",
                "source_revision",
                "programs",
                "roots",
                "release_executable",
            },
            location,
        )
        self.validate_manifest_header(
            value,
            schema=SUBJECT_GRAPH_SCHEMA,
            location=location,
            acceptance_run_id=acceptance_run_id,
            source_revision=source_revision,
        )
        programs = value.get("programs")
        roots = value.get("roots")
        root_names = {
            "admitted_files",
            "reachable_bodies",
            "refinement_certificates",
            "obligations",
            "proof_certificates",
            "modules",
            "codegen_matrix_cells",
            "objects",
            "translation_evidence",
            "call_edges",
            "executables",
        }
        if not self.exact_keys(roots, root_names, f"{location}.roots"):
            roots = {}
        else:
            for root_name, root_digest in roots.items():
                if not isinstance(root_digest, str) or not HEX_DIGEST.fullmatch(root_digest):
                    self.error(
                        f"{location}.roots.{root_name}",
                        "must be a lowercase 64-hex canonical root",
                    )
        if not isinstance(programs, list) or not programs:
            self.error(f"{location}.programs", "must be a non-empty list")
            return artifact_digests
        release_locator = value.get("release_executable")
        release_locator_valid = self.exact_keys(
            release_locator,
            {"program_id", "executable_id"},
            f"{location}.release_executable",
        )

        program_ids: set[str] = set()
        observed_admitted_files: set[str] = set()
        observed_languages: set[str] = set()
        observed_cross_language_directions: set[str] = set()
        observed_cross_language_value_categories: set[str] = set()
        observed_cross_language_matrix: set[tuple[str, str]] = set()
        observed_obligation_classes: set[str] = set()
        executable_records: dict[tuple[str, str], dict[str, Any]] = {}
        object_records_by_program: dict[str, dict[str, dict[str, Any]]] = {}
        root_rows: dict[str, list[dict[str, Any]]] = {name: [] for name in root_names}
        for program_index, program in enumerate(programs):
            program_location = f"{location}.programs[{program_index}]"
            program_keys = {
                "id",
                "entrypoints",
                "admitted_file_ids",
                "bodies",
                "refinement_certificates",
                "obligations",
                "proof_certificates",
                "modules",
                "objects",
                "translation_evidence",
                "executables",
                "call_edges",
                "contextual_refinement",
            }
            if not self.exact_keys(program, program_keys, program_location):
                continue
            program_id = program.get("id")
            if not isinstance(program_id, str) or not program_id:
                self.error(f"{program_location}.id", "must be a non-empty string")
                program_id = f"<invalid-{program_index}>"
            elif program_id in program_ids:
                self.error(f"{program_location}.id", f"duplicate program id {program_id!r}")
            else:
                program_ids.add(program_id)

            codegen = authority_contracts.get("codegen_surface", {})
            signed_cells = codegen.get("cells", {}) if isinstance(codegen, dict) else {}
            if not isinstance(signed_cells, dict) or not signed_cells:
                self.error(
                    f"{program_location}.objects",
                    "cannot realize an empty or invalid owner-signed codegen matrix",
                )
                signed_cells = {}
            for cell in sorted(signed_cells.values(), key=lambda row: row["id"]):
                root_rows["codegen_matrix_cells"].append(
                    {"program_id": program_id, **cell}
                )

            admitted_file_ids = program.get("admitted_file_ids")
            if (
                not isinstance(admitted_file_ids, list)
                or not admitted_file_ids
                or not all(isinstance(item, str) and item for item in admitted_file_ids)
                or len(admitted_file_ids) != len(set(admitted_file_ids))
            ):
                self.error(
                    f"{program_location}.admitted_file_ids",
                    "must be a non-empty duplicate-free string list",
                )
                admitted_file_ids = []
            for file_id in admitted_file_ids:
                if file_id not in admitted_corpus_ids:
                    self.error(
                        f"{program_location}.admitted_file_ids",
                        f"unknown or non-admitted corpus id {file_id!r}",
                    )
                observed_admitted_files.add(file_id)
                root_rows["admitted_files"].append(
                    {"program_id": program_id, "file_id": file_id}
                )

            def typed_rows(
                field: str,
                expected_keys: set[str],
                *,
                allow_empty: bool = False,
            ) -> list[dict[str, Any]]:
                rows = program.get(field)
                if not isinstance(rows, list) or (not rows and not allow_empty):
                    qualifier = "a list" if allow_empty else "a non-empty list"
                    self.error(f"{program_location}.{field}", f"must be {qualifier}")
                    return []
                result: list[dict[str, Any]] = []
                for row_index, row in enumerate(rows):
                    row_location = f"{program_location}.{field}[{row_index}]"
                    if self.exact_keys(row, expected_keys, row_location):
                        result.append(row)
                        root_name = "reachable_bodies" if field == "bodies" else field
                        root_rows[root_name].append({"program_id": program_id, **row})
                return result

            bodies = typed_rows(
                "bodies",
                {
                    "id",
                    "language",
                    "function_identity_sha256",
                    "source_language_semantics_id",
                    "source_language_semantics_sha256",
                    "source_semantics_sha256",
                    "trust_ir_semantics_id",
                    "trust_ir_semantics_sha256",
                    "trust_ir_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                },
            )
            body_ids: set[str] = set()
            semantics = authority_contracts.get("semantics", {})
            for row_index, body in enumerate(bodies):
                row_location = f"{program_location}.bodies[{row_index}]"
                body_id = body.get("id")
                if not isinstance(body_id, str) or not body_id or body_id in body_ids:
                    self.error(f"{row_location}.id", "must be a unique non-empty body id")
                else:
                    body_ids.add(body_id)
                if body.get("language") not in {"rust", "lean"}:
                    self.error(f"{row_location}.language", "must be 'rust' or 'lean'")
                else:
                    observed_languages.add(body["language"])
                    source_role = f"{body['language']}_language"
                    expected_source = semantics.get(source_role, {})
                    if body.get("source_language_semantics_id") != expected_source.get("id"):
                        self.error(
                            f"{row_location}.source_language_semantics_id",
                            "must name the owner-authorized source semantics",
                        )
                    if body.get("source_language_semantics_sha256") != expected_source.get(
                        "sha256"
                    ):
                        self.error(
                            f"{row_location}.source_language_semantics_sha256",
                            "must bind the owner-authorized source semantics",
                        )
                expected_ir = semantics.get("trust_ir", {})
                if body.get("trust_ir_semantics_id") != expected_ir.get("id"):
                    self.error(
                        f"{row_location}.trust_ir_semantics_id",
                        "must name the owner-authorized Trust-IR semantics",
                    )
                if body.get("trust_ir_semantics_sha256") != expected_ir.get("sha256"):
                    self.error(
                        f"{row_location}.trust_ir_semantics_sha256",
                        "must bind the owner-authorized Trust-IR semantics",
                    )
                for digest_field in (
                    "function_identity_sha256",
                    "source_language_semantics_sha256",
                    "source_semantics_sha256",
                    "trust_ir_semantics_sha256",
                    "trust_ir_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                ):
                    digest = body.get(digest_field)
                    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                        self.error(f"{row_location}.{digest_field}", "must be 64-hex")

            entrypoints = program.get("entrypoints")
            if (
                not isinstance(entrypoints, list)
                or not entrypoints
                or not all(isinstance(item, str) and item in body_ids for item in entrypoints)
                or len(entrypoints) != len(set(entrypoints))
            ):
                self.error(
                    f"{program_location}.entrypoints",
                    "must be a non-empty duplicate-free subset of body ids",
                )

            call_edges = typed_rows(
                "call_edges",
                {
                    "id",
                    "caller_body_id",
                    "callee_body_id",
                    "direction",
                    "value_category",
                    "canonical_type_sha256",
                    "abi_id",
                    "abi_sha256",
                    "memory_model_id",
                    "memory_model_sha256",
                    "import_assumption_closure_sha256",
                    "visibility",
                },
            )
            call_edge_ids: set[str] = set()
            body_by_id = {
                body["id"]: body
                for body in bodies
                if isinstance(body.get("id"), str) and body.get("id")
            }
            abi = semantics.get("abi_memory_model", {})
            for row_index, edge in enumerate(call_edges):
                row_location = f"{program_location}.call_edges[{row_index}]"
                edge_id = edge.get("id")
                if not isinstance(edge_id, str) or not edge_id or edge_id in call_edge_ids:
                    self.error(f"{row_location}.id", "must be a unique non-empty edge ID")
                else:
                    call_edge_ids.add(edge_id)
                caller_id = edge.get("caller_body_id")
                callee_id = edge.get("callee_body_id")
                caller = body_by_id.get(caller_id) if isinstance(caller_id, str) else None
                callee = body_by_id.get(callee_id) if isinstance(callee_id, str) else None
                if caller is None:
                    self.error(f"{row_location}.caller_body_id", "must name a reachable body")
                if callee is None:
                    self.error(f"{row_location}.callee_body_id", "must name a reachable body")
                if caller is not None and callee is not None:
                    expected_direction = f"{caller.get('language')}_to_{callee.get('language')}"
                    if edge.get("direction") != expected_direction:
                        self.error(
                            f"{row_location}.direction",
                            f"must equal {expected_direction!r}",
                        )
                    if caller.get("language") != callee.get("language"):
                        observed_cross_language_directions.add(expected_direction)
                        if isinstance(edge.get("value_category"), str):
                            observed_cross_language_value_categories.add(
                                edge["value_category"]
                            )
                            observed_cross_language_matrix.add(
                                (expected_direction, edge["value_category"])
                            )
                if edge.get("value_category") not in {
                    "value",
                    "aggregate",
                    "reference",
                    "error",
                    "callback",
                    "result",
                }:
                    self.error(f"{row_location}.value_category", "is not a supported category")
                for digest_field in (
                    "canonical_type_sha256",
                    "abi_sha256",
                    "memory_model_sha256",
                    "import_assumption_closure_sha256",
                ):
                    digest = edge.get(digest_field)
                    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                        self.error(f"{row_location}.{digest_field}", "must be 64-hex")
                for id_field in ("abi_id", "memory_model_id"):
                    if edge.get(id_field) != abi.get("id"):
                        self.error(
                            f"{row_location}.{id_field}",
                            "must name the owner-authorized ABI/memory model",
                        )
                for digest_field in ("abi_sha256", "memory_model_sha256"):
                    if edge.get(digest_field) != abi.get("sha256"):
                        self.error(
                            f"{row_location}.{digest_field}",
                            "must bind the owner-authorized ABI/memory model",
                        )
                if edge.get("visibility") != "call":
                    self.error(
                        f"{row_location}.visibility",
                        "cross-language computational edges must not cross the proof firewall",
                    )

            contextual_refinement = program.get("contextual_refinement")
            contextual_location = f"{program_location}.contextual_refinement"
            if self.exact_keys(
                contextual_refinement,
                {"assumption_closure_sha256", "evidence"},
                contextual_location,
            ):
                closure = contextual_refinement.get("assumption_closure_sha256")
                if not isinstance(closure, str) or not HEX_DIGEST.fullmatch(closure):
                    self.error(f"{contextual_location}.assumption_closure_sha256", "must be 64-hex")
                self.resolve_ref(contextual_refinement.get("evidence"), f"{contextual_location}.evidence")

            refinements = typed_rows(
                "refinement_certificates",
                {
                    "body_id",
                    "source_semantics_sha256",
                    "trust_ir_sha256",
                    "relation_id",
                    "relation_sha256",
                    "certificate_kind",
                    "finite_domain_sha256",
                    "exhaustiveness_evidence",
                    "all_elements_agreement_root_sha256",
                    "kernel_environment_id",
                    "kernel_environment_sha256",
                    "evidence",
                },
            )
            refinement_body_ids: list[str] = []
            body_by_id = {
                body["id"]: body
                for body in bodies
                if isinstance(body.get("id"), str) and body.get("id")
            }
            for row_index, refinement in enumerate(refinements):
                row_location = f"{program_location}.refinement_certificates[{row_index}]"
                body_id = refinement.get("body_id")
                if isinstance(body_id, str):
                    refinement_body_ids.append(body_id)
                    body = body_by_id.get(body_id)
                else:
                    body = None
                if body is None:
                    self.error(f"{row_location}.body_id", "must name a reachable body")
                else:
                    for field in ("source_semantics_sha256", "trust_ir_sha256"):
                        if refinement.get(field) != body.get(field):
                            self.error(
                                f"{row_location}.{field}",
                                "must equal the body's exact semantic digest",
                            )
                    relation_role = f"{body.get('language')}_to_trust_ir_refinement"
                    relation = semantics.get(relation_role, {})
                    if refinement.get("relation_id") != relation.get("id"):
                        self.error(
                            f"{row_location}.relation_id",
                            "must name the owner-authorized refinement relation",
                        )
                    if refinement.get("relation_sha256") != relation.get("sha256"):
                        self.error(
                            f"{row_location}.relation_sha256",
                            "must bind the owner-authorized refinement relation",
                        )
                proof_kernels = authority_contracts.get("proof_authority", {}).get(
                    "kernels",
                    {},
                )
                kernel_id = refinement.get("kernel_environment_id")
                kernel = proof_kernels.get(kernel_id, {}) if isinstance(kernel_id, str) else {}
                if not kernel:
                    self.error(
                        f"{row_location}.kernel_environment_id",
                        "must name an owner-authorized kernel environment",
                    )
                kernel_digest = refinement.get("kernel_environment_sha256")
                if not isinstance(kernel_digest, str) or not HEX_DIGEST.fullmatch(kernel_digest):
                    self.error(
                        f"{row_location}.kernel_environment_sha256",
                        "must be 64-hex",
                    )
                elif kernel_digest != kernel.get("environment_sha256"):
                    self.error(
                        f"{row_location}.kernel_environment_sha256",
                        "must equal the owner-authorized kernel environment",
                    )
                relation_digest = refinement.get("relation_sha256")
                if not isinstance(relation_digest, str) or not HEX_DIGEST.fullmatch(
                    relation_digest
                ):
                    self.error(f"{row_location}.relation_sha256", "must be 64-hex")
                certificate_kind = refinement.get("certificate_kind")
                finite_fields = (
                    refinement.get("finite_domain_sha256"),
                    refinement.get("exhaustiveness_evidence"),
                    refinement.get("all_elements_agreement_root_sha256"),
                )
                if certificate_kind == "universal":
                    if finite_fields != (None, None, None):
                        self.error(
                            row_location,
                            "universal certificates must not carry finite-domain substitutes",
                        )
                elif certificate_kind == "finite-exhaustive":
                    for field in (
                        "finite_domain_sha256",
                        "all_elements_agreement_root_sha256",
                    ):
                        digest = refinement.get(field)
                        if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                            self.error(f"{row_location}.{field}", "must be 64-hex")
                    self.resolve_ref(
                        refinement.get("exhaustiveness_evidence"),
                        f"{row_location}.exhaustiveness_evidence",
                    )
                else:
                    self.error(
                        f"{row_location}.certificate_kind",
                        "must be 'universal' or 'finite-exhaustive'",
                    )
                self.resolve_ref(refinement.get("evidence"), f"{row_location}.evidence")
            if sorted(refinement_body_ids) != sorted(body_ids):
                self.error(
                    f"{program_location}.refinement_certificates",
                    "must contain exactly one universal refinement certificate per body",
                )

            obligations = typed_rows(
                "obligations",
                {
                    "id",
                    "body_id",
                    "function_identity_sha256",
                    "formula_sha256",
                    "canonical_proposition_sha256",
                    "formula_encoder_id",
                    "formula_encoder_sha256",
                    "proposition_encoder_id",
                    "proposition_encoder_sha256",
                    "formula_to_proposition_evidence",
                    "policy_rule_id",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                    "module_id",
                },
            )
            obligation_ids: set[str] = set()
            obligation_by_id: dict[str, dict[str, Any]] = {}
            for row_index, obligation in enumerate(obligations):
                row_location = f"{program_location}.obligations[{row_index}]"
                obligation_id = obligation.get("id")
                if (
                    not isinstance(obligation_id, str)
                    or not obligation_id
                    or obligation_id in obligation_ids
                ):
                    self.error(f"{row_location}.id", "must be a unique non-empty obligation id")
                else:
                    obligation_ids.add(obligation_id)
                    obligation_by_id[obligation_id] = obligation
                obligation_body_id = obligation.get("body_id")
                if not isinstance(obligation_body_id, str) or obligation_body_id not in body_ids:
                    self.error(f"{row_location}.body_id", "must name a reachable body")
                body = body_by_id.get(obligation_body_id, {}) if isinstance(
                    obligation_body_id,
                    str,
                ) else {}
                for field in (
                    "function_identity_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                ):
                    if obligation.get(field) != body.get(field):
                        self.error(
                            f"{row_location}.{field}",
                            "must equal the reachable body's exact identity/state/effect digest",
                        )
                for field in (
                    "function_identity_sha256",
                    "formula_sha256",
                    "canonical_proposition_sha256",
                    "formula_encoder_sha256",
                    "proposition_encoder_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                ):
                    digest = obligation.get(field)
                    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                        self.error(f"{row_location}.{field}", "must be 64-hex")
                formula_encoder = authority_contracts.get("obligations", {}).get(
                    "formula_encoder",
                    {},
                )
                if obligation.get("formula_encoder_id") != formula_encoder.get("id"):
                    self.error(
                        f"{row_location}.formula_encoder_id",
                        "must name the owner-authorized formula encoder",
                    )
                if obligation.get("formula_encoder_sha256") != formula_encoder.get("sha256"):
                    self.error(
                        f"{row_location}.formula_encoder_sha256",
                        "must bind the owner-authorized formula encoder",
                    )
                proposition_encoder = authority_contracts.get("proof_authority", {}).get(
                    "canonical_proposition_encoder",
                    {},
                )
                if obligation.get("proposition_encoder_id") != proposition_encoder.get("id"):
                    self.error(
                        f"{row_location}.proposition_encoder_id",
                        "must name the owner-authorized canonical proposition encoder",
                    )
                if obligation.get("proposition_encoder_sha256") != proposition_encoder.get(
                    "sha256"
                ):
                    self.error(
                        f"{row_location}.proposition_encoder_sha256",
                        "must bind the owner-authorized canonical proposition encoder",
                    )
                self.resolve_ref(
                    obligation.get("formula_to_proposition_evidence"),
                    f"{row_location}.formula_to_proposition_evidence",
                )
                if not isinstance(obligation.get("policy_rule_id"), str) or not obligation.get(
                    "policy_rule_id"
                ):
                    self.error(f"{row_location}.policy_rule_id", "must be non-empty")
                else:
                    rule = authority_contracts.get("obligations", {}).get(
                        "rules",
                        {},
                    ).get(obligation.get("policy_rule_id"))
                    if not isinstance(rule, dict):
                        self.error(
                            f"{row_location}.policy_rule_id",
                            "must name an owner-authorized obligation rule",
                        )
                    elif isinstance(rule.get("class"), str):
                        observed_obligation_classes.add(rule["class"])

            proof_certificates = typed_rows(
                "proof_certificates",
                {
                    "id",
                    "obligation_id",
                    "body_id",
                    "function_identity_sha256",
                    "proposition_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                    "module_id",
                    "kernel_environment_id",
                    "kernel_environment_sha256",
                    "proof_grade",
                    "axiom_allowlist_root_sha256",
                    "evidence",
                },
            )
            proof_ids: set[str] = set()
            certified_obligation_ids: list[str] = []
            for row_index, certificate in enumerate(proof_certificates):
                row_location = f"{program_location}.proof_certificates[{row_index}]"
                certificate_id = certificate.get("id")
                if (
                    not isinstance(certificate_id, str)
                    or not certificate_id
                    or certificate_id in proof_ids
                ):
                    self.error(f"{row_location}.id", "must be a unique non-empty certificate id")
                else:
                    proof_ids.add(certificate_id)
                obligation_id = certificate.get("obligation_id")
                if isinstance(obligation_id, str):
                    certified_obligation_ids.append(obligation_id)
                    obligation = obligation_by_id.get(obligation_id)
                else:
                    obligation = None
                if obligation is None:
                    self.error(f"{row_location}.obligation_id", "must name an obligation")
                else:
                    for field in (
                        "body_id",
                        "function_identity_sha256",
                        "ssa_epoch_sha256",
                        "effect_summary_sha256",
                        "module_id",
                    ):
                        if certificate.get(field) != obligation.get(field):
                            self.error(
                                f"{row_location}.{field}",
                                "must equal the exact obligation identity/state/module binding",
                            )
                if obligation is not None and certificate.get(
                    "proposition_sha256"
                ) != obligation.get("canonical_proposition_sha256"):
                    self.error(
                        f"{row_location}.proposition_sha256",
                        "must equal the exact canonical Lean proposition digest",
                    )
                kernel_id = certificate.get("kernel_environment_id")
                kernel = (
                    authority_contracts.get("proof_authority", {})
                    .get("kernels", {})
                    .get(kernel_id, {})
                    if isinstance(kernel_id, str)
                    else {}
                )
                if not kernel:
                    self.error(
                        f"{row_location}.kernel_environment_id",
                        "must name an owner-authorized kernel environment",
                    )
                if certificate.get("kernel_environment_sha256") != kernel.get(
                    "environment_sha256"
                ):
                    self.error(
                        f"{row_location}.kernel_environment_sha256",
                        "must equal the owner-authorized kernel environment",
                    )
                if certificate.get("proof_grade") not in kernel.get("proof_grades", []):
                    self.error(
                        f"{row_location}.proof_grade",
                        "must be an owner-authorized proof grade",
                    )
                if certificate.get("axiom_allowlist_root_sha256") != kernel.get(
                    "axiom_allowlist_root_sha256"
                ):
                    self.error(
                        f"{row_location}.axiom_allowlist_root_sha256",
                        "must bind the owner-authorized axiom allowlist",
                    )
                for digest_field in (
                    "function_identity_sha256",
                    "proposition_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                    "kernel_environment_sha256",
                    "axiom_allowlist_root_sha256",
                ):
                    digest = certificate.get(digest_field)
                    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                        self.error(f"{row_location}.{digest_field}", "must be 64-hex")
                self.resolve_ref(certificate.get("evidence"), f"{row_location}.evidence")
            if sorted(certified_obligation_ids) != sorted(obligation_ids):
                self.error(
                    f"{program_location}.proof_certificates",
                    "must contain exactly one proof certificate per required obligation",
                )

            modules = typed_rows(
                "modules",
                {
                    "id",
                    "artifact",
                    "body_ids",
                    "call_edge_ids",
                    "obligation_ids",
                    "refinement_certificate_body_ids",
                    "proof_certificate_ids",
                    "assumption_closure_sha256",
                    "contextual_refinement_evidence",
                },
            )
            module_ids: set[str] = set()
            module_artifacts: dict[str, str] = {}
            module_body_ids: list[str] = []
            module_call_edge_ids: list[str] = []
            module_obligation_ids: list[str] = []
            module_refinement_ids: list[str] = []
            module_proof_ids: list[str] = []
            for row_index, module in enumerate(modules):
                row_location = f"{program_location}.modules[{row_index}]"
                module_id = module.get("id")
                if not isinstance(module_id, str) or not module_id or module_id in module_ids:
                    self.error(f"{row_location}.id", "must be a unique non-empty module id")
                else:
                    module_ids.add(module_id)
                module_path = self.resolve_ref(module.get("artifact"), f"{row_location}.artifact")
                artifact = module.get("artifact")
                if module_path is not None and isinstance(artifact, dict):
                    digest = artifact.get("sha256")
                    if isinstance(digest, str):
                        artifact_digests["modules"].add(digest)
                        if isinstance(module_id, str):
                            module_artifacts[module_id] = digest
                closure = module.get("assumption_closure_sha256")
                if not isinstance(closure, str) or not HEX_DIGEST.fullmatch(closure):
                    self.error(f"{row_location}.assumption_closure_sha256", "must be 64-hex")
                elif isinstance(contextual_refinement, dict) and closure != contextual_refinement.get(
                    "assumption_closure_sha256"
                ):
                    self.error(
                        f"{row_location}.assumption_closure_sha256",
                        "must equal the whole-program contextual refinement closure",
                    )
                self.resolve_ref(
                    module.get("contextual_refinement_evidence"),
                    f"{row_location}.contextual_refinement_evidence",
                )
                for field, sink in (
                    ("body_ids", module_body_ids),
                    ("call_edge_ids", module_call_edge_ids),
                    ("obligation_ids", module_obligation_ids),
                    ("refinement_certificate_body_ids", module_refinement_ids),
                    ("proof_certificate_ids", module_proof_ids),
                ):
                    ids = module.get(field)
                    if not isinstance(ids, list) or not all(
                        isinstance(item, str) and item for item in ids
                    ):
                        self.error(f"{row_location}.{field}", "must be a string list")
                    else:
                        sink.extend(ids)
            expected_module_sets = (
                ("body_ids", module_body_ids, body_ids),
                ("call_edge_ids", module_call_edge_ids, call_edge_ids),
                ("obligation_ids", module_obligation_ids, obligation_ids),
                (
                    "refinement_certificate_body_ids",
                    module_refinement_ids,
                    body_ids,
                ),
                ("proof_certificate_ids", module_proof_ids, proof_ids),
            )
            for field, observed, expected_ids in expected_module_sets:
                if sorted(observed) != sorted(expected_ids):
                    self.error(
                        f"{program_location}.modules.{field}",
                        "module inventory must be an exact duplicate-free partition",
                    )

            for row_index, obligation in enumerate(obligations):
                if obligation.get("module_id") not in module_ids:
                    self.error(
                        f"{program_location}.obligations[{row_index}].module_id",
                        "must name the owning admitted module",
                    )
            for row_index, certificate in enumerate(proof_certificates):
                if certificate.get("module_id") not in module_ids:
                    self.error(
                        f"{program_location}.proof_certificates[{row_index}].module_id",
                        "must name the owning admitted module",
                    )

            objects = typed_rows(
                "objects",
                {
                    "id",
                    "module_id",
                    "codegen_cell_id",
                    *CODEGEN_CELL_FIELDS,
                    "artifact",
                },
            )
            object_ids: set[str] = set()
            object_pairs: list[tuple[str, str]] = []
            object_records: dict[str, dict[str, Any]] = {}
            for row_index, obj in enumerate(objects):
                row_location = f"{program_location}.objects[{row_index}]"
                object_id = obj.get("id")
                object_id_valid = True
                if not isinstance(object_id, str) or not object_id or object_id in object_ids:
                    self.error(f"{row_location}.id", "must be a unique non-empty object id")
                    object_id_valid = False
                else:
                    object_ids.add(object_id)
                module_id = obj.get("module_id")
                if not isinstance(module_id, str) or module_id not in module_ids:
                    self.error(f"{row_location}.module_id", "must name an admitted module")
                cell = self.validate_codegen_cell_binding(obj, row_location, signed_cells)
                cell_id = obj.get("codegen_cell_id")
                if isinstance(module_id, str) and module_id in module_ids and cell is not None:
                    object_pairs.append((module_id, cell["id"]))
                artifact_path = self.resolve_ref(obj.get("artifact"), f"{row_location}.artifact")
                artifact = obj.get("artifact")
                artifact_digest = (
                    artifact.get("sha256") if isinstance(artifact, dict) else None
                )
                if artifact_path is not None and isinstance(artifact_digest, str):
                    artifact_digests["objects"].add(artifact_digest)
                if object_id_valid and isinstance(object_id, str):
                    object_records[object_id] = {
                        "module_id": module_id,
                        "codegen_cell_id": cell_id,
                        "artifact_sha256": artifact_digest,
                        "module_sha256": (
                            module_artifacts.get(module_id)
                            if isinstance(module_id, str)
                            else None
                        ),
                        "configuration": {
                            field: obj.get(field) for field in CODEGEN_CELL_FIELDS
                        },
                    }
            expected_object_pairs = {
                (module_id, cell_id)
                for module_id in module_ids
                for cell_id in signed_cells
            }
            if (
                len(object_pairs) != len(set(object_pairs))
                or set(object_pairs) != expected_object_pairs
            ):
                self.error(
                    f"{program_location}.objects",
                    "must contain exactly one object for every admitted module/codegen-cell pair",
                )
            object_records_by_program[program_id] = object_records

            translation_evidence = typed_rows(
                "translation_evidence",
                {
                    "id",
                    "object_id",
                    "module_id",
                    "codegen_cell_id",
                    *CODEGEN_CELL_FIELDS,
                    "translation_relation_id",
                    "translation_relation_sha256",
                    "module_sha256",
                    "object_sha256",
                    "evidence",
                },
            )
            evidence_ids: set[str] = set()
            evidence_object_ids: list[str] = []
            relation = codegen.get("translation_relation", {}) if isinstance(codegen, dict) else {}
            for row_index, evidence in enumerate(translation_evidence):
                row_location = f"{program_location}.translation_evidence[{row_index}]"
                evidence_id = evidence.get("id")
                if (
                    not isinstance(evidence_id, str)
                    or not evidence_id
                    or evidence_id in evidence_ids
                ):
                    self.error(f"{row_location}.id", "must be a unique non-empty evidence id")
                else:
                    evidence_ids.add(evidence_id)
                object_id = evidence.get("object_id")
                if isinstance(object_id, str) and object_id:
                    evidence_object_ids.append(object_id)
                else:
                    self.error(f"{row_location}.object_id", "must be a non-empty string")
                cell = self.validate_codegen_cell_binding(evidence, row_location, signed_cells)
                joined_object = object_records.get(object_id) if isinstance(object_id, str) else None
                if joined_object is None:
                    self.error(f"{row_location}.object_id", "must name an emitted object")
                else:
                    if evidence.get("module_id") != joined_object.get("module_id"):
                        self.error(
                            f"{row_location}.module_id",
                            "must equal the joined object's module",
                        )
                    if evidence.get("codegen_cell_id") != joined_object.get("codegen_cell_id"):
                        self.error(
                            f"{row_location}.codegen_cell_id",
                            "must equal the joined object's codegen cell",
                        )
                    for field in CODEGEN_CELL_FIELDS:
                        if evidence.get(field) != joined_object["configuration"].get(field):
                            self.error(
                                f"{row_location}.{field}",
                                "must equal the joined object's codegen configuration",
                            )
                    if evidence.get("module_sha256") != joined_object.get("module_sha256"):
                        self.error(
                            f"{row_location}.module_sha256",
                            "must bind the exact joined Trust-IR module artifact",
                        )
                    if evidence.get("object_sha256") != joined_object.get("artifact_sha256"):
                        self.error(
                            f"{row_location}.object_sha256",
                            "must bind the exact joined object artifact",
                        )
                if evidence.get("translation_relation_id") != relation.get("id"):
                    self.error(
                        f"{row_location}.translation_relation_id",
                        "must name the owner-authorized machine translation relation",
                    )
                if evidence.get("translation_relation_sha256") != relation.get("sha256"):
                    self.error(
                        f"{row_location}.translation_relation_sha256",
                        "must bind the owner-authorized machine translation relation",
                    )
                evidence_path = self.resolve_ref(
                    evidence.get("evidence"), f"{row_location}.evidence"
                )
                evidence_ref = evidence.get("evidence")
                if evidence_path is not None and isinstance(evidence_ref, dict):
                    digest = evidence_ref.get("sha256")
                    if isinstance(digest, str):
                        artifact_digests["translation_evidence"].add(digest)
            if (
                len(evidence_object_ids) != len(set(evidence_object_ids))
                or set(evidence_object_ids) != object_ids
            ):
                self.error(
                    f"{program_location}.translation_evidence",
                    "must contain exactly one translation-evidence row per emitted object",
                )

            executables = typed_rows(
                "executables",
                {
                    "id",
                    "codegen_cell_id",
                    *CODEGEN_CELL_FIELDS,
                    "object_ids",
                    "artifact",
                    "system_library_closure_sha256",
                    "composition_evidence",
                    "binary_semantics_evidence",
                },
            )
            executable_ids: set[str] = set()
            executable_cell_ids: list[str] = []
            partitioned_object_ids: list[str] = []
            for row_index, executable in enumerate(executables):
                row_location = f"{program_location}.executables[{row_index}]"
                executable_id = executable.get("id")
                executable_id_valid = True
                if (
                    not isinstance(executable_id, str)
                    or not executable_id
                    or executable_id in executable_ids
                ):
                    self.error(f"{row_location}.id", "must be a unique non-empty executable id")
                    executable_id_valid = False
                else:
                    executable_ids.add(executable_id)
                cell = self.validate_codegen_cell_binding(executable, row_location, signed_cells)
                cell_id = executable.get("codegen_cell_id")
                if isinstance(cell_id, str) and cell_id:
                    executable_cell_ids.append(cell_id)
                executable_path = self.resolve_ref(
                    executable.get("artifact"), f"{row_location}.artifact"
                )
                executable_artifact = executable.get("artifact")
                executable_digest = (
                    executable_artifact.get("sha256")
                    if isinstance(executable_artifact, dict)
                    else None
                )
                if executable_path is not None and isinstance(executable_digest, str):
                    artifact_digests["executables"].add(executable_digest)
                executable_object_ids = executable.get("object_ids")
                valid_object_list = (
                    isinstance(executable_object_ids, list)
                    and all(
                        isinstance(object_id, str) and object_id
                        for object_id in executable_object_ids
                    )
                    and len(executable_object_ids) == len(set(executable_object_ids))
                )
                if not valid_object_list:
                    self.error(
                        f"{row_location}.object_ids",
                        "must be a duplicate-free string list",
                    )
                    executable_object_ids = []
                expected_cell_objects = {
                    object_id
                    for object_id, record in object_records.items()
                    if record.get("codegen_cell_id") == cell_id
                }
                if set(executable_object_ids) != expected_cell_objects:
                    self.error(
                        f"{row_location}.object_ids",
                        "must contain exactly the objects emitted for the same codegen cell",
                    )
                partitioned_object_ids.extend(executable_object_ids)
                digest = executable.get("system_library_closure_sha256")
                if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                    self.error(f"{row_location}.system_library_closure_sha256", "must be 64-hex")
                for field in ("composition_evidence", "binary_semantics_evidence"):
                    self.resolve_ref(executable.get(field), f"{row_location}.{field}")
                if executable_id_valid and isinstance(executable_id, str):
                    executable_records[(program_id, executable_id)] = {
                        "artifact_sha256": executable_digest,
                        "codegen_cell_id": cell_id,
                        "object_ids": executable_object_ids,
                    }
            if (
                len(executable_cell_ids) != len(set(executable_cell_ids))
                or set(executable_cell_ids) != set(signed_cells)
            ):
                self.error(
                    f"{program_location}.executables",
                    "must contain exactly one linked executable per signed codegen cell",
                )
            if (
                len(partitioned_object_ids) != len(set(partitioned_object_ids))
                or set(partitioned_object_ids) != object_ids
            ):
                self.error(
                    f"{program_location}.executables.object_ids",
                    "executable object lists must exactly partition the emitted objects by cell",
                )

        if observed_languages != {"rust", "lean"}:
            self.error(
                f"{location}.programs.languages",
                "subject graph must contain reachable Rust and Lean bodies",
            )
        if observed_cross_language_directions != {"rust_to_lean", "lean_to_rust"}:
            self.error(
                f"{location}.programs.call_edges",
                "subject graph must contain typed Rust-to-Lean and Lean-to-Rust edges",
            )
        required_categories = {
            "value",
            "aggregate",
            "reference",
            "error",
            "callback",
            "result",
        }
        required_cross_language_matrix = {
            (direction, category)
            for direction in ("rust_to_lean", "lean_to_rust")
            for category in required_categories
        }
        if observed_cross_language_matrix != required_cross_language_matrix:
            self.error(
                f"{location}.programs.call_edges.value_category",
                "mixed subject must witness every direction/value-category pair in the complete cross-language matrix",
            )
        if observed_obligation_classes != OBLIGATION_CLASSES:
            self.error(
                f"{location}.programs.obligations.policy_classes",
                "subject graph must witness every owner-required obligation class",
            )
        if observed_admitted_files != admitted_corpus_ids:
            self.error(
                f"{location}.programs.admitted_file_ids",
                "program index must cover exactly the admitted corpus IDs",
            )
        release_record: dict[str, Any] | None = None
        if release_locator_valid and isinstance(release_locator, dict):
            release_program_id = release_locator.get("program_id")
            release_executable_id = release_locator.get("executable_id")
            if not isinstance(release_program_id, str) or not release_program_id:
                self.error(
                    f"{location}.release_executable.program_id",
                    "must be a non-empty string",
                )
            if not isinstance(release_executable_id, str) or not release_executable_id:
                self.error(
                    f"{location}.release_executable.executable_id",
                    "must be a non-empty string",
                )
            if isinstance(release_program_id, str) and isinstance(
                release_executable_id, str
            ):
                release_record = executable_records.get(
                    (release_program_id, release_executable_id)
                )
            if release_record is None:
                self.error(
                    f"{location}.release_executable",
                    "must resolve to exactly one typed executable row",
                )
            else:
                if release_record.get("artifact_sha256") != release_artifact_digest:
                    self.error(
                        f"{location}.release_executable",
                        "must select the exact receipt release artifact",
                    )
                release_objects = object_records_by_program.get(
                    release_program_id, {}
                )
                linked_inputs = [
                    release_objects[object_id].get("module_sha256")
                    for object_id in release_record.get("object_ids", [])
                    if object_id in release_objects
                ]
                if linked_inputs.count(linked_module_digest) != 1:
                    self.error(
                        f"{location}.release_executable",
                        "must consume exactly one object produced from the designated linked module",
                    )
        for root_name in sorted(root_names):
            rows = sorted(
                root_rows[root_name],
                key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")),
            )
            actual_root = _canonical_json_sha256(rows)
            if roots.get(root_name) != actual_root:
                self.error(
                    f"{location}.roots.{root_name}",
                    f"canonical root mismatch: recorded {roots.get(root_name)!r}, "
                    f"actual {actual_root!r}",
                )
        if linked_module_digest not in artifact_digests["modules"]:
            self.error("receipt.linked_module", "must name a typed module artifact")
        if release_artifact_digest not in artifact_digests["executables"]:
            self.error("receipt.release_artifact", "must name a typed linked executable")
        return artifact_digests

    def validate_policy(
        self,
        value: dict[str, Any] | None,
        source_revision: Any,
        acceptance_run_id: Any,
        authorized_inputs: dict[str, Any],
    ) -> None:
        location = "authority_policy"
        if value is None:
            return
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "repository_id",
                "completion_schema",
                "authorized_source_revision",
                "authorized_acceptance_run_id",
                "owner_key_fingerprint",
                "authorized_inputs",
                "contracts",
                "authorized_checkers",
            },
            location,
        )
        expected = {
            "schema": POLICY_SCHEMA,
            "goal_id": GOAL_ID,
            "repository_id": REPOSITORY_ID,
            "completion_schema": SCHEMA,
            "authorized_source_revision": source_revision,
            "authorized_acceptance_run_id": acceptance_run_id,
        }
        for key, wanted in expected.items():
            if value.get(key) != wanted:
                self.error(f"{location}.{key}", f"must equal {wanted!r}")
        fingerprint = value.get("owner_key_fingerprint")
        if not isinstance(fingerprint, str) or len(fingerprint) < 16:
            self.error(
                f"{location}.owner_key_fingerprint",
                "must name the externally trusted owner signing key",
            )
        inputs = value.get("authorized_inputs")
        if self.exact_keys(inputs, set(authorized_inputs), f"{location}.authorized_inputs"):
            for key, wanted in authorized_inputs.items():
                if inputs.get(key) != wanted:
                    self.error(
                        f"{location}.authorized_inputs.{key}",
                        "must equal the exact owner-authorized receipt input digest",
                    )
        contracts = value.get("contracts")
        if isinstance(contracts, dict):
            self.exact_keys(contracts, set(AUTHORITY_CONTRACTS), f"{location}.contracts")
        authorized = value.get("authorized_checkers")
        if not isinstance(authorized, dict) or set(authorized) != set(GATES):
            self.error(
                f"{location}.authorized_checkers",
                "must contain exactly G1-G8",
            )
            return
        for gate in GATES:
            row_location = f"{location}.authorized_checkers.{gate}"
            row = authorized.get(gate)
            if not self.exact_keys(row, {"id", "path", "sha256"}, row_location):
                continue
            expected_row = {
                "id": CHECKER_IDS[gate],
                "path": CHECKER_PATHS[gate],
            }
            for key, wanted in expected_row.items():
                if row.get(key) != wanted:
                    self.error(f"{row_location}.{key}", f"must equal {wanted!r}")
            if not isinstance(row.get("sha256"), str) or not HEX_DIGEST.fullmatch(
                row["sha256"]
            ):
                self.error(f"{row_location}.sha256", "must be a lowercase 64-hex digest")

    def verify_policy_authorization(
        self,
        envelope_path: Path | None,
        policy_path: Path | None,
        policy_digest: Any,
        policy_value: dict[str, Any] | None,
    ) -> None:
        """Verify candidate policy against an Ed25519 key supplied outside --root."""
        location = "policy_authorization"
        if self.trusted_owner_key is None:
            self.error(
                location,
                "--trusted-owner-key is required and must be rooted outside --root",
            )
            return
        try:
            self.trusted_owner_key.relative_to(self.root)
        except ValueError:
            pass
        else:
            self.error(location, "trusted owner key must be outside the candidate repository")
            return
        if not self.trusted_owner_key.is_file():
            self.error(location, f"trusted owner key does not exist: {self.trusted_owner_key}")
            return
        try:
            key_fields = self.trusted_owner_key.read_text(encoding="utf-8").strip().split()
        except (OSError, UnicodeError) as exc:
            self.error(location, f"cannot read trusted owner key: {exc}")
            return
        if len(key_fields) < 2 or key_fields[0] != "ssh-ed25519":
            self.error(location, "trusted owner key must contain one ssh-ed25519 public key")
            return
        if not SSH_KEYGEN.is_file():
            self.error(location, f"required verifier is unavailable: {SSH_KEYGEN}")
            return
        fingerprint_process = subprocess.run(
            [str(SSH_KEYGEN), "-lf", str(self.trusted_owner_key), "-E", "sha256"],
            check=False,
            capture_output=True,
            text=True,
            env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"},
        )
        fingerprint_fields = fingerprint_process.stdout.split()
        if fingerprint_process.returncode != 0 or len(fingerprint_fields) < 2:
            self.error(location, "cannot derive trusted owner key fingerprint")
            return
        fingerprint = fingerprint_fields[1]
        self.trusted_owner_fingerprint = fingerprint
        if policy_value is None or policy_value.get("owner_key_fingerprint") != fingerprint:
            self.error(
                f"{location}.signer_fingerprint",
                "policy fingerprint does not equal the externally trusted owner key",
            )
        if envelope_path is None or not envelope_path.is_file() or policy_path is None:
            return
        envelope = self.load_json(envelope_path, location)
        if envelope is None:
            return
        self.exact_keys(
            envelope,
            {
                "schema",
                "algorithm",
                "namespace",
                "signer_fingerprint",
                "policy_sha256",
                "signature",
            },
            location,
        )
        expected = {
            "schema": POLICY_AUTH_SCHEMA,
            "algorithm": "ssh-ed25519",
            "namespace": POLICY_SIGNATURE_NAMESPACE,
            "signer_fingerprint": fingerprint,
            "policy_sha256": policy_digest,
        }
        for key, wanted in expected.items():
            if envelope.get(key) != wanted:
                self.error(f"{location}.{key}", f"must equal {wanted!r}")
        signature_path = self.resolve_ref(envelope.get("signature"), f"{location}.signature")
        if signature_path is None or not signature_path.is_file():
            return
        with tempfile.TemporaryDirectory(prefix="trust-owner-policy-") as tmp:
            allowed_signers = Path(tmp) / "allowed_signers"
            allowed_signers.write_text(
                f"trust-owner {key_fields[0]} {key_fields[1]}\n",
                encoding="utf-8",
            )
            verify = subprocess.run(
                [
                    str(SSH_KEYGEN),
                    "-Y",
                    "verify",
                    "-f",
                    str(allowed_signers),
                    "-I",
                    "trust-owner",
                    "-n",
                    POLICY_SIGNATURE_NAMESPACE,
                    "-s",
                    str(signature_path),
                ],
                input=policy_path.read_bytes(),
                check=False,
                capture_output=True,
                env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"},
            )
        if verify.returncode != 0:
            detail = verify.stderr.decode("utf-8", errors="replace").strip()
            self.error(location, f"owner policy signature verification failed: {detail}")

    def post_run_integrity_check(self) -> None:
        """Close ordinary concurrent-mutation races around checker execution."""
        for path, expected in sorted(self.bound_files.items(), key=lambda item: str(item[0])):
            if not path.is_file():
                self.error("post_run_integrity", f"bound file disappeared: {path}")
                continue
            actual = _sha256(path)
            if actual != expected:
                self.error(
                    "post_run_integrity",
                    f"bound file changed during checker execution: {path}",
                )
        status_rc, dirty = _git(self.root, "status", "--porcelain", "--untracked-files=all")
        if status_rc != 0:
            self.error("post_run_integrity", "cannot re-inspect worktree state")
        elif dirty:
            self.error("post_run_integrity", "worktree became dirty during checker execution")

    def validate(self) -> dict[str, Any]:
        receipt = self.load_json(self.receipt_path, "receipt")
        gate_results = {gate: False for gate in GATES}
        if receipt is None:
            return self.verdict(gate_results)

        receipt_keys = {
            "schema",
            "goal_id",
            "repository_id",
            "acceptance_run_id",
            "source_revision",
            "toolchain_manifest",
            "corpus_manifest",
            "subject_graph",
            "linked_module",
            "release_artifact",
            "authority_policy",
            "policy_authorization",
            "gates",
        }
        self.exact_keys(receipt, receipt_keys, "receipt")
        if receipt.get("schema") != SCHEMA:
            self.error("receipt.schema", f"must equal {SCHEMA!r}")
        if receipt.get("goal_id") != GOAL_ID:
            self.error("receipt.goal_id", f"must equal {GOAL_ID!r}")
        if receipt.get("repository_id") != REPOSITORY_ID:
            self.error("receipt.repository_id", f"must equal {REPOSITORY_ID!r}")

        acceptance_run_id = receipt.get("acceptance_run_id")
        if not isinstance(acceptance_run_id, str) or not HEX_DIGEST.fullmatch(
            acceptance_run_id
        ):
            self.error(
                "receipt.acceptance_run_id",
                "must be a lowercase 64-hex run/subject identity",
            )

        source_revision = receipt.get("source_revision")
        if not isinstance(source_revision, str) or not GIT_REVISION.fullmatch(source_revision):
            self.error("receipt.source_revision", "must be a lowercase 40-64 hex revision")

        head_rc, head = _git(self.root, "rev-parse", "HEAD")
        if head_rc != 0:
            self.error("repository", "--root is not a readable Git worktree")
        elif source_revision != head:
            self.error(
                "receipt.source_revision",
                f"does not match --root HEAD: recorded {source_revision!r}, actual {head!r}",
            )
        origin_rc, origin = _git(self.root, "config", "--get", "remote.origin.url")
        canonical_origin = origin[:-4] if origin.endswith(".git") else origin
        if origin_rc != 0 or canonical_origin != REPOSITORY_ID:
            self.error(
                "repository.origin",
                f"must identify {REPOSITORY_ID!r}; actual {origin!r}",
            )
        status_rc, dirty = _git(self.root, "status", "--porcelain", "--untracked-files=all")
        if status_rc != 0:
            self.error("repository", "cannot inspect worktree state")
        elif dirty:
            self.error("repository", "worktree is not clean")

        receipt_digest = _sha256(self.receipt_path)
        self.bound_files[self.receipt_path] = receipt_digest
        toolchain_path = self.resolve_ref(
            receipt.get("toolchain_manifest"),
            "receipt.toolchain_manifest",
        )
        corpus_path = self.resolve_ref(receipt.get("corpus_manifest"), "receipt.corpus_manifest")
        subject_graph_path = self.resolve_ref(
            receipt.get("subject_graph"),
            "receipt.subject_graph",
        )
        linked_module_path = self.resolve_ref(
            receipt.get("linked_module"),
            "receipt.linked_module",
        )
        release_artifact_path = self.resolve_ref(
            receipt.get("release_artifact"),
            "receipt.release_artifact",
        )
        policy_path = self.resolve_ref(
            receipt.get("authority_policy"),
            "receipt.authority_policy",
        )
        policy_authorization_path = self.resolve_ref(
            receipt.get("policy_authorization"),
            "receipt.policy_authorization",
        )
        toolchain_digest = (
            receipt.get("toolchain_manifest", {}).get("sha256")
            if isinstance(receipt.get("toolchain_manifest"), dict)
            else None
        )
        corpus_digest = (
            receipt.get("corpus_manifest", {}).get("sha256")
            if isinstance(receipt.get("corpus_manifest"), dict)
            else None
        )
        subject_graph_digest = (
            receipt.get("subject_graph", {}).get("sha256")
            if isinstance(receipt.get("subject_graph"), dict)
            else None
        )
        linked_module_digest = (
            receipt.get("linked_module", {}).get("sha256")
            if isinstance(receipt.get("linked_module"), dict)
            else None
        )
        release_artifact_digest = (
            receipt.get("release_artifact", {}).get("sha256")
            if isinstance(receipt.get("release_artifact"), dict)
            else None
        )
        policy_digest = (
            receipt.get("authority_policy", {}).get("sha256")
            if isinstance(receipt.get("authority_policy"), dict)
            else None
        )
        policy_authorization_digest = (
            receipt.get("policy_authorization", {}).get("sha256")
            if isinstance(receipt.get("policy_authorization"), dict)
            else None
        )
        common_paths = {
            "toolchain_manifest": toolchain_path,
            "corpus_manifest": corpus_path,
            "subject_graph": subject_graph_path,
            "linked_module": linked_module_path,
            "release_artifact": release_artifact_path,
            "authority_policy": policy_path,
            "policy_authorization": policy_authorization_path,
        }
        non_null_common_paths = [path for path in common_paths.values() if path is not None]
        if len(non_null_common_paths) != len(set(non_null_common_paths)):
            self.error("receipt", "all common bound artifacts must use distinct paths")

        toolchain_manifest = (
            self.load_json(toolchain_path, "toolchain_manifest")
            if toolchain_path is not None and toolchain_path.is_file()
            else None
        )
        corpus_manifest = (
            self.load_json(corpus_path, "corpus_manifest")
            if corpus_path is not None and corpus_path.is_file()
            else None
        )
        subject_graph = (
            self.load_json(subject_graph_path, "subject_graph")
            if subject_graph_path is not None and subject_graph_path.is_file()
            else None
        )
        authority_policy = (
            self.load_json(policy_path, "authority_policy")
            if policy_path is not None and policy_path.is_file()
            else None
        )
        authorized_inputs = {
            "toolchain_manifest_sha256": toolchain_digest,
            "corpus_manifest_sha256": corpus_digest,
            "subject_graph_sha256": subject_graph_digest,
            "linked_module_sha256": linked_module_digest,
            "release_artifact_sha256": release_artifact_digest,
        }
        self.validate_policy(
            authority_policy,
            source_revision,
            acceptance_run_id,
            authorized_inputs,
        )
        self.verify_policy_authorization(
            policy_authorization_path,
            policy_path,
            policy_digest,
            authority_policy,
        )
        authority_contracts = self.validate_authority_contracts(authority_policy)
        self.validate_toolchain_manifest(
            toolchain_manifest,
            acceptance_run_id,
            source_revision,
            authority_contracts,
        )
        admitted_corpus_ids = self.validate_corpus_manifest(
            corpus_manifest,
            acceptance_run_id,
            source_revision,
            authority_contracts,
        )
        self.validate_subject_graph(
            subject_graph,
            acceptance_run_id,
            source_revision,
            admitted_corpus_ids,
            linked_module_digest,
            release_artifact_digest,
            authority_contracts,
        )
        if (
            policy_authorization_path is not None
            and policy_authorization_path.is_file()
            and policy_authorization_path.stat().st_size == 0
        ):
            self.error("receipt.policy_authorization", "must not be empty")

        gates = receipt.get("gates")
        if not isinstance(gates, dict):
            self.error("receipt.gates", "must be an object")
            return self.verdict(gate_results)
        actual_gates = set(gates)
        if actual_gates != set(GATES):
            missing = sorted(set(GATES) - actual_gates)
            unknown = sorted(actual_gates - set(GATES))
            if missing:
                self.error("receipt.gates", f"missing gates {missing}")
            if unknown:
                self.error("receipt.gates", f"unknown gates {unknown}")

        common_binding_ok = not self.errors
        descriptors: dict[str, tuple[str, Path, str, bytes, Path, Any]] = {}
        descriptor_ok = {gate: False for gate in GATES}
        checker_ids: set[str] = set()
        evidence_paths: set[Path] = set()
        for gate in GATES:
            before = len(self.errors)
            descriptor = gates.get(gate)
            location = f"receipt.gates.{gate}"
            if not self.exact_keys(
                descriptor,
                {"checker", "checker_sha256", "evidence"},
                location,
            ):
                continue
            checker = descriptor.get("checker")
            if not isinstance(checker, str) or not CHECKER_ID.fullmatch(checker):
                self.error(f"{location}.checker", "has an invalid checker id")
                continue
            if checker != CHECKER_IDS[gate]:
                self.error(
                    f"{location}.checker",
                    f"must equal the schema-owned checker id {CHECKER_IDS[gate]!r}",
                )
            if checker in checker_ids:
                self.error(f"{location}.checker", "checker ids must be distinct across G1-G8")
            checker_ids.add(checker)
            checker_result = self.resolve_checker(
                gate,
                source_revision,
                descriptor.get("checker_sha256"),
                f"{location}.checker_sha256",
            )
            authorized_checker = (
                authority_policy.get("authorized_checkers", {}).get(gate)
                if isinstance(authority_policy, dict)
                and isinstance(authority_policy.get("authorized_checkers"), dict)
                else None
            )
            if (
                not isinstance(authorized_checker, dict)
                or descriptor.get("checker_sha256") != authorized_checker.get("sha256")
            ):
                self.error(
                    f"{location}.checker_sha256",
                    "does not equal the owner-authorized checker digest",
                )
            evidence_path = self.resolve_ref(descriptor.get("evidence"), f"{location}.evidence")
            if checker_result is None or evidence_path is None:
                continue
            checker_path, checker_digest, checker_bytes = checker_result
            if evidence_path in evidence_paths:
                self.error(f"{location}.evidence.path", "evidence receipts must be distinct")
            evidence_paths.add(evidence_path)
            evidence_digest = (
                descriptor.get("evidence", {}).get("sha256")
                if isinstance(descriptor.get("evidence"), dict)
                else None
            )
            descriptors[gate] = (
                checker,
                checker_path,
                checker_digest,
                checker_bytes,
                evidence_path,
                evidence_digest,
            )
            descriptor_ok[gate] = len(self.errors) == before

        forbidden = {
            self.receipt_path,
            *evidence_paths,
            *(descriptor[1] for descriptor in descriptors.values()),
        }
        for metadata_path in (
            toolchain_path,
            corpus_path,
            subject_graph_path,
            policy_path,
            policy_authorization_path,
        ):
            if metadata_path is not None:
                forbidden.add(metadata_path)

        common_paths_ready = common_binding_ok and all(
            path is not None and path.is_file() for path in common_paths.values()
        )
        checker_verdicts: dict[str, dict[str, Any]] = {}

        def validate_gate(gate: str, prior_gates_root: str | None) -> None:
            before = len(self.errors)
            if gate not in descriptors:
                return
            if not common_paths_ready:
                self.error(f"{gate}.checker_run", "common bound artifacts are unavailable")
                return
            (
                checker,
                _checker_path,
                checker_digest,
                checker_bytes,
                evidence_path,
                evidence_digest,
            ) = descriptors[gate]
            assert toolchain_path is not None
            assert corpus_path is not None
            assert subject_graph_path is not None
            assert linked_module_path is not None
            assert release_artifact_path is not None
            assert policy_path is not None
            assert policy_authorization_path is not None
            checker_verdict = self.run_checker(
                gate,
                checker_bytes,
                evidence_path,
                toolchain_path,
                corpus_path,
                subject_graph_path,
                linked_module_path,
                release_artifact_path,
                policy_path,
                policy_authorization_path,
                acceptance_run_id,
                subject_graph_digest,
                linked_module_digest,
                release_artifact_digest,
                policy_digest,
                policy_authorization_digest,
                source_revision,
                checker_digest,
                evidence_digest,
                toolchain_digest,
                corpus_digest,
                prior_gates_root,
            )
            if checker_verdict is None:
                return
            checker_verdicts[gate] = checker_verdict
            verdict_keys = {
                "schema",
                "goal_id",
                "gate",
                "checker",
                "repository_id",
                "acceptance_run_id",
                "checker_sha256",
                "evidence_sha256",
                "source_revision",
                "toolchain_sha256",
                "corpus_manifest_sha256",
                "subject_graph_sha256",
                "linked_module_sha256",
                "release_artifact_sha256",
                "authority_policy_sha256",
                "policy_authorization_sha256",
                "prior_gates_root",
                "passed",
                "checks",
            }
            self.exact_keys(checker_verdict, verdict_keys, f"{gate}.checker_verdict")
            expected_scalars = {
                "schema": CHECKER_VERDICT_SCHEMA,
                "goal_id": GOAL_ID,
                "gate": gate,
                "checker": checker,
                "repository_id": REPOSITORY_ID,
                "acceptance_run_id": acceptance_run_id,
                "checker_sha256": checker_digest,
                "evidence_sha256": evidence_digest,
                "source_revision": source_revision,
                "toolchain_sha256": toolchain_digest,
                "corpus_manifest_sha256": corpus_digest,
                "subject_graph_sha256": subject_graph_digest,
                "linked_module_sha256": linked_module_digest,
                "release_artifact_sha256": release_artifact_digest,
                "authority_policy_sha256": policy_digest,
                "policy_authorization_sha256": policy_authorization_digest,
                "prior_gates_root": prior_gates_root,
            }
            for key, expected in expected_scalars.items():
                if checker_verdict.get(key) != expected:
                    self.error(
                        f"{gate}.checker_verdict.{key}",
                        f"must equal the receipt-bound value {expected!r}",
                    )
            if checker_verdict.get("passed") is not True:
                self.error(
                    f"{gate}.checker_verdict.passed",
                    "fresh checker verdict must be the boolean true",
                )

            checks = checker_verdict.get("checks")
            if not isinstance(checks, list) or not checks:
                self.error(f"{gate}.checker_verdict.checks", "must be a non-empty list")
                return
            rows: dict[str, dict[str, Any]] = {}
            for index, row in enumerate(checks):
                row_location = f"{gate}.checker_verdict.checks[{index}]"
                if not self.exact_keys(row, {"id", "passed", "artifacts"}, row_location):
                    continue
                check_id = row.get("id")
                if not isinstance(check_id, str) or not check_id:
                    self.error(f"{row_location}.id", "must be a non-empty string")
                    continue
                if check_id in rows:
                    self.error(f"{row_location}.id", f"duplicate check id {check_id!r}")
                rows[check_id] = row
                if row.get("passed") is not True:
                    self.error(f"{row_location}.passed", "must be the boolean true")
                artifacts = row.get("artifacts")
                if not isinstance(artifacts, list) or not artifacts:
                    self.error(f"{row_location}.artifacts", "must be a non-empty list")
                    continue
                seen_artifacts: set[Path] = set()
                for artifact_index, artifact in enumerate(artifacts):
                    artifact_path = self.resolve_ref(
                        artifact,
                        f"{row_location}.artifacts[{artifact_index}]",
                        forbidden=forbidden,
                    )
                    if artifact_path is not None and artifact_path in seen_artifacts:
                        self.error(
                            f"{row_location}.artifacts[{artifact_index}]",
                            "duplicates an artifact in the same check",
                        )
                    if artifact_path is not None:
                        seen_artifacts.add(artifact_path)

            required = set(REQUIRED_CHECKS[gate])
            observed = set(rows)
            if required - observed:
                self.error(
                    f"{gate}.checker_verdict.checks",
                    f"missing required checks {sorted(required - observed)}",
                )
            if observed - required:
                self.error(
                    f"{gate}.checker_verdict.checks",
                    f"unknown checks {sorted(observed - required)}",
                )
            gate_results[gate] = (
                common_binding_ok
                and descriptor_ok[gate]
                and len(self.errors) == before
            )

        for gate in GATES[:-1]:
            validate_gate(gate, None)

        if all(gate_results[gate] for gate in GATES[:-1]):
            root_payload = {
                "schema": "trust.two-language.prior-gates-root/v1",
                "goal_id": GOAL_ID,
                "repository_id": REPOSITORY_ID,
                "acceptance_run_id": acceptance_run_id,
                "source_revision": source_revision,
                "subject_graph_sha256": subject_graph_digest,
                "linked_module_sha256": linked_module_digest,
                "release_artifact_sha256": release_artifact_digest,
                "gates": {gate: checker_verdicts[gate] for gate in GATES[:-1]},
            }
            canonical = json.dumps(
                root_payload,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
            self.prior_gates_root = hashlib.sha256(canonical).hexdigest()
            validate_gate("G8", self.prior_gates_root)
        else:
            self.error("G8.checker_run", "G1-G7 must pass before the G8 seal checker runs")

        self.post_run_integrity_check()

        return self.verdict(gate_results)

    def verdict(self, gate_results: dict[str, bool]) -> dict[str, Any]:
        accepted = not self.errors and all(gate_results.values())
        return {
            "schema": VERDICT_SCHEMA,
            "goal_id": GOAL_ID,
            "accepted": accepted,
            "result": (
                "checker-verified-structurally-complete" if accepted else "incomplete"
            ),
            "gate_results": gate_results,
            "prior_gates_root": self.prior_gates_root,
            "trusted_owner_key_fingerprint": self.trusted_owner_fingerprint,
            "errors": self.errors,
            "scope": "checker-executed structural conjunction of G1-G8 evidence",
            "does_not_establish": (
                "the semantic correctness of an evidence-producing checker; "
                "that checker and its independent controls own that claim"
            ),
        }


def validate_receipt(
    receipt_path: str | Path,
    root: str | Path,
    trusted_owner_key: str | Path | None = None,
) -> dict[str, Any]:
    root_path = Path(root)
    resolved_receipt = Path(receipt_path)
    if not resolved_receipt.is_absolute():
        resolved_receipt = root_path / resolved_receipt
    owner_key_path = Path(trusted_owner_key) if trusted_owner_key is not None else None
    return ReceiptValidator(root_path, resolved_receipt, owner_key_path).validate()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--receipt", required=True, help="completion receipt JSON")
    parser.add_argument("--root", default=".", help="Git worktree and artifact root")
    parser.add_argument(
        "--trusted-owner-key",
        help="external ssh-ed25519 public key that authorizes the completion policy",
    )
    parser.add_argument(
        "--candidate-verifier",
        help=(
            "candidate-tree verifier whose bytes must equal this externally pinned "
            "verifier before validating a release"
        ),
    )
    parser.add_argument("--text", action="store_true", help="print a concise human verdict")
    args = parser.parse_args(argv)
    if args.candidate_verifier is not None:
        root_path = Path(args.root).resolve()
        running_path = Path(__file__)
        if running_path.is_symlink():
            parser.error("running verifier must not be a symlink")
        running_verifier = running_path.resolve()
        try:
            running_verifier.relative_to(root_path)
        except ValueError:
            pass
        else:
            parser.error("running verifier must be outside --root")
        candidate = Path(args.candidate_verifier)
        if not candidate.is_absolute():
            candidate = root_path / candidate
        if candidate.is_symlink():
            parser.error("--candidate-verifier must not be a symlink")
        candidate = candidate.resolve()
        try:
            candidate.relative_to(root_path)
        except ValueError:
            parser.error("--candidate-verifier must resolve inside --root")
        if (
            not candidate.is_file()
            or _sha256(candidate) != _sha256(running_verifier)
        ):
            parser.error(
                "candidate verifier bytes do not equal the externally pinned verifier"
            )
    verdict = validate_receipt(args.receipt, args.root, args.trusted_owner_key)
    if args.text:
        print(f"{verdict['goal_id']}: {verdict['result'].upper()}")
        for gate, passed in verdict["gate_results"].items():
            print(f"  {gate}: {'PASS' if passed else 'INCOMPLETE'}")
        for error in verdict["errors"]:
            print(f"  ERROR: {error}")
    else:
        print(json.dumps(verdict, indent=2, sort_keys=True))
    return 0 if verdict["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())
