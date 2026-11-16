#!/usr/bin/env python3
"""Fail-closed G8 release-reproducibility evidence checker.

The completion runner executes this checker from the schema-owned path at the
accepted source revision.  Running it directly is not product acceptance: the
top-level runner must first re-execute G1-G7 and authenticate the clean commit.

The release executable is a binary, not a JSON receipt.  No producer currently
embeds a replayable proof/evidence index in it, nor supplies authenticated
cold/warm run observations or fresh G1-G7 verdicts to this process.  Those
conjuncts refuse even when an authored artifact says "passed".  A caller must
also supply the trusted owner key and top-verifier pin outside the source tree;
neither is inferred from a candidate-controlled file.  "Outside the source
tree" is decided by filesystem identity, not spelling: a path that is, or lies
under, the --root directory's own inode is inside it however it is written.

Every malformed or hostile path (including a symlink loop, which Python 3.9's
Path.resolve raises as RuntimeError) is a structured refusal, so the checker
always prints exactly one verdict.
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
GATE = "G8"
CHECKER = "trust.two-language.g8.release-reproducibility/v3"
REPOSITORY = "https://github.com/alabsystems/trust"
RECEIPT_SCHEMA = "trust.two-language.completion/v2"
POLICY_SCHEMA = "trust.two-language.authority-policy/v2"
AUTH_SCHEMA = "trust.two-language.policy-authorization/v1"
TOOLCHAIN_SCHEMA = "trust.two-language.toolchain-manifest/v1"
ENV_SCHEMA = "trust.two-language.acceptance-environment-contract/v1"
SEAL_SCHEMA = "trust.two-language.detached-release-seal/v1"
POLICY_NAMESPACE = "trust-two-language-policy"
SEAL_NAMESPACE = "trust-two-language-g8-release"
HEX = re.compile(r"^[0-9a-f]{64}$")
REVISION = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
OPENSSH_BASE64 = re.compile(r"^[A-Za-z0-9+/]+={0,2}$")
SSH_KEYGEN = Path("/usr/bin/ssh-keygen")
PRIOR_GATES = tuple(f"G{i}" for i in range(1, 8))
RUN_MODES = {"cold_build", "warm_build", "cross_crate", "mixed_language", "tests", "release"}
TOOLCHAIN_ROLES = {
    "trustc", "rust_frontend", "lean_frontend", "clean_kernel", "trust_ir_producer",
    "trust_ir_linker", "trust_codegen", "trust_router", "proof_reconstructor",
    "runtime", "linker", "top_verifier", "python", "ssh_keygen",
}
REQUIRED = (
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


class Refusal(Exception):
    pass


def digest(path: Path) -> str:
    h = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1 << 20), b""):
                h.update(chunk)
    except OSError as exc:
        raise Refusal(f"cannot read {path}: {exc}") from exc
    return h.hexdigest()


def json_object(path: Path) -> dict[str, Any]:
    try:
        _trust_text = path.read_text(encoding="utf-8")
        if _trust_json_nesting_depth(_trust_text) > TRUST_MAX_JSON_DEPTH:
            raise ValueError(f"JSON nests deeper than {TRUST_MAX_JSON_DEPTH}")
        value = json.loads(_trust_text)
    except (OSError, UnicodeError, ValueError, RecursionError) as exc:
        raise Refusal(f"cannot read JSON {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise Refusal(f"{path} must contain a JSON object")
    return value


def exact(value: Any, keys: set[str], where: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        raise Refusal(f"{where} must have exactly {sorted(keys)}")
    return value


def hex_digest(value: Any, where: str) -> str:
    if not isinstance(value, str) or not HEX.fullmatch(value):
        raise Refusal(f"{where} must be lowercase 64-hex")
    return value


def resolved(raw: str, where: str) -> Path:
    # Python 3.9 raises RuntimeError for a symlink loop; later versions do not.
    try:
        return Path(raw).resolve()
    except (OSError, ValueError, RuntimeError) as exc:
        raise Refusal(f"{where} cannot be resolved: {exc}") from exc


def inside_root(root: Path, path: Path) -> bool:
    """Whether ``path`` is ``root`` or lies under it BY IDENTITY.

    A lexical test misses a case-aliased spelling on a case-insensitive
    filesystem, which names the same directory under a different string, so
    the path and each ancestor is compared with the root's (st_dev, st_ino).
    A component that cannot be inspected refuses: an unknown ancestor cannot
    be shown not to be the root."""
    if path.is_relative_to(root):
        return True
    try:
        root_stat = os.stat(root)
    except (OSError, ValueError) as exc:
        raise Refusal(f"--root cannot be inspected: {exc}") from exc
    for candidate in (path, *path.parents):
        try:
            st = os.stat(candidate)
        except (OSError, ValueError) as exc:
            raise Refusal(f"cannot inspect {candidate} to decide it is outside --root: {exc}") from exc
        if (st.st_dev, st.st_ino) == (root_stat.st_dev, root_stat.st_ino):
            return True
    return False


def external_path(root: Path, raw: str | None, where: str) -> Path:
    if not raw:
        raise Refusal(f"{where} is required outside --root")
    path = Path(raw)
    if not path.is_absolute():
        raise Refusal(f"{where} must be an absolute external path")
    candidate = resolved(raw, where)
    if candidate.is_relative_to(root):
        raise Refusal(f"{where} must be outside --root")
    if not candidate.is_file():
        raise Refusal(f"{where} does not exist")
    if inside_root(root, candidate):
        raise Refusal(f"{where} must be outside --root")
    return candidate


def ref(root: Path, value: Any, where: str) -> tuple[Path, str]:
    row = exact(value, {"path", "sha256"}, where)
    raw = row["path"]
    if not isinstance(raw, str) or not raw or "\0" in raw or Path(raw).is_absolute():
        raise Refusal(f"{where}.path must be a non-empty relative path")
    try:
        path = (root / raw).resolve()
    except (OSError, ValueError, RuntimeError) as exc:
        raise Refusal(f"{where}.path cannot be resolved: {exc}") from exc
    if not path.is_relative_to(root):
        raise Refusal(f"{where}.path escapes --root")
    expected = hex_digest(row["sha256"], f"{where}.sha256")
    if not path.is_file() or digest(path) != expected:
        raise Refusal(f"{where} file is missing or its digest differs")
    return path, expected


def input_file(root: Path, raw: str, expected: str, where: str) -> Path:
    path = resolved(raw, where)
    if not path.is_relative_to(root) or not path.is_file():
        raise Refusal(f"{where} must be a file under --root")
    if digest(path) != hex_digest(expected, f"{where} digest"):
        raise Refusal(f"{where} digest differs from its receipt binding")
    return path


def owner_key(root: Path, raw: str | None) -> tuple[Path, str, str]:
    """The external owner key's fingerprint and verifying material.

    Both come from the SAME bytes: the file must be exactly one non-blank line
    ``ssh-ed25519 <base64> [comment...]``; the material ``ssh-ed25519
    <base64>`` is what signatures verify under, and it is that material alone
    (not the original file) that ssh-keygen fingerprints.  Fingerprinting the
    file instead would let ``ssh-keygen -lf``, which skips unparseable lines,
    report a different key than the one written to allowed_signers."""
    path = external_path(root, raw, "--trusted-owner-key")
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise Refusal(f"cannot read external owner key: {exc}") from exc
    lines = [line for line in text.split("\n") if line.strip()]
    fields = lines[0].split() if len(lines) == 1 else []
    if (len(fields) < 2 or fields[0] != "ssh-ed25519"
            or not OPENSSH_BASE64.fullmatch(fields[1])):
        raise Refusal("external owner key must contain exactly one ssh-ed25519 key")
    material = f"{fields[0]} {fields[1]}"
    if not SSH_KEYGEN.is_file():
        raise Refusal("/usr/bin/ssh-keygen is unavailable")
    with tempfile.TemporaryDirectory(prefix="trust-g8-key-") as temp:
        normalized = Path(temp) / "owner.pub"
        normalized.write_text(f"{material}\n", encoding="utf-8")
        result = subprocess.run(
            [str(SSH_KEYGEN), "-lf", str(normalized), "-E", "sha256"],
            capture_output=True, text=True, check=False,
            env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"},
        )
    reported = result.stdout.splitlines()
    parts = reported[0].split() if len(reported) == 1 else []
    if (result.returncode != 0 or len(parts) < 3 or not parts[1].startswith("SHA256:")
            or parts[-1] != "(ED25519)"):
        raise Refusal("cannot fingerprint external owner key")
    return path, parts[1], material


def verify_signature(root: Path, signature: Any, message: bytes, namespace: str,
                     key_material: str) -> None:
    sig_path, _ = ref(root, signature, "signature")
    with tempfile.TemporaryDirectory(prefix="trust-g8-sig-") as temp:
        allowed = Path(temp) / "allowed_signers"
        allowed.write_text(f"trust-owner {key_material}\n", encoding="utf-8")
        result = subprocess.run(
            [str(SSH_KEYGEN), "-Y", "verify", "-f", str(allowed), "-I", "trust-owner",
             "-n", namespace, "-s", str(sig_path)],
            input=message, capture_output=True, check=False,
            env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"},
        )
    if result.returncode != 0:
        raise Refusal(f"external owner signature does not verify for {namespace}")


def require_cited(check_id: str, cited: tuple[Path, str], checked: tuple[Path, str]) -> None:
    """A structural row cites exactly the input its predicate decided on.

    Otherwise the verdict row would record an unrelated authored file as its
    evidence while the predicate read something else."""
    if cited != checked:
        raise Refusal(f"{check_id} artifact must be the input its predicate checks")


class Context:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.root = Path(args.root)
        self.receipt: dict[str, Any] | None = None
        self.policy: dict[str, Any] | None = None
        self.fingerprint: str | None = None
        self.key_material: str | None = None
        self.inputs: dict[str, Path] = {}
        self.common_error: str | None = None
        try:
            # An unresolvable --root refuses every conjunct via require_common.
            self.root = resolved(args.root, "--root")
            self.load_common()
        except (Refusal, OSError, ValueError, RuntimeError) as exc:
            self.common_error = str(exc)

    def load_common(self) -> None:
        a = self.args
        for field in (
            "acceptance_run_id", "checker_sha256", "evidence_sha256", "toolchain_sha256",
            "corpus_manifest_sha256", "subject_graph_sha256", "linked_module_sha256",
            "release_artifact_sha256", "authority_policy_sha256",
            "policy_authorization_sha256", "prior_gates_root",
        ):
            hex_digest(getattr(a, field), f"--{field.replace('_', '-')}")
        if not REVISION.fullmatch(a.source_revision or ""):
            raise Refusal("--source-revision must be lowercase 40- or 64-hex")
        if digest(Path(__file__)) != a.checker_sha256:
            raise Refusal("executed G8 checker bytes differ from --checker-sha256")
        paths = {
            "toolchain_manifest": (a.toolchain_manifest, a.toolchain_sha256),
            "corpus_manifest": (a.corpus_manifest, a.corpus_manifest_sha256),
            "subject_graph": (a.subject_graph, a.subject_graph_sha256),
            "linked_module": (a.linked_module, a.linked_module_sha256),
            "release_artifact": (a.release_artifact, a.release_artifact_sha256),
            "authority_policy": (a.authority_policy, a.authority_policy_sha256),
            "policy_authorization": (a.policy_authorization, a.policy_authorization_sha256),
        }
        receipt_path = resolved(a.receipt, "receipt")
        if not receipt_path.is_relative_to(self.root) or not receipt_path.is_file():
            raise Refusal("receipt must be a file under --root")
        receipt = json_object(receipt_path)
        exact(receipt, {
            "schema", "goal_id", "repository_id", "acceptance_run_id", "source_revision",
            *paths, "gates",
        }, "receipt")
        expected = {
            "schema": RECEIPT_SCHEMA, "goal_id": GOAL, "repository_id": REPOSITORY,
            "acceptance_run_id": a.acceptance_run_id, "source_revision": a.source_revision,
        }
        for field, value in expected.items():
            if receipt[field] != value:
                raise Refusal(f"receipt.{field} differs from the invocation")
        for name, (raw, sha) in paths.items():
            path = input_file(self.root, raw, sha, name)
            bound_path, bound_sha = ref(self.root, receipt[name], f"receipt.{name}")
            if (path, sha) != (bound_path, bound_sha):
                raise Refusal(f"receipt.{name} differs from the exact bound input")
            self.inputs[name] = path
        gates = exact(receipt["gates"], set(PRIOR_GATES) | {GATE}, "receipt.gates")
        g8 = exact(gates[GATE], {"checker", "checker_sha256", "evidence"}, "receipt.gates.G8")
        if g8["checker"] != CHECKER or g8["checker_sha256"] != a.checker_sha256:
            raise Refusal("receipt G8 descriptor differs from the executed checker")
        evidence_path, evidence_sha = ref(self.root, g8["evidence"], "receipt.gates.G8.evidence")
        if (evidence_path, evidence_sha) != (resolved(a.verify_evidence, "--verify-evidence"), a.evidence_sha256):
            raise Refusal("receipt G8 evidence differs from --verify-evidence")
        prior_evidence_paths: set[Path] = set()
        for gate in PRIOR_GATES:
            row = exact(gates[gate], {"checker", "checker_sha256", "evidence"}, gate)
            hex_digest(row["checker_sha256"], f"{gate}.checker_sha256")
            if not isinstance(row["checker"], str) or not row["checker"]:
                raise Refusal(f"{gate}.checker is missing")
            prior_path, _ = ref(self.root, row["evidence"], f"{gate}.evidence")
            if prior_path in {receipt_path, evidence_path} or prior_path in prior_evidence_paths:
                raise Refusal("G1-G7 evidence paths must be distinct from G8 and each other")
            prior_evidence_paths.add(prior_path)
        subject = json_object(Path(a.subject_graph))
        if subject.get("schema") != "trust.two-language.subject-index/v3":
            raise Refusal("subject graph is not the typed v3 subject index")
        if subject.get("acceptance_run_id") != a.acceptance_run_id or subject.get("source_revision") != a.source_revision:
            raise Refusal("subject graph run or revision differs")
        if not isinstance(subject.get("roots"), dict) or not subject["roots"]:
            raise Refusal("subject index has no canonical roots")
        self.receipt = receipt
        self.policy = json_object(Path(a.authority_policy))

    def require_acyclic_seal(self, seal_path: Path, signature_path: Path) -> None:
        assert self.receipt is not None
        forbidden = {
            resolved(self.args.receipt, "receipt"),
            resolved(self.args.verify_evidence, "--verify-evidence"),
            seal_path, signature_path,
        }
        for gate in PRIOR_GATES:
            evidence_path, _ = ref(self.root, self.receipt["gates"][gate]["evidence"],
                                   f"{gate}.evidence")
            bundle = json_object(evidence_path)
            artifacts = bundle.get("artifacts")
            if not isinstance(artifacts, dict):
                raise Refusal(f"{gate} evidence has no artifact index")
            for check_id, candidate in artifacts.items():
                if not isinstance(candidate, dict) or set(candidate) != {"path", "sha256"}:
                    raise Refusal(f"{gate}.{check_id} has no exact content reference")
                path, _ = ref(self.root, candidate, f"{gate}.{check_id}")
                if path in forbidden:
                    raise Refusal(f"{gate}.{check_id} makes the release seal cyclic")

    def require_common(self) -> None:
        if self.common_error is not None:
            raise Refusal(self.common_error)

    def authenticate_policy(self) -> None:
        self.require_common()
        a = self.args
        policy = self.policy
        assert policy is not None
        exact(policy, {
            "schema", "goal_id", "repository_id", "completion_schema",
            "authorized_source_revision", "authorized_acceptance_run_id",
            "owner_key_fingerprint", "authorized_inputs", "contracts",
            "authorized_checkers",
        }, "authority policy")
        if policy.get("schema") != POLICY_SCHEMA or policy.get("goal_id") != GOAL:
            raise Refusal("authority policy schema or goal differs")
        for field, expected in (
            ("repository_id", REPOSITORY),
            ("completion_schema", RECEIPT_SCHEMA),
            ("authorized_source_revision", a.source_revision),
            ("authorized_acceptance_run_id", a.acceptance_run_id),
        ):
            if policy.get(field) != expected:
                raise Refusal(f"authority policy {field} differs")
        _path, fingerprint, material = owner_key(self.root, a.trusted_owner_key)
        if policy.get("owner_key_fingerprint") != fingerprint:
            raise Refusal("authority policy fingerprint differs from external owner key")
        envelope = json_object(Path(a.policy_authorization))
        exact(envelope, {
            "schema", "algorithm", "namespace", "signer_fingerprint",
            "policy_sha256", "signature",
        }, "policy authorization")
        expected = {
            "schema": AUTH_SCHEMA, "algorithm": "ssh-ed25519", "namespace": POLICY_NAMESPACE,
            "signer_fingerprint": fingerprint, "policy_sha256": a.authority_policy_sha256,
        }
        for field, value in expected.items():
            if envelope[field] != value:
                raise Refusal(f"policy authorization {field} differs")
        verify_signature(self.root, envelope["signature"], Path(a.authority_policy).read_bytes(),
                         POLICY_NAMESPACE, material)
        authorized = exact(policy.get("authorized_inputs"), {
            "toolchain_manifest_sha256", "corpus_manifest_sha256", "subject_graph_sha256",
            "linked_module_sha256", "release_artifact_sha256",
        }, "signed policy authorized_inputs")
        for field in (
            "toolchain_manifest_sha256", "corpus_manifest_sha256", "subject_graph_sha256",
            "linked_module_sha256", "release_artifact_sha256",
        ):
            observed = a.toolchain_sha256 if field == "toolchain_manifest_sha256" else getattr(a, field)
            if authorized.get(field) != observed:
                raise Refusal(f"signed policy input {field} differs")
        if not isinstance(policy.get("contracts"), dict):
            raise Refusal("signed policy contracts must be an object")
        checker_rows = exact(policy.get("authorized_checkers"),
                             set(PRIOR_GATES) | {GATE}, "signed policy authorized_checkers")
        assert self.receipt is not None
        for gate, descriptor in self.receipt["gates"].items():
            row = exact(checker_rows[gate], {"id", "path", "sha256"},
                        f"signed policy authorized_checkers.{gate}")
            if row["id"] != descriptor["checker"] or row["sha256"] != descriptor["checker_sha256"]:
                raise Refusal(f"signed policy checker {gate} differs from the receipt")
            raw_path = row["path"]
            if not isinstance(raw_path, str) or not raw_path or Path(raw_path).is_absolute():
                raise Refusal(f"signed policy checker {gate} path is not relative")
        self.fingerprint, self.key_material = fingerprint, material


def seal(cx: Context, path: Path) -> None:
    cx.authenticate_policy()
    a = cx.args
    doc = json_object(path)
    exact(doc, {"schema", "prior_gates_root", "release_artifact_sha256", "signature"}, "seal")
    payload = {key: doc[key] for key in ("schema", "prior_gates_root", "release_artifact_sha256")}
    if payload != {
        "schema": SEAL_SCHEMA, "prior_gates_root": a.prior_gates_root,
        "release_artifact_sha256": a.release_artifact_sha256,
    }:
        raise Refusal("detached seal does not bind this pre-seal root and executable")
    assert cx.key_material is not None
    message = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    sig_path, _ = ref(cx.root, doc["signature"], "release seal signature")
    cx.require_acyclic_seal(path, sig_path)
    verify_signature(cx.root, doc["signature"], message, SEAL_NAMESPACE, cx.key_material)


def roster(cx: Context, cited: tuple[Path, str]) -> None:
    cx.authenticate_policy()
    policy = cx.policy
    assert policy is not None
    contracts = policy.get("contracts")
    if not isinstance(contracts, dict):
        raise Refusal("signed policy has no contracts")
    environment = exact(contracts.get("acceptance_environment"), {"id", "path", "sha256"},
                        "acceptance_environment contract reference")
    if environment["id"] != "trust.two-language.contract.acceptance-environment":
        raise Refusal("wrong acceptance_environment contract id")
    contract_path, contract_sha = ref(cx.root, {"path": environment["path"], "sha256": environment["sha256"]},
                                      "acceptance_environment")
    contract = json_object(contract_path)
    exact(contract, {"schema", "goal_id", "repository_id", "component_roster", "run_modes"},
          "acceptance environment contract")
    if contract.get("schema") != ENV_SCHEMA or contract.get("goal_id") != GOAL or contract.get("repository_id") != REPOSITORY:
        raise Refusal("signed acceptance environment contract header differs")
    modes = contract["run_modes"]
    if (not isinstance(modes, list) or len(modes) != len(RUN_MODES)
            or not all(isinstance(mode, str) for mode in modes) or set(modes) != RUN_MODES):
        raise Refusal("signed acceptance environment must enumerate the exact run modes")
    components = json_object(Path(cx.args.toolchain_manifest))
    if components.get("schema") != TOOLCHAIN_SCHEMA or components.get("goal_id") != GOAL:
        raise Refusal("toolchain manifest header differs")
    if components.get("acceptance_run_id") != cx.args.acceptance_run_id or components.get("source_revision") != cx.args.source_revision:
        raise Refusal("toolchain manifest run or source differs")
    roster_rows = contract.get("component_roster")
    observed = components.get("components")
    if not isinstance(roster_rows, list) or not isinstance(observed, list):
        raise Refusal("toolchain roster or components missing")
    signed: dict[str, dict[str, Any]] = {}
    for row in roster_rows:
        exact(row, {"role", "name", "version", "artifact_sha256"}, "signed roster row")
        role = row["role"]
        if not isinstance(role, str) or role in signed or role not in TOOLCHAIN_ROLES:
            raise Refusal("signed roster roles must be unique and known")
        if not isinstance(row["name"], str) or not row["name"] or not isinstance(row["version"], str) or not row["version"]:
            raise Refusal("signed roster names and versions must be non-empty strings")
        hex_digest(row["artifact_sha256"], f"signed {role} artifact")
        signed[role] = row
    actual: dict[str, dict[str, Any]] = {}
    for row in observed:
        exact(row, {"role", "name", "version", "artifact"}, "toolchain component")
        role = row["role"]
        if not isinstance(role, str) or role in actual or role not in TOOLCHAIN_ROLES:
            raise Refusal("toolchain component roles must be unique and known")
        if not isinstance(row["name"], str) or not row["name"] or not isinstance(row["version"], str) or not row["version"]:
            raise Refusal("toolchain names and versions must be non-empty strings")
        _, sha = ref(cx.root, row["artifact"], f"toolchain {role} artifact")
        actual[role] = {"role": role, "name": row["name"], "version": row["version"],
                        "artifact_sha256": sha}
    if set(signed) != TOOLCHAIN_ROLES or actual != signed:
        raise Refusal("actual toolchain roster differs from the signed complete roster")
    require_cited("authorized_toolchain_roster_exact", cited, (contract_path, contract_sha))


def external_verifier(cx: Context, cited: tuple[Path, str]) -> None:
    cx.require_common()
    pinned = external_path(cx.root, cx.args.external_verifier, "--external-verifier")
    expected = hex_digest(cx.args.external_verifier_sha256, "--external-verifier-sha256")
    if digest(pinned) != expected:
        raise Refusal("external verifier differs from externally supplied SHA-256 pin")
    candidate = cx.root / "scripts/two_language_completion_gate.py"
    if not candidate.is_file() or candidate.is_symlink() or digest(candidate) != expected:
        raise Refusal("candidate-tree top verifier differs from external pinned bytes")
    require_cited("externally_pinned_top_verifier", cited, (candidate, expected))


def unavailable(_cx: Context, _path: Path, reason: str) -> None:
    raise Refusal(reason)


REFUSALS = {
    "g1_through_g7_same_source_revision": "fresh G1-G7 checker verdicts are not supplied to G8; receipt descriptors cannot prove their source revision",
    "g1_through_g7_same_run_and_subject_graph": "no authenticated G1-G7 verdict/subject-root population is supplied; authored descriptors can be spliced",
    "pinned_reproducible_environment": "no independently replayed pinned environment observation exists",
    "cold_warm_cross_crate_release_reproducible": "no independently executed cold/warm/cross-crate/mixed/test/release comparison exists",
    "release_artifact_binds_all_evidence": "the executable has no independently verified proof/evidence package locator or replay API",
    "acceptance_run_matrix_exact": "signed run-mode names are not independently executed run observations",
}

STRUCTURAL_ONLY = {
    "detached_release_seal_binds_prior_root_and_artifact": (
        "detached seal signature verifies under the caller-supplied key, but no "
        "independently configured owner-key authorization anchor exists"
    ),
    "owner_authorized_policy_and_repository_identity": (
        "policy signature verifies under the caller-supplied key, but no "
        "independently configured owner-key authorization anchor exists"
    ),
    "authorized_toolchain_roster_exact": (
        "roster matches the contract signed by the caller-supplied key, but no "
        "independently configured owner-key authorization anchor exists"
    ),
    "externally_pinned_top_verifier": (
        "verifier bytes match the caller-supplied path and digest, but no "
        "independently configured owner verifier pin exists"
    ),
}
assert set(REFUSALS) | set(STRUCTURAL_ONLY) == set(REQUIRED)


def run(args: argparse.Namespace) -> tuple[dict[str, Any], list[str]]:
    cx = Context(args)
    errors: list[str] = []
    bundle: dict[str, Any] = {}
    try:
        path = input_file(cx.root, args.verify_evidence, args.evidence_sha256, "G8 evidence")
        bundle = json_object(path)
        exact(bundle, {"schema", "gate", "checker", "artifacts"}, "G8 evidence")
        if (bundle["schema"], bundle["gate"], bundle["checker"]) != (EVIDENCE_SCHEMA, GATE, CHECKER):
            raise Refusal("G8 evidence header differs")
        exact(bundle["artifacts"], set(REQUIRED), "G8 evidence artifacts")
    except (Refusal, OSError, ValueError, RuntimeError) as exc:
        errors.append(str(exc))
    bundle_malformed = bool(errors)
    artifacts = bundle.get("artifacts") if isinstance(bundle.get("artifacts"), dict) else {}
    checks: list[dict[str, Any]] = []
    for check_id in REQUIRED:
        artifact_refs: list[dict[str, str]] = []
        try:
            cx.require_common()
            path, cited_sha = ref(cx.root, artifacts.get(check_id), f"{check_id} artifact")
            artifact_refs = [artifacts[check_id]]
            if bundle_malformed:
                raise Refusal("G8 evidence bundle is malformed")
            if check_id in REFUSALS:
                unavailable(cx, path, REFUSALS[check_id])
            elif check_id == "detached_release_seal_binds_prior_root_and_artifact":
                seal(cx, path)
            elif check_id == "owner_authorized_policy_and_repository_identity":
                cx.authenticate_policy()
                require_cited(check_id, (path, cited_sha),
                              (cx.inputs["policy_authorization"], args.policy_authorization_sha256))
            elif check_id == "authorized_toolchain_roster_exact":
                roster(cx, (path, cited_sha))
            elif check_id == "externally_pinned_top_verifier":
                external_verifier(cx, (path, cited_sha))
            else:
                raise Refusal("unimplemented G8 conjunct")
            reason = STRUCTURAL_ONLY[check_id]
        except (Refusal, OSError, ValueError, RuntimeError) as exc:
            reason = str(exc)
        errors.append(f"{check_id}: {reason}")
        checks.append({"id": check_id, "passed": False, "artifacts": artifact_refs})
    passed = False
    verdict = {
        "schema": SCHEMA, "goal_id": GOAL, "gate": GATE, "checker": CHECKER,
        "repository_id": REPOSITORY, "acceptance_run_id": args.acceptance_run_id,
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
    return verdict, errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in (
        "verify-evidence", "root", "receipt", "toolchain-manifest", "corpus-manifest",
        "subject-graph", "linked-module", "release-artifact", "authority-policy",
        "policy-authorization", "acceptance-run-id", "source-revision", "checker-sha256",
        "evidence-sha256", "toolchain-sha256", "corpus-manifest-sha256",
        "subject-graph-sha256", "linked-module-sha256", "release-artifact-sha256",
        "authority-policy-sha256", "policy-authorization-sha256", "prior-gates-root",
    ):
        parser.add_argument(f"--{name}", required=True)
    parser.add_argument("--trusted-owner-key")
    parser.add_argument("--external-verifier")
    parser.add_argument("--external-verifier-sha256")
    args = parser.parse_args()
    verdict, errors = run(args)
    print(json.dumps(verdict))
    for error in errors:
        print(f"G8: {error}", file=sys.stderr)
    return 0 if verdict["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
