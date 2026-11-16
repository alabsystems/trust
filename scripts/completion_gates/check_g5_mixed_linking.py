#!/usr/bin/env python3
"""G5 — one linked two-language program: the schema-owned gate checker.

Named by ``scripts/two_language_completion_gate.py`` (``CHECKER_PATHS["G5"]``)
and executed by it under a fixed protocol: a read-only snapshot of this file,
``python -I``, ``PATH=/usr/bin:/bin``, ``cwd=--root``, and ONE JSON verdict on
stdout carrying the receipt-bound digests it was handed.  This file is
therefore self-contained (standard library only; no sibling imports).

WHAT THIS CHECKER IS, AND IS NOT.  It reads the artifact shapes for the eight
G5 conjuncts fixed by ``REQUIRED_CHECKS["G5"]``.  A content hash authenticates
the bytes read, not the truth of an authored report.  The Rust-to-Clean sidecar
is a narrow same-crate compiler diagnostic; none of the eight artifact readers
reconstructs its claim from the exact linked module and an independently
complete call/import inventory.  The other seven schemas have no bound producer
in this checker.  Their structural rules remain useful diagnostics, but every
conjunct refuses completion authority until its named source gap is closed.
No authored ``passed``, ``typed``, ``re-earned``, or ``conforming`` field can
turn G5 green.

EVIDENCE BUNDLE (``--verify-evidence``), schema ``trust.two-language.gate-evidence/v1``::

    {"schema": "trust.two-language.gate-evidence/v1", "gate": "G5",
     "checker": "trust.two-language.g5.mixed-linking/v2",
     "artifacts": {"<check id>": {"path": "<relative>", "sha256": "<64 hex>"}, ...}}

The bundle's own bytes must hash to ``--evidence-sha256``; they are read once
and parsed as hashed.  Every artifact path is root-relative, must not escape
``--root``, must exist, and must hash to the recorded digest.  No document may
nest JSON containers deeper than ``TRUST_MAX_JSON_DEPTH``.  The artifact shapes
accepted per conjunct are documented on the verifier functions below.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Callable

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
GATE = "G5"
CHECKER = "trust.two-language.g5.mixed-linking/v2"
REPOSITORY_ID = "https://github.com/alabsystems/trust"
HEX_DIGEST = re.compile(r"^[0-9a-f]{64}$")
# `ProofDigest`'s Display for a SHA-256 subject: the algorithm, a colon, and
# exactly 32 bytes as lowercase hex (first-party/trust-ir proof/evidence.rs).
GATE_SUBJECT_DIGEST = re.compile(r"^sha256:[0-9a-f]{64}$")

# Exactly REQUIRED_CHECKS["G5"] in scripts/two_language_completion_gate.py.
REQUIRED = (
    "rust_to_lean_typed_link",
    "lean_to_rust_typed_link",
    "cross_crate_digest_rechecked_link",
    "proof_call_firewall",
    "typed_bidirectional_call_graph",
    "cross_language_value_category_matrix",
    "shared_abi_and_memory_model",
    "cross_crate_import_assumption_closure",
)

# Artifact schemas fixed by this checker.  A conjunct passes only against a
# document carrying its exact schema id: renaming a schema is a contract change.
COVERAGE_CLEAN_ORIGIN_DISCLOSURE = "trust.clean-origin-disclosure.v1"
LEAN_TO_RUST_LINK_SCHEMA = "trust.two-language.lean-to-rust-link/v1"
CROSS_CRATE_LINK_SCHEMA = "trust.two-language.cross-crate-link/v1"
FIREWALL_SCHEMA = "trust.two-language.proof-call-firewall/v1"
CALL_GRAPH_SCHEMA = "trust.two-language.typed-call-graph/v1"
VALUE_MATRIX_SCHEMA = "trust.two-language.value-category-matrix/v1"
ABI_MODEL_SCHEMA = "trust.two-language.shared-abi-memory-model/v1"
ASSUMPTION_CLOSURE_SCHEMA = "trust.two-language.import-assumption-closure/v1"

VALUE_CATEGORIES = ("scalar", "aggregate", "reference", "error", "callback", "result")
DIRECTIONS = ("rust_to_lean", "lean_to_rust")


def sha256_of(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


class Refusal(Exception):
    """A conjunct refusal.  The message names the fix (v7/D3)."""




def load_json_object(path: Path) -> dict[str, Any]:
    try:
        _trust_text = path.read_text(encoding="utf-8")
        if _trust_json_nesting_depth(_trust_text) > TRUST_MAX_JSON_DEPTH:
            raise ValueError(f"JSON nests deeper than {TRUST_MAX_JSON_DEPTH}")
        value = json.loads(_trust_text)
    except (OSError, UnicodeError, ValueError, RecursionError) as exc:
        raise Refusal(f"artifact is not a JSON document: {exc}") from exc
    if not isinstance(value, dict):
        raise Refusal("artifact must be a JSON object")
    return value


def nonempty_str(value: Any) -> bool:
    return isinstance(value, str) and bool(value)


def require_schema(doc: dict[str, Any], schema: str) -> None:
    if doc.get("schema") != schema:
        raise Refusal(f"artifact schema must be {schema!r}, got {doc.get('schema')!r}")


def nonempty_list(doc: dict[str, Any], key: str) -> list[Any]:
    value = doc.get(key)
    if not isinstance(value, list) or not value:
        raise Refusal(f"`{key}` must be a non-empty list")
    return value


# ── artifact shape readers ─────────────────────────────────────────────────
#
# These rules diagnose malformed evidence.  Passing a shape rule is not a G5
# verdict; SOURCE_GAPS below still refuses unauthenticated source claims.


def verify_rust_to_lean_typed_link(path: Path) -> None:
    """Artifact: the compiler's ``*.trust-ir.coverage.json`` sidecar format
    (``clean_origin_join::coverage_section``).  Shape check: the crate
    RECORDED Clean-origin rows, at least one Rust->Clean call edge was
    re-pointed by IR-5, every linked row carries a ``refusals`` key whose value
    is an EMPTY list and a ``type_unchecked`` key whose value is an EMPTY list (absent, a non-list, or a
    non-empty list is refused: the seam links positions it could not type-decide
    and discloses them there), and every such edge targets an
    emitted row published at tier ``gate`` (carrier-faithful, bound to a
    ``sha256:<64 lowercase hex>`` subject digest), matched by exact
    ``def_index``/``func_id`` — identity, never name.  Every count and index is
    a JSON integer, never a boolean."""
    doc = load_json_object(path)
    section = doc.get("clean_origin")
    if not isinstance(section, dict):
        raise Refusal("coverage sidecar has no `clean_origin` section; compile under -Ztrust-verify=on with --emit=trust-ir")
    if section.get("recorded") is not True:
        raise Refusal("`clean_origin.recorded` is not true: the crate recorded no Clean-origin rows")
    emitted = section.get("emitted")
    linked = section.get("linked")
    if not isinstance(emitted, list):
        raise Refusal(f"`clean_origin.emitted` must be a list, got {type(emitted).__name__}")
    if not isinstance(linked, list) or not linked:
        raise Refusal("`clean_origin.linked` must be a non-empty list: no Rust->Clean edge was re-pointed (IR-5)")
    by_identity: dict[tuple[int, int], dict[str, Any]] = {}
    for row in emitted:
        if not isinstance(row, dict):
            raise Refusal("emitted rows must be objects")
        identity = (row.get("def_index"), row.get("func_id"))
        if any(type(value) is not int or value < 0 for value in identity):
            raise Refusal("emitted row identity must contain non-negative integer def_index and func_id")
        if identity in by_identity:
            raise Refusal(f"duplicate emitted row identity {identity}")
        by_identity[identity] = row
    for row in linked:
        if not isinstance(row, dict):
            raise Refusal("linked rows must be objects")
        # Both emitters in `clean_origin_join` write `refusals` as a JSON list of
        # strings.  Like `type_unchecked` below, an absent key or any other type is
        # not that list: `false`/`0`/`""`/`{}`/`null` must not read as "no refusals".
        if "refusals" not in row:
            raise Refusal(
                f"linked row {row.get('def_path')!r} carries no `refusals` key; the seam "
                f"records its refusals as a list, and an absent record is not zero refusals"
            )
        refusals = row["refusals"]
        if not isinstance(refusals, list):
            raise Refusal(
                f"linked row {row.get('def_path')!r} carries `refusals` of type "
                f"{type(refusals).__name__} ({refusals!r}); only an empty list is zero refusals"
            )
        if refusals:
            raise Refusal(f"linked row {row.get('def_path')!r} carries refusals: {refusals}")
        # G5's first conjunct is "linked by TYPE and identity, not only name or arity".
        # An empty `refusals` alone does not establish that: the seam links an edge it
        # could not DECIDE (a refinement, a `Ty::Error` hole, an unreconstructable SSA
        # value, two ids under one table-indexed constructor) and discloses the position
        # here instead of refusing it, because a refusal at that seam is a fatal
        # finalization error. So a typed link requires this key present AND an empty
        # list.  Both emitters in `clean_origin_join` write a JSON list of strings; any
        # other type is not that disclosure, so `false`/`0`/`""`/`{}` must not read as
        # "nothing undecided" by falsiness, nor a present `null` as a pre-guard row.
        if "type_unchecked" not in row:
            raise Refusal(
                f"linked row {row.get('def_path')!r} carries no `type_unchecked` key: it "
                f"predates the seam type guard, and an absent disclosure is not a typed link"
            )
        unchecked = row["type_unchecked"]
        if not isinstance(unchecked, list):
            raise Refusal(
                f"linked row {row.get('def_path')!r} carries `type_unchecked` of type "
                f"{type(unchecked).__name__} ({unchecked!r}); the seam discloses undecided "
                f"operand positions as a list, and only an empty list is a typed link"
            )
        if unchecked:
            raise Refusal(
                f"linked row {row.get('def_path')!r} left {len(unchecked)} operand position(s) "
                f"undecided at the seam: {unchecked}"
            )
        repointed = row.get("edges_repointed")
        if type(repointed) is not int or repointed < 1:
            raise Refusal(
                f"linked row {row.get('def_path')!r} re-pointed no edge: `edges_repointed` "
                f"must be a positive integer, got {repointed!r}"
            )
        target_identity = (row.get("source_def_index"), row.get("target_func_id"))
        if any(type(value) is not int or value < 0 for value in target_identity):
            raise Refusal("linked row identity must contain non-negative integer source_def_index and target_func_id")
        target = by_identity.get(target_identity)
        if target is None:
            raise Refusal(
                f"linked row {row.get('def_path')!r} targets (def_index={row.get('source_def_index')}, "
                f"func_id={row.get('target_func_id')}) which is not an emitted row — a link by name is not a typed link"
            )
        if target.get("tier") != "gate" or target.get("body_gate") != "carrier-faithful":
            raise Refusal(
                f"link target {target.get('clean_name')!r} is at tier {target.get('tier')!r}; G5 requires tier `gate` (carrier-faithful)"
            )
        digest = target.get("gate_subject_digest")
        if not isinstance(digest, str) or not GATE_SUBJECT_DIGEST.fullmatch(digest):
            raise Refusal(
                f"link target {target.get('clean_name')!r} has no digest-bound gate subject: "
                f"`gate_subject_digest` must be `sha256:` and 64 lowercase hex digits"
            )


def verify_lean_to_rust_typed_link(path: Path) -> None:
    """Artifact schema ``trust.two-language.lean-to-rust-link/v1``: produced by
    a (not yet existing) instrument recording Clean ``def`` bodies that CALL a
    Rust ``fn`` by type and identity.  Today a Clean def can only call a fixed
    ``PrimitiveCallee`` allow-list, so no real artifact exists and this conjunct
    is honestly red.  Shape check: ``links`` is non-empty and every link names a
    Rust callee by a non-negative integer ``rust_def_index`` and a non-empty
    ``rust_definition_identity``, from a named ``clean_name``, with a non-empty
    ``func_ty`` and ``verdict == "typed"``.  Those fields are not source authority."""
    doc = load_json_object(path)
    require_schema(doc, LEAN_TO_RUST_LINK_SCHEMA)
    for link in nonempty_list(doc, "links"):
        if not isinstance(link, dict):
            raise Refusal("links must be objects")
        for key in ("clean_name", "rust_def_index", "rust_definition_identity", "func_ty", "verdict"):
            if key not in link:
                raise Refusal(f"link lacks `{key}`")
        if link.get("verdict") != "typed":
            raise Refusal(f"link {link.get('clean_name')!r} verdict is {link.get('verdict')!r}, not \"typed\"")
        index = link.get("rust_def_index")
        if type(index) is not int or index < 0:
            raise Refusal("rust_def_index must be a non-negative integer identity, not a name or a boolean")
        for key in ("clean_name", "rust_definition_identity", "func_ty"):
            if not nonempty_str(link[key]):
                raise Refusal(f"link `{key}` must be a non-empty string, got {link[key]!r}")


def verify_cross_crate_digest_rechecked_link(path: Path) -> None:
    """Artifact schema ``trust.two-language.cross-crate-link/v1``: an importer
    crate's record that a Clean-origin Trust-IR row from ANOTHER crate was
    linked through a versioned wire format and its verdict RE-EARNED under the
    importer's own kernel.  Shape check: every link has ``lane == "trust-ir"``,
    a 64-hex ``exporter_digest``, ``importer_recheck == "re-earned"``, and
    names two different crates as non-empty ``importer_crate`` and
    ``exporter_crate`` strings.  This report does not replay the importer or hash the exporter bytes."""
    doc = load_json_object(path)
    require_schema(doc, CROSS_CRATE_LINK_SCHEMA)
    for link in nonempty_list(doc, "links"):
        if not isinstance(link, dict):
            raise Refusal("links must be objects")
        if link.get("lane") != "trust-ir":
            raise Refusal(f"link lane {link.get('lane')!r} is not \"trust-ir\" (G7 makes Trust-IR the authority)")
        if not isinstance(link.get("exporter_digest"), str) or not HEX_DIGEST.fullmatch(link["exporter_digest"]):
            raise Refusal("exporter_digest must be a lowercase 64-hex digest")
        if link.get("importer_recheck") != "re-earned":
            raise Refusal(f"importer_recheck is {link.get('importer_recheck')!r}, not \"re-earned\"")
        for key in ("importer_crate", "exporter_crate"):
            if not nonempty_str(link.get(key)):
                raise Refusal(f"link `{key}` must name a crate as a non-empty string, got {link.get(key)!r}")
        if link["importer_crate"] == link["exporter_crate"]:
            raise Refusal("a same-crate link is not a cross-crate link")


def verify_proof_call_firewall(path: Path) -> None:
    """Artifact schema ``trust.two-language.proof-call-firewall/v1``: a report
    that every PROOF-visibility item was checked against every CALL site
    transitively and none is reachable.  Shape check: ``checked_items >= 1``,
    ``transitive == true`` and ``violations == []``.  No graph is traversed here."""
    doc = load_json_object(path)
    require_schema(doc, FIREWALL_SCHEMA)
    checked = doc.get("checked_items")
    if type(checked) is not int or checked < 1:
        raise Refusal("checked_items must be a positive integer")
    if doc.get("transitive") is not True:
        raise Refusal("firewall report must be transitive")
    if doc.get("violations") != []:
        raise Refusal(f"firewall violations present: {doc.get('violations')}")


def verify_typed_bidirectional_call_graph(path: Path) -> None:
    """Artifact schema ``trust.two-language.typed-call-graph/v1``: a call graph
    whose edges carry ``func_ty`` and identity in BOTH directions.  Shape
    check: there is at least one edge per direction and every edge names its
    ``caller_identity``, ``callee_identity`` and ``func_ty`` as non-empty strings."""
    doc = load_json_object(path)
    require_schema(doc, CALL_GRAPH_SCHEMA)
    edges = nonempty_list(doc, "edges")
    seen = set()
    for edge in edges:
        if not isinstance(edge, dict):
            raise Refusal("edges must be objects")
        direction = edge.get("direction")
        if direction not in DIRECTIONS:
            raise Refusal(f"edge direction {direction!r} is not one of {DIRECTIONS}")
        for key in ("caller_identity", "callee_identity", "func_ty"):
            if key not in edge:
                raise Refusal(f"edge lacks `{key}`")
            if not nonempty_str(edge[key]):
                raise Refusal(f"edge `{key}` must be a non-empty string, got {edge[key]!r}")
        seen.add(direction)
    missing = [d for d in DIRECTIONS if d not in seen]
    if missing:
        raise Refusal(f"call graph has no edge in direction(s) {missing}")


def verify_cross_language_value_category_matrix(path: Path) -> None:
    """Artifact schema ``trust.two-language.value-category-matrix/v1``: every
    value category × direction cell carries a non-empty string ``evidence``
    reference and ``status == "crosses"``.  Shape check: the matrix is populated."""
    doc = load_json_object(path)
    require_schema(doc, VALUE_MATRIX_SCHEMA)
    cells = doc.get("cells")
    if not isinstance(cells, dict):
        raise Refusal("`cells` must be an object keyed `<category>/<direction>`")
    for category in VALUE_CATEGORIES:
        for direction in DIRECTIONS:
            cell = cells.get(f"{category}/{direction}")
            if not isinstance(cell, dict):
                raise Refusal(f"matrix cell {category}/{direction} is absent")
            if cell.get("status") != "crosses" or not cell.get("evidence"):
                raise Refusal(f"matrix cell {category}/{direction} does not cross with evidence")
            if not nonempty_str(cell["evidence"]):
                raise Refusal(
                    f"matrix cell {category}/{direction} evidence must be a non-empty string "
                    f"reference, got {cell['evidence']!r}"
                )


def verify_shared_abi_and_memory_model(path: Path) -> None:
    """Artifact schema ``trust.two-language.shared-abi-memory-model/v1``: a
    conformance report binding both producers to ONE ABI + memory model
    definition.  Shape check: ``abi_id`` and ``memory_model_id`` are named, both
    producers are listed as conforming, and ``divergences == []``.  This does
    not check either producer's layouts or memory operations."""
    doc = load_json_object(path)
    require_schema(doc, ABI_MODEL_SCHEMA)
    for key in ("abi_id", "memory_model_id"):
        if not isinstance(doc.get(key), str) or not doc[key]:
            raise Refusal(f"`{key}` must name the shared definition")
    producers = doc.get("conforming_producers")
    if (not isinstance(producers, list)
            or not all(isinstance(producer, str) for producer in producers)
            or {"Trust", "Clean"} - set(producers)):
        raise Refusal("both producers `Trust` and `Clean` must be listed as conforming")
    if doc.get("divergences") != []:
        raise Refusal(f"ABI/memory-model divergences present: {doc.get('divergences')}")


def verify_cross_crate_import_assumption_closure(path: Path) -> None:
    """Artifact schema ``trust.two-language.import-assumption-closure/v1``: the
    importer's assumption ledger, every entry discharged.  Shape check:
    ``assumptions`` is non-empty and each has ``status == "discharged"`` with a
    digest-bound ``discharged_by``.  This does not enumerate actual imports."""
    doc = load_json_object(path)
    require_schema(doc, ASSUMPTION_CLOSURE_SCHEMA)
    for entry in nonempty_list(doc, "assumptions"):
        if not isinstance(entry, dict):
            raise Refusal("assumptions must be objects")
        if entry.get("status") != "discharged":
            raise Refusal(f"assumption {entry.get('id')!r} is {entry.get('status')!r}, not discharged")
        by = entry.get("discharged_by")
        if not isinstance(by, dict) or not HEX_DIGEST.fullmatch(str(by.get("sha256", ""))):
            raise Refusal(f"assumption {entry.get('id')!r} is not discharged by a digest-bound artifact")


VERIFIERS: dict[str, Callable[[Path], None]] = {
    "rust_to_lean_typed_link": verify_rust_to_lean_typed_link,
    "lean_to_rust_typed_link": verify_lean_to_rust_typed_link,
    "cross_crate_digest_rechecked_link": verify_cross_crate_digest_rechecked_link,
    "proof_call_firewall": verify_proof_call_firewall,
    "typed_bidirectional_call_graph": verify_typed_bidirectional_call_graph,
    "cross_language_value_category_matrix": verify_cross_language_value_category_matrix,
    "shared_abi_and_memory_model": verify_shared_abi_and_memory_model,
    "cross_crate_import_assumption_closure": verify_cross_crate_import_assumption_closure,
}
assert tuple(VERIFIERS) == REQUIRED

# The acceptance runner binds these paths and digests, but supplies no trusted
# producer attestation or independently reconstructed G5 facts.  In particular,
# the checker never parses --linked-module or --subject-graph.  Keep every row
# red until its source witness is checked against those exact inputs.  Removing
# one entry is a checker-contract change requiring an actual verifier and tests.
SOURCE_GAPS = {
    "rust_to_lean_typed_link": (
        "same-crate coverage sidecar is not bound to the exact linked module "
        "or a complete Rust-to-Lean call-edge census"
    ),
    "lean_to_rust_typed_link": (
        "no compiler-emitted Lean-to-Rust callee identity and signature witness"
    ),
    "cross_crate_digest_rechecked_link": (
        "no importer replay over versioned exporter bytes bound to both crate identities"
    ),
    "proof_call_firewall": (
        "no transitive PROOF/CALL reachability check over the exact linked graph"
    ),
    "typed_bidirectional_call_graph": (
        "no independently reconstructed, complete typed call graph in both directions"
    ),
    "cross_language_value_category_matrix": (
        "no producer-backed executable witness for every value category and direction"
    ),
    "shared_abi_and_memory_model": (
        "no independently checked shared ABI and memory-model definition or conformance"
    ),
    "cross_crate_import_assumption_closure": (
        "no complete importer assumption inventory or replay of its discharges"
    ),
}
assert set(SOURCE_GAPS) == set(REQUIRED)


# ── driver ──────────────────────────────────────────────────────────────────


def resolve_ref(root: Path, ref: Any) -> tuple[Path | None, str | None]:
    """Resolve one ``{"path","sha256"}`` reference fail-closed.  Returns the
    path and, on refusal, the reason."""
    if not isinstance(ref, dict) or set(ref) != {"path", "sha256"}:
        return None, "artifact reference must be exactly {path, sha256}"
    raw, digest = ref.get("path"), ref.get("sha256")
    if not isinstance(raw, str) or not raw or "\0" in raw or Path(raw).is_absolute():
        return None, "artifact path must be a non-empty relative path"
    try:
        candidate = (root / raw).resolve()
    except (OSError, ValueError, RuntimeError) as exc:
        return None, f"artifact path cannot be resolved: {exc}"
    try:
        candidate.relative_to(root)
    except ValueError:
        return None, "artifact path escapes --root"
    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
        return candidate, "artifact sha256 must be a lowercase 64-hex digest"
    # Python 3.9's `Path.is_file` swallows only ENOENT/ENOTDIR/EBADF/ELOOP; any
    # other stat error (ENAMETOOLONG for a >255-byte component) must refuse the
    # row, not escape as a traceback that leaves stdout without a verdict.
    try:
        is_file = candidate.is_file()
    except OSError as exc:
        return candidate, f"artifact path cannot be inspected: {exc}"
    if not is_file:
        return candidate, f"artifact file does not exist: {raw}"
    try:
        actual = sha256_of(candidate)
    except OSError as exc:
        return candidate, f"artifact cannot be hashed: {exc}"
    if actual != digest:
        return candidate, f"artifact hash mismatch: recorded {digest}, actual {actual}"
    return candidate, None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
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
    args = ap.parse_args()

    root = Path(args.root).resolve()
    diagnostics: list[str] = []
    passed = True
    # G1-G7 are pre-seal facts: the receipt and the prior-gates root belong to
    # G8 only.  Their presence here is a protocol violation, refused.
    if args.receipt is not None or args.prior_gates_root is not None:
        passed = False
        diagnostics.append("G5 must not receive --receipt or --prior-gates-root (G8-only protocol inputs)")

    bundle: dict[str, Any] = {}
    try:
        # Read the bundle ONCE and parse exactly the bytes that were hashed: the
        # verdict echoes --evidence-sha256, so it must be the digest of what was read.
        bundle_bytes = Path(args.verify_evidence).read_bytes()
        if hashlib.sha256(bundle_bytes).hexdigest() != args.evidence_sha256:
            diagnostics.append(
                "evidence bundle digest differs from --evidence-sha256; no artifact is "
                "read from an unbound bundle"
            )
            passed = False
        else:
            bundle_text = bundle_bytes.decode("utf-8")
            if _trust_json_nesting_depth(bundle_text) > TRUST_MAX_JSON_DEPTH:
                raise Refusal(f"evidence bundle nests JSON deeper than {TRUST_MAX_JSON_DEPTH}")
            loaded = json.loads(bundle_text)
            if isinstance(loaded, dict):
                bundle = loaded
            else:
                diagnostics.append("evidence bundle must be a JSON object")
                passed = False
    except (OSError, UnicodeError, ValueError, RecursionError) as exc:
        diagnostics.append(f"evidence bundle unreadable: {exc}")
        passed = False
    except Refusal as exc:
        diagnostics.append(f"evidence bundle refused: {exc}")
        passed = False
    if bundle and (
        set(bundle) != {"schema", "gate", "checker", "artifacts"}
        or bundle.get("schema") != EVIDENCE_SCHEMA
        or bundle.get("gate") != GATE
        or bundle.get("checker") != CHECKER
        or not isinstance(bundle.get("artifacts"), dict)
    ):
        diagnostics.append(f"evidence bundle header must be exactly {{schema={EVIDENCE_SCHEMA!r}, gate={GATE!r}, checker={CHECKER!r}, artifacts}}")
        passed = False
    artifacts = bundle.get("artifacts") if isinstance(bundle.get("artifacts"), dict) else {}
    unknown = sorted(set(artifacts) - set(REQUIRED))
    if unknown:
        diagnostics.append(f"evidence binds unknown check ids: {unknown}")
        passed = False

    bound: dict[Path, str] = {}
    checks: list[dict[str, Any]] = []
    for check_id in REQUIRED:
        ref = artifacts.get(check_id)
        row_ok = False
        row_artifacts: list[Any] = []
        if ref is None:
            diagnostics.append(f"{check_id}: no artifact bound")
        else:
            path, refusal = resolve_ref(root, ref)
            if refusal is None and path is not None:
                if bound.get(path, ref["sha256"]) != ref["sha256"]:
                    refusal = "the same path is bound to conflicting digests"
                bound[path] = ref["sha256"]
            if refusal is not None:
                diagnostics.append(f"{check_id}: {refusal}")
            else:
                row_artifacts = [ref]
                try:
                    VERIFIERS[check_id](path)  # type: ignore[arg-type]
                    gap = SOURCE_GAPS.get(check_id)
                    if gap is not None:
                        raise Refusal(f"producer authority missing: {gap}")
                    row_ok = True
                except Refusal as exc:
                    diagnostics.append(f"{check_id}: {exc}")
        passed = passed and row_ok
        checks.append({"id": check_id, "passed": row_ok, "artifacts": row_artifacts})

    verdict = {
        "schema": SCHEMA,
        "goal_id": GOAL,
        "gate": GATE,
        "checker": CHECKER,
        "repository_id": REPOSITORY_ID,
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
    }
    print(json.dumps(verdict))
    for line in diagnostics:
        print(f"{GATE}: {line}", file=sys.stderr)
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
