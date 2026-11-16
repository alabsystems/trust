#!/usr/bin/env python3
"""G7 — Trust-IR is the executable authority: the schema-owned gate checker.

Named by ``scripts/two_language_completion_gate.py`` (``CHECKER_PATHS["G7"]``)
and executed under its fixed protocol (read-only snapshot, ``python -I``,
``PATH=/usr/bin:/bin``, ``cwd=--root``, one JSON verdict on stdout carrying
the receipt-bound digests).  Self-contained: standard library only.

This checker diagnoses the nine G7 conjuncts fixed by
``REQUIRED_CHECKS["G7"]``.  It runs no compiler or independent proof checker.
The JSON artifacts below are authored input, even when their bytes are hashed
by the receipt runner.  Their structural checks cannot establish that codegen
ran, that an object or executable has the claimed semantics, or that a
translation proof was checked.  All nine conjuncts therefore fail closed until
producer-bound evidence and independent replay are implemented.

EVIDENCE BUNDLE (``--verify-evidence``), schema ``trust.two-language.gate-evidence/v1``::

    {"schema": "trust.two-language.gate-evidence/v1", "gate": "G7",
     "checker": "trust.two-language.g7.codegen-authority/v3",
     "artifacts": {"<check id>": {"path": "<relative>", "sha256": "<64 hex>"}, ...}}

The bundle's own bytes must hash to ``--evidence-sha256`` and the
``--linked-module`` bytes to ``--linked-module-sha256``; the bundle is read once
and parsed as hashed.  No document may nest JSON containers deeper than
``TRUST_MAX_JSON_DEPTH``.
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
GATE = "G7"
CHECKER = "trust.two-language.g7.codegen-authority/v3"
REPOSITORY_ID = "https://github.com/alabsystems/trust"
HEX_DIGEST = re.compile(r"^[0-9a-f]{64}$")

# Exactly REQUIRED_CHECKS["G7"] in scripts/two_language_completion_gate.py.
REQUIRED = (
    "exact_linked_module_is_codegen_input",
    "full_admitted_codegen_surface",
    "zero_unproved_fallbacks",
    "machine_equivalence_evidence",
    "objects_biject_admitted_modules",
    "authorized_codegen_matrix_complete",
    "typed_module_object_executable_lineage",
    "linked_executable_composition_validated",
    "runtime_startup_syslib_closure_bound",
)

CODEGEN_RECEIPT_SCHEMA = "trust.two-language.codegen-receipt/v1"
MACHINE_EQUIVALENCE_SCHEMA = "trust.two-language.machine-equivalence/v1"
OBJECT_BIJECTION_SCHEMA = "trust.two-language.object-module-bijection/v1"
MATRIX_OBSERVATION_SCHEMA = "trust.two-language.codegen-matrix-observation/v1"
EXECUTABLE_LINEAGE_SCHEMA = "trust.two-language.executable-lineage/v1"
EXECUTABLE_COMPOSITION_SCHEMA = "trust.two-language.executable-composition/v1"
RUNTIME_CLOSURE_SCHEMA = "trust.two-language.runtime-closure/v1"
CODEGEN_CONTRACT_SCHEMA = "trust.two-language.codegen-surface-contract/v2"
CODEGEN_CONTRACT_ID = "trust.two-language.contract.codegen-surface"

# Mirrors CODEGEN_CELL_FIELDS in the runner: an observed row binds every one.
CODEGEN_CELL_FIELDS = (
    "target_id", "abi_id", "crate_type", "runtime_id", "startup_id",
    "linker_id", "unwind_mode", "debug_mode", "opt_level", "profile_id",
)
EQUIVALENCE_METHODS = ("proven-output", "translation-validation")

AUTHORITY_GAPS = {
    "exact_linked_module_is_codegen_input":
        "no authenticated default-build codegen trace binds the linked Trust-IR module to the emitted bytes",
    "full_admitted_codegen_surface":
        "no producer-bound census proves every admitted function and codegen configuration was emitted",
    "zero_unproved_fallbacks":
        "no authenticated compiler trace proves the output gate and zero unproved fallbacks for the whole build",
    "machine_equivalence_evidence":
        "no independent replay checks a translation proof against the exact module and object bytes",
    "objects_biject_admitted_modules":
        "no independently derived admitted-module/object inventory establishes this bijection",
    "authorized_codegen_matrix_complete":
        "signed cells and authored observations do not prove each cell built its exact objects",
    "typed_module_object_executable_lineage":
        "no independently checked typed-module/object/executable lineage binds the actual bytes",
    "linked_executable_composition_validated":
        "no independently checked linker composition proof binds the release executable and its objects",
    "runtime_startup_syslib_closure_bound":
        "no independently checked runtime, startup, and system-library closure binds the executable",
}
assert tuple(AUTHORITY_GAPS) == REQUIRED


def sha256_of(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1 << 20), b""):
                digest.update(chunk)
    except OSError as exc:
        raise Refusal(f"cannot hash {path}: {exc}") from exc
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


def require_schema(doc: dict[str, Any], schema: str) -> None:
    if doc.get("schema") != schema:
        raise Refusal(f"artifact schema must be {schema!r}, got {doc.get('schema')!r}")


def nonempty_list(doc: dict[str, Any], key: str) -> list[Any]:
    value = doc.get(key)
    if not isinstance(value, list) or not value:
        raise Refusal(f"`{key}` must be a non-empty list")
    return value


def unique_names(doc: dict[str, Any], key: str, *, allow_empty: bool = False) -> list[str]:
    values = doc.get(key)
    if not isinstance(values, list):
        raise Refusal(f"`{key}` must be a list")
    if not allow_empty and not values:
        raise Refusal(f"`{key}` must be a non-empty list")
    if any(not isinstance(value, str) or not value for value in values):
        raise Refusal(f"`{key}` must contain non-empty names")
    if len(values) != len(set(values)):
        raise Refusal(f"`{key}` contains duplicate names")
    return values


def require_hex(value: Any, what: str) -> str:
    if not isinstance(value, str) or not HEX_DIGEST.fullmatch(value):
        raise Refusal(f"{what} must be a lowercase 64-hex digest")
    return value


def load_codegen_receipt(path: Path) -> dict[str, Any]:
    """Schema ``trust.two-language.codegen-receipt/v1``: what a codegen run
    that consumed the LINKED Trust-IR module would write — the frontend it
    used, the exact module digest it consumed, the admitted function census,
    the objects it emitted, and its refusal/fallback/gate accounting."""
    doc = load_json_object(path)
    require_schema(doc, CODEGEN_RECEIPT_SCHEMA)
    for key in ("frontend", "linked_module_sha256", "admitted_functions", "objects", "refusals", "fallbacks", "output_gate"):
        if key not in doc:
            raise Refusal(f"codegen receipt lacks `{key}`")
    return doc


def receipt_objects(receipt: dict[str, Any]) -> list[dict[str, Any]]:
    """The receipt's ``objects``, each a dict naming a unique non-empty
    ``module_id``, a 64-hex ``sha256`` and a ``functions`` list of unique
    non-empty names; no function may be emitted by more than one object."""
    objects = nonempty_list(receipt, "objects")
    modules: set[str] = set()
    owner: dict[str, str] = {}
    for obj in objects:
        if not isinstance(obj, dict) or not isinstance(obj.get("functions"), list):
            raise Refusal("every object must list its functions")
        require_hex(obj.get("sha256"), "object sha256")
        module_id = obj.get("module_id")
        if not isinstance(module_id, str) or not module_id:
            raise Refusal("every object must name its module_id as a non-empty string")
        if module_id in modules:
            raise Refusal(f"module {module_id!r} is emitted as more than one object")
        modules.add(module_id)
        for name in unique_names(obj, "functions", allow_empty=True):
            if name in owner:
                raise Refusal(
                    f"function {name!r} is emitted by both module {owner[name]!r} and "
                    f"module {module_id!r}; each admitted function has exactly one object"
                )
            owner[name] = module_id
    return objects


# ── conjunct verifiers ──────────────────────────────────────────────────────


class Context:
    """Receipt-bound inputs used for structural diagnostics only."""

    def __init__(
        self,
        root: Path,
        linked_module_sha256: str,
        policy_path: Path,
        policy_sha256: str,
        artifacts: dict[str, Any],
        linked_module_refusal: str | None = None,
    ) -> None:
        self.root = root
        self.linked_module_sha256 = linked_module_sha256
        self.linked_module_refusal = linked_module_refusal
        self.policy_path = policy_path
        self.policy_sha256 = policy_sha256
        self.artifacts = artifacts

    def linked_module(self) -> str:
        """The linked-module digest, only once the checker hashed those bytes."""
        if self.linked_module_refusal is not None:
            raise Refusal(self.linked_module_refusal)
        return self.linked_module_sha256


def canonical_codegen_receipt(cx: Context) -> tuple[Path, dict[str, Any]]:
    ref = cx.artifacts.get("exact_linked_module_is_codegen_input")
    path, refusal = resolve_ref(cx.root, ref)
    if refusal is not None or path is None:
        raise Refusal(f"canonical codegen receipt is not bound: {refusal}")
    return path, load_codegen_receipt(path)


def require_same_codegen_receipt(path: Path, cx: Context) -> dict[str, Any]:
    canonical_path, doc = canonical_codegen_receipt(cx)
    if sha256_of(path) != sha256_of(canonical_path):
        raise Refusal("the three codegen-receipt checks must bind identical receipt bytes")
    return doc


def verify_exact_linked_module_is_codegen_input(path: Path, cx: Context) -> None:
    """Diagnose receipt claims about the frontend and linked-module digest."""
    doc = load_codegen_receipt(path)
    if doc.get("frontend") != "trust-ir":
        raise Refusal(f"codegen frontend is {doc.get('frontend')!r}; G7 requires the trust-ir frontend")
    consumed = require_hex(doc.get("linked_module_sha256"), "linked_module_sha256")
    linked = cx.linked_module()
    if consumed != linked:
        raise Refusal(
            f"receipt consumed module {consumed[:12]}… but the acceptance run's linked module is "
            f"{linked[:12]}…; codegen must consume the exact linked module"
        )


def verify_full_admitted_codegen_surface(path: Path, cx: Context) -> None:
    """Diagnose the authored function census and recorded refusals."""
    doc = require_same_codegen_receipt(path, cx)
    admitted = unique_names(doc, "admitted_functions")
    emitted: set[str] = set()
    for obj in receipt_objects(doc):
        emitted.update(obj["functions"])
    missing = sorted(set(admitted) - emitted)
    if missing:
        raise Refusal(f"admitted functions without an emitted object: {missing[:8]}")
    unexpected = sorted(emitted - set(admitted))
    if unexpected:
        raise Refusal(f"emitted functions absent from the authored admission list: {unexpected[:8]}")
    if doc.get("refusals") != []:
        raise Refusal(f"codegen refusals recorded: {doc.get('refusals')}")


def verify_zero_unproved_fallbacks(path: Path, cx: Context) -> None:
    """Diagnose fallback and output-gate claims in the same codegen receipt.
    ``fallbacks`` must be the JSON integer 0: ``false`` and ``0.0`` compare
    equal to 0 in Python but are not a fallback count."""
    doc = require_same_codegen_receipt(path, cx)
    fallbacks = doc.get("fallbacks")
    if type(fallbacks) is not int or fallbacks != 0:
        raise Refusal(f"unproved fallbacks recorded: {doc.get('fallbacks')}")
    if doc.get("output_gate") != "on":
        raise Refusal(f"proven-output gate was {doc.get('output_gate')!r}, not \"on\"")


def verify_machine_equivalence_evidence(path: Path, cx: Context) -> None:
    """Diagnose authored translation rows against the receipt's function names.
    Each row's ``object_sha256`` must be the digest of the receipt object that
    emitted that function."""
    doc = load_json_object(path)
    require_schema(doc, MACHINE_EQUIVALENCE_SCHEMA)
    _receipt_path, receipt = canonical_codegen_receipt(cx)
    expected = set(unique_names(receipt, "admitted_functions"))
    object_of = {name: obj["sha256"] for obj in receipt_objects(receipt) for name in obj["functions"]}
    observed: set[str] = set()
    for row in nonempty_list(doc, "functions"):
        if not isinstance(row, dict):
            raise Refusal("function rows must be objects")
        name = row.get("name")
        if not isinstance(name, str) or not name:
            raise Refusal("translation rows must name a function")
        if name in observed:
            raise Refusal(f"duplicate translation row for function {name!r}")
        observed.add(name)
        if row.get("verdict") != "preserved":
            raise Refusal(f"function {row.get('name')!r} verdict is {row.get('verdict')!r}, not preserved")
        if row.get("method") not in EQUIVALENCE_METHODS:
            raise Refusal(f"function {row.get('name')!r} method {row.get('method')!r} is not one of {EQUIVALENCE_METHODS}")
        claimed = require_hex(row.get("object_sha256"), f"function {row.get('name')!r} object_sha256")
        if name in object_of and claimed != object_of[name]:
            raise Refusal(
                f"function {name!r} translation row names object {claimed[:12]}…, but the "
                f"codegen receipt emits it in object {object_of[name][:12]}…"
            )
    missing = sorted(expected - observed)
    if missing:
        raise Refusal(f"missing translation rows for admitted functions: {missing[:8]}")
    unexpected = sorted(observed - expected)
    if unexpected:
        raise Refusal(f"translation rows name unadmitted functions: {unexpected[:8]}")


def verify_objects_biject_admitted_modules(path: Path, cx: Context) -> None:
    """Diagnose uniqueness of authored module/object pairs, and that they are
    exactly the canonical codegen receipt's (module_id, object sha256) pairs;
    this is not their authority."""
    doc = load_json_object(path)
    require_schema(doc, OBJECT_BIJECTION_SCHEMA)
    pairs = nonempty_list(doc, "pairs")
    modules = [p.get("module_id") if isinstance(p, dict) else None for p in pairs]
    objects = [p.get("object_sha256") if isinstance(p, dict) else None for p in pairs]
    if any(not isinstance(m, str) or not m for m in modules):
        raise Refusal("every pair must name a module_id")
    for digest in objects:
        require_hex(digest, "pair object_sha256")
    if len(set(modules)) != len(modules) or len(set(objects)) != len(objects):
        raise Refusal("module ids and object digests must each be unique (a bijection)")
    _receipt_path, receipt = canonical_codegen_receipt(cx)
    emitted = {(obj["module_id"], obj["sha256"]) for obj in receipt_objects(receipt)}
    claimed = set(zip(modules, objects))
    if claimed != emitted:
        raise Refusal(
            f"bijection pairs are not the codegen receipt's objects: "
            f"unemitted {sorted(claimed - emitted)[:4]}, unpaired {sorted(emitted - claimed)[:4]}"
        )


def load_codegen_contract(cx: Context) -> dict[str, Any]:
    """Recheck the runner's signed-policy reference for diagnostic consistency.

    The runner verifies the external owner signature. This checker binds the
    same policy bytes and resolves its required named contract reference; it
    does not infer proof authority from that signature or the matrix content.
    """
    require_hex(cx.policy_sha256, "authority policy sha256")
    if sha256_of(cx.policy_path) != cx.policy_sha256:
        raise Refusal("authority policy digest differs from --authority-policy-sha256")
    policy = load_json_object(cx.policy_path)
    contracts = policy.get("contracts")
    if not isinstance(contracts, dict) or "codegen_surface" not in contracts:
        raise Refusal("signed authority policy has no contracts.codegen_surface reference")
    ref = contracts["codegen_surface"]
    if not isinstance(ref, dict) or set(ref) != {"id", "path", "sha256"}:
        raise Refusal("codegen_surface contract reference must be exactly {id, path, sha256}")
    if ref["id"] != CODEGEN_CONTRACT_ID:
        raise Refusal(f"codegen_surface contract id must be {CODEGEN_CONTRACT_ID!r}")
    candidate, refusal = resolve_ref(cx.root, {"path": ref["path"], "sha256": ref["sha256"]})
    if refusal is not None or candidate is None:
        raise Refusal(f"codegen_surface contract reference is not bound: {refusal}")
    contract = load_json_object(candidate)
    require_schema(contract, CODEGEN_CONTRACT_SCHEMA)
    return contract


def verify_authorized_codegen_matrix_complete(path: Path, cx: Context) -> None:
    """Diagnose authored observations against enumerated signed matrix cells."""
    doc = load_json_object(path)
    require_schema(doc, MATRIX_OBSERVATION_SCHEMA)
    contract = load_codegen_contract(cx)
    cells: dict[str, dict[str, Any]] = {}
    for cell in nonempty_list(contract, "matrix_cells"):
        if not isinstance(cell, dict) or not isinstance(cell.get("id"), str) or not cell["id"]:
            raise Refusal("contract matrix cells must be objects with a non-empty id")
        if cell["id"] in cells:
            raise Refusal(f"duplicate signed matrix cell {cell['id']!r}")
        for field in CODEGEN_CELL_FIELDS:
            if not isinstance(cell.get(field), str) or not cell[field]:
                raise Refusal(f"signed matrix cell {cell['id']!r} must name `{field}` as a non-empty string")
        cells[cell["id"]] = cell
    observed: dict[str, dict[str, Any]] = {}
    for row in nonempty_list(doc, "rows"):
        if not isinstance(row, dict):
            raise Refusal("observed rows must be objects")
        cell_id = row.get("codegen_cell_id")
        cell = cells.get(cell_id) if isinstance(cell_id, str) else None
        if cell is None:
            raise Refusal(f"observed row names cell {cell_id!r}, which the owner-signed matrix does not authorize")
        if cell_id in observed:
            raise Refusal(f"duplicate matrix observation for signed cell {cell_id!r}")
        for field in CODEGEN_CELL_FIELDS:
            if not isinstance(row.get(field), str) or row[field] != cell[field]:
                raise Refusal(f"observed row for cell {cell_id!r} differs from the signed cell in `{field}`")
        require_hex(row.get("object_sha256"), f"cell {cell_id!r} object_sha256")
        observed[cell_id] = row
    unbuilt = sorted(set(cells) - set(observed))
    if unbuilt:
        raise Refusal(f"missing matrix observations for signed cells: {unbuilt}")


def verify_typed_module_object_executable_lineage(path: Path, cx: Context) -> None:
    """Diagnose the authored typed-module/object/executable digest chain.
    Every link must start from the acceptance run's linked module."""
    doc = load_json_object(path)
    require_schema(doc, EXECUTABLE_LINEAGE_SCHEMA)
    linked = cx.linked_module()
    for link in nonempty_list(doc, "chain"):
        if not isinstance(link, dict):
            raise Refusal("chain links must be objects")
        for key in ("module_sha256", "object_sha256", "executable_sha256"):
            require_hex(link.get(key), f"lineage {key}")
        if link.get("module_typed") is not True:
            raise Refusal("lineage must start from a TYPED Trust-IR module")
        if link["module_sha256"] != linked:
            raise Refusal(
                f"lineage starts from module {link['module_sha256'][:12]}…, not the acceptance "
                f"run's linked module {linked[:12]}…"
            )


def verify_linked_executable_composition_validated(path: Path, cx: Context) -> None:
    """Diagnose authored executable composition claims and component digests."""
    doc = load_json_object(path)
    require_schema(doc, EXECUTABLE_COMPOSITION_SCHEMA)
    for exe in nonempty_list(doc, "executables"):
        if not isinstance(exe, dict):
            raise Refusal("executables must be objects")
        require_hex(exe.get("executable_sha256"), "executable_sha256")
        if exe.get("composition_verdict") != "validated":
            raise Refusal(f"executable composition verdict is {exe.get('composition_verdict')!r}, not validated")
        components = exe.get("components")
        if not isinstance(components, list) or not components:
            raise Refusal("an executable must list its composed components")
        for component in components:
            require_hex(component.get("sha256") if isinstance(component, dict) else None, "component sha256")


def verify_runtime_startup_syslib_closure_bound(path: Path, cx: Context) -> None:
    """Diagnose authored runtime, startup, and system-library closure claims."""
    doc = load_json_object(path)
    require_schema(doc, RUNTIME_CLOSURE_SCHEMA)
    if doc.get("closure") != "bound":
        raise Refusal(f"closure is {doc.get('closure')!r}, not \"bound\"")
    for key in ("runtime_id", "startup_id"):
        if not isinstance(doc.get(key), str) or not doc[key]:
            raise Refusal(f"`{key}` must be named")
    for lib in nonempty_list(doc, "syslibs"):
        if not isinstance(lib, dict) or not isinstance(lib.get("name"), str) or not lib["name"]:
            raise Refusal("every syslib must be named")
        require_hex(lib.get("sha256"), f"syslib {lib.get('name')!r} sha256")


VERIFIERS: dict[str, Callable[[Path, Context], None]] = {
    "exact_linked_module_is_codegen_input": verify_exact_linked_module_is_codegen_input,
    "full_admitted_codegen_surface": verify_full_admitted_codegen_surface,
    "zero_unproved_fallbacks": verify_zero_unproved_fallbacks,
    "machine_equivalence_evidence": verify_machine_equivalence_evidence,
    "objects_biject_admitted_modules": verify_objects_biject_admitted_modules,
    "authorized_codegen_matrix_complete": verify_authorized_codegen_matrix_complete,
    "typed_module_object_executable_lineage": verify_typed_module_object_executable_lineage,
    "linked_executable_composition_validated": verify_linked_executable_composition_validated,
    "runtime_startup_syslib_closure_bound": verify_runtime_startup_syslib_closure_bound,
}
assert tuple(VERIFIERS) == REQUIRED


# ── driver (identical protocol to the G5 checker) ───────────────────────────


def resolve_ref(root: Path, ref: Any) -> tuple[Path | None, str | None]:
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
    except Refusal as exc:
        return candidate, str(exc)
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
    if args.receipt is not None or args.prior_gates_root is not None:
        passed = False
        diagnostics.append("G7 must not receive --receipt or --prior-gates-root (G8-only protocol inputs)")
    if not HEX_DIGEST.fullmatch(args.linked_module_sha256 or ""):
        passed = False
        diagnostics.append("--linked-module-sha256 must be a lowercase 64-hex digest")
    # The receipt's consumed-module digest is compared against the linked module
    # only once the checker itself has hashed those bytes.
    linked_module_refusal: str | None = None
    try:
        if sha256_of(Path(args.linked_module)) != args.linked_module_sha256:
            linked_module_refusal = "--linked-module bytes differ from --linked-module-sha256"
    except Refusal as exc:
        linked_module_refusal = f"--linked-module cannot be hashed: {exc}"
    if linked_module_refusal is not None:
        passed = False
        diagnostics.append(linked_module_refusal)
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
    cx = Context(
        root,
        args.linked_module_sha256,
        Path(args.authority_policy),
        args.authority_policy_sha256,
        artifacts,
        linked_module_refusal,
    )

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
                    VERIFIERS[check_id](path, cx)  # type: ignore[arg-type]
                except Refusal as exc:
                    diagnostics.append(f"{check_id}: {exc}")
                else:
                    # A hash-bound authored artifact can support diagnostics, not
                    # a G7 completion verdict. No independent object/proof replay
                    # is wired to any of these nine conjuncts yet.
                    diagnostics.append(f"{check_id}: {AUTHORITY_GAPS[check_id]}")
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
