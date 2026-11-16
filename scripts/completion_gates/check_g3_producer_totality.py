#!/usr/bin/env python3
"""Schema-owned G3 producer-totality checker.

The receipt runner executes this file as an isolated snapshot, and the Rust
scorecard replay runs the tree's pinned scorecard in an isolated interpreter
that reads no bytecode from the tree and writes none.  Producer
scorecards are observations, not admission authority: the owner-signed admission
contract and receipt-bound corpus fix the file population.  Subject-index roots
are locally recomputed from authored rows, not source/content authentication.
Rust admitted roots and every auxiliary source pinned by the retained
precompile input manifest are rehashed against this tree.  The join artifact
only correlates labels; it cannot create a body or certify a validator result.

The Rust scorecard's corpus-local gate omits full instance/runtime authority;
the Lean scorecard has a supplied (not authenticated) body census; the Lean
kernel roster says diagnostic-only; and no recheckable joined Trust-IR module
validator exists.  The other eight subject-index roots and stable body-content
identity are not established here.  These gaps keep G3 red even when every
currently measurable row is clean.
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
GATE = "G3"
CHECKER = "trust.two-language.g3.producer-totality/v2"
REPOSITORY_ID = "https://github.com/alabsystems/trust"
HEX = re.compile(r"^[0-9a-f]{64}$")
GIT_REVISION = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
REQUIRED = (
    "admitted_file_manifest_exact",
    "reachable_body_census_exact",
    "rust_zero_producer_residue",
    "lean_zero_producer_residue",
    "all_joined_modules_valid",
    "no_denominator_exclusions",
    "subject_index_roots_match",
)
ARTIFACTS = (
    "rust_scorecard", "lean_scorecard", "lean_input_manifest",
    "lean_body_census", "lean_inventory", "body_join",
)
# Exactly the artifacts each row's verify() path reads (through rust(), lean(),
# lean_inventory() and joined()): the runner binds a row's declared artifacts,
# so a row that reads an undeclared one under-discloses its evidence.
LEAN_BODY_ARTIFACTS = ("lean_scorecard", "lean_input_manifest", "lean_body_census")
JOINED_ARTIFACTS = ("rust_scorecard", *LEAN_BODY_ARTIFACTS, "body_join")
CHECK_ARTIFACTS = {
    "admitted_file_manifest_exact": ("rust_scorecard", *LEAN_BODY_ARTIFACTS),
    "reachable_body_census_exact": JOINED_ARTIFACTS,
    "rust_zero_producer_residue": ("rust_scorecard",),
    "lean_zero_producer_residue": (*LEAN_BODY_ARTIFACTS, "lean_inventory"),
    "all_joined_modules_valid": ("rust_scorecard",),
    "no_denominator_exclusions": JOINED_ARTIFACTS,
    "subject_index_roots_match": JOINED_ARTIFACTS,
}
assert tuple(CHECK_ARTIFACTS) == REQUIRED


class Refusal(Exception):
    pass


def exact(value: Any, keys: set[str], where: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        raise Refusal(f"{where}: expected exactly {sorted(keys)}")
    return value


def rows(value: Any, where: str, *, nonempty: bool = True) -> list[Any]:
    if not isinstance(value, list) or (nonempty and not value):
        raise Refusal(f"{where}: expected {'non-empty ' if nonempty else ''}array")
    return value


def string(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise Refusal(f"{where}: expected non-empty string")
    return value


def digest(value: Any, where: str) -> str:
    if not isinstance(value, str) or not HEX.fullmatch(value):
        raise Refusal(f"{where}: expected lowercase SHA-256")
    return value


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical_root(value: Any) -> str:
    raw = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def lean_canonical_digest(value: Any) -> str:
    raw = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def unique_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load(path: Path) -> dict[str, Any]:
    try:
        _trust_text = path.read_text(encoding="utf-8")
        if _trust_json_nesting_depth(_trust_text) > TRUST_MAX_JSON_DEPTH:
            raise ValueError(f"JSON nests deeper than {TRUST_MAX_JSON_DEPTH}")
        value = json.loads(_trust_text, object_pairs_hook=unique_pairs,
                           parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
        json.dumps(value, ensure_ascii=False, allow_nan=False).encode("utf-8")
    except (OSError, UnicodeError, ValueError, RecursionError) as exc:
        raise Refusal(f"cannot read {path.name} as strict JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise Refusal(f"{path.name}: expected JSON object")
    return value


class Context:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.root = Path(args.root).resolve()
        self.bundle: dict[str, Any] = {}
        self.refs: dict[str, dict[str, str]] = {}
        self.docs: dict[str, dict[str, Any]] = {}
        self.cache: dict[str, Any] = {}
        self.errors: list[str] = []
        try:
            self.bundle = exact(load(Path(args.verify_evidence)),
                                {"schema", "gate", "checker", "artifacts"}, "evidence bundle")
            if (self.bundle["schema"], self.bundle["gate"], self.bundle["checker"]) != (
                EVIDENCE_SCHEMA, GATE, CHECKER
            ):
                raise Refusal("evidence bundle has wrong schema, gate, or checker")
            artifacts = exact(self.bundle["artifacts"], set(ARTIFACTS), "evidence artifacts")
            for name in ARTIFACTS:
                path, ref = self.ref(artifacts[name], f"artifacts.{name}")
                self.refs[name] = ref
                self.docs[name] = load(path)
        except Refusal as exc:
            self.errors.append(str(exc))

    def path(self, raw: Any, where: str) -> Path:
        name = string(raw, where)
        path = Path(name)
        if "\0" in name or path.is_absolute() or "\\" in name or any(part in {"", ".", ".."} for part in name.split("/")):
            raise Refusal(f"{where}: path must be canonical and root-relative")
        try:
            candidate = (self.root / path).resolve()
        except (OSError, RuntimeError, ValueError) as exc:
            # RuntimeError: Python 3.9's pathlib on a symlink loop (and its
            # subclass RecursionError on a deep symlink chain).
            raise Refusal(f"{where}: path cannot be resolved: {exc}") from exc
        if not candidate.is_relative_to(self.root):
            raise Refusal(f"{where}: missing file or path escapes root: {name}")
        try:
            # Python 3.9's is_file re-raises errors such as ENAMETOOLONG.
            is_file = candidate.is_file()
        except OSError as exc:
            raise Refusal(f"{where}: path cannot be inspected: {exc}") from exc
        if not is_file:
            raise Refusal(f"{where}: missing file or path escapes root: {name}")
        return candidate

    def ref(self, value: Any, where: str) -> tuple[Path, dict[str, str]]:
        row = exact(value, {"path", "sha256"}, where)
        path = self.path(row["path"], where)
        expected = digest(row["sha256"], f"{where}.sha256")
        try:
            observed = sha256(path)
        except OSError as exc:
            raise Refusal(f"{where}: cannot read: {exc}") from exc
        if observed != expected:
            raise Refusal(f"{where}: content hash mismatch")
        return path, row

    def document(self, name: str, schema: str) -> dict[str, Any]:
        if name not in self.docs:
            raise Refusal(f"{name}: no bound artifact")
        doc = self.docs[name]
        if doc.get("schema") != schema:
            raise Refusal(f"{name}: expected schema {schema}")
        return doc

    def memo(self, name: str, compute: Any) -> Any:
        if name not in self.cache:
            self.cache[name] = compute()
        return self.cache[name]

    def admission(self) -> dict[str, tuple[str, str, str]]:
        def compute() -> dict[str, tuple[str, str, str]]:
            policy = load(Path(self.args.authority_policy))
            if policy.get("schema") != "trust.two-language.authority-policy/v2":
                raise Refusal("authority policy schema is not v2")
            contract_ref = exact(policy.get("contracts"), {
                "admission", "semantics", "obligations", "proof_authority",
                "compatibility_surfaces", "codegen_surface", "acceptance_environment",
            }, "authority policy contracts")["admission"]
            named = exact(contract_ref, {"id", "path", "sha256"}, "admission contract ref")
            if named["id"] != "trust.two-language.contract.admission":
                raise Refusal("admission contract has wrong identity")
            contract_path, _ = self.ref({"path": named["path"], "sha256": named["sha256"]},
                                        "admission contract")
            contract = load(contract_path)
            exact(contract, {"schema", "goal_id", "repository_id", "lanes"}, "admission contract")
            if (contract["schema"], contract["goal_id"], contract["repository_id"]) != (
                "trust.two-language.admission-contract/v1", GOAL, REPOSITORY_ID
            ):
                raise Refusal("admission contract header mismatch")
            corpus = load(Path(self.args.corpus_manifest))
            exact(corpus, {"schema", "goal_id", "repository_id", "acceptance_run_id",
                           "source_revision", "rust", "lean", "mixed"}, "corpus manifest")
            if (corpus["schema"], corpus["goal_id"], corpus["repository_id"],
                corpus["acceptance_run_id"], corpus["source_revision"]) != (
                "trust.two-language.corpus-manifest/v1", GOAL, REPOSITORY_ID,
                self.args.acceptance_run_id, self.args.source_revision
            ):
                raise Refusal("corpus manifest header mismatch")
            lanes = exact(contract["lanes"], {"rust", "lean", "mixed"}, "admission lanes")
            admitted: dict[str, tuple[str, str, str]] = {}
            seen_ids: set[str] = set()
            for lane in ("rust", "lean", "mixed"):
                owner_lane = exact(lanes[lane], {"upstream_repository", "upstream_revision",
                    "upstream_tree_sha256", "feature_manifest", "suite_manifest",
                    "exception_ledger", "entries"}, f"owner {lane}")
                observed = exact(corpus[lane], {"upstream_revision", "admission_policy_sha256",
                    "entries"}, f"corpus {lane}")
                if (observed["upstream_revision"] != owner_lane["upstream_revision"]
                    or observed["admission_policy_sha256"] != named["sha256"]
                    or observed["entries"] != owner_lane["entries"]):
                    raise Refusal(f"{lane}: corpus entries differ from owner admission contract")
                for row in rows(owner_lane["entries"], f"owner {lane}.entries"):
                    entry = exact(row, {"id", "kind", "admitted", "source", "expected_outcome"},
                                  f"owner {lane} entry")
                    entry_id = string(entry["id"], f"owner {lane} id")
                    if entry_id in seen_ids:
                        raise Refusal(f"duplicate owner corpus id {entry_id}")
                    seen_ids.add(entry_id)
                    string(entry["kind"], f"owner {lane} {entry_id}.kind")
                    _, source_ref = self.ref(entry["source"], f"owner {lane} {entry_id}.source")
                    if type(entry["admitted"]) is not bool:
                        raise Refusal(f"{entry_id}: admitted must be boolean")
                    if entry["admitted"]:
                        if entry["expected_outcome"] != "ok":
                            raise Refusal(f"{entry_id}: admitted file is not expected to compile")
                        admitted[entry_id] = (lane, source_ref["path"], source_ref["sha256"])
            if not any(lane == "rust" for lane, _, _ in admitted.values()) or not any(
                lane == "lean" for lane, _, _ in admitted.values()
            ):
                raise Refusal("owner admission lacks Rust or Lean admitted inputs")
            if not any(lane == "mixed" for lane, _, _ in admitted.values()):
                raise Refusal("owner admission lacks an admitted mixed input")
            return admitted
        return self.memo("admission", compute)

    def reject_source_aliases(self) -> None:
        # A resolved path keeps the spelling it was given, so a case variant
        # on a case-insensitive volume, or a hardlink, names one file under two
        # paths: one source is one (st_dev, st_ino).
        by_source: dict[tuple[int, int], list[str]] = {}
        for entry_id, (_, source, _) in self.admission().items():
            where = f"admitted {entry_id} source"
            try:
                info = os.stat(self.path(source, where))
            except OSError as exc:
                raise Refusal(f"{where} cannot be inspected: {exc}") from exc
            by_source.setdefault((info.st_dev, info.st_ino), []).append(entry_id)
        for ids in by_source.values():
            if len(ids) != 1:
                raise Refusal(
                    f"admitted IDs {sorted(ids)} share one source; one compilation cannot census "
                    "multiple admitted IDs/configurations"
                )

    def require_denominator_authority(self) -> None:
        self.reject_source_aliases()
        if any(lane == "mixed" for lane, _, _ in self.admission().values()):
            raise Refusal(
                "mixed admitted sources lack a compiler-independent per-ID/config Rust and Lean body census"
            )
        raise Refusal(
            "no authenticated per-admitted-ID/config body census binds all admitted files, "
            "generated instances, and runtime roots"
        )

    def require_body_identity_authority(self) -> None:
        raise Refusal(
            "subject function/body digests are authored labels: no authenticated stable body "
            "identity and source/Trust-IR content binding exists for the producer join"
        )

    def subject(self) -> tuple[dict[str, dict[str, Any]], dict[str, set[str]], set[str]]:
        def compute() -> tuple[dict[str, dict[str, Any]], dict[str, set[str]], set[str]]:
            doc = load(Path(self.args.subject_graph))
            exact(doc, {"schema", "goal_id", "acceptance_run_id", "source_revision",
                        "programs", "roots", "release_executable"}, "subject index")
            if (doc["schema"], doc["goal_id"], doc["acceptance_run_id"], doc["source_revision"]) != (
                "trust.two-language.subject-index/v3", GOAL,
                self.args.acceptance_run_id, self.args.source_revision
            ):
                raise Refusal("subject index header mismatch")
            roots = doc["roots"]
            if not isinstance(roots, dict):
                raise Refusal("subject index roots missing")
            programs: dict[str, dict[str, Any]] = {}
            root_names = {"admitted_files", "reachable_bodies", "refinement_certificates",
                          "obligations", "proof_certificates", "modules", "codegen_matrix_cells",
                          "objects", "translation_evidence", "call_edges", "executables"}
            exact(roots, root_names, "subject index roots")
            populations: dict[str, list[dict[str, Any]]] = {name: [] for name in (
                "admitted_files", "reachable_bodies", "modules"
            )}
            module_digests: set[str] = set()
            languages: set[str] = set()
            for program in rows(doc["programs"], "subject programs"):
                exact(program, {"id", "entrypoints", "admitted_file_ids", "bodies",
                    "refinement_certificates", "obligations", "proof_certificates", "modules",
                    "objects", "translation_evidence", "executables", "call_edges",
                    "contextual_refinement"}, "subject program")
                pid = string(program.get("id"), "subject program id")
                if pid in programs:
                    raise Refusal(f"duplicate subject program {pid}")
                files = rows(program.get("admitted_file_ids"), f"{pid}.admitted_file_ids")
                if any(not isinstance(item, str) or not item for item in files) or len(set(files)) != len(files):
                    raise Refusal(f"{pid}: invalid or duplicate admitted file ids")
                for file_id in files:
                    populations["admitted_files"].append({"program_id": pid, "file_id": file_id})
                bodies: dict[str, dict[str, Any]] = {}
                for body in rows(program.get("bodies"), f"{pid}.bodies"):
                    exact(body, {"id", "language", "function_identity_sha256",
                        "source_language_semantics_id", "source_language_semantics_sha256",
                        "source_semantics_sha256", "trust_ir_semantics_id", "trust_ir_semantics_sha256",
                        "trust_ir_sha256", "ssa_epoch_sha256", "effect_summary_sha256"}, f"{pid}.body")
                    bid = string(body["id"], f"{pid}.body.id")
                    if bid in bodies or not isinstance(body["language"], str) or (
                        body["language"] not in {"rust", "lean"}
                    ):
                        raise Refusal(f"{pid}: duplicate body or unknown language {bid}")
                    for key in ("function_identity_sha256", "source_language_semantics_sha256",
                                "source_semantics_sha256", "trust_ir_semantics_sha256",
                                "trust_ir_sha256", "ssa_epoch_sha256", "effect_summary_sha256"):
                        digest(body[key], f"{pid}.{bid}.{key}")
                    bodies[bid] = body
                    languages.add(body["language"])
                    populations["reachable_bodies"].append({"program_id": pid, **body})
                modules: dict[str, dict[str, Any]] = {}
                owners: dict[str, str] = {}
                for module in rows(program.get("modules"), f"{pid}.modules"):
                    exact(module, {"id", "artifact", "body_ids", "call_edge_ids", "obligation_ids",
                        "refinement_certificate_body_ids", "proof_certificate_ids",
                        "assumption_closure_sha256", "contextual_refinement_evidence"}, f"{pid}.module")
                    mid = string(module["id"], f"{pid}.module.id")
                    if mid in modules:
                        raise Refusal(f"{pid}: duplicate module {mid}")
                    _, module_ref = self.ref(module["artifact"], f"{pid}.{mid}.artifact")
                    module_digests.add(module_ref["sha256"])
                    for bid in rows(module["body_ids"], f"{pid}.{mid}.body_ids"):
                        bid = string(bid, f"{pid}.{mid}.body_ids")
                        if bid not in bodies or bid in owners:
                            raise Refusal(f"{pid}: module body partition has unknown/duplicate body {bid!r}")
                        owners[bid] = mid
                    modules[mid] = module
                    populations["modules"].append({"program_id": pid, **module})
                if set(owners) != set(bodies):
                    raise Refusal(f"{pid}: module body partition omits {sorted(set(bodies) - set(owners))[:4]}")
                programs[pid] = {"files": set(files), "bodies": bodies, "modules": modules,
                                 "body_module": owners}
            if languages != {"rust", "lean"}:
                raise Refusal("subject index does not contain both Rust and Lean reachable bodies")
            if self.args.linked_module_sha256 not in module_digests:
                raise Refusal("receipt linked module is not a typed subject module")
            for name, population in populations.items():
                ordered = sorted(population, key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")))
                if roots.get(name) != canonical_root(ordered):
                    raise Refusal(f"subject index {name} root differs from recomputed rows")
            return programs, {name: set(p["files"]) for name, p in programs.items()}, module_digests
        return self.memo("subject", compute)

    def rust(self) -> set[tuple[str, str, str]]:
        def compute() -> set[tuple[str, str, str]]:
            doc = self.document("rust_scorecard", "trust.trust-ir.producer-scorecard.v1")
            corpora = doc.get("corpora")
            if not isinstance(corpora, dict) or not corpora:
                raise Refusal("Rust scorecard has no corpora")
            admitted = {path: source for lane, path, source in self.admission().values() if lane == "rust"}
            measured_files: dict[str, str] = {}
            census_bodies: set[tuple[str, str, str]] = set()
            observed_bodies: set[tuple[str, str, str]] = set()
            for name, corpus in corpora.items():
                if not isinstance(corpus, dict):
                    raise Refusal(f"Rust corpus {name}: malformed")
                input_census = exact(corpus.get("input_census"), {"schema", "source", "files"},
                                     f"Rust {name} input census")
                if (input_census["schema"], input_census["source"]) != (
                    "trust.trust-ir.producer-input-census.v1", "precompile-content-manifest/v1"
                ):
                    raise Refusal(f"Rust {name}: unsupported input census")
                for row in rows(input_census["files"], f"Rust {name} inputs"):
                    exact(row, {"file", "sha256", "expected_outcome"}, "Rust input row")
                    path = string(row["file"], "Rust input file")
                    source = digest(row["sha256"], f"Rust {path} source")
                    if path in measured_files or row["expected_outcome"] != "ok":
                        raise Refusal(f"Rust {path}: duplicate or excluded input")
                    measured_files[path] = source
                    if sha256(self.path(path, f"Rust {path}")) != source:
                        raise Refusal(f"Rust {path}: source hash drift")
                # The retained precompile manifest also pins every auxiliary
                # source (mod/include!) the compiler read.  Bind each one to
                # this tree exactly as the admitted roots are bound: a sweep
                # over other auxiliary content did not measure this tree.
                evidence = corpus.get("census_evidence")
                manifest = exact(evidence.get("input_manifest") if isinstance(evidence, dict) else None,
                                 {"schema", "corpora"}, f"Rust {name} precompile input manifest")
                if manifest["schema"] != "trust.rust.measurement-input-manifest.v1":
                    raise Refusal(f"Rust {name}: unsupported precompile input manifest")
                precompile = exact(exact(manifest["corpora"], {"corpus"}, f"Rust {name} precompile corpora")["corpus"],
                                   {"files", "sources"}, f"Rust {name} precompile corpus")
                if precompile["files"] != input_census["files"]:
                    raise Refusal(f"Rust {name}: input census differs from retained precompile manifest")
                sources: dict[str, str] = {}
                for row in rows(precompile["sources"], f"Rust {name} precompile sources"):
                    exact(row, {"file", "sha256"}, "Rust precompile source row")
                    path = string(row["file"], "Rust precompile source file")
                    source = digest(row["sha256"], f"Rust {path} precompile source")
                    if path in sources:
                        raise Refusal(f"Rust {name}: duplicate precompile source {path}")
                    sources[path] = source
                    if sha256(self.path(path, f"Rust precompile source {path}")) != source:
                        raise Refusal(f"Rust {path}: precompile source hash drift")
                for row in input_census["files"]:
                    if sources.get(row["file"]) != row["sha256"]:
                        raise Refusal(f"Rust {row['file']}: input root is not a precompile source at its measured hash")
                body_census = exact(corpus.get("body_census"), {"schema", "source", "bodies"},
                                    f"Rust {name} body census")
                if (body_census["schema"], body_census["source"]) != (
                    "trust.trust-ir.producer-body-census.v1",
                    "independent-hir-and-typeck-generated-body-census/v1"
                ):
                    raise Refusal(f"Rust {name}: missing independent HIR/body census")
                for row in rows(body_census["bodies"], f"Rust {name} bodies", nonempty=False):
                    exact(row, {"file", "def", "kind"}, "Rust census body")
                    key = (string(row["file"], "Rust body file"), string(row["def"], "Rust body def"),
                           string(row["kind"], "Rust body kind"))
                    if key in census_bodies:
                        raise Refusal(f"duplicate Rust census body {key}")
                    census_bodies.add(key)
                outcomes: set[str] = set()
                for row in rows(corpus.get("files"), f"Rust {name} results"):
                    path = string(row.get("file") if isinstance(row, dict) else None, "Rust result file")
                    if path in outcomes or row.get("outcome") != "ok":
                        raise Refusal(f"Rust {path}: duplicate or non-ok file outcome {row.get('outcome')!r}")
                    outcomes.add(path)
                    validation = exact(row.get("validation"), {"total", "classes"}, f"Rust {path} validation")
                    classes = validation["classes"]
                    if type(validation["total"]) is not int or validation["total"] != 0 or classes != {}:
                        raise Refusal(f"Rust {path}: invalid or unmeasured assembled module")
                    # parse_bodies measures exactly these fields; a missing
                    # one is unmeasured, not clean.
                    anomalies = exact(row.get("anomalies"), {"duplicate_differential_events",
                        "duplicate_unsupported_events", "unsupported_event_without_differential_event"},
                        f"Rust {path} anomalies")
                    if any(type(anomalies[key]) is not int or anomalies[key] != 0 for key in (
                        "duplicate_differential_events", "duplicate_unsupported_events"
                    )) or anomalies["unsupported_event_without_differential_event"] != []:
                        raise Refusal(f"Rust {path}: parse anomalies or unmeasured anomaly fields")
                    for body in rows(row.get("bodies"), f"Rust {path} body rows", nonempty=False):
                        if not isinstance(body, dict):
                            raise Refusal(f"Rust {path}: malformed body row")
                        key = (path, string(body.get("def"), "Rust body def"),
                               string(body.get("kind"), "Rust body kind"))
                        if key in observed_bodies:
                            raise Refusal(f"duplicate Rust producer body {key}")
                        if (type(body.get("unsupported")) is not int or body["unsupported"] != 0
                            or body.get("reasons") != [] or body.get("symbolic") is not False
                            or body.get("opaque_collapse") is not False):
                            raise Refusal(f"Rust {key}: unsupported, symbolic, opaque, or unmeasured body")
                        observed_bodies.add(key)
                if outcomes != {row["file"] for row in input_census["files"]}:
                    raise Refusal(f"Rust {name}: measured files differ from input census")
            if measured_files != admitted:
                raise Refusal("Rust measured files/hashes differ from owner-admitted files")
            if observed_bodies != census_bodies:
                raise Refusal("Rust producer bodies differ from independent body census")
            return census_bodies
        return self.memo("rust", compute)

    def rust_replay(self) -> None:
        self.rust()
        provenance = self.document("rust_scorecard", "trust.trust-ir.producer-scorecard.v1").get("provenance")
        if not isinstance(provenance, dict) or provenance.get("repo_head") != self.args.source_revision:
            raise Refusal("Rust scorecard was not produced at the accepted source revision")
        compiler_hash = digest(provenance.get("trustc_sha256"), "Rust scorecard compiler hash")
        toolchain = load(Path(self.args.toolchain_manifest))
        components = rows(toolchain.get("components"), "toolchain components")
        trustc = [row for row in components if isinstance(row, dict) and row.get("role") == "trustc"]
        if len(trustc) != 1 or not isinstance(trustc[0].get("artifact"), dict) or (
            compiler_hash != trustc[0]["artifact"].get("sha256")
        ):
            raise Refusal("Rust scorecard compiler differs from receipt-bound trustc")
        path = self.path("scripts/trust_ir_producer_scorecard.py", "Rust scorecard checker")
        scorecard_path = self.path(self.refs["rust_scorecard"]["path"], "Rust scorecard")
        try:
            # The scorecard loads scripts/rust_instance_census.py by file path,
            # and an import by path reads the tree's __pycache__, which the
            # clean-tree gate permits (it is ignored): a planted unchecked-hash
            # .pyc would run in place of the pinned census.  So this child reads
            # bytecode only from a fresh empty prefix and writes none; it does
            # not inherit this process's -X options.
            with tempfile.TemporaryDirectory(prefix="trust-g3-scorecard-bytecode-") as bytecode:
                run = subprocess.run(
                    [sys.executable, "-I", "-B", "-X", f"pycache_prefix={bytecode}", str(path),
                     "--check-completion", str(scorecard_path)],
                    cwd=self.root, capture_output=True, text=True, timeout=300, check=False)
            verdict = json.loads(run.stdout)
        except (OSError, ValueError, subprocess.TimeoutExpired) as exc:
            raise Refusal(f"Rust scorecard raw compiler-census replay failed: {exc}") from exc
        if (run.returncode != 0 or not isinstance(verdict, dict) or verdict.get("complete") is not True
            or verdict.get("aggregate_source") != "recomputed_from_files"
            or verdict.get("artifact_errors") != []):
            detail = verdict.get("artifact_errors") if isinstance(verdict, dict) else run.stderr
            raise Refusal(f"Rust scorecard raw compiler-census replay is incomplete: {str(detail)[:350]}")

    def require_rust_totality_authority(self) -> None:
        scorecard = self.document("rust_scorecard", "trust.trust-ir.producer-scorecard.v1")
        for name, corpus in scorecard["corpora"].items():
            status = corpus.get("census_status") if isinstance(corpus, dict) else None
            if not isinstance(status, dict):
                raise Refusal(f"Rust {name}: missing complete instance/runtime census")
            unrepresented = status.get("mono_unrepresented")
            if not isinstance(unrepresented, dict) or unrepresented:
                raise Refusal(f"Rust {name}: unrepresented monomorphized/runtime classes {unrepresented!r}")
            unmeasured = status.get("unmeasured")
            if not isinstance(unmeasured, list) or unmeasured:
                raise Refusal(f"Rust {name}: unmeasured instance/runtime classes {unmeasured!r}")
            for field in ("reachable_instances", "runtime_roots", "external_dependency_closure",
                          "proc_macro_io", "build_environment"):
                if status.get(field) != "complete":
                    raise Refusal(f"Rust {name}: {field} is not independently complete")
        # The retained census/status lives in the scorecard itself.  Even a
        # favorable edit to those rows is not authenticated measurement.
        raise Refusal(
            "Rust retained scorecard/census rows are authored artifacts; no authenticated "
            "independent complete instance and runtime census is bound to G3"
        )

    def lean(self) -> set[tuple[str, str, str]]:
        def compute() -> set[tuple[str, str, str]]:
            manifest = self.document("lean_input_manifest", "trust.clean-corpus.input-manifest/v1")
            census = self.document("lean_body_census", "trust.clean-corpus.body-census/v1")
            doc = self.document("lean_scorecard", "trust.clean-corpus.scorecard/v2")
            exact(manifest, {"schema", "files"}, "Lean input manifest")
            exact(census, {"schema", "input_manifest_sha256", "files", "declarations"},
                  "Lean body census")
            if census.get("input_manifest_sha256") != lean_canonical_digest(manifest):
                raise Refusal("Lean body census does not bind the exact input manifest")
            admitted = {path: source for lane, path, source in self.admission().values() if lane == "lean"}
            inputs: dict[str, str] = {}
            auxiliaries: dict[str, list[dict[str, str]]] = {}
            for row in rows(manifest.get("files"), "Lean input files"):
                exact(row, {"file", "sha256", "expected_outcome", "auxiliary_inputs"}, "Lean input row")
                path = string(row["file"], "Lean input file")
                source = digest(row["sha256"], f"Lean {path} source")
                if path in inputs or row["expected_outcome"] != "ok" or not isinstance(row["auxiliary_inputs"], list):
                    raise Refusal(f"Lean {path}: duplicate or excluded input")
                inputs[path] = source
                if sha256(self.path(path, f"Lean {path}")) != source:
                    raise Refusal(f"Lean {path}: source hash drift")
                aux_rows: list[dict[str, str]] = []
                seen_aux: set[str] = set()
                for aux in row["auxiliary_inputs"]:
                    exact(aux, {"file", "sha256"}, f"Lean {path} auxiliary input")
                    aux_path = string(aux["file"], f"Lean {path} auxiliary path")
                    aux_hash = digest(aux["sha256"], f"Lean {aux_path} auxiliary hash")
                    if aux_path == path or aux_path in seen_aux:
                        raise Refusal(f"Lean {path}: duplicate/self auxiliary input")
                    seen_aux.add(aux_path)
                    if sha256(self.path(aux_path, f"Lean {aux_path}")) != aux_hash:
                        raise Refusal(f"Lean {aux_path}: auxiliary source hash drift")
                    aux_rows.append({"file": aux_path, "sha256": aux_hash})
                auxiliaries[path] = aux_rows
            if inputs != admitted:
                raise Refusal("Lean input files/hashes differ from owner-admitted files")
            census_files = rows(census.get("files"), "Lean census files")
            if (any(not isinstance(item, str) or not item for item in census_files)
                or set(census_files) != set(inputs) or len(census_files) != len(inputs)):
                raise Refusal("Lean body census file roster differs from admitted files")
            expected: set[tuple[str, str, str]] = set()
            for row in rows(census.get("declarations"), "Lean census declarations"):
                exact(row, {"file", "name", "kind"}, "Lean census declaration")
                key = (string(row["file"], "Lean declaration file"),
                       string(row["name"], "Lean declaration name"), string(row["kind"], "Lean kind"))
                if key[0] not in inputs or key[2] not in {"computational", "proof-only"} or key in expected:
                    raise Refusal(f"Lean census has duplicate/unknown declaration {key}")
                expected.add(key)
            files: set[str] = set()
            for row in rows(doc.get("per_file"), "Lean scorecard per_file"):
                if not isinstance(row, list) or len(row) != 3:
                    raise Refusal("Lean malformed per_file row")
                path = string(row[0], "Lean file outcome path")
                if path in files or row[1] != "ok":
                    raise Refusal(f"Lean {path}: duplicate or non-ok file outcome {row[1]!r}")
                files.add(path)
            if files != set(inputs):
                raise Refusal("Lean scorecard files differ from admitted files")
            records: set[str] = set()
            for row in rows(doc.get("file_records"), "Lean measured file records"):
                path = string(row.get("file") if isinstance(row, dict) else None, "Lean record file")
                if path in records or row.get("outcome") != "ok" or type(row.get("returncode")) is not int or row["returncode"] != 0 or row.get("sha256") != inputs.get(path):
                    raise Refusal(f"Lean {path}: incomplete compiler exit or source identity")
                if row.get("auxiliary_inputs") != auxiliaries[path]:
                    raise Refusal(f"Lean {path}: measured auxiliary input closure differs from manifest")
                records.add(path)
            if records != files:
                raise Refusal("Lean measured file records differ from admitted files")
            dispositions: dict[tuple[str, str], dict[str, tuple[str, str]]] = {}
            for row in rows(doc.get("rows"), "Lean producer declarations"):
                if not isinstance(row, list) or len(row) != 5 or not all(isinstance(item, str) for item in row):
                    raise Refusal("Lean malformed producer declaration")
                path, name, disposition, _, reason = row
                if path not in inputs or not name or not disposition:
                    raise Refusal(f"Lean malformed/unadmitted producer declaration {path}:{name}")
                lane = disposition.split(":", 1)[0]
                identity = (path, name)
                lanes = dispositions.setdefault(identity, {})
                if lane in lanes:
                    raise Refusal(f"Lean duplicate declaration lane {path}:{name}:{lane}")
                lanes[lane] = (disposition, reason)
            observed: set[tuple[str, str, str]] = set()
            for (path, name), lanes in dispositions.items():
                proof = "general" in lanes and lanes["general"][0] == "general:not-computational"
                kind = "proof-only" if proof else "computational"
                key = (path, name, kind)
                if key not in expected:
                    raise Refusal(f"Lean unexpected or misclassified declaration {key}")
                accepted = ({"general:not-computational", "planner-skipped"} if proof
                            else {"emitted:gate", "general:compiled"})
                spellings = {value[0] for value in lanes.values()}
                if not spellings <= accepted or (not proof and "emitted:gate" not in spellings):
                    raise Refusal(f"Lean {key}: not a fully modeled carrier-gate body")
                if not proof and any(reason for _, reason in lanes.values()):
                    raise Refusal(f"Lean {key}: producer carries a refusal reason")
                observed.add(key)
            if observed != expected:
                raise Refusal(f"Lean producer declarations omit {sorted(expected - observed)[:4]}")
            return {key for key in expected if key[2] == "computational"}
        return self.memo("lean", compute)

    def lean_inventory(self) -> None:
        doc = self.document("lean_inventory", "trust.lean.check-kernel-roster/v1")
        roster = doc.get("kernel_roster")
        if (doc.get("authority") != "post-lowering-inventory" or not isinstance(roster, dict)
            or roster.get("schema") != "trust.lean.kernel-roster/v1"
            or roster.get("authority") != "post-lowering-inventory"
            or roster.get("denominator_status") != "denominator_verified"
            or roster.get("runtime_body_universe") != "measured"):
            raise Refusal("Lean inventory is diagnostic-only or lacks post-lowering denominator/runtime-body authority")
        # Even a favorable label is not sufficient: the current roster has no
        # authenticated per-source, per-body join to the supplied scorecard
        # census.  A future instrument/schema must provide that relation.
        raise Refusal("Lean roster has no authenticated identity join to the supplied computational body census")

    def joined(self) -> None:
        doc = self.document("body_join", "trust.two-language.g3.producer-body-join/v1")
        exact(doc, {"schema", "rows"}, "producer body join")
        programs, _, _ = self.subject()
        admitted = self.admission()
        producer = {("rust", *key) for key in self.rust()} | {("lean", *key) for key in self.lean()}
        observed_producer: set[tuple[str, str, str, str]] = set()
        observed_subject: set[tuple[str, str]] = set()
        for row in rows(doc.get("rows"), "producer body join"):
            exact(row, {"program_id", "file_id", "language", "source_body", "source_kind",
                        "body_id", "module_id"}, "body join row")
            pid = string(row["program_id"], "join program")
            fid = string(row["file_id"], "join file")
            lang = string(row["language"], "join language")
            body_id = string(row["body_id"], "join body")
            module_id = string(row["module_id"], "join module")
            program = programs.get(pid)
            if program is None or fid not in program["files"] or fid not in admitted:
                raise Refusal(f"body join names unknown program/file {pid}/{fid}")
            lane, source_path, _ = admitted[fid]
            if lane == "mixed":
                raise Refusal("mixed admitted source has no compiler-independent Rust/Lean body census")
            if lane != lang or lang not in {"rust", "lean"}:
                raise Refusal(f"body join language mismatch for {fid}")
            source_key = (lang, source_path, string(row["source_body"], "join source body"),
                          string(row["source_kind"], "join source kind"))
            subject_key = (pid, body_id)
            if (source_key not in producer or source_key in observed_producer
                or subject_key in observed_subject or body_id not in program["bodies"]
                or program["bodies"][body_id]["language"] != lang
                or program["body_module"][body_id] != module_id):
                raise Refusal(f"body join has unknown/duplicate/wrong-module body {subject_key}")
            observed_producer.add(source_key)
            observed_subject.add(subject_key)
        expected_subject = {(pid, bid) for pid, program in programs.items() for bid in program["bodies"]}
        if observed_producer != producer or observed_subject != expected_subject:
            raise Refusal("producer/body join is not an exact duplicate-free bijection")


def verify(check_id: str, cx: Context) -> None:
    if check_id == "admitted_file_manifest_exact":
        admitted = cx.admission()
        programs, _, _ = cx.subject()
        observed = [file_id for program in programs.values() for file_id in program["files"]]
        if len(observed) != len(set(observed)) or set(observed) != set(admitted):
            raise Refusal("subject admitted files are not an exact partition of owner admission")
        cx.reject_source_aliases()
        cx.rust()
        cx.lean()
    elif check_id == "reachable_body_census_exact":
        cx.joined()
        cx.require_body_identity_authority()
    elif check_id == "rust_zero_producer_residue":
        cx.rust_replay()
        cx.require_rust_totality_authority()
    elif check_id == "lean_zero_producer_residue":
        cx.lean()
        cx.lean_inventory()
    # RETIREMENT HAZARD (comment only; no behaviour here). The G3 producer,
    # scripts/two_language_subject_index.py, fills every SHA-256 it cannot
    # measure with a published sentinel, sha256("trust.two-language.subject-index.
    # unmeasured/v1:<field>") -- six body digests and eight of the eleven roots --
    # and points the joined module at an `"trust_ir": "unretained"` locator.
    # They are well-formed, so today they are refused ONLY because
    # require_body_identity_authority, all_joined_modules_valid and
    # subject_index_roots_match refuse unconditionally. Before any of those three
    # is retired or relaxed, this checker must first reject those placeholders by
    # value; otherwise retiring the refusal turns a published placeholder into a pass.
    elif check_id == "all_joined_modules_valid":
        cx.subject()
        cx.rust_replay()
        raise Refusal("joined Rust/Lean Trust-IR modules lack an independently recheckable validator result")
    elif check_id == "no_denominator_exclusions":
        cx.admission()
        cx.rust()
        cx.lean()
        cx.joined()
        rust = cx.document("rust_scorecard", "trust.trust-ir.producer-scorecard.v1")
        for corpus in rust["corpora"].values():
            meta = corpus.get("sample_meta")
            if isinstance(meta, dict) and meta.get("campaign_pins_excluded_from_pool", 0) != 0:
                raise Refusal("Rust scorecard held admitted campaign files out of sampling")
        cx.require_denominator_authority()
    elif check_id == "subject_index_roots_match":
        cx.subject()
        cx.joined()
        raise Refusal(
            "only admitted_files, reachable_bodies, and modules roots are locally recomputed from authored rows; "
            "the other 8/11 subject-index roots and body content bindings remain unchecked"
        )
    else:
        raise Refusal(f"unknown G3 check {check_id}")


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
    revision_valid = GIT_REVISION.fullmatch(args.source_revision) is not None
    if not revision_valid:
        diagnostics.append("source_revision must be a lowercase 40- or 64-hex Git revision")
    if args.receipt is not None or args.prior_gates_root is not None:
        diagnostics.append("G3 is pre-seal and must not receive G8-only receipt/prior-gates-root")
    checks = []
    for check_id in REQUIRED:
        needed = CHECK_ARTIFACTS[check_id]
        present = [cx.refs[name] for name in needed if name in cx.refs]
        passed = False
        try:
            if not revision_valid:
                raise Refusal("invalid source revision cannot bind G3 evidence")
            if len(present) != len(needed):
                raise Refusal(f"missing bound artifact(s) {sorted(set(needed) - set(cx.refs))}")
            verify(check_id, cx)
            passed = True
        except (Refusal, OSError, UnicodeError, ValueError, TypeError, KeyError, RecursionError) as exc:
            diagnostics.append(f"{check_id}: {exc}")
        checks.append({"id": check_id, "passed": passed, "artifacts": present})
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
        print(f"G3: {line}", file=sys.stderr)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
