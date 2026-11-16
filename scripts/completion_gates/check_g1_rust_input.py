#!/usr/bin/env python3
"""Fail-closed G1 Rust-input evidence checker.

The top-level receipt runner executes a snapshot of this file with ``python -I``.
It is therefore standard-library-only and has no imports from the candidate
tree. The bundle has the usual ``trust.two-language.gate-evidence/v1`` shape:
``artifacts`` maps each G1 check ID to a root-relative {path, sha256} reference.
The pin check names the tracked baseline, the exception check names the tracked
test-exception ledger, and the other checks name one observation document with
schema ``trust.two-language.g1.rust-observation/v1``.

This is deliberately a NEGATIVE checker, not a complete G1 authority. It
recomputes owner-admitted case and feature identities, the pinned upstream
Git test-file population, and the Rust rows recorded in the subject graph.
The observation has no counters and must biject those populations, but is
self-authored. Neither that graph nor rustc's current mono-item collector is an
independent complete reachable-body census. The upstream test-file tree also
does not enumerate every harness variant or prove every valid Rust program.
No authenticated full-suite semantic/accept-reject run or exhaustive frontend
constructor/runtime instrument is bound by the present protocol. Consequently
those six conjuncts ALWAYS refuse, even when their structural checks succeed.
Only the pinned-revision and non-applicable-ledger checks can pass, by comparing
tracked Git blobs and the owner-signed admission contract. The non-applicable
check also reads the tracked surface-level ``exceptions.toml`` and, as for
``test-exceptions.toml``, refuses any row that is not ``resolved``, whatever its
class: an active row is a live waiver and an expired one was never retired.
The whole G1 verdict cannot pass until the missing instruments and their
authority bindings exist.

Every Git call runs as ``git --no-replace-objects --no-optional-locks -c
core.fsmonitor=false`` with every caller ``GIT_*`` variable stripped and the
runner's own neutralizers set in their place: no system or global
configuration tier, no XDG configuration, no system attributes, and no lazy
fetch. The checker runs directly as well as under the runner, so its own calls
keep off the repository settings through which a read-only command starts a
program: an fsmonitor hook, and a promisor remote's lazy-fetch transport. Lazy
fetch is off only on a Git that honors ``GIT_NO_LAZY_FETCH`` (2.45, and the
2.41.1/2.42.2/2.43.4/2.44.1 security releases); an earlier Git ignores it.
A repository carrying any ``refs/replace/*`` ref is refused by name before any
tree read: a replacement object would otherwise let a tracked-blob comparison
read a substituted ledger while HEAD and the worktree status look unchanged.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
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


VERDICT_SCHEMA = "trust.two-language.gate-checker-verdict/v2"
EVIDENCE_SCHEMA = "trust.two-language.gate-evidence/v1"
OBSERVATION_SCHEMA = "trust.two-language.g1.rust-observation/v1"
GOAL = "TRUST-TWO-LANGUAGE-100"
GATE = "G1"
CHECKER = "trust.two-language.g1.rust-input/v2"
REPOSITORY_ID = "https://github.com/alabsystems/trust"
BASELINE = "tests/upstream-rust/baseline.toml"
VERSION = "release/trust-version.toml"
TEST_EXCEPTIONS = "tests/upstream-rust/test-exceptions.toml"
SURFACE_EXCEPTIONS = "tests/upstream-rust/exceptions.toml"
# trust-upstream-compat model.rs ExceptionStatus, shared by both Rust ledgers.
EXCEPTION_STATUSES = {"active", "expired", "resolved"}
HEX = re.compile(r"[0-9a-f]{64}\Z")
OID = re.compile(r"(?:[0-9a-f]{40}|[0-9a-f]{64})\Z")
KEY = re.compile(r"[A-Za-z0-9_-]+\Z")
# TOML ends a line only at LF or CRLF. Every other character Python's
# str.splitlines breaks on -- a lone CR, VT, FF, FS/GS/RS, and U+0085/U+2028/
# U+2029, which TOML admits inside a comment -- would make this subset see a
# key or table header that a real TOML parser reads as comment text. The
# remaining C0 controls and DEL are invalid in TOML anyway. The tracked
# ledgers contain none of them, so each is refused wherever it appears.
TOML_FORBIDDEN = re.compile("[\x00-\x08\x0a-\x1f\x7f\x85\u2028\u2029]")
# TOML's decimal integer (no sign-plus, underscore, or leading-zero forms),
# bounded before int() so no interpreter's digit limit can raise.
TOML_INTEGER = re.compile(r"-?(?:0|[1-9][0-9]{0,18})\Z")
# The tracked ledgers nest arrays at most one level deep; the bound refuses
# deeper values before recursion can exhaust the interpreter stack.
TOML_MAX_ARRAY_DEPTH = 8
REQUIRED = (
    "pinned_upstream_rust_revision",
    "full_upstream_rust_surface",
    "all_reachable_rust_bodies_inventoried",
    "zero_upstream_rust_semantic_regressions",
    "non_applicable_rust_harness_rows_only",
    "owner_pinned_rust_surface_and_accept_reject_parity",
    "rust_frontend_constructor_totality",
    "rust_macro_build_asm_ffi_dynamic_runtime_surface",
)
REQUIRED_FEATURES = {
    "macros", "build_scripts", "inline_asm", "ffi", "dynamic_linking",
    "runtime_startup", "closures", "coroutines", "consts", "statics",
    "intrinsics", "unsafe", "generated_shims",
}
BASELINE_STATUSES = {
    "compatible", "diverged", "missing_local", "missing_upstream", "unknown"
}
RESIDUAL = {
    "full_upstream_rust_surface":
        "a Git test-file list is not the expanded full-suite/tool test population",
    "all_reachable_rust_bodies_inventoried":
        "the subject graph is not an independent source-to-codegen body census",
    "zero_upstream_rust_semantic_regressions":
        "no authenticated full-suite execution and semantic comparison is bound",
    "owner_pinned_rust_surface_and_accept_reject_parity":
        "authored outcomes are not an independent accept/reject parity run",
    "rust_frontend_constructor_totality":
        "no exhaustive rustc frontend constructor inventory or lowering proof is bound",
    "rust_macro_build_asm_ffi_dynamic_runtime_surface":
        "no exhaustive macro/build/asm/FFI/dynamic/runtime closure instrument is bound",
}


class Refusal(Exception):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def no_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise Refusal(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def json_object(data: bytes, label: str) -> dict[str, Any]:
    def refuse_constant(value: str) -> None:
        raise Refusal(f"{label}: non-finite JSON constant {value!r}")

    try:
        _trust_text = data.decode("utf-8")
        if _trust_json_nesting_depth(_trust_text) > TRUST_MAX_JSON_DEPTH:
            raise ValueError(f"JSON nests deeper than {TRUST_MAX_JSON_DEPTH}")
        value = json.loads(_trust_text, object_pairs_hook=no_duplicate_keys,
                           parse_constant=refuse_constant)
    except (UnicodeError, ValueError, RecursionError) as exc:
        raise Refusal(f"{label}: invalid JSON: {exc}") from exc
    if type(value) is not dict:
        raise Refusal(f"{label}: must be a JSON object")
    return value


def exact(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != keys:
        raise Refusal(f"{label}: expected exactly {sorted(keys)}")
    return value


def nonempty(value: Any, label: str) -> str:
    if type(value) is not str or not value:
        raise Refusal(f"{label}: must be a non-empty string")
    return value


def digest(value: Any, label: str) -> str:
    if type(value) is not str or HEX.fullmatch(value) is None:
        raise Refusal(f"{label}: must be a lowercase SHA-256 digest")
    return value


def sorted_unique(values: Any, label: str) -> list[str]:
    if type(values) is not list or any(type(item) is not str or not item for item in values):
        raise Refusal(f"{label}: must be a list of non-empty strings")
    if values != sorted(set(values)):
        raise Refusal(f"{label}: must be sorted and duplicate-free")
    return values


def _strip_comment(line: str) -> str:
    quoted = False
    escaped = False
    for index, char in enumerate(line):
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char == "#":
            return line[:index]
    return line


def _array_items(raw: str) -> list[str]:
    items: list[str] = []
    start = 0
    quoted = False
    escaped = False
    for index, char in enumerate(raw):
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char == ",":
            items.append(raw[start:index].strip())
            start = index + 1
    if quoted:
        raise Refusal("unterminated TOML array string")
    tail = raw[start:].strip()
    if tail:
        items.append(tail)
    if any(not item for item in items):
        raise Refusal("empty TOML array element")
    return items


def _toml_value(raw: str, label: str, depth: int = 0) -> Any:
    if raw.startswith('"') and raw.endswith('"'):
        try:
            value = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise Refusal(f"{label}: unsupported TOML string: {exc}") from exc
        if type(value) is not str:
            raise Refusal(f"{label}: expected TOML string")
        return value
    if raw in ("true", "false"):
        return raw == "true"
    if TOML_INTEGER.fullmatch(raw):
        value = int(raw)
        if not -(2 ** 63) <= value < 2 ** 63:
            raise Refusal(f"{label}: TOML integer outside the 64-bit range")
        return value
    if raw.startswith("[") and raw.endswith("]"):
        if depth >= TOML_MAX_ARRAY_DEPTH:
            raise Refusal(f"{label}: TOML array nesting exceeds {TOML_MAX_ARRAY_DEPTH}")
        return [_toml_value(item, label, depth + 1) for item in _array_items(raw[1:-1])]
    raise Refusal(f"{label}: value outside the supported TOML subset")


def toml_subset(data: bytes, label: str) -> dict[str, Any]:
    """Parse the pinned ledgers' scalar/array/table subset; refuse other syntax.

    Python 3.9 is the fixed runner here and lacks tomllib. Array continuations
    are supported for the real test-exception ledger's allowed_patterns rows.
    Lines end only where TOML ends them, at LF or CRLF; a line that still holds
    a TOML_FORBIDDEN character is refused rather than split differently from
    the canonical toml-crate reader.
    """
    try:
        segments = data.decode("utf-8").split("\n")
    except UnicodeError as exc:
        raise Refusal(f"{label}: invalid UTF-8: {exc}") from exc
    lines: list[str] = []
    for number, segment in enumerate(segments, 1):
        if number < len(segments) and segment.endswith("\r"):
            segment = segment[:-1]
        if TOML_FORBIDDEN.search(segment):
            raise Refusal(
                f"{label}:{number}: control character or non-TOML line break "
                "(TOML ends lines only at LF or CRLF)"
            )
        lines.append(segment)
    doc: dict[str, Any] = {}
    target = doc
    pending = ""
    for number, original in enumerate(lines, 1):
        line = _strip_comment(original).strip()
        if not line:
            continue
        if pending:
            pending += " " + line
            if not pending.rstrip().endswith("]"):
                continue
            line, pending = pending, ""
        elif "=" in line and line.partition("=")[2].strip().startswith("[") and not line.endswith("]"):
            pending = line
            continue
        if line.startswith("[["):
            if not line.endswith("]]") or not KEY.fullmatch(line[2:-2].strip()):
                raise Refusal(f"{label}:{number}: malformed array-of-tables")
            name = line[2:-2].strip()
            rows = doc.setdefault(name, [])
            if type(rows) is not list:
                raise Refusal(f"{label}:{number}: conflicting table {name}")
            target = {}
            rows.append(target)
            continue
        if line.startswith("["):
            if not line.endswith("]"):
                raise Refusal(f"{label}:{number}: malformed table")
            parts = line[1:-1].strip().split(".")
            if not parts or any(not KEY.fullmatch(part) for part in parts):
                raise Refusal(f"{label}:{number}: invalid table name")
            if len(parts) == 1:
                if parts[0] in doc:
                    raise Refusal(f"{label}:{number}: duplicate table")
                target = doc[parts[0]] = {}
            elif len(parts) == 2:
                holder = doc.get(parts[0])
                parent = holder[-1] if type(holder) is list and holder else holder
                if type(parent) is not dict or parts[1] in parent:
                    raise Refusal(f"{label}:{number}: missing parent or duplicate subtable")
                target = parent[parts[1]] = {}
            else:
                raise Refusal(f"{label}:{number}: nested table outside subset")
            continue
        key, sep, value = line.partition("=")
        key = key.strip()
        if not sep or not KEY.fullmatch(key) or key in target:
            raise Refusal(f"{label}:{number}: invalid or duplicate key")
        target[key] = _toml_value(value.strip(), f"{label}:{number}")
    if pending:
        raise Refusal(f"{label}: unterminated TOML array")
    return doc


class Context:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.root = Path(args.root).resolve(strict=True)
        self.revision = nonempty(args.source_revision, "source revision")
        if OID.fullmatch(self.revision) is None:
            raise Refusal("source revision must be a 40- or 64-hex Git commit")
        # --no-replace-objects already bypasses replacements; a repository that
        # carries one is still refused by name rather than silently read around.
        if self.git("for-each-ref", "--format=%(refname)", "refs/replace/").strip():
            raise Refusal("repository carries refs/replace/* object substitutions")
        if self.git("rev-parse", "HEAD").decode().strip() != self.revision:
            raise Refusal("source revision does not equal --root HEAD")
        self._inputs: dict[str, Any] | None = None

    def git(self, *argv: str) -> bytes:
        # The runner's _git_env and GIT_GLOBAL_OPTIONS, repeated here because
        # this checker also runs directly: every caller GIT_* variable is
        # dropped, then the system, global and XDG configuration tiers and the
        # system attributes file are replaced by empty ones, lazy fetching is
        # off (a promisor remote's transport would otherwise start a program
        # the candidate's configuration names on any missing-object read), and
        # core.fsmonitor is overridden on the command line, above every
        # configuration file, so no index read runs a candidate hook.
        env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        env.update(
            GIT_CONFIG_NOSYSTEM="1",
            GIT_CONFIG_GLOBAL=os.devnull,
            GIT_ATTR_NOSYSTEM="1",
            GIT_NO_LAZY_FETCH="1",
            XDG_CONFIG_HOME=os.devnull,
        )
        process = subprocess.run(
            ["git", "--no-replace-objects", "--no-optional-locks",
             "-c", "core.fsmonitor=false", *argv],
            cwd=self.root, capture_output=True, check=False, timeout=30, env=env,
        )
        if process.returncode:
            raise Refusal(f"git {' '.join(argv[:2])} failed: {process.stderr.decode(errors='replace')[:160]}")
        return process.stdout

    def path(self, relative: str) -> Path:
        if type(relative) is not str or not relative or Path(relative).is_absolute():
            raise Refusal("artifact path must be root-relative")
        parts = Path(relative).parts
        if any(part in ("", ".", "..") for part in parts):
            raise Refusal("artifact path has a traversal component")
        candidate = self.root
        for part in parts:
            candidate = candidate / part
            if candidate.is_symlink():
                raise Refusal(f"symlink in artifact path {relative!r}")
        try:
            candidate.resolve(strict=True).relative_to(self.root)
        except (OSError, ValueError) as exc:
            raise Refusal(f"artifact path unavailable or escapes root: {relative!r}") from exc
        if not candidate.is_file():
            raise Refusal(f"artifact is not a regular file: {relative!r}")
        return candidate

    def ref(self, value: Any, label: str) -> tuple[dict[str, str], bytes]:
        ref = exact(value, {"path", "sha256"}, label)
        path = self.path(nonempty(ref["path"], f"{label}.path"))
        wanted = digest(ref["sha256"], f"{label}.sha256")
        data = path.read_bytes()
        if sha256(data) != wanted:
            raise Refusal(f"{label}: SHA-256 mismatch")
        return {"path": ref["path"], "sha256": wanted}, data

    def bound_json(self, path: str, hash_value: str, label: str) -> dict[str, Any]:
        _, data = self.ref({"path": self.relative(path), "sha256": hash_value}, label)
        return json_object(data, label)

    def relative(self, path: str) -> str:
        try:
            return str(Path(path).resolve(strict=True).relative_to(self.root))
        except (OSError, ValueError) as exc:
            raise Refusal("runner input path is outside --root or unavailable") from exc

    def tracked(self, relative: str) -> tuple[dict[str, str], bytes]:
        path = self.path(relative)
        listing = self.git("ls-tree", self.revision, "--", relative).decode().strip()
        if not re.fullmatch(r"100(?:644|755) blob (?:[0-9a-f]{40}|[0-9a-f]{64})\t" + re.escape(relative), listing):
            raise Refusal(f"{relative}: not a regular tracked source-revision blob")
        blob = self.git("show", f"{self.revision}:{relative}")
        if path.read_bytes() != blob:
            raise Refusal(f"{relative}: on-disk bytes differ from accepted revision")
        return {"path": relative, "sha256": sha256(blob)}, blob

    def inputs(self) -> dict[str, Any]:
        if self._inputs is not None:
            return self._inputs
        args = self.args
        policy = self.bound_json(args.authority_policy, args.authority_policy_sha256, "authority policy")
        if (policy.get("schema") != "trust.two-language.authority-policy/v2"
                or policy.get("goal_id") != GOAL
                or policy.get("repository_id") != REPOSITORY_ID
                or policy.get("authorized_source_revision") != self.revision
                or policy.get("authorized_acceptance_run_id") != args.acceptance_run_id):
            raise Refusal("authority policy has wrong schema, repository, source, or run identity")
        contracts = exact(policy.get("contracts"), {
            "admission", "semantics", "obligations", "proof_authority",
            "compatibility_surfaces", "codegen_surface", "acceptance_environment",
        }, "authority policy contracts")
        named = exact(contracts["admission"], {"id", "path", "sha256"}, "admission reference")
        if named["id"] != "trust.two-language.contract.admission":
            raise Refusal("wrong admission contract identity")
        admission_ref, admission_bytes = self.ref(
            {"path": named["path"], "sha256": named["sha256"]}, "admission contract"
        )
        admission = json_object(admission_bytes, "admission contract")
        if (admission.get("schema") != "trust.two-language.admission-contract/v1"
                or admission.get("goal_id") != GOAL or admission.get("repository_id") != REPOSITORY_ID):
            raise Refusal("admission contract has wrong identity")
        lanes = admission.get("lanes")
        lane = exact(lanes, {"rust", "lean", "mixed"}, "admission lanes")["rust"]
        lane = exact(lane, {
            "upstream_repository", "upstream_revision", "upstream_tree_sha256",
            "feature_manifest", "suite_manifest", "exception_ledger", "entries",
        }, "Rust admission lane")
        if lane["upstream_repository"] != "https://github.com/rust-lang/rust":
            raise Refusal("owner Rust upstream repository is not rust-lang/rust")
        upstream = nonempty(lane["upstream_revision"], "owner upstream revision")
        if OID.fullmatch(upstream) is None:
            raise Refusal("owner upstream revision is not a Git commit")
        owner_tree_digest = digest(lane["upstream_tree_sha256"], "owner upstream tree SHA-256")
        entries = lane["entries"]
        if type(entries) is not list or not entries:
            raise Refusal("owner Rust entries must be non-empty")
        by_id: dict[str, dict[str, Any]] = {}
        for row in entries:
            row = exact(row, {"id", "kind", "admitted", "source", "expected_outcome"}, "owner Rust entry")
            name = nonempty(row["id"], "owner Rust entry ID")
            if name in by_id or type(row["admitted"]) is not bool:
                raise Refusal("duplicate Rust entry ID or non-boolean admission")
            if row["expected_outcome"] not in ("accept", "reject"):
                raise Refusal(f"owner entry {name}: unknown expected outcome")
            self.ref(row["source"], f"owner entry {name} source")
            by_id[name] = row
        if not any(row["admitted"] for row in entries):
            raise Refusal("no owner-admitted Rust entry")

        suite_ref, suite_bytes = self.ref(lane["suite_manifest"], "owner Rust suite manifest")
        suite = exact(json_object(suite_bytes, "owner Rust suite manifest"),
                      {"schema", "lane", "cases"}, "owner Rust suite manifest")
        if suite["schema"] != "trust.two-language.suite-manifest/v1" or suite["lane"] != "rust":
            raise Refusal("wrong owner Rust suite schema or lane")
        if sorted_unique(suite["cases"], "owner suite cases") != sorted(by_id):
            raise Refusal("owner suite cases do not biject owner Rust entries")

        feature_ref, feature_bytes = self.ref(lane["feature_manifest"], "owner Rust feature manifest")
        features = exact(json_object(feature_bytes, "owner Rust feature manifest"),
                         {"schema", "lane", "features"}, "owner Rust feature manifest")
        if features["schema"] != "trust.two-language.language-feature-manifest/v1" or features["lane"] != "rust":
            raise Refusal("wrong owner Rust feature schema or lane")
        feature_ids = sorted_unique(features["features"], "owner Rust features")
        if not REQUIRED_FEATURES <= set(feature_ids):
            raise Refusal(f"owner Rust feature manifest omits {sorted(REQUIRED_FEATURES - set(feature_ids))}")

        exception_ref, exception_bytes = self.ref(lane["exception_ledger"], "owner Rust exception ledger")
        exception_doc = exact(json_object(exception_bytes, "owner Rust exception ledger"),
                              {"schema", "lane", "rows"}, "owner Rust exception ledger")
        if exception_doc["schema"] != "trust.two-language.exception-ledger/v1" or exception_doc["lane"] != "rust":
            raise Refusal("wrong owner Rust exception schema or lane")
        rows = exception_doc["rows"]
        if type(rows) is not list:
            raise Refusal("owner Rust exception rows must be a list")
        seen: set[str] = set()
        for row in rows:
            row = exact(row, {"entry_id", "classification", "reason"}, "owner exception row")
            name = nonempty(row["entry_id"], "owner exception entry ID")
            if name in seen or name not in by_id:
                raise Refusal("owner exception row is duplicate or unknown")
            seen.add(name)
            if by_id[name]["admitted"] or row["classification"] != "non-applicable-harness":
                raise Refusal("owner exception waives admitted Rust or is not non-applicable")
            nonempty(row["reason"], "owner exception reason")

        corpus = self.bound_json(args.corpus_manifest, args.corpus_manifest_sha256, "corpus manifest")
        corpus_rust = exact(corpus.get("rust"),
                            {"upstream_revision", "admission_policy_sha256", "entries"}, "corpus Rust lane")
        if (corpus_rust["upstream_revision"] != upstream
                or corpus_rust["admission_policy_sha256"] != admission_ref["sha256"]
                or corpus_rust["entries"] != entries):
            raise Refusal("corpus Rust population differs from owner admission")

        graph = self.bound_json(args.subject_graph, args.subject_graph_sha256, "subject graph")
        programs = graph.get("programs")
        if type(programs) is not list or not programs:
            raise Refusal("subject graph has no programs")
        graph_files: set[str] = set()
        bodies: set[tuple[str, str, str]] = set()
        program_ids: set[str] = set()
        for program in programs:
            if type(program) is not dict:
                raise Refusal("subject graph program is not an object")
            program_id = nonempty(program.get("id"), "program ID")
            if program_id in program_ids:
                raise Refusal("duplicate subject-graph program ID")
            program_ids.add(program_id)
            files = sorted_unique(program.get("admitted_file_ids"), "program admitted files")
            graph_files.update(files)
            body_rows = program.get("bodies")
            if type(body_rows) is not list:
                raise Refusal("program bodies must be a list")
            local_ids: set[str] = set()
            local_identities: set[str] = set()
            for body in body_rows:
                if type(body) is not dict or body.get("language") != "rust":
                    continue
                body_id = nonempty(body.get("id"), "Rust body ID")
                identity = digest(body.get("function_identity_sha256"), "Rust function identity")
                if body_id in local_ids or identity in local_identities:
                    raise Refusal("duplicate Rust body ID or function identity in a program")
                local_ids.add(body_id)
                local_identities.add(identity)
                bodies.add((program_id, body_id, identity))
        admitted = {name for name, row in by_id.items() if row["admitted"]}
        if not admitted <= graph_files:
            raise Refusal(f"subject graph omits owner-admitted Rust entries {sorted(admitted - graph_files)}")
        if not bodies:
            raise Refusal("subject graph records no Rust bodies")

        baseline_ref, baseline_bytes = self.tracked(BASELINE)
        baseline = toml_subset(baseline_bytes, BASELINE)
        if baseline.get("schema_version") != "0.1.0":
            raise Refusal("unknown upstream Rust baseline schema")
        baseline_upstream = exact(baseline.get("upstream"),
                                  {"channel", "revision", "snapshot_date"}, "baseline upstream")
        pin = f"rust-lang/rust:{upstream}"
        if baseline_upstream["revision"] != pin:
            raise Refusal("tracked baseline disagrees with owner Rust upstream revision")
        baseline_entries = baseline.get("entries")
        if type(baseline_entries) is not list or not baseline_entries:
            raise Refusal("baseline has no surface entries")
        status_ids: set[str] = set()
        statuses: list[str] = []
        for entry in baseline_entries:
            if type(entry) is not dict:
                raise Refusal("baseline surface is not a table")
            name = nonempty(entry.get("id"), "baseline surface ID")
            status = nonempty(entry.get("status"), "baseline surface status")
            if name in status_ids or status not in BASELINE_STATUSES:
                raise Refusal("duplicate baseline surface or unknown status")
            status_ids.add(name)
            statuses.append(status)
        version_ref, version_bytes = self.tracked(VERSION)
        version = toml_subset(version_bytes, VERSION)
        alignment = version.get("rust_alignment")
        if type(alignment) is not dict or alignment.get("revision") != pin:
            raise Refusal("release Rust alignment disagrees with pinned baseline")

        # An unavailable pinned commit is a hard stop. The candidate checkout's
        # tests/ files are not a substitute for the upstream tree.
        try:
            object_type = self.git("cat-file", "-t", upstream).strip()
        except Refusal as exc:
            raise Refusal(
                "pinned upstream Rust commit object is unavailable locally; "
                "provide that exact owner-pinned object before computing the test-file "
                "denominator (candidate-tree files are not a substitute)"
            ) from exc
        if object_type != b"commit":
            raise Refusal("pinned upstream Rust object is not a commit")
        # A tree listing, not a declared count, fixes the test-file denominator.
        # The contract's tree digest is SHA-256 over the raw Git tree object,
        # not an authored count or a digest-shaped label.
        tree_oid = self.git("rev-parse", f"{upstream}^{{tree}}").decode().strip()
        if owner_tree_digest != sha256(self.git("cat-file", "tree", tree_oid)):
            raise Refusal("owner upstream tree SHA-256 differs from the pinned Git tree object")
        tree_files = self.git("ls-tree", "-rz", "--name-only", upstream, "--", "tests")
        try:
            test_files = sorted(path.decode("utf-8") for path in tree_files.split(b"\0") if path)
        except UnicodeError as exc:
            raise Refusal("upstream Git tree contains a non-UTF-8 test path") from exc
        if not test_files or any(not path.startswith("tests/") for path in test_files):
            raise Refusal("pinned upstream Git tree has no readable tests/ population")
        if test_files != sorted(set(test_files)):
            raise Refusal("upstream Git test tree has duplicate file paths")

        ledger_ref, ledger_bytes = self.tracked(TEST_EXCEPTIONS)
        ledger = toml_subset(ledger_bytes, TEST_EXCEPTIONS)
        if ledger.get("schema_version") != "0.1.0":
            raise Refusal("unknown upstream Rust test-exception schema")
        ledger_rows = ledger.get("exceptions", [])
        if type(ledger_rows) is not list:
            raise Refusal("test-exception ledger has malformed rows")
        for row in ledger_rows:
            if type(row) is not dict:
                raise Refusal("test-exception row is malformed")
            if row.get("status") == "active":
                raise Refusal(f"active upstream Rust test exception {row.get('id')!r} cannot waive G1")
            # Only a retired row is inert. model.rs ExceptionStatus has no
            # `superseded`, and an `expired` row was never closed out.
            if row.get("status") not in EXCEPTION_STATUSES:
                raise Refusal("unknown upstream Rust test-exception status")
            if row.get("status") == "expired":
                raise Refusal(f"expired upstream Rust test exception {row.get('id')!r} is not retired")

        self._inputs = {
            "upstream": upstream, "entries": by_id, "admitted": admitted,
            "features": feature_ids, "test_files": test_files, "bodies": bodies,
            "statuses": statuses, "baseline_ref": baseline_ref, "version_ref": version_ref,
            "ledger_ref": ledger_ref, "admission_ref": admission_ref,
            "suite_ref": suite_ref, "feature_ref": feature_ref,
            "exception_ref": exception_ref,
        }
        return self._inputs

    def observation(self, raw: bytes) -> None:
        canonical = self.inputs()
        doc = exact(json_object(raw, "Rust observation"), {
            "schema", "source_revision", "upstream_revision", "admitted_entry_ids",
            "upstream_test_files", "reachable_bodies", "suite_results", "features",
            "unmeasured",
        }, "Rust observation")
        if doc["schema"] != OBSERVATION_SCHEMA:
            raise Refusal("unknown Rust observation schema")
        if doc["source_revision"] != self.revision or doc["upstream_revision"] != canonical["upstream"]:
            raise Refusal("Rust observation has wrong source or upstream revision")
        if sorted_unique(doc["admitted_entry_ids"], "observed admitted IDs") != sorted(canonical["admitted"]):
            raise Refusal("observed admitted IDs omit or add owner-admitted cases")
        if sorted_unique(doc["upstream_test_files"], "observed upstream test files") != canonical["test_files"]:
            raise Refusal("observed upstream test files omit or add pinned Git-tree files")
        observed_bodies: set[tuple[str, str, str]] = set()
        body_rows = doc["reachable_bodies"]
        if type(body_rows) is not list:
            raise Refusal("observed Rust bodies must be a list")
        for row in body_rows:
            row = exact(row, {"program_id", "body_id", "function_identity_sha256"}, "observed body")
            identity = (
                nonempty(row["program_id"], "observed program ID"),
                nonempty(row["body_id"], "observed body ID"),
                digest(row["function_identity_sha256"], "observed function identity"),
            )
            if identity in observed_bodies:
                raise Refusal("duplicate observed Rust body")
            observed_bodies.add(identity)
        if observed_bodies != canonical["bodies"]:
            raise Refusal("observed Rust bodies differ from subject-graph rows")
        outcomes: dict[str, str] = {}
        if type(doc["suite_results"]) is not list:
            raise Refusal("suite results must be a list")
        for row in doc["suite_results"]:
            row = exact(row, {"entry_id", "observed_outcome"}, "suite result")
            name = nonempty(row["entry_id"], "suite result entry ID")
            if name in outcomes or name not in canonical["entries"]:
                raise Refusal("duplicate or unknown suite result entry")
            if row["observed_outcome"] not in ("accept", "reject"):
                raise Refusal(f"suite result {name}: unknown or partial outcome")
            if row["observed_outcome"] != canonical["entries"][name]["expected_outcome"]:
                raise Refusal(f"suite result {name}: observed outcome differs from owner expectation")
            outcomes[name] = row["observed_outcome"]
        if set(outcomes) != set(canonical["entries"]):
            raise Refusal("suite results omit owner-authorized entries")
        feature_rows = doc["features"]
        if type(feature_rows) is not list:
            raise Refusal("feature observations must be a list")
        observed_features: set[str] = set()
        for row in feature_rows:
            row = exact(row, {"id", "outcome"}, "feature observation")
            name = nonempty(row["id"], "feature ID")
            if name in observed_features or row["outcome"] != "covered":
                raise Refusal("duplicate, unknown, or partial feature observation")
            observed_features.add(name)
        if observed_features != set(canonical["features"]):
            raise Refusal("feature observations omit or add owner features")
        if doc["unmeasured"] != []:
            raise Refusal("Rust observation discloses unmeasured input surface")


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
    global_ok = True
    cx: Context | None = None
    artifacts: dict[str, Any] = {}
    try:
        if args.receipt is not None or args.prior_gates_root is not None:
            raise Refusal("G1 must not receive G8-only receipt or prior-gates root")
        digest(args.acceptance_run_id, "acceptance run ID")
        if sha256(Path(__file__).read_bytes()) != digest(args.checker_sha256, "checker SHA-256"):
            raise Refusal("checker snapshot SHA-256 differs from runner binding")
        cx = Context(args)
        for path, hash_value, label in (
            (args.toolchain_manifest, args.toolchain_sha256, "toolchain manifest"),
            (args.linked_module, args.linked_module_sha256, "linked module"),
            (args.release_artifact, args.release_artifact_sha256, "release artifact"),
            (args.policy_authorization, args.policy_authorization_sha256, "policy authorization"),
        ):
            cx.ref({"path": cx.relative(path), "sha256": hash_value}, label)
        _, bundle_bytes = cx.ref(
            {"path": cx.relative(args.verify_evidence), "sha256": args.evidence_sha256},
            "G1 evidence bundle",
        )
        bundle = exact(json_object(bundle_bytes, "G1 evidence bundle"),
                       {"schema", "gate", "checker", "artifacts"}, "G1 evidence bundle")
        if (bundle["schema"] != EVIDENCE_SCHEMA or bundle["gate"] != GATE
                or bundle["checker"] != CHECKER):
            raise Refusal("G1 evidence bundle has wrong schema, gate, or checker")
        artifacts = exact(bundle["artifacts"], set(REQUIRED), "G1 evidence artifacts")
    except (OSError, subprocess.TimeoutExpired, Refusal) as exc:
        diagnostics.append(str(exc))
        global_ok = False

    checks: list[dict[str, Any]] = []
    for check_id in REQUIRED:
        row_refs: list[dict[str, str]] = []
        row_ok = False
        try:
            if not global_ok or cx is None:
                raise Refusal("common G1 binding is invalid")
            ref, raw = cx.ref(artifacts[check_id], check_id)
            row_refs.append(ref)
            canonical = cx.inputs()
            if check_id == "pinned_upstream_rust_revision":
                if ref != canonical["baseline_ref"]:
                    raise Refusal("pin evidence must be the tracked upstream Rust baseline")
                row_refs.extend([canonical["version_ref"], canonical["admission_ref"]])
                row_ok = True
            elif check_id == "non_applicable_rust_harness_rows_only":
                if ref != canonical["ledger_ref"]:
                    raise Refusal("exception evidence must be the tracked test-exception ledger")
                row_refs.append(canonical["exception_ref"])
                # The surface-level waiver ledger gets the same class-blind rule:
                # an active row of any class is an unretired waiver.
                surface_ref, surface_bytes = cx.tracked(SURFACE_EXCEPTIONS)
                row_refs.append(surface_ref)
                surface = toml_subset(surface_bytes, SURFACE_EXCEPTIONS)
                if surface.get("schema_version") != "0.1.0":
                    raise Refusal("unknown upstream Rust surface-exception schema")
                surface_rows = surface.get("exceptions", [])
                if type(surface_rows) is not list:
                    raise Refusal("surface-exception ledger has malformed rows")
                for row in surface_rows:
                    if type(row) is not dict:
                        raise Refusal("surface-exception row is malformed")
                    if row.get("status") == "active":
                        raise Refusal(f"active upstream Rust surface exception {row.get('id')!r} cannot waive G1")
                    if row.get("status") not in EXCEPTION_STATUSES:
                        raise Refusal("unknown upstream Rust surface-exception status")
                    if row.get("status") == "expired":
                        raise Refusal(f"expired upstream Rust surface exception {row.get('id')!r} is not retired")
                row_ok = True
            else:
                cx.observation(raw)
                row_refs.extend([
                    canonical["admission_ref"], canonical["suite_ref"],
                    canonical["feature_ref"], canonical["baseline_ref"],
                ])
                if check_id in ("full_upstream_rust_surface", "zero_upstream_rust_semantic_regressions"):
                    if any(status != "compatible" for status in canonical["statuses"]):
                        raise Refusal("upstream Rust baseline contains unknown or non-compatible surfaces")
                raise Refusal(
                    "structural observation is self-authored; " + RESIDUAL[check_id]
                )
        except (OSError, subprocess.TimeoutExpired, Refusal, KeyError) as exc:
            diagnostics.append(f"{check_id}: {exc}")
        checks.append({"id": check_id, "passed": row_ok, "artifacts": row_refs})

    verdict = {
        "schema": VERDICT_SCHEMA, "goal_id": GOAL, "gate": GATE, "checker": CHECKER,
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
        "passed": global_ok and all(row["passed"] for row in checks), "checks": checks,
    }
    print(json.dumps(verdict, sort_keys=True))
    for line in diagnostics:
        print(f"G1: {line}", file=sys.stderr)
    return 0 if verdict["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
