#!/usr/bin/env python3
"""Produce a fail-closed receipt for a pinned hand-authored coverage fixture.

The receipt is deliberately harder to produce than an ordinary benchmark
report.  It is published only after source, tool, compiler-coverage, dump,
analysis, and kernel-scorecard populations all reconcile exactly.  The fixture
is curated synthetic Rust; its legacy ``realcode`` name is an identifier, not
a claim that it is an uncurated sample of downstream projects.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import datetime as dt
import errno
import hashlib
import json
import os
import secrets
import signal
import stat
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "trust.realcode-coverage-evidence.v1"
ATTEMPT_SCHEMA = "trust.realcode-coverage-attempt.v1"
IDENTITY_SCHEMA = "trustc.coverage-function-identities.v1"
PROVENANCE_SCHEMA = "trust.stage-tool-provenance.v2"
PROVE_SCHEMA = "trust.prove-scorecard.v1"
ACCEPTED_PROVENANCE = {"release-ready", "internal-release-ready"}
CORPUS_REL = Path("reports/2026-06-29-honest-real-code-coverage/corpus/realcode.rs")
ANALYZER_REL = Path("reports/2026-06-29-honest-real-code-coverage/analyze.py")
PROVENANCE_VERIFIER_REL = Path("scripts/recreate_bootstrap.py")
CORPUS_CLASSIFICATION = {
    "kind": "curated-hand-authored-synthetic-fixture",
    "selection": "deliberately selected language patterns in one spec-free source file",
    "external_projects_sampled": 0,
    "claim_boundary": (
        "Measures the exact pinned fixture only; it is neither an uncurated nor a "
        "statistically representative sample of downstream Rust projects."
    ),
}
TRANSPORT_PREFIX = "TRUST_JSON:"
COVERAGE_PREFIX = "TRUST_COVERAGE:"
OUTCOMES = ("proved", "failed", "unknown", "timeout", "runtime_checked", "skipped")

# Every current numeric field serialized by trust_clean::prove::ProveScorecard.
# Keep the field inventory explicit: a producer/schema drift must be reviewed,
# not silently accepted as an authoritative measurement.
_SCORECARD_FUNCTION_TALLIES = (
    "inhabited",
    "type_grounded_not_inhabited",
    "not_grounded",
    "faithfulness_certified",
    "faithfulness_full",
    "safety_vc_faithful",
    "safety_vc_faithful_overflow",
    "safety_vc_faithful_usub",
    "safety_vc_faithful_signed_overflow",
    "safety_vc_faithful_bounds",
    "safety_vc_faithful_div",
    "safety_vc_faithful_rem",
    "safety_vc_faithful_negation",
    "safety_vc_faithful_shift",
    "fully_faithful",
    "mirsem_refinement_proven",
    "mirsem_branch_refinement_proven",
    "loop_refinement_proven",
    "loop_total_correct_proven",
    "loop_synth_invariant_proven",
    "nested_loop_proven",
    "break_loop_proven",
    "monotone_nested_proven",
    "fully_faithful_via_trustir",
    "fully_faithful_mirsem_fallback",
)
_SCORECARD_OTHER_TALLIES = (
    "kernel_rejected",
    "declined",
    "total_obligations",
    "postcondition_obligations",
    "safety_obligations",
    "safety_discharged",
    "structural_adts",
    "structural_enums",
    "structural_floats",
    "structural_field_obligations",
    "opaque_struct_obligations",
    "loop_headers_detected",
    "loop_headers_recognized",
    "structural_containers",
)
_SCORECARD_SAFETY_KIND_TALLIES = (
    "safety_vc_faithful_overflow",
    "safety_vc_faithful_usub",
    "safety_vc_faithful_signed_overflow",
    "safety_vc_faithful_bounds",
    "safety_vc_faithful_div",
    "safety_vc_faithful_rem",
    "safety_vc_faithful_negation",
    "safety_vc_faithful_shift",
)


class EvidenceError(RuntimeError):
    """A fail-closed evidence validation error."""


def _reject_constant(value: str) -> None:
    raise EvidenceError(f"non-finite JSON number is forbidden: {value}")


def _reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def strict_json_bytes(data: bytes, label: str) -> Any:
    try:
        text = data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{label} is not UTF-8: {error}") from error
    try:
        return json.loads(
            text,
            object_pairs_hook=_reject_duplicate_pairs,
            parse_constant=_reject_constant,
        )
    except EvidenceError:
        raise
    except json.JSONDecodeError as error:
        raise EvidenceError(f"{label} is malformed JSON: {error}") from error


def strict_json_file(path: Path, label: str) -> Any:
    return strict_json_bytes(path.read_bytes(), label)


def canonical_json_bytes(value: Any) -> bytes:
    try:
        rendered = json.dumps(
            value,
            sort_keys=True,
            indent=2,
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError) as error:
        raise EvidenceError(f"receipt is not strict JSON: {error}") from error
    return (rendered + "\n").encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def regular_file(path: Path, label: str, *, executable: bool = False) -> os.stat_result:
    try:
        info = path.lstat()
    except OSError as error:
        raise EvidenceError(f"cannot inspect {label} at {path}: {error}") from error
    if not stat.S_ISREG(info.st_mode):
        raise EvidenceError(f"{label} must be a regular, non-symlink file: {path}")
    if executable and not os.access(path, os.X_OK):
        raise EvidenceError(f"{label} is not executable: {path}")
    return info


def file_snapshot(path: Path, label: str, *, executable: bool = False) -> dict[str, Any]:
    info = regular_file(path, label, executable=executable)
    return {
        "path": str(path),
        "size": info.st_size,
        "sha256": sha256_file(path),
    }


def require_unchanged(path: Path, before: dict[str, Any], label: str) -> None:
    after = file_snapshot(path, label, executable=label in {"trustc", "targo-trust", "system-git"})
    if after != before:
        raise EvidenceError(f"{label} changed while evidence was being collected")


def nonnegative_int(value: Any, label: str) -> int:
    if type(value) is not int or value < 0:
        raise EvidenceError(f"{label} must be a non-negative integer")
    return value


def nonempty_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise EvidenceError(f"{label} must be a non-empty string")
    return value


def resolve_system_git() -> Path:
    """Select Git only from the fixed OS-owned execution path."""

    for candidate in (Path("/usr/bin/git"), Path("/bin/git")):
        try:
            resolved = candidate.resolve(strict=True)
            regular_file(resolved, "system Git", executable=True)
        except (OSError, EvidenceError):
            continue
        return resolved
    raise EvidenceError("no executable regular Git exists in the fixed system path")


def run_git(repo: Path, git: Path, args: list[str]) -> bytes:
    command = [str(git), "-C", str(repo), *args]
    try:
        with tempfile.TemporaryDirectory(prefix="trust-coverage-git-") as isolated:
            env = _fixed_execution_environment()
            env.update(
                {
                    "HOME": isolated,
                    "TMPDIR": isolated,
                    "TMP": isolated,
                    "TEMP": isolated,
                    "LC_ALL": "C",
                    "LANG": "C",
                    "TZ": "UTC",
                    "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_TERMINAL_PROMPT": "0",
                }
            )
            result = subprocess.run(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=30,
                env=env,
            )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise EvidenceError(f"could not run {' '.join(command)}: {error}") from error
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise EvidenceError(f"{' '.join(command)} failed: {detail}")
    return result.stdout


def clean_head(repo: Path, git: Path) -> str:
    top = Path(run_git(repo, git, ["rev-parse", "--show-toplevel"]).decode().strip()).resolve()
    if top != repo:
        raise EvidenceError(f"--repo-root is not the Git top level: {repo} (top level is {top})")
    head = run_git(repo, git, ["rev-parse", "--verify", "HEAD^{commit}"]).decode().strip()
    if len(head) not in (40, 64) or any(ch not in "0123456789abcdef" for ch in head):
        raise EvidenceError(f"Git returned a non-canonical HEAD: {head!r}")
    status_bytes = run_git(
        repo,
        git,
        ["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none"],
    )
    if status_bytes:
        paths = [entry.decode("utf-8", errors="replace") for entry in status_bytes.split(b"\0") if entry]
        preview = ", ".join(paths[:8])
        raise EvidenceError(f"source tree is not clean at HEAD {head}: {preview}")
    return head


@dataclasses.dataclass(frozen=True)
class Capture:
    label: str
    command: list[str]
    exit_code: int
    stdout: bytes
    stderr: bytes

    def digest_record(self) -> dict[str, Any]:
        return {
            "command": self.command,
            "exit_code": self.exit_code,
            "stdout": {"size": len(self.stdout), "sha256": sha256_bytes(self.stdout)},
            "stderr": {"size": len(self.stderr), "sha256": sha256_bytes(self.stderr)},
        }


def run_capture(
    label: str,
    command: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    scratch: Path,
    timeout: int,
    max_output_bytes: int,
) -> Capture:
    safe_label = "".join(ch if ch.isalnum() else "-" for ch in label)
    stdout_path = scratch / f"{safe_label}.stdout"
    stderr_path = scratch / f"{safe_label}.stderr"
    try:
        with stdout_path.open("xb") as stdout_handle, stderr_path.open("xb") as stderr_handle:
            process = subprocess.Popen(
                command,
                cwd=cwd,
                env=env,
                stdin=subprocess.DEVNULL,
                stdout=stdout_handle,
                stderr=stderr_handle,
                start_new_session=True,
            )
            try:
                exit_code = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired as error:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    process.kill()
                process.wait()
                raise EvidenceError(f"{label} exceeded its {timeout}s timeout") from error
    except EvidenceError:
        raise
    except OSError as error:
        raise EvidenceError(f"could not run {label}: {error}") from error

    for stream, path in (("stdout", stdout_path), ("stderr", stderr_path)):
        size = regular_file(path, f"{label} {stream}").st_size
        if size > max_output_bytes:
            raise EvidenceError(
                f"{label} {stream} is {size} bytes, over the {max_output_bytes}-byte evidence limit"
            )
    return Capture(label, command, exit_code, stdout_path.read_bytes(), stderr_path.read_bytes())


_FIXED_SYSTEM_PATH = "/usr/bin:/bin:/usr/sbin:/sbin"


def _fixed_execution_environment() -> dict[str, str]:
    return {"PATH": _FIXED_SYSTEM_PATH}


def scrubbed_environment(
    trustc: Path, *, isolated_home: Path, temporary_directory: Path
) -> tuple[dict[str, str], dict[str, Any]]:
    """Build a closed execution environment for evidence-producing children.

    In particular, do not carry Python import hooks, compiler search paths, or
    dynamic-loader/preload state across the authority boundary. Merely hashing
    such ambient state would make it reproducible, not trustworthy.
    """

    env = _fixed_execution_environment()
    env.update(
        {
            "HOME": str(isolated_home),
            "TMPDIR": str(temporary_directory),
            "TMP": str(temporary_directory),
            "TEMP": str(temporary_directory),
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
        }
    )

    stage_root = trustc.parent.parent
    library_paths: list[str] = []
    candidates = [stage_root / "lib"]
    rustlib = stage_root / "lib/rustlib"
    if rustlib.is_dir():
        candidates.extend(sorted(path / "lib" for path in rustlib.iterdir() if path.is_dir()))
    for candidate in candidates:
        if candidate.is_dir() and str(candidate) not in library_paths:
            library_paths.append(str(candidate))
    library_var = "DYLD_LIBRARY_PATH" if sys.platform == "darwin" else "LD_LIBRARY_PATH"
    if library_paths:
        env[library_var] = os.pathsep.join(dict.fromkeys(library_paths))

    authority = {name: sha256_bytes(value.encode("utf-8")) for name, value in sorted(env.items())}
    descriptor = {
        "schema": "trust.coverage-environment-authority.v2",
        "value_sha256_by_name": authority,
        "canonical_sha256": sha256_bytes(canonical_json_bytes(authority)),
        "path_policy": "fixed-os-owned-directories",
        "fixed_system_path": _FIXED_SYSTEM_PATH,
        "ambient_allowlist": [],
        "excluded_ambient_names": sorted(os.environ),
        "controlled_names": [
            "PATH",
            "HOME",
            "TMPDIR",
            "TMP",
            "TEMP",
            "LC_ALL",
            "LANG",
            "TZ",
            "PYTHONNOUSERSITE",
            "PYTHONDONTWRITEBYTECODE",
        ],
        "runtime_library_variable": library_var,
        "derived_runtime_library_paths": library_paths,
    }
    return env, descriptor


def parse_identity(capture: Capture, label: str) -> str:
    if capture.exit_code != 0:
        raise EvidenceError(f"{label} identity command exited {capture.exit_code}")
    if capture.stderr:
        raise EvidenceError(f"{label} identity command wrote unexpected stderr")
    try:
        identity = capture.stdout.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{label} identity is not UTF-8: {error}") from error
    if not identity.strip():
        raise EvidenceError(f"{label} identity command returned an empty identity")
    return identity.rstrip("\n")


def sorted_unique_strings(value: Any, label: str) -> list[str]:
    if not isinstance(value, list):
        raise EvidenceError(f"{label} must be a list")
    strings = [nonempty_string(item, f"{label} entry") for item in value]
    if strings != sorted(strings) or len(strings) != len(set(strings)):
        raise EvidenceError(f"{label} must be sorted and duplicate-free")
    return strings


def parse_debug_coverage(stderr: bytes, expected: list[str], label: str) -> dict[str, Any]:
    try:
        text = stderr.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{label} stderr is not UTF-8: {error}") from error
    records: dict[str, str] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if COVERAGE_PREFIX not in line:
            continue
        if not line.startswith(COVERAGE_PREFIX):
            raise EvidenceError(f"{label} contains an embedded/noncanonical TRUST_COVERAGE line")
        payload = line[len(COVERAGE_PREFIX) :].strip()
        if " => " not in payload:
            raise EvidenceError(f"{label} contains a malformed TRUST_COVERAGE line: {line}")
        function, classification = payload.rsplit(" => ", 1)
        if not function or not classification or function in records:
            raise EvidenceError(f"{label} contains an empty or duplicate coverage classification")
        records[function] = classification
    if sorted(records) != expected:
        raise EvidenceError(
            f"{label} debug function population differs from coverage inventory "
            f"(debug={len(records)}, expected={len(expected)})"
        )
    counts = collections.Counter(
        classification.split(":", 1)[0] for classification in records.values()
    )
    return {"records": dict(sorted(records.items())), "classification_counts": dict(sorted(counts.items()))}


def _transport_lines(data: bytes, stream: str, label: str) -> list[dict[str, Any]]:
    try:
        text = data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{label} {stream} is not UTF-8: {error}") from error
    messages: list[dict[str, Any]] = []
    for number, raw in enumerate(text.splitlines(), 1):
        stripped = raw.strip()
        if TRANSPORT_PREFIX not in stripped:
            continue
        if stream != "stderr":
            raise EvidenceError(f"{label} emitted unauthenticated TRUST_JSON on {stream}")
        if not stripped.startswith(TRANSPORT_PREFIX):
            raise EvidenceError(f"{label} has embedded/noncanonical TRUST_JSON at stderr line {number}")
        parsed = strict_json_bytes(
            stripped[len(TRANSPORT_PREFIX) :].encode("utf-8"),
            f"{label} TRUST_JSON stderr line {number}",
        )
        if not isinstance(parsed, dict):
            raise EvidenceError(f"{label} TRUST_JSON line {number} is not an object")
        messages.append(parsed)
    return messages


def parse_transport(capture: Capture, session: str, label: str) -> dict[str, Any]:
    if capture.exit_code != 0:
        raise EvidenceError(f"{label} compiler exited {capture.exit_code}")
    _transport_lines(capture.stdout, "stdout", label)
    messages = _transport_lines(capture.stderr, "stderr", label)
    if not messages:
        raise EvidenceError(f"{label} emitted no TRUST_JSON transport")
    allowed_types = {"function_result", "coverage_summary", "crate_summary"}
    for message in messages:
        if message.get("type") not in allowed_types:
            raise EvidenceError(f"{label} emitted unsupported TRUST_JSON type {message.get('type')!r}")

    coverages = [m for m in messages if m.get("type") == "coverage_summary"]
    summaries = [m for m in messages if m.get("type") == "crate_summary"]
    functions = [m for m in messages if m.get("type") == "function_result"]
    if len(coverages) != 1 or len(summaries) != 1:
        raise EvidenceError(f"{label} requires exactly one coverage_summary and one crate_summary")
    coverage = coverages[0]
    summary = summaries[0]
    for item_label, item in (("coverage_summary", coverage), ("crate_summary", summary)):
        if item.get("crate_name") != "realcode":
            raise EvidenceError(f"{label} {item_label} is not for crate realcode")
        if item.get("verification_session", "") != session:
            raise EvidenceError(f"{label} {item_label} session does not match invocation nonce")

    eligible = nonnegative_int(coverage.get("eligible"), f"{label} eligible")
    processed = nonnegative_int(coverage.get("processed"), f"{label} processed")
    if eligible == 0 or processed != eligible:
        raise EvidenceError(f"{label} coverage incomplete: processed={processed}, eligible={eligible}")
    identities = coverage.get("function_identities")
    if not isinstance(identities, dict) or identities.get("schema") != IDENTITY_SCHEMA:
        raise EvidenceError(f"{label} lacks the exact function-identity inventory")
    eligible_functions = sorted_unique_strings(
        identities.get("eligible_functions"), f"{label} eligible_functions"
    )
    processed_functions = sorted_unique_strings(
        identities.get("processed_functions"), f"{label} processed_functions"
    )
    if len(eligible_functions) != eligible or eligible_functions != processed_functions:
        raise EvidenceError(f"{label} function identities do not prove exact complete coverage")

    by_function: dict[str, dict[str, Any]] = {}
    totals = collections.Counter({outcome: 0 for outcome in OUTCOMES})
    total_obligations = 0
    functions_verified = 0
    for row in functions:
        function = nonempty_string(row.get("function"), f"{label} function_result.function")
        if function in by_function:
            raise EvidenceError(f"{label} repeats function_result for {function}")
        if row.get("crate_name") != "realcode" or row.get("verification_session", "") != session:
            raise EvidenceError(f"{label} function_result identity/session mismatch for {function}")
        results = row.get("results")
        if not isinstance(results, list):
            raise EvidenceError(f"{label} {function} results is not a list")
        observed = collections.Counter({outcome: 0 for outcome in OUTCOMES})
        for index, result in enumerate(results):
            if not isinstance(result, dict):
                raise EvidenceError(f"{label} {function} result {index} is not an object")
            outcome = result.get("outcome")
            if outcome not in OUTCOMES:
                raise EvidenceError(f"{label} {function} has invalid outcome {outcome!r}")
            nonempty_string(result.get("kind"), f"{label} {function} result.kind")
            if not isinstance(result.get("description"), str):
                raise EvidenceError(f"{label} {function} result.description must be a string")
            observed[outcome] += 1
            totals[outcome] += 1
        expected_counts = {
            "proved": observed["proved"],
            "failed": observed["failed"],
            "unknown": observed["unknown"] + observed["timeout"] + observed["skipped"],
            "timed_out": observed["timeout"],
            "skipped": observed["skipped"],
            "runtime_checked": observed["runtime_checked"],
            "total": len(results),
        }
        for key, expected in expected_counts.items():
            if nonnegative_int(row.get(key, 0), f"{label} {function}.{key}") != expected:
                raise EvidenceError(f"{label} {function} transport count {key} is inconsistent")
        cached = nonnegative_int(row.get("cached", 0), f"{label} {function}.cached")
        if cached > len(results):
            raise EvidenceError(f"{label} {function}.cached exceeds its obligation population")
        if results and observed["proved"] == len(results):
            functions_verified += 1
        total_obligations += len(results)
        by_function[function] = row

    if sorted(by_function) != processed_functions:
        raise EvidenceError(
            f"{label} function_result population differs from coverage inventory "
            f"(rows={len(by_function)}, inventory={len(processed_functions)})"
        )
    expected_summary = {
        "functions_analyzed": len(by_function),
        "functions_verified": functions_verified,
        "total_proved": totals["proved"],
        "total_failed": totals["failed"],
        "total_unknown": totals["unknown"] + totals["timeout"] + totals["skipped"],
        "total_timed_out": totals["timeout"],
        "total_skipped": totals["skipped"],
        "total_runtime_checked": totals["runtime_checked"],
        "total_obligations": total_obligations,
    }
    for key, expected in expected_summary.items():
        if nonnegative_int(summary.get(key, 0), f"{label} crate_summary.{key}") != expected:
            raise EvidenceError(f"{label} crate_summary {key} is inconsistent")

    return {
        "coverage_complete": True,
        "eligible": eligible,
        "processed": processed,
        "function_identities": eligible_functions,
        "outcome_counts": {
            "proved": totals["proved"],
            "failed": totals["failed"],
            "unknown": totals["unknown"],
            "timed_out": totals["timeout"],
            "skipped": totals["skipped"],
            "runtime_checked": totals["runtime_checked"],
            "total": total_obligations,
        },
        "function_results": [by_function[name] for name in sorted(by_function)],
        "crate_summary": summary,
        "coverage_summary": coverage,
    }


def validate_dumps(dump_dir: Path, expected_functions: list[str]) -> dict[str, Any]:
    try:
        entries = sorted(dump_dir.iterdir(), key=lambda path: path.name)
    except OSError as error:
        raise EvidenceError(f"cannot enumerate compiler dump directory: {error}") from error
    if not entries:
        raise EvidenceError("compiler produced no VerifiableFunction dumps")
    manifest: list[dict[str, Any]] = []
    def_paths: list[str] = []
    for path in entries:
        if path.suffix != ".json":
            raise EvidenceError(f"unexpected non-JSON entry in dump directory: {path.name}")
        info = regular_file(path, f"dump {path.name}")
        value = strict_json_file(path, f"dump {path.name}")
        if not isinstance(value, dict):
            raise EvidenceError(f"dump {path.name} is not a JSON object")
        def_path = nonempty_string(value.get("def_path"), f"dump {path.name}.def_path")
        if not isinstance(value.get("body"), dict):
            raise EvidenceError(f"dump {path.name} has no MIR body object")
        def_paths.append(def_path)
        manifest.append(
            {"file": path.name, "def_path": def_path, "size": info.st_size, "sha256": sha256_file(path)}
        )
    if len(def_paths) != len(set(def_paths)):
        raise EvidenceError("compiler dumps contain duplicate def_path identities")
    if sorted(def_paths) != expected_functions:
        raise EvidenceError(
            f"dump population differs from exact eligible coverage population "
            f"(dumps={len(def_paths)}, eligible={len(expected_functions)})"
        )
    return {
        "count": len(manifest),
        "manifest": manifest,
        "manifest_sha256": sha256_bytes(canonical_json_bytes(manifest)),
    }


def validate_analysis(value: Any, expected_functions: list[str]) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise EvidenceError("analyze.py output is not a JSON object")
    population = len(expected_functions)
    if nonnegative_int(value.get("n_functions"), "analysis.n_functions") != population:
        raise EvidenceError("analyze.py function denominator differs from compiler coverage")
    for key in ("type_coverage", "func_type_coverage", "loop_coverage"):
        if not isinstance(value.get(key), dict):
            raise EvidenceError(f"analysis is missing {key}")
    types = value["type_coverage"]
    if types.get("method") != "report-local-syntactic-ty-constructor-count.v1":
        raise EvidenceError("analysis type metric lacks its secondary syntactic claim boundary")
    total_types = nonnegative_int(types.get("total_ty_nodes"), "analysis total_ty_nodes")
    structural = nonnegative_int(types.get("structural_nodes"), "analysis structural_nodes")
    failclosed = nonnegative_int(types.get("failclosed_nodes"), "analysis failclosed_nodes")
    if structural + failclosed != total_types:
        raise EvidenceError("analysis type denominator is internally inconsistent")
    func_types = value["func_type_coverage"]
    if nonnegative_int(
        func_types.get("func_with_only_structural_types"), "analysis structural functions"
    ) > population:
        raise EvidenceError("analysis structural function count exceeds population")
    loops = value["loop_coverage"]
    if loops.get("method") != "report-local-mir-shape-heuristic.v1":
        raise EvidenceError("analysis loop metric lacks its report-local heuristic boundary")
    if nonnegative_int(loops.get("n_functions_with_loops"), "analysis loop functions") > population:
        raise EvidenceError("analysis loop function count exceeds population")
    headers = nonnegative_int(loops.get("total_loop_headers"), "analysis loop headers")
    by_kind = loops.get("by_kind")
    if not isinstance(by_kind, dict) or any(
        not isinstance(key, str) or type(count) is not int or count < 0 for key, count in by_kind.items()
    ):
        raise EvidenceError("analysis loop by_kind is malformed")
    if sum(by_kind.values()) != headers:
        raise EvidenceError("analysis loop denominator is internally inconsistent")
    per_func = value.get("per_func")
    if not isinstance(per_func, list) or len(per_func) != population:
        raise EvidenceError("analysis per_func denominator differs from compiler coverage")
    analysis_functions: list[str] = []
    for index, row in enumerate(per_func):
        if not isinstance(row, dict):
            raise EvidenceError(f"analysis per_func row {index} is not an object")
        analysis_functions.append(
            nonempty_string(row.get("def_path"), f"analysis per_func row {index}.def_path")
        )
    if len(analysis_functions) != len(set(analysis_functions)):
        raise EvidenceError("analysis per_func contains duplicate function identities")
    if sorted(analysis_functions) != expected_functions:
        raise EvidenceError("analysis per_func population differs from exact compiler coverage")
    return value


def validate_proof_population(value: Any, population: int, budget: int) -> dict[str, Any]:
    if not isinstance(value, dict) or value.get("schema") != PROVE_SCHEMA:
        raise EvidenceError("prove output does not use trust.prove-scorecard.v1")
    if value.get("status") not in {"measured", "rejected"}:
        raise EvidenceError("prove output status is neither measured nor rejected")
    if value.get("budget_secs_per_function") != budget:
        raise EvidenceError("prove output budget differs from requested budget")
    scorecard = value.get("scorecard")
    if not isinstance(scorecard, dict):
        raise EvidenceError("prove output has no scorecard object")
    total = nonnegative_int(scorecard.get("total"), "prove scorecard.total")
    if total != population:
        raise EvidenceError("prove scorecard denominator differs from compiler coverage")

    tallies = {
        key: nonnegative_int(scorecard.get(key), f"prove scorecard.{key}")
        for key in (*_SCORECARD_FUNCTION_TALLIES, *_SCORECARD_OTHER_TALLIES)
    }
    declined = tallies["declined"]
    if declined > total:
        raise EvidenceError("prove scorecard declined count exceeds its function population")
    processed = total - declined
    oversized_function_tallies = sorted(
        key for key in _SCORECARD_FUNCTION_TALLIES if tallies[key] > processed
    )
    if oversized_function_tallies:
        raise EvidenceError(
            "prove scorecard one-per-function tallies exceed its non-declined population: "
            + ", ".join(oversized_function_tallies)
        )
    categorized = (
        tallies["inhabited"]
        + tallies["type_grounded_not_inhabited"]
        + tallies["not_grounded"]
    )
    if categorized > processed:
        raise EvidenceError("prove scorecard function outcome categories overlap or exceed population")

    proven = scorecard.get("proven")
    if not isinstance(proven, list) or any(not isinstance(item, str) or not item for item in proven):
        raise EvidenceError("prove scorecard proven is not a non-empty string list")
    if len(proven) != tallies["inhabited"]:
        raise EvidenceError("prove scorecard proven paths do not match inhabited tally")
    declined_paths = scorecard.get("declined_paths")
    if not isinstance(declined_paths, list) or any(
        not isinstance(item, str) or not item for item in declined_paths
    ):
        raise EvidenceError("prove scorecard declined_paths is not a non-empty string list")
    if len(declined_paths) != declined:
        raise EvidenceError("prove scorecard declined paths do not match declined tally")

    rejections = scorecard.get("rejections")
    if not isinstance(rejections, list) or any(not isinstance(item, str) for item in rejections):
        raise EvidenceError("kernel scorecard rejections is not a string list")
    if len(rejections) != tallies["kernel_rejected"]:
        raise EvidenceError("prove scorecard rejection records do not match kernel_rejected tally")

    if tallies["total_obligations"] != (
        tallies["postcondition_obligations"] + tallies["safety_obligations"]
    ):
        raise EvidenceError("prove scorecard obligation partition is inconsistent")
    if tallies["safety_discharged"] > tallies["safety_obligations"]:
        raise EvidenceError("prove scorecard discharges more safety obligations than it reports")
    if (
        tallies["structural_field_obligations"] + tallies["opaque_struct_obligations"]
        > tallies["safety_obligations"]
    ):
        raise EvidenceError("prove scorecard struct-field obligation tallies exceed safety scope")

    if tallies["structural_enums"] > tallies["structural_adts"]:
        raise EvidenceError("prove scorecard structural enum tally exceeds structural ADTs")
    if tallies["structural_floats"] > tallies["structural_adts"]:
        raise EvidenceError("prove scorecard structural float tally exceeds structural ADTs")
    if tallies["loop_headers_recognized"] > tallies["loop_headers_detected"]:
        raise EvidenceError("prove scorecard recognizes more loop headers than it detected")
    if tallies["loop_total_correct_proven"] > tallies["loop_refinement_proven"]:
        raise EvidenceError("prove scorecard total-correct loop tally exceeds partial loop tally")
    if tallies["fully_faithful"] != (
        tallies["fully_faithful_via_trustir"]
        + tallies["fully_faithful_mirsem_fallback"]
    ):
        raise EvidenceError("prove scorecard fully-faithful lane partition is inconsistent")
    oversized_safety_kinds = sorted(
        key
        for key in _SCORECARD_SAFETY_KIND_TALLIES
        if tallies[key] > tallies["safety_vc_faithful"]
    )
    if oversized_safety_kinds:
        raise EvidenceError(
            "prove scorecard safety-kind tallies exceed safety_vc_faithful: "
            + ", ".join(oversized_safety_kinds)
        )
    return value


def validate_proof(value: Any, population: int, budget: int) -> dict[str, Any]:
    value = validate_proof_population(value, population, budget)
    if value.get("status") != "measured" or value.get("bridge_gate_error") is not None:
        raise EvidenceError("prove output is not an accepted measured kernel scorecard")
    scorecard = value["scorecard"]
    if not isinstance(scorecard.get("bridge_agreement"), dict):
        raise EvidenceError("measured prove scorecard has no attached bridge agreement evidence")
    if scorecard["kernel_rejected"] != 0:
        raise EvidenceError("kernel scorecard contains a kernel rejection")
    if scorecard.get("rejections", []):
        raise EvidenceError("kernel scorecard contains rejection records")
    return value


def validate_provenance(
    value: Any,
    *,
    repo: Path,
    head: str,
    trustc: Path,
    trustc_sha: str,
    trustc_identity: str,
    targo: Path,
    targo_sha: str,
) -> dict[str, Any]:
    if not isinstance(value, dict) or value.get("schema") != PROVENANCE_SCHEMA:
        raise EvidenceError("stage2 provenance does not use trust.stage-tool-provenance.v2")
    if value.get("status") not in ACCEPTED_PROVENANCE:
        raise EvidenceError(f"stage2 provenance status is not accepted: {value.get('status')!r}")
    if value.get("stage") != 2 or value.get("source_tree_clean") is not True:
        raise EvidenceError("stage2 provenance is not a clean stage-2 receipt")
    if value.get("tool_binding_status") != "ready" or value.get("errors") != []:
        raise EvidenceError("stage2 provenance tool bindings are not ready/error-free")
    host = nonempty_string(value.get("host"), "stage2 provenance host")
    if value.get("path_scope") != "repository-root-relative":
        raise EvidenceError("stage2 provenance path scope is not repository-root-relative")
    bootstrap = value.get("bootstrap_lineage")
    if not isinstance(bootstrap, dict) or bootstrap.get("status") != "trust_from_trust":
        raise EvidenceError("accepted stage2 provenance is not Trust-from-Trust")
    lineage = value.get("source_lineage")
    if (
        not isinstance(lineage, dict)
        or lineage.get("errors") != []
        or lineage.get("stable_across_build") is not True
        or lineage.get("source_tree_clean") is not True
    ):
        raise EvidenceError("stage2 provenance source lineage is not clean and stable")
    repositories = lineage.get("repositories")
    if not isinstance(repositories, list):
        raise EvidenceError("stage2 provenance has no source repository inventory")
    root_rows = [row for row in repositories if isinstance(row, dict) and row.get("path") == "."]
    if len(root_rows) != 1 or root_rows[0].get("head") != head:
        raise EvidenceError("stage2 provenance does not bind the clean Git HEAD")

    compiler = value.get("compiler")
    if not isinstance(compiler, dict):
        raise EvidenceError("stage2 provenance has no compiler binding")
    expected_trustc_rel = str(trustc.relative_to(repo))
    if (
        compiler.get("path") != expected_trustc_rel
        or compiler.get("compiler_sha256") != trustc_sha
        or compiler.get("source_commit") != head
        or compiler.get("compiler_verbose") != trustc_identity
    ):
        raise EvidenceError("stage2 provenance compiler identity/SHA/source binding differs")

    tools = value.get("tools")
    if not isinstance(tools, list):
        raise EvidenceError("stage2 provenance has no tool inventory")
    targo_rows = [row for row in tools if isinstance(row, dict) and row.get("name") == "targo-trust"]
    expected_targo_rel = str(targo.relative_to(repo))
    if len(targo_rows) != 1 or (
        targo_rows[0].get("path") != expected_targo_rel
        or targo_rows[0].get("sha256") != targo_sha
        or targo_rows[0].get("status") != "bound"
    ):
        raise EvidenceError("stage2 provenance targo-trust SHA/path binding differs")
    return {"status": value["status"], "host": host}


def _secure_directory_flags() -> int:
    required = ("O_DIRECTORY", "O_NOFOLLOW")
    missing = [name for name in required if not hasattr(os, name)]
    dir_fd_functions = (os.open, os.mkdir, os.stat, os.unlink, os.rename)
    unsupported = [
        function.__name__
        for function in dir_fd_functions
        if function not in os.supports_dir_fd
    ]
    if missing or unsupported:
        detail = ", ".join(missing + unsupported)
        raise EvidenceError(f"secure receipt publication is unavailable: missing {detail}")
    return os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


def _open_secure_parent(path: Path, *, create: bool) -> tuple[Path, int | None]:
    """Open the lexical parent through no-follow directory descriptors."""

    absolute = Path(os.path.abspath(os.fspath(path)))
    if not absolute.name:
        raise EvidenceError("output receipt must name a file")
    if not absolute.anchor:
        raise EvidenceError(f"output receipt has no absolute anchor: {absolute}")
    flags = _secure_directory_flags()
    directory_fd = os.open(absolute.anchor, flags)
    try:
        for component in absolute.parent.parts[1:]:
            try:
                next_fd = os.open(component, flags, dir_fd=directory_fd)
            except FileNotFoundError:
                if not create:
                    os.close(directory_fd)
                    return absolute, None
                try:
                    os.mkdir(component, 0o755, dir_fd=directory_fd)
                except FileExistsError:
                    pass
                try:
                    next_fd = os.open(component, flags, dir_fd=directory_fd)
                except OSError as error:
                    raise EvidenceError(
                        "output receipt parent component is not a real directory: "
                        f"{absolute.parent} ({error})"
                    ) from error
            except OSError as error:
                if error.errno in {errno.ELOOP, errno.ENOTDIR}:
                    raise EvidenceError(
                        "output receipt parent component is a symlink or not a "
                        f"directory: {absolute.parent}"
                    ) from error
                raise
            os.close(directory_fd)
            directory_fd = next_fd
        return absolute, directory_fd
    except BaseException:
        os.close(directory_fd)
        raise


def _snapshot_at(directory_fd: int, filename: str, display: Path) -> dict[str, Any] | None:
    try:
        entry = os.stat(filename, dir_fd=directory_fd, follow_symlinks=False)
    except FileNotFoundError:
        return None
    if not stat.S_ISREG(entry.st_mode):
        raise EvidenceError(
            f"existing output receipt must be a regular, non-symlink file: {display}"
        )
    try:
        descriptor = os.open(filename, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory_fd)
    except OSError as error:
        raise EvidenceError(f"cannot securely open output receipt {display}: {error}") from error
    digest = hashlib.sha256()
    with os.fdopen(descriptor, "rb") as handle:
        before = os.fstat(handle.fileno())
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
        after = os.fstat(handle.fileno())
    stable_fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    if any(getattr(before, field) != getattr(after, field) for field in stable_fields):
        raise EvidenceError(f"output receipt changed while it was being inspected: {display}")
    current = os.stat(filename, dir_fd=directory_fd, follow_symlinks=False)
    if not stat.S_ISREG(current.st_mode) or any(
        getattr(after, field) != getattr(current, field) for field in stable_fields
    ):
        raise EvidenceError(f"output receipt changed while it was being inspected: {display}")
    return {
        "device": after.st_dev,
        "inode": after.st_ino,
        "size": after.st_size,
        "sha256": digest.hexdigest(),
    }


def output_snapshot(path: Path) -> dict[str, Any] | None:
    absolute, directory_fd = _open_secure_parent(path, create=False)
    if directory_fd is None:
        return None
    try:
        return _snapshot_at(directory_fd, absolute.name, absolute)
    finally:
        os.close(directory_fd)


def require_safe_parent_components(path: Path) -> None:
    """Reject a lexical output path that traverses a symlink/non-directory."""

    if not path.is_absolute():
        raise EvidenceError("output receipt safety check requires an absolute path")
    current = Path(path.anchor)
    for part in path.parent.parts[1:]:
        current /= part
        try:
            info = current.lstat()
        except FileNotFoundError:
            continue
        except OSError as error:
            raise EvidenceError(f"cannot inspect output parent component {current}: {error}") from error
        if stat.S_ISLNK(info.st_mode):
            raise EvidenceError(f"output receipt parent component is a symlink: {current}")
        if not stat.S_ISDIR(info.st_mode):
            raise EvidenceError(f"output receipt parent component is not a directory: {current}")


def atomic_publish(path: Path, data: bytes, expected_previous: dict[str, Any] | None) -> None:
    if not path.is_absolute() or not path.name:
        raise EvidenceError("output receipt must be an absolute path naming a file")
    absolute, directory_fd = _open_secure_parent(path, create=True)
    assert directory_fd is not None
    temporary: str | None = None
    try:
        if _snapshot_at(directory_fd, absolute.name, absolute) != expected_previous:
            raise EvidenceError("output receipt changed concurrently; refusing to overwrite it")
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
        for _attempt in range(100):
            candidate = f".{absolute.name}.{secrets.token_hex(16)}.tmp"
            try:
                descriptor = os.open(candidate, flags, 0o600, dir_fd=directory_fd)
            except FileExistsError:
                continue
            temporary = candidate
            break
        if temporary is None:
            raise EvidenceError("could not allocate a unique same-directory receipt temporary")
        try:
            with os.fdopen(descriptor, "wb") as handle:
                os.fchmod(handle.fileno(), 0o644)
                handle.write(data)
                handle.flush()
                os.fsync(handle.fileno())
        except BaseException:
            try:
                os.close(descriptor)
            except OSError:
                pass
            raise
        if _snapshot_at(directory_fd, absolute.name, absolute) != expected_previous:
            raise EvidenceError("output receipt changed concurrently; refusing to overwrite it")
        os.replace(
            temporary,
            absolute.name,
            src_dir_fd=directory_fd,
            dst_dir_fd=directory_fd,
        )
        temporary = None
        os.fsync(directory_fd)
    finally:
        if temporary is not None:
            try:
                os.unlink(temporary, dir_fd=directory_fd)
            except FileNotFoundError:
                pass
        os.close(directory_fd)


def validate_receipt(receipt: dict[str, Any]) -> None:
    if receipt.get("schema") != SCHEMA or receipt.get("status") != "measured":
        raise EvidenceError("internal receipt schema/status validation failed")
    population = receipt.get("population")
    if not isinstance(population, dict):
        raise EvidenceError("internal receipt population is missing")
    eligible = nonnegative_int(population.get("eligible"), "receipt population.eligible")
    if eligible == 0 or population.get("processed") != eligible or population.get("coverage_complete") is not True:
        raise EvidenceError("internal receipt coverage is incomplete")
    if population.get("dump_count") != eligible:
        raise EvidenceError("internal receipt dump denominator differs")
    if receipt.get("analysis", {}).get("n_functions") != eligible:
        raise EvidenceError("internal receipt analysis denominator differs")
    if receipt.get("proof", {}).get("scorecard", {}).get("total") != eligible:
        raise EvidenceError("internal receipt proof denominator differs")
    if receipt.get("corpus_classification") != CORPUS_CLASSIFICATION:
        raise EvidenceError("internal receipt corpus classification is missing or misleading")


def resolve_tools(repo: Path, trustc_arg: str | None, targo_arg: str | None) -> tuple[Path, Path]:
    if trustc_arg:
        trustc = Path(trustc_arg).expanduser().resolve()
    else:
        candidates = [
            path.resolve()
            for path in sorted((repo / "build").glob("*/stage2/bin/trustc"))
            if path.is_file() and os.access(path, os.X_OK)
        ]
        if len(candidates) != 1:
            raise EvidenceError(
                "could not select exactly one stage2 trustc; pass --trustc explicitly "
                f"(found {len(candidates)})"
            )
        trustc = candidates[0]
    targo = Path(targo_arg).expanduser().resolve() if targo_arg else trustc.parent / "targo-trust"
    regular_file(trustc, "trustc", executable=True)
    regular_file(targo, "targo-trust", executable=True)
    try:
        trustc.relative_to(repo)
        targo.relative_to(repo)
    except ValueError as error:
        raise EvidenceError("trustc and targo-trust must be repository-local stage2 tools") from error
    if trustc.parent.parent.name != "stage2" or targo.parent != trustc.parent:
        raise EvidenceError("trustc and targo-trust must be sibling binaries in one stage2 sysroot")
    return trustc, targo


def compile_command(
    trustc: Path,
    corpus: Path,
    output: Path,
    session: str,
    *,
    dump_dir: Path | None,
) -> list[str]:
    command = [
        str(trustc),
        "--crate-name",
        "realcode",
        "--edition",
        "2021",
        "--crate-type",
        "lib",
        "--emit=metadata",
        "-Coverflow-checks=yes",
        "-Cdebug-assertions=yes",
        "-Ccodegen-units=1",
        "-Ztrust-policy=advisory",
        "-Ztrust-verify-output=json",
    ]
    if dump_dir is not None:
        # Current trustc deliberately rejects an authenticated session nonce in
        # compiler early-exit modes. Dump-only is therefore an unscoped,
        # receipt-bound extraction; the separate non-early-exit survey below
        # carries the fresh session nonce.
        command.extend([f"-Ztrust-dump=mir-only:{dump_dir}"])
    else:
        command.append(f"-Ztrust-verify-session={session}")
    command.extend(["-o", str(output), str(corpus)])
    return command


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".", help="clean Trust Git checkout (default: cwd)")
    parser.add_argument("--trustc", help="repository-local stage2 trustc (auto-selected if unique)")
    parser.add_argument("--targo-trust", help="stage2 targo-trust (default: sibling of trustc)")
    parser.add_argument("--provenance", help="stage2 tool-provenance.json (default: selected sysroot)")
    parser.add_argument("--output", required=True, help="JSON receipt to atomically publish")
    parser.add_argument(
        "--diagnostic-output",
        help="rejected complete-attempt JSON (default: OUTPUT.last-attempt.json)",
    )
    parser.add_argument("--prove-budget-secs", type=int, default=30)
    parser.add_argument("--compile-timeout-secs", type=int, default=3600)
    parser.add_argument("--prove-timeout-secs", type=int, default=0, help="0 derives from corpus size")
    parser.add_argument("--provenance-timeout-secs", type=int, default=600)
    parser.add_argument("--max-output-bytes", type=int, default=128 * 1024 * 1024)
    parsed = parser.parse_args(argv)
    for name in (
        "prove_budget_secs",
        "compile_timeout_secs",
        "provenance_timeout_secs",
        "max_output_bytes",
    ):
        if getattr(parsed, name) <= 0:
            parser.error(f"--{name.replace('_', '-')} must be positive")
    if parsed.prove_timeout_secs < 0:
        parser.error("--prove-timeout-secs must be non-negative")
    return parsed


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo = Path(args.repo_root).expanduser().resolve()
    # Keep the lexical absolute path. Path.resolve() would hide parent symlinks
    # before the publication boundary can reject them.
    output = Path(os.path.abspath(Path(args.output).expanduser()))
    diagnostic_output = Path(
        os.path.abspath(
            Path(args.diagnostic_output).expanduser()
            if args.diagnostic_output
            else output.with_name(output.name + ".last-attempt.json")
        )
    )
    if diagnostic_output == output:
        raise EvidenceError("--diagnostic-output must differ from --output")
    require_safe_parent_components(output)
    require_safe_parent_components(diagnostic_output)
    previous_output = output_snapshot(output)
    previous_diagnostic_output = output_snapshot(diagnostic_output)
    system_git = resolve_system_git()
    system_git_snapshot = file_snapshot(system_git, "system Git", executable=True)
    head = clean_head(repo, system_git)
    trustc, targo = resolve_tools(repo, args.trustc, args.targo_trust)
    provenance = (
        Path(args.provenance).expanduser().resolve()
        if args.provenance
        else trustc.parent.parent / "tool-provenance.json"
    )
    corpus = repo / CORPUS_REL
    analyzer = repo / ANALYZER_REL
    provenance_verifier = repo / PROVENANCE_VERIFIER_REL
    script = Path(__file__).resolve()

    source_files = {
        "corpus": (corpus, file_snapshot(corpus, "coverage corpus")),
        "analyzer": (analyzer, file_snapshot(analyzer, "coverage analyzer")),
        "provenance_verifier": (
            provenance_verifier,
            file_snapshot(provenance_verifier, "stage provenance verifier"),
        ),
        "evidence_command": (script, file_snapshot(script, "coverage evidence command")),
    }
    tool_files = {
        "trustc": (trustc, file_snapshot(trustc, "trustc", executable=True)),
        "targo-trust": (targo, file_snapshot(targo, "targo-trust", executable=True)),
        "system-git": (system_git, system_git_snapshot),
    }
    provenance_before = file_snapshot(provenance, "stage2 provenance")
    provenance_value = strict_json_file(provenance, "stage2 provenance")
    with tempfile.TemporaryDirectory(prefix="trust-realcode-coverage-") as temporary:
        scratch = Path(temporary)
        isolated_home = scratch / "home"
        execution_tmp = scratch / "tmp"
        isolated_home.mkdir(mode=0o700)
        execution_tmp.mkdir(mode=0o700)
        env, environment_authority = scrubbed_environment(
            trustc,
            isolated_home=isolated_home,
            temporary_directory=execution_tmp,
        )
        environment_authority["system_tools"] = {"git": system_git_snapshot}
        identity_trustc = run_capture(
            "trustc-identity",
            [str(trustc), "-vV"],
            cwd=repo,
            env=env,
            scratch=scratch,
            timeout=30,
            max_output_bytes=args.max_output_bytes,
        )
        identity_targo = run_capture(
            "targo-identity",
            [str(targo), "--version"],
            cwd=repo,
            env=env,
            scratch=scratch,
            timeout=30,
            max_output_bytes=args.max_output_bytes,
        )
        trustc_identity = parse_identity(identity_trustc, "trustc")
        targo_identity = parse_identity(identity_targo, "targo-trust")
        provenance_metadata = validate_provenance(
            provenance_value,
            repo=repo,
            head=head,
            trustc=trustc,
            trustc_sha=tool_files["trustc"][1]["sha256"],
            trustc_identity=trustc_identity,
            targo=targo,
            targo_sha=tool_files["targo-trust"][1]["sha256"],
        )

        provenance_command = [
            sys.executable,
            str(provenance_verifier),
            "--verify-stage-provenance",
            "--stage",
            "2",
            "--host",
            provenance_metadata["host"],
            "--require-immutable-lineage",
        ]
        provenance_check_before = run_capture(
            "provenance-before",
            provenance_command,
            cwd=repo,
            env=env,
            scratch=scratch,
            timeout=args.provenance_timeout_secs,
            max_output_bytes=args.max_output_bytes,
        )
        if provenance_check_before.exit_code != 0:
            raise EvidenceError("canonical stage2 provenance verification failed before measurement")

        dump_dir = scratch / "dump"
        dump_dir.mkdir()
        extract_session = ""
        compile_env = dict(env)
        compile_env["TRUST_COVERAGE_DEBUG"] = "1"
        extraction = run_capture(
            "extract",
            compile_command(
                trustc,
                corpus,
                scratch / "extract.rmeta",
                extract_session,
                dump_dir=dump_dir,
            ),
            cwd=repo,
            env=compile_env,
            scratch=scratch,
            timeout=args.compile_timeout_secs,
            max_output_bytes=args.max_output_bytes,
        )
        extraction_transport = parse_transport(extraction, extract_session, "extraction")
        extraction_debug = parse_debug_coverage(
            extraction.stderr, extraction_transport["function_identities"], "extraction"
        )
        dumps = validate_dumps(dump_dir, extraction_transport["function_identities"])

        survey_session = f"realcode-survey-{secrets.token_hex(16)}"
        survey_capture = run_capture(
            "survey",
            compile_command(
                trustc,
                corpus,
                scratch / "survey.rmeta",
                survey_session,
                dump_dir=None,
            ),
            cwd=repo,
            env=compile_env,
            scratch=scratch,
            timeout=args.compile_timeout_secs,
            max_output_bytes=args.max_output_bytes,
        )
        survey = parse_transport(survey_capture, survey_session, "survey")
        survey_debug = parse_debug_coverage(survey_capture.stderr, survey["function_identities"], "survey")
        if survey["function_identities"] != extraction_transport["function_identities"]:
            raise EvidenceError("survey and dump-only extraction measured different function populations")

        analysis_capture = run_capture(
            "analysis",
            [sys.executable, str(analyzer), str(dump_dir)],
            cwd=repo,
            env=env,
            scratch=scratch,
            timeout=120,
            max_output_bytes=args.max_output_bytes,
        )
        if analysis_capture.exit_code != 0 or analysis_capture.stderr:
            raise EvidenceError("coverage analyzer failed or wrote unexpected stderr")
        analysis = validate_analysis(
            strict_json_bytes(analysis_capture.stdout, "analyze.py stdout"),
            extraction_transport["function_identities"],
        )
        dumps_after_analysis = validate_dumps(dump_dir, extraction_transport["function_identities"])
        if dumps_after_analysis != dumps:
            raise EvidenceError("compiler dump population changed while analyze.py was running")

        prove_timeout = args.prove_timeout_secs or max(
            600, args.prove_budget_secs * dumps["count"] + 300
        )
        prove_capture = run_capture(
            "prove",
            [
                str(targo),
                "trust",
                "prove",
                "--kernel",
                "--dump-dir",
                str(dump_dir),
                f"--budget-secs={args.prove_budget_secs}",
                "--format=json",
            ],
            cwd=repo,
            env=env,
            scratch=scratch,
            timeout=prove_timeout,
            max_output_bytes=args.max_output_bytes,
        )
        proof_candidate = validate_proof_population(
            strict_json_bytes(prove_capture.stdout, "prove JSON stdout"),
            dumps["count"],
            args.prove_budget_secs,
        )
        proof_rejection_reasons: list[str] = []
        if prove_capture.exit_code != 0:
            proof_rejection_reasons.append(f"prove process exited {prove_capture.exit_code}")
        if prove_capture.stderr:
            proof_rejection_reasons.append("prove process wrote stderr")
        try:
            proof = validate_proof(proof_candidate, dumps["count"], args.prove_budget_secs)
        except EvidenceError as error:
            proof = proof_candidate
            proof_rejection_reasons.append(str(error))
        dumps_after_proof = validate_dumps(dump_dir, extraction_transport["function_identities"])
        if dumps_after_proof != dumps:
            raise EvidenceError("compiler dump population changed while kernel prove was running")

        provenance_check_after = run_capture(
            "provenance-after",
            provenance_command,
            cwd=repo,
            env=env,
            scratch=scratch,
            timeout=args.provenance_timeout_secs,
            max_output_bytes=args.max_output_bytes,
        )
        if provenance_check_after.exit_code != 0:
            raise EvidenceError("canonical stage2 provenance verification failed after measurement")

        for label, (path, snapshot) in source_files.items():
            require_unchanged(path, snapshot, label)
        for label, (path, snapshot) in tool_files.items():
            require_unchanged(path, snapshot, label)
        require_unchanged(provenance, provenance_before, "stage2 provenance")
        if clean_head(repo, system_git) != head:
            raise EvidenceError("clean Git HEAD changed while evidence was being collected")

        captures = {
            "trustc_identity": identity_trustc,
            "targo_trust_identity": identity_targo,
            "provenance_before": provenance_check_before,
            "extraction": extraction,
            "survey": survey_capture,
            "analysis": analysis_capture,
            "prove": prove_capture,
            "provenance_after": provenance_check_after,
        }
        source_receipt = {
            "git_head": head,
            "git_clean_before_and_after": True,
            **{label: snapshot for label, (_, snapshot) in source_files.items()},
        }
        tools_receipt = {
            "trustc": {
                **tool_files["trustc"][1],
                "identity": trustc_identity,
                "identity_sha256": sha256_bytes(identity_trustc.stdout),
            },
            "targo-trust": {
                **tool_files["targo-trust"][1],
                "identity": targo_identity,
                "identity_sha256": sha256_bytes(identity_targo.stdout),
            },
            "python": {
                "executable": sys.executable,
                "version": sys.version,
                "version_sha256": sha256_bytes(sys.version.encode("utf-8")),
            },
            "system-git": tool_files["system-git"][1],
        }
        provenance_receipt = {
            **provenance_before,
            "schema": provenance_value.get("schema"),
            "status": provenance_metadata["status"],
            "stage": 2,
            "host": provenance_metadata["host"],
            "source_commit": head,
            "canonical_verifier_passed_before_and_after": True,
        }
        population_receipt = {
            "eligible": extraction_transport["eligible"],
            "processed": extraction_transport["processed"],
            "coverage_complete": True,
            "function_identities": extraction_transport["function_identities"],
            "dump_count": dumps["count"],
            "dump_manifest": dumps["manifest"],
            "dump_manifest_sha256": dumps["manifest_sha256"],
            "dump_manifest_stable_after_analysis_and_proof": True,
        }
        raw_evidence = {label: capture.digest_record() for label, capture in captures.items()}

        if proof_rejection_reasons:
            require_safe_parent_components(output)
            if output_snapshot(output) != previous_output:
                raise EvidenceError(
                    "accepted output receipt changed concurrently; refusing a misleading last-attempt claim"
                )
            attempt = {
                "schema": ATTEMPT_SCHEMA,
                "status": "rejected",
                "admissible_as_measurement": False,
                "proof_credit": 0,
                "primary_receipt_unchanged": True,
                "claim_boundary": (
                    "Durable diagnostic for a complete-population kernel/bridge rejection; "
                    "this document grants no proof credit and is never accepted-release authority."
                ),
                "generated_at_utc": dt.datetime.now(dt.timezone.utc)
                .isoformat()
                .replace("+00:00", "Z"),
                "rejection_reasons": proof_rejection_reasons,
                "source": source_receipt,
                "corpus_classification": CORPUS_CLASSIFICATION,
                "environment_authority": environment_authority,
                "stage2_provenance": provenance_receipt,
                "tools": tools_receipt,
                "population": population_receipt,
                "survey": {
                    "session": survey_session,
                    "transport": survey,
                    "debug_coverage": survey_debug,
                },
                "analysis": analysis,
                "proof": proof_candidate,
                "raw_evidence": raw_evidence,
            }
            atomic_publish(
                diagnostic_output,
                canonical_json_bytes(attempt),
                previous_diagnostic_output,
            )
            raise EvidenceError(
                "kernel/bridge measurement was rejected; accepted receipt preserved and "
                f"zero-credit diagnostic published to {diagnostic_output}"
            )

        receipt: dict[str, Any] = {
            "schema": SCHEMA,
            "status": "measured",
            "claim_boundary": (
                "Exact coverage and measured outcomes for the pinned, curated, hand-authored "
                "synthetic realcode.rs fixture only; "
                "failed, unknown, timed-out, skipped, runtime-checked, declined, opaque, and "
                "unrecognized work remains negative evidence and earns no proof credit."
            ),
            "generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z"),
            "source": source_receipt,
            "corpus_classification": CORPUS_CLASSIFICATION,
            "environment_authority": environment_authority,
            "stage2_provenance": provenance_receipt,
            "tools": tools_receipt,
            "population": population_receipt,
            "extraction": {
                "session": extract_session,
                "transport": extraction_transport,
                "debug_coverage": extraction_debug,
            },
            "survey": {
                "session": survey_session,
                "transport": survey,
                "debug_coverage": survey_debug,
            },
            "analysis": analysis,
            "verifier_loop_coverage": {
                "source": "proof.scorecard",
                "claim_boundary": (
                    "Verifier-computed structural loop-header detection/recognition over the exact "
                    "dump population; separate from kernel proof credit."
                ),
                "loop_headers_detected": proof["scorecard"]["loop_headers_detected"],
                "loop_headers_recognized": proof["scorecard"]["loop_headers_recognized"],
            },
            "proof": proof,
            "raw_evidence": raw_evidence,
        }
        validate_receipt(receipt)
        rendered = canonical_json_bytes(receipt)
        atomic_publish(output, rendered, previous_output)
        print(f"published {SCHEMA} ({dumps['count']} functions) -> {output}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except EvidenceError as error:
        print(f"coverage evidence rejected: {error}", file=sys.stderr)
        raise SystemExit(1)
