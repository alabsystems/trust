#!/usr/bin/env python3
"""Fail-closed native trust_ir solver sample verification harness."""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shlex
import subprocess
import sys
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SAMPLE = Path("examples/full_verifier_three_suite.rs")
DEFAULT_REPORT_DIR = Path("reports/verification-samples/native-solver-sample")
REQUIRED_SUITES = ("zani", "sunder", "certus")
TEXT_MARKERS = ("trust-ir", "native trust_ir", "zani", "sunder", "certus", "fixture")
FIXTURE_MARKERS = ("fixture", "native-trust-ir-test", "text-only", "mock", "stub")
SUITE_KEYS = ("suite", "verifier", "backend", "engine", "solver", "checker", "tool", "name")
OUTCOME_KEYS = ("proved", "runtime_checked", "unknown", "failed")
REPLAY_ARTIFACT_MARKERS = ("replay",)
CHECK_ARTIFACT_MARKERS = (
    "check",
    "checked",
    "certificate",
    "proofcertificate",
    "proof-certificate",
    "proof_certificate",
    "report",
)
CERTUS_NATIVE_TMIR_PROOF_CERTIFICATE_URI_PREFIX = (
    "artifact://certus/native-trust-ir-proof-artifacts/"
)
CERTUS_PROOF_CERTIFICATE_URI_PREFIX = "artifact://certus/proof-artifacts/"
CERTUS_PROOF_ARTIFACT_ID_PREFIX = "certus-proof-certificate:v1:"
LOWERING_RE = re.compile(
    r"failed to lower `(?P<function>[^`]+)` into typed trust_ir NativeVerificationBundle input:"
    r" (?P<reason>.*?)(?:$|\n)"
)
UNSUPPORTED_RE = re.compile(
    r"unsupported type: Unsupported \{ kind: \"(?P<kind>[^\"]+)\", detail: \"(?P<detail>[^\"]+)\""
)
SUITE_RE = re.compile(r"\b(?P<suite>zani|sunder|certus)\b", re.IGNORECASE)


@dataclass(frozen=True)
class EvidenceHit:
    suite: str | None
    path: str
    native_trust_ir: bool
    proofish: bool
    fixture: bool
    text_only: bool
    summary: str


@dataclass(frozen=True)
class GateResult:
    ok: bool
    errors: tuple[str, ...]
    warnings: tuple[str, ...]
    suite_paths: Mapping[str, tuple[str, ...]]
    native_trust_ir_paths: tuple[str, ...]
    obligation_evidence: tuple[Mapping[str, Any], ...] = ()
    proof_grade_status: Mapping[str, Any] | None = None

    def describe(self) -> str:
        if self.ok:
            suite_bits = ", ".join(
                f"{suite}: {', '.join(paths)}" for suite, paths in self.suite_paths.items()
            )
            return f"native solver sample verification gate passed ({suite_bits})"
        return "native solver sample verification gate failed:\n- " + "\n- ".join(self.errors)


@dataclass(frozen=True)
class MissingStage2Tool:
    tool: str
    checked_paths: tuple[str, ...]


class Stage2ToolDiscoveryError(FileNotFoundError):
    def __init__(self, missing: Sequence[MissingStage2Tool]) -> None:
        self.missing = tuple(missing)
        detail = "; ".join(
            f"{item.tool} checked {', '.join(item.checked_paths)}"
            for item in self.missing
        )
        super().__init__(f"could not find executable stage2 tool(s): {detail}")


@dataclass
class WalkContext:
    native_suites: tuple[str, ...] = ()
    proofish: bool = False
    fixture: bool = False
    text_marker_paths: list[str] = field(default_factory=list)


def load_json_report(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"{path} is not valid JSON: {exc}") from exc


def evaluate_report(report: Any) -> GateResult:
    hits: list[EvidenceHit] = []
    native_paths: set[str] = set()
    text_marker_paths: set[str] = set()
    _walk_report(report, "$", WalkContext(), hits, native_paths, text_marker_paths)
    obligation_evidence = structured_evidence_rows(report)
    accepted_suite_rows = _accepted_structured_suite_rows(obligation_evidence)
    proof_grade_status = proof_grade_status_report(report)

    errors: list[str] = []
    warnings: list[str] = []

    if not isinstance(report, Mapping):
        errors.append("verification report must be one JSON object")

    if _explicit_failure(report):
        errors.append("report declares an unsuccessful/failed verification run")

    if not native_paths:
        errors.append("missing structured native trust_ir evidence")

    if not obligation_evidence:
        errors.append("missing structured obligation evidence rows")

    suite_paths: dict[str, tuple[str, ...]] = {}
    for suite in REQUIRED_SUITES:
        accepted = accepted_suite_rows.get(suite, ())
        suite_paths[suite] = tuple(sorted(set(accepted)))
        if not accepted:
            rejected = [
                hit.summary
                for hit in hits
                if hit.suite == suite and (hit.fixture or hit.text_only or not hit.native_trust_ir)
            ]
            rejected.extend(
                _invalid_structured_row_summary(row, suite)
                for row in obligation_evidence
                if _row_mentions_suite(row, suite) and _accepted_suite_for_row(row) != suite
            )
            detail = f"; rejected evidence: {'; '.join(rejected[:3])}" if rejected else ""
            errors.append(
                f"missing structured native trust_ir proof evidence for {suite}; "
                "native_trust_ir and proof_evidence must appear on the same row with matching "
                f"suite/request/native IDs{detail}"
            )
        suite_status = proof_grade_status["suites"][suite]
        if not suite_status["proof_grade"]:
            errors.append(_suite_status_error(suite_status))

    warnings.extend(
        f"text marker ignored as proof evidence: {path}"
        for path in sorted(text_marker_paths)[:8]
    )

    return GateResult(
        ok=not errors,
        errors=tuple(errors),
        warnings=tuple(warnings),
        suite_paths=suite_paths,
        native_trust_ir_paths=tuple(sorted(native_paths)),
        obligation_evidence=tuple(obligation_evidence),
        proof_grade_status=proof_grade_status,
    )


def gate_report_file(path: Path) -> GateResult:
    return evaluate_report(load_json_report(path))


def extract_blockers(
    *,
    gate_errors: Sequence[str],
    native_trust_ir_paths: Sequence[str],
    returncode: int | None = None,
    stdout_text: str = "",
    stderr_text: str = "",
) -> list[dict[str, Any]]:
    """Build compact live-run blocker summaries without weakening the gate."""
    blockers: list[dict[str, Any]] = []
    seen: set[tuple[tuple[str, str], ...]] = set()

    def add(blocker: dict[str, Any]) -> None:
        normalized = tuple(sorted((key, str(value)) for key, value in blocker.items()))
        if normalized not in seen:
            seen.add(normalized)
            blockers.append(blocker)

    if returncode not in (None, 0):
        add({"kind": "command_returncode", "returncode": returncode})

    for error in gate_errors:
        error_l = error.lower()
        if "missing structured native trust_ir evidence" in error_l:
            add({"kind": "missing_native_trust_ir_paths"})
        suite = _missing_suite_from_error(error)
        if suite is not None:
            add({"kind": "missing_suite_evidence", "suite": suite})

    if not native_trust_ir_paths:
        add({"kind": "missing_native_trust_ir_paths"})

    symptom_text = "\n".join(
        part for part in (stderr_text, stdout_text, _json_string_text(stdout_text)) if part
    )
    for function, reason in _lowering_symptoms(symptom_text):
        unsupported = UNSUPPORTED_RE.search(reason)
        if unsupported:
            add(
                {
                    "kind": "unsupported_adt_lowering",
                    "function": function,
                    "type_kind": unsupported.group("kind"),
                    "detail": unsupported.group("detail"),
                }
            )
        else:
            add(
                {
                    "kind": "native_trust_ir_lowering_blocker",
                    "function": function,
                    "detail": _compact_line(reason),
                }
            )

    for line in _symptom_lines(symptom_text):
        line_l = line.lower()
        if "proof adapter is not wired" in line_l:
            suite = _line_suite(line)
            blocker = {
                "kind": "suite_adapter_missing",
                "detail": _compact_line(line),
            }
            if suite is not None:
                blocker["suite"] = suite
            add(blocker)
        elif "requires certus_core::vc::typedproofobligation" in line_l:
            add({"kind": "certus_typed_proof_obligation_missing"})
        elif "requires a typed trustrust_irmemoryproofunit payload" in line_l:
            add({"kind": "certus_memory_proof_unit_missing"})

    return blockers


def remaining_gap_report(
    *,
    gate_ok: bool,
    gate_errors: Sequence[str],
    evidence: Mapping[str, Any] | None,
    blockers: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    summary = evidence.get("summary", {}) if isinstance(evidence, Mapping) else {}
    missing_suites = summary.get("missing_required_suites")
    if not isinstance(missing_suites, list):
        missing_suites = list(REQUIRED_SUITES)
    observed_rows = summary.get("obligation_evidence_rows")
    if not isinstance(observed_rows, int):
        observed_rows = 0
    proof_grade_status = evidence.get("proof_grade_status", {}) if isinstance(evidence, Mapping) else {}
    suite_status = proof_grade_status.get("suites", {}) if isinstance(proof_grade_status, Mapping) else {}
    suite_blockers = {
        suite: status.get("blockers", [])
        for suite, status in suite_status.items()
        if isinstance(status, Mapping) and status.get("proof_grade") is not True
    }

    return {
        "schema": "trust.native-solver-sample-verification.remaining-gap.v1",
        "blocked": not gate_ok,
        "requirement": (
            "one JSON object containing same-row structured native_trust_ir and proof_evidence "
            "entries for zani, sunder, and certus; zani/sunder require solver transcript plus "
            "replay/check artifacts, and certus requires a digest-bound proof certificate or the "
            "same transcript plus replay/check artifact policy"
        ),
        "missing_required_suites": missing_suites,
        "observed_obligation_evidence_rows": observed_rows,
        "gate_errors": list(gate_errors),
        "blockers": list(blockers),
        "suite_blockers": suite_blockers,
    }


def _walk_report(
    value: Any,
    path: str,
    context: WalkContext,
    hits: list[EvidenceHit],
    native_paths: set[str],
    text_marker_paths: set[str],
) -> None:
    if isinstance(value, dict):
        object_text = _object_text(value)
        fixture = context.fixture or _contains_any(object_text, FIXTURE_MARKERS)
        proofish = context.proofish or _structured_proof_evidence(value)
        native_suites = set(context.native_suites)
        native_self_suites = _structured_native_trust_ir_suites(value)
        native_suites.update(native_self_suites)
        if native_self_suites and not fixture:
            native_paths.add(path)

        suites = _structured_suites(value)
        text_only = False
        if not suites:
            for suite in REQUIRED_SUITES:
                if suite in object_text and not _suite_has_structured_field(value, suite):
                    suites.add(suite)
                    text_only = True

        hits.extend(
            (
                EvidenceHit(
                    suite=suite,
                    path=path,
                    native_trust_ir=suite in native_suites,
                    proofish=proofish,
                    fixture=fixture,
                    text_only=text_only,
                    summary=(
                        f"{path} (native_trust_ir={suite in native_suites}, proofish={proofish}, "
                        f"fixture={fixture}, text_only={text_only})"
                    ),
                )
            )
            for suite in suites
        )

        next_context = WalkContext(
            native_suites=tuple(sorted(native_suites)),
            proofish=proofish,
            fixture=fixture,
            text_marker_paths=context.text_marker_paths,
        )
        for key, child in value.items():
            _walk_report(child, f"{path}.{key}", next_context, hits, native_paths, text_marker_paths)
        return

    if isinstance(value, list):
        for idx, child in enumerate(value):
            _walk_report(child, f"{path}[{idx}]", context, hits, native_paths, text_marker_paths)
        return

    if isinstance(value, str) and _contains_any(value, TEXT_MARKERS):
        text_marker_paths.add(path)


def structured_evidence_rows(report: Any) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[tuple[str, str, str]] = set()
    _collect_structured_evidence_rows(report, "$", rows, seen)
    return rows


def structured_evidence_report(report: Any) -> dict[str, Any]:
    rows = structured_evidence_rows(report)
    accepted_suite_rows = _accepted_structured_suite_rows(rows)
    native_suites: dict[str, int] = {}
    proof_suites: dict[str, int] = {}
    proof_grade_suites: dict[str, int] = {}
    native_rows = 0
    proof_rows = 0
    proof_grade_rows = 0

    for row in rows:
        native_trust_ir = row.get("native_trust_ir")
        if isinstance(native_trust_ir, Mapping):
            native_rows += 1
            suite = _suite_field(native_trust_ir)
            if suite is not None:
                native_suites[suite] = native_suites.get(suite, 0) + 1
        proof_evidence = row.get("proof_evidence")
        if isinstance(proof_evidence, Mapping):
            proof_rows += 1
            suite = _suite_field(proof_evidence)
            if suite is not None:
                proof_suites[suite] = proof_suites.get(suite, 0) + 1
        accepted_suite = _accepted_suite_for_row(row)
        if accepted_suite is not None:
            proof_grade_rows += 1
            proof_grade_suites[accepted_suite] = proof_grade_suites.get(accepted_suite, 0) + 1

    return {
        "schema": "trust.native-solver-sample-verification.evidence.v1",
        "source": "structured native_trust_ir/proof_evidence JSON fields",
        "obligation_evidence": rows,
        "proof_grade_status": proof_grade_status_report(report),
        "summary": {
            "obligation_evidence_rows": len(rows),
            "native_trust_ir_rows": native_rows,
            "proof_evidence_rows": proof_rows,
            "proof_grade_rows": proof_grade_rows,
            "native_trust_ir_suites": dict(sorted(native_suites.items())),
            "proof_evidence_suites": dict(sorted(proof_suites.items())),
            "proof_grade_suites": dict(sorted(proof_grade_suites.items())),
            "accepted_suite_rows": {
                suite: list(paths) for suite, paths in sorted(accepted_suite_rows.items())
            },
            "missing_required_suites": [
                suite for suite in REQUIRED_SUITES if suite not in accepted_suite_rows
            ],
            "required_suites": list(REQUIRED_SUITES),
        },
    }


def proof_grade_status_report(report: Any) -> dict[str, Any]:
    """Classify proof-grade status per native suite from obligation rows."""
    suites = {suite: _empty_suite_status(suite) for suite in REQUIRED_SUITES}
    unattributed: list[dict[str, Any]] = []

    for path, obligation in _iter_obligation_rows(report):
        suite = _obligation_suite(obligation)
        if suite not in suites:
            unattributed.append(
                {
                    "path": path,
                    "suite": suite or "missing",
                    "status": _obligation_outcome_status(obligation),
                    "native_trust_ir_present": _native_trust_ir_present(obligation),
                    "proof_evidence_accepted": False,
                    "detail": _first_obligation_diagnostic(obligation),
                }
            )
            continue

        row = suites[suite]
        row["obligations"] += 1
        status = _obligation_outcome_status(obligation)
        if status not in OUTCOME_KEYS:
            status = "unknown"
        row[status] += 1

        if _native_trust_ir_present(obligation, suite):
            row["native_trust_ir_present"] += 1
            row["native_trust_ir_paths"].append(path)

        if _publishable_proof_evidence_accepted(obligation, suite):
            row["proof_evidence_accepted"] += 1
            row["accepted_proof_evidence_paths"].append(path)

        artifact_presence = _proof_artifact_policy_presence(obligation, suite)
        if artifact_presence["solver_transcript"]:
            row["solver_transcript_artifacts_present"] += 1
        if artifact_presence["replay"]:
            row["replay_artifacts_present"] += 1
        if artifact_presence["check"]:
            row["check_artifacts_present"] += 1
        if artifact_presence["replay"] or artifact_presence["check"]:
            row["replay_or_check_artifacts_present"] += 1
        if artifact_presence["certus_certificate"]:
            row["certus_certificate_artifacts_present"] += 1
        if artifact_presence["proof_policy"]:
            row["proof_artifacts_present"] += 1

        transport_status = _transport_proof_status(obligation)
        if transport_status is not None:
            statuses = row["transport_proof_statuses"]
            statuses[transport_status] = statuses.get(transport_status, 0) + 1

        if _transport_only_proof_evidence_present(obligation):
            row["transport_only_proof_evidence"] += 1

        for diagnostic in _obligation_diagnostics(obligation):
            if len(row["sample_diagnostics"]) >= 6:
                break
            if diagnostic not in row["sample_diagnostics"]:
                row["sample_diagnostics"].append(diagnostic)

    for row in suites.values():
        _finalize_suite_status(row)

    blocked_suites = [
        suite for suite, row in suites.items() if not row["proof_grade"]
    ]
    proof_grade_suites = [
        suite for suite, row in suites.items() if row["proof_grade"]
    ]
    return {
        "schema": "trust.native-solver-sample-verification.proof-grade-status.v1",
        "required_suites": list(REQUIRED_SUITES),
        "summary": {
            "proof_grade_suites": proof_grade_suites,
            "blocked_suites": blocked_suites,
            "unattributed_obligations": len(unattributed),
        },
        "suites": suites,
        "unattributed_obligations": unattributed,
    }


def _iter_obligation_rows(report: Any) -> Iterable[tuple[str, Mapping[str, Any]]]:
    if not isinstance(report, Mapping):
        return
    functions = report.get("functions")
    if not isinstance(functions, list):
        return
    for fn_idx, function in enumerate(functions):
        if not isinstance(function, Mapping):
            continue
        obligations = function.get("obligations")
        if not isinstance(obligations, list):
            continue
        for idx, obligation in enumerate(obligations):
            if isinstance(obligation, Mapping):
                yield f"$.functions[{fn_idx}].obligations[{idx}]", obligation


def _empty_suite_status(suite: str) -> dict[str, Any]:
    return {
        "suite": suite,
        "proof_grade": False,
        "obligations": 0,
        "proved": 0,
        "runtime_checked": 0,
        "unknown": 0,
        "failed": 0,
        "native_trust_ir_present": 0,
        "native_trust_ir_all_present": False,
        "proof_evidence_accepted": 0,
        "proof_evidence_all_accepted": False,
        "solver_transcript_artifacts_present": 0,
        "replay_artifacts_present": 0,
        "check_artifacts_present": 0,
        "replay_or_check_artifacts_present": 0,
        "replay_or_check_artifacts_all_present": False,
        "certus_certificate_artifacts_present": 0,
        "proof_artifacts_present": 0,
        "proof_artifacts_all_present": False,
        "transport_only_proof_evidence": 0,
        "transport_proof_statuses": {},
        "native_trust_ir_paths": [],
        "accepted_proof_evidence_paths": [],
        "sample_diagnostics": [],
        "blockers": [],
    }


def _finalize_suite_status(row: dict[str, Any]) -> None:
    obligations = row["obligations"]
    row["native_trust_ir_all_present"] = obligations > 0 and row["native_trust_ir_present"] == obligations
    row["proof_evidence_all_accepted"] = (
        obligations > 0 and row["proof_evidence_accepted"] == obligations
    )
    row["replay_or_check_artifacts_all_present"] = (
        obligations > 0 and row["replay_or_check_artifacts_present"] == obligations
    )
    row["proof_artifacts_all_present"] = (
        obligations > 0 and row["proof_artifacts_present"] == obligations
    )
    row["proof_grade"] = (
        obligations > 0
        and row["proved"] == obligations
        and row["runtime_checked"] == 0
        and row["unknown"] == 0
        and row["failed"] == 0
        and row["native_trust_ir_all_present"]
        and row["proof_evidence_all_accepted"]
        and row["proof_artifacts_all_present"]
    )

    blockers: list[dict[str, Any]] = []
    first_detail = row["sample_diagnostics"][0] if row["sample_diagnostics"] else None

    def add(kind: str, detail: str | None = None, **extra: Any) -> None:
        blocker: dict[str, Any] = {"kind": kind}
        if detail:
            blocker["detail"] = detail
        blocker.update(extra)
        blockers.append(blocker)

    if obligations == 0:
        add("missing_suite_obligations", "no obligations were attributed to this required suite")
    if row["runtime_checked"]:
        add(
            "runtime_checked_obligations",
            first_detail,
            count=row["runtime_checked"],
        )
    if row["unknown"]:
        add("unknown_obligations", first_detail, count=row["unknown"])
    if row["failed"]:
        add("failed_obligations", first_detail, count=row["failed"])
    if row["native_trust_ir_present"] < obligations:
        add(
            "native_trust_ir_missing",
            first_detail,
            present=row["native_trust_ir_present"],
            expected=obligations,
        )
    if row["proof_evidence_accepted"] < obligations:
        add(
            "proof_evidence_not_accepted",
            first_detail,
            accepted=row["proof_evidence_accepted"],
            expected=obligations,
        )
    if row["proof_artifacts_present"] < obligations:
        add(
            "proof_artifacts_missing",
            first_detail,
            present=row["proof_artifacts_present"],
            expected=obligations,
        )
    non_proved_transport = {
        status: count
        for status, count in row["transport_proof_statuses"].items()
        if status != "proved"
    }
    if non_proved_transport:
        add("transport_proof_status_not_proved", first_detail, statuses=non_proved_transport)
    if row["transport_only_proof_evidence"]:
        add(
            "transport_only_proof_evidence",
            "transport evidence is not the publishable proof boundary",
            count=row["transport_only_proof_evidence"],
        )
    row["blockers"] = blockers


def _suite_status_error(row: Mapping[str, Any]) -> str:
    blockers = row.get("blockers")
    blocker_bits: list[str] = []
    if isinstance(blockers, list):
        for blocker in blockers[:3]:
            if not isinstance(blocker, Mapping):
                continue
            kind = blocker.get("kind")
            detail = blocker.get("detail")
            if isinstance(kind, str):
                bit = kind
                if isinstance(detail, str) and detail:
                    bit = f"{bit}: {_compact_line(detail, 120)}"
                blocker_bits.append(bit)
    blocker_text = "; blockers: " + "; ".join(blocker_bits) if blocker_bits else ""
    return (
        f"{row.get('suite')} proof-grade status blocked: obligations={row.get('obligations')}, "
        f"proved={row.get('proved')}, runtime_checked={row.get('runtime_checked')}, "
        f"unknown={row.get('unknown')}, failed={row.get('failed')}, "
        f"native_trust_ir_present={row.get('native_trust_ir_present')}, "
        f"proof_evidence_accepted={row.get('proof_evidence_accepted')}, "
        f"solver_transcript_artifacts_present={row.get('solver_transcript_artifacts_present')}, "
        f"replay_or_check_artifacts_present={row.get('replay_or_check_artifacts_present')}, "
        f"certus_certificate_artifacts_present={row.get('certus_certificate_artifacts_present')}, "
        f"proof_artifacts_present={row.get('proof_artifacts_present')}"
        f"{blocker_text}"
    )


def _obligation_suite(obligation: Mapping[str, Any]) -> str | None:
    candidates = (
        _mapping_field(obligation, "proof_evidence"),
        _mapping_field(_mapping_field(obligation, "proof_evidence") or {}, "native_trust_ir"),
        _mapping_field(_mapping_field(obligation, "transport_evidence") or {}, "proof_evidence"),
        _mapping_field(_mapping_field(obligation, "transport_evidence") or {}, "native_trust_ir"),
        _mapping_field(obligation, "native_trust_ir", "native_trust_ir_evidence"),
    )
    for candidate in candidates:
        if isinstance(candidate, Mapping):
            suite = _suite_field(candidate)
            if suite is not None:
                return suite
    for candidate in candidates:
        if isinstance(candidate, Mapping):
            suite = candidate.get("suite")
            if isinstance(suite, str) and suite.strip():
                return suite.strip().lower()
    return None


def _obligation_outcome_status(obligation: Mapping[str, Any]) -> str:
    status = _status_from_obligation(obligation)
    if status is None:
        proof = _mapping_field(obligation, "proof_evidence")
        if isinstance(proof, Mapping):
            status_value = proof.get("status")
            if isinstance(status_value, str):
                status = status_value
    if status is None:
        transport = _mapping_field(obligation, "transport_evidence")
        proof = _mapping_field(transport or {}, "proof_evidence")
        if isinstance(proof, Mapping):
            status_value = proof.get("status")
            if isinstance(status_value, str):
                status = status_value
    return _normalize_outcome_status(status)


def _normalize_outcome_status(status: str | None) -> str:
    if not isinstance(status, str):
        return "unknown"
    status_l = status.strip().lower().replace("-", "_")
    if status_l in {"proved", "verified", "accepted"}:
        return "proved"
    if status_l in {"runtime_checked", "runtimechecked", "unsupported", "skipped"}:
        return "runtime_checked"
    if status_l in {"failed", "failure", "rejected", "timeout", "timed_out"}:
        return "failed"
    return "unknown"


def _obligation_native_trust_ir(obligation: Mapping[str, Any]) -> Mapping[str, Any] | None:
    proof = _mapping_field(obligation, "proof_evidence")
    transport = _mapping_field(obligation, "transport_evidence")
    for candidate in (
        _mapping_field(obligation, "native_trust_ir", "native_trust_ir_evidence"),
        _mapping_field(proof or {}, "native_trust_ir", "native_trust_ir_evidence"),
        _mapping_field(transport or {}, "native_trust_ir", "native_trust_ir_evidence"),
    ):
        if isinstance(candidate, Mapping):
            return candidate
    return None


def _native_trust_ir_present(obligation: Mapping[str, Any], suite: str | None = None) -> bool:
    native_trust_ir = _obligation_native_trust_ir(obligation)
    if not isinstance(native_trust_ir, Mapping):
        return False
    if suite is not None and _suite_field(native_trust_ir) != suite:
        return False
    return (
        native_trust_ir.get("present") is True
        and _nonempty_str(native_trust_ir.get("request_id"))
        and _nonempty_str(native_trust_ir.get("native_id"))
        and _artifacts_structured(native_trust_ir.get("artifacts"))
    )


def _top_level_proof_evidence_accepted(obligation: Mapping[str, Any], suite: str) -> bool:
    proof = _mapping_field(obligation, "proof_evidence")
    if not isinstance(proof, Mapping) or _suite_field(proof) != suite:
        return False
    if not _is_proof_evidence(proof):
        return False
    native_trust_ir = _mapping_field(proof, "native_trust_ir", "native_trust_ir_evidence")
    if not isinstance(native_trust_ir, Mapping):
        native_trust_ir = _obligation_native_trust_ir(obligation)
    if not isinstance(native_trust_ir, Mapping):
        return False
    if not _native_trust_ir_present({"native_trust_ir": native_trust_ir}, suite):
        return False
    if proof.get("request_id") != native_trust_ir.get("request_id"):
        return False
    if proof.get("native_id") != native_trust_ir.get("native_id"):
        return False

    transport = _mapping_field(obligation, "transport_evidence")
    transport_proof = _mapping_field(transport or {}, "proof_evidence")
    if isinstance(transport_proof, Mapping):
        if _suite_field(transport_proof) != suite:
            return False
        if _normalize_outcome_status(_scalar_or_none(transport_proof.get("status"))) != "proved":
            return False
        if proof.get("request_id") != transport_proof.get("request_id"):
            return False
        if proof.get("native_id") != transport_proof.get("native_id"):
            return False
    return True


def _publishable_proof_evidence_accepted(obligation: Mapping[str, Any], suite: str) -> bool:
    if _top_level_proof_evidence_accepted(obligation, suite):
        return True
    return suite == "certus" and _certus_transport_certificate_evidence_accepted(obligation)


def _certus_transport_certificate_evidence_accepted(obligation: Mapping[str, Any]) -> bool:
    transport = _mapping_field(obligation, "transport_evidence")
    if not isinstance(transport, Mapping):
        return False
    return _certus_certificate_evidence_accepted(
        _mapping_field(transport, "native_trust_ir", "native_trust_ir_evidence"),
        _mapping_field(transport, "proof_evidence"),
    )


def _certus_certificate_row_accepted(row: Mapping[str, Any]) -> bool:
    return _certus_certificate_evidence_accepted(
        row.get("native_trust_ir"),
        row.get("proof_evidence"),
    )


def _certus_certificate_evidence_accepted(
    native_trust_ir: Any,
    proof_evidence: Any,
) -> bool:
    if not _bound_native_proof_evidence(native_trust_ir, proof_evidence, "certus"):
        return False
    row = {"native_trust_ir": native_trust_ir, "proof_evidence": proof_evidence}
    presence = _proof_artifact_policy_presence(row, "certus")
    return presence["certus_certificate"] and presence["proof_policy"]


def _bound_native_proof_evidence(
    native_trust_ir: Any,
    proof_evidence: Any,
    suite: str,
) -> bool:
    if not isinstance(native_trust_ir, Mapping) or not isinstance(proof_evidence, Mapping):
        return False
    if not _is_native_trust_ir_evidence(native_trust_ir) or not _is_proof_evidence(proof_evidence):
        return False
    if _suite_field(native_trust_ir) != suite or _suite_field(proof_evidence) != suite:
        return False
    if native_trust_ir.get("request_id") != proof_evidence.get("request_id"):
        return False
    if native_trust_ir.get("native_id") != proof_evidence.get("native_id"):
        return False
    return True


def _transport_proof_status(obligation: Mapping[str, Any]) -> str | None:
    transport = _mapping_field(obligation, "transport_evidence")
    proof = _mapping_field(transport or {}, "proof_evidence")
    if not isinstance(proof, Mapping):
        return None
    status = proof.get("status")
    if isinstance(status, str):
        return status.strip().lower().replace("-", "_")
    return "missing"


def _transport_only_proof_evidence_present(obligation: Mapping[str, Any]) -> bool:
    if _mapping_field(obligation, "proof_evidence") is not None:
        return False
    transport = _mapping_field(obligation, "transport_evidence")
    proof = _mapping_field(transport or {}, "proof_evidence")
    if not isinstance(proof, Mapping):
        return False
    return not _certus_transport_certificate_evidence_accepted(obligation)


def _proof_artifact_policy_presence(
    obligation: Mapping[str, Any],
    suite: str,
) -> dict[str, bool]:
    artifacts: list[Mapping[str, Any]] = []
    _collect_artifacts(_mapping_field(obligation, "proof_evidence"), artifacts)
    _collect_artifacts(_mapping_field(obligation, "native_trust_ir", "native_trust_ir_evidence"), artifacts)
    transport = _mapping_field(obligation, "transport_evidence")
    _collect_artifacts(_mapping_field(transport or {}, "proof_evidence"), artifacts)
    _collect_artifacts(_mapping_field(transport or {}, "native_trust_ir", "native_trust_ir_evidence"), artifacts)

    solver_transcript = False
    replay = False
    check = False
    certus_certificate = False
    for artifact in artifacts:
        solver_transcript = solver_transcript or _is_solver_transcript_artifact(artifact)
        replay = replay or _is_replay_artifact(artifact)
        check = check or _is_check_artifact(artifact)
        certus_certificate = (
            certus_certificate or _is_certus_digest_bound_proof_certificate_artifact(artifact)
        )

    transcript_plus_replay_or_check = solver_transcript and (replay or check)
    proof_policy = (
        (suite == "certus" and certus_certificate) or transcript_plus_replay_or_check
    )
    return {
        "solver_transcript": solver_transcript,
        "replay": replay,
        "check": check,
        "certus_certificate": certus_certificate,
        "proof_policy": proof_policy,
    }


def _collect_artifacts(value: Mapping[str, Any] | None, artifacts: list[Mapping[str, Any]]) -> None:
    if not isinstance(value, Mapping):
        return
    raw_artifacts = value.get("artifacts")
    if isinstance(raw_artifacts, list):
        artifacts.extend(artifact for artifact in raw_artifacts if isinstance(artifact, Mapping))
    nested_native = _mapping_field(value, "native_trust_ir", "native_trust_ir_evidence")
    if isinstance(nested_native, Mapping):
        raw_native_artifacts = nested_native.get("artifacts")
        if isinstance(raw_native_artifacts, list):
            artifacts.extend(
                artifact for artifact in raw_native_artifacts if isinstance(artifact, Mapping)
            )


def _is_solver_transcript_artifact(artifact: Mapping[str, Any]) -> bool:
    return _normalized_artifact_kind(artifact.get("kind")) in {
        "solver_transcript",
        "smt_transcript",
        "smtlib_transcript",
        "solver_transcript_log",
    }


def _is_replay_artifact(artifact: Mapping[str, Any]) -> bool:
    kind = _normalized_artifact_kind(artifact.get("kind"))
    if kind in {
        "proof_replay",
        "proof_replay_trace",
        "replay_log",
        "machine_replay",
        "machine_code_replay",
    }:
        return True
    return _contains_any(_object_text(artifact), REPLAY_ARTIFACT_MARKERS)


def _is_check_artifact(artifact: Mapping[str, Any]) -> bool:
    kind = _normalized_artifact_kind(artifact.get("kind"))
    if kind in {
        "proof_check",
        "proof_check_report",
        "checked_proof_report",
        "checked_report",
        "checker_report",
        "certificate",
        "proof_certificate",
        "checked_certificate",
    }:
        return True
    return _contains_any(_object_text(artifact), CHECK_ARTIFACT_MARKERS)


def _is_certus_digest_bound_proof_certificate_artifact(
    artifact: Mapping[str, Any],
) -> bool:
    if _normalized_artifact_kind(artifact.get("kind")) != "proof_certificate":
        return False
    digest = _canonical_sha256_digest(artifact.get("digest"))
    uri = artifact.get("uri")
    if digest is None or not isinstance(uri, str):
        return False
    return _certus_proof_certificate_uri_matches_digest(uri.strip(), digest)


def _canonical_sha256_digest(value: Any) -> str | None:
    if not isinstance(value, Mapping):
        return None
    algorithm = value.get("algorithm")
    digest = value.get("value")
    if (
        algorithm == "sha256"
        and isinstance(digest, str)
        and len(digest) == 64
        and all(ch in "0123456789abcdef" for ch in digest)
    ):
        return digest
    return None


def _certus_proof_certificate_uri_matches_digest(uri: str, digest: str) -> bool:
    exported_id = f"{CERTUS_PROOF_ARTIFACT_ID_PREFIX}{digest}"
    return uri in {
        f"{CERTUS_NATIVE_TMIR_PROOF_CERTIFICATE_URI_PREFIX}{digest}",
        f"{CERTUS_NATIVE_TMIR_PROOF_CERTIFICATE_URI_PREFIX}{digest}.json",
        f"{CERTUS_PROOF_CERTIFICATE_URI_PREFIX}{exported_id}",
        f"{CERTUS_PROOF_CERTIFICATE_URI_PREFIX}{exported_id}.alethe",
    }


def _normalized_artifact_kind(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    normalized = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", value.strip())
    normalized = re.sub(r"[^A-Za-z0-9]+", "_", normalized)
    return normalized.strip("_").lower()


def _obligation_diagnostics(obligation: Mapping[str, Any]) -> list[str]:
    diagnostics: list[str] = []
    outcome = obligation.get("outcome")
    if isinstance(outcome, Mapping):
        note = outcome.get("note")
        if isinstance(note, str) and note.strip():
            diagnostics.append(_compact_line(note))
    for value in (
        _mapping_field(obligation, "proof_evidence"),
        _obligation_native_trust_ir(obligation),
        _mapping_field(_mapping_field(obligation, "transport_evidence") or {}, "proof_evidence"),
    ):
        if not isinstance(value, Mapping):
            continue
        raw_diagnostics = value.get("diagnostics")
        if not isinstance(raw_diagnostics, list):
            continue
        for diagnostic in raw_diagnostics:
            if not isinstance(diagnostic, Mapping):
                continue
            message = diagnostic.get("message")
            if isinstance(message, str) and message.strip():
                diagnostics.append(_compact_line(message))
    return diagnostics


def _first_obligation_diagnostic(obligation: Mapping[str, Any]) -> str | None:
    diagnostics = _obligation_diagnostics(obligation)
    return diagnostics[0] if diagnostics else None


def _collect_structured_evidence_rows(
    value: Any,
    path: str,
    rows: list[dict[str, Any]],
    seen: set[tuple[str, str, str]],
) -> None:
    if isinstance(value, Mapping):
        native_trust_ir = _mapping_field(value, "native_trust_ir", "native_trust_ir_evidence")
        proof_evidence = _mapping_field(value, "proof_evidence")
        if proof_evidence is not None and native_trust_ir is None:
            native_trust_ir = _mapping_field(proof_evidence, "native_trust_ir", "native_trust_ir_evidence")
        elif proof_evidence is None and _proof_evidence_like(value):
            proof_evidence = value

        if native_trust_ir is not None or proof_evidence is not None:
            native_key = json.dumps(native_trust_ir, sort_keys=True, default=str) if native_trust_ir else ""
            proof_key = (
                json.dumps(proof_evidence, sort_keys=True, default=str) if proof_evidence else ""
            )
            key = (path, native_key, proof_key)
            if key not in seen:
                seen.add(key)
                row: dict[str, Any] = {
                    "path": path,
                    "function": _scalar_or_none(value.get("function")),
                    "obligation_id": _scalar_or_none(value.get("obligation_id")),
                    "kind": _scalar_or_none(value.get("kind")),
                    "status": _status_from_obligation(value),
                }
                if ".transport_evidence" in path:
                    row["transport_only"] = True
                if native_trust_ir is not None:
                    row["native_trust_ir"] = dict(native_trust_ir)
                if proof_evidence is not None:
                    row["proof_evidence"] = dict(proof_evidence)
                rows.append(row)

        for key, child in value.items():
            if str(key).lower() in {"native_trust_ir", "native_trust_ir_evidence", "proof_evidence"}:
                continue
            _collect_structured_evidence_rows(child, f"{path}.{key}", rows, seen)
        return

    if isinstance(value, list):
        for idx, child in enumerate(value):
            _collect_structured_evidence_rows(child, f"{path}[{idx}]", rows, seen)


def _mapping_field(obj: Mapping[str, Any], *names: str) -> Mapping[str, Any] | None:
    wanted = {name.lower() for name in names}
    for key, value in obj.items():
        if str(key).lower() in wanted and isinstance(value, Mapping):
            return value
    return None


def _proof_evidence_like(obj: Mapping[str, Any]) -> bool:
    return (
        _suite_field(obj) is not None
        and _nonempty_str(obj.get("backend"))
        and any(
            key in obj
            for key in (
                "status",
                "proof_id",
                "native_id",
                "strength",
                "evidence",
                "artifacts",
                "diagnostics",
            )
        )
    )


def _scalar_or_none(value: Any) -> str | None:
    if isinstance(value, (str, int, float, bool)):
        return str(value)
    return None


def _status_from_obligation(obj: Mapping[str, Any]) -> str | None:
    outcome = obj.get("outcome")
    if isinstance(outcome, str):
        return outcome
    if isinstance(outcome, Mapping):
        status = outcome.get("status")
        if isinstance(status, str):
            return status
    status = obj.get("status")
    if isinstance(status, str):
        return status
    return None


def _accepted_structured_suite_rows(rows: Sequence[Mapping[str, Any]]) -> dict[str, tuple[str, ...]]:
    accepted: dict[str, list[str]] = {}
    for row in rows:
        suite = _accepted_suite_for_row(row)
        if suite is None:
            continue
        path = _scalar_or_none(row.get("path")) or "$"
        accepted.setdefault(suite, []).append(path)
    return {suite: tuple(paths) for suite, paths in accepted.items()}


def _accepted_suite_for_row(row: Mapping[str, Any]) -> str | None:
    if row.get("transport_only") is True:
        if _contains_any(_object_text(row), FIXTURE_MARKERS):
            return None
        return "certus" if _certus_certificate_row_accepted(row) else None
    native_trust_ir = row.get("native_trust_ir")
    proof_evidence = row.get("proof_evidence")
    if not isinstance(native_trust_ir, Mapping) or not isinstance(proof_evidence, Mapping):
        return None
    if _contains_any(_object_text(row), FIXTURE_MARKERS):
        return None
    if not _is_native_trust_ir_evidence(native_trust_ir) or not _is_proof_evidence(proof_evidence):
        return None

    native_suite = _suite_field(native_trust_ir)
    proof_suite = _suite_field(proof_evidence)
    if native_suite is None or native_suite != proof_suite:
        return None
    if native_trust_ir.get("request_id") != proof_evidence.get("request_id"):
        return None
    if native_trust_ir.get("native_id") != proof_evidence.get("native_id"):
        return None
    if not _proof_artifact_policy_presence(row, native_suite)["proof_policy"]:
        return None
    return native_suite


def _row_mentions_suite(row: Mapping[str, Any], suite: str) -> bool:
    native_trust_ir = row.get("native_trust_ir")
    proof_evidence = row.get("proof_evidence")
    return any(
        _suite_field(value) == suite
        for value in (native_trust_ir, proof_evidence)
        if isinstance(value, Mapping)
    )


def _invalid_structured_row_summary(row: Mapping[str, Any], suite: str) -> str:
    native_trust_ir = row.get("native_trust_ir")
    proof_evidence = row.get("proof_evidence")
    path = _scalar_or_none(row.get("path")) or "$"
    native_suite = _suite_field(native_trust_ir) if isinstance(native_trust_ir, Mapping) else None
    proof_suite = _suite_field(proof_evidence) if isinstance(proof_evidence, Mapping) else None
    native_id = native_trust_ir.get("native_id") if isinstance(native_trust_ir, Mapping) else None
    proof_native_id = proof_evidence.get("native_id") if isinstance(proof_evidence, Mapping) else None
    native_request = native_trust_ir.get("request_id") if isinstance(native_trust_ir, Mapping) else None
    proof_request = proof_evidence.get("request_id") if isinstance(proof_evidence, Mapping) else None
    return (
        f"{path} (suite={suite}, native_suite={native_suite}, proof_suite={proof_suite}, "
        f"request_match={native_request == proof_request}, native_id_match={native_id == proof_native_id})"
    )


def _missing_suite_from_error(error: str) -> str | None:
    prefix = "missing structured native trust_ir proof evidence for "
    if not error.startswith(prefix):
        return None
    suite = error[len(prefix) :].split(";", 1)[0].strip().lower()
    return suite if suite in REQUIRED_SUITES else None


def _lowering_symptoms(text: str) -> list[tuple[str, str]]:
    return [
        (match.group("function"), _compact_line(match.group("reason")))
        for match in LOWERING_RE.finditer(text)
    ]


def _symptom_lines(text: str) -> list[str]:
    lines: list[str] = []
    for raw in text.splitlines():
        line = _compact_line(raw)
        if line:
            lines.append(line)
    return lines


def _json_string_text(text: str) -> str:
    if not text.strip():
        return ""
    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        return ""
    strings: list[str] = []
    _collect_strings(value, strings)
    return "\n".join(strings)


def _collect_strings(value: Any, strings: list[str]) -> None:
    if isinstance(value, str):
        strings.append(value)
    elif isinstance(value, Mapping):
        for child in value.values():
            _collect_strings(child, strings)
    elif isinstance(value, list):
        for child in value:
            _collect_strings(child, strings)


def _line_suite(line: str) -> str | None:
    match = SUITE_RE.search(line)
    if match is None:
        return None
    suite = match.group("suite").lower()
    return suite if suite in REQUIRED_SUITES else None


def _compact_line(value: str, limit: int = 240) -> str:
    compact = " ".join(value.strip().split())
    if len(compact) <= limit:
        return compact
    return compact[: limit - 3].rstrip() + "..."


def _structured_native_trust_ir_suites(obj: Mapping[str, Any]) -> set[str]:
    suites: set[str] = set()
    if _is_native_trust_ir_evidence(obj):
        suites.add(str(obj["suite"]).lower())
    for key, value in obj.items():
        if str(key).lower() in {"native_trust_ir", "native_trust_ir_evidence"} and isinstance(value, Mapping):
            if _is_native_trust_ir_evidence(value):
                suites.add(str(value["suite"]).lower())
    return suites


def _structured_proof_evidence(obj: Mapping[str, Any]) -> bool:
    if _is_proof_evidence(obj):
        return True
    for key, value in obj.items():
        if str(key).lower() == "proof_evidence" and isinstance(value, Mapping):
            if _is_proof_evidence(value):
                return True
    return False


def _structured_suites(obj: Mapping[str, Any]) -> set[str]:
    suites: set[str] = set()
    if _is_proof_evidence(obj):
        suites.add(str(obj["suite"]).lower())
    for key, value in obj.items():
        if str(key).lower() == "proof_evidence" and isinstance(value, Mapping):
            if _is_proof_evidence(value):
                suites.add(str(value["suite"]).lower())
    return suites


def _is_native_trust_ir_evidence(obj: Mapping[str, Any]) -> bool:
    suite = _suite_field(obj)
    return (
        suite is not None
        and _nonempty_str(obj.get("backend"))
        and obj.get("present") is True
        and _nonempty_str(obj.get("request_id"))
        and _nonempty_str(obj.get("native_id"))
        and _artifacts_structured(obj.get("artifacts"))
        and _diagnostics_structured(obj.get("diagnostics"))
    )


def _is_proof_evidence(obj: Mapping[str, Any]) -> bool:
    suite = _suite_field(obj)
    status = obj.get("status")
    return (
        suite is not None
        and _nonempty_str(obj.get("backend"))
        and _nonempty_str(obj.get("request_id"))
        and _nonempty_str(obj.get("native_id"))
        and isinstance(status, str)
        and status.lower() == "proved"
        and (
            _strength_structured(obj.get("strength"))
            or _strength_structured(obj.get("evidence"))
        )
        and _artifacts_structured(obj.get("artifacts"))
        and _diagnostics_structured(obj.get("diagnostics"))
    )


def _suite_field(obj: Mapping[str, Any]) -> str | None:
    suite = obj.get("suite")
    if not isinstance(suite, str):
        return None
    suite_l = suite.lower()
    return suite_l if suite_l in REQUIRED_SUITES else None


def _nonempty_str(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _strength_structured(value: Any) -> bool:
    if not isinstance(value, Mapping):
        return False
    return _nonempty_str(value.get("reasoning")) and _nonempty_str(value.get("assurance"))


def _artifacts_structured(value: Any) -> bool:
    if not isinstance(value, list) or not value:
        return False
    return all(_artifact_structured(artifact) for artifact in value)


def _artifact_structured(value: Any) -> bool:
    if not isinstance(value, Mapping) or not _nonempty_str(value.get("kind")):
        return False
    digest = value.get("digest")
    has_digest = (
        isinstance(digest, Mapping)
        and _nonempty_str(digest.get("algorithm"))
        and _nonempty_str(digest.get("value"))
    )
    return has_digest or _nonempty_str(value.get("uri")) or _nonempty_str(value.get("artifact_id"))


def _diagnostics_structured(value: Any) -> bool:
    if not isinstance(value, list):
        return False
    return all(_diagnostic_structured(diagnostic) for diagnostic in value)


def _diagnostic_structured(value: Any) -> bool:
    return (
        isinstance(value, Mapping)
        and _nonempty_str(value.get("code"))
        and _nonempty_str(value.get("severity"))
        and _nonempty_str(value.get("message"))
    )


def _suite_has_structured_field(obj: Mapping[str, Any], suite: str) -> bool:
    for key, value in obj.items():
        key_l = str(key).lower()
        if suite in key_l and _contains_any(key_l, SUITE_KEYS):
            return True
        if _contains_any(key_l, SUITE_KEYS):
            scalar = _scalar_text(value)
            if scalar == suite or scalar.startswith((f"{suite}.", f"{suite}-")):
                return True
    return False


def _explicit_failure(report: Any) -> bool:
    if not isinstance(report, Mapping):
        return False
    success = report.get("success")
    if success is False:
        return True
    status = report.get("status")
    if isinstance(status, str) and status.lower() in {"failed", "failure", "rejected"}:
        return True
    verification = report.get("verification")
    if isinstance(verification, Mapping):
        status = verification.get("status")
        if isinstance(status, str) and status.lower() in {"failed", "failure", "rejected"}:
            return True
    return False


def _object_text(obj: Mapping[str, Any]) -> str:
    return json.dumps(obj, sort_keys=True, default=str).lower()


def _scalar_text(value: Any) -> str:
    if isinstance(value, (str, int, float, bool)) or value is None:
        return str(value).strip().lower()
    return ""


def _contains_any(value: str, needles: Iterable[str]) -> bool:
    value_l = value.lower()
    return any(needle in value_l for needle in needles)


def stage2_tool_candidates(root: Path, tool: str) -> tuple[Path, ...]:
    host = _host_triple()
    return (
        root / "build" / host / "stage2" / "bin" / tool,
        root / "build" / "host" / "stage2" / "bin" / tool,
    )


def discover_stage2_tools(root: Path, tools: Sequence[str]) -> dict[str, Path]:
    found: dict[str, Path] = {}
    missing: list[MissingStage2Tool] = []
    for tool in tools:
        candidates = stage2_tool_candidates(root, tool)
        for candidate in candidates:
            if candidate.exists() and os.access(candidate, os.X_OK):
                found[tool] = candidate
                break
        else:
            missing.append(
                MissingStage2Tool(
                    tool=tool,
                    checked_paths=tuple(str(candidate) for candidate in candidates),
                )
            )
    if missing:
        raise Stage2ToolDiscoveryError(missing)
    return found


def discover_stage2_tool(root: Path, tool: str) -> Path:
    return discover_stage2_tools(root, (tool,))[tool]


def stage2_tool_blockers(exc: Stage2ToolDiscoveryError) -> list[dict[str, Any]]:
    return [
        {
            "kind": "missing_stage2_tool",
            "tool": missing.tool,
            "checked_paths": list(missing.checked_paths),
        }
        for missing in exc.missing
    ]


def build_command(root: Path, samples: Sequence[Path], extra_args: Sequence[str]) -> tuple[list[str], dict[str, str]]:
    tools = discover_stage2_tools(root, ("trustc", "targo"))
    trustc = tools["trustc"]
    targo = tools["targo"]
    env = os.environ.copy()
    env["TRUSTC"] = str(trustc)
    env["RUSTC"] = str(trustc)
    env.setdefault("CARGO_TERM_COLOR", "never")
    return (
        [
            str(targo),
            "trust",
            "check",
            "--format",
            "json",
            *(str(sample) for sample in samples),
            *extra_args,
        ],
        env,
    )


def run_live(args: argparse.Namespace) -> int:
    root = args.repo_root.resolve()
    sample_args = args.sample if args.sample is not None else [DEFAULT_SAMPLE.as_posix()]
    samples = [Path(sample) for sample in sample_args]
    report_dir = args.report_dir
    if not report_dir.is_absolute():
        report_dir = root / report_dir
    report_dir.mkdir(parents=True, exist_ok=True)

    try:
        command, env = build_command(root, samples, args.extra_arg)
    except Stage2ToolDiscoveryError as exc:
        stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
        meta_path = report_dir / f"native-solver-sample-{stamp}.run.json"
        errors = [str(exc)]
        blockers = stage2_tool_blockers(exc)
        meta = {
            "schema": "trust.native-solver-sample-verification.v1",
            "timestamp": stamp,
            "command": None,
            "returncode": None,
            "samples": [str(sample) for sample in samples],
            "tool_discovery": {
                "host_triple": _host_triple(),
                "missing": blockers,
            },
            "gate": {
                "ok": False,
                "errors": errors,
                "warnings": [],
                "suite_paths": {suite: [] for suite in REQUIRED_SUITES},
                "native_trust_ir_paths": [],
            },
            "blockers": blockers,
            "remaining_gap": remaining_gap_report(
                gate_ok=False,
                gate_errors=errors,
                evidence=None,
                blockers=blockers,
            ),
        }
        meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(str(exc), file=sys.stderr)
        print(f"run metadata: {meta_path}")
        return 1

    result = subprocess.run(
        command,
        cwd=root,
        env=env,
        text=True,
        capture_output=True,
        timeout=args.timeout,
        check=False,
    )

    stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    stdout_path = report_dir / f"native-solver-sample-{stamp}.stdout.json"
    stderr_path = report_dir / f"native-solver-sample-{stamp}.stderr.txt"
    meta_path = report_dir / f"native-solver-sample-{stamp}.run.json"
    stdout_path.write_text(result.stdout, encoding="utf-8")
    stderr_path.write_text(result.stderr, encoding="utf-8")

    meta = {
        "schema": "trust.native-solver-sample-verification.v1",
        "timestamp": stamp,
        "command": shlex.join(command),
        "returncode": result.returncode,
        "stdout": str(stdout_path.relative_to(root)),
        "stderr": str(stderr_path.relative_to(root)),
        "samples": [str(sample) for sample in samples],
    }

    try:
        stdout_report = load_json_report(stdout_path)
        gate = evaluate_report(stdout_report)
    except ValueError as exc:
        errors = []
        if result.returncode != 0:
            errors.append(f"verification command returned non-zero ({result.returncode})")
        errors.append(str(exc))
        meta["gate"] = {"ok": False, "errors": errors, "native_trust_ir_paths": []}
        meta["blockers"] = extract_blockers(
            gate_errors=errors,
            native_trust_ir_paths=(),
            returncode=result.returncode,
            stdout_text=result.stdout,
            stderr_text=result.stderr,
        )
        meta["remaining_gap"] = remaining_gap_report(
            gate_ok=False,
            gate_errors=errors,
            evidence=None,
            blockers=meta["blockers"],
        )
        meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(str(exc), file=sys.stderr)
        return 1

    meta["evidence"] = structured_evidence_report(stdout_report)
    meta["proof_grade_status"] = meta["evidence"]["proof_grade_status"]
    gate_errors = list(gate.errors)
    if result.returncode != 0:
        gate_errors.insert(0, f"verification command returned non-zero ({result.returncode})")
    gate_ok = gate.ok and result.returncode == 0

    meta["gate"] = {
        "ok": gate_ok,
        "errors": gate_errors,
        "warnings": list(gate.warnings),
        "suite_paths": {suite: list(paths) for suite, paths in gate.suite_paths.items()},
        "native_trust_ir_paths": list(gate.native_trust_ir_paths),
    }
    meta["blockers"] = extract_blockers(
        gate_errors=gate_errors,
        native_trust_ir_paths=gate.native_trust_ir_paths,
        returncode=result.returncode,
        stdout_text=result.stdout,
        stderr_text=result.stderr,
    )
    meta["remaining_gap"] = remaining_gap_report(
        gate_ok=gate_ok,
        gate_errors=gate_errors,
        evidence=meta["evidence"],
        blockers=meta["blockers"],
    )
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if result.returncode != 0:
        print(f"verification command returned non-zero ({result.returncode}): {shlex.join(command)}")
    print(gate.describe())
    if gate.warnings:
        print("warnings:")
        for warning in gate.warnings:
            print(f"- {warning}")
    print(f"run metadata: {meta_path}")
    return 0 if gate_ok else 1


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument(
        "--sample",
        action="append",
        default=None,
        help="Sample program to verify. May be repeated. Defaults to the three-suite sample.",
    )
    parser.add_argument("--report-dir", type=Path, default=DEFAULT_REPORT_DIR)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument(
        "--check-report",
        type=Path,
        help="Parse and gate an existing JSON report without running stage2 tools.",
    )
    parser.add_argument(
        "--extra-arg",
        action="append",
        default=[],
        help="Additional argument passed after sample paths to targo trust check.",
    )
    return parser.parse_args(argv)


def _host_triple() -> str:
    machine = platform.machine().lower()
    arch = {"arm64": "aarch64", "aarch64": "aarch64", "x86_64": "x86_64", "amd64": "x86_64"}.get(
        machine, machine
    )
    system = platform.system().lower()
    if system == "darwin":
        return f"{arch}-apple-darwin"
    if system == "linux":
        return f"{arch}-unknown-linux-gnu"
    if system.startswith("win"):
        return f"{arch}-pc-windows-msvc"
    return f"{arch}-unknown-{system}"


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.check_report:
        gate = gate_report_file(args.check_report)
        print(gate.describe())
        return 0 if gate.ok else 1
    return run_live(args)


if __name__ == "__main__":
    raise SystemExit(main())
