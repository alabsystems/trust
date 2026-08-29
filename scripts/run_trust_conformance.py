#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Run the Publication V3 trust-conformance corpus.

The initial runner intentionally consumes a manifest plus committed fixture
evidence. Later workers can replace individual checks with stable tool outputs
without changing the report envelope consumed by dscan/dpub.

Exit codes: 0 all cases passed; 1 a case failed; 2 manifest/output error (or
--strict over an incomplete corpus); 3 no failures but a case ran zero checks.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import io
import json
import sys
import tempfile
from collections.abc import Mapping
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO_ROOT / "trust-conformance" / "manifest.json"

MANIFEST_SCHEMA_VERSION = "trust-conformance-manifest/v1"
REPORT_SCHEMA_VERSION = "trust-conformance-report/v1"

EXIT_OK = 0
EXIT_FAILED = 1
EXIT_ERROR = 2
# Distinct from pass and from fail: the corpus ran, but part of it was not evaluated.
EXIT_INCOMPLETE = 3

ALLOWED_CATEGORIES = {
    "deductive",
    "reachability",
    "proof-calculus",
    "temporal-spec",
    "solver-evidence",
    "trust-integration",
}
ALLOWED_STATUSES = ("pass", "fail", "blocked", "waived")


class ManifestError(ValueError):
    """Raised when a conformance manifest is malformed."""


@dataclass(frozen=True)
class CheckResult:
    kind: str
    status: str
    path: str | None = None
    target_path: str | None = None
    pointer: str | None = None
    expected: Any | None = None
    actual: Any | None = None
    message: str | None = None

    def to_dict(self) -> dict[str, Any]:
        required: dict[str, Any] = {
            "kind": self.kind,
            "status": self.status,
        }
        optional = {
            key: value
            for key, value in (
                ("path", self.path),
                ("target_path", self.target_path),
                ("pointer", self.pointer),
                ("expected", self.expected),
                ("actual", self.actual),
                ("message", self.message),
            )
            if value is not None
        }
        return required | optional


def _utc_now() -> str:
    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _load_json(path: Path, kind: str = "manifest") -> Any:
    try:
        return json.loads(path.read_text())
    except FileNotFoundError as exc:
        raise ManifestError(f"{kind} not found: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ManifestError(f"invalid JSON in {path}: {exc}") from exc


def _require_mapping(value: Any, context: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ManifestError(f"{context} must be an object")
    return value


def _require_string(value: Any, context: str) -> str:
    if not isinstance(value, str) or not value:
        raise ManifestError(f"{context} must be a non-empty string")
    return value


def _validate_manifest(manifest: Mapping[str, Any]) -> None:
    schema_version = manifest.get("schema_version")
    if schema_version != MANIFEST_SCHEMA_VERSION:
        raise ManifestError(
            f"schema_version must be {MANIFEST_SCHEMA_VERSION!r}, got {schema_version!r}"
        )

    _require_string(manifest.get("suite"), "suite")
    cases = manifest.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ManifestError("cases must be a non-empty list")

    seen_ids: set[str] = set()
    categories: set[str] = set()
    for index, raw_case in enumerate(cases):
        case = _require_mapping(raw_case, f"cases[{index}]")
        case_id = _require_string(case.get("id"), f"cases[{index}].id")
        if case_id in seen_ids:
            raise ManifestError(f"duplicate case id: {case_id}")
        seen_ids.add(case_id)

        category = _require_string(case.get("category"), f"{case_id}.category")
        if category not in ALLOWED_CATEGORIES:
            raise ManifestError(f"{case_id}.category is not allowed: {category}")
        categories.add(category)

        _require_string(case.get("title"), f"{case_id}.title")
        _require_string(case.get("description"), f"{case_id}.description")

        has_blocked = "blocked" in case
        has_waiver = "waiver" in case
        if has_blocked and has_waiver:
            raise ManifestError(f"{case_id} cannot be both blocked and waived")
        if has_blocked:
            blocked = _require_mapping(case.get("blocked"), f"{case_id}.blocked")
            _require_string(blocked.get("reason"), f"{case_id}.blocked.reason")
        elif has_waiver:
            waiver = _require_mapping(case.get("waiver"), f"{case_id}.waiver")
            _require_string(waiver.get("reason"), f"{case_id}.waiver.reason")
        else:
            checks = case.get("checks")
            if not isinstance(checks, list) or not checks:
                raise ManifestError(f"{case_id}.checks must be a non-empty list")
            for check_index, raw_check in enumerate(checks):
                check = _require_mapping(raw_check, f"{case_id}.checks[{check_index}]")
                kind = _require_string(check.get("kind"), f"{case_id}.checks[{check_index}].kind")
                if kind not in {
                    "file_exists",
                    "json_pointer_equals",
                    "json_pointer_file_sha256_equals",
                }:
                    raise ManifestError(f"{case_id}.checks[{check_index}].kind is not allowed: {kind}")
                _require_string(check.get("path"), f"{case_id}.checks[{check_index}].path")
                if kind in {"json_pointer_equals", "json_pointer_file_sha256_equals"}:
                    _require_string(
                        check.get("pointer"), f"{case_id}.checks[{check_index}].pointer"
                    )
                if kind == "json_pointer_file_sha256_equals":
                    _require_string(
                        check.get("target_path"),
                        f"{case_id}.checks[{check_index}].target_path",
                    )
                if kind == "json_pointer_equals":
                    if "expected" not in check:
                        raise ManifestError(f"{case_id}.checks[{check_index}].expected is required")

    missing = ALLOWED_CATEGORIES - categories
    if missing:
        raise ManifestError("manifest does not cover categories: " + ", ".join(sorted(missing)))


def _resolve_repo_path(repo_root: Path, raw_path: str) -> Path:
    path = Path(raw_path)
    if path.is_absolute():
        raise ManifestError(f"manifest paths must be relative: {raw_path}")
    resolved = (repo_root / path).resolve()
    try:
        resolved.relative_to(repo_root.resolve())
    except ValueError as exc:
        raise ManifestError(f"manifest path escapes repository root: {raw_path}") from exc
    return resolved


def _json_pointer_get(document: Any, pointer: str) -> Any:
    if pointer == "":
        return document
    if not pointer.startswith("/"):
        raise ManifestError(f"JSON pointer must start with '/': {pointer}")

    value = document
    for raw_token in pointer.split("/")[1:]:
        token = raw_token.replace("~1", "/").replace("~0", "~")
        if isinstance(value, Mapping):
            if token not in value:
                raise KeyError(token)
            value = value[token]
        elif isinstance(value, list):
            try:
                value = value[int(token)]
            except (ValueError, IndexError) as exc:
                raise KeyError(token) from exc
        else:
            raise KeyError(token)
    return value


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _normalize_sha256(value: str) -> str:
    return value.removeprefix("sha256:").lower()


def _run_check(repo_root: Path, check: Mapping[str, Any]) -> CheckResult:
    kind = str(check["kind"])
    raw_path = str(check["path"])
    path = _resolve_repo_path(repo_root, raw_path)

    if kind == "file_exists":
        if path.is_file():
            return CheckResult(kind=kind, status="pass", path=raw_path)
        return CheckResult(kind=kind, status="fail", path=raw_path, message="file is missing")

    if kind == "json_pointer_equals":
        pointer = str(check["pointer"])
        expected = check["expected"]
        try:
            document = _load_json(path, kind="evidence file")
            actual = _json_pointer_get(document, pointer)
        except (ManifestError, KeyError) as exc:
            return CheckResult(
                kind=kind,
                status="fail",
                path=raw_path,
                pointer=pointer,
                expected=expected,
                message=str(exc),
            )
        if actual == expected:
            return CheckResult(
                kind=kind,
                status="pass",
                path=raw_path,
                pointer=pointer,
                expected=expected,
                actual=actual,
            )
        return CheckResult(
            kind=kind,
            status="fail",
            path=raw_path,
            pointer=pointer,
            expected=expected,
            actual=actual,
            message="JSON value did not match expected value",
        )

    if kind == "json_pointer_file_sha256_equals":
        pointer = str(check["pointer"])
        raw_target_path = str(check["target_path"])
        target_path = _resolve_repo_path(repo_root, raw_target_path)
        try:
            document = _load_json(path, kind="evidence file")
            actual = _json_pointer_get(document, pointer)
            expected_digest = _sha256_file(target_path)
        except (ManifestError, KeyError, FileNotFoundError) as exc:
            return CheckResult(
                kind=kind,
                status="fail",
                path=raw_path,
                target_path=raw_target_path,
                pointer=pointer,
                message=str(exc),
            )
        if not isinstance(actual, str):
            return CheckResult(
                kind=kind,
                status="fail",
                path=raw_path,
                target_path=raw_target_path,
                pointer=pointer,
                actual=actual,
                message="JSON value is not a string sha256 digest",
            )
        expected = f"sha256:{expected_digest}"
        if _normalize_sha256(actual) == expected_digest:
            return CheckResult(
                kind=kind,
                status="pass",
                path=raw_path,
                target_path=raw_target_path,
                pointer=pointer,
                expected=expected,
                actual=actual,
            )
        return CheckResult(
            kind=kind,
            status="fail",
            path=raw_path,
            target_path=raw_target_path,
            pointer=pointer,
            expected=expected,
            actual=actual,
            message="JSON sha256 digest did not match target file",
        )

    raise ManifestError(f"unsupported check kind: {kind}")


def _case_evidence(case: Mapping[str, Any]) -> list[str]:
    raw_evidence = case.get("evidence", [])
    if not isinstance(raw_evidence, list):
        raise ManifestError(f"{case['id']}.evidence must be a list")
    return [_require_string(item, f"{case['id']}.evidence[]") for item in raw_evidence]


def _run_case(repo_root: Path, case: Mapping[str, Any]) -> dict[str, Any]:
    result: dict[str, Any] = {
        "id": case["id"],
        "category": case["category"],
        "title": case["title"],
        "evidence": _case_evidence(case),
    }
    if "waiver" in case:
        waiver = _require_mapping(case["waiver"], f"{case['id']}.waiver")
        result.update(
            {
                "status": "waived",
                "reason": waiver["reason"],
                "waiver": dict(waiver),
                "checks": [],
            }
        )
        return result

    if "blocked" in case:
        blocked = _require_mapping(case["blocked"], f"{case['id']}.blocked")
        result.update(
            {
                "status": "blocked",
                "reason": blocked["reason"],
                "blocked": dict(blocked),
                "checks": [],
            }
        )
        return result

    checks = [
        _run_check(repo_root, _require_mapping(check, f"{case['id']}.checks[]"))
        for check in case["checks"]
    ]
    status = "pass" if all(check.status == "pass" for check in checks) else "fail"
    result.update(
        {
            "status": status,
            "checks": [check.to_dict() for check in checks],
        }
    )
    return result


def _categories_without_executed_checks(results: list[dict[str, Any]]) -> list[str]:
    """`_validate_manifest` counts a blocked/waived case as category coverage, so a category can be
    'covered' while running zero checks. Name those categories rather than let them read as covered."""
    declared: set[str] = set()
    executed: set[str] = set()
    for result in results:
        category = str(result["category"])
        declared.add(category)
        if result["checks"]:
            executed.add(category)
    return sorted(declared - executed)


def _emit_failure_notice(report: Mapping[str, Any]) -> None:
    """With --output the report leaves stdout entirely, so name the failures on stderr too."""
    if not report["summary"]["fail"]:
        return
    print("trust-conformance FAILED:", file=sys.stderr)
    for result in report["results"]:
        if result["status"] != "fail":
            continue
        print(f"  {result['id']} [{result['category']}]", file=sys.stderr)
        for check in result["checks"]:
            if check["status"] == "fail":
                detail = check.get("message") or "check failed"
                print(f"    {check['kind']} {check.get('path', '')}: {detail}", file=sys.stderr)


def _emit_incomplete_notice(report: Mapping[str, Any]) -> bool:
    """Blocked/waived cases execute zero checks; staying silent is how a retired case reads as green."""
    summary = report["summary"]
    if not (summary["blocked"] or summary["waived"]):
        return False
    print(
        "trust-conformance INCOMPLETE: the cases below executed ZERO checks "
        "and prove nothing about their category.",
        file=sys.stderr,
    )
    for result in report["results"]:
        if result["status"] in {"blocked", "waived"}:
            reason = result.get("reason") or "no reason recorded"
            print(
                f"  {result['status']}: {result['id']} [{result['category']}]: {reason}",
                file=sys.stderr,
            )
    uncovered = report.get("categories_without_executed_checks") or []
    if uncovered:
        print(
            "  categories with NO executed checks: " + ", ".join(uncovered),
            file=sys.stderr,
        )
    return True


def run_manifest(
    manifest_path: Path = DEFAULT_MANIFEST,
    *,
    repo_root: Path = REPO_ROOT,
    generated_at: str | None = None,
) -> dict[str, Any]:
    """Run a trust-conformance manifest and return a JSON-serializable report."""
    manifest_path = manifest_path.resolve()
    repo_root = repo_root.resolve()
    manifest = _require_mapping(_load_json(manifest_path), "manifest")
    _validate_manifest(manifest)

    results = [_run_case(repo_root, _require_mapping(case, "case")) for case in manifest["cases"]]
    summary = {"total": len(results), "pass": 0, "fail": 0, "blocked": 0, "waived": 0}
    for result in results:
        summary[str(result["status"])] += 1

    return {
        "schema_version": REPORT_SCHEMA_VERSION,
        "generated_at": generated_at or _utc_now(),
        "manifest": {
            "path": str(manifest_path.relative_to(repo_root))
            if manifest_path.is_relative_to(repo_root)
            else str(manifest_path),
            "schema_version": manifest["schema_version"],
            "suite": manifest["suite"],
            "issue": manifest.get("issue"),
        },
        "summary": summary,
        "results": results,
        "blocked": [result["id"] for result in results if result["status"] == "blocked"],
        "waived": [result["id"] for result in results if result["status"] == "waived"],
        "categories_without_executed_checks": _categories_without_executed_checks(results),
    }


def _contained_output_path(
    path: Path,
    *,
    repo_root: Path,
    allow_outside_root: bool,
) -> Path:
    resolved = path.resolve() if path.is_absolute() else (repo_root / path).resolve()
    resolved_root = repo_root.resolve()
    if allow_outside_root:
        return resolved
    try:
        resolved.relative_to(resolved_root)
    except ValueError as exc:
        raise ManifestError(
            f"--output must stay within --repo-root ({resolved_root}); "
            "pass --allow-outside-root to override"
        ) from exc
    return resolved


def _write_report(
    report: Mapping[str, Any],
    output: Path | None,
    *,
    repo_root: Path,
    allow_outside_root: bool,
) -> None:
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if output is None:
        print(text, end="")
        return
    output = _contained_output_path(
        output,
        repo_root=repo_root,
        allow_outside_root=allow_outside_root,
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)


def _planted_manifest(tmp_dir: Path, name: str, retire_key: str) -> Path:
    """Retire every case: a zero-check corpus that still claims all six categories."""
    manifest = json.loads(DEFAULT_MANIFEST.read_text())
    for case in manifest["cases"]:
        for key in ("checks", "blocked", "waiver"):
            case.pop(key, None)
        case[retire_key] = {"reason": "planted by --selftest"}
    path = tmp_dir / name
    path.write_text(json.dumps(manifest, indent=2))
    return path


def _run_cli(argv: list[str]) -> tuple[int, str]:
    err = io.StringIO()
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
        code = main(argv)
    return code, err.getvalue()


def run_selftest() -> int:
    """Plant retired cases through main() and watch the silent-green path fail."""
    failures = 0

    def check(label: str, ok: bool, detail: str) -> None:
        nonlocal failures
        print(f"selftest: {'ok  ' if ok else 'FAIL'} {label}: {detail}")
        if not ok:
            failures += 1

    with tempfile.TemporaryDirectory() as raw_tmp:
        tmp = Path(raw_tmp)

        for retire_key in ("blocked", "waiver"):
            planted = _planted_manifest(tmp, f"all_{retire_key}.json", retire_key)
            code, err = _run_cli(["--manifest", str(planted)])
            check(
                f"every case {retire_key} cannot exit 0",
                code == EXIT_INCOMPLETE,
                f"exit={code} (want {EXIT_INCOMPLETE})",
            )
            check(
                f"every case {retire_key} prints the loud notice",
                "INCOMPLETE" in err,
                f"stderr={err.strip().splitlines()[0][:70]!r}" if err.strip() else "stderr EMPTY",
            )
            check(
                f"every case {retire_key} names its uncovered categories",
                "categories with NO executed checks" in err,
                f"category line present={'categories with NO executed checks' in err}",
            )

        code, _ = _run_cli(["--manifest", str(tmp / "all_blocked.json"), "--strict"])
        check("--strict keeps its exit 2", code == EXIT_ERROR, f"exit={code} (want {EXIT_ERROR})")

        code, err = _run_cli(["--manifest", str(DEFAULT_MANIFEST)])
        check(
            "unretired corpus prints no INCOMPLETE notice",
            "INCOMPLETE" not in err,
            f"exit={code}",
        )
        check("unretired corpus never exits 3", code != EXIT_INCOMPLETE, f"exit={code}")
        check(
            "a failing corpus names its failures on stderr",
            code != EXIT_FAILED or "trust-conformance FAILED:" in err,
            f"exit={code}, notice present={'trust-conformance FAILED:' in err}",
        )

    print(f"selftest: {f'FAIL - {failures} check(s)' if failures else 'all checks passed'}")
    return EXIT_FAILED if failures else EXIT_OK


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run trust-conformance checks.")
    parser.add_argument(
        "--manifest",
        type=Path,
        default=DEFAULT_MANIFEST,
        help="Conformance manifest path.",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=REPO_ROOT,
        help="Repository root used to resolve manifest evidence paths.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Write JSON report to this path instead of stdout.",
    )
    parser.add_argument(
        "--allow-outside-root",
        action="store_true",
        help="Allow --output to write outside --repo-root.",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Report blocked/waived cases as exit 2 rather than the default exit 3.",
    )
    parser.add_argument(
        "--selftest",
        action="store_true",
        help="Plant retired cases through main() and assert they cannot exit 0.",
    )
    args = parser.parse_args(argv)

    if args.selftest:
        return run_selftest()

    try:
        report = run_manifest(args.manifest, repo_root=args.repo_root)
    except ManifestError as exc:
        print(f"trust-conformance manifest error: {exc}", file=sys.stderr)
        return EXIT_ERROR

    try:
        _write_report(
            report,
            args.output,
            repo_root=args.repo_root,
            allow_outside_root=args.allow_outside_root,
        )
    except ManifestError as exc:
        print(f"trust-conformance output error: {exc}", file=sys.stderr)
        return EXIT_ERROR
    if args.output is not None:
        print(f"Wrote trust-conformance report: {args.output}", file=sys.stderr)

    _emit_failure_notice(report)
    incomplete = _emit_incomplete_notice(report)

    if report["summary"]["fail"] > 0:
        return EXIT_FAILED
    if args.strict and incomplete:
        return EXIT_ERROR
    # Both callers run bare (`fast.trust-conformance`; targo release_validate `fixed_args: &[]`),
    # so exiting 0 here would let a waiver retire a whole category with a silent green.
    if incomplete:
        return EXIT_INCOMPLETE
    return EXIT_OK


if __name__ == "__main__":
    raise SystemExit(main())
