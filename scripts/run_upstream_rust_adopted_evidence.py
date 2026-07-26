#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Collect adopted upstream Rust test evidence without inventing skips.

The report produced by this runner separates:

* passed checks that actually exited successfully,
* active per-test expected-failure ledger entries, and
* suites or batches that have not run because they require full rebuild/test
  budget.

It is intentionally conservative: a guarded command blocked by the x.py dry-run
rebuild guard is reported as not-yet-run, not as passed or skipped.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence

UTC = timezone.utc


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STAGE2_SYSROOT = REPO_ROOT / "build" / "aarch64-apple-darwin" / "stage2"
GUARD_SCRIPT = "./scripts/check_upstream_rust_test_toolchain.sh"
SCHEMA = "trust.upstream-rust.adopted-execution-report.v1"
SCHEMA_VERSION = "1"
GENERATOR = "scripts/run_upstream_rust_adopted_evidence.py"
GENERATOR_VERSION = "1"
VALIDATION_DATE_ENV = "TRUST_UPSTREAM_COMPAT_VALIDATION_DATE"
BYTES_PER_GIB = 1024 * 1024 * 1024
DEFAULT_MIN_FREE_GIB = 50.0
STATUS_BUCKET_KEYS = (
    "passed",
    "failed",
    "known_expected_failures",
    "not_yet_run_due_to_cost",
    "blocked_by_precondition",
)

REPRESENTATIVE_PATHS = [
    "tests/ui/entry-point/hello-world.rs",
    "tests/codegen-llvm/array-codegen.rs",
    "tests/incremental/hello_world.rs",
]

DIRECT_COMPILETEST_FULL_ROOTS = [
    "tests/ui",
    "tests/ui-fulldeps",
    "tests/codegen-llvm",
    "tests/codegen-units",
    "tests/assembly-llvm",
    "tests/incremental",
    "tests/mir-opt",
    "tests/run-make",
    "tests/run-make-cargo",
    "tests/crashes",
    "tests/debuginfo",
    "tests/coverage",
    "tests/coverage-run-rustdoc",
    "tests/pretty",
    "tests/rustdoc-html",
    "tests/rustdoc-ui",
    "tests/rustdoc-json",
    "tests/rustdoc-js",
    "tests/rustdoc-js-std",
    "tests/rustdoc-gui",
    "tests/build-std",
]

PRIMARY_COMPILETEST_PREFIXES = (
    "tests/assembly/",
    "tests/assembly-llvm/",
    "tests/auxiliary/",
    "tests/build-std/",
    "tests/codegen/",
    "tests/codegen-llvm/",
    "tests/codegen-units/",
    "tests/coverage/",
    "tests/coverage-run-rustdoc/",
    "tests/crashes/",
    "tests/debuginfo/",
    "tests/incremental/",
    "tests/mir-opt/",
    "tests/pretty/",
    "tests/run-make-cargo/",
    "tests/run-make/",
    "tests/run-pass/",
    "tests/run-pass-valgrind/",
    "tests/rustdoc/",
    "tests/rustdoc-gui/",
    "tests/rustdoc-html/",
    "tests/rustdoc-json/",
    "tests/rustdoc-js/",
    "tests/rustdoc-js-std/",
    "tests/rustdoc-ui/",
    "tests/ui/",
    "tests/ui-fulldeps/",
)


@dataclass(frozen=True)
class CommandResult:
    argv: list[str]
    command: str
    exit_status: int | None
    timed_out: bool
    stdout_path: str
    stderr_path: str
    stdout_excerpt: str
    stderr_excerpt: str


@dataclass(frozen=True)
class PlannedCommand:
    argv: list[str]
    command: str


def now_utc() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def today_utc() -> str:
    return datetime.now(UTC).date().isoformat()


def shell_join(argv: Sequence[str]) -> str:
    return " ".join(shlex.quote(arg) for arg in argv)


def rel(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def command_env(stage2_sysroot: Path) -> dict[str, str]:
    env = os.environ.copy()
    bin_dir = stage2_sysroot / "bin"
    lib_dir = stage2_sysroot / "lib"
    env["TRUST_STAGE2_SYSROOT"] = str(stage2_sysroot)
    env["PATH"] = f"{bin_dir}{os.pathsep}{env.get('PATH', '')}"
    if sys.platform == "darwin":
        env["DYLD_LIBRARY_PATH"] = f"{lib_dir}{os.pathsep}{env.get('DYLD_LIBRARY_PATH', '')}"
    else:
        env["LD_LIBRARY_PATH"] = f"{lib_dir}{os.pathsep}{env.get('LD_LIBRARY_PATH', '')}"
    return env


def run_capture(
    argv: Sequence[str],
    *,
    root: Path,
    env: Mapping[str, str],
    log_dir: Path,
    log_id: str,
    timeout: int,
) -> CommandResult:
    stdout_path = log_dir / f"{log_id}.stdout.txt"
    stderr_path = log_dir / f"{log_id}.stderr.txt"
    log_dir.mkdir(parents=True, exist_ok=True)
    timed_out = False
    try:
        completed = subprocess.run(
            list(argv),
            cwd=root,
            env=dict(env),
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        exit_status: int | None = completed.returncode
        stdout = completed.stdout
        stderr = completed.stderr
    except subprocess.TimeoutExpired as error:
        timed_out = True
        exit_status = None
        stdout = error.stdout if isinstance(error.stdout, str) else (error.stdout or b"").decode()
        stderr = error.stderr if isinstance(error.stderr, str) else (error.stderr or b"").decode()
        stderr += f"\nTIMEOUT after {timeout} seconds\n"
    except OSError as error:
        exit_status = 127
        stdout = ""
        stderr = f"failed to execute {shell_join(argv)}: {error}\n"

    stdout_path.write_text(stdout, encoding="utf-8")
    stderr_path.write_text(stderr, encoding="utf-8")
    return CommandResult(
        argv=list(argv),
        command=shell_join(argv),
        exit_status=exit_status,
        timed_out=timed_out,
        stdout_path=rel(stdout_path, root),
        stderr_path=rel(stderr_path, root),
        stdout_excerpt=excerpt(stdout),
        stderr_excerpt=excerpt(stderr),
    )


def excerpt(text: str, *, limit: int = 4000) -> str:
    if len(text) <= limit:
        return text
    return text[:limit] + "\n...[truncated]..."


def git(root: Path, args: Sequence[str]) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=root,
        text=True,
        capture_output=True,
        check=True,
    )
    return completed.stdout.strip()


def parse_trustc_verbose(stdout: str) -> dict[str, str]:
    parsed: dict[str, str] = {}
    for line in stdout.splitlines():
        if ": " in line:
            key, value = line.split(": ", 1)
            parsed[key.strip()] = value.strip()
        elif line.startswith("trustc "):
            parsed["version"] = line.strip()
    return parsed


def load_toml(path: Path) -> dict[str, Any]:
    try:
        import tomllib
    except ModuleNotFoundError as error:
        raise RuntimeError(
            "TOML parsing requires Python 3.11+ with tomllib; use python3.11 or newer"
        ) from error

    with path.open("rb") as handle:
        return tomllib.load(handle)


def baseline_revision(root: Path) -> str:
    baseline = load_toml(root / "tests" / "upstream-rust" / "baseline.toml")
    return str(baseline["upstream"]["revision"])


def tracked_revision(root: Path) -> str | None:
    fixes = load_toml(root / "tests" / "upstream-rust" / "upstream-fixes.toml")
    value = fixes.get("tracked_until_revision")
    return str(value) if value else None


def gibibytes(value: int) -> float:
    return value / BYTES_PER_GIB


def disk_preflight(path: Path, *, min_free_gib: float) -> dict[str, Any]:
    required = int(min_free_gib * BYTES_PER_GIB)
    try:
        usage = shutil.disk_usage(path)
    except OSError as error:
        return {
            "id": "repo_disk_capacity",
            "path": str(path),
            "required_free_gib": min_free_gib,
            "status": "failed",
            "error": str(error),
        }

    shortfall = max(0, required - usage.free)
    status = "passed" if usage.free >= required else "failed"
    return {
        "id": "repo_disk_capacity",
        "path": str(path),
        "total_bytes": usage.total,
        "used_bytes": usage.used,
        "free_bytes": usage.free,
        "free_gib": round(gibibytes(usage.free), 2),
        "required_free_gib": min_free_gib,
        "shortfall_gib": round(gibibytes(shortfall), 2),
        "status": status,
        "cleanup_advice": (
            "free disk space before full upstream Rust scoring, or move this "
            "worktree/build/report output to a larger isolated volume"
        ),
    }


def revision_ref(revision: str) -> str:
    return revision.split(":", 1)[1] if ":" in revision else revision


def is_full_commit_hash(value: str) -> bool:
    return len(value) == 40 and all(char in "0123456789abcdefABCDEF" for char in value)


def active_test_exceptions(root: Path, validation_date: str) -> list[dict[str, Any]]:
    ledger = load_toml(root / "tests" / "upstream-rust" / "test-exceptions.toml")
    active: list[dict[str, Any]] = []
    for row in ledger.get("exceptions", []):
        if row.get("status") != "active":
            continue
        expires_on = str(row.get("expires_on", "9999-12-31"))
        reviewed_on = str(row.get("reviewed_on", "0000-01-01"))
        active.append(
            {
                "id": row.get("id"),
                "test_id": row.get("test_id"),
                "suite": row.get("suite"),
                "path": row.get("path"),
                "revision": row.get("revision"),
                "kind": row.get("kind"),
                "status": row.get("status"),
                "owner": row.get("owner"),
                "issue": row.get("issue"),
                "reviewed_on": reviewed_on,
                "expires_on": expires_on,
                "active_on_validation_date": reviewed_on <= validation_date <= expires_on,
                "observed_in_current_batch": False,
            }
        )
    return active


def upstream_test_counts(root: Path, revision: str) -> dict[str, Any]:
    ref = revision_ref(revision)
    output = git(root, ["ls-tree", "-r", "--name-only", ref, "--", "tests"])
    paths = [line for line in output.splitlines() if line.startswith("tests/")]
    primary = sorted({primary_compiletest_path(path) for path in paths if primary_compiletest_path(path)})
    by_suite: dict[str, int] = {}
    for path in primary:
        suite = path.split("/", 3)[1] if path.startswith("tests/") else "<unknown>"
        by_suite[suite] = by_suite.get(suite, 0) + 1
    return {
        "revision": revision,
        "resolved_revision": ref,
        "test_tree_files": len(paths),
        "primary_compiletest_paths": len(primary),
        "primary_compiletest_by_suite": dict(sorted(by_suite.items())),
    }


def primary_compiletest_path(path: str) -> str | None:
    if not path.startswith(PRIMARY_COMPILETEST_PREFIXES):
        return None
    if path.startswith("tests/run-make/"):
        parts = path.split("/")
        return "/".join(parts[:3]) if len(parts) >= 3 else None
    if path.endswith(".rs") or path.endswith(".js"):
        return path
    return None


def rebuild_guard_lines(stderr: str) -> list[str]:
    pattern = re.compile(r"^(Building|Creating a sysroot|Uplifting library)\b")
    return [line for line in stderr.splitlines() if pattern.search(line)]


def full_suite_commands(stage2_sysroot: Path, baseline: str, tracked: str | None) -> list[dict[str, Any]]:
    bin_dir = stage2_sysroot / "bin"
    lib_dir = stage2_sysroot / "lib"
    env_prefix = [
        f"DYLD_LIBRARY_PATH={lib_dir}${{DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}}",
        f"PATH={bin_dir}:$PATH",
    ]
    commands: list[dict[str, Any]] = []
    for command_id, revision, purpose in [
        (
            "adopted_baseline_release_full",
            baseline,
            "Full release proof for the adopted upstream Rust baseline.",
        ),
        (
            "tracked_upstream_release_full",
            tracked,
            "Full release proof for the latest upstream revision reviewed by the upstream-fix ledger.",
        ),
    ]:
        if revision is None:
            continue
        out_dir = f"reports/upstream-rust/<run-id>/{command_id}"
        argv = [
            str(bin_dir / "targo"),
            "trust",
            "domination",
            "upstream-tests",
            "--release",
            "--proof-mode",
            "full",
            "--upstream-revision",
            revision,
            "--out-dir",
            out_dir,
        ]
        if is_full_commit_hash(revision_ref(revision)):
            argv.extend(["--no-fetch"])
        commands.append(
            {
                "id": command_id,
                "kind": "canonical_release_scorecard",
                "purpose": purpose,
                "command": " ".join(env_prefix + [shell_join(argv)]),
                "argv": argv,
                "not_run_reason": "full upstream Rust suite is expensive and may apply the ported overlay to tests/ by default; run only with clean worktree, time, disk, and source-change budget",
                "claim_after_success": "May claim full suite success only if scorecard.json records executed=true, proof_mode=full, execution_exit_status=0, proof_artifacts_complete=true, validation_failures=[], totals.failed=0, and totals.tool_failures=0 except ledger-accounted failures.",
            }
        )

    guarded_xpy = [
        GUARD_SCRIPT,
        "--",
        "./x.py",
        "test",
        "--stage",
        "2",
        "--trust-vanilla",
        "--no-fail-fast",
        *DIRECT_COMPILETEST_FULL_ROOTS,
    ]
    commands.append(
        {
            "id": "current_tree_direct_compiletest_full",
            "kind": "guarded_xpy_compiletest",
            "purpose": "Direct current-checkout compiletest sweep through the stage2 vanilla Trust compiler. This is not an adopted-baseline overlay proof by itself.",
            "command": f"TRUST_STAGE2_SYSROOT={stage2_sysroot} {shell_join(guarded_xpy)}",
            "argv": guarded_xpy,
            "not_run_reason": "full compiletest sweep is expensive and the representative dry run currently plans stage/tool rebuild work",
            "claim_after_success": "Use as supporting current-tree compiletest evidence only; adopted-baseline release proof still requires the canonical upstream-tests scorecard.",
        }
    )
    return commands


def row_counts_by_status(status_buckets: Mapping[str, Any]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for key in STATUS_BUCKET_KEYS:
        rows = status_buckets.get(key, [])
        counts[key] = len(rows) if isinstance(rows, list) else 0
    counts["total"] = sum(counts.values())
    return counts


def validate_report(report: Mapping[str, Any]) -> list[dict[str, str]]:
    findings: list[dict[str, str]] = []

    if report.get("schema") != SCHEMA:
        findings.append(
            {
                "field": "schema",
                "message": f"expected {SCHEMA!r}, found {report.get('schema')!r}",
            }
        )
    if report.get("schema_version") != SCHEMA_VERSION:
        findings.append(
            {
                "field": "schema_version",
                "message": f"expected {SCHEMA_VERSION!r}, found {report.get('schema_version')!r}",
            }
        )

    generated = report.get("generated")
    if not isinstance(generated, Mapping):
        findings.append({"field": "generated", "message": "generated metadata must be an object"})
    else:
        if generated.get("schema") != SCHEMA:
            findings.append(
                {
                    "field": "generated.schema",
                    "message": f"expected {SCHEMA!r}, found {generated.get('schema')!r}",
                }
            )
        if generated.get("schema_version") != SCHEMA_VERSION:
            findings.append(
                {
                    "field": "generated.schema_version",
                    "message": (
                        f"expected {SCHEMA_VERSION!r}, found "
                        f"{generated.get('schema_version')!r}"
                    ),
                }
            )
        if generated.get("generator_version") != GENERATOR_VERSION:
            findings.append(
                {
                    "field": "generated.generator_version",
                    "message": (
                        f"expected {GENERATOR_VERSION!r}, found "
                        f"{generated.get('generator_version')!r}"
                    ),
                }
            )

    status_buckets = report.get("status_buckets")
    if not isinstance(status_buckets, Mapping):
        findings.append(
            {"field": "status_buckets", "message": "status_buckets must be an object"}
        )
        return findings

    computed_counts = row_counts_by_status(status_buckets)
    declared_counts = report.get("row_counts_by_status")
    if not isinstance(declared_counts, Mapping):
        findings.append(
            {
                "field": "row_counts_by_status",
                "message": "row_counts_by_status must be an object",
            }
        )
        return findings

    for key, computed in computed_counts.items():
        declared = declared_counts.get(key)
        if declared != computed:
            findings.append(
                {
                    "field": f"row_counts_by_status.{key}",
                    "message": f"declared {declared!r}, computed {computed}",
                }
            )

    return findings


def validation_json(findings: Sequence[Mapping[str, str]]) -> dict[str, Any]:
    return {
        "status": "passed" if not findings else "failed",
        "finding_count": len(findings),
        "findings": list(findings),
    }


def build_report(args: argparse.Namespace) -> dict[str, Any]:
    root = args.root.resolve()
    stage2 = args.stage2_sysroot.resolve()
    report_dir = args.output_dir.resolve()
    logs = report_dir / "logs"
    env = command_env(stage2)
    validation_date = args.validation_date

    repo_head = git(root, ["rev-parse", "--verify", "HEAD^{commit}"])
    baseline = baseline_revision(root)
    tracked = tracked_revision(root)
    disk = disk_preflight(root, min_free_gib=args.min_free_gib)

    trustc = run_capture(
        [str(stage2 / "bin" / "trustc"), "-Vv"],
        root=root,
        env=env,
        log_dir=logs,
        log_id="trustc-vv",
        timeout=args.tool_timeout,
    )
    targo = run_capture(
        [str(stage2 / "bin" / "targo"), "-Vv"],
        root=root,
        env=env,
        log_dir=logs,
        log_id="targo-vv",
        timeout=args.tool_timeout,
    )
    targo_trust = run_capture(
        [str(stage2 / "bin" / "targo-trust"), "--version"],
        root=root,
        env=env,
        log_dir=logs,
        log_id="targo-trust-version",
        timeout=args.tool_timeout,
    )
    guard = run_capture(
        [GUARD_SCRIPT],
        root=root,
        env=env,
        log_dir=logs,
        log_id="toolchain-guard",
        timeout=args.guard_timeout,
    )
    representative_argv = [
        GUARD_SCRIPT,
        "--",
        "./x.py",
        "test",
        "--stage",
        "2",
        "--trust-vanilla",
        "--no-fail-fast",
        *REPRESENTATIVE_PATHS,
    ]
    if guard.exit_status == 0 and disk["status"] == "passed":
        representative: CommandResult | PlannedCommand = run_capture(
            representative_argv,
            root=root,
            env=env,
            log_dir=logs,
            log_id="representative-scoped-batch",
            timeout=args.representative_timeout,
        )
        representative_rebuild_lines = rebuild_guard_lines(representative.stderr_excerpt)
        representative_bucket = (
            "passed"
            if representative.exit_status == 0
            else "not_yet_run_due_to_cost"
            if representative_rebuild_lines
            else "failed"
        )
        representative_status = (
            "passed"
            if representative.exit_status == 0
            else "blocked_by_rebuild_guard"
            if representative_rebuild_lines
            else "failed_before_success"
        )
    elif disk["status"] != "passed":
        representative = PlannedCommand(
            argv=representative_argv,
            command=f"TRUST_STAGE2_SYSROOT={stage2} {shell_join(representative_argv)}",
        )
        representative_rebuild_lines = []
        representative_bucket = "blocked_by_precondition"
        representative_status = "not_run_due_to_failed_disk_preflight"
    else:
        representative = PlannedCommand(
            argv=representative_argv,
            command=f"TRUST_STAGE2_SYSROOT={stage2} {shell_join(representative_argv)}",
        )
        representative_rebuild_lines = []
        representative_bucket = "blocked_by_precondition"
        representative_status = "not_run_due_to_failed_toolchain_guard"

    active_exceptions = active_test_exceptions(root, validation_date)
    adopted_counts = upstream_test_counts(root, baseline)
    tracked_counts = upstream_test_counts(root, tracked) if tracked else None

    passed = []
    failed = []
    for check_id, result in [
        ("trustc_identity", trustc),
        ("targo_identity", targo),
        ("targo_trust_identity", targo_trust),
        ("toolchain_guard_preflight", guard),
    ]:
        if result.exit_status == 0:
            passed.append(
                {
                    "id": check_id,
                    "exit_status": 0,
                    "command": result.command,
                    "stdout": result.stdout_path,
                    "stderr": result.stderr_path,
                }
            )
        else:
            failed.append(
                {
                    "id": check_id,
                    "exit_status": result.exit_status,
                    "timed_out": result.timed_out,
                    "command": result.command,
                    "stdout": result.stdout_path,
                    "stderr": result.stderr_path,
                    "stderr_excerpt": result.stderr_excerpt,
                }
            )

    not_yet_run_due_to_cost: list[dict[str, Any]] = []
    if representative_bucket == "not_yet_run_due_to_cost":
        assert isinstance(representative, CommandResult)
        not_yet_run_due_to_cost.append(
            {
                "id": "representative_scoped_batch",
                "attempted": True,
                "exit_status": representative.exit_status,
                "status": representative_status,
                "command": representative.command,
                "stdout": representative.stdout_path,
                "stderr": representative.stderr_path,
                "paths": REPRESENTATIVE_PATHS,
                "reason": "x.py dry-run planned stage/tool rebuild work before compiletest execution",
                "rebuild_guard_lines": representative_rebuild_lines,
            }
        )
    elif representative_bucket == "failed":
        assert isinstance(representative, CommandResult)
        failed.append(
            {
                "id": "representative_scoped_batch",
                "exit_status": representative.exit_status,
                "timed_out": representative.timed_out,
                "command": representative.command,
                "stdout": representative.stdout_path,
                "stderr": representative.stderr_path,
                "stderr_excerpt": representative.stderr_excerpt,
            }
        )

    for command in full_suite_commands(stage2, baseline, tracked):
        not_yet_run_due_to_cost.append(
            {
                "id": command["id"],
                "attempted": False,
                "status": "not_run_due_to_cost",
                "command": command["command"],
                "reason": command["not_run_reason"],
            }
        )

    blocked_by_precondition: list[dict[str, Any]] = []
    if disk["status"] != "passed":
        blocked_by_precondition.append(
            {
                "id": "repo_disk_capacity",
                "attempted": True,
                "status": disk["status"],
                "reason": (
                    f"repo volume has {disk.get('free_gib', 'unknown')} GiB free; "
                    f"requires at least {disk['required_free_gib']} GiB before "
                    "upstream Rust scoring"
                ),
                "disk": disk,
            }
        )
    if representative_bucket == "blocked_by_precondition":
        reason = (
            "disk preflight did not pass for the current checkout, so the "
            "guarded x.py batch was not feasible"
            if representative_status == "not_run_due_to_failed_disk_preflight"
            else "toolchain guard did not pass for the current checkout, so "
            "the guarded x.py batch was not feasible"
        )
        blocked_by_precondition.append(
            {
                "id": "representative_scoped_batch",
                "attempted": False,
                "status": representative_status,
                "command": representative.command,
                "paths": REPRESENTATIVE_PATHS,
                "reason": reason,
                "blocking_command": guard.command,
                "blocking_stderr": guard.stderr_path,
            }
        )

    status_buckets = {
        "passed": passed,
        "failed": failed,
        "known_expected_failures": active_exceptions,
        "not_yet_run_due_to_cost": not_yet_run_due_to_cost,
        "blocked_by_precondition": blocked_by_precondition,
    }
    generated_at = now_utc()
    report = {
        "schema": SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "generated": {
            "schema": SCHEMA,
            "schema_version": SCHEMA_VERSION,
            "generator": GENERATOR,
            "generator_version": GENERATOR_VERSION,
            "generated_at": generated_at,
        },
        "generated_at": generated_at,
        "validation_date": validation_date,
        "repo_root": str(root),
        "repo_head": repo_head,
        "stage2_sysroot": str(stage2),
        "claims": {
            "full_suite_success_claimed": False,
            "representative_compiletest_success_claimed": isinstance(
                representative, CommandResult
            )
            and representative.exit_status == 0,
            "no_fake_skips": True,
            "no_source_overlay_applied": True,
        },
        "preflight": {
            "disk": disk,
        },
        "stage2_tools": {
            "trustc": {
                "path": str(stage2 / "bin" / "trustc"),
                "exit_status": trustc.exit_status,
                "version": parse_trustc_verbose(trustc.stdout_excerpt),
                "stdout": trustc.stdout_path,
                "stderr": trustc.stderr_path,
            },
            "targo": {
                "path": str(stage2 / "bin" / "targo"),
                "exit_status": targo.exit_status,
                "stdout": targo.stdout_path,
                "stderr": targo.stderr_path,
            },
            "targo-trust": {
                "path": str(stage2 / "bin" / "targo-trust"),
                "exit_status": targo_trust.exit_status,
                "stdout": targo_trust.stdout_path,
                "stderr": targo_trust.stderr_path,
            },
        },
        "ledgers": {
            "baseline": "tests/upstream-rust/baseline.toml",
            "baseline_revision": baseline,
            "upstream_fixes": "tests/upstream-rust/upstream-fixes.toml",
            "tracked_until_revision": tracked,
            "test_exceptions": "tests/upstream-rust/test-exceptions.toml",
            "active_test_exceptions": active_exceptions,
        },
        "adopted_upstream_scope": {
            "baseline": adopted_counts,
            "tracked_until": tracked_counts,
        },
        "commands": {
            "toolchain_guard": {
                "status": "passed" if guard.exit_status == 0 else "failed",
                **command_result_json(guard),
            },
            "representative_scoped_batch": {
                "status": representative_status,
                "bucket": representative_bucket,
                "paths": REPRESENTATIVE_PATHS,
                "rebuild_guard_lines": representative_rebuild_lines,
                **command_result_json(representative),
            },
            "full_suite": full_suite_commands(stage2, baseline, tracked),
        },
        "row_counts_by_status": row_counts_by_status(status_buckets),
        "status_buckets": status_buckets,
        "first_executable_batch": {
            "id": "representative_scoped_batch",
            "status": representative_status,
            "bucket": representative_bucket,
            "passed_paths": REPRESENTATIVE_PATHS
            if isinstance(representative, CommandResult) and representative.exit_status == 0
            else [],
            "known_expected_failures_observed": [],
            "not_yet_run_paths": []
            if isinstance(representative, CommandResult) and representative.exit_status == 0
            else REPRESENTATIVE_PATHS,
            "command": representative.command,
        },
    }
    report["validation"] = validation_json(validate_report(report))
    return report


def command_result_json(result: CommandResult | PlannedCommand) -> dict[str, Any]:
    if isinstance(result, PlannedCommand):
        return {
            "argv": result.argv,
            "command": result.command,
            "exit_status": None,
            "timed_out": False,
            "stdout": None,
            "stderr": None,
            "stdout_excerpt": "",
            "stderr_excerpt": "",
        }
    return {
        "argv": result.argv,
        "command": result.command,
        "exit_status": result.exit_status,
        "timed_out": result.timed_out,
        "stdout": result.stdout_path,
        "stderr": result.stderr_path,
        "stdout_excerpt": result.stdout_excerpt,
        "stderr_excerpt": result.stderr_excerpt,
    }


def write_report(report: Mapping[str, Any], output_dir: Path, pretty: bool) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)
    path = output_dir / "adopted-upstream-test-execution.json"
    text = json.dumps(report, indent=2 if pretty else None, sort_keys=pretty)
    if pretty:
        text += "\n"
    path.write_text(text, encoding="utf-8")
    latest = output_dir.parent / "latest-adopted-upstream-test-execution.json"
    latest.write_text(text, encoding="utf-8")
    return path


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    default_run_id = "worker3-adopted-execution-" + datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--stage2-sysroot", type=Path, default=DEFAULT_STAGE2_SYSROOT)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=REPO_ROOT / "reports" / "upstream-rust" / default_run_id,
    )
    parser.add_argument(
        "--validation-date",
        default=os.environ.get(VALIDATION_DATE_ENV, today_utc()),
        help="Date used to evaluate active test exceptions.",
    )
    parser.add_argument("--tool-timeout", type=int, default=60)
    parser.add_argument("--guard-timeout", type=int, default=120)
    parser.add_argument("--representative-timeout", type=int, default=1800)
    parser.add_argument(
        "--min-free-gib",
        type=float,
        default=DEFAULT_MIN_FREE_GIB,
        help="Minimum free space required before running representative upstream scoring.",
    )
    parser.add_argument("--pretty", action="store_true")
    parser.add_argument(
        "--strict-exit",
        action="store_true",
        help="Return nonzero when the report contains failed or precondition-blocked checks.",
    )
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="Run report-shape validation self-checks without executing upstream evidence commands.",
    )
    return parser.parse_args(argv)


def self_check() -> int:
    status_buckets = {
        "passed": [{"id": "toolchain_guard_preflight"}],
        "failed": [{"id": "representative_scoped_batch"}],
        "known_expected_failures": [],
        "not_yet_run_due_to_cost": [{"id": "adopted_baseline_release_full"}],
        "blocked_by_precondition": [],
    }
    report: dict[str, Any] = {
        "schema": SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "generated": {
            "schema": SCHEMA,
            "schema_version": SCHEMA_VERSION,
            "generator": GENERATOR,
            "generator_version": GENERATOR_VERSION,
            "generated_at": "2026-01-01T00:00:00Z",
        },
        "row_counts_by_status": row_counts_by_status(status_buckets),
        "status_buckets": status_buckets,
    }
    findings = validate_report(report)
    if findings:
        print(json.dumps(validation_json(findings), indent=2, sort_keys=True), file=sys.stderr)
        return 1

    mismatched = json.loads(json.dumps(report))
    mismatched["row_counts_by_status"]["passed"] = 99
    mismatch_findings = validate_report(mismatched)
    if not any(finding["field"] == "row_counts_by_status.passed" for finding in mismatch_findings):
        print("self-check failed: row count mismatch was not detected", file=sys.stderr)
        return 1

    print("run_upstream_rust_adopted_evidence.py self-check passed")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.self_check:
        return self_check()
    report = build_report(args)
    path = write_report(report, args.output_dir.resolve(), args.pretty)
    print(path)
    representative = report["commands"]["representative_scoped_batch"]
    validation_failed = report["validation"]["status"] != "passed"
    if args.strict_exit and (
        validation_failed
        or report["status_buckets"]["failed"]
        or report["status_buckets"]["blocked_by_precondition"]
    ):
        return 1
    return 0 if representative["status"] in {
        "passed",
        "blocked_by_rebuild_guard",
        "not_run_due_to_failed_disk_preflight",
        "not_run_due_to_failed_toolchain_guard",
    } else 1


if __name__ == "__main__":
    raise SystemExit(main())
