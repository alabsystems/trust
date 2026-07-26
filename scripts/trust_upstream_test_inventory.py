#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Inventory upstream Rust compiletest suites available in this checkout.

This is a static proof artifact generator: it records which upstream Rust test
roots are locally present, how large each suite is by file category, and the
stage2 trust-vanilla commands reviewers can replay. It intentionally does not
run ``x.py`` and does not modify bootstrap wiring.
"""

from __future__ import annotations

import argparse
import json
import shlex
import subprocess
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
REPORT_SCHEMA = "trust.upstream-rust-test-inventory.v1"
GUARD_SCRIPT = "./scripts/check_upstream_rust_test_toolchain.sh"

# The actual current upstream compiletest suite layout. NOTE: upstream renamed
# `tests/codegen`->`tests/codegen-llvm` and `tests/assembly`->`tests/assembly-llvm`
# (to namespace per-backend), and split `tests/rustdoc` into
# rustdoc-{html,json,js,js-std,gui,ui}. Listing the *current* names here keeps
# the inventory honest: the renamed suites ARE present and must not be reported
# as "missing" coverage gaps just because the pre-rename directory name is gone.
EXPECTED_SUITES: tuple[tuple[str, str], ...] = (
    ("ui", "tests/ui"),
    ("ui-fulldeps", "tests/ui-fulldeps"),
    ("codegen-llvm", "tests/codegen-llvm"),
    ("codegen-units", "tests/codegen-units"),
    ("assembly-llvm", "tests/assembly-llvm"),
    ("mir-opt", "tests/mir-opt"),
    ("incremental", "tests/incremental"),
    ("run-make", "tests/run-make"),
    ("run-make-cargo", "tests/run-make-cargo"),
    ("debuginfo", "tests/debuginfo"),
    ("coverage", "tests/coverage"),
    ("coverage-run-rustdoc", "tests/coverage-run-rustdoc"),
    ("crashes", "tests/crashes"),
    ("pretty", "tests/pretty"),
    ("rustdoc-html", "tests/rustdoc-html"),
    ("rustdoc-json", "tests/rustdoc-json"),
    ("rustdoc-js", "tests/rustdoc-js"),
    ("rustdoc-js-std", "tests/rustdoc-js-std"),
    ("rustdoc-gui", "tests/rustdoc-gui"),
    ("rustdoc-ui", "tests/rustdoc-ui"),
)

LOCAL_NON_UPSTREAM_TEST_DIRS = {
    "__pycache__",
    "auxiliary",
    "cargo_wrapper",
    "compat",
    "context",
    "crash_analysis",
    "evals",
    "fixtures",
    "gh_post",
    "gh_rate_limit",
    "health_check",
    "pulse",
    "test_looper",
    "trust-added",
    "trust-conformance",
    "upstream-rust",
}

SKIP_DIR_NAMES = {
    ".git",
    "__pycache__",
    "build",
    "tmp",
    "target",
}

CATEGORY_BY_EXTENSION = {
    ".rs": "rust_sources",
    ".stderr": "expected_stderr",
    ".stdout": "expected_stdout",
    ".fixed": "expected_fixed",
    ".mir": "mir_dumps",
    ".diff": "mir_or_codegen_diffs",
    ".ll": "llvm_ir",
    ".s": "assembly",
    ".asm": "assembly",
    ".json": "json",
    ".js": "javascript",
    ".css": "css",
    ".html": "html",
    ".md": "markdown",
    ".toml": "toml",
    ".yml": "yaml",
    ".yaml": "yaml",
}

SPECIAL_FILENAMES = {
    "Makefile": "makefiles",
    "rmake.rs": "run_make_drivers",
    "README.md": "readmes",
    "CURRENT_RUSTC_VERSION": "run_make_metadata",
}


def _now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _repo_head(root: Path) -> str | None:
    try:
        result = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    return result.stdout.strip() or None


def _format_command(argv: Sequence[str]) -> str:
    return " ".join(shlex.quote(part) for part in argv)


def _relative(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def _iter_suite_files(root: Path) -> Iterable[Path]:
    for path in root.rglob("*"):
        if any(part in SKIP_DIR_NAMES for part in path.relative_to(root).parts[:-1]):
            continue
        if path.is_file():
            yield path


def _classify_file(path: Path) -> str:
    special = SPECIAL_FILENAMES.get(path.name)
    if special is not None:
        return special
    suffix = path.suffix
    if not suffix:
        return "no_extension"
    return CATEGORY_BY_EXTENSION.get(suffix, "other")


def _count_suite_files(path: Path) -> dict[str, Any]:
    extensions: Counter[str] = Counter()
    categories: Counter[str] = Counter()
    total_files = 0

    for file_path in _iter_suite_files(path):
        total_files += 1
        suffix = file_path.suffix or "<none>"
        extensions[suffix] += 1
        categories[_classify_file(file_path)] += 1

    return {
        "total_files": total_files,
        "by_extension": dict(sorted(extensions.items())),
        "by_category": dict(sorted(categories.items())),
    }


def _sample_commands(relative_root: str | None) -> list[dict[str, Any]]:
    commands: list[dict[str, Any]] = [
        {
            "id": "self-contained-trust-toolchain-preflight",
            "argv": [GUARD_SCRIPT],
            "command": GUARD_SCRIPT,
            "purpose": "Confirm stage2 trustc, targo, targo-trust, and trustd are resolved from the self-contained Trust sysroot.",
        }
    ]
    if relative_root is not None:
        xpy_argv = [
            "./x.py",
            "test",
            "--stage",
            "2",
            "--trust-vanilla",
            "--no-fail-fast",
            relative_root,
        ]
        argv = [GUARD_SCRIPT, "--", *xpy_argv]
        commands.append(
            {
                "id": "suite-stage2-trust-vanilla",
                "argv": argv,
                "command": _format_command(argv),
                "xpy_argv": xpy_argv,
                "xpy_command": _format_command(xpy_argv),
                "purpose": "Replay this suite through stage2 x.py with Trust's vanilla-compatibility mode.",
            }
        )
    return commands


def _expected_suite_rows(root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for name, relative in EXPECTED_SUITES:
        path = root / relative
        present = path.is_dir()
        row: dict[str, Any] = {
            "name": name,
            "root": relative,
            "source": "expected",
            "present": present,
            "supported": present,
            "status": "present" if present else "missing",
            "unsupported_reasons": [] if present else ["suite_root_missing"],
            "counts": _count_suite_files(path) if present else _empty_counts(),
            "sample_commands": _sample_commands(relative if present else None),
        }
        rows.append(row)
    return rows


def _empty_counts() -> dict[str, Any]:
    return {"total_files": 0, "by_extension": {}, "by_category": {}}


def _looks_like_upstream_suite(path: Path) -> bool:
    if not path.is_dir() or path.name in LOCAL_NON_UPSTREAM_TEST_DIRS:
        return False
    if path.name.startswith("."):
        return False
    for child in path.rglob("*"):
        relative_parts = child.relative_to(path).parts
        if any(part in SKIP_DIR_NAMES for part in relative_parts[:-1]):
            continue
        if child.is_dir() and child.name in {"auxiliary", "compiletest-self-test"}:
            return True
        if child.is_file() and (
            child.suffix
            in {".rs", ".stderr", ".stdout", ".mir", ".diff", ".ll", ".s", ".asm"}
            or child.name in SPECIAL_FILENAMES
        ):
            return True
    return False


def _detected_suite_rows(root: Path, known_roots: set[str]) -> list[dict[str, Any]]:
    tests_root = root / "tests"
    if not tests_root.is_dir():
        return []

    rows: list[dict[str, Any]] = []
    for path in sorted(tests_root.iterdir(), key=lambda candidate: candidate.name):
        relative = _relative(path, root)
        if relative in known_roots or not _looks_like_upstream_suite(path):
            continue
        rows.append(
            {
                "name": path.name,
                "root": relative,
                "source": "detected",
                "present": True,
                "supported": True,
                "status": "present",
                "unsupported_reasons": [],
                "counts": _count_suite_files(path),
                "sample_commands": _sample_commands(relative),
            }
        )
    return rows


def build_inventory(root: Path) -> dict[str, Any]:
    root = root.resolve()
    expected = _expected_suite_rows(root)
    known_roots = {row["root"] for row in expected}
    detected = _detected_suite_rows(root, known_roots)
    suites = expected + detected

    summary = {
        "expected_suites": len(expected),
        "detected_extra_suites": len(detected),
        "present_suites": sum(1 for suite in suites if suite["present"]),
        "missing_suites": sum(1 for suite in suites if not suite["present"]),
        "unsupported_suites": sum(1 for suite in suites if not suite["supported"]),
        "total_files": sum(suite["counts"]["total_files"] for suite in suites),
    }

    return {
        "schema": REPORT_SCHEMA,
        "generated_at": _now(),
        "repo_root": str(root),
        "repo_head": _repo_head(root),
        "toolchain_contract": {
            "stage": 2,
            "mode": "trust-vanilla",
            "self_contained_tools": ["trustc", "targo", "targo-trust", "trustd"],
            "preflight": GUARD_SCRIPT,
            "guarded_suite_runner": f"{GUARD_SCRIPT} --",
            "rebuild_guard": "The runner executes an x.py dry-run and refuses planned stage/tool rebuild steps unless explicitly opted in.",
            "rebuild_opt_in": "TRUST_UPSTREAM_TEST_ALLOW_REBUILD=1 or --allow-rebuild",
        },
        "summary": summary,
        "suites": suites,
    }


def write_inventory(report: dict[str, Any], output: Path | None, *, pretty: bool) -> None:
    text = json.dumps(report, indent=2 if pretty else None, sort_keys=pretty)
    if pretty:
        text += "\n"
    if output is None:
        print(text)
        return
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text, encoding="utf-8")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=REPO_ROOT,
        help="Repository checkout to inventory. Defaults to this script's repo.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Write JSON to this path instead of stdout.",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print JSON for review.",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    report = build_inventory(args.root)
    write_inventory(report, args.output, pretty=args.pretty)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
