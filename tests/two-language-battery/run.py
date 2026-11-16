#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0 OR MIT

"""Two-language conformance battery runner.

Runs every program in the battery through the Trust toolchain and records what
the compiler ACTUALLY did, not what the docs claim it does.

The battery's integrity rests on two rules:

1. Negative controls must fail, and must fail FOR THE RIGHT REASON. A file
   expected to be rejected that fails with a parse error or an unresolved name
   is not evidence about verification — it is a broken test that would
   otherwise read as a pass. Those are reported as `reject-wrong-reason` and
   count as failures of the battery, not successes of the compiler.
2. Nothing is scored from a stale or unsealed toolchain. The trustc version
   stamp embeds the superproject HEAD; the runner requires an exact match plus
   a clean superproject and exact submodule pins before writing canonical
   results.

Usage:
    python3 tests/two-language-battery/run.py [--filter PAT] [--output FILE]
    python3 tests/two-language-battery/run.py --canonical --output /external/new.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path


@lru_cache(maxsize=1)
def _trustc_path() -> Path:
    """Resolve the one physical stage2 trustc used by every battery lane.

    Relative explicit paths are interpreted against the repository root, not
    the caller's current directory. Without an override, ask rustup for the
    physical binary once; Tippy is always its sibling.
    """
    explicit = os.environ.get("TRUST_PROBE_TRUSTC")
    if explicit:
        path = Path(explicit)
        if not path.is_absolute():
            path = REPO_ROOT / path
    else:
        rustup = shutil.which("rustup")
        if rustup is None:
            fallback = Path.home() / ".cargo" / "bin" / "rustup"
            rustup = str(fallback) if fallback.is_file() else None
        if rustup is None:
            raise RuntimeError(
                "cannot resolve the trust toolchain: rustup is not on PATH and "
                "TRUST_PROBE_TRUSTC is unset"
            )
        resolved = subprocess.run(
            [rustup, "which", "--toolchain", "trust", "trustc"],
            capture_output=True,
            text=True,
            timeout=60,
            cwd=REPO_ROOT,
        )
        if resolved.returncode != 0 or not resolved.stdout.strip():
            detail = resolved.stderr.strip() or f"exit {resolved.returncode}"
            raise RuntimeError(f"rustup could not resolve trustc: {detail}")
        path = Path(resolved.stdout.strip())

    try:
        path = path.resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(f"cannot resolve measured trustc {path}: {exc}") from exc
    if not path.is_file() or not os.access(path, os.X_OK):
        raise RuntimeError(f"measured trustc is not a regular executable: {path}")
    return path


def _tippy_path() -> Path:
    direct = _trustc_path().parent / "tippy-driver"
    if not direct.is_file() or not os.access(direct, os.X_OK):
        raise RuntimeError(
            "the measured trustc stage2 directory has no regular executable "
            f"tippy-driver sibling: {direct}"
        )
    return direct


def _trustc_cmd() -> list[str]:
    return [str(_trustc_path())]


def _tippy_cmd() -> list[str]:
    return [str(_tippy_path())]


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


BATTERY_DIR = Path(__file__).resolve().parent
REPO_ROOT = BATTERY_DIR.parent.parent

CANONICAL_FIXTURES = {
    "lane-a-rust/a10_saturating_fold.rs": ("A-rust", "pass", "trustc"),
    "lane-a-rust/a11_FRONTIER_rem_measure.rs": ("A-rust", "frontier", "trustc"),
    "lane-a-rust/a12_FRONTIER_multipath_loop.rs": ("A-rust", "frontier", "trustc"),
    "lane-a-rust/a1_saturating_accumulator.rs": ("A-rust", "pass", "trustc"),
    "lane-a-rust/a2_ring_index.rs": ("A-rust", "pass", "trustc"),
    "lane-a-rust/a3_NEG_false_ensures.rs": ("A-rust", "reject", "trustc"),
    "lane-a-rust/a4_gcd_decreases.rs": ("A-rust", "pass", "trustc"),
    "lane-a-rust/a5_NEG_no_descent.rs": ("A-rust", "reject", "trustc"),
    "lane-a-rust/a6_binary_search_loop.rs": ("A-rust", "pass", "trustc"),
    "lane-a-rust/a7_checked_arith.rs": ("A-rust", "pass", "trustc"),
    "lane-a-rust/a8_NEG_wrong_invariant.rs": ("A-rust", "reject", "trustc"),
    "lane-a-rust/a9_bounds_safety.rs": ("A-rust", "pass", "trustc"),
    "lane-b-lean/b1_arith_lemmas.rs": ("B-lean", "pass", "trustc"),
    "lane-b-lean/b2_NEG_bad_proof.rs": ("B-lean", "reject", "trustc"),
    "lane-b-lean/b3_library_composition.rs": ("B-lean", "pass", "trustc"),
    "lane-b-lean/b4_bool_reasoning.rs": ("B-lean", "pass", "trustc"),
    "lane-c-combo/c1_cited_min2.rs": ("C-combo", "pass", "trustc"),
    "lane-c-combo/c2_uncited_defeq.rs": ("C-combo", "pass", "trustc"),
    "lane-c-combo/c3_NEG_divergent_defeq.rs": ("C-combo", "reject", "trustc"),
    "lane-c-combo/c4_island_in_requires.rs": ("C-combo", "frontier", "trustc"),
    "lane-c-combo/c5_NEG_wrong_citation.rs": ("C-combo", "reject", "trustc"),
    "lane-c-combo/c6_readable_select.rs": ("C-combo", "pass", "trustc"),
    "lane-c-combo/c7_theorem_about_the_function.rs": ("C-combo", "pass", "trustc"),
    "lane-d-legacy/d1_kani_contracts.rs": ("D-legacy", "tippy-emits-lean", "tippy"),
    "lane-d-legacy/d2_kani_nondet.rs": ("D-legacy", "tippy-emits-lean", "tippy"),
    "lane-e-ir-spine/e1_both_languages_in_ir.rs": (
        "E-ir-spine",
        "ir-carries-both-languages",
        "trustc",
    ),
    "lane-e-ir-spine/e2_rust_calls_clean_in_ir.rs": (
        "E-ir-spine",
        "ir-links-clean-origin",
        "trustc",
    ),
}

DIRECTIVE_RE = re.compile(r"^//@\s*(battery-[a-z-]+)\s*:\s*(.*?)\s*$", re.MULTILINE)

# Classification runs ONLY over diagnostic prose, never over source-location
# lines. Every diagnostic embeds the absolute path of the file under test —
# which contains "trust" — so matching a marker like "trust" against raw stderr
# classified EVERY failure as a verification rejection, making `reject-correct`
# unfalsifiable. Markers below are therefore verdict phrases the compiler
# actually prints, not vocabulary that could appear in a path.

# "The machinery could not model this." A capability frontier — NOT evidence
# that the tool refuted anything, and never a successful negative control.
FRONTIER_MARKERS = (
    "unsupported",
    "[unknown]",
    "outside the exact",
    "fragment",
    "no full-verification primary owner",
    "awaits sealed",
    "unknown or timed out",
)

# "The file was malformed." A negative control failing only with these has
# proved nothing about verification.
MALFORMED_MARKERS = (
    "expected one of",
    "unexpected token",
    "cannot find",
    "unresolved import",
    "failed to resolve",
    "not found in this scope",
    "mismatched types",
    "unknown start of token",
    "cannot resolve a prelude import",
    "incompatible version of rustc",
    "invalid branded",
)


def diagnostic_prose(stderr: str) -> str:
    """Drop source-location and source-echo lines before classifying.

    rustc renders locations as ` --> /abs/path:line:col` and echoes source with
    a leading `NN | `. Both carry the file's own path and text, which would
    otherwise be matched as if the compiler had said it.
    """
    keep = []
    for line in stderr.splitlines():
        s = line.strip()
        if s.startswith("-->") or s.startswith("::: "):
            continue
        if re.match(r"^\d+\s*\|", s) or s.startswith("|"):
            continue
        keep.append(line)
    return "\n".join(keep).lower()


# Lane D asks whether tippy SUGGESTS the Lean the user should write instead, so
# only the suggestion-bearing parts of a diagnostic can answer it:
#
#   * the code a `help:` carries in backticks, whether rustc renders that help
#     inline on a label line (`   | ^^^ help: msg: `code``), on its own line,
#     or as `= help:`;
#   * the added/replaced lines of a multi-line suggestion (`NN + code`,
#     `NN ~ code`).
#
# A `note:` or a warning message EXPLAINS; it suggests nothing. The previous
# marker list was matched against all diagnostic prose, and on 2026-09-27 (pack
# 5ab8dcccfcb) it scored d1 `tippy-emits-lean` on the `#[kani::proof]` NOTE
# "... Trust's authoritative surfaces are `requires`/`ensures` signature
# clauses and `clean { .. }` Lean islands" while every actual suggestion was a
# Rust clause — a false green by the lane's own target. Inside suggestion code
# only a Lean ARTIFACT counts: a Lean declaration with a signature or body, or
# a `clean { … }` island whose body is more than a `..` placeholder. Source
# echo lines (`NN | …`) are the fixture's own text and never count.
_SOURCE_ECHO_RE = re.compile(r"^\s*(?:\d+|LL)\s*\|")
_SUGGESTION_LINE_RE = re.compile(r"^\s*(?:\d+|LL)\s*[+~]\s?(?P<code>.*)$")
_HELP_RE = re.compile(r"\bhelp:\s*(?P<rest>.*)$")
_BACKTICK_CODE_RE = re.compile(r"`([^`]+)`")
_LEAN_DECLARATION_RE = re.compile(
    r"(?<![\w.])(?:theorem|lemma|def|abbrev|inductive|structure)\s+[A-Za-z_][\w.']*.*?:"
)
_CLEAN_ISLAND_RE = re.compile(r"(?<![\w.])clean\s*\{(?P<body>[^}]*)")
_PLACEHOLDER_ONLY_RE = re.compile(r"^[\s.…]*$")


def _is_lean_artifact(code: str) -> bool:
    if _LEAN_DECLARATION_RE.search(code):
        return True
    return any(
        not _PLACEHOLDER_ONLY_RE.match(m.group("body"))
        for m in _CLEAN_ISLAND_RE.finditer(code)
    )


def suggested_lean_artifacts(text: str) -> list[str]:
    """Return the suggestion code in `text` that is a Lean artifact.

    Empty means tippy suggested no Lean, however often its explanatory prose
    names Lean or `clean { .. }`.
    """
    found = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith(("-->", "::: ")) or _SOURCE_ECHO_RE.match(line):
            continue
        suggestion = _SUGGESTION_LINE_RE.match(line)
        if suggestion:
            candidates = [suggestion.group("code")]
        else:
            help_text = _HELP_RE.search(line)
            if not help_text:
                continue
            candidates = _BACKTICK_CODE_RE.findall(help_text.group("rest"))
        found.extend(code.strip() for code in candidates if _is_lean_artifact(code))
    return found


def is_toolchain_sealed(stamp: dict) -> bool:
    return (
        stamp.get("rustc_vV_exit_code") == 0
        and stamp.get("toolchain_binary") == "trustc"
        and stamp.get("trust_brand_present") is True
        and stamp.get("trustc_sha256") is not None
        and stamp.get("tippy_version_exit_code") == 0
        and stamp.get("tippy_driver_sha256") is not None
        and stamp.get("toolchain_matches_head") is True
        and stamp.get("repo_clean") is True
        and stamp.get("submodules_clean") is True
    )


def submodule_drift_lines(status_output: str) -> list[str]:
    return [
        line
        for line in status_output.splitlines()
        if line.startswith(("+", "-", "U"))
    ]


def toolchain_stamp() -> dict:
    """Record and validate the exact checkout/compiler identity."""
    out = {}
    try:
        trustc = _trustc_path()
        out["trustc_sha256"] = _sha256_file(trustc)
        v = subprocess.run(
            [str(trustc), "-vV"],
            capture_output=True, text=True, timeout=60, cwd=REPO_ROOT,
        )
        out["rustc_vV_exit_code"] = v.returncode
        out["rustc_vV"] = v.stdout.strip()
        m = re.search(r"commit-hash:\s*([0-9a-f]{40})", v.stdout)
        out["toolchain_commit"] = m.group(1) if m else None
        binary = re.search(r"^binary:\s*(\S+)\s*$", v.stdout, re.MULTILINE)
        out["toolchain_binary"] = binary.group(1) if binary else None
        out["trust_brand_present"] = bool(
            re.search(r"^trust:\s*\S+\s*$", v.stdout, re.MULTILINE)
        )
        if v.returncode != 0:
            out["rustc_vV_error"] = v.stderr.strip() or f"exit {v.returncode}"
    except Exception as exc:  # noqa: BLE001 - recorded, not raised
        out["rustc_vV_error"] = str(exc)
        out["toolchain_commit"] = None
        out["trustc_sha256"] = None

    try:
        tippy = _tippy_path()
        out["tippy_driver_sha256"] = _sha256_file(tippy)
        tippy_version = subprocess.run(
            [str(tippy), "--version"],
            capture_output=True,
            text=True,
            timeout=60,
            cwd=REPO_ROOT,
        )
        out["tippy_version_exit_code"] = tippy_version.returncode
        out["tippy_version"] = next(
            (line.strip() for line in tippy_version.stdout.splitlines() if line.strip()),
            None,
        )
    except Exception as exc:  # noqa: BLE001 - recorded, not raised
        out["tippy_version_error"] = str(exc)
        out["tippy_version_exit_code"] = None
        out["tippy_driver_sha256"] = None

    head_proc = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    head = head_proc.stdout.strip() if head_proc.returncode == 0 else ""
    out["repo_head"] = head
    if head_proc.returncode != 0:
        out["repo_head_error"] = head_proc.stderr.strip() or f"exit {head_proc.returncode}"

    status = subprocess.run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    out["repo_clean"] = status.returncode == 0 and not status.stdout
    if status.returncode != 0:
        out["repo_status_error"] = status.stderr.strip() or f"exit {status.returncode}"

    submodules = subprocess.run(
        ["git", "submodule", "status", "--recursive"],
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    drift = submodule_drift_lines(submodules.stdout)
    out["submodules_clean"] = submodules.returncode == 0 and not drift
    if drift:
        out["submodule_drift"] = drift
    if submodules.returncode != 0:
        out["submodule_status_error"] = (
            submodules.stderr.strip() or f"exit {submodules.returncode}"
        )

    tc = out.get("toolchain_commit")
    if tc and head:
        out["toolchain_matches_head"] = tc == head
        if not out["toolchain_matches_head"]:
            behind = subprocess.run(
                ["git", "rev-list", "--count", f"{tc}..HEAD"],
                capture_output=True, text=True, cwd=REPO_ROOT,
            ).stdout.strip()
            out["toolchain_commits_behind_head"] = behind or None
    else:
        out["toolchain_matches_head"] = None
    out["toolchain_sealed"] = is_toolchain_sealed(out)
    return out


def same_measurement_identity(before: dict, after: dict) -> bool:
    """Whether the checkout/compiler identity stayed fixed for the whole run."""
    fields = (
        "rustc_vV_exit_code",
        "rustc_vV",
        "trustc_sha256",
        "toolchain_commit",
        "toolchain_binary",
        "trust_brand_present",
        "tippy_version_exit_code",
        "tippy_version",
        "tippy_driver_sha256",
        "repo_head",
        "repo_clean",
        "submodules_clean",
        "submodule_drift",
        "toolchain_matches_head",
        "toolchain_sealed",
    )
    return all(before.get(field) == after.get(field) for field in fields)


def parse_directives(text: str) -> dict:
    return {k: v for k, v in DIRECTIVE_RE.findall(text)}


def validate_fixture_directives(path: Path, text: str) -> tuple[str, str, str]:
    pairs = DIRECTIVE_RE.findall(text)
    known = {
        "battery-expect",
        "battery-flags",
        "battery-ir-lean-marker",
        "battery-ir-rust-marker",
        "battery-ir-clean-def",
        "battery-lane",
        "battery-tool",
    }
    unknown = sorted({key for key, _ in pairs} - known)
    if unknown:
        raise RuntimeError(f"{path}: unknown battery directive(s): {', '.join(unknown)}")

    counts = {key: sum(1 for found, _ in pairs if found == key) for key in known}
    for required in ("battery-lane", "battery-expect", "battery-flags"):
        if counts[required] != 1:
            raise RuntimeError(
                f"{path}: expected exactly one {required}, found {counts[required]}"
            )
    for optional in known - {"battery-lane", "battery-expect", "battery-flags"}:
        if counts[optional] > 1:
            raise RuntimeError(f"{path}: duplicate {optional} directive")

    directives = dict(pairs)
    return (
        directives["battery-lane"],
        directives["battery-expect"],
        directives.get("battery-tool", "trustc"),
    )


def capture_fixture_inventory(files: list[Path], canonical: bool) -> dict[Path, bytes]:
    actual = {}
    captured = {}
    for path in files:
        if canonical and path.is_symlink():
            raise RuntimeError(f"canonical battery fixture must not be a symlink: {path}")
        try:
            relative = path.relative_to(BATTERY_DIR).as_posix()
            contents = path.read_bytes()
            text = contents.decode("utf-8")
        except (OSError, UnicodeError, ValueError) as exc:
            raise RuntimeError(f"cannot read battery fixture {path}: {exc}") from exc
        if relative in actual:
            raise RuntimeError(f"duplicate battery fixture path: {relative}")
        actual[relative] = validate_fixture_directives(path, text)
        captured[path] = contents

    if canonical and actual != CANONICAL_FIXTURES:
        missing = sorted(CANONICAL_FIXTURES.keys() - actual.keys())
        extra = sorted(actual.keys() - CANONICAL_FIXTURES.keys())
        changed = sorted(
            path
            for path in CANONICAL_FIXTURES.keys() & actual.keys()
            if CANONICAL_FIXTURES[path] != actual[path]
        )
        detail = []
        if missing:
            detail.append(f"missing={missing}")
        if extra:
            detail.append(f"extra={extra}")
        if changed:
            detail.append(f"directive_mismatch={changed}")
        raise RuntimeError(
            # Count DERIVED, never hardcoded: the literal here said "25" while
            # CANONICAL_FIXTURES already held 26, so the message misreported the
            # very manifest it was defending. A hardcoded count in an error about
            # inventory drift is itself inventory drift.
            f"canonical battery inventory differs from the reviewed "
            f"{len(CANONICAL_FIXTURES)}-fixture "
            f"manifest: {'; '.join(detail)}"
        )
    return captured


def fixture_snapshot(captured: dict[Path, bytes]) -> str:
    digest = hashlib.sha256()
    for path, contents in captured.items():
        relative = path.relative_to(BATTERY_DIR).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    return digest.hexdigest()


def validate_output_policy(
    filter_pat: str | None,
    output: Path,
    canonical_output: Path,
    explicit_trustc: bool,
    *,
    canonical: bool = False,
) -> None:
    canonical_run = canonical or output == canonical_output
    if filter_pat and canonical_run:
        raise ValueError(
            "--filter requires a non-canonical --output; refusing to truncate "
            "results.json"
        )
    if canonical_run and not explicit_trustc:
        raise ValueError(
            "canonical results require TRUST_PROBE_TRUSTC to name the exact "
            "stage2 trustc; this also binds Tippy to the sibling driver"
        )


def validate_external_canonical_output(output: Path, root: Path) -> None:
    """Keep new canonical evidence out of the immutable source graph.

    This changes output placement, not the fixture population or toolchain
    requirements. The legacy default results.json remains available explicitly.
    """
    if output.resolve().is_relative_to(root.resolve()):
        raise ValueError("--canonical --output must be outside the source checkout")
    if output.exists() or output.is_symlink():
        raise ValueError("--canonical --output requires a new file; nothing was overwritten")
    if not output.parent.is_dir():
        raise ValueError("--canonical --output requires an existing output directory")


def write_scorecard_atomic(
    output: Path, document: dict, *, create_only: bool = False
) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    output_mode = output.stat().st_mode & 0o777 if output.exists() else 0o644
    fd, temporary = tempfile.mkstemp(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent
    )
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            os.fchmod(handle.fileno(), output_mode)
            json.dump(document, handle, indent=2)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        if create_only:
            # Atomic no-clobber publication, including a file/symlink created
            # after preflight. The temporary is in the same filesystem.
            os.link(temporary, output)
            os.unlink(temporary)
        else:
            os.replace(temporary, output)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def discover(filter_pat: str | None) -> list[Path]:
    files = sorted(p for p in BATTERY_DIR.rglob("*.rs") if p.is_file())
    if filter_pat:
        files = [p for p in files if filter_pat in str(p)]
    return files


# The verification report is machine-readable; parse it instead of guessing
# from vocabulary:
#   Trust verification: 2 proved, 1 failed, 0 unknown, 0 timed out, ...
OBLIGATION_SUMMARY_RE = re.compile(
    r"^\s*(?:(?:=\s*)?note:\s*)?trust verification:\s*"
    r"(\d+)\s+proved,\s*(\d+)\s+failed,\s*(\d+)\s+unknown"
    r"(?:,\s*(\d+)\s+timed out)?", re.IGNORECASE | re.MULTILINE
)

# A kernel rejection wrapper also carries resource, missing-name and internal
# failures. Only an explicit terminal type mismatch can credit a bad proof.
# Likewise the noun "counterexample" may describe failed replay, not a finding.
OBLIGATION_FAILED_RE = re.compile(
    r"^\s*(?:=\s*)?(?:error|note):\s*\[[^\]\n]+\]\s+failed\s+\([^)\n]+\)[:;]",
    re.IGNORECASE | re.MULTILINE,
)
# Since cb1/B2 (2026-09-28) a citation whose POSTCONDITION goal was built and
# refuted leads with that goal: "... audit against this postcondition with
# `result` bound to the imported definition of `f`:". Same verdict, same kernel
# dump; only the head names which goal failed.
KERNEL_TYPE_MISMATCH_RE = re.compile(
    r"^\s*error:\s*(?:clean island declaration rejected:\s*"
    r'|citation `[^`\n]+` failed the strict clean statement/certification audit'
    r'(?: against this postcondition with `result` bound to the imported definition of `[^`\n]+`)?:\s*'
    r'strict certification audit failed:\s*\[termrejected\s*\{\s*error:\s*")'
    r"typemismatch\s*\{\s*expected:",
    re.IGNORECASE | re.MULTILINE,
)
KERNEL_OPTION_MISMATCH_RE = re.compile(
    r"^\s*error:\s*clean island declaration rejected:\s*typemismatch\s*"
    r"\{\s*expected:[^\n]*\(option '[^'\n]+'\)", re.IGNORECASE | re.MULTILINE,
)
KERNEL_INCOMPLETE_MARKERS = (
    "heartbeatexceeded",
    "heartbeat limit exceeded",
    "declarationbudgetexhausted",
    "declaration budget exhausted",
    "excessivememory",
    "excessive memory consumption",
    "deeprecursion",
    "deep recursion detected",
    "recursiondepthexceeded",
    "type checking interrupted",
    "crossvalidationfailure",
    "cross-validation failure",
    "internalinvariant",
    "unknownident",
    "unknownconstant",
)

# Surfaces the front end refuses to model at all.
SURFACE_FRONTIER_MARKERS = (
    "unsupported source-contract call",
    "[unknown]",
    "unsupported",
    "lacked exact kernel/native proof authority",
    "proof evidence unavailable",
    "certification audit failed",
    "failed the strict clean",
)

# Real compiler obligation rows spell the verdict AFTER the kind tag, not
# `[unknown]`: `[hardened_panic_boundary] UNKNOWN (trust-mc): ...`.
UNRESOLVED_VERDICT_RE = re.compile(
    r"\[[^\]\n]+\]\s+(?:unknown|timed[_ -]out)\b", re.IGNORECASE
)


def obligation_counts(stderr: str) -> tuple[int, int, int]:
    """Total (failed, unknown, timed out) across every report in the run."""
    failed = unknown = timed_out = 0
    for _proved, f, u, t in OBLIGATION_SUMMARY_RE.findall(stderr):
        failed += int(f)
        unknown += int(u)
        timed_out += int(t or 0)
    return failed, unknown, timed_out


def classify_failure(stderr: str) -> str:
    """Why did this fail: the proof was refused, unmodellable, or malformed?

    Decided by COUNTS, not vocabulary. An earlier keyword version got this
    backwards twice over: matching raw stderr classified everything as a
    rejection (the file's own path contains "trust"), and then letting any
    "unsupported" substring win classified genuine refutations as frontiers —
    because a report routinely carries unsupported rows for unrelated
    obligations alongside the one real refutation.

    `malformed` still wins outright: if the compiler could not read the
    program, nothing else it printed is evidence about verification.
    """
    prose = diagnostic_prose(stderr)
    if "internal compiler error" in prose:
        return "compiler-failure"
    if any(m in prose for m in MALFORMED_MARKERS) or KERNEL_OPTION_MISMATCH_RE.search(prose):
        return "malformed"
    if any(m in prose for m in KERNEL_INCOMPLETE_MARKERS):
        return "frontier"

    failed, unknown, timed_out = obligation_counts(prose)
    if failed > 0 or KERNEL_TYPE_MISMATCH_RE.search(prose) or OBLIGATION_FAILED_RE.search(prose):
        # At least one obligation was REFUTED, whatever else is unsupported.
        return "refutation"
    if (
        unknown > 0
        or timed_out > 0
        or UNRESOLVED_VERDICT_RE.search(prose)
        or any(m in prose for m in SURFACE_FRONTIER_MARKERS)
    ):
        return "frontier"
    # An aggregate strict-build refusal, an undischarged goal, or missing
    # evidence alone does not say the proposed program/proof was refuted.
    return "unclassified"


def run_one(path: Path, timeout: int, source_path: Path | None = None) -> dict:
    measured_source = source_path or path
    text = measured_source.read_text(encoding="utf-8")
    d = parse_directives(text)
    expect = d.get("battery-expect", "pass")
    lane = d.get("battery-lane", "unknown")
    flags = d.get("battery-flags", "").split()
    tool = d.get("battery-tool", "trustc")

    rec: dict = {
        "file": str(path.relative_to(REPO_ROOT)),
        "lane": lane,
        "expect": expect,
        "tool": tool,
        "flags": flags,
    }

    with tempfile.TemporaryDirectory(prefix="two-lang-battery-") as td:
        if tool == "tippy":
            cmd = _tippy_cmd()
        else:
            cmd = _trustc_cmd()

        # `-Ztrust-dump=ir:` with the direct TrustIr frontend requires an
        # explicit crate name; harmless everywhere else, so it is unconditional.
        crate_name = re.sub(r"[^A-Za-z0-9_]", "_", path.stem)
        cmd += [
            str(measured_source),
            "--edition",
            "2021",
            "--crate-name",
            crate_name,
            "--out-dir",
            td,
        ] + flags

        ir_dir = None
        if expect in ("ir-carries-both-languages", "ir-links-clean-origin"):
            ir_dir = Path(td) / "irdump"
            ir_dir.mkdir(parents=True, exist_ok=True)
            cmd += [f"-Ztrust-dump=ir:{ir_dir}"]

        # The scorecard is committed, so every recorded string is scrubbed of
        # machine-local roots: the checkout path and the per-run temp dir would
        # otherwise bake this machine's home directory into the repository (and
        # trip the publication boundary's forbidden-content guard). Only the
        # STORED copies are normalized — classification below runs on the raw
        # `_full_*` streams, so verdicts are unaffected.
        def portable(s: str) -> str:
            authored = f"<repo>/{rec['file']}"
            return (
                s.replace(str(measured_source), authored)
                .replace(str(REPO_ROOT), "<repo>")
                .replace(td, "<tmp>")
            )

        rec["command"] = portable(" ".join(cmd))
        try:
            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout, cwd=REPO_ROOT,
            )
            rec["exit_code"] = proc.returncode
            # Keep complete diagnostic text for both classification and later
            # inspection. An 8 KB tail loses the first failing obligation in
            # ordinary multi-function reports and forces another compile just
            # to recover the cause. Only stored path spellings are normalized;
            # the classifier still consumes the original complete streams.
            full_stdout, full_stderr = proc.stdout, proc.stderr
            rec["stdout"] = portable(full_stdout)
            rec["stderr"] = portable(full_stderr)
            rec["stdout_truncated"] = False
            rec["stderr_truncated"] = False
            rec["streams_complete"] = True
            rec["_full_stderr"] = full_stderr
            rec["_full_stdout"] = full_stdout

            if ir_dir is not None:
                # The publisher spells the requested crate's canonical text
                # exactly this way. Binary bytes, sidecars, temporary files and
                # other crates cannot supply textual marker or call evidence.
                module_name = f"{crate_name}.trust-ir.txt"
                blobs, names = [], []
                for f in sorted(ir_dir.rglob("*")):
                    if not f.is_file():
                        continue
                    names.append(str(f.relative_to(ir_dir)))
                    if f != ir_dir / module_name:
                        continue
                    blobs.append(f.read_text(encoding="utf-8", errors="replace"))
                rec["ir_module_artifacts"] = [n for n in names if n == module_name]
                rec["ir_artifact_count"] = len(rec["ir_module_artifacts"])
                rec["ir_artifacts"] = names[:50]
                rec["_ir_blob"] = "\n".join(blobs)
                # IR-5 (e2): the linkage verdict reads the coverage sidecar
                # STRUCTURED — never the marker blob (the sidecar is excluded
                # from the blob above, deliberately, and stays excluded).
                if expect == "ir-links-clean-origin":
                    coverage_path = ir_dir / f"{crate_name}.coverage.json"
                    if coverage_path.is_file():
                        rec["_coverage_json"] = coverage_path.read_text(
                            encoding="utf-8", errors="replace"
                        )
        except subprocess.TimeoutExpired as exc:
            # TimeoutExpired may carry bytes even when text=True was requested.
            # Preserve the output already observed, but never score an earlier
            # proof message as a completed compiler result.
            def partial_text(value: str | bytes | None) -> str:
                if isinstance(value, bytes):
                    return value.decode("utf-8", errors="replace")
                return value or ""

            rec["exit_code"] = None
            rec["stdout"] = portable(partial_text(exc.stdout))
            rec["stderr"] = portable(partial_text(exc.stderr))
            rec["stdout_truncated"] = False
            rec["stderr_truncated"] = False
            rec["streams_complete"] = False
            rec["error"] = f"TIMEOUT after {timeout}s"
            rec["verdict"] = "timeout"
            rec["battery_ok"] = False
            return rec

    # Classify on the original complete streams; path-normalized complete
    # copies stay in the scorecard for later diagnosis.
    stderr = rec.pop("_full_stderr", rec["stderr"])
    stdout = rec.pop("_full_stdout", rec["stdout"])
    compiled = rec["exit_code"] == 0

    # rustc's ordinary diagnostic refusal is exit 1. A panic, signal, or
    # launcher failure cannot earn negative-control credit from an earlier
    # proof diagnostic printed before the driver failed.
    if rec["exit_code"] not in (0, 1):
        rec["verdict"] = "driver-failed"
        rec["failure_kind"] = "compiler-failure"
        rec["battery_ok"] = False
        return rec

    if expect == "pass":
        rec["verdict"] = "pass" if compiled else "unexpected-reject"
        rec["battery_ok"] = compiled
        if not compiled:
            rec["failure_kind"] = classify_failure(stderr)

    elif expect == "reject":
        if compiled:
            rec["verdict"] = "FALSE-ACCEPT"
            rec["battery_ok"] = False
        else:
            kind = classify_failure(stderr)
            rec["failure_kind"] = kind
            if kind == "refutation":
                rec["verdict"] = "reject-correct"
                rec["battery_ok"] = True
            elif kind == "frontier":
                # The build failed on an unsupported/unknown row, so the tool
                # never refuted anything. Counting this as a successful
                # negative control would let a capability gap impersonate a
                # proof of rejection.
                rec["verdict"] = "reject-by-frontier"
                rec["battery_ok"] = False
            else:
                rec["verdict"] = "reject-wrong-reason"
                rec["battery_ok"] = False

    elif expect == "frontier":
        # A documented capability gap: the program is legitimate and its
        # contract is true, but some lane cannot model it yet. Recorded as a
        # measurement, not scored as a compiler failure.
        kind = classify_failure(stderr) if not compiled else None
        rec["failure_kind"] = kind
        if compiled:
            rec["verdict"] = "frontier-closed"  # the gap closed — good news
            rec["battery_ok"] = True
        elif kind == "frontier":
            rec["verdict"] = "frontier-confirmed"
            rec["battery_ok"] = True
        elif kind == "refutation":
            rec["verdict"] = "frontier-refuted"  # claims a TRUE clause is false
            rec["battery_ok"] = False
        else:
            rec["verdict"] = "frontier-malformed"
            rec["battery_ok"] = False

    elif expect == "ir-links-clean-origin":
        # IR-5 linkage: the Clean def must be RECORDED (a clean_origin.emitted
        # row) and the Rust caller's call edge must be RE-POINTED at it (a
        # linked row with edges_repointed >= 1, and `call @func.<id>` in the
        # canonical text). Recording without linkage is the honest pre-IR-5
        # verdict `ir-clean-declared-only` — a measurement, not a battery error
        # class of its own invention (the e1 `ir-rust-only` discipline).
        clean_def = d.get("battery-ir-clean-def", "")
        blob = rec.pop("_ir_blob", "")
        coverage_text = rec.pop("_coverage_json", "")
        rec["ir_artifact_count"] = rec.get("ir_artifact_count", 0)
        if not compiled:
            rec["verdict"] = "ir-compile-failed"
            rec["failure_kind"] = classify_failure(stderr)
            rec["battery_ok"] = False
        elif rec["ir_artifact_count"] == 0:
            rec["verdict"] = "ir-no-artifact"
            rec["battery_ok"] = False
        else:
            recorded_func_id = None
            recorded_def_index = None
            linked = False
            try:
                coverage = json.loads(coverage_text) if coverage_text else {}
                clean_origin = coverage.get("clean_origin", {})
                if clean_origin.get("recorded") is True:
                    for row in clean_origin.get("emitted", []):
                        if clean_def and clean_def in str(row.get("def_path", "")):
                            recorded_func_id = row.get("func_id")
                            recorded_def_index = row.get("def_index")
                            break
                if type(recorded_func_id) is int and type(recorded_def_index) is int:
                    for row in clean_origin.get("linked", []):
                        if (
                            row.get("target_func_id") == recorded_func_id
                            and type(row.get("source_def_index")) is int
                            and row.get("source_def_index") == recorded_def_index
                            and type(row.get("decl_func_id")) is int
                            and row.get("edges_repointed", 0) >= 1
                        ):
                            linked = True
                            break
            except (ValueError, TypeError):
                pass
            identities_recorded = (
                type(recorded_func_id) is int and type(recorded_def_index) is int
            )
            call_spelling = f"call @func.{recorded_func_id}(" if identities_recorded else None
            call_in_text = bool(call_spelling) and call_spelling in blob
            rec["clean_recorded_func_id"] = recorded_func_id
            rec["clean_recorded_def_index"] = recorded_def_index
            rec["clean_linked"] = linked
            rec["clean_call_in_text"] = call_in_text
            if not identities_recorded:
                rec["verdict"] = "ir-no-clean-row"
                rec["battery_ok"] = False
            elif linked and call_in_text:
                rec["verdict"] = "ir-links-clean-origin"
                rec["battery_ok"] = True
            else:
                rec["verdict"] = "ir-clean-declared-only"
                rec["battery_ok"] = False

    elif expect == "ir-carries-both-languages":
        rust_marker = d.get("battery-ir-rust-marker")
        lean_marker = d.get("battery-ir-lean-marker")
        blob = rec.pop("_ir_blob", "")
        rec["ir_artifact_count"] = rec.get("ir_artifact_count", 0)
        rust_in_ir = bool(rust_marker) and rust_marker in blob
        lean_in_ir = bool(lean_marker) and lean_marker in blob
        rec["rust_in_ir"] = rust_in_ir
        rec["lean_in_ir"] = lean_in_ir
        if not compiled:
            rec["verdict"] = "ir-compile-failed"
            rec["failure_kind"] = classify_failure(stderr)
            rec["battery_ok"] = False
        elif rec["ir_artifact_count"] == 0:
            rec["verdict"] = "ir-no-artifact"
            rec["battery_ok"] = False
        elif rust_in_ir and lean_in_ir:
            rec["verdict"] = "ir-carries-both-languages"
            rec["battery_ok"] = True
        elif rust_in_ir:
            # The documented state of the spine: Rust reaches TrustIr, the
            # island does not. Not a battery error — a measurement.
            rec["verdict"] = "ir-rust-only"
            rec["battery_ok"] = False
        elif lean_in_ir:
            rec["verdict"] = "ir-lean-only"
            rec["battery_ok"] = False
        else:
            rec["verdict"] = "ir-neither-language"
            rec["battery_ok"] = False

    elif expect == "tippy-emits-lean":
        tippy_prose = diagnostic_prose(stdout + "\n" + stderr)
        # Read the RAW streams, not `tippy_prose`: that view drops every
        # `|`-prefixed line, which is where rustc renders an inline `help:`.
        lean_suggestions = suggested_lean_artifacts(stdout + "\n" + stderr)
        emits_lean = bool(lean_suggestions)
        fired = (
            "legacy" in tippy_prose
            or "spec_sugar" in tippy_prose
            or "spec sugar" in tippy_prose
        )
        rec["lint_fired"] = fired
        rec["emits_lean"] = emits_lean
        rec["lean_suggestions"] = [
            s.replace(str(REPO_ROOT), "<repo>") for s in lean_suggestions[:10]
        ]
        if not compiled:
            rec["verdict"] = "tippy-compile-failed"
            rec["failure_kind"] = classify_failure(stderr)
            rec["battery_ok"] = False
        elif emits_lean:
            rec["verdict"] = "tippy-emits-lean"
            rec["battery_ok"] = True
        elif fired:
            rec["verdict"] = "tippy-fires-but-no-lean"
            rec["battery_ok"] = False
        else:
            rec["verdict"] = "tippy-silent"
            rec["battery_ok"] = False
    else:
        rec["verdict"] = f"unknown-expectation:{expect}"
        rec["battery_ok"] = False

    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--filter", default=None)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument(
        "--canonical",
        action="store_true",
        help=(
            "require the full reviewed fixture population and this checkout's sealed "
            "stage2 tools, writing to a new external --output without dirtying source"
        ),
    )
    ap.add_argument(
        "--output",
        default=None,
        help="Scorecard JSON path (default: canonical results.json for full runs)",
    )
    ap.add_argument(
        "--allow-unsealed-toolchain",
        action="store_true",
        help=(
            "permit an exploratory run with a stale/dirty toolchain; requires "
            "a non-canonical --output"
        ),
    )
    args = ap.parse_args()

    canonical_output = (BATTERY_DIR / "results.json").resolve()
    requested_output = Path(args.output) if args.output else canonical_output
    output = requested_output.resolve()
    if args.canonical and not args.output:
        ap.error("--canonical requires an explicit new external --output")
    canonical_run = args.canonical or output == canonical_output
    if canonical_run and args.allow_unsealed_toolchain:
        ap.error("canonical runs cannot use --allow-unsealed-toolchain")
    try:
        if args.canonical:
            validate_external_canonical_output(requested_output, REPO_ROOT)
        validate_output_policy(
            args.filter,
            output,
            canonical_output,
            bool(os.environ.get("TRUST_PROBE_TRUSTC")),
            canonical=args.canonical,
        )
    except ValueError as exc:
        ap.error(str(exc))

    files = discover(args.filter)
    if not files:
        print("ERROR: battery selection contains no Rust fixtures", file=sys.stderr)
        return 2
    try:
        captured = capture_fixture_inventory(files, canonical_run)
        captured_digest = fixture_snapshot(captured)
    except RuntimeError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    if canonical_run:
        expected_stage2_bin = (REPO_ROOT / "build" / "host" / "stage2" / "bin").resolve()
        try:
            measured_stage2_bin = _trustc_path().parent
        except RuntimeError as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 2
        if measured_stage2_bin != expected_stage2_bin:
            print(
                "ERROR: canonical results must use this checkout's physical "
                f"stage2 bin directory ({expected_stage2_bin}), got "
                f"{measured_stage2_bin}",
                file=sys.stderr,
            )
            return 2

    stamp = toolchain_stamp()
    if stamp.get("toolchain_sealed") is not True:
        reasons = []
        if stamp.get("rustc_vV_exit_code") != 0:
            reasons.append("trustc -vV did not exit successfully")
        if stamp.get("toolchain_binary") != "trustc":
            reasons.append("version stamp is not branded as binary: trustc")
        if stamp.get("trust_brand_present") is not True:
            reasons.append("version stamp has no Trust brand")
        if stamp.get("trustc_sha256") is None:
            reasons.append("trustc binary identity is unavailable")
        if stamp.get("tippy_version_exit_code") != 0:
            reasons.append("sibling tippy-driver --version did not exit successfully")
        if stamp.get("tippy_driver_sha256") is None:
            reasons.append("Tippy binary identity is unavailable")
        if stamp.get("toolchain_matches_head") is not True:
            reasons.append(
                "toolchain commit does not exactly match HEAD"
                + (
                    f" ({stamp.get('toolchain_commits_behind_head')} commits behind)"
                    if stamp.get("toolchain_commits_behind_head")
                    else ""
                )
            )
        if stamp.get("repo_clean") is not True:
            reasons.append("superproject worktree is dirty or unreadable")
        if stamp.get("submodules_clean") is not True:
            reasons.append("submodule pins are dirty, missing, or drifted")
        detail = "; ".join(reasons)
        if not args.allow_unsealed_toolchain:
            print(f"ERROR: refusing unsealed battery run: {detail}", file=sys.stderr)
            return 2
        if output == canonical_output:
            print(
                "ERROR: --allow-unsealed-toolchain requires a non-canonical "
                "--output; refusing to overwrite results.json",
                file=sys.stderr,
            )
            return 2
        print(
            f"WARNING: exploratory unsealed run: {detail}",
            file=sys.stderr,
        )

    results = []
    with tempfile.TemporaryDirectory(prefix="two-lang-battery-input-") as snapshot_dir:
        snapshot_root = Path(snapshot_dir)
        measured_paths = {}
        for path, contents in captured.items():
            measured = snapshot_root / path.relative_to(BATTERY_DIR)
            measured.parent.mkdir(parents=True, exist_ok=True)
            measured.write_bytes(contents)
            measured.chmod(0o444)
            measured_paths[path] = measured

        for path in files:
            rec = run_one(path, args.timeout, measured_paths[path])
            results.append(rec)
            flag = "ok " if rec.get("battery_ok") else "BAD"
            print(f"[{flag}] {rec['lane']:9s} {rec['verdict']:26s} {rec['file']}")

    by_lane: dict[str, dict[str, int]] = {}
    for r in results:
        b = by_lane.setdefault(r["lane"], {"total": 0, "ok": 0})
        b["total"] += 1
        b["ok"] += 1 if r.get("battery_ok") else 0

    summary = {
        "total": len(results),
        "ok": sum(1 for r in results if r.get("battery_ok")),
        "false_accepts": sum(1 for r in results if r.get("verdict") == "FALSE-ACCEPT"),
        "reject_wrong_reason": sum(
            1 for r in results if r.get("verdict") == "reject-wrong-reason"
        ),
        "by_lane": by_lane,
    }

    # D and E are explicit target-spec measurements. Their one known,
    # fail-closed current verdict is permitted alongside the target actually
    # closing; every other result in those lanes is a regression. All A/B/C
    # rows must satisfy their per-file directive.
    permitted_target_verdicts = {
        "D-legacy": {"tippy-fires-but-no-lean", "tippy-emits-lean"},
        "E-ir-spine": {
            "ir-rust-only",
            "ir-carries-both-languages",
            "ir-clean-declared-only",
            "ir-links-clean-origin",
        },
    }
    blocking = []
    for rec in results:
        permitted = permitted_target_verdicts.get(rec["lane"])
        if permitted is not None:
            bad = rec.get("verdict") not in permitted
        else:
            bad = rec.get("battery_ok") is not True
        if bad:
            blocking.append({"file": rec["file"], "verdict": rec.get("verdict")})
    summary["blocking_failures"] = len(blocking)
    summary["blocking_rows"] = blocking

    # Recheck after every compiler invocation and before creating the
    # scorecard. This detects a concurrent pull/edit/submodule move or stage2
    # replacement with a different version stamp; mixed-identity rows never
    # reach even a scratch output.
    final_stamp = toolchain_stamp()
    if not same_measurement_identity(stamp, final_stamp):
        print(
            "ERROR: checkout or compiler identity changed during the battery; "
            "discarding mixed-identity results",
            file=sys.stderr,
        )
        return 2
    try:
        final_files = discover(args.filter)
        final_captured = capture_fixture_inventory(final_files, canonical_run)
        final_digest = fixture_snapshot(final_captured)
    except RuntimeError as exc:
        print(f"ERROR: postflight fixture audit failed: {exc}", file=sys.stderr)
        return 2
    if [path.relative_to(BATTERY_DIR) for path in final_files] != [
        path.relative_to(BATTERY_DIR) for path in files
    ] or final_digest != captured_digest:
        print(
            "ERROR: battery fixture inventory or content changed during the run; "
            "discarding results",
            file=sys.stderr,
        )
        return 2
    if not args.allow_unsealed_toolchain and final_stamp.get("toolchain_sealed") is not True:
        print(
            "ERROR: toolchain lost its sealed identity during the battery; "
            "discarding results",
            file=sys.stderr,
        )
        return 2
    stamp["end_identity_revalidated"] = True
    stamp["fixture_manifest_sha256"] = captured_digest

    doc = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "measurement_scope": "canonical-reviewed-battery" if canonical_run else "exploratory-selection",
        "toolchain": stamp,
        "summary": summary,
        "results": results,
    }
    try:
        if args.canonical:
            validate_external_canonical_output(output, REPO_ROOT)
        write_scorecard_atomic(output, doc, create_only=args.canonical)
    except (OSError, ValueError) as exc:
        print(f"ERROR: scorecard publication refused: {exc}", file=sys.stderr)
        return 2

    print()
    print(f"battery: {summary['ok']}/{summary['total']} as specified")
    for lane, b in sorted(by_lane.items()):
        print(f"  {lane:9s} {b['ok']}/{b['total']}")
    if summary["false_accepts"]:
        print(f"  !! FALSE ACCEPTS: {summary['false_accepts']} (soundness)")
    if summary["reject_wrong_reason"]:
        print(
            f"  !! rejected for the wrong reason: {summary['reject_wrong_reason']} "
            "(battery integrity)"
        )
    if blocking:
        print(f"  !! blocking semantic rows: {len(blocking)}")
        for row in blocking:
            print(f"     {row['verdict']}: {row['file']}")
    print(f"scorecard: {output}")

    # Known D/E target measurements are non-blocking; every other row must
    # satisfy its directive. Staleness and partial-canonical runs have already
    # been rejected before execution.
    return 1 if blocking else 0


if __name__ == "__main__":
    sys.exit(main())
