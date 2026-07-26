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
2. Nothing is scored from a stale toolchain. The trustc version stamp embeds
   the superproject HEAD; the runner records both and flags a mismatch.

Usage:
    python3 tests/two-language-battery/run.py [--filter PAT] [--output FILE]
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

BATTERY_DIR = Path(__file__).resolve().parent
REPO_ROOT = BATTERY_DIR.parent.parent

DIRECTIVE_RE = re.compile(r"^//@\s*(battery-[a-z-]+)\s*:\s*(.*?)\s*$", re.MULTILINE)

# Classification runs ONLY over diagnostic prose, never over source-location
# lines. Every diagnostic embeds the absolute path of the file under test —
# which contains "trust" — so matching a marker like "trust" against raw stderr
# classified EVERY failure as a verification rejection, making `reject-correct`
# unfalsifiable. Markers below are therefore verdict phrases the compiler
# actually prints, not vocabulary that could appear in a path.

# "The proof was refused." Only these justify scoring a negative control as a
# successful rejection.
REFUTATION_MARKERS = (
    "strict verification failed",
    "safety verification incomplete",
    "obligation(s) were not",
    "[failed]",
    "were not fully verified",
    "were not proved",
    "counterexample",
    "does not typecheck",
    "kernel rejected",
    "type mismatch",
    "undischarged",
    "citation does not",
)

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

LEAN_EMISSION_MARKERS = ("clean {", "clean{", "theorem ", ":= fun", "rfl")


def toolchain_stamp() -> dict:
    """Record which compiler produced these results, and whether it is HEAD."""
    out = {}
    try:
        v = subprocess.run(
            ["rustup", "run", "trust", "rustc", "-vV"],
            capture_output=True, text=True, timeout=60, cwd=REPO_ROOT,
        )
        out["rustc_vV"] = v.stdout.strip()
        m = re.search(r"commit-hash:\s*([0-9a-f]+)", v.stdout)
        out["toolchain_commit"] = m.group(1) if m else None
    except Exception as exc:  # noqa: BLE001 - recorded, not raised
        out["rustc_vV_error"] = str(exc)
        out["toolchain_commit"] = None

    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        capture_output=True, text=True, cwd=REPO_ROOT,
    ).stdout.strip()
    out["repo_head"] = head

    tc = out.get("toolchain_commit")
    if tc and head:
        out["toolchain_matches_head"] = head.startswith(tc) or tc.startswith(head[:len(tc)])
        if not out["toolchain_matches_head"]:
            behind = subprocess.run(
                ["git", "rev-list", "--count", f"{tc}..HEAD"],
                capture_output=True, text=True, cwd=REPO_ROOT,
            ).stdout.strip()
            out["toolchain_commits_behind_head"] = behind or None
    else:
        out["toolchain_matches_head"] = None
    return out


def parse_directives(text: str) -> dict:
    return {k: v for k, v in DIRECTIVE_RE.findall(text)}


def discover(filter_pat: str | None) -> list[Path]:
    files = sorted(p for p in BATTERY_DIR.rglob("*.rs") if p.is_file())
    if filter_pat:
        files = [p for p in files if filter_pat in str(p)]
    return files


# The verification report is machine-readable; parse it instead of guessing
# from vocabulary:
#   Trust verification: 2 proved, 1 failed, 0 unknown, 0 timed out, ...
OBLIGATION_SUMMARY_RE = re.compile(
    r"trust verification:\s*(\d+)\s+proved,\s*(\d+)\s+failed,\s*(\d+)\s+unknown", re.IGNORECASE
)

# Kernel-level refusals carry no obligation summary — the Clean kernel rejected
# the TERM itself, which is the strongest refutation available.
KERNEL_REFUTATION_MARKERS = (
    "declaration rejected",
    "typemismatch",
    "termrejected",
    "failed the strict clean",
    "certification audit failed",
)

# Surfaces the front end refuses to model at all.
SURFACE_FRONTIER_MARKERS = (
    "unsupported source-contract call",
    "[unknown]",
    "unsupported",
)


def obligation_counts(stderr: str) -> tuple[int, int]:
    """Total (failed, unknown) across every verification report in the run."""
    failed = unknown = 0
    for _proved, f, u in OBLIGATION_SUMMARY_RE.findall(stderr):
        failed += int(f)
        unknown += int(u)
    return failed, unknown


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
    if any(m in prose for m in MALFORMED_MARKERS):
        return "malformed"

    failed, unknown = obligation_counts(prose)
    if failed > 0:
        # At least one obligation was REFUTED, whatever else is unsupported.
        return "refutation"
    if any(m in prose for m in KERNEL_REFUTATION_MARKERS):
        return "refutation"
    if unknown > 0 or any(m in prose for m in SURFACE_FRONTIER_MARKERS):
        return "frontier"
    if any(m in prose for m in REFUTATION_MARKERS):
        return "refutation"
    return "unclassified"


def run_one(path: Path, timeout: int) -> dict:
    text = path.read_text(encoding="utf-8", errors="replace")
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
        # The rustup `trust` toolchain is a SYMLINK to build/host/stage2, and
        # the branded frontend-identity check refuses a toolchain directory
        # that traverses a symlink ("invalid branded Tippy driver identity").
        # Invoke the real binary directly so lane D measures the lint rather
        # than the launcher.
        if tool == "tippy":
            # .resolve() matters twice over: `build/host` is itself a symlink
            # to `build/<triple>`, and the identity check rejects ANY symlink
            # in the toolchain path, not just the rustup one.
            direct = (REPO_ROOT / "build" / "host" / "stage2" / "bin" / "tippy-driver").resolve()
            cmd = [str(direct)] if direct.exists() else ["rustup", "run", "trust", "tippy-driver"]
        else:
            cmd = ["rustup", "run", "trust", "trustc"]

        # `-Ztrust-dump=ir:` with the direct TrustIr frontend requires an
        # explicit crate name; harmless everywhere else, so it is unconditional.
        crate_name = re.sub(r"[^A-Za-z0-9_]", "_", path.stem)
        cmd += [str(path), "--edition", "2021", "--crate-name", crate_name, "--out-dir", td] + flags

        ir_dir = None
        if expect == "ir-carries-both-languages":
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
            return s.replace(str(REPO_ROOT), "<repo>").replace(td, "<tmp>")

        rec["command"] = portable(" ".join(cmd))
        try:
            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout, cwd=REPO_ROOT,
            )
            rec["exit_code"] = proc.returncode
            # Keep the FULL streams for classification and truncate only for
            # storage. Classifying the stored excerpt is a silent verdict
            # corrupter: Trust's reports are long, and the per-function
            # "N proved, M failed" summary that decides refutation-vs-frontier
            # routinely falls outside an 8 KB tail.
            full_stdout, full_stderr = proc.stdout, proc.stderr
            rec["stdout"] = portable(full_stdout[-8000:])
            rec["stderr"] = portable(full_stderr[-8000:])
            rec["stderr_truncated"] = len(full_stderr) > 8000
            rec["_full_stderr"] = full_stderr
            rec["_full_stdout"] = full_stdout

            if ir_dir is not None:
                # Read every published artifact as text; the markers are
                # distinctive identifiers, so a substring hit is evidence the
                # language reached the module.
                blobs, names = [], []
                for f in sorted(ir_dir.rglob("*")):
                    if not f.is_file():
                        continue
                    names.append(str(f.relative_to(ir_dir)))
                    # Search ONLY the TrustIr module artifacts. The coverage
                    # sidecar and the publication lock live in the same
                    # directory and carry unrelated identifiers, which would
                    # let a marker "appear in the IR" without being in the IR.
                    if ".trust-ir." not in f.name:
                        continue
                    blobs.append(f.read_text(encoding="utf-8", errors="replace"))
                rec["ir_module_artifacts"] = [n for n in names if ".trust-ir." in n]
                rec["ir_artifact_count"] = len(rec["ir_module_artifacts"])
                rec["ir_artifacts"] = names[:50]
                rec["_ir_blob"] = "\n".join(blobs)
        except subprocess.TimeoutExpired:
            rec["exit_code"] = None
            rec["stdout"] = ""
            rec["stderr"] = f"TIMEOUT after {timeout}s"
            rec["verdict"] = "timeout"
            rec["battery_ok"] = False
            return rec

    # Classify on the complete streams; the truncated copies stay in the
    # scorecard for humans.
    stderr = rec.pop("_full_stderr", rec["stderr"])
    stdout = rec.pop("_full_stdout", rec["stdout"])
    combined = (stdout + "\n" + stderr).lower()
    compiled = rec["exit_code"] == 0

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
        emits_lean = any(m in combined for m in LEAN_EMISSION_MARKERS)
        fired = "legacy" in combined or "spec_sugar" in combined or "spec sugar" in combined
        rec["lint_fired"] = fired
        rec["emits_lean"] = emits_lean
        if emits_lean:
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
        "--output",
        default=str(BATTERY_DIR / "results.json"),
        help="Scorecard JSON path",
    )
    args = ap.parse_args()

    stamp = toolchain_stamp()
    if stamp.get("toolchain_matches_head") is False:
        print(
            f"WARNING: toolchain is {stamp.get('toolchain_commits_behind_head')} "
            f"commits behind HEAD — results are about the OLD compiler.",
            file=sys.stderr,
        )

    files = discover(args.filter)
    results = []
    for p in files:
        rec = run_one(p, args.timeout)
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

    doc = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "toolchain": stamp,
        "summary": summary,
        "results": results,
    }
    Path(args.output).write_text(json.dumps(doc, indent=2), encoding="utf-8")

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
    print(f"scorecard: {args.output}")

    # Exit non-zero ONLY on soundness breaks or broken controls; a documented
    # unimplemented lane (lane D) is a measurement, not a runner error.
    return 1 if (summary["false_accepts"] or summary["reject_wrong_reason"]) else 0


if __name__ == "__main__":
    sys.exit(main())
