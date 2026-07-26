#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0 OR MIT

"""E6/E9 fragment probe — what the two-language surface actually admits.

Each probe is a four-to-eight line program pairing a Rust function with a Clean
island definition, written so that exactly one thing about it is interesting.
The runner compiles each under `-Ztrust-verify=on` with the E6/E9 debug channels
on, and records:

  * whether each function was ADMITTED into the kernel (E6), and as which shape;
  * whether the uncited `ensures` DISCHARGED by definitional equality (E9).

Why this exists: the E6 fragment is much narrower than the prose around it
suggests, and the boundary is not where a reader would guess. Two of the five
recognized body shapes are unreachable in practice, every constant-shaped probe
fails, and `Select` discharges only when the island is written in the kernel's
internal encoding rather than the way a person would write it. A prose
description of that boundary goes stale silently; this matrix does not.

Usage:
    python3 tests/e6-fragment-probe/run.py
    python3 tests/e6-fragment-probe/run.py --filter select

Exit code is non-zero when a probe's measured verdict differs from the
`probe-expect` recorded in its header. That is the point: when someone widens
the fragment, the probes that newly discharge FAIL this runner, and the fix is
to update the expectation deliberately — a widening should never land silently.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
PROBES = HERE / "probes"

DIRECTIVE_RE = re.compile(r"^//@\s*(probe-[a-z-]+)\s*:\s*(.*?)\s*$", re.MULTILINE)
E6_RE = re.compile(
    r"TRUST_E6_DEBUG fn=(?P<fn>\S+) admissible=(?P<adm>true|false).*?"
    r"recognize=(?P<shape>Some\([A-Za-z]+|None)"
)
E9_OK_RE = re.compile(r"TRUST_E9_DEBUG DEFEQ-DISCHARGED fn=(?P<fn>\S+)")
# The rejection line always carries fn=, but the verdict payload varies — some
# arms have `detail: "..."`, others do not. Requiring `detail:` silently
# reclassified genuine defeq rejections as "unproved", which is the flattering
# direction, so the detail is captured separately and optionally.
E9_NO_RE = re.compile(r"TRUST_E9_DEBUG DEFEQ-NOT-CERTIFIED fn=(?P<fn>\S+)(?P<rest>[^\n]*)")
E9_DETAIL_RE = re.compile(r"detail: \"(?P<detail>[^\"]*)\"")


def parse_directives(text: str) -> dict:
    out: dict = {}
    for k, v in DIRECTIVE_RE.findall(text):
        if k == "probe-note":
            out.setdefault(k, []).append(v)
        else:
            out[k] = v
    return out


def toolchain_stamp() -> dict:
    try:
        p = subprocess.run(
            ["rustup", "run", "trust", "rustc", "-vV"],
            capture_output=True, text=True, timeout=60, cwd=REPO_ROOT,
        )
        m = re.search(r"commit-hash:\s*([0-9a-f]+)", p.stdout)
        host = re.search(r"host:\s*(\S+)", p.stdout)
        commit = m.group(1) if m else None
    except Exception as exc:  # noqa: BLE001
        return {"error": str(exc), "commit": None, "host": None}
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=REPO_ROOT
    ).stdout.strip()
    return {
        "commit": commit,
        "host": host.group(1) if host else None,
        "repo_head": head,
        "matches_head": bool(commit and head.startswith(commit)),
    }


def classify(stdout: str, stderr: str) -> tuple[str, str]:
    """Verdict for the probe, plus a one-line reason."""
    out = stdout + "\n" + stderr
    # An ICE is never a verdict about the fragment. Before this check a crash
    # fell through to "unproved", which reads as an ordinary coverage gap and
    # hides a compiler bug in a column of expected-looking results.
    if "unexpectedly panicked" in out or "internal compiler error" in out:
        loc = re.search(r"panicked at ([^\n]+)", out)
        return "ice", loc.group(1) if loc else "compiler panic"
    if E9_OK_RE.search(out):
        return "discharged", ""
    m = E9_NO_RE.search(out)
    if m:
        rest = m.group("rest")
        detail = E9_DETAIL_RE.search(rest)
        if detail:
            # The kernel actually checked a constructed Eq.refl and refused it.
            return "defeq-rejected", detail.group("detail")
        verdict = re.search(r"verdict=(\S+)", rest)
        raw = verdict.group(1) if verdict else rest.strip()[:120]
        if raw.startswith("ClauseOutsideFragment"):
            # Distinct and more informative than "not defeq": the clause never
            # reached the kernel, because the clause itself is outside the
            # elaboration fragment (an unsupported domain, a generic, a
            # reference, an unadmitted callee). Collapsing this into
            # `defeq-rejected` would hide WHERE the boundary actually is.
            return "clause-outside-fragment", raw
        return "defeq-rejected", raw
    if re.search(r"^error\[E\d+\]", out, re.MULTILINE):
        first = re.search(r"^error\[E\d+\]: (.*)$", out, re.MULTILINE)
        return "compile-error", first.group(1) if first else ""
    if re.search(r"^error:", out, re.MULTILINE):
        return "unproved", "no defeq attempt reached; obligations left unproved"
    return "other", ""


def run_probe(path: Path, timeout: int) -> dict:
    text = path.read_text(encoding="utf-8")
    d = parse_directives(text)
    env = dict(os.environ)
    env["TRUST_E6_DEBUG"] = "1"
    env["TRUST_E9_DEBUG"] = "1"
    env["PATH"] = str(Path.home() / ".cargo" / "bin") + os.pathsep + env.get("PATH", "")

    with tempfile.TemporaryDirectory(prefix="e6-probe-") as td:
        cmd = [
            "rustup", "run", "trust", "trustc", str(path),
            "--crate-type=lib", "--edition", "2021", "--crate-name", "probe",
            "-Ztrust-verify=on", "--out-dir", td,
        ]
        try:
            p = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout, cwd=REPO_ROOT, env=env
            )
            stdout, stderr, code = p.stdout, p.stderr, p.returncode
        except subprocess.TimeoutExpired:
            return {
                "probe": path.name, "verdict": "timeout", "expect": d.get("probe-expect"),
                "ok": False, "shape": None, "admissible": {}, "reason": f"timeout {timeout}s",
                "note": d.get("probe-note", []),
            }

    verdict, reason = classify(stdout, stderr)
    admissible = {}
    shapes = {}
    for m in E6_RE.finditer(stdout + "\n" + stderr):
        fn = m.group("fn")
        admissible[fn] = m.group("adm") == "true"
        shapes[fn] = m.group("shape").replace("Some(", "")

    expect = d.get("probe-expect", "discharged")
    return {
        "probe": path.name,
        "expect": expect,
        "verdict": verdict,
        "ok": verdict == expect,
        "declared_shape": d.get("probe-shape"),
        "observed_shapes": shapes,
        "admissible": admissible,
        "reason": reason,
        "note": d.get("probe-note", []),
        "exit_code": code,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--filter", default=None)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--output", default=str(HERE / "matrix.json"))
    args = ap.parse_args()

    stamp = toolchain_stamp()
    if stamp.get("matches_head") is False:
        print(
            f"NOTE: toolchain {stamp.get('commit')} != HEAD {str(stamp.get('repo_head'))[:10]}; "
            "verdicts describe the BUILT compiler, not the source tree.",
            file=sys.stderr,
        )

    probes = sorted(PROBES.glob("*.rs"))
    if args.filter:
        probes = [p for p in probes if args.filter in p.name]

    rows = [run_probe(p, args.timeout) for p in probes]

    print(f"{'probe':<34} {'expect':<15} {'verdict':<15} shape")
    print("-" * 86)
    for r in rows:
        flag = " " if r["ok"] else "!"
        shape = ",".join(sorted(set(r["observed_shapes"].values()))) or "-"
        print(f"{flag}{r['probe']:<33} {str(r['expect']):<15} {r['verdict']:<15} {shape}")

    deviations = [r for r in rows if not r["ok"]]
    discharged = sum(1 for r in rows if r["verdict"] == "discharged")

    print()
    print(f"{discharged}/{len(rows)} probes discharge; {len(deviations)} deviate from expectation")
    if deviations:
        print()
        for r in deviations:
            print(f"  ! {r['probe']}: expected {r['expect']}, got {r['verdict']}")
            if r["reason"]:
                print(f"      {r['reason'][:120]}")
        print()
        print("  A deviation is not automatically a bug: if the fragment was widened")
        print("  deliberately, update the probe's `probe-expect` in the same commit.")

    doc = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "toolchain": stamp,
        "summary": {
            "total": len(rows),
            "discharged": discharged,
            "deviations": len(deviations),
        },
        "probes": rows,
    }
    Path(args.output).write_text(json.dumps(doc, indent=2), encoding="utf-8")
    print(f"matrix: {args.output}")
    return 1 if deviations else 0


if __name__ == "__main__":
    sys.exit(main())
