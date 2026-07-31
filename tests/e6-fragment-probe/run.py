#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0 OR MIT

"""E6/E9 fragment probe — what the two-language surface actually admits.

Each probe is a focused program pairing a Rust function with a Clean island
definition, written so that exactly one thing about it is interesting.
The runner compiles each under `-Ztrust-verify=on` with the E6/E9 debug channels
on, and records:

  * whether each function was ADMITTED into the kernel (E6), and as which shape;
  * whether an `ensures` DISCHARGED by uncited definitional equality or a cited
    theorem (E9).

Why this exists: the E6 fragment is narrower than the prose around it suggests,
and the boundary is not where a reader would guess. Natural unsigned `Select`
and the closed compiler-authenticated S3/S4 wrapping lane now discharge;
exact certified-callee closure is live; a citation to a theorem in a DEFERRED
island (one naming the `trust_import_*` namespace) discharges after the
whole-crate mint; while every constant-shaped probe remains outside the working
lane. A prose description of that boundary goes stale silently; this matrix does
not.

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
import shlex
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path


def _trustc_cmd() -> list[str]:
    """The trustc to measure.

    Defaults to the rustup `trust` toolchain. `TRUST_PROBE_TRUSTC` overrides it
    with an explicit binary, which is how an isolated worktree build gets
    measured without repointing the toolchain a shared tree depends on.
    """
    explicit = os.environ.get("TRUST_PROBE_TRUSTC")
    if explicit:
        return [explicit]
    rustup = Path.home() / ".cargo" / "bin" / "rustup"
    return [str(rustup) if rustup.is_file() else "rustup", "run", "trust", "trustc"]

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
PROBES = HERE / "probes"

# Horizontal whitespace only. `\s*` also consumes newlines, which made an empty
# `probe-note:` absorb the next directive and corrupted the recorded matrix.
DIRECTIVE_RE = re.compile(
    r"^//@[ \t]*(probe-[a-z-]+)[ \t]*:[ \t]*(.*?)[ \t]*$", re.MULTILINE
)
E6_RE = re.compile(
    r"TRUST_E6_DEBUG fn=(?P<fn>\S+) admissible=(?P<adm>true|false).*?"
    r"recognize=(?P<shape>Some\([A-Za-z]+|None)"
)
# Three lanes discharge, and each prints its own marker: the uncited
# definitional-equality lane prints `DEFEQ-DISCHARGED`, the in-walk cited lane
# prints plain `DISCHARGED`, and the item-10 post-walk lane (a citation to a
# theorem in a DEFERRED island) prints `POST-WALK-DISCHARGED`. Matching only some
# of them silently UNDERSTATES the measured surface — which is how `d13`/`d14`
# first read as `island-only` while the compiler was in fact publishing
# `3 proved`. An understating instrument is less dangerous than a flattering one
# and still wrong.
E9_OK_RE = re.compile(r"TRUST_E9_DEBUG (?:DEFEQ-|POST-WALK-)?DISCHARGED fn=(?P<fn>\S+)")
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
            [*_trustc_cmd(), "-vV"],
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
    # A probe with no clause to discharge: what is under test is whether the
    # ISLAND itself typechecks. Compiles clean and the kernel registered the
    # declarations => the property holds.
    if "Clean island kernel-checked" in out and not re.search(r"^error", out, re.MULTILINE):
        if not E9_OK_RE.search(out) and not E9_NO_RE.search(out):
            return "island-only", ""
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
    extra_flags = shlex.split(d.get("probe-flags", ""))
    if extra_flags not in ([], ["-O"]):
        raise ValueError(
            f"{path.name}: unsupported probe-flags {extra_flags!r}; "
            "the closed harness currently permits only `-O`"
        )
    env = dict(os.environ)
    env["TRUST_E6_DEBUG"] = "1"
    env["TRUST_E9_DEBUG"] = "1"
    env["PATH"] = str(Path.home() / ".cargo" / "bin") + os.pathsep + env.get("PATH", "")

    with tempfile.TemporaryDirectory(prefix="e6-probe-") as td:
        cmd = [
            *_trustc_cmd(), str(path),
            "--crate-type=lib", "--edition", "2021", "--crate-name", "probe",
            "-Ztrust-verify=on", *extra_flags, "--out-dir", td,
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
        "flags": extra_flags,
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
