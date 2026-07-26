#!/usr/bin/env python3
"""A/B microbenchmark for the trust_verify supportability classifier.

Compiles a synthetic crate twice (or compares two trustc binaries) and
reports wall time, peak RSS, stderr byte volume, and per-function
`note:` counts. The synthetic crate mixes the three classifier verdicts
so a single run answers:

- did the classifier skip Unsupported functions before lowering?
- did SpecBearing / Inferrable functions still verify?
- how much wall time + log volume did we save?

Two invocation modes:

  bench_verifier.py compare BASELINE_TRUSTC PATCHED_TRUSTC
      Times the same source against two trustc binaries (e.g.
      build/<host>/stage1/bin/trustc before vs after the patch).

  bench_verifier.py single TRUSTC
      Times the source against one trustc binary. Useful as a sanity
      check ("does the classifier emit the new skip reason on this
      input?") before doing the full A/B.

The synthetic source is generated under a temp dir and cleaned up.
Pass `--keep` to retain it for inspection.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""

from __future__ import annotations

import argparse
import json
import os
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path


SYNTHETIC_CRATE = r'''//! Synthetic benchmark crate for trust_verify supportability classifier.
//! Mix of SpecBearing / Inferrable / Unsupported functions, repeated
//! NFOLD times to amplify the per-function cost difference.

#![allow(dead_code)]
#![allow(unused_variables)]

use core::num::NonZeroU32;

// Inferrable: plain arithmetic, no spec, MIR shape fully supported.
{INFERRABLE_FNS}

// Unsupported: pattern type in signature (TyKind::Pat). Classifier
// should fast-reject on the parameter type without invoking lowering.
{UNSUPPORTED_FNS}

// SpecBearing: would carry #[trust::ensures] in real code. We use a
// no-op marker so the synthetic crate compiles without the attribute
// scaffolding being available. The classifier sees no contract, so
// these compile as Inferrable in this synthetic context — that's fine
// for the benchmark, which is measuring the skip-vs-not-skip delta.
{SPEC_FNS}

pub fn entrypoint() -> u64 { 0 }
'''


def gen_synthetic(out: Path, nfold: int) -> Path:
    """Generate the benchmark source crate. Returns path to lib.rs."""
    inferrable = "\n".join(
        f"#[inline(never)]\npub fn inferrable_{i}(a: u32, b: u32) -> u32 {{ a.wrapping_add(b) }}"
        for i in range(nfold)
    )
    unsupported = "\n".join(
        f"#[inline(never)]\npub fn unsupported_{i}(n: NonZeroU32) -> u32 {{ n.get() }}"
        for i in range(nfold)
    )
    spec = "\n".join(
        f"#[inline(never)]\npub fn spec_{i}(x: u32) -> u32 {{ x.saturating_add(1) }}"
        for i in range(nfold)
    )
    src = SYNTHETIC_CRATE.format(
        INFERRABLE_FNS=inferrable,
        UNSUPPORTED_FNS=unsupported,
        SPEC_FNS=spec,
    )
    crate_dir = out / "bench-crate"
    crate_dir.mkdir(parents=True, exist_ok=True)
    src_dir = crate_dir / "src"
    src_dir.mkdir(exist_ok=True)
    lib_rs = src_dir / "lib.rs"
    lib_rs.write_text(src, encoding="utf-8")
    (crate_dir / "Cargo.toml").write_text(
        '[package]\nname = "bench_crate"\nversion = "0.0.0"\nedition = "2021"\n'
        '[lib]\npath = "src/lib.rs"\n',
        encoding="utf-8",
    )
    return lib_rs


@dataclass
class RunResult:
    wall_seconds: float
    peak_rss_kb: int
    stderr_bytes: int
    note_lines: int
    unsupported_notes: int
    classifier_skips: int
    exit_code: int
    stderr_excerpt: list[str] = field(default_factory=list)

    def as_dict(self) -> dict:
        return {
            "wall_seconds": round(self.wall_seconds, 3),
            "peak_rss_kb": self.peak_rss_kb,
            "stderr_bytes": self.stderr_bytes,
            "note_lines": self.note_lines,
            "unsupported_notes": self.unsupported_notes,
            "classifier_skips": self.classifier_skips,
            "exit_code": self.exit_code,
        }


NOTE_RE = re.compile(rb"^note:", re.MULTILINE)
UNSUPPORTED_RE = re.compile(rb"verifier evidence status: Unsupported", re.MULTILINE)
CLASSIFIER_SKIP_RE = re.compile(rb"Trust: classifier rejects", re.MULTILINE)


def run_one(trustc: Path, lib_rs: Path, label: str) -> RunResult:
    out_dir = lib_rs.parent.parent / f"target-{label}"
    out_dir.mkdir(exist_ok=True)
    cmd = [
        str(trustc),
        "--crate-name", "bench_crate",
        "--edition=2021",
        "--crate-type", "lib",
        "-C", "opt-level=0",
        # The verifier is an optimized-MIR pass; metadata-only emission can
        # avoid querying optimized MIR and turn this benchmark into a no-op.
        "--emit=link",
        "-o", str(out_dir / "out.rlib"),
        str(lib_rs),
    ]
    env = os.environ.copy()
    # CLASSIFIER_SKIP_RE below parses this trace event. Without the matching
    # filter every run reports zero skips even when the classifier is active.
    env["RUSTC_LOG"] = "rustc_mir_transform::trust_verify=trace"
    env["RUST_BACKTRACE"] = "0"
    pre_rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    t0 = time.monotonic()
    completed = subprocess.run(cmd, capture_output=True, env=env)
    elapsed = time.monotonic() - t0
    post_rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    stderr = completed.stderr
    excerpt_lines = stderr.decode("utf-8", "replace").splitlines()[:20]
    return RunResult(
        wall_seconds=elapsed,
        peak_rss_kb=max(0, post_rss - pre_rss),
        stderr_bytes=len(stderr),
        note_lines=len(NOTE_RE.findall(stderr)),
        unsupported_notes=len(UNSUPPORTED_RE.findall(stderr)),
        classifier_skips=len(CLASSIFIER_SKIP_RE.findall(stderr)),
        exit_code=completed.returncode,
        stderr_excerpt=excerpt_lines,
    )


def render_table(label_a: str, a: RunResult, label_b: str, b: RunResult) -> str:
    def fmt(v_a, v_b):
        if isinstance(v_a, float):
            sa, sb = f"{v_a:.3f}", f"{v_b:.3f}"
        else:
            sa, sb = f"{v_a}", f"{v_b}"
        try:
            if v_a > 0:
                delta = f"{(v_b - v_a) / v_a * 100:+.1f}%"
            else:
                delta = "—"
        except (TypeError, ZeroDivisionError):
            delta = "—"
        return sa, sb, delta

    rows = [
        ("metric", label_a, label_b, "Δ"),
        ("wall_seconds", *fmt(a.wall_seconds, b.wall_seconds)),
        ("peak_rss_kb", *fmt(a.peak_rss_kb, b.peak_rss_kb)),
        ("stderr_bytes", *fmt(a.stderr_bytes, b.stderr_bytes)),
        ("note_lines", *fmt(a.note_lines, b.note_lines)),
        ("unsupported_notes", *fmt(a.unsupported_notes, b.unsupported_notes)),
        ("classifier_skips", *fmt(a.classifier_skips, b.classifier_skips)),
        ("exit_code", *fmt(a.exit_code, b.exit_code)),
    ]
    widths = [max(len(str(r[i])) for r in rows) for i in range(4)]
    lines = []
    for i, r in enumerate(rows):
        line = "  ".join(str(cell).ljust(w) for cell, w in zip(r, widths))
        lines.append(line)
        if i == 0:
            lines.append("-" * len(line))
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--nfold", type=int, default=200,
                   help="how many copies of each Inferrable/Unsupported/SpecBearing fn (default 200)")
    p.add_argument("--keep", action="store_true", help="don't delete the synthetic crate dir")
    sub = p.add_subparsers(dest="mode", required=True)
    sub_cmp = sub.add_parser("compare", help="A/B compare two trustc binaries")
    sub_cmp.add_argument("baseline_trustc", type=Path, help="trustc without the patch")
    sub_cmp.add_argument("patched_trustc", type=Path, help="trustc with the patch")
    sub_one = sub.add_parser("single", help="time one trustc binary")
    sub_one.add_argument("trustc", type=Path)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    work = Path(tempfile.mkdtemp(prefix="trust-bench-"))
    try:
        lib_rs = gen_synthetic(work, args.nfold)
        print(f"synthetic crate: {lib_rs} ({args.nfold} fns per category)")
        if args.mode == "single":
            r = run_one(args.trustc, lib_rs, "run")
            print(json.dumps(r.as_dict(), indent=2))
            if r.exit_code != 0:
                print("\nstderr excerpt:")
                for line in r.stderr_excerpt:
                    print(f"  {line}")
            return r.exit_code
        else:
            print(f"\nbaseline: {args.baseline_trustc}")
            a = run_one(args.baseline_trustc, lib_rs, "baseline")
            print(f"patched:  {args.patched_trustc}")
            b = run_one(args.patched_trustc, lib_rs, "patched")
            print()
            print(render_table("baseline", a, "patched", b))
            if a.exit_code != 0 or b.exit_code != 0:
                print("\nNON-ZERO EXIT — stderr excerpts:")
                for label, r in [("baseline", a), ("patched", b)]:
                    if r.exit_code != 0:
                        print(f"--- {label} ---")
                        for line in r.stderr_excerpt:
                            print(f"  {line}")
            return 0
    finally:
        if not args.keep:
            shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
