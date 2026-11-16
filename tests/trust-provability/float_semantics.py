#!/usr/bin/env python3
"""Defined-IEEE-semantics rows: reported, never fatal, never silently absent.

Pins the 2026-08-03 fix for two defects found in ordinary float code
(`reports/2026-08-02-float-arithmetic-blocks-and-f32-hole.md`):

1. **`f64` arithmetic did not compile.** `a + b` was refuted — correctly, since
   `f64::MAX + f64::MAX` is `+inf` — and the refutation failed the build. But
   reaching `inf` is DEFINED IEEE-754 behaviour producing a defined value: no
   panic, no UB, vanilla Rust runs it. Failing there is "failing by restricting
   valid Rust", which `DESIGN_PHILOSOPHY.md:186-189` forbids.

2. **`f32` arithmetic emitted no obligation at all.** Every arm of the witness
   builder was hardcoded to width 64, so an f32 operand fell through to `None` —
   the same signal the discharge path uses for "proved safe". The row came back
   `no_obligations` / `proved` having checked nothing.

The two defects pull in opposite directions, which is why both assertions matter
here: fixing (1) alone would have left a silent hole, and fixing (2) alone would
have made f32 uncompilable too.

    python3 tests/trust-provability/float_semantics.py     # CI gate

HAZARD (shared with `policy_directions.py`): exit codes are the measurement
here, so every run is screened for the compiler refusing our FLAGS or ICEing
before any code is read as a verdict.
"""
import json
import os
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get(
    "TRUST_PROVABILITY_TRUSTC",
    os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"),
)

BASE = [
    "-Zthreads=1", "-Ztrust-verify=on", "-Ztrust-verify-output=json",
    "-Coverflow-checks=on", "--edition=2021", "--crate-type=lib", "--emit=metadata",
]

# (label, source, builds_by_default, must_emit_an_obligation)
CASES = [
    ("f64 add", "pub fn f(a: f64, b: f64) -> f64 { a + b }", True, True),
    ("f64 sub", "pub fn f(a: f64, b: f64) -> f64 { a - b }", True, True),
    ("f64 mul", "pub fn f(a: f64, b: f64) -> f64 { a * b }", True, True),
    ("f32 add", "pub fn f(a: f32, b: f32) -> f32 { a + b }", True, True),
    ("f32 sub", "pub fn f(a: f32, b: f32) -> f32 { a - b }", True, True),
    ("f32 mul", "pub fn f(a: f32, b: f32) -> f32 { a * b }", True, True),
    # NEGATIVE CONTROLS. Without these the battery would pass just as well if the
    # fix had simply stopped failing builds altogether, which is the obvious way
    # to get this wrong.
    ("u32 add (integer overflow refutation)",
     "pub fn f(a: u32, b: u32) -> u32 { a + b }", False, True),
    ("unguarded slice index",
     "pub fn f(v: &[u32]) -> u32 { v[0] }", False, True),
]


def run(source, certify=False):
    d = tempfile.mkdtemp(prefix="floatsem_")
    path = os.path.join(d, "t.rs")
    with open(path, "w") as fh:
        fh.write(source + "\n")
    env = dict(os.environ)
    cmd = [TRUSTC, *BASE] + (["-Ztrust-policy=certify"] if certify else []) + \
          ["--out-dir", d, path]
    proc = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=300)
    err = proc.stderr
    for probe in ("unknown unstable option", "Unrecognized option", "unknown debugging option"):
        if probe in err:
            sys.exit(f"HARNESS: {probe!r} — fix the battery, do not read this as a verdict")
    if "unexpectedly panicked" in err:
        sys.exit("HARNESS: ICE — a crash is not a verdict")
    obligations = 0
    for line in err.splitlines():
        i = line.find("TRUST_JSON:")
        if i < 0:
            continue
        try:
            obj = json.loads(line[i + len("TRUST_JSON:"):].strip())
        except json.JSONDecodeError:
            continue
        if obj.get("type") == "function_result":
            obligations += len(obj.get("results") or [])
    return proc.returncode == 0, obligations


def main():
    if not os.path.exists(TRUSTC):
        print(f"SKIP: no stage2 trustc at {TRUSTC}")
        return 0
    print(subprocess.run([TRUSTC, "-V"], capture_output=True, text=True).stdout.strip(), "\n")

    failures = []
    for label, source, want_build, want_obligation in CASES:
        built, obligations = run(source)
        print(f"  {label:40s} builds={str(built):5s} obligations={obligations}")
        if built != want_build:
            failures.append(
                f"{label}: expected build={'ok' if want_build else 'rejected'}, got "
                f"{'ok' if built else 'rejected'}")
        if want_obligation and obligations == 0:
            failures.append(
                f"{label}: ZERO obligations — the row reports as verified having checked "
                f"nothing. A missing witness shape must never mint a `proved` row.")

    # certify is the release gate and must still demand full discharge, so the
    # float rows that build by default must be rejected under it. Without this,
    # "tolerated by default" would be indistinguishable from "not checked".
    for label, source, _, _ in CASES[:6]:
        built, _ = run(source, certify=True)
        print(f"  {label:40s} certify_builds={built}")
        if built:
            failures.append(f"{label}: certify must reject a float row that is not discharged")

    if failures:
        print("\nFLOAT SEMANTICS BATTERY FAILED:")
        for line in failures:
            print(f"  - {line}")
        return 1
    print("\nfloat semantics hold: reported, never fatal by default, never absent, "
          "still gated by certify")
    return 0


if __name__ == "__main__":
    sys.exit(main())
