#!/usr/bin/env python3
"""A1-A3 precise edit-loop key — shadow-mint parity measurement (sound by construction).

`-Ztrust-witness-precise` switches mint+replay to the PRECISE per-referenced-def key
(hits without the whole-crate SVH — the edit-loop key), but the replayed candidate is
NEVER trusted: the provider byte-diffs it against real typeck, records PARITY-MATCH /
PARITY-DIVERGE, and always returns real typeck's result. So it measures the precise
key's divergence rate (the negative-information hole) with ZERO behavioral risk. This
pins:
  * SOUNDNESS: precise-mode output is byte-identical to a no-flag build (real typeck
    is always what's returned) — the precise key cannot miscompile;
  * FUNCTION: on unchanged code the precise key retrieves a consistent witness
    (PARITY-MATCH), demonstrating the edit-loop key + the measurement fire.

Run after `x.py build --stage 2`:
    TRUST_SEED_STAIRCASE=1 python3 tests/trust-witness/precise_parity_smoke.py
"""
import subprocess, os, sys, re, glob, hashlib, tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get("TRUST_WITNESS_TRUSTC",
                        os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"))
WORK = tempfile.mkdtemp(prefix="precise_")
SRC = os.path.join(WORK, "s.rs")
open(SRC, "w").write(
    "pub struct P { x: i32 }\n"
    "impl P { pub fn get(&self) -> i32 { self.x } }\n"
    "pub fn u(p: &P) -> i32 { let a = p.get(); let b = p.get(); a + b }\n"
)

BASE = ["-Zthreads=1", "-Ztrust-verify=off", "-Ztrust-witness=off",
        "--edition", "2021", "--crate-type=lib", "--emit=metadata,obj"]


def run(extra, outdir, stats=False):
    os.makedirs(outdir, exist_ok=True)
    env = dict(os.environ); env["TRUST_SEED_STAIRCASE"] = "1"
    if stats:
        env["TRUST_WITNESS_STATS"] = "1"
    return subprocess.run([TRUSTC] + BASE + extra + ["--out-dir", outdir, SRC],
                          capture_output=True, text=True, env=env)


def digests(d):
    return {e: sorted(hashlib.sha256(open(f, "rb").read()).hexdigest()
                      for f in glob.glob(os.path.join(d, f"*.{e}"))) for e in ("rmeta", "o")}


store = os.path.join(WORK, "store")
run(["-Ztrust-witness-precise", f"-Ztrust-witness=mint:{store}"], os.path.join(WORK, "m"))
replay = run(["-Ztrust-witness-precise", f"-Ztrust-witness=replay:{store}"], os.path.join(WORK, "r"), stats=True)
noflag = run([], os.path.join(WORK, "n"))

probs = []
if not glob.glob(os.path.join(store, "*.twit")):
    probs.append("no precise-keyed witness minted")
if "PARITY-MATCH" not in replay.stderr:
    probs.append("no PARITY-MATCH recorded (precise key did not retrieve a consistent witness)")
if "PARITY-DIVERGE" in replay.stderr:
    probs.append("unexpected PARITY-DIVERGE on unchanged code")
if digests(os.path.join(WORK, "r")) != digests(os.path.join(WORK, "n")):
    probs.append("precise-mode output NOT byte-identical to no-flag (the key was trusted!)")
if replay.returncode != noflag.returncode:
    probs.append(f"exit {replay.returncode} != no-flag {noflag.returncode}")

n_match = replay.stderr.count("PARITY-MATCH")
print(f"  {'PASS' if not probs else 'FAIL'}  precise-parity: matches={n_match} "
      f"byte-identical={digests(os.path.join(WORK,'r'))==digests(os.path.join(WORK,'n'))}"
      + ("" if not probs else "  <- " + "; ".join(probs)))
if probs:
    sys.exit(1)
print("\nprecise-key parity smoke PASS (edit-loop key measured, never trusted; output byte-identical)")
