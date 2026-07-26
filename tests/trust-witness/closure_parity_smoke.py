#!/usr/bin/env python3
"""Closures scope widening (precise/parity lane) — sound by construction.

A capture-less closure root (`fn g() { let _c = |x: i32| x + 1; 7 }`) is a clean
MISS on the TRUST replay path (`forest_const_walk_set(.., precise=false)` rejects
the Closure child — see replay_regression.py `closure_root`). Under
`-Ztrust-witness-precise` we ADMIT the Closure child into the walk and encode the
`ty::Closure` node type (encode.rs tag 16), so the root is MINTED under the
edit-loop key and the closure body's types are shadow-measured. The candidate is
NEVER trusted: precise mode returns real typeck and only records PARITY-MATCH /
PARITY-DIVERGE. This pins:
  * SCOPE: a closure-containing root is now minted+measured (was a hard MISS);
  * SOUNDNESS: precise-mode output is byte-identical to a no-flag build (the
    closure result is never installed from the witness) — closures cannot
    miscompile through this lane;
  * FUNCTION: on unchanged code the closure witness round-trips (PARITY-MATCH).

Run after `x.py build --stage 2`:
    TRUST_SEED_STAIRCASE=1 python3 tests/trust-witness/closure_parity_smoke.py
"""
import subprocess, os, sys, glob, hashlib, tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get("TRUST_WITNESS_TRUSTC",
                        os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"))
WORK = tempfile.mkdtemp(prefix="closure_parity_")
SRC = os.path.join(WORK, "s.rs")
open(SRC, "w").write(
    "pub fn g() -> i32 {\n"
    "    let _c = |x: i32| x + 1;\n"
    "    7\n"
    "}\n"
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
    probs.append("no closure witness minted under the precise key (scope widening did not fire)")
if "PARITY-MATCH" not in replay.stderr:
    probs.append("no PARITY-MATCH recorded (closure witness did not round-trip)")
if "PARITY-DIVERGE" in replay.stderr:
    probs.append("unexpected PARITY-DIVERGE on unchanged closure code")
if digests(os.path.join(WORK, "r")) != digests(os.path.join(WORK, "n")):
    probs.append("precise-mode closure output NOT byte-identical to no-flag (the witness was trusted!)")
if replay.returncode != noflag.returncode:
    probs.append(f"exit {replay.returncode} != no-flag {noflag.returncode}")

n_match = replay.stderr.count("PARITY-MATCH")
print(f"  {'PASS' if not probs else 'FAIL'}  closure-parity: matches={n_match} "
      f"byte-identical={digests(os.path.join(WORK,'r'))==digests(os.path.join(WORK,'n'))}"
      + ("" if not probs else "  <- " + "; ".join(probs)))
if probs:
    sys.exit(1)
print("\nclosure scope-widening parity smoke PASS (closure minted+measured under the "
      "edit-loop key, never trusted; output byte-identical)")
