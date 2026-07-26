#!/usr/bin/env python3
"""Generics scope widening (precise/parity lane) — sound by construction.

A polymorphic root (`fn f<T>(x: T) -> T`, `fn pair<A,B>(a:A,b:B)->(A,B)`) mints and
parity-measures under `-Ztrust-witness-precise` with NO closure-style relaxation:
`encode_ty` already encodes `ty::Param` (tag 15) and a generic fn's liberated sig is
plain safe/Rust-ABI/non-variadic, so the polymorphic root passes mintable's
reconstruction-faithfulness gates directly. This is the generics half of scope
widening, delivered by the A1–A3 precise-lane machinery; this smoke pins it as a
durable regression. As with every precise-lane root, the candidate is NEVER trusted
— the provider byte-compares against real typeck and always returns real typeck — so
precise-mode output is byte-identical to a no-flag build.

Run after `x.py build --stage 2`:
    TRUST_SEED_STAIRCASE=1 python3 tests/trust-witness/generics_parity_smoke.py
"""
import subprocess, os, sys, glob, hashlib, tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get("TRUST_WITNESS_TRUSTC",
                        os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"))

BASE = ["-Zthreads=1", "-Ztrust-verify=off", "-Ztrust-witness=off",
        "--edition", "2021", "--crate-type=lib", "--emit=metadata,obj"]

CASES = {
    "identity": "pub fn f<T>(x: T) -> T { x }",
    "let_bound": "pub fn id<T>(x: T) -> T { let y = x; y }",
    "pair": "pub fn pair<A, B>(a: A, b: B) -> (A, B) { (a, b) }",
}


def run(src, extra, outdir, stats=False):
    os.makedirs(outdir, exist_ok=True)
    env = dict(os.environ); env["TRUST_SEED_STAIRCASE"] = "1"
    if stats:
        env["TRUST_WITNESS_STATS"] = "1"
    return subprocess.run([TRUSTC] + BASE + extra + ["--out-dir", outdir, src],
                          capture_output=True, text=True, env=env)


def digests(d):
    return {e: sorted(hashlib.sha256(open(f, "rb").read()).hexdigest()
                      for f in glob.glob(os.path.join(d, f"*.{e}"))) for e in ("rmeta", "o")}


any_fail = False
for name, code in CASES.items():
    WORK = tempfile.mkdtemp(prefix=f"gen_{name}_")
    SRC = os.path.join(WORK, "s.rs")
    open(SRC, "w").write(code + "\n")
    store = os.path.join(WORK, "store")
    run(SRC, ["-Ztrust-witness-precise", f"-Ztrust-witness=mint:{store}"], os.path.join(WORK, "m"))
    replay = run(SRC, ["-Ztrust-witness-precise", f"-Ztrust-witness=replay:{store}"],
                 os.path.join(WORK, "r"), stats=True)
    noflag = run(SRC, [], os.path.join(WORK, "n"))

    probs = []
    if not glob.glob(os.path.join(store, "*.twit")):
        probs.append("no generic witness minted under the precise key")
    if "PARITY-MATCH" not in replay.stderr:
        probs.append("no PARITY-MATCH (generic witness did not round-trip)")
    if "PARITY-DIVERGE" in replay.stderr:
        probs.append("unexpected PARITY-DIVERGE on unchanged generic code")
    if digests(os.path.join(WORK, "r")) != digests(os.path.join(WORK, "n")):
        probs.append("precise-mode output NOT byte-identical to no-flag (witness trusted!)")

    n_match = replay.stderr.count("PARITY-MATCH")
    print(f"  {'PASS' if not probs else 'FAIL'}  generics:{name} matches={n_match}"
          + ("" if not probs else "  <- " + "; ".join(probs)))
    any_fail = any_fail or bool(probs)

if any_fail:
    sys.exit(1)
print("\ngenerics scope-widening parity smoke PASS (polymorphic roots minted+measured "
      "under the edit-loop key, never trusted; output byte-identical)")
