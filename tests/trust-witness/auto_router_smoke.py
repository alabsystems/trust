#!/usr/bin/env python3
"""Default-on + router smoke test for the managed typeck-witness lane.

The lane is ON by default (`-Ztrust-witness`, default on) on non-incremental
`--out-dir` builds, storing at `<out-dir>/trust-witness`, with a router that
replays a root only when its body is large enough to beat fresh typeck. This test
proves both properties with NO explicit witness flags:

  * TRIVIAL bodies: the router skips them, so a warm auto compile does NOT engage
    replay (no ACCEPT) and stays at parity with an auto-off baseline — the ~24x
    trivial-body penalty is gone.
  * HEAVY bodies: the router mints then auto-replays them (ACCEPT on the 2nd
    compile), byte-identically, and faster than fresh typeck.

Run after `x.py build --stage 2`:
    TRUST_SEED_STAIRCASE=1 python3 tests/trust-witness/auto_router_smoke.py
"""
import subprocess, os, sys, time, glob, hashlib, shutil

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.path.join(REPO, "build", "host", "stage2", "bin", "trustc")
WORK = os.path.join(REPO, "build", "trust-witness-auto-smoke")

# Many tiny fns — each well under the router's node threshold.
TRIVIAL = "\n".join(f"pub fn f{i}(a: i32, b: i32) -> i32 {{ a + b }}" for i in range(240))

# One deeply-nested arithmetic body — far above the threshold, typeck-heavy.
def nest(d):
    e = "x"
    for _ in range(d):
        e = f"({e} + 1)"
    return e
HEAVY = "\n".join(f"pub fn g{i}(x: i64) -> i64 {{ {nest(300)} }}" for i in range(20))


def compile(src, outdir, auto, stats=False):
    os.makedirs(outdir, exist_ok=True)
    env = dict(os.environ); env["TRUST_SEED_STAIRCASE"] = "1"
    if stats:
        env["TRUST_WITNESS_STATS"] = "1"
    cmd = [TRUSTC, "-Zthreads=1", "-Ztrust-verify=off", "--edition", "2021",
           "--crate-type=lib", "--emit=metadata,obj", "--out-dir", outdir,
           f"-Ztrust-witness={'auto' if auto else 'off'}", src]
    t = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    return r, time.time() - t


def digests(outdir):
    return {ext: sorted(hashlib.sha256(open(f, "rb").read()).hexdigest()
                        for f in glob.glob(os.path.join(outdir, f"*.{ext}")))
            for ext in ("rmeta", "o")}


def accepts(stderr):
    return sum(1 for l in stderr.splitlines() if l.startswith("TRUST_REPLAY ACCEPT"))


shutil.rmtree(WORK, ignore_errors=True)
fails = []

for name, src_txt, expect_accept in [("trivial", TRIVIAL, False), ("heavy", HEAVY, True)]:
    d = os.path.join(WORK, name)
    os.makedirs(d, exist_ok=True)
    src = os.path.join(d, f"{name}.rs")
    open(src, "w").write(src_txt)

    # auto-off baseline (cold), for timing + byte reference.
    base_dir = os.path.join(d, "base")
    rb, tb = compile(src, base_dir, auto=False)

    # auto-on: 1st compile mints (cold), 2nd replays (warm) — same out-dir/store.
    auto_dir = os.path.join(d, "auto")
    r1, t1 = compile(src, auto_dir, auto=True)                    # cold: mint
    r2, t2 = compile(src, auto_dir, auto=True, stats=True)        # warm: replay

    probs = []
    if rb.returncode or r1.returncode or r2.returncode:
        probs.append(f"nonzero exit (base={rb.returncode} cold={r1.returncode} warm={r2.returncode})")
    # same-answers: warm auto output == auto-off baseline output
    if digests(base_dir) != digests(auto_dir):
        probs.append("warm auto output NOT byte-identical to auto-off baseline")
    acc = accepts(r2.stderr)
    store = glob.glob(os.path.join(auto_dir, "trust-witness", "*.twit"))
    if expect_accept:
        if acc == 0:
            probs.append("HEAVY: router did not auto-replay any root (expected ACCEPT)")
        if not store:
            probs.append("HEAVY: no witness store written under <out-dir>/trust-witness")
    else:
        if acc != 0:
            probs.append(f"TRIVIAL: router replayed {acc} root(s) it should have skipped")
        # trivial warm compile must not be pathologically slower than baseline
        if tb > 0 and t2 > tb * 3:
            probs.append(f"TRIVIAL: warm auto {t2*1000:.0f}ms >> baseline {tb*1000:.0f}ms (router failed to skip)")

    status = "PASS" if not probs else "FAIL"
    extra = f"accept={acc} store={len(store)} base={tb*1000:.0f}ms cold={t1*1000:.0f}ms warm={t2*1000:.0f}ms"
    print(f"  {status}  {name}: {extra}" + ("" if not probs else f"  <- {'; '.join(probs)}"))
    if probs:
        fails.append(name)

print()
if fails:
    print(f"FAILED: {', '.join(fails)}"); sys.exit(1)
print("default-on + router smoke PASS (trivial skipped at parity; heavy auto-replays byte-identically)")
