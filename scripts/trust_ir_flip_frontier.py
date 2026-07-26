#!/usr/bin/env python3
"""trust_ir_flip_frontier.py — tally the derived-MIR (FLIP) differential verdict + reason
histogram across a tests/ui sample, to RANK the next flip lever by corpus mass.

Unlike the producer scorecard (interpreter differential + shape tags), this parses the
`trust-ir-lower: derived-MIR differential, ..., verdict=X, detail="Y"` line emitted at
compiler/rustc_mir_build/src/builder/mod.rs under `-Z trust-ir-lower`. DerivedAgreed = a
body that FLIPS; every other verdict carries a `detail` reason — the histogram of those
reasons is the flip frontier.

Each compile is OOM-guarded (guarded_compile: setsid + RSS watchdog + group-kill on
timeout) — safe to fan out. Usage:
  python3 scripts/trust_ir_flip_frontier.py --sample-size 800 --seed 20260701 --jobs 8
"""
import argparse
import collections
import concurrent.futures
import os
import re
import sys
import tempfile

# Reuse the scorecard's seeded sampling + the OOM-guarded compile.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trust_ir_producer_scorecard import collect_ui_sample, guarded_compile

TRUSTC = os.path.abspath("build/host/stage2/bin/trustc")
LOG_TARGET = "rustc_mir_build::builder=debug"
# verdict + detail off the derived-MIR differential line.
DERIVED_RE = re.compile(
    r"trust-ir-lower: derived-MIR differential, "
    r"def=DefId\([^~]*~\s*(?P<path>.+?)\), verdict=(?P<verdict>\w+), "
    r'detail="(?P<detail>.*?)",'
)
COMPILE_FLAGS = [
    "-Z", "trust-ir-lower", "-Z", "trust-verify=off",
    "--edition", "2021", "--crate-type", "lib",
    "-C", "link-dead-code=yes", "-C", "codegen-units=1",
    "-C", "opt-level=0", "-C", "debuginfo=0",
    "--cap-lints", "allow", "--emit=obj",
]

# Collapse a `detail` string to a stable BUCKET key (strip body-specific type spellings so
# the histogram groups by WALL, not by incidental type). e.g.
#   shim: Call(callee return outside the fragment: !)          -> shim: Call(callee return outside the fragment)
#   shim: aggregate return type is Drop-bearing / non-Copy ... -> shim: aggregate return type ...
#   producer: 2 unsupported THIR shape(s)                      -> producer: N unsupported THIR shape(s)
_NUM = re.compile(r"\b\d+\b")
_PAREN_TY = re.compile(r"(\([^)]*: )[^)]*\)")           # (label: <ty>) -> (label)
_ANGLE = re.compile(r"[<{][^<>{}]*[>}]")                # strip <..>/{..} type payloads
def bucket(detail: str) -> str:
    d = detail
    d = _PAREN_TY.sub(r"\1…)", d)
    d = _ANGLE.sub("…", d)
    d = _NUM.sub("N", d)
    # trim trailing per-body specifics after a colon-space in some shim messages
    return d.strip()


def run_one(src, timeout):
    src = os.path.abspath(src)
    env = dict(os.environ)
    env["RUSTC_LOG"] = LOG_TARGET
    with tempfile.TemporaryDirectory(prefix="ff_") as td:
        out = os.path.join(td, "out.o")
        argv = [TRUSTC, *COMPILE_FLAGS, "-o", out, src]
        code, stderr = guarded_compile(argv, td, env, timeout)
    text = stderr.decode("utf-8", "replace") if isinstance(stderr, (bytes, bytearray)) else (stderr or "")
    rows = []
    for m in DERIVED_RE.finditer(text):
        rows.append((m.group("verdict"), m.group("detail"), m.group("path")))
    return {"src": src, "code": code, "rows": rows, "n": len(rows)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sample-size", type=int, default=800)
    ap.add_argument("--seed", type=int, default=20260701)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--top", type=int, default=40)
    ap.add_argument("--dump-bucket", type=str, default=None,
                    help="print (file, def-path) for every non-flip wall whose bucket contains this substring")
    args = ap.parse_args()

    repo = os.getcwd()
    sample, meta = collect_ui_sample(repo, args.seed, args.sample_size)
    print(f"[frontier] sampled {len(sample)} files (seed={args.seed}), jobs={args.jobs}, "
          f"mem-cap={os.environ.get('TRUST_COMPILE_MEM_CAP_GB','20')}GB", flush=True)

    verdicts = collections.Counter()
    reason_hist = collections.Counter()        # bucket -> body count (non-Agreed only)
    reason_files = collections.defaultdict(set)  # bucket -> set of files (for sole-blocker feel)
    dump_hits = []                               # (file, def-path) for --dump-bucket
    n_bodies = 0
    n_done = 0
    oom = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(run_one, s, args.timeout): s for s in sample}
        for fut in concurrent.futures.as_completed(futs):
            r = fut.result()
            n_done += 1
            if r["code"] is None:
                oom += 1
            for verdict, detail, path in r["rows"]:
                n_bodies += 1
                verdicts[verdict] += 1
                if verdict != "DerivedAgreed":
                    b = bucket(detail)
                    reason_hist[b] += 1
                    reason_files[b].add(r["src"])
                    if args.dump_bucket and args.dump_bucket in b:
                        dump_hits.append((os.path.relpath(r["src"], repo), path))
            if n_done % 100 == 0:
                print(f"  ..{n_done}/{len(sample)} files, {n_bodies} bodies, "
                      f"agreed={verdicts['DerivedAgreed']}", flush=True)

    total = sum(verdicts.values())
    agreed = verdicts.get("DerivedAgreed", 0)
    print("\n================ FLIP FRONTIER ================")
    print(f"files: {len(sample)}  (killed/oom/timeout: {oom})")
    print(f"bodies with a verdict: {total}")
    print(f"verdicts: {dict(verdicts)}")
    if total:
        print(f"FLIP RATE (DerivedAgreed / bodies): {agreed}/{total} = {100*agreed/total:.2f}%")
    print(f"\n---- top {args.top} NON-FLIP walls (by body count) ----")
    for b, c in reason_hist.most_common(args.top):
        print(f"  {c:5d}  [{len(reason_files[b]):4d}f]  {b}")
    if args.dump_bucket:
        print(f"\n---- bodies hitting a wall containing '{args.dump_bucket}' ({len(dump_hits)}) ----")
        for f, p in sorted(dump_hits):
            print(f"  {f}  ::  {p}")


if __name__ == "__main__":
    main()
