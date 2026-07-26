#!/usr/bin/env python3
"""Trust certified-scoreboard: the monotone proof that the clean CIC kernel takes
the `ay` SMT solver OUT of the trusted base on REAL code, and that the count only grows.

For each std-only aterm leaf crate it runs the stage2 `trustc` with strict
verification (now the default lane; per-fn budget raised, since the stock budget
times out and downgrades Proved->Unknown) and parses the Level-0 verification
report into:

  obligations | proved | kernel_certified | smt_backed | failed | unknown | runtime_checked

`kernel_certified` (sum of the "of which N kernel-certified by the clean CIC kernel"
notes) is the HEADLINE: it is the number of real obligations whose proof is
re-checked by the ~zero-trust kernel, so ay is not trusted for them. The scoreboard
is meant to be CI-ratcheted: total kernel_certified must be NON-DECREASING.

Usage:
  trust_certified_scoreboard.py [--trustc PATH] [--aterm DIR] [--baseline FILE] [--out FILE]
Exit 1 if --baseline is given and total kernel_certified regressed below it.
"""
import argparse, json, os, re, subprocess, sys, glob

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Real aterm leaf crates whose source is std-only (compile standalone with trustc).
DEFAULT_CRATES = [
    "aterm-bidi", "aterm-bits", "aterm-codec", "aterm-cap",
    "aterm-rle", "aterm-log", "aterm-buffer", "aterm-hash", "aterm-sixel",
]

RE_REPORT = re.compile(
    r"(\d+) proved, (\d+) failed, (\d+) unknown, (\d+) timed out, (\d+) runtime-checked out of (\d+) obligation"
)
RE_CERT = re.compile(r"of which (\d+) kernel-certified")
RE_SMT = re.compile(r"smt-backed=(\d+)|of which (\d+) smt-backed")


def run_crate(trustc, lib_rs):
    env = dict(os.environ)
    env.update(RUST_LOG="off")
    try:
        p = subprocess.run(
            [trustc, "--crate-type=lib", "--edition=2021",
             "-Z", "trust-verify-function-budget-ms=600000",
             "-Z", "trust-verify-worker-threads=1",
             "-A", "warnings", lib_rs, "-o", "/tmp/_sb_out"],
            env=env, capture_output=True, text=True, timeout=1800,
        )
    except subprocess.TimeoutExpired:
        return None
    out = p.stdout + p.stderr
    agg = dict(obligations=0, proved=0, failed=0, unknown=0, timed_out=0,
               runtime_checked=0, kernel_certified=0, smt_backed=0)
    for m in RE_REPORT.finditer(out):
        proved, failed, unknown, timed, rtc, total = map(int, m.groups())
        agg["proved"] += proved; agg["failed"] += failed; agg["unknown"] += unknown
        agg["timed_out"] += timed; agg["runtime_checked"] += rtc; agg["obligations"] += total
    for m in RE_CERT.finditer(out):
        agg["kernel_certified"] += int(m.group(1))
    for m in RE_SMT.finditer(out):
        agg["smt_backed"] += int(next(g for g in m.groups() if g))
    return agg


def main():
    ap = argparse.ArgumentParser()
    # Defaults are derived from this script's own location, so the scoreboard
    # runs from any checkout rather than assuming one home-directory layout.
    ap.add_argument("--trustc",
                    default=os.path.join(REPO_ROOT, "build/host/stage2/bin/trustc"))
    ap.add_argument("--aterm",
                    default=os.path.join(os.path.dirname(REPO_ROOT), "aterm"))
    ap.add_argument("--baseline")
    ap.add_argument("--out")
    a = ap.parse_args()

    board, totals = {}, dict(obligations=0, proved=0, failed=0, unknown=0,
                             timed_out=0, runtime_checked=0, kernel_certified=0, smt_backed=0)
    for crate in DEFAULT_CRATES:
        hits = glob.glob(os.path.join(a.aterm, "crates", crate, "src", "lib.rs"))
        if not hits:
            continue
        agg = run_crate(a.trustc, hits[0])
        if agg is None:
            board[crate] = {"error": "timeout"}; continue
        board[crate] = agg
        for k in totals:
            totals[k] += agg[k]

    result = {"totals": totals, "per_crate": board}
    js = json.dumps(result, indent=2)
    if a.out:
        open(a.out, "w").write(js)
    print(js)
    print(f"\nHEADLINE kernel_certified (ay OUT of TCB on real obligations): {totals['kernel_certified']}",
          file=sys.stderr)

    if a.baseline and os.path.exists(a.baseline):
        base = json.load(open(a.baseline))["totals"]["kernel_certified"]
        if totals["kernel_certified"] < base:
            print(f"REGRESSION: kernel_certified {totals['kernel_certified']} < baseline {base}", file=sys.stderr)
            return 1
        print(f"OK: kernel_certified {totals['kernel_certified']} >= baseline {base} (monotone)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
