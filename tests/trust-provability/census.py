#!/usr/bin/env python3
"""Program 3 Phase A.1 — bucket every non-proving obligation BY CAUSE.

The prove rate is known (1222/5379 = 22.7% on trust-types,
reports/rung3-trustc-self-verifies-trust-types.md:20). The *split* is not, and
each cause wants a different fix — so this instrument exists before any fix does.

  python3 tests/trust-provability/census.py --files 'tests/ui/trust/*.rs' \
      --out reports/provability-census-<date>

Charter: docs/plans/2026-07-25-program-3-prove-rate.md §5 Phase A.

THE FOUR BUCKETS

  (a) incompleteness   the prover could not establish a fact that is true
  (b) authority-gap    a solver DID establish it, but no exact kernel/native
                       authority could be minted, so the row cannot be Proved
                       and can never license an optimization
  (c) unmodeled        the verifier could not model the construct at all
  (d) no-specification NOT a defect. A function with no authored contract has
                       nothing functional to prove. Reported separately and
                       NEVER folded into a prove-rate denominator without
                       saying so (charter Phase A.3).

Bucket (b) is the one that is easy to miss and expensive to leave: those rows
are *provable today* and are being thrown away.

HAZARD: classify on the JSON transport, never on an exit code. See
tests/trust-provability/minimal_pairs.py for why.
"""
import argparse, collections, glob, json, os, re, subprocess, sys, tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get("TRUST_PROVABILITY_TRUSTC",
                        os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"))

AUTHORITY_GAP = re.compile(
    r"without exact kernel/native proof authority|lacked exact kernel/native",
    re.IGNORECASE)
UNMODELED = re.compile(
    r"unsupported|cannot lower|could not lower|capability gap|unmodeled|"
    r"MIR shape the verifier cannot lower|not modeled",
    re.IGNORECASE)
TIMEOUT = re.compile(r"timed? ?out|budget|deadline", re.IGNORECASE)


def bucket(row):
    """(a)|(b)|(c) for a non-proving row. (d) is per-function, not per-row."""
    outcome = row["outcome"].lower()
    reason = row["reason"] or ""
    if outcome == "proved":
        return None
    if AUTHORITY_GAP.search(reason):
        return "b_authority_gap"
    if outcome in ("skipped",) or UNMODELED.search(reason):
        return "c_unmodeled"
    if outcome == "failed":
        # A refutation is not a completeness gap -- unless it is FALSE, which
        # this instrument cannot decide. Counted apart so it is never quietly
        # absorbed into (a). Program 3's wall is about exactly this class.
        return "refuted"
    if outcome in ("timeout",) or TIMEOUT.search(reason):
        return "a_incompleteness_timeout"
    return "a_incompleteness"


def run_file(path, extra):
    d = tempfile.mkdtemp(prefix="census_")
    env = dict(os.environ)
    env["TRUST_SEED_STAIRCASE"] = "1"
    cmd = [TRUSTC, "-Zthreads=1", "-Ztrust-verify=on", "-Ztrust-policy=advisory",
           "-Ztrust-verify-output=json", "-Coverflow-checks=on", "--edition=2021",
           "--crate-type=lib", "--emit=metadata", "--out-dir", d, path] + extra
    return subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=300)


def parse(stderr):
    """-> list of (func_path, [rows]) from the JSON transport."""
    out = []
    for line in stderr.splitlines():
        i = line.find("TRUST_JSON:")
        if i < 0:
            continue
        try:
            obj = json.loads(line[i + len("TRUST_JSON:"):].strip())
        except json.JSONDecodeError:
            continue
        if obj.get("type") != "function_result":
            continue
        rows = []
        for o in (obj.get("results") or []):
            rows.append({
                "outcome": str(o.get("outcome", "?")),
                "kind": str(o.get("kind", "?")),
                "reason": o.get("reason") or "",
                "solver": o.get("solver") or "",
                "counterexample": bool(o.get("counterexample")
                                       or o.get("counterexample_model")),
            })
        out.append((obj.get("function") or obj.get("func_path") or "?", rows))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--files", action="append", required=True,
                    help="glob of .rs files (repeatable)")
    ap.add_argument("--out", help="directory for data.json + CENSUS.md")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--extra", default="", help="extra trustc flags, space-separated")
    args = ap.parse_args()

    if not os.path.exists(TRUSTC):
        print(f"SKIP: no stage2 trustc at {TRUSTC}")
        return 0
    stamp = subprocess.run([TRUSTC, "-V"], capture_output=True, text=True).stdout.strip()
    host = ""
    for ln in subprocess.run([TRUSTC, "-vV"], capture_output=True,
                             text=True).stdout.splitlines():
        if ln.startswith("host:"):
            host = ln.split(":", 1)[1].strip()

    paths = []
    for g in args.files:
        paths.extend(sorted(glob.glob(g, recursive=True)))
    if args.limit:
        paths = paths[:args.limit]
    if not paths:
        print("no input files matched")
        return 2

    buckets = collections.Counter()
    by_kind = collections.Counter()
    gap_kinds = collections.Counter()
    reasons = collections.Counter()
    proved = total = 0
    funcs = fn_with_rows = 0
    failed_files = []

    for p in paths:
        try:
            r = run_file(p, args.extra.split() if args.extra else [])
        except subprocess.TimeoutExpired:
            failed_files.append((p, "timeout"))
            continue
        if "unknown unstable option" in r.stderr or "Unrecognized option" in r.stderr:
            print("HARNESS: a flag this script passes no longer exists:")
            print("  " + (re.search(r"unknown unstable option: `[^`]*`", r.stderr)
                          or re.search(r"Unrecognized option: '[^']*'", r.stderr)).group(0))
            return 2
        got = parse(r.stderr)
        if not got:
            failed_files.append((p, "no transport rows"))
            continue
        for _fn, rows in got:
            funcs += 1
            if rows:
                fn_with_rows += 1
            for row in rows:
                total += 1
                if row["outcome"].lower() == "proved":
                    proved += 1
                    continue
                b = bucket(row)
                buckets[b] += 1
                by_kind[(b, row["kind"])] += 1
                if b == "b_authority_gap":
                    gap_kinds[row["kind"]] += 1
                if row["reason"]:
                    reasons[row["reason"][:110]] += 1

    nonproving = total - proved
    print(f"\ntrustc: {stamp}")
    print(f"host:   {host}")
    print(f"files:  {len(paths)}   functions with transport rows: {fn_with_rows}")
    print(f"\nobligations: {total}   proved: {proved} "
          f"({100.0*proved/total if total else 0:.1f}%)   non-proving: {nonproving}")
    print("\ncause taxonomy (non-proving rows only):")
    for b, n in buckets.most_common():
        print(f"  {b:26} {n:6}  {100.0*n/nonproving if nonproving else 0:5.1f}%")
    if sum(buckets.values()) != nonproving:
        print(f"  !! buckets sum to {sum(buckets.values())}, expected {nonproving}")

    if gap_kinds:
        print("\n(b) authority-gap by kind — these are ALREADY PROVED by a solver:")
        for k, n in gap_kinds.most_common(12):
            print(f"  {k:28} {n}")

    print("\ntop reasons:")
    for rs, n in reasons.most_common(12):
        print(f"  {n:5}  {rs}")

    if failed_files:
        print(f"\n{len(failed_files)} file(s) produced no rows "
              f"(NOT counted anywhere — they are absent data, not zeros):")
        for p, why in failed_files[:8]:
            print(f"  {os.path.relpath(p, REPO)}: {why}")

    if args.out:
        os.makedirs(args.out, exist_ok=True)
        with open(os.path.join(args.out, "data.json"), "w") as fh:
            json.dump({
                "trustc": stamp, "host": host, "files": len(paths),
                "obligations": total, "proved": proved, "non_proving": nonproving,
                "buckets": dict(buckets),
                "authority_gap_by_kind": dict(gap_kinds),
                "by_bucket_kind": {f"{b}|{k}": n for (b, k), n in by_kind.items()},
                "no_rows_files": [p for p, _ in failed_files],
            }, fh, indent=2, sort_keys=True)
            fh.write("\n")
        print(f"\nwrote {args.out}/data.json")

    print("\nNOTE (charter Phase A.3): bucket (d) no-specification is NOT reported "
          "here as a row bucket.\nA function with no authored contract has nothing "
          "functional to prove; those obligations do not\nexist rather than fail. "
          "Do not quote a prove rate without stating which denominator it uses.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
