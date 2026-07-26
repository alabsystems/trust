#!/usr/bin/env python3
"""Program 3, item C.8 — the monotone proof/certification ratchet.

The completeness-gap ruling
(`docs/design/2026-07-25-completeness-gap-policy-ruling.md`, Andrew 2026-07-25:
*"B for now so that we can dogfood, but eventually A"*) names one predictable
failure mode for policy B:

> *"the build passes" becomes the definition of done and the certified fraction
> never moves.*

This is the defence, and the ruling requires it to exist **in the same change as
the default flip, not after it**. It is landed ahead of the flip deliberately, so
the flip is a smaller change with its guard already in place.

    python3 tests/trust-provability/ratchet.py --check     # CI gate
    python3 tests/trust-provability/ratchet.py --update    # accept a new floor

WHAT IT RATCHETS. Per corpus: the PROVED fraction and, separately, the
CERTIFIED fraction. They are different numbers and only the second licenses an
optimization — a row can be `Proved` by a solver and still carry no exact
kernel/native authority, which is the authority gap this program exists to close.
Reporting only "proved" would let the certified fraction rot silently, which is
exactly the failure mode above.

DIRECTION. Regression is what is prevented, not absolute level. A drop fails; a
rise is progress and wants `--update` plus a sentence in the commit saying why it
moved. That asymmetry is the whole mechanism.

HAZARD, inherited from every instrument here: classify on the JSON transport,
never on an exit code. A renamed flag exits non-zero and a harness that reads
that as "rejected" will certify a live defect as fixed — it has happened in this
repo. See `tests/trust-provability/README.md`.
"""
import argparse, glob, json, os, subprocess, sys, tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get("TRUST_PROVABILITY_TRUSTC",
                        os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"))
BASELINE = os.path.join(os.path.dirname(__file__), "ratchet_baseline.json")

# Corpora to ratchet. Each is a glob relative to the repo root.
CORPORA = {
    "provability-corpus": "tests/trust-provability/corpus/*.rs",
}


def measure(pattern):
    """-> {proved, certified, total, files} over one corpus, from the transport."""
    proved = certified = total = 0
    files = 0
    for path in sorted(glob.glob(os.path.join(REPO, pattern))):
        d = tempfile.mkdtemp(prefix="ratchet_")
        env = dict(os.environ)
        env["TRUST_SEED_STAIRCASE"] = "1"
        try:
            r = subprocess.run(
                [TRUSTC, "-Zthreads=1", "-Ztrust-verify=on", "-Ztrust-policy=advisory",
                 "-Ztrust-verify-output=json", "-Coverflow-checks=on", "--edition=2021",
                 "--crate-type=lib", "--emit=metadata", "--out-dir", d, path],
                capture_output=True, text=True, env=env, timeout=300)
        except subprocess.TimeoutExpired:
            print(f"  !! timeout on {os.path.relpath(path, REPO)} — NOT counted as zero; "
                  f"absent data is not a measurement")
            continue
        if "unknown unstable option" in r.stderr or "Unrecognized option" in r.stderr:
            sys.exit("HARNESS: a flag this script passes no longer exists; fix the harness "
                     "rather than reading its failure as a verdict")
        saw_rows = False
        for line in r.stderr.splitlines():
            i = line.find("TRUST_JSON:")
            if i < 0:
                continue
            try:
                obj = json.loads(line[i + len("TRUST_JSON:"):].strip())
            except json.JSONDecodeError:
                continue
            if obj.get("type") != "function_result":
                continue
            for row in obj.get("results") or []:
                saw_rows = True
                total += 1
                if str(row.get("outcome", "")).lower() == "proved":
                    proved += 1
                    # CERTIFIED is strictly stronger than proved: the row must
                    # carry evidence an independent checker validated. Only this
                    # licenses an erasure.
                    ev = row.get("proof_evidence") or {}
                    strength = (ev.get("strength") or {})
                    assurance = strength.get("assurance") or (ev.get("evidence") or {}).get(
                        "assurance")
                    if assurance == "Certified":
                        certified += 1
        if saw_rows:
            files += 1
    return {"proved": proved, "certified": certified, "total": total, "files": files}


def stamp():
    v = subprocess.run([TRUSTC, "-V"], capture_output=True, text=True).stdout.strip()
    host = ""
    for ln in subprocess.run([TRUSTC, "-vV"], capture_output=True, text=True).stdout.splitlines():
        if ln.startswith("host:"):
            host = ln.split(":", 1)[1].strip()
    return v, host


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true", help="fail if a fraction regressed")
    g.add_argument("--update", action="store_true", help="accept the current numbers as the floor")
    args = ap.parse_args()

    if not os.path.exists(TRUSTC):
        print(f"SKIP: no stage2 trustc at {TRUSTC}")
        return 0

    v, host = stamp()
    print(f"trustc: {v}\nhost:   {host}\n")
    observed = {name: measure(pat) for name, pat in CORPORA.items()}
    for name, m in observed.items():
        pr = 100.0 * m["proved"] / m["total"] if m["total"] else 0.0
        ce = 100.0 * m["certified"] / m["total"] if m["total"] else 0.0
        print(f"  {name}: {m['files']} files · {m['total']} obligations · "
              f"proved {m['proved']} ({pr:.1f}%) · certified {m['certified']} ({ce:.1f}%)")

    if args.update:
        json.dump({"_trustc": v, "_host": host, "corpora": observed},
                  open(BASELINE, "w"), indent=1, sort_keys=True)
        open(BASELINE, "a").write("\n")
        print(f"\nwrote {os.path.relpath(BASELINE, REPO)} — say in the commit WHY it moved")
        return 0

    if not os.path.exists(BASELINE):
        print("\nno baseline; run --update once to establish the floor")
        return 0
    base = json.load(open(BASELINE)).get("corpora", {})
    regressions = []
    for name, m in observed.items():
        b = base.get(name)
        if b is None:
            print(f"\n  {name}: new corpus, not in the baseline — run --update")
            continue
        for axis in ("proved", "certified"):
            # Compare FRACTIONS, not counts: adding a fixture must not be able to
            # dilute the floor, and removing one must not be able to raise it.
            ob = m[axis] / m["total"] if m["total"] else 0.0
            bb = b[axis] / b["total"] if b["total"] else 0.0
            if ob + 1e-9 < bb:
                regressions.append(
                    f"  {name}.{axis}: {100*bb:.1f}% -> {100*ob:.1f}%  "
                    f"({b[axis]}/{b['total']} -> {m[axis]}/{m['total']})")
    if regressions:
        print("\nRATCHET REGRESSION — a fraction went DOWN:")
        print("\n".join(regressions))
        print("\nThe ratchet prevents regression, not stagnation. If this drop is "
              "intended,\nsay why in the commit and rerun with --update.")
        return 1
    print("\nratchet OK — no fraction regressed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
