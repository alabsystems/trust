#!/usr/bin/env python3
"""Vacuity table: does a contract kind's PROVABLE SET consist of exactly the tautologies?

WHY THIS EXISTS
---------------
A widening whose new acceptances are exactly the TAUTOLOGIES is the signature of
a false-proof class. It is easy to ship by accident, it moves every headline
metric, and it means nothing: the row is provable precisely when it is worthless.

The mechanism is always the same. A verification condition is discharged by
asking a solver whether its VIOLATION formula is unsatisfiable. That question is
about the PROGRAM only if the violation formula conjoins the program state
reaching the obligation's program point with the negated predicate. If instead
the formula is the bare negated clause -- `Not(P)` with P's free names bound to
nothing -- then UNSAT of it is validity of P, a fact about the clause's TEXT. A
row meaning "P is valid" is proved exactly when P constrains nothing.

So the diagnostic is a differential one, and it needs a predicate that is TRUE OF
EVERY VALUE OF THE TYPE BUT NOT A LOGICAL TAUTOLOGY. `x >= 0` for `x: u32` is
the canonical one: any lane that reasons about the program can prove it, and any
lane that only checks the text cannot. A kind that proves `1 == 1` and `x == x`
while failing `x >= 0` is not reasoning about the program at all.

MEASURED, on the sealed toolchain `trust-e26541e3`:

    kind        1==1     x==x     true     false    x>=0     x>100     verdict
    requires    unknown  unknown  skipped  skipped  unknown  unknown   REFUSED
    ensures     proved   proved   unknown  unknown  PROVED   unknown   CONTENTFUL
    invariant   proved   proved   unknown  unknown  unknown  unknown   VACUOUS
    decreases   unknown  unknown  unknown  unknown  unknown  unknown   REFUSED

`invariant` proves the two tautologies and nothing else -- the signature. Its
proved rows carry `solver=clean-kernel-certified` and `kind=invariant`, i.e. they
are exactly what a ratchet counts as `proved_by_kind.invariant` AND
`kernel_certified`. `ensures` proves `x >= 0`, which is the discriminator: that
lane is body-aware and is sound.

This script is therefore EXPECTED TO FAIL on `trust-e26541e3` and on any
toolchain that predates the kind gate in `trust_certify::certify_vc`. That
failure is the finding, not a defect in the script.

Usage:
    python3 scripts/check_kernel_authority_vacuity.py [--trustc PATH] [--json]

Exit status: 0 if no kind's provable set is exactly the tautologies; 1 otherwise.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache 2.0
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

# The probe body is deliberately trivial and total: `x / 2` cannot panic for
# `x: u32`, so nothing the body does can mask a clause's outcome.
BODY = "pub fn f(x: u32) -> u32 { x / 2 }"

# Each probe is (label, predicate, class). The classes are what make the table a
# DIAGNOSTIC rather than a list:
#   tautology     - valid as pure logic, independent of the program or the type
#   type_universal- true of EVERY value of the parameter's type, NOT a tautology
#   contingent    - true of some values and false of others
#   literal       - the degenerate constants, included because they are the
#                   first thing anyone writes and they probe the parser's path
PROBES = [
    ("1==1", "1 == 1", "tautology"),
    ("x==x", "x == x", "tautology"),
    ("true", "true", "literal"),
    ("false", "false", "literal"),
    ("x>=0", "x >= 0", "type_universal"),
    ("x>100", "x > 100", "contingent"),
]

KINDS = ["requires", "ensures", "invariant", "decreases"]


def run_probe(trustc: str, workdir: str, kind: str, label: str, predicate: str):
    """Compile one probe and return (outcome, solver) for the clause's row."""
    stem = f"probe_{kind}_{label}".replace("=", "eq").replace(">", "gt").replace("<", "lt")
    src = os.path.join(workdir, f"{stem}.rs")
    with open(src, "w") as handle:
        handle.write(
            "#![feature(register_tool)]\n"
            "#![register_tool(trust)]\n"
            f"#[trust::{kind}({predicate})]\n"
            f"{BODY}\n"
        )
    proc = subprocess.run(
        [
            trustc, "--edition", "2021", "--crate-type", "lib",
            "-Ztrust-verify=on", "-Ztrust-policy=advisory",
            "-Ztrust-verify-output=json", "-Ztrust-verify-level=1",
            src, "--out-dir", workdir,
        ],
        capture_output=True, text=True, timeout=600,
    )
    outcome, solver = "absent", "-"
    for line in (proc.stdout + proc.stderr).splitlines():
        if not line.startswith("TRUST_JSON:"):
            continue
        try:
            payload = json.loads(line[len("TRUST_JSON:"):])
        except json.JSONDecodeError:
            continue
        if payload.get("type") != "function_result":
            continue
        if not payload.get("function", "").endswith("::f"):
            continue
        for row in payload.get("results", []):
            if row.get("kind") == "no_obligations":
                continue
            # A `proved` row anywhere for this function is what matters: it is
            # the row that would reach a ratchet's proved_by_kind bucket.
            if row.get("outcome") == "proved":
                return "proved", row.get("solver", "?")
            if outcome == "absent":
                outcome, solver = row.get("outcome", "?"), row.get("solver", "?")
    return outcome, solver


def classify(rows):
    """Verdict for one kind, from the set of predicate classes it PROVES."""
    proved_classes = {cls for (_, _, cls), (outcome, _) in rows if outcome == "proved"}
    if not proved_classes:
        return "REFUSED", "nothing is provable; the kind reaches no proof authority"
    if proved_classes == {"tautology"}:
        return "VACUOUS", (
            "the provable set is EXACTLY the tautologies -- the row is provable precisely "
            "when it constrains nothing, so its formula is not a statement about the program"
        )
    if proved_classes & {"type_universal", "contingent"}:
        return "CONTENTFUL", (
            "a non-tautology is provable, so the lane reasons about the program and not "
            "merely about the clause text"
        )
    return "REVIEW", f"provable classes {sorted(proved_classes)} need a human judgement"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--trustc",
        default=os.environ.get(
            "TRUSTC", os.path.expanduser("~/toolchains/trust-current/bin/trustc")
        ),
        help="trustc to probe (default: the sealed ~/toolchains/trust-current)",
    )
    parser.add_argument("--json", action="store_true", help="emit machine-readable results")
    args = parser.parse_args()

    trustc = args.trustc
    if not (os.path.isfile(trustc) and os.access(trustc, os.X_OK)) and not shutil.which(trustc):
        print(f"error: trustc not found or not executable: {trustc}", file=sys.stderr)
        return 2

    results, verdicts = {}, {}
    with tempfile.TemporaryDirectory(prefix="vacuity-") as workdir:
        for kind in KINDS:
            rows = []
            for probe in PROBES:
                label, predicate, _ = probe
                rows.append((probe, run_probe(trustc, workdir, kind, label, predicate)))
            results[kind] = rows
            verdicts[kind] = classify(rows)

    if args.json:
        print(json.dumps(
            {
                "trustc": trustc,
                "kinds": {
                    kind: {
                        "probes": {
                            label: {"predicate": pred, "class": cls,
                                    "outcome": outcome, "solver": solver}
                            for (label, pred, cls), (outcome, solver) in rows
                        },
                        "verdict": verdicts[kind][0],
                        "reason": verdicts[kind][1],
                    }
                    for kind, rows in results.items()
                },
            },
            indent=2,
        ))
    else:
        # Wide enough for the longest probe label AND the longest outcome word,
        # so the table stays readable when every cell says "unknown".
        width = max(
            max(len(label) for label, _, _ in PROBES),
            len("runtime_checked"),
        ) + 2
        header = "kind".ljust(11) + "".join(label.ljust(width) for label, _, _ in PROBES)
        print(header + "verdict")
        print("-" * (len(header) + 12))
        for kind in KINDS:
            cells = "".join(outcome.ljust(width) for _, (outcome, _) in results[kind])
            print(kind.ljust(11) + cells + verdicts[kind][0])
        print()
        for kind in KINDS:
            verdict, reason = verdicts[kind]
            print(f"  {kind:<10} {verdict}: {reason}")
            for (label, _, cls), (outcome, solver) in results[kind]:
                if outcome == "proved":
                    print(f"               proved {label} ({cls}) via {solver}")

    vacuous = [kind for kind, (verdict, _) in verdicts.items() if verdict == "VACUOUS"]
    if vacuous:
        print(
            "\nFAIL: "
            + ", ".join(vacuous)
            + " -- provable set is exactly the tautologies. Such a row is a trusted "
            "assumption dressed as a proof; it must not reach kernel proof authority.",
            file=sys.stderr,
        )
        return 1
    print("\nOK: no kind's provable set is exactly the tautologies.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
