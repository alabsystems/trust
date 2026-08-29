#!/usr/bin/env python3
"""Trust (D4): the spec-surface PARITY gate — one predicate, three surfaces.

WHY THIS GATE EXISTS
====================
Design of record v3 (`docs/design/2026-07-09-two-language-spec-surface.md`)
ratifies first-class clauses as the sole documented surface and demotes the
upstream attribute spellings to "compat desugaring only". Nothing enforced the
word EXACT in that ruling, so the two surfaces became two implementations, and
two implementations drift. Measured on the sealed toolchain `trust-e26541e3`
before this gate existed, ONE source predicate could mean three different
things:

  * native `fn f(..) ensures result == x + 1` proved a `postcond` obligation,
    while `#[trust::ensures(result == x + 1)]` produced an `unknown` row that
    proved nothing and still read, to a human and to the ratchet, as a
    guarantee;
  * native `decreases e` verified, the `register_tool(trust)` attribute of the
    same name verified IDENTICALLY, and the very same source bytes compiled
    with `--extern trust=<shim>` were E0433 — so LINKING THE COMPAT SHIM
    deleted a working clause;
  * `#[trust::invariant(false)]` was erased outright (the D1 lane), and no
    attribute spelling of a LOOP clause parses at all (E0658).

The paradox that makes all of this matter at once: the surface that WORKS
(raw clause grammar) cannot be used by any crate that must also build on stock
rustc, because cfg-stripping happens after parsing and stock rustc rejects the
file at parse time. So every real crate uses the surface that is demoted,
under-implemented, and drifting.

WHAT IT CHECKS
==============
For each corpus case the same predicate is compiled three ways:

  native   the first-class clause grammar        `fn f(..) requires P`
  tool     `#![register_tool(trust)]` + `#[trust::requires(P)]`
  extern   THE SAME BYTES as `tool`, plus `--extern trust=<trust-spec>`

`tool` and `extern` differ only in the LINK LINE. A divergence between those
two columns is therefore caused by a linking decision alone, which is the
sharpest possible statement of the defect: a crate's contracts change meaning
depending on what it links.

The obligation multiset (kind + outcome, with file/line/digest normalised away)
must match across every surface listed in the case's `agree` set. Cases that
are KNOWN to diverge carry an explicit `xfail` with the reason and are reported
as such; the gate fails if an `xfail` case starts AGREEING (delete the xfail) or
if any non-xfail case diverges (a regression).

This is deliberately a source-to-VERDICT gate, not a source-to-compiles gate.
A surface that accepts a clause and contributes no obligation is exactly the
failure this whole lane exists to eliminate, and only the verdict shows it.

USAGE
=====
    python3 scripts/check_spec_surface_parity.py \
        --toolchain-bin ~/toolchains/trust-current/bin \
        [--spec-lib <path to libtrust.dylib>]   # built from crates/trust-spec

With no `--spec-lib` the shim is built from `crates/trust-spec/src/lib.rs` with
the toolchain under test, which is what makes the `extern` column meaningful —
and which is exactly what ay's ratchet does, so the pairing under test is the
pairing that ships.

WHAT IT REPORTED WHEN WRITTEN (sealed toolchain `trust-e26541e3`)
================================================================
0 of 10 cases agreed on all three surfaces and 8 were LINK-SPLIT — that is,
in 8 of 10 cases the SAME SOURCE BYTES meant something different depending only
on whether `--extern trust=` was on the command line. The two `decreases` cases
are the ones this branch's compiler change repairs: against
`trust-e26541e3` they are reported `skip`, because that toolchain has no
`trust::decreases` mapping and the shim's own fail-closed marker says so out
loud. Against a toolchain built from this branch they must read `OK`. Every
other case is an `xfail` carrying the specific reason it is still open, so this
file doubles as the measured ledger of what a dual-building crate cannot yet
say. `authored_refused` rising here is the healthy direction (amendment §4):
these are the language's limits becoming countable instead of being absorbed
by authors.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from collections import Counter

TOOL_PRELUDE = "#![feature(register_tool)]\n#![register_tool(trust)]\n"
HEADER = '#![crate_type="lib"]\n'
SURFACES = ("native", "tool", "extern")

REC = "{ if n == 0 { 0 } else { g(n - 1) } }"


def case(cid, what, native, attr, agree=SURFACES, xfail=None):
    return {
        "id": cid,
        "what": what,
        "native": HEADER + native,
        "attr": HEADER + attr,
        "agree": tuple(agree),
        "xfail": xfail,
    }


# The corpus. Every entry is a predicate a real crate would plausibly write.
CORPUS = [
    case(
        "requires_holds",
        "a precondition that holds",
        "pub fn f(x: u32) -> u32 requires x < 100 { x + 1 }\n",
        "#[trust::requires(x < 100)]\npub fn f(x: u32) -> u32 { x + 1 }\n",
        xfail="tool-lane `requires` has no ASSUMPTION power: native and extern "
        "emit an `assumption:requires` row, the tool lane emits an unknown "
        "obligation instead. Measured trust-e26541e3.",
    ),
    case(
        "requires_out_of_scope",
        "a precondition naming something that is not a parameter",
        "pub fn f(x: u32) -> u32 requires zzz < 100 { x + 1 }\n",
        "#[trust::requires(zzz < 100)]\npub fn f(x: u32) -> u32 { x + 1 }\n",
        xfail="native refuses with a clause-scope error and extern with E0425, "
        "but the tool lane SILENTLY degrades an out-of-scope name to an "
        "unproved obligation. Fail-closed, but not fail-loud.",
    ),
    case(
        "ensures_holds",
        "a postcondition that holds",
        "pub fn f(x: u32) -> u32 requires x < 100 ensures result == x + 1 { x + 1 }\n",
        "#[trust::requires(x < 100)]\n#[trust::ensures(result == x + 1)]\n"
        "pub fn f(x: u32) -> u32 { x + 1 }\n",
        xfail="attribute `ensures` with a bare `result` payload is dropped as "
        "Unsupported: native proves `postcond`, extern emits `unknown`. "
        "Fixed by branch spec/attribute-ensures-bare-result-2026-08-26; this "
        "xfail must be deleted when that lands.",
    ),
    case(
        "ensures_false",
        "a postcondition that is FALSE — every surface must refuse it",
        "pub fn f(x: u32) -> u32 requires x < 100 ensures result == x + 2 { x + 1 }\n",
        "#[trust::requires(x < 100)]\n#[trust::ensures(result == x + 2)]\n"
        "pub fn f(x: u32) -> u32 { x + 1 }\n",
        xfail="same Unsupported drop as `ensures_holds`. Note that NO surface "
        "falsely proves this one — the divergence is in which kind of row is "
        "reported, not in soundness.",
    ),
    case(
        "decreases_correct",
        "a termination measure that is the right one",
        "pub fn g(n: u32) -> u32 decreases n %s\n" % REC,
        "#[trust::decreases(n)]\npub fn g(n: u32) -> u32 %s\n" % REC,
    ),
    case(
        "decreases_false",
        "a termination measure that is WRONG — must fail closed everywhere",
        "pub fn g(n: u32) -> u32 decreases 0 %s\n" % REC,
        "#[trust::decreases(0)]\npub fn g(n: u32) -> u32 %s\n" % REC,
    ),
    case(
        "decreases_out_of_scope",
        "a termination measure naming something that is not a parameter",
        "pub fn g(n: u32) -> u32 decreases limit %s\n" % REC,
        "#[trust::decreases(limit)]\npub fn g(n: u32) -> u32 %s\n" % REC,
        xfail="the tool lane silently degrades the out-of-scope measure to an "
        "unproved obligation instead of refusing it, exactly as it does for "
        "`requires`. native and extern both refuse.",
    ),
    case(
        "loop_invariant_holds",
        "a loop invariant that holds",
        "pub fn c(limit: u32) {\n let mut n = limit;\n"
        " while n > 0 invariant n <= limit { n -= 1; }\n}\n",
        "pub fn c(limit: u32) {\n let mut n = limit;\n"
        " #[trust::invariant(n <= limit)]\n while n > 0 { n -= 1; }\n}\n",
        xfail="NO attribute spelling of a loop clause exists on any surface: an "
        "attribute in statement position is E0658 (`attributes on expressions "
        "are experimental`) and, for the tool lane, `custom attributes cannot "
        "be applied to expressions`. Loud, but it means a dual-building crate "
        "cannot state a loop invariant at all.",
    ),
    case(
        "loop_invariant_false",
        "a loop invariant that is FALSE",
        "pub fn c(limit: u32) {\n let mut n = limit;\n"
        " while n > 0 invariant n == 0 { n -= 1; }\n}\n",
        "pub fn c(limit: u32) {\n let mut n = limit;\n"
        " #[trust::invariant(n == 0)]\n while n > 0 { n -= 1; }\n}\n",
        xfail="same missing loop-clause attribute position as "
        "`loop_invariant_holds`.",
    ),
    case(
        "unconsumed_trust_attribute",
        "an attribute in the RESERVED `trust::` namespace that no clause claims",
        "pub fn h(a: u32) -> u32 { a + 1 }\n",
        "#[trust::totally_made_up_clause(whatever @@ nonsense)]\n"
        "pub fn h(a: u32) -> u32 { a + 1 }\n",
        xfail="E5 conservation is NOT enforced on the tool lane: an unclaimed "
        "`trust::` attribute carrying arbitrary garbage is accepted in total "
        "silence and the function is credited unchanged. The extern lane "
        "rejects it only incidentally (E0433 — no such proc macro). This is a "
        "SILENT ACCEPTANCE and the corpus records it deliberately; the case is "
        "expected to become a hard error on every surface.",
    ),
]


def compile_case(tc_bin, spec_lib, workdir, name, src, extern):
    name = name.replace("-", "_")
    path = os.path.join(workdir, name + ".rs")
    with open(path, "w") as fh:
        fh.write(src)
    out = os.path.join(workdir, "out")
    os.makedirs(out, exist_ok=True)
    argv = [
        os.path.join(tc_bin, "trustc"),
        "--crate-type=lib",
        "--crate-name=" + name,
        "--edition=2021",
        "--emit=metadata",
        "--out-dir", out,
    ]
    if extern:
        argv += ["--extern", "trust=" + spec_lib]
    argv += [
        "-Z", "trust-verify-level=2",
        "-Z", "trust-verify-profile=unix_hardened",
        "-Z", "trust-verify-timeout-ms=5000",
        "-Z", "trust-verify-output=both",
        "-Z", "trust-policy=advisory",
        "-Z", "trust-verify-session=surface-parity-%s-%d" % (name, int(time.time())),
        path,
    ]
    proc = subprocess.run(argv, capture_output=True, text=True)
    rows, errors = [], []
    for line in proc.stderr.splitlines():
        marker = line.find("TRUST_JSON:")
        if marker < 0:
            if line.startswith("error"):
                errors.append(line.strip())
            continue
        try:
            record = json.loads(line[marker + len("TRUST_JSON:"):])
        except ValueError:
            continue
        if record.get("type") != "function_result":
            continue
        for result in record.get("results", []):
            rows.append((result["kind"], result["outcome"]))
    # A REFUSAL is a verdict too, and a good one. It is compared as its own
    # value so that "both surfaces refuse" counts as agreement while "one
    # refuses and one silently accepts" does not.
    return {"refused": bool(errors), "rows": sorted(rows), "errors": errors[:2]}


def render(result):
    if result["refused"]:
        return "REFUSED(%s)" % result["errors"][0].split(":")[0][:26]
    if not result["rows"]:
        return "accepted, NO obligations"
    counted = Counter(result["rows"])
    return " ".join(
        "%s/%s%s" % (kind, outcome, "" if n == 1 else "x%d" % n)
        for (kind, outcome), n in sorted(counted.items())
    )


def verdict_key(result):
    return (result["refused"], tuple(result["rows"]))


def build_shim(tc_bin, workdir, repo_root):
    src = os.path.join(repo_root, "crates", "trust-spec", "src", "lib.rs")
    if not os.path.isfile(src):
        raise SystemExit("no trust-spec source at %s" % src)
    outdir = os.path.join(workdir, "spec")
    os.makedirs(outdir, exist_ok=True)
    proc = subprocess.run(
        [os.path.join(tc_bin, "trustc"), "--crate-type=proc-macro",
         "--crate-name=trust", "--edition=2024", "-Ztrust-verify=off", "-O",
         "--extern", "proc_macro", "--out-dir", outdir, src],
        capture_output=True, text=True)
    for candidate in ("libtrust.dylib", "libtrust.so"):
        path = os.path.join(outdir, candidate)
        if os.path.isfile(path):
            return path
    raise SystemExit("could not build the trust-spec shim:\n%s" % proc.stderr[-2000:])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain-bin", required=True)
    parser.add_argument("--spec-lib")
    parser.add_argument("--only", help="run a single case id")
    args = parser.parse_args()

    tc_bin = os.path.expanduser(args.toolchain_bin)
    if not os.access(os.path.join(tc_bin, "trustc"), os.X_OK):
        raise SystemExit("no trustc at %s" % tc_bin)
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    workdir = tempfile.mkdtemp(prefix="trust-surface-parity-")
    spec_lib = os.path.expanduser(args.spec_lib) if args.spec_lib else \
        build_shim(tc_bin, workdir, repo_root)

    failures, unexpected_pass = [], []
    for entry in CORPUS:
        if args.only and entry["id"] != args.only:
            continue
        results = {
            "native": compile_case(tc_bin, spec_lib, workdir,
                                   "sp_n_" + entry["id"], entry["native"], False),
            "tool": compile_case(tc_bin, spec_lib, workdir,
                                 "sp_t_" + entry["id"],
                                 TOOL_PRELUDE + entry["attr"], False),
            "extern": compile_case(tc_bin, spec_lib, workdir,
                                   "sp_x_" + entry["id"],
                                   TOOL_PRELUDE + entry["attr"], True),
        }
        keys = {s: verdict_key(results[s]) for s in entry["agree"]}
        agreed = len(set(keys.values())) == 1
        link_split = verdict_key(results["tool"]) != verdict_key(results["extern"])

        # A toolchain that predates the `trust::decreases` mapping is detected
        # EXACTLY, by the shim's own fail-closed marker rather than by a version
        # guess. Such a toolchain cannot express the attribute at all, so its
        # divergence is a property of the toolchain under test, not a
        # regression in this tree. The marker firing is itself the good news:
        # before the guard existed, this same configuration silently ERASED the
        # measure and reported `termination/proved`.
        pre_fix = "reached the trust-spec compatibility passthrough" in \
            " ".join(results["extern"]["errors"])
        if pre_fix and not agreed:
            print("%-26s skip     [toolchain has no `trust::decreases` mapping; "
                  "shim refused, did not erase]" % entry["id"])
            for surface in SURFACES:
                print("      %-7s %s" % (surface, render(results[surface])))
            sys.stdout.flush()
            continue

        status = "OK    " if agreed else "DIVERGE"
        if entry["xfail"]:
            status = "xfail " if not agreed else "XPASS "
        print("%-26s %s%s" % (entry["id"], status,
                              "   [LINK-SPLIT]" if link_split else ""))
        for surface in SURFACES:
            print("      %-7s %s" % (surface, render(results[surface])))
        if not agreed and not entry["xfail"]:
            failures.append(entry["id"])
        if agreed and entry["xfail"]:
            unexpected_pass.append(entry["id"])
        sys.stdout.flush()

    print()
    if failures:
        print("FAIL: %d case(s) diverge between surfaces that must agree: %s"
              % (len(failures), ", ".join(failures)))
    if unexpected_pass:
        print("FAIL: %d xfail case(s) now AGREE — delete their xfail: %s"
              % (len(unexpected_pass), ", ".join(unexpected_pass)))
    if failures or unexpected_pass:
        return 1
    print("spec-surface parity: no new divergence "
          "(%d known-open case(s) still recorded as xfail)"
          % sum(1 for e in CORPUS if e["xfail"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
