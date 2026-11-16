#!/usr/bin/env python3
# trust_ir_verifier_acceptance_pins.py --- the verdicts the trust-ir verification path must reproduce.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# The 2026-09-29 compile-path ruling (R-1/R-2, docs/plans/2026-09-29-trust-ir-sole-compile-path.md)
# moves verification off MIR: trust-ir becomes the only input, and the MIR-derived
# lanes survive only as test oracles. Every soundness hole the MIR lanes closed is
# pinned by a tests/ui/trust fixture that says what verdict a program must get
# ("certify refuses this impostor", "std's own item keeps its credit"). When the
# trust-ir path takes over, it must give those programs the SAME verdicts, or it
# re-opens the hole (a refusal becomes an accept) or silently loses a capability
# (an accept becomes a refusal).
#
# scripts/trust_ir_verifier_acceptance_pins.txt names those fixtures and records,
# per fixture, the verdict class its directives demand today. This script is the
# ratchet on that record:
#
#   --check   every listed file exists, is listed once, and its directives still
#             demand the recorded verdict class. A refusal pin that is edited into
#             a check-pass (or loses a revision) fails here, naming the file, so the
#             change has to be made to the manifest too, in the open.
#   --derive  print the class this script derives for each listed file (for
#             writing a new entry).
#
# THE VERDICT CLASS is derived from compiletest directives only, per revision:
# a revision PASSES when a `check-pass`/`build-pass`/`run-pass` directive applies
# to it (unprefixed, or `//@[rev]`), and otherwise must FAIL (a ui test with no
# pass mode is expected not to compile). The class is `accept` (every revision
# passes), `refuse` (every revision fails) or `mixed:<passing>/<revisions>`.
# It says nothing about WHICH errors; the fixture's own `//~` annotations do.
#
# This never builds or runs a compiler.

from __future__ import annotations

import argparse
import os
import re
import sys

MANIFEST_DEFAULT = os.path.join("scripts", "trust_ir_verifier_acceptance_pins.txt")
PASS_MODES = ("check-pass", "build-pass", "run-pass")
DIRECTIVE = re.compile(r"^\s*//@(?:\[([^\]]+)\])?\s*(.*?)\s*$")


def repo_root() -> str:
    return os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def derive_class(path: str) -> str:
    revisions: list[str] = []
    global_pass = False
    rev_pass: set[str] = set()
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            m = DIRECTIVE.match(line)
            if not m:
                continue
            prefix, body = m.group(1), m.group(2)
            if prefix is None and body.startswith("revisions:"):
                revisions.extend(body[len("revisions:"):].split())
                continue
            mode = body.split(":", 1)[0].strip()
            if mode in PASS_MODES:
                if prefix is None:
                    global_pass = True
                else:
                    for rev in prefix.split(","):
                        rev_pass.add(rev.strip())
    if not revisions:
        return "accept" if global_pass else "refuse"
    passing = sum(1 for rev in revisions if global_pass or rev in rev_pass)
    if passing == len(revisions):
        return "accept"
    if passing == 0:
        return "refuse"
    return f"mixed:{passing}/{len(revisions)}"


def read_manifest(path: str) -> list[tuple[int, str, str, str]]:
    entries = []
    with open(path, encoding="utf-8") as fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.split("#", 1)[0].strip()
            if not line:
                continue
            parts = line.split(None, 2)
            if len(parts) < 3:
                raise SystemExit(
                    f"{path}:{lineno}: expected `<path> <class> <invariant-tag>`, got {raw.rstrip()!r}"
                )
            entries.append((lineno, parts[0], parts[1], parts[2]))
    return entries


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--manifest", default=MANIFEST_DEFAULT)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--derive", action="store_true")
    args = ap.parse_args()

    root = repo_root()
    manifest = os.path.join(root, args.manifest)
    entries = read_manifest(manifest)
    problems = []
    seen: dict[str, int] = {}
    for lineno, rel, recorded, tag in entries:
        if rel in seen:
            problems.append(f"{args.manifest}:{lineno}: {rel} is already listed at line {seen[rel]}")
            continue
        seen[rel] = lineno
        if not rel.startswith("tests/ui/trust/") or not rel.endswith(".rs"):
            problems.append(f"{args.manifest}:{lineno}: {rel} is not a tests/ui/trust/**.rs fixture")
            continue
        full = os.path.join(root, rel)
        if not os.path.isfile(full):
            problems.append(f"{args.manifest}:{lineno}: {rel} does not exist")
            continue
        derived = derive_class(full)
        if args.derive:
            print(f"{rel}  {derived}  {tag}")
        elif derived != recorded:
            problems.append(
                f"{args.manifest}:{lineno}: {rel}: the manifest records `{recorded}`, its directives "
                f"now demand `{derived}`. A pin's verdict moved; change the manifest in the same "
                f"commit and say why, or restore the fixture."
            )
    if problems:
        for p in problems:
            print(p, file=sys.stderr)
        return 1
    if args.check:
        print(f"trust-ir verifier acceptance pins: OK ({len(entries)} fixtures)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
