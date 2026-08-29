#!/usr/bin/env python3
# trust_ir_b4_classifier.py — pre-register the B4 (Borrow-family) wave populations
# from a producer-scorecard data.json, offline, zero compiler changes.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# The 100%-lowering campaign's law is instrument-before-fix with PRE-REGISTERED
# populations (CLAUDE.md; reports/trust-ir-frontier-table-2026-08-20.md §7).
# The B4 scout (2026-08-28) found that the Borrow family's occurrence mass
# (~2,650) collapses to ~150 bodies at body granularity, and that the single
# largest slice is not a borrow shape at all but a MACRO: bodies whose EVERY
# blocker span sits inside the assert_eq!/assert_ne! expansion
# (library/core/src/macros/mod.rs:40-110). 594/1121 Borrow(non-local place)
# details are macro-expansion spans, so any sub-taxonomy keyed on source
# snippets undercounts — this classifier keys on the EXPANSION SITE, exactly
# as the scout's risk row prescribes.
#
# WHAT IT REPORTS
# ---------------
#   assert_only   bodies whose every reason_detail span is inside the
#                 assert-machinery window (the B4.3 population), plus the tag
#                 histogram inside that population
#   borrow_sole   bodies whose only distinct reason tag is
#                 Borrow(non-local place), classified by source shape when the
#                 span's file is readable (unit-literal / nested-ref /
#                 const-aggregate / field / index / other)
#
# Measured at commit time on postbuild-locked-2026-08-27 (the canonical
# corpus): assert_only = 99, borrow_sole = 26. Re-run rather than quote:
#
#   python3 scripts/trust_ir_b4_classifier.py \
#     reports/trust-ir-producer-baseline-2026-07-01/postbuild-locked-2026-08-27/data.json \
#     --expect assert_only=99 --expect borrow_sole=26
#
# --expect makes a drifted number a non-zero exit instead of a stale quote
# (the frontier table's discipline). --selftest mutates the predicate window
# and requires the count to MOVE, proving the gate is load-bearing.

import argparse
import collections
import json
import re
import sys

MACRO_SPAN = re.compile(r"library/core/src/macros/mod\.rs:(\d+):")
ASSERT_WINDOW = (40, 110)


def load_bodies(path):
    with open(path) as fh:
        data = json.load(fh)
    corpora = data.get("corpora", {})
    for name, corpus in corpora.items():
        for frow in corpus.get("files", []):
            for body in frow.get("bodies", []):
                yield frow.get("file", "?"), body


def all_spans_in_assert_window(body, window):
    details = body.get("reason_details", [])
    if not details:
        return False
    hits = 0
    for det in details:
        m = MACRO_SPAN.search(det)
        if m and window[0] <= int(m.group(1)) <= window[1]:
            hits += 1
        else:
            return False
    return hits > 0


SRC_SPAN = re.compile(r"(/[^ :]+\.rs):(\d+):(\d+): (\d+):(\d+)")


def classify_borrow_source(detail):
    """Best-effort source-shape class for a Borrow(non-local place) span."""
    m = SRC_SPAN.search(detail)
    if not m:
        return "unreadable"
    path, line, col, _eline, _ecol = (
        m.group(1),
        int(m.group(2)),
        int(m.group(3)),
        m.group(4),
        m.group(5),
    )
    try:
        with open(path) as fh:
            src = fh.read().split("\n")[line - 1]
    except OSError:
        return "unreadable"
    snippet = src[max(0, col - 1) :].strip()
    if snippet.startswith("&()"):
        return "unit-literal"
    if snippet.startswith("&&") or snippet.startswith("& &"):
        return "nested-ref"
    if re.match(r"&\s*\[", snippet):
        return "aggregate-literal"
    if re.match(r"&\s*\w+\s*\{", snippet):
        return "struct-literal"
    if re.match(r"&(?:mut\s+)?[\w.]+\[", snippet):
        return "index"
    if re.match(r"&(?:mut\s+)?\w+(\.\w+)+\b(?!\()", snippet):
        return "field"
    if re.match(r"&\s*\*", snippet):
        return "deref-chain"
    if re.match(r"&\s*[A-Z][\w:]*::", snippet):
        return "const-path"
    return "other"


def run(path, window):
    assert_pop = []
    assert_tags = collections.Counter()
    borrow_sole = []
    borrow_classes = collections.Counter()
    for fname, body in load_bodies(path):
        if body.get("unsupported", 0) == 0:
            continue
        reasons = body.get("reasons", [])
        details = body.get("reason_details", [])
        if all_spans_in_assert_window(body, window):
            assert_pop.append((fname, body.get("def", "?")))
            for r in reasons:
                assert_tags[r] += 1
        if set(reasons) == {"Borrow(non-local place)"}:
            classes = sorted(
                {classify_borrow_source(det) for r, det in zip(reasons, details) if r == "Borrow(non-local place)"}
            )
            borrow_sole.append((fname, body.get("def", "?"), "+".join(classes) or "unreadable"))
            for c in classes:
                borrow_classes[c] += 1
    return assert_pop, assert_tags, borrow_sole, borrow_classes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("data_json")
    ap.add_argument("--expect", action="append", default=[], metavar="KEY=N")
    ap.add_argument("--list", action="store_true", help="print the full body lists")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()

    assert_pop, assert_tags, borrow_sole, borrow_classes = run(args.data_json, ASSERT_WINDOW)

    print(f"assert_only = {len(assert_pop)} bodies (every blocker span in macros/mod.rs:{ASSERT_WINDOW[0]}-{ASSERT_WINDOW[1]})")
    print(f"  tags inside: {dict(assert_tags.most_common(10))}")
    print(f"borrow_sole = {len(borrow_sole)} bodies (only distinct tag = Borrow(non-local place))")
    print(f"  source classes: {dict(borrow_classes.most_common())}")
    if args.list:
        print("\n[assert_only]")
        for fname, defn in assert_pop:
            print(f"  {defn}  ({fname})")
        print("\n[borrow_sole]")
        for fname, defn, cls in borrow_sole:
            print(f"  {defn}  [{cls}]  ({fname})")

    if args.selftest:
        # Mutation: shrink the window to a single line — the count must MOVE
        # (a predicate that reports the same population under a broken window
        # is not load-bearing).
        mut_pop, _, _, _ = run(args.data_json, (ASSERT_WINDOW[0], ASSERT_WINDOW[0]))
        if len(mut_pop) == len(assert_pop):
            print("SELFTEST FAIL: window mutation did not move assert_only", file=sys.stderr)
            return 3
        print(f"selftest ok: window mutation moved assert_only {len(assert_pop)} -> {len(mut_pop)}")

    counts = {"assert_only": len(assert_pop), "borrow_sole": len(borrow_sole)}
    rc = 0
    for spec in args.expect:
        key, _, want = spec.partition("=")
        got = counts.get(key)
        if got != int(want):
            print(f"EXPECT FAIL: {key} = {got}, expected {want}", file=sys.stderr)
            rc = 2
    return rc


if __name__ == "__main__":
    sys.exit(main())
