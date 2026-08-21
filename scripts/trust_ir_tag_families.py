#!/usr/bin/env python3
"""The trust-ir producer TAG -> LANE FAMILY map: its checker and its census.

WHY THIS FILE EXISTS (2026-08-19)
---------------------------------
Nothing in the tree said which fail-closed tag belongs to which lane family, so
three agents partitioned the same corpus three different ways on the same day:

    pattern-family sole  =  107 / 164 / 197
    memory-family  sole  =  128 / 337 / 342

Every rank in the roadmap is family-boundary-dependent, so with a 90-body spread
on PATTERN and a 214-body spread on MEMORY, every rank was unfalsifiable — two
lanes could be ranked in either order by choosing a boundary, and nobody was
choosing one on purpose.

`trust_ir_tag_families.json` is that boundary, as data. This script is:

  * `--check`  the GATE. Fails when the producer emits a tag with no family
               entry, when the static scan can no longer explain a tag the corpus
               observed (a new emission mechanism), or when the map carries an
               entry that matches nothing. A slice cannot silently widen a family
               or invent a tag outside one.
  * `--report` the CENSUS. Per family: tags, tag events, bodies touched, and
               bodies SOLE (every tag in the body belongs to this family — the
               honest lower bound on what clearing the family would make clean).
               Prints the per-head breakdown inside each family so an alternative
               boundary can be RECOMPUTED from the table rather than argued, and
               prints the UNCLASSIFIED bucket in full.

The census answers "how many bodies would this family unblock", which is the
CLEAN-rate question. It does not answer "how many would become Agreed" — measured
at ~1% marginal, that is a different and much smaller number. See
`trust_ir_marginal_conversion.py`; do not price a lane off a sole-count alone.

USAGE
-----
    trust_ir_tag_families.py --check [--artifact DIR]
    trust_ir_tag_families.py --report DIR [--top N]

`--check` with no artifact scans the source only; with an artifact it also runs
the scan-completeness self-test that found `trust-mir-extract` as a fourth
emission root. Exit: 0 ok · 1 a tag has no family (or a stale/missing entry).
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAP_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "trust_ir_tag_families.json")

LIT = re.compile(r'"((?:[^"\\\n]|\\.)*)"')
TAG_GRAMMAR = re.compile(r"^[A-Z][A-Za-z0-9]*(\(.+\))?$")
FN_STATIC_STR = re.compile(r"fn\s+(\w+)\s*\([^{]*?->\s*&'static str\s*\{")


def load_map(path=MAP_PATH):
    with open(path) as fh:
        return json.load(fh)


def _fn_bodies(text):
    """Yield the source of every `fn ... -> &'static str` body (brace-matched)."""
    for m in FN_STATIC_STR.finditer(text):
        i = text.index("{", m.end() - 1)
        depth, j = 0, i
        while j < len(text):
            if text[j] == "{":
                depth += 1
            elif text[j] == "}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        yield m.group(1), text[i:j]


def scan_source(spec, repo=REPO):
    """Extract the tag universe the producer source can emit: {tag: {rule, ...}}."""
    universe = collections.defaultdict(set)

    def keep(v):
        return TAG_GRAMMAR.fullmatch(v) and "{" not in v and "}" not in v

    for root in spec["scan_roots"]:
        path = os.path.join(repo, root["path"])
        if not os.path.exists(path):
            print(f"MISSING scan root {root['path']} — the map cannot be checked "
                  f"against a source tree it cannot read", file=sys.stderr)
            continue
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        rules = set(root["rules"])
        if "R2" in rules:
            for fname, body in _fn_bodies(text):
                for m in LIT.finditer(body):
                    if keep(m.group(1)):
                        universe[m.group(1)].add(f"R2:{root['path']}:{fname}")
        for ln in text.splitlines():
            if ln.lstrip().startswith("//"):
                continue
            for m in LIT.finditer(ln):
                v = m.group(1)
                if not keep(v):
                    continue
                if "R1" in rules and "unsupported" in ln and ".push" in ln:
                    universe[v].add(f"R1:{root['path']}")
                if "R3" in rules and "Reject(" in ln:
                    universe[v].add(f"R3:{root['path']}")
                if "R5" in rules and ".ok_or(" in ln:
                    universe[v].add(f"R5:{root['path']}")
                if "R4" in rules and "(" in v:
                    universe[v].add(f"R4:{root['path']}")
    for t in spec.get("legacy_tags", []):
        universe[t].add("legacy_tags")
    for t in spec.get("not_a_tag", {}):
        universe.pop(t, None)
    return universe


def head_of(tag):
    return tag.split("(", 1)[0] if "(" in tag else tag


def family_of(tag, spec):
    ov = spec.get("tag_overrides", {})
    if tag in ov:
        return ov[tag], "override"
    h = head_of(tag)
    hr = spec.get("head_rules", {})
    if h in hr:
        return hr[h], "head"
    if tag in hr:  # a legacy lowercase tag listed whole
        return hr[tag], "head"
    return None, None


def observed_tags(artifact, corpus="ui_sample"):
    """{tag: occurrences} and the per-body reason lists, from a scorecard artifact."""
    path = artifact if artifact.endswith(".json") else os.path.join(artifact, "data.json")
    with open(path) as fh:
        doc = json.load(fh)
    c = doc["corpora"][corpus]
    bodies = [b for f in c["files"] for b in f.get("bodies", [])]
    hist = collections.Counter(t for b in bodies for t in b.get("reasons", []))
    return doc, bodies, hist


# --------------------------------------------------------------------------
# the gate
# --------------------------------------------------------------------------
def check(spec, artifact=None) -> int:
    universe = scan_source(spec)
    errors, notes = [], []

    print(f"scan roots: {len(spec['scan_roots'])} · "
          f"tag universe from source: {len(universe)}")

    unmapped = sorted(t for t in universe if family_of(t, spec)[0] is None)
    if unmapped:
        errors.append(
            f"{len(unmapped)} tag(s) the producer can emit have NO family entry. Add a "
            f"`head_rules` entry for the head, or a `tag_overrides` entry for the exact "
            f"tag, in scripts/trust_ir_tag_families.json — or, if the scan picked up a "
            f"literal that is not a tag, name it in `not_a_tag` WITH the reason:\n    "
            + "\n    ".join(unmapped[:40])
            + (f"\n    ... +{len(unmapped) - 40} more" if len(unmapped) > 40 else ""))

    fams = set(spec["families"])
    for k, v in list(spec["head_rules"].items()) + list(spec["tag_overrides"].items()):
        if v not in fams:
            errors.append(f"entry {k!r} names family {v!r}, which is not in `families`")

    # stale entries: a rule that matches nothing the producer can emit any more.
    heads_seen = {head_of(t) for t in universe} | set(universe)
    stale_heads = sorted(h for h in spec["head_rules"] if h not in heads_seen)
    stale_ov = sorted(t for t in spec["tag_overrides"] if t not in universe)
    stale_nat = sorted(t for t in spec.get("not_a_tag", {})
                       if t not in scan_source({**spec, "not_a_tag": {}}))
    if stale_heads:
        errors.append(f"stale `head_rules` entr(ies) — the producer no longer emits any tag "
                      f"with this head: {stale_heads}")
    if stale_ov:
        errors.append(f"stale `tag_overrides` entr(ies) — no such tag in the producer: "
                      f"{stale_ov}")
    if stale_nat:
        errors.append(f"stale `not_a_tag` entr(ies) — the scan no longer produces this "
                      f"false positive: {stale_nat}")

    if artifact:
        _, bodies, hist = observed_tags(artifact)
        missed = sorted(t for t in hist if t not in universe)
        print(f"artifact: {artifact} · {len(bodies)} bodies · {len(hist)} distinct tags observed")
        if missed:
            errors.append(
                f"SCAN DRIFT — {len(missed)} tag(s) OBSERVED in the artifact that the static "
                f"scan cannot explain. The producer grew an emission mechanism or a source "
                f"root the map does not read; extend `scan_roots`/`scan_rules` until the scan "
                f"recovers them (this exact test is what found crates/trust-mir-extract):\n    "
                + "\n    ".join(missed))
        unobs = [t for t in hist if family_of(t, spec)[0] is None]
        if unobs:
            notes.append(f"{len(unobs)} of the unmapped tags are LIVE in the artifact "
                         f"(not merely reachable in source)")

    by_fam = collections.Counter(family_of(t, spec)[0] for t in universe)
    print("\nfamily coverage of the source universe:")
    for f in sorted(spec["families"]):
        print(f"  {f:18} {by_fam.get(f, 0):4} tag(s)")
    if by_fam.get(None):
        print(f"  {'(NO FAMILY)':18} {by_fam[None]:4} tag(s)  <-- these fail the check")
    if not by_fam.get("UNCLASSIFIED"):
        errors.append("UNCLASSIFIED is EMPTY. A map that classifies every tag into a lane "
                      "family is asserting that every blocker has an owner, which has never "
                      "been true; the bucket exists so the un-owned ones stay visible.")

    for n in notes:
        print(f"note: {n}")
    if errors:
        print("\nTAG-FAMILY CHECK: FAIL", file=sys.stderr)
        for e in errors:
            print("  * " + e, file=sys.stderr)
        return 1
    print("\nTAG-FAMILY CHECK: OK — every tag the producer can emit has a family, the scan "
          "explains every observed tag, and no map entry is stale.")
    return 0


# --------------------------------------------------------------------------
# the census
# --------------------------------------------------------------------------
def report(spec, artifact, top=8) -> int:
    doc, bodies, hist = observed_tags(artifact)
    p = doc["provenance"]
    dirty = [b for b in bodies if b.get("reasons")]
    print(f"artifact : {artifact}")
    print(f"           trustc {p.get('repo_describe')} · {p.get('date_utc', '')[:19]}")
    print(f"bodies {len(bodies)} · dirty {len(dirty)} · clean {len(bodies) - len(dirty)} "
          f"· distinct tags {len(hist)}")
    print("\nFAMILY CENSUS — 'sole' = every tag in the body belongs to this family, i.e. "
          "clearing\nthe family alone would make the body clean. Sole counts are a lower "
          "bound and do NOT\nsum to the dirty total: a body blocked by two families counts "
          "sole for neither.")

    fam_tags = collections.defaultdict(list)
    unmapped_live = []
    for t in hist:
        f, _ = family_of(t, spec)
        if f is None:
            unmapped_live.append(t)
        else:
            fam_tags[f].append(t)

    rows = []
    for f in spec["families"]:
        tags = set(fam_tags.get(f, []))
        touched = [b for b in dirty if any(t in tags for t in b["reasons"])]
        sole = [b for b in dirty if b["reasons"] and all(t in tags for t in b["reasons"])]
        events = sum(hist[t] for t in tags)
        rows.append((f, len(tags), events, len(touched), len(sole), sole))

    rows.sort(key=lambda r: -r[4])
    print(f"\n  {'family':18} {'tags':>5} {'events':>7} {'touched':>8} {'SOLE':>6}")
    for f, nt, ev, tc, so, _ in rows:
        print(f"  {f:18} {nt:>5} {ev:>7} {tc:>8} {so:>6}")
    multi = len(dirty) - sum(r[4] for r in rows)
    print(f"  {'(multi-family)':18} {'':>5} {'':>7} {'':>8} {multi:>6}   "
          f"bodies no single family can clear")

    print("\nPER-HEAD BREAKDOWN inside each family — this is what makes an alternative "
          "boundary\nrecomputable: move a head, subtract its rows, recount.")
    for f, nt, ev, tc, so, sole_bodies in rows:
        if not nt:
            continue
        heads = collections.Counter()
        for t in fam_tags[f]:
            heads[head_of(t)] += hist[t]
        sole_heads = collections.Counter()
        for b in sole_bodies:
            for h in {head_of(t) for t in b["reasons"]}:
                sole_heads[h] += 1
        print(f"\n  {f} (sole {so}):")
        for h, c in heads.most_common(top):
            print(f"    {h:26} {c:>6} events · appears in {sole_heads.get(h, 0)} sole body/ies")
        if len(heads) > top:
            print(f"    ... +{len(heads) - top} more head(s)")

    print("\nUNCLASSIFIED — printed in full, always. No family and no B-item owns these; "
          "a slice\nhere opens a NEW lane rather than widening one.")
    ut = sorted(fam_tags.get("UNCLASSIFIED", []), key=lambda t: -hist[t])
    for t in ut:
        print(f"    {hist[t]:>6}  {t}")
    if not ut:
        print("    (empty — which the checker treats as a defect in the map, not a clean bill)")

    if unmapped_live:
        print(f"\n!! {len(unmapped_live)} LIVE tag(s) with NO family entry — `--check` fails "
              f"on these:")
        for t in sorted(unmapped_live):
            print(f"    {hist[t]:>6}  {t}")

    # ---- double-counting probes -----------------------------------------
    probes = spec.get("lane_probes", {})
    if probes:
        print("\nDOUBLE-COUNTING PROBES — a candidate lane whose tags all sit inside one "
              "family is\nNOT separately rankable: ranking both counts the same bodies twice.")
        for name, pr in probes.items():
            tags = [t for t in pr["tags"] if t in hist]
            absent = [t for t in pr["tags"] if t not in hist]
            fams = {family_of(t, spec)[0] for t in pr["tags"]}
            sole = [b for b in dirty if b["reasons"] and all(t in set(tags) for t in b["reasons"])]
            events = sum(hist[t] for t in tags)
            print(f"\n  {name}: {len(tags)} of {len(pr['tags'])} tag(s) live, "
                  f"{events} events, sole {len(sole)}")
            print(f"    families spanned: {sorted(f for f in fams if f)}")
            if len(fams) == 1:
                f = fams.pop()
                fsole = next(r[4] for r in rows if r[0] == f)
                print(f"    VERDICT: SUBSET of {f} (family sole {fsole}). Double-counted if "
                      f"both are ranked — strike the probe, or carve its tags OUT of {f} "
                      f"here and re-measure both.")
            else:
                print(f"    VERDICT: spans {len(fams)} families — it is a cross-cutting "
                      f"description, not a lane; rank the families.")
            if absent:
                print(f"    not present in this artifact: {absent}")

    for name, dep in spec.get("pending_dependencies", {}).items():
        print(f"\nPENDING DEPENDENCY — {name}\n  owner: {dep['owner']}\n  "
              f"blocked on: {dep['blocked_on']}\n  would add: {dep['what_it_would_add']}")

    print("\nA sole count is a CLEAN-rate number. The marginal clean->Agreed conversion "
          "measured\nover whole windows is ~1% (0.6% / 2.8% / 0.0%), not the ~59% aggregate "
          "agreed/clean —\nso a family's sole count is NOT its Agreed yield. Price the second "
          "axis with\nscripts/trust_ir_marginal_conversion.py before ranking a lane on it.")
    return 0


def selftest(spec) -> int:
    """Mutation proof that the gate actually fires. A check nobody has watched fail is a
    check nobody knows is wired up — measured in this repo, a pin gate written for exactly
    the bug it was meant to catch had never executed once."""
    import contextlib
    import io

    cases = []

    def run(label, mutate):
        s = json.loads(json.dumps(spec))
        mutate(s)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            rc = check(s)
        cases.append((label, rc != 0))

    run("a producer tag with no family entry",
        lambda s: s["head_rules"].pop("Borrow"))
    run("an entry naming a family that does not exist",
        lambda s: s["head_rules"].__setitem__("Borrow", "NO-SUCH-FAMILY"))
    run("a stale head rule (head the producer never emits)",
        lambda s: s["head_rules"].__setitem__("Nonexistent", "MEMORY"))
    run("a stale override",
        lambda s: s["tag_overrides"].__setitem__("Call(no such tag ever)", "CALL"))
    run("an EMPTY UNCLASSIFIED bucket",
        lambda s: [s["head_rules"].__setitem__(k, "MEMORY")
                   for k, v in list(s["head_rules"].items()) if v == "UNCLASSIFIED"])

    ok = True
    for label, fired in cases:
        print(f"  [{'ok ' if fired else 'BAD'}] {label}: "
              + ("the gate FAILS, as it must" if fired else "the gate is SILENT about it"))
        ok &= fired
    print("TAG-FAMILY SELFTEST: " + ("OK" if ok else "FAIL"),
          file=sys.stdout if ok else sys.stderr)
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="run the gate (default)")
    ap.add_argument("--selftest", action="store_true",
                    help="mutation proof that the gate fails on a broken map (touches nothing "
                         "on disk)")
    ap.add_argument("--report", metavar="DIR", help="census over a postbuild artifact")
    ap.add_argument("--artifact", metavar="DIR",
                    help="with --check: also run the scan-completeness self-test")
    ap.add_argument("--map", default=MAP_PATH)
    ap.add_argument("--top", type=int, default=8)
    ap.add_argument("--move", action="append", default=[], metavar="HEAD=FAMILY",
                    help="re-run the census with a boundary moved (repeatable). This is how "
                         "an alternative partition is MEASURED instead of asserted — the "
                         "107/164/197 pattern-sole spread was three unstated boundaries.")
    args = ap.parse_args()
    spec = load_map(args.map)
    for mv in args.move:
        head, _, fam = mv.partition("=")
        if fam not in spec["families"]:
            ap.error(f"--move {mv}: {fam!r} is not a family in the map")
        spec["head_rules"][head] = fam
        for t in list(spec["tag_overrides"]):
            if head_of(t) == head:
                spec["tag_overrides"][t] = fam
    if args.move:
        print(f"BOUNDARY MOVED for this run only: {', '.join(args.move)}\n")
    if args.selftest:
        return selftest(spec)
    if args.report:
        return report(spec, args.report, args.top)
    return check(spec, args.artifact)


if __name__ == "__main__":
    sys.exit(main())
