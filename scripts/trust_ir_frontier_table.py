#!/usr/bin/env python3
"""trust_ir_frontier_table.py — the trust-ir FRONTIER TABLE, derived from an artifact.

WHY THIS FILE EXISTS (2026-08-20)
---------------------------------
Nothing in the tree enumerated the `note_class` partition, so every lane in the
coverage campaign was working from counts HAND-CARRIED IN PROSE. Re-derivation
against `postbuild-b8-control-03591` found, in one sitting:

    a "27-row" class was 22        a "23-row" class was 16
    a "5-row"  class was 20        a "365 rows" figure matched no sum in the artifact
    two separately-tracked items were THE SAME 5 ROWS seen from two sides
    a 37-row class — larger than most items on the official table — had never
        been ranked at all, because nothing enumerated the classes

`trust_ir_tag_families.py` answers the same question one level down (which
fail-closed TAG belongs to which lane family) and is the CLEAN-rate instrument.
This is its sibling for the level above: which NOTE CLASS a body's verdict fell
into, which is the AGREED-rate instrument. They read the same artifact and are
not substitutes — a tag says why a body is not clean, a note class says why a
CLEAN body has no verdict, and ~99% of realized Agreed gains came from the
second population.

THREE PROPERTIES, EACH LOAD-BEARING
-----------------------------------
  * THE TABLE SUMS. Every row is printed with a residual line, and the sum is
    asserted against the body total. An anonymous catch-all has already cost
    this project a whole unplannable wave (`clean-skip-extern-callee`, 1021 rows
    under one string); a partition that does not visibly sum is how the next one
    hides.
  * THE SELF-CHECK IS AGAINST THE ARTIFACT'S OWN AGGREGATE. Everything printed
    is recomputed from `files[i].bodies[j]`, then cross-checked against the
    `aggregate` block the sweep wrote. A disagreement is an EXTRACTION BUG in
    this script and is reported as such — never as a new number.
  * NOTES ARE SPLIT, NOT SUMMARIZED. A class is not an item; the notes inside it
    are. `clean-skip-other` holds 22 distinct notes and its largest member is
    249 rows. `--class NAME` dumps the witnesses so a lane goes to bodies rather
    than to guesses.

A COUNT HERE IS AN UPPER BOUND ON WHAT FIXING THE CLASS YIELDS
--------------------------------------------------------------
Two independent masking effects, both measured in this campaign:

  * `classify_note` attributes a body to the FIRST rule that matches, and the
    differential's param loop RETURNS AT THE FIRST FAILING PARAM
    (crates/trust-thir-lower/src/differential.rs, the ParamClass loop). A row
    that a fix retires often just surfaces the next blocker in the same body.
  * A clean row is not an Agreed row. Marginal clean->Agreed conversion measured
    over 21 consecutive artifacts is ~1% (scripts/trust_ir_marginal_conversion.py at 4b7ad005d7),
    so a class's row count is a CLEAN-rate quantity. Price the Agreed axis off
    the MODELLED column: OPAQUE-COLLAPSE rows have never once been Agreed in
    this artifact (0 of 118) and SYMBOLIC rows agree at ~15% (64 of 440).

USAGE
-----
    trust_ir_frontier_table.py ARTIFACT [--corpus ui_sample]
    trust_ir_frontier_table.py ARTIFACT --class clean-skip-ptr-pointee-aggregate
    trust_ir_frontier_table.py ARTIFACT --expect bodies=7256 --expect agreed=2850
    trust_ir_frontier_table.py --selftest

ARTIFACT is a `postbuild-*` directory or a `data.json` path. No network, no
build, no subprocess: this reads one JSON file and prints.

Exit: 0 ok · 1 usage/read error · 2 the derived table disagrees with the
artifact's own aggregate, or an `--expect` failed.

Author: Andrew Yates | Copyright 2026 | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys

# The scorecard stores `note[:160]` (trust_ir_producer_scorecard.py, the body record
# builder) while `classify_note` runs on the FULL note. Any structured marker that lands
# past this offset is therefore in the CLASS but not in the artifact's note text, and a
# re-derivation from the stored note silently loses it. Detected and reported, never
# assumed absent.
NOTE_CAP = 160

# `[blockers: ...]` is the B8 step-1 seam-declaration marker
# (crate_module.rs::blocker_summary). Its parser requires the closing bracket, so a
# marker truncated by NOTE_CAP degrades to "no marker" rather than to a partial one.
BLOCKER_OPEN = "[blockers: "
BLOCKERS_RE = re.compile(r"\[blockers: ([^\]]*)\]")

# Lane names, in the order they must be read: a body is priced on the lane it is IN, and
# these three have wildly different historical Agreed rates.
LANES = ("MODELLED", "SYMBOLIC", "OPAQUE", "DIRTY")


def load(artifact: str, corpus: str = "ui_sample"):
    """(doc, corpus_dict, [(file_record, body_record), ...]) from a scorecard artifact."""
    path = artifact if artifact.endswith(".json") else os.path.join(artifact, "data.json")
    with open(path, encoding="utf-8") as fh:
        doc = json.load(fh)
    if corpus not in doc.get("corpora", {}):
        raise SystemExit(
            f"{path}: no corpus {corpus!r}; this artifact carries "
            f"{sorted(doc.get('corpora', {}))}"
        )
    c = doc["corpora"][corpus]
    rows = [(f, b) for f in c["files"] for b in f.get("bodies", [])]
    return doc, c, rows


def lane_of(body) -> str:
    """The pricing lane. Order is load-bearing and mirrors the scorecard's own aggregate:
    a dirty body is not clean; a clean body is SYMBOLIC, else OPAQUE-COLLAPSE, else
    MODELLED. `symbolic`/`opaque_collapse` may be None on an older artifact (the scorecard
    records absent as None, not False, so "not measured" stays distinguishable) — a None
    reads as "not that lane", which is what the aggregate does too."""
    if body.get("unsupported", 0):
        return "DIRTY"
    if body.get("symbolic"):
        return "SYMBOLIC"
    if body.get("opaque_collapse"):
        return "OPAQUE"
    return "MODELLED"


def note_shape(note: str) -> str:
    """A note with its per-body specifics erased, so 14 distinct havoc notes that differ
    only in the offending function name roll up into the ONE actionable item they are.

    Deliberately crude and deliberately deterministic: digits -> `#`, backtick- and
    quote-delimited identifiers -> a placeholder, `bbN` -> `bb#`. It never merges two
    notes with different prose, so a rollup can hide a distinction only by an identifier
    the producer chose to interpolate — and the raw notes are printed underneath anyway.
    """
    s = note
    s = re.sub(r"`[^`]*`", "`~`", s)
    # `offender: fn NAME` / `reachable function NAME` interpolate a body name into
    # otherwise identical prose. Left alone they split ONE item into as many shapes as the
    # corpus has offenders — the `clean-skip-oracle-havoc` class reads as 14 items and is
    # 3. The raw notes are printed underneath every shape, so a merge cannot lose a
    # distinction, only surface one at the right altitude.
    s = re.sub(r"\bfn [A-Za-z0-9_:{}#<>\[\]]*", "fn ~", s)
    s = re.sub(r"\bbb\d+\b", "bb#", s)
    s = re.sub(r"\d+", "#", s)
    return s


def truncation_report(rows):
    """Notes at the storage cap, and structured markers the cap ate. Both are reasons a
    distinct-note split is a LOWER bound on the number of items in a class."""
    at_cap = [b for _, b in rows if len(b.get("note") or "") >= NOTE_CAP]
    lost_marker = [
        b for _, b in rows
        if BLOCKER_OPEN in (b.get("note") or "")
        and not BLOCKERS_RE.search(b.get("note") or "")
    ]
    return at_cap, lost_marker


# --------------------------------------------------------------------------
# the table
# --------------------------------------------------------------------------
def build(rows):
    """The partition, plus the residual. Returns (per_class, residual_rows)."""
    per = collections.OrderedDict()
    residual = []
    tally = collections.defaultdict(lambda: {"rows": [], "lanes": collections.Counter()})
    for f, b in rows:
        cls = b.get("note_class")
        if not isinstance(cls, str) or not cls:
            residual.append((f, b))
            continue
        t = tally[cls]
        t["rows"].append((f, b))
        t["lanes"][lane_of(b)] += 1
    for cls in sorted(tally, key=lambda k: (-len(tally[k]["rows"]), k)):
        per[cls] = tally[cls]
    return per, residual


def crosscheck(doc, corpus, rows, per, residual):
    """Recomputed-vs-embedded. Returns (checks, failures); a failure means THIS SCRIPT is
    wrong, not that the artifact holds a new number."""
    agg = corpus.get("aggregate", {})
    b = agg.get("bodies", {}) or {}
    val = agg.get("validation", {}) or {}
    lanes = collections.Counter(lane_of(x) for _, x in rows)
    clean = [x for _, x in rows if not x.get("unsupported", 0)]
    agreed = [x for _, x in rows if x.get("note_class") == "agreed"]
    files = corpus["files"]
    measured = [f for f in files if isinstance(f.get("validation"), dict)]
    invalid = [f for f in measured if (f["validation"].get("total") or 0) > 0]
    divergences = agg.get("bodies", {}).get("divergences", [])

    derived = {
        "bodies": len(rows),
        "clean": len(clean),
        "modelled": lanes["MODELLED"],
        "symbolic": lanes["SYMBOLIC"],
        "opaque_collapse_clean": lanes["OPAQUE"],
        "agreed": len(agreed),
        "divergences": len([x for _, x in rows if x.get("mode") == "MirOracle"]),
        "modules_measured": len(measured),
        "modules_invalid": len(invalid),
        "note_classes": len(per),
        "class_sum": sum(len(v["rows"]) for v in per.values()) + len(residual),
    }
    embedded = {
        "bodies": b.get("total"),
        "clean": b.get("lowered_clean"),
        "modelled": b.get("lowered_clean_modelled"),
        "symbolic": b.get("lowered_clean_symbolic"),
        "opaque_collapse_clean": b.get("lowered_clean_opaque"),
        "agreed": b.get("agreed"),
        "divergences": len(divergences) if isinstance(divergences, list) else divergences,
        "modules_measured": val.get("modules_measured"),
        "modules_invalid": val.get("modules_invalid"),
        "note_classes": len(b.get("note_class_histogram", {})) or None,
        "class_sum": b.get("total"),
    }
    checks, failures = [], []
    for k, d in derived.items():
        e = embedded.get(k)
        if e is None:
            checks.append((k, d, None, "no embedded counterpart"))
            continue
        ok = d == e
        checks.append((k, d, e, "ok" if ok else "MISMATCH"))
        if not ok:
            failures.append(f"{k}: derived {d} != artifact aggregate {e}")
    # The partition gate. Not a comparison — an identity that must hold by construction.
    if derived["class_sum"] != derived["bodies"]:
        failures.append(
            f"the note_class partition does not sum: "
            f"{derived['class_sum']} classified+residual != {derived['bodies']} bodies"
        )
    return checks, failures


def print_table(doc, corpus, rows, per, residual, args):
    p = doc.get("provenance", {})
    total = len(rows)
    agreed = len(per.get("agreed", {}).get("rows", []))
    non_agreed = total - agreed

    print(f"artifact  : {args.artifact}")
    print(f"            repo_head {p.get('repo_head', '?')}  "
          f"{p.get('repo_describe', '')}  {p.get('date_utc', '')[:19]}")
    print(f"            seed {p.get('seed')} · sample {p.get('sample_size_requested')} "
          f"files · corpus {args.corpus}")
    print()

    checks, failures = crosscheck(doc, corpus, rows, per, residual)
    print("SELF-CHECK — every figure below is RECOMPUTED from files[i].bodies[j] and")
    print("cross-checked against the `aggregate` block the sweep itself wrote. A MISMATCH")
    print("means this script's extraction is wrong; it does not mean a new number.")
    print(f"  {'figure':24} {'derived':>9} {'artifact':>9}   status")
    for k, d, e, st in checks:
        print(f"  {k:24} {d:>9} {'-' if e is None else e:>9}   {st}")
    for want in args.expect:
        key, _, val = want.partition("=")
        got = dict((c[0], c[1]) for c in checks).get(key)
        if got is None:
            failures.append(f"--expect {want}: no such figure (have {[c[0] for c in checks]})")
        elif str(got) != val:
            failures.append(f"--expect {want}: derived {got}")
        else:
            print(f"  expect {key}={val}: ok")
    print()

    at_cap, lost_marker = truncation_report(rows)
    if at_cap or lost_marker:
        print(f"NOTE STORAGE — the scorecard stores note[:{NOTE_CAP}] while `classify_note` "
              f"runs on the\nFULL note, so the split below is a LOWER bound on the number of "
              f"distinct items.")
        print(f"  {len(at_cap)} row(s) carry a note at the {NOTE_CAP}-char cap "
              f"(text beyond it is not in the artifact)")
        if lost_marker:
            print(f"  {len(lost_marker)} row(s) carry a `{BLOCKER_OPEN}` marker the cap "
                  f"TRUNCATED before its closing `]`.")
            print(f"     Its parser requires the bracket, so those rows re-derive as "
                  f"UNMARKED — the marker is\n     in the artifact's note_class but not in "
                  f"its note. Raise the cap or move the marker earlier.")
        print()

    print(f"FRONTIER TABLE — {total} bodies, {non_agreed} of them NOT Agreed.")
    print("Lane columns price the AGREED axis; the row count prices only the CLEAN axis.")
    print("OPAQUE-COLLAPSE rows are the ones that have never been Agreed in this artifact.")
    print()
    w = max([len(c) for c in per] + [22])
    print(f"  {'note_class':{w}} {'rows':>6} {'%all':>6} {'%!agr':>6} "
          f"{'MODELLED':>9} {'SYMB':>6} {'OPAQ':>6} {'DIRTY':>6}")
    for cls, v in per.items():
        n = len(v["rows"])
        share_all = f"{100 * n / total:.1f}"
        share_na = "-" if cls == "agreed" else f"{100 * n / non_agreed:.1f}"
        L = v["lanes"]
        print(f"  {cls:{w}} {n:>6} {share_all:>6} {share_na:>6} "
              f"{L['MODELLED']:>9} {L['SYMBOLIC']:>6} {L['OPAQUE']:>6} {L['DIRTY']:>6}")
    # The residual line is printed ALWAYS, including when it is zero. A partition that
    # only shows its residual when non-empty trains the reader to stop looking for it.
    print(f"  {'(RESIDUAL: no note_class)':{w}} {len(residual):>6}")
    ssum = sum(len(v["rows"]) for v in per.values()) + len(residual)
    print(f"  {'SUM':{w}} {ssum:>6}   "
          + ("== body total, the partition is a partition"
             if ssum == total else f"!= body total {total}  <-- PARTITION BROKEN"))
    if residual:
        print("\n  RESIDUAL WITNESSES (first 20) — a body with no note_class is a scorecard")
        print("  defect, not a class; it must not be absorbed anywhere.")
        for f, b in residual[:20]:
            print(f"    {f['file']}  {b.get('def')}")

    lane_gap(per, rows)

    print("\n" + "=" * 78)
    print("NOTES INSIDE EACH CLASS — this is where a class becomes an item.")
    print("SHAPE rolls up notes that differ only in an interpolated identifier; the raw")
    print("distinct notes are printed underneath it. Both are needed: the shape is the")
    print("item, the raw note is the evidence.")
    for cls, v in per.items():
        if args.only_class and cls != args.only_class:
            continue
        if cls == "agreed" and not args.include_agreed and not args.only_class:
            print(f"\n{'-' * 78}\n{cls}  n={len(v['rows'])}   "
                  f"(verdict class — pass --include-agreed to expand)")
            continue
        notes = collections.Counter(b.get("note") or "" for _, b in v["rows"])
        shapes = collections.Counter()
        shape_notes = collections.defaultdict(collections.Counter)
        for note, ct in notes.items():
            s = note_shape(note)
            shapes[s] += ct
            shape_notes[s][note] += ct
        capped = sum(ct for n, ct in notes.items() if len(n) >= NOTE_CAP)
        print(f"\n{'-' * 78}\n{cls}  n={len(v['rows'])}  "
              f"distinct notes={len(notes)}  shapes={len(shapes)}")
        if capped:
            # A truncated note can split ONE shape into several (the interpolated
            # identifier is cut at a different column each time), and it can also MERGE two
            # shapes whose prose diverges only past the cap. Disclosed per class rather than
            # silently normalized away: which of the two happened is not decidable from the
            # artifact, and guessing is how a class count becomes wrong.
            print(f"  ! {capped} of these rows carry a note at the {NOTE_CAP}-char storage "
                  f"cap. A shape boundary here\n    may be an artifact of truncation rather "
                  f"than of the producer — UNDETERMINED from this file.")
        for s, ct in sorted(shapes.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"  {ct:>6}  SHAPE  {s}")
            raw = sorted(shape_notes[s].items(), key=lambda kv: (-kv[1], kv[0]))
            if len(raw) == 1 and raw[0][0] == s:
                continue
            for note, rc in raw[:args.max_notes]:
                print(f"  {rc:>6}    note  {note}")
            if len(raw) > args.max_notes:
                print(f"  {'':>6}    ... +{len(raw) - args.max_notes} more distinct "
                      f"note(s) in this shape (--max-notes to widen)")

    if failures:
        print("\nFRONTIER TABLE: FAIL", file=sys.stderr)
        for x in failures:
            print("  * " + x, file=sys.stderr)
        return 2
    return 0


def lane_gap(per, rows):
    """The MODELLED->Agreed gap, partitioned. This is the priceable table: it is the only
    population where a re-adjudication has ever converted at a useful rate."""
    mod_total = sum(v["lanes"]["MODELLED"] for v in per.values())
    mod_agreed = per.get("agreed", {}).get("lanes", collections.Counter())["MODELLED"]
    gap = mod_total - mod_agreed
    print(f"\nMODELLED->Agreed GAP: {mod_total} MODELLED, {mod_agreed} Agreed, "
          f"gap {gap}.")
    print("The gap is partitioned by the classes above (MODELLED column, excluding "
          "`agreed`).")
    print("Rank on THIS column, not on `rows`: a class of not-yet-clean bodies converts at")
    print("~1% (measured over 21 artifacts), a class of already-clean MODELLED bodies")
    print("is what ~99% of realized Agreed gains came from.")
    acc = 0
    ranked = sorted(
        ((v["lanes"]["MODELLED"], cls) for cls, v in per.items() if cls != "agreed"),
        key=lambda kv: (-kv[0], kv[1]),
    )
    for m, cls in ranked:
        if not m:
            continue
        acc += m
        print(f"    {m:>6}  {100 * m / gap:>5.1f}%  {cls}")
    print(f"    {acc:>6}         SUM   "
          + ("== gap" if acc == gap else f"!= gap {gap}  <-- BROKEN"))


def dump_class(rows, per, cls, args):
    if cls not in per:
        print(f"no such note_class {cls!r} in this artifact. Present:", file=sys.stderr)
        for k, v in per.items():
            print(f"    {len(v['rows']):>6}  {k}", file=sys.stderr)
        return 1
    v = per[cls]
    print(f"{cls}  n={len(v['rows'])}  lanes={dict(v['lanes'])}")
    print("Witnesses, sorted by (file, def) — deterministic, so two runs diff cleanly.")
    print(f"  {'lane':9} {'kind':9} {'file':62} def")
    for f, b in sorted(v["rows"], key=lambda x: (x[0]["file"], x[1].get("def") or "")):
        print(f"  {lane_of(b):9} {(b.get('kind') or '?'):9} {f['file']:62} {b.get('def')}")
        if args.with_notes:
            print(f"  {'':9} {'':9} note: {b.get('note')}")
    files = sorted({f["file"] for f, _ in v["rows"]})
    print(f"\n{len(files)} distinct file(s).")
    return 0


def emit_json(doc, corpus, rows, per, residual, out):
    p = doc.get("provenance", {})
    payload = {
        "schema": "trust.trust-ir.frontier-table.v1",
        "source": {
            "repo_head": p.get("repo_head"),
            "repo_describe": p.get("repo_describe"),
            "date_utc": p.get("date_utc"),
            "seed": p.get("seed"),
        },
        "bodies": len(rows),
        "agreed": len(per.get("agreed", {}).get("rows", [])),
        "residual": len(residual),
        "classes": [
            {
                "note_class": cls,
                "rows": len(v["rows"]),
                "lanes": {k: v["lanes"][k] for k in LANES},
                "notes": [
                    {"count": ct, "note": n}
                    for n, ct in sorted(
                        collections.Counter(b.get("note") or "" for _, b in v["rows"]).items(),
                        key=lambda kv: (-kv[1], kv[0]),
                    )
                ],
            }
            for cls, v in per.items()
        ],
    }
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=1, sort_keys=False)
        fh.write("\n")
    print(f"\nwrote {out}")


def selftest() -> int:
    """Mutation proof that the two gates FIRE. A partition gate nobody has watched fail is
    a gate nobody knows is wired up — measured in this repo, a pin gate written for exactly
    the bug it was meant to catch had never executed once."""
    import contextlib
    import io

    def artifact(bodies, agg_overrides=None):
        agg = {
            "validation": {"modules_measured": 1, "modules_invalid": 0},
            "bodies": {
                "total": len(bodies),
                "lowered_clean": sum(1 for b in bodies if not b.get("unsupported")),
                "lowered_clean_modelled": sum(1 for b in bodies if lane_of(b) == "MODELLED"),
                "lowered_clean_symbolic": sum(1 for b in bodies if lane_of(b) == "SYMBOLIC"),
                "lowered_clean_opaque": sum(1 for b in bodies if lane_of(b) == "OPAQUE"),
                "agreed": sum(1 for b in bodies if b.get("note_class") == "agreed"),
                "divergences": [],
                "note_class_histogram": dict(
                    collections.Counter(b.get("note_class") for b in bodies)),
            },
        }
        agg["bodies"].update(agg_overrides or {})
        return {
            "provenance": {},
            "corpora": {"ui_sample": {
                "aggregate": agg,
                "files": [{"file": "t.rs", "validation": {"total": 0, "classes": {}},
                           "bodies": bodies}],
            }},
        }

    base = [
        {"def": "a", "kind": "named", "unsupported": 0, "symbolic": False,
         "opaque_collapse": False, "mode": "Agreed", "note_class": "agreed", "note": "eq"},
        {"def": "b", "kind": "named", "unsupported": 0, "symbolic": False,
         "opaque_collapse": False, "mode": "NotRun", "note_class": "clean-skip-x",
         "note": "skip"},
    ]

    cases = []

    def run(label, bodies, agg_overrides=None):
        doc = artifact(bodies, agg_overrides)
        c = doc["corpora"]["ui_sample"]
        rows = [(f, b) for f in c["files"] for b in f["bodies"]]
        per, residual = build(rows)
        _, failures = crosscheck(doc, c, rows, per, residual)
        cases.append((label, bool(failures)))

    run("a body with NO note_class lands in the residual, not in a neighbour",
        base + [{"def": "c", "kind": "named", "unsupported": 0, "symbolic": False,
                 "opaque_collapse": False, "mode": "NotRun", "note": "?"}],
        # The aggregate still claims 3 bodies in 2 classes -> the histogram-length check
        # and the class-sum identity are what must catch the unclassified row.
        {"note_class_histogram": {"agreed": 1, "clean-skip-x": 1, "ghost": 1}})
    run("the artifact's own aggregate disagreeing with the rows (a stale total)",
        base, {"total": 99})
    run("a lane figure disagreeing (SYMBOLIC miscounted)",
        base, {"lowered_clean_symbolic": 7})
    run("an agreed count disagreeing",
        base, {"agreed": 42})

    # And the negative control: the gate must be SILENT on a coherent artifact, or every
    # positive above is meaningless.
    doc = artifact(base)
    c = doc["corpora"]["ui_sample"]
    rows = [(f, b) for f in c["files"] for b in f["bodies"]]
    per, residual = build(rows)
    _, failures = crosscheck(doc, c, rows, per, residual)
    cases.append(("NEGATIVE CONTROL: a coherent artifact passes", not failures))

    with contextlib.redirect_stdout(io.StringIO()):
        pass
    ok = True
    for label, fired in cases:
        print(f"  [{'ok ' if fired else 'BAD'}] {label}")
        ok &= fired
    print("FRONTIER-TABLE SELFTEST: " + ("OK" if ok else "FAIL"),
          file=sys.stdout if ok else sys.stderr)
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("artifact", nargs="?",
                    help="a postbuild-* directory or a data.json path")
    ap.add_argument("--corpus", default="ui_sample")
    ap.add_argument("--class", dest="only_class", metavar="NAME",
                    help="dump the body identifiers and source files for one class")
    ap.add_argument("--with-notes", action="store_true",
                    help="with --class: print each witness's note")
    ap.add_argument("--include-agreed", action="store_true",
                    help="expand the `agreed` verdict class in the note breakdown")
    ap.add_argument("--max-notes", type=int, default=12, metavar="N",
                    help="cap raw notes printed per shape (tail count always disclosed)")
    ap.add_argument("--expect", action="append", default=[], metavar="FIGURE=VALUE",
                    help="pin a known-good control figure; repeatable. Fails the run "
                         "rather than printing a number that disagrees with it.")
    ap.add_argument("--json", metavar="OUT", help="also write the table as JSON")
    ap.add_argument("--selftest", action="store_true",
                    help="mutation proof that the gates fire (touches nothing on disk)")
    args = ap.parse_args()

    if args.selftest:
        return selftest()
    if not args.artifact:
        ap.error("ARTIFACT is required (or use --selftest)")

    try:
        doc, corpus, rows = load(args.artifact, args.corpus)
    except OSError as e:
        print(f"cannot read artifact: {e}", file=sys.stderr)
        return 1

    per, residual = build(rows)

    if args.only_class and not args.include_agreed and args.json is None \
            and not args.expect:
        return dump_class(rows, per, args.only_class, args)

    rc = print_table(doc, corpus, rows, per, residual, args)
    if args.json:
        emit_json(doc, corpus, rows, per, residual, args.json)
    return rc


if __name__ == "__main__":
    sys.exit(main())
