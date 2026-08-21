#!/usr/bin/env python3
"""MARGINAL clean->Agreed conversion between two trust-ir producer scorecard artifacts.

WHY THIS FILE EXISTS (2026-08-19)
---------------------------------
Every coverage lane in the trust-ir campaign was priced against the AGGREGATE
ratio printed on the scorecard: `agreed / lowered_clean`, ~59% at the time of
writing. That ratio answers "what fraction of the clean population happens to be
Agreed today". It was read as "what fraction of the bodies my slice makes clean
will become Agreed" — a different question, and the two numbers are two orders of
magnitude apart.

Measured retrospectively over 21 consecutive artifacts at a stable 7256-body
sample (`postbuild-waveUD` 2026-08-18 -> `postbuild-slice20-control`):

    window                            newly clean+MODELLED   of those Agreed   rate
    postbuild-p171b       -> control          176                   1          0.6%
    postbuild-2026-08-10-green -> control       36                   1          2.8%
    postbuild-waveRD      -> control           12                   0          0.0%

~1%, not 59%. And of the newly-Agreed rows in each of those windows, ~99% were
ALREADY CLEAN in the baseline: Agreed comes from RE-ADJUDICATING already-clean
bodies (oracle/comparator/differential work), essentially never from making new
bodies clean (producer coverage work). Two different lanes, two different yields,
one number was being used to price both.

That is the number this tool exists to keep in front of whoever ranks the next
slice. It is deliberately a separate tool from the scorecard: the scorecard
measures ONE artifact, this measures the DELTA between two, and the delta is
where the decision-relevant quantity lives.

RELATION TO `trust_ir_rowdiff.py`
---------------------------------
`trust_ir_rowdiff.py` is the row-exact regression comparator over per-crate
`*.coverage.json` DUMPS (`def_path`/`instr_count`/`spliced`/`lineage`); it exists
to make a silent loss impossible. This tool compares two `postbuild-*/data.json`
SCORECARD artifacts (the seeded `tests/ui` sample) and answers one economic
question: what did the last N slices buy, per newly-clean body. They read
different files and are not substitutes.

SAMPLE IDENTITY IS A FAIL-CLOSED PRECONDITION
---------------------------------------------
The seeded `ui_sample` is NOT stable across a `tests/ui` change: the eligible
pool moves and the seed then selects a different 2000 files. Diffing two
artifacts drawn from different samples silently mixes "this body changed class"
with "this body was not in the other sample at all". So: the sampled file sets
must be IDENTICAL or the run aborts. `--intersect` opts explicitly into the
common-file-set comparison and prints exactly how many files and bodies that
dropped — a disclosed restriction, never a silent one.

USAGE
-----
    trust_ir_marginal_conversion.py BASELINE SUBJECT [--intersect] [--json OUT]

BASELINE/SUBJECT may each be a `postbuild-*` directory or a `data.json` path.

Exit codes: 0 measured · 2 sample mismatch (rerun with --intersect) · 1 usage.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys

# `def` carries a per-crate disambiguator that changes with the compiler
# generation and with unrelated crate content: `foo[f5b3]::bar`. It is not part
# of the body's identity, and leaving it in makes every body look new.
HASH = re.compile(r"\[[0-9a-f]{4,16}\]")

CORPUS_DEFAULT = "ui_sample"


def strip_hash(defname: str) -> str:
    return HASH.sub("", defname)


def load(path: str, corpus: str):
    """Return (provenance, sample_meta, {key: body}, dup_count, file_set)."""
    if os.path.isdir(path):
        path = os.path.join(path, "data.json")
    with open(path) as fh:
        doc = json.load(fh)
    if corpus not in doc.get("corpora", {}):
        sys.exit(f"{path}: no corpus {corpus!r} (have {list(doc.get('corpora', {}))})")
    c = doc["corpora"][corpus]
    rows, dups = {}, 0
    seen = collections.Counter()
    files = set()
    for f in c["files"]:
        files.add(f["file"])
        for b in f.get("bodies", []):
            base = (f["file"], strip_hash(b["def"]))
            # Two bodies in one file can collide after stripping (a generic
            # instantiated twice, a macro expansion). Disambiguate positionally
            # and count it, rather than dropping one silently.
            n = seen[base]
            seen[base] += 1
            if n:
                dups += 1
            rows[(*base, n)] = b
    return doc["provenance"], c.get("sample_meta", {}), rows, dups, files


def cls(b) -> str:
    """MODELLED / SYMBOLIC / OPAQUE / UNMEASURED, for a CLEAN body only.

    Mirrors `trust_ir_producer_scorecard.py:body_stats` exactly, including its
    most-dishonest-wins precedence (symbolic before opaque_collapse), so the
    per-body classification here can never disagree with the artifact's own
    aggregate lines.
    """
    if b.get("symbolic") is None:
        return "UNMEASURED"
    if b.get("symbolic") is True:
        return "SYMBOLIC"
    if b.get("opaque_collapse") is True:
        return "OPAQUE"
    return "MODELLED"


def is_clean(b) -> bool:
    return b["unsupported"] == 0


def is_agreed(b) -> bool:
    return b["mode"] == "Agreed"


def pct(n, d):
    return f"{100.0 * n / d:.1f}%" if d else "n/a"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("baseline")
    ap.add_argument("subject")
    ap.add_argument("--corpus", default=CORPUS_DEFAULT)
    ap.add_argument("--intersect", action="store_true",
                    help="compare over the COMMON sampled files when the two samples "
                         "differ; the restriction is printed, never silent")
    ap.add_argument("--json", metavar="PATH", help="write the full measurement")
    ap.add_argument("--list", type=int, default=0, metavar="N",
                    help="print up to N example defs per set")
    args = ap.parse_args()

    bp, bmeta, base, bdup, bfiles = load(args.baseline, args.corpus)
    sp, smeta, subj, sdup, sfiles = load(args.subject, args.corpus)

    print(f"baseline: {args.baseline}")
    print(f"          trustc {bp.get('repo_describe')} · {bp.get('date_utc', '')[:19]}")
    print(f"subject : {args.subject}")
    print(f"          trustc {sp.get('repo_describe')} · {sp.get('date_utc', '')[:19]}")

    # ---- sample identity, fail-closed ------------------------------------
    restricted = False
    if bfiles != sfiles:
        only_b, only_s = bfiles - sfiles, sfiles - bfiles
        msg = (f"SAMPLE MISMATCH: {len(only_b)} file(s) only in baseline, "
               f"{len(only_s)} only in subject "
               f"(eligible pool {bmeta.get('eligible')} -> {smeta.get('eligible')}). "
               f"The seeded ui_sample is not stable across a tests/ui change.")
        if not args.intersect:
            print(msg, file=sys.stderr)
            print("Refusing to diff: rerun with --intersect to compare the common "
                  "file set with the restriction disclosed.", file=sys.stderr)
            return 2
        common = bfiles & sfiles
        drop_b = sum(1 for k in base if k[0] not in common)
        drop_s = sum(1 for k in subj if k[0] not in common)
        base = {k: v for k, v in base.items() if k[0] in common}
        subj = {k: v for k, v in subj.items() if k[0] in common}
        restricted = True
        print()
        print("!! " + msg)
        print(f"!! --intersect: restricted to {len(common)} common file(s); "
              f"dropped {drop_b} baseline body/ies and {drop_s} subject body/ies.")
    if bmeta.get("seed") != smeta.get("seed"):
        print(f"!! seeds differ ({bmeta.get('seed')} vs {smeta.get('seed')}) — "
              f"the samples are unrelated populations.", file=sys.stderr)
        return 2
    if bdup or sdup:
        print(f"note: hash-stripped def collisions disambiguated positionally "
              f"(baseline {bdup}, subject {sdup})")

    matched = base.keys() & subj.keys()
    only_base = base.keys() - subj.keys()
    only_subj = subj.keys() - base.keys()

    def pop(rows):
        clean = [b for b in rows.values() if is_clean(b)]
        by = collections.Counter(cls(b) for b in clean)
        return {
            "bodies": len(rows),
            "clean": len(clean),
            "MODELLED": by["MODELLED"], "SYMBOLIC": by["SYMBOLIC"],
            "OPAQUE": by["OPAQUE"], "UNMEASURED": by["UNMEASURED"],
            "agreed": sum(1 for b in rows.values() if is_agreed(b)),
        }

    pb, ps = pop(base), pop(subj)
    print()
    print("POPULATION (whole artifact, after any --intersect restriction)")
    print(f"  {'':12} {'baseline':>9} {'subject':>9} {'delta':>7}")
    for k in ("bodies", "clean", "MODELLED", "SYMBOLIC", "OPAQUE", "UNMEASURED", "agreed"):
        print(f"  {k:12} {pb[k]:>9} {ps[k]:>9} {ps[k] - pb[k]:>+7}")
    print(f"  matched bodies {len(matched)} · baseline-only {len(only_base)} "
          f"· subject-only {len(only_subj)}")
    print("  (baseline-only/subject-only rows are NOT conversions — a body that "
          "appears or disappears\n   changed file outcome or identity, and is "
          "excluded from every rate below.)")

    # ---- the set differences, over MATCHED bodies only -------------------
    newly_clean = [k for k in matched if is_clean(subj[k]) and not is_clean(base[k])]
    lost_clean = [k for k in matched if is_clean(base[k]) and not is_clean(subj[k])]
    newly_agreed = [k for k in matched if is_agreed(subj[k]) and not is_agreed(base[k])]
    lost_agreed = [k for k in matched if is_agreed(base[k]) and not is_agreed(subj[k])]

    nc_by_cls = collections.Counter(cls(subj[k]) for k in newly_clean)
    nc_modelled = [k for k in newly_clean if cls(subj[k]) == "MODELLED"]

    print()
    print("NEWLY CLEAN (dirty in baseline, clean in subject) — the producer-coverage lane")
    print(f"  newly clean          {len(newly_clean)}   "
          f"(lost clean {len(lost_clean)}, net {len(newly_clean) - len(lost_clean):+d})")
    for c in ("MODELLED", "SYMBOLIC", "OPAQUE", "UNMEASURED"):
        print(f"    of which {c:11} {nc_by_cls[c]}")
    print("  SYMBOLIC/OPAQUE newly-clean rows are clean bought by OPACITY, not by "
          "modelling;\n  the goal statement excludes them from progress.")

    print()
    print("MARGINAL CONVERSION — of the newly clean+MODELLED, how many are Agreed")
    nm_agreed = [k for k in nc_modelled if is_agreed(subj[k])]
    print(f"  newly clean+MODELLED {len(nc_modelled)}")
    print(f"  of those Agreed      {len(nm_agreed)}")
    print(f"  MARGINAL RATE        {pct(len(nm_agreed), len(nc_modelled))}   "
          f"<-- price a coverage slice against THIS")
    nc_agreed_any = [k for k in newly_clean if is_agreed(subj[k])]
    print(f"  (any newly-clean class: {len(nc_agreed_any)} of {len(newly_clean)} "
          f"= {pct(len(nc_agreed_any), len(newly_clean))})")
    agg = pct(ps["agreed"], ps["clean"])
    print(f"  aggregate ratio in the subject artifact: agreed/clean = "
          f"{ps['agreed']}/{ps['clean']} = {agg}")
    print("  The aggregate is a STOCK, the marginal rate is a FLOW. Ranking a slice "
          "by the stock\n  over-prices it by whatever the gap is.")

    # ---- where does Agreed actually come from ----------------------------
    was_clean = [k for k in newly_agreed if is_clean(base[k])]
    was_dirty = [k for k in newly_agreed if not is_clean(base[k])]
    print()
    print("WHERE NEWLY-AGREED COMES FROM (the attribution that reprices the campaign)")
    print(f"  newly Agreed             {len(newly_agreed)}   "
          f"(lost Agreed {len(lost_agreed)}, net {len(newly_agreed) - len(lost_agreed):+d})")
    print(f"    ALREADY CLEAN in baseline {len(was_clean):>5}  "
          f"({pct(len(was_clean), len(newly_agreed))}) — re-adjudication lane "
          f"(oracle/comparator/differential)")
    print(f"    newly clean               {len(was_dirty):>5}  "
          f"({pct(len(was_dirty), len(newly_agreed))}) — producer-coverage lane")

    if args.list:
        def show(title, keys):
            print(f"\n  {title} ({len(keys)}):")
            for k in sorted(keys)[: args.list]:
                print(f"    {k[1]}   [{k[0]}]")
            if len(keys) > args.list:
                print(f"    ... +{len(keys) - args.list} more")
        show("newly clean+MODELLED", nc_modelled)
        show("newly clean+MODELLED and Agreed", nm_agreed)
        show("newly Agreed, was already clean", was_clean)

    if args.json:
        out = {
            "schema": "trust.trust-ir.marginal-conversion.v1",
            "baseline": {"path": args.baseline, "provenance": bp,
                         "sample_meta": bmeta, "population": pb},
            "subject": {"path": args.subject, "provenance": sp,
                        "sample_meta": smeta, "population": ps},
            "restricted_to_common_files": restricted,
            "matched": len(matched), "baseline_only": len(only_base),
            "subject_only": len(only_subj),
            "newly_clean": len(newly_clean),
            "newly_clean_by_class": dict(nc_by_cls),
            "lost_clean": len(lost_clean),
            "newly_clean_modelled": len(nc_modelled),
            "newly_clean_modelled_agreed": len(nm_agreed),
            "marginal_rate": (len(nm_agreed) / len(nc_modelled)) if nc_modelled else None,
            "newly_agreed": len(newly_agreed),
            "lost_agreed": len(lost_agreed),
            "newly_agreed_was_already_clean": len(was_clean),
            "newly_agreed_was_newly_clean": len(was_dirty),
            "aggregate_agreed_over_clean": (ps["agreed"] / ps["clean"]) if ps["clean"] else None,
            "defs": {
                "newly_clean_modelled": sorted(k[1] for k in nc_modelled),
                "newly_clean_modelled_agreed": sorted(k[1] for k in nm_agreed),
                "newly_agreed_was_already_clean": sorted(k[1] for k in was_clean),
            },
        }
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1)
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
