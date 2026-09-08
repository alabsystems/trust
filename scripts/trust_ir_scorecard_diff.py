#!/usr/bin/env python3
"""A/B a PRODUCER change over two `trust_ir_producer_scorecard.py` artifacts.

    python3 scripts/trust_ir_scorecard_diff.py <control-dir> <subject-dir>

Each directory is a scorecard `--out-dir` (holding `data.json`). Reports, per body:
became-clean with the tag set it USED to carry, became-dirty with the tag set it NOW
carries, the Agreed delta, and -- ranked ABOVE all of those -- any body that VANISHED.

WHY THIS FILE EXISTS, AND WHY THE VANISHED-BODY BANNER IS AT THE TOP (2026-09-02)
--------------------------------------------------------------------------------
`scripts/trust_ir_rowdiff.py` is THE consolidated comparator for trust-ir coverage
dumps, and it already treats a disappeared body as a HARD class. Its own header
records why: six near-identical scratch comparators disagreed about which fields count
as a difference, and "a finding that is present but unranked is a finding nobody acts
on." It reads a flat `bodies` array, though, and the producer scorecard emits
`corpora.ui_sample.files[].bodies` -- so the producer sweeps used a private scratch
comparator instead, and the consolidation never reached them. This file is that
comparator, brought in-tree, so the next author inherits the ranked banner rather than
a seventh scratch copy.

The defect that forced it: a producer lane reintroduced a rustc query cycle
(`E0391`, building MIR for a nested async closure's by-move body), so
`tests/ui/async-await/async-closures/validate-synthetic-body.rs` stopped compiling and
its eight bodies stopped being emitted. The A/B headline read:

    lowered clean: control 6435/7251 (88.7%) -> subject 6446/7243 (89.0%)   delta +11
    BECAME DIRTY: 0

which is exactly what a good batch looks like. **A body that stops being emitted leaves
BOTH the numerator and the denominator**, so a file that fails to compile can RAISE the
reported percentage: 18 bodies became clean, 7 previously-clean bodies vanished, net
+11, and the denominator moved from 7,251 to 7,243 in a column nobody was reading.
The header line already carried `only-control 8`. Nothing was missing except the habit,
so it now shouts.

READ `only-control` BEFORE THE DELTA. `became-dirty 0` means nothing over a body set
that shrank.
"""
import json, sys, collections

_HASH = __import__("re").compile(r"\[[0-9a-f]{4,}\]")

def key_of(f, b):
    # The def string carries a per-build crate-disambiguator hash (`cr3[432d]::f`),
    # which differs between two builds of the same source and would make every body
    # look new. Strip it so the join is on identity, not on build.
    return (f["file"], _HASH.sub("", b["def"]))

def load(p):
    d = json.load(open(p + "/data.json"))
    out = {}
    for f in d["corpora"]["ui_sample"]["files"]:
        for b in f.get("bodies", []):
            out[key_of(f, b)] = b
    return out, d

def tags(b):
    return tuple(sorted({t for t, _ in (b.get("collect_primary") or [])}))

ctl_p, sub_p = sys.argv[1], sys.argv[2]

# Trust (2026-09-02): a body that stops being EMITTED leaves both the numerator and the
# denominator, so a file that fails to compile can RAISE the reported clean percentage. That
# happened once — a producer lane reintroduced a rustc query cycle, eight bodies vanished, and
# the headline read "+11 clean, BECAME DIRTY: 0". The header line already carried the evidence
# and nothing was missing except the habit of reading it, so this now SHOUTS instead.
def _only_control_banner(only_control):
    if not only_control:
        return
    print()
    print("!" * 78)
    print(f"!! {len(only_control)} BODY(S) VANISHED FROM THE SUBJECT — TREAT AS A COMPILE FAILURE")
    print("!! A vanished body leaves BOTH the numerator and the denominator, so the clean")
    print("!! percentage below is NOT comparable and `became dirty: 0` means nothing.")
    print("!! Compile the named file(s) with the subject driver before reading any delta.")
    for f, d in only_control[:12]:
        print(f"!!   {f}  {d}")
    if len(only_control) > 12:
        print(f"!!   ... and {len(only_control) - 12} more")
    print("!" * 78)
    print()
ctl, dc = load(ctl_p)
sub, ds = load(sub_p)
common = set(ctl) & set(sub)
print(f"control bodies {len(ctl)}  subject bodies {len(sub)}  common {len(common)}"
      f"  only-control {len(set(ctl)-set(sub))}  only-subject {len(set(sub)-set(ctl))}")
_only_control_banner(sorted(set(ctl) - set(sub)))

def clean(b): return b.get("unsupported", 0) == 0
cc = sum(1 for b in ctl.values() if clean(b))
sc = sum(1 for b in sub.values() if clean(b))
print(f"lowered clean: control {cc}/{len(ctl)} ({100*cc/len(ctl):.1f}%) -> "
      f"subject {sc}/{len(sub)} ({100*sc/len(sub):.1f}%)   delta {sc-cc:+d}")

became_clean = collections.Counter()
became_dirty = collections.Counter()
examples = collections.defaultdict(list)
for k in common:
    a, b = ctl[k], sub[k]
    if not clean(a) and clean(b):
        became_clean[tags(a)] += 1
        if len(examples[("C", tags(a))]) < 3: examples[("C", tags(a))].append(k[1])
    elif clean(a) and not clean(b):
        became_dirty[tags(b)] += 1
        if len(examples[("D", tags(b))]) < 3: examples[("D", tags(b))].append(k[1])

ca = sum(1 for b in ctl.values() if b.get("equal"))
sa = sum(1 for b in sub.values() if b.get("equal"))
print(f"Agreed: control {ca} -> subject {sa}   delta {sa-ca:+d}")
print(f"\nBECAME CLEAN: {sum(became_clean.values())}")
for t, n in became_clean.most_common():
    print(f"  {n:5d}  {list(t)}\n           e.g. {examples[('C',t)]}")
print(f"\nBECAME DIRTY: {sum(became_dirty.values())}")
for t, n in became_dirty.most_common():
    print(f"  {n:5d}  {list(t)}\n           e.g. {examples[('D',t)]}")

for name, d in (("control", dc), ("subject", ds)):
    v = d.get("validation") or {}
    print(f"{name} validation: {v if v else d.get('corpora',{}).get('ui_sample',{}).get('validation','-')}")
