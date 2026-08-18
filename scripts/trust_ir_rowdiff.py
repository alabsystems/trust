#!/usr/bin/env python3
"""ROW-EXACT control/subject differential over trust-ir coverage dumps + flip logs.

THE ONE comparator. Before this file there were six near-identical copies in
per-lane scratchpads (laneP/rowexact.py, mfclose/rowexact.py, mfzero/rowexact.py,
rvmf/rowexact2.py, rmfz/wcdiff.py, wave-tr-ledger/covdiff.py) and four byte-identical
copies of fliplog.py. They disagreed about which fields count as a difference, and the
union of what they watched still left `spliced`, `instr_count` and `lineage` unwatched
by every one of them.

WHY THIS FILE EXISTS — the defect it was built to make impossible (2026-08-13)
------------------------------------------------------------------------------
Three compiler-synthesized `#[derive(Clone)]` bodies in `clean-kernel` stopped
lowering across a Trust compiler generation:

    <env::algebra_rat_quotient::SumTree as Clone>::clone              20 instrs -> 1
    <env::inductive_no_confusion::NoConfusionCandidate as Clone>::clone  35 -> 1
    <env::inductive_no_confusion_hetero::EqTelescopeGroup as Clone>::clone 20 -> 1

Four consecutive merge reviews certified "0 lost, 0 new mismatch" and were, on their
own terms, correct. All three bodies sit in the derived-MIR `unsupported` bucket in
BOTH generations, so every published `agreed / unsupported / mismatch` table read
`1540/12228/1 -> 1541/12228/0` and showed nothing. The axis that moved --
`lowered`, `spliced`, `instr_count`, `lineage` -- was not a column.

Two of the six comparators did store `lowered` in the row, and the `unsupported` set
did move, so the rows were not literally absent from their moved-row lists. That is
worse, not better: the rows were printed with no verdict, no class and no count,
indistinguishable from benign churn, while every summary line in the same report said
"0 lost". A finding that is present but unranked is a finding nobody acts on.

So this tool does three things the copies did not:

  1. `lowered`, `spliced`, `instr_count`, `lineage`, `symbolic`, `func_id`, `kind`,
     `calls`, `seam`, `deferred_to_seam`, `unsupported_details`, `collect_*` and the
     UNTRUNCATED `markers_detail` are FIRST-CLASS compared axes, per body.
  2. Every count is a SET DIFFERENCE over per-body keys, reported as LOST and GAINED
     SEPARATELY. A simultaneous loss and gain never cancels. Net deltas are printed
     only beside the set truth, never alone.
  3. A body collapsing to a stub is its own named, counted, headlined regression class
     (STUB COLLAPSE), not a row buried in an unclassified list.
  4. `markers_lines` counts the marker lines the comparison ACTUALLY compared, because
     `markers_exact: true` is two claims wearing one name: agreement over a real marker
     sequence, and agreement over two EMPTY ones. Measured 2026-08-13, only 27 of 1,082
     `markers_exact` rows were non-vacuous (105 marker lines in total) and 182 of 209
     flip events passed a marker gate comparing two empty sequences. A body whose
     marker evidence evaporates while the boolean stays `true` is its own named HARD
     class (MARKER CLAIM WENT VACUOUS) -- the same split, for the same reason, as
     `refused` vs `ADMITTED-WRONG`.

`--legacy-tuple` re-runs the old comparators' tuple on the same inputs and prints what
they would have said, so the burial is quantified in the same run instead of argued.

USAGE
-----
    trust_ir_rowdiff.py rows  <control.coverage.json> <subject.coverage.json>
    trust_ir_rowdiff.py tree  <control-dump-dir>      <subject-dump-dir> [--crate NAME]
    trust_ir_rowdiff.py flips <control.flip.txt>      <subject.flip.txt>

    --json PATH        write the full machine-readable differential
    --max-rows N       cap printed rows per class (default 40; 0 = unlimited)
    --legacy-tuple     also report what the pre-consolidation comparators saw
    --fail-on CLASS    regression (default, HARD classes) | soft | any | never

Classes are tiered. HARD is coverage that is GONE -- a body that no longer lowers,
no longer splices, no longer agrees, or has left the dump. SOFT is a body that is
still lowered and spliced but measures smaller. Both are always printed and counted;
the tier decides only what turns the exit code red, so a gate that must stay
meaningful does not cry wolf over a leaner but complete lowering.

EXIT: 0 clean, 1 regressions found, 2 usage/IO error.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import argparse
import collections
import glob
import json
import os
import re
import sys

# ---------------------------------------------------------------------------
# THE AXES.
#
# `direction` is what a REGRESSION looks like on that axis, and it is the whole
# point of the table: an axis with no direction is an axis whose movement nobody
# ever gets paged about.
#
#   down     numeric decrease is a regression
#   up       numeric increase is a regression
#   lost     true -> false is a regression
#   gone     non-empty -> empty is a regression
#   watch    any change is reported, no verdict attached
# ---------------------------------------------------------------------------
Axis = collections.namedtuple("Axis", "name direction note")

AXES = (
    Axis("lowered", "lost", "THIR->trust-ir produced a body at all"),
    Axis("spliced", "lost", "the lowered body was spliced into the module"),
    Axis("symbolic", "watch", "body is symbolic rather than concrete"),
    Axis("instr_count", "down", "trust-ir instructions in the body"),
    Axis("lineage", "gone", "content digest of the lowered body"),
    Axis("func_id", "gone", "slot the body occupies in the module"),
    Axis("kind", "watch", "fn / const-init / declaration / ..."),
    Axis("unsupported", "watch", "rejected THIR shapes, name -> count"),
    Axis("unsupported_details", "watch", "source spans of the rejections"),
    Axis("collect_primary", "watch", "primary collection rejections"),
    Axis("collect_cascade", "watch", "cascaded collection rejections"),
    Axis("calls_resolved", "down", "callees resolved to a local body"),
    Axis("calls_extern", "watch", "callees that are declaration-only"),
    Axis("calls_unresolved", "up", "callees not resolved at all"),
    Axis("dm_verdict", "watch", "derived-MIR differential verdict"),
    Axis("dm_detail", "watch", "derived-MIR differential detail"),
    Axis("markers_exact", "lost", "lifetime-marker sequence matched exactly"),
    Axis("markers_detail", "watch", "the marker comparison, UNTRUNCATED"),
    Axis("markers_lines", "down", "marker lines ACTUALLY compared (0 == vacuous)"),
    Axis("markers_class", "watch", "right / refused / ADMITTED-WRONG / no-derived-body"),
    Axis("interp_verdict", "watch", "interpreter differential verdict"),
    Axis("interp_samples", "down", "interpreter samples actually run"),
    Axis("interp_detail", "watch", "why the interpreter did or did not run"),
    Axis("deferred_to_seam", "watch", "body handed to the crate seam"),
    Axis("seam_state", "watch", "seam resolution state"),
    Axis("seam_verdict", "watch", "seam differential verdict"),
    Axis("seam_detail", "watch", "why the seam did or did not assert"),
)
AXIS_NAMES = tuple(a.name for a in AXES)
AXIS_BY_NAME = {a.name: a for a in AXES}

# What the six pre-consolidation comparators joined on. Kept verbatim so
# `--legacy-tuple` is a measurement of the old instrument, not a paraphrase.
LEGACY_TUPLES = {
    "laneP/rowexact.py, mfclose/rowexact.py":
        ("dm_verdict", "markers_exact", "interp_verdict", "unsupported"),
    "mfzero/rowexact.py, rvmf/rowexact2.py":
        ("dm_verdict", "markers_exact", "interp_verdict", "unsupported", "lowered",
         "markers_detail"),
    "rmfz/wcdiff.py":
        ("dm_verdict", "markers_exact", "markers_detail", "interp_verdict",
         "unsupported", "lowered"),
    "wave-tr-ledger/covdiff.py":
        ("dm_verdict", "markers_exact"),
}

# build-script crates carry a per-build hash in the dump filename
HASHED = re.compile(r"_[0-9a-f]{16}_\d+$")


class RowDiffError(Exception):
    """Usage or input error. Never raised for a regression -- that is a verdict."""


# ---------------------------------------------------------------------------
# loading
# ---------------------------------------------------------------------------
def _pairs(v):
    """Normalise `[[name, count], ...]` to a sorted tuple. Tolerates a bare list."""
    if not v:
        return ()
    out = []
    for e in v:
        if isinstance(e, (list, tuple)) and len(e) == 2:
            out.append((str(e[0]), e[1]))
        else:
            out.append((str(e), 1))
    return tuple(sorted(out))


def _details(v):
    if not isinstance(v, dict):
        return ()
    return tuple(sorted((str(k), tuple(str(x) for x in (vv or []))) for k, vv in v.items()))


MARKER_LINES = re.compile(r"^(\d+) marker line\(s\) identical$")


def marker_lines(dm):
    """How many marker lines the comparison ACTUALLY compared.

    `markers_exact: true` is two different claims wearing one name: agreement over
    a real marker sequence, and agreement over two EMPTY sequences. Matching
    emptiness is honest -- it is not a bug and not the gate malfunctioning -- but it
    carries no fidelity content, and no boolean on this row distinguishes the two.
    Returns None when the count is not stated (e.g. `marker channel(...)` skips).
    """
    m = MARKER_LINES.match(dm.get("markers_detail") or "")
    return int(m.group(1)) if m else None


def classify_markers(dm):
    """Port of `rmfz/wcdiff.py`'s classifier -- kept because consolidation must not
    quietly drop a capability one copy had.

    The distinction it draws is the one that matters for trust: a body that REFUSED
    to emit derived markers is honest about knowing nothing, whereas a body that
    emitted a marker sequence which disagrees is ADMITTED-AND-WRONG. Both carry
    `markers_exact == false`, so no boolean can tell them apart.
    """
    detail = dm.get("markers_detail") or ""
    if dm.get("markers_exact") is True:
        # Split the "right" bucket the same way `refused` was split out of
        # `ADMITTED-WRONG`: two states, one name, no boolean between them.
        return "right-vacuous" if marker_lines(dm) == 0 else "right"
    if detail == "" or detail.startswith("marker channel("):
        return "no-derived-body"
    if not detail.startswith("markers differ: "):
        return "UNKNOWN-DETAIL"
    rest = detail[len("markers differ: "):]
    if rest.startswith("line 0: ") and rest.endswith("vs derived `<end>`"):
        return "refused"
    return "ADMITTED-WRONG"


def row_of(body):
    """Project one coverage body onto every axis. No truncation anywhere."""
    diffs = body.get("differentials") or {}
    dm = diffs.get("derived_mir") or {}
    interp = diffs.get("interpreter") or {}
    seam = diffs.get("seam") or {}
    calls = body.get("calls") or {}
    return {
        "lowered": body.get("lowered"),
        "spliced": body.get("spliced"),
        "symbolic": body.get("symbolic"),
        "instr_count": body.get("instr_count"),
        "lineage": body.get("lineage") or "",
        "func_id": body.get("func_id"),
        "kind": body.get("kind"),
        "unsupported": _pairs(body.get("unsupported")),
        "unsupported_details": _details(body.get("unsupported_details")),
        "collect_primary": _pairs(body.get("collect_primary")),
        "collect_cascade": _pairs(body.get("collect_cascade")),
        "calls_resolved": calls.get("resolved"),
        "calls_extern": calls.get("extern_decls"),
        "calls_unresolved": calls.get("unresolved"),
        "dm_verdict": dm.get("verdict", "none"),
        "dm_detail": dm.get("detail") or "",
        "markers_exact": bool(dm.get("markers_exact")),
        "markers_detail": dm.get("markers_detail") or "",
        "markers_lines": marker_lines(dm),
        "markers_class": classify_markers(dm),
        "interp_verdict": interp.get("verdict", "none"),
        "interp_samples": interp.get("samples"),
        "interp_detail": interp.get("detail") or "",
        "deferred_to_seam": bool(diffs.get("deferred_to_seam")),
        "seam_state": seam.get("state", "none"),
        "seam_verdict": seam.get("verdict", "none"),
        "seam_detail": seam.get("detail") or "",
    }


def load_file(path, crate_label=None):
    try:
        with open(path) as fh:
            doc = json.load(fh)
    except FileNotFoundError as exc:
        raise RowDiffError(f"no such coverage file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise RowDiffError(f"{path}: not valid JSON ({exc})") from exc
    if "bodies" not in doc:
        raise RowDiffError(f"{path}: no `bodies` array -- not a trust-ir coverage dump")
    crate = crate_label or doc.get("crate", "?")
    rows = {}
    for body in doc["bodies"]:
        rows[(crate, body["def_path"], body.get("def_index"))] = row_of(body)
    return rows, doc.get("totals") or {}


def crate_of(path):
    name = os.path.basename(path)
    name = name[: -len(".coverage.json")] if name.endswith(".coverage.json") else name
    return HASHED.sub("", name)


def load_tree(root, only=None):
    files = sorted(glob.glob(os.path.join(root, "**", "*.coverage.json"), recursive=True))
    if not files:
        raise RowDiffError(f"no *.coverage.json under {root}")
    rows, totals, seen = {}, collections.Counter(), []
    for path in files:
        crate = crate_of(path)
        if only and crate != only:
            continue
        part, tot = load_file(path, crate_label=crate)
        rows.update(part)
        seen.append(crate)
        for k, v in tot.items():
            if isinstance(v, int):
                totals[k] += v
    if not rows:
        raise RowDiffError(f"{root}: no coverage rows"
                           + (f" for crate {only}" if only else ""))
    return rows, dict(totals), sorted(set(seen))


# ---------------------------------------------------------------------------
# the differential
# ---------------------------------------------------------------------------
def _num(v):
    return v if isinstance(v, (int, float)) and not isinstance(v, bool) else None


def axis_regressed(axis, before, after):
    """Is this per-axis movement a regression? Direction-aware, never a net count."""
    if before == after:
        return False
    if axis.direction == "lost":
        return bool(before) and not after
    if axis.direction == "gone":
        return bool(before) and not after
    if axis.direction == "down":
        a, b = _num(before), _num(after)
        return a is not None and b is not None and b < a
    if axis.direction == "up":
        a, b = _num(before), _num(after)
        return a is not None and b is not None and b > a
    return False


def is_stub_collapse(before, after):
    """A real lowered body became a stub.

    Deliberately broader than `lowered: true -> false`, because the collapse can
    also present as a body that still claims to be lowered while its instruction
    count falls to the 1-instruction placeholder. Either spelling is the same
    event and must land in the same class.
    """
    ib, ia = _num(before["instr_count"]), _num(after["instr_count"])
    had_body = bool(before["lowered"]) and (ib is None or ib > 1)
    if not had_body:
        return False
    if not after["lowered"]:
        return True
    return ia is not None and ia <= 1 and (ib is None or ib > 1)


def diff_rows(control, subject):
    shared = sorted(set(control) & set(subject))
    only_c = sorted(set(control) - set(subject))
    only_s = sorted(set(subject) - set(control))

    moved = []            # (key, [axis names that differ])
    lost = collections.defaultdict(list)     # axis -> keys that regressed
    gained = collections.defaultdict(list)   # axis -> keys that improved
    changed = collections.Counter()          # axis -> rows differing at all
    stubs, unstubs = [], []

    for key in shared:
        before, after = control[key], subject[key]
        delta = [a.name for a in AXES if before[a.name] != after[a.name]]
        if not delta:
            continue
        moved.append((key, delta))
        for name in delta:
            axis = AXIS_BY_NAME[name]
            changed[name] += 1
            if axis_regressed(axis, before[name], after[name]):
                lost[name].append(key)
            elif axis_regressed(axis, after[name], before[name]):
                gained[name].append(key)
        if is_stub_collapse(before, after):
            stubs.append(key)
        elif is_stub_collapse(after, before):
            unstubs.append(key)

    # verdict transitions, as sets rather than bucket totals
    def verdict_set(rows, field, value):
        return {k for k, r in rows.items() if r[field] == value}

    def went_vacuous(a, b):
        return {k for k in shared
                if (a[k]["markers_lines"] or 0) > 0 and b[k]["markers_lines"] == 0
                and a[k]["markers_exact"] and b[k]["markers_exact"]}

    ag_c = verdict_set(control, "dm_verdict", "agreed")
    ag_s = verdict_set(subject, "dm_verdict", "agreed")
    mm_c = verdict_set(control, "dm_verdict", "mismatch")
    mm_s = verdict_set(subject, "dm_verdict", "mismatch")

    return {
        "shared": shared, "only_control": only_c, "only_subject": only_s,
        "moved": moved, "lost": dict(lost), "gained": dict(gained),
        "changed": dict(changed), "stub_collapse": stubs, "stub_recovery": unstubs,
        "agreed_lost": sorted(ag_c - ag_s), "agreed_gained": sorted(ag_s - ag_c),
        "mismatch_new": sorted(mm_s - mm_c), "mismatch_cleared": sorted(mm_c - mm_s),
        "markers_went_vacuous": sorted(went_vacuous(control, subject)),
        "markers_became_real": sorted(went_vacuous(subject, control)),
        "admitted_wrong_new": sorted(
            verdict_set(subject, "markers_class", "ADMITTED-WRONG")
            - verdict_set(control, "markers_class", "ADMITTED-WRONG")),
        "admitted_wrong_cleared": sorted(
            verdict_set(control, "markers_class", "ADMITTED-WRONG")
            - verdict_set(subject, "markers_class", "ADMITTED-WRONG")),
    }


# HARD is coverage that is gone: a body that no longer lowers, no longer splices,
# no longer agrees, or has left the dump. SOFT is a body that is still there and
# still lowering but measures smaller. Both are always PRINTED and counted -- the
# tier decides only what turns the exit code red, so that a gate which must stay
# meaningful does not cry wolf over a leaner but complete lowering.
HARD_AXES = ("lowered", "spliced", "lineage", "markers_exact")
SOFT_AXES = ("instr_count", "calls_resolved", "calls_unresolved",
             "interp_samples", "func_id", "markers_lines")


def regression_classes(d):
    """The headline list, as (name, keys, note, severity). Order is severity."""
    out = []
    if d["stub_collapse"]:
        out.append(("STUB COLLAPSE", d["stub_collapse"],
                    "a real lowered body became a <=1-instruction stub", "hard"))
    for name in HARD_AXES:
        if d["lost"].get(name):
            out.append((f"{name} LOST", d["lost"][name], AXIS_BY_NAME[name].note, "hard"))
    if d["agreed_lost"]:
        out.append(("derived-MIR agreed LOST", d["agreed_lost"], "", "hard"))
    if d["mismatch_new"]:
        out.append(("NEW derived-MIR mismatch", d["mismatch_new"], "", "hard"))
    if d["markers_went_vacuous"]:
        out.append(("MARKER CLAIM WENT VACUOUS", d["markers_went_vacuous"],
                    "still `markers_exact: true`, but now compares two EMPTY marker "
                    "sequences -- the exactness claim survived, its content did not", "hard"))
    if d["admitted_wrong_new"]:
        out.append(("NEW ADMITTED-WRONG markers", d["admitted_wrong_new"],
                    "emitted a derived marker sequence that disagrees -- worse than "
                    "refusing, and no boolean distinguishes the two", "hard"))
    if d["only_control"]:
        out.append(("BODY DISAPPEARED", d["only_control"],
                    "present in control, absent from subject", "hard"))
    for name in SOFT_AXES:
        if d["lost"].get(name):
            out.append((f"{name} LOST", d["lost"][name], AXIS_BY_NAME[name].note, "soft"))
    return out


# ---------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------
def _short(v, width=88):
    s = repr(v) if not isinstance(v, str) else v
    s = s.replace("\n", "\\n")
    return s if len(s) <= width else s[: width - 1] + "…"


def print_row(key, control, subject, axes, indent="      "):
    before, after = control[key], subject[key]
    crate, path, idx = key
    print(f"  {path}   [{crate} def_index={idx}]")
    for name in axes:
        if before[name] == after[name]:
            continue
        print(f"{indent}{name:20} {_short(before[name])}")
        print(f"{indent}{'':20} -> {_short(after[name])}")


def report(control, subject, totals_c, totals_s, args, extra_note=""):
    d = diff_rows(control, subject)
    cap = None if args.max_rows == 0 else args.max_rows

    print("== trust-ir ROW-EXACT differential ==")
    if extra_note:
        print(f"   {extra_note}")
    print(f"   control rows {len(control)}   subject rows {len(subject)}")
    print(f"   control-only {len(d['only_control'])}   "
          f"subject-only {len(d['only_subject'])}")
    for key in d["only_control"][:cap]:
        print(f"     CONTROL-ONLY {key[1]}")
    for key in d["only_subject"][:cap]:
        print(f"     SUBJECT-ONLY {key[1]}")

    # ---- totals beside the set truth --------------------------------------
    # A net delta on its own is the exact shape of report that hid this defect
    # for four reviews. It is printed here only with LOST and GAINED next to it.
    print("\n--- file totals, with the per-body SET truth beside every net delta ---")
    print(f"    {'axis':22} {'control':>9} {'subject':>9} {'net':>7}   "
          f"{'LOST':>5} {'GAINED':>6}   {'moved':>6}")
    total_keys = ("bodies", "lowered", "spliced", "symbolic", "instr_count",
                  "declarations", "initializer_bodies", "unsupported")
    for name in total_keys:
        if name not in totals_c and name not in totals_s:
            continue
        cv, sv = totals_c.get(name), totals_s.get(name)
        net = (sv - cv) if isinstance(cv, int) and isinstance(sv, int) else None
        lost = len(d["lost"].get(name, ()))
        gain = len(d["gained"].get(name, ()))
        moved = d["changed"].get(name, 0)
        flag = ""
        if net == 0 and (lost or gain):
            flag = "   <== NET ZERO, ROWS MOVED"
        print(f"    {name:22} {str(cv):>9} {str(sv):>9} "
              f"{('' if net is None else f'{net:+d}'):>7}   "
              f"{lost:>5} {gain:>6}   {moved:>6}{flag}")

    # ---- every axis, always, even the quiet ones --------------------------
    print("\n--- every watched axis (rows differing / regressed / improved) ---")
    for axis in AXES:
        moved = d["changed"].get(axis.name, 0)
        lost = len(d["lost"].get(axis.name, ()))
        gain = len(d["gained"].get(axis.name, ()))
        mark = "  *" if lost else ""
        print(f"    {axis.name:22} moved={moved:<6} LOST={lost:<5} GAINED={gain:<5}"
              f" [{axis.direction}]{mark}")

    # ---- the published table, next to what it cannot see ------------------
    # `agreed / unsupported / mismatch` is the table four consecutive merge
    # reviews published. It is reproduced here deliberately, with the rows that
    # LEFT and ENTERED each bucket beside it, so that a bucket which is static
    # by count AND by membership is visibly static rather than reassuring.
    print("\n--- derived-MIR verdict buckets (the table the reviews published) ---")
    print(f"    {'bucket':22} {'control':>9} {'subject':>9} {'net':>7}   "
          f"{'LEFT':>5} {'ENTERED':>7}")
    bc = collections.Counter(r["dm_verdict"] for r in control.values())
    bs = collections.Counter(r["dm_verdict"] for r in subject.values())
    for value in sorted(set(bc) | set(bs)):
        cset = {k for k, r in control.items() if r["dm_verdict"] == value}
        sset = {k for k, r in subject.items() if r["dm_verdict"] == value}
        left, entered = len(cset - sset), len(sset - cset)
        print(f"    {value:22} {bc[value]:>9} {bs[value]:>9} "
              f"{bs[value] - bc[value]:>+7}   {left:>5} {entered:>7}")
    # Rows this table can say anything at all about: those that changed bucket.
    bucket_visible = {k for k in d["shared"]
                      if control[k]["dm_verdict"] != subject[k]["dm_verdict"]}

    # ---- headline ---------------------------------------------------------
    classes = regression_classes(d)
    hard = [c for c in classes if c[3] == "hard"]
    soft = [c for c in classes if c[3] == "soft"]
    print(f"\n--- ROW-EXACT: {len(d['moved'])} of {len(d['shared'])} shared rows moved ---")
    print(f"--- REGRESSION CLASSES: {len(hard)} HARD, {len(soft)} SOFT ---")
    if not classes:
        print("    (none)")
    for name, keys, note, sev in classes:
        suffix = f"   -- {note}" if note else ""
        marker = "***" if sev == "hard" else " · "
        print(f"    {marker} [{sev}] {name:26} {len(keys):>5}{suffix}")
    if soft:
        print("    SOFT = the body is still lowered and spliced but measures smaller;")
        print("    reported and counted, but it does not by itself turn this gate red.")
    print(f"    (improvements: agreed GAINED {len(d['agreed_gained'])}, "
          f"mismatch CLEARED {len(d['mismatch_cleared'])}, "
          f"lowered GAINED {len(d['gained'].get('lowered', ()))}, "
          f"stub RECOVERY {len(d['stub_recovery'])})")

    # The indictment. This is the exact situation that went unreported four times:
    # every regressed row invisible to the bucket table, and real coverage gone.
    regressed_rows = set()
    for _name, keys, _note, _sev in classes:
        regressed_rows.update(keys)
    invisible = regressed_rows - bucket_visible
    if regressed_rows and not (regressed_rows & bucket_visible):
        print("\n    !!! THE BUCKET TABLE IS CLEAN AND THE CRATE STILL REGRESSED. !!!")
        print(f"    All {len(invisible)} regressed row(s) hold their derived-MIR bucket,")
        print("    so a review reading only agreed/unsupported/mismatch would report")
        print("    '0 lost' and be correct on its own terms -- as four consecutive merge")
        print("    reviews were. The loss above is on the coverage axes (lowered /")
        print("    spliced / instr_count / lineage), which that table has no column for.")
        print("    This is the blind spot this tool exists to close.")
    elif invisible:
        print(f"\n    NOTE: {len(invisible)} of {len(regressed_rows)} regressed row(s) hold")
        print("    their derived-MIR bucket and are invisible to the published table.")

    # ---- the rows themselves ----------------------------------------------
    for name, keys, _note, sev in classes:
        print(f"\n=== [{sev}] {name}: {len(keys)} row(s) ===")
        for key in keys[:cap]:
            if key in control and key in subject:
                print_row(key, control, subject, AXIS_NAMES)
                bd, sd = control[key], subject[key]
                if bd["dm_verdict"] == sd["dm_verdict"]:
                    print(f"      derived-MIR verdict UNCHANGED "
                          f"({bd['dm_verdict']}) -- bucket totals CANNOT see this row")
            else:
                print(f"  {key[1]}   [{key[0]} def_index={key[2]}]")
        if cap is not None and len(keys) > cap:
            print(f"  ... and {len(keys) - cap} more (raise --max-rows)")

    if args.all:
        print(f"\n=== every moved row: {len(d['moved'])} ===")
        for key, axes in d["moved"][:cap]:
            print_row(key, control, subject, axes)

    # ---- what the old instruments would have said -------------------------
    if args.legacy_tuple:
        print("\n--- WHAT THE PRE-CONSOLIDATION COMPARATORS SAW ---")
        stub_keys = set(d["stub_collapse"])
        for who, fields in LEGACY_TUPLES.items():
            n = sum(1 for key in d["shared"]
                    if tuple(control[key][f] for f in fields)
                    != tuple(subject[key][f] for f in fields))
            seen = sum(1 for key in stub_keys
                       if tuple(control[key][f] for f in fields)
                       != tuple(subject[key][f] for f in fields))
            verdict = ("watches `lowered`" if "lowered" in fields
                       else "does NOT watch `lowered`")
            print(f"    {who}")
            print(f"        tuple={fields}")
            print(f"        moved rows={n}   of the {len(stub_keys)} stub-collapse "
                  f"rows it would flag {seen} -- and CLASSIFY 0")
            print(f"        {verdict}; watches `spliced` "
                  f"{'yes' if 'spliced' in fields else 'NO'}; "
                  f"`instr_count` {'yes' if 'instr_count' in fields else 'NO'}; "
                  f"`lineage` {'yes' if 'lineage' in fields else 'NO'}")

    if args.json:
        payload = {
            "schema": "trust.trust_ir_rowdiff.v1",
            "rows": {"control": len(control), "subject": len(subject),
                     "shared": len(d["shared"]),
                     "only_control": [list(k) for k in d["only_control"]],
                     "only_subject": [list(k) for k in d["only_subject"]]},
            "totals": {"control": totals_c, "subject": totals_s},
            "axes": {a.name: {"direction": a.direction,
                              "moved": d["changed"].get(a.name, 0),
                              "lost": [list(k) for k in d["lost"].get(a.name, ())],
                              "gained": [list(k) for k in d["gained"].get(a.name, ())]}
                     for a in AXES},
            "regression_classes": [{"name": n, "severity": sev, "count": len(k),
                                    "rows": [list(x) for x in k]}
                                   for n, k, _, sev in classes],
            "stub_collapse": [list(k) for k in d["stub_collapse"]],
            "stub_recovery": [list(k) for k in d["stub_recovery"]],
            "agreed_lost": [list(k) for k in d["agreed_lost"]],
            "agreed_gained": [list(k) for k in d["agreed_gained"]],
            "mismatch_new": [list(k) for k in d["mismatch_new"]],
            "markers_went_vacuous": [list(k) for k in d["markers_went_vacuous"]],
            "markers_became_real": [list(k) for k in d["markers_became_real"]],
            "admitted_wrong_new": [list(k) for k in d["admitted_wrong_new"]],
            "admitted_wrong_cleared": [list(k) for k in d["admitted_wrong_cleared"]],
            "mismatch_cleared": [list(k) for k in d["mismatch_cleared"]],
            "moved_rows": [{"key": list(k), "axes": ax} for k, ax in d["moved"]],
        }
        with open(args.json, "w") as fh:
            json.dump(payload, fh, indent=1)
            fh.write("\n")
        print(f"\nwrote {args.json}")

    if args.fail_on == "never":
        return 0
    if args.fail_on == "any":
        return 1 if (d["moved"] or d["only_control"] or d["only_subject"]) else 0
    if args.fail_on == "soft":
        return 1 if classes else 0
    return 1 if hard else 0


# ---------------------------------------------------------------------------
# flip logs
# ---------------------------------------------------------------------------
DID = re.compile(r"did=DefId\(([^)]*)\)")
FLIP = re.compile(r"trust-ir-flip: (CTFE )?compiled from trust-ir")
FB = re.compile(r'FALLBACK to built MIR, did=DefId\(([^)]*)\), reason="(.*?)", stage="([^"]*)"')

# `0:13226 ~ clean_kernel[1f2d]::env::proof_search::constant_kind_rank`
# The `[1f2d]` is cargo's per-BUILD crate disambiguator and the leading `0:13226`
# is a def-index that also moves. Neither is body identity.
DID_PARTS = re.compile(r"^\s*(\d+):(\d+)\s*~\s*([A-Za-z0-9_]+)(?:\[([0-9a-f]+)\])?(?:::(.*))?$")


def norm_did(raw):
    """Body identity from a DefId string: crate + path, disambiguator stripped.

    THE DEFECT THIS FIXES. All four copies of `fliplog.py` joined on the RAW DefId
    string. Two independently-built logs carry different disambiguators
    (`clean_kernel[1f2d]` vs `clean_kernel[4676]`), so the join matched nothing and
    the comparator reported 100% of flips as simultaneously LOST and GAINED --
    "LOST 153 / GAINED 153" on two logs of the same crate. That is the loudest
    output the harness produces, and in the configuration people actually use it in
    it was pure noise. A reader who learns to ignore the LOST section is exactly as
    blind as one who never had it, so this is the same failure as the silent one
    approached from the other side.
    """
    m = DID_PARTS.match(raw)
    if not m:
        return raw.strip()
    crate, path = m.group(3), m.group(5)
    return f"{crate}::{path}" if path else crate


def parse_flips(path):
    if not os.path.exists(path):
        raise RowDiffError(f"no such flip log: {path}")
    flips, ctfe, fallbacks = set(), set(), {}
    reasons = collections.Counter()
    raw_of, disambiguators = {}, set()
    with open(path, errors="replace") as fh:
        for line in fh:
            m = FB.search(line)
            if m:
                key = norm_did(m.group(1))
                raw_of[key] = m.group(1)
                fallbacks[key] = (m.group(2), m.group(3))
                reasons[(m.group(3), m.group(2))] += 1
                continue
            if FLIP.search(line):
                did = DID.search(line)
                if did:
                    key = norm_did(did.group(1))
                    raw_of[key] = did.group(1)
                    parts = DID_PARTS.match(did.group(1))
                    if parts and parts.group(4):
                        disambiguators.add(parts.group(4))
                    (ctfe if "CTFE" in line else flips).add(key)
    return flips, ctfe, fallbacks, reasons, disambiguators


def report_flips(cpath, spath, args):
    fc, cc, bc, rc, dc = parse_flips(cpath)
    fs, cs, bs, rs, ds = parse_flips(spath)
    cap = None if args.max_rows == 0 else args.max_rows
    print("== trust-ir FLIP-LOG differential ==")
    if dc and ds and dc != ds:
        print(f"   note: crate disambiguators differ ({','.join(sorted(dc))} vs "
              f"{','.join(sorted(ds))}); joined on crate::path, which is stable.")
        print("   Joining on the raw DefId here would report every flip as both LOST")
        print("   and GAINED. See norm_did() for why that mattered.")
    for label, a, b in (("codegen flips", fc, fs), ("CTFE flips", cc, cs),
                        ("fallbacks", set(bc), set(bs))):
        print(f"   {label:15} control={len(a):<6} subject={len(b):<6} "
              f"net={len(b) - len(a):+d}   LOST={len(a - b)} GAINED={len(b - a)}")

    regressed = False
    for label, a, b in (("codegen", fc, fs), ("CTFE", cc, cs)):
        lost, gained = sorted(a - b), sorted(b - a)
        print(f"\n--- {label}: LOST {len(lost)} / GAINED {len(gained)} ---")
        if lost:
            regressed = True
            for did in lost[:cap]:
                why = bs.get(did, ("(no fallback logged -- body never reached the seam)", ""))
                print(f"  *** LOST FLIP *** {did}\n      subject fallback: {why[0]} [{why[1]}]")
        for did in gained[:cap]:
            print(f"  + {did}")
        if cap is not None and len(gained) > cap:
            print(f"  ... and {len(gained) - cap} more gained")

    print("\n--- fallback reasons whose count moved ---")
    moved = [k for k in set(rc) | set(rs) if rc[k] != rs[k]]
    if not moved:
        print("  (none)")
    for k in sorted(moved, key=lambda k: -abs(rs[k] - rc[k]))[:cap]:
        print(f"  {rc[k]:5} -> {rs[k]:5}   [{k[0]}] {k[1]}")

    if args.json:
        with open(args.json, "w") as fh:
            json.dump({
                "schema": "trust.trust_ir_rowdiff.flips.v1",
                "codegen": {"control": sorted(fc), "subject": sorted(fs),
                            "lost": sorted(fc - fs), "gained": sorted(fs - fc)},
                "ctfe": {"control": sorted(cc), "subject": sorted(cs),
                         "lost": sorted(cc - cs), "gained": sorted(cs - cc)},
                "fallback_reasons": {"control": {f"{k[0]}|{k[1]}": v for k, v in rc.items()},
                                     "subject": {f"{k[0]}|{k[1]}": v for k, v in rs.items()}},
            }, fh, indent=1)
            fh.write("\n")
        print(f"\nwrote {args.json}")

    if args.fail_on == "never":
        return 0
    if args.fail_on == "any":
        return 1 if (fc ^ fs or cc ^ cs or moved) else 0
    return 1 if regressed else 0


# ---------------------------------------------------------------------------
def build_parser():
    p = argparse.ArgumentParser(
        prog="trust_ir_rowdiff.py",
        description="Row-exact control/subject differential over trust-ir coverage dumps.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__.split("USAGE", 1)[0])
    p.add_argument("mode", choices=("rows", "tree", "flips"))
    p.add_argument("control")
    p.add_argument("subject")
    p.add_argument("--crate", default=None, help="tree mode: restrict to one crate")
    p.add_argument("--json", default=None, metavar="PATH")
    p.add_argument("--max-rows", type=int, default=40, help="0 = unlimited")
    p.add_argument("--all", action="store_true", help="print every moved row")
    p.add_argument("--legacy-tuple", action="store_true",
                   help="also report what the pre-consolidation comparators saw")
    p.add_argument("--fail-on", choices=("regression", "soft", "any", "never"),
                   default="regression",
                   help="regression = HARD classes only (default); soft = hard+soft; "
                        "any = any moved row; never = report only")
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)
    try:
        if args.mode == "flips":
            return report_flips(args.control, args.subject, args)
        if args.mode == "rows":
            control, tc = load_file(args.control)
            subject, ts = load_file(args.subject)
            note = f"{args.control}\n   {args.subject}"
        else:
            control, tc, cc = load_tree(args.control, args.crate)
            subject, ts, sc = load_tree(args.subject, args.crate)
            note = (f"{args.control}  crates={','.join(cc)}\n"
                    f"   {args.subject}  crates={','.join(sc)}")
        return report(control, subject, tc, ts, args, extra_note=note)
    except RowDiffError as exc:
        print(f"trust_ir_rowdiff: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
