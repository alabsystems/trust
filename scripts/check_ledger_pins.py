#!/usr/bin/env python3
"""check_ledger_pins.py — every blob a reviewed landing-gate ledger pins holds
in the tree being pushed, or the entry that pins it says it lapsed
(LEDGER-PIN-CURRENCY-AT-LANDING-1).

Two ledgers record a review of exact file bytes:

  scripts/gates/land-escape-audits.toml      each [[audit]] and [[not_path]]
      row pins its file's blob and the blob of every premise its reasoning
      rests on; land_select grants the row only while all of them hold
      (audit_holds), and an unresolved site reads everything
  scripts/ir_cohort_physical_read_set.json   the blob of every module the
      IR-only cohort run executes; land_gate narrows that run
      (ir_diagnostic_readers_match) only while every reader is its pinned blob,
      and runs the full selection and physical check otherwise

Both products already fail closed on a moved pin: it costs selection scope,
never soundness, so this row guards no verdict. What went red is the ledgers'
currency tests (land_development_test's BootstrapFixtureAuditTests,
land_gate_test's FixtureEscapeAuditTests, EscapeAuditRenewalTests and
IrDiagnosticPhysicalInputsTests), which hold the live entries to the live tree.
A landing that moved a pinned premise or reader outside their selection ran
none of them, so dev main went red until someone else renewed the pin (three
times on 2026-11-10), and a moved pin no test reads lapsed a row silently. This
row moves the decision to the landing that moves the pin. In the pushed tree,
every pin must

  * HOLD: the path is a blob there whose object id is the pinned one; or
  * belong to an entry EXPLICITLY LAPSED in the same tree: a row's
    `lapsed = "YYYY-MM-DD <commit>: <why>"` (land_select.LAPSED), or the read
    set's `"lapsed": {"<reader>": "YYYY-MM-DD <commit>: <why>"}`. A lapsed row
    grants nothing (audit_holds); a read set with any lapse never narrows
    (ir_diagnostic_readers_match accepts only `schema` and `readers`). The
    currency tests skip exactly the lapsed entries, by that marker, never by a
    blob that differs.

It also refuses an entry the product would silently drop (a row land_select
does not load, a duplicate row, a lapse naming no reader): each grants
nothing and fails the ledger's own load tests. It reads git objects only and
compiles nothing (well under a second).

WHICH TREE IS JUDGED. With TRUST_PUSHED_REFS set and non-blank (the pre-push
hook and `scripts/land_gate.py push-rows` export git's `<local_ref> <local_sha>
<remote_ref> <remote_sha>` lines) every non-deletion pushed sha's own tree,
from git objects: never the index or the working tree. A deletion-only push
prints `SKIPPED:`; a malformed line exits 2; a sha this clone cannot read is a
red that is not keyed. With it unset, HEAD's tree (or `--rev REV`'s).

FINDING KEYS. One `FINDING: <key>` per cause, then `FINDINGS: complete` when
every cause was keyed, so push-rows grades a red the destination already
carries INHERITED and FAILs a push that adds one. A key names the entry and
the pin, never the tree's blob or the push:
  escape-audits <audit|not_path> <file> MOVED <pinned path> <pinned blob>
  escape-audits <audit|not_path> <file> ABSENT <pinned path>
  escape-audits <audit|not_path> <file or #n> MALFORMED | DUPLICATE
  escape-audits LEDGER-ABSENT | LEDGER-UNREADABLE
  ir-read-set <reader> MOVED <pinned blob> | ABSENT
  ir-read-set LAPSE-NAMES-NO-READER <name> | MALFORMED | LEDGER-ABSENT
A lapsed entry whose pins all hold again is a NOTE, not a red: deleting its
marker restores what it grants.

Usage:
    scripts/check_ledger_pins.py              # the push, else HEAD
    scripts/check_ledger_pins.py --rev REV    # one revision's tree

Exit codes: 0 every pin holds or is lapsed (or nothing pushed); 1 a red (keyed
or not); 2 usage, or a malformed TRUST_PUSHED_REFS.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

ROOT = Path(__file__).resolve().parents[1]


def reexec_for_tomllib() -> None:
    """This row reads TOML twice: the escape-audit ledger, and (through
    land_select, which refuses to import without it) the landing gate's row
    table gates/land.toml. Under a Python older than 3.11, which has no
    tomllib, run this script again under the newest Python >= 3.11 on PATH (as
    land_gate.py does); with none, a red with no key (a ledger this row cannot
    read is not a pass). It runs BEFORE land_select is imported: that import
    is where an old interpreter stops."""
    if sys.version_info >= (3, 11):
        return
    for cand in ("python3.14", "python3.13", "python3.12", "python3.11"):
        path = shutil.which(cand)
        if path:
            os.execv(path, [path, *(["-B"] if sys.dont_write_bytecode else []), str(Path(__file__).resolve()),
                            *sys.argv[1:]])
    print("LEDGER PINS UNREADABLE: the escape-audit ledger is TOML and needs Python >= 3.11 (tomllib); none is on "
          "PATH. A ledger this row cannot read is not a pass.")
    sys.exit(1)


if __name__ == "__main__":
    reexec_for_tomllib()

sys.path.insert(0, str(ROOT / "scripts" / "lib"))

import land_select as ls  # noqa: E402  (its row rules: audit_row_ok, not_path_row_ok, LAPSED)

AUDITS = ls.AUDITS_FILE
READ_SET = "scripts/ir_cohort_physical_read_set.json"
READ_SET_SCHEMA = "trust.land-gate.ir-cohort-read-set.v1"
HEX_SHA = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
ZERO_SHA = re.compile(r"^0+$")
LS_TREE_BATCH = 256


class GateError(Exception):
    """A tree or object this clone cannot read: a red with no key."""


@dataclass
class Moved:
    key: str
    path: str
    pinned: str
    actual: Optional[str]  # None: no blob at the path


@dataclass
class Verdict:
    ledger: str
    summary: str = ""
    moved: List[Moved] = field(default_factory=list)
    findings: List[str] = field(default_factory=list)
    explained: List[str] = field(default_factory=list)  # why each non-MOVED finding is one
    notes: List[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Git objects
# ---------------------------------------------------------------------------

def git(root: Path, *args: str) -> bytes:
    try:
        return ls.git(str(root), "--literal-pathspecs", *args) if args[0] == "ls-tree" else ls.git(str(root), *args)
    except RuntimeError as exc:
        raise GateError(str(exc).splitlines()[-1] if str(exc) else "git failed") from None


def blobs_at(root: Path, tree: str, paths: Sequence[str]) -> Dict[str, Tuple[str, str]]:
    """{path: (object type, object id)} for each of `paths` the tree holds as
    an entry (a directory at a pinned path is no entry)."""
    wanted = sorted(set(paths))
    out: Dict[str, Tuple[str, str]] = {}
    for start in range(0, len(wanted), LS_TREE_BATCH):
        chunk = wanted[start:start + LS_TREE_BATCH]
        for record in git(root, "ls-tree", "-r", "-z", "--full-tree", tree, "--", *chunk).split(b"\0"):
            if not record:
                continue
            meta, tab, raw = record.partition(b"\t")
            fields = meta.split()
            if not tab or len(fields) != 3:
                raise GateError(f"unreadable `git ls-tree` record {record[:80]!r}")
            path = raw.decode("utf-8", "surrogateescape")
            if path in chunk:
                out[path] = (fields[1].decode("ascii"), fields[2].decode("ascii"))
    return out


def ledger_bytes(root: Path, tree: str, path: str) -> Optional[bytes]:
    entry = blobs_at(root, tree, [path]).get(path)
    if entry is None or entry[0] != "blob":
        return None
    return git(root, "cat-file", "blob", entry[1])


def pin_state(entries: Dict[str, Tuple[str, str]], path: str, blob: str) -> Tuple[bool, Optional[str]]:
    """(whether the pin holds, the blob the tree holds at the path or None)."""
    entry = entries.get(path)
    actual = entry[1] if entry is not None and entry[0] == "blob" else None
    return actual == blob, actual


# ---------------------------------------------------------------------------
# The two ledgers
# ---------------------------------------------------------------------------

def audit_rows(raw: Optional[bytes]) -> Tuple[Optional[dict], Optional[str]]:
    if raw is None:
        return None, "LEDGER-ABSENT"
    if ls.tomllib is None:
        raise GateError("this interpreter has no tomllib (Python >= 3.11 reads the escape-audit ledger)")
    try:
        return ls.tomllib.loads(raw.decode("utf-8")), None
    except (UnicodeDecodeError, ls.tomllib.TOMLDecodeError) as exc:
        return None, f"LEDGER-UNREADABLE ({type(exc).__name__}: {str(exc).splitlines()[0] if str(exc) else ''})"


def row_pins(row: dict) -> List[Tuple[str, str]]:
    return [(row["file"], row["blob"]), *((pin["file"], pin["blob"]) for pin in row.get("premises", []))]


def judge_audits(root: Path, tree: str, raw: Optional[bytes]) -> Verdict:
    v = Verdict("escape-audits")
    doc, problem = audit_rows(raw)
    if doc is None:
        key = problem.split(" ", 1)[0]
        v.findings.append(f"escape-audits {key}")
        v.explained.append(f"{AUDITS}: {problem}; every row then grants nothing and the ledger's tests cannot load it")
        v.summary = f"{AUDITS}: not readable"
        return v
    tables: List[Tuple[str, list]] = []
    for table in ("audit", "not_path"):
        rows = doc.get(table, [])
        if not isinstance(rows, list):
            v.findings.append(f"escape-audits {table} #0 MALFORMED")
            v.explained.append(f"[[{table}]] is not an array of tables: land_select loads none of it")
            rows = []
        tables.append((table, rows))
    valid: List[Tuple[str, dict]] = []
    for table, rows in tables:
        ok = ls.audit_row_ok if table == "audit" else ls.not_path_row_ok
        seen: Dict[str, int] = {}
        for n, row in enumerate(rows, 1):
            name = row.get("file") if isinstance(row, dict) and isinstance(row.get("file"), str) and row.get("file") \
                else f"#{n}"
            if not ok(row):
                v.findings.append(f"escape-audits {table} {name} MALFORMED")
                why = (" (`lapsed` must read \"YYYY-MM-DD <commit>: <why>\")"
                       if isinstance(row, dict) and not ls.lapse_ok(row) else "")
                v.explained.append(f"[[{table}]] {name}: land_select does not load this row{why}, so it grants "
                                   "nothing and the ledger's load test fails; fix its keys and values")
                continue
            if name in seen:
                v.findings.append(f"escape-audits {table} {name} DUPLICATE")
                v.explained.append(f"[[{table}]] {name}: a second row for the file (rows {seen[name]} and {n}); "
                                   "land_select keeps one and the ledger's load test fails; merge them")
                continue
            seen[name] = n
            valid.append((table, row))
    entries = blobs_at(root, tree, [path for _t, row in valid for path, _b in row_pins(row)])
    held = lapsed = 0
    for table, row in valid:
        moved = [(path, blob, actual) for path, blob in row_pins(row)
                 for holds, actual in [pin_state(entries, path, blob)] if not holds]
        if "lapsed" in row:
            lapsed += 1
            if not moved:
                v.notes.append(f"NOTE: [[{table}]] {row['file']} is lapsed but every pin it holds is current: "
                               "deleting its `lapsed` key (after re-reading it) restores the row")
            continue
        if not moved:
            held += 1
            continue
        for path, blob, actual in moved:
            key = (f"escape-audits {table} {row['file']} MOVED {path} {blob}" if actual is not None
                   else f"escape-audits {table} {row['file']} ABSENT {path}")
            v.moved.append(Moved(key, path, blob, actual))
            v.findings.append(key)
    v.summary = (f"{AUDITS}: {len(valid)} loaded row(s): {held} hold, {lapsed} lapsed, "
                 f"{len(valid) - held - lapsed} with a moved pin")
    return v


def judge_read_set(root: Path, tree: str, raw: Optional[bytes]) -> Verdict:
    v = Verdict("ir-read-set")
    if raw is None:
        v.findings.append("ir-read-set LEDGER-ABSENT")
        v.explained.append(f"{READ_SET} is not a file in this tree: the IR-only run never narrows, and the "
                           "read set's tests cannot load it")
        v.summary = f"{READ_SET}: absent"
        return v

    def unique(pairs):
        out = {}
        for key, value in pairs:
            if key in out:
                raise ValueError(f"duplicate field {key!r}")
            out[key] = value
        return out

    problem = None
    try:
        doc = json.loads(raw.decode("utf-8"), object_pairs_hook=unique)
    except (UnicodeDecodeError, ValueError) as exc:
        doc, problem = None, f"not JSON land_gate reads ({exc})"
    if doc is not None:
        if not isinstance(doc, dict) or not set(doc) <= {"schema", "readers", "lapsed"}:
            problem = "a field other than schema, readers and lapsed"
        elif doc.get("schema") != READ_SET_SCHEMA:
            problem = f"schema is not {READ_SET_SCHEMA}"
        elif not isinstance(doc.get("readers"), dict) or not all(
                isinstance(k, str) and isinstance(b, str) and re.fullmatch(r"[0-9a-f]{40}(?:[0-9a-f]{24})?", b)
                for k, b in doc["readers"].items()):
            problem = "readers is not a map of paths to object ids"
        elif "lapsed" in doc and (not isinstance(doc["lapsed"], dict) or not doc["lapsed"] or not all(
                isinstance(k, str) and isinstance(w, str) and ls.LAPSED.fullmatch(w) for k, w in doc["lapsed"].items())):
            problem = 'lapsed is not a non-empty map of readers to "YYYY-MM-DD <commit>: <why>"'
    if problem is not None:
        v.findings.append("ir-read-set MALFORMED")
        v.explained.append(f"{READ_SET}: {problem}; the IR-only run never narrows on it, and its tests fail")
        v.summary = f"{READ_SET}: malformed"
        return v
    readers: Dict[str, str] = doc["readers"]
    lapses: Dict[str, str] = doc.get("lapsed", {})
    for name in sorted(set(lapses) - set(readers)):
        v.findings.append(f"ir-read-set LAPSE-NAMES-NO-READER {name}")
        v.explained.append(f"{READ_SET}: lapsed names {name}, which is not a reader; lapse a reader by its path")
    entries = blobs_at(root, tree, list(readers))
    held = 0
    for reader in sorted(readers):
        blob = readers[reader]
        current, actual = pin_state(entries, reader, blob)
        if reader in lapses:
            if current:
                v.notes.append(f"NOTE: reader {reader} is lapsed but its pin is current: deleting it from "
                               "`lapsed` (after the refuter review) restores the narrowing")
            continue
        if current:
            held += 1
            continue
        key = f"ir-read-set {reader} MOVED {blob}" if actual is not None else f"ir-read-set {reader} ABSENT"
        v.moved.append(Moved(key, reader, blob, actual))
        v.findings.append(key)
    narrowing = "off (a reader is lapsed)" if lapses else "on while every pin holds"
    v.summary = (f"{READ_SET}: {len(readers)} reader(s): {held} hold, {len(set(lapses) & set(readers))} lapsed, "
                 f"{len(v.moved)} moved; IR-only narrowing {narrowing}")
    return v


def judge_tree(root: Path, tree: str) -> List[Verdict]:
    return [judge_audits(root, tree, ledger_bytes(root, tree, AUDITS)),
            judge_read_set(root, tree, ledger_bytes(root, tree, READ_SET))]


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def report_tree(label: str, verdicts: Sequence[Verdict]) -> bool:
    ok = True
    for v in verdicts:
        ok = ok and not v.findings
        print(f"[{label}] {v.summary}{': every pin holds or is lapsed' if not v.findings else ''}")
        for m in v.moved:
            where = f"the tree holds {m.actual}" if m.actual else "the tree holds no blob there"
            print(f"[{label}]   {m.key.split(' ', 1)[1]}  ({where})")
        for line in v.explained:
            print(f"[{label}]   {line}")
        for note in v.notes:
            print(f"[{label}]   {note}")
    return ok


def repair_lines(verdicts: Sequence[Verdict]) -> List[str]:
    lines = ["LEDGER PIN MOVED: a reviewed ledger pins a blob the pushed tree does not hold, and its entry does not "
             "say it lapsed, so the ledger's currency tests fail on this tree.",
             "  The landing that moves a pinned file carries, in the same push, for each entry named above, ONE of "
             "(docs/DECISION_QUEUE.md LEDGER-PIN-CURRENCY-AT-LANDING-1):"]
    if any(v.ledger == "escape-audits" and v.moved for v in verdicts):
        lines += [
            f"  {AUDITS}, a row:",
            "    RENEW  re-read the row's file and premises at the new blobs (`git diff <pinned> <new>` per moved "
            "pin), have an independent refuter check that no read, listing, history read, process or caller "
            "changed, add a dated paragraph to the row's reason (what moved, by which commit, why the row still "
            "holds), and set each moved pin to `git rev-parse <rev>:<path>`;",
            "    LAPSE  add `lapsed = \"YYYY-MM-DD <commit>: <what moved; why it was not renewed>\"` to the row. It "
            "then grants nothing (its site is unresolved: selection scope, never soundness) until a renewal "
            "deletes the key; keep its last reviewed pins for that review.",
        ]
    if any(v.ledger == "ir-read-set" and v.moved for v in verdicts):
        lines += [
            f"  {READ_SET}, a reader:",
            "    RENEW  give an independent refuter the old and new blobs, the other readers at the new revision "
            "(the path it must trace: a blob alone cannot show which of its functions that run reaches) and the "
            "question \"does any change add or alter a physical read on the IR-only cohort run's path?\" "
            "(refuted when unsure), record its verdict in the commit message, and set the reader's pin;",
            "    LAPSE  add `\"lapsed\": {\"<reader>\": \"YYYY-MM-DD <commit>: <why>\"}` beside `readers` (keep its "
            "old pin). The IR-only run then never narrows until it is re-pinned and the map is deleted.",
        ]
    if any(v.explained for v in verdicts):
        lines.append("  Neither clears the other finding(s); each is explained above.")
    return lines


def emit_findings(keys: Sequence[str], complete: bool) -> None:
    for key in sorted(set(keys)):
        print(f"FINDING: {key}")
    if complete and keys:
        print("FINDINGS: complete")


# ---------------------------------------------------------------------------
# Subjects
# ---------------------------------------------------------------------------

def parse_pushed_refs(raw: str) -> List[Tuple[str, str]]:
    pushed = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != 4 or not HEX_SHA.match(fields[1]) or not HEX_SHA.match(fields[3]):
            raise ValueError(f"malformed TRUST_PUSHED_REFS line {line!r}; expected "
                             "`<local_ref> <local_sha> <remote_ref> <remote_sha>`")
        pushed.append((fields[0], fields[1]))
    return pushed


def resolve_tree(root: Path, rev: str) -> str:
    out = git(root, "rev-parse", "--verify", "--quiet", "--end-of-options", f"{rev}^{{tree}}").decode("ascii").strip()
    if not HEX_SHA.match(out):
        raise GateError(f"{rev} names no tree")
    return out


def judge_subjects(root: Path, subjects: Sequence[Tuple[str, str]], heading: str) -> int:
    """Judge each (label, revision); one verdict per distinct tree."""
    trees: Dict[str, List[str]] = {}
    unreadable: List[str] = []
    for label, rev in subjects:
        try:
            trees.setdefault(resolve_tree(root, rev), []).append(label)
        except GateError:
            unreadable.append(f"[{label}] LEDGER PINS UNREADABLE: {rev} does not name a tree in this clone; "
                              "a tree this check cannot read is not a pass")
    print(heading, flush=True)
    keys: List[str] = []
    complete, ok = not unreadable, not unreadable
    for line in unreadable:
        print(line)
    all_verdicts: List[Verdict] = []
    for tree, labels in trees.items():
        label = ", ".join(labels)
        try:
            verdicts = judge_tree(root, tree)
        except GateError as exc:
            print(f"[{label}] LEDGER PINS UNREADABLE: {exc}")
            complete = ok = False
            continue
        all_verdicts.extend(verdicts)
        ok = report_tree(label, verdicts) and ok
        keys.extend(k for v in verdicts for k in v.findings)
    if ok:
        print("PASS: every pin of the escape-audit ledger and the IR read set holds or is explicitly lapsed")
        return 0
    if keys:
        for line in repair_lines(all_verdicts):
            print(line)
    emit_findings(keys, complete)
    return 1


def judge_push(root: Path, raw: str) -> int:
    try:
        pushed = parse_pushed_refs(raw)
    except ValueError as exc:
        print(f"LEDGER PINS INVALID: {exc}", file=sys.stderr)
        return 2
    live = [(ref, sha) for ref, sha in pushed if not ZERO_SHA.match(sha)]
    deletions = len(pushed) - len(live)
    if not live:
        print(f"SUBJECT: the pushed trees (TRUST_PUSHED_REFS: {deletions} deletion(s), nothing else)")
        print("SKIPPED: deletion(s) only, no tree pushed — nothing to judge")
        return 0
    names = ", ".join(f"{ref} {sha[:12]}" for ref, sha in live)
    extra = f"; {deletions} deletion(s) not judged" if deletions else ""
    return judge_subjects(root, [(f"{ref} {sha[:12]}", sha) for ref, sha in live],
                          f"SUBJECT: the pushed trees (TRUST_PUSHED_REFS: {names}{extra}), from git objects, "
                          "not the working tree")


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--rev", help="judge this revision's tree (ignores TRUST_PUSHED_REFS)")
    args = ap.parse_args(argv)
    if args.rev:
        return judge_subjects(ROOT, [(args.rev, args.rev)], f"SUBJECT: {args.rev}'s tree, from git objects")
    raw = os.environ.get("TRUST_PUSHED_REFS", "")
    if raw.strip():
        return judge_push(ROOT, raw)
    return judge_subjects(ROOT, [("HEAD", "HEAD")],
                          "SUBJECT: HEAD's tree, from git objects (no push in flight: TRUST_PUSHED_REFS unset or "
                          "empty)")


if __name__ == "__main__":
    sys.exit(main())
