#!/usr/bin/env python3
"""Reproduce the seal-line audit's mechanical classes and check its .tsv covers the line.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

SEAL-1 clause 4 (docs/DECISION_QUEUE.md) and SEAL-1-P5A require an audit of every commit
on the deployed seal's line that main does not contain: `git rev-list MAIN..SEAL`. The
record is docs/audits/2026-10-17-seal-line-audit.md, with one row per commit in
docs/audits/2026-10-17-seal-line-audit.tsv. People read and judge each row; this script
re-derives the part of the judgement a machine can, and checks the table against it.

    python3 scripts/seal_line_audit.py [--main REF] [--seal REF] [--tsv PATH]

Defaults are the refs the 2026-10-17 record was judged at: main `dfd8b72138d` and the seal
`321aaeda754` (the local tag `atpkg-trust-9192-seal`, aterm's store trust 9192). Git only:
it reads the object store and runs `git log`, `git patch-id`, `git rev-list` and
`git merge-base`. It builds, fetches and changes nothing. The .tsv path is relative to
the top of the checkout.

THE MECHANICAL CLASSES. The main side is every non-merge commit reachable from MAIN and
not from the fork point, `git merge-base MAIN <oldest seal-line commit>`. That includes
the main commits the seal line merged back in, which are on main too.

  MERGE     the commit has more than one parent. Each other parent is reported with
            whether it is an ancestor of MAIN.
  EMPTY     the commit's tree equals its first parent's tree.
  PATCH-ID  `git patch-id --stable` equals a main commit's.
  LINES     the multiset of changed (+/-) lines, whitespace removed, equals a main
            commit's, though the patch-id differs (the context lines moved). An empty
            change set never matches.
  NAMED     a main commit's message names the seal commit by a prefix of 8 or more
            characters: a `Ported-from:`, cherry-pick or "Recovered from" line, or a
            mention such as a "not ported" record. It is a trace for the reader, not
            a verdict.
  CHERRY    the seal commit's message names its source on main ("cherry-pick <sha>",
            "upstream <sha>", "Ported-from: <sha>"), and that sha is a main commit.
  SUBJECT   a main commit has the same subject line.
  UNTRACED  none of the above: the row rests only on its human reading.

THE CHECKS. Each failure is printed and the exit status is 1:

  * the .tsv's rows are exactly `git rev-list --reverse MAIN..SEAL`, in that order,
    numbered from 1, with no duplicate;
  * every verdict is one of ON-MAIN, SUPERSEDED, DROP-OK, PORT, MEASURE;
  * an EMPTY row is DROP-OK;
  * a row with a PATCH-ID or LINES twin is ON-MAIN or SUPERSEDED, and its evidence names
    one of the twins (a hex prefix of 7 or more characters);
  * every ON-MAIN and SUPERSEDED row's evidence names at least one commit that is an
    ancestor of MAIN, so each "on main" or "superseded by" claim points at main.

PORT and MEASURE rows are open work, not failures of the record: the script lists them,
and clause 4 is met only once each is closed by a main commit (a port, or a measurement
committed as the row's evidence).

A seal that is an ancestor of MAIN has an empty line (the 2026-10-22 addendum,
docs/audits/2026-10-22-seal-line-addendum.md, for trust 15698 `20565c3255`). Then there is
no fork point and nothing to class, the main side is empty, and the table must have no row:
the same checks run over no commit.
"""

from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import re
import subprocess
import sys
import tempfile
from pathlib import Path

DEFAULT_MAIN = "dfd8b72138d"
DEFAULT_SEAL = "321aaeda754"
DEFAULT_TSV = "docs/audits/2026-10-17-seal-line-audit.tsv"
VERDICTS = ("ON-MAIN", "SUPERSEDED", "DROP-OK", "PORT", "MEASURE")
COLUMNS = ("row", "sha", "subject", "verdict", "evidence", "relied_on_by", "port")
HEX = re.compile(r"\b[0-9a-f]{7,40}\b")
SOURCE = re.compile(
    r"(?:cherry[- ]pick(?:ed)?(?: of| from)?(?: commit)?|upstream(?:'s)?|ported[- ]from:?)\s+([0-9a-f]{8,40})\b",
    re.IGNORECASE,
)


def git(*args: str) -> str:
    return subprocess.run(
        ("git", *args), check=True, capture_output=True, text=True, errors="replace"
    ).stdout


def is_ancestor(a: str, b: str) -> bool:
    return (
        subprocess.run(
            ("git", "merge-base", "--is-ancestor", a, b), capture_output=True
        ).returncode
        == 0
    )


def diff_digests(rev_args: list[str]) -> tuple[dict[str, str], dict[str, str]]:
    """One `git log -p` pass: each commit's stable patch-id and its changed-lines digest."""
    log = subprocess.Popen(
        ("git", "log", "-p", "-M", "--no-merges", "--no-color", "--format=commit %H", *rev_args),
        stdout=subprocess.PIPE,
    )
    with tempfile.TemporaryFile() as out:
        pid = subprocess.Popen(("git", "patch-id", "--stable"), stdin=subprocess.PIPE, stdout=out)
        lines_by_commit: dict[str, str] = {}
        current = None
        changed: list[bytes] = []
        in_header = False

        def flush() -> None:
            if current is not None and changed:
                h = hashlib.sha1()
                for line in sorted(changed):
                    h.update(line + b"\n")
                lines_by_commit[current] = h.hexdigest()

        assert log.stdout is not None and pid.stdin is not None
        for raw in log.stdout:
            pid.stdin.write(raw)
            if raw.startswith(b"commit ") and len(raw.split()) == 2:
                flush()
                current = raw.split()[1].decode()
                changed = []
                in_header = False
            elif raw.startswith(b"diff --git "):
                in_header = True
            elif raw.startswith(b"@@"):
                in_header = False
            elif not in_header and raw[:1] in (b"+", b"-"):
                changed.append(raw[:1] + b"".join(raw[1:].split()))
        flush()
        pid.stdin.close()
        if log.wait() != 0 or pid.wait() != 0:
            sys.exit("seal_line_audit: git log -p | git patch-id --stable failed")
        out.seek(0)
        patch_ids = {}
        for line in out.read().decode().splitlines():
            pid_hash, commit = line.split()
            patch_ids[commit] = pid_hash
    return patch_ids, lines_by_commit


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--main", default=DEFAULT_MAIN)
    ap.add_argument("--seal", default=DEFAULT_SEAL)
    ap.add_argument("--tsv", default=DEFAULT_TSV)
    args = ap.parse_args()
    tsv = Path(git("rev-parse", "--show-toplevel").strip()) / args.tsv

    main_sha = git("rev-parse", "--verify", f"{args.main}^{{commit}}").strip()
    seal_sha = git("rev-parse", "--verify", f"{args.seal}^{{commit}}").strip()
    line = git("rev-list", "--reverse", f"{main_sha}..{seal_sha}").split()
    # An empty line (the seal is an ancestor of main) has no oldest commit to fork from;
    # MAIN itself as the fork point makes the main side empty, and the table must be too.
    fork = git("merge-base", main_sha, line[0]).strip() if line else main_sha
    print(f"main {main_sha[:11]}  seal {seal_sha[:11]}  fork point {fork[:11]}")
    print(f"seal line: {len(line)} commits (git rev-list {main_sha[:11]}..{seal_sha[:11]})")

    failures: list[str] = []

    # --- the table -------------------------------------------------------------------
    with open(tsv, newline="") as f:
        reader = csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE)
        if tuple(reader.fieldnames or ()) != COLUMNS:
            failures.append(f"{args.tsv}: columns {reader.fieldnames}, expected {list(COLUMNS)}")
            rows = []
        else:
            rows = list(reader)
    by_sha = {}
    for i, r in enumerate(rows, 1):
        if r["row"] != str(i):
            failures.append(f"row {i}: numbered {r['row']!r}")
        if r["sha"] in by_sha:
            failures.append(f"row {i}: {r['sha']} duplicates row {by_sha[r['sha']]['row']}")
        by_sha[r["sha"]] = r
        if r["verdict"] not in VERDICTS:
            failures.append(f"row {i}: verdict {r['verdict']!r} is not one of {', '.join(VERDICTS)}")
    table_order = [r["sha"] for r in rows]
    missing = [s for s in line if s not in by_sha]
    extra = [s for s in table_order if s not in set(line)]
    for s in missing:
        failures.append(f"{s[:11]} is on the seal line and has no row")
    for s in extra:
        failures.append(f"{s[:11]} has a row and is not on the seal line")
    if not missing and not extra and table_order != line:
        failures.append("rows are not in `git rev-list --reverse` order")

    # --- the mechanical classes ------------------------------------------------------
    main_patch, main_lines = diff_digests([main_sha, f"^{fork}"])
    seal_patch, seal_lines = diff_digests([seal_sha, f"^{main_sha}"])
    patch_to_main = collections.defaultdict(list)
    for c, p in main_patch.items():
        patch_to_main[p].append(c)
    lines_to_main = collections.defaultdict(list)
    for c, d in main_lines.items():
        lines_to_main[d].append(c)

    subjects = collections.defaultdict(list)
    bodies = []
    for rec in git("log", "--no-merges", "--format=%H%x00%s%x00%B%x1e", main_sha, f"^{fork}").split("\x1e"):
        rec = rec.lstrip("\n")
        if not rec:
            continue
        c, subject, body = rec.split("\x00", 2)
        subjects[subject].append(c)
        bodies.append((c, body))
    tokens_by_main = [(c, set(HEX.findall(body))) for c, body in bodies]
    main_set = set(c for c, _ in bodies)

    classes: dict[str, list[str]] = {}
    twins: dict[str, dict[str, list[str]]] = {}
    for s in line:
        parents = git("rev-list", "--parents", "-n", "1", s).split()[1:]
        cls: list[str] = []
        tw: dict[str, list[str]] = {}
        if len(parents) > 1:
            cls.append("MERGE")
            tw["MERGE"] = [
                f"{p[:11]}{'' if is_ancestor(p, main_sha) else ' (not on main)'}" for p in parents[1:]
            ]
        elif git("rev-parse", f"{s}^{{tree}}") == git("rev-parse", f"{parents[0]}^{{tree}}"):
            cls.append("EMPTY")
        if s in seal_patch and patch_to_main.get(seal_patch[s]):
            cls.append("PATCH-ID")
            tw["PATCH-ID"] = patch_to_main[seal_patch[s]]
        elif s in seal_lines and lines_to_main.get(seal_lines[s]):
            cls.append("LINES")
            tw["LINES"] = lines_to_main[seal_lines[s]]
        named = [c for c, toks in tokens_by_main if any(len(t) >= 8 and s.startswith(t) for t in toks)]
        if named:
            cls.append("NAMED")
            tw["NAMED"] = named
        sources = []
        for tok in SOURCE.findall(git("log", "-1", "--format=%B", s)):
            full = subprocess.run(
                ("git", "rev-parse", "--verify", "--quiet", f"{tok}^{{commit}}"),
                capture_output=True, text=True,
            ).stdout.strip()
            if full in main_set:
                sources.append(full)
        if sources:
            cls.append("CHERRY")
            tw["CHERRY"] = sources
        subj = git("log", "-1", "--format=%s", s).rstrip("\n")
        if len(parents) == 1 and subjects.get(subj):
            cls.append("SUBJECT")
            tw["SUBJECT"] = subjects[subj]
        classes[s] = cls or ["UNTRACED"]
        twins[s] = tw

    # --- the checks against the table ------------------------------------------------
    ancestor_cache: dict[str, bool] = {}

    def names_main_commit(text: str) -> list[str]:
        found = []
        for tok in HEX.findall(text):
            if tok not in ancestor_cache:
                full = subprocess.run(
                    ("git", "rev-parse", "--verify", "--quiet", f"{tok}^{{commit}}"),
                    capture_output=True, text=True,
                ).stdout.strip()
                ancestor_cache[tok] = bool(full) and is_ancestor(full, main_sha)
            if ancestor_cache[tok]:
                found.append(tok)
        return found

    for s in line:
        r = by_sha.get(s)
        if r is None:
            continue
        n, verdict, evidence = r["row"], r["verdict"], r["evidence"]
        if "EMPTY" in classes[s] and verdict != "DROP-OK":
            failures.append(f"row {n} {s[:11]}: an empty commit is {verdict}, expected DROP-OK")
        for k in ("PATCH-ID", "LINES"):
            if k in twins[s]:
                if verdict not in ("ON-MAIN", "SUPERSEDED"):
                    failures.append(f"row {n} {s[:11]}: has a {k} twin on main and is {verdict}")
                cited = HEX.findall(evidence)
                if not any(t.startswith(c) for t in twins[s][k] for c in cited):
                    failures.append(
                        f"row {n} {s[:11]}: evidence names none of its {k} twins "
                        f"({', '.join(t[:11] for t in twins[s][k])})"
                    )
        if verdict in ("ON-MAIN", "SUPERSEDED") and not names_main_commit(evidence):
            failures.append(f"row {n} {s[:11]}: {verdict} but the evidence names no ancestor of main")

    # --- report ----------------------------------------------------------------------
    print()
    print("row  sha          verdict     class                     main twins")
    for i, s in enumerate(line, 1):
        verdict = by_sha[s]["verdict"] if s in by_sha else "(no row)"
        tw = "; ".join(
            f"{k} " + ",".join(t if k == "MERGE" else t[:11] for t in v[:3]) + (" …" if len(v) > 3 else "")
            for k, v in twins[s].items()
        )
        print(f"{i:>3}  {s[:11]}  {verdict:<10}  {'+'.join(classes[s]):<24}  {tw}".rstrip())

    print()
    count = collections.Counter()
    for s in line:
        for c in classes[s]:
            count[c] += 1
    traced = [s for s in line if not {"MERGE", "EMPTY", "UNTRACED"} & set(classes[s])]
    print("mechanical classes (a commit can be in several):")
    for c in ("MERGE", "EMPTY", "PATCH-ID", "LINES", "NAMED", "CHERRY", "SUBJECT", "UNTRACED"):
        print(f"  {c:<9} {count[c]:>3}")
    print(f"  traced non-merge commits {len(traced)}, untraced {count['UNTRACED']}, merges {count['MERGE']}, "
          f"empty {count['EMPTY']}: {len(traced) + count['UNTRACED'] + count['MERGE'] + count['EMPTY']} of {len(line)}")
    verdicts = collections.Counter(r["verdict"] for r in rows)
    print("verdicts: " + ", ".join(f"{v} {verdicts[v]}" for v in VERDICTS) + f"; rows {len(rows)}")
    open_rows = [r for r in rows if r["verdict"] in ("PORT", "MEASURE")]
    if open_rows:
        print(f"open (clause 4 is met only when each is closed by a main commit): {len(open_rows)}")
        for r in open_rows:
            print(f"  row {r['row']} {r['sha'][:11]} {r['verdict']}: {r['port']}")

    print()
    if failures:
        for f_ in failures:
            print(f"FAIL: {f_}")
        print(f"seal_line_audit: {len(failures)} failure(s)")
        return 1
    print(f"seal_line_audit: OK, {len(rows)} rows cover the seal line exactly; every check holds")
    return 0


if __name__ == "__main__":
    sys.exit(main())
