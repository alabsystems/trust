#!/usr/bin/env python3
"""Count the straight-line (scalar, bool) tuple-return leaf shape in a mir-only dump corpus.

This is the runnable form of the yield figures in
`reports/2026-07-28-az-tuple-return-track-b.md` §3. The first draft of that report backed
84/60/24 with a prose filter description only; every other number in the corpus work carries
a command, so this closes the gap.

    python3 scan_tuple_return_leaves.py <dump-dir>

`<dump-dir>` is a directory of `*.json` VerifiableFunction dumps produced by the command in
`PROVENANCE.md`. Output is the four counts the report states, plus the op inventory, so a
re-run can be diffed against the report line by line.

The recognizer-shape filter, stated exactly as the report uses it:
  * CFG is Goto/Return only (no SwitchInt, no Call, no Assert, no Drop);
  * every statement is Use / Cast / BinaryOp / Aggregate;
  * the return statement is `Aggregate(Tuple, [scalar, bool])`.
It is a SHAPE count over the dump — an upper bound on what a witness could reach, never a
claim that those rows certify. See the report's caveat 3.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache 2.0
"""

import json
import pathlib
import sys
from collections import Counter


def _stmt_kind(stmt):
    """The rvalue discriminant of one statement, or None if it is not an Assign."""
    if not isinstance(stmt, dict):
        return None
    rv = stmt.get("Assign", {}).get("rvalue") if "Assign" in stmt else stmt.get("rvalue")
    if isinstance(rv, str):
        return rv
    if isinstance(rv, dict) and rv:
        return next(iter(rv))
    return None


def _terminator_kind(block):
    term = block.get("terminator")
    if isinstance(term, str):
        return term
    if isinstance(term, dict) and term:
        return next(iter(term))
    return None


def classify(doc):
    """Return (is_leaf, n_stmts, ops) for one VerifiableFunction document."""
    body = doc.get("body") or doc
    blocks = body.get("blocks") or body.get("basic_blocks") or []
    ops = Counter()
    stmts_total = 0
    saw_tuple_return = False

    for block in blocks:
        if _terminator_kind(block) not in ("Goto", "Return", None):
            return (False, 0, ops)
        for stmt in block.get("stmts") or block.get("statements") or []:
            kind = _stmt_kind(stmt)
            if kind is None:
                continue
            if kind not in ("Use", "Cast", "BinaryOp", "Aggregate"):
                return (False, 0, ops)
            ops[kind] += 1
            stmts_total += 1
            if kind == "Aggregate":
                saw_tuple_return = True

    return (saw_tuple_return and stmts_total > 0, stmts_total, ops)


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__.strip().splitlines()[0], file=sys.stderr)
        print(f"usage: {sys.argv[0]} <dump-dir>", file=sys.stderr)
        return 2

    root = pathlib.Path(sys.argv[1])
    leaves, by_stmt_count, ops_total = set(), Counter(), Counter()
    seen = set()

    for path in sorted(root.rglob("*.json")):
        try:
            doc = json.loads(path.read_text())
        except (json.JSONDecodeError, UnicodeDecodeError):
            continue
        def_path = doc.get("def_path") or doc.get("function") or path.stem
        seen.add(def_path)
        is_leaf, n_stmts, ops = classify(doc)
        if is_leaf:
            leaves.add(def_path)
            by_stmt_count[n_stmts] += 1
            ops_total.update(ops)

    print(f"unique def_paths in corpus : {len(seen)}")
    print(f"straight-line tuple leaves : {len(leaves)}")
    for n_stmts, count in sorted(by_stmt_count.items()):
        print(f"  {n_stmts}-stmt leaves          : {count}")
    print(f"op inventory               : {dict(sorted(ops_total.items()))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
