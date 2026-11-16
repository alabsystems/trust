#!/usr/bin/env python3
"""Check executed battery rows against the independently discovered fixtures.

This checks coverage only, never compiler correctness or row verdicts. A full
run must visit every fixture exactly once. Filtered runs are explicitly partial
and must still execute at least one existing fixture without duplicates.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import sys


def fixture_names(rows_dir: Path) -> set[str]:
    # ir-audit contains retained reference measurements, not a source program.
    return {
        path.name for path in rows_dir.iterdir()
        if path.is_dir() and path.name != "ir-audit"
        and (re.match(r"r\d+_", path.name) or path.name.startswith("ir-"))
    }


def coverage_errors(expected: set[str], executed: list[str], *, only: str = "",
                    lane: str = "") -> list[str]:
    errors = []
    actual = set(executed)
    if not expected:
        errors.append("fixture inventory is empty")
    if not executed:
        errors.append("no fixture rows executed")
    duplicates = sorted(name for name, count in Counter(executed).items() if count != 1)
    if duplicates:
        errors.append("duplicate rows: " + ", ".join(duplicates))
    unknown = sorted(actual - expected)
    if unknown:
        errors.append("rows without fixture directories: " + ", ".join(unknown))
    if only:
        if only not in expected:
            errors.append("unknown --only fixture: " + only)
        if actual != {only}:
            errors.append("--only must execute exactly " + only)
    elif not lane:
        missing = sorted(expected - actual)
        if missing:
            errors.append("unexecuted fixtures: " + ", ".join(missing))
    elif lane == "trustc-ir":
        selected = {name for name in expected if name.startswith("ir-")}
        if actual != selected:
            errors.append("trustc-ir lane differs from its fixture inventory; missing="
                          + ",".join(sorted(selected - actual)) + "; extra="
                          + ",".join(sorted(actual - selected)))
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows-dir", type=Path, required=True)
    parser.add_argument("--only", default="")
    parser.add_argument("--lane", default="")
    args = parser.parse_args()
    try:
        expected = fixture_names(args.rows_dir)
    except OSError as error:
        print("battery inventory: " + str(error), file=sys.stderr)
        return 1
    executed = [line.strip() for line in sys.stdin if line.strip()]
    errors = coverage_errors(expected, executed, only=args.only, lane=args.lane)
    for error in errors:
        print("battery inventory: " + error, file=sys.stderr)
    if errors:
        return 1
    scope = "partial (filtered)" if args.only or args.lane else "full"
    print(f"battery inventory: {scope}, {len(executed)}/{len(expected)} fixtures executed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
