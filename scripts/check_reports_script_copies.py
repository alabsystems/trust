#!/usr/bin/env python3
"""Refuse a tracked file under reports/ that is a byte-identical copy of a live script.

A session archive that copies `scripts/…` verbatim adds nothing that `git log`
does not already keep, and a reader who finds the copy cannot tell whether it
is the live gate or a frozen one. On 2026-09-23 three such copies were found
under `reports/2026-09-17-consolidation-checkpoint/native-rustdoc-alias01/
source/scripts/`; that directory went with the rest of the 2026-09-17/18
session residue on 2026-09-25. This check keeps the
class from coming back.

"Live script" means a tracked, non-empty blob outside `reports/` that is
executable (mode 100755) or whose name ends in `.sh`, `.py` or `.pl`. Data
files that a script reads (such as `scripts/*.txt` manifests) are not
scripts. Identity is the git blob id in the index, so the check covers exactly
what would be committed. The COPY's mode is ignored, because an archived copy
loses the executable bit and is still a copy.

Exit 0 when there are no copies, and 1 (listing each one) when there are.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

EMPTY_BLOB = "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"
SCRIPT_SUFFIXES = (".sh", ".py", ".pl")


def is_live_script(path: str, mode: str) -> bool:
    if path.startswith("reports/"):
        return False
    return mode == "100755" or path.endswith(SCRIPT_SUFFIXES)


def index_blobs(repo: Path) -> list[tuple[str, str, str]]:
    out = subprocess.run(
        ["git", "-C", str(repo), "ls-files", "-s", "-z"],
        check=True,
        capture_output=True,
    ).stdout
    rows = []
    for record in out.split(b"\0"):
        if not record:
            continue
        meta, _, path = record.partition(b"\t")
        mode, sha, _stage = meta.decode().split()
        if mode == "160000":  # gitlink, not a blob
            continue
        rows.append((path.decode("utf-8", "surrogateescape"), sha, mode))
    return rows


def find_copies(rows: list[tuple[str, str, str]]) -> list[tuple[str, list[str]]]:
    live: dict[str, list[str]] = defaultdict(list)
    for path, sha, mode in rows:
        if sha != EMPTY_BLOB and is_live_script(path, mode):
            live[sha].append(path)
    copies = []
    for path, sha, _mode in rows:
        if path.startswith("reports/") and sha in live:
            copies.append((path, sorted(live[sha])))
    return sorted(copies)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="repository root (default: this script's checkout)",
    )
    args = parser.parse_args(argv)
    copies = find_copies(index_blobs(args.repo))
    if not copies:
        print("reports-script-copies: OK (no tracked reports/ file is a byte copy of a live script)")
        return 0
    for path, originals in copies:
        print(f"reports-script-copies: {path} is byte-identical to {', '.join(originals)}")
    print(
        f"reports-script-copies: FAIL: {len(copies)} copy/copies. Delete them and cite "
        "the live path and blob in the archive instead."
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
