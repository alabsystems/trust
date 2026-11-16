#!/usr/bin/env python3
"""Channel-C census: what probe channel C says about every codegen item of a corpus.

Step 2 increment 4d, sub-step 4d.0a (docs/design/2026-10-08-step2-inc4d-shims-plan.md
§1(d)). Probe channel C (`-Ztrust-instance-flip-probe=*`, crates/trust-thir-lower/src/
instance_probe.rs `channel_c`) prints one `TRUST-WALLA-PROBE C sym=` row per `MonoItem::Fn`
the collector hands codegen: its instance kind (`kind=item`, `kind=shim-clone`, ...), the
instance-keyed producer's route (`route=thir|mir|pre-route`), the result, and the optional
columns (`drops=` for a local item, `glue=` for a drop-glue item, `shim=` from 4d.1, `rmeta=`
for an upstream item). This script runs a stage-1 `rustc` over a list of files with the flags
of tests/run-make/trust-cg-f1-shims's Part A and aggregates those rows into JSON, so the shim
population increment 4d must retire is a measured number, not a guess.

The flags are fixed (`FLAGS`): `-Copt-level=0 -Ccodegen-units=1 -Cpanic=abort
-Ztrust-verify=off -Ztrust-ir-lower -Ztrust-instance-flip-probe=*`, plus `--emit=obj` (channel
C runs in codegen; nothing links). A file's crate type is the one it would compile as: its own
`#![crate_type = ..]` if it has one, a binary if it defines `fn main`, a library otherwise. Its
`//@ edition:` directive is honoured (a range's lower bound; 2021 when absent); every other
directive (`aux-build`, `compile-flags`, `revisions`) is NOT, so a file that needs one may fail
to compile, and is counted as such. A file that compiles but prints no channel-C summary is
counted separately: the probe did not run for it, which is not the same as "no rows". A binary
carries the runtime's own shims (`std::rt::lang_start`'s closure through a `dyn Fn` vtable, and
`main` called through `FnOnce`): read per-kind counts with that in mind.

It changes nothing it measures: the probe installs nothing and changes no emitted code.

USAGE
-----
    channel_c_survey.py --rustc build/<host>/stage1/bin/rustc --out census.json \\
        [--jobs 4] [--timeout 600] [--git-files-at REV] FILE_OR_DIR...

A directory argument contributes its top-level `*.rs` files. `--git-files-at REV` keeps only
the files that existed at REV (the 980-file corpus of 4c's census is `tests/ui/drop` +
`tests/ui/trust` at af0d9d943a). Exit status: 0 when at least one file was probed, 1 when none
was (a vacuous census is not a result), 2 on a usage error.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import argparse
import collections
import concurrent.futures
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Callable, Iterable, Optional

FLAGS = [
    "-Copt-level=0",
    "-Ccodegen-units=1",
    "-Cpanic=abort",
    "-Ztrust-verify=off",
    "-Ztrust-ir-lower",
    "-Ztrust-instance-flip-probe=*",
]

ROW_PREFIX = "TRUST-WALLA-PROBE C sym="
SUMMARY_PREFIX = "TRUST-WALLA-PROBE C summary "
# The optional columns, in the order channel C prints them, then the def path. A column's value
# runs to the next column key: a refusal class may contain spaces
# (`refused(LaneRefused("opaque collapse"))`).
OPTIONAL_COLUMNS = ("drops", "glue", "shim", "rmeta")
TAIL_KEYS = OPTIONAL_COLUMNS + ("def",)

_HEAD = re.compile(
    r"^TRUST-WALLA-PROBE C sym=(?P<sym>\S+) kind=(?P<kind>\S+) local=(?P<local>\S+) "
    r"route=(?P<route>\S+) result=(?P<rest>.*)$"
)
_EDITION = re.compile(r"^\s*//@\s*edition\s*:\s*(\S+)", re.MULTILINE)
_CRATE_TYPE_ATTR = re.compile(r"#!\[\s*crate_type\s*=")
_FN_MAIN = re.compile(r"^\s*(?:pub\s+)?(?:async\s+)?fn\s+main\s*\(", re.MULTILINE)


def parse_row(line: str) -> dict | None:
    """One channel-C row as a dict, or None when `line` is not a row.

    Keys: sym, kind, local, route, result, and each optional column present (drops, glue,
    shim, rmeta), plus def (the def path and the args text, verbatim).
    """
    match = _HEAD.match(line.rstrip("\n"))
    if not match:
        return None
    row = {k: match.group(k) for k in ("sym", "kind", "local", "route")}
    rest = match.group("rest")
    # Cut `rest` at each ` <key>=` that is present, in print order.
    cuts = []
    search_from = 0
    for key in TAIL_KEYS:
        at = rest.find(f" {key}=", search_from)
        if at >= 0:
            cuts.append((at, key))
            search_from = at + 1
    row["result"] = rest[: cuts[0][0]] if cuts else rest
    for index, (at, key) in enumerate(cuts):
        end = cuts[index + 1][0] if index + 1 < len(cuts) else len(rest)
        row[key] = rest[at + len(key) + 2 : end]
    return row


def parse_summary(line: str) -> dict[str, int] | None:
    """The channel-C summary line's integer fields, or None when `line` is not one."""
    if not line.startswith(SUMMARY_PREFIX):
        return None
    fields = {}
    for token in line[len(SUMMARY_PREFIX) :].split():
        key, sep, value = token.partition("=")
        if sep and value.isdigit():
            fields[key] = int(value)
    return fields


def parse_stderr(stderr: str) -> tuple[list[dict], dict[str, int] | None]:
    """Every channel-C row of one compile's stderr, and its summary (None if it printed none)."""
    rows, summary = [], None
    for line in stderr.splitlines():
        if line.startswith(ROW_PREFIX):
            row = parse_row(line)
            if row is not None:
                rows.append(row)
        elif line.startswith(SUMMARY_PREFIX):
            summary = parse_summary(line)
    return rows, summary


def crate_type_args(source: str) -> list[str]:
    """The `--crate-type` the file would compile as: its own attribute, else bin with a
    `fn main`, else lib."""
    if _CRATE_TYPE_ATTR.search(source) or _FN_MAIN.search(source):
        return []
    return ["--crate-type=lib"]


def edition_of(source: str) -> str:
    """The `//@ edition:` directive's edition; a range (`2015..2021`, `2021..`) gives its
    lower bound, an open lower bound (`..2021`) 2015; 2021 when there is no directive."""
    match = _EDITION.search(source)
    if not match:
        return "2021"
    edition = match.group(1)
    if ".." in edition:
        return edition.split("..", 1)[0] or "2015"
    return edition


def command_for(rustc: str, path: Path, out_dir: str) -> list[str]:
    source = path.read_text(encoding="utf-8", errors="replace")
    return (
        [rustc, str(path), f"--edition={edition_of(source)}"]
        + crate_type_args(source)
        + FLAGS
        + ["--emit=obj", "--out-dir", out_dir]
    )


# A runtime alias, so no `X | None` here: plain `python3` is 3.9 on the maintainer box
# (scripts/tests/python_floor_test.py).
Runner = Callable[[list[str], int], tuple[Optional[int], str]]


def run_rustc(cmd: list[str], timeout: int) -> tuple[int | None, str]:
    """Run one compile; (exit status or None on timeout, stderr)."""
    try:
        done = subprocess.run(
            cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
            timeout=timeout, check=False,
        )
    except subprocess.TimeoutExpired:
        return None, ""
    return done.returncode, done.stderr.decode("utf-8", errors="replace")


def survey_file(rustc: str, path: Path, timeout: int, runner: Runner) -> dict:
    with tempfile.TemporaryDirectory(prefix="channel-c-") as out_dir:
        status, stderr = runner(command_for(rustc, path, out_dir), timeout)
    rows, summary = parse_stderr(stderr)
    if status is None:
        outcome = "timeout"
    elif summary is not None:
        outcome = "probed"
    elif status == 0:
        outcome = "no-probe-output"
    else:
        outcome = "compile-failed"
    return {"file": str(path), "status": status, "outcome": outcome, "rows": rows,
            "summary": summary}


def aggregate(results: Iterable[dict], keep_rows: bool = False) -> dict:
    """The census: counts over every row of every probed file, keyed for the plan's tables.
    With `keep_rows`, each per-file entry also carries its parsed rows (to re-aggregate a
    subset later)."""
    results = sorted(results, key=lambda r: r["file"])
    outcomes = collections.Counter(r["outcome"] for r in results)
    by_kind = collections.Counter()
    by_kind_route_result = collections.Counter()
    by_column = {column: collections.Counter() for column in OPTIONAL_COLUMNS}
    summary_totals = collections.Counter()
    files_by_kind: dict[str, set[str]] = collections.defaultdict(set)
    per_file = []
    for result in results:
        kinds = collections.Counter()
        for row in result["rows"]:
            kind = row["kind"]
            kinds[kind] += 1
            by_kind[kind] += 1
            by_kind_route_result[f"{kind}|{row['route']}|{row['result']}"] += 1
            for column in OPTIONAL_COLUMNS:
                if column in row:
                    by_column[column][f"{kind}|{row[column]}"] += 1
            files_by_kind[kind].add(result["file"])
        if result["summary"]:
            summary_totals.update(result["summary"])
        entry = {"file": result["file"], "outcome": result["outcome"],
                 "status": result["status"], "rows": len(result["rows"]),
                 "kinds": dict(sorted(kinds.items()))}
        if keep_rows:
            entry["row_list"] = result["rows"]
        per_file.append(entry)
    shim_kinds = sorted(k for k in by_kind if k.startswith("shim-"))
    return {
        "flags": FLAGS + ["--emit=obj"],
        "files": len(results),
        "outcomes": dict(sorted(outcomes.items())),
        "rows": sum(by_kind.values()),
        "by_kind": dict(sorted(by_kind.items())),
        "by_kind_route_result": dict(sorted(by_kind_route_result.items())),
        **{f"by_kind_{c}": dict(sorted(by_column[c].items())) for c in OPTIONAL_COLUMNS},
        "shim_kinds": shim_kinds,
        "files_by_shim_kind": {k: len(files_by_kind[k]) for k in shim_kinds},
        "summary_totals": dict(sorted(summary_totals.items())),
        "per_file": per_file,
    }


def expand(paths: Iterable[str]) -> list[Path]:
    files = []
    for name in paths:
        path = Path(name)
        if path.is_dir():
            files.extend(sorted(p for p in path.glob("*.rs") if p.is_file()))
        elif path.is_file():
            files.append(path)
        else:
            raise FileNotFoundError(name)
    return files


def files_at(rev: str, files: list[Path]) -> list[Path]:
    """The members of `files` that exist at git revision `rev`."""
    listed = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", rev], check=True, capture_output=True, text=True,
    ).stdout.split("\n")
    present = set(listed)
    root = Path(subprocess.run(["git", "rev-parse", "--show-toplevel"], check=True,
                               capture_output=True, text=True).stdout.strip())
    return [f for f in files if str(f.resolve().relative_to(root)) in present]


def survey(rustc: str, files: list[Path], jobs: int, timeout: int,
           runner: Runner = run_rustc, keep_rows: bool = False) -> dict:
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        results = list(pool.map(lambda f: survey_file(rustc, f, timeout, runner), files))
    census = aggregate(results, keep_rows)
    census["rustc"] = rustc
    return census


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("paths", nargs="+", help="files, or directories of top-level *.rs")
    parser.add_argument("--rustc", required=True, help="the stage-1 rustc to probe with")
    parser.add_argument("--out", required=True, help="where to write the census JSON")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=600, help="seconds per file")
    parser.add_argument("--git-files-at", metavar="REV",
                        help="keep only the files that existed at this git revision")
    parser.add_argument("--keep-rows", action="store_true",
                        help="store each file's parsed rows in the JSON (per_file[].row_list)")
    args = parser.parse_args(argv)
    try:
        files = expand(args.paths)
    except FileNotFoundError as missing:
        print(f"channel_c_survey: no such file or directory: {missing}", file=sys.stderr)
        return 2
    if args.git_files_at:
        files = files_at(args.git_files_at, files)
    if not files:
        print("channel_c_survey: no input files", file=sys.stderr)
        return 2
    census = survey(args.rustc, files, args.jobs, args.timeout, keep_rows=args.keep_rows)
    Path(args.out).write_text(json.dumps(census, indent=1, sort_keys=False) + "\n")
    probed = census["outcomes"].get("probed", 0)
    print(f"channel_c_survey: {len(files)} files, {probed} probed, {census['rows']} rows; "
          f"shim kinds: {census['files_by_shim_kind']}; wrote {args.out}")
    return 0 if probed else 1


if __name__ == "__main__":
    sys.exit(main())
