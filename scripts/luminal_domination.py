#!/usr/bin/env python3
"""luminal_domination.py — how much of the Luminal compiler Trust has met.

docs/design/2026-11-12-one-software.md names Luminal
(github.com/luminal-ai/luminal) as the complete subset: every capability it has
is a row Trust must meet. This instrument counts the rows.

The ledger is <ledger>/capabilities.json (default tests/luminal-domination):
one row per finding read from Luminal's source at the commit the file names.

  kind      `capability`: something Luminal can do; it is in the denominator.
            `observation`: a fact about Luminal's repository that is not a
            capability (a stale document, a CI arrangement, an absence); it is
            outside the count and carries no package and no exit.
  package   the docs/PLAN.md package (`PKG-U<n>`) that meets a capability row.
            It must be a row of the plan's table.
  luminal_evidence / luminal_validation / luminal_maturity
            where the capability is in Luminal, how Luminal tests it, and how
            mature it is there (`docs-only`: described and not published).
  exit      null until the row is met, then

                {"repo": "trust", "cwd": "<relative path>", "argv": [...],
                 "evidence": "proved" | "sampled" | "refused-by-design",
                 "luminal_oracle": "exact" | "tolerance",
                 "trust_form": "<how Trust's form differs, or empty>"}

            `luminal_oracle` is the filling reviewer's statement of how
            Luminal's own test decides the capability: `exact` (equality, a
            structural check) or `tolerance` (a comparison within an epsilon,
            sampled outputs). `proved` requires `exact`, and an `exact` row
            whose luminal_validation reads as a tolerance comparison
            (TOLERANCE_RE) is refused: the prose can only make the check
            stricter, never stand in for the statement.

            `repo` is `trust` or a sibling's name. A sibling resolves to
            first-party/<repo> when that directory exists, else to the
            directory named by TRUST_SIBLING_<REPO> (upper case, `-` as `_`).

A row is NAMED when its exit is filled. A row is MET only when its command, run
by this invocation, exits 0 and prints the line

    LUMINAL-ROW <id> PASS

on stdout. The line is required because a test sweep can exit 0 with every test
ignored. A reading of source is never an exit, and a named row that was not run
is never counted as met.

Modes:
    (default)        validate the ledger and print how many rows are named. Runs
                     nothing, so it says nothing about how many are met.
    --run            run every named exit and print how many rows are met, split
                     by evidence. Exit 1 if a named row fails.
    --require-all    implies --run; exit 1 unless every capability row is met.
    --by-area        also print the count per area.
    --by-package     also print the count per plan package.
    --package PKG-U<n>
                     (repeatable) consider only the capability rows of these
                     packages: the denominator, the counts, --run and
                     --require-all are theirs alone. This is a package's own
                     exit test. The whole ledger is still validated, and a
                     package no capability row names is an error (exit 2).
    --expect-named N --expect-total M
                     exit 1 unless the ledger has exactly N named rows of M
                     capability rows (the gate manifest's drift pin: a commit
                     that fills a row moves the pin in the same change).

Exit codes: 0 ok; 1 a named row failed, a pin did not match, or --require-all
is not satisfied; 2 the ledger or the plan is invalid, or --package names a
package with no capability row.

What this does NOT establish: that a named command is as strong as Luminal's own
test for that capability (a reviewer judges that when the row is filled; a row
whose Luminal test is a tolerance comparison may not claim `proved`: that
rule is checked here against the row's stated `luminal_oracle`, which a
reviewer can still state wrongly); anything about speed; that a row's package is the
right one (packages were assigned by area with keyword overrides, and the
package that meets a row may correct it); or anything about the observation
rows.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_LEDGER = "tests/luminal-domination"
DEFAULT_PLAN = "docs/PLAN.md"
LEDGER_FILE = "capabilities.json"
SCHEMA = 2
ROW_KEYS = {
    "id",
    "area",
    "kind",
    "package",
    "capability",
    "luminal_evidence",
    "luminal_validation",
    "luminal_maturity",
    "exit",
}
EXIT_KEYS = {"repo", "cwd", "argv", "evidence", "luminal_oracle", "trust_form"}
MATURITIES = ("solid", "partial", "experimental", "docs-only")
KINDS = ("capability", "observation")
EVIDENCE = ("proved", "sampled", "refused-by-design")
ORACLES = ("exact", "tolerance")
# Wording in luminal_validation that describes a tolerance comparison. The
# committed ledger says it as "tolerance", "assert_close at 1e-3", "at <1e-4",
# "(1.5e-7), i.e. an approximation": any one refuses an `exact` oracle.
TOLERANCE_RE = re.compile(
    r"toleran|assert_close|allclose|isclose|approx|\batol\b|\brtol\b|epsilon|\bulps?\b"
    r"|[0-9](?:\.[0-9]+)?e-[0-9]",
    re.IGNORECASE,
)
PACKAGE_RE = re.compile(r"PKG-U[0-9]+")
PLAN_ROW_RE = re.compile(r"^\| (PKG-U[0-9]+) \|", re.MULTILINE)
REPO_NAME_RE = re.compile(r"[a-z0-9][a-z0-9-]*")
NAME = "luminal-domination"
STDOUT_TAIL = 20  # lines of a failed command's captured stdout shown for diagnosis


def plan_packages(plan_path):
    """The PKG-U ids that open a table row of the plan, or an error string."""
    try:
        text = plan_path.read_text(encoding="utf-8")
    except OSError as error:
        return None, f"plan {plan_path}: {error}"
    packages = set(PLAN_ROW_RE.findall(text))
    if not packages:
        return None, f"plan {plan_path}: no table row starts `| PKG-U<n> |`"
    return packages, None


def exit_errors(row):
    """Why this row's filled `exit` is not a valid exit (empty when it is)."""
    exit_ = row["exit"]
    if not isinstance(exit_, dict) or set(exit_) != EXIT_KEYS:
        return [f"exit must be null or an object with keys {sorted(EXIT_KEYS)}"]
    errors = []
    repo = exit_["repo"]
    if not isinstance(repo, str) or not REPO_NAME_RE.fullmatch(repo):
        errors.append(f"exit.repo {repo!r} is not `trust` or a sibling name")
    cwd = exit_["cwd"]
    if not isinstance(cwd, str) or not cwd:
        errors.append("exit.cwd must be a non-empty relative path (`.` for the root)")
    elif Path(cwd).is_absolute() or ".." in Path(cwd).parts:
        errors.append("exit.cwd must be relative and stay inside its repository")
    argv = exit_["argv"]
    if not isinstance(argv, list) or not argv or not all(
        isinstance(arg, str) and arg for arg in argv
    ):
        errors.append("exit.argv must be a non-empty list of non-empty strings")
    evidence, oracle = exit_["evidence"], exit_["luminal_oracle"]
    if not isinstance(evidence, str) or evidence not in EVIDENCE:
        errors.append(f"exit.evidence {evidence!r} is not one of {list(EVIDENCE)}")
    if not isinstance(oracle, str) or oracle not in ORACLES:
        errors.append(f"exit.luminal_oracle {oracle!r} is not one of {list(ORACLES)}")
    else:
        if oracle == "exact" and TOLERANCE_RE.search(row["luminal_validation"]):
            errors.append(
                "exit.luminal_oracle is `exact` but luminal_validation describes a "
                "tolerance comparison"
            )
        if evidence == "proved" and oracle != "exact":
            errors.append(
                "exit.evidence is `proved` but Luminal's test is a tolerance comparison: "
                "a tolerance comparison is sampled evidence, never proof"
            )
    if not isinstance(exit_["trust_form"], str):
        errors.append("exit.trust_form must be a string (empty when the form does not differ)")
    return errors


def load(ledger_dir, plan_path):
    """Read and validate the ledger. Returns (doc, rows, errors)."""
    path = ledger_dir / LEDGER_FILE
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        return {}, [], [f"{path}: {error}"]
    if not isinstance(doc, dict):
        return {}, [], [f"{path}: the top level is not an object"]
    errors = []
    if doc.get("schema") != SCHEMA:
        errors.append(f"schema is {doc.get('schema')!r}, expected {SCHEMA}")
    for key in ("luminal_repository", "luminal_commit"):
        if not isinstance(doc.get(key), str) or not doc[key]:
            errors.append(f"{key} is missing")
    packages, plan_error = plan_packages(plan_path)
    if plan_error:
        errors.append(plan_error)
    rows = doc.get("capabilities")
    if not isinstance(rows, list) or not rows:
        errors.append("capabilities is missing or empty")
        return doc, [], errors
    seen = set()
    unplanned = {}
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"row {index}: not an object")
            continue
        where = f"row {index} ({row.get('id', '?')})"
        if set(row) != ROW_KEYS:
            errors.append(f"{where}: keys are {sorted(row)}, expected {sorted(ROW_KEYS)}")
            continue
        for key in ("id", "area", "capability", "luminal_evidence", "luminal_validation"):
            if not isinstance(row[key], str) or not row[key].strip():
                errors.append(f"{where}: {key} is empty")
                row[key] = ""
        if row["id"] in seen:
            errors.append(f"{where}: duplicate id")
        seen.add(row["id"])
        if not isinstance(row["luminal_maturity"], str) or row["luminal_maturity"] not in MATURITIES:
            errors.append(f"{where}: luminal_maturity {row['luminal_maturity']!r}")
        if not isinstance(row["kind"], str) or row["kind"] not in KINDS:
            errors.append(f"{where}: kind {row['kind']!r} is not one of {list(KINDS)}")
            continue
        if row["kind"] == "observation":
            if row["package"] is not None:
                errors.append(f"{where}: an observation row has no package")
            if row["exit"] is not None:
                errors.append(f"{where}: an observation row has no exit (it is not counted)")
            continue
        package = row["package"]
        if not isinstance(package, str) or not PACKAGE_RE.fullmatch(package):
            errors.append(f"{where}: package {package!r} is not `PKG-U<n>`")
        elif packages is not None and package not in packages:
            unplanned.setdefault(package, []).append(row["id"])
        if row["exit"] is not None:
            errors.extend(f"{where}: {error}" for error in exit_errors(row))
    for package in sorted(unplanned, key=lambda name: (len(name), name)):
        ids = unplanned[package]
        errors.append(
            f"package {package} is not a table row of {plan_path}: {len(ids)} rows name it "
            f"(first: {ids[0]})"
        )
    return doc, rows, errors


def sibling_root(repo):
    """The checkout of `repo`, or (None, why)."""
    if repo == "trust":
        return REPO, None
    pinned = REPO / "first-party" / repo
    if pinned.is_dir():
        return pinned, None
    variable = "TRUST_SIBLING_" + repo.upper().replace("-", "_")
    named = os.environ.get(variable)
    if named and Path(named).is_dir():
        return Path(named), None
    return None, f"sibling `{repo}` is not at first-party/{repo} and {variable} names no directory"


def run_exit(row):
    """Run one named exit. Returns None when the row is met, else why not."""
    exit_ = row["exit"]
    root, why = sibling_root(exit_["repo"])
    if root is None:
        return why
    cwd = root / exit_["cwd"]
    if not cwd.is_dir():
        return f"exit.cwd {exit_['cwd']!r} is not a directory of `{exit_['repo']}`"
    try:
        result = subprocess.run(
            exit_["argv"],
            cwd=cwd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            text=True,
            errors="replace",
            check=False,
        )
    except OSError as error:
        return f"the command did not start: {error}"
    marker = f"LUMINAL-ROW {row['id']} PASS"
    lines = result.stdout.splitlines()
    if result.returncode == 0 and marker in (line.strip() for line in lines):
        return None
    for line in lines[-STDOUT_TAIL:]:
        print(f"{NAME}: {row['id']}: stdout: {line}", file=sys.stderr)
    if result.returncode != 0:
        return f"the command exited {result.returncode}"
    return f"the command exited 0 without printing `{marker}`"


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        epilog="See the module docstring for the ledger format and what a count means.",
    )
    parser.add_argument("--ledger", default=DEFAULT_LEDGER, metavar="DIR")
    parser.add_argument("--plan", default=DEFAULT_PLAN, metavar="PATH")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--require-all", action="store_true")
    parser.add_argument("--by-area", action="store_true")
    parser.add_argument("--by-package", action="store_true")
    parser.add_argument("--package", action="append", default=[], metavar="PKG-U<n>")
    parser.add_argument("--expect-named", type=int, metavar="N")
    parser.add_argument("--expect-total", type=int, metavar="M")
    args = parser.parse_args(argv)
    if (args.expect_named is None) != (args.expect_total is None):
        parser.error("--expect-named and --expect-total are given together")
    run = args.run or args.require_all

    doc, rows, errors = load(REPO / args.ledger, REPO / args.plan)
    if errors:
        for error in errors:
            print(f"{NAME}: INVALID: {error}", file=sys.stderr)
        return 2

    capabilities = [row for row in rows if row["kind"] == "capability"]
    observations = len(rows) - len(capabilities)
    scope = ""
    if args.package:
        wanted_packages = sorted(set(args.package), key=lambda name: (len(name), name))
        empty = [name for name in wanted_packages
                 if not any(row["package"] == name for row in capabilities)]
        if empty:
            for name in empty:
                print(f"{NAME}: INVALID: --package {name}: no capability row names it",
                      file=sys.stderr)
            return 2
        capabilities = [row for row in capabilities if row["package"] in wanted_packages]
        scope = " of " + ", ".join(wanted_packages)
    named = [row for row in capabilities if row["exit"] is not None]
    unpublished = sum(1 for row in capabilities if row["luminal_maturity"] == "docs-only")
    total = len(capabilities)
    tail = (
        f"{observations} observation rows are outside the count; {unpublished} of the "
        f"{total} are described by Luminal and not published (Luminal {doc['luminal_commit']})"
    )
    rows_text = f"capability rows{scope}"

    status = 0
    if args.expect_named is not None and (args.expect_named, args.expect_total) != (
        len(named),
        total,
    ):
        print(
            f"{NAME}: PIN MISMATCH: expected named {args.expect_named} of "
            f"{args.expect_total}, the ledger has named {len(named)} of {total}; the "
            "commit that fills, empties, adds or removes a row moves the pin with it",
            file=sys.stderr,
        )
        status = 1

    failed = {}
    if run:
        for row in named:
            sys.stdout.flush()
            why = run_exit(row)
            if why is not None:
                failed[row["id"]] = why
        counted = [row for row in named if row["id"] not in failed]
        by_evidence = Counter(row["exit"]["evidence"] for row in counted)
        split = ", ".join(f"{kind} {by_evidence[kind]}" for kind in EVIDENCE)
        print(f"{NAME}: met {len(counted)} of {total} {rows_text} ({split}); {tail}")
    else:
        counted = named
        print(
            f"{NAME}: named {len(named)} of {total} {rows_text} "
            f"(exit commands not run; met is unknown); {tail}"
        )

    for wanted, key in ((args.by_area, "area"), (args.by_package, "package")):
        if not wanted:
            continue
        totals = Counter(row[key] for row in capabilities)
        done = Counter(row[key] for row in counted)
        order = sorted(totals, key=lambda name: (len(name), name) if key == "package" else name)
        for group in order:
            print(f"  {group}: {done[group]} of {totals[group]}")

    for row_id, why in failed.items():
        print(f"{NAME}: NOT MET: {row_id}: {why}", file=sys.stderr)
    if failed:
        status = 1
    if args.require_all and len(counted) != total:
        print(
            f"{NAME}: --require-all: {total - len(counted)} of {total} {rows_text} are not met",
            file=sys.stderr,
        )
        status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
