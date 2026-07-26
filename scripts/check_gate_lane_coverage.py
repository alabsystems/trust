#!/usr/bin/env python3
"""Every test lane in the tree must be named by the gate manifest.

A lane that exists but appears in no manifest row is a lane nobody runs, and
nothing announces that: the file sits in the tree looking maintained while no
orchestrator ever invokes it. This walks the on-disk lane inventory and fails
when a lane is unnamed, so adding an e2e script, a gate script, a witness or
elide regression, a `scripts/tests/` test, or a compiletest suite forces a
manifest row in the same change.

Coverage is literal by default: a lane is covered when its repo-relative path
appears verbatim in some row's command. Lanes reached through an aggregate
(a glob runner, a `targo trust` subcommand) are covered by naming that
aggregate in `INDIRECT` below, which keeps the indirection written down instead
of inferred. `DOC_ENFORCEMENT_LANES` adds one more class: a document that claims
a test keeps it honest must name a test that a manifest row actually runs.

It also validates the manifest's own shape: six pipe-separated columns, a
recognized profile set, and a `last_green` that is either `never` or an ISO
date that is not in the future.

Usage:
    scripts/check_gate_lane_coverage.py
    scripts/check_gate_lane_coverage.py --list-uncovered

Exit codes:
    0   every lane is named and every row is well-formed
    1   an unnamed lane or a malformed row

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import re
import sys
from datetime import date, datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
HARNESS = REPO_ROOT / "tests" / "run_trust_comprehensive_harness.sh"

KNOWN_PROFILES = {"all", "manifest", "fast", "quick", "suites", "slow", "release"}

# Lanes that no row names directly, each with the aggregate that does run them.
# A lane belongs here only when the aggregate genuinely executes it; the point
# of the table is that the indirection is stated, not that the lane is excused.
INDIRECT: dict[str, str] = {
    # The whole `tests/e2e_*.sh` corpus runs as one lane.
    "tests/e2e_*.sh": "scripts/run_e2e_shell_corpus.sh",
    # `scripts/tests/*` run as one lane.
    "scripts/tests/*": "scripts/check_script_tests.sh",
    # The corpus fetch is the first thing the calibration lane does; the
    # payload is external, so it cannot be a gate of its own.
    "scripts/js262/fetch_corpus.sh": "scripts/js262/calibrate.sh",
}

# Documents that name a test as the thing keeping them true, mapped to that
# test's file and the cargo package that owns it. A claim of the form "this test
# fails if the document drifts" is worth exactly as much as whatever runs the
# test, and docs/TCB.md carried that claim while its test sat in no manifest row
# at all (found 2026-07-25). Both halves are closed here: the document must
# still name the file, and some row must run it. A cargo test target is
# addressed by package plus `--test` selector rather than by path, so this class
# is matched on the selector instead of the literal-path rule used above.
DOC_ENFORCEMENT_LANES: dict[str, tuple[str, str]] = {
    "docs/TCB.md": (
        "crates/trust-integration-tests/tests/tcb_document_exhaustiveness.rs",
        "trust-integration-tests",
    ),
}

# Compiletest suites are directories under `tests/`; these are not suites.
NON_SUITE_TEST_DIRS = {
    "auxiliary",
    "compat",
    "crashes",
    "fixtures",
    "js262",
    "trust-added",
    "trust-comprehensive",
    "trust-elide",
    "trust-falsification",
    "trust-witness",
    "ts-corpus",
    "ts-transform-corpus",
    "upstream-rust",
}


def manifest_rows() -> list[list[str]]:
    """The manifest rows, read out of `emit_gate_manifest`'s quoted heredoc.

    Read rather than executed: the harness runs gates when sourced, and this
    check must be able to inspect the manifest without running anything.
    """
    text = HARNESS.read_text(encoding="utf-8")
    start = text.index("emit_gate_manifest() {")
    body = text[text.index("<<'EOF'", start) + len("<<'EOF'") : text.index("\nEOF\n", start)]
    return [line.split("|") for line in body.strip("\n").split("\n") if line.strip()]


def lane_inventory() -> dict[str, list[Path]]:
    """Every runnable lane in the tree, grouped by the class it belongs to."""
    tests = REPO_ROOT / "tests"
    scripts = REPO_ROOT / "scripts"
    inventory: dict[str, list[Path]] = {
        "e2e": sorted(tests.glob("e2e_*.sh")),
        "gate-script": sorted(scripts.glob("trust_*_gate.sh")),
        "script-test": sorted(
            p for p in scripts.glob("tests/*") if p.suffix in (".py", ".sh")
        ),
        "witness": sorted((tests / "trust-witness").glob("*.py")),
        "elide": sorted((tests / "trust-elide").glob("*.py")),
        "suite": sorted(
            p
            for p in tests.iterdir()
            if p.is_dir() and p.name not in NON_SUITE_TEST_DIRS
        ),
        "orchestrator": sorted(tests.glob("run_trust_*_suite.sh")),
        "js262": sorted((scripts / "js262").glob("*.sh")),
    }
    # `tests/crashes` is a compiletest suite despite sitting in the exclusion
    # list above, which exists to keep ledger and fixture directories out.
    inventory["suite"].append(tests / "crashes")
    inventory["suite"].sort()
    return inventory


def check() -> tuple[list[str], list[str]]:
    errors: list[str] = []
    uncovered: list[str] = []
    rows = manifest_rows()
    if not rows:
        return (["gate manifest is empty"], [])

    today = datetime.now(timezone.utc).date()
    seen_ids: set[str] = set()
    for row in rows:
        if len(row) != 6:
            errors.append(f"row has {len(row)} columns, expected 6: {'|'.join(row)}")
            continue
        gate_id, profiles, _category, required, last_green, _command = row
        if gate_id in seen_ids:
            errors.append(f"{gate_id}: duplicate gate id")
        seen_ids.add(gate_id)
        for profile in profiles.split(","):
            if profile not in KNOWN_PROFILES:
                errors.append(f"{gate_id}: unknown profile {profile!r}")
        if required not in ("true", "false"):
            errors.append(f"{gate_id}: required must be true/false, got {required!r}")
        if last_green != "never":
            if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", last_green):
                errors.append(
                    f"{gate_id}: last_green must be `never` or ISO date, got {last_green!r}"
                )
            else:
                recorded = date.fromisoformat(last_green)
                if recorded > today:
                    errors.append(
                        f"{gate_id}: last_green {last_green} is in the future; a gate "
                        "cannot have passed on a day that has not happened"
                    )

    command_list = [row[-1] for row in rows if len(row) == 6]
    commands = "\n".join(command_list)
    for aggregate in INDIRECT.values():
        if aggregate not in commands:
            errors.append(
                f"{aggregate} is the declared aggregate for an indirect lane class "
                "but no manifest row runs it"
            )

    indirect_classes = {
        "e2e": "tests/e2e_*.sh",
        "script-test": "scripts/tests/*",
    }
    for lane_class, lanes in lane_inventory().items():
        for lane in lanes:
            rel = lane.relative_to(REPO_ROOT).as_posix()
            if rel in commands:
                continue
            if lane_class in indirect_classes:
                continue
            if rel in INDIRECT:
                continue
            uncovered.append(f"{lane_class}: {rel}")

    for doc, (test_path, package) in DOC_ENFORCEMENT_LANES.items():
        doc_file = REPO_ROOT / doc
        test_file = REPO_ROOT / test_path
        if not doc_file.exists():
            errors.append(f"{doc}: declared doc-enforcement lane, but the document is gone")
            continue
        if not test_file.exists():
            errors.append(f"{doc}: enforcing test {test_path} does not exist")
            continue
        if test_path not in doc_file.read_text(encoding="utf-8"):
            errors.append(
                f"{doc}: no longer names {test_path} as the test that keeps it true; "
                "either restore the claim or drop the pair from DOC_ENFORCEMENT_LANES"
            )
        selector = f"--test {test_file.stem}"
        if not any(
            selector in command and f"-p {package}" in command for command in command_list
        ):
            uncovered.append(f"doc-enforcement ({doc}): {test_path}")

    return (errors, uncovered)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--list-uncovered",
        action="store_true",
        help="Print uncovered lanes and exit 0; for triage, not for gating.",
    )
    args = parser.parse_args()

    errors, uncovered = check()

    if args.list_uncovered:
        for lane in uncovered:
            print(lane)
        return 0

    if errors:
        print("GATE MANIFEST MALFORMED:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
    if uncovered:
        print("LANES IN NO MANIFEST ROW:", file=sys.stderr)
        for lane in uncovered:
            print(f"  {lane}", file=sys.stderr)
        print(
            "\nEach lane above exists in the tree and no gate runs it. Add a row to\n"
            "`emit_gate_manifest` in tests/run_trust_comprehensive_harness.sh, or add\n"
            "the lane to `INDIRECT` naming the aggregate that already runs it.",
            file=sys.stderr,
        )
    if errors or uncovered:
        return 1

    print(
        "GATE LANE COVERAGE OK: every e2e, gate script, script test, witness/elide "
        "regression, compiletest suite, orchestrator, js262 lane, and declared "
        "doc-enforcement test is named by the gate manifest."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
