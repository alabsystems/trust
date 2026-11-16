#!/usr/bin/env python3
"""Fail-closed gate: every per-test exception row carries exactly one lane.

`tests/upstream-rust/test-exceptions.toml` waives per-test upstream-Rust
failures. Until this gate existed, a row said WHICH test it waived but never
under WHICH verification lane the waived failure was observed, so a waiver
written from a verification-off run could be cited by a run at the shipping
default (`-Ztrust-verify=on -Ztrust-policy=strict`) — where a refutation with a
counterexample hard-fails the build and false refutations are a real class.

This gate makes `lane` REQUIRED. It reads the assignment from the row itself
when the row has one (post-migration; see test-exception-lanes.toml), and
otherwise from the `tests/upstream-rust/test-exception-lanes.toml` sidecar,
which exists only because `TestException` in
`crates/trust-upstream-compat/src/model.rs` is `deny_unknown_fields` and would
reject an inline key today.

Checks, all fail-closed:

  1.  both files parse;
  2.  every exception id has at least one lane assignment, and at most one per
      lane (a MISSING assignment is a failure — that is what "required" means
      here; a test that fails on two lanes is two observations, two rows);
  3.  no lane row names an id that is not in the ledger (a retired row must not
      leave a stale lane claim behind);
  4.  lane is exactly "vanilla", "default" or "verified" — the three compiletest
      lanes (`--trust-vanilla`, no lane flag, `--trust-verified`);
  5.  every assignment carries a YYYY-MM-DD `measured_on` and non-empty
      `evidence` — a lane claim with no observation behind it is the thing this
      gate exists to stop;
  6.  `lane = "verified"` is REFUSED while `verified_lane_available = false`,
      because a lane that cannot be run cannot have produced a measurement;
  7.  the premise behind (6) is RE-DERIVED FROM SOURCE on every run, never
      trusted from the ledger. The gate walks the whole chain that makes
      `x.py test --trust-verified` reach a rustc invocation (compiletest's
      sentinel, flags, `trust_verified()`, the `Verified` arm, the CLI option,
      the mutual exclusion with `--trust-vanilla`, and bootstrap's forwarding).
      A chain that is FULLY present means the lane exists; fully absent means it
      does not; PARTIALLY present is a hard failure, because a half-wired lane
      is the one state that can accept the flag and still not verify. It also
      re-asserts the DEFAULT lane's own predicate --
      `rustc_supports_trust_verification || trust_vanilla()` -- because every
      existing `vanilla` row is a claim about that predicate;
  7b. `verified_lane_available = true` is refused when the source says the lane
      is not there, and must name its basis in `verified_lane_landed_by`;
  8.  an inline `lane` on a row (post-migration) must agree with the sidecar
      when both are present.

`--run -- <x.py test command>` is how the harness `suite.*` rows honor the
ledger. After the checks pass, it runs the command with `--skip <path>` for
exactly the rows that are active, unexpired, of a kind that nets a failure,
observed on the lane the COMMAND runs on (read from its own lane flag), and
under one of its `tests/...` paths. Any other failure still fails the command.
When the command passes, each skipped test is run alone; one that passes gets
a `WARN:` line, because a waiver that covers no failure should be retired, not
left to expire. `--dry-run` prints the command and runs nothing.

Usage:
    tests/upstream-rust/check_exception_lanes.py
    tests/upstream-rust/check_exception_lanes.py --json
    tests/upstream-rust/check_exception_lanes.py --self-test
    tests/upstream-rust/check_exception_lanes.py --run [--dry-run] -- python3 x.py test ...

Exit codes:
    0   every active exception row carries a well-formed lane assignment
        (--run: the command's own exit status)
    1   one or more findings (release gate fail)
    2   --run was given something other than an `x.py test` command

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Sequence


REPO_ROOT = Path(__file__).resolve().parents[2]
LEDGER = REPO_ROOT / "tests" / "upstream-rust" / "test-exceptions.toml"
LANES = REPO_ROOT / "tests" / "upstream-rust" / "test-exception-lanes.toml"
COMPILETEST_COMMON = REPO_ROOT / "src" / "tools" / "compiletest" / "src" / "common.rs"
COMPILETEST_CLI = REPO_ROOT / "src" / "tools" / "compiletest" / "src" / "cli.rs"
COMPILETEST_RUNTEST = REPO_ROOT / "src" / "tools" / "compiletest" / "src" / "runtest.rs"
BOOTSTRAP_TEST = (
    REPO_ROOT / "src" / "bootstrap" / "src" / "core" / "build_steps" / "test.rs"
)

# The predicate that isolates compiletest's own compiles on the vanilla AND the
# default lane. Every `vanilla` and `default` row is a claim about it, so it is
# re-asserted whether or not a verified lane exists: if it drifts, those lanes
# may no longer be the lanes the rows were measured on.
DEFAULT_LANE_PREDICATE = "self.rustc_supports_trust_verification || self.trust_vanilla()"

# Every link in the chain that makes `x.py test --trust-verified` reach a real
# rustc invocation. Whitespace-normalized needles; see `compiletest_premise_findings`.
VERIFIED_LANE_CHAIN: tuple[tuple[str, str, str], ...] = (
    (
        "common",
        "compiletest defines the verified-lane sentinel",
        'TRUST_VERIFIED_SENTINEL: &str = "--compiletest-trust-verified";',
    ),
    (
        "common",
        "compiletest names the shipping default in argv",
        'TRUST_VERIFIED_RUSTC_FLAGS: [&str; 2] = ["-Ztrust-verify=on", "-Ztrust-policy=strict"];',
    ),
    (
        "common",
        "Config::trust_verified reads the sentinel",
        "pub(crate) fn trust_verified(&self) -> bool { self.target_rustcflags.iter().any(|flag| "
        "flag == TRUST_VERIFIED_SENTINEL) }",
    ),
    (
        "common",
        "the isolation function has a Verified arm that appends those flags",
        "TrustVerificationLane::Verified => {",
    ),
    (
        "common",
        "the Verified arm appends the verified flags",
        "command.args(TRUST_VERIFIED_RUSTC_FLAGS);",
    ),
    (
        "common",
        "the verified sentinel is an internal flag (never leaks into a test's argv)",
        "flag == TRUST_VANILLA_SENTINEL || flag == TRUST_VERIFIED_SENTINEL",
    ),
    # The 1.101 migration ported compiletest's argument parsing from the
    # getopts parser in lib.rs to the Args struct in cli.rs (the port keeps
    # the Trust comments); these three links live there now, spelled
    # through `args.`.
    (
        "cli",
        "compiletest registers --trust-verified and pushes the sentinel",
        "target_rustcflags.push(TRUST_VERIFIED_SENTINEL.to_string());",
    ),
    (
        "cli",
        "--trust-vanilla and --trust-verified are mutually exclusive",
        "if args.trust_vanilla && args.trust_verified {",
    ),
    (
        "cli",
        "--trust-verified refuses a driver with no verifier",
        "if args.trust_verified && !args.rustc_supports_trust_verification {",
    ),
    (
        "runtest",
        "the verified lane has its own result stamp (no silent reuse of an "
        "unverified run's results)",
        "if config.trust_verified() { TRUST_VERIFIED_SENTINEL.hash(&mut hash); }",
    ),
    (
        "bootstrap_test",
        "bootstrap forwards --trust-verified to compiletest",
        'cmd.arg("--trust-verified");',
    ),
)

VALID_LANES = ("vanilla", "default", "verified")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
# x.py's lane flags; a command with neither runs the default lane.
LANE_FLAGS = {"--trust-vanilla": "vanilla", "--trust-verified": "verified"}
# The kinds `failure_covering_exception` (crates/trust-upstream-compat/src/porting.rs)
# lets net a failed compiletest test. A row of any other kind waives no failure.
FAILURE_NETTING_KINDS = ("expected_fail", "intentional_divergence")


def _reexec_under_a_toml_capable_python() -> None:
    """Re-exec under an interpreter that HAS a TOML parser, if this one lacks one.

    Same rationale as scripts/check_ledger_expirations.py: `tomllib` is stdlib
    only from 3.11, and on this box bare `python3` is the 3.9 CommandLineTools
    build while a 3.14 sits on the same PATH. A gate that refuses because of the
    interpreter that invoked it reports nothing about the tree.
    """
    import importlib.util
    import os
    import shutil

    if importlib.util.find_spec("tomllib") or importlib.util.find_spec("tomli"):
        return
    if os.environ.get("TRUST_LANES_PY_REEXEC"):
        return
    for candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        found = shutil.which(candidate)
        if not found:
            continue
        os.environ["TRUST_LANES_PY_REEXEC"] = "1"
        os.execv(found, [found, os.path.abspath(__file__), *sys.argv[1:]])


_reexec_under_a_toml_capable_python()

TOML_PARSER_ERROR = (
    "error: no TOML parser available for lane checks; use Python 3.11+ for "
    "stdlib tomllib, or install tomli for this Python environment"
)


def load_toml_text(text: str) -> dict[str, Any]:
    try:
        import tomllib
    except ModuleNotFoundError:
        try:
            import tomli as tomllib  # type: ignore[no-redef]
        except ModuleNotFoundError as exc:
            raise RuntimeError(TOML_PARSER_ERROR) from exc
    return tomllib.loads(text)


def entry_is_active(entry: dict[str, Any]) -> bool:
    """Only `status = "active"` rows are gated.

    A missing `status` is treated as active — better to surface a
    missing-field problem than to skip a row silently.
    """
    status = entry.get("status")
    if status is None:
        return True
    return str(status).lower() == "active"


def compiletest_premise_findings(
    sources: dict[str, str | None],
) -> tuple[list[str], bool | None]:
    """Re-derive from SOURCE whether a verified lane exists, and whether the
    default lane is still the lane every `vanilla` row was measured on.

    Returns `(findings, lane_in_source)` where `lane_in_source` is:
        True   every link of `VERIFIED_LANE_CHAIN` is present -- `x.py test
               --trust-verified` reaches a rustc invocation that states
               `-Ztrust-verify=on -Ztrust-policy=strict`;
        False  no link is present -- the pre-lane world;
        None   the chain is PARTIAL, or a source file could not be read. This is
               the dangerous state and it is always a finding: a half-wired lane
               can accept the flag and still not verify, producing vanilla
               evidence under a verified label. Never resolved by guessing.

    Nothing here is trusted from the ledger. The ledger asserts
    `verified_lane_available`; this function checks that assertion against the
    code, in the direction that can mislead.
    """
    findings: list[str] = []

    missing_files = [name for name, text in sources.items() if text is None]
    if missing_files:
        findings.append(
            "cannot re-derive the verified-lane premise: unreadable source "
            f"{sorted(missing_files)}. Refusing to assume it."
        )
        return findings, None

    normalized = {name: " ".join((text or "").split()) for name, text in sources.items()}

    # --- the DEFAULT lane, which every `vanilla` row is a claim about ---------
    if 'TRUST_VANILLA_RUSTC_FLAG: &str = "-Ztrust-verify=off"' not in normalized["common"]:
        findings.append(
            "compiletest no longer defines TRUST_VANILLA_RUSTC_FLAG as "
            '"-Ztrust-verify=off"; re-measure which lanes run verification and '
            "update `verified_lane_available` / this gate together."
        )
    if DEFAULT_LANE_PREDICATE not in normalized["common"]:
        findings.append(
            "compiletest no longer decides the DEFAULT lane on "
            "`rustc_supports_trust_verification || trust_vanilla()`. Every "
            "`vanilla` row is a claim about that predicate; re-measure before "
            "trusting any lane assignment."
        )

    # --- the VERIFIED lane, link by link -------------------------------------
    present: list[str] = []
    absent: list[str] = []
    for file_key, label, needle in VERIFIED_LANE_CHAIN:
        (present if needle in normalized[file_key] else absent).append(label)

    if not present:
        # The pre-lane world. Coherent: no lane, so no verified row.
        return findings, False
    if absent:
        findings.append(
            "the verified lane is HALF-WIRED: "
            f"{len(present)} of {len(VERIFIED_LANE_CHAIN)} links present, missing "
            f"{absent}. A partially-wired lane can accept `--trust-verified` and "
            "still not verify, which produces vanilla evidence under a verified "
            "label. Refusing to call the lane available or unavailable."
        )
        return findings, None
    return findings, True


def check(
    ledger_doc: dict[str, Any],
    lanes_doc: dict[str, Any],
    sources: dict[str, str | None],
) -> tuple[list[str], dict[str, Any]]:
    findings: list[str] = []

    exceptions = ledger_doc.get("exceptions") or []
    lane_rows = lanes_doc.get("lanes") or []

    verified_available = lanes_doc.get("verified_lane_available")
    if not isinstance(verified_available, bool):
        findings.append(
            "test-exception-lanes.toml must set `verified_lane_available` to a "
            "boolean; a lane ledger that does not say whether the verified lane "
            "exists cannot refuse an unmeasurable verified waiver."
        )
        verified_available = False

    premise_findings, lane_in_source = compiletest_premise_findings(sources)
    findings.extend(premise_findings)

    # The ledger ASSERTS the flag; the source DECIDES it. Cross-check in the
    # direction that can mislead: a `true` the code does not support would let
    # every unmeasurable verified row through. The opposite skew (the lane is
    # wired but the ledger still says false) is legitimate -- the mechanism can
    # land before anyone has run it -- so it is reported, not refused.
    if verified_available and lane_in_source is not True:
        findings.append(
            "test-exception-lanes.toml claims `verified_lane_available = true`, "
            "but the compiletest/bootstrap source does not show a fully-wired "
            "`--trust-verified` lane. A verified row would then waive a failure "
            "no lane could have observed. Fix the lane or drop the claim."
        )
    if verified_available and not str(lanes_doc.get("verified_lane_landed_by") or "").strip():
        findings.append(
            "`verified_lane_available = true` must name its basis in "
            "`verified_lane_landed_by` -- which change wired the lane, and which "
            "positive controls a run must show. An unexplained `true` is exactly "
            "the unmeasured claim this gate exists to refuse."
        )

    # --- sidecar index: one row per (id, lane), duplicate-checked -------------
    sidecar: dict[str, list[dict[str, Any]]] = {}
    for raw in lane_rows:
        if not isinstance(raw, dict):
            findings.append("test-exception-lanes.toml: `lanes` contains a non-table entry")
            continue
        row_id = raw.get("id")
        if not isinstance(row_id, str) or not row_id.strip():
            findings.append("test-exception-lanes.toml: a `[[lanes]]` row has no `id`")
            continue
        if any(str(prior.get("lane")) == str(raw.get("lane")) for prior in sidecar.get(row_id, [])):
            findings.append(
                f"{row_id}: lane {raw.get('lane')!r} assigned more than once — ambiguous "
                f"assignments let a reader pick the convenient one"
            )
            continue
        sidecar.setdefault(row_id, []).append(raw)

    active_ids: list[str] = []
    assignments: dict[str, list[str]] = {}

    for index, raw in enumerate(exceptions):
        if not isinstance(raw, dict):
            findings.append(f"test-exceptions.toml: exceptions[{index}] is not a table")
            continue
        exc_id = raw.get("id")
        if not isinstance(exc_id, str) or not exc_id.strip():
            findings.append(f"test-exceptions.toml: exceptions[{index}] has no `id`")
            continue
        if not entry_is_active(raw):
            continue
        active_ids.append(exc_id)

        inline_lane = raw.get("lane")
        sides = sidecar.get(exc_id, [])

        if inline_lane is None and not sides:
            findings.append(
                f"{exc_id}: NO lane assignment. Every active exception must declare "
                f"the lane its failure was observed on (one of {VALID_LANES}) — "
                f"add a `[[lanes]]` row to test-exception-lanes.toml, or an inline "
                f"`lane` once model.rs carries the field."
            )
            continue

        side_lanes = [str(side.get("lane")) for side in sides]
        if inline_lane is not None and sides and side_lanes != [str(inline_lane)]:
            findings.append(
                f"{exc_id}: inline lane {inline_lane!r} disagrees with sidecar "
                f"lanes {side_lanes!r}. Delete the sidecar rows once the "
                f"inline field is authoritative; never leave two answers."
            )
            continue

        lanes = [str(inline_lane)] if inline_lane is not None else side_lanes
        row_findings: list[str] = []
        for lane in lanes:
            if lane not in VALID_LANES:
                row_findings.append(f"{exc_id}: lane {lane!r} is not one of {VALID_LANES}")
            elif lane == "verified" and not verified_available:
                row_findings.append(
                    f"{exc_id}: lane = \"verified\" while `verified_lane_available = "
                    f"false`. No compiletest lane runs at -Ztrust-verify=on, so this "
                    f"failure cannot have been measured on it. Land the opt-in in "
                    f"VERIFIED-LANE-RUNBOOK.md and flip the flag in the same change."
                )
        if inline_lane is None:
            for side in sides:
                measured_on = side.get("measured_on")
                evidence = side.get("evidence")
                if not isinstance(measured_on, str) or not DATE_RE.match(measured_on):
                    row_findings.append(
                        f"{exc_id} ({side.get('lane')}): `measured_on` {measured_on!r} "
                        f"is not YYYY-MM-DD"
                    )
                elif not isinstance(evidence, str) or not evidence.strip():
                    row_findings.append(
                        f"{exc_id} ({side.get('lane')}): lane assignment carries no "
                        f"`evidence`. A lane claim with no observation behind it is "
                        f"exactly what this gate stops."
                    )
        if row_findings:
            findings.extend(row_findings)
            continue

        assignments[exc_id] = lanes

    known = set(active_ids)
    for row_id in sidecar:
        if row_id not in known:
            findings.append(
                f"{row_id}: lane row names no ACTIVE exception in "
                f"test-exceptions.toml. A retired row must not leave a stale lane "
                f"claim behind — delete it."
            )

    summary = {
        "active_exceptions": len(active_ids),
        "assigned": len(assignments),
        **{
            lane: sum(1 for lanes in assignments.values() if lane in lanes)
            for lane in VALID_LANES
        },
        "verified_lane_available": bool(verified_available),
        "verified_lane_in_source": lane_in_source,
        "findings": len(findings),
        "lanes_by_id": assignments,
    }
    return findings, summary


# --- --run: a suite row's x.py command, with the waivers of ITS lane ---------


def xpy_test_index(argv: Sequence[str]) -> int | None:
    """Index of `x.py` in an `... x.py test ...` argv, or None."""
    for index, arg in enumerate(argv[:-1]):
        if Path(arg).name == "x.py" and argv[index + 1] == "test":
            return index
    return None


def command_lane(argv: Sequence[str]) -> str:
    """The lane an `x.py test` argv runs on, read off the argv itself."""
    lanes = {LANE_FLAGS[arg] for arg in argv if arg in LANE_FLAGS}
    if len(lanes) > 1:
        raise ValueError("--trust-vanilla and --trust-verified together; x.py refuses that too")
    return lanes.pop() if lanes else "default"


def split_test_paths(argv: Sequence[str]) -> tuple[list[str], list[str]]:
    """(the `tests/...` paths the command selects, the argv without them).

    A `--skip`/`--exclude` value is not a selected path.
    """
    paths: list[str] = []
    rest: list[str] = []
    previous = ""
    for arg in argv:
        if arg.startswith("tests/") and previous not in ("--skip", "--exclude"):
            paths.append(arg.rstrip("/"))
        else:
            rest.append(arg)
        previous = arg
    return paths, rest


def lane_waivers(
    ledger_doc: dict[str, Any],
    lanes_by_id: dict[str, list[str]],
    lane: str,
    test_paths: Sequence[str],
    today: str,
) -> tuple[list[dict[str, Any]], list[str]]:
    """(rows a run on `lane` over `test_paths` may skip, why each other row may not)."""
    waived: list[dict[str, Any]] = []
    notes: list[str] = []
    for row in ledger_doc.get("exceptions") or []:
        if not isinstance(row, dict) or row.get("status") != "active":
            continue
        path = str(row.get("path") or "")
        if not any(path == root or path.startswith(root + "/") for root in test_paths):
            continue
        exc_id = row.get("id")
        observed = lanes_by_id.get(str(exc_id), [])
        expires_on = str(row.get("expires_on") or "")
        if lane not in observed:
            notes.append(f"runs: {path} [{exc_id}] is waived only on {observed}, not {lane}")
        elif row.get("kind") not in FAILURE_NETTING_KINDS:
            notes.append(f"runs: {path} [{exc_id}] kind {row.get('kind')!r} nets no failure")
        elif not DATE_RE.match(expires_on) or expires_on < today:
            notes.append(f"runs: {path} [{exc_id}] waiver expired on {expires_on!r}")
        else:
            waived.append(row)
    return waived, notes


def say(line: str) -> None:
    print(line, flush=True)


def run_command(argv: list[str]) -> int:
    # The re-exec marker is this script's own; the suite must not inherit it.
    env = {key: value for key, value in os.environ.items() if key != "TRUST_LANES_PY_REEXEC"}
    return subprocess.run(argv, check=False, env=env).returncode


def run_with_waivers(
    argv: Sequence[str],
    ledger_doc: dict[str, Any],
    lanes_doc: dict[str, Any],
    sources: dict[str, str | None],
    *,
    today: str,
    repo_root: Path,
    dry_run: bool = False,
    run: Callable[[list[str]], int] = run_command,
) -> int:
    index = xpy_test_index(argv)
    if index is None:
        print(f"error: --run wraps an `x.py test` command, got: {shlex.join(argv)}", file=sys.stderr)
        return 2
    try:
        lane = command_lane(argv)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    test_paths, rest = split_test_paths(argv[index + 2 :])
    if not test_paths:
        print("error: the command names no tests/... path to scope waivers to", file=sys.stderr)
        return 2
    head = list(argv[: index + 2])

    findings, summary = check(ledger_doc, lanes_doc, sources)
    if findings:
        print("refusing to run: the waiver ledger has findings, so no lane's waivers are known:", file=sys.stderr)
        for finding in findings:
            print(f"  • {finding}", file=sys.stderr)
        return 1

    waived, notes = lane_waivers(ledger_doc, summary["lanes_by_id"], lane, test_paths, today)
    say(f"waiver lane: {lane} (tests/upstream-rust/test-exceptions.toml, {today})")
    for note in notes:
        say(f"  {note}")
    command = list(argv)
    for row in waived:
        say(f"  skips: {row['path']} [{row['id']}] until {row['expires_on']}")
        command += ["--skip", str(row["path"])]
    say(f"command: {shlex.join(command)}")
    if dry_run:
        return 0

    status = run(command)
    if status != 0:
        return status
    for row in waived:
        path = str(row["path"])
        if not (repo_root / path).exists():
            say(f"WARN: {row['id']} waives {path}, which does not exist; retire the row")
            continue
        probe = head + rest + [path]
        say(f"probe: {shlex.join(probe)}")
        probe_status = run(probe)
        if probe_status == 0:
            say(
                f"WARN: {row['id']}: {path} exits 0 alone on the {lane} lane (passed, "
                f"or ignored on this host), so its waiver covers no failure here; retire "
                f"its {lane} row in tests/upstream-rust/test-exception-lanes.toml"
            )
        else:
            say(f"  still fails (exit {probe_status}): {path}")
    return 0


SELF_TEST_LEDGER = """
schema_version = "0.1.0"

[[exceptions]]
id = "a"
status = "active"

[[exceptions]]
id = "b"
status = "active"

[[exceptions]]
id = "retired"
status = "resolved"
"""

# The PRE-LANE world: default lane intact, no `--trust-verified` anywhere.
SELF_TEST_SOURCES_NO_LANE: dict[str, str | None] = {
    "common": (
        'pub(crate) const TRUST_VANILLA_RUSTC_FLAG: &str = "-Ztrust-verify=off";\n'
        "    pub(crate) fn configure_compiletest_rustc(&self, command: &mut Command) {\n"
        "        configure_trust_verification_isolation(\n"
        "            command,\n"
        "            self.rustc_supports_trust_verification || self.trust_vanilla(),\n"
        "        );\n"
        "    }\n"
    ),
    "cli": "",
    "runtest": "",
    "bootstrap_test": "",
}


def _self_test_sources_with_lane() -> dict[str, str | None]:
    """The POST-LANE world, built from the chain the gate itself checks for.

    Synthesized from `VERIFIED_LANE_CHAIN` rather than pasted, so the self-test
    cannot drift away from the production needles.
    """
    sources: dict[str, str | None] = {
        "common": SELF_TEST_SOURCES_NO_LANE["common"],
        "cli": "",
        "runtest": "",
        "bootstrap_test": "",
    }
    for file_key, _label, needle in VERIFIED_LANE_CHAIN:
        sources[file_key] = f"{sources[file_key]}\n{needle}\n"
    return sources


def self_test() -> int:
    """Exercise every refusal on synthetic inputs. A test beats a claim."""
    cases: list[tuple[str, str, bool, str]] = []

    good = """
verified_lane_available = false
[[lanes]]
id = "a"
lane = "vanilla"
measured_on = "2026-09-01"
evidence = "run x"
[[lanes]]
id = "b"
lane = "vanilla"
measured_on = "2026-09-01"
evidence = "run y"
"""
    cases.append(("fully assigned", good, True, ""))

    missing = """
verified_lane_available = false
[[lanes]]
id = "a"
lane = "vanilla"
measured_on = "2026-09-01"
evidence = "run x"
"""
    cases.append(("missing assignment for b", missing, False, "NO lane assignment"))

    stale = good + """
[[lanes]]
id = "ghost"
lane = "vanilla"
measured_on = "2026-09-01"
evidence = "run z"
"""
    cases.append(("stale lane row", stale, False, "names no ACTIVE exception"))

    retired_claim = good + """
[[lanes]]
id = "retired"
lane = "vanilla"
measured_on = "2026-09-01"
evidence = "run z"
"""
    cases.append(("lane row for retired exception", retired_claim, False, "names no ACTIVE exception"))

    bad_lane = good.replace('id = "b"\nlane = "vanilla"', 'id = "b"\nlane = "branded"')
    cases.append(("unknown lane value", bad_lane, False, "is not one of"))

    verified_while_unavailable = good.replace(
        'id = "b"\nlane = "vanilla"', 'id = "b"\nlane = "verified"'
    )
    cases.append(
        (
            "verified waiver while no verified lane exists",
            verified_while_unavailable,
            False,
            "verified_lane_available",
        )
    )

    verified_when_available = verified_while_unavailable.replace(
        "verified_lane_available = false",
        'verified_lane_available = true\nverified_lane_landed_by = "the wiring change"',
    )
    cases.append(("verified waiver once the lane exists", verified_when_available, True, ""))

    no_evidence = good.replace('evidence = "run y"', 'evidence = ""')
    cases.append(("lane claim with no evidence", no_evidence, False, "no `evidence`"))

    bad_date = good.replace('measured_on = "2026-09-01"\nevidence = "run y"',
                            'measured_on = "soon"\nevidence = "run y"')
    cases.append(("non-ISO measured_on", bad_date, False, "not YYYY-MM-DD"))

    dup = good + """
[[lanes]]
id = "a"
lane = "vanilla"
measured_on = "2026-09-02"
evidence = "run dup"
"""
    cases.append(("duplicate assignment", dup, False, "more than once"))

    second_lane = good + """
[[lanes]]
id = "a"
lane = "default"
measured_on = "2026-09-02"
evidence = "default-lane run"
"""
    cases.append(("a second lane is a second observation", second_lane, True, ""))

    second_lane_unmeasured = second_lane.replace('evidence = "default-lane run"', 'evidence = ""')
    cases.append(
        ("a second lane with no evidence", second_lane_unmeasured, False, "(default): lane assignment carries no `evidence`")
    )

    second_lane_verified = second_lane.replace('lane = "default"', 'lane = "verified"')
    cases.append(
        ("a second, verified lane while none exists", second_lane_verified, False, "verified_lane_available")
    )

    no_flag = good.replace("verified_lane_available = false", "")
    cases.append(("missing verified_lane_available", no_flag, False, "must set `verified_lane_available`"))

    ledger = load_toml_text(SELF_TEST_LEDGER)
    with_lane = _self_test_sources_with_lane()
    failures: list[str] = []
    for name, lanes_text, want_pass, want_fragment in cases:
        # Cases that assert `verified_lane_available = true` need the source to
        # back that claim; the rest run against the pre-lane world.
        sources = (
            with_lane
            if "verified_lane_available = true" in lanes_text
            else SELF_TEST_SOURCES_NO_LANE
        )
        findings, _ = check(ledger, load_toml_text(lanes_text), sources)
        passed = not findings
        if passed != want_pass:
            failures.append(
                f"{name}: expected {'pass' if want_pass else 'fail'}, got "
                f"{'pass' if passed else 'fail'} ({findings})"
            )
        elif want_fragment and not any(want_fragment in f for f in findings):
            failures.append(f"{name}: no finding mentioned {want_fragment!r}: {findings}")

    # --- the premise is RE-DERIVED, not assumed -----------------------------
    def derive(lanes_text: str, sources: dict[str, str | None]):
        findings, summary = check(ledger, load_toml_text(lanes_text), sources)
        return findings, summary["verified_lane_in_source"]

    drifted = {"common": "fn nothing() {}", "cli": "", "runtest": "", "bootstrap_test": ""}
    findings, _ = derive(good, drifted)
    if not any("no longer" in f for f in findings):
        failures.append("drifted compiletest source did not trip the premise re-derivation")

    unreadable = {"common": None, "cli": "", "runtest": "", "bootstrap_test": ""}
    findings, in_source = derive(good, unreadable)
    if not findings or in_source is not None:
        failures.append("unreadable compiletest source did not fail closed")

    # A fully-wired lane is recognized as such...
    findings, in_source = derive(good, with_lane)
    if findings or in_source is not True:
        failures.append(f"fully-wired lane not recognized: {findings} / {in_source}")

    # ...and the pre-lane world as such.
    _, in_source = derive(good, SELF_TEST_SOURCES_NO_LANE)
    if in_source is not False:
        failures.append("pre-lane source was not reported as lane-absent")

    # A HALF-WIRED lane is the dangerous state: neither available nor absent.
    for file_key, label, needle in VERIFIED_LANE_CHAIN:
        half = dict(with_lane)
        half[file_key] = (half[file_key] or "").replace(needle, "")
        findings, in_source = derive(good, half)
        if in_source is not None or not any("HALF-WIRED" in f for f in findings):
            failures.append(f"removing {label!r} did not trip the half-wired refusal")

    # `verified_lane_available = true` is refused when the source disagrees...
    available_claim = good.replace(
        "verified_lane_available = false",
        'verified_lane_available = true\nverified_lane_landed_by = "basis"',
    )
    findings, _ = check(ledger, load_toml_text(available_claim), SELF_TEST_SOURCES_NO_LANE)
    if not any("does not show a fully-wired" in f for f in findings):
        failures.append("an unsupported `verified_lane_available = true` was not refused")

    # ...and must name its basis even when the source agrees.
    unexplained = good.replace(
        "verified_lane_available = false", "verified_lane_available = true"
    )
    findings, _ = check(ledger, load_toml_text(unexplained), with_lane)
    if not any("verified_lane_landed_by" in f for f in findings):
        failures.append("`verified_lane_available = true` with no basis was not refused")

    if failures:
        print("lane-gate self-test FAILED:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print(
        f"lane-gate self-test passed ({len(cases)} ledger cases + "
        f"{6 + len(VERIFIED_LANE_CHAIN)} premise cases)."
    )
    return 0


def parse_args(argv: Sequence[str]) -> tuple[argparse.Namespace, list[str]]:
    own, command = list(argv), []
    if "--" in own:
        split = own.index("--")
        own, command = own[:split], own[split + 1 :]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Machine-readable output.")
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Exercise the gate's refusals on synthetic ledgers and exit.",
    )
    parser.add_argument(
        "--run",
        action="store_true",
        help="Run the `x.py test` command after `--`, skipping its lane's waivers.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="With --run: print the command it would run, and run nothing.",
    )
    args = parser.parse_args(own)
    if args.run != bool(command) or (args.dry_run and not args.run):
        parser.error("--run takes the command after `--`, and --dry-run needs --run")
    return args, command


def main() -> int:
    args, command = parse_args(sys.argv[1:])
    if args.self_test:
        return self_test()

    try:
        for path in (LEDGER, LANES):
            if not path.exists():
                print(f"error: {path} is missing", file=sys.stderr)
                return 1
        ledger_doc = load_toml_text(LEDGER.read_text(encoding="utf-8"))
        lanes_doc = load_toml_text(LANES.read_text(encoding="utf-8"))
    except RuntimeError as exc:
        print(exc, file=sys.stderr)
        return 1
    except Exception as exc:  # noqa: BLE001 - a parse failure must be a finding
        print(f"error: ledger parse failed: {exc}", file=sys.stderr)
        return 1

    def read(path: Path) -> str | None:
        try:
            return path.read_text(encoding="utf-8")
        except OSError:
            return None

    sources: dict[str, str | None] = {
        "common": read(COMPILETEST_COMMON),
        "cli": read(COMPILETEST_CLI),
        "runtest": read(COMPILETEST_RUNTEST),
        "bootstrap_test": read(BOOTSTRAP_TEST),
    }

    if args.run:
        return run_with_waivers(
            command,
            ledger_doc,
            lanes_doc,
            sources,
            today=datetime.now(timezone.utc).date().isoformat(),
            repo_root=REPO_ROOT,
            dry_run=args.dry_run,
        )

    findings, summary = check(ledger_doc, lanes_doc, sources)

    if args.json:
        json.dump({"summary": summary, "findings": findings}, sys.stdout, indent=2)
        sys.stdout.write("\n")
    else:
        print("Exception lane check")
        print(f"  active exceptions:        {summary['active_exceptions']}")
        print(f"  with a lane assignment:   {summary['assigned']}")
        print(f"    vanilla:                {summary['vanilla']}")
        print(f"    default:                {summary['default']}")
        print(f"    verified:               {summary['verified']}")
        print(f"  verified lane available:  {summary['verified_lane_available']}")
        in_source = summary["verified_lane_in_source"]
        derived = {True: "wired", False: "absent", None: "INDETERMINATE"}[in_source]
        print(f"  verified lane in source:  {derived}")
        if findings:
            print("")
            print("FINDINGS — gate FAIL:")
            for finding in findings:
                print(f"  • {finding}")

    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
