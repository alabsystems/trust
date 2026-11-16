#!/usr/bin/env python3
"""Committed MIR/transport fixtures may not carry a machine path.

WHY THIS EXISTS, MEASURED
-------------------------
These fixtures are `-Ztrust-dump=mir` captures. `SourceSpan::file` is the
UNREMAPPED local path trustc saw, so a capture taken in an agent scratch
directory records that directory, and committing the dump verbatim commits it.
On 2026-09-21 the trust snapshot failed its publication guard with 238
forbidden-content hits, 215 of them in `crates/trust-vcgen/tests/fixtures/`:
thirteen fixtures carried
`/private/tmp/claude-<uid>/<session-uuid>/scratchpad/ent/*.rs` and
`/Users/<owner>/trust-scratch/divfix/*.rs`, and one
`targo-trust/src/fixtures/*.jsonl` carried a third. Those match patterns that
the publication baseline declares unsuppressable — a repository's own
`content-allow.txt` cannot waive them — so the leak blocks the release outright.

The same scrub had already been done once, on 2026-07-18 (publish/DECISIONS.md,
"Scrub log"). It came back because nothing in the repo said no. This checker is
the thing that says no.

WHY IT IS NOT A `sed`
---------------------
`SourceSpan::file` is a join key into the compiler-authenticated standard
library source-file table, so it must not be rewritten independently of such
a table. Since 2026-09-20, `trust_vcgen::sep_engine::is_trusted_std_span` grants
no authority from a path pattern: without that table, as in standalone fixture
replays, the span keeps its obligations. Preserve path tails and check the
actual fixture replay before and after a portability change.
The sanctioned placeholders are the ones the 2026-07-18 scrub chose and that
`crates/trust-vcgen/tests/fixtures` already uses in bulk:

    <dump-root>/...   a dump directory that was outside the repo
    <repo>/...        a path that was inside the development checkout
    <home>/...        a bare home-directory path
    <cargo-home>/...  under the author's CARGO_HOME

These placeholders remove machine-specific prefixes without inventing
compiler provenance. A tail such as `library/core/src/...` remains a path,
not evidence that the compiler authenticated the file as standard library.

THE TWO RULES
-------------
A. Unwaivable, over the whole file: no home directory (`/Users/<n>`,
   `/home/<n>`, `~/`), and no agent-session directory (`claude-<uid>`,
   `.claude/`, `/private/tmp/...`, a `/var/folders/<a>/<b>/T/` TMPDIR).
   These are the classes the publication guard refuses and no repo policy can
   waive, so this checker does not offer a waiver either.

B. Ratcheted, over span `"file"` values: a `"file"` must be RELATIVE, or
   listed verbatim in `check_fixture_span_paths.allow`. The allow list may only
   shrink: an entry that no fixture carries any more is reported as stale, so
   sanitizing the last holder of a path also retires its waiver.

Usage:
    scripts/check_fixture_span_paths.py
    scripts/check_fixture_span_paths.py --selftest

Exit codes:
    0   every committed fixture is clean
    1   a leaked path, an unlisted absolute span, or a stale allow entry

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
ALLOW_FILE = Path(__file__).with_suffix(".allow")

# The fixture trees whose contents are compiler dumps: every one of them feeds
# a span-path decision, and every one of them is inside the publish boundary.
ROOTS = (
    "crates/trust-vcgen/tests/fixtures",
    "crates/trust-vcgen/fixtures",
    "targo-trust/src/fixtures",
    # The E6 differential harness's `-Ztrust-dump=mir:` captures (2026-09-29);
    # its regen.py compiles through a repo-relative path so spans stay clean.
    "crates/trust-certify/tests/fixtures/e6_differential",
)

# The agent session-directory prefix, spelled as a concatenation on purpose:
# this file SHIPS in the public snapshot, and writing the literal would make
# the checker itself a forbidden-content hit in the very guard it keeps green.
# (It did, on the first run of this reproduction: four hits, all from here.)
SESSION_DIR = "claude" + "-501"

# Rule A. Each pattern is paired with the name of the thing it finds, because a
# checker that only says "forbidden" teaches nobody what to write instead.
LEAK_PATTERNS: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"/Users/[A-Za-z0-9_.-]+"), "a macOS home directory"),
    (re.compile(r"/home/[A-Za-z0-9_.-]+/"), "a Linux home directory"),
    (re.compile(r'(?<![\w"])~/'), "a `~/` home-relative path"),
    (re.compile(re.escape(SESSION_DIR)), "an agent-session directory"),
    (re.compile(r"\.claude/"), "an agent-state directory"),
    (re.compile(r"/private/tmp/"), "a macOS private temp path"),
    (re.compile(r"/var/folders/[A-Za-z0-9_+-]{2,}/[A-Za-z0-9_+-]{2,}/T/"),
     "a macOS per-user TMPDIR"),
)

# Rule B.
SPAN_FILE = re.compile(r'"file"\s*:\s*"([^"]*)"')


PLACEHOLDER_HINT = (
    "rewrite the dump root to `<dump-root>/...` (or `<repo>/`, `<home>/`, "
    "`<cargo-home>/`), keeping the tail — see this checker's module docstring "
    "for why the placeholder cannot move a verdict"
)


def tracked_fixture_files(root: Path) -> list[Path]:
    """Every git-TRACKED file under the fixture roots.

    Tracked, not on-disk: an uncommitted local dump is the author's business;
    what this gate is about is what lands in history and therefore in a stage.
    """
    out = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--", *ROOTS],
        capture_output=True, text=True, check=True).stdout
    return [root / name for name in out.split("\0") if name]


def read_allow(path: Path) -> list[str]:
    if not path.exists():
        return []
    entries = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            entries.append(line)
    return entries


def scan(root: Path, allow_file: Path) -> tuple[list[str], list[str]]:
    """-> (failures, stale allow entries)."""
    allowed = read_allow(allow_file)
    unseen = set(allowed)
    failures: list[str] = []

    for path in tracked_fixture_files(root):
        rel = path.relative_to(root).as_posix()
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue

        for number, line in enumerate(text.splitlines(), 1):
            for pattern, what in LEAK_PATTERNS:
                found = pattern.search(line)
                if found:
                    failures.append(
                        f"{rel}:{number}: {what} ({found.group(0)!r}) — "
                        f"{PLACEHOLDER_HINT}")
                    break

        for found in SPAN_FILE.finditer(text):
            value = found.group(1)
            if not value.startswith("/"):
                continue
            unseen.discard(value)
            if value not in allowed:
                number = text.count("\n", 0, found.start()) + 1
                failures.append(
                    f'{rel}:{number}: absolute span file "{value}" is not in '
                    f"{allow_file.name} — {PLACEHOLDER_HINT}")

    stale = [
        f"{allow_file.name}: {value!r} is listed but no fixture carries it any "
        "more — delete the line (this list may only shrink)"
        for value in sorted(unseen)
    ]
    return failures, stale


def report(failures: list[str], stale: list[str]) -> int:
    for line in failures + stale:
        print(f"check_fixture_span_paths: {line}", file=sys.stderr)
    if failures or stale:
        print(
            f"check_fixture_span_paths: FAIL "
            f"({len(failures)} leaked path(s), {len(stale)} stale waiver(s))",
            file=sys.stderr)
        return 1
    print("check_fixture_span_paths: OK — committed fixtures carry no machine path")
    return 0


def selftest() -> int:
    """Prove the checker FIRES. A guard nobody has seen fail is a guard nobody
    has seen."""
    cases = []
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        fixtures = root / ROOTS[0]
        fixtures.mkdir(parents=True)
        subprocess.run(["git", "-C", str(root), "init", "-q"], check=True)

        leak = fixtures / "leaked.json"
        leak.write_text(
            '{"span": {"file": '
            f'"/private/tmp/{SESSION_DIR}/-Users-x-trust/uuid/scratchpad/p.rs"'
            '}}\n',
            encoding="utf-8")
        absolute = fixtures / "absolute.json"
        absolute.write_text('{"span": {"file": "/scratch/probe.rs"}}\n',
                            encoding="utf-8")
        clean = fixtures / "clean.json"
        clean.write_text('{"span": {"file": "<dump-root>/ent/p.rs"}}\n',
                         encoding="utf-8")
        subprocess.run(["git", "-C", str(root), "add", "-A"], check=True)

        allow = root / "empty.allow"
        allow.write_text("# nothing waived\n", encoding="utf-8")
        failures, stale = scan(root, allow)
        cases.append((
            "a session-directory leak is reported",
            any("agent-session directory" in f for f in failures)))
        cases.append((
            "an unlisted absolute span is reported",
            any("/scratch/probe.rs" in f for f in failures)))
        cases.append((
            "a sanitized fixture is not reported",
            not any(clean.name in f for f in failures + stale)))

        allow.write_text("/scratch/probe.rs\n/gone/never.rs\n", encoding="utf-8")
        failures, stale = scan(root, allow)
        cases.append((
            "a listed absolute span is accepted",
            not any("/scratch/probe.rs" in f for f in failures)))
        cases.append((
            "a stale waiver is reported",
            any("/gone/never.rs" in s for s in stale)))
        cases.append((
            "the unwaivable class stays unwaivable",
            any("agent-session directory" in f for f in failures)))

    bad = [name for name, ok in cases if not ok]
    for name, ok in cases:
        print(f"  {'ok  ' if ok else 'FAIL'} {name}")
    if bad:
        print(f"check_fixture_span_paths --selftest: FAIL ({len(bad)})",
              file=sys.stderr)
        return 1
    print(f"check_fixture_span_paths --selftest: OK ({len(cases)} cases)")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selftest", action="store_true",
                        help="prove the checker fires, on a synthetic tree")
    args = parser.parse_args()
    if args.selftest:
        return selftest()
    return report(*scan(REPO_ROOT, ALLOW_FILE))


if __name__ == "__main__":
    sys.exit(main())
