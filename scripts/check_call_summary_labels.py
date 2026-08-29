#!/usr/bin/env python3
"""Every direct-call-summary exit must carry a census label.

`try_direct_call_summary` (first-party/trust-mc,
trust-mc-trust-bmc/src/translate_chc.rs) is the mechanism that lets a caller be
proved panic-free THROUGH a call. It declines through 83 separate exits — 18
`return None` statements (17 through the `decline!` macro plus the opcode-
carrying catch-all) and 65 `?` propagations — and the campaign question
"why does the call summary decline, and how often" is answerable only because
each of those exits now names itself:

    call_summary_scalar(&state.locals, *lhs)
        .or_decline(decline, "int_binop_lhs_unbound", line!())?

An exit added WITHOUT a label is silent: the census still counts the decline,
but attributes it to the `__unlabelled__` sentinel, so the cause split silently
stops being complete and the sole-blocked column silently stops being right.

This is the CHEAP half of the instrument's drift check — a pure source scan, no
build, milliseconds — so it can sit in the pre-push profile. The authoritative
half is
`trust-mc-trust-bmc/tests/call_summary_census.rs::every_direct_call_summary_exit_is_labelled`,
which runs the same scan inside the crate; this script reads that test's
`EXPECTED_LABELLED_EXITS` constant rather than carrying its own copy, so the two
cannot drift apart about the number.

Usage:
    scripts/check_call_summary_labels.py
    scripts/check_call_summary_labels.py --selftest

Exit codes:
    0   every exit is labelled, every label is unique, the count matches
    1   an unlabelled exit, a duplicate label, or a count mismatch
    2   the source could not be read (submodule not checked out, anchors moved)

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SOURCE = REPO_ROOT / "first-party/trust-mc/trust-mc-trust-bmc/src/translate_chc.rs"
RUST_TEST = REPO_ROOT / "first-party/trust-mc/trust-mc-trust-bmc/tests/call_summary_census.rs"

START = "fn try_direct_call_summary("
# The interpreter region ends where the next unrelated method begins.
END = "fn add_transition_rule("

TAG_PATTERNS = ('.or_decline(decline,"', 'decline!(decline,"', 'note_with_detail("')


class Failure(Exception):
    """A real finding, distinguished from an environment problem (exit 2)."""


def region(text: str) -> list[tuple[int, str]]:
    """Interpreter source lines, 1-based, with line comments stripped.

    The strip is load-bearing, not cosmetic: several of the interpreter's own
    comments quote `?` and `return None` while explaining why an arm exists.
    """
    lines = text.split("\n")
    try:
        start = next(i for i, l in enumerate(lines) if l.lstrip().startswith(START))
        end = next(i for i, l in enumerate(lines) if l.lstrip().startswith(END))
    except StopIteration as exc:  # pragma: no cover - anchor drift
        raise SystemExit(
            f"check_call_summary_labels: cannot locate the interpreter region in {SOURCE}.\n"
            f"  Expected a line starting `{START}` and a later one starting `{END}`.\n"
            "  If the method was renamed or moved, update START/END here AND the same\n"
            "  anchors in tests/call_summary_census.rs — they must agree."
        ) from exc
    if start >= end:
        raise SystemExit("check_call_summary_labels: interpreter region is inverted")
    return [(start + off + 1, l.split("//")[0]) for off, l in enumerate(lines[start:end])]


def scan(text: str) -> tuple[list[int], list[int], list[str]]:
    """Return (unlabelled `?` lines, unlabelled `return None` lines, tags)."""
    image_chars: list[str] = []
    owner: list[int] = []
    for line, code in region(text):
        for ch in code:
            if not ch.isspace():
                image_chars.append(ch)
                owner.append(line)
    image = "".join(image_chars)

    bad_question = [
        owner[i]
        for i, ch in enumerate(image)
        if ch == "?" and not image[:i].endswith(("line!())", "line!(),)"))
    ]
    bad_return = [
        owner[m.start()]
        for m in re.finditer("returnNone", image)
        if "decline.note" not in image[max(0, m.start() - 240) : m.start()]
    ]

    tags: list[str] = []
    for pattern in TAG_PATTERNS:
        pos = 0
        while (at := image.find(pattern, pos)) != -1:
            after = at + len(pattern)
            close = image.find('"', after)
            if close == -1:
                break
            tags.append(image[after:close])
            pos = close + 1
    return bad_question, bad_return, tags


def expected_count() -> int:
    """The count pinned by the in-crate test — read, never duplicated."""
    try:
        text = RUST_TEST.read_text()
    except OSError as exc:
        raise SystemExit(f"check_call_summary_labels: cannot read {RUST_TEST}: {exc}") from exc
    match = re.search(r"EXPECTED_LABELLED_EXITS:\s*usize\s*=\s*(\d+)", text)
    if not match:
        raise SystemExit(
            "check_call_summary_labels: EXPECTED_LABELLED_EXITS is gone from "
            f"{RUST_TEST}. That constant is the single pinned count; this gate reads it "
            "rather than carrying a second copy that could disagree."
        )
    return int(match.group(1))


def check(text: str, expected: int) -> None:
    bad_question, bad_return, tags = scan(text)
    if bad_question:
        raise Failure(
            "these `?` exits in try_direct_call_summary carry no census label:\n"
            + "".join(f"    translate_chc.rs:{line}\n" for line in bad_question)
            + '  Fix: wrap the fallible expression in `.or_decline(decline, "<tag>", line!())`.\n'
            "  An unlabelled exit still declines the summary; the census just cannot say why."
        )
    if bad_return:
        raise Failure(
            "these `return None` exits in try_direct_call_summary carry no census label:\n"
            + "".join(f"    translate_chc.rs:{line}\n" for line in bad_return)
            + '  Fix: use `decline!(decline, "<tag>");` instead of a bare `return None;`.'
        )
    duplicates = sorted({t for t in tags if tags.count(t) > 1})
    if duplicates:
        raise Failure(
            f"duplicate census tags: {duplicates}\n"
            "  Every exit must be separately nameable — a shared tag turns the cause\n"
            "  split into a SUM over unrelated exits, which is the attribution failure\n"
            "  the census exists to remove."
        )
    if len(tags) != expected:
        raise Failure(
            f"labelled-exit count is {len(tags)}, EXPECTED_LABELLED_EXITS says {expected}.\n"
            "  If you ADDED an exit: label it and bump the constant in\n"
            "  trust-mc-trust-bmc/tests/call_summary_census.rs.\n"
            "  If it DROPPED: a label was deleted and that decline is now reported as\n"
            "  `__unlabelled__`."
        )


def selftest() -> int:
    """Mutation-prove the gate: a green gate that cannot go red is not a gate."""
    try:
        text = SOURCE.read_text()
    except OSError as exc:
        print(f"check_call_summary_labels: cannot read {SOURCE}: {exc}", file=sys.stderr)
        return 2
    expected = expected_count()

    failures: list[str] = []

    # Control: the real source must pass, or the mutations below prove nothing.
    try:
        check(text, expected)
    except Failure as exc:
        failures.append(f"control (unmutated source) should PASS but failed: {exc}")

    # Mutation 1: strip one `?` label -> the unlabelled-`?` arm must fire.
    stripped = re.sub(r'\.or_decline\(decline, "[a-z0-9_]+", line!\(\)\)', "", text, count=1)
    if stripped == text:
        failures.append("mutation 1 changed nothing: no `.or_decline(...)` label found")
    else:
        try:
            check(stripped, expected)
            failures.append("mutation 1 (deleted a `?` label) was NOT caught")
        except Failure:
            pass

    # Mutation 2: turn one `decline!` back into a bare `return None`.
    unmacroed = re.sub(r'decline!\(decline, "[a-z0-9_]+"\);', "return None;", text, count=1)
    if unmacroed == text:
        failures.append("mutation 2 changed nothing: no `decline!(...)` found")
    else:
        try:
            check(unmacroed, expected)
            failures.append("mutation 2 (bare `return None`) was NOT caught")
        except Failure:
            pass

    # Mutation 3: duplicate a tag -> the uniqueness arm must fire.
    tags = scan(text)[2]
    if len(tags) < 2:
        failures.append("mutation 3 needs at least two tags")
    else:
        duped = text.replace(f'"{tags[1]}"', f'"{tags[0]}"', 1)
        try:
            check(duped, expected)
            failures.append("mutation 3 (duplicated tag) was NOT caught")
        except Failure:
            pass

    if failures:
        print("check_call_summary_labels --selftest: FAIL", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print("check_call_summary_labels --selftest: ok (control passes; 3 mutations caught)")
    return 0


def main() -> int:
    if "--selftest" in sys.argv[1:]:
        return selftest()
    try:
        text = SOURCE.read_text()
    except OSError as exc:
        print(
            f"check_call_summary_labels: cannot read {SOURCE}: {exc}\n"
            "  The trust-mc submodule worktree is probably not checked out.\n"
            "  Run: bash scripts/submodule_sync.sh",
            file=sys.stderr,
        )
        return 2
    try:
        check(text, expected_count())
    except Failure as exc:
        print(f"check_call_summary_labels: FAIL — {exc}", file=sys.stderr)
        return 1
    print("check_call_summary_labels: ok — every call-summary exit is labelled")
    return 0


if __name__ == "__main__":
    sys.exit(main())
