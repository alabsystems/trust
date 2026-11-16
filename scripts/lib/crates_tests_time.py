#!/usr/bin/env python3
"""The crates/ tests lane's one time-bound rule, for every caller.

scripts/check_crates_tests_scoped.py runs it for both of the lane's callers:
scripts/hooks/pre-push's `scoped.crates-tests` (the members a push touches) and
scripts/land_gate.py's `crates-tests` leg (the members a change reaches beyond
those, handed over by --also-members). Both get their bound from this module,
over the crates the lane is asked to test, and from nothing else: the land gate
passes no TRUST_CRATES_TESTS_BUDGET_S of its own (docs/DECISION_QUEUE.md,
CRATES-TIME-1).

WHY A STALL BOUND, NOT A FIXED TOTAL (CRATES-TIME-1, 2026-10-28). Until then the
hook's lane had a flat 1200 s for the whole lane and the land gate's leg
max(1200, 240 s x its members). On 2026-10-28 the refuted-unreachable line's
three pushes of one change were each refused NOT JUDGED for time, all on m2 (18
cores, shared, load 40-120): the hook lane tested 3 touched members
(trust-certify, trust-json, trust-vcgen) plus one instrument, 252 test binaries,
and macOS's first-exec admission alone took 593 s, 580 s and 1157 s of the 1200 s
(push-3 was killed with 231 of 252 binaries done and trust-vcgen's lib still
printing). The same tree's land gate leg tested 36 reached members, 393 binaries,
under 8640 s and passed in 1295 s and 4632 s. The per-member formula would not
have saved the push: max(1200, 240 x 3) is 1200. Most of a binary's wall time on
this host is outside libtest's clock (the first-exec hold, image load), and it
grows with the host's load and the size of crates/target/debug/deps, so any fixed
total is a latency budget that the host, not the change, decides.

THE RULE.
  * STALL: the lane stops, NOT JUDGED, when nothing it runs has made progress
    for stall_s() seconds (TRUST_CRATES_TESTS_STALL_S, default DEFAULT_STALL_S).
    Progress is a line of output from a test binary while that binary still
    runs, a test binary ending, and an executable carried through macOS's
    first-exec check. A line read after its binary ended is not progress: it
    comes from something the binary left holding its output open (a daemon a
    test leaves), which would otherwise keep the stall bound from ever ending a
    hang elsewhere. The builds (cargo building the tests, targo-trust's build)
    are not judged by the stall bound at all: one rustc can be silent for long
    on a loaded host and cargo is silent while it waits on another build's
    lock, which is latency, not a hang, so the ceiling alone bounds a build and
    the stall clock starts again when it ends. A hung binary therefore still
    ends the lane NOT JUDGED, stall_s() after the last progress, however many
    binaries finished before it; a lane that is slow but moving is never
    stopped for being slow.
  * CEILING: the whole lane still has one outer wall-clock bound,
    budget_s(crates) = max(CEILING_FLOOR_S, CEILING_PER_CRATE_S x crates), the
    same function for both callers. It stops a lane that keeps printing and
    never ends (a livelock), and it is sized so that no lane measured on m2
    comes near it: 14400 s for a 3-crate hook lane (one touched member and two
    instruments, 213 binaries) that passed in 1537 s, 2082 s and 3636 s on the
    backing line's pushes; 32400 s for a 36-member gate leg (393 binaries) that
    passed in 1295 s, 4632 s and 4941 s. TRUST_CRATES_TESTS_BUDGET_S, when set,
    replaces the ceiling for either caller.
  * Sizing the stall: the slowest binary in those runs took 1160 s and printed
    all the way (trust-vcgen's lib, 5521 tests); the slowest with few tests took
    669 s for 37 (opaque_deref_store_reseat), so none of them was silent for
    anything near DEFAULT_STALL_S, and the lane as a whole runs up to
    TRUST_CRATES_TESTS_JOBS of them at once.
  * Sizing the ceiling: it only ever ends a lane that keeps progressing and
    never finishes, or a build that never ends, since the stall bound ends a
    hang first. For a gate leg that reaches every member (99 crates on a
    scripts/ change, which fail-closes the selector) it is 89100 s, about 25 h.
Either bound running out kills everything the lane started and exits 3, NOT
JUDGED. Neither turns an unrun test into a pass.

What this does NOT promise: that a push of a tree whose land gate was green can
never be NOT JUDGED for time. The hook tests the touched members and the gate the
others, so their runs differ; the push is refused for time only when nothing it
runs progressed for stall_s() seconds (a hang) or its own ceiling ran out, never
because a fixed total was smaller than the host made the run.

Python 3.9 compatible. scripts/tests/check_crates_tests_scoped_test.py
(TimeBoundTest) and scripts/tests/land_gate_test.py hold both callers to it.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import os
from typing import Mapping, Optional

BUDGET_ENV = "TRUST_CRATES_TESTS_BUDGET_S"
STALL_ENV = "TRUST_CRATES_TESTS_STALL_S"
CEILING_FLOOR_S = 14400
CEILING_PER_CRATE_S = 900
DEFAULT_STALL_S = 1800


def _env(env: Optional[Mapping[str, str]]) -> Mapping[str, str]:
    return os.environ if env is None else env


def _positive_int(name: str, text: str) -> int:
    try:
        value = int(text)
    except ValueError:
        raise ValueError(f"{name} must be an integer number of seconds, not {text!r}") from None
    if value < 1:
        raise ValueError(f"{name} must be at least 1 second, not {value}")
    return value


def budget_s(crates: int, env: Optional[Mapping[str, str]] = None) -> int:
    """The lane's ceiling for a run that tests `crates` crates: BUDGET_ENV when
    set, else max(CEILING_FLOOR_S, CEILING_PER_CRATE_S x crates). ValueError for
    a BUDGET_ENV that is not a positive integer."""
    text = _env(env).get(BUDGET_ENV, "")
    if text:
        return _positive_int(BUDGET_ENV, text)
    return max(CEILING_FLOOR_S, CEILING_PER_CRATE_S * max(crates, 0))


def stall_s(env: Optional[Mapping[str, str]] = None) -> int:
    """How long the lane may go with nothing progressing: STALL_ENV when set,
    else DEFAULT_STALL_S. ValueError for one that is not a positive integer."""
    text = _env(env).get(STALL_ENV, "")
    return _positive_int(STALL_ENV, text) if text else DEFAULT_STALL_S


def describe(crates: int, env: Optional[Mapping[str, str]] = None) -> str:
    """One line naming both bounds and where each came from."""
    e = _env(env)
    ceiling = budget_s(crates, e)
    if e.get(BUDGET_ENV, ""):
        why = f"{BUDGET_ENV}"
    else:
        why = f"max({CEILING_FLOOR_S}, {CEILING_PER_CRATE_S} s x {crates} crate(s)); {BUDGET_ENV} replaces it"
    stall = stall_s(e)
    stall_why = STALL_ENV if e.get(STALL_ENV, "") else f"default; {STALL_ENV} replaces it"
    return (f"time bound: stops after {stall}s with nothing progressing ({stall_why}), "
            f"or after {ceiling}s in all ({why})")
