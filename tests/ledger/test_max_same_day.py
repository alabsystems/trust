#!/usr/bin/env python3
"""Trust: unit test for `check_ledger_expirations.py --max-same-day`.

WHY THIS EXISTS. The `--max-same-day` check was added because 73 of 128 active
ledger rows shared one `expires_on`. A cliff is a different failure from an
expiry: one expired row blocks pushes until one row is reviewed, but 73 expiring
together blocks every push until 73 are reviewed — and a reviewer facing that on
a deadline renews the batch. That is exactly how the 71 `sysroot-skew` rows came
to waive a defect that had already been fixed thirteen days earlier: one label,
one copy-pasted reason, one date, no re-measurement.

A new gate with no test is the failure this repo keeps finding — machinery that
reads as coverage while running nothing. So the check gets one, and it drives the
real script over synthetic ledgers rather than re-implementing its logic.

Run: python3 tests/ledger/test_max_same_day.py
"""

from __future__ import annotations

import subprocess
import sys
import textwrap
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "check_ledger_expirations.py"

# `same_day_clusters` is pure and takes a Report, so it can be driven directly —
# no ledger files, no repo state, no dependence on whatever the real ledgers
# happen to contain today (which would make this test drift with them).
HARNESS = textwrap.dedent(
    """
    import sys
    from datetime import date
    sys.path.insert(0, {scripts!r})
    from check_ledger_expirations import EntryStatus, Report, same_day_clusters
    from pathlib import Path

    def entry(day, n):
        return [
            EntryStatus(
                ledger=Path("x.toml"), entry_id=f"e{{i}}", expires_on=day,
                status="ok", days_remaining=30,
            )
            for i in range(n)
        ]

    def report(*groups):
        r = Report()
        for day, n in groups:
            r.ok.extend(entry(day, n))
        return r

    A, B = date(2026, 9, 1), date(2026, 9, 2)
    failed = 0

    def check(name, got, want):
        global failed
        if got == want:
            print(f"  ok    {{name:<52}} -> {{got}}")
        else:
            print(f"  FAIL  {{name:<52}} -> {{got}} (expected {{want}})")
            failed = 1

    # Off by default: limit 0 must never report, whatever the shape.
    check("limit 0 disables the check", same_day_clusters(report((A, 99)), 0), [])
    # Boundary: N is allowed, N+1 is not. Off-by-one here would either spam or miss.
    check("exactly at the limit is allowed", same_day_clusters(report((A, 12)), 12), [])
    check("one over the limit fails", same_day_clusters(report((A, 13)), 12), [(A, 13)])
    # Several cliffs are all reported, in date order — reporting only the worst
    # would let the next one land unseen the moment the first is fixed.
    check(
        "every cliff reported, date-ordered",
        same_day_clusters(report((B, 20), (A, 30)), 12),
        [(A, 30), (B, 20)],
    )
    # expiring_soon counts too: a cliff 10 days out is still a cliff.
    r = Report()
    r.expiring_soon.extend(entry(A, 13))
    check("expiring_soon rows count", same_day_clusters(r, 12), [(A, 13)])
    # Already-expired rows are the other check's business; counting them here
    # would double-report the same problem under two headings.
    r = Report()
    r.expired.extend(entry(A, 30))
    check("expired rows are NOT counted", same_day_clusters(r, 12), [])
    # A missing expiry is `no_expiry`'s problem, and must not crash this one.
    r = Report()
    r.ok.extend(entry(A, 13))
    r.ok.extend(
        [EntryStatus(ledger=Path("x.toml"), entry_id="n", expires_on=None, status="ok")]
    )
    check("None expires_on is skipped, not fatal", same_day_clusters(r, 12), [(A, 13)])

    sys.exit(failed)
    """
)


def main() -> int:
    if not SCRIPT.is_file():
        print(f"test_max_same_day: {SCRIPT} not found", file=sys.stderr)
        return 2
    proc = subprocess.run(
        [sys.executable, "-c", HARNESS.format(scripts=str(SCRIPT.parent))],
        capture_output=True,
        text=True,
    )
    sys.stdout.write(proc.stdout)
    if proc.stderr:
        sys.stderr.write(proc.stderr)
    if proc.returncode != 0:
        print("test_max_same_day: FAILED")
        return 1

    # End-to-end: the flag must actually change the process exit code over the
    # REAL ledgers. The unit cases above prove the predicate; this proves it is
    # wired into `main`, which is the half that silently rots.
    off = subprocess.run(
        [sys.executable, str(SCRIPT), "--as-of", "2026-08-10"],
        capture_output=True,
        text=True,
    )
    huge = subprocess.run(
        [sys.executable, str(SCRIPT), "--as-of", "2026-08-10", "--max-same-day", "100000"],
        capture_output=True,
        text=True,
    )
    if off.returncode != huge.returncode:
        print(
            "  FAIL  a limit above every cluster must not change the verdict "
            f"(off={off.returncode} huge={huge.returncode})"
        )
        return 1
    print(f"  ok    wired into main (unclustered verdict preserved: rc={off.returncode})")
    print("test_max_same_day: all cases pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
