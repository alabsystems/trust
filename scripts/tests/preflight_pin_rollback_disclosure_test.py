#!/usr/bin/env python3
"""preflight_pin_rollback_disclosure_test.py — the pin_behind_history hatch, both ways.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

`tools/preflight.py::check_pin_behind_history` refuses a `first-party/*` pin that
is a strict ancestor of one this repo recorded earlier. That is the right default —
an accidental backward walk is invisible in a merge, because a gitlink has no
textual content — but it shipped with NO way to express a DELIBERATE rollback,
and its printed fix was the checkout that restores the offending pin.

That mattered on 2026-08-28: adopting `first-party/clean` ac4874697 (which requires
ay 0.18.0 while six sibling first-party repos require 0.17.0 through the same
patched source URL) split every ay crate in two and stage2 stopped compiling. The
only in-repo repair is a backward walk of that one pin — which preflight then
refused to let anyone build, while telling them to undo the repair.

`scripts/check_pin_regression.sh` already states the convention this restores:
"THE ESCAPE HATCH IS DISCLOSURE, NOT SUPPRESSION" — say it in the commit message
as `pin-rollback: <path> <why>`, with no env-var off switch.

A hatch is only worth having if the gate can still be SEEN to fail, so this test
builds the same fixture TWICE and asserts opposite verdicts: undisclosed must
FAIL, disclosed must not. A test that only exercised the disclosed side would
pass just as well against a check that had been deleted.

Exit 0 iff both directions hold.
"""

from __future__ import annotations

import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

# `tools/preflight.py` hard-exits without tomllib (3.11+). Re-exec rather than
# skip: a test that quietly passes on an old interpreter is a test that stops
# guarding the moment someone's PATH changes.
if sys.version_info < (3, 11) and not os.environ.get("_PF_TEST_REEXEC"):
    for candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        found = shutil.which(candidate)
        if found:
            os.environ["_PF_TEST_REEXEC"] = "1"
            os.execv(found, [found, str(Path(__file__).resolve()), *sys.argv[1:]])
    sys.stderr.write(
        "preflight pin-rollback disclosure test: needs python >= 3.11 (tools/preflight.py "
        "imports tomllib) and no python3.11+ is on PATH — refusing to report a green skip\n"
    )
    raise SystemExit(1)


def _load_preflight():
    spec = importlib.util.spec_from_file_location("pf_under_test", REPO / "tools" / "preflight.py")
    mod = importlib.util.module_from_spec(spec)
    # dataclasses resolves `cls.__module__` through sys.modules; a module loaded
    # without being registered there crashes in @dataclass on 3.12+.
    sys.modules["pf_under_test"] = mod
    spec.loader.exec_module(mod)
    return mod


def _sh(*args: str, cwd: Path) -> str:
    return subprocess.run(args, cwd=cwd, capture_output=True, text=True, check=True).stdout


def _fixture(disclose: bool) -> Path:
    """A superproject whose first-party gitlink walked BACKWARD by one commit."""
    root = Path(tempfile.mkdtemp())
    sub, sup = root / "sub", root / "sup"
    sub.mkdir()
    sup.mkdir()
    for repo in (sub, sup):
        _sh("git", "init", "-q", ".", cwd=repo)
        _sh("git", "config", "user.email", "t@t", cwd=repo)
        _sh("git", "config", "user.name", "t", cwd=repo)

    (sub / "f").write_text("one\n")
    _sh("git", "add", "f", cwd=sub)
    _sh("git", "commit", "-qm", "one", cwd=sub)
    older = _sh("git", "rev-parse", "HEAD", cwd=sub).strip()
    (sub / "f").write_text("two\n")
    _sh("git", "add", "f", cwd=sub)
    _sh("git", "commit", "-qm", "two", cwd=sub)
    newer = _sh("git", "rev-parse", "HEAD", cwd=sub).strip()

    (sup / "first-party").mkdir()
    _sh("git", "-c", "protocol.file.allow=always", "submodule", "add", "-q",
        "--force", str(sub), "first-party/m", cwd=sup)
    _sh("git", "-C", "first-party/m", "checkout", "-q", newer, cwd=sup)
    _sh("git", "add", "-A", cwd=sup)
    _sh("git", "commit", "-qm", "record the NEWER pin", cwd=sup)

    _sh("git", "-C", "first-party/m", "checkout", "-q", older, cwd=sup)
    _sh("git", "add", "first-party/m", cwd=sup)
    message = "roll it back"
    if disclose:
        message += "\n\npin-rollback: first-party/m deliberate, testing the disclosure path"
    _sh("git", "commit", "-qm", message, cwd=sup)
    return sup


def main() -> int:
    pf = _load_preflight()
    failures: list[str] = []

    for disclose in (False, True):
        report = pf.Report(False)
        pf.check_pin_behind_history(_fixture(disclose), report)
        rows = [f for f in report.findings if f.check == "pin_behind_history"]
        blocking = [f for f in rows if f.severity == pf.FAIL]
        label = "DISCLOSED" if disclose else "UNDISCLOSED"

        if not rows:
            failures.append(f"{label}: the check reported NOTHING; it did not run on the fixture")
        elif disclose and blocking:
            failures.append(f"{label}: a disclosed rollback still FAILs — the hatch does not work")
        elif not disclose and not blocking:
            failures.append(f"{label}: an undisclosed backward walk did NOT fail — the gate is inert")
        else:
            print(f"  OK  {label}: {rows[0].severity}  {rows[0].title}")

    if failures:
        print("\npreflight pin-rollback disclosure test FAILED:")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("\npreflight pin-rollback disclosure test OK: refuses undisclosed, admits disclosed")
    return 0


def load_tests(loader, tests, pattern):
    """`land_gate.py validation-tests` loads this module with unittest (the
    landing gate's selector names it, LAND-SELECT-VALIDATION-REACH-1): main()'s
    undisclosed and disclosed fixtures are one case."""
    def test_pin_rollback_disclosure():
        if main() != 0:
            raise AssertionError("preflight pin-rollback disclosure test FAILED (its cases are printed above)")
    tests.addTest(unittest.FunctionTestCase(test_pin_rollback_disclosure))
    return tests


if __name__ == "__main__":
    raise SystemExit(main())
