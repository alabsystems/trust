#!/usr/bin/env python3
"""tests/upstream-rust/check_exception_lanes.py: the lane gate and `--run`.

`--run` is how every `suite.*` harness row honors the waiver ledger. It is
driven here against a fake `x.py` that records its argv and fails the tests it
is told to, so what a row hands x.py is asserted without a stage2 build:
  * only rows observed on the command's own lane are skipped, never another
    lane's, an expired row, a retired row, or a kind that nets no failure;
  * an unwaived failure still fails the run, and a ledger with findings runs
    nothing;
  * a skipped test that passes when run alone is reported with `WARN:`;
  * every real `suite.*` row routes through `--run` and dry-runs clean.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CHECKER = REPO / "tests" / "upstream-rust" / "check_exception_lanes.py"
HARNESS = REPO / "tests" / "run_trust_comprehensive_harness.sh"

# The checker re-execs itself when this interpreter has no TOML parser; loaded
# as a module that would replace THIS process, so turn it off and let a missing
# parser fail the tests instead.
os.environ["TRUST_LANES_PY_REEXEC"] = "1"
_spec = importlib.util.spec_from_file_location("check_exception_lanes", CHECKER)
lanes = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(lanes)

TODAY = "2026-09-29"

LEDGER = """
schema_version = "0.1.0"

[[exceptions]]
id = "both-lanes"
suite = "ui"
path = "tests/ui/a.rs"
kind = "intentional_divergence"
status = "active"
expires_on = "2099-01-01"

[[exceptions]]
id = "vanilla-only"
suite = "ui"
path = "tests/ui/b.rs"
kind = "expected_fail"
status = "active"
expires_on = "2099-01-01"

[[exceptions]]
id = "expired"
suite = "ui"
path = "tests/ui/c.rs"
kind = "expected_fail"
status = "active"
expires_on = "2026-09-28"

[[exceptions]]
id = "skip-kind"
suite = "ui"
path = "tests/ui/d.rs"
kind = "expected_skip"
status = "active"
expires_on = "2099-01-01"

[[exceptions]]
id = "fulldeps"
suite = "ui-fulldeps"
path = "tests/ui-fulldeps/e.rs"
kind = "expected_fail"
status = "active"
expires_on = "2099-01-01"

[[exceptions]]
id = "retired"
suite = "ui"
path = "tests/ui/f.rs"
kind = "expected_fail"
status = "resolved"
expires_on = "2099-01-01"
"""


def lane_row(exc_id: str, lane: str) -> str:
    return (
        f'[[lanes]]\nid = "{exc_id}"\nlane = "{lane}"\n'
        f'measured_on = "2026-09-29"\nevidence = "run {exc_id}/{lane}"\n'
    )


LANES = "verified_lane_available = false\n" + "".join(
    lane_row(exc_id, lane)
    for exc_id, lane in (
        ("both-lanes", "vanilla"),
        ("both-lanes", "default"),
        ("vanilla-only", "vanilla"),
        ("expired", "default"),
        ("skip-kind", "default"),
        ("fulldeps", "default"),
    )
)

# Exits 1 when a test named in FAKE_XPY_FAILING is selected and not skipped,
# and 97 when it inherits the checker's re-exec marker (set above).
FAKE_XPY = r"""
import json, os, sys
if "TRUST_LANES_PY_REEXEC" in os.environ:
    sys.exit(97)
args = sys.argv[1:]
with open(os.environ["FAKE_XPY_LOG"], "a") as log:
    log.write(json.dumps(args) + "\n")
skipped = {args[i + 1] for i, a in enumerate(args[:-1]) if a == "--skip"}
roots = [a for i, a in enumerate(args) if a.startswith("tests/") and (i == 0 or args[i - 1] != "--skip")]
failing = [t for t in os.environ.get("FAKE_XPY_FAILING", "").split(":") if t]
selected = [t for t in failing if t not in skipped and any(t == r or t.startswith(r + "/") for r in roots)]
sys.exit(1 if selected else 0)
"""


class RunWithWaivers(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="exception-lanes-"))
        self.addCleanup(lambda: subprocess.run(["rm", "-rf", str(self.tmp)], check=False))
        for rel in ("tests/ui/a.rs", "tests/ui/b.rs", "tests/ui/c.rs", "tests/ui/d.rs", "tests/ui-fulldeps/e.rs"):
            (self.tmp / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.tmp / rel).write_text("fn main() {}\n")
        self.xpy = self.tmp / "x.py"
        self.xpy.write_text(FAKE_XPY)
        self.log = self.tmp / "xpy.log"
        self.ledger = lanes.load_toml_text(LEDGER)
        self.lanes_doc = lanes.load_toml_text(LANES)

    def run_rows(self, *args: str, failing: tuple[str, ...] = (), lanes_doc=None, dry_run=False):
        os.environ["FAKE_XPY_LOG"] = str(self.log)
        os.environ["FAKE_XPY_FAILING"] = ":".join(failing)
        out = io.StringIO()
        err = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = lanes.run_with_waivers(
                [sys.executable, str(self.xpy), "test", "--stage", "2", *args],
                self.ledger,
                self.lanes_doc if lanes_doc is None else lanes_doc,
                lanes.SELF_TEST_SOURCES_NO_LANE,
                today=TODAY,
                repo_root=self.tmp,
                dry_run=dry_run,
            )
        calls = [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []
        return status, calls, out.getvalue(), err.getvalue()

    @staticmethod
    def skips(argv: list[str]) -> list[str]:
        return [argv[i + 1] for i, a in enumerate(argv[:-1]) if a == "--skip"]

    def test_default_lane_skips_only_its_own_rows(self) -> None:
        status, calls, out, _ = self.run_rows("tests/ui", failing=("tests/ui/a.rs",))
        self.assertEqual(status, 0, out)
        self.assertEqual(calls[0], ["test", "--stage", "2", "tests/ui", "--skip", "tests/ui/a.rs"])
        # The waived test is then run alone, still fails, and is not reported.
        self.assertEqual(calls[1:], [["test", "--stage", "2", "tests/ui/a.rs"]])
        self.assertNotIn("WARN:", out)
        self.assertIn("still fails", out)
        self.assertIn("[vanilla-only] is waived only on ['vanilla'], not default", out)
        self.assertIn("[expired] waiver expired", out)
        self.assertIn("[skip-kind] kind 'expected_skip' nets no failure", out)
        self.assertNotIn("retired", out)

    def test_an_unwaived_failure_still_fails_and_is_not_probed(self) -> None:
        for failing in ("tests/ui/b.rs", "tests/ui/c.rs", "tests/ui/d.rs", "tests/ui/f.rs"):
            with self.subTest(failing=failing):
                self.log.unlink(missing_ok=True)
                status, calls, _, _ = self.run_rows("tests/ui", failing=("tests/ui/a.rs", failing))
                self.assertEqual(status, 1)
                self.assertEqual(len(calls), 1, calls)

    def test_a_waived_test_that_passes_is_reported(self) -> None:
        status, calls, out, _ = self.run_rows("tests/ui")
        self.assertEqual(status, 0)
        self.assertEqual(len(calls), 2)
        self.assertIn("WARN: both-lanes: tests/ui/a.rs exits 0 alone on the default lane", out)

    def test_a_waived_path_that_is_gone_is_reported(self) -> None:
        (self.tmp / "tests/ui/a.rs").unlink()
        status, calls, out, _ = self.run_rows("tests/ui")
        self.assertEqual(status, 0)
        self.assertEqual(len(calls), 1)
        self.assertIn("WARN: both-lanes waives tests/ui/a.rs, which does not exist", out)

    def test_the_lane_is_read_off_the_command(self) -> None:
        _, calls, _, _ = self.run_rows("--trust-vanilla", "tests/ui", dry_run=True)
        self.assertEqual(calls, [])
        _, _, out, _ = self.run_rows("--trust-vanilla", "tests/ui", dry_run=True)
        self.assertIn("waiver lane: vanilla", out)
        self.assertIn("--skip tests/ui/a.rs --skip tests/ui/b.rs\n", out)
        status, calls, _, _ = self.run_rows("--trust-verified", "tests/ui", failing=("tests/ui/a.rs",))
        self.assertEqual(status, 1)
        self.assertEqual(self.skips(calls[0]), [])

    def test_a_suite_path_is_a_path_boundary(self) -> None:
        _, calls, _, _ = self.run_rows("tests/ui-fulldeps")
        self.assertEqual(self.skips(calls[0]), ["tests/ui-fulldeps/e.rs"])
        self.log.unlink()
        _, calls, _, _ = self.run_rows("tests/ui")
        self.assertNotIn("tests/ui-fulldeps/e.rs", self.skips(calls[0]))

    def test_several_suites_probe_one_test_each(self) -> None:
        status, calls, _, _ = self.run_rows("tests/ui", "tests/ui-fulldeps", "--no-fail-fast")
        self.assertEqual(status, 0)
        self.assertEqual(self.skips(calls[0]), ["tests/ui/a.rs", "tests/ui-fulldeps/e.rs"])
        self.assertEqual(
            calls[1:],
            [
                ["test", "--stage", "2", "--no-fail-fast", "tests/ui/a.rs"],
                ["test", "--stage", "2", "--no-fail-fast", "tests/ui-fulldeps/e.rs"],
            ],
        )

    def test_a_ledger_with_findings_runs_nothing(self) -> None:
        unassigned = lanes.load_toml_text(LANES.replace('id = "fulldeps"', 'id = "ghost"'))
        status, calls, _, err = self.run_rows("tests/ui", lanes_doc=unassigned)
        self.assertEqual(status, 1)
        self.assertEqual(calls, [])
        self.assertIn("fulldeps: NO lane assignment", err)

    def test_refusals(self) -> None:
        for argv, needle in (
            (["cargo", "test"], "wraps an `x.py test` command"),
            ([sys.executable, str(self.xpy), "build", "tests/ui"], "wraps an `x.py test` command"),
            ([sys.executable, str(self.xpy), "test", "--trust-vanilla", "--trust-verified", "tests/ui"], "together"),
            ([sys.executable, str(self.xpy), "test", "--skip", "tests/ui/a.rs"], "names no tests/"),
        ):
            with self.subTest(argv=argv):
                err = io.StringIO()
                with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
                    status = lanes.run_with_waivers(
                        argv, self.ledger, self.lanes_doc, lanes.SELF_TEST_SOURCES_NO_LANE,
                        today=TODAY, repo_root=self.tmp, run=lambda argv: self.fail("ran"),
                    )
                self.assertEqual(status, 2)
                self.assertIn(needle, err.getvalue())


class RealTree(unittest.TestCase):
    def checker(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(CHECKER), *args], cwd=REPO, capture_output=True, text=True
        )

    def test_self_test_and_real_ledger(self) -> None:
        for args in (("--self-test",), ()):
            with self.subTest(args=args):
                proc = self.checker(*args)
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_every_suite_row_runs_through_its_lane_waivers(self) -> None:
        listing = subprocess.run(
            ["bash", str(HARNESS), "--list", "suites"],
            cwd=REPO, capture_output=True, text=True, check=True,
        ).stdout
        rows = [line.split("\t") for line in listing.splitlines() if line.startswith("suite.")]
        self.assertGreater(len(rows), 10)
        prefix = "tests/upstream-rust/check_exception_lanes.py --run -- "
        for gate_id, _category, _required, _last_green, command in rows:
            with self.subTest(gate_id=gate_id):
                self.assertTrue(command.startswith(prefix + "python3 x.py test --stage 2 tests/"), command)
                proc = self.checker("--run", "--dry-run", "--", *command[len(prefix):].split())
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                self.assertIn("waiver lane: default", proc.stdout)
                self.assertIn(f"command: {command[len(prefix):]}", proc.stdout)


if __name__ == "__main__":
    unittest.main()
