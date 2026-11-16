"""Tests for scripts/luminal_domination.py, the count of Luminal capabilities met.

Each case is a fixture ledger and a fixture plan in a temporary directory and
the program run as the gate runs it. What is held:

  * a ledger the schema refuses is INVALID (exit 2): a wrong schema number, a
    duplicate id, a `cwd` that is absolute or climbs out, a package the plan
    does not have, an observation row carrying an exit, a maturity or kind that
    is not a string, an exit without a `luminal_oracle`, `proved` claimed for a
    row whose stated oracle is `tolerance`, and an `exact` oracle on a row
    whose luminal_validation describes a tolerance comparison in any of the
    committed ledger's wordings;
  * the default mode runs nothing and never counts a row as met;
  * under --run a row is met only when its command exits 0 in that run and
    prints `LUMINAL-ROW <id> PASS`: a command that exits 0 without the line and
    a command that prints the line and exits non-zero are both not met, and the
    run exits 1;
  * --require-all runs the commands itself and exits 1 unless every capability
    row is met;
  * the pins (--expect-named, --expect-total) refuse a ledger that moved;
  * a sibling repository resolves through first-party/ or TRUST_SIBLING_<REPO>,
    and a row whose sibling resolves nowhere is not met;
  * the committed ledger validates against the committed plan, and holds
    exactly the counts the gate manifest's row pins;
  * the gate manifest's `--run` row runs every named exit, unfiltered, as a
    required slow row and never in the push profile.

    python3 -B scripts/tests/luminal_domination_test.py

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Dict, List, Optional

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts" / "luminal_domination.py"
HARNESS = REPO / "tests" / "run_trust_comprehensive_harness.sh"
MANIFEST_ROW = "fast.luminal-domination-ledger"
RUN_ROW = "slow.luminal-domination-met"

PLAN = "| ID | Goal | Exit | Depends on |\n|---|---|---|---|\n" + "".join(
    f"| PKG-U{n} | a goal | an exit | — |\n" for n in (1, 2, 3)
)


def capability(row_id: str, **changes) -> dict:
    row = {
        "id": row_id,
        "area": "an-area",
        "kind": "capability",
        "package": "PKG-U1",
        "capability": "does a thing",
        "luminal_evidence": "src/thing.rs:1",
        "luminal_validation": "a unit test compares outputs exactly",
        "luminal_maturity": "solid",
        "exit": None,
    }
    row.update(changes)
    return row


def observation(row_id: str, **changes) -> dict:
    return capability(row_id, **{"kind": "observation", "package": None, **changes})


def exit_(argv: List[str], **changes) -> dict:
    value = {"repo": "trust", "cwd": ".", "argv": argv, "evidence": "sampled",
             "luminal_oracle": "exact", "trust_form": ""}
    value.update(changes)
    return value


def prints(text: str, status: int = 0) -> List[str]:
    """A command that prints `text` and exits `status`."""
    return [sys.executable, "-c", f"import sys; print({text!r}); sys.exit({status})"]


def passes(row_id: str) -> List[str]:
    return prints(f"LUMINAL-ROW {row_id} PASS")


class LuminalDominationTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="luminal-domination-test-")
        self.addCleanup(self._tmp.cleanup)
        self.tmp = Path(self._tmp.name)
        (self.tmp / "PLAN.md").write_text(PLAN, encoding="utf-8")

    def ledger(self, rows: List[dict], **top) -> Path:
        doc = {
            "schema": 2,
            "luminal_repository": "https://example.invalid/luminal",
            "luminal_commit": "abc1234",
            "capabilities": rows,
        }
        doc.update(top)
        directory = self.tmp / "ledger"
        directory.mkdir(exist_ok=True)
        (directory / "capabilities.json").write_text(json.dumps(doc), encoding="utf-8")
        return directory

    def run_script(self, *args: str, ledger: Optional[Path] = None,
                   env: Optional[Dict[str, str]] = None) -> subprocess.CompletedProcess:
        command = [sys.executable, "-B", str(SCRIPT), "--plan", str(self.tmp / "PLAN.md")]
        if ledger is not None:
            command += ["--ledger", str(ledger)]
        return subprocess.run([*command, *args], capture_output=True, text=True, timeout=120,
                              env={**os.environ, **(env or {})})

    def assert_invalid(self, rows: List[dict], needle: str, **top) -> None:
        proc = self.run_script(ledger=self.ledger(rows, **top))
        self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)
        self.assertIn("luminal-domination: INVALID:", proc.stderr)
        self.assertIn(needle, proc.stderr)
        self.assertEqual(proc.stdout, "", "an invalid ledger prints no count")

    # -- the default mode -------------------------------------------------

    def test_default_mode_counts_named_rows_and_runs_nothing(self):
        marker = self.tmp / "ran"
        touch = [sys.executable, "-c", f"open({str(marker)!r}, 'w').close()"]
        rows = [capability("a", exit=exit_(touch)), capability("b", luminal_maturity="docs-only"),
                observation("c")]
        proc = self.run_script(ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(
            proc.stdout,
            "luminal-domination: named 1 of 2 capability rows (exit commands not run; met is "
            "unknown); 1 observation rows are outside the count; 1 of the 2 are described by "
            "Luminal and not published (Luminal abc1234)\n")
        self.assertFalse(marker.exists(), "the default mode ran an exit command")
        self.assertNotRegex(proc.stdout, r"\bmet [0-9]", "an unrun row was counted as met")

    def test_groups_count_capability_rows_only(self):
        rows = [capability("a", area="x", package="PKG-U2", exit=exit_(passes("a"))),
                capability("b", area="x", package="PKG-U1"),
                capability("c", area="y", package="PKG-U1"), observation("d", area="y")]
        proc = self.run_script("--by-area", "--by-package", ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(proc.stdout.splitlines()[1:],
                         ["  x: 1 of 2", "  y: 0 of 1", "  PKG-U1: 0 of 2", "  PKG-U2: 1 of 1"])

    # -- what the schema refuses ------------------------------------------

    def test_bad_schema_is_invalid(self):
        self.assert_invalid([capability("a")], "schema is 1, expected 2", schema=1)

    def test_a_row_with_another_key_set_is_invalid(self):
        row = capability("a")
        del row["kind"]
        self.assert_invalid([row], "keys are")
        self.assert_invalid([capability("a", note="extra")], "keys are")

    def test_duplicate_id_is_invalid(self):
        self.assert_invalid([capability("a"), capability("a")], "duplicate id")

    def test_an_exit_cwd_outside_its_repository_is_invalid(self):
        for cwd in ("/tmp", "../elsewhere", "crates/../../elsewhere"):
            with self.subTest(cwd=cwd):
                self.assert_invalid([capability("a", exit=exit_(passes("a"), cwd=cwd))],
                                    "exit.cwd must be relative and stay inside its repository")

    def test_a_malformed_exit_is_invalid(self):
        good = exit_(passes("a"))
        for change, needle in (({"argv": []}, "exit.argv"), ({"argv": ["ok", ""]}, "exit.argv"),
                               ({"evidence": "tested"}, "exit.evidence"),
                               ({"evidence": ["proved"]}, "exit.evidence"),
                               ({"luminal_oracle": "close"}, "exit.luminal_oracle"),
                               ({"luminal_oracle": None}, "exit.luminal_oracle"),
                               ({"repo": "../trust"}, "exit.repo"),
                               ({"trust_form": None}, "exit.trust_form")):
            with self.subTest(change=change):
                self.assert_invalid([capability("a", exit={**good, **change})], needle)
        legacy = {"cwd": ".", "argv": passes("a")}
        self.assert_invalid([capability("a", exit=legacy)], "exit must be null or an object")

    def test_a_package_the_plan_does_not_have_is_invalid(self):
        self.assert_invalid([capability("a", package="PKG-U9"), capability("b", package="PKG-U9")],
                            "package PKG-U9 is not a table row of")
        self.assert_invalid([capability("a", package="PKG-C6a")], "is not `PKG-U<n>`")
        self.assert_invalid([capability("a", package=None)], "is not `PKG-U<n>`")

    def test_a_plan_with_no_package_row_is_invalid(self):
        (self.tmp / "PLAN.md").write_text("# Plan\n\nPKG-U1 is mentioned in prose only.\n",
                                          encoding="utf-8")
        self.assert_invalid([capability("a")], "no table row starts `| PKG-U<n> |`")

    def test_an_observation_row_with_an_exit_or_a_package_is_invalid(self):
        self.assert_invalid([capability("a"), observation("b", exit=exit_(passes("b")))],
                            "an observation row has no exit")
        self.assert_invalid([capability("a"), observation("b", package="PKG-U1")],
                            "an observation row has no package")

    def test_proved_on_a_tolerance_row_is_invalid(self):
        tolerance = "outputs compared within a 1e-5 Tolerance"
        self.assert_invalid(
            [capability("a", luminal_validation=tolerance,
                        exit=exit_(passes("a"), evidence="proved", luminal_oracle="tolerance"))],
            "a tolerance comparison is sampled evidence, never proof")
        # The same row as sampled evidence is a valid ledger.
        rows = [capability("a", luminal_validation=tolerance,
                           exit=exit_(passes("a"), luminal_oracle="tolerance"))]
        self.assertEqual(self.run_script(ledger=self.ledger(rows)).returncode, 0)

    def test_an_exact_oracle_on_a_tolerance_description_is_invalid(self):
        # Wordings the committed ledger uses for tolerance tests, most of them
        # without the word "tolerance": the prose refuses `exact` for each.
        for wording in ("compares against candle with assert_close at 1e-3 absolute",
                        "compare logits across backends at <1e-4",
                        "matches the reference (1.5e-7), i.e. an approximation",
                        "np.allclose with atol and rtol",
                        "outputs compared within a 1e-5 Tolerance"):
            with self.subTest(wording=wording):
                self.assert_invalid(
                    [capability("a", luminal_validation=wording,
                                exit=exit_(passes("a"), evidence="proved"))],
                    "exit.luminal_oracle is `exact` but luminal_validation describes")

    def test_a_maturity_or_kind_that_is_not_a_string_is_invalid(self):
        self.assert_invalid([capability("a", luminal_maturity=["solid"])], "luminal_maturity")
        self.assert_invalid([capability("a", luminal_maturity={"solid": 1})], "luminal_maturity")
        self.assert_invalid([capability("a", kind=["capability"])], "kind")

    # -- --run ------------------------------------------------------------

    def test_run_counts_a_row_whose_command_passes_and_prints_its_line(self):
        rows = [capability("a", exit=exit_(passes("a"), evidence="proved")),
                capability("b", exit=exit_(passes("b"), evidence="refused-by-design")),
                capability("c"), observation("d")]
        proc = self.run_script("--run", ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertTrue(proc.stdout.startswith(
            "luminal-domination: met 2 of 3 capability rows "
            "(proved 1, sampled 0, refused-by-design 1); 1 observation rows"), proc.stdout)

    def test_exit_zero_without_the_pass_line_is_not_met(self):
        # A sweep that exits 0 with every test ignored prints no PASS line; so
        # does a command that prints another row's line.
        for argv in (prints("test result: ok. 0 passed; 0 failed; 12 ignored"), passes("b"),
                     prints("LUMINAL-ROW a PASSED"), prints("note: LUMINAL-ROW a PASS expected")):
            with self.subTest(argv=argv[-1]):
                proc = self.run_script("--run", ledger=self.ledger([capability("a", exit=exit_(argv))]))
                self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
                self.assertIn("met 0 of 1 capability rows", proc.stdout)
                self.assertIn("NOT MET: a: the command exited 0 without printing "
                              "`LUMINAL-ROW a PASS`", proc.stderr)

    def test_a_failing_command_is_never_counted_as_met(self):
        failing = prints("LUMINAL-ROW a PASS", status=3)
        rows = [capability("a", exit=exit_(failing)), capability("b", exit=exit_(passes("b")))]
        proc = self.run_script("--run", "--by-area", ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("met 1 of 2 capability rows (proved 0, sampled 1, refused-by-design 0)",
                      proc.stdout)
        self.assertIn("  an-area: 1 of 2", proc.stdout)
        self.assertIn("NOT MET: a: the command exited 3", proc.stderr)

    def test_a_command_that_cannot_start_is_not_met(self):
        rows = [capability("a", exit=exit_(["zz-no-such-program-luminal-domination"]))]
        proc = self.run_script("--run", ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("NOT MET: a: the command did not start", proc.stderr)
        rows = [capability("a", exit=exit_(passes("a"), cwd="zz-no-such-directory"))]
        proc = self.run_script("--run", ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("NOT MET: a: exit.cwd 'zz-no-such-directory' is not a directory", proc.stderr)

    # -- --require-all ----------------------------------------------------

    def test_require_all_runs_the_commands_and_refuses_an_unmet_row(self):
        marker = self.tmp / "ran"
        touch = [sys.executable, "-c",
                 f"open({str(marker)!r}, 'w').close(); print('LUMINAL-ROW a PASS')"]
        rows = [capability("a", exit=exit_(touch)), capability("b")]
        proc = self.run_script("--require-all", ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertTrue(marker.exists(), "--require-all did not run the named command")
        self.assertIn("met 1 of 2 capability rows", proc.stdout)
        self.assertIn("--require-all: 1 of 2 capability rows are not met", proc.stderr)

    def test_require_all_does_not_take_a_named_row_on_its_word(self):
        # Every row is named, and one command fails: named 2 of 2 is not met 2 of 2.
        rows = [capability("a", exit=exit_(passes("a"))),
                capability("b", exit=exit_(prints("nothing")))]
        proc = self.run_script("--require-all", ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("met 1 of 2 capability rows", proc.stdout)

    def test_require_all_passes_when_every_capability_row_is_met(self):
        rows = [capability("a", exit=exit_(passes("a"))), observation("b")]
        proc = self.run_script("--require-all", ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("met 1 of 1 capability rows", proc.stdout)

    # -- --package --------------------------------------------------------

    def test_package_restricts_the_count_and_the_run_to_its_rows(self):
        marker = self.tmp / "ran-other"
        other = [sys.executable, "-c",
                 f"open({str(marker)!r}, 'w').close(); print('LUMINAL-ROW c PASS')"]
        rows = [capability("a", package="PKG-U2", exit=exit_(passes("a"))),
                capability("b", package="PKG-U2", luminal_maturity="docs-only"),
                capability("c", package="PKG-U1", exit=exit_(other)),
                capability("d", package="PKG-U3"), observation("e")]
        ledger = self.ledger(rows)
        proc = self.run_script("--package", "PKG-U2", "--by-package", ledger=ledger)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(proc.stdout.splitlines(), [
            "luminal-domination: named 1 of 2 capability rows of PKG-U2 (exit commands not run; "
            "met is unknown); 1 observation rows are outside the count; 1 of the 2 are described "
            "by Luminal and not published (Luminal abc1234)", "  PKG-U2: 1 of 2"])
        # A package's own exit: only its rows run, and one unmet row of it refuses.
        proc = self.run_script("--run", "--require-all", "--package", "PKG-U2", ledger=ledger)
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("met 1 of 2 capability rows of PKG-U2", proc.stdout)
        self.assertIn("--require-all: 1 of 2 capability rows of PKG-U2 are not met", proc.stderr)
        self.assertFalse(marker.exists(), "--package ran another package's exit command")
        # Met in full for one package, whatever the other packages' rows are.
        proc = self.run_script("--require-all", "--package", "PKG-U1", ledger=ledger)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("met 1 of 1 capability rows of PKG-U1", proc.stdout)
        # Repeatable; the pins compare the restricted counts.
        proc = self.run_script("--package", "PKG-U3", "--package", "PKG-U1", "--expect-named", "1",
                               "--expect-total", "2", ledger=ledger)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("named 1 of 2 capability rows of PKG-U1, PKG-U3", proc.stdout)

    def test_a_package_with_no_row_met_fails_its_exit(self):
        rows = [capability("a", package="PKG-U2"), capability("b", package="PKG-U2")]
        proc = self.run_script("--run", "--require-all", "--package", "PKG-U2",
                               ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("met 0 of 2 capability rows of PKG-U2", proc.stdout)

    def test_a_package_no_capability_row_names_is_an_error(self):
        rows = [capability("a", package="PKG-U2"), observation("b")]
        for package in ("PKG-U3", "PKG-U9", "PKG-C6a"):
            with self.subTest(package=package):
                proc = self.run_script("--run", "--require-all", "--package", package,
                                       ledger=self.ledger(rows))
                self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)
                self.assertIn(f"INVALID: --package {package}: no capability row names it",
                              proc.stderr)
                self.assertEqual(proc.stdout, "")

    def test_package_still_validates_the_whole_ledger(self):
        rows = [capability("a", package="PKG-U2"), capability("b", package="PKG-U9")]
        proc = self.run_script("--package", "PKG-U2", ledger=self.ledger(rows))
        self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)
        self.assertIn("package PKG-U9 is not a table row of", proc.stderr)

    # -- the pins ---------------------------------------------------------

    def test_the_pins_refuse_a_ledger_that_moved(self):
        rows = [capability("a", exit=exit_(passes("a"))), capability("b"), observation("c")]
        ledger = self.ledger(rows)
        ok = self.run_script("--expect-named", "1", "--expect-total", "2", ledger=ledger)
        self.assertEqual(ok.returncode, 0, ok.stderr)
        for named, total in (("0", "2"), ("1", "3"), ("2", "2")):
            with self.subTest(named=named, total=total):
                proc = self.run_script("--expect-named", named, "--expect-total", total,
                                       ledger=ledger)
                self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
                self.assertIn(f"PIN MISMATCH: expected named {named} of {total}, the ledger has "
                              "named 1 of 2", proc.stderr)
        alone = self.run_script("--expect-named", "1", ledger=ledger)
        self.assertEqual(alone.returncode, 2, "one pin without the other is a usage error")

    # -- siblings ---------------------------------------------------------

    def test_a_sibling_resolves_through_its_environment_variable_or_not_at_all(self):
        repo = "zz-no-such-sibling"
        self.assertFalse((REPO / "first-party" / repo).exists())
        rows = [capability("a", exit=exit_(passes("a"), repo=repo, cwd="sub"))]
        ledger = self.ledger(rows)
        variable = "TRUST_SIBLING_ZZ_NO_SUCH_SIBLING"
        absent = {key: value for key, value in os.environ.items() if key != variable}
        proc = subprocess.run(
            [sys.executable, "-B", str(SCRIPT), "--plan", str(self.tmp / "PLAN.md"), "--ledger",
             str(ledger), "--run"], capture_output=True, text=True, timeout=120, env=absent)
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("met 0 of 1 capability rows", proc.stdout)
        self.assertIn(f"NOT MET: a: sibling `{repo}` is not at first-party/{repo} and {variable} "
                      "names no directory", proc.stderr)
        sibling = self.tmp / "sibling"
        (sibling / "sub").mkdir(parents=True)
        proc = self.run_script("--run", ledger=ledger, env={variable: str(sibling)})
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("met 1 of 1 capability rows", proc.stdout)

    # -- the committed ledger ---------------------------------------------

    def test_the_committed_ledger_validates_and_holds_the_manifest_pins(self):
        rows = [line for line in HARNESS.read_text(encoding="utf-8").splitlines()
                if line.startswith(MANIFEST_ROW + "|")]
        self.assertEqual(len(rows), 1, f"the gate manifest has one {MANIFEST_ROW} row")
        command = rows[0].split("|", 5)[5]
        pins = re.fullmatch(
            r"python3 -B scripts/luminal_domination\.py --ledger tests/luminal-domination "
            r"--expect-named ([0-9]+) --expect-total ([0-9]+)", command)
        self.assertIsNotNone(pins, command)
        named, total = pins.groups()
        # The row's own command, against the committed plan (no --plan override).
        proc = subprocess.run([sys.executable, "-B", str(SCRIPT), "--ledger",
                               "tests/luminal-domination", "--expect-named", named,
                               "--expect-total", total],
                              cwd=REPO, capture_output=True, text=True, timeout=120)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertTrue(proc.stdout.startswith(
            f"luminal-domination: named {named} of {total} capability rows "
            "(exit commands not run; met is unknown); "), proc.stdout)
        self.assertGreater(int(total), 400, "the denominator is Luminal's capabilities")

    def test_the_run_row_runs_every_named_exit_outside_the_push_profile(self):
        rows = [line.split("|", 5) for line in HARNESS.read_text(encoding="utf-8").splitlines()
                if line.startswith(RUN_ROW + "|")]
        self.assertEqual(len(rows), 1, f"the gate manifest has one {RUN_ROW} row")
        _, profiles, _, required, _, command = rows[0]
        # Every named row, so no --package filter and no pin: a row that is
        # named and stops passing turns this row red.
        self.assertEqual(command, "python3 -B scripts/luminal_domination.py --ledger "
                                  "tests/luminal-domination --run")
        self.assertEqual(required, "true")
        self.assertIn("slow", profiles.split(","))
        self.assertNotIn("push", profiles.split(","),
                         "the exits build trust-ir's test graph and SemR")


def main() -> int:
    return 0 if unittest.main(exit=False).result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
