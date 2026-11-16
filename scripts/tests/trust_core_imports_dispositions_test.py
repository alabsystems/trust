#!/usr/bin/env python3
"""Controls for the disposition column of docs/trust-core/denominators/imports.toml.

The column is I-FFI-SPECIFIED's numerator (E2.6.6: an ExtSpec or a named refusal for every std import),
keyed by (exact Mach-O spelling, target, OS release). scripts/trust_core/denominators/imports.py renders
it from the committed [[import_set]] names and its DISPOSITIONS table, and `--check-dispositions` (also
run first by `--check`) validates it without the pinned dylibs. This file shows:

* the committed column passes, and says 0 of 195 on both Apple targets (nothing is specified or refused);
* each mutation of a copy of the committed table is refused by the rule it breaks, beside the unmutated
  control: a dropped row, a row naming no import, a word outside the vocabulary, an unspecified row keyed
  on one release, a wrong count, a row keyed on the other target, a missing column, a hand-edited row that
  obeys every rule but is not the rendering, and an import-set name that no longer matches its digest;
* each DISPOSITIONS entry that breaks a rule is refused (a specified row on every release, a spec path that
  does not exist, a symbol that is not an import, a second row for one release, a listed `unspecified`),
  and a well-formed refused row renders to a column that passes with numerator 1 (the positive control);
* `--write-dispositions` reproduces the committed table byte for byte, and `--check` refuses a mutated
  column with exit 1 on a host that holds none of the pinned inputs (before the exit-3 re-measurement).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import importlib.util
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_core" / "denominators" / "imports.py"
TABLE = ROOT / "docs" / "trust-core" / "denominators" / "imports.toml"
SPEC = importlib.util.spec_from_file_location("trust_core_imports", SCRIPT)
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)

AARCH = "std.aarch64-apple-darwin@stage2-248a9f1dd"
X86 = "std.x86_64-apple-darwin@stage0-8b50cbcc5"


def once(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)


def row(symbol: str, target: str = "aarch64-apple-darwin") -> str:
    return (f'  {{ symbol = "{symbol}", target = "{target}", os_release = "*", '
            'disposition = "unspecified" },\n')


class CommittedColumn(unittest.TestCase):
    def setUp(self):
        self.text = TABLE.read_text(encoding="utf-8")

    def refused(self, text: str, fragment: str, table=None):
        with self.assertRaises(M.Refusal) as ctx:
            M.check_dispositions(text, table)
        self.assertIn(fragment, str(ctx.exception))

    def test_control_passes_and_the_numerator_is_zero_of_195(self):
        summary = M.check_dispositions(self.text)
        self.assertEqual(summary, [
            f"{AARCH}: 0/195 specified or refused (0 specified, 0 refused, 195 unspecified)",
            f"{X86}: 0/195 specified or refused (0 specified, 0 refused, 195 unspecified)",
        ])
        self.assertEqual(M.DISPOSITIONS, [])

    def test_the_key_is_the_exact_spelling(self):
        # x86_64's `$NOCANCEL` variant is its own row; aarch64 has no such import.
        self.assertIn(row("_close$NOCANCEL", "x86_64-apple-darwin"), self.text)
        self.assertNotIn(row("_close$NOCANCEL"), self.text)

    def test_a_dropped_row(self):
        self.refused(once(self.text, row("_fcntl"), ""), "1 imports with no row ['_fcntl']")

    def test_a_row_naming_no_import(self):
        self.refused(once(self.text, row("_fcntl"), row("_fcntl") + row("_pipe2")),
                     "1 rows naming no import ['_pipe2']")

    def test_a_word_outside_the_vocabulary(self):
        self.refused(once(self.text, row("_fcntl"), row("_fcntl").replace('"unspecified"', '"assumed"')),
                     "disposition 'assumed' is not one of")

    def test_an_unspecified_row_keyed_on_one_release(self):
        self.refused(once(self.text, row("_fcntl"), row("_fcntl").replace('"*"', '"26.0"')),
                     "an unspecified row is stated for every release")

    def test_a_wrong_count(self):
        block = f'input = "{AARCH}"'
        at = self.text.index(block)
        mutated = self.text[:at] + self.text[at:].replace("numerator = 0", "numerator = 1", 1)
        self.refused(mutated, "numerator = 1, but the rows give 0")

    def test_a_row_keyed_on_the_other_target(self):
        self.refused(once(self.text, row("_fcntl"), row("_fcntl", "x86_64-apple-darwin")),
                     "keyed on target 'x86_64-apple-darwin' inside the aarch64-apple-darwin block")

    def test_a_missing_column(self):
        at = self.text.index("\n" + M.DISPOSITION_BEGIN)
        self.refused(self.text[:at + 1], "no disposition column")

    def test_a_hand_edit_that_obeys_every_rule_is_still_not_the_rendering(self):
        edited = once(self.text, row("_fcntl"),
                      '  { symbol = "_fcntl", target = "aarch64-apple-darwin", os_release = "26.0", '
                      'disposition = "refused", refusal = "UnmodeledPlatformEffect{_fcntl}", reason = "r" },\n')
        block = f'input = "{AARCH}"'
        at = self.text.index(block)
        tail = edited[at:].replace("numerator = 0", "numerator = 1", 1).replace("refused = 0", "refused = 1", 1)
        edited = edited[:at] + tail.replace("unspecified = 195", "unspecified = 194", 1)
        self.refused(edited, "is not its rendering")

    def test_an_import_set_name_that_no_longer_matches_its_digest(self):
        # The first `_fcntl` line is in the aarch64 std set's [import_set.names] (the rustc_driver set and
        # the x86_64 set list it too).
        self.refused(self.text.replace('  "_fcntl",\n', '  "_fcntl_x",\n', 1),
                     f"[[import_set]] '{AARCH}': read 195 names")


class DispositionTable(unittest.TestCase):
    def setUp(self):
        self.sets = M.committed_import_sets(TABLE.read_text(encoding="utf-8"))

    def entry(self, **over):
        base = {"symbol": "_fcntl", "target": "aarch64-apple-darwin", "os_release": "26.0",
                "disposition": "refused", "refusal": "UnmodeledPlatformEffect{_fcntl}",
                "reason": "the command-split clause is not written"}
        base.update(over)
        return {k: v for k, v in base.items() if v is not None}

    def refused(self, table, fragment):
        with self.assertRaises(M.Refusal) as ctx:
            M.render_dispositions(self.sets, table)
        self.assertIn(fragment, str(ctx.exception))

    def test_a_specified_row_on_every_release(self):
        self.refused([self.entry(disposition="specified", refusal=None, reason=None, os_release="*",
                                 spec="docs/TCB.md#x")], "never '*'")

    def test_a_spec_path_that_does_not_exist(self):
        self.refused([self.entry(disposition="specified", refusal=None, reason=None,
                                 spec="crates/trust-platform/clean/Trust/Platform/Fd.lean#fcntl")],
                     "is not `<existing repo path>#<clause>`")

    def test_a_symbol_that_is_not_an_import(self):
        self.refused([self.entry(symbol="_pipe2")], "names no import")

    def test_a_second_row_for_one_release(self):
        self.refused([self.entry(), self.entry()], "a second row for OS release '26.0'")

    def test_a_listed_unspecified(self):
        self.refused([self.entry(disposition="unspecified", refusal=None, reason=None, os_release="*")],
                     "is neither `specified` nor `refused`")

    def test_a_refused_row_renders_to_a_column_that_passes(self):
        table = [self.entry()]
        head = TABLE.read_text(encoding="utf-8")
        head = head[:head.index("\n" + M.DISPOSITION_BEGIN) + 1]
        text = head.rstrip("\n") + "\n\n" + M.render_dispositions(self.sets, table)
        summary = M.check_dispositions(text, table)
        self.assertEqual(summary[0], f"{AARCH}: 1/195 specified or refused (0 specified, 1 refused, "
                                     "194 unspecified)")
        # The same text under the committed (empty) table is refused: the column must match the table.
        with self.assertRaises(M.Refusal):
            M.check_dispositions(text)


class Cli(unittest.TestCase):
    def run_script(self, *argv):
        return subprocess.run([sys.executable, str(SCRIPT), *argv], capture_output=True, text=True, cwd=ROOT)

    def test_check_dispositions_passes_on_the_committed_table(self):
        run = self.run_script("--check-dispositions")
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("imports: dispositions OK", run.stderr)

    def test_write_dispositions_reproduces_the_committed_table(self):
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / "imports.toml"
            shutil.copyfile(TABLE, copy)
            run = self.run_script("--write-dispositions", "--record", str(copy))
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(copy.read_text(encoding="utf-8"), TABLE.read_text(encoding="utf-8"))

    def test_check_refuses_a_mutated_column_before_it_needs_the_pinned_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / "imports.toml"
            copy.write_text(once(TABLE.read_text(encoding="utf-8"), row("_fcntl"), ""), encoding="utf-8")
            run = self.run_script("--check", "--record", str(copy), "--build-dir", str(Path(tmp) / "build"),
                                  "--atpkg-store", str(Path(tmp) / "store"))
        self.assertEqual(run.returncode, 1, run.stderr[-2000:])
        self.assertIn("imports: REFUSED dispositions:", run.stderr)
        self.assertNotIn("UNAVAILABLE", run.stderr)


if __name__ == "__main__":
    unittest.main()
