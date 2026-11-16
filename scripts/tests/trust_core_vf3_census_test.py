#!/usr/bin/env python3
"""Controls for scripts/trust_core/vf3_census.py (proven-core plan VF3, the proved-row census).

* The REAL census at the committed record's pin reproduces docs/trust-core/denominators/
  vf3-proved-census.tsv byte for byte (`--check` exits 0), and two measurements are identical.
* A record with one row changed, one row removed, or no pin makes `--check` exit 1 (drift is a
  failure, never a pass), beside the unmutated control.
* The reader fails closed: an unknown count word, counts that do not add up, and a report with no
  anchor are errors, and a report with any unproved count is not a proved row.
* The producer restriction: a row is `admitted` only under an effective `-Ztrust-ir-lower=strict`
  with no strict error at it; every other row is `unmeasured` and its fragment's N is `blocked`.
* Every rung of the fragment ladder has a positive and a negative control.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_core" / "vf3_census.py"
SPEC = importlib.util.spec_from_file_location("trust_core_vf3_census", SCRIPT)
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M  # dataclasses resolve string annotations through sys.modules
SPEC.loader.exec_module(M)
C = M.C
RECORD = ROOT / M.RECORD_REL

REPORT = ("note: Trust verification: {p} proved, 0 failed, {u} unknown, 0 timed out, 0 runtime-checked "
          "out of {n} obligation(s)\n  --> $DIR/{f}:{line}:1\n")


def classify(src: str, line: int = 1) -> tuple[str, str]:
    item = M.find_item(src, line)
    assert item is not None, src
    fragment, body, features, _ = M.classify(item, M.defined_fns(src), [])
    return fragment, body


_EMPTY = tempfile.TemporaryDirectory()  # an empty root under the overlay; removed at exit


def tree(files: dict[str, str]) -> "C.DirTree":
    return C.DirTree(Path(_EMPTY.name), files)


class RealCensus(unittest.TestCase):
    def test_check_reproduces_the_record(self):
        self.assertEqual(M.main(["--check", "--repo", str(ROOT)]), 0)

    def test_two_measurements_are_identical(self):
        pin = M.recorded_pin(RECORD.read_text(encoding="utf-8"))
        a = M.render(M.measure(C.GitTree(ROOT, pin)), pin)
        b = M.render(M.measure(C.GitTree(ROOT, pin)), pin)
        self.assertEqual(a, b)
        self.assertEqual(a, RECORD.read_text(encoding="utf-8"))

    def _check_copy(self, mutate) -> int:
        text = RECORD.read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / "census.tsv"
            copy.write_text(mutate(text), encoding="utf-8")
            return M.main(["--check", "--repo", str(ROOT), "--record", str(copy)])

    def test_unmutated_copy_passes(self):
        self.assertEqual(self._check_copy(lambda t: t), 0)

    def test_changed_row_is_drift(self):
        def mutate(t):
            lines = t.split("\n")
            n = next(i for i, l in enumerate(lines) if l.startswith("row\t"))
            cells = lines[n].split("\t")
            cells[5] = "F3" if cells[5] != "F3" else "F4"
            lines[n] = "\t".join(cells)
            return "\n".join(lines)
        self.assertEqual(self._check_copy(mutate), 1)

    def test_removed_row_is_drift(self):
        def mutate(t):
            lines = t.split("\n")
            n = next(i for i, l in enumerate(lines) if l.startswith("row\t"))
            return "\n".join(lines[:n] + lines[n + 1:])
        self.assertEqual(self._check_copy(mutate), 1)

    def test_changed_summary_count_is_drift(self):
        def mutate(t):
            lines = t.split("\n")
            n = next(i for i, l in enumerate(lines) if l.startswith("summary\t"))
            cells = lines[n].split("\t")
            cells[-1] = str(int(cells[-1]) + 1)
            lines[n] = "\t".join(cells)
            return "\n".join(lines)
        self.assertEqual(self._check_copy(mutate), 1)

    def test_trailing_byte_is_drift(self):
        self.assertEqual(self._check_copy(lambda t: t + "\n"), 1)

    def test_no_pin_fails(self):
        self.assertEqual(self._check_copy(lambda t: t.replace("# measured_at_commit\t", "# measured_at\t")), 1)


class Reader(unittest.TestCase):
    SRC = "//@ compile-flags: -Ztrust-verify=on\npub fn f(x: u8) -> u8 {\n    x + 1\n}\n"

    def rows(self, stderr: str, src: str = SRC):
        return M.measure(tree({"tests/ui/t/a.rs": src, "tests/ui/t/a.stderr": stderr}))

    def test_all_proved_is_a_row(self):
        rows = self.rows(REPORT.format(p=1, u=0, n=1, f="a.rs", line=2))
        self.assertEqual([(r.function, r.fragment, r.admission) for r in rows], [("f", "F1", "unmeasured")])

    def test_unknown_count_is_not_proved(self):
        self.assertEqual(self.rows(REPORT.format(p=1, u=1, n=2, f="a.rs", line=2)), [])

    def test_counts_that_do_not_add_up_fail(self):
        with self.assertRaises(M.CensusError):
            self.rows(REPORT.format(p=1, u=0, n=3, f="a.rs", line=2))

    def test_unknown_count_word_fails(self):
        with self.assertRaises(M.CensusError):
            self.rows("note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, "
                      "1 waved out of 2 obligation(s)\n  --> $DIR/a.rs:2:1\n")

    def test_missing_anchor_fails(self):
        with self.assertRaises(M.CensusError):
            self.rows(REPORT.format(p=1, u=0, n=1, f="a.rs", line=2).split("\n")[0] + "\n\n")

    def test_assumed_requires_is_vacuous_pre(self):
        rows = self.rows("note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, "
                         "1 assumed (requires) out of 2 obligation(s)\n  --> $DIR/a.rs:2:1\n")
        self.assertEqual([r.pre for r in rows], ["vacuous-pre"])

    def test_strict_revision_is_admitted_and_others_unmeasured(self):
        src = ("//@ revisions: on strict\n//@ compile-flags: -Ztrust-verify=on\n"
               "//@[strict] compile-flags: -Ztrust-ir-lower=strict\npub fn f(x: u8) -> u8 {\n    x + 1\n}\n")
        files = {"tests/ui/t/a.rs": src,
                 "tests/ui/t/a.on.stderr": REPORT.format(p=1, u=0, n=1, f="a.rs", line=4),
                 "tests/ui/t/a.strict.stderr": REPORT.format(p=1, u=0, n=1, f="a.rs", line=4)}
        rows = M.measure(tree(files))
        self.assertEqual([(r.revision, r.admission) for r in rows], [("on", "unmeasured"), ("strict", "admitted")])
        text = M.render(rows, "0" * 40)
        self.assertIn("vf5-n\tF1\tblocked\t1\t", text)
        only_strict = M.render([r for r in rows if r.admission == "admitted"], "0" * 40)
        self.assertIn("vf5-n\tF1\tmeasured\t1\t-", only_strict)

    def test_strict_error_at_the_row_is_not_admitted(self):
        src = "//@ compile-flags: -Ztrust-verify=on -Ztrust-ir-lower=strict\npub fn f(x: u8) -> u8 {\n    x + 1\n}\n"
        err = ("error: -Ztrust-ir-lower=strict: THIR-derived trust-ir DISAGREES with the built MIR\n"
               "  --> $DIR/a.rs:2:1\n\n")
        self.assertEqual([r.admission for r in self.rows(REPORT.format(p=1, u=0, n=1, f="a.rs", line=2), src)],
                         ["admitted"])
        self.assertEqual([r.admission for r in self.rows(err + REPORT.format(p=1, u=0, n=1, f="a.rs", line=2), src)],
                         ["unmeasured"])

    def test_strict_then_verify_off_is_not_strict(self):
        self.assertTrue(M.strict_effective(["-Ztrust-ir-lower=strict"]))
        self.assertFalse(M.strict_effective(["-Ztrust-ir-lower=strict", "-Ztrust-verify=off"]))
        self.assertFalse(M.strict_effective(["-Ztrust-ir-lower=strict", "-Ztrust-ir-lower=on"]))
        self.assertTrue(M.strict_effective(["-Z", "trust-ir-lower=strict"]))


class Ladder(unittest.TestCase):
    """Each rung: the smallest function that needs it, and its F1 twin one construct away."""

    def test_f1(self):
        self.assertEqual(classify("fn f(a: u32, b: bool) -> u32 { if b { a + 1 } else { a * 3 } }"), ("F1", "F1"))
        self.assertEqual(classify("fn f(a: i64) -> bool { match a { 0 | 1 => true, 2..=9 => false, _ => a < 3 } }"),
                         ("F1", "F1"))

    def test_f1_bv(self):
        self.assertEqual(classify("fn f(a: u32, b: u32) -> u32 { a * b }")[0], "F1-bv")
        self.assertEqual(classify("fn f(a: u32) -> u32 { a >> 3 }")[0], "F1-bv")
        self.assertEqual(classify("fn f(a: u32) -> u64 { a as u64 }")[0], "F1-bv")
        self.assertEqual(classify("fn f(a: u32) -> u32 { a.wrapping_add(1) }")[0], "F1-bv")
        self.assertEqual(classify("fn f(a: u32, b: u32) -> u32 { a & b }")[0], "F1-bv")

    def test_f2(self):
        self.assertEqual(classify("fn g(a: u8) -> u8 { a }\nfn f(a: u8) -> u8 { g(a) }", 2)[0], "F2")
        self.assertEqual(classify("fn f(mut a: u8) -> u8 { while a > 0 { a -= 1; } a }")[0], "F2")
        self.assertEqual(classify("fn f(a: u8) -> u8\n    ensures result == a\n{ a }"), ("F2", "F1"))
        self.assertEqual(classify("fn f(a: u8) -> u8\n    requires a > 0\n{ a - 1 }"), ("F2", "F1"))

    def test_f3(self):
        self.assertEqual(classify("fn f(a: &u8) -> u8 { *a }")[0], "F3")
        self.assertEqual(classify("fn f(a: u8) -> u8 { let b = &a; a }")[0], "F3")
        self.assertEqual(classify("fn f(a: *const u8) -> u8 { 0 }")[0], "F3")

    def test_f4(self):
        self.assertEqual(classify("fn f(a: u8) -> Option<u8> { Some(a) }")[0], "F4")
        self.assertEqual(classify("fn f(a: [u8; 4]) -> u8 { a[0] }")[0], "F4")
        self.assertEqual(classify("fn f(a: u8) -> u8 { assert!(a > 0); a }")[0], "F4")
        self.assertEqual(classify("fn f(a: u8) -> (u8, u8) { (a, a) }")[0], "F4")
        self.assertEqual(classify("fn f(a: Option<u8>) -> u8 { match a { Some(x) => x, None => 0 } }")[0], "F4")

    def test_outside(self):
        self.assertEqual(classify("fn f(a: f64) -> f64 { a }")[0], "outside")
        self.assertEqual(classify("fn f<T>(a: T) -> T { a }")[0], "outside")
        self.assertEqual(classify("fn f(a: u8) -> u8 { let g = |x: u8| x; a }")[0], "outside")

    def test_if_is_not_a_macro(self):
        self.assertEqual(classify("fn g(a: u8) -> bool { a > 0 }\nfn f(a: u8) -> u8 { if !g(a) { 0 } else { a } }", 2)[0],
                         "F2")

    def test_comments_and_strings_do_not_count(self):
        self.assertEqual(classify("fn f(a: u8) -> u8 { /* a[0] & *b */ a + 1 // loop\n }"), ("F1", "F1"))
        self.assertEqual(classify('fn f(a: u8) -> usize { let _ = "x"; 0 }')[0], "F4")


if __name__ == "__main__":
    unittest.main()
