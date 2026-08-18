#!/usr/bin/env python3
"""Self-test for scripts/trust_ir_rowdiff.py.

The instrument this file tests exists because four consecutive merge reviews certified
"0 lost, 0 new mismatch" while three `#[derive(Clone)]` bodies silently dropped from
real bodies (20/35/20 trust-ir instructions) to 1-instruction stubs. A defect in a
measuring device is worse than a defect in the thing measured, so the fix is proved
here BY MUTATION rather than asserted:

  * `test_blind_spot_is_real` reconstructs the exact published review table
    (agreed 1540->1541, unsupported 12228 both sides, mismatch 1->0) and asserts the
    OLD comparator tuple reports the three collapsed bodies as UNremarkable -- i.e.
    the blind spot is reproduced here, not taken on trust;
  * `test_stub_collapse_is_a_reported_row` asserts the new tool names exactly those
    three bodies in the STUB COLLAPSE class and exits non-zero;
  * `test_loss_and_gain_do_not_cancel` asserts a simultaneous loss+gain, which leaves
    every total unchanged, is still reported as 1 LOST and 1 GAINED.

Run directly (`python3 scripts/tests/trust_ir_rowdiff_test.py`) or via
`scripts/check_script_tests.sh`.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import trust_ir_rowdiff as rd  # noqa: E402

classify = rd.classify_markers


THE_THREE = [
    "<env::algebra_rat_quotient::SumTree as std::clone::Clone>::clone",
    "<env::inductive_no_confusion::NoConfusionCandidate as std::clone::Clone>::clone",
    "<env::inductive_no_confusion_hetero::EqTelescopeGroup as std::clone::Clone>::clone",
]
THE_THREE_INSTRS = [20, 35, 20]
THE_THREE_REJECTIONS = [
    ("EnumMatch(ref payload no layout descriptor)",
     "crates/clean-kernel/src/env/algebra_rat_quotient.rs:3447:10: 3447:15"),
    ("Adt(unsupported field)",
     "crates/clean-kernel/src/env/inductive_no_confusion.rs:74:10: 74:15"),
    ("Adt(unsupported field)",
     "crates/clean-kernel/src/env/inductive_no_confusion_hetero.rs:94:10: 94:15"),
]


def body(def_path, def_index, *, lowered=True, spliced=True, instrs=10,
         dm_verdict="unsupported", markers_exact=False, unsupported=(),
         details=None, interp="not-run", lineage="sha256:aa", func_id=1):
    return {
        "def_path": def_path, "def_index": def_index, "kind": "fn",
        "lowered": lowered, "symbolic": False, "spliced": spliced,
        "lineage": lineage, "func_id": func_id, "instr_count": instrs,
        "unsupported": [list(u) for u in unsupported],
        "unsupported_details": details or {},
        "collect_primary": [list(u) for u in unsupported], "collect_cascade": [],
        "calls": {"resolved": 1, "extern_decls": 0, "unresolved": 0},
        "differentials": {
            "interpreter": {"verdict": interp, "samples": 0, "detail": ""},
            "derived_mir": {"verdict": dm_verdict, "detail": "",
                            "markers_exact": markers_exact, "markers_detail": ""},
            "deferred_to_seam": False,
            "seam": {"state": "not-applicable"},
        },
    }


def stubbed(b, rejection):
    """Apply the measured real-world collapse to a body: real body -> 1-instr stub."""
    name, span = rejection
    out = json.loads(json.dumps(b))
    out["lowered"] = False
    out["spliced"] = False
    out["instr_count"] = 1
    out["func_id"] = None
    out["lineage"] = "sha256:bb"
    out["unsupported"] = [[name, 1]]
    out["unsupported_details"] = {name: [span]}
    out["collect_primary"] = [[name, 1]]
    out["calls"] = {"resolved": 0, "extern_decls": 0, "unresolved": 0}
    # The load-bearing fact: the derived-MIR bucket does NOT move.
    out["differentials"]["derived_mir"]["verdict"] = "unsupported"
    out["differentials"]["interpreter"]["verdict"] = "unsupported"
    return out


def doc(bodies):
    lowered = sum(1 for b in bodies if b["lowered"])
    return {
        "schema": "trust.thir-lower.crate-module.coverage.v2",
        "crate": "clean_kernel",
        "totals": {
            "bodies": len(bodies), "lowered": lowered,
            "symbolic": 0, "spliced": sum(1 for b in bodies if b["spliced"]),
            "declarations": 0, "initializer_bodies": 0,
            "instr_count": sum(b["instr_count"] for b in bodies),
            "unsupported": sum(len(b["unsupported"]) for b in bodies),
            "calls": {"resolved": 0, "extern_decls": 0, "unresolved": 0},
        },
        "bodies": bodies,
    }


def write(tmp, name, bodies):
    path = os.path.join(tmp, name)
    with open(path, "w") as fh:
        json.dump(doc(bodies), fh)
    return path


def run(argv):
    """Invoke the tool exactly as a caller would; return (exit_code, stdout)."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        code = rd.main(argv)
    return code, buf.getvalue()


def the_published_scenario():
    """Control/subject reproducing the four reviews' published table.

    The real table read `agreed 1540 / unsupported 12228 / mismatch 1` ->
    `1541 / 12228 / 0`: one body's mismatch cleared into `agreed`, the `unsupported`
    bucket identical on both sides, and the three collapsed bodies sitting inside that
    identical bucket throughout. Scaled down in row count; every axis that matters
    keeps its measured value.
    """
    control, subject = [], []
    for i, (path, instrs, rej) in enumerate(
            zip(THE_THREE, THE_THREE_INSTRS, THE_THREE_REJECTIONS)):
        b = body(path, 28000 + i, instrs=instrs)
        control.append(b)
        subject.append(stubbed(b, rej))
    # the whole of the published movement: one mismatch clears into agreed.
    control.append(body("kernel::mm", 2, dm_verdict="mismatch"))
    subject.append(body("kernel::mm", 2, dm_verdict="agreed", markers_exact=True))
    # untouched filler, so "moved rows" is a small fraction of the crate
    for i in range(20):
        b = body(f"kernel::quiet_{i}", 100 + i, dm_verdict="agreed", markers_exact=True)
        control.append(b)
        subject.append(json.loads(json.dumps(b)))
    return control, subject


class BlindSpot(unittest.TestCase):
    def test_blind_spot_is_real(self):
        """MUTATION PROOF: the old tuple cannot rank the three collapsed bodies.

        Two separate failures are asserted, because they are separate defects:
          (a) the bucket comparator (covdiff's `verdict + markers_exact`) does not
              move AT ALL on any of the three -- literally invisible;
          (b) the richer tuples do move, but every axis that moves is one they carry
              no verdict for, so the rows are printed unranked among benign churn
              while the summary says 0 lost.
        """
        control, subject = the_published_scenario()
        c = {b["def_path"]: rd.row_of(b) for b in control}
        s = {b["def_path"]: rd.row_of(b) for b in subject}

        bucket = LEGACY("wave-tr-ledger/covdiff.py")
        for path in THE_THREE:
            self.assertEqual(
                tuple(c[path][f] for f in bucket), tuple(s[path][f] for f in bucket),
                f"expected covdiff's tuple to be BLIND to {path}; if this now differs, "
                "the scenario no longer reproduces the defect")

        # The published table, reproduced: unsupported identical BY MEMBERSHIP (not
        # merely by count), agreed +1, mismatch -1. Membership is the stronger claim
        # and it is the one that makes the bucket instrument genuinely blind here.
        unsup_c = {p for p, r in c.items() if r["dm_verdict"] == "unsupported"}
        unsup_s = {p for p, r in s.items() if r["dm_verdict"] == "unsupported"}
        self.assertEqual(unsup_c, unsup_s,
                         "the `unsupported` bucket must be identical as a SET, as "
                         "published; no body enters or leaves it")
        self.assertTrue(set(THE_THREE) <= unsup_c,
                        "the three collapsed bodies must sit inside that static bucket")
        self.assertEqual(sum(1 for r in c.values() if r["dm_verdict"] == "agreed") + 1,
                         sum(1 for r in s.values() if r["dm_verdict"] == "agreed"),
                         "agreed must read +1, as published")
        self.assertEqual(sum(1 for r in c.values() if r["dm_verdict"] == "mismatch") - 1,
                         sum(1 for r in s.values() if r["dm_verdict"] == "mismatch"),
                         "mismatch must read -1, as published")

        # and no legacy tuple carries a verdict for any axis that actually moved
        verdictless = {"lowered", "spliced", "instr_count", "lineage", "func_id",
                       "unsupported", "unsupported_details", "collect_primary",
                       "interp_verdict", "calls_resolved"}
        for name, fields in rd.LEGACY_TUPLES.items():
            moved_axes = {f for f in fields if c[THE_THREE[0]][f] != s[THE_THREE[0]][f]}
            self.assertTrue(moved_axes <= verdictless,
                            f"{name} would have ranked this row via {moved_axes}")

    def test_stub_collapse_is_a_reported_row(self):
        control, subject = the_published_scenario()
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            out_json = os.path.join(tmp, "out.json")
            code, out = run(["rows", a, b, "--json", out_json, "--legacy-tuple"])

        self.assertEqual(code, 1, "a stub collapse must be a non-zero exit")
        self.assertIn("STUB COLLAPSE", out)
        for path in THE_THREE:
            self.assertIn(path, out, f"{path} must be named in the report")
        self.assertIn("bucket totals CANNOT see this row", out)
        self.assertIn("THE BUCKET TABLE IS CLEAN AND THE CRATE STILL REGRESSED", out,
                      "no body changed derived-MIR bucket, yet three bodies of "
                      "lowering coverage were lost; the report must say so in as "
                      "many words rather than leaving the reader to notice")
        # every coverage axis that actually moved must be named in the headline
        for axis in ("lowered LOST", "spliced LOST", "instr_count LOST"):
            self.assertIn(axis, out)

    def test_json_names_exactly_the_three(self):
        control, subject = the_published_scenario()
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            out_json = os.path.join(tmp, "out.json")
            run(["rows", a, b, "--json", out_json])
            with open(out_json) as output:
                payload = json.load(output)

        self.assertEqual(sorted(r[1] for r in payload["stub_collapse"]),
                         sorted(THE_THREE))
        self.assertEqual(sorted(r[1] for r in payload["axes"]["lowered"]["lost"]),
                         sorted(THE_THREE))
        self.assertEqual(sorted(r[1] for r in payload["axes"]["spliced"]["lost"]),
                         sorted(THE_THREE))
        self.assertEqual(sorted(r[1] for r in payload["axes"]["instr_count"]["lost"]),
                         sorted(THE_THREE))
        # `lineage` is a `gone` axis: the digest changed but did not vanish, so it is
        # reported as moved with no verdict. That is the honest reading and it must
        # not be silently promoted to a loss.
        self.assertEqual(payload["axes"]["lineage"]["moved"], len(THE_THREE))
        self.assertEqual(payload["axes"]["lineage"]["lost"], [])
        self.assertEqual(payload["axes"]["lineage"]["gained"], [])


class Cancellation(unittest.TestCase):
    def test_loss_and_gain_do_not_cancel(self):
        """One body loses `lowered`, another gains it. Every total is unchanged."""
        control = [body("kernel::a", 1, lowered=True, spliced=True, instrs=12),
                   body("kernel::b", 2, lowered=False, spliced=False, instrs=1)]
        subject = [body("kernel::a", 1, lowered=False, spliced=False, instrs=1),
                   body("kernel::b", 2, lowered=True, spliced=True, instrs=12)]
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            out_json = os.path.join(tmp, "o.json")
            code, out = run(["rows", a, b, "--json", out_json])
            with open(out_json) as output:
                payload = json.load(output)

        self.assertEqual(payload["totals"]["control"]["lowered"],
                         payload["totals"]["subject"]["lowered"],
                         "the scenario is only interesting if the TOTAL is unchanged")
        self.assertEqual(code, 1)
        self.assertEqual([r[1] for r in payload["axes"]["lowered"]["lost"]],
                         ["kernel::a"])
        self.assertEqual([r[1] for r in payload["axes"]["lowered"]["gained"]],
                         ["kernel::b"])
        self.assertEqual([r[1] for r in payload["stub_collapse"]], ["kernel::a"])
        self.assertEqual([r[1] for r in payload["stub_recovery"]], ["kernel::b"])
        self.assertIn("NET ZERO, ROWS MOVED", out)


class QuietAxes(unittest.TestCase):
    def test_lowered_body_whose_content_changed_is_reported(self):
        """`lowered` and every bucket stay put; only the content digest moves."""
        control = [body("kernel::c", 1, dm_verdict="agreed", markers_exact=True,
                        lineage="sha256:before")]
        subject = [body("kernel::c", 1, dm_verdict="agreed", markers_exact=True,
                        lineage="sha256:after")]
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            _code, out = run(["rows", a, b])
        self.assertIn("lineage", out)
        self.assertRegex(out, r"lineage\s+moved=1")

    def test_shrunk_body_is_reported_as_SOFT_and_does_not_cry_wolf(self):
        """A leaner but complete lowering is reported, counted, and not a red gate.

        Measured on the real A/B: 215 bodies shrank, of which 67 are still fully
        lowered and spliced. Gating on those would make every cross-generation
        comparison red and train reviewers to ignore the tool -- which is how the
        original defect survived. So the row is always printed; only `--fail-on soft`
        makes it fail.
        """
        control = [body("kernel::d", 1, instrs=40, dm_verdict="agreed",
                        markers_exact=True)]
        subject = [body("kernel::d", 1, instrs=9, dm_verdict="agreed",
                        markers_exact=True)]
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            code, out = run(["rows", a, b])
            soft_code, _ = run(["rows", a, b, "--fail-on", "soft"])
        self.assertIn("instr_count LOST", out, "the row must still be reported")
        self.assertIn("[soft]", out)
        self.assertEqual(code, 0, "a still-lowered, still-spliced body is not a HARD loss")
        self.assertEqual(soft_code, 1, "--fail-on soft must gate on it")

    def test_hard_and_soft_are_both_counted_in_the_headline(self):
        control = [body("kernel::hard", 1, instrs=30),
                   body("kernel::soft", 2, instrs=40, dm_verdict="agreed",
                        markers_exact=True)]
        subject = [body("kernel::hard", 1, lowered=False, spliced=False, instrs=1),
                   body("kernel::soft", 2, instrs=9, dm_verdict="agreed",
                        markers_exact=True)]
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            code, out = run(["rows", a, b])
        self.assertEqual(code, 1, "the HARD row must gate")
        self.assertRegex(out, r"REGRESSION CLASSES: [1-9]\d* HARD, [1-9]\d* SOFT")

    def test_collapse_to_stub_while_still_claiming_lowered(self):
        """The other spelling of the same event must land in the same class."""
        control = [body("kernel::e", 1, instrs=30)]
        subject = [body("kernel::e", 1, instrs=1)]
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            code, out = run(["rows", a, b])
        self.assertEqual(code, 1)
        self.assertIn("STUB COLLAPSE", out)


class AdmittedWrong(unittest.TestCase):
    """`refused` -> `ADMITTED-WRONG` is a trust regression no boolean can express.

    Both states carry `markers_exact == false` and both sat at `verdict == agreed`
    in the real measurement, so the bucket table, the markers_exact count and every
    legacy tuple's verdict are all static across it. The strings below are the
    MEASURED ones from `expr::types::BigNat::is_zero::{closure#0}` across the two
    compiler generations: the derived side stops declining and starts asserting a
    marker sequence that disagrees on liveness, slot and binding.
    """
    REFUSED = "markers differ: line 0: built `mk b0.0:live s0:u64` vs derived `<end>`"
    WRONG = ("markers differ: line 1: built `mk b0.1:live s1:u64` vs derived "
             "`mk b0.2:dead s0:u64`")

    def _rows(self, detail_a, detail_b):
        a = body("expr::types::BigNat::is_zero::{closure#0}", 7, dm_verdict="agreed")
        b = json.loads(json.dumps(a))
        a["differentials"]["derived_mir"]["markers_detail"] = detail_a
        b["differentials"]["derived_mir"]["markers_detail"] = detail_b
        return [a], [b]

    def test_refused_to_admitted_wrong_is_a_hard_class(self):
        control, subject = self._rows(self.REFUSED, self.WRONG)
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            out_json = os.path.join(tmp, "o.json")
            code, out = run(["rows", a, b, "--json", out_json])
            with open(out_json) as output:
                payload = json.load(output)

        self.assertEqual(code, 1)
        self.assertIn("NEW ADMITTED-WRONG markers", out)
        self.assertEqual([r[1] for r in payload["admitted_wrong_new"]],
                         ["expr::types::BigNat::is_zero::{closure#0}"])
        # the axes that stayed put are exactly the ones the old reports showed
        self.assertEqual(payload["axes"]["markers_exact"]["moved"], 0)
        self.assertEqual(payload["axes"]["dm_verdict"]["moved"], 0)

    def test_classifier_boundaries(self):
        self.assertEqual(classify({"markers_exact": True}), "right")
        self.assertEqual(classify({"markers_exact": False, "markers_detail": ""}),
                         "no-derived-body")
        self.assertEqual(classify({"markers_exact": False,
                                   "markers_detail": self.REFUSED}), "refused")
        self.assertEqual(classify({"markers_exact": False,
                                   "markers_detail": self.WRONG}), "ADMITTED-WRONG")

    def test_improvement_direction_is_not_a_regression(self):
        control, subject = self._rows(self.WRONG, self.REFUSED)
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            code, _ = run(["rows", a, b])
        self.assertEqual(code, 0, "going from wrong to refusing is an improvement")


class MarkerVacuity(unittest.TestCase):
    """`markers_exact: true` over 21 marker lines and over ZERO are not one state.

    Same shape as `refused` vs `ADMITTED-WRONG`: two distinct states share one name,
    and no boolean on the row separates them. Here the boolean stays `true` and the
    derived-MIR bucket stays `agreed` on BOTH sides, so the bucket table, the
    `markers_exact` count and every legacy tuple are static across the event -- a
    body's entire marker evidence can evaporate and the review reads green.

    The numbers are MEASURED, not invented: `expr::bvar_in_range` is the richest
    non-vacuous row in the 2026-08-13 whole-crate dump at 21 marker lines, and of
    1,082 `markers_exact` rows only 27 carried any marker line at all.
    """
    REAL = "21 marker line(s) identical"
    VACUOUS = "0 marker line(s) identical"

    def _rows(self, detail_a, detail_b):
        a = body("expr::bvar_in_range", 16566, dm_verdict="agreed", markers_exact=True)
        b = json.loads(json.dumps(a))
        a["differentials"]["derived_mir"]["markers_detail"] = detail_a
        b["differentials"]["derived_mir"]["markers_detail"] = detail_b
        return [a], [b]

    def test_marker_claim_going_vacuous_is_a_hard_class(self):
        control, subject = self._rows(self.REAL, self.VACUOUS)
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            out_json = os.path.join(tmp, "o.json")
            code, out = run(["rows", a, b, "--json", out_json])
            with open(out_json) as output:
                payload = json.load(output)

        self.assertEqual(code, 1)
        self.assertIn("MARKER CLAIM WENT VACUOUS", out)
        self.assertEqual([r[1] for r in payload["markers_went_vacuous"]],
                         ["expr::bvar_in_range"])
        # exactly the axes that made this invisible before: both stay put
        self.assertEqual(payload["axes"]["markers_exact"]["moved"], 0)
        self.assertEqual(payload["axes"]["dm_verdict"]["moved"], 0)
        # and the axis that finally sees it does move, in the LOST direction
        self.assertEqual(payload["axes"]["markers_lines"]["moved"], 1)
        self.assertEqual([r[1] for r in payload["axes"]["markers_lines"]["lost"]],
                         ["expr::bvar_in_range"])

    def test_the_old_tuple_is_blind_to_it(self):
        """The blind spot is reproduced here, not taken on trust."""
        control, subject = self._rows(self.REAL, self.VACUOUS)
        c, s = rd.row_of(control[0]), rd.row_of(subject[0])
        for field in ("markers_exact", "dm_verdict", "lowered", "spliced",
                      "instr_count", "lineage", "unsupported"):
            self.assertEqual(c[field], s[field], f"{field} must be static")
        self.assertNotEqual(c["markers_lines"], s["markers_lines"])

    def test_classifier_splits_right_from_right_vacuous(self):
        self.assertEqual(classify({"markers_exact": True,
                                   "markers_detail": self.REAL}), "right")
        self.assertEqual(classify({"markers_exact": True,
                                   "markers_detail": self.VACUOUS}), "right-vacuous")
        # a count that is not stated is NOT evidence of vacuity -- stay conservative
        self.assertEqual(classify({"markers_exact": True}), "right")
        self.assertEqual(classify({"markers_exact": True,
                                   "markers_detail": "marker channel(built): x"}),
                         "right")

    def test_marker_lines_parser(self):
        ml = rd.marker_lines
        self.assertEqual(ml({"markers_detail": self.REAL}), 21)
        self.assertEqual(ml({"markers_detail": self.VACUOUS}), 0)
        self.assertIsNone(ml({}))
        self.assertIsNone(ml({"markers_detail": "markers differ: line 0: built `x`"}))
        self.assertIsNone(ml({"markers_detail": "marker channel(built): x"}))

    def test_becoming_non_vacuous_is_not_a_regression(self):
        control, subject = self._rows(self.VACUOUS, self.REAL)
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            code, out = run(["rows", a, b])
        self.assertEqual(code, 0, "gaining real marker evidence is an improvement")
        self.assertNotIn("MARKER CLAIM WENT VACUOUS", out)

    def test_two_vacuous_sides_are_not_a_regression(self):
        """Matching emptiness is honest. It must not become a false positive."""
        control, subject = self._rows(self.VACUOUS, self.VACUOUS)
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            code, out = run(["rows", a, b])
        self.assertEqual(code, 0)
        self.assertNotIn("MARKER CLAIM WENT VACUOUS", out)

    def test_a_shrink_that_is_not_to_zero_is_soft_not_hard(self):
        """Losing 21 lines down to 2 is a real loss, but it is not VACUITY."""
        control, subject = self._rows(self.REAL, "2 marker line(s) identical")
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            code, out = run(["rows", a, b])
        self.assertEqual(code, 0, "SOFT alone must not turn the gate red")
        self.assertNotIn("MARKER CLAIM WENT VACUOUS", out)
        self.assertIn("markers_lines LOST", out)


class NegativeControls(unittest.TestCase):
    def test_identical_inputs_are_green(self):
        control, _ = the_published_scenario()
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", json.loads(json.dumps(control)))
            code, out = run(["rows", a, b])
        self.assertEqual(code, 0, "identical dumps must not report a regression")
        self.assertIn("REGRESSION CLASSES: 0", out)

    def test_pure_improvement_is_green(self):
        control = [body("kernel::f", 1, lowered=False, spliced=False, instrs=1)]
        subject = [body("kernel::f", 1, lowered=True, spliced=True, instrs=25,
                        dm_verdict="agreed", markers_exact=True)]
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            code, _out = run(["rows", a, b])
        self.assertEqual(code, 0, "gaining coverage is not a regression")

    def test_disappearing_body_is_a_regression(self):
        control = [body("kernel::g", 1), body("kernel::h", 2)]
        subject = [body("kernel::g", 1)]
        with tempfile.TemporaryDirectory() as tmp:
            a = write(tmp, "a.coverage.json", control)
            b = write(tmp, "b.coverage.json", subject)
            code, out = run(["rows", a, b])
        self.assertEqual(code, 1)
        self.assertIn("BODY DISAPPEARED", out)

    def test_bad_input_exits_two_not_one(self):
        with tempfile.TemporaryDirectory() as tmp:
            junk = os.path.join(tmp, "junk.coverage.json")
            with open(junk, "w") as output:
                output.write("{}")
            code, _ = run(["rows", junk, junk])
        self.assertEqual(code, 2, "an unreadable input is an error, not a verdict")


class Flips(unittest.TestCase):
    LOG_A = (
        'trust-ir-flip: compiled from trust-ir did=DefId(0:11 ~ clean_kernel[a]::x)\n'
        'trust-ir-flip: compiled from trust-ir did=DefId(0:12 ~ clean_kernel[a]::y)\n'
        'trust-ir-flip: CTFE compiled from trust-ir did=DefId(0:13 ~ clean_kernel[a]::z)\n'
    )
    LOG_B = (
        'trust-ir-flip: compiled from trust-ir did=DefId(0:12 ~ clean_kernel[a]::y)\n'
        'trust-ir-flip: compiled from trust-ir did=DefId(0:14 ~ clean_kernel[a]::w)\n'
        'trust-ir-flip: CTFE compiled from trust-ir did=DefId(0:13 ~ clean_kernel[a]::z)\n'
        'FALLBACK to built MIR, did=DefId(0:11 ~ clean_kernel[a]::x), '
        'reason="Adt(unsupported field)", stage="lower"\n'
    )

    def test_build_disambiguator_does_not_forge_losses(self):
        """MUTATION PROOF for the second instrument defect.

        Cargo stamps a per-BUILD crate disambiguator into the DefId
        (`clean_kernel[1f2d]` vs `clean_kernel[4676]`), and all four copies of
        `fliplog.py` joined on the raw string. Measured on two real logs of the same
        crate at the same revision, that reported `LOST 153 / GAINED 153` -- the
        loudest output the harness has, and pure noise. Same bodies, different
        stamps, must be zero lost.
        """
        same = ('trust-ir-flip: compiled from trust-ir '
                'did=DefId(0:13226 ~ clean_kernel[{h}]::env::proof_search::rank)\n'
                'trust-ir-flip: compiled from trust-ir '
                'did=DefId(0:13403 ~ clean_kernel[{h}]::env::types::{{impl#0}}::is_regular)\n')
        with tempfile.TemporaryDirectory() as tmp:
            a = os.path.join(tmp, "a.flip.txt")
            b = os.path.join(tmp, "b.flip.txt")
            with open(a, "w") as output:
                output.write(same.format(h="1f2d"))
            with open(b, "w") as output:
                output.write(same.format(h="4676"))
            code, out = run(["flips", a, b])

        self.assertEqual(code, 0, "identical bodies under a different build stamp "
                                  "must not read as 153 lost and 153 gained")
        self.assertIn("LOST=0 GAINED=0", out)
        self.assertIn("disambiguators differ", out,
                      "the normalisation must be stated, not silent")
        # and the raw-string join really would have forged the losses
        raw_a = {"0:13226 ~ clean_kernel[1f2d]::env::proof_search::rank"}
        raw_b = {"0:13226 ~ clean_kernel[4676]::env::proof_search::rank"}
        self.assertEqual(len(raw_a - raw_b), 1,
                         "if this is ever 0 the defect stopped reproducing")
        self.assertEqual(rd.norm_did(list(raw_a)[0]), rd.norm_did(list(raw_b)[0]))

    def test_a_lost_flip_is_reported_despite_a_net_zero_count(self):
        with tempfile.TemporaryDirectory() as tmp:
            a = os.path.join(tmp, "a.flip.txt")
            b = os.path.join(tmp, "b.flip.txt")
            with open(a, "w") as output:
                output.write(self.LOG_A)
            with open(b, "w") as output:
                output.write(self.LOG_B)
            code, out = run(["flips", a, b])
        self.assertEqual(code, 1)
        self.assertIn("LOST FLIP", out)
        # normalised identity: the build stamp is stripped, the path is not
        self.assertIn("clean_kernel::x", out)
        self.assertIn("net=+0", out, "the net count is zero; the set difference is not")
        self.assertIn("Adt(unsupported field)", out)


def LEGACY(name):
    for key, fields in rd.LEGACY_TUPLES.items():
        if name in key:
            return fields
    raise KeyError(name)


if __name__ == "__main__":
    unittest.main(verbosity=2)
