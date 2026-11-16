#!/usr/bin/env python3
"""Self-test for scripts/channel_c_survey.py (step 2 increment 4d, sub-step 4d.0a).

The census is only as good as its row parser, so the parser is fed channel C's real row
shapes (copied from a stage-1 run of tests/run-make/trust-cg-f1-shims's subjects and from
instance_probe.rs's format string): a result that contains spaces, each optional column, a
def path and args that contain spaces, and the summary line. `survey()` is then driven end to
end over temporary files with a fake compiler, so the outcome classes (probed,
compile-failed, no-probe-output, timeout) and the crate-type and edition rules are pinned
without a stage-1 build. `main()` is run for real against `/usr/bin/false`, which probes
nothing: a vacuous census must exit 1.

Run directly (`python3 scripts/tests/channel_c_survey_test.py`) or via
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
from pathlib import Path

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import channel_c_survey as cc  # noqa: E402

ITEM_ROW = (
    "TRUST-WALLA-PROBE C sym=_RNvCs1_10clone_unit3run kind=item local=true route=thir "
    "result=ok(input=Thir,functions=2) drops=none def=run args=[]"
)
SHIM_ROW = (
    "TRUST-WALLA-PROBE C sym=_RNvXs_NtCs2_4core5clone kind=shim-clone local=false route=mir "
    "result=residue def=std::clone::Clone::clone args=[()]"
)
REFUSED_ROW = (
    "TRUST-WALLA-PROBE C sym=_RINvCs1_10clone_unit3dupuEB2_ kind=item local=true route=thir "
    'result=refused(LaneRefused("opaque collapse")) drops=none def=dup args=[()]'
)
GLUE_ROW = (
    "TRUST-WALLA-PROBE C sym=_RINvNtCs3_4core3ptr13drop_in_placeB_ kind=shim-drop-glue "
    "local=false route=mir result=residue glue=refused-upstream-body "
    "def=std::ptr::drop_in_place args=[std::vec::Vec<u64, std::alloc::Global>]"
)
UPSTREAM_ROW = (
    "TRUST-WALLA-PROBE C sym=_RNvMs_NtCs4_5alloc3vec3len kind=item local=false route=mir "
    "result=residue rmeta=no-header def=std::vec::Vec::<T, A>::len "
    "args=[u64, std::alloc::Global]"
)
SHIM_COLUMN_ROW = (
    "TRUST-WALLA-PROBE C sym=_RNvXs0_x kind=shim-fn-ptr-addr local=false route=mir "
    "result=residue shim=structural-match def=std::ops::FnPtr::addr args=[fn()]"
)
SUMMARY = (
    "TRUST-WALLA-PROBE C summary fn_items=6 thir_ok=1 assembly_refused=0 erased=0 "
    "not_conserved=0 abstracted=0 refused=1 residue=4 panics=0 non_fn=0 drops_placed=0 "
    "drops_elided=0 drops_mismatch=0 drops_unchecked=0 glue_match=0 glue_differs=0 "
    "glue_refused=1 glue_oracle_failed=0 glue_misses=0 glue_extras=0 rmeta_entry=0 "
    "rmeta_entry_refused=0 rmeta_absent=0 rmeta_no_header=1"
)
STDERR = "\n".join([
    "note: trust-cg trust-ir frontend: unrelated noise",
    ITEM_ROW, SHIM_ROW, REFUSED_ROW, GLUE_ROW, UPSTREAM_ROW, SHIM_COLUMN_ROW,
    "TRUST-WALLA-PROBE C class residue-mir-route=4",
    SUMMARY,
])


class ParseTest(unittest.TestCase):
    def test_item_row_with_drops(self):
        row = cc.parse_row(ITEM_ROW)
        self.assertEqual(row["kind"], "item")
        self.assertEqual(row["route"], "thir")
        self.assertEqual(row["result"], "ok(input=Thir,functions=2)")
        self.assertEqual(row["drops"], "none")
        self.assertEqual(row["def"], "run args=[]")
        self.assertNotIn("glue", row)

    def test_a_result_with_spaces_is_kept_whole(self):
        row = cc.parse_row(REFUSED_ROW)
        self.assertEqual(row["result"], 'refused(LaneRefused("opaque collapse"))')
        self.assertEqual(row["drops"], "none")

    def test_shim_residue_has_no_optional_column(self):
        row = cc.parse_row(SHIM_ROW)
        self.assertEqual((row["kind"], row["route"], row["result"]),
                         ("shim-clone", "mir", "residue"))
        for column in cc.OPTIONAL_COLUMNS:
            self.assertNotIn(column, row)
        self.assertEqual(row["def"], "std::clone::Clone::clone args=[()]")

    def test_each_optional_column(self):
        self.assertEqual(cc.parse_row(GLUE_ROW)["glue"], "refused-upstream-body")
        self.assertEqual(cc.parse_row(UPSTREAM_ROW)["rmeta"], "no-header")
        self.assertEqual(cc.parse_row(SHIM_COLUMN_ROW)["shim"], "structural-match")
        self.assertEqual(cc.parse_row(UPSTREAM_ROW)["def"],
                         "std::vec::Vec::<T, A>::len args=[u64, std::alloc::Global]")

    def test_non_rows(self):
        self.assertIsNone(cc.parse_row("TRUST-WALLA-PROBE C class residue-mir-route=4"))
        self.assertIsNone(cc.parse_row(SUMMARY))
        self.assertIsNone(cc.parse_summary(ITEM_ROW))

    def test_summary(self):
        summary = cc.parse_summary(SUMMARY)
        self.assertEqual(summary["fn_items"], 6)
        self.assertEqual(summary["residue"], 4)
        self.assertEqual(summary["rmeta_no_header"], 1)

    def test_parse_stderr(self):
        rows, summary = cc.parse_stderr(STDERR)
        self.assertEqual(len(rows), 6)
        self.assertEqual(summary["fn_items"], 6)
        self.assertEqual(cc.parse_stderr("error: no probe here\n"), ([], None))


class RulesTest(unittest.TestCase):
    def test_crate_type(self):
        self.assertEqual(cc.crate_type_args("pub fn f() {}"), ["--crate-type=lib"])
        self.assertEqual(cc.crate_type_args("fn main() {}"), [])
        self.assertEqual(cc.crate_type_args("pub async fn main() {}"), [])
        self.assertEqual(cc.crate_type_args('#![crate_type = "lib"]\nfn main() {}'), [])
        self.assertEqual(cc.crate_type_args("fn mainly() {}"), ["--crate-type=lib"])

    def test_edition(self):
        self.assertEqual(cc.edition_of("//@ edition: 2024\nfn main() {}"), "2024")
        self.assertEqual(cc.edition_of("//@ edition:2018\n"), "2018")
        self.assertEqual(cc.edition_of("fn main() {}"), "2021")
        self.assertEqual(cc.edition_of("//@ edition:2015..2021\n"), "2015")
        self.assertEqual(cc.edition_of("//@ edition: 2021..\n"), "2021")
        self.assertEqual(cc.edition_of("//@ edition: ..2021\n"), "2015")

    def test_command_carries_part_a_flags(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp, "a.rs")
            path.write_text("//@ edition: 2018\npub fn f() {}\n")
            cmd = cc.command_for("rustc", path, "out")
        self.assertEqual(cmd[:3], ["rustc", str(path), "--edition=2018"])
        self.assertIn("--crate-type=lib", cmd)
        for flag in ("-Copt-level=0", "-Ccodegen-units=1", "-Cpanic=abort", "-Ztrust-verify=off",
                     "-Ztrust-ir-lower", "-Ztrust-instance-flip-probe=*", "--emit=obj"):
            self.assertIn(flag, cmd)


class SurveyTest(unittest.TestCase):
    def test_outcomes_and_aggregation(self):
        def fake(cmd, timeout):
            name = Path(cmd[1]).name
            return {
                "probed.rs": (0, STDERR),
                "broken.rs": (1, "error[E0425]: cannot find value"),
                "silent.rs": (0, ""),
                "slow.rs": (None, ""),
            }[name]

        with tempfile.TemporaryDirectory() as tmp:
            for name in ("probed.rs", "broken.rs", "silent.rs", "slow.rs"):
                Path(tmp, name).write_text("pub fn f() {}\n")
            files = cc.expand([tmp])
            census = cc.survey("rustc", files, jobs=2, timeout=5, runner=fake)
        self.assertEqual(census["files"], 4)
        self.assertEqual(census["outcomes"], {"compile-failed": 1, "no-probe-output": 1,
                                              "probed": 1, "timeout": 1})
        self.assertEqual(census["rows"], 6)
        self.assertEqual(census["by_kind"], {"item": 3, "shim-clone": 1, "shim-drop-glue": 1,
                                             "shim-fn-ptr-addr": 1})
        self.assertEqual(census["by_kind_route_result"]["shim-clone|mir|residue"], 1)
        self.assertEqual(
            census["by_kind_route_result"]['item|thir|refused(LaneRefused("opaque collapse"))'], 1)
        self.assertEqual(census["by_kind_glue"], {"shim-drop-glue|refused-upstream-body": 1})
        self.assertEqual(census["by_kind_shim"], {"shim-fn-ptr-addr|structural-match": 1})
        self.assertEqual(census["by_kind_drops"], {"item|none": 2})
        self.assertEqual(census["shim_kinds"], ["shim-clone", "shim-drop-glue", "shim-fn-ptr-addr"])
        self.assertEqual(census["files_by_shim_kind"]["shim-clone"], 1)
        self.assertEqual(census["summary_totals"]["residue"], 4)
        json.dumps(census)  # the census is JSON
        self.assertNotIn("row_list", census["per_file"][0])
        kept = cc.aggregate([{"file": "a.rs", "status": 0, "outcome": "probed",
                              "rows": cc.parse_stderr(STDERR)[0], "summary": None}], keep_rows=True)
        self.assertEqual(len(kept["per_file"][0]["row_list"]), 6)

    def test_main_on_a_vacuous_census_exits_1(self):
        with tempfile.TemporaryDirectory() as tmp:
            Path(tmp, "a.rs").write_text("pub fn f() {}\n")
            out = Path(tmp, "census.json")
            with contextlib.redirect_stdout(io.StringIO()):
                status = cc.main(["--rustc", "/usr/bin/false", "--out", str(out), "--jobs", "1",
                                  str(Path(tmp, "a.rs"))])
            self.assertEqual(status, 1)
            census = json.loads(out.read_text())
        self.assertEqual(census["outcomes"], {"compile-failed": 1})

    def test_main_on_a_missing_path_exits_2(self):
        with contextlib.redirect_stderr(io.StringIO()):
            status = cc.main(["--rustc", "rustc", "--out", os.devnull, "/no/such/file.rs"])
        self.assertEqual(status, 2)


if __name__ == "__main__":
    unittest.main()
