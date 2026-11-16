#!/usr/bin/env python3
"""The producer scorecard NAMES what the module validator objected to.

`crate_module.rs` emits one `trust-ir-lower: module validation detail` event per
validation error, carrying the error's Debug rendering (which struct, enum or
constant, which ids). The scorecard used to parse only the per-class counts and
the total, so an artifact could say a module was ill-formed but never WHICH
item — and `aggregate` did not say which FILES were invalid either. These pins
cover the three layers: the per-file parse, the per-artifact file list, and the
markdown that surfaces both.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]


def load_scorecard_module():
    path = REPO_ROOT / "scripts" / "trust_ir_producer_scorecard.py"
    spec = importlib.util.spec_from_file_location("trust_ir_producer_scorecard", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


scorecard = load_scorecard_module()

# The emitter's shape (`tracing::debug!(class = %class, n, ..)`, then one
# `detail = ?error` event per error, then the summary), as the sweep captures it.
INVALID_STDERR = """\
DEBUG trust-ir-lower: module validation error, class=CallArgTypeMismatch, n=2
DEBUG trust-ir-lower: module validation detail, detail=CallArgTypeMismatch { func: FuncId(3), block: 0, arg: 1, expected: I64, found: Ptr }
DEBUG trust-ir-lower: module validation detail, detail=CallArgTypeMismatch { func: FuncId(7), block: 2, arg: 0, expected: F64, found: I64 }
DEBUG trust-ir-lower: module validation error, class=UnknownStruct, n=1
DEBUG trust-ir-lower: module validation detail, detail=UnknownStruct { id: StructId(12), name: "Wrapper<u8>" }
DEBUG trust-ir-lower: module validation summary, total=3
"""


class ParseValidationTest(unittest.TestCase):
    def test_invalid_module_carries_every_detail_in_order(self) -> None:
        v = scorecard.parse_validation(INVALID_STDERR)
        self.assertEqual(v["total"], 3)
        self.assertEqual(v["classes"], {"CallArgTypeMismatch": 2, "UnknownStruct": 1})
        self.assertEqual(
            v["details"],
            [
                "CallArgTypeMismatch { func: FuncId(3), block: 0, arg: 1, expected: I64, found: Ptr }",
                "CallArgTypeMismatch { func: FuncId(7), block: 2, arg: 0, expected: F64, found: I64 }",
                'UnknownStruct { id: StructId(12), name: "Wrapper<u8>" }',
            ],
        )

    def test_detail_events_are_never_counted_as_classes(self) -> None:
        # The detail payload starts with the class name; it must not leak into
        # the class histogram, which is VALERR_RE's alone.
        v = scorecard.parse_validation(INVALID_STDERR)
        self.assertEqual(sum(v["classes"].values()), v["total"])

    def test_invalid_module_without_detail_events_reads_as_an_empty_list(self) -> None:
        # A binary that emits the summary but not the detail event: `[]` on an
        # invalid row is itself the finding, distinct from a missing key.
        stderr = "\n".join(
            line for line in INVALID_STDERR.splitlines() if "validation detail" not in line
        )
        v = scorecard.parse_validation(stderr)
        self.assertEqual(v["total"], 3)
        self.assertEqual(v["details"], [])

    def test_clean_module_carries_no_details_key(self) -> None:
        v = scorecard.parse_validation(
            "DEBUG trust-ir-lower: module validation summary, total=0\n"
        )
        self.assertEqual(v, {"total": 0, "classes": {}})

    def test_absent_summary_stays_none(self) -> None:
        self.assertIsNone(scorecard.parse_validation("nothing from the tripwire here\n"))


def _row(file: str, validation) -> dict:
    return {"file": file, "outcome": "ok", "bodies": [], "validation": validation}


class AggregateInvalidFilesTest(unittest.TestCase):
    def test_names_exactly_the_invalid_files(self) -> None:
        invalid = scorecard.parse_validation(INVALID_STDERR)
        clean = scorecard.parse_validation(
            "DEBUG trust-ir-lower: module validation summary, total=0\n"
        )
        legacy = {"total": 1, "classes": {"DuplicateFunctionName": 1}}  # pre-detail row
        results = [
            _row("a.rs", invalid),
            _row("b.rs", clean),
            _row("c.rs", None),
            _row("d.rs", legacy),
            {"file": "e.rs", "outcome": "timeout", "bodies": [], "validation": invalid},
        ]
        rows = scorecard.aggregate(results)["validation"]["invalid_files"]
        self.assertEqual([r["file"] for r in rows], ["a.rs", "d.rs"])
        self.assertEqual(rows[0]["total"], 3)
        self.assertEqual(rows[0]["details"], invalid["details"])
        # An older row simply has no `details` key — never an invented empty list.
        self.assertNotIn("details", rows[1])

    def test_all_clean_is_an_empty_list_not_a_missing_key(self) -> None:
        clean = {"total": 0, "classes": {}}
        agg = scorecard.aggregate([_row("a.rs", clean)])
        self.assertEqual(agg["validation"]["invalid_files"], [])


def _render(aggregate: dict) -> str:
    return scorecard.render_markdown(
        {
            "schema": "trust.trust-ir.producer-scorecard.v1",
            "provenance": {
                "date_utc": "2026-09-29T00:00:00+00:00",
                "repo_head": "a" * 40,
                "repo_describe": "test",
                "trustc_version_verbose": "trustc fixture",
                "rustc_log_filter": scorecard.RUSTC_LOG_FILTER,
                "compile_flags": [],
                "seed": 1,
            },
            "corpora": {"fixture": {"sample_meta": None, "aggregate": aggregate, "files": []}},
        }
    )


class RenderInvalidFilesTest(unittest.TestCase):
    def test_names_files_and_details_and_caps_the_list(self) -> None:
        invalid = scorecard.parse_validation(INVALID_STDERR)
        results = [_row(f"f{i:02}.rs", invalid) for i in range(22)]
        md = _render(scorecard.aggregate(results))
        self.assertIn(
            "  - INVALID `f00.rs`: {'CallArgTypeMismatch': 2, 'UnknownStruct': 1}", md
        )
        self.assertIn('    - UnknownStruct { id: StructId(12), name: "Wrapper<u8>" }', md)
        self.assertIn("  - INVALID `f19.rs`:", md)
        self.assertNotIn("  - INVALID `f20.rs`:", md)
        self.assertIn("  - ... +2 more invalid file(s); full list in data.json", md)

    def test_an_artifact_predating_the_key_still_renders(self) -> None:
        invalid = scorecard.parse_validation(INVALID_STDERR)
        aggregate = scorecard.aggregate([_row("a.rs", invalid)])
        del aggregate["validation"]["invalid_files"]
        md = _render(aggregate)
        self.assertIn("**1 of 1 INVALID**", md)
        self.assertNotIn("  - INVALID `", md)


if __name__ == "__main__":
    unittest.main()
