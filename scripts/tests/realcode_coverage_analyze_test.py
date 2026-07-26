#!/usr/bin/env python3
"""Fail-closed tests for the report-local real-code analyzer."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ANALYZER = (
    Path(__file__).resolve().parents[2]
    / "reports/2026-06-29-honest-real-code-coverage/analyze.py"
)


def run_analyzer(directory: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(ANALYZER), str(directory)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


class RealcodeCoverageAnalyzeTest(unittest.TestCase):
    def test_non_dict_and_malformed_ty_shapes_are_failclosed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            dump = Path(temporary)
            (dump / "fixture.json").write_text(
                json.dumps(
                    {
                        "name": "fixture",
                        "def_path": "realcode::fixture",
                        "body": {
                            "locals": [{"ty": "Bool"}, {"ty": None}, {"ty": {}}],
                            "blocks": [],
                        },
                    }
                ),
                encoding="utf-8",
            )
            result = run_analyzer(dump)
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads(result.stdout)
            self.assertEqual(report["type_coverage"]["total_ty_nodes"], 3)
            self.assertEqual(report["type_coverage"]["structural_nodes"], 1)
            self.assertEqual(report["type_coverage"]["failclosed_nodes"], 2)
            self.assertEqual(report["type_coverage"]["failclosed_by_ctor"]["<unknown>"], 1)
            self.assertEqual(report["type_coverage"]["failclosed_by_ctor"]["<malformed>"], 1)
            self.assertEqual(
                report["type_coverage"]["method"],
                "report-local-syntactic-ty-constructor-count.v1",
            )
            self.assertEqual(report["per_func"][0]["def_path"], "realcode::fixture")
            self.assertEqual(
                report["loop_coverage"]["method"], "report-local-mir-shape-heuristic.v1"
            )

    def test_malformed_dump_is_fatal_not_silently_omitted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            dump = Path(temporary)
            (dump / "bad.json").write_text("{not-json", encoding="utf-8")
            result = run_analyzer(dump)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_duplicate_json_keys_are_fatal(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            dump = Path(temporary)
            (dump / "bad.json").write_text(
                '{"def_path":"realcode::a","def_path":"realcode::b","body":{}}',
                encoding="utf-8",
            )
            result = run_analyzer(dump)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("duplicate JSON key", result.stderr)


if __name__ == "__main__":
    unittest.main()
