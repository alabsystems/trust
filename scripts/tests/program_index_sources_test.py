#!/usr/bin/env python3
"""The committed benchmark roster must name present source files."""

from __future__ import annotations

import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "examples/bench/program_index/index.json"


class ProgramIndexSourcesTests(unittest.TestCase):
    def test_every_program_source_exists(self) -> None:
        index = json.loads(INDEX.read_text(encoding="utf-8"))
        missing = sorted(
            row["path"]
            for row in index["programs"]
            if not (ROOT / row["path"]).is_file()
        )
        self.assertEqual(missing, [])


if __name__ == "__main__":
    unittest.main()
