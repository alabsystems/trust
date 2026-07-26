#!/usr/bin/env python3
"""Keep the upstream baseline, its runbook command, and CLI default identical."""

from __future__ import annotations

from pathlib import Path
import re
import unittest


REPO_ROOT = Path(__file__).resolve().parents[2]


class UpstreamRevisionConsistencyTests(unittest.TestCase):
    def test_baseline_documented_command_and_cli_defaults_match(self) -> None:
        baseline = (REPO_ROOT / "tests" / "upstream-rust" / "baseline.toml").read_text(
            encoding="utf-8"
        )
        upstream_section = re.search(
            r"(?ms)^\[upstream\]\s*(.*?)(?=^\[)",
            baseline,
        )
        self.assertIsNotNone(upstream_section, "baseline has no [upstream] table")
        revision_match = re.search(
            r'(?m)^revision\s*=\s*"([^"]+)"\s*$', upstream_section.group(1)
        )
        self.assertIsNotNone(revision_match, "baseline [upstream] has no revision")
        baseline_revision = revision_match.group(1)

        documented = re.findall(r"--upstream-revision\s+(rust-lang/rust:[0-9a-f]{40})", baseline)
        self.assertEqual(
            documented,
            [baseline_revision],
            "the canonical baseline command must contain the exact current revision once",
        )

        main_source = (
            REPO_ROOT / "crates" / "trust-upstream-compat" / "src" / "main.rs"
        ).read_text(encoding="utf-8")
        cli_default = re.search(
            r'(?ms)const\s+DEFAULT_PORT_UPSTREAM_REVISION:\s*&str\s*=\s*"([^"]+)"\s*;',
            main_source,
        )
        self.assertIsNotNone(cli_default, "DEFAULT_PORT_UPSTREAM_REVISION is missing")
        self.assertEqual(cli_default.group(1), baseline_revision)

        porting_source = (
            REPO_ROOT / "crates" / "trust-upstream-compat" / "src" / "porting.rs"
        ).read_text(encoding="utf-8")
        reviewed_default = re.search(
            r'(?ms)const\s+DEFAULT_REVIEWED_UPSTREAM_REVISION:\s*&str\s*=\s*"([^"]+)"\s*;',
            porting_source,
        )
        self.assertIsNotNone(
            reviewed_default, "DEFAULT_REVIEWED_UPSTREAM_REVISION is missing"
        )
        self.assertEqual(reviewed_default.group(1), baseline_revision)


if __name__ == "__main__":
    unittest.main()
