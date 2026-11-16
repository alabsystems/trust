#!/usr/bin/env python3
"""Regression tests for publish/strip_machine_paths.py (export transform T2).

TRUST-27: T2 rewrote only the `<home>/trust/` prefix, so sibling or scratch
checkouts, shared scratch trees and tilde links into the trust checkout reached
the export and were left for the central forbidden-content guard to reject at
stage time.

This file SHIPS in the public snapshot (scripts/ is allowlisted) and T2 runs
over it, so every machine path below is assembled at run time: a literal one
would be rewritten by the transform under test, and would trip the guard.
"""
from __future__ import annotations

import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "publish" / "strip_machine_paths.py"

USERS = "/" + "Users" + "/"
HOME = "/" + "home" + "/"
TILDE = "~" + "/"

# The central guard's path rules (publication/baseline/forbidden-content.txt),
# restated here so the test does not trust the script's own copy.
GUARD = [
    re.compile("/" + "Users" + "/[A-Za-z]"),
    re.compile("/" + "home" + "/[a-z]+/(ny|ay|clean|trust)"),
    re.compile("~" + "/(clean|trust)(/|$)", re.MULTILINE),
]


def guard_hits(text: str) -> list[str]:
    return [rule.pattern for rule in GUARD if rule.search(text)]


# publish/ is not part of the public snapshot, so the suite skips there. In the
# private tree publish/ exists, and a missing SCRIPT must fail, not skip.
@unittest.skipUnless((REPO / "publish").is_dir(), "publish/ is not part of the public snapshot")
class StripMachinePathsTests(unittest.TestCase):
    def run_t2(self, files: dict[str, str]) -> tuple[subprocess.CompletedProcess[str], dict[str, str]]:
        with tempfile.TemporaryDirectory() as tmp:
            export = Path(tmp) / "export"
            for rel, text in files.items():
                path = export / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            result = subprocess.run(
                [sys.executable, str(SCRIPT), str(export)],
                capture_output=True,
                text=True,
                timeout=60,
            )
            after = {rel: (export / rel).read_text(encoding="utf-8") for rel in files}
        return result, after

    def test_the_three_trust_27_shapes_are_rewritten_and_pass_the_guard(self) -> None:
        sibling = f"//! Source: `{USERS}someone/a3d-wt-trust/crates/a3d-kernel/src/lib.rs:140`\n"
        shared = f"logs under `{USERS}Shared/trust-bidirectional-main-20260915/root-main/`\n"
        tilde = f"compiled with `{TILDE}trust/build/host/stage2/bin/trustc`\n"
        result, after = self.run_t2({"a.rs": sibling, "b.md": shared, "c.md": tilde})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for rel, text in after.items():
            self.assertEqual(guard_hits(text), [], f"{rel}: {text!r}")
        # What the reader gets: the sibling's name survives, the owner does not.
        self.assertIn("<home>/a3d-wt-trust/crates/a3d-kernel/src/lib.rs:140", after["a.rs"])
        self.assertIn("<shared>/trust-bidirectional-main-20260915/root-main/", after["b.md"])
        self.assertIn("`build/host/stage2/bin/trustc`", after["c.md"])

    def test_the_original_prefix_is_still_made_repo_relative(self) -> None:
        text = f'"file": "{USERS}someone/trust/crates/trust-clean/fixtures/x/SOURCE.rs"\n'
        linux = f"at {HOME}someone/trust/library/core/src/lib.rs:1\n"
        result, after = self.run_t2({"d.json": text, "e.txt": linux})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(after["d.json"], '"file": "crates/trust-clean/fixtures/x/SOURCE.rs"\n')
        self.assertEqual(after["e.txt"], "at library/core/src/lib.rs:1\n")

    def test_other_first_party_homes_and_bare_tilde_links(self) -> None:
        text = (
            f"{HOME}someone/clean/Clean/Kernel.lean\n"
            f"{USERS}someone/ay/src/lib.rs\n"
            f"see {TILDE}clean/README.md\n"
            f"the checkout at {TILDE}trust\n"
        )
        result, after = self.run_t2({"f.md": text})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(guard_hits(after["f.md"]), [], after["f.md"])

    def test_text_without_machine_paths_is_byte_identical(self) -> None:
        text = "~/trust-corpora is a sibling corpus; /usr/lib and home/users stay.\n"
        result, after = self.run_t2({"g.md": text})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(after["g.md"], text)

    def test_this_file_carries_no_literal_machine_path(self) -> None:
        # It ships; T2 must leave it unchanged and the guard must not fire on it.
        self.assertEqual(guard_hits(Path(__file__).read_text(encoding="utf-8")), [])


if __name__ == "__main__":
    unittest.main()
