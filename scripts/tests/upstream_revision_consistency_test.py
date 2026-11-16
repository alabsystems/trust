#!/usr/bin/env python3
"""Keep the baseline, documented command, and release alignment consistent.

The CLI now resolves an omitted upstream revision from the selected baseline;
porting compares against that same parsed baseline. There is no independent
Rust default revision to bump. The native trust-upstream-compat tests check
selected-baseline resolution, explicit overrides, and invalid-baseline refusal.

The required fast diagnostic row retains mutation controls for record consistency
and accidental reintroduction of retired fixed defaults. Development-main pushes
use the focused live-verifier and proof-input profile; migrations run these
revision controls explicitly. Parsing remains compatible with Python 3.9.
"""

from __future__ import annotations

import re
import shutil
import tempfile
import unittest
from pathlib import Path
from typing import List, Optional


REPO_ROOT = Path(__file__).resolve().parents[2]

BASELINE = "tests/upstream-rust/baseline.toml"
ALIGNMENT = "release/trust-version.toml"
CLI = "crates/trust-upstream-compat/src/main.rs"
PORTING = "crates/trust-upstream-compat/src/porting.rs"
HARNESS = "tests/run_trust_comprehensive_harness.sh"
THIS_TEST = "scripts/tests/upstream_revision_consistency_test.py"

# Retired independent defaults must not become a second revision authority.
RETIRED_DEFAULTS = (
    (CLI, "DEFAULT_PORT_UPSTREAM_REVISION"),
    (PORTING, "DEFAULT_REVIEWED_UPSTREAM_REVISION"),
)

def table_revision(text: str, table: str) -> Optional[str]:
    """The `revision = "..."` value of TOML table `[table]`, or None."""
    section = re.search(rf"(?ms)^\[{re.escape(table)}\]\s*(.*?)(?=^\[|\Z)", text)
    if section is None:
        return None
    match = re.search(r'(?m)^revision\s*=\s*"([^"]+)"\s*$', section.group(1))
    return match.group(1) if match else None


def findings(root: Path) -> List[str]:
    """Every spelling that disagrees with the baseline, one line each."""

    def read(rel: str) -> str:
        return (root / rel).read_text(encoding="utf-8")

    baseline_text = read(BASELINE)
    baseline = table_revision(baseline_text, "upstream")
    if baseline is None:
        return [f"{BASELINE}: [upstream] has no revision"]

    out = []
    documented = re.findall(
        r"--upstream-revision\s+(rust-lang/rust:[0-9a-f]{40})", baseline_text
    )
    if documented != [baseline]:
        out.append(
            f"{BASELINE}: the canonical port command must name {baseline} exactly "
            f"once; it names {documented}"
        )

    alignment = table_revision(read(ALIGNMENT), "rust_alignment")
    if alignment != baseline:
        out.append(
            f"{ALIGNMENT}: [rust_alignment] revision is {alignment!r}, "
            f"the baseline is {baseline}"
        )

    for rel, name in RETIRED_DEFAULTS:
        if re.search(rf"\bconst\s+{re.escape(name)}\s*:", read(rel)):
            out.append(f"{rel}: retired fixed default {name} must derive from the selected baseline")
    return out


def manifest_rows(harness_text: str) -> List[List[str]]:
    body = re.search(
        r"(?ms)^emit_gate_manifest\(\) \{\n\s*cat <<'EOF'\n(.*?)^EOF$", harness_text
    )
    if body is None:
        return []
    return [
        line.split("|", 5)
        for line in body.group(1).splitlines()
        if line.count("|") >= 5
    ]


def required_profile_rows_running(
    harness_text: str, script: str, profile: str
) -> List[List[str]]:
    """Required manifest rows in the selected profile that run `script`."""
    return [
        row
        for row in manifest_rows(harness_text)
        if profile in row[1].split(",") and row[3] == "true" and script in row[5]
    ]


class UpstreamRevisionConsistencyTests(unittest.TestCase):
    def test_every_spelling_matches_the_baseline(self) -> None:
        self.assertEqual(findings(REPO_ROOT), [])

    def test_remains_an_explicit_required_fast_diagnostic(self) -> None:
        harness = (REPO_ROOT / HARNESS).read_text(encoding="utf-8")
        self.assertTrue(manifest_rows(harness), f"{HARNESS}: no emit_gate_manifest rows parsed")
        self.assertTrue(
            required_profile_rows_running(harness, THIS_TEST, "fast"),
            f"no required `fast` diagnostic row of {HARNESS} runs {THIS_TEST}",
        )
        self.assertEqual(required_profile_rows_running(harness, THIS_TEST, "push"), [])


class MutationControls(unittest.TestCase):
    """Record drift and reintroduced fixed defaults must be refused."""

    # A revision no file spells, so the mutation is the only difference.
    OTHER = "rust-lang/rust:0123456789abcdef0123456789abcdef01234567"

    def setUp(self) -> None:
        self.root = self.fresh_copy()

    def fresh_copy(self) -> Path:
        root = Path(tempfile.mkdtemp(prefix="upstream-revision-consistency-"))
        self.addCleanup(shutil.rmtree, root, ignore_errors=True)
        for rel in (BASELINE, ALIGNMENT, CLI, PORTING):
            target = root / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(REPO_ROOT / rel, target)
        self.baseline = table_revision(
            (root / BASELINE).read_text(encoding="utf-8"), "upstream"
        )
        self.assertIsNotNone(self.baseline)
        self.assertNotEqual(self.OTHER, self.baseline)
        self.assertEqual(findings(root), [], "the unmutated copy must pass")
        return root

    def rewrite(self, rel: str, old: str, new: str, count: int) -> None:
        path = self.root / rel
        text = path.read_text(encoding="utf-8")
        self.assertEqual(text.count(old), count, f"{rel}: expected {count} of {old!r}")
        path.write_text(text.replace(old, new), encoding="utf-8")

    def assert_names_exactly(self, rels: List[str]) -> None:
        found = findings(self.root)
        self.assertEqual(
            sorted(line.split(":", 1)[0] for line in found), sorted(rels), found
        )

    def test_a_consistent_baseline_migration_needs_no_rust_constant_bump(self) -> None:
        self.rewrite(BASELINE, self.baseline, self.OTHER, 2)
        self.rewrite(ALIGNMENT, self.baseline, self.OTHER, 1)
        self.assertEqual(findings(self.root), [])

    def test_each_retired_fixed_default_is_refused(self) -> None:
        for rel, name in RETIRED_DEFAULTS:
            for value in (self.baseline, self.OTHER):
                with self.subTest(constant=name, value=value):
                    self.root = self.fresh_copy()
                    path = self.root / rel
                    with path.open("a", encoding="utf-8") as target:
                        target.write(f'\nconst {name}: &str = "{value}";\n')
                    self.assert_names_exactly([rel])

    def test_a_missing_baseline_revision_is_refused(self) -> None:
        self.rewrite(BASELINE, "\n[upstream]\n", "\n[retired_upstream]\n", 1)
        self.assertEqual(findings(self.root), [f"{BASELINE}: [upstream] has no revision"])

    def test_rust_alignment_is_checked(self) -> None:
        self.rewrite(ALIGNMENT, self.baseline, self.OTHER, 1)
        self.assert_names_exactly([ALIGNMENT])

    def test_documented_command_is_checked(self) -> None:
        self.rewrite(
            BASELINE,
            f"--upstream-revision {self.baseline}",
            f"--upstream-revision {self.OTHER}",
            1,
        )
        self.assert_names_exactly([BASELINE])

    def test_a_fast_only_or_optional_row_is_not_the_push_path(self) -> None:
        harness = (REPO_ROOT / HARNESS).read_text(encoding="utf-8")
        rows = [row for row in manifest_rows(harness) if THIS_TEST in row[5]]
        self.assertTrue(rows, f"no {HARNESS} row runs {THIS_TEST}")
        for column, value in ((1, "fast"), (3, "false")):
            with self.subTest(column=column, value=value):
                mutated = harness
                for row in rows:
                    changed = list(row)
                    changed[column] = value
                    mutated = mutated.replace("|".join(row), "|".join(changed), 1)
                self.assertEqual(
                    required_profile_rows_running(mutated, THIS_TEST, "push"), []
                )
                self.assertEqual(
                    bool(required_profile_rows_running(mutated, THIS_TEST, "fast")),
                    column == 1,
                )


if __name__ == "__main__":
    unittest.main()
