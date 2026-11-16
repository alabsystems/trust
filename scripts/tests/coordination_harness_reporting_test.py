#!/usr/bin/env python3
"""Optional coordination failures stay visible through the real harness and hook."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
HARNESS = ROOT / "tests/run_trust_comprehensive_harness.sh"
HOOK = ROOT / "scripts/hooks/pre-push"
# Synthetic rows. These controls once borrowed the real manifest's
# `fast.two-language-claim-ledger` (advisory) and its `-selftest` (required)
# rows; both were removed on 2026-09-30 with the retired ledger they read, and
# the property under test -- an optional row's failure is reported, is not
# evidence and blocks nothing, while a required row's failure still blocks --
# belongs to the harness and hook, not to any one lane.
ADVISORY = "fast.fixture-advisory"
SELFTEST = "fast.fixture-required-control"
PRODUCT = "scoped.fixture-product"
ROW_TEMPLATES = {
    ADVISORY: [ADVISORY, "fast,push,release", "infrastructure", "false", "never", ""],
    SELFTEST: [SELFTEST, "fast,push,release", "infrastructure", "true", "never", ""],
}


def harness_python():
    """Find the harness's existing Python >=3.10 + TOML prerequisite."""
    candidates = [sys.executable]
    candidates.extend(shutil.which(name) for name in (
        "python3.14", "python3.13", "python3.12", "python3.11", "python3.10",
    ))
    probe = (
        "import importlib.util, sys; "
        "sys.exit(0 if sys.version_info >= (3, 10) and "
        "(importlib.util.find_spec('tomllib') or importlib.util.find_spec('tomli')) else 1)"
    )
    for candidate in dict.fromkeys(candidates):
        if candidate and subprocess.run([candidate, "-c", probe], capture_output=True).returncode == 0:
            return candidate
    return None


class CoordinationReportingControls(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-coordination-report-")
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)
        (self.repo / "tests/trust-comprehensive").mkdir(parents=True)
        (self.repo / "scripts/hooks").mkdir(parents=True)
        # The shell harness has an existing Python >=3.10 requirement. Do not
        # let macOS's older system `python3` obscure the reporting controls.
        self.harness_python = harness_python()
        self.fixture_bin = self.repo / "fixture-bin"
        self.fixture_bin.mkdir()
        if self.harness_python:
            (self.fixture_bin / "python3").symlink_to(self.harness_python)
        self.harness = self.repo / "tests" / HARNESS.name
        self.hook = self.repo / "scripts/hooks/pre-push"
        self.hook.write_text(HOOK.read_text(), encoding="utf-8")
        (self.repo / "tests/trust-comprehensive/divergences.toml").write_text(
            'schema_version = "0.1.0"\ndivergences = []\n', encoding="utf-8"
        )
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)

    def fixture(self, advisory: int, selftest: int = 0, product: int = 0,
                *, advisory_id: str = ADVISORY) -> None:
        source = HARNESS.read_text(encoding="utf-8")
        marker = "<<'EOF'"
        start = source.index(marker, source.index("emit_gate_manifest() {")) + len(marker)
        end = source.index("\nEOF\n", start)
        # Replace the whole manifest with tiny controls the real runners execute.
        rows = []
        for gate_id, name, status in ((ADVISORY, "advisory", advisory),
                                      (SELFTEST, "selftest", selftest)):
            row = list(ROW_TEMPLATES[gate_id])
            if gate_id == ADVISORY:
                row[0] = advisory_id
            row[5] = f"bash tests/{name}.sh"
            rows.append("|".join(row))
            (self.repo / "tests" / f"{name}.sh").write_text(
                f"echo 'fixture {name} ran'\nexit {status}\n", encoding="utf-8"
            )
        rows.append(f"{PRODUCT}|fast,push|soundness|true|never|bash tests/product.sh")
        (self.repo / "tests/product.sh").write_text(
            f"echo 'fixture product ran'\nexit {product}\n", encoding="utf-8"
        )
        self.harness.write_text(source[:start] + "\n" + "\n".join(rows) + source[end:],
                                encoding="utf-8")

    def run_harness(self):
        if not self.harness_python:
            self.skipTest("real harness requires Python >=3.10 with tomllib or tomli")
        environment = dict(os.environ)
        environment.update({
            "PATH": str(self.fixture_bin) + os.pathsep + environment.get("PATH", ""),
            "TRUST_COMPREHENSIVE_OUT_DIR": str(self.repo / "report"),
            "TRUST_COMPREHENSIVE_RUN_ID": "fixture",
            # An optional error must not prevent later required checks running.
            "TRUST_COMPREHENSIVE_FAIL_FAST": "1",
        })
        result = subprocess.run(["bash", str(self.harness), "fast"], cwd=self.repo,
                                env=environment, capture_output=True, text=True)
        report_path = self.repo / "report/report.json"
        self.assertTrue(report_path.exists(), result.stdout + result.stderr)
        report = json.loads(report_path.read_text())
        return result, report

    def run_hook(self):
        environment = dict(os.environ)
        for key in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "TRUST_PUSHED_REFS"):
            environment.pop(key, None)
        return subprocess.run(["bash", str(self.hook)], cwd=self.repo, env=environment,
                              input="", capture_output=True, text=True)

    def test_optional_crash_and_timeout_are_failed_not_evidence_without_blocking_harness(self):
        for status in (1, 124, 137):
            with self.subTest(status=status):
                self.fixture(status)
                result, report = self.run_harness()
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(report["verdict"], "passed")
                self.assertEqual(len(report["gates"]), 3, "optional failure stopped required checks")
                row = report["gates"][0]
                self.assertEqual(row["gate_id"], ADVISORY)
                self.assertFalse(row["required"])
                self.assertEqual(row["status"], "failed")
                self.assertEqual(row["exit_code"], status)
                self.assertEqual(row["evidence_classification"], "not_evidence")
                self.assertFalse(row["proof_evidence"])
                self.assertFalse(row["release_evidence"])
                self.assertIn(f"status:   FAIL exit={status}", result.stdout)

    def test_required_validator_selftest_failure_still_blocks_harness(self):
        self.fixture(137, selftest=1)
        result, report = self.run_harness()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(report["verdict"], "failed_undocumented")
        self.assertEqual([row["gate_id"] for row in report["gates"]], [ADVISORY, SELFTEST])
        self.assertTrue(report["gates"][1]["required"])
        self.assertEqual(report["gates"][1]["status"], "failed")

    def test_required_product_failure_still_blocks_harness(self):
        self.fixture(137, product=1)
        result, report = self.run_harness()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(report["verdict"], "failed_undocumented")
        self.assertEqual(report["gates"][-1]["gate_id"], PRODUCT)
        self.assertTrue(report["gates"][-1]["required"])

    def test_hook_surfaces_optional_failure_and_runs_required_checks(self):
        self.fixture(124)
        result = self.run_hook()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"WARN: {ADVISORY} FAILED exit=124", result.stdout)
        self.assertIn(f"PASS: {SELFTEST}", result.stdout)
        self.assertIn(f"PASS: {PRODUCT}", result.stdout)
        self.assertNotIn(f"PASS: {ADVISORY}\n", result.stdout)

    def test_hook_required_validator_and_product_failures_still_block(self):
        for selftest, product in ((1, 0), (0, 1)):
            with self.subTest(selftest=selftest, product=product):
                self.fixture(137, selftest=selftest, product=product)
                result = self.run_hook()
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(f"FAIL: {SELFTEST if selftest else PRODUCT}", result.stdout)
                self.assertIn("PRE-PUSH: RED", result.stdout)

    def test_hook_carries_optional_flag_through_scoped_dispatch(self):
        self.fixture(137, advisory_id="scoped.fixture-advisory")
        result = self.run_hook()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("WARN: scoped.fixture-advisory FAILED exit=137", result.stdout)

    def test_ignoring_hook_required_flag_recreates_the_push_blocker(self):
        self.fixture(137)
        baseline = self.run_hook()
        self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
        source = self.hook.read_text()
        # Every dispatch path that carries `required` into lane_grade must
        # ignore it, or the mutation proves nothing about the paths it
        # missed: three textual run_lane sites (solo fast lanes, a scoped
        # lane before the overlapped one (227d82898a), every other scoped
        # lane), the jobs<=1 array form, the pooled grade_fast_lane call,
        # and grade_overlap_lane. The pooled path is the one this fixture
        # takes (pool of 16), which is why the run_lane-only mutation read
        # rc=0 (docs/issues/2026-10-26-pre-push-required-flag-mutation-control-CLOSED.md).
        anchors = [
            ('run_lane "$gate_id" "$command" "$required"',
             'run_lane "$gate_id" "$command" "true"', 3),
            ('run_lane "${ids[$i]}" "${cmds[$i]}" "${reqs[$i]}"',
             'run_lane "${ids[$i]}" "${cmds[$i]}" "true"', 1),
            ('grade_fast_lane "$printed" "${ids[$printed]}" "${cmds[$printed]}" "${reqs[$printed]}"',
             'grade_fast_lane "$printed" "${ids[$printed]}" "${cmds[$printed]}" "true"', 1),
            ('grade_overlap_lane "$gate_id" "$required" "$command"',
             'grade_overlap_lane "$gate_id" "true" "$command"', 1),
        ]
        for original, mutated, count in anchors:
            self.assertEqual(
                source.count(original), count, f"re-anchor dispatch path: {original}")
            source = source.replace(original, mutated)
        self.hook.write_text(source)
        mutated = self.run_hook()
        self.assertEqual(mutated.returncode, 1, mutated.stdout + mutated.stderr)
        self.assertIn(f"FAIL: {ADVISORY}", mutated.stdout)


if __name__ == "__main__":
    unittest.main()
