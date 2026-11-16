#!/usr/bin/env python3
"""Focused recipe and fail-closed report tests; no upstream suite is run."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "run_upstream_rust_adopted_evidence.py"
SPEC = importlib.util.spec_from_file_location("run_upstream_rust_adopted_evidence", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
runner = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = runner
SPEC.loader.exec_module(runner)

PIN = "a" * 40
TRACKED_PIN = "b" * 40
HOST = "aarch64-apple-darwin"


def result(log_id: str, *, status: int = 0, stdout: str = "", stderr: str = "") -> runner.CommandResult:
    return runner.CommandResult(
        argv=[log_id],
        command=log_id,
        exit_status=status,
        timed_out=False,
        stdout_path=f"logs/{log_id}.stdout.txt",
        stderr_path=f"logs/{log_id}.stderr.txt",
        stdout_excerpt=stdout,
        stderr_excerpt=stderr,
    )


def flag(argv: list[str], name: str) -> str:
    return argv[argv.index(name) + 1]


class AdoptedUpstreamRecipeTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="adopted upstream recipe ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name, "repo with spaces")
        self.root.mkdir()
        self.stage2 = self.root / "build" / HOST / "stage2"
        self.report_dir = self.root / "reports" / "upstream-rust" / "run with spaces"

    def commands(self, host: str | None = HOST, tracked: str | None = f"rust-lang/rust:{TRACKED_PIN}") -> list[dict]:
        return runner.full_suite_commands(
            self.root,
            self.stage2,
            self.report_dir,
            f"rust-lang/rust:{PIN}",
            tracked,
            host,
            "adopted-upstream-20260924T010203Z",
        )

    def test_release_argv_is_complete_native_no_apply_and_runnable(self) -> None:
        baseline, tracked, direct = self.commands()
        self.assertEqual(baseline["kind"], "canonical_release_scorecard")
        self.assertEqual(tracked["kind"], "tracked_upstream_scorecard")
        self.assertEqual(direct["kind"], "guarded_xpy_compiletest")
        out_dir = "reports/upstream-rust/run with spaces/adopted_baseline_release_full"
        summary_out = f"{out_dir}/compat-summary.json"
        self.assertEqual(
            baseline["argv"],
            [
                str(self.stage2 / "bin" / "targo"),
                "trust", "domination", "upstream-tests", "--release",
                "--proof-scope", "upstream-rust", "--proof-mode", "full",
                "--execute", "--no-apply", "--summary-out", summary_out,
                "--out-dir", out_dir, "--run-id",
                "adopted-upstream-20260924T010203Z-adopted_baseline_release_full",
                "--target-arch", "aarch64", "--target", HOST,
                "--target-triple", HOST, "--host", "aarch64", "--host-triple", HOST,
                "--upstream-revision", f"rust-lang/rust:{PIN}",
                "--upstream-remote", "https://github.com/rust-lang/rust.git",
                "--no-fetch",
            ],
        )
        self.assertEqual(baseline["summary_out"], summary_out)
        self.assertEqual(baseline["out_dir"], out_dir)
        self.assertIn("--compat-summary", baseline["validation_command"])
        self.assertIn("--target-triple", baseline["validation_command"])
        self.assertIsNone(tracked["validation_command"])
        self.assertEqual(flag(tracked["argv"], "--upstream-revision"), f"rust-lang/rust:{TRACKED_PIN}")
        self.assertNotIn("--apply", baseline["argv"])
        self.assertNotIn("--no-execute", baseline["argv"])
        self.assertNotIn("<run-id>", baseline["command"])

        bin_dir = self.stage2 / "bin"
        bin_dir.mkdir(parents=True)
        targo = bin_dir / "targo"
        targo.write_text(
            '#!/bin/sh\nprintf "%s\\n" "$@" > "$RECIPE_CAPTURE"\n'
            'printf "sysroot=%s\\n" "$TRUST_STAGE2_SYSROOT" >> "$RECIPE_CAPTURE"\n',
            encoding="utf-8",
        )
        targo.chmod(0o755)
        captured = self.root / "captured argv.txt"
        with mock.patch.dict("os.environ", {"RECIPE_CAPTURE": str(captured)}):
            subprocess.run(["/bin/sh", "-c", baseline["command"]], check=True)
        self.assertEqual(
            captured.read_text(encoding="utf-8").splitlines(),
            baseline["argv"][1:] + [f"sysroot={self.stage2}"],
        )

    def test_unverified_identity_downgrades_release_recipes(self) -> None:
        baseline, tracked, direct = self.commands(host=None)
        for row in (baseline, tracked):
            self.assertEqual(row["kind"], "release_recipe_unavailable")
            self.assertEqual(row["argv"], [])
            self.assertIsNone(row["command"])
            self.assertIn("no release command or claim", row["not_run_reason"])
        self.assertEqual(direct["kind"], "guarded_xpy_compiletest")

    def test_symbolic_tracked_revision_does_not_claim_local_no_fetch(self) -> None:
        baseline, tracked, _ = self.commands(tracked="rust-lang/rust:main")
        self.assertIn("--no-fetch", baseline["argv"])
        self.assertNotIn("--no-fetch", tracked["argv"])
        self.assertEqual(flag(tracked["argv"], "--upstream-revision"), "rust-lang/rust:main")

    def test_native_identity_requires_guard_trustc_and_physical_host_match(self) -> None:
        trustc = result("trustc", stdout=f"trustc 1.99.0\nhost: {HOST}\n")
        guard = result("guard")
        self.assertEqual(runner.native_stage2_host_triple(self.stage2, trustc, guard), HOST)
        self.assertIsNone(runner.native_stage2_host_triple(self.stage2, trustc, result("guard", status=1)))
        self.assertIsNone(runner.native_stage2_host_triple(self.stage2, result("trustc", status=1), guard))
        self.assertIsNone(runner.native_stage2_host_triple(self.stage2, result("trustc", stdout="trustc 1.99.0\n"), guard))
        self.assertIsNone(runner.native_stage2_host_triple(
            self.stage2, result("trustc", stdout="host: x86_64-apple-darwin\n"), guard))
        self.assertIsNone(runner.native_stage2_host_triple(
            self.root / "build" / "host" / "stage2", trustc, guard))
        self.assertIsNone(runner.native_stage2_host_triple(
            self.root / "build" / "aarch64-unknown-freebsd" / "stage2",
            result("trustc", stdout="host: aarch64-unknown-freebsd\n"), guard))

    def test_linux_recipe_uses_linux_runtime_library_path(self) -> None:
        host = "x86_64-unknown-linux-gnu"
        self.stage2 = self.root / "build" / host / "stage2"
        self.assertEqual(runner.native_stage2_host_triple(
            self.stage2, result("trustc", stdout=f"host: {host}\n"), result("guard")), host)
        baseline, direct = self.commands(host=host, tracked=None)
        self.assertEqual(flag(baseline["argv"], "--host-triple"), host)
        self.assertEqual(flag(baseline["argv"], "--target-triple"), host)
        self.assertIn("LD_LIBRARY_PATH=", baseline["command"])
        self.assertNotIn("DYLD_LIBRARY_PATH=", baseline["command"])
        self.assertEqual(direct["kind"], "guarded_xpy_compiletest")

    def build_report(self, *, guard_status: int = 0, trustc_output: str | None = None) -> dict:
        args = runner.parse_args([
            "--root", str(self.root), "--stage2-sysroot", str(self.stage2),
            "--output-dir", str(self.report_dir), "--validation-date", "2026-09-24",
        ])
        if trustc_output is None:
            trustc_output = f"trustc 1.99.0\nhost: {HOST}\n"

        def capture(argv: list[str], **kwargs: object) -> runner.CommandResult:
            log_id = str(kwargs["log_id"])
            if log_id == "trustc-vv":
                return result(log_id, stdout=trustc_output)
            if log_id == "toolchain-guard":
                return result(log_id, status=guard_status)
            if log_id == "representative-scoped-batch":
                return result(log_id, status=1, stderr="Building stage2 compiler artifacts\n")
            return result(log_id)

        with (
            mock.patch.object(runner, "git", return_value="c" * 40),
            mock.patch.object(runner, "baseline_revision", return_value=f"rust-lang/rust:{PIN}"),
            mock.patch.object(runner, "tracked_revision", return_value=f"rust-lang/rust:{TRACKED_PIN}"),
            mock.patch.object(runner, "disk_preflight", return_value={"status": "passed"}),
            mock.patch.object(runner, "run_capture", side_effect=capture),
            mock.patch.object(runner, "active_test_exceptions", return_value=[{"id": "existing-ledger-row"}]),
            mock.patch.object(runner, "upstream_test_counts", return_value={"primary_compiletest_paths": 2}),
        ):
            return runner.build_report(args)

    def test_report_preserves_unrun_and_expected_failure_buckets(self) -> None:
        report = self.build_report()
        self.assertEqual(report["validation"]["status"], "passed")
        self.assertFalse(report["claims"]["full_suite_success_claimed"])
        self.assertTrue(report["claims"]["no_source_overlay_applied"])
        self.assertEqual(report["preflight"]["native_stage2_host_triple"], HOST)
        self.assertEqual(report["status_buckets"]["known_expected_failures"], [{"id": "existing-ledger-row"}])
        self.assertEqual(report["status_buckets"]["passed"][0]["id"], "trustc_identity")
        self.assertEqual(report["status_buckets"]["failed"], [])
        self.assertEqual(report["status_buckets"]["blocked_by_precondition"], [])
        unrun = report["status_buckets"]["not_yet_run_due_to_cost"]
        self.assertEqual({row["id"] for row in unrun}, {
            "representative_scoped_batch", "adopted_baseline_release_full",
            "tracked_upstream_release_full", "current_tree_direct_compiletest_full",
        })
        self.assertTrue(all(row["status"] != "passed" for row in unrun))
        self.assertEqual(report["row_counts_by_status"], runner.row_counts_by_status(report["status_buckets"]))

    def test_report_blocks_release_recipe_when_identity_unavailable(self) -> None:
        for kwargs in ({"guard_status": 1}, {"trustc_output": "trustc 1.99.0\n"}):
            with self.subTest(kwargs=kwargs):
                report = self.build_report(**kwargs)
                self.assertEqual(report["validation"]["status"], "passed")
                self.assertFalse(report["claims"]["full_suite_success_claimed"])
                self.assertIsNone(report["preflight"]["native_stage2_host_triple"])
                self.assertEqual(
                    {row["id"] for row in report["status_buckets"]["blocked_by_precondition"]},
                    {"adopted_baseline_release_full", "tracked_upstream_release_full"}
                    | ({"representative_scoped_batch"} if kwargs.get("guard_status") else set()),
                )
                self.assertTrue(all(
                    row["kind"] == "release_recipe_unavailable"
                    for row in report["commands"]["full_suite"][:2]
                ))
                self.assertEqual(report["row_counts_by_status"], runner.row_counts_by_status(report["status_buckets"]))


if __name__ == "__main__":
    unittest.main()
