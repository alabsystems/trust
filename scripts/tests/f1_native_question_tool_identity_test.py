#!/usr/bin/env python3
"""The F1 driver requires a working explicit Targo lane, not one version banner."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import MagicMock, patch

spec = importlib.util.spec_from_file_location(
    "f1_question_driver", Path(__file__).resolve().parents[1] / "check_f1_native_question_binding.py"
)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


class ToolIdentityTests(unittest.TestCase):
    def test_current_and_seed_banners_require_the_same_explicit_lane(self):
        for banner in (
            "targo 1.98.0 (aa5290982 2026-11-13) (targo)\n",
            "targo 1.101.0-dev (82bb867ed 2026-11-07) (targo 0.13.0+g82bb867ed)\n",
        ):
            with self.subTest(banner=banner), patch.object(
                driver.subprocess, "check_output", return_value=banner
            ) as probe:
                self.assertEqual(driver.genuine_targo_identity(Path("/tools/targo"), {}, (7, 8)),
                                 banner.strip())
                probe.assert_called_once_with(
                    ["/tools/targo", "--unverified", "--version"], cwd=driver.ROOT,
                    env={}, text=True, pass_fds=(7, 8),
                )

    def test_a_lane_refusal_is_not_hidden_by_a_targo_banner(self):
        refused = subprocess.CalledProcessError(2, ["/tools/targo", "--unverified", "--version"])
        with patch.object(driver.subprocess, "check_output", side_effect=refused):
            with self.assertRaises(subprocess.CalledProcessError):
                driver.genuine_targo_identity(Path("/tools/targo"), {}, ())

    def test_empty_and_non_targo_output_refuse(self):
        for output in ("", "\n", "cargo 1.98.0\n", "targo-compatible 1.0\n"):
            with self.subTest(output=output), patch.object(
                driver.subprocess, "check_output", return_value=output
            ):
                with self.assertRaises(RuntimeError):
                    driver.genuine_targo_identity(Path("/tools/targo"), {}, ())


class NativeQuestionExecutionTests(unittest.TestCase):
    """Exercise the checker protocol without bootstrapping a compiler."""

    summary = "test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;"
    cases = (
        "actual_native_questions_and_compiled_function_share_ir_owned_digests",
        "changed_verified_function_is_refused_even_when_unknown_output_would_ship",
        "unchanged_body_does_not_hide_a_changed_module_type_context",
    )

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.targo = self.root / "targo"
        self.targo.write_text("fixture tool; never executed")
        self.image = self.root / "compiled-harness"
        self.image.write_bytes(b"retained harness fixture")
        package = self.root / "crates/trust-cg-bridge"
        self.artifact = {
            "reason": "compiler-artifact", "executable": str(self.image),
            "target": {"name": "f1_native_question_binding", "kind": ["test"],
                       "src_path": str(package / "tests/f1_native_question_binding.rs")},
            "profile": {"test": True}, "manifest_path": str(package / "Cargo.toml"),
            "package_id": "fixture-package-id",
            "trust_executable_sha256": hashlib.sha256(self.image.read_bytes()).hexdigest(),
        }

    def action(self, state, **changes):
        return {
            "reason": "test-execution", "schema": "targo.test-execution.v2", "state": state,
            "total": 1, "index": 0, "package": "trust-cg-bridge", "package_id": "fixture-package-id",
            "target": "f1_native_question_binding", "kind": "test", "harness": True,
            "prerequisite_artifact": str(self.image), "signal": None, "weight": 1, "exclusive": False,
            "exit_code": 0 if state == "passed" else None, **changes,
        }

    def output(self, line, stream="stdout"):
        return {"reason": "test-output", "schema": "targo.test-output.v1", "index": 0,
                "stream": stream, "line": line}

    def wire(self, cases=None, summary=None):
        cases = self.cases if cases is None else cases
        summary = self.summary if summary is None else summary
        return [
            self.artifact, self.action("ready"), self.action("running"),
            self.output("diagnostic with an incidental test reference", "stderr"),
            *(self.output(f"test {name} ... ok") for name in cases),
            self.output(summary), self.action("passed"),
        ]

    def execute(self, rows, code=0):
        process = MagicMock()
        process.__enter__.return_value = process
        process.stdout = iter((line if isinstance(line, str) else json.dumps(line)) + "\n" for line in rows)
        process.wait.return_value = code
        argv = ["driver", "--targo", str(self.targo), "--target-dir", str(self.root / "target")]
        with patch.object(driver.sys, "argv", argv), patch.object(driver, "ROOT", self.root), patch.object(
            driver, "genuine_targo_identity", return_value="targo fixture"
        ), patch.object(driver.landing_targo, "resource_fds", return_value=()), patch.object(
            driver.subprocess, "Popen", return_value=process
        ) as launch, patch("builtins.print"):
            result = driver.main()
        command = launch.call_args.args[0]
        self.assertEqual(command[command.index("--test") + 1], "f1_native_question_binding")
        self.assertEqual(command[command.index("--target-dir") + 1], str(self.root / "target"))
        self.assertIn("--message-format=json-render-diagnostics", command)
        self.assertNotIn("stderr", launch.call_args.kwargs)
        return result

    def test_complete_bound_inventory_is_required(self):
        self.assertEqual(self.execute(self.wire()), 0)

    def test_text_summary_without_observed_actions_refuses(self):
        with self.assertRaisesRegex(RuntimeError, "lifecycle"):
            self.execute([self.summary])

    def test_equal_count_with_wrong_test_or_stderr_only_refuses(self):
        rows = self.wire()
        rows[4] = self.output(rows[4]["line"], "stderr")
        for wire in (self.wire(("other_test", *self.cases[1:])), rows):
            with self.subTest(wire=wire), self.assertRaisesRegex(RuntimeError, "expected tests"):
                self.execute(wire)

    def test_invalid_summaries_cannot_admit_a_good_roster(self):
        for summary in (self.summary.replace("3 passed", "2 passed"),
                        self.summary.replace("0 failed", "1 failed"),
                        self.summary.replace("0 ignored", "1 ignored"),
                        self.summary.replace("0 filtered out", "1 filtered out")):
            with self.subTest(summary=summary), self.assertRaisesRegex(RuntimeError, "expected tests"):
                self.execute(self.wire(summary=summary))

    def test_missing_or_wrong_action_binding_refuses(self):
        rows = self.wire()
        for change in (None, self.action("passed", prerequisite_artifact="not-built"),
                       self.action("passed", package_id="different-package")):
            wire = rows[:-1] if change is None else [*rows[:-1], change]
            with self.subTest(change=change), self.assertRaisesRegex(RuntimeError, "lifecycle|compiled artifact"):
                self.execute(wire)

    def test_same_path_with_changed_artifact_bytes_refuses(self):
        rows = self.wire()
        self.image.write_bytes(b"different retained harness")
        with self.assertRaisesRegex(RuntimeError, "artifact digest"):
            self.execute(rows)

    def test_failed_child_cannot_borrow_a_successful_wire(self):
        self.assertEqual(self.execute(self.wire(), code=9), 9)


if __name__ == "__main__":
    unittest.main()
