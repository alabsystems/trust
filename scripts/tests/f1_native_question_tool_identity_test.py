#!/usr/bin/env python3
"""The F1 driver requires a working explicit Targo lane, not one version banner."""

import importlib.util
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

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


if __name__ == "__main__":
    unittest.main()
