#!/usr/bin/env python3
"""Check actual Cargo feature resolution for production and oracle callers."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.lib import land_select
from scripts.lib.test_python import fixture_shebang


# atpkg's targo refuses a target directory it reads from `.cargo/config.toml`
# (`target-dir = "crates/target"`): "build cache ownership refused: explicit
# build target is unmanaged or unsupported", exit 75, no unit graph. It accepts
# the same directory named as CARGO_TARGET_DIR, which is how the land gate's
# crates legs (land_gate.crates_target_dir, by its real path) and
# scripts/regen-trustir-oleans.sh name it. A caller's own target keeps its
# precedence.
TARGET_DIR_VARIABLES = ("CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR", "TARGO_TARGET_DIR")


def targo_environment(environ):
    env = dict(environ)
    if not any(env.get(name) for name in TARGET_DIR_VARIABLES):
        env["CARGO_TARGET_DIR"] = os.path.realpath(ROOT / "crates" / "target")
    return env


def unit_graph(targo, mode, *options, environ=None):
    # Unit graphs use Cargo's real default-member and resolver decisions,
    # without compiling or executing any Rust target. Metadata's workspace
    # graph alone cannot distinguish dev-only activation from a normal edge.
    return subprocess.run(
        [targo, "--unverified", mode, "--offline", "--locked",
         "--unit-graph", "-Zunstable-options", *options],
        cwd=ROOT, env=targo_environment(os.environ if environ is None else environ),
        capture_output=True, text=True, timeout=120,
    )


class MirTestOracleFeatureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.targo = os.environ.get("TARGO") or shutil.which("targo")
        if not cls.targo:
            raise AssertionError("the native Trust toolchain is required")
        probe = subprocess.run(
            [cls.targo, "--unverified", "--version"],
            cwd=ROOT, env=targo_environment(os.environ),
            capture_output=True, text=True, timeout=120,
        )
        if probe.returncode or "targo" not in probe.stdout.lower():
            raise AssertionError(f"not a genuine Targo: {probe.stdout}\n{probe.stderr}")

    def router_units(self, mode, *options):
        result = unit_graph(self.targo, mode, *options)
        self.assertEqual(result.returncode, 0, result.stderr)
        graph = json.loads(result.stdout)
        units = [unit for unit in graph["units"]
                 if unit["target"]["name"] == "trust_router"]
        self.assertTrue(units, "the real graph must include trust-router")
        return units

    def test_normal_default_members_do_not_enable_mir_oracle(self):
        units = self.router_units("build")
        self.assertTrue(
            all("mir-test-oracle" not in unit["features"] for unit in units),
            [(unit["mode"], unit["features"]) for unit in units],
        )

    def test_comparison_tests_enable_the_mir_oracle(self):
        units = self.router_units(
            "test", "--manifest-path", "crates/trust-integration-tests/Cargo.toml",
        )
        self.assertTrue(
            any("mir-test-oracle" in unit["features"] for unit in units),
            [(unit["mode"], unit["features"]) for unit in units],
        )

    def test_manifest_changes_schedule_guard_without_reclassifying_inputs(self):
        for path in (
            "Cargo.toml",
            "crates/trust-router/Cargo.toml",
            "crates/trust-integration-tests/Cargo.toml",
            "benchmarks/verify_overhead/Cargo.toml",
            "crates/future-consumer/Cargo.toml",
            "Crates/FutureConsumer/CARGO.TOML",
        ):
            with self.subTest(path=path):
                self.assertIn(
                    "scripts.tests.mir_test_oracle_feature_test",
                    land_select.validation_test_modules([path]),
                )
                self.assertIsNotNone(land_select.everything_reason(path))


class UnitGraphTargetTests(unittest.TestCase):
    """The probe names its target in the environment, never only in config.

    A fake targo records the target variables it is handed (and nothing else
    of the environment) and answers a one-unit graph."""

    def fake_targo(self):
        tmp = tempfile.TemporaryDirectory(prefix="mir-oracle-target.")
        self.addCleanup(tmp.cleanup)
        record = Path(tmp.name) / "record.json"
        fake = Path(tmp.name) / "targo"
        # fixture_shebang: an interpreter path with a space in it (atpkg's on
        # macOS) is no shebang the kernel can run, and the exec is then ENOENT.
        fake.write_text(
            fixture_shebang()
            + "import json, os\n"
            f"names = {TARGET_DIR_VARIABLES!r}\n"
            f"with open({str(record)!r}, 'w') as out:\n"
            "    json.dump({name: os.environ.get(name) for name in names}, out)\n"
            "print(json.dumps({'units': [{'target': {'name': 'trust_router'},"
            " 'mode': 'build', 'features': []}]}))\n"
        )
        fake.chmod(0o755)
        return fake, record

    def handed(self, environ):
        fake, record = self.fake_targo()
        result = unit_graph(str(fake), "build", environ=environ)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(record.read_text())

    def test_a_caller_naming_no_target_hands_the_configured_one_by_its_real_path(self):
        handed = self.handed({"PATH": os.environ.get("PATH", "")})
        self.assertEqual(handed["CARGO_TARGET_DIR"], os.path.realpath(ROOT / "crates" / "target"))
        self.assertIsNone(handed["CARGO_BUILD_TARGET_DIR"])
        self.assertIsNone(handed["TARGO_TARGET_DIR"])

    def test_an_interpreter_path_with_spaces_executes_the_real_probe(self):
        with tempfile.TemporaryDirectory(prefix="mir-oracle-interpreter.") as directory:
            runtime = Path(directory) / "Python Runtime"
            runtime.mkdir()
            executable = runtime / "python3"
            executable.symlink_to(sys.executable)
            with mock.patch.object(sys, "executable", str(executable)):
                handed = self.handed({"PATH": os.environ.get("PATH", "")})
        self.assertEqual(handed["CARGO_TARGET_DIR"], os.path.realpath(ROOT / "crates" / "target"))

    def test_a_caller_target_keeps_its_precedence(self):
        for name in TARGET_DIR_VARIABLES:
            with self.subTest(name=name):
                handed = self.handed({"PATH": os.environ.get("PATH", ""), name: "/caller/target"})
                self.assertEqual(handed[name], "/caller/target")
                for other in TARGET_DIR_VARIABLES:
                    if other != name:
                        self.assertIsNone(handed[other])


if __name__ == "__main__":
    unittest.main()
