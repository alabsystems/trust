#!/usr/bin/env python3
"""Exercise reproducibility reporting with an inert x.py fixture, never a compiler."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import shlex
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "repro_wholestage2_selfcompare.sh"
HOST = "aarch64-apple-darwin"
FIXTURE = r'''
import json
import os
from pathlib import Path
import sys

assert sys.argv[1:] == ["build", "--stage", "2"]
calls_path = Path("fixture-calls.json")
calls = json.loads(calls_path.read_text()) if calls_path.exists() else []
mode = os.environ["TRUST_REPRO_FIXTURE_MODES"].split(",")[len(calls)]
calls.append({"argv": sys.argv[1:], "mode": mode})
calls_path.write_text(json.dumps(calls))
if mode == "failed":
    print("inert build fixture failed", flush=True)
    sys.exit(23)

host = os.environ["TRUST_HOST_TRIPLE"]
stage = Path("build") / host / "stage2"
release = Path("build") / host / "stage2-rustc" / host / "release"
library = stage / "lib/rustlib" / host / "lib"
artifacts = {
    stage / "bin/trustc": b"inert launcher fixture",
    stage / "lib/librustc_driver-aaaaaaaaaaaaaaaa.dylib": b"inert driver fixture",
    library / "libstd-aaaaaaaaaaaaaaaa.rlib": b"inert std fixture",
    library / "libcore-aaaaaaaaaaaaaaaa.rlib": b"inert core fixture",
    library / "libcompiler_builtins-aaaaaaaaaaaaaaaa.rlib": b"inert intrinsics fixture",
    release / "librustc_codegen_trust_cg.dylib": b"inert legacy backend fixture",
}
if mode in ("different", "missing-then-different", "different-then-missing"):
    artifacts[stage / "lib/librustc_driver-aaaaaaaaaaaaaaaa.dylib"] += b" different"
if mode == "missing":
    del artifacts[library / "libstd-aaaaaaaaaaaaaaaa.rlib"]
if mode == "missing-then-different":
    del artifacts[stage / "bin/trustc"]
if mode == "different-then-missing":
    del artifacts[release / "librustc_codegen_trust_cg.dylib"]
for path, content in artifacts.items():
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content)

if mode == "driver-impl":
    print("   Compiling rustc_driver_impl v0.0.0 (inert fixture)")
elif mode == "unrelated":
    print("   Compiling rustc_driver_helper v0.0.0 (inert fixture)")
elif mode != "assembly-only":
    print("   Compiling rustc_driver v0.0.0 (inert fixture)")
print("Assembling stage2 compiler (inert fixture, no compilation)")
'''


class WholeStage2SelfcompareTests(unittest.TestCase):
    def run_fixture(self, *modes, tool_fault=None):
        temporary = tempfile.TemporaryDirectory(prefix="trust repro fixture ")
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name).resolve()
        script = root / "scripts" / SCRIPT.name
        script.parent.mkdir()
        shutil.copyfile(SCRIPT, script)
        (root / "x.py").write_text(FIXTURE)
        bindir = root / "fixture-bin"
        bindir.mkdir()
        (bindir / "python3").symlink_to(Path(sys.executable).resolve())
        faults = {
            "copy-fails": ("cp", "exit 23\n"),
            "second-copy-fails": (
                "cp",
                'case "$2" in *B-trustc-*) exit 23 ;; esac\n'
                + "exec " + shlex.quote(shutil.which("cp")) + ' "$@"\n',
            ),
            "digest-fails": ("shasum", "exit 23\n"),
            "digest-empty": ("shasum", "exit 0\n"),
            "size-fails": ("stat", "exit 23\n"),
        }
        if tool_fault is not None:
            name, body = faults[tool_fault]
            tool = bindir / name
            tool.write_text("#!/bin/sh\n" + body)
            tool.chmod(0o755)
        home = root / "home"
        home.mkdir()
        env = dict(os.environ)
        env.update(
            HOME=str(home),
            PATH=str(bindir) + os.pathsep + env.get("PATH", os.defpath),
            TRUST_HOST_TRIPLE=HOST,
            TRUST_BUILD_TIMEOUT="4",
            TRUST_REPRO_FIXTURE_MODES=",".join(modes),
            PYTHONDONTWRITEBYTECODE="1",
        )
        result = subprocess.run(
            ["/bin/bash", str(script), "--keep", "--log", "reports/fixture"],
            cwd=root, env=env, text=True, capture_output=True, timeout=30,
        )
        calls = json.loads((root / "fixture-calls.json").read_text())
        return result, calls

    def assert_exit(self, result, expected):
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)

    def test_matching_fresh_driver_builds_keep_all_six_artifacts(self):
        result, calls = self.run_fixture("fresh", "fresh")
        self.assert_exit(result, 0)
        self.assertEqual(len(calls), 2)
        self.assertEqual(result.stdout.count("RESULT : MATCH"), 6)
        self.assertNotIn("integer expression expected", result.stderr)

    def test_driver_impl_compilation_is_accepted(self):
        result, calls = self.run_fixture("driver-impl", "driver-impl")
        self.assert_exit(result, 0)
        self.assertEqual(len(calls), 2)

    def test_assembly_only_first_build_refuses_before_comparison(self):
        result, calls = self.run_fixture("assembly-only", "fresh")
        self.assert_exit(result, 2)
        self.assertEqual(len(calls), 1)
        self.assertIn("NON-INDEPENDENT", result.stdout)
        self.assertNotIn("RESULT : MATCH", result.stdout)

    def test_assembly_only_second_build_refuses_before_comparison(self):
        result, calls = self.run_fixture("fresh", "assembly-only")
        self.assert_exit(result, 2)
        self.assertEqual(len(calls), 2)
        self.assertIn("NON-INDEPENDENT", result.stdout)
        self.assertNotIn("RESULT : MATCH", result.stdout)

    def test_unrelated_driver_prefix_is_not_compilation_evidence(self):
        result, calls = self.run_fixture("unrelated", "fresh")
        self.assert_exit(result, 2)
        self.assertEqual(len(calls), 1)

    def test_real_byte_difference_remains_a_difference(self):
        result, calls = self.run_fixture("fresh", "different")
        self.assert_exit(result, 1)
        self.assertEqual(len(calls), 2)
        self.assertIn("RESULT : DIFFER", result.stdout)

    def test_missing_artifact_still_refuses(self):
        result, calls = self.run_fixture("missing", "missing")
        self.assert_exit(result, 2)
        self.assertEqual(len(calls), 2)
        self.assertIn("RESULT : UNMEASURED", result.stdout)

    def test_missing_artifact_takes_precedence_over_byte_differences(self):
        for mode in ("missing-then-different", "different-then-missing"):
            for modes in (("fresh", mode), (mode, "fresh")):
                with self.subTest(modes=modes):
                    result, calls = self.run_fixture(*modes)
                    self.assert_exit(result, 2)
                    self.assertEqual(len(calls), 2)
                    self.assertIn("RESULT : UNMEASURED", result.stdout)
                    self.assertIn("RESULT : DIFFER", result.stdout)
                    self.assertEqual(sum(line.startswith("### ") for line in result.stdout.splitlines()), 6)

    def test_failed_build_still_refuses(self):
        result, calls = self.run_fixture("failed", "fresh")
        self.assert_exit(result, 2)
        self.assertEqual(len(calls), 1)
        self.assertIn("BUILD A FAILED rc=23", result.stdout)

    def assert_capture_refusal(self, fault, build, calls_count):
        result, calls = self.run_fixture("fresh", "fresh", tool_fault=fault)
        self.assert_exit(result, 2)
        self.assertEqual(len(calls), calls_count)
        self.assertIn("CAPTURE " + build + " FAILED", result.stdout)
        self.assertNotIn("RESULT : MATCH", result.stdout)

    def test_failed_first_copy_refuses_before_comparison(self):
        self.assert_capture_refusal("copy-fails", "A", 1)

    def test_failed_second_copy_refuses_before_comparison(self):
        self.assert_capture_refusal("second-copy-fails", "B", 2)

    def test_failed_digest_refuses_before_comparison(self):
        self.assert_capture_refusal("digest-fails", "A", 1)

    def test_empty_digest_refuses_before_comparison(self):
        self.assert_capture_refusal("digest-empty", "A", 1)

    def test_failed_size_measurement_refuses_before_comparison(self):
        self.assert_capture_refusal("size-fails", "A", 1)


if __name__ == "__main__":
    unittest.main()
