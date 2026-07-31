#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0 OR MIT

"""Fail-closed regression tests for the two-language battery runner."""

from __future__ import annotations

import importlib.util
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock


RUNNER_PATH = Path(__file__).with_name("run.py")
SPEC = importlib.util.spec_from_file_location("two_language_battery_run", RUNNER_PATH)
assert SPEC is not None and SPEC.loader is not None
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


def sealed_stamp() -> dict:
    return {
        "rustc_vV_exit_code": 0,
        "toolchain_binary": "trustc",
        "trust_brand_present": True,
        "trustc_sha256": "a" * 64,
        "tippy_version_exit_code": 0,
        "tippy_driver_sha256": "b" * 64,
        "toolchain_matches_head": True,
        "repo_clean": True,
        "submodules_clean": True,
    }


class BatteryRunnerTests(unittest.TestCase):
    def test_current_canonical_inventory_is_exact(self) -> None:
        files = runner.discover(None)
        captured = runner.capture_fixture_inventory(files, canonical=True)
        self.assertEqual(len(captured), 25)
        self.assertEqual(len(runner.fixture_snapshot(captured)), 64)

    def test_deleted_fixture_cannot_shrink_canonical_inventory(self) -> None:
        files = runner.discover(None)
        with self.assertRaisesRegex(RuntimeError, "reviewed 25-fixture manifest"):
            runner.capture_fixture_inventory(files[:-1], canonical=True)

    def test_duplicate_required_directive_is_rejected(self) -> None:
        text = """\
//@ battery-lane: A-rust
//@ battery-lane: B-lean
//@ battery-expect: pass
//@ battery-flags: --crate-type=lib
"""
        with self.assertRaisesRegex(RuntimeError, "exactly one battery-lane"):
            runner.validate_fixture_directives(Path("duplicate.rs"), text)

    def test_fixture_snapshot_changes_with_exact_bytes(self) -> None:
        path = runner.discover(None)[0]
        original = {path: path.read_bytes()}
        changed = {path: original[path] + b"\n"}
        self.assertNotEqual(
            runner.fixture_snapshot(original),
            runner.fixture_snapshot(changed),
        )

    def test_relative_explicit_trustc_and_tippy_share_one_stage2(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            bindir = root / "stage2" / "bin"
            bindir.mkdir(parents=True)
            trustc = bindir / "trustc"
            tippy = bindir / "tippy-driver"
            trustc.write_text("#!/bin/sh\n", encoding="utf-8")
            tippy.write_text("#!/bin/sh\n", encoding="utf-8")
            trustc.chmod(0o755)
            tippy.chmod(0o755)

            runner._trustc_path.cache_clear()
            try:
                with (
                    mock.patch.object(runner, "REPO_ROOT", root),
                    mock.patch.dict(
                        os.environ,
                        {"TRUST_PROBE_TRUSTC": "stage2/bin/trustc"},
                    ),
                ):
                    self.assertEqual(runner._trustc_path(), trustc.resolve())
                    self.assertEqual(runner._tippy_path(), tippy.resolve())
            finally:
                runner._trustc_path.cache_clear()

    def test_nonzero_or_unbranded_toolchain_never_seals(self) -> None:
        for field, value in (
            ("rustc_vV_exit_code", 1),
            ("toolchain_binary", "rustc"),
            ("trust_brand_present", False),
            ("tippy_version_exit_code", 134),
            ("repo_clean", False),
            ("submodules_clean", False),
        ):
            with self.subTest(field=field):
                stamp = sealed_stamp()
                stamp[field] = value
                self.assertFalse(runner.is_toolchain_sealed(stamp))
        self.assertTrue(runner.is_toolchain_sealed(sealed_stamp()))

    def test_every_submodule_drift_prefix_is_rejected(self) -> None:
        for prefix in ("+", "-", "U"):
            with self.subTest(prefix=prefix):
                line = f"{prefix}{'a' * 40} first-party/example"
                self.assertEqual(runner.submodule_drift_lines(line), [line])
        clean = f" {'a' * 40} first-party/example"
        self.assertEqual(runner.submodule_drift_lines(clean), [])

    def test_postflight_identity_detects_binary_and_checkout_drift(self) -> None:
        before = {
            "rustc_vV_exit_code": 0,
            "rustc_vV": "version",
            "trustc_sha256": "a",
            "toolchain_commit": "head",
            "toolchain_binary": "trustc",
            "trust_brand_present": True,
            "tippy_version_exit_code": 0,
            "tippy_version": "version",
            "tippy_driver_sha256": "b",
            "repo_head": "head",
            "repo_clean": True,
            "submodules_clean": True,
            "toolchain_matches_head": True,
            "toolchain_sealed": True,
        }
        self.assertTrue(runner.same_measurement_identity(before, dict(before)))
        for field in ("trustc_sha256", "tippy_driver_sha256", "repo_head"):
            with self.subTest(field=field):
                after = dict(before)
                after[field] = "changed"
                self.assertFalse(runner.same_measurement_identity(before, after))

    def test_tippy_nonzero_cannot_impersonate_known_target_verdict(self) -> None:
        source = runner.BATTERY_DIR / "lane-d-legacy" / "d1_kani_contracts.rs"
        with tempfile.TemporaryDirectory() as td:
            snapshot = Path(td) / source.name
            snapshot.write_bytes(source.read_bytes())
            process = subprocess.CompletedProcess(
                ["fake-tippy"],
                1,
                stdout="legacy spec_sugar clean {",
                stderr="driver crashed",
            )
            with (
                mock.patch.object(runner, "_tippy_cmd", return_value=["fake-tippy"]),
                mock.patch.object(runner.subprocess, "run", return_value=process),
            ):
                result = runner.run_one(source, 1, snapshot)
        self.assertEqual(result["verdict"], "tippy-compile-failed")
        self.assertFalse(result["battery_ok"])

    def test_symlink_alias_resolves_to_canonical_output(self) -> None:
        canonical = (runner.BATTERY_DIR / "results.json").resolve()
        with tempfile.TemporaryDirectory() as td:
            alias = Path(td) / "alias.json"
            alias.symlink_to(canonical)
            self.assertEqual(alias.resolve(), canonical)
            with self.assertRaisesRegex(ValueError, "--filter requires"):
                runner.validate_output_policy(
                    "lane-c",
                    alias.resolve(),
                    canonical,
                    explicit_trustc=True,
                )

    def test_atomic_write_failure_preserves_existing_scorecard(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            output = Path(td) / "results.json"
            output.write_text("old scorecard\n", encoding="utf-8")
            with (
                mock.patch.object(
                    runner.json,
                    "dump",
                    side_effect=RuntimeError("serialization failed"),
                ),
                self.assertRaisesRegex(RuntimeError, "serialization failed"),
            ):
                runner.write_scorecard_atomic(output, {"new": True})
            self.assertEqual(output.read_text(encoding="utf-8"), "old scorecard\n")
            self.assertEqual(list(Path(td).iterdir()), [output])


if __name__ == "__main__":
    unittest.main()
