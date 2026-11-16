#!/usr/bin/env python3
"""Exercise stage2 path selection through the real upstream preflight script."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "check_upstream_rust_test_toolchain.sh"
TOOLS = (
    "targo", "trustc", "targo-trust", "trustd", "trustdoc", "trustfmt",
    "targo-fmt", "tippy", "targo-tippy", "tippy-driver", "trust-analyzer",
)
VERSION_TOOL = """import json
import os
from pathlib import Path
import sys

invoked = Path(sys.argv[0])
with open(os.environ['TRUST_FIXTURE_TOOL_LOG'], 'a') as log:
    log.write(json.dumps({'tool': invoked.name, 'path': str(invoked), 'args': sys.argv[1:]}) + '\\n')
# Model the canonical-directory prerequisite of authenticated targo dispatch.
# Other tools can report a version through the host alias, as the real tools do.
if invoked.name == 'targo' and invoked != invoked.resolve():
    raise SystemExit('noncanonical targo directory')
if invoked.name == 'targo' and sys.argv[1:] == ['--unverified', '--version'] and os.environ.get('TRUST_FIXTURE_STALE_TARGO') == '1':
    raise SystemExit('error: unexpected argument --unverified')
if invoked.name == 'targo' and sys.argv[1:] == ['trust', 'domination', 'upstream-tests', '--help']:
    print('trust-upstream-compat port')
else:
    print('binary: ' + invoked.name)
    print('commit-hash: ' + os.environ['TRUST_FIXTURE_COMMIT'])
    print('host: ' + os.environ.get('TRUST_FIXTURE_HOST', 'fixture-host'))
"""


class Stage2PathControls(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-stage2-path-")
        self.addCleanup(self.temporary.cleanup)
        self.scratch = Path(self.temporary.name).resolve()
        self.repo = self.scratch / "repo with spaces"
        (self.repo / "scripts").mkdir(parents=True)
        shutil.copy2(SCRIPT, self.repo / "scripts" / SCRIPT.name)
        (self.repo / ".gitignore").write_text("build/\n", encoding="utf-8")
        (self.repo / "source.rs").write_text("pub fn value() {}\n", encoding="utf-8")
        self.git("init", "-q")
        self.git("config", "user.name", "Stage2 fixture")
        self.git("config", "user.email", "stage2-fixture@example.invalid")
        self.git("add", ".")
        self.git("commit", "-qm", "initial compiler source")
        self.commit = self.git("rev-parse", "HEAD")
        self.sysroot = self.repo / "build" / "fixture-host" / "stage2"
        self.install_tools(self.sysroot)
        (self.repo / "build" / "host").symlink_to("fixture-host", target_is_directory=True)
        self.alias = self.repo / "build" / "host" / "stage2"
        self.tool_log = self.scratch / "tools.jsonl"

    def git(self, *args: str) -> str:
        return subprocess.run(
            ["git", "-C", str(self.repo), *args], check=True,
            capture_output=True, text=True,
        ).stdout.strip()

    def install_tools(self, sysroot: Path) -> None:
        (sysroot / "bin").mkdir(parents=True)
        library = sysroot / "lib" / "rustlib" / "fixture-host" / "lib"
        library.mkdir(parents=True)
        (library / "libstd-fixture.rlib").write_bytes(b"fixture")
        for name in TOOLS:
            tool = sysroot / "bin" / name
            # A `#!{sys.executable}` shebang cannot carry an interpreter path with spaces
            # (atpkg's python lives under `Application Support/`): exec splits it and the
            # tool never runs, which the checker then reports as `does not run -Vv` rather
            # than as the fixture defect it is. The sh/python polyglot keeps argv[0] as this
            # file (the canonical-directory modeling below reads it) under any interpreter path.
            tool.write_text(
                f'#!/bin/sh\n""":"\nexec "{sys.executable}" "$0" "$@"\n":"""\n{VERSION_TOOL}',
                encoding="utf-8")
            tool.chmod(0o755)

    def run_preflight(self, *args: str, selected: Path | None = None,
                      stale_targo: bool = False):
        environment = dict(os.environ)
        environment.pop("TRUST_STAGE2_SYSROOT", None)
        environment.pop("TRUST_UPSTREAM_TEST_ALLOW_REBUILD", None)
        environment["TRUST_FIXTURE_COMMIT"] = self.commit
        environment["TRUST_FIXTURE_TOOL_LOG"] = str(self.tool_log)
        if stale_targo:
            environment["TRUST_FIXTURE_STALE_TARGO"] = "1"
        if selected is not None:
            environment["TRUST_STAGE2_SYSROOT"] = str(selected)
        return subprocess.run(
            ["bash", str(self.repo / "scripts" / SCRIPT.name), *args],
            cwd=self.repo, env=environment, capture_output=True, text=True,
        )

    def assert_canonical_success(self, result) -> None:
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"sysroot: {self.sysroot}\n", result.stdout)
        self.assertIn("toolchain_checkout_match: true", result.stdout)
        calls = [json.loads(line) for line in self.tool_log.read_text().splitlines()]
        self.assertTrue(calls)
        self.assertTrue(all(Path(row["path"]).parent == self.sysroot / "bin" for row in calls))
        self.assertTrue(any(row["tool"] == "targo" and row["args"] == ["tippy", "-V"]
                            for row in calls))

    def test_default_host_alias_is_canonicalized_before_tool_dispatch(self) -> None:
        self.assert_canonical_success(self.run_preflight())

    def test_explicit_host_alias_is_canonicalized(self) -> None:
        self.assert_canonical_success(self.run_preflight(selected=self.alias))

    def test_physical_stage2_path_still_passes(self) -> None:
        self.assert_canonical_success(self.run_preflight(selected=self.sysroot))

    def test_stage2_info_binds_validated_physical_compiler(self) -> None:
        info_path = self.scratch / "stage2-info.json"
        result = self.run_preflight("--stage2-info-out", str(info_path), selected=self.alias)
        self.assert_canonical_success(result)
        info = json.loads(info_path.read_text(encoding="utf-8"))
        self.assertEqual(info, {
            "schema_version": "trust.stage2-preflight.v1",
            "sysroot": str(self.sysroot),
            "trustc": str(self.sysroot / "bin" / "trustc"),
            "host_triple": "fixture-host",
            "trustc_commit": self.commit,
            "toolchain_checkout_match": True,
        })

    def test_stage2_info_refuses_rebuild_opt_in(self) -> None:
        info_path = self.scratch / "stage2-info.json"
        result = self.run_preflight("--allow-rebuild", "--stage2-info-out", str(info_path))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("--stage2-info-out cannot use --allow-rebuild", result.stderr)
        self.assertFalse(info_path.exists())

    def test_external_symlink_escape_is_refused_before_executing_tools(self) -> None:
        external = self.scratch / "outside" / "stage2"
        self.install_tools(external)
        escape = self.repo / "build" / "escape" / "stage2"
        escape.parent.mkdir()
        escape.symlink_to(external, target_is_directory=True)
        for args in ((), ("--allow-rebuild", "--", "./x.py", "test")):
            with self.subTest(args=args):
                result = self.run_preflight(*args, selected=escape)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("stage2 sysroot must be repo-local", result.stderr)
                self.assertFalse(self.tool_log.exists(), "escaped tool executed before refusal")

    def test_repo_local_alias_to_wrong_stage_is_refused(self) -> None:
        wrong_stage = self.repo / "build" / "other-host" / "stage1"
        self.install_tools(wrong_stage)
        alias = wrong_stage.parent / "stage2"
        alias.symlink_to("stage1", target_is_directory=True)
        result = self.run_preflight(selected=alias)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("stage2 sysroot must be repo-local", result.stderr)
        self.assertFalse(self.tool_log.exists())

    def test_canonicalization_does_not_admit_stale_compiler_revision(self) -> None:
        (self.repo / "source.rs").write_text("pub fn changed() {}\n", encoding="utf-8")
        self.git("add", "source.rs")
        self.git("commit", "-qm", "compiler source changed after stage2")
        info_path = self.scratch / "stale-stage2-info.json"
        result = self.run_preflight("--stage2-info-out", str(info_path), selected=self.alias)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("does not match checkout", result.stderr)
        self.assertIn("non-evidence file changed after stage2 build: source.rs", result.stderr)
        self.assertNotIn("targo tippy dispatch does not run", result.stderr)
        self.assertFalse(info_path.exists())

    def test_stale_cargo_under_targo_name_is_refused(self) -> None:
        result = self.run_preflight(stale_targo=True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("targo rejects --unverified", result.stderr)

    def test_explicit_target_needs_its_own_libstd(self) -> None:
        result = self.run_preflight("--target-triple", "x86_64-unknown-linux-gnu")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("stage2 target rustlib is missing", result.stderr)
        self.assertNotIn("OK: upstream Rust", result.stdout)

    def test_summary_mode_refuses_rebuild_opt_in(self) -> None:
        result = self.run_preflight("--allow-rebuild", "--target-triple", "fixture-host",
                                    "--compat-summary", "summary.json")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("--compat-summary cannot use --allow-rebuild", result.stderr)
        self.assertFalse(self.tool_log.exists())

    def test_summary_mode_refuses_cross_target_host(self) -> None:
        result = self.run_preflight("--target-triple", "x86_64-unknown-linux-gnu",
                                    "--compat-summary", "summary.json")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("native stage2 host and target to match", result.stderr)


if __name__ == "__main__":
    unittest.main()
