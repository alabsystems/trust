#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Exercise analyzer version freshness through real Cargo rebuilds and Git refs.

Run under build-slot with a genuine TARGO on PATH or in the environment.
The small dependency-free package uses the actual analyzer build script.
"""
from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BUILD_SCRIPT = ROOT / "src/tools/rust-analyzer/crates/rust-analyzer/build.rs"


class AnalyzerVersionWorktreeTest(unittest.TestCase):
    def test_versions_follow_linked_packed_detached_and_regular_heads(self):
        targo = os.environ.get("TARGO") or shutil.which("targo")
        self.assertIsNotNone(targo, "genuine Targo is required")
        version = subprocess.run([targo, "--unverified", "--version"],
                                 text=True, capture_output=True, check=True)
        self.assertTrue(version.stdout.startswith("targo "), version.stdout)
        with tempfile.TemporaryDirectory(prefix="trust analyzer version ") as directory:
            base = Path(directory)
            repo = base / "repo"
            repo.mkdir()
            (repo / "src").mkdir()
            (repo / "Cargo.toml").write_text(
                '[package]\nname="analyzer-head-probe"\nversion="0.0.0"\nedition="2024"\n')
            (repo / "build.rs").write_bytes(BUILD_SCRIPT.read_bytes())
            (repo / "src/main.rs").write_text(
                'fn main() { println!("{}", option_env!("RA_COMMIT_HASH").unwrap_or("missing")); }\n')
            note = repo / "identity.txt"
            note.write_text("initial source identity\n")
            env = dict(os.environ, GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
                       GIT_OPTIONAL_LOCKS="0", CARGO_TARGET_DIR=str(base / "target"),
                       CFG_RELEASE="1.101.0-dev", CFG_VER_HASH="unchanged-bootstrap-input")

            def run(cwd, *command):
                result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                self.assertEqual(result.returncode, 0, result.stdout)
                return result.stdout.strip()

            def git(cwd, *command):
                return run(cwd, "git", "-c", "user.name=Trust version regression",
                           "-c", "user.email=trust-version-regression@example.invalid", *command)

            def advance(cwd, label):
                (cwd / "identity.txt").write_text(label + "\n")
                git(cwd, "add", "identity.txt")
                git(cwd, "commit", "-m", label)

            def assert_current(cwd):
                expected = git(cwd, "rev-parse", "HEAD")
                run(cwd, targo, "--unverified", "build", "--offline", "--locked")
                binary = base / "target/debug/analyzer-head-probe"
                if os.name == "nt":
                    binary = binary.with_suffix(".exe")
                self.assertEqual(run(cwd, str(binary)), expected)

            git(repo, "init", "--initial-branch=main")
            run(repo, targo, "generate-lockfile", "--offline")
            git(repo, "add", "Cargo.toml", "Cargo.lock", "build.rs", "src/main.rs", "identity.txt")
            git(repo, "commit", "-m", "Initial source")
            linked = base / "linked"
            git(repo, "worktree", "add", "-b", "version-regression", str(linked))
            assert_current(linked)
            advance(linked, "advance symbolic linked head")
            assert_current(linked)
            git(linked, "pack-refs", "--all", "--prune")
            assert_current(linked)
            advance(linked, "advance formerly packed head")
            assert_current(linked)
            git(linked, "checkout", "--detach")
            assert_current(linked)
            advance(linked, "advance detached head")
            assert_current(linked)
            assert_current(repo)
            advance(repo, "advance regular head")
            assert_current(repo)


if __name__ == "__main__":
    unittest.main()
