#!/usr/bin/env python3
"""Synthetic consistency fixtures; none represents a real upstream suite run."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "validate_upstream_rust_compat_summary.py"
PREFLIGHT = SCRIPT.with_name("check_upstream_rust_test_toolchain.sh")
COLLECTOR = SCRIPT.with_name("collect_strict_superiority_artifacts.sh")


# A `#!{sys.executable}` shebang cannot carry an interpreter path with spaces (atpkg's python
# lives under `Application Support/`): exec splits it and the fake never runs. This sh/python
# polyglot execs the interpreter quoted and keeps argv[0] as the fake's own path.
PYTHON_SHEBANG = f'#!/bin/sh\n""":"\nexec "{sys.executable}" "$0" "$@"\n":"""\n'


class SummaryValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="trust-upstream-summary-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name, "repo with spaces")
        (self.root / "tests/ui").mkdir(parents=True)
        (self.root / "tests/ui/hello.rs").write_text("fn main() {}\n", encoding="utf-8")
        (self.root / "tests/run-make/example").mkdir(parents=True)
        (self.root / "tests/run-make/example/rmake.rs").write_text(
            "fn main() {}\n", encoding="utf-8")
        (self.root / ".gitignore").write_text("build/\nreports/\n", encoding="utf-8")
        self.git("init", "-q")
        self.git("config", "user.name", "Summary fixture")
        self.git("config", "user.email", "summary@example.invalid")
        self.git("add", ".")
        self.git("commit", "-qm", "pinned upstream fixture")
        self.pin = self.git("rev-parse", "HEAD")
        self.blob = self.git("rev-parse", f"{self.pin}:tests/ui/hello.rs")
        self.runmake_blob = self.git("rev-parse", f"{self.pin}:tests/run-make/example/rmake.rs")
        (self.root / "tests/upstream-rust").mkdir()
        (self.root / "release").mkdir()
        (self.root / "tests/upstream-rust/baseline.toml").write_text(
            'schema_version = "0.1.0"\nid = "fixture-baseline"\n'
            f'[upstream]\nrevision = "rust-lang/rust:{self.pin}"\n'
            '[[entries]]\nid = "toolchain.rustc"\n'
            '[[entries]]\nid = "toolchain.rustdoc"\n', encoding="utf-8")
        (self.root / "release/trust-version.toml").write_text(
            f'[rust_alignment]\nrevision = "rust-lang/rust:{self.pin}"\n', encoding="utf-8")
        (self.root / "scripts").mkdir()
        shutil.copy2(SCRIPT, self.root / "scripts" / SCRIPT.name)
        shutil.copy2(PREFLIGHT, self.root / "scripts" / PREFLIGHT.name)
        self.git("add", ".")
        self.git("commit", "-qm", "fixture baseline")
        self.head = self.git("rev-parse", "HEAD")
        bootstrap = self.root / "build/bootstrap/debug/bootstrap"
        bootstrap.parent.mkdir(parents=True)
        bootstrap.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        bootstrap.chmod(0o755)
        self.write_run("aarch64-apple-darwin", "aarch64-apple-darwin")

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), *args], check=True,
                              capture_output=True, text=True).stdout.strip()

    @staticmethod
    def write_json(path: Path, value: dict) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    def write_run(self, target: str, host: str) -> None:
        arch = target.split("-", 1)[0]
        host_arch = host.split("-", 1)[0]
        self.out_dir = self.root / "reports" / arch / "porting"
        self.proof = self.out_dir / "proof"
        self.summary_path = self.root / "reports" / arch / "compat-summary.json"
        self.out_dir.mkdir(parents=True, exist_ok=True)
        self.proof.mkdir(parents=True, exist_ok=True)
        run_id = f"synthetic-{arch}"
        command = shlex.join([
            str(self.root / "build/bootstrap/debug/bootstrap"), "test", "--src", str(self.root),
            "--stage", "2", "--trust-vanilla", "--no-fail-fast", "--host", host,
            "--target", target, "--set", "rust.verbose-tests=true", "--force-rerun",
        ])
        log = f"$ {command}\n# executor=rust-bootstrap\n# upstream_exit_status=0\n# exit_status=0\n"
        (self.out_dir / "execution.log").write_text(log, encoding="utf-8")
        case = {"upstream_revision": self.pin, "local_revision": self.head,
                "aggregate_exit_status": 0, "proof_scope": "upstream_rust",
                "aggregate_exit_supplies_individual_outcomes": False,
                "execution_command": command,
                "log_sha256": hashlib.sha256(log.encode()).hexdigest(),
                "test_input_closure_before": {"files": {}},
                "test_input_closure_after": {"files": {}},
                "test_input_admission": {"unresolved": []},
                "expected": [{"test_id": "upstream.hello", "path": "tests/ui/hello.rs",
                              "names": ["[ui] tests/ui/hello.rs"], "unresolved": []},
                             {"test_id": "upstream.runmake", "path": "tests/run-make/example",
                              "names": ["[run-make] tests/run-make/example"], "unresolved": []}],
                "observations": [{"path": "tests/ui/hello.rs", "name": "[ui] tests/ui/hello.rs",
                                  "outcome": "passed", "complete_suite": True},
                                 {"path": "tests/run-make/example",
                                  "name": "[run-make] tests/run-make/example",
                                  "outcome": "passed", "complete_suite": True}],
                "reconciled": [{"test_id": "upstream.hello", "outcome": "passed"},
                               {"test_id": "upstream.runmake", "outcome": "passed"}]}
        self.write_json(self.proof / "case-evidence.json", case)
        proof_totals = {"total": 2, "upstream": 2, "trust_added": 0, "passed": 2,
                        "upstream_inapplicable": 0, "excepted": 0, "unaccounted": 0}
        self.write_json(self.proof / "inventory.json", {
            "upstream_revision": self.pin, "local_revision": self.head,
            "tests": [{"id": "upstream.hello", "path": "tests/ui/hello.rs",
                       "source": "upstream_rust", "revision": self.pin,
                       "source_git_blob": self.blob},
                      {"id": "upstream.runmake", "path": "tests/run-make/example",
                       "source": "upstream_rust", "revision": self.pin,
                       "source_git_blob": self.runmake_blob}],
        })
        self.write_json(self.proof / "results.json", {
            "results": [{"test_id": "upstream.hello", "outcome": "passed"},
                        {"test_id": "upstream.runmake", "outcome": "passed"}],
        })
        self.write_json(self.proof / "proof-summary.json", proof_totals)
        artifacts = {}
        for name in ("inventory.json", "results.json", "proof-summary.json"):
            path = self.proof / name
            raw = path.read_bytes()
            artifacts[name] = {"path": str(path), "exists": True, "valid": True,
                               "size_bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}
        scorecard = {
            "executed": True, "proof_mode": "full", "proof_scope": "upstream_rust",
            "proof_artifacts_complete": True, "execution_exit_status": 0,
            "resolved_upstream_revision": self.pin, "baseline_revision": self.pin,
            "local_repository_revision": self.head, "upstream_test_files": 2,
            "imported_files": 2, "validation_failures": [], "missing_proof_artifacts": [],
            "invalid_proof_artifacts": [], "primary_upstream_tests": ["tests/run-make/example", "tests/ui/hello.rs"],
            "upstream_revision_drift": {"drifted_from_baseline": False},
            "execution_telemetry": {"executor": "rust-bootstrap", "proof_scope": "upstream_rust",
                                    "exit_status": 0, "upstream_exit_status": 0,
                                    "trust_added_manifest_executed": False,
                                    "trust_added_proof_inventory_tests": 0,
                                    "proof_inventory_tests": 2,
                                    "upstream_proof_inventory_tests": 2},
            "totals": {"failed": 0, "tool_failures": 0, "excepted": 0},
            "proof_artifact_validation": {"complete": True, "missing": [], "invalid": [],
                                          "artifacts": artifacts, "summary_totals": proof_totals},
        }
        self.write_json(self.out_dir / "scorecard.json", scorecard)
        argv = ["targo", "trust", "domination", "upstream-tests", "--release",
                "--proof-scope", "upstream-rust", "--proof-mode", "full", "--execute",
                "--no-apply", "--summary-out", str(self.summary_path), "--out-dir", str(self.out_dir),
                "--run-id", run_id, "--target-arch", arch, "--target", target,
                "--target-triple", target, "--host", host_arch, "--host-triple", host,
                "--upstream-revision", f"rust-lang/rust:{self.pin}",
                "--upstream-remote", "https://github.com/rust-lang/rust.git"]
        contract = {"satisfied": True, "requires_release": True, "requires_execute": True,
                    "requires_summary_out": True, "requires_proof_mode": "full",
                    "release": True, "execute": True, "proof_mode": "full",
                    "proof_scope": "upstream_rust", "target_arch": arch, "target": target,
                    "target_triple": target, "host": host_arch, "host_triple": host,
                    "run_id": run_id, "summary_out": str(self.summary_path), "out_dir": str(self.out_dir)}
        self.summary = {
            "schema_version": "0.1.0", "baseline_id": "fixture-baseline",
            "generated_on": datetime.now(timezone.utc).date().isoformat(), "run_id": run_id,
            "repo_head": self.head, "repo_dirty": False,
            "upstream_revision": f"https://github.com/rust-lang/rust.git:{self.pin}",
            "target_arch": arch, "architecture": arch, "target": target,
            "target_triple": target, "host": host_arch, "host_triple": host,
            "runner": {"python_used": False, "implementation": "rust",
                       "entrypoint": "targo trust domination upstream-tests",
                       "command": "trust-upstream-compat port", "run_id": run_id,
                       "release": True, "execute": True, "proof_mode": "full",
                       "proof_scope": "upstream_rust", "target_arch": arch, "target": target,
                       "target_triple": target, "host": host_arch, "host_triple": host,
                       "summary_out": str(self.summary_path), "out_dir": str(self.out_dir),
                       "argv": argv, "proof_totals": proof_totals,
                       "release_evidence_contract": contract},
            "results": [{"baseline_entry_id": "toolchain.rustc", "outcome": "compatible"},
                        {"baseline_entry_id": "toolchain.rustdoc", "outcome": "compatible"}],
            "totals": {"total": 2, "compatible": 2, "divergent": 0, "excepted": 0,
                       "fixed_upstream": 0, "unknown": 0},
        }
        self.write_json(self.summary_path, self.summary)
        self.target = target
        self.host = host

    def run_validator(self, *, env=None):
        return subprocess.run([sys.executable, str(SCRIPT), "--repo-root", str(self.root),
                               "--summary", str(self.summary_path), "--target-triple", self.target,
                               "--host-triple", self.host], capture_output=True, text=True, env=env)

    def assert_rejected(self, fragment: str) -> None:
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(fragment, result.stderr)

    def one_test_tree(self) -> str:
        def mktree(entries: str) -> str:
            return subprocess.run(
                ["git", "-C", str(self.root), "mktree"], input=entries,
                capture_output=True, text=True, check=True,
            ).stdout.strip()

        ui = mktree(f"100644 blob {self.blob}\thello.rs\n")
        tests = mktree(f"040000 tree {ui}\tui\n")
        return mktree(f"040000 tree {tests}\ttests\n")

    def shrink_retained_population(self) -> None:
        inventory_path = self.proof / "inventory.json"
        inventory = json.loads(inventory_path.read_text())
        inventory["tests"] = inventory["tests"][:1]
        self.write_json(inventory_path, inventory)

        results_path = self.proof / "results.json"
        results = json.loads(results_path.read_text())
        results["results"] = results["results"][:1]
        self.write_json(results_path, results)

        totals_path = self.proof / "proof-summary.json"
        totals = json.loads(totals_path.read_text())
        for key in ("total", "upstream", "passed"):
            totals[key] = 1
        self.write_json(totals_path, totals)

        case_path = self.proof / "case-evidence.json"
        case = json.loads(case_path.read_text())
        for key in ("expected", "observations", "reconciled"):
            case[key] = case[key][:1]
        self.write_json(case_path, case)

        scorecard_path = self.out_dir / "scorecard.json"
        scorecard = json.loads(scorecard_path.read_text())
        scorecard["upstream_test_files"] = 1
        scorecard["imported_files"] = 1
        scorecard["primary_upstream_tests"] = ["tests/ui/hello.rs"]
        telemetry = scorecard["execution_telemetry"]
        telemetry["proof_inventory_tests"] = 1
        telemetry["upstream_proof_inventory_tests"] = 1
        validation = scorecard["proof_artifact_validation"]
        validation["summary_totals"] = totals
        for name in ("inventory.json", "results.json", "proof-summary.json"):
            raw = (self.proof / name).read_bytes()
            validation["artifacts"][name].update(
                size_bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
        self.write_json(scorecard_path, scorecard)
        self.summary["runner"]["proof_totals"] = totals
        self.write_json(self.summary_path, self.summary)

    def add_gitlink(self, *, initialized: bool) -> Path:
        submodule = self.root / "deps/module"
        submodule.mkdir(parents=True)
        pin = self.pin
        if initialized:
            subprocess.run(["git", "-C", str(submodule), "init", "-q"], check=True)
            subprocess.run(["git", "-C", str(submodule), "config", "user.name", "Submodule fixture"],
                           check=True)
            subprocess.run(["git", "-C", str(submodule), "config", "user.email",
                            "submodule@example.invalid"], check=True)
            (submodule / "source.rs").write_text("fn main() {}\n", encoding="utf-8")
            subprocess.run(["git", "-C", str(submodule), "add", "."], check=True)
            subprocess.run(["git", "-C", str(submodule), "commit", "-qm", "submodule fixture"],
                           check=True)
            pin = subprocess.run(["git", "-C", str(submodule), "rev-parse", "HEAD"],
                                 check=True, capture_output=True, text=True).stdout.strip()
        self.git("update-index", "--add", "--cacheinfo", f"160000,{pin},deps/module")
        self.git("commit", "-qm", "record gitlink")
        self.head = self.git("rev-parse", "HEAD")
        self.write_run(self.target, self.host)
        return submodule

    def test_hand_authored_aarch64_fixture_cannot_earn_release_acceptance(self) -> None:
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("lacks independent Rust-owned execution", result.stderr)

    def test_hand_authored_x86_64_fixture_cannot_earn_release_acceptance(self) -> None:
        self.write_run("x86_64-unknown-linux-gnu", "x86_64-unknown-linux-gnu")
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("lacks independent Rust-owned execution", result.stderr)

    def test_repo_ignored_outputs_and_empty_directory_remain_diagnostic(self) -> None:
        (self.root / "empty").mkdir()
        (self.root / "build/.gitignore").write_text("*\n", encoding="utf-8")
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("lacks independent Rust-owned execution", result.stderr)

    def test_git_environment_cannot_spoof_dirty_checkout(self) -> None:
        clean = self.root.parent / "clean-copy"
        subprocess.run(["git", "clone", "-q", str(self.root), str(clean)], check=True)
        (self.root / "dirty.txt").write_text("uncommitted\n", encoding="utf-8")
        result = self.run_validator(env={
            **os.environ, "GIT_DIR": str(clean / ".git"), "GIT_WORK_TREE": str(clean),
        })
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("repository is dirty", result.stderr)
        self.assertNotIn("structurally consistent", result.stdout)

    def test_local_worktree_config_cannot_spoof_dirty_checkout(self) -> None:
        clean = self.root.parent / "clean-copy"
        subprocess.run(["git", "clone", "-q", str(self.root), str(clean)], check=True)
        self.git("config", "core.worktree", str(clean))
        (self.root / "dirty.txt").write_text("uncommitted\n", encoding="utf-8")
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("repository is dirty", result.stderr)
        self.assertNotIn("structurally consistent", result.stdout)

    def test_filemode_config_cannot_hide_executable_change(self) -> None:
        self.git("config", "core.filemode", "false")
        (self.root / "tests/ui/hello.rs").chmod(0o755)
        self.assert_rejected("repository is dirty")

    def test_local_excludes_file_cannot_hide_untracked_source(self) -> None:
        excludes = self.root.parent / "local-excludes"
        excludes.write_text("source-added.rs\n", encoding="utf-8")
        self.git("config", "core.excludesFile", str(excludes))
        (self.root / "source-added.rs").write_text("fn main() {}\n", encoding="utf-8")
        self.assert_rejected("repository is dirty")

    def test_info_exclude_cannot_hide_untracked_source(self) -> None:
        (self.root / ".git/info/exclude").write_text("source-added.rs\n", encoding="utf-8")
        (self.root / "source-added.rs").write_text("fn main() {}\n", encoding="utf-8")
        self.assert_rejected("repository is dirty")

    def test_untracked_gitignore_cannot_hide_itself_or_source(self) -> None:
        new_dir = self.root / "new-source"
        new_dir.mkdir()
        (new_dir / ".gitignore").write_text("*\n", encoding="utf-8")
        (new_dir / "source.rs").write_text("fn main() {}\n", encoding="utf-8")
        self.assert_rejected("repository is dirty")

    def test_assume_unchanged_cannot_hide_tracked_content(self) -> None:
        self.git("update-index", "--assume-unchanged", "tests/ui/hello.rs")
        (self.root / "tests/ui/hello.rs").write_text("fn changed() {}\n", encoding="utf-8")
        self.assert_rejected("repository is dirty")

    def test_skip_worktree_cannot_hide_tracked_content(self) -> None:
        self.git("update-index", "--skip-worktree", "tests/ui/hello.rs")
        (self.root / "tests/ui/hello.rs").write_text("fn changed() {}\n", encoding="utf-8")
        self.assert_rejected("repository is dirty")

    def test_tracked_symlink_target_is_checked(self) -> None:
        link = self.root / "source-link"
        link.symlink_to("tests/ui/hello.rs")
        self.git("add", "source-link")
        self.git("commit", "-qm", "add tracked symlink")
        self.head = self.git("rev-parse", "HEAD")
        self.write_run(self.target, self.host)
        result = self.run_validator()
        self.assertIn("structurally consistent", result.stdout)
        link.unlink()
        link.symlink_to("tests/run-make/example/rmake.rs")
        self.assert_rejected("repository is dirty")

    def test_committed_crlf_checkout_remains_diagnostic(self) -> None:
        (self.root / ".gitattributes").write_text(
            "tests/ui/hello.rs text eol=crlf\n", encoding="utf-8")
        self.git("add", ".gitattributes")
        self.git("commit", "-qm", "declare CRLF checkout")
        self.head = self.git("rev-parse", "HEAD")
        self.write_run(self.target, self.host)
        source = self.root / "tests/ui/hello.rs"
        source.write_bytes(b"fn main() {}\r\n")
        self.git("add", "tests/ui/hello.rs")
        self.assertEqual(self.git("rev-parse", ":tests/ui/hello.rs"),
                         self.git("rev-parse", "HEAD:tests/ui/hello.rs"))
        result = self.run_validator()
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("lacks independent Rust-owned execution", result.stderr)
        self.git("update-index", "--assume-unchanged", "tests/ui/hello.rs")
        source.write_bytes(b"fn changed() {}\r\n")
        self.assert_rejected("repository is dirty")

    def test_committed_eol_only_checkout_remains_diagnostic(self) -> None:
        (self.root / ".gitattributes").write_text(
            "tests/ui/hello.rs eol=crlf\n", encoding="utf-8")
        self.git("add", ".gitattributes")
        self.git("commit", "-qm", "declare CRLF checkout")
        self.head = self.git("rev-parse", "HEAD")
        self.write_run(self.target, self.host)
        (self.root / "tests/ui/hello.rs").write_bytes(b"fn main() {}\r\n")
        self.git("add", "tests/ui/hello.rs")
        result = self.run_validator()
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("lacks independent Rust-owned execution", result.stderr)

    def test_committed_auto_crlf_checkout_remains_diagnostic(self) -> None:
        (self.root / ".gitattributes").write_text(
            "tests/ui/hello.rs text=auto eol=crlf\n", encoding="utf-8")
        self.git("add", ".gitattributes")
        self.git("commit", "-qm", "declare CRLF checkout")
        self.head = self.git("rev-parse", "HEAD")
        self.write_run(self.target, self.host)
        source = self.root / "tests/ui/hello.rs"
        source.write_bytes(b"fn main() {}\r\n")
        self.git("add", "tests/ui/hello.rs")
        self.assertEqual(self.git("status", "--porcelain=v1"), "")
        result = self.run_validator()
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("lacks independent Rust-owned execution", result.stderr)

    def test_auto_crlf_does_not_convert_binary_blob(self) -> None:
        (self.root / ".gitattributes").write_text(
            "binary.bin text=auto eol=crlf\n", encoding="utf-8")
        binary = self.root / "binary.bin"
        binary.write_bytes(b"\0binary\n")
        self.git("add", ".gitattributes", "binary.bin")
        self.git("commit", "-qm", "record binary auto attributes")
        self.head = self.git("rev-parse", "HEAD")
        self.write_run(self.target, self.host)
        self.git("update-index", "--assume-unchanged", "binary.bin")
        binary.write_bytes(b"\0binary\r\n")
        self.assertEqual(self.git("status", "--porcelain=v1"), "")
        self.assert_rejected("tracked bytes changed")

    def test_uninitialized_gitlink_cannot_appear_clean(self) -> None:
        self.add_gitlink(initialized=False)
        self.assertEqual(self.git("status", "--porcelain=v1", "--ignore-submodules=none"), "")
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("submodule", result.stderr)
        self.assertNotIn("structurally consistent", result.stdout)

    def test_initialized_clean_gitlink_remains_diagnostic(self) -> None:
        self.add_gitlink(initialized=True)
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("lacks independent Rust-owned execution", result.stderr)

    def test_assume_unchanged_cannot_hide_dirty_submodule(self) -> None:
        submodule = self.add_gitlink(initialized=True)
        subprocess.run(["git", "-C", str(submodule), "update-index", "--assume-unchanged",
                        "source.rs"], check=True)
        (submodule / "source.rs").write_text("fn changed() {}\n", encoding="utf-8")
        self.assertEqual(self.git("status", "--porcelain=v1", "--ignore-submodules=none"), "")
        self.assert_rejected("tracked bytes changed")

    def test_assume_unchanged_cannot_hide_submodule_pin_drift(self) -> None:
        submodule = self.add_gitlink(initialized=True)
        subprocess.run(["git", "-C", str(submodule), "commit", "--allow-empty", "-qm",
                        "advance submodule"], check=True)
        self.git("update-index", "--assume-unchanged", "deps/module")
        self.assertEqual(self.git("status", "--porcelain=v1", "--ignore-submodules=none"), "")
        self.assert_rejected("submodule pin differs")

    def test_scorecard_symlink_within_repository_remains_diagnostic(self) -> None:
        scorecard = self.out_dir / "scorecard.json"
        retained = self.out_dir / "scorecard-retained.json"
        scorecard.rename(retained)
        scorecard.symlink_to(retained)
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("lacks independent Rust-owned execution", result.stderr)

    def test_scorecard_symlink_outside_repository_is_refused(self) -> None:
        scorecard = self.out_dir / "scorecard.json"
        external = self.root.parent / "external-scorecard.json"
        shutil.copy2(scorecard, external)
        scorecard.unlink()
        scorecard.symlink_to(external)
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("scorecard", result.stderr)
        self.assertNotIn("structurally consistent", result.stdout)

    def test_other_retained_inputs_cannot_follow_symlinks_outside_repository(self) -> None:
        for path, label in ((self.proof / "case-evidence.json", "case evidence"),
                            (self.out_dir / "execution.log", "execution log")):
            with self.subTest(path=path.name):
                external = self.root.parent / f"external-{path.name}"
                shutil.copy2(path, external)
                path.unlink()
                path.symlink_to(external)
                result = self.run_validator()
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(label, result.stderr)
                self.assertNotIn("structurally consistent", result.stdout)
                path.unlink()
                shutil.copy2(external, path)

    def test_local_attributes_cannot_launder_crlf_change(self) -> None:
        (self.root / ".git/info/attributes").write_text(
            "tests/ui/hello.rs text eol=crlf\n", encoding="utf-8")
        (self.root / "tests/ui/hello.rs").write_bytes(b"fn main() {}\r\n")
        self.git("add", "tests/ui/hello.rs")
        self.assertEqual(self.git("status", "--porcelain=v1"), "")
        self.assert_rejected("local attributes override")

    def test_configured_attributes_file_cannot_launder_crlf_change(self) -> None:
        attributes = self.root.parent / "local-attributes"
        attributes.write_text("tests/ui/hello.rs text eol=crlf\n", encoding="utf-8")
        self.git("config", "core.attributesFile", str(attributes))
        (self.root / "tests/ui/hello.rs").write_bytes(b"fn main() {}\r\n")
        self.git("add", "tests/ui/hello.rs")
        self.assertEqual(self.git("status", "--porcelain=v1"), "")
        self.assert_rejected("repository is dirty")

    def test_replacement_commit_cannot_shrink_pinned_denominator(self) -> None:
        forged_commit = self.git("commit-tree", self.one_test_tree(), "-m", "forged pin")
        self.git("replace", self.pin, forged_commit)
        self.git("config", "core.useReplaceRefs", "true")
        self.assertEqual(self.git("ls-tree", "-r", "--name-only", self.pin, "--", "tests"),
                         "tests/ui/hello.rs")
        self.assertEqual(len(self.git("--no-replace-objects", "ls-tree", "-r", "--name-only",
                                      self.pin, "--", "tests").splitlines()), 2)
        self.shrink_retained_population()
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("scorecard.upstream_test_files must equal 2", result.stderr)
        self.assertNotIn("structurally consistent", result.stdout)

    def test_replacement_tree_cannot_shrink_pinned_denominator(self) -> None:
        original_tree = self.git("rev-parse", f"{self.pin}^{{tree}}")
        self.git("replace", original_tree, self.one_test_tree())
        self.assertEqual(self.git("ls-tree", "-r", "--name-only", self.pin, "--", "tests"),
                         "tests/ui/hello.rs")
        self.shrink_retained_population()
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("scorecard.upstream_test_files must equal 2", result.stderr)
        self.assertNotIn("structurally consistent", result.stdout)

    def test_cyclic_summary_path_is_refused_without_traceback(self) -> None:
        loop = self.root / "reports" / "loop.json"
        loop.symlink_to(loop)
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--repo-root", str(self.root),
             "--summary", str(loop), "--target-triple", self.target,
             "--host-triple", self.host],
            capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("upstream Rust summary rejected", result.stderr)
        self.assertNotIn("Traceback", result.stderr)

    def test_retained_old_date_is_not_arbitrarily_expired(self) -> None:
        self.summary["generated_on"] = "2025-01-01"
        self.write_json(self.summary_path, self.summary)
        result = self.run_validator()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("lacks independent Rust-owned execution", result.stderr)

    def test_noncanonical_date_is_refused_without_same_day_requirement(self) -> None:
        self.summary["generated_on"] = "2025-W01-3"
        self.write_json(self.summary_path, self.summary)
        self.assert_rejected("not a canonical ISO date")

    def test_cross_target_summary_cannot_be_clean(self) -> None:
        self.write_run("x86_64-unknown-linux-gnu", "aarch64-apple-darwin")
        self.assert_rejected("native host and target to match")

    def test_preflight_invokes_validator_on_exact_stage2(self) -> None:
        from scripts.tests.check_upstream_rust_test_toolchain_test import TOOLS, VERSION_TOOL

        stage2 = self.root / "build/aarch64-apple-darwin/stage2"
        (stage2 / "bin").mkdir(parents=True)
        target_lib = stage2 / "lib/rustlib/aarch64-apple-darwin/lib"
        target_lib.mkdir(parents=True)
        (target_lib / "libstd-fixture.rlib").write_bytes(b"synthetic")
        for name in TOOLS:
            tool = stage2 / "bin" / name
            tool.write_text(PYTHON_SHEBANG + VERSION_TOOL, encoding="utf-8")
            tool.chmod(0o755)
        env = dict(os.environ)
        env.update(TRUST_STAGE2_SYSROOT=str(stage2), TRUST_FIXTURE_COMMIT=self.head,
                   TRUST_FIXTURE_HOST="aarch64-apple-darwin",
                   TRUST_FIXTURE_TOOL_LOG=str(self.root / "build/tool-log.jsonl"))
        result = subprocess.run(
            ["bash", str(self.root / "scripts" / PREFLIGHT.name),
             "--target-triple", self.target, "--compat-summary", str(self.summary_path)],
            cwd=self.root, env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("structurally consistent", result.stdout)
        self.assertIn("summary validation failed", result.stderr)

    def test_collector_plan_includes_post_run_validation_for_both_architectures(self) -> None:
        artifact_root = COLLECTOR.parent.parent / "reports/strict-superiority"
        artifact_root.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix="collector-plan-", dir=artifact_root)
        self.addCleanup(temporary.cleanup)
        env = dict(os.environ)
        env.update(OUT_DIR=temporary.name, RUN_ID="synthetic-plan",
                   TARGO="/missing/targo-trust",
                   TRUST_X86_64_TRIPLE="x86_64-unknown-linux-gnu",
                   TRUST_AARCH64_TRIPLE="aarch64-apple-darwin")
        result = subprocess.run(["bash", str(COLLECTOR), "--plan"], cwd=self.root,
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        validation_lines = [line for line in result.stderr.splitlines()
                            if "check_upstream_rust_test_toolchain.sh" in line
                            and "--compat-summary" in line]
        self.assertEqual(len(validation_lines), 2, result.stderr)
        self.assertTrue(any("--target-triple x86_64-unknown-linux-gnu --compat-summary" in line
                            for line in validation_lines))
        self.assertTrue(any("--target-triple aarch64-apple-darwin --compat-summary" in line
                            for line in validation_lines))

    def test_stale_checkout_is_refused(self) -> None:
        self.summary["repo_head"] = self.pin
        self.write_json(self.summary_path, self.summary)
        self.assert_rejected("stale")

    def test_dirty_checkout_is_refused(self) -> None:
        (self.root / "source-changed.rs").write_text("fn changed() {}\n", encoding="utf-8")
        self.assert_rejected("repository is dirty")

    def test_wrong_upstream_pin_is_refused(self) -> None:
        self.summary["upstream_revision"] = f"rust-lang/rust:{self.head}"
        self.write_json(self.summary_path, self.summary)
        self.assert_rejected("upstream revision differs")

    def test_wrong_target_label_is_refused(self) -> None:
        self.summary["target_arch"] = "x86_64"
        self.write_json(self.summary_path, self.summary)
        self.assert_rejected("summary.target_arch")

    def test_partial_import_is_refused(self) -> None:
        scorecard = json.loads((self.out_dir / "scorecard.json").read_text())
        scorecard["imported_files"] = 0
        self.write_json(self.out_dir / "scorecard.json", scorecard)
        self.assert_rejected("scorecard.imported_files")

    def test_runner_bootstrap_args_cannot_hide_skip(self) -> None:
        self.summary["runner"]["argv"].extend(["--bootstrap-args", "--skip tests/ui/hello.rs"])
        self.write_json(self.summary_path, self.summary)
        self.assert_rejected("runner argv contains unsupported or narrowing option: --bootstrap-args")

    def test_runner_bounded_import_equals_form_is_refused(self) -> None:
        self.summary["runner"]["argv"].append("--max-files=1")
        self.write_json(self.summary_path, self.summary)
        self.assert_rejected("runner argv contains unsupported or narrowing option: --max-files=1")

    def test_omitted_primary_path_is_refused_against_git_tree(self) -> None:
        scorecard = json.loads((self.out_dir / "scorecard.json").read_text())
        scorecard["primary_upstream_tests"] = []
        self.write_json(self.out_dir / "scorecard.json", scorecard)
        self.assert_rejected("primary test population differs from pinned Git tree")

    def test_partial_proof_inventory_is_refused_even_with_updated_hash(self) -> None:
        inventory_path = self.proof / "inventory.json"
        inventory = json.loads(inventory_path.read_text())
        inventory["tests"] = []
        self.write_json(inventory_path, inventory)
        scorecard_path = self.out_dir / "scorecard.json"
        scorecard = json.loads(scorecard_path.read_text())
        raw = inventory_path.read_bytes()
        scorecard["proof_artifact_validation"]["artifacts"]["inventory.json"].update(
            size_bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
        self.write_json(scorecard_path, scorecard)
        self.assert_rejected("proof inventory/results are empty")

    def test_wrong_source_blob_is_refused_even_with_updated_hash(self) -> None:
        inventory_path = self.proof / "inventory.json"
        inventory = json.loads(inventory_path.read_text())
        inventory["tests"][0]["source_git_blob"] = self.head
        self.write_json(inventory_path, inventory)
        scorecard_path = self.out_dir / "scorecard.json"
        scorecard = json.loads(scorecard_path.read_text())
        raw = inventory_path.read_bytes()
        scorecard["proof_artifact_validation"]["artifacts"]["inventory.json"].update(
            size_bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
        self.write_json(scorecard_path, scorecard)
        self.assert_rejected("source binding differs")

    def test_wrong_executed_target_is_refused(self) -> None:
        case_path = self.proof / "case-evidence.json"
        case = json.loads(case_path.read_text())
        case["execution_command"] = case["execution_command"].replace(
            "--target aarch64-apple-darwin", "--target x86_64-apple-darwin")
        log = f"$ {case['execution_command']}\n# executor=rust-bootstrap\n# upstream_exit_status=0\n# exit_status=0\n"
        (self.out_dir / "execution.log").write_text(log, encoding="utf-8")
        case["log_sha256"] = hashlib.sha256(log.encode()).hexdigest()
        self.write_json(case_path, case)
        self.assert_rejected("executed suite --target")

    def test_false_bootstrap_launcher_is_refused(self) -> None:
        case_path = self.proof / "case-evidence.json"
        case = json.loads(case_path.read_text())
        command = shlex.split(case["execution_command"])
        command[0] = "/bin/false"
        case["execution_command"] = shlex.join(command)
        log = f"$ {case['execution_command']}\n# executor=rust-bootstrap\n# upstream_exit_status=0\n# exit_status=0\n"
        (self.out_dir / "execution.log").write_text(log, encoding="utf-8")
        case["log_sha256"] = hashlib.sha256(log.encode()).hexdigest()
        self.write_json(case_path, case)
        self.assert_rejected("launcher is not the repo-local Rust bootstrap")

    def test_skip_option_is_refused_even_with_success_footer(self) -> None:
        case_path = self.proof / "case-evidence.json"
        case = json.loads(case_path.read_text())
        case["execution_command"] += " --skip tests/ui/hello.rs"
        log = f"$ {case['execution_command']}\n# executor=rust-bootstrap\n# upstream_exit_status=0\n# exit_status=0\n"
        (self.out_dir / "execution.log").write_text(log, encoding="utf-8")
        case["log_sha256"] = hashlib.sha256(log.encode()).hexdigest()
        self.write_json(case_path, case)
        self.assert_rejected("unsupported or narrowing option: --skip")

    def test_exclude_option_is_refused_even_with_success_footer(self) -> None:
        case_path = self.proof / "case-evidence.json"
        case = json.loads(case_path.read_text())
        case["execution_command"] += " --exclude tests/ui/hello.rs"
        log = f"$ {case['execution_command']}\n# executor=rust-bootstrap\n# upstream_exit_status=0\n# exit_status=0\n"
        (self.out_dir / "execution.log").write_text(log, encoding="utf-8")
        case["log_sha256"] = hashlib.sha256(log.encode()).hexdigest()
        self.write_json(case_path, case)
        self.assert_rejected("unsupported or narrowing option: --exclude")

    def test_missing_case_observation_is_refused(self) -> None:
        case_path = self.proof / "case-evidence.json"
        case = json.loads(case_path.read_text())
        case["observations"] = []
        self.write_json(case_path, case)
        self.assert_rejected("omitted expected observations")

    def test_missing_execution_footer_is_refused(self) -> None:
        case_path = self.proof / "case-evidence.json"
        case = json.loads(case_path.read_text())
        log = f"$ {case['execution_command']}\n# executor=rust-bootstrap\n"
        (self.out_dir / "execution.log").write_text(log, encoding="utf-8")
        case["log_sha256"] = hashlib.sha256(log.encode()).hexdigest()
        self.write_json(case_path, case)
        self.assert_rejected("completion footer")

    def test_unknown_compatibility_result_is_refused(self) -> None:
        self.summary["results"][0]["outcome"] = "unknown"
        self.write_json(self.summary_path, self.summary)
        self.assert_rejected("unknown, divergent, or waived")

    def test_malformed_summary_result_is_refused_cleanly(self) -> None:
        self.summary["results"][0] = "hand-authored"
        self.write_json(self.summary_path, self.summary)
        self.assert_rejected("summary row must be an object")

    def test_duplicate_summary_key_is_refused(self) -> None:
        self.summary_path.write_text('{"repo_head":"x","repo_head":"y"}\n', encoding="utf-8")
        self.assert_rejected("duplicate JSON key")


if __name__ == "__main__":
    unittest.main()
