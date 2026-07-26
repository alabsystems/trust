"""Focused tests for bootstrap installation and provenance gates."""

import importlib.util
import io
import json
import os
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "recreate_bootstrap.py"
SPEC = importlib.util.spec_from_file_location("recreate_bootstrap", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
recreate_bootstrap = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = recreate_bootstrap
SPEC.loader.exec_module(recreate_bootstrap)


class RustupRegistrationTests(unittest.TestCase):
    def test_seed_mode_does_not_present_stock_rust_as_a_prerequisite(self):
        def fake_which(name: str):
            if name in {"rustc", "cargo"}:
                return None
            return f"/nonexistent-test-bin/{name}"

        with patch.object(recreate_bootstrap, "which", side_effect=fake_which), patch.object(
            recreate_bootstrap, "find_python_ge_311", return_value=sys.executable
        ), patch.object(recreate_bootstrap, "find_rustup", return_value=None), patch.object(
            recreate_bootstrap.platform, "system", return_value="Linux"
        ):
            checks = recreate_bootstrap.check_prereqs(seed_mode=True)

        names = {check.name for check in checks}
        self.assertNotIn("rustc", names)
        self.assertNotIn("cargo", names)

    def test_missing_rustup_is_an_early_required_prerequisite_for_registration(self):
        with patch.object(recreate_bootstrap, "find_rustup", return_value=None):
            checks = recreate_bootstrap.check_prereqs(require_rustup=True)
        rustup = next(check for check in checks if check.name == "rustup")
        self.assertTrue(rustup.required)
        self.assertFalse(rustup.ok)

    def test_stage1_never_invokes_rustup_without_explicit_opt_in(self):
        with patch.object(recreate_bootstrap, "register_rustup_toolchain") as register:
            self.assertTrue(
                recreate_bootstrap.maybe_register_rustup_toolchain(
                    Path("/checkout"), "test-host", 1
                )
            )
        register.assert_not_called()

    def test_homebrew_keg_only_rustup_is_discovered(self):
        with tempfile.TemporaryDirectory() as directory:
            rustup = Path(directory) / "bin" / "rustup"
            rustup.parent.mkdir()
            rustup.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            rustup.chmod(rustup.stat().st_mode | stat.S_IXUSR)

            def fake_which(name: str):
                return "/mock/brew" if name == "brew" else None

            prefix = SimpleNamespace(returncode=0, stdout=f"{directory}\n", stderr="")
            with patch.object(recreate_bootstrap, "which", side_effect=fake_which), patch.object(
                recreate_bootstrap.subprocess, "run", return_value=prefix
            ) as run:
                self.assertEqual(recreate_bootstrap.find_rustup(), str(rustup))
            run.assert_called_once_with(
                ["/mock/brew", "--prefix", "rustup"],
                capture_output=True,
                text=True,
                check=False,
                timeout=10,
            )

    def test_stage2_registration_failure_propagates(self):
        with patch.object(
            recreate_bootstrap, "register_rustup_toolchain", return_value=False
        ) as register:
            self.assertFalse(
                recreate_bootstrap.maybe_register_rustup_toolchain(
                    Path("/checkout"), "test-host", 2
                )
            )
        register.assert_called_once_with(Path("/checkout"), "test-host", 2)

    def test_link_failure_is_not_reported_as_success(self):
        failure = SimpleNamespace(returncode=1, stdout="", stderr="link refused")
        with patch.object(recreate_bootstrap, "find_rustup", return_value="/mock/rustup"), patch.object(
            recreate_bootstrap.subprocess, "run", return_value=failure
        ):
            self.assertFalse(
                recreate_bootstrap.register_rustup_toolchain(
                    Path(os.sep) / "checkout", "test-host", 2
                )
            )


class BootstrapBuildLaunchTests(unittest.TestCase):
    def test_stage2_provenance_build_rejects_forwarded_xpy_authority(self):
        with patch.object(recreate_bootstrap, "ensure_python_311"), patch.object(
            recreate_bootstrap, "line_buffer_output"
        ), patch.object(
            recreate_bootstrap, "repo_root", return_value=Path("/checkout")
        ), patch.object(
            recreate_bootstrap, "host_triple", return_value="test-host"
        ), patch.object(
            recreate_bootstrap, "resolve_seed"
        ) as resolve_seed, patch.object(
            recreate_bootstrap.subprocess, "run"
        ) as run:
            result = recreate_bootstrap.main(
                ["--stage", "2", "--", "--set=build.rustc=/tmp/stock"]
            )

        self.assertEqual(result, 2)
        resolve_seed.assert_not_called()
        run.assert_not_called()

    def test_stage1_developer_build_may_forward_non_provenance_args(self):
        self.assertEqual(
            recreate_bootstrap.normalized_xpy_extra(
                ["--", "--set=build.rustc=/tmp/developer-rustc"]
            ),
            ["--set=build.rustc=/tmp/developer-rustc"],
        )

    def test_no_register_makes_rustup_optional_for_stage2(self):
        self.assertTrue(
            recreate_bootstrap.rustup_registration_required(
                2,
                no_build=False,
                no_register=False,
                register_non_stage2=False,
            )
        )
        self.assertFalse(
            recreate_bootstrap.rustup_registration_required(
                2,
                no_build=False,
                no_register=True,
                register_non_stage2=False,
            )
        )

    def launch_environment(self, *, seed_mode: bool) -> dict[str, str]:
        captured: dict[str, str] = {}

        def run(command, *, env, cwd):
            self.assertEqual(
                command[:5],
                [sys.executable, "/checkout/x.py", "build", "--stage", "2"],
            )
            self.assertEqual(cwd, "/checkout")
            captured.update(env)
            return SimpleNamespace(returncode=0)

        hostile = {
            "RUSTFLAGS": "-Ztrust-verify-full",
            "RUSTFLAGS_BOOTSTRAP": "-Ztrust-verify-full",
            "CARGO_TARGET_TEST_RUSTFLAGS": "-Ztrust-policy=advisory",
            "UNRELATED": "preserved",
        }
        with patch.dict(os.environ, hostile, clear=True), patch.object(
            recreate_bootstrap, "add_homebrew_library_path"
        ), patch.object(recreate_bootstrap.subprocess, "run", side_effect=run):
            self.assertEqual(
                recreate_bootstrap.run_xpy_build(
                    Path("/checkout"), 2, None, [], seed_mode=seed_mode
                ),
                0,
            )
        return captured

    def test_seed_build_uses_exact_recorded_bootstrap_off_switch(self):
        env = self.launch_environment(seed_mode=True)
        self.assertEqual(
            env["RUSTFLAGS_BOOTSTRAP"],
            recreate_bootstrap.BOOTSTRAP_COMPILER_VERIFICATION["flag"],
        )
        self.assertNotIn("RUSTFLAGS", env)
        self.assertNotIn("CARGO_TARGET_TEST_RUSTFLAGS", env)
        self.assertEqual(env["UNRELATED"], "preserved")

    def test_genesis_build_never_receives_trust_specific_off_switch(self):
        env = self.launch_environment(seed_mode=False)
        self.assertNotIn("RUSTFLAGS_BOOTSTRAP", env)
        self.assertNotIn("RUSTFLAGS", env)
        self.assertNotIn("CARGO_TARGET_TEST_RUSTFLAGS", env)
        self.assertEqual(env["UNRELATED"], "preserved")


class FreshSeedMaterializationTests(unittest.TestCase):
    host = "test-host"

    def test_quarantine_is_recoverable_and_does_not_touch_other_stages(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            host_root = root / "build" / self.host
            stage0 = host_root / "stage0"
            stage1 = host_root / "stage1" / "sentinel"
            stage2 = host_root / "stage2" / "sentinel"
            archive = root / "bootstrap" / "trust-stage0" / "seed.tar.xz"
            (stage0 / "bin").mkdir(parents=True)
            (stage0 / "bin" / "trustc").write_bytes(b"seed")
            stage1.parent.mkdir(parents=True)
            stage1.write_bytes(b"stage1")
            stage2.parent.mkdir(parents=True)
            stage2.write_bytes(b"stage2")
            archive.parent.mkdir(parents=True)
            archive.write_bytes(b"archive")

            quarantine = recreate_bootstrap.quarantine_seed_stage0(root, self.host)
            self.assertIsNotNone(quarantine)
            assert quarantine is not None
            self.assertFalse(stage0.exists())
            self.assertEqual((quarantine / "bin" / "trustc").read_bytes(), b"seed")
            self.assertEqual(stage1.read_bytes(), b"stage1")
            self.assertEqual(stage2.read_bytes(), b"stage2")
            self.assertEqual(archive.read_bytes(), b"archive")

            recreate_bootstrap.recover_seed_stage0_quarantine(
                root, self.host, quarantine
            )
            self.assertEqual((stage0 / "bin" / "trustc").read_bytes(), b"seed")
            self.assertFalse(quarantine.exists())

    def test_success_cleanup_preserves_fresh_replacement(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stage0 = root / "build" / self.host / "stage0"
            stage0.mkdir(parents=True)
            (stage0 / "old").write_bytes(b"old")
            quarantine = recreate_bootstrap.quarantine_seed_stage0(root, self.host)
            assert quarantine is not None
            stage0.mkdir()
            (stage0 / "fresh").write_bytes(b"fresh")

            recreate_bootstrap.discard_seed_stage0_quarantine(
                root, self.host, quarantine
            )
            self.assertFalse(quarantine.exists())
            self.assertEqual((stage0 / "fresh").read_bytes(), b"fresh")

    def test_cleanup_io_failure_is_controlled_and_preserves_replacement(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stage0 = root / "build" / self.host / "stage0"
            stage0.mkdir(parents=True)
            (stage0 / "old").write_bytes(b"old")
            quarantine = recreate_bootstrap.quarantine_seed_stage0(root, self.host)
            assert quarantine is not None
            stage0.mkdir()
            (stage0 / "fresh").write_bytes(b"fresh")

            with patch.object(
                recreate_bootstrap.shutil,
                "rmtree",
                side_effect=OSError("cleanup refused"),
            ), self.assertRaisesRegex(RuntimeError, "could not remove superseded"):
                recreate_bootstrap.discard_seed_stage0_quarantine(
                    root, self.host, quarantine
                )

            self.assertTrue(quarantine.is_dir())
            self.assertEqual((stage0 / "fresh").read_bytes(), b"fresh")

    def test_absent_stage0_is_idempotent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "build" / self.host).mkdir(parents=True)
            self.assertIsNone(
                recreate_bootstrap.quarantine_seed_stage0(root, self.host)
            )

    def test_symlinks_and_host_traversal_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "checkout"
            external = Path(directory) / "external"
            external_stage0 = external / "stage0"
            external_stage0.mkdir(parents=True)
            sentinel = external_stage0 / "sentinel"
            sentinel.write_bytes(b"outside")
            (root / "build").mkdir(parents=True)
            (root / "build" / self.host).symlink_to(external, target_is_directory=True)

            with self.assertRaisesRegex(RuntimeError, "must not be a symlink"):
                recreate_bootstrap.quarantine_seed_stage0(root, self.host)
            with self.assertRaisesRegex(RuntimeError, "unsafe host component"):
                recreate_bootstrap.quarantine_seed_stage0(root, "../external")
            self.assertEqual(sentinel.read_bytes(), b"outside")

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "checkout"
            external = Path(directory) / "external-build"
            external_stage0 = external / self.host / "stage0"
            external_stage0.mkdir(parents=True)
            sentinel = external_stage0 / "sentinel"
            sentinel.write_bytes(b"outside")
            root.mkdir()
            (root / "build").symlink_to(external, target_is_directory=True)

            with self.assertRaisesRegex(RuntimeError, "build directory must not be a symlink"):
                recreate_bootstrap.quarantine_seed_stage0(root, self.host)
            self.assertEqual(sentinel.read_bytes(), b"outside")

    def test_interrupted_quarantine_resumes_or_refuses_without_accumulating(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            host_root = root / "build" / self.host
            quarantine = host_root / "stage0.preexisting-fresh-seed"
            quarantine.mkdir(parents=True)
            (quarantine / "old").write_bytes(b"old")

            self.assertEqual(
                recreate_bootstrap.quarantine_seed_stage0(root, self.host),
                quarantine,
            )
            self.assertEqual(list(host_root.glob("stage0.preexisting-*")), [quarantine])

            stage0 = host_root / "stage0"
            stage0.mkdir()
            (stage0 / "new").write_bytes(b"new")
            with self.assertRaisesRegex(RuntimeError, "refusing to choose or delete either"):
                recreate_bootstrap.quarantine_seed_stage0(root, self.host)
            self.assertEqual((quarantine / "old").read_bytes(), b"old")
            self.assertEqual((stage0 / "new").read_bytes(), b"new")

    def test_fresh_seed_conflicts_fail_before_resolution(self):
        cases = (
            ["--fresh-seed", "--require-seed", "--check"],
            ["--fresh-seed", "--require-seed", "--no-build"],
            ["--fresh-seed", "--require-seed", "--stage", "1"],
            ["--fresh-seed", "--require-seed", "--genesis"],
            ["--fresh-seed", "--verify-stage-provenance"],
            ["--fresh-seed", "--stage", "2"],
        )
        with patch.object(recreate_bootstrap, "ensure_python_311"), patch.object(
            recreate_bootstrap, "line_buffer_output"
        ), patch.object(
            recreate_bootstrap, "repo_root", return_value=Path("/checkout")
        ), patch.object(
            recreate_bootstrap, "host_triple", return_value=self.host
        ), patch.object(recreate_bootstrap, "resolve_seed") as resolve_seed:
            for argv in cases:
                with self.subTest(argv=argv):
                    self.assertEqual(recreate_bootstrap.main(argv), 2)
        resolve_seed.assert_not_called()

    def test_fresh_seed_verifies_immutable_receipt_before_registration(self):
        source = {
            "status": "immutable_release",
            "closure_sha256": "a" * 64,
            "errors": [],
        }
        bootstrap = {
            "status": "seed-validated-pending-hydration",
            "mode": "seed",
            "config_sha256": "b" * 64,
            "errors": [],
        }
        authority = {
            "status": "ready",
            "authority_sha256": "c" * 64,
            "errors": [],
        }
        events: list[str] = []
        quarantine = Path(
            "/checkout/build/test-host/stage0.preexisting-fresh-seed"
        )
        verification_results = iter((True, False))

        with ExitStack() as stack:
            stack.enter_context(patch.object(recreate_bootstrap, "ensure_python_311"))
            stack.enter_context(patch.object(recreate_bootstrap, "line_buffer_output"))
            stack.enter_context(
                patch.object(recreate_bootstrap, "repo_root", return_value=Path("/checkout"))
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "host_triple", return_value=self.host)
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "resolve_seed",
                    side_effect=lambda *_args, **_kwargs: events.append("resolve") or True,
                )
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "check_prereqs", return_value=[])
            )
            for name in (
                "print_prereqs",
                "ensure_submodules",
                "scrub_pat_from_remotes",
                "write_config",
            ):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "capture_source_lineage",
                    side_effect=lambda *_args, **_kwargs: events.append("source") or source,
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "quarantine_seed_stage0",
                    side_effect=lambda *_args: (events.append("quarantine"), quarantine)[1],
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "capture_bootstrap_lineage",
                    side_effect=lambda *_args, **_kwargs: events.append("bootstrap") or bootstrap,
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "capture_build_authority",
                    side_effect=lambda *_args, **_kwargs: events.append("authority") or authority,
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "run_xpy_build",
                    side_effect=lambda *_args, **_kwargs: events.append("xpy") or 0,
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "install_ay_solver",
                    side_effect=lambda *_args, **_kwargs: events.append("install") or True,
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "audit_stage_tool_provenance",
                    side_effect=lambda *_args, **_kwargs: events.append("audit") or True,
                )
            )
            verify = stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "verify_stage_tool_provenance",
                    side_effect=lambda *_args, **_kwargs: (
                        events.append("verify"),
                        next(verification_results),
                    )[1],
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "discard_seed_stage0_quarantine",
                    side_effect=lambda *_args: events.append("discard"),
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "maybe_register_rustup_toolchain",
                    side_effect=lambda *_args, **_kwargs: events.append("register") or True,
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "recover_seed_stage0_quarantine",
                    side_effect=lambda *_args: events.append("recover"),
                )
            )
            self.assertEqual(
                recreate_bootstrap.main(
                    ["--fresh-seed", "--require-seed", "--stage", "2"]
                ),
                0,
            )
            self.assertEqual(
                events,
                [
                    "resolve",
                    "source",
                    "quarantine",
                    "bootstrap",
                    "authority",
                    "xpy",
                    "install",
                    "audit",
                    "verify",
                    "discard",
                    "register",
                ],
            )
            self.assertTrue(verify.call_args.kwargs["require_immutable_lineage"])

            events.clear()
            self.assertEqual(
                recreate_bootstrap.main(
                    ["--fresh-seed", "--require-seed", "--stage", "2"]
                ),
                1,
            )
            self.assertEqual(
                events,
                [
                    "resolve",
                    "source",
                    "quarantine",
                    "bootstrap",
                    "authority",
                    "xpy",
                    "install",
                    "audit",
                    "verify",
                    "recover",
                ],
            )


class SubmoduleMaterializationTests(unittest.TestCase):
    @staticmethod
    def git(repository: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                "git",
                "-c",
                "protocol.file.allow=always",
                "-C",
                str(repository),
                *arguments,
            ],
            check=True,
            capture_output=True,
            text=True,
        )

    def create_repository(self, path: Path, name: str) -> None:
        path.mkdir()
        self.git(path, "init", "--quiet")
        self.git(path, "config", "user.name", "Bootstrap Test")
        self.git(path, "config", "user.email", "bootstrap@example.invalid")
        (path / "Cargo.toml").write_text(
            f'[package]\nname = "{name}"\nversion = "0.0.0"\n',
            encoding="utf-8",
        )
        (path / "Cargo.lock").write_text(
            "# tracked bootstrap fixture\n", encoding="utf-8"
        )
        self.git(path, "add", "Cargo.toml", "Cargo.lock")
        self.git(path, "commit", "--quiet", "-m", "fixture")

    def partial_checkout(self, directory: str) -> Path:
        base = Path(directory)
        ay = base / "ay-source"
        clean = base / "clean-source"
        superproject = base / "superproject"
        checkout = base / "checkout"
        self.create_repository(ay, "ay-fixture")
        self.create_repository(clean, "clean-fixture")
        superproject.mkdir()
        self.git(superproject, "init", "--quiet")
        self.git(superproject, "config", "user.name", "Bootstrap Test")
        self.git(
            superproject,
            "config",
            "user.email",
            "bootstrap@example.invalid",
        )
        self.git(
            superproject,
            "submodule",
            "add",
            "--quiet",
            str(ay),
            "first-party/ay",
        )
        self.git(
            superproject,
            "submodule",
            "add",
            "--quiet",
            str(clean),
            "first-party/clean",
        )
        self.git(superproject, "commit", "--quiet", "-m", "submodules")
        subprocess.run(
            [
                "git",
                "-c",
                "protocol.file.allow=always",
                "clone",
                "--quiet",
                "--no-recurse-submodules",
                str(superproject),
                str(checkout),
            ],
            check=True,
        )
        self.git(
            checkout,
            "submodule",
            "update",
            "--init",
            "--",
            "first-party/ay",
        )
        return checkout

    def ensure_with_test_file_transport(self, checkout: Path) -> list[list[str]]:
        """Admit local fixture remotes without weakening production policy."""
        real_update = recreate_bootstrap._run_submodule_update_process
        updates: list[list[str]] = []

        def run_update(command, **kwargs):
            updates.append(command)
            return real_update(command, **kwargs)

        test_overrides = recreate_bootstrap.CONTROLLED_GIT_CONFIG_OVERRIDES + (
            "protocol.file.allow=always",
        )
        with patch.object(
            recreate_bootstrap,
            "CONTROLLED_GIT_CONFIG_OVERRIDES",
            test_overrides,
        ), patch.object(
            recreate_bootstrap,
            "_submodule_url_is_allowed",
            return_value=True,
        ), patch.object(
            recreate_bootstrap,
            "_run_submodule_update_process",
            side_effect=run_update,
        ):
            recreate_bootstrap.ensure_submodules(checkout)
        return updates

    def test_ay_present_does_not_hide_another_missing_indexed_submodule(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            ay_source = Path(directory) / "ay-source"
            (ay_source / "post-gitlink.txt").write_text(
                "deliberately advanced submodule commit\n", encoding="utf-8"
            )
            self.git(ay_source, "add", "post-gitlink.txt")
            self.git(ay_source, "commit", "--quiet", "-m", "advance ay")
            advanced = self.git(ay_source, "rev-parse", "HEAD").stdout.strip()
            ay_checkout = checkout / "first-party" / "ay"
            self.git(ay_checkout, "fetch", "--quiet", "origin")
            self.git(ay_checkout, "checkout", "--quiet", "--detach", advanced)
            ay_head = self.git(
                ay_checkout, "rev-parse", "HEAD"
            ).stdout.strip()
            before = self.git(checkout, "submodule", "status").stdout.splitlines()
            self.assertEqual([line[0] for line in before], ["+", "-"])

            updates = self.ensure_with_test_file_transport(checkout)

            after = self.git(checkout, "submodule", "status").stdout.splitlines()
            self.assertEqual([line[0] for line in after], ["+", " "])
            self.assertTrue(updates)
            self.assertTrue(all("--checkout" in command for command in updates))
            self.assertEqual(
                self.git(ay_checkout, "rev-parse", "HEAD").stdout.strip(),
                ay_head,
            )

    def test_path_and_git_ssh_environment_cannot_select_executable_authority(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "authority-fixture")
            attacker_bin = Path(directory) / "attacker-bin"
            attacker_bin.mkdir()
            marker = Path(directory) / "path-git-executed"
            fake_git = attacker_bin / "git"
            fake_git.write_text(
                f"#!/bin/sh\nprintf compromised > {marker}\nexit 99\n",
                encoding="utf-8",
            )
            fake_git.chmod(0o755)

            hostile_environment = {
                "PATH": str(attacker_bin),
                "GIT_EXEC_PATH": str(attacker_bin),
                "GIT_SSH": str(fake_git),
                "GIT_SSH_COMMAND": f"{fake_git} ssh",
                "GIT_ASKPASS": str(fake_git),
                "SSH_ASKPASS": str(fake_git),
                "GIT_CONFIG_COUNT": "1",
                "GIT_CONFIG_KEY_0": "credential.helper",
                "GIT_CONFIG_VALUE_0": f"!{fake_git}",
            }
            with patch.dict(os.environ, hostile_environment, clear=False):
                controlled = recreate_bootstrap._provenance_git_environment()
                result = recreate_bootstrap._run_git_read(
                    repository, ["rev-parse", "--verify", "HEAD"]
                )

            self.assertEqual(result.stdout.strip(), self.git(repository, "rev-parse", "HEAD").stdout.strip())
            self.assertFalse(marker.exists(), "PATH-selected Git or helper executed")
            for name in hostile_environment:
                if name != "PATH":
                    self.assertNotEqual(controlled.get(name), hostile_environment[name])
            self.assertEqual(controlled["PATH"], recreate_bootstrap.CONTROLLED_GIT_PATH)

    def test_materialization_opens_only_user_credential_lookup(self):
        hostile_environment = {
            "HOME": "/credential-home",
            "XDG_CONFIG_HOME": "/credential-xdg",
            "GH_CONFIG_DIR": "/credential-gh",
            "GH_TOKEN": "must-not-be-forwarded",
            "GITHUB_TOKEN": "must-not-be-forwarded-either",
            "GIT_ASKPASS": "/tmp/attacker-askpass",
            "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_KEY_0": "credential.helper",
            "GIT_CONFIG_VALUE_0": "!attacker",
            "HTTPS_PROXY": "http://attacker.invalid",
            "DYLD_INSERT_LIBRARIES": "/tmp/attacker.dylib",
        }
        interactive_stdin = SimpleNamespace(isatty=lambda: True)
        with patch.dict(os.environ, hostile_environment, clear=True), patch.object(
            recreate_bootstrap.sys, "stdin", interactive_stdin
        ):
            materialization = recreate_bootstrap._submodule_materialization_environment()
            provenance = recreate_bootstrap._provenance_git_environment()
            credential_environment = recreate_bootstrap._credential_gh_environment()

        self.assertNotEqual(materialization["HOME"], "/credential-home")
        self.assertNotIn("XDG_CONFIG_HOME", materialization)
        self.assertNotIn("GH_CONFIG_DIR", materialization)
        self.assertEqual(
            credential_environment,
            {"GH_CONFIG_DIR": "/credential-gh", "HOME": "/credential-home"},
        )
        self.assertEqual(materialization["GIT_TERMINAL_PROMPT"], "1")
        self.assertNotIn("GIT_ASKPASS", materialization)
        for name in (
            "GH_TOKEN",
            "GITHUB_TOKEN",
            "GIT_CONFIG_COUNT",
            "GIT_CONFIG_KEY_0",
            "GIT_CONFIG_VALUE_0",
            "HTTPS_PROXY",
            "DYLD_INSERT_LIBRARIES",
        ):
            self.assertNotIn(name, materialization)
        self.assertNotEqual(provenance["HOME"], "/credential-home")
        self.assertEqual(provenance["GIT_TERMINAL_PROMPT"], "0")
        self.assertIn("GIT_ASKPASS", provenance)

        with patch.dict(
            os.environ,
            {"HOME": "/caller-home", "XDG_CONFIG_HOME": "/caller-xdg"},
            clear=True,
        ):
            derived = recreate_bootstrap._submodule_materialization_environment()
        self.assertNotIn("GH_CONFIG_DIR", derived)
        self.assertNotEqual(derived["HOME"], "/caller-home")
        self.assertNotIn("XDG_CONFIG_HOME", derived)
        with patch.dict(
            os.environ,
            {"HOME": "/caller-home", "XDG_CONFIG_HOME": "/caller-xdg"},
            clear=True,
        ):
            self.assertEqual(
                recreate_bootstrap._credential_gh_environment(),
                {"GH_CONFIG_DIR": "/caller-xdg/gh", "HOME": "/caller-home"},
            )

        noninteractive_stdin = SimpleNamespace(isatty=lambda: False)
        with patch.object(recreate_bootstrap.sys, "stdin", noninteractive_stdin):
            noninteractive = recreate_bootstrap._submodule_materialization_environment()
        self.assertEqual(noninteractive["GIT_TERMINAL_PROMPT"], "0")

    def test_gh_helper_reads_but_never_stores_credentials(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fake_gh = root / "fake-gh"
            marker = root / "helper-calls"
            fake_gh.write_text(
                "#!/bin/sh\n"
                "printf '%s\\n' \"$3\" >> \"$TEST_HELPER_MARKER\"\n"
                "if test \"$3\" = get; then\n"
                "  printf 'username=x-access-token\\npassword=test-token\\n\\n'\n"
                "fi\n",
                encoding="utf-8",
            )
            fake_gh.chmod(0o700)
            helper = recreate_bootstrap._read_only_gh_credential_helper(fake_gh)
            env = recreate_bootstrap._provenance_git_environment()
            env["TEST_HELPER_MARKER"] = str(marker)
            approve = "protocol=https\nhost=github.com\nusername=u\npassword=p\n\n"
            subprocess.run(
                recreate_bootstrap._controlled_git_command(
                    ["-c", helper, "credential", "approve"]
                ),
                input=approve,
                text=True,
                capture_output=True,
                check=True,
                env=env,
                timeout=10,
            )
            self.assertFalse(marker.exists(), "credential store reached gh")

            filled = subprocess.run(
                recreate_bootstrap._controlled_git_command(
                    ["-c", helper, "credential", "fill"]
                ),
                input="protocol=https\nhost=github.com\n\n",
                text=True,
                capture_output=True,
                check=True,
                env=env,
                timeout=10,
            )
            self.assertIn("password=test-token", filled.stdout)
            self.assertEqual(marker.read_text(encoding="utf-8"), "get\n")

    def test_submodule_url_policy_is_exact_github_https_without_credentials(self):
        self.assertTrue(
            recreate_bootstrap._submodule_url_is_allowed(
                "https://github.com/alabsystems/ay.git"
            )
        )
        for value in (
            "git@github.com:alabsystems/ay.git",
            "ssh://git@github.com/alabsystems/ay.git",
            "http://github.com/alabsystems/ay.git",
            "https://user:secret@github.com/alabsystems/ay.git",
            "https://github.com:443/alabsystems/ay.git",
            "https://github.com/alabsystems/ay.git?token=secret",
            "https://github.com/alabsystems/ay.git#secret",
            "https://github.com.evil.invalid/alabsystems/ay.git",
            "https://github.com/alabsystems/ay",
        ):
            with self.subTest(value=value):
                self.assertFalse(
                    recreate_bootstrap._submodule_url_is_allowed(value)
                )

    @unittest.skipUnless(os.name == "posix", "POSIX credential path authority")
    def test_gh_authority_accepts_owned_homebrew_style_alias(self):
        with tempfile.TemporaryDirectory(dir=SCRIPT.parent) as directory:
            root = Path(directory)
            executable = root / "Cellar" / "gh" / "1.0" / "bin" / "gh"
            executable.parent.mkdir(parents=True)
            executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            executable.chmod(0o700)
            alias = root / "bin" / "gh"
            alias.parent.mkdir()
            alias.symlink_to(Path("..") / "Cellar" / "gh" / "1.0" / "bin" / "gh")

            self.assertEqual(
                recreate_bootstrap._trusted_credential_executable(alias),
                executable.resolve(strict=True),
            )

    @unittest.skipUnless(os.name == "posix", "POSIX Homebrew credential snapshot")
    def test_gh_authority_snapshots_fixed_homebrew_shape(self):
        with tempfile.TemporaryDirectory(dir=SCRIPT.parent) as directory:
            root = Path(directory)
            homebrew = root / "homebrew"
            cellar = homebrew / "Cellar" / "gh"
            executable = cellar / "2.93.0" / "bin" / "gh"
            executable.parent.mkdir(parents=True)
            original = b"#!/bin/sh\nprintf 'fixture gh\\n'\n"
            executable.write_bytes(original)
            executable.chmod(0o500)
            alias = homebrew / "bin" / "gh"
            alias.parent.mkdir()
            alias.symlink_to(Path("..") / "Cellar" / "gh" / "2.93.0" / "bin" / "gh")
            # Match the standard Homebrew installation shape that motivated
            # the snapshot: these ancestors are not execution authority.
            alias.parent.chmod(0o775)
            (homebrew / "Cellar").chmod(0o775)
            snapshot_directory = root / "snapshot"
            snapshot_directory.mkdir(mode=0o700)

            with patch.object(
                recreate_bootstrap,
                "_HOMEBREW_CREDENTIAL_LAYOUTS",
                ((alias, cellar),),
            ), patch.object(
                recreate_bootstrap,
                "which",
                return_value=str(alias),
            ):
                self.assertIsNone(
                    recreate_bootstrap._trusted_credential_executable(alias)
                )
                snapshot = recreate_bootstrap._credential_gh_executable(
                    snapshot_directory
                )

            self.assertEqual(
                snapshot, snapshot_directory / "gh-credential-helper"
            )
            assert snapshot is not None
            self.assertEqual(snapshot.read_bytes(), original)
            self.assertEqual(stat.S_IMODE(snapshot.stat().st_mode), 0o700)
            self.assertNotEqual(snapshot.resolve(), executable.resolve())

            executable.chmod(0o700)
            executable.write_bytes(b"replaced after snapshot\n")
            self.assertEqual(snapshot.read_bytes(), original)

            failed_snapshot_directory = root / "failed-snapshot"
            failed_snapshot_directory.mkdir(mode=0o700)
            with patch.object(
                recreate_bootstrap,
                "_HOMEBREW_CREDENTIAL_LAYOUTS",
                ((alias, cellar),),
            ), patch.object(
                recreate_bootstrap.os,
                "fsync",
                side_effect=OSError("simulated durable-copy failure"),
            ):
                self.assertIsNone(
                    recreate_bootstrap._snapshot_homebrew_credential_executable(
                        alias, failed_snapshot_directory
                    )
                )
            self.assertFalse(
                (failed_snapshot_directory / "gh-credential-helper").exists()
            )

            occupied_snapshot_directory = root / "occupied-snapshot"
            occupied_snapshot_directory.mkdir(mode=0o700)
            occupied = occupied_snapshot_directory / "gh-credential-helper"
            occupied.write_bytes(b"pre-existing private file\n")
            occupied.chmod(0o600)
            with patch.object(
                recreate_bootstrap,
                "_HOMEBREW_CREDENTIAL_LAYOUTS",
                ((alias, cellar),),
            ):
                self.assertIsNone(
                    recreate_bootstrap._snapshot_homebrew_credential_executable(
                        alias, occupied_snapshot_directory
                    )
                )
            self.assertEqual(occupied.read_bytes(), b"pre-existing private file\n")

    @unittest.skipUnless(os.name == "posix", "POSIX Homebrew credential snapshot")
    def test_gh_snapshot_stays_bound_when_path_alias_changes_after_open(self):
        with tempfile.TemporaryDirectory(dir=SCRIPT.parent) as directory:
            root = Path(directory)
            homebrew = root / "homebrew"
            cellar = homebrew / "Cellar" / "gh"
            first = cellar / "1.0" / "bin" / "gh"
            second = cellar / "2.0" / "bin" / "gh"
            for executable, contents in (
                (first, b"first opened inode\n"),
                (second, b"later alias target\n"),
            ):
                executable.parent.mkdir(parents=True)
                executable.write_bytes(contents)
                executable.chmod(0o500)
            alias = homebrew / "bin" / "gh"
            alias.parent.mkdir()
            alias.symlink_to(Path("..") / "Cellar" / "gh" / "1.0" / "bin" / "gh")
            alias.parent.chmod(0o775)
            (homebrew / "Cellar").chmod(0o775)
            snapshot_directory = root / "snapshot"
            snapshot_directory.mkdir(mode=0o700)
            real_open = os.open
            raced = False

            def open_and_replace_alias(path, flags, mode=0o777):
                nonlocal raced
                descriptor = real_open(path, flags, mode)
                if not raced and Path(path) == first:
                    raced = True
                    alias.unlink()
                    alias.symlink_to(
                        Path("..") / "Cellar" / "gh" / "2.0" / "bin" / "gh"
                    )
                return descriptor

            with patch.object(
                recreate_bootstrap,
                "_HOMEBREW_CREDENTIAL_LAYOUTS",
                ((alias, cellar),),
            ), patch.object(
                recreate_bootstrap.os,
                "open",
                side_effect=open_and_replace_alias,
            ):
                snapshot = recreate_bootstrap._snapshot_homebrew_credential_executable(
                    alias, snapshot_directory
                )

            self.assertTrue(raced)
            assert snapshot is not None
            self.assertEqual(alias.resolve(strict=True), second)
            self.assertEqual(snapshot.read_bytes(), b"first opened inode\n")

    @unittest.skipUnless(os.name == "posix", "POSIX credential source ownership")
    def test_gh_snapshot_rejects_foreign_owned_or_multiply_linked_source(self):
        metadata = SimpleNamespace(
            st_mode=stat.S_IFREG | 0o500,
            st_nlink=1,
            st_size=1024,
            st_uid=os.geteuid() + 1,
        )
        self.assertFalse(
            recreate_bootstrap._credential_source_metadata_is_allowed(
                metadata, Path("/opt/homebrew/Cellar/gh/1/bin/gh"), os.geteuid()
            )
        )
        metadata.st_uid = os.geteuid()
        metadata.st_nlink = 2
        self.assertFalse(
            recreate_bootstrap._credential_source_metadata_is_allowed(
                metadata, Path("/opt/homebrew/Cellar/gh/1/bin/gh"), os.geteuid()
            )
        )

    @unittest.skipUnless(os.name == "posix", "POSIX credential path authority")
    def test_gh_authority_rejects_cross_user_writable_ancestor(self):
        with tempfile.TemporaryDirectory(dir=SCRIPT.parent) as directory:
            shared = Path(directory) / "shared"
            shared.mkdir(mode=0o700)
            executable = shared / "bin" / "gh"
            executable.parent.mkdir()
            executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            executable.chmod(0o700)
            shared.chmod(0o777)
            try:
                self.assertIsNone(
                    recreate_bootstrap._trusted_credential_executable(executable)
                )
            finally:
                shared.chmod(0o700)

    @unittest.skipUnless(os.name == "posix", "POSIX credential path authority")
    def test_gh_authority_rejects_foreign_owned_leaf(self):
        with tempfile.TemporaryDirectory(dir=SCRIPT.parent) as directory:
            executable = Path(directory) / "gh"
            executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            executable.chmod(0o700)
            foreign_euid = os.geteuid() + 1
            with patch.object(
                recreate_bootstrap,
                "_trusted_posix_path_chain",
                return_value=True,
            ), patch.object(recreate_bootstrap.os, "geteuid", return_value=foreign_euid):
                self.assertIsNone(
                    recreate_bootstrap._trusted_credential_executable(executable)
                )

    @unittest.skipUnless(os.name == "posix", "POSIX process-group termination")
    def test_timed_out_update_kills_its_descendant_process_group(self):
        with tempfile.TemporaryDirectory() as directory:
            descendant_pid_file = Path(directory) / "descendant.pid"
            command = [
                "/bin/sh",
                "-c",
                '/bin/sleep 60 & child=$!; printf "%s\\n" "$child" > "$1"; wait',
                "submodule-update-fixture",
                str(descendant_pid_file),
            ]
            with self.assertRaises(subprocess.TimeoutExpired):
                recreate_bootstrap._run_submodule_update_process(
                    command,
                    environment={"PATH": recreate_bootstrap.CONTROLLED_GIT_PATH},
                    timeout_seconds=0.5,
                    credential_gh=None,
                )
            self.assertTrue(descendant_pid_file.is_file())
            descendant_pid = int(descendant_pid_file.read_text(encoding="utf-8").strip())

            def descendant_is_alive() -> bool:
                try:
                    os.kill(descendant_pid, 0)
                except ProcessLookupError:
                    return False
                process_stat = Path(f"/proc/{descendant_pid}/stat")
                if process_stat.is_file():
                    fields = process_stat.read_text(encoding="utf-8").split()
                    if len(fields) > 2 and fields[2] == "Z":
                        return False
                return True

            deadline = time.monotonic() + 2
            while descendant_is_alive() and time.monotonic() < deadline:
                time.sleep(0.02)
            self.assertFalse(
                descendant_is_alive(),
                "a timed-out update left its transport/helper descendant alive",
            )

    @unittest.skipUnless(os.name == "posix", "POSIX post-success process group")
    def test_successful_git_leader_cannot_leave_background_descendant(self):
        with tempfile.TemporaryDirectory() as directory:
            descendant_pid_file = Path(directory) / "descendant.pid"
            command = [
                "/bin/sh",
                "-c",
                '/bin/sleep 60 & child=$!; printf "%s\\n" "$child" > "$1"; exit 0',
                "submodule-update-fixture",
                str(descendant_pid_file),
            ]
            result = recreate_bootstrap._run_submodule_update_process(
                command,
                environment={"PATH": recreate_bootstrap.CONTROLLED_GIT_PATH},
                timeout_seconds=5,
                credential_gh=None,
            )
            self.assertEqual(result.returncode, 0)
            descendant_pid = int(
                descendant_pid_file.read_text(encoding="utf-8").strip()
            )
            deadline = time.monotonic() + 2
            while time.monotonic() < deadline:
                try:
                    os.kill(descendant_pid, 0)
                except ProcessLookupError:
                    break
                time.sleep(0.02)
            else:
                self.fail(
                    "a successful Git leader left its background descendant alive"
                )

    def test_interrupted_update_terminates_process_tree_before_reraising(self):
        process = SimpleNamespace(
            pid=424242,
            stdout=io.BytesIO(),
        )
        with patch.object(
            recreate_bootstrap.subprocess, "Popen", return_value=process
        ), patch.object(
            recreate_bootstrap,
            "_wait_submodule_process_group",
            side_effect=KeyboardInterrupt,
        ), patch.object(
            recreate_bootstrap, "_terminate_submodule_process_tree"
        ) as terminate, self.assertRaises(KeyboardInterrupt):
            recreate_bootstrap._run_submodule_update_process(
                ["/fixed/git", "submodule", "update"],
                environment={"PATH": recreate_bootstrap.CONTROLLED_GIT_PATH},
                timeout_seconds=1,
                credential_gh=None,
            )
        terminate.assert_called_once_with(process)

    def test_submodule_child_diagnostics_are_byte_bounded_and_drained(self):
        diagnostics = io.StringIO()
        command = [
            sys.executable,
            "-c",
            "import sys; sys.stdout.write('A' * 256)",
        ]
        with patch.object(
            recreate_bootstrap,
            "SUBMODULE_UPDATE_OUTPUT_LIMIT_BYTES",
            32,
        ), patch.object(recreate_bootstrap.sys, "stderr", diagnostics):
            result = recreate_bootstrap._run_submodule_update_process(
                command,
                environment={"PATH": recreate_bootstrap.CONTROLLED_GIT_PATH},
                timeout_seconds=10,
                credential_gh=None,
            )
        self.assertEqual(result.returncode, 0)
        rendered = diagnostics.getvalue()
        self.assertEqual(rendered.count("A"), 32)
        self.assertIn("diagnostic output truncated after 32 bytes", rendered)

    def test_update_auth_is_command_scoped_bounded_and_not_persisted(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            real_update = recreate_bootstrap._run_submodule_update_process
            updates: list[tuple[list[str], dict[str, object]]] = []
            credential_snapshot_directories: list[Path] = []

            def run_update(command, **kwargs):
                updates.append((command, kwargs.copy()))
                with patch.object(
                    recreate_bootstrap,
                    "_revalidate_credential_gh_executable",
                ) as revalidate:
                    result = real_update(command, **kwargs)
                self.assertEqual(revalidate.call_count, 2)
                return result

            def credential_helper(snapshot_directory):
                credential_snapshot_directories.append(snapshot_directory)
                return Path("/mock/read-only-gh")

            test_overrides = recreate_bootstrap.CONTROLLED_GIT_CONFIG_OVERRIDES + (
                "protocol.file.allow=always",
            )
            hostile = {
                "HOME": str(Path(directory) / "credential-home"),
                "GH_TOKEN": "ambient-token-must-not-cross",
            }
            with patch.dict(os.environ, hostile, clear=False), patch.object(
                recreate_bootstrap,
                "CONTROLLED_GIT_CONFIG_OVERRIDES",
                test_overrides,
            ), patch.object(
                recreate_bootstrap,
                "_submodule_url_is_allowed",
                return_value=True,
            ), patch.object(
                recreate_bootstrap,
                "_credential_gh_executable",
                side_effect=credential_helper,
            ), patch.object(
                recreate_bootstrap,
                "_run_submodule_update_process",
                side_effect=run_update,
            ):
                recreate_bootstrap.ensure_submodules(checkout)

            self.assertTrue(updates)
            self.assertTrue(credential_snapshot_directories)
            self.assertTrue(
                all(
                    not directory.exists()
                    for directory in credential_snapshot_directories
                )
            )
            for command, kwargs in updates:
                self.assertEqual(
                    kwargs["timeout_seconds"],
                    recreate_bootstrap.SUBMODULE_UPDATE_TIMEOUT_SECONDS,
                )
                self.assertEqual(
                    kwargs["credential_gh"], Path("/mock/read-only-gh")
                )
                self.assertIn("credential.interactive=always", command)
                helper = next(
                    part for part in command if part.startswith("credential.helper=!")
                )
                self.assertIn('test "$1" = get', helper)
                self.assertNotIn("ambient-token-must-not-cross", command)
                update_env = kwargs["environment"]
                assert isinstance(update_env, dict)
                self.assertNotIn("GH_TOKEN", update_env)
                self.assertEqual(
                    update_env["GIT_CONFIG_GLOBAL"], os.devnull
                )

            for repository in (
                checkout,
                checkout / "first-party" / "ay",
                checkout / "first-party" / "clean",
            ):
                local = self.git(repository, "config", "--local", "--list").stdout.lower()
                self.assertNotIn("credential.", local)
                self.assertNotIn("extraheader", local)

    def test_timeout_fails_closed_and_scrubs_remote_credentials(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            credential_snapshot_directories: list[Path] = []
            self.git(
                checkout,
                "remote",
                "set-url",
                "origin",
                "https://user:secret@example.invalid/trust.git",
            )
            def run_update(command, **kwargs):
                self.assertEqual(
                    kwargs.get("timeout_seconds"),
                    recreate_bootstrap.SUBMODULE_UPDATE_TIMEOUT_SECONDS,
                )
                raise subprocess.TimeoutExpired(
                    command, recreate_bootstrap.SUBMODULE_UPDATE_TIMEOUT_SECONDS
                )

            def credential_helper(snapshot_directory):
                credential_snapshot_directories.append(snapshot_directory)
                helper = snapshot_directory / "gh-credential-helper"
                helper.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                helper.chmod(0o700)
                return helper

            test_overrides = recreate_bootstrap.CONTROLLED_GIT_CONFIG_OVERRIDES + (
                "protocol.file.allow=always",
            )
            with patch.object(
                recreate_bootstrap,
                "CONTROLLED_GIT_CONFIG_OVERRIDES",
                test_overrides,
            ), patch.object(
                recreate_bootstrap,
                "_submodule_url_is_allowed",
                return_value=True,
            ), patch.object(
                recreate_bootstrap,
                "_credential_gh_executable",
                side_effect=credential_helper,
            ), patch.object(
                recreate_bootstrap,
                "_run_submodule_update_process",
                side_effect=run_update,
            ), self.assertRaisesRegex(
                RuntimeError,
                r"timed out after 600s.*gh auth status",
            ):
                recreate_bootstrap.ensure_submodules(checkout)

            self.assertTrue(credential_snapshot_directories)
            self.assertTrue(
                all(
                    not snapshot_directory.exists()
                    for snapshot_directory in credential_snapshot_directories
                )
            )

            self.assertEqual(
                self.git(checkout, "remote", "get-url", "origin").stdout.strip(),
                "https://example.invalid/trust.git",
            )
            states = self.git(checkout, "submodule", "status").stdout.splitlines()
            self.assertEqual([line[0] for line in states], [" ", "-"])

    def test_keyboard_interrupt_still_runs_post_failure_remote_cleanup(self):
        interrupt = KeyboardInterrupt()
        with patch.object(
            recreate_bootstrap,
            "_submodule_materialization_environment",
            return_value={"GIT_TERMINAL_PROMPT": "0"},
        ), patch.object(
            recreate_bootstrap,
            "_submodule_auth_config",
            return_value=([], None),
        ), patch.object(
            recreate_bootstrap,
            "_initialize_missing_submodules",
            side_effect=interrupt,
        ), patch.object(
            recreate_bootstrap, "scrub_pat_from_remotes"
        ) as scrub, self.assertRaises(KeyboardInterrupt):
            recreate_bootstrap._materialize_missing_submodules(
                Path("/checkout"), Path("/private/snapshot")
            )
        scrub.assert_called_once_with(Path("/checkout"))

    def test_remote_cleanup_scrubs_every_fetch_and_push_url(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "remote-cleanup-fixture")
            self.git(
                repository,
                "remote",
                "add",
                "origin",
                "https://first:secret-one@github.com/example/one.git",
            )
            self.git(
                repository,
                "config",
                "--add",
                "remote.origin.url",
                "https://second:secret-two@github.com/example/two.git",
            )
            for url in (
                "https://push-one:secret-three@github.com/example/one.git",
                "https://push-two:secret-four@github.com/example/two.git",
            ):
                self.git(
                    repository,
                    "config",
                    "--add",
                    "remote.origin.pushurl",
                    url,
                )

            recreate_bootstrap.scrub_pat_from_remotes(repository)

            fetch_urls = self.git(
                repository, "config", "--get-all", "remote.origin.url"
            ).stdout.splitlines()
            push_urls = self.git(
                repository, "config", "--get-all", "remote.origin.pushurl"
            ).stdout.splitlines()
            self.assertEqual(
                fetch_urls,
                [
                    "https://github.com/example/one.git",
                    "https://github.com/example/two.git",
                ],
            )
            self.assertEqual(
                push_urls,
                [
                    "https://github.com/example/one.git",
                    "https://github.com/example/two.git",
                ],
            )

    def test_remote_cleanup_rejects_query_credentials_without_echoing_them(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "remote-query-fixture")
            secret = "query-secret-must-not-appear"
            self.git(
                repository,
                "remote",
                "add",
                "origin",
                f"https://github.com/example/repo.git?token={secret}",
            )
            with self.assertRaisesRegex(
                RuntimeError, r"query or fragment"
            ) as raised:
                recreate_bootstrap.scrub_pat_from_remotes(repository)
            self.assertNotIn(secret, str(raised.exception))

    def test_indexed_credential_url_is_rejected_before_update_or_disclosure(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            secret = "indexed-secret-must-not-appear"
            self.git(
                checkout,
                "config",
                "-f",
                str(checkout / ".gitmodules"),
                "submodule.first-party/clean.url",
                f"https://user:{secret}@github.com/alabsystems/clean.git",
            )
            self.git(checkout, "add", ".gitmodules")
            real_policy = recreate_bootstrap._submodule_url_is_allowed

            def fixture_policy(value):
                return value.startswith("/") or real_policy(value)

            stdout = io.StringIO()
            stderr = io.StringIO()
            with patch.object(
                recreate_bootstrap,
                "_submodule_url_is_allowed",
                side_effect=fixture_policy,
            ), patch.object(
                recreate_bootstrap,
                "_run_submodule_update_process",
            ) as update, patch.object(
                recreate_bootstrap.sys, "stdout", stdout
            ), patch.object(
                recreate_bootstrap.sys, "stderr", stderr
            ), self.assertRaisesRegex(
                RuntimeError, r"unsafe indexed submodule URL"
            ) as raised:
                recreate_bootstrap.ensure_submodules(checkout)

            update.assert_not_called()
            disclosed = stdout.getvalue() + stderr.getvalue() + str(raised.exception)
            self.assertNotIn(secret, disclosed)
            self.assertNotIn(
                "submodule.first-party/clean.url",
                self.git(checkout, "config", "--local", "--list").stdout,
            )

    def test_indexed_custom_update_is_rejected_before_process_launch(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            marker = Path(directory) / "indexed-update-ran"
            self.git(
                checkout,
                "config",
                "-f",
                str(checkout / ".gitmodules"),
                "submodule.first-party/clean.update",
                f"!touch {marker}",
            )
            self.git(checkout, "add", ".gitmodules")
            with patch.object(
                recreate_bootstrap,
                "_submodule_url_is_allowed",
                return_value=True,
            ), patch.object(
                recreate_bootstrap,
                "_run_submodule_update_process",
            ) as update, self.assertRaisesRegex(
                RuntimeError, r"custom indexed submodule update authority"
            ):
                recreate_bootstrap.ensure_submodules(checkout)
            update.assert_not_called()
            self.assertFalse(marker.exists())

    def test_hostile_local_update_command_is_rejected_before_initialization(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            marker = Path(directory) / "update-command-executed"
            self.git(
                checkout,
                "config",
                "submodule.first-party/clean.update",
                f"!touch {marker}",
            )
            test_overrides = recreate_bootstrap.CONTROLLED_GIT_CONFIG_OVERRIDES + (
                "protocol.file.allow=always",
            )
            with patch.object(
                recreate_bootstrap,
                "CONTROLLED_GIT_CONFIG_OVERRIDES",
                test_overrides,
            ), patch.object(
                recreate_bootstrap,
                "_submodule_url_is_allowed",
                return_value=True,
            ), self.assertRaisesRegex(RuntimeError, r"submodule\..*\.update"):
                recreate_bootstrap.ensure_submodules(checkout)
            self.assertFalse(marker.exists())

    def test_local_hooks_and_executable_helpers_are_rejected(self):
        hostile_settings = (
            ("core.hooksPath", "/tmp/hostile-hooks"),
            ("credential.helper", "!touch /tmp/credential-helper-ran"),
            ("http.https://github.com/.extraHeader", "Authorization: secret"),
            ("http.https://github.com.sslVerify", "false"),
            ("HTTP.https://github.com.Proxy", "http://127.0.0.1:9"),
            ("http.https://github.com.cookieFile", "/tmp/private-cookie-jar"),
            ("http.cookieFile", "/tmp/private-cookie-jar"),
            ("protocol.ftp.allow", "always"),
            ("url.https://evil.invalid/.insteadOf", "https://github.com/"),
            ("filter.attack.smudge", "touch /tmp/filter-ran"),
            ("diff.attack.textconv", "touch /tmp/textconv-ran"),
            ("init.templateDir", "/tmp/hostile-template"),
            ("include.path", "/tmp/hostile-git-config"),
        )
        for key, value in hostile_settings:
            with self.subTest(key=key), tempfile.TemporaryDirectory() as directory:
                repository = Path(directory) / "repository"
                self.create_repository(repository, "local-authority-fixture")
                self.git(repository, "config", key, value)
                with self.assertRaisesRegex(RuntimeError, r"hidden execution"):
                    recreate_bootstrap._run_git_read(
                        repository, ["rev-parse", "--verify", "HEAD"]
                    )

    def test_worktree_config_scope_is_inspected_redacted_and_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "worktree-authority-fixture")
            secret = "worktree-secret-must-not-appear"
            self.git(repository, "config", "extensions.worktreeConfig", "true")
            self.git(
                repository,
                "config",
                "--worktree",
                "credential.https://user:" + secret + "@github.com.helper",
                "!hostile-helper",
            )
            with self.assertRaisesRegex(
                RuntimeError, r"extensions\.worktreeconfig"
            ) as raised:
                recreate_bootstrap._run_git_read(
                    repository, ["rev-parse", "--verify", "HEAD"]
                )
            diagnostic = str(raised.exception)
            self.assertNotIn(secret, diagnostic)
            self.assertIn("worktree:credential.<redacted>.helper", diagnostic)

    def test_empty_url_scoped_credential_config_is_still_authority(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "empty-credential-fixture")
            self.git(
                repository,
                "config",
                "credential.https://github.com.helper",
                "",
            )
            with self.assertRaisesRegex(RuntimeError, r"credential\.<redacted>\.helper"):
                recreate_bootstrap._run_git_read(
                    repository, ["rev-parse", "--verify", "HEAD"]
                )

    def test_dirty_tracked_lockfile_is_preserved_and_blocks_initialization(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            lockfile = checkout / "first-party" / "ay" / "Cargo.lock"
            changed = b"# irreplaceable user lockfile edit\n"
            lockfile.write_bytes(changed)

            with patch.object(
                recreate_bootstrap,
                "_submodule_url_is_allowed",
                return_value=True,
            ), self.assertRaisesRegex(
                RuntimeError,
                r"(?s)tracked Cargo\.lock changes.*first-party/ay/Cargo\.lock",
            ):
                recreate_bootstrap.ensure_submodules(checkout)

            self.assertEqual(lockfile.read_bytes(), changed)
            states = self.git(checkout, "submodule", "status").stdout.splitlines()
            self.assertEqual([line[0] for line in states], [" ", "-"])


class AyInstallProvenanceTests(unittest.TestCase):
    host = "test-host"

    def layout(self, directory: str):
        root = Path(directory)
        bindir = root / "build" / self.host / "stage2" / "bin"
        producer_dir = root / "build" / self.host / "stage3-tools-bin" / self.host
        bindir.mkdir(parents=True)
        producer_dir.mkdir(parents=True)
        (bindir / "trustc").write_bytes(b"trustc")
        return root, bindir, producer_dir

    def test_existing_bootstrap_hardlink_is_never_copied_through(self):
        with tempfile.TemporaryDirectory() as directory:
            root, bindir, producer_dir = self.layout(directory)
            producer = producer_dir / "ay"
            producer.write_bytes(b"trust-built-ay")
            os.link(producer, bindir / "ay")
            before_inode = producer.stat().st_ino

            with patch.object(recreate_bootstrap.subprocess, "run") as run:
                self.assertTrue(recreate_bootstrap.install_ay_solver(root, self.host, 2))
            run.assert_not_called()
            self.assertEqual(producer.read_bytes(), b"trust-built-ay")
            self.assertEqual(producer.stat().st_ino, before_inode)
            self.assertTrue(os.path.samefile(producer, bindir / "ay"))

    def test_displaced_hardlink_is_unlinked_before_restoring_producer(self):
        with tempfile.TemporaryDirectory() as directory:
            root, bindir, producer_dir = self.layout(directory)
            producer = producer_dir / "ay"
            producer.write_bytes(b"trust-built-ay")
            displaced_cache = root / "ambient-ay-cache"
            displaced_cache.write_bytes(b"ambient-ay")
            os.link(displaced_cache, bindir / "ay")

            self.assertTrue(recreate_bootstrap.install_ay_solver(root, self.host, 2))
            self.assertEqual((bindir / "ay").read_bytes(), b"trust-built-ay")
            self.assertEqual(producer.read_bytes(), b"trust-built-ay")
            self.assertEqual(displaced_cache.read_bytes(), b"ambient-ay")
            self.assertFalse(os.path.samefile(displaced_cache, bindir / "ay"))

    def test_missing_producer_fallback_uses_exact_stage_toolchain_and_lock(self):
        with tempfile.TemporaryDirectory() as directory:
            root, bindir, _producer_dir = self.layout(directory)
            targo = bindir / "targo"
            targo.write_bytes(b"targo")
            ay_dir = root / "first-party" / "ay"
            ay_dir.mkdir(parents=True)

            def build(command, *, cwd, env):
                self.assertEqual(command[0], str(targo))
                self.assertIn("--locked", command)
                self.assertEqual(env["RUSTC"], str(bindir / "trustc"))
                self.assertEqual(env["PATH"].split(os.pathsep)[0], str(bindir))
                self.assertEqual(Path(cwd), ay_dir)
                output = ay_dir / "target" / "release" / "ay"
                output.parent.mkdir(parents=True)
                output.write_bytes(b"stage2-built-ay")
                return SimpleNamespace(returncode=0)

            with patch.object(recreate_bootstrap, "add_homebrew_library_path"), patch.object(
                recreate_bootstrap.subprocess, "run", side_effect=build
            ):
                self.assertTrue(recreate_bootstrap.install_ay_solver(root, self.host, 2))
            self.assertEqual((bindir / "ay").read_bytes(), b"stage2-built-ay")


class StageToolProvenanceTests(unittest.TestCase):
    host = "test-host"
    commit = "1" * 40

    @staticmethod
    def executable(path: Path, payload: bytes) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)
        path.chmod(path.stat().st_mode | stat.S_IXUSR)

    def layout(self, directory: str):
        root = Path(directory)
        stage_root = root / "build" / self.host / "stage2"
        bindir = stage_root / "bin"
        tools_dir = root / "build" / self.host / "stage3-tools-bin" / self.host
        for public, producer in recreate_bootstrap.STAGE_TOOL_PRODUCERS.items():
            producer_path = tools_dir / producer
            if not producer_path.exists():
                self.executable(producer_path, f"producer:{producer}".encode())
            installed = bindir / public
            installed.parent.mkdir(parents=True, exist_ok=True)
            os.link(producer_path, installed)
        stage1_trustc = root / "build" / self.host / "stage1" / "bin" / "trustc"
        stage2_trustc = bindir / "trustc"
        self.executable(stage1_trustc, b"stage1-trustc")
        self.executable(stage2_trustc, b"stage2-trustc")
        os.link(stage2_trustc, bindir / "rustc")
        helper_producer = tools_dir / "rust-analyzer-proc-macro-srv"
        self.executable(helper_producer, b"proc-macro-helper")
        owned_helper = stage_root / "libexec" / "trust-analyzer-proc-macro-srv"
        owned_helper.parent.mkdir(parents=True)
        os.link(helper_producer, owned_helper)
        return root, stage_root, bindir, tools_dir

    def identity_capture(self, stage_root: Path):
        def capture(path: Path, args: tuple[str, ...]):
            if args == ("-Vv",):
                return True, f"trustc 1.99.0\ncommit-hash: {self.commit}\nhost: {self.host}"
            if args == ("--print", "sysroot"):
                return True, str(stage_root)
            return True, f"{path.name} test-version"
        return capture

    def lineage(self, status: str = "immutable_release", digest: str = "a" * 64):
        return {
            "schema": "trust.source-lineage.v1",
            "status": status,
            "source_tree_clean": status == "immutable_release",
            "closure_sha256": digest,
            "submodule_status_sha256": "b" * 64,
            "repositories": [{"path": ".", "head": self.commit}],
            "errors": [],
        }

    @staticmethod
    def bootstrap_lineage(
        status: str = "trust_from_trust",
        digest: str = "d" * 64,
        *,
        hydrated: bool = True,
        admission_status: str = "public-promoted",
    ):
        mode = "seed" if status == "trust_from_trust" else "genesis"
        if mode == "seed":
            compiler = (
                {
                    "schema": "trust.seed-compiler-identity.v1",
                    "status": "validated",
                    "stage0_root": "build/test-host/stage0",
                    "stage0_root_present": True,
                    "tools": [],
                    "forbidden_paths_present": [],
                    "stage0_tree": {
                        "schema": "trust.seed-stage0-tree.v1",
                        "closure_sha256": "e" * 64,
                    },
                    "reported_sysroot_matches": True,
                    "errors": [],
                }
                if hydrated
                else {
                    "schema": "trust.seed-compiler-identity.v1",
                    "status": "not-materialized",
                    "stage0_root": "build/test-host/stage0",
                    "stage0_root_present": False,
                    "tools": [],
                    "forbidden_paths_present": [],
                    "stage0_tree": None,
                    "errors": [],
                }
            )
            validated_seed = {
                "schema": "trust.validated-seed-lineage.v1",
                "status": "validated" if hydrated else "validated-payloads",
                "admission_status": admission_status,
                "authority_sha256": "f" * 64,
                "authority": {"schema": "trust.seed-authority.v1"},
                "compiler": compiler,
                "errors": [],
            }
            genesis_adapter = None
        else:
            validated_seed = None
            genesis_adapter = {
                "schema": "trust.genesis-adapter-authority.v1",
                "status": "ready",
                "authority_sha256": "9" * 64,
                "authority": {"schema": "trust.genesis-adapter-authority.v1"},
                "errors": [],
            }
        return {
            "schema": "trust.bootstrap-lineage.v1",
            "status": status,
            "mode": mode,
            "trust_from_trust": status == "trust_from_trust",
            "config_path": "bootstrap.toml",
            "config_sha256": digest,
            "declared_stage0_overrides": (
                []
                if mode == "seed"
                else ["cargo", "cargo-clippy", "rustc", "rustdoc", "rustfmt"]
            ),
            "validated_seed": validated_seed,
            "genesis_adapter": genesis_adapter,
            "errors": [],
        }

    @staticmethod
    def build_authority(digest: str = "8" * 64):
        return {
            "schema": "trust.build-authority.v1",
            "status": "ready",
            "host": "test-host",
            "ambient_overrides": {},
            "ambient_cargo_configs": [],
            "native_tools": [],
            "selected_llvm": None,
            "platform_toolchain": None,
            "sdk": {"platform": "test", "status": "system-native"},
            "dynamic_dependencies": None,
            "derived_library_paths": [],
            "authority_sha256": digest,
            "errors": [],
        }

    def run_audit(
        self,
        root: Path,
        stage_root: Path,
        *,
        before=None,
        after=None,
        bootstrap_before=None,
        bootstrap_after=None,
    ):
        before = self.lineage() if before is None else before
        after = before if after is None else after
        if bootstrap_before is None:
            bootstrap_before = self.bootstrap_lineage(hydrated=False)
            if bootstrap_after is None:
                bootstrap_after = self.bootstrap_lineage(hydrated=True)
        elif bootstrap_after is None:
            bootstrap_after = bootstrap_before
        build_authority = self.build_authority()
        with patch.object(
            recreate_bootstrap,
            "_capture_identity",
            side_effect=self.identity_capture(stage_root),
        ), patch.object(
            recreate_bootstrap, "capture_source_lineage", return_value=after
        ), patch.object(
            recreate_bootstrap,
            "capture_bootstrap_lineage",
            return_value=bootstrap_after,
        ), patch.object(
            recreate_bootstrap,
            "capture_build_authority",
            return_value=build_authority,
        ):
            return recreate_bootstrap.audit_stage_tool_provenance(
                root,
                self.host,
                2,
                before,
                bootstrap_before,
                build_authority,
            )

    def verify_receipt(
        self,
        root: Path,
        stage_root: Path,
        lineage,
        *,
        bootstrap=None,
        require_immutable_lineage: bool = False,
        require_public_release: bool = False,
    ):
        bootstrap = self.bootstrap_lineage() if bootstrap is None else bootstrap
        build_authority = self.build_authority()
        with patch.object(
            recreate_bootstrap,
            "_capture_identity",
            side_effect=self.identity_capture(stage_root),
        ), patch.object(
            recreate_bootstrap, "capture_source_lineage", return_value=lineage
        ), patch.object(
            recreate_bootstrap, "capture_bootstrap_lineage", return_value=bootstrap
        ), patch.object(
            recreate_bootstrap,
            "capture_build_authority",
            return_value=build_authority,
        ):
            return recreate_bootstrap.verify_stage_tool_provenance(
                root,
                self.host,
                2,
                require_immutable_lineage=require_immutable_lineage,
                require_public_release=require_public_release,
            )

    def test_every_public_tool_is_bound_to_its_bootstrap_producer(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage_root))
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["schema"], "trust.stage-tool-provenance.v2")
            self.assertEqual(
                receipt["bootstrap_compiler_verification"],
                {
                    "mode": "disabled",
                    "flag": "-Ztrust-verify=off",
                    "reason": "bootstrap stability",
                    "counts_as_self_proof": False,
                },
            )
            self.assertEqual(receipt["status"], "release-ready")
            self.assertEqual(receipt["tool_binding_status"], "ready")
            self.assertTrue(receipt["source_tree_clean"])
            self.assertTrue(receipt["trust_from_trust"])
            self.assertEqual(
                {tool["name"] for tool in receipt["tools"]},
                set(recreate_bootstrap.STAGE_TOOL_PRODUCERS),
            )
            self.assertTrue(all(tool["status"] == "bound" for tool in receipt["tools"]))
            self.assertTrue(all(tool["producer_stage"] == 3 for tool in receipt["tools"]))
            self.assertTrue(
                all(tool["producer_compiler_stage"] == 2 for tool in receipt["tools"])
            )
            self.assertTrue(
                all(
                    tool["producer_path"].startswith(
                        f"build/{self.host}/stage3-tools-bin/{self.host}/"
                    )
                    for tool in receipt["tools"]
                )
            )
            self.assertTrue(receipt["compiler"]["compatibility_alias_same_inode"])
            self.assertTrue(receipt["proc_macro_helper"]["retired_public_path_absent"])
            receipt_path = stage_root / "tool-provenance.json"
            before_verify = receipt_path.read_bytes()
            self.assertTrue(self.verify_receipt(root, stage_root, self.lineage()))
            self.assertTrue(
                self.verify_receipt(
                    root,
                    stage_root,
                    self.lineage(),
                    require_immutable_lineage=True,
                    require_public_release=True,
                )
            )
            self.assertEqual(receipt_path.read_bytes(), before_verify)

    def test_internal_seed_is_immutable_but_not_public_release(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            before = self.bootstrap_lineage(
                hydrated=False,
                admission_status="internal-admitted",
            )
            after = self.bootstrap_lineage(
                hydrated=True,
                admission_status="internal-admitted",
            )
            self.assertTrue(
                self.run_audit(
                    root,
                    stage_root,
                    bootstrap_before=before,
                    bootstrap_after=after,
                )
            )
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["status"], "internal-release-ready")
            self.assertTrue(
                self.verify_receipt(
                    root,
                    stage_root,
                    self.lineage(),
                    bootstrap=after,
                    require_immutable_lineage=True,
                )
            )
            self.assertFalse(
                self.verify_receipt(
                    root,
                    stage_root,
                    self.lineage(),
                    bootstrap=after,
                    require_public_release=True,
                )
            )

    def test_preexisting_internal_seed_stays_candidate_ready(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            preexisting = self.bootstrap_lineage(
                hydrated=True,
                admission_status="internal-admitted",
            )
            self.assertTrue(
                self.run_audit(
                    root,
                    stage_root,
                    bootstrap_before=preexisting,
                    bootstrap_after=preexisting,
                )
            )
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["status"], "candidate-ready")
            self.assertEqual(
                receipt["bootstrap_lineage"]["validated_seed"][
                    "materialization_status"
                ],
                "preexisting-unproven",
            )
            self.assertFalse(
                self.verify_receipt(
                    root,
                    stage_root,
                    self.lineage(),
                    bootstrap=preexisting,
                    require_immutable_lineage=True,
                )
            )

    def test_changed_final_tool_rejects_the_entire_stage(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, bindir, _tools_dir = self.layout(directory)
            installed = bindir / "ay"
            installed.unlink()
            self.executable(installed, b"ambient-replacement")
            self.assertFalse(self.run_audit(root, stage_root))
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["status"], "rejected")
            self.assertTrue(any("ay" in error for error in receipt["errors"]))

    def test_staged_source_is_visible_candidate_and_never_release_ready(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            lineage = self.lineage("staged_proposal")
            self.assertTrue(self.run_audit(root, stage_root, before=lineage))
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["status"], "candidate-ready")
            self.assertFalse(receipt["source_tree_clean"])
            self.assertTrue(self.verify_receipt(root, stage_root, lineage))
            self.assertFalse(
                self.verify_receipt(
                    root, stage_root, lineage, require_immutable_lineage=True
                )
            )

    def test_local_genesis_is_candidate_even_with_clean_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            source = self.lineage()
            genesis = self.bootstrap_lineage("local_genesis")
            self.assertTrue(
                self.run_audit(
                    root,
                    stage_root,
                    before=source,
                    bootstrap_before=genesis,
                )
            )
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["status"], "candidate-ready")
            self.assertTrue(receipt["source_tree_clean"])
            self.assertFalse(receipt["trust_from_trust"])
            self.assertTrue(
                self.verify_receipt(root, stage_root, source, bootstrap=genesis)
            )
            self.assertFalse(
                self.verify_receipt(
                    root,
                    stage_root,
                    source,
                    bootstrap=genesis,
                    require_immutable_lineage=True,
                )
            )

    def test_read_only_verifier_rejects_source_drift_and_tool_replacement(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, bindir, _tools_dir = self.layout(directory)
            lineage = self.lineage()
            self.assertTrue(self.run_audit(root, stage_root, before=lineage))
            receipt_path = stage_root / "tool-provenance.json"
            original_receipt = receipt_path.read_bytes()
            drifted = self.lineage(digest="c" * 64)
            self.assertFalse(self.verify_receipt(root, stage_root, drifted))
            self.assertEqual(receipt_path.read_bytes(), original_receipt)
            installed = bindir / "ay"
            installed.unlink()
            self.executable(installed, b"post-receipt-replacement")
            self.assertFalse(self.verify_receipt(root, stage_root, lineage))
            self.assertEqual(receipt_path.read_bytes(), original_receipt)

    def test_read_only_verifier_rejects_forged_receipt_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            lineage = self.lineage()
            self.assertTrue(self.run_audit(root, stage_root, before=lineage))
            receipt_path = stage_root / "tool-provenance.json"
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["tools"][0]["version"] = "forged version"
            receipt["proc_macro_helper"]["status"] = "forged"
            receipt["compiler"]["reported_sysroot_path_scope"] = "portable"
            receipt["source_lineage"]["source_tree_clean"] = False
            receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
            forged_receipt = receipt_path.read_bytes()
            self.assertFalse(self.verify_receipt(root, stage_root, lineage))
            self.assertEqual(receipt_path.read_bytes(), forged_receipt)

    def test_verifier_requires_exact_bootstrap_compiler_verification_disclosure(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            lineage = self.lineage()
            self.assertTrue(self.run_audit(root, stage_root, before=lineage))
            receipt_path = stage_root / "tool-provenance.json"
            original = json.loads(receipt_path.read_text(encoding="utf-8"))

            forged_claim = {
                **recreate_bootstrap.BOOTSTRAP_COMPILER_VERIFICATION,
                "counts_as_self_proof": True,
            }
            for replacement in (None, False, forged_claim):
                receipt = dict(original)
                if replacement is None:
                    receipt.pop("bootstrap_compiler_verification")
                else:
                    receipt["bootstrap_compiler_verification"] = replacement
                receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
                self.assertFalse(self.verify_receipt(root, stage_root, lineage))


class SourceLineageTests(unittest.TestCase):
    @staticmethod
    def git(root: Path, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["git", "-C", str(root), *args],
            check=True,
            capture_output=True,
            text=True,
        )

    def initialized_repository(self, directory: str) -> tuple[Path, Path]:
        root = Path(directory)
        self.git(root, "init")
        self.git(root, "config", "user.email", "trust-test@example.invalid")
        self.git(root, "config", "user.name", "Trust Test")
        tracked = root / "tracked.txt"
        tracked.write_text("committed\n", encoding="utf-8")
        self.git(root, "add", "tracked.txt")
        self.git(root, "commit", "-m", "fixture")
        return root, tracked

    def test_clean_and_staged_source_lineage_are_distinct(self):
        with tempfile.TemporaryDirectory() as directory:
            root, tracked = self.initialized_repository(directory)
            clean = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(clean["status"], "immutable_release")
            self.assertTrue(clean["source_tree_clean"])
            self.assertEqual([row["path"] for row in clean["repositories"]], ["."])

            tracked.write_text("staged\n", encoding="utf-8")
            self.git(root, "add", "tracked.txt")
            staged = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(staged["status"], "staged_proposal")
            self.assertFalse(staged["source_tree_clean"])
            self.assertTrue(staged["repositories"][0]["has_staged_changes"])
            self.git(root, "config", "core.abbrev", "5")
            self.git(root, "config", "diff.noprefix", "true")
            config_varied = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(staged["closure_sha256"], config_varied["closure_sha256"])
            self.assertEqual(staged["repositories"], config_varied["repositories"])

    def test_unstaged_or_untracked_source_lineage_rejects(self):
        with tempfile.TemporaryDirectory() as directory:
            root, tracked = self.initialized_repository(directory)
            tracked.write_text("unstaged\n", encoding="utf-8")
            unstaged = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(unstaged["status"], "rejected")
            self.assertTrue(unstaged["repositories"][0]["has_unstaged_changes"])

        with tempfile.TemporaryDirectory() as directory:
            root, _tracked = self.initialized_repository(directory)
            (root / "untracked.txt").write_text("untracked\n", encoding="utf-8")
            untracked = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(untracked["status"], "rejected")
            self.assertEqual(
                untracked["repositories"][0]["untracked_files"][0]["path"],
                "untracked.txt",
            )

    def test_global_excludes_and_config_injection_cannot_hide_untracked_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root, _tracked = self.initialized_repository(directory)
            hidden = root / "hidden-by-global-ignore.txt"
            hidden.write_text("must remain visible\n", encoding="utf-8")
            excludes = root.parent / "global-excludes"
            excludes.write_text("hidden-by-global-ignore.txt\n", encoding="utf-8")
            global_config = root.parent / "injected-gitconfig"
            global_config.write_text(
                f"[core]\n\texcludesFile = {excludes}\n"
                "[submodule]\n\tactive = false\n",
                encoding="utf-8",
            )
            injected_env = {
                "GIT_CONFIG_GLOBAL": str(global_config),
                "GIT_CONFIG_COUNT": "1",
                "GIT_CONFIG_KEY_0": "submodule.active",
                "GIT_CONFIG_VALUE_0": "false",
            }
            with patch.dict(os.environ, injected_env, clear=False):
                lineage = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(lineage["status"], "rejected")
            self.assertEqual(
                [row["path"] for row in lineage["repositories"][0]["untracked_files"]],
                ["hidden-by-global-ignore.txt"],
            )

    def test_checkout_byte_transform_configuration_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root, _tracked = self.initialized_repository(directory)
            self.git(root, "config", "core.autocrlf", "true")
            lineage = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(lineage["status"], "rejected")
            self.assertEqual(
                lineage["repositories"][0]["checkout_policy"]["core.autocrlf"],
                "true",
            )
            self.assertTrue(
                any("core.autocrlf" in error for error in lineage["errors"])
            )

    def test_repository_owned_eol_attributes_bind_actual_checkout_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root, _tracked = self.initialized_repository(directory)
            attributes = root / ".gitattributes"
            attributes.write_text("crlf.txt text eol=crlf\n", encoding="utf-8")
            crlf = root / "crlf.txt"
            crlf.write_bytes(b"line one\nline two\n")
            self.git(root, "add", ".gitattributes", "crlf.txt")
            self.git(root, "commit", "-m", "add repository-owned CRLF fixture")
            crlf.write_bytes(b"line one\r\nline two\r\n")
            lineage = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(lineage["status"], "immutable_release")
            self.assertEqual(
                lineage["repositories"][0]["attribute_normalized_paths"],
                ["crlf.txt"],
            )

    def test_repository_local_untracked_attributes_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root, _tracked = self.initialized_repository(directory)
            info_attributes = root / ".git" / "info" / "attributes"
            info_attributes.write_text("*.txt text eol=crlf\n", encoding="utf-8")
            lineage = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(lineage["status"], "rejected")
            self.assertTrue(lineage["repositories"][0]["info_attributes_present"])

    def test_unsafe_clean_filter_is_rejected_without_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            root, tracked = self.initialized_repository(directory)
            (root / ".gitattributes").write_text(
                "tracked.txt filter=provenance-test\n",
                encoding="utf-8",
            )
            self.git(root, "add", ".gitattributes")
            self.git(root, "commit", "-m", "declare unsafe filter fixture")
            marker = root.parent / "filter-executed"
            self.git(
                root,
                "config",
                "filter.provenance-test.clean",
                f"sh -c 'touch {marker}; cat'",
            )
            tracked.write_text("raw bytes differ\n", encoding="utf-8")
            marker.unlink(missing_ok=True)
            lineage = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(lineage["status"], "rejected")
            self.assertFalse(marker.exists())
            self.assertTrue(
                any(
                    "filter.provenance-test.clean" in error
                    and "hidden execution" in error
                    for error in lineage["errors"]
                )
            )

    def test_index_shortcuts_cannot_hide_consumed_working_tree_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root, tracked = self.initialized_repository(directory)
            self.git(root, "update-index", "--assume-unchanged", "tracked.txt")
            tracked.write_text("hidden by assume-unchanged\n", encoding="utf-8")
            assumed = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(assumed["status"], "rejected")
            self.assertEqual(
                assumed["repositories"][0]["assume_unchanged_paths"],
                ["tracked.txt"],
            )
            self.assertEqual(
                assumed["repositories"][0]["working_tree_mismatch_paths"],
                ["tracked.txt"],
            )

        with tempfile.TemporaryDirectory() as directory:
            root, tracked = self.initialized_repository(directory)
            self.git(root, "update-index", "--skip-worktree", "tracked.txt")
            tracked.write_text("hidden by skip-worktree\n", encoding="utf-8")
            skipped = recreate_bootstrap.capture_source_lineage(root)
            self.assertEqual(skipped["status"], "rejected")
            self.assertEqual(
                skipped["repositories"][0]["skip_worktree_paths"],
                ["tracked.txt"],
            )
            self.assertEqual(
                skipped["repositories"][0]["working_tree_mismatch_paths"],
                ["tracked.txt"],
            )

    def test_recursive_submodule_state_is_root_relative_and_staged_only(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture_root = Path(directory)
            child = fixture_root / "child"
            child.mkdir()
            self.initialized_repository(str(child))

            parent = fixture_root / "parent"
            parent.mkdir()
            self.initialized_repository(str(parent))
            self.git(
                parent,
                "-c",
                "protocol.file.allow=always",
                "submodule",
                "add",
                str(child),
                "modules/child",
            )
            self.git(parent, "commit", "-m", "add child")

            clean = recreate_bootstrap.capture_source_lineage(parent)
            self.assertEqual(clean["status"], "immutable_release")
            self.assertEqual(
                [row["path"] for row in clean["repositories"]],
                [".", "modules/child"],
            )
            child_row = clean["repositories"][1]
            self.assertEqual(child_row["parent_repository"], ".")
            self.assertTrue(child_row["head_matches_parent_head"])
            self.assertTrue(child_row["head_matches_parent_index"])

            status_before_tag = self.git(
                parent, "submodule", "status", "--recursive"
            ).stdout
            self.git(parent / "modules" / "child", "tag", "local-only-description")
            status_after_tag = self.git(
                parent, "submodule", "status", "--recursive"
            ).stdout
            self.assertNotEqual(status_before_tag, status_after_tag)
            local_ref_only = recreate_bootstrap.capture_source_lineage(parent)
            self.assertEqual(clean["closure_sha256"], local_ref_only["closure_sha256"])
            self.assertEqual(clean["repositories"], local_ref_only["repositories"])

            checked_out_child = parent / "modules" / "child"
            (checked_out_child / "tracked.txt").write_text("staged child\n", encoding="utf-8")
            self.git(checked_out_child, "add", "tracked.txt")
            staged = recreate_bootstrap.capture_source_lineage(parent)
            self.assertEqual(staged["status"], "staged_proposal")
            self.assertTrue(staged["repositories"][1]["has_staged_changes"])


class SeedAuthorityTests(unittest.TestCase):
    version = "1.99.0-trust"
    date = "2026-07-13"

    @staticmethod
    def archive_specs():
        return (
            (
                "trustc",
                (("bin", "trustc"), ("bin", "rustc"), ("bin", "trustdoc"),
                 ("libexec", "trust-analyzer-proc-macro-srv")),
            ),
            ("targo", (("bin", "targo"), ("bin", "cargo"))),
            ("targo-trust", (("bin", "targo-trust"),)),
            ("trustfmt", (("bin", "trustfmt"), ("bin", "targo-fmt"))),
            (
                "tippy",
                (("bin", "tippy"), ("bin", "targo-tippy"), ("bin", "tippy-driver")),
            ),
            ("trust-analyzer", (("bin", "trust-analyzer"),)),
        )

    def seed_archives(self, root: Path, host: str):
        pins = {
            "compiler_version": self.version,
            "rustfmt_version": self.version,
            "compiler_date": self.date,
            "compiler_git_commit_hash": "c" * 40,
        }
        payloads = []
        date_dir = root / "bootstrap" / "trust-stage0" / "dist" / self.date
        date_dir.mkdir(parents=True)
        for component, members in self.archive_specs():
            filename = f"{component}-{self.version}-{host}.tar.xz"
            archive = date_dir / filename
            prefix = filename.removesuffix(".tar.xz")
            with tarfile.open(archive, "w:xz") as bundle:
                for destination_dir, tool in members:
                    leaf = recreate_bootstrap._host_executable(tool, host)
                    content_tool = {"rustc": "trustc", "cargo": "targo"}.get(
                        tool, tool
                    )
                    data = f"seed:{destination_dir}:{content_tool}".encode("utf-8")
                    member = tarfile.TarInfo(
                        f"{prefix}/{component}/{destination_dir}/{leaf}"
                    )
                    member.mode = 0o755
                    member.size = len(data)
                    bundle.addfile(member, io.BytesIO(data))
            payloads.append(
                {
                    "path": archive.relative_to(root).as_posix(),
                    "pinned_sha256": recreate_bootstrap._sha256_file(archive),
                    "actual_sha256": recreate_bootstrap._sha256_file(archive),
                    "matches_pin": True,
                }
            )
        # This archive shares the old prefix but must never collide with trustc.
        dev = date_dir / f"trustc-dev-{self.version}-{host}.tar.xz"
        with tarfile.open(dev, "w:xz"):
            pass
        payloads.append(
            {
                "path": dev.relative_to(root).as_posix(),
                "pinned_sha256": recreate_bootstrap._sha256_file(dev),
                "actual_sha256": recreate_bootstrap._sha256_file(dev),
                "matches_pin": True,
            }
        )
        return pins, payloads

    def test_exact_archive_names_bind_complete_posix_and_windows_surfaces(self):
        for host, executable_suffix in (
            ("test-host", ""),
            ("x86_64-pc-windows-msvc", ".exe"),
        ):
            with self.subTest(host=host), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                pins, payloads = self.seed_archives(root, host)
                errors = []
                records, bindings = recreate_bootstrap._capture_seed_archive_members(
                    root, host, pins, payloads, errors
                )
                self.assertEqual(errors, [])
                self.assertEqual(len(records), 13)
                self.assertEqual(set(bindings), {
                    *(f"bin/{name}{executable_suffix}" for name in recreate_bootstrap.SEED_STAGE0_REQUIRED_BINS),
                    *(f"libexec/{name}{executable_suffix}" for name in recreate_bootstrap.SEED_STAGE0_REQUIRED_LIBEXEC_BINS),
                })
                trustc = next(row for row in records if row["destination"] == f"bin/trustc{executable_suffix}")
                self.assertIn("/trustc/bin/trustc", trustc["member_path"].removesuffix(".exe"))
                self.assertNotIn("trustc-dev", trustc["archive_path"])

    def test_hydrated_seed_requires_every_executable_and_forbidden_absence(self):
        host = "test-host"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pins, payloads = self.seed_archives(root, host)
            errors = []
            _records, bindings = recreate_bootstrap._capture_seed_archive_members(
                root, host, pins, payloads, errors
            )
            self.assertEqual(errors, [])
            stage0 = root / "build" / host / "stage0"
            for destination, binding in bindings.items():
                path = stage0 / destination
                path.parent.mkdir(parents=True, exist_ok=True)
                archive = root / str(binding["archive_path"])
                with tarfile.open(archive, "r:xz") as bundle:
                    source = bundle.extractfile(str(binding["member_path"]))
                    assert source is not None
                    path.write_bytes(source.read())
                path.chmod(0o755)

            def identity(path: Path, args: tuple[str, ...]):
                if args == ("-Vv",):
                    return True, (
                        f"trustc {self.version}\n"
                        f"commit-hash: {'c' * 40}\nhost: {host}"
                    )
                if args == ("--print", "sysroot"):
                    return True, str(stage0)
                if path.name == "trustfmt":
                    return True, f"trustfmt {self.version}"
                return True, f"targo {self.version}"

            reported_product_identities = {
                "trustc": f"trustc {self.version}",
                "targo": f"targo {self.version}",
                "trustfmt": f"trustfmt {self.version}",
            }

            with patch.object(recreate_bootstrap, "_capture_identity", side_effect=identity):
                captured = recreate_bootstrap._capture_seed_compiler_identity(
                    root, host, pins, bindings, reported_product_identities
                )
            self.assertEqual(captured["status"], "validated")
            self.assertEqual(captured["errors"], [])
            self.assertEqual(len(captured["tools"]), 13)
            self.assertFalse((stage0 / "bin" / "rustfmt").exists())

            non_executable = stage0 / "bin" / "tippy"
            non_executable.chmod(0o644)
            with patch.object(recreate_bootstrap, "_capture_identity", side_effect=identity):
                rejected = recreate_bootstrap._capture_seed_compiler_identity(
                    root, host, pins, bindings, reported_product_identities
                )
            self.assertEqual(rejected["status"], "rejected")
            self.assertTrue(any("not executable" in error for error in rejected["errors"]))


class BuildAuthorityTests(unittest.TestCase):
    def test_clt_python_normalizes_only_exact_launcher_defaults(self):
        launcher_env = {
            "CPATH": "/usr/local/include",
            "LIBRARY_PATH": "/usr/local/lib",
            "SDKROOT": "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
            "CC": "/user/compiler",
        }
        with patch.dict(os.environ, launcher_env, clear=True), patch.object(
            recreate_bootstrap.platform, "system", return_value="Darwin"
        ), patch.object(
            recreate_bootstrap.sys,
            "executable",
            "/Library/Developer/CommandLineTools/usr/bin/python3",
        ), patch.object(
            recreate_bootstrap.sys, "version_info", (3, 11)
        ):
            recreate_bootstrap.ensure_python_311()
            self.assertNotIn("CPATH", os.environ)
            self.assertNotIn("LIBRARY_PATH", os.environ)
            self.assertNotIn("SDKROOT", os.environ)
            self.assertEqual(os.environ["CC"], "/user/compiler")

    def test_clt_python_preserves_extended_launcher_values_for_rejection(self):
        with patch.dict(
            os.environ,
            {"CPATH": "/usr/local/include:/user/include"},
            clear=True,
        ), patch.object(
            recreate_bootstrap.platform, "system", return_value="Darwin"
        ), patch.object(
            recreate_bootstrap.sys,
            "executable",
            "/Library/Developer/CommandLineTools/usr/bin/python3",
        ), patch.object(
            recreate_bootstrap.sys, "version_info", (3, 11)
        ):
            recreate_bootstrap.ensure_python_311()
            self.assertEqual(os.environ["CPATH"], "/usr/local/include:/user/include")

    def test_ambient_compiler_override_rejects_native_authority(self):
        bound = {
            "name": "tool",
            "status": "bound",
            "resolved_local_path": "/tool",
            "resolved_real_path": "/tool",
            "sha256": "a" * 64,
            "identity": "tool version",
        }
        with tempfile.TemporaryDirectory() as directory, patch.dict(
            os.environ, {"CC": "/ambient/compiler"}, clear=True
        ), patch.object(recreate_bootstrap.Path, "home", return_value=Path(directory)), patch.object(
            recreate_bootstrap, "which", return_value="/tool"
        ), patch.object(
            recreate_bootstrap, "_native_tool_record", return_value=bound
        ), patch.object(
            recreate_bootstrap.platform, "system", return_value="Linux"
        ):
            authority = recreate_bootstrap.capture_build_authority(
                Path(directory), "test-host", None
            )
        self.assertEqual(authority["status"], "rejected")
        self.assertEqual(set(authority["ambient_overrides"]), {"CC"})

    def test_build_authority_rejects_language_git_and_python_injection_namespaces(self):
        overrides = recreate_bootstrap._ambient_build_authority_overrides(
            {
                "TRUST_JOBS": "1",
                "RUST_BOOTSTRAP_CONFIG": "/tmp/other.toml",
                "CARGOFLAGS_BOOTSTRAP": "--target injected",
                "BOOTSTRAP_SKIP_TARGET_SANITY": "1",
                "GIT_DIR": "/tmp/other.git",
                "PYTHONPATH": "/tmp/injected",
                "DYLD_INSERT_LIBRARIES": "/tmp/injected.dylib",
                recreate_bootstrap.REEXEC_GUARD_ENV: "1",
                "UNRELATED": "allowed",
            }
        )
        self.assertEqual(
            set(overrides),
            {
                "TRUST_JOBS",
                "RUST_BOOTSTRAP_CONFIG",
                "CARGOFLAGS_BOOTSTRAP",
                "BOOTSTRAP_SKIP_TARGET_SANITY",
                "GIT_DIR",
                "PYTHONPATH",
                "DYLD_INSERT_LIBRARIES",
            },
        )

    def test_external_adapter_symlink_keeps_lexical_repository_path(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "repo"
            external = Path(directory) / "external" / "lib"
            external.mkdir(parents=True)
            adapter = root / "build" / "test-host" / "genesis-stage0"
            adapter.mkdir(parents=True)
            os.symlink(external, adapter / "lib", target_is_directory=True)
            self.assertEqual(
                recreate_bootstrap._repository_lexical_relative_path(
                    root, adapter / "lib"
                ),
                "build/test-host/genesis-stage0/lib",
            )
            with self.assertRaises(ValueError):
                recreate_bootstrap._repository_relative_path(root, adapter / "lib")


@unittest.skipUnless(sys.version_info >= (3, 11), "bootstrap lineage requires tomllib")
class BootstrapLineageTests(unittest.TestCase):
    def test_genesis_config_uses_the_cargo_compatibility_identity(self):
        import tomllib

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = recreate_bootstrap.write_config(
                root,
                "test-host",
                force=True,
                seed_mode=False,
            )
            build = tomllib.loads(config.read_text(encoding="utf-8"))["build"]
            adapter = root / "build" / "test-host" / "genesis-stage0" / "bin"
            self.assertEqual(build["cargo"], str(adapter / "cargo"))
            self.assertNotEqual(build["cargo"], str(adapter / "targo"))

    def test_seed_and_genesis_configs_have_distinct_release_authority(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = root / "bootstrap.toml"
            config.write_text(
                "# Generated by scripts/recreate_bootstrap.py (seed stage0 mode).\n",
                encoding="utf-8",
            )
            validated_seed = {
                "schema": "trust.validated-seed-lineage.v1",
                "status": "validated",
                "errors": [],
            }
            with patch.object(
                recreate_bootstrap,
                "capture_validated_seed_lineage",
                return_value=validated_seed,
            ):
                seed = recreate_bootstrap.capture_bootstrap_lineage(root, "test-host")
            self.assertEqual(seed["status"], "trust_from_trust")
            self.assertTrue(seed["trust_from_trust"])
            self.assertEqual(seed["config_path"], "bootstrap.toml")
            self.assertIsNone(seed["genesis_adapter"])

            adapter = root / "build" / "test-host" / "genesis-stage0" / "bin"
            config.write_text(
                "# Generated by scripts/recreate_bootstrap.py (genesis stage0 mode).\n"
                "[build]\n"
                f'rustc = "{adapter / "trustc"}"\n'
                f'cargo = "{adapter / "cargo"}"\n'
                f'rustdoc = "{adapter / "trustdoc"}"\n'
                f'rustfmt = "{adapter / "trustfmt"}"\n'
                f'cargo-clippy = "{adapter / "targo-tippy"}"\n',
                encoding="utf-8",
            )
            genesis_authority = {
                "schema": "trust.genesis-adapter-authority.v1",
                "status": "ready",
                "authority_sha256": "a" * 64,
                "authority": {},
                "errors": [],
            }
            with patch.object(
                recreate_bootstrap,
                "_capture_genesis_adapter_authority",
                return_value=genesis_authority,
            ):
                genesis = recreate_bootstrap.capture_bootstrap_lineage(
                    root, "test-host"
                )
            self.assertEqual(genesis["status"], "local_genesis")
            self.assertFalse(genesis["trust_from_trust"])
            self.assertEqual(genesis["genesis_adapter"], genesis_authority)

    def test_nix_seed_binary_rewrite_is_explicitly_unsupported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "bootstrap.toml").write_text(
                "# Generated by scripts/recreate_bootstrap.py (seed stage0 mode).\n"
                "[build]\npatch-binaries-for-nix = true\n",
                encoding="utf-8",
            )
            validated_seed = {
                "schema": "trust.validated-seed-lineage.v1",
                "status": "validated",
                "errors": [],
            }
            with patch.object(
                recreate_bootstrap,
                "capture_validated_seed_lineage",
                return_value=validated_seed,
            ):
                lineage = recreate_bootstrap.capture_bootstrap_lineage(
                    root, "test-host"
                )
            self.assertEqual(lineage["status"], "rejected")
            self.assertTrue(any("Nix patchelf" in error for error in lineage["errors"]))

    def test_seed_marker_cannot_hide_a_stock_stage0_override(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = root / "bootstrap.toml"
            config.write_text(
                "# Generated by scripts/recreate_bootstrap.py (seed stage0 mode).\n"
                "[build]\n"
                'rustc = "/ambient/rustc"\n',
                encoding="utf-8",
            )
            lineage = recreate_bootstrap.capture_bootstrap_lineage(root)
            self.assertEqual(lineage["status"], "rejected")
            self.assertFalse(lineage["trust_from_trust"])
            self.assertEqual(lineage["declared_stage0_overrides"], ["rustc"])

    def test_invalid_bootstrap_toml_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = root / "bootstrap.toml"
            config.write_text(
                "# Generated by scripts/recreate_bootstrap.py (seed stage0 mode).\n[build\n",
                encoding="utf-8",
            )
            lineage = recreate_bootstrap.capture_bootstrap_lineage(root)
            self.assertEqual(lineage["status"], "rejected")
            self.assertTrue(any("valid UTF-8 TOML" in error for error in lineage["errors"]))


if __name__ == "__main__":
    unittest.main()
