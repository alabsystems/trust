"""Focused tests for bootstrap installation and provenance gates."""

from __future__ import annotations

import importlib.util
import ast
import copy
import hashlib
import inspect
import io
import json
import lzma
import os
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
import unicodedata
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
from mint_clean_lean_inputs_test import CleanLeanInputTests, fixture as clean_lean_fixture
from build_slot_test import BuildSlotTests
from seed_runtime_prerequisite_test import SeedRuntimePrerequisiteTests

# macOS temp dirs live under the /var -> /private/var symlink, and git reports
# resolved paths; compare like with like.
tempfile.tempdir = os.path.realpath(tempfile.gettempdir())


SCRIPT = Path(__file__).resolve().parents[1] / "recreate_bootstrap.py"
SPEC = importlib.util.spec_from_file_location("recreate_bootstrap", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
recreate_bootstrap = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = recreate_bootstrap
SPEC.loader.exec_module(recreate_bootstrap)

# The normal support entrypoint must use the same producer environment.
from bootstrap_xpy_environment_test import BootstrapXpyEnvironmentTests

# Fixture executables here are written by a test a moment before the recreator
# runs them, and on a busy Mac the first exec of a new file can wait 10-61 s
# (KNOWN_HAZARDS TRUST-KI-1014-3): past the 10 s and 30 s bounds the recreator
# puts on a tool's `--version`, a driver's `-Z help` or `otool`, so a test about
# something else failed (2026-10-14: test_off_switch_probe_uses_the_given_driver_path,
# None != 'flag', green alone at once; TRUST-KI-1014-6). While this module's tests
# run, a real child started under a shorter bound is given FIXTURE_PATIENCE_SECONDS
# instead. The recreator's bounds are unchanged: a test that replaces
# subprocess.run sees each as the recreator wrote it, and
# test_the_recreator_keeps_its_own_bounds pins three of them.
FIXTURE_PATIENCE_SECONDS = 600
_BOUNDED_RUN = subprocess.run


def _patient_run(*args, timeout=None, **kwargs):
    if timeout is not None and timeout < FIXTURE_PATIENCE_SECONDS:
        timeout = FIXTURE_PATIENCE_SECONDS
    return _BOUNDED_RUN(*args, timeout=timeout, **kwargs)


_SHELL_UMASK = None


def setUpModule():
    global _SHELL_UMASK
    subprocess.run = _patient_run
    # The fixtures model a checkout made under umask 022. The recreator refuses a build
    # directory others can write (EmptyLlvmDirectoryModeTests pins that), and on a host
    # whose shell umask is 002 every fixture's build/ would otherwise be group-writable:
    # measured on the GB10 2026-11-13, 13 cases refused for that alone.
    _SHELL_UMASK = os.umask(0o022)


def tearDownModule():
    subprocess.run = _BOUNDED_RUN
    if _SHELL_UMASK is not None:
        os.umask(_SHELL_UMASK)


# What scripts/promote-toolchain.sh reads a stage receipt with. It cannot import
# the recreator (it runs under whatever python3 is on PATH), so the rules the
# two share are held together by the tests that load both.
STAGE_RECEIPT_READER = Path(__file__).resolve().parents[2] / "scripts/lib/stage_receipt_provenance.py"


def load_stage_receipt_reader():
    spec = importlib.util.spec_from_file_location("stage_receipt_provenance", STAGE_RECEIPT_READER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


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
        # This assertion is about a missing registrar, not the host's compiler.
        with patch.object(recreate_bootstrap, "find_rustup", return_value=None), patch.object(
            recreate_bootstrap, "tool_version", return_value="fixture version"
        ), patch.object(recreate_bootstrap, "find_python_ge_311", return_value=sys.executable):
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
            recreate_bootstrap, "atpkg_trust_sysroot", return_value=None
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
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name).resolve()

        def run(command, *, env, cwd):
            self.assertEqual(
                command[:5],
                [sys.executable, str(root / "x.py"), "build", "--stage", "2"],
            )
            self.assertEqual(cwd, str(root))
            self.assertEqual(env["CARGO_HOME"], str(root / "build/bootstrap-cargo-home"))
            captured.update(env)
            return SimpleNamespace(returncode=0)

        hostile = {
            # Spelled with flags the compiler source actually declares, like the
            # `-Ztrust-policy=advisory` sentinel below: scripts/check_toolchain_coherence.py
            # scans scripts/ for `-Z trust-*` tokens, so an invented flag name here reads
            # as a removed/renamed compiler option. The assertions below only care that
            # these are scrubbed, never what they say.
            "RUSTFLAGS": "-Ztrust-verify=on",
            "RUSTFLAGS_BOOTSTRAP": "-Ztrust-verify=on",
            "CARGO_TARGET_TEST_RUSTFLAGS": "-Ztrust-policy=advisory",
            "CARGO_HOME": "/ambient/cargo-home",
            "UNRELATED": "preserved",
        }
        with patch.dict(os.environ, hostile, clear=True), patch.object(
            recreate_bootstrap, "add_homebrew_library_path"
        ), patch.object(
            recreate_bootstrap,
            "seed_verification_off_switch",
            return_value="flag",
        ), patch.object(recreate_bootstrap.subprocess, "run", side_effect=run):
            self.assertEqual(
                recreate_bootstrap.run_xpy_build(
                    root, "test-host", 2, None, [], seed_mode=seed_mode
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


class BootstrapCargoIsolationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.scratch = Path(temporary.name).resolve()
        self.root = self.scratch / "checkout"
        self.root.mkdir()

    def test_read_only_capture_ignores_unconsumed_user_home_configuration(self):
        user = self.scratch / "user"
        (user / ".cargo").mkdir(parents=True)
        config = user / ".cargo/config.toml"
        config.write_text('[build]\nrustc="/user/compiler"\n')
        original = config.read_bytes()
        with patch.object(recreate_bootstrap.Path, "home", return_value=user):
            authority, errors = recreate_bootstrap.bootstrap_cargo_authority(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(authority["unbound_config_paths"], [])
        self.assertFalse((self.root / "build").exists())
        self.assertEqual(config.read_bytes(), original)

    def test_owned_home_is_selected_without_mutating_parent_environment(self):
        environment = {"UNRELATED": "preserved"}
        recreate_bootstrap.prepare_bootstrap_cargo_environment(self.root, environment)
        selected = Path(environment["CARGO_HOME"])
        self.assertEqual(selected, self.root / "build/bootstrap-cargo-home")
        self.assertTrue(selected.is_dir())
        self.assertEqual(environment["UNRELATED"], "preserved")
        self.assertEqual(list(selected.iterdir()), [])

    def test_existing_owned_home_configuration_is_rejected_before_child(self):
        selected = self.root / "build/bootstrap-cargo-home"
        selected.mkdir(parents=True)
        for name in ("config", "config.toml"):
            with self.subTest(name=name):
                config = selected / name
                config.write_text('[build]\nrustc="/unbound/compiler"\n')
                with self.assertRaisesRegex(RuntimeError, "unbound Cargo configuration"):
                    recreate_bootstrap.prepare_bootstrap_cargo_environment(self.root, {})
                config.unlink()

    def test_ancestor_configuration_is_not_hidden_by_an_empty_cargo_home(self):
        config = self.scratch / ".cargo/config.toml"
        config.parent.mkdir()
        config.write_text('[build]\nrustc="/ancestor/compiler"\n')
        _authority, errors = recreate_bootstrap.bootstrap_cargo_authority(self.root)
        self.assertTrue(any(str(config) in error for error in errors))
        with self.assertRaisesRegex(RuntimeError, "clean worktree"):
            recreate_bootstrap.prepare_bootstrap_cargo_environment(self.root, {})
        self.assertTrue(config.exists())

    def test_build_and_cargo_home_symlink_escapes_are_rejected(self):
        outside = self.scratch / "outside"
        outside.mkdir()
        build = self.root / "build"
        build.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, "real directory"):
            recreate_bootstrap.prepare_bootstrap_cargo_environment(self.root, {})
        self.assertEqual(list(outside.iterdir()), [])
        build.unlink()
        build.mkdir()
        (build / "bootstrap-cargo-home").symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, "real directory"):
            recreate_bootstrap.prepare_bootstrap_cargo_environment(self.root, {})
        self.assertEqual(list(outside.iterdir()), [])


class SeedFetchTransportTests(unittest.TestCase):
    date = "2026-07-13"

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "src").mkdir()
        self.stage0 = self.root / "src/stage0"
        self.stage0.write_text(
            f"compiler_date={self.date}\n"
            f"dist/{self.date}/trustc-seed.tar.xz={'1' * 64}\n"
            f"dist/{self.date}/targo-seed.tar.xz={'2' * 64}\n"
        )
        self.ledger = self.root / "bootstrap/trust-stage0/seed-ledger.toml"
        self.ledger.parent.mkdir(parents=True)
        self.ledger.write_text('[release]\nrepo = "owner/trust"\ntag = "exact-seed"\n')
        # An empty atpkg store: never the person's own.
        store = patch.object(recreate_bootstrap, "atpkg_store_prefix",
                             return_value=self.root / "no-store")
        store.start()
        self.addCleanup(store.stop)

    def command(self, *client):
        return [*client, "release", "download", "owner/trust", "exact-seed",
                "--asset", "targo-seed.tar.xz", "--asset", "trustc-seed.tar.xz",
                "--dir", str(self.ledger.parent / "dist" / self.date), "--clobber"]

    def test_standalone_agh_uses_exact_ledger_and_pinned_asset_names(self):
        with patch.object(recreate_bootstrap, "which", side_effect={"agh": "/tools/agh"}.__getitem__), \
                patch.object(recreate_bootstrap.subprocess, "run", return_value=SimpleNamespace(returncode=0)) as run:
            self.assertTrue(recreate_bootstrap.fetch_seed_payloads(self.root, self.date))
        run.assert_called_once_with(self.command("/tools/agh"), cwd=str(self.root))

    def test_bundled_aterm_agh_works_without_standalone_agh_or_gh(self):
        with patch.object(recreate_bootstrap, "which", side_effect={"agh": None, "aterm": "/tools/aterm"}.__getitem__), \
                patch.object(recreate_bootstrap.subprocess, "run", return_value=SimpleNamespace(returncode=0)) as run:
            self.assertTrue(recreate_bootstrap.fetch_seed_payloads(self.root, self.date))
        run.assert_called_once_with(self.command("/tools/aterm", "agh"), cwd=str(self.root))

    def test_missing_agh_and_aterm_never_falls_back_to_gh(self):
        with patch.object(recreate_bootstrap, "which", side_effect={"agh": None, "aterm": None}.__getitem__), \
                patch.object(recreate_bootstrap.subprocess, "run") as run:
            self.assertFalse(recreate_bootstrap.fetch_seed_payloads(self.root, self.date))
        run.assert_not_called()

    def test_missing_ledger_and_unpinned_or_nonflat_assets_never_download(self):
        original = self.stage0.read_text()
        cases = ["", f"dist/{self.date}/../escape.tar.xz=bad\n",
                 "dist/other-date/trustc.tar.xz=bad\n", f"dist/{self.date}/*.tar.xz=bad\n"]
        with patch.object(recreate_bootstrap, "which", return_value="/tools/agh"), \
                patch.object(recreate_bootstrap.subprocess, "run") as run:
            for contents in cases:
                with self.subTest(contents=contents):
                    self.stage0.write_text(contents)
                    self.assertFalse(recreate_bootstrap.fetch_seed_payloads(self.root, self.date))
            self.stage0.write_text(original)
            self.ledger.unlink()
            self.assertFalse(recreate_bootstrap.fetch_seed_payloads(self.root, self.date))
        run.assert_not_called()

    def test_download_failure_is_bounded_and_does_not_select_another_seed(self):
        with patch.object(recreate_bootstrap, "which", side_effect={"agh": "/tools/agh"}.__getitem__), \
                patch.object(recreate_bootstrap.subprocess, "run", return_value=SimpleNamespace(returncode=7)) as run, \
                patch.object(recreate_bootstrap, "validate_seed") as validate:
            self.assertFalse(recreate_bootstrap.resolve_seed(self.root, allow_fetch=True))
        self.assertEqual(run.call_count, 2)
        for call in run.call_args_list:
            self.assertEqual(call.args[0], self.command("/tools/agh"))
        validate.assert_not_called()

    def test_successful_transport_with_missing_asset_still_refuses(self):
        with patch.object(recreate_bootstrap, "which", return_value="/tools/agh"), \
                patch.object(recreate_bootstrap.subprocess, "run", return_value=SimpleNamespace(returncode=0)), \
                patch.object(recreate_bootstrap, "validate_seed") as validate:
            self.assertFalse(recreate_bootstrap.resolve_seed(self.root, allow_fetch=True))
        validate.assert_not_called()


@unittest.skipUnless(sys.platform == "darwin", "atpkg hands a tree out only as APFS clones")
class SeedStoreTests(unittest.TestCase):
    """DC-16c: atpkg's `trust-stage0` tree is tried before agh, and the pins decide."""

    date = "2026-07-13"
    host = "aarch64-apple-darwin"
    manifest = "5" * 64

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name) / "trust"
        (self.root / "src").mkdir(parents=True)
        self.archives = {"trustc-seed.tar.xz": b"trustc seed", "targo-seed.tar.xz": b"targo seed"}
        pins = "".join(f"dist/{self.date}/{name}={hashlib.sha256(body).hexdigest()}\n"
                       for name, body in sorted(self.archives.items()))
        (self.root / "src/stage0").write_text(
            f"compiler_channel_manifest_hash={self.manifest}\ncompiler_date={self.date}\n{pins}")
        ledger = self.root / "bootstrap/trust-stage0/seed-ledger.toml"
        ledger.parent.mkdir(parents=True)
        ledger.write_text('[release]\nrepo = "owner/trust"\ntag = "exact-seed"\n')
        self.prefix = Path(temporary.name) / "pkg"
        store = patch.object(recreate_bootstrap, "atpkg_store_prefix", return_value=self.prefix)
        store.start()
        self.addCleanup(store.stop)
        self.dist = self.root / "bootstrap/trust-stage0/dist" / self.date

    def lay_tree(self, manifest=None, archives=None):
        """A complete tree as atpkg lays one: the archives, then `<key>.ready`."""
        inputs = ("trust-stage0-tree-key/v1\ncompiler_channel_manifest_hash "
                  f"{manifest or self.manifest}\n")
        key = hashlib.sha256(inputs.encode()).hexdigest()
        tree = self.prefix / "trees.noindex/trust-stage0" / self.host / key
        tree.mkdir(parents=True)
        for name, body in (archives or self.archives).items():
            (tree / name).write_bytes(body)
        tree.with_name(key + ".ready").write_text("ok\nplatform=aarch64-macos\n")
        return tree

    def fetch(self):
        with patch.object(recreate_bootstrap, "which", return_value="/tools/agh"), \
                patch.object(recreate_bootstrap.subprocess, "run",
                             return_value=SimpleNamespace(returncode=0)) as run:
            fetched = recreate_bootstrap.fetch_seed_payloads(self.root, self.date, host=self.host)
        return fetched, run

    def test_the_store_tree_of_the_pinned_manifest_is_taken_before_agh(self):
        tree = self.lay_tree()
        fetched, run = self.fetch()
        self.assertTrue(fetched)
        run.assert_not_called()
        for name, body in self.archives.items():
            taken, stored = self.dist / name, tree / name
            self.assertEqual(taken.read_bytes(), body)
            # A clone, never a link: its own inode, and the store's file stays unlinked.
            self.assertFalse(taken.is_symlink())
            self.assertNotEqual(os.stat(taken).st_ino, os.stat(stored).st_ino)
            self.assertEqual(os.stat(stored).st_nlink, 1)
        self.assertTrue(tree.with_name(tree.name + ".used").is_file())
        self.assertEqual(sorted(p.name for p in self.dist.iterdir()), sorted(self.archives))

    def test_an_archive_that_fails_its_pin_is_left_for_agh(self):
        self.lay_tree(archives={**self.archives, "targo-seed.tar.xz": b"not the pinned bytes"})
        fetched, run = self.fetch()
        self.assertTrue(fetched)
        self.assertEqual((self.dist / "trustc-seed.tar.xz").read_bytes(), b"trustc seed")
        self.assertFalse((self.dist / "targo-seed.tar.xz").exists())
        command = run.call_args.args[0]
        self.assertEqual(command[command.index("--asset"):command.index("--dir")],
                         ["--asset", "targo-seed.tar.xz"])

    def test_a_tree_of_another_manifest_or_unmarked_is_not_read(self):
        self.lay_tree(manifest="6" * 64)
        mine = self.lay_tree()
        mine.with_name(mine.name + ".ready").unlink()
        fetched, run = self.fetch()
        self.assertTrue(fetched)
        self.assertFalse(self.dist.exists() and any(self.dist.iterdir()))
        command = run.call_args.args[0]
        self.assertEqual(command.count("--asset"), 2)

    def test_a_validated_seed_records_the_key_inputs_a_builder_packs_it_under(self):
        self.lay_tree()
        with patch.object(recreate_bootstrap, "validate_seed", return_value=True):
            self.assertTrue(recreate_bootstrap.resolve_seed(self.root, allow_fetch=True,
                                                            host=self.host))
        inputs = (self.dist / ".trust-stage0-tree-key").read_text()
        self.assertEqual(inputs, recreate_bootstrap.stage0_tree_key_inputs(self.root))
        self.assertIn(f"compiler_channel_manifest_hash {self.manifest}", inputs)

    def test_the_recorded_key_inputs_leave_the_checkout_clean(self):
        repo = Path(__file__).resolve().parents[2]
        recorded = f"bootstrap/trust-stage0/dist/{self.date}/.trust-stage0-tree-key"
        checked = subprocess.run(["git", "-C", str(repo), "check-ignore", "-q", recorded],
                                 check=False)
        self.assertEqual(checked.returncode, 0, f"{recorded} is not ignored")

    def test_the_stage1_seed_switch_at_false_leaves_the_store_unread(self):
        self.lay_tree()
        with patch.object(recreate_bootstrap, "which", return_value="/tools/agh"), \
                patch.object(recreate_bootstrap.subprocess, "run",
                             return_value=SimpleNamespace(returncode=0)) as run:
            fetched = recreate_bootstrap.fetch_seed_payloads(self.root, self.date, host=self.host,
                                                             use_store=False)
        self.assertTrue(fetched)
        self.assertFalse(self.dist.exists() and any(self.dist.iterdir()))
        command = run.call_args.args[0]
        self.assertEqual(command.count("--asset"), 2)
        enabled = recreate_bootstrap.stage1_seed_enabled
        self.assertTrue(enabled(None))
        self.assertTrue(enabled(b"[rust]\nchannel = \"dev\"\n"))
        self.assertTrue(enabled(b"[rust]\ntrust-stage1-seed = true\n"))
        self.assertFalse(enabled(b"[rust]\ntrust-stage1-seed = false\n"))
        self.assertFalse(enabled(b"rust.trust-stage1-seed = false\n"))

    def test_resolve_seed_passes_the_switch_to_the_fetch(self):
        with patch.object(recreate_bootstrap, "fetch_seed_payloads", return_value=False) as fetch:
            self.assertFalse(recreate_bootstrap.resolve_seed(self.root, allow_fetch=True,
                                                             host=self.host, use_store=False))
        self.assertIs(fetch.call_args.kwargs["use_store"], False)


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
            ["--genesis", "--require-seed"],
            # The check of a --fresh-seed build is allowed since 2026-10-14
            # (the next test); a check of what --fresh-seed refuses is not.
            ["--fresh-seed", "--require-seed", "--check", "--no-build"],
            ["--fresh-seed", "--require-seed", "--check", "--stage", "1"],
            ["--fresh-seed", "--check", "--stage", "2"],
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
        ), patch.object(
            recreate_bootstrap, "atpkg_trust_sysroot", return_value=None
        ), patch.object(recreate_bootstrap, "resolve_seed") as resolve_seed:
            for argv in cases:
                with self.subTest(argv=argv):
                    self.assertEqual(recreate_bootstrap.main(argv), 2)
        resolve_seed.assert_not_called()

    def fresh_seed_check(self, root, argv, selection=None):
        """main(argv) on `root` with no tool, pack, fetch or build reachable.

        The atpkg pack, every step that writes, moves or builds, and the
        native captures are made to fail the test if reached; the seed
        archives validate. Returns (exit status, what was printed, resolve_seed).
        """
        output = io.StringIO()
        with ExitStack() as stack:
            for name in ("ensure_python_311", "line_buffer_output", "print_prereqs"):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            stack.enter_context(patch.object(recreate_bootstrap, "repo_root", return_value=root))
            stack.enter_context(patch.object(recreate_bootstrap, "host_triple", return_value=self.host))
            stack.enter_context(patch.object(recreate_bootstrap, "check_prereqs", return_value=[]))
            if selection is not None:
                stack.enter_context(
                    patch.object(recreate_bootstrap, "resolve_stage0_selection", return_value=selection)
                )
            for name in (
                "atpkg_trust_sysroot",
                "quarantine_seed_stage0",
                "ensure_submodules",
                "ensure_local_genesis_stage0",
                "write_config",
                "capture_source_lineage",
                "capture_bootstrap_lineage",
                "capture_build_authority",
                "run_xpy_build",
            ):
                stack.enter_context(
                    patch.object(
                        recreate_bootstrap, name, side_effect=AssertionError(f"a check reached {name}")
                    )
                )
            resolve_seed = stack.enter_context(
                patch.object(recreate_bootstrap, "resolve_seed", return_value=True)
            )
            stack.enter_context(patch("sys.stdout", output))
            status = recreate_bootstrap.main(argv)
        return status, output.getvalue(), resolve_seed

    def test_fresh_seed_check_selects_the_stage0_its_build_uses_and_sets_nothing_aside(self):
        # Until 2026-10-14 --fresh-seed refused --check, so the check nearest to
        # the seal command, `--check --require-seed --stage 2`
        # (scripts/dev-bootstrap.sh --check), tried an installed atpkg pack
        # first and answered `stage0 mode: atpkg` for a build that never uses
        # one (KNOWN_HAZARDS TRUST-KI-1014-6). The check of that build now
        # selects as it does: the pinned archives only, without fetching, and
        # it sets no stage0 aside.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            status, printed, resolve_seed = self.fresh_seed_check(
                root, ["--check", "--stage", "2", "--require-seed", "--fresh-seed"]
            )
            self.assertEqual(status, 0, printed)
            resolve_seed.assert_called_once_with(root, allow_fetch=False, host=self.host, use_store=True)
            self.assertIn(
                f"\n--fresh-seed: the build sets build/{self.host}/stage0 aside and x.py hydrates "
                "it again from the pinned archives validated above; a check sets nothing aside.\n",
                printed,
            )
            self.assertTrue(
                printed.endswith("\n--check: prerequisites OK (stage0 mode: seed).\n"), printed
            )
            self.assertNotIn("installed atpkg pack", printed)
            self.assertEqual(list(root.iterdir()), [])

            # Where the build is refused at the selection, so is its check, in
            # the same words: a config that selects atpkg.
            config = root / "bootstrap.toml"
            config.write_text('# (atpkg stage0 mode)\n[build]\nrustc = "/pkg/trust/bin/trustc"\n')
            for argv in (
                ["--check", "--stage", "2", "--require-seed", "--fresh-seed"],
                ["--stage", "2", "--require-seed", "--fresh-seed"],
            ):
                with self.subTest(argv=argv):
                    status, printed, resolve_seed = self.fresh_seed_check(root, argv)
                    self.assertEqual(status, 1, printed)
                    self.assertIn(
                        f"\nStage0 selection refused: {config} selects atpkg, but this invocation "
                        "requires seed; use --force-config to change it\n",
                        printed,
                    )
                    resolve_seed.assert_not_called()

    def test_a_check_that_selects_atpkg_names_the_build_it_answers_for(self):
        # A check without --fresh-seed still answers for the build with its own
        # flags, which may use an installed pack; it now says so, and names the
        # check of a --fresh-seed build, before the mode line that ends it.
        note = (
            "\nThis check answers for a build with these flags, which uses the installed atpkg "
            "pack. A --fresh-seed build never does: `--check --require-seed --fresh-seed` "
            "answers for that one.\n"
        )
        atpkg = recreate_bootstrap.Stage0Selection("atpkg", None, None)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            status, printed, _ = self.fresh_seed_check(
                root, ["--check", "--stage", "2", "--require-seed"], selection=atpkg
            )
            self.assertEqual(status, 0, printed)
            self.assertIn(note, printed)
            self.assertTrue(
                printed.endswith(note + "\n--check: prerequisites OK (stage0 mode: atpkg).\n"), printed
            )
            # Not for a check of a stage 0/1 build, nor for one that selected the archives.
            for argv, selection in (
                (["--check", "--stage", "1", "--no-register"], atpkg),
                (["--check", "--stage", "2", "--require-seed"], recreate_bootstrap.Stage0Selection("seed", None, None)),
            ):
                with self.subTest(argv=argv, mode=selection.mode):
                    status, printed, _ = self.fresh_seed_check(root, argv, selection=selection)
                    self.assertEqual(status, 0, printed)
                    self.assertNotIn("installed atpkg pack", printed)

    def test_fresh_seed_verifies_immutable_receipt_before_registration(self):
        source = {
            "status": "immutable_release",
            "closure_sha256": "a" * 64,
            "errors": [],
        }
        bootstrap = {
            "status": "seed-validated-pending-hydration",
            "mode": "seed",
            "config_path": "bootstrap.toml",
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
                patch.object(recreate_bootstrap, "atpkg_trust_sysroot", return_value=None)
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "repo_root", return_value=Path("/checkout"))
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "host_triple", return_value=self.host)
            )
            # This test is about the checked-in SEED; the machine running it may
            # carry an atpkg-installed trust pack, which main() prefers.
            stack.enter_context(
                patch.object(recreate_bootstrap, "atpkg_trust_sysroot", return_value=None)
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
            ):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            stack.enter_context(patch.object(
                recreate_bootstrap, "write_config", return_value=recreate_bootstrap.WrittenBootstrapConfig(
                    Path("/checkout/bootstrap.toml"), "b" * 64
                )
            ))
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
            # A build directory with no LLVM in it yet: x.py builds one.
            llvm_observed = StageToolProvenanceTests.llvm_observation()
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "capture_llvm_before_build",
                    side_effect=lambda *_args, **_kwargs: events.append("llvm") or llvm_observed,
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
            audit = stack.enter_context(
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
                    "llvm",
                    "xpy",
                    "install",
                    "audit",
                    "verify",
                    "discard",
                    "register",
                ],
            )
            self.assertTrue(verify.call_args.kwargs["require_immutable_lineage"])
            # The receipt is to say how its build was started: as given, in order.
            self.assertEqual(
                audit.call_args.kwargs["invocation"],
                ["--fresh-seed", "--require-seed", "--stage", "2"],
            )
            # And which LLVM it carries: the audit is handed what was observed
            # before x.py ran.
            self.assertIs(audit.call_args.kwargs["llvm_before"], llvm_observed)

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
                    "llvm",
                    "xpy",
                    "install",
                    "audit",
                    "verify",
                    "recover",
                ],
            )


    def test_fresh_seed_refuses_seed_lineage_when_atpkg_stage0_was_selected(self):
        # Fresh selection now always chooses archives. Inject the historical
        # wrong decision explicitly to keep testing the downstream mismatch
        # firewall, rather than accidentally failing on an unbound mock config.
        source = {
            "status": "immutable_release",
            "closure_sha256": "a" * 64,
            "errors": [],
        }
        bootstrap = {
            "status": "seed-validated-pending-hydration",
            "mode": "seed",
            "config_sha256": "b" * 64,
            "config_path": "bootstrap.toml",
            "errors": [],
        }
        quarantine = Path("/checkout/build/test-host/stage0.preexisting-fresh-seed")
        with ExitStack() as stack:
            stack.enter_context(patch.object(
                recreate_bootstrap, "resolve_stage0_selection",
                return_value=recreate_bootstrap.Stage0Selection("atpkg", None, None),
            ))
            stack.enter_context(patch.object(
                recreate_bootstrap, "write_config",
                return_value=recreate_bootstrap.WrittenBootstrapConfig(
                    Path("/checkout/bootstrap.toml"), "b" * 64
                ),
            ))
            for name in (
                "ensure_python_311",
                "line_buffer_output",
                "print_prereqs",
                "ensure_submodules",
                "scrub_pat_from_remotes",
            ):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            stack.enter_context(
                patch.object(recreate_bootstrap, "repo_root", return_value=Path("/checkout"))
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "host_triple", return_value=self.host)
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "resolve_seed", return_value=True)
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "check_prereqs", return_value=[])
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "atpkg_trust_sysroot",
                    return_value=Path("/atpkg/store/trust/1"),
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap, "capture_source_lineage", return_value=source
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap, "quarantine_seed_stage0", return_value=quarantine
                )
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap, "capture_bootstrap_lineage", return_value=bootstrap
                )
            )
            authority = stack.enter_context(
                patch.object(recreate_bootstrap, "capture_build_authority")
            )
            xpy = stack.enter_context(patch.object(recreate_bootstrap, "run_xpy_build"))
            recover = stack.enter_context(
                patch.object(recreate_bootstrap, "recover_seed_stage0_quarantine")
            )
            stdout = io.StringIO()
            with patch.object(sys, "stdout", stdout):
                result = recreate_bootstrap.main(
                    ["--fresh-seed", "--require-seed", "--stage", "2"]
                )
        self.assertEqual(result, 1)
        authority.assert_not_called()
        xpy.assert_not_called()
        recover.assert_called_once_with(Path("/checkout"), self.host, quarantine)
        self.assertIn(
            "stage0 mode mismatch: the recreator selected 'atpkg' but the bootstrap "
            "config declares 'seed'",
            stdout.getvalue(),
        )


@unittest.skipUnless(os.name == "posix", "actual POSIX direct-child lifecycle control")
class SubmoduleProgressBoundTests(unittest.TestCase):
    """An acquisition ends for lack of progress, never on a total (RL-100).

    The child is a real process under the real process-tree custody. It writes into
    its stage's object directory one step at a time, and the bound's clock is the
    test's: each reading of it is a minute later, and each measurement first lets the
    child take its next step, so ten minutes pass in as many steps.
    """

    STEP_SECONDS = 60

    CHILD = r"""
import os, sys, time
objects, steps = sys.argv[1], [int(word) for word in sys.argv[2:]]
for number, count in enumerate(steps):
    while not os.path.exists(os.path.join(objects, "..", f"step-{number}")):
        time.sleep(0.005)
    if count:
        with open(os.path.join(objects, "pack", f"tmp_pack_{number}"), "wb") as stream:
            stream.write(b"\0" * count)
    os.replace(os.path.join(objects, "..", f"step-{number}"), os.path.join(objects, "..", f"done-{number}"))
if os.environ.get("FIXTURE_NEVER_ENDS"):
    print("fixture transport: waiting on a peer that sends nothing more", flush=True)
    time.sleep(3600)
"""

    def acquire(self, directory, steps, *, never_ends=False):
        """Run the fixture child under the progress bound; return (bound, minutes the clock ran)."""
        stage = Path(directory) / "first-party/.trust-submodule-fixture/source"
        objects = stage / ".git/objects"
        (objects / "pack").mkdir(parents=True)
        state = {"now": 0.0, "step": 0, "begun": False}

        def clock():
            state["now"] += self.STEP_SECONDS
            return state["now"]

        def measure(paths):
            if not state["begun"]:
                # The bound's first reading, before the child exists.
                state["begun"] = True
                return recreate_bootstrap._submodule_progress_bytes(paths)
            # Let the child take its next step, then read what it left.
            number = state["step"]
            if number < len(steps):
                (stage / ".git" / f"step-{number}").write_text("")
                deadline = time.monotonic() + 30
                while not (stage / ".git" / f"done-{number}").exists():
                    self.assertLess(time.monotonic(), deadline, "the fixture child did not take its step")
                    time.sleep(0.005)
                state["step"] += 1
            return recreate_bootstrap._submodule_progress_bytes(paths)

        bound = recreate_bootstrap._SubmoduleProgress(
            "first-party/fixture", (objects,), clock=clock, measure=measure)
        environment = recreate_bootstrap._provenance_git_environment()
        if never_ends:
            environment["FIXTURE_NEVER_ENDS"] = "1"
        with patch.object(sys, "stderr", io.StringIO()):
            result = recreate_bootstrap._run_submodule_update_process(
                [sys.executable, "-I", "-c", self.CHILD, str(objects), *map(str, steps)],
                environment=environment, timeout_seconds=None, credential_gh=None, progress=bound)
        return bound, state, result

    def test_submodule_acquisition_that_keeps_receiving_outlives_the_former_600_seconds(self):
        self.assertFalse(hasattr(recreate_bootstrap, "SUBMODULE_UPDATE_TIMEOUT_SECONDS"))
        with tempfile.TemporaryDirectory() as directory:
            # Forty minutes of a megabyte a minute: four times the total that ended it before.
            bound, state, result = self.acquire(directory, [1024 * 1024] * 40)
        self.assertEqual(result.returncode, 0)
        self.assertGreaterEqual(state["now"], 40 * self.STEP_SECONDS)
        self.assertGreater(state["now"], 4 * 600)
        self.assertEqual(state["step"], 40)
        self.assertGreaterEqual(bound.received, 39 * 1024 * 1024)

    def test_submodule_acquisition_that_stalls_ends_naming_the_submodule(self):
        with tempfile.TemporaryDirectory() as directory:
            started = time.monotonic()
            with self.assertRaises(recreate_bootstrap._SubmoduleStalled) as raised:
                # Three megabytes in three minutes, one line, then nothing written or printed.
                self.acquire(directory, [1024 * 1024] * 3, never_ends=True)
            elapsed = time.monotonic() - started
        refusal = str(raised.exception)
        self.assertRegex(refusal, r"^first-party/fixture showed too little progress: 31457\d\d bytes observed "
                                  r"under its watched paths and on its output, "
                                  r"0\.0 bytes/s over its last 600 s against a floor of 16 bytes/s, "
                                  r"and none observed for the last 600 s; bytes it holds elsewhere are not seen$")
        # The refusal reports an observation. A transport that shows nothing until its transfer
        # is complete would read the same, so it never says the child received nothing.
        self.assertNotRegex(refusal, r"received|stood still")
        # It is a timeout to every caller that handles one, and the child that slept an hour is gone.
        self.assertIsInstance(raised.exception, subprocess.TimeoutExpired)
        self.assertLess(elapsed, 60)
        # Ended one window after its last byte, not a window after its start.
        self.assertEqual(raised.exception.timeout, recreate_bootstrap.SUBMODULE_STALL_WINDOW_SECONDS)

    def test_submodule_acquisition_below_its_floor_rate_ends_naming_its_rate(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(recreate_bootstrap._SubmoduleStalled) as raised:
                # A megabyte, then 300 bytes a minute, 5 bytes/s, for as long as it is let.
                self.acquire(directory, [1024 * 1024] + [300] * 200, never_ends=True)
        refusal = str(raised.exception)
        self.assertRegex(refusal, r"^first-party/fixture showed too little progress: 10515\d\d bytes observed "
                                  r"under its watched paths and on its output, "
                                  r"5\.0 bytes/s over its last 600 s against a floor of 16 bytes/s, "
                                  r"and none observed for the last 0 s; bytes it holds elsewhere are not seen$")

    def test_an_acquisition_that_prints_and_writes_nothing_is_ended_and_one_that_prints_is_not(self):
        clock = {"now": 0.0}
        bound = recreate_bootstrap._SubmoduleProgress("local Git status", clock=lambda: clock["now"])
        bound.begin()
        for _ in range(30):
            clock["now"] += 30
            bound.printed(30 * 70)  # one progress line a second
            bound.check(["git"])
        self.assertEqual(bound.received, 30 * 30 * 70)
        # Then silence. It ends when its last window's average is under the floor: for 70
        # bytes/s that is 480 s after the last line; a megabyte a second has the whole window.
        with self.assertRaisesRegex(recreate_bootstrap._SubmoduleStalled,
                                    r"^local Git status showed too little progress: 63000 bytes observed "
                                    r"under its watched paths and on its output, "
                                    r"14\.0 bytes/s over its last 600 s against a floor of 16 bytes/s, "
                                    r"and none observed for the last 480 s; bytes it holds elsewhere are not seen$"):
            for _ in range(21):
                clock["now"] += 30
                bound.check(["git"])
        self.assertEqual(clock["now"], 900 + 480)

    def test_progress_counts_growth_under_its_paths_and_never_a_shrinking_tree(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "objects/pack").mkdir(parents=True)
            (root / "objects/pack/tmp_pack").write_bytes(b"x" * 5000)
            (root / "objects/link").symlink_to(root)
            clock = {"now": 0.0}
            bound = recreate_bootstrap._SubmoduleProgress("fixture", (root / "objects", root / "absent"),
                                                          clock=lambda: clock["now"])
            self.assertEqual(recreate_bootstrap._submodule_progress_bytes(bound.paths), 5000)
            bound.begin()
            clock["now"] += 10
            (root / "objects/pack/tmp_pack").write_bytes(b"x" * 9000)
            bound.check(["agh"])
            self.assertEqual(bound.received, 4000)
            # The transfer renames its temporary pack and drops a duplicate: not a loss.
            clock["now"] += 10
            (root / "objects/pack/tmp_pack").write_bytes(b"x" * 100)
            bound.check(["agh"])
            self.assertEqual(bound.received, 4000)
            clock["now"] += 10
            (root / "objects/pack/pack-1.pack").write_bytes(b"x" * 700)
            bound.check(["agh"])
            self.assertEqual(bound.received, 4700)

    def test_whole_tree_local_git_reads_have_the_stall_window_and_small_queries_thirty_seconds(self):
        calls = []

        def run(command, **options):
            calls.append((command, options["timeout"]))
            return subprocess.CompletedProcess(command, 0, b"", b"")
        with patch.object(recreate_bootstrap.subprocess, "run", side_effect=run):
            recreate_bootstrap._local_submodule_git(["-C", "/stage", "status", "--porcelain=v1"], whole_tree=True)
            recreate_bootstrap._local_submodule_git(["-C", "/stage", "rev-parse", "HEAD"])
        self.assertEqual([timeout for _command, timeout in calls],
                         [recreate_bootstrap.SUBMODULE_STALL_WINDOW_SECONDS, 30])
        # The two reads of every path of a checkout, where the 30 s ended a tick on 2026-11-16.
        source = Path(recreate_bootstrap.__file__).read_text()
        for read in ('"status", "--porcelain=v1", "--untracked-files=all", "--ignored", "--ignore-submodules=all"],\n'
                     '                                      whole_tree=True)',
                     '"ls-files", "--stage", "-z"], whole_tree=True)'):
            self.assertEqual(source.count(read), 1, read)


@unittest.skipUnless(os.name == "posix", "actual POSIX direct-child lifecycle control")
class SubmoduleRelayStartupTests(unittest.TestCase):
    def test_missing_nonreaping_wait_refuses_before_spawning(self):
        with patch.object(recreate_bootstrap.os, "waitid", None, create=True), \
             patch.object(recreate_bootstrap.subprocess, "Popen",
                          side_effect=RuntimeError("transport started without wait custody")) as spawn, \
             self.assertRaisesRegex(RuntimeError, "nonreaping child wait"):
            recreate_bootstrap._run_submodule_update_process(
                [sys.executable, "-I", "-c", "pass"],
                environment=recreate_bootstrap._provenance_git_environment(),
                timeout_seconds=5, credential_gh=None)
        spawn.assert_not_called()

    def test_cleanup_diagnostic_preserves_original_failure_without_add_note(self):
        class LegacyFailure(RuntimeError):
            add_note = None

        primary = LegacyFailure("original source acquisition failure")
        process = SimpleNamespace(pid=424242, stdout=io.BytesIO(), returncode=None)
        diagnostics = io.StringIO()
        with patch.object(recreate_bootstrap.subprocess, "Popen", return_value=process), \
             patch.object(recreate_bootstrap, "_submodule_wait_custody_available",
                          return_value=True, create=True), \
             patch.object(recreate_bootstrap, "_wait_submodule_process_group", side_effect=primary), \
             patch.object(recreate_bootstrap, "_terminate_submodule_process_tree",
                          side_effect=RuntimeError("cleanup custody unavailable")) as retire, \
             patch.object(recreate_bootstrap.sys, "stderr", diagnostics), \
             self.assertRaises(LegacyFailure) as caught:
            recreate_bootstrap._run_submodule_update_process(
                ["/fixed/agh", "repo", "fetch"], environment={},
                timeout_seconds=5, credential_gh=None)
        self.assertIs(caught.exception, primary)
        retire.assert_called_once_with(process)
        self.assertIn("cleanup custody unavailable", diagnostics.getvalue())

    def test_cleanup_failure_keeps_original_transport_timeout(self):
        command = ["/fixed/agh", "repo", "fetch"]
        primary = subprocess.TimeoutExpired(command, 0.5)
        process = SimpleNamespace(pid=424242, stdout=io.BytesIO(), returncode=None)
        with patch.object(recreate_bootstrap.subprocess, "Popen", return_value=process), \
             patch.object(recreate_bootstrap, "_submodule_wait_custody_available", return_value=True), \
             patch.object(recreate_bootstrap, "_wait_submodule_process_group", side_effect=primary), \
             patch.object(recreate_bootstrap, "_terminate_submodule_process_tree",
                          side_effect=RuntimeError("cleanup custody unavailable")) as retire, \
             self.assertRaises(subprocess.TimeoutExpired) as caught:
            recreate_bootstrap._run_submodule_update_process(
                command, environment={}, timeout_seconds=0.5, credential_gh=None)
        self.assertEqual(caught.exception.cmd, command)
        self.assertEqual(caught.exception.timeout, 0.5)
        self.assertIs(caught.exception.__cause__, primary)
        retire.assert_called_once_with(process)

    def test_ignored_child_disposition_refuses_before_spawning(self):
        original = recreate_bootstrap.signal.signal(recreate_bootstrap.signal.SIGCHLD,
                                                     recreate_bootstrap.signal.SIG_IGN)
        try:
            with patch.object(recreate_bootstrap.subprocess, "Popen") as spawn, \
                 self.assertRaisesRegex(RuntimeError, "default SIGCHLD disposition"):
                recreate_bootstrap._run_submodule_update_process(
                    [sys.executable, "-I", "-c", "pass"],
                    environment=recreate_bootstrap._provenance_git_environment(),
                    timeout_seconds=5, credential_gh=None)
            spawn.assert_not_called()
        finally:
            recreate_bootstrap.signal.signal(recreate_bootstrap.signal.SIGCHLD, original)

    def test_consumed_actual_child_wait_never_signals_a_numeric_group_again(self):
        child = subprocess.Popen([sys.executable, "-I", "-c", "pass"], start_new_session=True)
        self.assertEqual(child.wait(timeout=5), 0)
        with patch.object(recreate_bootstrap.os, "killpg") as signal_group, \
             self.assertRaisesRegex(RuntimeError, "wait custody was already consumed"):
            recreate_bootstrap._terminate_submodule_process_tree(child)
        signal_group.assert_not_called()

    def test_lost_actual_child_wait_never_signals_a_numeric_group(self):
        child = subprocess.Popen([sys.executable, "-I", "-c", "pass"], start_new_session=True)
        os.waitpid(child.pid, 0)
        try:
            with patch.object(recreate_bootstrap.os, "killpg") as signal_group, \
                 self.assertRaisesRegex(RuntimeError, "wait custody is unavailable"):
                recreate_bootstrap._terminate_submodule_process_tree(child)
            signal_group.assert_not_called()
        finally:
            # The native wait above consumed the original child. Inform Popen;
            # no numeric process control is available or needed after it.
            child.returncode = 0

    def test_relay_start_and_constructor_failures_reap_the_actual_child(self):
        actual_popen = subprocess.Popen
        for failure in ("constructor", "start"):
            with self.subTest(failure=failure):
                children = []
                def spawn(*args, **kwargs):
                    child = actual_popen(*args, **kwargs)
                    children.append(child)
                    return child
                target = recreate_bootstrap.threading if failure == "constructor" else recreate_bootstrap.threading.Thread
                attribute = "Thread" if failure == "constructor" else "start"
                try:
                    with patch.object(recreate_bootstrap.subprocess, "Popen", side_effect=spawn), \
                         patch.object(target, attribute, side_effect=RuntimeError("relay cannot start")), \
                         self.assertRaisesRegex(RuntimeError, "relay cannot start"):
                        recreate_bootstrap._run_submodule_update_process(
                            [sys.executable, "-I", "-c", "import time; time.sleep(30)"],
                            environment=recreate_bootstrap._provenance_git_environment(),
                            timeout_seconds=5, credential_gh=None)
                    self.assertEqual(len(children), 1)
                    self.assertIsNotNone(children[0].returncode)
                    self.assertIsNotNone(children[0].poll())
                    self.assertTrue(children[0].stdout.closed)
                finally:
                    for child in children:
                        if child.poll() is None:
                            recreate_bootstrap._terminate_submodule_process_tree(child)

    def test_successful_owned_relay_preserves_command_exit(self):
        for status in (0, 7):
            with self.subTest(status=status):
                result = recreate_bootstrap._run_submodule_update_process(
                    [sys.executable, "-I", "-c", f"print('owned relay control'); raise SystemExit({status})"],
                    environment=recreate_bootstrap._provenance_git_environment(),
                    timeout_seconds=5, credential_gh=None)
                self.assertEqual(result.returncode, status)


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

    def test_direct_state_reads_actual_head_without_status_or_describe(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            child = checkout / "first-party/ay"
            policy = recreate_bootstrap._submodule_url_is_allowed
            read = recreate_bootstrap._run_git_read

            def no_description(repository, arguments):
                self.assertNotIn(arguments[0], ("submodule", "describe"))
                return read(repository, arguments)

            with patch.object(recreate_bootstrap, "_submodule_url_is_allowed",
                              side_effect=lambda value: value.startswith("/") or policy(value)), patch.object(
                recreate_bootstrap, "_run_git_read", side_effect=no_description
            ):
                states = recreate_bootstrap._direct_submodule_states(checkout)
                self.assertEqual([(state.marker, state.needs_registration) for state in states],
                                 [(" ", False), ("-", False)])
                self.git(child, "config", "user.name", "Bootstrap Test")
                self.git(child, "config", "user.email", "bootstrap@example.invalid")
                (child / "advanced.txt").write_text("retained child change\n", encoding="utf-8")
                self.git(child, "add", "advanced.txt")
                self.git(child, "commit", "--quiet", "-m", "advance child")
                advanced = self.git(child, "rev-parse", "HEAD").stdout.strip()
                self.git(checkout, "config", "--replace-all", "submodule.first-party/ay.active", "true")
                self.git(checkout, "config", "--unset-all", "submodule.first-party/ay.active")
                self.git(checkout, "config", "--unset-all", "submodule.first-party/ay.url")
                states = recreate_bootstrap._direct_submodule_states(checkout)
                self.assertEqual((states[0].marker, states[0].needs_registration), ("+", True))
                self.assertEqual(self.git(child, "rev-parse", "HEAD").stdout.strip(), advanced)

    def test_direct_state_preserves_native_active_pathspec_and_boolean_policy(self):
        cases = (
            (("first-party/*",), None, True),
            ((":!elsewhere/*",), None, True),
            (("other/*",), None, False),
            ((":!first-party/ay",), None, False),
            (("first-party/*", ":!first-party/ay"), None, False),
            ((":!first-party/ay", "first-party/*"), None, False),
            ((":!first-party/ay",), ("true",), True),
            (("first-party/*",), ("false",), False),
            (("",), None, None),
            (("first-party/*", ""), None, None),
            (("",), ("true",), True),
            (("",), ("false",), False),
            (("first-party/*",), ("",), False),
            (("first-party/*",), ("true", ""), False),
        )
        for globals_, named, expected in cases:
            with self.subTest(globals_=globals_, named=named), tempfile.TemporaryDirectory() as directory:
                checkout = self.partial_checkout(directory)
                # `submodule update --init` may install its own per-name true override.
                self.git(checkout, "config", "--replace-all", "submodule.first-party/ay.active", "true")
                self.git(checkout, "config", "--unset-all", "submodule.first-party/ay.active")
                for value in globals_:
                    self.git(checkout, "config", "--add", "submodule.active", value)
                # Isolate ay's policy; a missing clean child has its own explicit selection.
                self.git(checkout, "config", "submodule.first-party/clean.active", "true")
                for value in named or ():
                    self.git(checkout, "config", "--add", "submodule.first-party/ay.active", value)
                if expected is None:
                    with self.assertRaises(subprocess.CalledProcessError):
                        self.git(checkout, "submodule", "status", "--", "first-party/ay")
                else:
                    actual = self.git(checkout, "submodule", "status", "--", "first-party/ay")
                    self.assertEqual(actual.stdout[0], " " if expected else "-")
                policy = recreate_bootstrap._submodule_url_is_allowed
                with patch.object(recreate_bootstrap, "_submodule_url_is_allowed",
                                  side_effect=lambda value: value.startswith("/") or policy(value)):
                    if expected:
                        states = recreate_bootstrap._direct_submodule_states(checkout)
                        self.assertEqual((states[0].marker, states[0].needs_registration), (" ", False))
                    else:
                        with self.assertRaises(RuntimeError):
                            recreate_bootstrap._direct_submodule_states(checkout)

    def test_direct_state_refuses_mismatched_and_trailing_empty_registered_urls(self):
        for value in ("https://github.com/alabsystems/other.git", ""):
            with self.subTest(value=value), tempfile.TemporaryDirectory() as directory:
                checkout = self.partial_checkout(directory)
                self.git(checkout, "config", "--add", "submodule.first-party/ay.url", value)
                values = recreate_bootstrap._submodule_config_values(
                    checkout, "submodule.first-party/ay.url"
                )
                self.assertEqual(values[-1], value)
                self.assertEqual(len(values), 2)
                policy = recreate_bootstrap._submodule_url_is_allowed
                with patch.object(recreate_bootstrap, "_submodule_url_is_allowed",
                                  side_effect=lambda item: item.startswith("/") or policy(item)):
                    with self.assertRaisesRegex(RuntimeError, "registration differs|hidden execution"):
                        recreate_bootstrap._direct_submodule_states(checkout)

    def ensure_with_test_file_transport(self, checkout: Path, *, before_fetch=None, after_fetch=None) -> list[list[str]]:
        """Fake ONLY Agh's owner-routed transfer with an owned local Git source."""
        acquisitions = []
        def fetch(url, destination, source_ref, private_ref, **kwargs):
            acquisitions.append([url, source_ref, private_ref, str(destination)])
            if before_fetch is not None:
                before_fetch(url, destination, source_ref, private_ref)
            subprocess.run(recreate_bootstrap._controlled_git_command([
                "-c", "protocol.file.allow=always", "-C", str(destination),
                "fetch", "--quiet", "--no-tags", "--no-recurse-submodules", "--", url,
                source_ref + ":" + private_ref,
            ]), env=recreate_bootstrap._provenance_git_environment(), check=True,
               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if after_fetch is not None:
                after_fetch(url, destination, source_ref, private_ref)
            return {"commit": source_ref}
        policy = recreate_bootstrap._submodule_url_is_allowed
        with patch.object(recreate_bootstrap, "_submodule_url_is_allowed", side_effect=lambda value: value.startswith("/") or policy(value)), patch.object(
            recreate_bootstrap, "_agh_source_fetch", side_effect=fetch
        ):
            recreate_bootstrap.ensure_submodules(checkout)
        return acquisitions

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
            self.assertTrue(all(len(command[1]) == 40 and command[2].startswith("refs/agh/") for command in updates))
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
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            executable = root / "Cellar" / "gh" / "1.0" / "bin" / "gh"
            executable.parent.mkdir(parents=True)
            executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            executable.chmod(0o700)
            alias = root / "bin" / "gh"
            alias.parent.mkdir()
            # This fixture promises immutable ancestors regardless of umask.
            for parent in (
                root / "Cellar", root / "Cellar" / "gh",
                root / "Cellar" / "gh" / "1.0", executable.parent, alias.parent,
            ):
                parent.chmod(0o700)
            alias.symlink_to(Path("..") / "Cellar" / "gh" / "1.0" / "bin" / "gh")

            self.assertEqual(
                recreate_bootstrap._trusted_credential_executable(alias),
                executable.resolve(strict=True),
            )

    @unittest.skipUnless(os.name == "posix", "POSIX Homebrew credential snapshot")
    def test_gh_authority_snapshots_fixed_homebrew_shape(self):
        with tempfile.TemporaryDirectory() as directory:
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
        with tempfile.TemporaryDirectory() as directory:
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
            real_process = recreate_bootstrap._run_submodule_update_process
            processes = []
            def process(command, **kwargs):
                processes.append((command, kwargs.copy()))
                return real_process(command, **kwargs)
            with patch.object(recreate_bootstrap, "_credential_gh_executable", side_effect=AssertionError("gh must not be selected")), patch.object(
                recreate_bootstrap, "_submodule_auth_config", side_effect=AssertionError("credentials must not be extracted")
            ), patch.object(recreate_bootstrap, "_run_submodule_update_process", side_effect=process):
                acquisitions = self.ensure_with_test_file_transport(checkout)
            self.assertEqual(len(acquisitions), 1)
            self.assertTrue(processes)
            for command, kwargs in processes:
                self.assertNotIn("fetch", command)
                self.assertNotIn("update", command)
                self.assertIsNone(kwargs["credential_gh"])
                # No total: the checkout ends only for lack of progress in the tree it writes.
                self.assertIsNone(kwargs["timeout_seconds"])
                bound = kwargs["progress"]
                self.assertEqual((bound.window, bound.floor),
                                 (recreate_bootstrap.SUBMODULE_STALL_WINDOW_SECONDS,
                                  recreate_bootstrap.SUBMODULE_FLOOR_BYTES_PER_SECOND))
                self.assertEqual(bound.paths, (Path(command[command.index("-C") + 1]),))
                self.assertIn("local Git checkout in ", bound.label)
                self.assertEqual(kwargs["environment"]["GIT_TERMINAL_PROMPT"], "0")
                self.assertEqual(kwargs["environment"]["GIT_NO_LAZY_FETCH"], "1")
                self.assertIn("protocol.https.allow=never", command)
            child = checkout / "first-party/clean"
            self.assertTrue((child / ".git").is_dir())
            self.assertEqual(self.git(child,"remote","get-url","origin").stdout.strip(), acquisitions[0][0])
            self.assertEqual(self.git(child,"config","--get-all","remote.origin.fetch").stdout.strip(), "+refs/heads/*:refs/remotes/origin/*")
            self.assertFalse((child / ".git/objects/info/alternates").exists())
            for repository in (checkout, checkout / "first-party/ay", child):
                local = self.git(repository, "config", "--local", "--list").stdout.lower()
                self.assertNotIn("credential.", local)
                self.assertNotIn("extraheader", local)

    def test_timeout_fails_closed_and_scrubs_remote_credentials(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            self.git(checkout, "remote", "set-url", "origin", "https://user:secret@example.invalid/trust.git")
            with patch.object(recreate_bootstrap, "_submodule_url_is_allowed", return_value=True), patch.object(
                recreate_bootstrap, "_agh_source_fetch", side_effect=subprocess.TimeoutExpired(["agh", "repo", "fetch"],600)
            ), self.assertRaisesRegex(RuntimeError, "Agh submodule acquisition of first-party/clean timed out"):
                recreate_bootstrap.ensure_submodules(checkout)
            self.assertEqual(self.git(checkout, "remote", "get-url", "origin").stdout.strip(), "https://example.invalid/trust.git")
            self.assertEqual([row[0] for row in self.git(checkout,"submodule","status").stdout.splitlines()], [" ","-"])
            self.assertFalse(list((checkout/"first-party").glob(".trust-submodule-*")))

    def test_keyboard_interrupt_still_runs_post_failure_remote_cleanup(self):
        from contextlib import nullcontext
        with patch.object(recreate_bootstrap, "_submodule_owner_lock", return_value=nullcontext()), patch.object(
            recreate_bootstrap, "_inspect_submodule_tree", return_value=[]
        ), patch.object(recreate_bootstrap, "_initialize_missing_submodules", side_effect=KeyboardInterrupt), patch.object(
            recreate_bootstrap, "scrub_pat_from_remotes"
        ) as scrub, self.assertRaises(KeyboardInterrupt):
            recreate_bootstrap._materialize_missing_submodules(Path("/checkout"))
        scrub.assert_called_once_with(Path("/checkout"))

    def test_agh_acquisition_rejects_changed_parent_index_and_preserves_empty_inode(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout=self.partial_checkout(directory); child=checkout/"first-party/clean"; before=child.stat().st_ino
            def mutate(*args):
                (checkout/"unrelated").write_text("concurrent indexed input")
                self.git(checkout,"add","unrelated")
            with self.assertRaisesRegex(RuntimeError,"index changed during acquisition"):
                self.ensure_with_test_file_transport(checkout,before_fetch=mutate)
            self.assertEqual(child.stat().st_ino,before);self.assertEqual(list(child.iterdir()),[])
            self.assertFalse(list((checkout/"first-party").glob(".trust-submodule-*")))

    def test_agh_acquisition_preserves_new_destination_contents_and_no_registration(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout=self.partial_checkout(directory);child=checkout/"first-party/clean"
            def mutate(*args):(child/"personal").write_text("preserve")
            with self.assertRaisesRegex(RuntimeError,"destination changed"):
                self.ensure_with_test_file_transport(checkout,before_fetch=mutate)
            self.assertEqual((child/"personal").read_text(),"preserve")
            self.assertNotIn("submodule.first-party/clean.url",self.git(checkout,"config","--local","--list").stdout)

    def test_materialized_unregistered_child_is_registered_without_fetch_or_head_movement(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout=self.partial_checkout(directory);child=checkout/"first-party/ay";head=self.git(child,"rev-parse","HEAD").stdout.strip()
            self.git(checkout,"config","--local","--unset-all","submodule.first-party/ay.url")
            acquired=self.ensure_with_test_file_transport(checkout)
            self.assertEqual(len(acquired),1);self.assertIn("clean-source",acquired[0][0])
            self.assertEqual(self.git(child,"rev-parse","HEAD").stdout.strip(),head)
            self.assertTrue(all(row[0]==" " for row in self.git(checkout,"submodule","status").stdout.splitlines()))

    def test_indexed_gitlink_oid_is_retained_and_missing_index_row_refuses_before_agh(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout=self.partial_checkout(directory)
            with patch.object(recreate_bootstrap,"_submodule_url_is_allowed",return_value=True):
                entries=recreate_bootstrap._indexed_submodules(checkout)
            self.assertEqual(len(entries),2)
            self.assertTrue(all(len(row.oid)==40 and len(row.modules_blob)==40 for row in entries))
            self.git(checkout,"update-index","--force-remove","first-party/clean")
            with patch.object(recreate_bootstrap,"_submodule_url_is_allowed",return_value=True),patch.object(recreate_bootstrap,"_agh_source_fetch")as fetch,self.assertRaisesRegex(RuntimeError,"not one stage0 SHA1 gitlink"):
                recreate_bootstrap.ensure_submodules(checkout)
            fetch.assert_not_called()

    def test_agh_private_ref_must_name_exact_indexed_oid_even_if_object_is_present(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout=self.partial_checkout(directory);source=Path(directory)/"clean-source"
            (source/"new").write_text("different commit")
            self.git(source,"add","new");self.git(source,"commit","-qm","later")
            wrong=self.git(source,"rev-parse","HEAD").stdout.strip()
            def acquire(url,destination,oid,private_ref,*,scratch_parent):
                self.assertEqual(scratch_parent,destination.parent)
                self.git(destination,"fetch","--quiet",url,wrong+":"+private_ref)
                return {"commit":oid}
            with patch.object(recreate_bootstrap,"_submodule_url_is_allowed",return_value=True),patch.object(
                recreate_bootstrap,"_agh_source_fetch",side_effect=acquire
            ),self.assertRaisesRegex(RuntimeError,"private ref differs"):
                recreate_bootstrap.ensure_submodules(checkout)
            self.assertEqual(list((checkout/"first-party/clean").iterdir()),[])

    def test_missing_objects_cannot_fall_back_to_fixed_git_network(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout=self.partial_checkout(directory)
            with patch.object(recreate_bootstrap,"_submodule_url_is_allowed",return_value=True),patch.object(
                recreate_bootstrap,"_agh_source_fetch",return_value={}
            ),patch.object(recreate_bootstrap,"_run_submodule_update_process")as process,self.assertRaisesRegex(RuntimeError,"fixed local Git"):
                recreate_bootstrap.ensure_submodules(checkout)
            process.assert_not_called()

    def test_parent_configuration_changed_during_fetch_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout=self.partial_checkout(directory)
            def mutate(*args):self.git(checkout,"config","local.test","preserve concurrent config")
            with self.assertRaisesRegex(RuntimeError,"registration changed during acquisition"):
                self.ensure_with_test_file_transport(checkout,after_fetch=mutate)
            self.assertEqual(self.git(checkout,"config","local.test").stdout.strip(),"preserve concurrent config")
            self.assertNotIn("submodule.first-party/clean.url",self.git(checkout,"config","--local","--list").stdout)

    def test_unknown_existing_child_contents_refuse_before_any_agh_call(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout=self.partial_checkout(directory);child=checkout/"first-party/clean";(child/"personal").write_text("keep")
            with patch.object(recreate_bootstrap,"_submodule_url_is_allowed",return_value=True),patch.object(
                recreate_bootstrap,"_agh_source_fetch"
            )as acquire,self.assertRaisesRegex(RuntimeError,"unknown existing data"):
                recreate_bootstrap.ensure_submodules(checkout)
            acquire.assert_not_called();self.assertEqual((child/"personal").read_text(),"keep")

    def test_symbolic_child_directory_cannot_redirect_acquisition(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout=self.partial_checkout(directory);child=checkout/"first-party/clean";child.rmdir()
            external=Path(directory)/"external";external.mkdir();(external/"personal").write_text("keep")
            child.symlink_to(external,target_is_directory=True)
            with patch.object(recreate_bootstrap,"_submodule_url_is_allowed",return_value=True),patch.object(
                recreate_bootstrap,"_agh_source_fetch"
            )as acquire,self.assertRaisesRegex(RuntimeError,"aliased"):
                recreate_bootstrap.ensure_submodules(checkout)
            acquire.assert_not_called();self.assertEqual((external/"personal").read_text(),"keep")

    def test_staged_git_alias_and_shared_objects_refuse_without_touching_target(self):
        for kind in ("git-symlink","alternates","hardlink"):
            with self.subTest(kind=kind),tempfile.TemporaryDirectory()as directory:
                checkout=self.partial_checkout(directory);external=Path(directory)/"external";external.mkdir();(external/"personal").write_text("keep")
                def mutate(url,stage,*args):
                    if kind=="git-symlink":
                        (stage/".git").rename(stage.parent/"retained-git");(stage/".git").symlink_to(external,target_is_directory=True)
                    elif kind=="alternates":
                        (stage/".git/objects/info/alternates").write_text(str(external)+"\n")
                    else:os.link(stage/".git/config",external/"config-link")
                with self.assertRaisesRegex(RuntimeError,"real .git|alternates|aliases/special"):
                    self.ensure_with_test_file_transport(checkout,after_fetch=mutate)
                self.assertEqual((external/"personal").read_text(),"keep")
                self.assertEqual(list((checkout/"first-party/clean").iterdir()),[])

    def test_staged_partial_objects_and_absolute_worktree_are_not_admitted(self):
        for key,value in (("remote.origin.promisor","true"),("core.worktree","STAGE")):
            with self.subTest(key=key),tempfile.TemporaryDirectory()as directory:
                checkout=self.partial_checkout(directory)
                def mutate(url,stage,*args):self.git(stage,"config",key,str(stage)if value=="STAGE"else value)
                with self.assertRaisesRegex(RuntimeError,"defer objects or redirect worktree"):
                    self.ensure_with_test_file_transport(checkout,after_fetch=mutate)

    def test_no_replace_install_preserves_new_empty_destination_and_original_inode(self):
        with tempfile.TemporaryDirectory()as directory:
            checkout=self.partial_checkout(directory);child=checkout/"first-party/clean";original=child.stat().st_ino;config=(checkout/".git/config").read_bytes();created=[]
            factory=recreate_bootstrap._submodule_exclusive_move
            def substitute(parent,container):
                move,close=factory(parent,container)
                def inject(source,destination):
                    if source.name=="source"and destination==child:
                        destination.mkdir();created.append(destination.stat().st_ino)
                    move(source,destination)
                return inject,close
            with patch.object(recreate_bootstrap,"_submodule_exclusive_move",side_effect=substitute),self.assertRaises(OSError):
                self.ensure_with_test_file_transport(checkout)
            self.assertEqual(child.stat().st_ino,created[0]);self.assertEqual(list(child.iterdir()),[])
            preserved=list((checkout/"first-party").glob(".trust-submodule-*/original-empty"));self.assertEqual(len(preserved),1);self.assertEqual(preserved[0].stat().st_ino,original)
            self.assertEqual((checkout/".git/config").read_bytes(),config)

    def test_parent_index_lock_and_existing_owner_lock_are_never_removed(self):
        for name in ("index.lock","trust-bootstrap-submodules.lock"):
            with self.subTest(name=name),tempfile.TemporaryDirectory()as directory:
                checkout=self.partial_checkout(directory);lock=checkout/".git"/name;lock.write_text("unknown owner: preserve")
                with patch.object(recreate_bootstrap,"_submodule_url_is_allowed",return_value=True),patch.object(
                    recreate_bootstrap,"_agh_source_fetch"
                )as acquire,self.assertRaisesRegex(RuntimeError,"locked|existing lock"):
                    recreate_bootstrap.ensure_submodules(checkout)
                acquire.assert_not_called();self.assertEqual(lock.read_text(),"unknown owner: preserve")

    def test_unmerged_gitlink_refuses_before_agh(self):
        with tempfile.TemporaryDirectory()as directory:
            checkout=self.partial_checkout(directory);oid=self.git(Path(directory)/"clean-source","rev-parse","HEAD").stdout.strip()
            data=f"0 {'0'*40}\tfirst-party/clean\n160000 {oid} 1\tfirst-party/clean\n160000 {oid} 2\tfirst-party/clean\n"
            subprocess.run(["git","-C",str(checkout),"update-index","--index-info"],input=data,text=True,check=True)
            with patch.object(recreate_bootstrap,"_submodule_url_is_allowed",return_value=True),patch.object(
                recreate_bootstrap,"_agh_source_fetch"
            )as acquire,self.assertRaisesRegex(RuntimeError,"unmerged or unsupported indexed gitlink"):
                recreate_bootstrap.ensure_submodules(checkout)
            acquire.assert_not_called()

    def test_absent_child_destination_installs_detached_and_has_canonical_origin(self):
        with tempfile.TemporaryDirectory()as directory:
            checkout=self.partial_checkout(directory);child=checkout/"first-party/clean";child.rmdir()
            acquired=self.ensure_with_test_file_transport(checkout)
            self.assertEqual(len(acquired),1)
            self.assertEqual(self.git(child,"rev-parse","HEAD").stdout.strip(),acquired[0][1])
            self.assertEqual(self.git(child,"remote","get-url","origin").stdout.strip(),acquired[0][0])
            detached=subprocess.run(["git","-C",str(child),"symbolic-ref","--quiet","HEAD"],capture_output=True)
            self.assertEqual(detached.returncode,1)
            self.assertTrue((child/".git").is_dir())

    def test_materialization_owner_is_held_through_cleanup_and_final_inspection(self):
        with tempfile.TemporaryDirectory()as directory:
            repository=Path(directory)/"repository";self.create_repository(repository,"owner-fixture");probes=[]
            def held(root):
                with self.assertRaisesRegex(RuntimeError,"existing lock"):
                    with recreate_bootstrap._submodule_owner_lock(root):
                        self.fail("second materialization acquired ownership")
                probes.append(True)
            def inspect(root):held(root);return []
            with patch.object(recreate_bootstrap,"_initialize_missing_submodules",return_value=0),patch.object(
                recreate_bootstrap,"_inspect_submodule_tree",side_effect=inspect
            ),patch.object(recreate_bootstrap,"scrub_pat_from_remotes",side_effect=held):
                recreate_bootstrap._materialize_missing_submodules(repository)
            self.assertEqual(len(probes),3)
            self.assertFalse((repository/".git/trust-bootstrap-submodules.lock").exists())

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

    def declare_clean_branch(self, checkout: Path, line: str) -> None:
        """Write one more line into clean's indexed declaration, the last section of .gitmodules."""
        modules = checkout / ".gitmodules"
        declared = self.git(checkout, "show", "HEAD:.gitmodules").stdout
        self.assertTrue(declared.rstrip().endswith("clean-source"))
        modules.write_text(declared + line + "\n", encoding="utf-8")
        self.git(checkout, "add", ".gitmodules")

    def test_an_indexed_branch_declaration_is_admitted_and_the_child_stays_at_its_gitlink(self):
        # aterm declares vendor/astream with `branch = main`; the first train tick to reach
        # before_cut ended there on "unsupported indexed .gitmodules key" (2026-11-17).
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            source = Path(directory) / "clean-source"
            pin = self.git(checkout, "rev-parse", ":first-party/clean").stdout.strip()
            branch = self.git(source, "symbolic-ref", "--short", "HEAD").stdout.strip()
            # The declared branch moves past the gitlink: `submodule update --remote` would follow it.
            (source / "later").write_text("past the pin\n", encoding="utf-8")
            self.git(source, "add", "later")
            self.git(source, "commit", "--quiet", "-m", "later")
            self.assertNotEqual(self.git(source, "rev-parse", "HEAD").stdout.strip(), pin)
            self.declare_clean_branch(checkout, "\tbranch = " + branch)
            with patch.object(recreate_bootstrap, "_submodule_url_is_allowed", return_value=True):
                self.assertEqual(
                    {(row.path.as_posix(), row.oid) for row in recreate_bootstrap._indexed_submodules(checkout)},
                    {("first-party/ay", self.git(checkout, "rev-parse", ":first-party/ay").stdout.strip()),
                     ("first-party/clean", pin)})
            acquired = self.ensure_with_test_file_transport(checkout)
            self.assertEqual([row[1] for row in acquired], [pin])
            child = checkout / "first-party/clean"
            self.assertEqual(self.git(child, "rev-parse", "HEAD").stdout.strip(), pin)
            self.assertFalse((child / "later").exists())
            self.assertTrue(all(row[0] == " " for row in self.git(checkout, "submodule", "status").stdout.splitlines()))

    PLAIN_BRANCHES = (".", "main", "release/1.2", "feature_x-1", "v0.15.0")
    UNSAFE_BRANCHES = ("", "-main", "--upload-pack=x", "+main", "main..other", "main...other", "main~1", "main^",
                       "main^{commit}", "main:other", "@{u}", "main@{1}", "*", "a b", ".hidden", "main.", "main.lock",
                       "main/", "/main", "a//b", "a/.b", "a/-b", "..", "refs/heads/x y", "ma\tin", "m\u00e4in",
                       "m" * 256)

    def test_a_declared_branch_is_a_plain_name_or_the_superprojects_own(self):
        for value in self.PLAIN_BRANCHES:
            self.assertTrue(recreate_bootstrap._submodule_branch_is_plain(value), value)
        for value in self.UNSAFE_BRANCHES:
            self.assertFalse(recreate_bootstrap._submodule_branch_is_plain(value), value)

    def test_an_indexed_branch_that_is_not_a_plain_name_is_refused_before_agh(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            for value in ("-main", "main..other", "main^{commit}", "main:other", "a b", ".hidden", "main.lock"):
                with self.subTest(value=value):
                    self.declare_clean_branch(checkout, "\tbranch = " + value)
                    with patch.object(recreate_bootstrap, "_submodule_url_is_allowed", return_value=True), patch.object(
                        recreate_bootstrap, "_agh_source_fetch"
                    ) as fetch, self.assertRaisesRegex(RuntimeError, r"unsafe indexed submodule branch") as raised:
                        recreate_bootstrap.ensure_submodules(checkout)
                    fetch.assert_not_called()
                    self.assertNotIn(value, str(raised.exception))
            self.assertEqual(list((checkout / "first-party/clean").iterdir()), [])

    def test_every_other_indexed_declaration_key_is_still_refused_before_agh(self):
        # Each changes what a command this owner does run reports or fetches.
        with tempfile.TemporaryDirectory() as directory:
            checkout = self.partial_checkout(directory)
            for line in ("\tignore = all", "\tshallow = true", "\tfetchRecurseSubmodules = true", "\tactive = false",
                         "\tbranches = main"):
                with self.subTest(line=line):
                    self.declare_clean_branch(checkout, line)
                    with patch.object(recreate_bootstrap, "_submodule_url_is_allowed", return_value=True), patch.object(
                        recreate_bootstrap, "_agh_source_fetch"
                    ) as fetch, self.assertRaisesRegex(RuntimeError, r"unsupported indexed \.gitmodules key"):
                        recreate_bootstrap.ensure_submodules(checkout)
                    fetch.assert_not_called()
            # Two branch records for one child are a duplicate, as two URLs are.
            self.declare_clean_branch(checkout, "\tbranch = main\n\tbranch = other")
            with patch.object(recreate_bootstrap, "_submodule_url_is_allowed", return_value=True), patch.object(
                recreate_bootstrap, "_agh_source_fetch"
            ) as fetch, self.assertRaisesRegex(RuntimeError, r"duplicate indexed \.gitmodules branch record"):
                recreate_bootstrap.ensure_submodules(checkout)
            fetch.assert_not_called()

    def test_no_owner_of_a_materialized_child_follows_a_declared_branch(self):
        """`branch` is admitted because Git reads it only for `submodule update --remote`, which none passes."""
        scripts = SCRIPT.parent
        for name in ("recreate_bootstrap.py", "daily_toolchain_stage.py", "daily_dependency_git.py"):
            words = {node.value for node in ast.walk(ast.parse((scripts / name).read_text(encoding="utf-8")))
                     if isinstance(node, ast.Constant) and isinstance(node.value, str)}
            self.assertFalse({"--remote", "--remote-submodules"} & words, name)
        self.assertNotIn("--remote", (scripts / "submodule_sync.sh").read_text(encoding="utf-8"))

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
            ("core.hooksPath", "scripts/hooks"),
            ("core.hooksPath", "scripts/hooks-pin"),
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

    def test_source_root_hooks_and_disabled_sparse_worktree_scope_are_inert(self):
        for maintained in ("scripts/hooks", "scripts/hooks-pin"):
            with self.subTest(maintained=maintained), tempfile.TemporaryDirectory() as directory:
                repository = Path(directory) / "repository"
                self.create_repository(repository, "source-root-git-config")
                self.git(repository, "config", "extensions.worktreeConfig", "true")
                linked = Path(directory) / "linked"
                self.git(repository, "worktree", "add", "--quiet", "--detach", str(linked))
                self.git(repository, "config", "core.hooksPath", maintained)
                for checkout in (repository, linked):
                    with self.subTest(checkout=checkout):
                        def config_bytes():
                            result = {}
                            for name in ("config", "config.worktree"):
                                path = Path(self.git(checkout, "rev-parse", "--git-path", name).stdout.strip())
                                if not path.is_absolute():
                                    path = checkout / path
                                result[name] = path.read_bytes() if path.exists() else None
                            return result

                        hooks = checkout / maintained
                        hooks.mkdir(parents=True)
                        hook = hooks / "post-checkout"
                        hook.write_text('#!/bin/sh\n: > "$0-ran"\n', encoding="utf-8")
                        hook.chmod(0o755)
                        marker = hooks / "post-checkout-ran"
                        # A normal Git command proves the configured hook is live.
                        self.git(checkout, "checkout", "--quiet", "--detach", "HEAD")
                        self.assertTrue(marker.exists())
                        marker.unlink()
                        with patch.object(recreate_bootstrap, "repo_root", return_value=checkout):
                            # An absent optional worktree scope is admitted too.
                            before = config_bytes()
                            recreate_bootstrap._run_git_read(
                                checkout, ["checkout", "--quiet", "--detach", "HEAD"]
                            )
                            self.assertEqual(before, config_bytes())
                            for key in ("core.sparseCheckout", "core.sparseCheckoutCone", "index.sparse"):
                                self.git(checkout, "config", "--worktree", key, "false")
                            records = recreate_bootstrap._repository_git_config_records(checkout)
                            before = config_bytes()
                            recreate_bootstrap._run_git_read(
                                checkout, ["checkout", "--quiet", "--detach", "HEAD"]
                            )
                            self.assertEqual(before, config_bytes())
                            self.assertEqual(
                                records, recreate_bootstrap._repository_git_config_records(checkout)
                            )
                        self.assertFalse(marker.exists(), "bootstrap executed repository hooks")
                        self.assertEqual(
                            self.git(checkout, "config", "core.hooksPath").stdout.strip(), maintained,
                        )

    def test_source_root_hook_exception_is_local_and_maintained_only(self):
        for scope, value in (
            ("local", "scripts/arbitrary-hooks"),
            ("local", "/tmp/hostile-hooks"),
            ("worktree", "scripts/hooks"),
            ("worktree", "scripts/hooks-pin"),
        ):
            with self.subTest(scope=scope, value=value), tempfile.TemporaryDirectory() as directory:
                repository = Path(directory) / "repository"
                self.create_repository(repository, "source-root-hook-refusal")
                self.git(repository, "config", "extensions.worktreeConfig", "true")
                self.git(repository, "config", f"--{scope}", "core.hooksPath", value)
                with patch.object(recreate_bootstrap, "repo_root", return_value=repository):
                    with self.assertRaisesRegex(RuntimeError, r"hidden execution"):
                        recreate_bootstrap._run_git_read(repository, ["rev-parse", "--verify", "HEAD"])

    def test_the_installed_ssh_keepalive_is_admitted_with_the_hooks_path_on_a_trust_root_only(self):
        # scripts/install-git-hooks.sh writes both into the clone it installs the push hook in.
        # A gate that kept the hooks path and refused the keepalive refused every such clone:
        # the train's landing worktree at its first read (2026-11-17), and this recreator in a
        # developer's hook-installed checkout.
        keepalive = recreate_bootstrap.INSTALLED_SSH_KEEPALIVE_COMMAND
        declared = re.search(r'^TRUST_SSH_KEEPALIVE_COMMAND="([^"]*)"$',
                             (SCRIPT.parent / "hooks/_ssh_keepalive.sh").read_text(encoding="utf-8"), re.MULTILINE)
        self.assertIsNotNone(declared)
        self.assertEqual(declared.group(1), keepalive)
        # No command of this owner can run it: ssh is denied by name on every one.
        self.assertIn("protocol.ssh.allow=never", recreate_bootstrap.CONTROLLED_GIT_CONFIG_OVERRIDES)
        self.assertIn("protocol.ssh.allow=never", recreate_bootstrap._controlled_git_command([]))
        read = ["rev-parse", "--verify", "HEAD"]
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "installed-keepalive")
            linked = Path(directory) / "linked"
            self.git(repository, "worktree", "add", "--quiet", "--detach", str(linked))
            self.git(repository, "config", "core.hooksPath", "scripts/hooks")
            self.git(repository, "config", "core.sshCommand", keepalive)
            config = (repository / ".git/config").read_bytes()
            # Any other repository still refuses both: a child, a sibling, a snapshot.
            for checkout in (repository, linked):
                with self.subTest(refused=checkout), self.assertRaisesRegex(
                        RuntimeError, r"local:core\.hookspath, local:core\.sshcommand"):
                    recreate_bootstrap._run_git_read(checkout, read)
            # The recreator's own root keeps what its installer wrote.
            with patch.object(recreate_bootstrap, "repo_root", return_value=repository):
                recreate_bootstrap._run_git_read(repository, read)
            # So does a checkout a caller admits (the train's landing worktree), and only it.
            with recreate_bootstrap.admitted_trust_checkout(linked):
                recreate_bootstrap._run_git_read(linked, read)
                with self.assertRaisesRegex(RuntimeError, r"local:core\.sshcommand"):
                    recreate_bootstrap._run_git_read(repository, read)
            with self.assertRaisesRegex(RuntimeError, r"local:core\.sshcommand"):
                recreate_bootstrap._run_git_read(linked, read)
            self.assertEqual((repository / ".git/config").read_bytes(), config)

    def test_any_other_ssh_command_is_refused_on_a_trust_root(self):
        keepalive = recreate_bootstrap.INSTALLED_SSH_KEEPALIVE_COMMAND
        settings = (
            (("local", "/usr/bin/false"),),
            (("local", "ssh"),),
            (("local", keepalive + " -o ProxyCommand=/usr/bin/false"),),
            (("local", keepalive + " -i /tmp/key"),),
            (("local", "/opt/other/" + keepalive),),
            (("local", keepalive.replace("=30", "=31")),),
            (("local", "ssh -o ServerAliveCountMax=10 -o ServerAliveInterval=30"),),
            (("local", keepalive + "; /usr/bin/false"),),
            # One admitted value does not carry a second.
            (("local", keepalive), ("local", "/usr/bin/false")),
            # The installer writes the clone's own config, never a worktree scope.
            (("worktree", keepalive),),
        )
        for values in settings:
            with self.subTest(values=values), tempfile.TemporaryDirectory() as directory:
                repository = Path(directory) / "repository"
                self.create_repository(repository, "other-ssh-command")
                self.git(repository, "config", "extensions.worktreeConfig", "true")
                for scope, value in values:
                    self.git(repository, "config", f"--{scope}", "--add", "core.sshCommand", value)
                with patch.object(recreate_bootstrap, "repo_root", return_value=repository), self.assertRaisesRegex(
                        RuntimeError, r"hidden execution.*core\.sshcommand"):
                    recreate_bootstrap._run_git_read(repository, ["rev-parse", "--verify", "HEAD"])
                with recreate_bootstrap.admitted_trust_checkout(repository), self.assertRaisesRegex(
                        RuntimeError, r"hidden execution.*core\.sshcommand"):
                    recreate_bootstrap._run_git_read(repository, ["rev-parse", "--verify", "HEAD"])

    def test_source_root_worktree_exception_refuses_unknown_enabled_and_duplicate_values(self):
        settings = (
            (("core.sparseCheckout", "true"),),
            (("core.sparseCheckout", "invalid"),),
            (("core.sparseCheckout", "true"), ("core.sparseCheckout", "false")),
            (("user.name", "Unsupported worktree override"),),
            (("include.path", "/tmp/hostile-git-config"),),
            (("credential.helper", "!hostile-helper"),),
        )
        for values in settings:
            with self.subTest(values=values), tempfile.TemporaryDirectory() as directory:
                repository = Path(directory) / "repository"
                self.create_repository(repository, "source-root-worktree-refusal")
                self.git(repository, "config", "extensions.worktreeConfig", "true")
                for key, value in values:
                    self.git(repository, "config", "--worktree", "--add", key, value)
                # Git itself refuses an invalid sparse boolean before even
                # resolving config.worktree; the inspection must fail closed.
                diagnostic = (
                    r"could not locate worktree Git config"
                    if any(value == "invalid" for _, value in values)
                    else r"extensions\.worktreeconfig"
                )
                with patch.object(
                    recreate_bootstrap, "repo_root", return_value=repository
                ), self.assertRaisesRegex(RuntimeError, diagnostic):
                    recreate_bootstrap._run_git_read(
                        repository, ["rev-parse", "--verify", "HEAD"]
                    )

    def test_disabled_sparse_worktree_exception_does_not_extend_to_submodules(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "other-repository-worktree-refusal")
            self.git(repository, "config", "extensions.worktreeConfig", "true")
            for key in ("core.sparseCheckout", "core.sparseCheckoutCone", "index.sparse"):
                self.git(repository, "config", "--worktree", key, "false")
            with self.assertRaisesRegex(RuntimeError, r"extensions\.worktreeconfig"):
                recreate_bootstrap._run_git_read(
                    repository, ["rev-parse", "--verify", "HEAD"]
                )

    def test_absent_optional_worktree_config_preserves_local_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "optional-worktree-config")
            self.git(repository, "config", "extensions.worktreeConfig", "true")
            linked = Path(directory) / "linked"
            self.git(repository, "worktree", "add", "--quiet", "--detach", str(linked))
            for checkout in (repository, linked):
                with self.subTest(checkout=checkout):
                    records = recreate_bootstrap._repository_git_config_records(checkout)
                    self.assertIn(("local", "user.name", "Bootstrap Test"), records)
                    self.assertFalse(any(scope == "worktree" for scope, _, _ in records))
                    # Absence is not a waiver for the separate policy boundary.
                    with self.assertRaisesRegex(RuntimeError, r"extensions\.worktreeconfig"):
                        recreate_bootstrap._reject_local_git_execution_authority(checkout)
            self.git(linked, "config", "--worktree", "user.name", "Linked User")
            records = recreate_bootstrap._repository_git_config_records(linked)
            self.assertIn(("local", "user.name", "Bootstrap Test"), records)
            self.assertIn(("worktree", "user.name", "Linked User"), records)

    def test_optional_worktree_config_refuses_nonregular_and_permission_errors(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "unsafe-worktree-config")
            self.git(repository, "config", "extensions.worktreeConfig", "true")
            config = repository / ".git" / "config.worktree"
            for kind in ("directory", "symlink", "broken-symlink"):
                with self.subTest(kind=kind):
                    if kind == "directory":
                        config.mkdir()
                    else:
                        config.symlink_to("config" if kind == "symlink" else "absent-config")
                    try:
                        with self.assertRaisesRegex(RuntimeError, "worktree Git config"):
                            recreate_bootstrap._read_repository_git_config_scope(repository, "worktree")
                    finally:
                        config.rmdir() if kind == "directory" else config.unlink()
            real_lstat = Path.lstat
            def inaccessible(path):
                if path == config:
                    raise PermissionError("permission denied by fixture")
                return real_lstat(path)
            with patch.object(Path, "lstat", inaccessible), self.assertRaisesRegex(
                RuntimeError, "permission denied by fixture"
            ):
                recreate_bootstrap._read_repository_git_config_scope(repository, "worktree")

    def test_worktree_config_disappearance_during_read_is_not_absence(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory) / "repository"
            self.create_repository(repository, "racing-worktree-config")
            self.git(repository, "config", "extensions.worktreeConfig", "true")
            self.git(repository, "config", "--worktree", "user.name", "Linked User")
            before = recreate_bootstrap._worktree_config_snapshot(repository)
            with patch.object(
                recreate_bootstrap, "_worktree_config_snapshot", side_effect=[before, None]
            ), self.assertRaisesRegex(RuntimeError, "changed while being read"):
                recreate_bootstrap._read_repository_git_config_scope(repository, "worktree")

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

    def test_target_qualified_ay_is_not_replaced_by_stale_flat_or_later_tools(self):
        with tempfile.TemporaryDirectory() as directory:
            root, bindir, _producer_dir = self.layout(directory)
            producer = root / "build" / self.host / "stage3-tools-bin" / self.host / "ay"
            producer.parent.mkdir(parents=True, exist_ok=True)
            producer.write_bytes(b"current-stage2-ay")
            os.link(producer, bindir / "ay")
            (producer.parent.parent / "ay").write_bytes(b"stale-flat-ay")
            later = root / "build" / self.host / "stage4-tools-bin" / self.host / "ay"
            later.parent.mkdir(parents=True)
            later.write_bytes(b"stale-later-stage-ay")

            with patch.object(recreate_bootstrap.subprocess, "run") as run:
                self.assertTrue(recreate_bootstrap.install_ay_solver(root, self.host, 2))
            run.assert_not_called()
            self.assertEqual((bindir / "ay").read_bytes(), b"current-stage2-ay")
            self.assertTrue(os.path.samefile(producer, bindir / "ay"))
            self.assertEqual((producer.parent.parent / "ay").read_bytes(), b"stale-flat-ay")
            self.assertEqual(later.read_bytes(), b"stale-later-stage-ay")

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

    def test_flat_ay_producer_wins_over_a_stale_nested_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root, bindir, producer_dir = self.layout(directory)
            (producer_dir / "ay").write_bytes(b"current-flat-ay")
            nested = producer_dir / self.host / "ay"
            nested.parent.mkdir()
            nested.write_bytes(b"stale-nested-ay")
            with patch.object(recreate_bootstrap.subprocess, "run") as run:
                self.assertTrue(recreate_bootstrap.install_ay_solver(root, self.host, 2))
            run.assert_not_called()
            self.assertEqual((bindir / "ay").read_bytes(), b"current-flat-ay")
            self.assertEqual(nested.read_bytes(), b"stale-nested-ay")

    def test_nested_ay_without_a_flat_producer_is_not_installed(self):
        with tempfile.TemporaryDirectory() as directory:
            root, bindir, producer_dir = self.layout(directory)
            nested = producer_dir / self.host / "ay"
            nested.parent.mkdir()
            nested.write_bytes(b"wrong-layout-ay")
            with patch.object(recreate_bootstrap.subprocess, "run") as run:
                self.assertFalse(recreate_bootstrap.install_ay_solver(root, self.host, 2))
            run.assert_not_called()
            self.assertFalse((bindir / "ay").exists())


class StageToolProvenanceTests(unittest.TestCase):
    host = "test-host"
    commit = "1" * 40

    def test_external_accepted_receipt_preserves_rejected_origin_and_seals_exact_bytes(self):
        reader = load_stage_receipt_reader()
        with tempfile.TemporaryDirectory() as directory:
            root, stage, _bin, _tools = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage))
            accepted = root / "accepted.json"
            accepted.write_bytes((stage / "tool-provenance.json").read_bytes())
            digest = hashlib.sha256(accepted.read_bytes()).hexdigest()
            rejected = b'{"status":"rejected","errors":["historical unmapped tool"]}\n'
            (stage / "tool-provenance.json").write_bytes(rejected)
            selection = dict(receipt_path=accepted, receipt_sha256=digest, source_root=root)
            expected = reader.lines(stage, self.commit, **selection)
            with self.assertRaises(reader.StageReceiptError):
                reader.lines(stage, self.commit)
            sealed = root / "new-seal"
            shutil.copytree(stage, sealed, copy_function=os.link)
            reader.copy_selected_receipt(stage, self.commit, root, accepted, digest, sealed)
            self.assertEqual(reader.lines(sealed, self.commit), expected)
            self.assertEqual((stage / "tool-provenance.json").read_bytes(), rejected)
            self.assertEqual((sealed / "tool-provenance.json").read_bytes(), accepted.read_bytes())
            with self.assertRaisesRegex(reader.StageReceiptError, "distinct new seal"):
                reader.copy_selected_receipt(stage, self.commit, root, accepted, digest, stage)
            nested = stage / 'nested-copy'
            nested.mkdir()
            for destination in (nested, stage.parent):
                with self.subTest(destination=destination), self.assertRaisesRegex(
                        reader.StageReceiptError, "distinct new seal"):
                    reader.copy_selected_receipt(stage, self.commit, root, accepted, digest, destination)
            self.assertEqual((stage / "tool-provenance.json").read_bytes(), rejected)

    def test_external_receipt_cannot_rebind_an_original_stage_or_compiler(self):
        reader = load_stage_receipt_reader()
        for case in ("copied-stage", "foreign-root", "foreign-host", "foreign-commit", "changed-compiler"):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as directory:
                root, stage, _bin, _tools = self.layout(directory)
                self.assertTrue(self.run_audit(root, stage))
                value = json.loads((stage / "tool-provenance.json").read_bytes())
                selected_stage, source_root = stage, root
                if case == "copied-stage":
                    selected_stage = root / "copy"
                    shutil.copytree(stage, selected_stage)
                elif case == "foreign-root":
                    source_root = root / "foreign"
                    shutil.copytree(stage, source_root / "build" / self.host / "stage2")
                elif case == "foreign-host":
                    value["host"] = "other-host"
                elif case == "foreign-commit":
                    value["compiler"]["source_commit"] = "0" * 40
                else:
                    (stage / "bin/trustc").write_bytes(b"replacement compiler")
                accepted = root / "accepted.json"
                accepted.write_text(json.dumps(value))
                with self.assertRaises(reader.StageReceiptError):
                    reader.lines(selected_stage, self.commit, receipt_path=accepted,
                                 receipt_sha256=hashlib.sha256(accepted.read_bytes()).hexdigest(),
                                 source_root=source_root)

    def test_external_receipt_requires_exact_regular_hash_and_all_selector_fields(self):
        reader = load_stage_receipt_reader()
        with tempfile.TemporaryDirectory() as directory:
            root, stage, _bin, _tools = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage))
            accepted = root / "accepted.json"
            accepted.write_bytes((stage / "tool-provenance.json").read_bytes())
            digest = hashlib.sha256(accepted.read_bytes()).hexdigest()
            link = root / "link.json"
            link.symlink_to(accepted)
            for path, expected in ((accepted, "0" * 64), (link, digest),
                                   (root / "absent.json", digest), (Path("relative.json"), digest)):
                with self.subTest(path=path), self.assertRaises(reader.StageReceiptError):
                    reader.lines(stage, self.commit, receipt_path=path,
                                 receipt_sha256=expected, source_root=root)
            for options in ({"receipt_path": accepted}, {"receipt_sha256": digest},
                            {"source_root": root}):
                with self.subTest(options=options), self.assertRaises(reader.StageReceiptError):
                    reader.lines(stage, self.commit, **options)
            selection = ["--stage-provenance-receipt", str(accepted),
                         "--stage-provenance-sha256", digest, "--source-root", str(root)]
            for options in (selection[:-2], selection + selection[:2]):
                with patch.object(sys, "stderr", io.StringIO()):
                    self.assertEqual(reader.main([*options, str(stage), self.commit]), 2)

    def test_external_llvm_requirement_uses_the_selected_receipt_too(self):
        reader = load_stage_receipt_reader()
        with tempfile.TemporaryDirectory() as directory:
            root, stage, _bin, _tools = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage))
            accepted = root / "accepted.json"
            accepted.write_bytes((stage / "tool-provenance.json").read_bytes())
            digest = hashlib.sha256(accepted.read_bytes()).hexdigest()
            (stage / "tool-provenance.json").write_text('{"status":"rejected"}')
            # This fixture has no stated LLVM. Both reads must see its accepted
            # external audit: exit3 is the LLVM requirement, not rejected exit1.
            with patch.object(sys, "stderr", io.StringIO()), patch.object(
                    sys, "stdout", SimpleNamespace(buffer=io.BytesIO())):
                self.assertEqual(reader.main(["--require-llvm-identity",
                    "--stage-provenance-receipt", str(accepted),
                    "--stage-provenance-sha256", digest, "--source-root", str(root),
                    str(stage), self.commit]), 3)

    def test_external_receipt_copy_refuses_symlink_destination(self):
        reader = load_stage_receipt_reader()
        with tempfile.TemporaryDirectory() as directory:
            root, stage, _bin, _tools = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage))
            accepted = root / "accepted.json"
            accepted.write_bytes((stage / "tool-provenance.json").read_bytes())
            digest = hashlib.sha256(accepted.read_bytes()).hexdigest()
            sealed = root / "new-seal"
            shutil.copytree(stage, sealed)
            (sealed / "tool-provenance.json").unlink()
            (sealed / "tool-provenance.json").symlink_to(accepted)
            before = accepted.read_bytes()
            with self.assertRaisesRegex(reader.StageReceiptError, "regular file"):
                reader.copy_selected_receipt(stage, self.commit, root, accepted, digest, sealed)
            self.assertEqual(accepted.read_bytes(), before)

    def test_external_receipt_shell_copy_uses_original_stage_and_exact_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage, _bin, _tools = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage))
            accepted = root / 'accepted.json'
            accepted.write_bytes((stage/'tool-provenance.json').read_bytes())
            digest = hashlib.sha256(accepted.read_bytes()).hexdigest()
            rejected = b'{"status":"rejected","errors":["original refusal"]}\n'
            (stage/'tool-provenance.json').write_bytes(rejected)
            destination = root/'new-seal'
            shutil.copytree(stage,destination)
            promoter = Path(__file__).resolve().parents[1]/'promote-toolchain.sh'
            source = promoter.read_text()
            begin = source.index('\nPROV_CLASS=""')+1
            helper = root/'helpers.sh'
            helper.write_text(source[begin:source.index('\nprov_report() {',begin)])
            shell = '''set -euo pipefail
source "$1"
PROMOTER_ROOT="$2"; REPO="$3"; SRC="$4"; COMMIT="$5"
STAGE_PROVENANCE_RECEIPT="$6"; STAGE_PROVENANCE_SHA="$7"; DEST="$8"
prov_selected_receipt_action copy
'''
            env = dict(os.environ,PATH=f'{Path(sys.executable).parent}:/usr/bin:/bin')
            result = subprocess.run(['/bin/bash','-c',shell,'copy',str(helper),
                str(promoter.parent.parent),str(root),str(stage),self.commit,
                str(accepted),digest,str(destination)],env=env,capture_output=True,text=True,timeout=10)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual((stage/'tool-provenance.json').read_bytes(),rejected)
            self.assertEqual((destination/'tool-provenance.json').read_bytes(),accepted.read_bytes())

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
        # `rustdoc` is the compat alias of `trustdoc` (cargo spawns `rustdoc` by
        # name for doctests, 76d408e1cd), and the audit requires the pair. The
        # fixture used to install only the Trust name, so every provenance test
        # failed with "missing public stage tools: rustdoc" once the audit
        # started requiring it.
        os.link(bindir / "trustdoc", bindir / "rustdoc")
        helper_producer = tools_dir / "rust-analyzer-proc-macro-srv"
        self.executable(helper_producer, b"proc-macro-helper")
        owned_helper = stage_root / "libexec" / "trust-analyzer-proc-macro-srv"
        owned_helper.parent.mkdir(parents=True)
        os.link(helper_producer, owned_helper)
        return root, stage_root, bindir, tools_dir

    def target_qualified_layout(self, directory: str):
        root, stage_root, bindir, tools_dir = self.layout(directory)
        expected = root / "build" / self.host / "stage3-tools-bin" / self.host
        # Keep these regressions usable against the pre-fix flat fixture too.
        # The expected path is the actual ToolBuild output compiler2 passed to
        # tools_bin_dir: stage3-tools-bin/<target>, never a searched generation.
        if tools_dir != expected:
            saved = tools_dir.with_name("before-target-qualification")
            tools_dir.rename(saved)
            tools_dir.mkdir()
            saved.rename(expected)
        return root, stage_root, bindir, expected

    def test_target_qualified_producers_win_over_stale_flat_and_later_outputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, tools_dir = self.target_qualified_layout(directory)
            for producer in tools_dir.iterdir():
                self.executable(tools_dir.parent / producer.name, b"stale-flat:" + producer.name.encode())
                self.executable(
                    root / "build" / self.host / "stage4-tools-bin" / self.host / producer.name,
                    b"stale-later:" + producer.name.encode(),
                )
            self.assertTrue(self.run_audit(root, stage_root))
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["tools_dir"], f"build/{self.host}/stage3-tools-bin/{self.host}")
            self.assertTrue(self.verify_receipt(root, stage_root, self.lineage()))
            for row in [*receipt["tools"], receipt["proc_macro_helper"]]:
                self.assertEqual(Path(row["producer_path"]).parent, Path(receipt["tools_dir"]))

    def test_equal_bytes_at_flat_later_or_other_target_cannot_replace_required_producers(self):
        for wrong_layout in ("flat", "later-stage", "other-target"):
            with self.subTest(wrong_layout=wrong_layout), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, tools_dir = self.target_qualified_layout(directory)
                self.assertTrue(self.run_audit(root, stage_root))
                wrong = {
                    "flat": tools_dir.parent,
                    "later-stage": root / "build" / self.host / "stage4-tools-bin" / self.host,
                    "other-target": tools_dir.with_name("other-target"),
                }[wrong_layout]
                for producer in tools_dir.iterdir():
                    self.executable(wrong / producer.name, producer.read_bytes())
                tools_dir.rename(root / "saved-required-producers")
                self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))
                self.assertFalse(self.run_audit(root, stage_root))

    def test_receipt_cannot_rebind_target_producers_to_equal_flat_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, tools_dir = self.target_qualified_layout(directory)
            self.assertTrue(self.run_audit(root, stage_root))
            path = stage_root / "tool-provenance.json"
            receipt = json.loads(path.read_text())
            flat = tools_dir.parent
            for producer in tools_dir.iterdir():
                self.executable(flat / producer.name, producer.read_bytes())
            receipt["tools_dir"] = f"build/{self.host}/stage3-tools-bin"
            for row in [*receipt["tools"], receipt["proc_macro_helper"]]:
                row["producer_path"] = str(Path(receipt["tools_dir"]) / Path(row["producer_path"]).name)
            path.write_text(json.dumps(receipt))
            before = path.read_bytes()
            self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))
            self.assertEqual(path.read_bytes(), before)

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

    @classmethod
    def atpkg_lineage(cls):
        # Trust-from-Trust without a seed: the stage0 an installed pack ships.
        # `_atpkg_authority_ready` is what admits the pack; a test that binds
        # this lineage answers for it.
        return {
            **cls.bootstrap_lineage(status="local_genesis"),
            "status": "local_atpkg",
            "mode": "atpkg",
            "trust_from_trust": True,
            "declared_stage0_overrides": [],
            "genesis_adapter": None,
            "atpkg_authority": {"authority_sha256": "7" * 64, "authority": {"pack": "fixture"}},
        }

    @classmethod
    def with_host_record(cls, lineage, kind: str):
        """`lineage` whose seed capture selected a host record of `kind`, `mint` or
        `fixed-point`, where capture_validated_seed_lineage records it
        (authority.seed_ledger.host_records). The fixed-point record discloses what
        scripts/seed_fixed_point.py admits, read from that file."""
        lineage = copy.deepcopy(lineage)
        helper = recreate_bootstrap.seed_host_ledger_module()
        if kind == "mint":
            record = {"schema": helper.SCHEMA, "host": cls.host, "mint": {"self_host_proof": "pass"}}
        else:
            fp = helper.fixed_point_module()
            record = {"schema": helper.FIXED_POINT_SCHEMA, "host": cls.host, "admission_kind": fp.KIND,
                      "root_disclosure": {**dict(fp.DISCLOSURE), "stock_built_ancestor": fp.STOCK_ANCESTOR,
                                          "stock_built_ancestor_commit": fp.STOCK_ANCESTOR_COMMIT,
                                          "root_commit": fp.ROOT_COMMIT}}
        lineage["validated_seed"]["authority"] = {
            "schema": "trust.seed-authority.v1",
            "seed_ledger": {"host_records": {"selected_host": cls.host, "records": {cls.host: record}}},
        }
        return lineage

    # What the reader writes of a seed whose selected host record is a fixed point.
    FIXED_POINT_PROVENANCE = [
        "stage_receipt_seed_admission=fixed-point-unpinned-root",
        "stage_receipt_seed_root_disclosure=root=unpinned-host-chain predecessor_pin=none "
        "double_compile_diverse=false stock_built_ancestor=inferred-no-receipt",
    ]

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
        invocation=None,
        llvm_before=None,
        llvm_source=None,
        build_authority=None,
        build_authority_before=None,
        receipt_path=None,
    ):
        before = self.lineage() if before is None else before
        after = before if after is None else after
        if bootstrap_before is None:
            bootstrap_before = self.bootstrap_lineage(hydrated=False)
            if bootstrap_after is None:
                bootstrap_after = self.bootstrap_lineage(hydrated=True)
        elif bootstrap_after is None:
            bootstrap_after = bootstrap_before
        build_authority = self.build_authority() if build_authority is None else build_authority
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
        ), patch.object(
            # The fixture tree is not a git repository; only an audit that is
            # handed `llvm_before` asks.
            recreate_bootstrap,
            "capture_llvm_source_identity",
            return_value=self.llvm_source() if llvm_source is None else llvm_source,
        ):
            return recreate_bootstrap.audit_stage_tool_provenance(
                root,
                self.host,
                2,
                before,
                bootstrap_before,
                build_authority if build_authority_before is None else build_authority_before,
                **({} if invocation is None else {"invocation": invocation}),
                **({} if llvm_before is None else {"llvm_before": llvm_before}),
                **({} if receipt_path is None else {"receipt_path": receipt_path}),
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
        require_llvm_identity: bool = False,
        llvm_source=None,
        build_authority=None,
        receipt_path=None,
    ):
        bootstrap = self.bootstrap_lineage() if bootstrap is None else bootstrap
        build_authority = self.build_authority() if build_authority is None else build_authority
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
        ), patch.object(
            recreate_bootstrap,
            "capture_llvm_source_identity",
            return_value=self.llvm_source() if llvm_source is None else llvm_source,
        ):
            return recreate_bootstrap.verify_stage_tool_provenance(
                root,
                self.host,
                2,
                require_immutable_lineage=require_immutable_lineage,
                require_public_release=require_public_release,
                # Only when asked: every other call is the one main made
                # before the requirement existed.
                **({"require_llvm_identity": True} if require_llvm_identity else {}),
                **({} if receipt_path is None else {"receipt_path": receipt_path}),
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
                all(tool["producer_compiler_stage"] == 1 for tool in receipt["tools"])
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
            self.assertEqual(receipt["rustdoc_alias"]["status"], "bound")
            self.assertEqual(receipt["rustdoc_alias"]["owner"], "trustdoc")
            self.assertTrue(receipt["rustdoc_alias"]["same_inode"])
            self.assertEqual(
                receipt["rustdoc_alias"]["sha256"], receipt["rustdoc_alias"]["owner_sha256"]
            )
            self.assertTrue(receipt["proc_macro_helper"]["retired_public_path_absent"])
            self.assertEqual(receipt["proc_macro_helper"]["producer_compiler_stage"], 1)
            self.assertEqual(receipt["compiler"]["producer_compiler_stage"], 1)
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

    def test_tool_and_helper_generation_labels_are_exact_previous_stage_integers(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage_root))
            receipt_path = stage_root / "tool-provenance.json"
            original = receipt_path.read_bytes()
            for member in ("tool", "helper"):
                for invalid in (0, 2, 3, True, 1.0):
                    with self.subTest(member=member, invalid=invalid):
                        receipt = json.loads(original)
                        row = (next(row for row in receipt["tools"] if row["name"] == "targo")
                               if member == "tool" else receipt["proc_macro_helper"])
                        row["producer_compiler_stage"] = invalid
                        changed = json.dumps(receipt).encode()
                        receipt_path.write_bytes(changed)
                        self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))
                        self.assertEqual(receipt_path.read_bytes(), changed)
            receipt_path.write_bytes(original)
            self.assertTrue(self.verify_receipt(root, stage_root, self.lineage()))

    def test_copied_tool_and_helper_are_bound_by_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, bindir, tools_dir = self.layout(directory)
            helper = stage_root / "libexec" / "trust-analyzer-proc-macro-srv"
            for installed in (bindir / "targo-trust", helper):
                content = installed.read_bytes()
                installed.unlink()
                self.executable(installed, content)
            self.assertTrue(self.run_audit(root, stage_root))
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            tool = next(row for row in receipt["tools"] if row["name"] == "targo-trust")
            self.assertFalse(tool["same_inode"])
            self.assertFalse(receipt["proc_macro_helper"]["same_inode"])
            self.assertTrue(self.verify_receipt(root, stage_root, self.lineage()))
            # Same path and mode with different bytes still refuses read-back.
            self.executable(helper, b"changed-helper")
            self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))

    def test_an_adjacent_tools_generation_cannot_supply_the_stage_producers(self):
        for adjacent_stage in (2, 4):
            with self.subTest(adjacent_stage=adjacent_stage), \
                    tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, tools_dir = self.layout(directory)
                adjacent = root / "build" / self.host / f"stage{adjacent_stage}-tools-bin" / self.host
                adjacent.parent.mkdir(parents=True, exist_ok=True)
                # Preserve every byte and installed hard link. Only the claimed
                # producing generation is wrong, so equal bytes cannot admit it.
                tools_dir.rename(adjacent)
                self.assertFalse(self.run_audit(root, stage_root))
                receipt = json.loads((stage_root / "tool-provenance.json").read_text())
                self.assertEqual(receipt["tool_binding_status"], "rejected")
                self.assertTrue(any("missing x.py producer" in error for error in receipt["errors"]))

    def test_a_flat_directory_cannot_supply_the_stage_producers(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, tools_dir = self.layout(directory)
            saved = tools_dir.parent.with_name("saved-producers")
            tools_dir.parent.rename(saved)
            (saved / self.host).rename(tools_dir.parent)
            # The obsolete spelling preserves all producer bytes and hard
            # links, but the real bootstrap owner never writes this layout.
            self.assertFalse(self.run_audit(root, stage_root))
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["tool_binding_status"], "rejected")
            self.assertTrue(any("missing x.py producer" in error for error in receipt["errors"]))

    def test_receipt_reader_refuses_adjacent_generation_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage_root))
            path = stage_root / "tool-provenance.json"
            original = path.read_bytes()
            for name in ("tools", "proc_macro_helper"):
                with self.subTest(name=name):
                    receipt = json.loads(original)
                    row = receipt["tools"][0] if name == "tools" else receipt[name]
                    row["producer_stage"] = 4
                    row["producer_compiler_stage"] = 2
                    path.write_text(json.dumps(receipt))
                    self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))

    @staticmethod
    def migrate_to_noindex(root: Path) -> None:
        """`mv build build.noindex && ln -s build.noindex build` (docs/BUILD_AND_INSTALL.md)."""
        (root / "build").rename(root / "build.noindex")
        (root / "build").symlink_to("build.noindex", target_is_directory=True)

    def test_receipt_spelling_survives_the_build_noindex_migration(self):
        # Spotlight is kept out of build/ by `mv build build.noindex && ln -s
        # build.noindex build`. A receipt must name the same paths on both sides
        # of that move: the files are the same, and a receipt that went stale
        # because of a rename would force a rebuild of a tree nothing changed in.
        for audit_after_migration in (False, True):
            with self.subTest(audit_after_migration=audit_after_migration), \
                    tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                root = root.resolve()
                stage_root = root / "build" / self.host / "stage2"
                if audit_after_migration:
                    self.migrate_to_noindex(root)
                # A trustc reached through the link answers `--print sysroot`
                # with the physical path (measured 2026-09-25).
                self.assertTrue(self.run_audit(root, stage_root.resolve()))
                if not audit_after_migration:
                    self.migrate_to_noindex(root)
                receipt = json.loads((stage_root / "tool-provenance.json").read_text())
                self.assertEqual(receipt["stage_root"], f"build/{self.host}/stage2")
                self.assertEqual(
                    receipt["tools_dir"], f"build/{self.host}/stage3-tools-bin/{self.host}"
                )
                self.assertEqual(
                    receipt["compiler"]["path"], f"build/{self.host}/stage2/bin/trustc"
                )
                self.assertTrue(
                    self.verify_receipt(root, stage_root.resolve(), self.lineage()),
                    json.dumps(receipt, indent=1)[:4000],
                )

    def test_recorded_sysroot_is_compared_by_identity_not_by_spelling_only(self):
        # The sysroot a compiler reported is compared by resolved identity so
        # that the build.noindex move does not stale it. A DIFFERENT directory
        # is still a mismatch.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage_root))
            receipt_path = stage_root / "tool-provenance.json"
            receipt = json.loads(receipt_path.read_text())
            receipt["compiler"]["reported_sysroot_local_path"] = str(
                root / "build" / self.host / "stage1"
            )
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            output = io.StringIO()
            with patch("sys.stdout", output):
                self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))
            self.assertIn("compiler-reported local sysroot differs", output.getvalue())

    def test_receipt_paths_keep_the_physical_spelling_without_the_sanctioned_link(self):
        # Only the sanctioned link is folded back to `build/`. A real directory
        # that merely happens to be called build.noindex keeps its own name.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "build").mkdir()
            (root / "build.noindex" / "x").mkdir(parents=True)
            self.assertEqual(
                recreate_bootstrap._repository_relative_path(root, root / "build.noindex" / "x"),
                "build.noindex/x",
            )
            elsewhere = root / "elsewhere"
            elsewhere.mkdir()
            (root / "build").rmdir()
            (root / "build").symlink_to("elsewhere", target_is_directory=True)
            self.assertEqual(
                recreate_bootstrap._repository_relative_path(root, root / "build" / "."),
                "elsewhere",
            )

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

    def test_documentation_alias_must_match_bound_tool_during_audit_and_replay(self):
        for mutation in ("replace", "remove"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root, stage_root, bindir, _tools_dir = self.layout(directory)
                self.assertTrue(self.run_audit(root, stage_root))
                alias = bindir / "rustdoc"
                alias.unlink()
                if mutation == "replace":
                    self.executable(alias, b"unbound-documentation-tool")
                self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))
                self.assertFalse(self.run_audit(root, stage_root))
                receipt = json.loads((stage_root / "tool-provenance.json").read_text())
                self.assertTrue(any("rustdoc" in error for error in receipt["errors"]))

    def add_optional_tools(self, bindir: Path, tools_dir: Path) -> None:
        for public, producer in recreate_bootstrap.OPTIONAL_STAGE_TOOL_PRODUCERS.items():
            self.executable(tools_dir / producer, f"producer:{producer}".encode())
            os.link(tools_dir / producer, bindir / public)

    def test_optional_miri_tools_are_bound_when_present(self):
        # 2026-09-30: a complete seed-first stage2 (81fd6cee789) carried
        # trust-miri/targo-miri, which the surface contract admits as optional,
        # and the audit failed it after a successful build with "unmapped public
        # stage tools: targo-miri, trust-miri".
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, bindir, tools_dir = self.layout(directory)
            self.add_optional_tools(bindir, tools_dir)
            self.assertTrue(self.run_audit(root, stage_root))
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["status"], "release-ready")
            self.assertEqual(
                {tool["name"] for tool in receipt["tools"]},
                set(recreate_bootstrap.STAGE_TOOL_PRODUCERS)
                | set(recreate_bootstrap.OPTIONAL_STAGE_TOOL_PRODUCERS),
            )
            self.assertTrue(all(tool["status"] == "bound" for tool in receipt["tools"]))
            self.assertTrue(self.verify_receipt(root, stage_root, self.lineage()))

    def test_optional_tool_is_held_to_its_producer(self):
        for mutation in ("replace-before-audit", "replace-after-receipt", "remove-after-receipt"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root, stage_root, bindir, tools_dir = self.layout(directory)
                self.add_optional_tools(bindir, tools_dir)
                installed = bindir / "trust-miri"
                if mutation == "replace-before-audit":
                    installed.unlink()
                    self.executable(installed, b"ambient-miri")
                    self.assertFalse(self.run_audit(root, stage_root))
                    receipt = json.loads((stage_root / "tool-provenance.json").read_text())
                    self.assertTrue(any("trust-miri" in error for error in receipt["errors"]))
                    continue
                self.assertTrue(self.run_audit(root, stage_root))
                receipt_path = stage_root / "tool-provenance.json"
                original_receipt = receipt_path.read_bytes()
                installed.unlink()
                if mutation == "replace-after-receipt":
                    self.executable(installed, b"post-receipt-miri")
                self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))
                self.assertEqual(receipt_path.read_bytes(), original_receipt)

    def test_stock_miri_spelling_stays_unmapped(self):
        # Only the Trust names are optional; the stock spellings stay forbidden.
        for name in ("miri", "cargo-miri"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root, stage_root, bindir, _tools_dir = self.layout(directory)
                self.executable(bindir / name, b"stock-miri")
                self.assertFalse(self.run_audit(root, stage_root))
                receipt = json.loads((stage_root / "tool-provenance.json").read_text())
                self.assertIn(f"unmapped public stage tools: {name}", receipt["errors"])

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

    def test_foreign_rustdoc_alias_rejects_the_entire_stage(self):
        # `rustdoc` is admitted as a public name only because it is byte-identical to
        # `trustdoc`; an ambient replacement under that name must fail the audit, and a
        # post-receipt replacement must fail the read-only verifier without rewriting
        # the receipt.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, bindir, _tools_dir = self.layout(directory)
            lineage = self.lineage()
            self.assertTrue(self.run_audit(root, stage_root, before=lineage))
            receipt_path = stage_root / "tool-provenance.json"
            original_receipt = receipt_path.read_bytes()
            alias = bindir / "rustdoc"
            alias.unlink()
            self.executable(alias, b"ambient-rustdoc")
            self.assertFalse(self.verify_receipt(root, stage_root, lineage))
            self.assertEqual(receipt_path.read_bytes(), original_receipt)
            self.assertFalse(self.run_audit(root, stage_root, before=lineage))
            receipt = json.loads(receipt_path.read_text())
            self.assertEqual(receipt["status"], "rejected")
            self.assertEqual(receipt["rustdoc_alias"]["status"], "mismatch")
            self.assertIn(
                "stage rustdoc compatibility alias differs from trustdoc", receipt["errors"]
            )

    def test_copied_rustdoc_alias_is_bound_by_bytes_not_inode(self):
        # A filesystem where x.py copies instead of hardlinking records
        # same_inode=False; the byte binding alone must then catch a replacement.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, bindir, _tools_dir = self.layout(directory)
            alias = bindir / "rustdoc"
            alias.unlink()
            self.executable(alias, (bindir / "trustdoc").read_bytes())
            lineage = self.lineage()
            self.assertTrue(self.run_audit(root, stage_root, before=lineage))
            receipt_path = stage_root / "tool-provenance.json"
            receipt = json.loads(receipt_path.read_text())
            self.assertEqual(receipt["rustdoc_alias"]["status"], "bound")
            self.assertFalse(receipt["rustdoc_alias"]["same_inode"])
            self.assertTrue(self.verify_receipt(root, stage_root, lineage))
            original_receipt = receipt_path.read_bytes()
            alias.write_bytes(b"ambient-rustdoc")
            self.assertFalse(self.verify_receipt(root, stage_root, lineage))
            self.assertEqual(receipt_path.read_bytes(), original_receipt)

    def test_missing_rustdoc_alias_rejects_the_entire_stage(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, bindir, _tools_dir = self.layout(directory)
            lineage = self.lineage()
            self.assertTrue(self.run_audit(root, stage_root, before=lineage))
            receipt_path = stage_root / "tool-provenance.json"
            original_receipt = receipt_path.read_bytes()
            (bindir / "rustdoc").unlink()
            self.assertFalse(self.verify_receipt(root, stage_root, lineage))
            self.assertEqual(receipt_path.read_bytes(), original_receipt)
            self.assertFalse(self.run_audit(root, stage_root, before=lineage))
            receipt = json.loads(receipt_path.read_text())
            self.assertEqual(receipt["status"], "rejected")
            self.assertEqual(receipt["rustdoc_alias"]["status"], "missing")
            self.assertIn("missing public stage tools: rustdoc", receipt["errors"])

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

    def test_local_atpkg_is_candidate_and_replay_binds_exact_authority_read_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            source = self.lineage()
            atpkg = self.bootstrap_lineage("local_genesis")
            atpkg.update({
                "mode": "atpkg",
                "status": "local_atpkg",
                "trust_from_trust": True,
                "genesis_adapter": None,
                "atpkg_authority": AtpkgStage0AuthorityTests.authority_snapshot(),
            })
            self.assertTrue(self.run_audit(root, stage_root, before=source, bootstrap_before=atpkg))
            receipt_path = stage_root / "tool-provenance.json"
            original = receipt_path.read_bytes()
            receipt = json.loads(original)
            self.assertEqual(receipt["status"], "candidate-ready")
            self.assertEqual(receipt["bootstrap_lineage"]["status"], "local_atpkg")
            self.assertTrue(receipt["trust_from_trust"])
            self.assertTrue(self.verify_receipt(root, stage_root, source, bootstrap=atpkg))
            self.assertFalse(self.verify_receipt(
                root, stage_root, source, bootstrap=atpkg, require_immutable_lineage=True
            ))
            self.assertFalse(self.verify_receipt(
                root, stage_root, source, bootstrap=atpkg, require_public_release=True
            ))
            changed = copy.deepcopy(atpkg)
            changed["atpkg_authority"] = AtpkgStage0AuthorityTests.authority_snapshot("replacement")
            self.assertFalse(self.verify_receipt(root, stage_root, source, bootstrap=changed))
            self.assertEqual(receipt_path.read_bytes(), original)

            for field, value in (
                ("stable_across_build", False),
                ("pre_build_authority_sha256", "0" * 64),
                ("post_build_authority_sha256", "0" * 64),
                ("authority_sha256", "0" * 64),
                ("status", "verified"),
            ):
                with self.subTest(field=field):
                    forged = copy.deepcopy(receipt)
                    forged["bootstrap_lineage"]["atpkg_authority"][field] = value
                    receipt_path.write_text(json.dumps(forged), encoding="utf-8")
                    forged_bytes = receipt_path.read_bytes()
                    self.assertFalse(self.verify_receipt(root, stage_root, source, bootstrap=atpkg))
                    self.assertEqual(receipt_path.read_bytes(), forged_bytes)

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
            receipt["rustdoc_alias"]["same_inode"] = not receipt["rustdoc_alias"]["same_inode"]
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

    # THE COMMAND LINE. On 2026-10-12 three seals were cut from builds started
    # with exactly these arguments, and no sealed file said so: the receipt named
    # the lineage (seed, Trust-from-Trust, freshly materialized) and the build
    # stamp named x.py's own `build --stage 2`.
    SEED_INVOCATION = ["--stage", "2", "--require-seed", "--fresh-seed", "--no-register"]
    # The build command README.md, INSTALL.md, docs/BUILD_AND_INSTALL.md,
    # docs/BOOTSTRAP_FROM_SCRATCH.md and scripts/dev-bootstrap.sh give, and the
    # one a seal is cut with.
    EVERYDAY_INVOCATION = ["--stage", "2", "--require-seed", "--fresh-seed"]
    SEAL_INVOCATION = [*SEED_INVOCATION, "--require-llvm-identity"]

    def test_receipt_records_the_arguments_its_build_was_started_with(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage_root, invocation=self.SEED_INVOCATION))
            receipt_path = stage_root / "tool-provenance.json"
            receipt = json.loads(receipt_path.read_text())
            self.assertEqual(
                receipt["recreator_invocation"],
                {
                    "schema": "trust.recreator-invocation.v1",
                    "scope": "self-reported",
                    "argv": self.SEED_INVOCATION,
                },
            )
            # Nothing about the receipt it is added to moved.
            self.assertEqual(receipt["schema"], "trust.stage-tool-provenance.v2")
            self.assertEqual(receipt["status"], "release-ready")
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

    def test_the_invocation_record_is_one_new_key_and_a_receipt_without_it_verifies(self):
        # Every receipt written before the record existed has none (the three
        # sealed on 2026-10-12 among them). Such a receipt verifies as it did,
        # and the record changes no other field of one that carries it.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            receipt_path = stage_root / "tool-provenance.json"
            self.assertTrue(self.run_audit(root, stage_root))
            without = json.loads(receipt_path.read_text())
            self.assertNotIn("recreator_invocation", without)
            self.assertTrue(
                self.verify_receipt(
                    root,
                    stage_root,
                    self.lineage(),
                    require_immutable_lineage=True,
                    require_public_release=True,
                )
            )
            self.assertTrue(self.run_audit(root, stage_root, invocation=self.SEED_INVOCATION))
            with_record = json.loads(receipt_path.read_text())
            self.assertEqual(set(with_record) - set(without), {"recreator_invocation"})
            del with_record["recreator_invocation"]
            self.assertEqual(with_record, without)

    def malformed_invocation_records(self):
        good = recreate_bootstrap.recreator_invocation_record(self.SEED_INVOCATION)
        return (
            ("not an object", list(self.SEED_INVOCATION), "recreator_invocation is not an object"),
            (
                "a key the schema does not have",
                {**good, "program": "scripts/recreate_bootstrap.py"},
                "recreator_invocation does not hold exactly the keys argv, schema, scope",
            ),
            (
                "a key missing",
                {"schema": good["schema"], "argv": good["argv"]},
                "recreator_invocation does not hold exactly the keys argv, schema, scope",
            ),
            (
                "another schema",
                {**good, "schema": "trust.recreator-invocation.v2"},
                "recreator_invocation.schema is not trust.recreator-invocation.v1",
            ),
            (
                "a claim to be more than self-reported",
                {**good, "scope": "verified"},
                "recreator_invocation.scope is not self-reported",
            ),
            (
                "the arguments as one string",
                {**good, "argv": " ".join(self.SEED_INVOCATION)},
                "recreator_invocation.argv is not a list of strings",
            ),
            (
                "an argument that is not a string",
                {**good, "argv": ["--stage", 2]},
                "recreator_invocation.argv is not a list of strings",
            ),
            (
                "a line break in an argument",
                {**good, "argv": ["--host", "a\nprovenance_class=BUILD-STAMPED-CLEAN"]},
                "recreator_invocation.argv holds a control or unprintable character",
            ),
            (
                "a control character past ASCII",
                {**good, "argv": ["--host", "a\x85provenance_class=BUILD-STAMPED-CLEAN"]},
                "recreator_invocation.argv holds a control or unprintable character",
            ),
            (
                "an argument that was not text",
                {**good, "argv": ["--llvm-config", "/opt/llvm\udcff/bin/llvm-config"]},
                "recreator_invocation.argv holds a control or unprintable character",
            ),
            # Both ends of each of the three refused ranges (U+0000-001F,
            # U+007F-009F, U+D800-DFFF), through the verifier and through
            # promotion's reader: a rule one code point short at an end lets
            # that end through one of them.
            *(
                (
                    f"U+{code:04X}, an end of a refused range",
                    {**good, "argv": ["--host", "a" + chr(code) + "b"]},
                    "recreator_invocation.argv holds a control or unprintable character",
                )
                for code in (0x0000, 0x001F, 0x007F, 0x009F, 0xD800, 0xDFFF)
            ),
        )

    def test_a_malformed_invocation_record_is_refused_by_both_of_its_readers(self):
        # The verifier cannot recompute a command line, so the record's form is
        # all it holds it to; promotion's reader holds it to the same form, for
        # the same reasons, before it quotes the arguments in a seal's PROVENANCE.
        reader = load_stage_receipt_reader()
        for label, record, message in self.malformed_invocation_records():
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                self.assertTrue(self.run_audit(root, stage_root, invocation=self.SEED_INVOCATION))
                receipt_path = stage_root / "tool-provenance.json"
                receipt = json.loads(receipt_path.read_text())
                receipt["recreator_invocation"] = record
                receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
                output = io.StringIO()
                with patch("sys.stdout", output):
                    self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))
                self.assertIn(f"ERROR: {message}", output.getvalue())
                self.assertEqual(
                    reader.invocation_errors(record),
                    recreate_bootstrap._recreator_invocation_errors(record),
                )
                with self.assertRaises(reader.StageReceiptError) as refused:
                    reader.lines(stage_root, self.commit)
                self.assertIn(message, str(refused.exception))
        good = recreate_bootstrap.recreator_invocation_record(self.SEED_INVOCATION)
        self.assertEqual(recreate_bootstrap._recreator_invocation_errors(good), [])
        self.assertEqual(reader.invocation_errors(good), [])
        self.assertEqual(reader.INVOCATION_SCHEMA, recreate_bootstrap.RECREATOR_INVOCATION_SCHEMA)
        self.assertEqual(reader.INVOCATION_SCOPE, recreate_bootstrap.RECREATOR_INVOCATION_SCOPE)
        self.assertEqual(set(good), set(reader.INVOCATION_KEYS))

    def test_an_argument_that_cannot_be_recorded_rejects_the_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            output = io.StringIO()
            with patch("sys.stdout", output):
                self.assertFalse(
                    self.run_audit(root, stage_root, invocation=["--host", "test\nhost"])
                )
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            self.assertEqual(receipt["status"], "rejected")
            self.assertIn(
                "recreator_invocation.argv holds a control or unprintable character",
                receipt["errors"],
            )

    def test_main_refuses_arguments_it_could_not_record_before_any_work(self):
        def work_started(*_args, **_kwargs):
            raise AssertionError("the recreator started work")

        unrecordable = ["--llvm-config", "/opt/llvm\n22/bin/llvm-config"]
        output = io.StringIO()
        with patch.object(recreate_bootstrap, "ensure_python_311"), patch.object(
            recreate_bootstrap, "line_buffer_output"
        ), patch.object(
            recreate_bootstrap, "repo_root", return_value=Path("/checkout")
        ), patch.object(
            recreate_bootstrap, "host_triple", return_value=self.host
        ), patch.object(
            recreate_bootstrap, "check_prereqs", side_effect=work_started
        ), patch.object(
            recreate_bootstrap, "resolve_stage0_selection", side_effect=work_started
        ), patch("sys.stdout", output):
            # A build, and the check of one: a check answers for the same flags.
            for flags in (["--stage", "2"], ["--stage", "2", "--check"], ["--stage", "3", "--no-register"]):
                with self.subTest(flags=flags):
                    self.assertEqual(recreate_bootstrap.main([*flags, *unrecordable]), 2)
            # Stage 1 and --no-build write no receipt, so they have nothing to
            # record and go on to their work as before.
            for flags in (["--stage", "1"], ["--stage", "2", "--no-build"]):
                with self.subTest(flags=flags), self.assertRaisesRegex(
                    AssertionError, "the recreator started work"
                ):
                    recreate_bootstrap.main([*flags, *unrecordable])
            # What can be recorded is not refused, whatever this interpreter's
            # Unicode tables say of it and however long it is: a character
            # assigned after an older python3 was built, one not assigned at
            # all, a path longer than a PROVENANCE line.
            for recordable in (
                ["--llvm-config", "/opt/llvm-\U0001FAE8/bin/llvm-config"],
                ["--llvm-config", "/opt/llvm-" + self.unassigned_character() + "/bin/llvm-config"],
                ["--llvm-config", "/opt/" + "x" * 9000 + "/bin/llvm-config"],
            ):
                with self.subTest(recordable=recordable[1][:24]), self.assertRaisesRegex(
                    AssertionError, "the recreator started work"
                ):
                    recreate_bootstrap.main(["--stage", "2", *recordable])
        self.assertEqual(
            output.getvalue().count(
                "these cannot be recorded: recreator_invocation.argv holds a control or "
                "unprintable character"
            ),
            3,
        )

    @staticmethod
    def unassigned_character() -> str:
        # A code point the running interpreter's Unicode tables do not know:
        # what `str.isprintable()` says of it here is what an older python3
        # says of a character assigned since it was built.
        return next(
            chr(code) for code in range(0x378, sys.maxunicode)
            if unicodedata.category(chr(code)) == "Cn"
        )

    def test_the_recorded_arguments_are_one_ascii_line_under_any_interpreter(self):
        # This script (Python 3.11+) decides whether an argument can be
        # recorded; promotion's reader decides again, under whatever python3 is
        # on PATH, and writes the line. On 2026-10-12 both asked
        # str.isprintable(), i.e. each interpreter's own Unicode tables:
        # python3.14 found U+1FAE8 printable and /usr/bin/python3 3.9.6 did
        # not, so a build this script had accepted and stamped would have been
        # refused by promotion after the whole build. The rule is three code
        # point ranges now, the same in both files, and the line is ASCII.
        reader = load_stage_receipt_reader()
        controls = {
            code for code in range(sys.maxunicode + 1)
            if unicodedata.category(chr(code)) in ("Cc", "Cs")
        }
        # Both categories are immutable sets (Unicode stability policy), so
        # this count is the same under every interpreter.
        self.assertEqual(len(controls), 65 + 2048)
        self.assertEqual(sys.maxunicode, 0x10FFFF)

        # The rule a third time, by its numbers, and what this interpreter's
        # tables call a control or a surrogate: the same 2113 code points.
        def refused_code_point(code):
            return code <= 0x1F or 0x7F <= code <= 0x9F or 0xD800 <= code <= 0xDFFF

        self.assertEqual(
            controls, {code for code in range(sys.maxunicode + 1) if refused_code_point(code)}
        )
        # EVERY code point, under each of the two rules, alone and inside a
        # word. Until 2026-10-13 this probed the controls and every 257th code
        # point (6,447 of the 1,114,112), and a rule that refused one more
        # character anywhere else passed it: U+200B or the tag characters
        # U+E0000-E007F in promotion's reader, the bidi isolates U+2066-2069
        # or the noncharacters U+FDD0-FDEF in the recreator (four mutants the
        # second review of this rule found alive). A reader that refuses what
        # the recreator accepted is the defect the rule was written against.
        rules = (
            ("promotion's reader", reader.unrecordable_character),
            ("the recreator", recreate_bootstrap._unrecordable_character),
        )
        for whose, rule in rules:
            for form in ("{}", "a{}b"):
                with self.subTest(rule=whose, form=form):
                    wrong = [
                        f"U+{code:04X}" for code in range(sys.maxunicode + 1)
                        if rule(form.format(chr(code))) != refused_code_point(code)
                    ]
                    self.assertEqual((len(wrong), wrong[:16]), (0, []))
        # Each end of the three ranges and the first code point outside it, by
        # number and not through the function above; then the code points
        # those four mutants refused, and the last one there is.
        refusal = ["recreator_invocation.argv holds a control or unprintable character"]
        for code, refused in (
            (0x0000, True), (0x001F, True), (0x0020, False),
            (0x007E, False), (0x007F, True), (0x009F, True), (0x00A0, False),
            (0xD7FF, False), (0xD800, True), (0xDFFF, True), (0xE000, False),
            (0x200B, False), (0x2066, False), (0x2069, False), (0xFDD0, False),
            (0xFDEF, False), (0xE0000, False), (0xE007F, False), (0x10FFFF, False),
        ):
            with self.subTest(code_point=f"U+{code:04X}"):
                argument = "a" + chr(code) + "b"
                record = recreate_bootstrap.recreator_invocation_record(["--host", argument])
                for whose, rule in rules:
                    self.assertIs(rule(chr(code)), refused, whose)
                    self.assertIs(rule(argument), refused, whose)
                self.assertEqual(reader.invocation_errors(record), refusal if refused else [])
                self.assertEqual(
                    recreate_bootstrap._recreator_invocation_errors(record),
                    refusal if refused else [],
                )
        unassigned = self.unassigned_character()
        self.assertFalse(unassigned.isprintable())
        self.assertFalse(reader.unrecordable_character(unassigned))

        def as_bytes(text):
            return "".join(f"\\x{byte:02x}" for byte in text.encode("utf-8"))

        rows = (
            (["--stage", "2", "--require-seed"], "--stage 2 --require-seed"),
            (["--llvm-config", "/opt/llvm 22/bin/llvm-config"],
             "--llvm-config '/opt/llvm 22/bin/llvm-config'"),
            # Assigned in Unicode 14: unprintable to a python3 built before it.
            (["--llvm-config", "/opt/llvm-\U0001FAE8/bin"],
             "--llvm-config $'/opt/llvm-\\xf0\\x9f\\xab\\xa8/bin'"),
            (["--llvm-config", "/opt/llvm-" + unassigned + "/bin"],
             "--llvm-config $'/opt/llvm-" + as_bytes(unassigned) + "/bin'"),
            # A quote and a backslash inside the $'...' form, and a digit after
            # an escaped byte (the escape takes two hex digits, no more).
            (["caf\u00e91 it's a\\n"], "$'caf\\xc3\\xa91 it\\'s a\\\\n'"),
            # Characters that would break or reorder a line if written as
            # themselves (a line separator, a right-to-left override, a
            # no-break space) are bytes on it.
            (["a\u2028stage_receipt_status=release-ready", "\u202e", "\u00a0"],
             "$'a\\xe2\\x80\\xa8stage_receipt_status=release-ready' $'\\xe2\\x80\\xae' $'\\xc2\\xa0'"),
            # The first code point outside each refused range (U+0020 and
            # U+007E in one word, U+00A0, U+D7FF and U+E000), then what a wider
            # rule would refuse (a zero-width space, the bidi isolates, the
            # noncharacters U+FDD0 and U+FDEF, two tag characters, the last
            # code point): every one is recorded, and read back.
            ([" ~", "\u00a0", "\ud7ff\ue000", "\u200b", "\u2066\u2069", "\ufdd0\ufdef",
              "\U000e0000\U000e007f", "\U0010ffff"],
             "' ~' $'\\xc2\\xa0' $'\\xed\\x9f\\xbf\\xee\\x80\\x80' $'\\xe2\\x80\\x8b' "
             "$'\\xe2\\x81\\xa6\\xe2\\x81\\xa9' $'\\xef\\xb7\\x90\\xef\\xb7\\xaf' "
             "$'\\xf3\\xa0\\x80\\x80\\xf3\\xa0\\x81\\xbf' $'\\xf4\\x8f\\xbf\\xbf'"),
            # What a printf FORMAT would interpret, as plain ASCII arguments
            # and inside the $'...' form: a percent sign and a backslash stay
            # the characters they are.
            (["100%", "%s%n", "a\\tb", "\\", "caf\u00e9\\101%d"],
             "100% %s%n 'a\\tb' '\\' $'caf\\xc3\\xa9\\\\101%d'"),
            ([""], "''"),
            ([], "(no arguments)"),
            # The reader's own words, given as arguments, stay arguments.
            (["not-recorded"], "'not-recorded'"),
            (["not-recorded", "--stage"], "not-recorded --stage"),
            (["(no", "arguments)"], "'(no' 'arguments)'"),
        )
        bash = shutil.which("bash")
        self.assertIsNotNone(bash)
        for argv, line in rows:
            with self.subTest(line=line), tempfile.TemporaryDirectory() as directory:
                record = recreate_bootstrap.recreator_invocation_record(argv)
                self.assertEqual(recreate_bootstrap._recreator_invocation_errors(record), [])
                self.assertEqual(reader.invocation_errors(record), [])
                self.assertEqual(reader.quoted_arguments(argv), line)
                # From the receipt this script writes to the line promotion records.
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                self.assertTrue(self.run_audit(root, stage_root, invocation=argv))
                self.assertTrue(self.verify_receipt(root, stage_root, self.lineage()))
                recorded = reader.lines(stage_root, self.commit)
                self.assertEqual(recorded[-1], "stage_receipt_recreator_argv=" + line)
                for text in recorded:
                    self.assertRegex(text, r"\A[a-z0-9_]+=[ -~]+\Z")
                if argv:
                    # bash reads the line back as the arguments it was started with.
                    read_back = subprocess.run(
                        [bash, "-c", "printf '%s\\0' " + line],
                        capture_output=True, timeout=60, check=True,
                    ).stdout
                    self.assertEqual(
                        read_back, b"".join(word.encode("utf-8") + b"\0" for word in argv)
                    )

        # THE LENGTH OF THE LINE. The strictest reader of a seal's PROVENANCE
        # (first-party/trust-mc scripts/development_seal.py) refuses a line of
        # more than 8192 characters; the quoted arguments get half of that, and
        # longer ones are pointed at in the sealed receipt, never cut.
        self.assertEqual(reader.ARGV_QUOTED_MAX, 4096)
        flags = ["--stage", "2", "--llvm-config"]
        room = reader.ARGV_QUOTED_MAX - len(" ".join(flags)) - 1
        at_the_bound = [*flags, "x" * room]
        self.assertEqual(reader.quoted_arguments(at_the_bound), " ".join(at_the_bound))
        self.assertEqual(len(reader.quoted_arguments(at_the_bound)), 4096)
        # The bound is on what is WRITTEN, so quoting that makes an argument
        # longer counts: a non-ASCII character is 4 written characters a byte,
        # a quote is 5. Exactly 4096 as written, with e-acutes and with
        # quotes, is a line; one character more, below, is pointed at.
        for argv, line in (
            (["\u00e9" * 511 + "x" * 5], "$'" + "\\xc3\\xa9" * 511 + "xxxxx'"),
            (["'" * 818 + "x" * 4], "'" + "'\"'\"'" * 818 + "xxxx'"),
        ):
            with self.subTest(at_the_bound=line[:8]):
                self.assertEqual(len(line), 4096)
                self.assertEqual(reader.quoted_arguments(argv), line)
        # (arguments, their length as written, their length in UTF-8 bytes as given)
        for argv, length, unquoted in (
            ([*flags, "x" * (room + 1)], 4097, 4097),
            # 2000 characters, 16 on the line each.
            (["\U0001FAE8" * 2000], 3 + 16 * 2000, 8000),
            # Arguments that FIT as they are given, in characters and in
            # bytes, and do not fit as they are written. A bound taken on the
            # bytes before the quoting passed the two rows above (a mutant the
            # second review found alive) and would write these four as lines:
            # 8803 characters for the first, where the strictest reader of
            # PROVENANCE stops at 8192.
            (["\u00e9" * 1100], 3 + 8 * 1100, 2200),
            (["'" * 1000], 2 + 5 * 1000, 1000),
            (["\u00e9" * 511 + "x" * 6], 4097, 1028),
            (["'" * 819], 4097, 819),
        ):
            with self.subTest(length=length, first=argv[0][:1]), tempfile.TemporaryDirectory() as directory:
                self.assertEqual(len(" ".join(argv).encode("utf-8")), unquoted)
                pointer = (
                    f"(not quoted here: {length} characters when quoted, more than 4096; "
                    "read recreator_invocation.argv in tool-provenance.json)"
                )
                self.assertEqual(reader.quoted_arguments(argv), pointer)
                # Too long for the line is not unrecordable: the receipt holds
                # the arguments whole, and the build is not refused for them.
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                self.assertTrue(self.run_audit(root, stage_root, invocation=argv))
                self.assertTrue(self.verify_receipt(root, stage_root, self.lineage()))
                receipt = json.loads((stage_root / "tool-provenance.json").read_text())
                self.assertEqual(receipt["recreator_invocation"]["argv"], argv)
                recorded = reader.lines(stage_root, self.commit)
                self.assertEqual(recorded[-1], "stage_receipt_recreator_argv=" + pointer)
                self.assertLess(max(len(text) for text in recorded), 8192 // 2)

    # THE LLVM A STAGE CARRIES. On 2026-10-12 two of three seals reused the
    # first one's build directory, and with it an LLVM built at another commit.
    # x.py did not then rebuild the in-tree LLVM for a committed change to it
    # (Trust vendors src/llvm-project, so the commit input of x.py's LLVM stamp
    # is the empty string; since 2026-10-13 it does, but it keeps an LLVM that
    # cannot say what it was built from), the only guard was a git comparison
    # an agent ran by hand, and neither the receipt nor the seal's PROVENANCE
    # said which LLVM a stage carried. The fixture rows below stand for HEAD's
    # entries.
    @classmethod
    def llvm_source(cls, *, llvm_tree="3" * 40, bootstrap_tree="2" * 40, clean=True):
        """capture_llvm_source_identity's answer for a tree with these object ids."""
        rows = [
            {"path": "src/bootstrap", "type": "tree", "oid": bootstrap_tree},
            {"path": "src/llvm-project", "type": "tree", "oid": llvm_tree},
            {"path": "src/version", "type": "blob", "oid": "4" * 40},
        ]
        return {
            "paths": rows,
            "identity_sha256": recreate_bootstrap._llvm_source_identity_sha256(rows),
            "clean": clean,
            "errors": [],
        }

    @classmethod
    def llvm_build_record(cls, **changes):
        """The build record of an LLVM built from `llvm_source()` for main_around_llvm's build."""
        source = cls.llvm_source()
        return {
            "schema": "trust.llvm-build-record.v1",
            "built_at_commit": cls.commit,
            "host": cls.host,
            "source_identity_sha256": source["identity_sha256"],
            "source_paths": source["paths"],
            "bootstrap_config_sha256": "b" * 64,
            "native_authority_sha256": "c" * 64,
            "output_fingerprint_sha256": "6" * 64,
            **changes,
        }

    @classmethod
    def llvm_observation(cls, *, present=False, record=None):
        """capture_llvm_before_build's answer: no LLVM in the build directory, or one that is there."""
        return {
            "mode": "in-tree",
            "mode_reasons": [],
            "source": cls.llvm_source(),
            "output": {
                "dirs": [f"build/{cls.host}/llvm"] if present else [],
                "present": present,
                "stamp_present": present,
                "uncovered": [],
                "fingerprint_sha256": "6" * 64 if present else None,
                "errors": [],
            },
            "build_record": record,
            "build_record_errors": [],
        }

    def llvm_out(self, root: Path) -> Path:
        return root / "build" / self.host / "llvm"

    def install_llvm(self, root: Path, payload: bytes = b"llvm built once") -> Path:
        """What an x.py LLVM build leaves in build/<host>/llvm."""
        out = self.llvm_out(root)
        self.executable(out / "bin" / "llvm-config", payload)
        (out / "bin" / "llvm-ranlib").symlink_to("llvm-ar")
        (out / "lib").mkdir()
        (out / "lib" / "libLLVMCore.a").write_bytes(payload + b": core")
        (out / "include" / "llvm").mkdir(parents=True)
        (out / "include" / "llvm" / "Config.h").write_text("#define LLVM 1\n")
        (out / "build").mkdir()
        (out / "build" / "CMakeCache.txt").write_text("cmake's own work tree\n")
        (out / ".llvm-stamp").write_text(hashlib.sha256(b"").hexdigest())
        return out

    def observe_llvm(self, root: Path, source=None):
        config = root / "bootstrap.toml"
        if not config.exists():
            config.write_text("[llvm]\ndownload-ci-llvm = false\n")
        with patch.object(
            recreate_bootstrap,
            "capture_llvm_source_identity",
            return_value=self.llvm_source() if source is None else source,
        ):
            return recreate_bootstrap.capture_llvm_before_build(root, self.host, None, config)

    def llvm_build(
        self, root: Path, stage_root: Path, *, x_py=None, source=None, source_after=None, **audit
    ):
        """One provenance build of the fixture: observe, let `x_py` stand for x.py, audit.

        `source` is the LLVM source identity of the tree, `source_after` what
        it is once x.py is done when that differs. Returns (the audit's
        verdict, the receipt it wrote, what it printed).
        """
        before = self.observe_llvm(root, source)
        if x_py is not None:
            x_py()
        output = io.StringIO()
        with patch("sys.stdout", output):
            verdict = self.run_audit(
                root,
                stage_root,
                llvm_before=before,
                llvm_source=source if source_after is None else source_after,
                **audit,
            )
        receipt = json.loads((stage_root / "tool-provenance.json").read_text())
        return verdict, receipt, output.getvalue()

    def install_native_lld(self, root: Path, stage_root: Path) -> None:
        self.install_llvm(root)
        prefix = root / "build" / self.host / "lld"
        self.executable(prefix / "bin/lld", b"native-lld")
        (prefix / ".lld-stamp").write_text(hashlib.sha256(b"").hexdigest())
        self.executable(stage_root / "bin/rust-lld", b"native-lld")

    def test_native_lld_uses_its_stated_llvm_producer_not_a_rust_tools_bin(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            verdict, receipt, output = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_native_lld(root, stage_root),
            )
            self.assertTrue(verdict, output)
            row, = receipt["native_stage_tools"]
            self.assertEqual(row["name"], "rust-lld")
            self.assertEqual(row["producer_kind"], "in-tree-llvm-project")
            self.assertEqual(row["producer_path"], f"build/{self.host}/lld/bin/lld")
            self.assertEqual(row["sha256"], row["producer_sha256"])
            self.assertNotIn("producer_compiler_stage", row)
            self.assertNotIn("rust-lld", {tool["name"] for tool in receipt["tools"]})
            self.assertTrue(self.verify_receipt(
                root, stage_root, self.lineage(), require_llvm_identity=True,
            ))

    def test_portable_reader_checks_native_lld_bytes_and_llvm_binding(self):
        reader = load_stage_receipt_reader()
        with tempfile.TemporaryDirectory() as directory:
            root, stage, _bin, _tools = self.layout(directory)
            verdict, receipt, output = self.llvm_build(
                root, stage, x_py=lambda: self.install_native_lld(root, stage))
            self.assertTrue(verdict, output)
            path = stage / 'tool-provenance.json'
            original = path.read_bytes()
            reader.lines(stage, self.commit)
            for case in ('bytes', 'producer', 'llvm-output', 'duplicate'):
                with self.subTest(case=case):
                    changed = json.loads(original)
                    row = changed['native_stage_tools'][0]
                    if case == 'bytes':
                        (stage/'bin/rust-lld').write_bytes(b'changed native linker')
                    elif case == 'producer':
                        row['producer_path'] = f'build/{self.host}/llvm/bin/lld'
                    elif case == 'llvm-output':
                        row['llvm_output_fingerprint_sha256'] = '0'*64
                    else:
                        changed['native_stage_tools'].append(dict(row))
                    path.write_text(json.dumps(changed))
                    with self.assertRaises(reader.StageReceiptError):
                        reader.lines(stage, self.commit)
                    (stage/'bin/rust-lld').write_bytes(b'native-lld')
            path.write_bytes(original)
            reader.lines(stage, self.commit)

    def test_native_lld_cannot_use_an_unstated_llvm_or_a_lookalike(self):
        for failure in ("unstated", "missing", "mismatch", "linked"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                before = self.observe_llvm(root)
                self.install_native_lld(root, stage_root)
                installed = stage_root / "bin/rust-lld"
                producer = root / "build" / self.host / "lld/bin/lld"
                if failure == "missing":
                    producer.unlink()
                elif failure == "mismatch":
                    installed.write_bytes(b"an unrelated native linker")
                elif failure == "linked":
                    installed.unlink()
                    installed.symlink_to(producer)
                self.assertFalse(self.run_audit(
                    root, stage_root, llvm_before=None if failure == "unstated" else before,
                ))

    def test_native_lld_readonly_verifier_rejects_rebinding_and_changed_bytes(self):
        for failure in ("installed", "both", "record-path", "missing-row"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                verdict, receipt, output = self.llvm_build(
                    root, stage_root, x_py=lambda: self.install_native_lld(root, stage_root),
                )
                self.assertTrue(verdict, output)
                path = stage_root / "tool-provenance.json"
                if failure in ("installed", "both"):
                    (stage_root / "bin/rust-lld").write_bytes(b"replacement")
                    if failure == "both":
                        (root / "build" / self.host / "lld/bin/lld").write_bytes(b"replacement")
                elif failure == "record-path":
                    receipt["native_stage_tools"][0]["producer_path"] = f"build/{self.host}/llvm/bin/lld"
                    path.write_text(json.dumps(receipt))
                else:
                    del receipt["native_stage_tools"]
                    path.write_text(json.dumps(receipt))
                before = path.read_bytes()
                self.assertFalse(self.verify_receipt(
                    root, stage_root, self.lineage(), require_llvm_identity=True,
                ))
                self.assertEqual(path.read_bytes(), before, "the verifier is read-only")

    def test_native_lld_requires_current_llvm_output_even_without_opt_in(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            verdict, _receipt, output = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_native_lld(root, stage_root),
            )
            self.assertTrue(verdict, output)
            (self.llvm_out(root) / "lib/libLLVMCore.a").write_bytes(b"different LLVM")
            self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))

    def test_native_lld_malformed_llvm_output_dirs_is_a_refusal(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            verdict, receipt, output = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_native_lld(root, stage_root),
            )
            self.assertTrue(verdict, output)
            receipt["llvm_identity"]["output_dirs"] = None
            (stage_root / "tool-provenance.json").write_text(json.dumps(receipt))
            self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))

    def test_separate_stage_receipt_preserves_original_and_refuses_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            original = stage_root / "tool-provenance.json"
            original.write_text('{"status":"rejected","errors":["original failure"]}\n')
            raw = original.read_bytes()
            separate = root / "repaired-provenance.json"
            self.assertTrue(self.run_audit(root, stage_root, receipt_path=separate))
            self.assertTrue(self.verify_receipt(
                root, stage_root, self.lineage(), receipt_path=separate,
            ))
            self.assertEqual(original.read_bytes(), raw)
            repaired = separate.read_bytes()
            with self.assertRaisesRegex(ValueError, "new absolute"):
                self.run_audit(root, stage_root, receipt_path=separate)
            self.assertEqual(separate.read_bytes(), repaired)
            link = root / "linked-provenance.json"
            link.symlink_to(separate)
            with self.assertRaisesRegex(ValueError, "new absolute"):
                self.run_audit(root, stage_root, receipt_path=link)
            self.assertFalse(self.verify_receipt(root, stage_root, self.lineage(), receipt_path=link))
            with self.assertRaisesRegex(ValueError, "outside the retained build"):
                self.run_audit(root, stage_root, receipt_path=stage_root / "different.json")
            self.assertFalse((stage_root / "different.json").exists())
            self.assertEqual(original.read_bytes(), raw)

    def test_detached_reaudit_does_not_rewrite_the_retained_llvm_build_record(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            before = self.observe_llvm(root)
            self.install_native_lld(root, stage_root)
            self.assertTrue(self.run_audit(root, stage_root, llvm_before=before))
            record = self.llvm_out(root) / recreate_bootstrap.LLVM_BUILD_RECORD_NAME
            raw, original = record.read_bytes(), record.stat()
            original_receipt = (stage_root / "tool-provenance.json").read_bytes()
            self.assertTrue(self.run_audit(
                root, stage_root, llvm_before=before, receipt_path=root / "reaudited.json",
            ))
            after = record.stat()
            self.assertEqual(record.read_bytes(), raw)
            self.assertEqual((after.st_ino, after.st_mtime_ns, after.st_ctime_ns),
                             (original.st_ino, original.st_mtime_ns, original.st_ctime_ns))
            self.assertEqual((stage_root / "tool-provenance.json").read_bytes(), original_receipt)

    def test_detached_reaudit_refuses_missing_or_changed_llvm_record_without_replacing_it(self):
        for failure in ("missing", "changed"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                before = self.observe_llvm(root)
                self.install_native_lld(root, stage_root)
                self.assertTrue(self.run_audit(root, stage_root, llvm_before=before))
                record = self.llvm_out(root) / recreate_bootstrap.LLVM_BUILD_RECORD_NAME
                if failure == "missing":
                    record.unlink()
                else:
                    record.write_bytes(b"changed retained record")
                self.assertFalse(self.run_audit(
                    root, stage_root, llvm_before=before, receipt_path=root / "refused.json",
                ))
                if failure == "missing":
                    self.assertFalse(record.exists())
                else:
                    self.assertEqual(record.read_bytes(), b"changed retained record")

    def test_receipt_says_the_llvm_was_built_in_this_run_and_leaves_its_build_record(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_llvm(root)
            )
            self.assertTrue(verdict, printed)
            source = self.llvm_source()
            fingerprint = recreate_bootstrap.capture_llvm_output(root, self.host)[
                "fingerprint_sha256"
            ]
            self.assertRegex(fingerprint, r"\A[0-9a-f]{64}\Z")
            record_path = self.llvm_out(root) / ".trust-llvm-build-record.json"
            record = json.loads(record_path.read_text())
            self.assertEqual(
                record,
                {
                    "schema": "trust.llvm-build-record.v1",
                    "built_at_commit": self.commit,
                    "host": self.host,
                    "source_identity_sha256": source["identity_sha256"],
                    "source_paths": source["paths"],
                    # The config and the native authority of THIS build: what
                    # the fixture's lineage and authority captures answer.
                    "bootstrap_config_sha256": "d" * 64,
                    "native_authority_sha256": "8" * 64,
                    "output_fingerprint_sha256": fingerprint,
                },
            )
            self.assertEqual(
                receipt["llvm_identity"],
                {
                    "schema": "trust.llvm-identity.v1",
                    "mode": "in-tree",
                    "provenance": "built-in-this-run",
                    "identity_stated": True,
                    "reasons": [],
                    "source_identity_sha256": source["identity_sha256"],
                    "source_paths": source["paths"],
                    "output_dirs": [f"build/{self.host}/llvm"],
                    "output_fingerprint_sha256": fingerprint,
                    "build_record": record,
                },
            )
            # Nothing about the receipt it is added to moved.
            self.assertEqual(receipt["schema"], "trust.stage-tool-provenance.v2")
            self.assertEqual(receipt["status"], "release-ready")
            self.assertIn(
                "  llvm: in-tree, built-in-this-run, identity stated (source identity "
                f"{source['identity_sha256'][:12]}, src/llvm-project tree {'3' * 12}, built at "
                f"commit {self.commit[:12]})\n",
                printed,
            )
            # x.py's stamp is x.py's: constraint (a) of this record is that no
            # build is made to rebuild LLVM by it.
            self.assertEqual(
                (self.llvm_out(root) / ".llvm-stamp").read_text(), hashlib.sha256(b"").hexdigest()
            )
            self.assertEqual(
                sorted(path.name for path in self.llvm_out(root).iterdir()),
                [".llvm-stamp", ".trust-llvm-build-record.json", "bin", "build", "include", "lib"],
            )
            receipt_path = stage_root / "tool-provenance.json"
            before_verify = (receipt_path.read_bytes(), record_path.read_bytes())
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
            self.assertEqual((receipt_path.read_bytes(), record_path.read_bytes()), before_verify)

    def test_the_llvm_record_is_one_new_key_and_a_receipt_without_it_verifies(self):
        # Every receipt written before the record existed has none (the three
        # sealed on 2026-10-12 among them). Such a receipt verifies as it did,
        # release class and all, whatever the build directory holds, and the
        # record changes no other field of one that carries it.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            receipt_path = stage_root / "tool-provenance.json"
            self.assertTrue(self.run_audit(root, stage_root, invocation=self.SEED_INVOCATION))
            without_bytes = receipt_path.read_bytes()
            without = json.loads(without_bytes)
            self.assertNotIn("llvm_identity", without)
            self.assertEqual(without["status"], "release-ready")

            def verifies_as_a_release():
                return self.verify_receipt(
                    root,
                    stage_root,
                    self.lineage(),
                    require_immutable_lineage=True,
                    require_public_release=True,
                )

            self.assertTrue(verifies_as_a_release())
            verdict, with_record, printed = self.llvm_build(
                root,
                stage_root,
                x_py=lambda: self.install_llvm(root),
                invocation=self.SEED_INVOCATION,
            )
            self.assertTrue(verdict, printed)
            self.assertEqual(set(with_record) - set(without), {"llvm_identity"})
            del with_record["llvm_identity"]
            self.assertEqual(with_record, without)
            # The old receipt, beside an LLVM and its build record, and beside
            # an LLVM of any other sources: it is not asked.
            receipt_path.write_bytes(without_bytes)
            self.assertTrue(verifies_as_a_release())
            (self.llvm_out(root) / "lib" / "libLLVMCore.a").write_bytes(b"another LLVM")
            (self.llvm_out(root) / ".trust-llvm-build-record.json").unlink()
            self.assertTrue(verifies_as_a_release())
            self.assertEqual(receipt_path.read_bytes(), without_bytes)

    def test_a_reused_llvm_is_stated_only_on_the_evidence_of_its_build_record(self):
        first_commit = self.commit
        later_commit = "5" * 40
        where = f"build/{self.host}/llvm"

        def record_path(root):
            return self.llvm_out(root) / ".trust-llvm-build-record.json"

        def library(root):
            return self.llvm_out(root) / "lib" / "libLLVMCore.a"

        def first_build(root, stage_root):
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_llvm(root)
            )
            self.assertTrue(verdict, printed)
            return receipt["llvm_identity"]["build_record"]

        # A later commit that changed nothing LLVM is built from, in the same
        # build directory: x.py reuses the LLVM, and the record left by the run
        # that built it is the evidence of which sources it came from.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            built = first_build(root, stage_root)
            self.commit = later_commit
            verdict, receipt, printed = self.llvm_build(root, stage_root)
            self.assertTrue(verdict, printed)
            llvm = receipt["llvm_identity"]
            self.assertEqual(
                (llvm["mode"], llvm["provenance"], llvm["identity_stated"], llvm["reasons"]),
                ("in-tree", "reused", True, []),
            )
            self.assertEqual(llvm["build_record"], built)
            self.assertEqual(llvm["build_record"]["built_at_commit"], first_commit)
            self.assertEqual(receipt["compiler"]["source_commit"], later_commit)
            self.assertEqual(json.loads(record_path(root).read_text()), built)
            self.assertEqual(receipt["status"], "release-ready")
            self.assertIn(
                f"  llvm: in-tree, reused, identity stated (source identity "
                f"{llvm['source_identity_sha256'][:12]}, src/llvm-project tree {'3' * 12}, "
                f"built at commit {first_commit[:12]})\n",
                printed,
            )
            self.assertTrue(
                self.verify_receipt(
                    root,
                    stage_root,
                    self.lineage(),
                    require_immutable_lineage=True,
                    require_public_release=True,
                )
            )

        def other_config(digest):
            return {
                "bootstrap_before": self.bootstrap_lineage(hydrated=False, digest=digest),
                "bootstrap_after": self.bootstrap_lineage(hydrated=True, digest=digest),
            }

        # What is NOT evidence. Each row is one reuse that x.py would make
        # without a word (its stamp is unchanged in every one of them) and that
        # a seal must not present as a release.
        cases = (
            (
                "a build directory from before the record: the three seals of 2026-10-12",
                lambda root: record_path(root).unlink(),
                {},
                "it holds no build record (.trust-llvm-build-record.json): it was built before "
                "the recreator wrote one, by a plain x.py build, or over a directory that was "
                "already there",
            ),
            (
                "a commit changed an LLVM source",
                None,
                {"source": self.llvm_source(llvm_tree="9" * 40)},
                f"its build record is for LLVM source identity {self.llvm_source()['identity_sha256'][:12]} "
                f"(built at commit {first_commit[:12]}), and this tree's is "
                f"{self.llvm_source(llvm_tree='9' * 40)['identity_sha256'][:12]}",
            ),
            (
                "a commit changed bootstrap, which composes LLVM's cmake line",
                None,
                {"source": self.llvm_source(bootstrap_tree="9" * 40)},
                f"its build record is for LLVM source identity {self.llvm_source()['identity_sha256'][:12]} ",
            ),
            (
                "another bootstrap config",
                None,
                other_config("c" * 64),
                "its build record is for another bootstrap config (dddddddddddd; this run's is "
                "cccccccccccc)",
            ),
            (
                "other native tools",
                None,
                {"build_authority": self.build_authority("7" * 64)},
                "its build record is for another native tool and SDK authority (888888888888; "
                "this run's is 777777777777)",
            ),
            (
                "an installed file that changed after the recorded build",
                lambda root: library(root).write_bytes(b"relinked by hand"),
                {},
                "its installed files are not the ones its build record fingerprints: they "
                "changed after that build",
            ),
            (
                "a build record that is not one",
                lambda root: record_path(root).write_text("{}\n"),
                {},
                "its build record is unusable: the LLVM build record does not hold exactly the keys ",
            ),
            (
                "a build record that is not JSON",
                lambda root: record_path(root).write_text("built at 1111\n"),
                {},
                "its build record is unusable: it is not JSON: ",
            ),
            (
                "a build record the directory only points at",
                lambda root: (
                    record_path(root).rename(root / "record-of-another-directory.json"),
                    record_path(root).symlink_to(root / "record-of-another-directory.json"),
                ),
                {},
                "its build record is unusable: it is not a regular file",
            ),
        )
        for label, damage, build, reason in cases:
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                self.commit = first_commit
                first_build(root, stage_root)
                if damage is not None:
                    damage(root)
                self.commit = later_commit
                stamp = (self.llvm_out(root) / ".llvm-stamp").read_bytes()
                kept = record_path(root).read_bytes() if record_path(root).exists() else None
                verdict, receipt, printed = self.llvm_build(root, stage_root, **build)
                # Never an error: the build is good for everything but a
                # release claim, and no other machine's ordinary build is
                # stopped or made to rebuild LLVM by this record.
                self.assertTrue(verdict, printed)
                llvm = receipt["llvm_identity"]
                self.assertEqual(
                    (llvm["provenance"], llvm["identity_stated"], llvm["build_record"]),
                    ("reused", False, None),
                )
                self.assertEqual(len(llvm["reasons"]), 1, llvm["reasons"])
                self.assertTrue(
                    llvm["reasons"][0].startswith(f"{where} was reused, and {reason}"),
                    llvm["reasons"],
                )
                self.assertIn(f"    not stated: {where} was reused, and {reason}", printed)
                # The status word is what this build got before the record
                # existed: the LLVM does not move it.
                self.assertEqual(receipt["status"], "release-ready")
                self.assertEqual(receipt["errors"], [])
                # The reuse itself was left as x.py had it.
                self.assertEqual((self.llvm_out(root) / ".llvm-stamp").read_bytes(), stamp)
                self.assertEqual(
                    record_path(root).read_bytes() if record_path(root).exists() else None, kept
                )
                replay = {
                    "llvm_source": build.get("source"),
                    "build_authority": build.get("build_authority"),
                    "bootstrap": build.get("bootstrap_after"),
                }
                # Every consumer of that word gets the answer it got: the
                # verifier bare and with each requirement it had.
                self.assertTrue(self.verify_receipt(root, stage_root, self.lineage(), **replay))
                self.assertTrue(
                    self.verify_receipt(
                        root,
                        stage_root,
                        self.lineage(),
                        require_immutable_lineage=True,
                        require_public_release=True,
                        **replay,
                    )
                )
                # Only the requirement that asks for the identity refuses it.
                output = io.StringIO()
                with patch("sys.stdout", output):
                    self.assertFalse(
                        self.verify_receipt(
                            root, stage_root, self.lineage(), require_llvm_identity=True, **replay
                        )
                    )
                self.assertIn(
                    "  ERROR: the identity of the LLVM this stage carries is required "
                    "(--require-llvm-identity) and this receipt does not state it: "
                    f"{where} was reused, and {reason}",
                    output.getvalue(),
                )

        # An LLVM directory that was there and that x.py rebuilt over: the run
        # watched some of its objects being compiled, not all.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.commit = first_commit
            first_build(root, stage_root)
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, x_py=lambda: library(root).write_bytes(b"rebuilt incrementally")
            )
            self.assertTrue(verdict, printed)
            llvm = receipt["llvm_identity"]
            self.assertEqual(
                (llvm["provenance"], llvm["identity_stated"], llvm["build_record"]),
                ("changed-in-this-run", False, None),
            )
            self.assertEqual(
                llvm["reasons"],
                [
                    f"{where} was there before this run and what is installed changed during "
                    "it: x.py built over objects this run did not watch being compiled"
                ],
            )
            self.assertEqual(receipt["status"], "release-ready")

        # An LLVM build x.py did not finish: no stamp, so no identity.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)

            def interrupted():
                (self.install_llvm(root) / ".llvm-stamp").unlink()

            verdict, receipt, printed = self.llvm_build(root, stage_root, x_py=interrupted)
            self.assertTrue(verdict, printed)
            llvm = receipt["llvm_identity"]
            self.assertEqual((llvm["provenance"], llvm["identity_stated"]), ("unknown", False))
            self.assertEqual(
                llvm["reasons"], [f"x.py left no completed in-tree LLVM build in {where}"]
            )
            self.assertFalse(record_path(root).exists())
            self.assertEqual(receipt["status"], "release-ready")

    def test_an_llvm_built_from_sources_that_are_not_heads_is_not_stated(self):
        # HEAD's object ids are the identity of what was compiled only when the
        # working tree and the index hold exactly HEAD under the LLVM paths.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            verdict, receipt, printed = self.llvm_build(
                root,
                stage_root,
                x_py=lambda: self.install_llvm(root),
                source=self.llvm_source(clean=False),
            )
            self.assertTrue(verdict, printed)
            llvm = receipt["llvm_identity"]
            self.assertEqual(
                (llvm["provenance"], llvm["identity_stated"], llvm["build_record"]),
                ("built-in-this-run", False, None),
            )
            self.assertEqual(
                llvm["reasons"],
                [
                    "something under src/bootstrap, src/llvm-project, src/version is staged, "
                    "modified or untracked: HEAD's object ids are not what gets compiled"
                ],
            )
            # No record is left for a later run to reuse this LLVM on.
            self.assertFalse((self.llvm_out(root) / ".trust-llvm-build-record.json").exists())
            # The word follows the source lineage, which this fixture says is
            # immutable; the LLVM record does not move it. (A real tree with
            # such an edit has a lineage that is not immutable, and is
            # candidate-ready for that.)
            self.assertEqual(receipt["status"], "release-ready")

    def test_an_llvm_built_while_its_inputs_moved_is_not_stated_and_leaves_no_record(self):
        # The record a run leaves is what a later run reuses the LLVM on, so it
        # is left only by a run whose LLVM sources, bootstrap config and native
        # tools were the same before x.py as after it.
        where = f"build/{self.host}/llvm"
        moved = "the bootstrap config or the native tool and SDK authority changed during the build"
        cases = (
            (
                "an LLVM source committed during the build",
                {"source_after": self.llvm_source(llvm_tree="9" * 40)},
                True,
                ["the LLVM source identity changed during the build"],
            ),
            (
                "an LLVM source edited during the build",
                {"source_after": self.llvm_source(clean=False)},
                True,
                [
                    "something under src/bootstrap, src/llvm-project, src/version is staged, "
                    "modified or untracked: HEAD's object ids are not what gets compiled"
                ],
            ),
            (
                "the bootstrap config rewritten during the build",
                {
                    "bootstrap_before": self.bootstrap_lineage(hydrated=False, digest="c" * 64),
                    "bootstrap_after": self.bootstrap_lineage(hydrated=True, digest="d" * 64),
                },
                False,
                [moved],
            ),
            (
                "another compiler on PATH by the end of the build",
                {
                    "build_authority_before": self.build_authority("7" * 64),
                    "build_authority": self.build_authority("8" * 64),
                },
                False,
                [moved],
            ),
            (
                # The commit a build record names is the one LLVM's own build
                # read from git (its VCSRevision.h): with two, there is none.
                "HEAD moved during the build, to a commit with the same LLVM inputs",
                {
                    "before": {
                        **self.lineage(digest="b" * 64),
                        "repositories": [{"path": ".", "head": "7" * 40}],
                    },
                    "after": self.lineage(),
                },
                False,
                ["HEAD moved during the build, so no one commit is the one this LLVM was built at"],
            ),
        )
        for label, build, verdict_expected, reasons in cases:
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                verdict, receipt, printed = self.llvm_build(
                    root, stage_root, x_py=lambda: self.install_llvm(root), **build
                )
                # The config and the authority moving reject the receipt as
                # they always did; the LLVM sources moving under an unchanged
                # source lineage is this record's own finding.
                self.assertEqual(verdict, verdict_expected, printed)
                llvm = receipt["llvm_identity"]
                self.assertEqual(
                    (llvm["provenance"], llvm["identity_stated"], llvm["build_record"]),
                    ("built-in-this-run", False, None),
                )
                self.assertEqual(llvm["reasons"], reasons)
                self.assertFalse((self.llvm_out(root) / ".trust-llvm-build-record.json").exists())
                self.assertEqual(
                    receipt["status"], "release-ready" if verdict_expected else "rejected"
                )

        # What cannot be fingerprinted has no identity either.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)

            def with_a_pipe():
                os.mkfifo(self.install_llvm(root) / "lib" / "pipe")

            verdict, receipt, printed = self.llvm_build(root, stage_root, x_py=with_a_pipe)
            self.assertTrue(verdict, printed)
            self.assertEqual(
                receipt["llvm_identity"]["reasons"],
                [
                    f"{where}/lib/pipe is neither a regular file nor a link",
                    f"x.py left no completed in-tree LLVM build in {where}",
                ],
            )
            self.assertFalse(receipt["llvm_identity"]["identity_stated"])
            self.assertIsNone(receipt["llvm_identity"]["output_fingerprint_sha256"])

    def test_the_llvm_record_cannot_fail_a_build_that_did_not_ask_for_it(self):
        # By default the record is all that is new about a build. So nothing
        # that goes wrong with the record is an error of the audit: the receipt
        # says the identity is not stated, and why, under the status word the
        # build earned without it.
        def passes_and_is_not_stated(root, stage_root, verdict, receipt, printed, reason):
            self.assertTrue(verdict, printed)
            self.assertEqual((receipt["status"], receipt["errors"]), ("release-ready", []))
            llvm = receipt["llvm_identity"]
            self.assertEqual((llvm["identity_stated"], llvm["build_record"]), (False, None))
            self.assertEqual(llvm["reasons"], [reason])
            self.assertEqual(
                recreate_bootstrap._llvm_identity_errors(llvm, receipt), [], "a record the verifier accepts"
            )
            self.assertIn(f"    not stated: {reason}\n", printed)
            self.assertFalse((self.llvm_out(root) / ".trust-llvm-build-record.json").exists())
            self.assertTrue(
                self.verify_receipt(
                    root,
                    stage_root,
                    self.lineage(),
                    require_immutable_lineage=True,
                    require_public_release=True,
                )
            )
            self.assertFalse(
                self.verify_receipt(root, stage_root, self.lineage(), require_llvm_identity=True)
            )
            return llvm

        # A build record that cannot be left in the build directory: the
        # receipt must not quote evidence that is not there.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            with patch.object(
                recreate_bootstrap, "write_llvm_build_record", side_effect=OSError("disk full")
            ) as write:
                verdict, receipt, printed = self.llvm_build(
                    root, stage_root, x_py=lambda: self.install_llvm(root)
                )
            write.assert_called_once()
            self.assertEqual(write.call_args.args[:2], (root, self.host))
            llvm = passes_and_is_not_stated(
                root,
                stage_root,
                verdict,
                receipt,
                printed,
                "this run could not leave its LLVM build record in the build directory: disk full",
            )
            # What was observed is still said.
            self.assertEqual(
                (llvm["mode"], llvm["provenance"], llvm["output_dirs"]),
                ("in-tree", "built-in-this-run", [f"build/{self.host}/llvm"]),
            )
            self.assertRegex(llvm["output_fingerprint_sha256"], r"\A[0-9a-f]{64}\Z")

        # An observation the file system refuses, before x.py and after it:
        # the build goes on, and the receipt says what could not be seen.
        denied = PermissionError(13, "Permission denied")
        unobserved = "the LLVM this build carries could not be observed: [Errno 13] Permission denied"
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.install_llvm(root)
            with patch.object(recreate_bootstrap, "capture_llvm_output", side_effect=denied):
                before = self.observe_llvm(root)
            self.assertEqual(
                before,
                {
                    "mode": "unknown",
                    "mode_reasons": [unobserved],
                    "unobserved": True,
                    "source": {"paths": [], "identity_sha256": None, "clean": False, "errors": []},
                    "output": None,
                    "build_record": None,
                    "build_record_errors": [],
                },
            )
            rows = recreate_bootstrap.llvm_identity_obstacle_rows(
                before, host=self.host, config_sha256="d" * 64, native_authority_sha256="8" * 64
            )
            self.assertEqual(rows, [("unobserved", unobserved)])
            self.assertEqual(
                recreate_bootstrap.llvm_before_report(self.host, before, [unobserved]),
                [f"not observed: {unobserved}"],
            )
            refusal = recreate_bootstrap.llvm_identity_refusal(
                root, self.host, before, rows, self.SEAL_INVOCATION, root / "bootstrap.toml"
            )
            self.assertIn("\nNo single command applies: the recreator could not read what it needs", refusal)
            self.assertNotIn("rm -rf", refusal)
            output = io.StringIO()
            with patch("sys.stdout", output):
                verdict = self.run_audit(root, stage_root, llvm_before=before)
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            llvm = passes_and_is_not_stated(
                root, stage_root, verdict, receipt, output.getvalue(), unobserved
            )
            self.assertEqual((llvm["mode"], llvm["provenance"]), ("unknown", "unknown"))
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            before = self.observe_llvm(root)
            output = io.StringIO()
            with patch.object(recreate_bootstrap, "capture_llvm_output", side_effect=denied), patch(
                "sys.stdout", output
            ):
                verdict = self.run_audit(root, stage_root, llvm_before=before)
            receipt = json.loads((stage_root / "tool-provenance.json").read_text())
            passes_and_is_not_stated(
                root,
                stage_root,
                verdict,
                receipt,
                output.getvalue(),
                "the LLVM this build carries could not be observed after the build: [Errno 13] "
                "Permission denied",
            )

        # A record its own rules refuse (here: a word the vocabulary does not
        # have) is not written, and is not an error either.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            bind = recreate_bootstrap.bind_llvm_identity

            def sideways(*args, **kwargs):
                identity, record = bind(*args, **kwargs)
                return {**identity, "provenance": "sideways"}, record

            with patch.object(recreate_bootstrap, "bind_llvm_identity", side_effect=sideways):
                verdict, receipt, printed = self.llvm_build(
                    root, stage_root, x_py=lambda: self.install_llvm(root)
                )
            llvm = passes_and_is_not_stated(
                root,
                stage_root,
                verdict,
                receipt,
                printed,
                "this run could not form a record of its LLVM: llvm_identity.provenance is "
                "'sideways'; a record of mode in-tree says one of built-in-this-run, reused, "
                "changed-in-this-run, unknown",
            )
            self.assertEqual(
                llvm,
                {
                    "schema": "trust.llvm-identity.v1",
                    "mode": "unknown",
                    "provenance": "unknown",
                    "identity_stated": False,
                    "reasons": llvm["reasons"],
                    "source_identity_sha256": None,
                    "source_paths": [],
                    "output_dirs": [],
                    "output_fingerprint_sha256": None,
                    "build_record": None,
                },
            )

        # NOR ONLY WHAT THE FILE SYSTEM REFUSES, before x.py: whatever the
        # observation meets is the same answer, with the class said where the
        # message alone would not explain it.
        for error, said in (
            (RecursionError("maximum recursion depth exceeded"), "RecursionError: maximum recursion depth exceeded"),
            (MemoryError(), "MemoryError"),
            (ValueError("embedded null byte"), "ValueError: embedded null byte"),
            (KeyError("present"), "KeyError: 'present'"),
        ):
            with self.subTest(said), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                self.install_llvm(root)
                with patch.object(recreate_bootstrap, "capture_llvm_output", side_effect=error):
                    before = self.observe_llvm(root)
                self.assertEqual(
                    before,
                    {
                        "mode": "unknown",
                        "mode_reasons": [f"the LLVM this build carries could not be observed: {said}"],
                        "unobserved": True,
                        "source": {"paths": [], "identity_sha256": None, "clean": False, "errors": []},
                        "output": None,
                        "build_record": None,
                        "build_record_errors": [],
                    },
                )

        # NOR AFTER IT. The audit runs after the
        # whole build, with the stage0 `--fresh-seed` set aside not yet put
        # back or discarded: ANY exception out of the observation after the
        # build, out of the record's own rules or out of the write is the same
        # "not stated", never an exception out of the audit. (A build record
        # nested deeper than the JSON parser's stack raised RecursionError
        # through the first version of this.)
        for label, name, error, reason in (
            (
                "the observation after the build",
                "capture_llvm_output",
                RecursionError("maximum recursion depth exceeded"),
                "the LLVM this build carries could not be observed after the build: RecursionError: "
                "maximum recursion depth exceeded",
            ),
            (
                "the observation after the build, out of memory",
                "capture_llvm_output",
                MemoryError(),
                "the LLVM this build carries could not be observed after the build: MemoryError",
            ),
            (
                "the record's own rules",
                "_llvm_identity_errors",
                KeyError("mode"),
                "this run could not form a record of its LLVM: its own rules could not be applied "
                "to it (KeyError: 'mode')",
            ),
            (
                "leaving the build record",
                "write_llvm_build_record",
                RuntimeError("boom"),
                "this run could not leave its LLVM build record in the build directory: "
                "RuntimeError: boom",
            ),
        ):
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                before = self.observe_llvm(root)
                self.install_llvm(root)
                output = io.StringIO()
                with patch.object(recreate_bootstrap, name, side_effect=error), patch(
                    "sys.stdout", output
                ):
                    verdict = self.run_audit(root, stage_root, llvm_before=before)
                receipt = json.loads((stage_root / "tool-provenance.json").read_text())
                passes_and_is_not_stated(
                    root, stage_root, verdict, receipt, output.getvalue(), reason
                )

    @staticmethod
    def llvm_git(root: Path, *args: str) -> str:
        return subprocess.run(
            ["git", "-C", str(root), *args], check=True, capture_output=True, text=True
        ).stdout

    def test_the_llvm_source_identity_sees_the_commit_x_pys_stamp_does_not(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            git = lambda *args: self.llvm_git(root, *args)  # noqa: E731
            git("init")
            git("config", "user.email", "trust-test@example.invalid")
            git("config", "user.name", "Trust Test")
            source = root / "src" / "llvm-project" / "llvm" / "lib" / "Analysis.cpp"
            recipe = root / "src" / "bootstrap" / "llvm.rs"
            for path, text in (
                (source, "int scev() { return 1; }\n"),
                (recipe, "// the cmake line\n"),
                (root / "src" / "version", "0.10.0\n"),
                (root / "compiler" / "lib.rs", "// not LLVM\n"),
            ):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            git("add", "src", "compiler")
            git("commit", "-m", "fixture")

            def x_py_stamp():
                # What generate_smart_stamp_hash (src/bootstrap/src/utils/build_stamp.rs)
                # hashes for a vendored src/llvm-project: the uncommitted diff, the
                # status, and an empty commit id.
                llvm = root / "src" / "llvm-project"
                return hashlib.sha256(
                    self.llvm_git(llvm, "diff", ".").encode()
                    + self.llvm_git(
                        llvm, "status", ".", "--porcelain", "-z", "--untracked-files=normal"
                    ).encode()
                ).hexdigest()

            first = recreate_bootstrap.capture_llvm_source_identity(root)
            self.assertEqual(first["errors"], [])
            self.assertTrue(first["clean"])
            self.assertEqual(
                first["paths"],
                [
                    {"path": path, "type": kind, "oid": git("rev-parse", f"HEAD:{path}").strip()}
                    for path, kind in (
                        ("src/bootstrap", "tree"),
                        ("src/llvm-project", "tree"),
                        ("src/version", "blob"),
                    )
                ],
            )
            self.assertEqual(
                first["identity_sha256"],
                recreate_bootstrap._llvm_source_identity_sha256(first["paths"]),
            )
            clean_stamp = x_py_stamp()
            self.assertEqual(clean_stamp, hashlib.sha256(b"").hexdigest())

            # A commit that touches nothing LLVM is built from: the same identity.
            (root / "compiler" / "lib.rs").write_text("// still not LLVM\n")
            git("commit", "-am", "elsewhere")
            self.assertEqual(recreate_bootstrap.capture_llvm_source_identity(root), first)

            # An uncommitted edit of an LLVM source: x.py's stamp moves (it would
            # rebuild), and HEAD's ids are no longer what would be compiled.
            source.write_text("int scev() { return 2; }\n")
            self.assertNotEqual(x_py_stamp(), clean_stamp)
            edited = recreate_bootstrap.capture_llvm_source_identity(root)
            self.assertEqual((edited["paths"], edited["clean"]), (first["paths"], False))
            git("add", "src")
            self.assertFalse(recreate_bootstrap.capture_llvm_source_identity(root)["clean"])

            # THE HAZARD: the edit committed. x.py's stamp is back to what it was
            # for the old sources, so until 2026-10-13 x.py kept the LLVM built
            # from them (since then it rebuilds LLVM when HEAD:src/llvm-project
            # moves from the tree recorded beside the stamp, but keeps an LLVM
            # that cannot say what it was built from); the identity is another
            # one.
            git("commit", "-m", "llvm: change scev")
            self.assertEqual(x_py_stamp(), clean_stamp)
            second = recreate_bootstrap.capture_llvm_source_identity(root)
            self.assertTrue(second["clean"])
            self.assertNotEqual(second["identity_sha256"], first["identity_sha256"])
            changed = [
                (old["path"], old["oid"] != new["oid"])
                for old, new in zip(first["paths"], second["paths"])
            ]
            self.assertEqual(
                changed, [("src/bootstrap", False), ("src/llvm-project", True), ("src/version", False)]
            )

            # The recipe is an input too: x.py does not rebuild LLVM when
            # bootstrap changes (its record names only src/llvm-project).
            recipe.write_text("// another cmake line\n")
            git("commit", "-am", "bootstrap: another LLVM flag")
            third = recreate_bootstrap.capture_llvm_source_identity(root)
            self.assertNotEqual(third["identity_sha256"], second["identity_sha256"])

            # Untracked: under an LLVM path it is part of what cmake may read;
            # anywhere else it is not this record's business.
            (root / "notes.txt").write_text("elsewhere\n")
            self.assertTrue(recreate_bootstrap.capture_llvm_source_identity(root)["clean"])
            (source.parent / "Extra.cpp").write_text("int extra;\n")
            self.assertFalse(recreate_bootstrap.capture_llvm_source_identity(root)["clean"])
            (source.parent / "Extra.cpp").unlink()

            # EACH of the three paths is held to HEAD, not src/llvm-project
            # alone: the recipe and the version are compiled into LLVM from
            # the working tree as well. (A check restricted to the LLVM tree
            # passed every case above: a mutant the review found alive.)
            version = root / "src" / "version"

            def is_clean():
                captured = recreate_bootstrap.capture_llvm_source_identity(root)
                self.assertEqual((captured["errors"], captured["paths"]), ([], third["paths"]))
                return captured["clean"]

            self.assertTrue(is_clean())
            for label, dirty, undo in (
                (
                    "the recipe edited",
                    lambda: recipe.write_text("// a cmake line nobody committed\n"),
                    lambda: git("checkout", "--", "src/bootstrap"),
                ),
                (
                    "the recipe edited and staged",
                    lambda: (recipe.write_text("// staged\n"), git("add", "src/bootstrap")),
                    lambda: (git("reset", "-q", "--", "src/bootstrap"), git("checkout", "--", "src/bootstrap")),
                ),
                (
                    "an untracked file in the recipe",
                    lambda: (recipe.parent / "local.rs").write_text("// untracked\n"),
                    lambda: (recipe.parent / "local.rs").unlink(),
                ),
                (
                    "the version edited",
                    lambda: version.write_text("0.10.1\n"),
                    lambda: git("checkout", "--", "src/version"),
                ),
                (
                    "the version edited and staged",
                    lambda: (version.write_text("0.10.2\n"), git("add", "src/version")),
                    lambda: (git("reset", "-q", "--", "src/version"), git("checkout", "--", "src/version")),
                ),
                (
                    "the version removed",
                    lambda: version.unlink(),
                    lambda: git("checkout", "--", "src/version"),
                ),
            ):
                with self.subTest(label):
                    dirty()
                    self.assertFalse(is_clean())
                    undo()
                    self.assertTrue(is_clean())

        # A tree git cannot answer for has no identity, and says why.
        with tempfile.TemporaryDirectory() as directory:
            unknown = recreate_bootstrap.capture_llvm_source_identity(Path(directory))
            self.assertEqual(
                (unknown["paths"], unknown["identity_sha256"], unknown["clean"]), ([], None, False)
            )
            self.assertTrue(unknown["errors"])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.llvm_git(root, "init")
            self.llvm_git(root, "config", "user.email", "trust-test@example.invalid")
            self.llvm_git(root, "config", "user.name", "Trust Test")
            (root / "src").mkdir()
            (root / "src" / "version").write_text("0.10.0\n")
            self.llvm_git(root, "add", "src")
            self.llvm_git(root, "commit", "-m", "no LLVM here")
            partial = recreate_bootstrap.capture_llvm_source_identity(root)
            self.assertEqual(
                partial["errors"],
                ["HEAD does not hold exactly one entry for each of src/bootstrap, src/llvm-project, src/version"],
            )
            self.assertIsNone(partial["identity_sha256"])

    def test_the_llvm_output_fingerprint_is_what_is_installed_and_nothing_else(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            absent = recreate_bootstrap.capture_llvm_output(root, self.host)
            self.assertEqual(
                absent,
                {
                    "dirs": [],
                    "present": False,
                    "stamp_present": False,
                    "uncovered": [],
                    "fingerprint_sha256": None,
                    "errors": [],
                },
            )
            out = self.install_llvm(root)

            def fingerprint():
                captured = recreate_bootstrap.capture_llvm_output(root, self.host)
                self.assertEqual((captured["present"], captured["errors"]), (True, []))
                return captured["fingerprint_sha256"]

            built = fingerprint()
            self.assertRegex(built, r"\A[0-9a-f]{64}\Z")
            self.assertEqual(fingerprint(), built)
            self.assertTrue(recreate_bootstrap.capture_llvm_output(root, self.host)["stamp_present"])

            # NOT in it: x.py's stamp, this script's record, cmake's work tree.
            (out / ".llvm-stamp").write_text("another stamp")
            (out / ".trust-llvm-build-record.json").write_text("{}\n")
            (out / "build" / "CMakeCache.txt").write_text("reconfigured\n")
            (out / "build" / "lib").mkdir()
            (out / "build" / "lib" / "Core.o").write_bytes(b"an object")
            self.assertEqual(fingerprint(), built)
            # Nor ANY other dot entry at the top of the directory: bootstrap may
            # come to leave a second stamp beside its first (a fix of
            # LLVM-STAMP-COMMITTED-1 would), and an LLVM that was recorded
            # before must still be the LLVM that is there after.
            (out / ".llvm-source-stamp").write_text("a second stamp")
            (out / ".bootstrap-state").mkdir()
            (out / ".bootstrap-state" / "tree").write_text("11b2938808\n")
            self.assertEqual(fingerprint(), built)
            (out / ".llvm-stamp").unlink()
            unstamped = recreate_bootstrap.capture_llvm_output(root, self.host)
            self.assertEqual(
                (unstamped["stamp_present"], unstamped["fingerprint_sha256"]), (False, built)
            )

            # In it: every installed file's bytes, every link's target, every name.
            seen = {built}
            for change in (
                lambda: (out / "lib" / "libLLVMCore.a").write_bytes(b"llvm built once: cor3"),
                lambda: (out / "bin" / "llvm-config").write_bytes(b"another llvm-config"),
                lambda: (out / "include" / "llvm" / "Config.h").write_text("#define LLVM 2\n"),
                lambda: (out / "include" / "llvm" / "New.h").write_text("\n"),
                lambda: (out / "lib" / "libLLVMCore.a").rename(out / "lib" / "libLLVMCore2.a"),
                lambda: (
                    (out / "bin" / "llvm-ranlib").unlink(),
                    (out / "bin" / "llvm-ranlib").symlink_to("llvm-ar2"),
                ),
                # A directory named like the work tree, below the top: installed content.
                lambda: (
                    (out / "lib" / "build").mkdir(),
                    (out / "lib" / "build" / "x").write_text("x"),
                ),
                # A dot file below the top is content as well.
                lambda: (out / "lib" / ".hidden.a").write_bytes(b"x"),
                # A link to a directory is its target, as a link to a file is.
                lambda: (out / "lib" / "cmake").symlink_to("build", target_is_directory=True),
                lambda: (
                    (out / "lib" / "cmake").unlink(),
                    (out / "lib" / "cmake").symlink_to("../include", target_is_directory=True),
                ),
            ):
                change()
                seen.add(fingerprint())
            self.assertEqual(len(seen), 11)
            # ... and is not entered: one that points into cmake's work tree
            # does not make that tree installed content.
            (out / "lib" / "cmake").unlink()
            (out / "lib" / "cmake").symlink_to("../build", target_is_directory=True)
            linked = fingerprint()
            self.assertNotIn(linked, seen)
            (out / "build" / "CMakeCache.txt").write_text("reconfigured again\n")
            self.assertEqual(fingerprint(), linked)

        # What is not a directory of files and links is refused, not hashed around.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            elsewhere = self.install_llvm(root / "elsewhere")
            (root / "build" / self.host).mkdir(parents=True)
            self.llvm_out(root).symlink_to(elsewhere, target_is_directory=True)
            linked = recreate_bootstrap.capture_llvm_output(root, self.host)
            self.assertEqual(
                (linked["present"], linked["fingerprint_sha256"], linked["errors"]),
                (False, None, [f"build/{self.host}/llvm is not a real directory"]),
            )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out = self.install_llvm(root)
            os.mkfifo(out / "lib" / "pipe")
            odd = recreate_bootstrap.capture_llvm_output(root, self.host)
            self.assertIsNone(odd["fingerprint_sha256"])
            self.assertEqual(
                odd["errors"],
                [f"build/{self.host}/llvm/lib/pipe is neither a regular file nor a link"],
            )

    def install_lld(self, root: Path, payload: bytes = b"lld built once") -> Path:
        """What x.py's LLD build leaves in build/<host>/lld (bootstrap `lld_out`)."""
        out = root / "build" / self.host / "lld"
        self.executable(out / "bin" / "lld", payload)
        (out / "build").mkdir()
        (out / "build" / "CMakeCache.txt").write_text("lld's own work tree\n")
        (out / ".lld-stamp").write_text("")
        return out

    def test_lld_is_part_of_the_llvm_a_stage_carries_and_what_is_not_covered_is_not_stated(self):
        # x.py builds LLD from src/llvm-project into a directory of its own
        # (rust-lld in the sysroot), and LLD's stamp is weaker than LLVM's: it
        # says a build completed once, whatever was committed or edited since.
        llvm_dir, lld_dir = f"build/{self.host}/llvm", f"build/{self.host}/lld"
        no_record = (
            "it holds no build record (.trust-llvm-build-record.json): it was built before the "
            "recreator wrote one, by a plain x.py build, or over a directory that was already there"
        )

        def output(root):
            return recreate_bootstrap.capture_llvm_output(root, self.host)

        def obstacles(before):
            return recreate_bootstrap.llvm_identity_obstacles(
                before, host=self.host, config_sha256="d" * 64, native_authority_sha256="8" * 64
            )

        def refusal(root, before):
            rows = recreate_bootstrap.llvm_identity_obstacle_rows(
                before, host=self.host, config_sha256="d" * 64, native_authority_sha256="8" * 64
            )
            self.assertEqual([reason for _kind, reason in rows], obstacles(before))
            return recreate_bootstrap.llvm_identity_refusal(
                root, self.host, before, rows, self.SEAL_INVOCATION, root / "bootstrap.toml"
            )

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.install_llvm(root)
            alone = output(root)
            self.assertEqual((alone["dirs"], alone["stamp_present"]), ([llvm_dir], True))
            lld = self.install_lld(root)
            both = output(root)
            self.assertEqual(
                (both["dirs"], both["stamp_present"], both["errors"]), ([llvm_dir, lld_dir], True, [])
            )
            self.assertNotEqual(both["fingerprint_sha256"], alone["fingerprint_sha256"])
            (lld / "build" / "CMakeCache.txt").write_text("reconfigured\n")
            self.assertEqual(output(root)["fingerprint_sha256"], both["fingerprint_sha256"])
            (lld / "bin" / "lld").write_bytes(b"another lld")
            self.assertNotEqual(output(root)["fingerprint_sha256"], both["fingerprint_sha256"])
            # Every directory that is there holds a completed build, or none does.
            (lld / ".lld-stamp").unlink()
            self.assertFalse(output(root)["stamp_present"])
            (lld / ".lld-stamp").write_text("")
            llvm_stamp = self.llvm_out(root) / ".llvm-stamp"
            kept = llvm_stamp.read_bytes()
            llvm_stamp.unlink()
            self.assertFalse(output(root)["stamp_present"])
            llvm_stamp.write_bytes(kept)
            self.assertTrue(output(root)["stamp_present"])
            # The same bytes under another directory are another entry.
            moved = output(root)["fingerprint_sha256"]
            (lld / "bin" / "lld").rename(self.llvm_out(root) / "bin" / "lld")
            self.assertNotEqual(output(root)["fingerprint_sha256"], moved)

        # Built together in one run, then reused together on the one record;
        # then an LLD relinked since, which x.py's stamp does not see.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, x_py=lambda: (self.install_llvm(root), self.install_lld(root))
            )
            self.assertTrue(verdict, printed)
            llvm = receipt["llvm_identity"]
            self.assertEqual(
                (llvm["provenance"], llvm["identity_stated"], llvm["output_dirs"]),
                ("built-in-this-run", True, [llvm_dir, lld_dir]),
            )
            verdict, receipt, printed = self.llvm_build(root, stage_root)
            self.assertTrue(verdict, printed)
            self.assertEqual(
                (receipt["llvm_identity"]["provenance"], receipt["llvm_identity"]["identity_stated"]),
                ("reused", True),
            )
            self.assertEqual(receipt["llvm_identity"]["output_dirs"], [llvm_dir, lld_dir])
            self.assertTrue(
                self.verify_receipt(
                    root, stage_root, self.lineage(), require_immutable_lineage=True
                )
            )
            (root / lld_dir / "bin" / "lld").write_bytes(b"relinked by hand")
            verdict, receipt, printed = self.llvm_build(root, stage_root)
            self.assertTrue(verdict, printed)
            self.assertEqual(
                receipt["llvm_identity"]["reasons"],
                [
                    f"{llvm_dir} and {lld_dir} was reused, and its installed files are not the ones "
                    "its build record fingerprints: they changed after that build"
                ],
            )
            self.assertEqual(receipt["status"], "release-ready")
            before = self.observe_llvm(root)
            self.assertIn(
                f"\n    rm -rf {root / llvm_dir} {root / lld_dir}\n", refusal(root, before)
            )

        # An LLD built over an LLVM that was there (rust.lld turned on later):
        # the run watched the one being built and not the other.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_llvm(root)
            )
            self.assertTrue(receipt["llvm_identity"]["identity_stated"], printed)
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_lld(root)
            )
            self.assertTrue(verdict, printed)
            llvm = receipt["llvm_identity"]
            self.assertEqual(
                (llvm["provenance"], llvm["identity_stated"], llvm["output_dirs"]),
                ("changed-in-this-run", False, [llvm_dir, lld_dir]),
            )
            self.assertEqual(
                llvm["reasons"],
                [
                    f"{llvm_dir} was there before this run and what is installed changed during "
                    "it: x.py built over objects this run did not watch being compiled"
                ],
            )

        # LLVM removed and an old LLD left behind: x.py keeps that LLD (its
        # stamp is there), so this is not a build from nothing, and the
        # refusal names the directory that is left.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.install_lld(root)
            before = self.observe_llvm(root)
            self.assertEqual(
                obstacles(before), [f"{lld_dir} is there and x.py will use it, and {no_record}"]
            )
            self.assertIn(f"\n    rm -rf {root / lld_dir}\n", refusal(root, before))
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_llvm(root)
            )
            self.assertTrue(verdict, printed)
            llvm = receipt["llvm_identity"]
            self.assertEqual(
                (llvm["provenance"], llvm["identity_stated"], llvm["build_record"]),
                ("changed-in-this-run", False, None),
            )
            self.assertFalse((self.llvm_out(root) / ".trust-llvm-build-record.json").exists())

        # An LLD with no LLVM beside it after the build is not an in-tree LLVM.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_lld(root)
            )
            self.assertTrue(verdict, printed)
            self.assertEqual(
                receipt["llvm_identity"]["reasons"],
                [f"x.py left no completed in-tree LLVM build in {llvm_dir}"],
            )

        # What x.py builds from src/llvm-project in a layout this record does
        # not fingerprint: the identity is not stated for part of what a stage
        # carries, and removing LLVM would not make it so.
        for uncovered in (
            f"build/{self.host}/native/sanitizers",
            f"build/{self.host}/native/libunwind",
            f"build/{self.host}/offload",
            # Per target: the std of another target brings its own.
            "build/other-target/native/crt",
        ):
            with self.subTest(uncovered=uncovered), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                reason = (
                    f"{uncovered} is there: x.py builds it from src/llvm-project too, and this "
                    "record does not cover it"
                )

                def x_py():
                    self.install_llvm(root)
                    (root / uncovered).mkdir(parents=True)

                verdict, receipt, printed = self.llvm_build(root, stage_root, x_py=x_py)
                self.assertTrue(verdict, printed)
                llvm = receipt["llvm_identity"]
                self.assertEqual(
                    (llvm["provenance"], llvm["identity_stated"], llvm["build_record"]),
                    ("built-in-this-run", False, None),
                )
                self.assertEqual(llvm["reasons"], [reason])
                self.assertFalse((self.llvm_out(root) / ".trust-llvm-build-record.json").exists())
                self.assertEqual(receipt["status"], "release-ready")
                before = self.observe_llvm(root)
                self.assertEqual(
                    obstacles(before),
                    [reason, f"{llvm_dir} is there and x.py will use it, and {no_record}"],
                )
                refused = refusal(root, before)
                self.assertIn(f"  - {reason}\n", refused)
                # Each obstacle with its own command, and where a command
                # cannot be enough the refusal says so.
                self.assertIn(f"\n    rm -rf {root / llvm_dir}\n", refused)
                self.assertIn(
                    "If the bootstrap config no longer builds them (the recreator's own does not):\n"
                    f"    rm -rf {root / uncovered}\n"
                    "For a config that does build them no single command applies: such a build cannot\n"
                    "state its LLVM's identity with this record.\n",
                    refused,
                )
        # A directory beside them that is none of these is nobody's business here.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)

            def x_py():
                self.install_llvm(root)
                (root / "build" / self.host / "native" / "rtstartup").mkdir(parents=True)
                (root / "build" / "tmp").mkdir()

            verdict, receipt, printed = self.llvm_build(root, stage_root, x_py=x_py)
            self.assertTrue(receipt["llvm_identity"]["identity_stated"], printed)

    def test_the_llvm_mode_is_read_from_the_config_x_py_obeys(self):
        external = "/opt/llvm 22/bin/llvm-config"
        rows = (
            ("[llvm]\ndownload-ci-llvm = false\n", None, "in-tree", None),
            # `--llvm-config` reaches the config only when this script writes
            # it; an existing config is reused as it is.
            (
                "[llvm]\ndownload-ci-llvm = false\n",
                external,
                "unknown",
                f"--llvm-config {external!r} was given, and bootstrap.toml, reused as it is, does "
                "not name it: x.py would not link it",
            ),
            (
                f'[llvm]\ndownload-ci-llvm = false\n[target.{self.host}]\nllvm-config = "{external}"\n',
                external,
                "external",
                None,
            ),
            (
                f'[target.{self.host}]\nllvm-config = "{external}"\n',
                None,
                "unknown",
                f"bootstrap.toml links the external llvm-config {external!r}, which is not the "
                "one this run binds (--llvm-config None)",
            ),
            (
                f'[target.{self.host}]\nllvm-config = "/opt/other/llvm-config"\n',
                external,
                "unknown",
                "bootstrap.toml links the external llvm-config '/opt/other/llvm-config', which is "
                f"not the one this run binds (--llvm-config {external!r})",
            ),
            # Another target's llvm-config is not the host's LLVM.
            (
                '[llvm]\ndownload-ci-llvm = false\n[target.other-host]\nllvm-config = "/x"\n',
                None,
                "in-tree",
                None,
            ),
            *(
                (
                    text,
                    None,
                    "unknown",
                    f"bootstrap.toml does not set llvm.download-ci-llvm = false (it is {value!r}): "
                    "x.py may link a downloaded LLVM, which this record cannot identify",
                )
                for text, value in (
                    ("[llvm]\ndownload-ci-llvm = true\n", True),
                    ('[llvm]\ndownload-ci-llvm = "if-unchanged"\n', "if-unchanged"),
                    ("[llvm]\nninja = true\n", None),
                    ('profile = "compiler"\n', None),
                )
            ),
            (
                "[llvm\n",
                None,
                "unknown",
                "the bootstrap config could not be read for its LLVM settings: ",
            ),
            # Nor is a config nested deeper than the TOML parser's stack: it is
            # a reason, not an exception out of the observation.
            (
                "a = " + "[" * 2000 + "\n",
                None,
                "unknown",
                "the bootstrap config could not be read for its LLVM settings: RecursionError",
            ),
            # `include`: x.py merges the named files into this one, and they
            # supply whatever it leaves unset: another llvm-config, any llvm.*
            # key. Only this file is read and hashed, so nothing it says
            # settles which LLVM is linked. Whatever else it holds.
            *(
                (
                    text,
                    argument,
                    "unknown",
                    "bootstrap.toml has an `include` key: x.py merges the included files, which "
                    "can name another llvm-config or configure LLVM differently, and neither this "
                    "record nor the receipt's config digest covers them",
                )
                for text, argument in (
                    ('include = ["extra.toml"]\n[llvm]\ndownload-ci-llvm = false\n', None),
                    ("include = []\n[llvm]\ndownload-ci-llvm = false\n", None),
                    (
                        f'include = ["extra.toml"]\n[llvm]\ndownload-ci-llvm = false\n'
                        f'[target.{self.host}]\nllvm-config = "{external}"\n',
                        external,
                    ),
                    ('include = ["extra.toml"]\n', external),
                )
            ),
        )
        with tempfile.TemporaryDirectory() as directory:
            config = Path(directory) / "bootstrap.toml"
            for text, argument, mode, reason in rows:
                with self.subTest(text=text, argument=argument):
                    config.write_text(text)
                    got_mode, reasons = recreate_bootstrap._llvm_mode(config, self.host, argument)
                    self.assertEqual(got_mode, mode)
                    if reason is None:
                        self.assertEqual(reasons, [])
                    else:
                        self.assertEqual(len(reasons), 1)
                        self.assertTrue(reasons[0].startswith(reason), reasons)
            config.unlink()
            self.assertEqual(
                recreate_bootstrap._llvm_mode(config, self.host, None)[0], "unknown"
            )

        # THE CASE THE REVIEW MEASURED. An LLVM built from nothing and
        # recorded; then the same config gains an `include` whose file names an
        # external llvm-config. Nothing the build record compares has to move
        # (the top-level file's digest is whatever the fixture says it is), and
        # the stage would link another LLVM: the reuse is not stated.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, x_py=lambda: self.install_llvm(root)
            )
            self.assertTrue(receipt["llvm_identity"]["identity_stated"], printed)
            (root / "bootstrap.toml").write_text(
                'include = ["extra.toml"]\n[llvm]\ndownload-ci-llvm = false\n'
            )
            (root / "extra.toml").write_text(
                f'[target.{self.host}]\nllvm-config = "/opt/other/bin/llvm-config"\n'
            )
            verdict, receipt, printed = self.llvm_build(root, stage_root)
            self.assertTrue(verdict, printed)
            llvm = receipt["llvm_identity"]
            self.assertEqual(
                (llvm["mode"], llvm["provenance"], llvm["identity_stated"], llvm["build_record"]),
                ("unknown", "unknown", False, None),
            )
            self.assertEqual(len(llvm["reasons"]), 1)
            self.assertTrue(llvm["reasons"][0].startswith("bootstrap.toml has an `include` key"))
            # And it is known before x.py starts.
            before = self.observe_llvm(root)
            self.assertEqual(
                recreate_bootstrap.llvm_identity_obstacle_rows(
                    before, host=self.host, config_sha256="d" * 64, native_authority_sha256="8" * 64
                ),
                [("config", llvm["reasons"][0])],
            )

        # AN EXTERNAL LLVM IS NEVER STATED, whatever the build authority bound
        # of its llvm-config: the build did not watch it being built and holds
        # no record of such a build, and the authority binds the llvm-config
        # executable, not the libraries it points at. (Until the independent
        # re-read of 2026-10-13 the first row was stated, with this checkout's
        # LLVM source ids beside it.) An LLVM of unknown mode is not either, and
        # since the follow-up of 2026-10-13 nothing of this checkout stands
        # beside it: the config x.py obeys does not say which LLVM is linked, so
        # its src/llvm-project and its build directory may describe one the
        # stage does not link (the third reading measured a config naming an
        # llvm-config the run did not bind, sealed with this checkout's ids).
        reader = load_stage_receipt_reader()
        not_bound_here = (
            f"bootstrap.toml links the external llvm-config {external!r}, which is not the one "
            "this run binds (--llvm-config None)"
        )
        bound = {"name": "llvm-config", "status": "bound", "sha256": "5" * 64}
        external_reason = (
            "the stage links an external LLVM through --llvm-config: this build did not watch "
            "that LLVM being built and it carries no record of such a build, and the build "
            "authority binds the llvm-config executable (its path, sha256 and version) and its "
            "dylib closure, not the libraries it points at; so which sources that LLVM was built "
            "from is not established, and this checkout's src/llvm-project does not describe it"
        )
        self.assertEqual(recreate_bootstrap.LLVM_EXTERNAL_REASON, external_reason)
        unbound = "the build authority did not bind the external llvm-config"
        moved = "the bootstrap config or the native tool and SDK authority changed during the build"
        for mode, mode_reasons, selected, stable, reasons in (
            ("external", [], bound, True, [external_reason]),
            ("external", [], None, True, [external_reason, unbound]),
            ("external", [], {**bound, "status": "rejected"}, True, [external_reason, unbound]),
            ("external", [], bound, False, [external_reason, moved]),
            ("unknown", ["x.py may link a downloaded LLVM"], None, True, ["x.py may link a downloaded LLVM"]),
            ("unknown", [not_bound_here], None, True, [not_bound_here]),
            ("unknown", [not_bound_here], bound, False, [not_bound_here, moved]),
        ):
            with self.subTest(mode=mode, selected=selected, stable=stable), \
                    tempfile.TemporaryDirectory() as directory, patch.object(
                        recreate_bootstrap, "capture_llvm_source_identity", return_value=self.llvm_source()
                    ) as asked_git:
                root = Path(directory)
                # An in-tree LLVM left in the build directory by an earlier
                # build is not what such a stage carries.
                self.install_llvm(root)
                identity, written = recreate_bootstrap.bind_llvm_identity(
                    root,
                    self.host,
                    {
                        "mode": mode,
                        "mode_reasons": mode_reasons,
                        "source": self.llvm_source(),
                        "output": None,
                        "build_record": None,
                        "build_record_errors": [],
                    },
                    commit=self.commit,
                    commit_before=self.commit,
                    config_sha256="d" * 64,
                    native_authority_sha256="8" * 64,
                    selected_llvm=selected,
                    inputs_stable=stable,
                )
                self.assertIsNone(written)
                # This checkout's LLVM source ids stand beside neither: they do
                # not describe an external LLVM and are not known to describe
                # one of unknown mode, and git is not asked for either.
                is_external = mode == "external"
                asked_git.assert_not_called()
                self.assertEqual(
                    identity,
                    {
                        "schema": "trust.llvm-identity.v1",
                        "mode": mode,
                        "provenance": mode,
                        "identity_stated": False,
                        "reasons": reasons,
                        "source_identity_sha256": None,
                        "source_paths": [],
                        "output_dirs": [],
                        "output_fingerprint_sha256": None,
                        "build_record": None,
                    },
                )
                receipt = {"host": self.host, "build_authority": {"selected_llvm": selected}}
                self.assertEqual(recreate_bootstrap._llvm_identity_errors(identity, receipt), [])
                self.assertEqual(reader.llvm_identity_errors(identity, receipt), [])
                self.assertFalse((self.llvm_out(root) / ".trust-llvm-build-record.json").exists())
                lines = reader.llvm_lines({**receipt, "llvm_identity": identity})
                self.assertEqual(
                    lines,
                    [
                        f"stage_receipt_llvm={mode}",
                        "stage_receipt_llvm_identity=not-stated",
                        f"stage_receipt_llvm_provenance={mode}",
                        "stage_receipt_llvm_source_sha256=not-recorded",
                        "stage_receipt_llvm_source_tree=not-recorded",
                        "stage_receipt_llvm_built_at_commit=not-recorded",
                        "stage_receipt_llvm_output_sha256=not-recorded",
                    ],
                )
                if not is_external:
                    self.assertEqual(
                        recreate_bootstrap.llvm_identity_summary(identity),
                        "unknown: which LLVM x.py links is not known, identity NOT stated (no "
                        "source identity describes it)",
                    )
                    # THE RECORD 381ac1ea0d's RECREATOR WROTE for it: the same,
                    # with this checkout's LLVM source ids. Still a receipt both
                    # rules accept (a stage sealed by default stays sealable),
                    # and the seal still writes no id of this checkout beside it.
                    source = self.llvm_source()
                    old_shape = {
                        **identity,
                        "source_identity_sha256": source["identity_sha256"],
                        "source_paths": source["paths"],
                    }
                    self.assertEqual(recreate_bootstrap._llvm_identity_errors(old_shape, receipt), [])
                    self.assertEqual(reader.llvm_identity_errors(old_shape, receipt), [])
                    self.assertEqual(reader.llvm_lines({**receipt, "llvm_identity": old_shape}), lines)
                if is_external:
                    self.assertEqual(
                        recreate_bootstrap.llvm_identity_summary(identity),
                        "external, linked through --llvm-config, identity NOT stated (no source "
                        "identity describes it)",
                    )
                    # THE RECORD THE FIRST VERSION WROTE, and each part of it:
                    # stated on the bound llvm-config, with this checkout's
                    # LLVM source ids. Both readers refuse it, bound or not.
                    source = self.llvm_source()
                    for label, changes, messages in (
                        (
                            "stated, with the checkout's ids",
                            {
                                "identity_stated": True,
                                "reasons": [],
                                "source_identity_sha256": source["identity_sha256"],
                                "source_paths": source["paths"],
                            },
                            [
                                "llvm_identity states the identity of an external LLVM: which sources "
                                "an LLVM linked through --llvm-config was built from is never "
                                "established",
                                "llvm_identity of an external LLVM carries a source identity: this "
                                "checkout's LLVM sources do not describe an LLVM linked through "
                                "--llvm-config",
                            ],
                        ),
                        (
                            "not stated, with the checkout's ids",
                            {
                                "source_identity_sha256": source["identity_sha256"],
                                "source_paths": source["paths"],
                            },
                            [
                                "llvm_identity of an external LLVM carries a source identity: this "
                                "checkout's LLVM sources do not describe an LLVM linked through "
                                "--llvm-config",
                            ],
                        ),
                        (
                            "stated, with no ids",
                            {"identity_stated": True, "reasons": []},
                            ["llvm_identity states an identity without a source identity"],
                        ),
                    ):
                        with self.subTest(label):
                            old_shape = {**identity, **changes}
                            self.assertEqual(
                                recreate_bootstrap._llvm_identity_errors(old_shape, receipt), messages
                            )
                            self.assertEqual(reader.llvm_identity_errors(old_shape, receipt), messages)

        # BEFORE x.py, an external LLVM is one thing known to stand against the
        # claim, and the only one: nothing of this checkout's LLVM sources or
        # of the build directory is observed for it (an old in-tree LLVM is
        # there, and the LLVM sources are not asked about), because none of it
        # is what the stage links.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.install_llvm(root)
            config = root / "bootstrap.toml"
            config.write_text(
                f'[llvm]\ndownload-ci-llvm = false\n[target.{self.host}]\nllvm-config = "{external}"\n'
            )
            with patch.object(recreate_bootstrap, "capture_llvm_source_identity") as asked_git, \
                    patch.object(recreate_bootstrap, "capture_llvm_output") as looked:
                before = recreate_bootstrap.capture_llvm_before_build(root, self.host, external, config)
            asked_git.assert_not_called()
            looked.assert_not_called()
            self.assertEqual(
                before,
                {
                    "mode": "external",
                    "mode_reasons": [],
                    "source": {"paths": [], "identity_sha256": None, "clean": False, "errors": []},
                    "output": None,
                    "build_record": None,
                    "build_record_errors": [],
                },
            )
            rows = recreate_bootstrap.llvm_identity_obstacle_rows(
                before, host=self.host, config_sha256="d" * 64, native_authority_sha256="8" * 64
            )
            self.assertEqual(rows, [("external", external_reason)])
            self.assertEqual(
                recreate_bootstrap.llvm_before_report(self.host, before, [external_reason]),
                ["mode: external", f"its identity cannot be stated: {external_reason}"],
            )
            asked = [*self.SEAL_INVOCATION, "--llvm-config", external]
            refusal = recreate_bootstrap.llvm_identity_refusal(
                root, self.host, before, rows, asked, config
            )
            self.assertEqual(
                refusal,
                "\n"
                "Refusing to build: --require-llvm-identity asks that this build state the identity of\n"
                "the LLVM it carries, and it is known now that it could not:\n"
                f"  - {external_reason}\n"
                "No single command applies: nothing in this checkout or its build directory is in the\n"
                "way, and nothing removed from them would help. The claim needs a build WITHOUT\n"
                "--llvm-config, one that builds the in-tree LLVM (src/llvm-project) or reuses one with\n"
                "the record of such a build. Run this command again without --llvm-config, and with\n"
                f"--force-config if {config} names an llvm-config (it OVERWRITES that file).\n"
                "Without --require-llvm-identity this build goes ahead on the LLVM --llvm-config names,\n"
                "and its receipt says that the identity is not stated, and why.",
            )
            # No `rm`: the directory is not the obstacle. And not "the same
            # command again": the same command links the same LLVM.
            self.assertNotIn("rm -rf", refusal)
            self.assertNotIn("the same command", refusal)
            # The step that follows the advice: without --llvm-config, the
            # config that still names one is the obstacle, and its refusal
            # says how the recreator writes one that does not.
            with patch.object(
                recreate_bootstrap, "capture_llvm_source_identity", return_value=self.llvm_source()
            ):
                before = recreate_bootstrap.capture_llvm_before_build(root, self.host, None, config)
            rows = recreate_bootstrap.llvm_identity_obstacle_rows(
                before, host=self.host, config_sha256="d" * 64, native_authority_sha256="8" * 64
            )
            self.assertEqual([kind for kind, _reason in rows], ["config"])
            refusal = recreate_bootstrap.llvm_identity_refusal(
                root, self.host, before, rows, self.SEAL_INVOCATION, config
            )
            self.assertIn(
                f"No single command applies to the bootstrap config: {config} is what x.py obeys,\n"
                "and it must itself say that the in-tree LLVM is linked: `[llvm] download-ci-llvm =\n"
                f"false`, no `include`, and no `[target.{self.host}] llvm-config` (an LLVM linked through\n"
                "--llvm-config is never stated). Edit it, or drop --llvm-config and let the recreator\n"
                "write its own again with --force-config, which OVERWRITES that file.\n"
                "Then run the same command again:\n",
                refusal,
            )

        # BEFORE x.py, AN LLVM OF UNKNOWN MODE is its config's reasons and
        # nothing else, in the two cases the third reading of 2026-10-13
        # measured (a config naming an llvm-config, and a run with no
        # --llvm-config or with one spelled otherwise): no source identity is
        # asked for, printed or recorded, and the build directory is not looked
        # at, because neither is known to be what the stage links. (Until the
        # follow-up of that day the log printed, and the receipt and the seal
        # carried, this checkout's LLVM source ids beside it.)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.install_llvm(root)
            named = str(root / "opt" / "bin" / "llvm-config")
            config = root / "bootstrap.toml"
            config.write_text(f'[llvm]\ndownload-ci-llvm = false\n[target.{self.host}]\nllvm-config = "{named}"\n')
            for given in (None, str(root / "opt" / "bin" / ".." / "bin" / "llvm-config")):
                with self.subTest(given=given):
                    reason = (
                        f"bootstrap.toml links the external llvm-config {named!r}, which is not the one "
                        f"this run binds (--llvm-config {given!r})"
                    )
                    with patch.object(recreate_bootstrap, "capture_llvm_source_identity") as asked_git, \
                            patch.object(recreate_bootstrap, "capture_llvm_output") as looked:
                        before, rows, printed = recreate_bootstrap.observe_llvm_before_build(
                            root,
                            self.host,
                            given,
                            config,
                            config_sha256="d" * 64,
                            native_authority_sha256="8" * 64,
                        )
                    asked_git.assert_not_called()
                    looked.assert_not_called()
                    self.assertEqual(
                        before,
                        {
                            "mode": "unknown",
                            "mode_reasons": [reason],
                            "source": {"paths": [], "identity_sha256": None, "clean": False, "errors": []},
                            "output": None,
                            "build_record": None,
                            "build_record_errors": [],
                        },
                    )
                    self.assertEqual(rows, [("config", reason)])
                    self.assertEqual(printed, ["mode: unknown", f"its identity cannot be stated: {reason}"])

    def test_the_status_word_does_not_depend_on_the_llvm_record(self):
        # One function chooses the status word, for the audit and for the
        # verifier, and it is the function it was before the record existed:
        # it is not handed the record. Everything that reads the word (the
        # recreator's own fresh-seed verification, `--verify-stage-provenance`
        # with either lineage requirement, compat_check.py, the evidence
        # collectors, run_tests_after_build.sh, trust_e2e_receipt.py,
        # promotion) therefore gets the answer it got.
        classify = recreate_bootstrap._classify_receipt_status
        self.assertEqual(
            list(inspect.signature(classify).parameters), ["source_status", "bootstrap_lineage"]
        )
        release = {"status": "trust_from_trust", "validated_seed": {
            "status": "validated",
            "materialization_status": "fresh-from-validated-archives",
            "admission_status": "internal-admitted",
        }}
        public = copy.deepcopy(release)
        public["validated_seed"]["admission_status"] = "public-promoted"
        preexisting = copy.deepcopy(release)
        preexisting["validated_seed"]["materialization_status"] = "preexisting-unproven"
        genesis = {"status": "local_genesis", "validated_seed": None}
        for source, lineage, word in (
            ("immutable_release", release, "internal-release-ready"),
            ("immutable_release", public, "release-ready"),
            ("immutable_release", preexisting, "candidate-ready"),
            ("immutable_release", genesis, "candidate-ready"),
            ("staged_proposal", release, "candidate-ready"),
        ):
            with self.subTest(source=source, word=word):
                self.assertEqual(classify(source, lineage), word)

        # The same build audited three ways: without the record, over an LLVM
        # it watched being built (stated), and over an LLVM directory that was
        # there with nothing saying what it was built from (not stated). One
        # receipt, but for the one key; for each class of lineage.
        internal = {
            "bootstrap_before": self.bootstrap_lineage(hydrated=False, admission_status="internal-admitted"),
            "bootstrap_after": self.bootstrap_lineage(hydrated=True, admission_status="internal-admitted"),
        }
        extracted = {
            "bootstrap_before": self.bootstrap_lineage(hydrated=True),
            "bootstrap_after": self.bootstrap_lineage(hydrated=True),
        }
        for label, lineage, word in (
            ("a public release", {}, "release-ready"),
            ("an internal release", internal, "internal-release-ready"),
            ("a seed that was already extracted", extracted, "candidate-ready"),
        ):
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                receipt_path = stage_root / "tool-provenance.json"
                self.assertTrue(self.run_audit(root, stage_root, **lineage))
                without = json.loads(receipt_path.read_text())
                self.assertEqual(without["status"], word)
                self.assertNotIn("llvm_identity", without)

                verdict, stated, printed = self.llvm_build(
                    root, stage_root, x_py=lambda: self.install_llvm(root), **lineage
                )
                self.assertTrue(verdict, printed)
                self.assertTrue(stated.pop("llvm_identity")["identity_stated"])
                self.assertEqual(stated, without)

                (self.llvm_out(root) / ".trust-llvm-build-record.json").unlink()
                verdict, unstated, printed = self.llvm_build(root, stage_root, **lineage)
                self.assertTrue(verdict, printed)
                self.assertFalse(unstated.pop("llvm_identity")["identity_stated"])
                self.assertEqual(unstated, without)

    def main_around_llvm(self, argv, observed, **results):
        """main(argv) with every capture and build step replaced, the LLVM one by `observed`.

        `results` replaces what a step answers: a value, or a function of the
        step's own arguments. Returns (exit status, the steps in order, what
        was printed, the mocks by name).
        """
        events: list[str] = []

        def step(name, result):
            def run(*args, **kwargs):
                events.append(name)
                return result(*args, **kwargs) if callable(result) else result

            return run

        output = io.StringIO()
        with ExitStack() as stack:
            for name in (
                "ensure_python_311",
                "line_buffer_output",
                "print_prereqs",
                "ensure_submodules",
                "scrub_pat_from_remotes",
            ):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            for name, result in (
                ("atpkg_trust_sysroot", None),
                ("repo_root", Path("/checkout")),
                ("host_triple", self.host),
                ("resolve_seed", True),
                ("check_prereqs", []),
                (
                    "write_config",
                    recreate_bootstrap.WrittenBootstrapConfig(
                        Path("/checkout/bootstrap.toml"), "b" * 64
                    ),
                ),
                (
                    "capture_source_lineage",
                    {
                        "status": "immutable_release",
                        "closure_sha256": "a" * 64,
                        "repositories": [{"path": ".", "head": self.commit}],
                        "errors": [],
                    },
                ),
                (
                    "capture_bootstrap_lineage",
                    {
                        "status": "seed-validated-pending-hydration",
                        "mode": "seed",
                        "config_path": "bootstrap.toml",
                        "config_sha256": "b" * 64,
                        "errors": [],
                    },
                ),
            ):
                stack.enter_context(patch.object(recreate_bootstrap, name, return_value=result))
            mocks = {
                name: stack.enter_context(
                    patch.object(
                        recreate_bootstrap, name, side_effect=step(name, results.get(name, result))
                    )
                )
                for name, result in (
                    ("quarantine_seed_stage0", Path("/checkout/build/test-host/stage0.kept")),
                    (
                        "capture_build_authority",
                        {"status": "ready", "authority_sha256": "c" * 64, "errors": []},
                    ),
                    ("capture_llvm_before_build", observed),
                    ("run_xpy_build", 0),
                    ("leave_llvm_build_record_after_failed_build", None),
                    ("install_ay_solver", True),
                    ("audit_stage_tool_provenance", True),
                    ("verify_stage_tool_provenance", True),
                    ("discard_seed_stage0_quarantine", None),
                    ("recover_seed_stage0_quarantine", None),
                    ("maybe_register_rustup_toolchain", True),
                )
            }
            self.assertLessEqual(set(results), set(mocks))
            stack.enter_context(patch("sys.stdout", output))
            status = recreate_bootstrap.main(argv)
        return status, events, output.getvalue(), mocks

    def test_words_after_the_options_are_refused_where_nothing_reads_them(self):
        # argparse hands every word from the first one that is not an option,
        # and everything after `--`, to the x.py remainder. Only a build that
        # runs x.py reads it: forwarded for stage 0/1, refused for Stage2+. The
        # verifier answered before it looked, so a requirement typed there was
        # dropped without a word: `--verify-stage-provenance --stage 2 stage2
        # --require-llvm-identity` verified WITHOUT it, exit 0 (measured by the
        # third reading of the LLVM-identity change, 2026-10-13), and
        # `--no-build` set up a checkout. Each spelling is now refused, exit 2,
        # before anything is verified, observed, configured or built.
        from unittest.mock import call

        checkout = Path("/checkout")
        refused = (
            "They are refused, never ignored: an option typed after a stray word or `--` is not "
            "read as an option. Type every option before any other word.\n"
        )
        for argv, mode, words in (
            (
                ["--verify-stage-provenance", "--stage", "2", "stage2", "--require-llvm-identity"],
                "--verify-stage-provenance",
                "stage2 --require-llvm-identity",
            ),
            (["--verify-stage-provenance", "--", "--require-llvm-identity"], "--verify-stage-provenance", "--require-llvm-identity"),
            (
                ["--verify-stage-provenance", "--require-immutable-lineage", "--", "--require-public-release"],
                "--verify-stage-provenance",
                "--require-public-release",
            ),
            (["--verify-stage-provenance", "--stage", "2", "stray"], "--verify-stage-provenance", "stray"),
            (["--verify-stage-provenance", "--", "a b"], "--verify-stage-provenance", "'a b'"),
            (["--no-build", "--stage", "1", "--", "--require-llvm-identity"], "--no-build", "--require-llvm-identity"),
            (["--no-build", "library/std"], "--no-build", "library/std"),
            (["--check", "--no-build", "--", "library/std"], "--no-build", "library/std"),
        ):
            with self.subTest(argv=argv):
                status, events, printed, mocks = self.main_around_llvm(argv, self.llvm_observation())
                self.assertEqual((status, events), (2, []))
                self.assertIn(
                    f"\n{mode} runs no x.py build, and these words after its options would reach "
                    f"nothing: {words}\n" + refused,
                    printed,
                )
                for name in ("verify_stage_tool_provenance", "capture_llvm_before_build", "run_xpy_build"):
                    mocks[name].assert_not_called()
        # The same verification without a stray word answers as it did, with
        # the requirement it names; a `--` with nothing after it is no word.
        for argv in (
            ["--verify-stage-provenance", "--require-llvm-identity", "--stage", "2"],
            ["--verify-stage-provenance", "--require-llvm-identity", "--"],
        ):
            with self.subTest(argv=argv):
                status, events, printed, mocks = self.main_around_llvm(argv, self.llvm_observation())
                self.assertEqual((status, events), (0, ["verify_stage_tool_provenance"]), printed)
                self.assertEqual(
                    mocks["verify_stage_tool_provenance"].call_args,
                    call(
                        checkout,
                        self.host,
                        2,
                        require_immutable_lineage=False,
                        require_public_release=False,
                        require_llvm_identity=True,
                    ),
                )
        # A stage-1 build still forwards what follows its options to x.py, and
        # a Stage2+ build still refuses it (BootstrapBuildLaunchTests).
        status, events, printed, mocks = self.main_around_llvm(
            ["--stage", "1", "--no-register", "--", "library/std"], self.llvm_observation()
        )
        self.assertEqual(status, 0, printed)
        self.assertEqual(mocks["run_xpy_build"].call_args.args[4], ["library/std"])
        # Its --check answers for that build, which forwards them: no refusal.
        status, events, printed, mocks = self.main_around_llvm(
            ["--check", "--stage", "1", "--no-register", "--", "library/std"], self.llvm_observation()
        )
        self.assertEqual(status, 0, printed)
        self.assertIn("\n--check: prerequisites OK (stage0 mode: ", printed)
        mocks["run_xpy_build"].assert_not_called()
        status, events, printed, mocks = self.main_around_llvm(
            [*self.SEAL_INVOCATION, "stage2", "--require-llvm-identity"], self.llvm_observation()
        )
        self.assertEqual((status, events), (2, []))
        self.assertIn(
            "\nStage2+ provenance builds refuse forwarded x.py arguments: stage2 --require-llvm-identity\n",
            printed,
        )

    def test_verification_refuses_an_option_it_does_not_read(self):
        # The verifier reads the stage and host it verifies, the requirements
        # it asks, and --check, whose report it replaces. Until 2026-10-14 it ran
        # with whatever else was typed and read none of it, so
        # `--verify-stage-provenance --require-seed` (or `--llvm-config X`,
        # `--no-build`) answered "verified" with the same arguments to the
        # verifier as without them (measured by the review of the follow-up of
        # 2026-10-13). Each is now refused, exit 2, before anything is verified.
        from unittest.mock import call

        takes = (
            "An option it does not use is refused, never ignored. It takes --stage, --host, "
            "--require-immutable-lineage, --require-public-release, --require-llvm-identity and "
            "--check (whose report it replaces).\n"
        )
        rows = (
            (["--require-seed"], "--require-seed"),
            (["--llvm-config", "/opt/llvm/bin/llvm-config"], "--llvm-config"),
            (["--no-build"], "--no-build"),
            (["-j", "8"], "--jobs"),
            (["--register-non-stage2"], "--register-non-stage2"),
            (["--no-register"], "--no-register"),
            (["--no-atpkg"], "--no-atpkg"),
            (["--force"], "--force"),
            (["--genesis"], "--genesis"),
            (["--no-fetch"], "--no-fetch"),
            (["--force-config"], "--force-config"),
            # Every one is named, in the parser's order, whatever order it was typed in.
            (["--no-fetch", "--require-seed"], "--require-seed --no-fetch"),
        )
        for typed, named in rows:
            argv = ["--verify-stage-provenance", "--stage", "2", *typed]
            with self.subTest(argv=argv):
                status, events, printed, mocks = self.main_around_llvm(argv, self.llvm_observation())
                self.assertEqual((status, events), (2, []), printed)
                self.assertIn(
                    "\n--verify-stage-provenance reads a stage receipt and builds nothing, and does not "
                    f"use: {named}\n" + takes,
                    printed,
                )
                for name in ("verify_stage_tool_provenance", "capture_llvm_before_build", "run_xpy_build"):
                    mocks[name].assert_not_called()
        # A row above for every option of the parser but what the verifier reads
        # (and --fresh-seed, refused there by its own conflict and pinned in
        # test_fresh_seed_conflicts_fail_before_resolution, the three --clean-lean-*
        # options, refused by the Clean Lean block, and the three tool-preparation
        # options, refused by their own conflicts; both pinned below): an
        # option added later needs a row, and is refused until it is given one.
        reads = {
            "verify_stage_provenance",
            "check",
            "stage",
            "host",
            "require_immutable_lineage",
            "require_public_release",
            "require_llvm_identity",
            "extra",
            "fresh_seed",
            # Refused by the Clean Lean block before the verifier runs: each alone as an
            # incomplete selection, all three together through its stage-2 conflict.
            "clean_lean_manifest",
            "clean_lean_lib",
            "clean_lean_manifest_sha256",
        }
        lean = (["--clean-lean-manifest", "/m.json"], ["--clean-lean-lib", "/lib/lean"],
                ["--clean-lean-manifest-sha256", "0" * 64])
        for typed in (*lean, [word for option in lean for word in option]):
            argv = ["--verify-stage-provenance", "--stage", "2", *typed]
            with self.subTest(argv=argv):
                status, events, printed, mocks = self.main_around_llvm(argv, self.llvm_observation())
                self.assertEqual((status, events), (2, []), printed)
                self.assertIn("Clean Lean input selection refused", printed)
                for name in ("verify_stage_tool_provenance", "capture_llvm_before_build", "run_xpy_build"):
                    mocks[name].assert_not_called()
        # Refused by their own conflicts before the verifier runs, each in its own words:
        # --prepare-tool and source cache hints grant no provenance grade, and
        # --tool-source-inspector needs a --prepare-tool.
        own = {
            "prepare_tool": (["--prepare-tool", "targo-build-tool"],
                             "\n--prepare-tool requires stage0/1 --no-build with an explicit source inspector"),
            "source_object_cache": (["--source-object-cache", "first-party/clean=/r"],
                                    "\n--source-object-cache requires full indexed source materialization."),
            "source_working_cache": (["--source-working-cache", "first-party/clean=/r"],
                                     "\n--source-working-cache requires full indexed source materialization."),
            "tool_source_inspector": (["--tool-source-inspector", "/t/targo"],
                                      "\n--tool-source-inspector requires an explicit --prepare-tool."),
        }
        both = (["--prepare-tool", "targo-build-tool", "--tool-source-inspector", "/t/targo"],
                own["prepare_tool"][1])
        for typed, refusal in (*own.values(), both):
            argv = ["--verify-stage-provenance", "--stage", "2", *typed]
            with self.subTest(argv=argv):
                status, events, printed, mocks = self.main_around_llvm(argv, self.llvm_observation())
                self.assertEqual((status, events), (2, []), printed)
                self.assertIn(refusal, printed)
                self.assertNotIn("verified", printed)
                for name in ("verify_stage_tool_provenance", "capture_llvm_before_build", "run_xpy_build"):
                    mocks[name].assert_not_called()
        self.assertEqual(
            {named for _typed, named in rows if " " not in named},
            {"--" + dest.replace("_", "-") for dest in vars(recreate_bootstrap.parse_args([]))
             if dest not in reads and dest not in own},
        )
        # What it reads, as every caller in the tree spells it (run_tests_after_build.sh,
        # compat_check.py, the two collect_* scripts, INSTALL.md), verifies as it did,
        # with each requirement handed on; so does it after --check.
        for argv, requirements in (
            (
                ["--verify-stage-provenance", "--require-immutable-lineage", "--stage", "2", "--host", self.host],
                (True, False, False),
            ),
            (
                [
                    "--check",
                    "--verify-stage-provenance",
                    "--require-public-release",
                    "--require-llvm-identity",
                    "--stage",
                    "2",
                ],
                (False, True, True),
            ),
        ):
            with self.subTest(argv=argv):
                status, events, printed, mocks = self.main_around_llvm(argv, self.llvm_observation())
                self.assertEqual((status, events), (0, ["verify_stage_tool_provenance"]), printed)
                self.assertEqual(
                    mocks["verify_stage_tool_provenance"].call_args,
                    call(
                        Path("/checkout"),
                        self.host,
                        2,
                        require_immutable_lineage=requirements[0],
                        require_public_release=requirements[1],
                        require_llvm_identity=requirements[2],
                    ),
                )
        # The stage is read at any value, not only at its default of 2: every
        # row above types `--stage 2`, which a rule that stopped reading --stage
        # would still let through (the second reading of 2026-10-14, its
        # surviving mutant RX9). A stage 3 is verified as stage 3, and a stage
        # 1 is refused for what it is, not as an option the verifier does not use.
        status, events, printed, mocks = self.main_around_llvm(
            ["--verify-stage-provenance", "--stage", "3"], self.llvm_observation()
        )
        self.assertEqual((status, events), (0, ["verify_stage_tool_provenance"]), printed)
        self.assertEqual(
            mocks["verify_stage_tool_provenance"].call_args,
            call(
                Path("/checkout"),
                self.host,
                3,
                require_immutable_lineage=False,
                require_public_release=False,
                require_llvm_identity=False,
            ),
        )
        status, events, printed, mocks = self.main_around_llvm(
            ["--verify-stage-provenance", "--stage", "1"], self.llvm_observation()
        )
        self.assertEqual((status, events), (2, []), printed)
        self.assertIn("\n--verify-stage-provenance requires --stage 2 or newer.\n", printed)
        self.assertNotIn("does not use", printed)
        mocks["verify_stage_tool_provenance"].assert_not_called()

    def test_a_value_option_given_twice_is_refused(self):
        # argparse keeps the last value of a repeated option: until 2026-10-14
        # `--verify-stage-provenance --stage 2 --stage 3` verified stage 3 without
        # a word about the 2 (measured by the review of the follow-up of
        # 2026-10-13). One value is used, so a second is refused, exit 2, as an
        # unknown option is; the same value twice too, and through either spelling.
        for argv, message in (
            (["--verify-stage-provenance", "--stage", "2", "--stage", "3"], "--stage given twice (2, then 3)"),
            (["--stage=2", "--stage", "2"], "--stage given twice (2, then 2)"),
            (["--check", "--host", "a", "--host", "b"], "--host given twice (a, then b)"),
            (["--stage", "1", "-j", "4", "--jobs", "8"], "--jobs given twice (4, then 8)"),
            (["--llvm-config", "/a/llvm-config", "--llvm-config", "/b/llvm-config"],
             "--llvm-config given twice (/a/llvm-config, then /b/llvm-config)"),
        ):
            with self.subTest(argv=argv):
                stderr = io.StringIO()
                with patch("sys.stderr", stderr), self.assertRaises(SystemExit) as raised:
                    recreate_bootstrap.parse_args(argv)
                self.assertEqual(raised.exception.code, 2)
                self.assertIn(
                    f"recreate-bootstrap: error: {message}: one value is used, so a second is "
                    "refused, never ignored\n",
                    stderr.getvalue(),
                )
        # Through main, before anything is verified.
        with patch.object(recreate_bootstrap, "ensure_python_311"), patch.object(
            recreate_bootstrap, "line_buffer_output"
        ), patch.object(recreate_bootstrap, "verify_stage_tool_provenance") as verify, patch(
            "sys.stderr", io.StringIO()
        ), self.assertRaises(SystemExit) as raised:
            recreate_bootstrap.main(["--verify-stage-provenance", "--stage", "2", "--stage", "3"])
        self.assertEqual(raised.exception.code, 2)
        verify.assert_not_called()
        # Once, each is what it was.
        args = recreate_bootstrap.parse_args(
            ["--stage", "1", "--host", "h", "-j", "4", "--llvm-config", "/a/llvm-config"]
        )
        self.assertEqual(
            (args.stage, args.host, args.jobs, args.llvm_config), (1, "h", 4, "/a/llvm-config")
        )

    def test_an_empty_host_or_llvm_config_is_refused(self):
        # Until 2026-10-14 an empty value read as the default: `--host ""` (or
        # `--host=`) meant the detected host in every mode, the verifier
        # included (measured by the second reading of the follow-up's close),
        # and `--llvm-config ""` meant the in-tree LLVM to the config writer
        # and the prerequisite check while the Stage2 capture and the LLVM-mode
        # code tested for no value at all. An empty word names nothing: it is
        # refused, exit 2, as an unknown option is, in every mode and through
        # either spelling.
        refusal = (
            "is empty: an empty value names nothing, so it is refused, never read as the "
            "default (leave the option out for the default)\n"
        )
        for argv, option in (
            (["--host", ""], "--host"),
            (["--host="], "--host"),
            (["--verify-stage-provenance", "--stage", "2", "--host", ""], "--host"),
            (["--check", "--host="], "--host"),
            (["--llvm-config", ""], "--llvm-config"),
            (["--llvm-config="], "--llvm-config"),
            (["--check", "--stage", "1", "--llvm-config", ""], "--llvm-config"),
            # An empty second value is refused for what it is.
            (["--host", "h", "--host", ""], "--host"),
        ):
            with self.subTest(argv=argv):
                stderr = io.StringIO()
                with patch("sys.stderr", stderr), self.assertRaises(SystemExit) as raised:
                    recreate_bootstrap.parse_args(argv)
                self.assertEqual(raised.exception.code, 2)
                self.assertIn(f"recreate-bootstrap: error: {option} {refusal}", stderr.getvalue())
        # Through main, before anything is verified or selected.
        for argv in (
            ["--verify-stage-provenance", "--stage", "2", "--host", ""],
            ["--stage", "2", "--require-seed", "--fresh-seed", "--llvm-config", ""],
        ):
            with self.subTest(argv=argv), patch.object(
                recreate_bootstrap, "ensure_python_311"
            ), patch.object(recreate_bootstrap, "line_buffer_output"), patch.object(
                recreate_bootstrap, "verify_stage_tool_provenance"
            ) as verify, patch.object(
                recreate_bootstrap, "resolve_stage0_selection"
            ) as select, patch(
                "sys.stderr", io.StringIO()
            ), self.assertRaises(SystemExit) as raised:
                recreate_bootstrap.main(argv)
            self.assertEqual(raised.exception.code, 2)
            verify.assert_not_called()
            select.assert_not_called()
        # Left out, each is its default; given, each is what was typed.
        args = recreate_bootstrap.parse_args([])
        self.assertEqual((args.host, args.llvm_config), (None, None))
        args = recreate_bootstrap.parse_args(["--host=h", "--llvm-config=/a/llvm-config"])
        self.assertEqual((args.host, args.llvm_config), ("h", "/a/llvm-config"))

    def test_require_llvm_identity_refuses_before_x_py_and_no_other_flag_does(self):
        everyday = self.EVERYDAY_INVOCATION
        seal = self.SEAL_INVOCATION
        where = f"build/{self.host}/llvm"
        no_record = (
            f"{where} is there and x.py will use it, and it holds no build record "
            "(.trust-llvm-build-record.json): it was built before the recreator wrote one, by a "
            "plain x.py build, or over a directory that was already there"
        )
        from unittest.mock import call

        checkout = Path("/checkout")
        the_build = [
            "capture_build_authority",
            "capture_llvm_before_build",
            "run_xpy_build",
            "install_ay_solver",
            "audit_stage_tool_provenance",
        ]

        # The build directories of the three seals of 2026-10-12, as they
        # stand, and every build directory there was before this record: an
        # LLVM, x.py's stamp, and nothing that says what it was built from.
        old_directory = self.llvm_observation(present=True)

        # THE DOCUMENTED BUILD COMMAND goes through it as it always did: x.py
        # is started with the arguments it was started with, the one
        # verification is the fresh-seed one with the one requirement it had,
        # and the toolchain is registered. What is new is what it prints and
        # what the audit is handed.
        status, events, printed, mocks = self.main_around_llvm(everyday, old_directory)
        self.assertEqual(status, 0, printed)
        self.assertEqual(
            events,
            [
                "quarantine_seed_stage0",
                *the_build,
                "verify_stage_tool_provenance",
                "discard_seed_stage0_quarantine",
                "maybe_register_rustup_toolchain",
            ],
        )
        self.assertEqual(
            mocks["run_xpy_build"].call_args,
            call(checkout, self.host, 2, None, [], seed_mode=True, seed_compiler=None),
        )
        self.assertEqual(
            mocks["verify_stage_tool_provenance"].call_args_list,
            [call(checkout, self.host, 2, require_immutable_lineage=True)],
        )
        self.assertIs(mocks["audit_stage_tool_provenance"].call_args.kwargs["llvm_before"], old_directory)
        self.assertIn(
            "\nObserving the LLVM this build will carry:\n"
            "  mode: in-tree\n"
            f"  source identity: {self.llvm_source()['identity_sha256']} (src/llvm-project tree "
            f"{'3' * 40})\n"
            f"  {where}: present\n"
            f"  its identity cannot be stated: {no_record}\n",
            printed,
        )
        self.assertNotIn("Refusing to build", printed)

        # So does every other build that does not ask: none is refused for
        # its LLVM, whatever the directory holds.
        other_sources = self.llvm_source(llvm_tree="9" * 40)
        dirty = self.llvm_observation()
        dirty["source"] = self.llvm_source(clean=False)
        downloaded = {
            **self.llvm_observation(),
            "mode": "unknown",
            "mode_reasons": ["bootstrap.toml does not set llvm.download-ci-llvm = false"],
            "output": None,
        }
        unstamped = self.llvm_observation(present=True, record=self.llvm_build_record())
        unstamped["output"]["stamp_present"] = False
        linked = self.llvm_observation()
        linked["output"]["errors"] = [f"{where} is not a real directory"]
        uncovered = self.llvm_observation()
        uncovered["output"]["uncovered"] = ["build/other-target/native/crt"]
        cannot = {
            "an LLVM with no record": old_directory,
            "a record for other LLVM sources": self.llvm_observation(
                present=True,
                record=self.llvm_build_record(
                    source_identity_sha256=other_sources["identity_sha256"],
                    source_paths=other_sources["paths"],
                ),
            ),
            "LLVM sources that are not HEAD's": dirty,
            "a config that may link a downloaded LLVM": downloaded,
            "an LLVM directory without x.py's stamp": unstamped,
            "a link where the LLVM directory would be": linked,
            "an output this record does not cover": uncovered,
        }
        for label, observed in cannot.items():
            for argv in (
                everyday,
                [*everyday, "--no-register"],
                ["--stage", "2", "--require-seed", "--no-register"],
                ["--stage", "2"],
            ):
                with self.subTest(label, argv=argv):
                    status, events, printed, mocks = self.main_around_llvm(argv, observed)
                    self.assertEqual(status, 0, printed)
                    self.assertEqual(
                        [event for event in events if event in the_build], the_build
                    )
                    self.assertIs(
                        mocks["audit_stage_tool_provenance"].call_args.kwargs["llvm_before"], observed
                    )
                    self.assertIn("  its identity cannot be stated: ", printed)
                    self.assertNotIn("Refusing to build", printed)
                    self.assertNotIn("recover_seed_stage0_quarantine", events)
                    for verified in mocks["verify_stage_tool_provenance"].call_args_list:
                        self.assertNotIn("require_llvm_identity", verified.kwargs)

        # WITH THE FLAG the same directory stops the build before x.py, with
        # the stage0 it had set aside put back, and the refusal says what to
        # remove and what to run.
        status, events, printed, mocks = self.main_around_llvm(seal, old_directory)
        self.assertEqual(status, 1)
        self.assertEqual(
            events,
            [
                "quarantine_seed_stage0",
                "capture_build_authority",
                "capture_llvm_before_build",
                "recover_seed_stage0_quarantine",
            ],
        )
        self.assertIn(
            "\nRefusing to build: --require-llvm-identity asks that this build state the identity of\n"
            "the LLVM it carries, and it is known now that it could not:\n"
            f"  - {no_record}\n",
            printed,
        )
        # Why x.py's own rebuild is not enough, as x.py is since 2026-10-13.
        self.assertIn(
            "\nx.py rebuilds the in-tree LLVM when HEAD:src/llvm-project moves from the tree recorded\n"
            "beside it, but it keeps an LLVM that cannot say what it was built from (one built before\n"
            "that record, whose own build header names no commit this checkout has), and a change\n"
            "to src/bootstrap, src/version, the bootstrap config or the native tools rebuilds none.\n"
            "So the recreator states an in-tree LLVM's identity only for one it watched being built\n"
            "from nothing, or one whose directory carries the record of such a build for the same\n"
            "LLVM sources, bootstrap config and native tools.\n",
            printed,
        )
        self.assertNotIn("does not rebuild the in-tree LLVM for a committed change", printed)
        self.assertIn(
            "this build directory reuse the LLVM on it):\n"
            f"    rm -rf /checkout/{where}\n"
            "(A fresh checkout or build directory does the same and leaves this one as it is.)\n"
            "Then run the same command again:\n"
            "    python3 scripts/recreate_bootstrap.py --stage 2 --require-seed --fresh-seed "
            "--no-register --require-llvm-identity\n"
            "Without --require-llvm-identity the build goes ahead on the LLVM that is there, and its\n"
            "receipt says that the identity is not stated, and why.\n",
            printed,
        )

        # EVERY refusal carries its command, or says that no single command
        # applies; and none offers to remove a directory that is not the
        # obstacle.
        remedies = {
            "an LLVM with no record": (f"    rm -rf /checkout/{where}\n", True),
            "a record for other LLVM sources": (f"    rm -rf /checkout/{where}\n", True),
            "LLVM sources that are not HEAD's": (
                "No single command applies to the LLVM sources: HEAD's object ids are the identity of\n"
                "what is compiled only when nothing under them differs from HEAD. Commit, or remove,\n"
                "what this lists:\n"
                "    git status --short --untracked-files=all -- src/bootstrap src/llvm-project src/version\n",
                False,
            ),
            "a config that may link a downloaded LLVM": (
                "No single command applies to the bootstrap config: /checkout/bootstrap.toml is what "
                "x.py obeys,\n",
                False,
            ),
            "an LLVM directory without x.py's stamp": (f"    rm -rf /checkout/{where}\n", True),
            "a link where the LLVM directory would be": (
                f"No single command applies to what is at build/{self.host}/llvm (or "
                f"build/{self.host}/lld): the\n",
                False,
            ),
            "an output this record does not cover": (
                "    rm -rf /checkout/build/other-target/native/crt\n"
                "For a config that does build them no single command applies: such a build cannot\n",
                True,
            ),
        }
        self.assertEqual(set(remedies), set(cannot))
        for label, observed in cannot.items():
            with self.subTest(label, flag=True):
                status, events, printed, mocks = self.main_around_llvm(seal, observed)
                self.assertEqual(status, 1)
                self.assertNotIn("run_xpy_build", events)
                self.assertEqual(events[-1], "recover_seed_stage0_quarantine")
                mocks["audit_stage_tool_provenance"].assert_not_called()
                refusal = printed[printed.index("\nRefusing to build: ") :]
                remedy, removes = remedies[label]
                self.assertIn(remedy, refusal)
                self.assertEqual("rm -rf" in refusal, removes, refusal)
                self.assertIn(
                    "Then run the same command again:\n    python3 scripts/recreate_bootstrap.py ",
                    refusal,
                )
        # The line above the obstacle does not call a link "absent".
        status, events, printed, mocks = self.main_around_llvm(seal, linked)
        self.assertIn(
            f"  {where}: not observed (the reason is below); x.py uses what is there\n"
            f"  its identity cannot be stated: {where} is not a real directory\n",
            printed,
        )
        self.assertNotIn("absent", printed)
        status, events, printed, mocks = self.main_around_llvm(seal, unstamped)
        self.assertIn(
            f"  - {where} is there without the stamp x.py leaves when a build completes, so x.py "
            "will run LLVM's build over it: over objects this run did not watch being compiled\n",
            printed,
        )

        # No LLVM in the build directory: x.py builds it in this run, and the
        # flag adds the one verification that asks for the identity.
        status, events, printed, mocks = self.main_around_llvm(seal, self.llvm_observation())
        self.assertEqual(status, 0, printed)
        self.assertEqual(
            events,
            [
                "quarantine_seed_stage0",
                *the_build,
                "verify_stage_tool_provenance",
                "verify_stage_tool_provenance",
                "discard_seed_stage0_quarantine",
            ],
        )
        self.assertEqual(
            mocks["verify_stage_tool_provenance"].call_args_list,
            [
                call(checkout, self.host, 2, require_immutable_lineage=True),
                call(checkout, self.host, 2, require_llvm_identity=True),
            ],
        )
        self.assertIn(f"  {where}: absent, so x.py builds LLVM in this run\n", printed)
        self.assertNotIn("cannot be stated", printed)

        # An LLVM that is there with the record of its build, for these
        # sources, this config and these native tools: the seal reuses it.
        evidenced = self.llvm_observation(present=True, record=self.llvm_build_record())
        status, events, printed, mocks = self.main_around_llvm(seal, evidenced)
        self.assertEqual(status, 0, printed)
        self.assertIn("run_xpy_build", events)
        self.assertIs(mocks["audit_stage_tool_provenance"].call_args.kwargs["llvm_before"], evidenced)
        self.assertIn(
            f"  {where}: present, with a build record that is evidence for this run (built at "
            f"commit {self.commit})\n",
            printed,
        )

        # And each thing that makes that record evidence of something else.
        for label, record, reason in (
            (
                "a committed LLVM change since",
                self.llvm_build_record(
                    source_identity_sha256=other_sources["identity_sha256"],
                    source_paths=other_sources["paths"],
                ),
                f"its build record is for LLVM source identity {other_sources['identity_sha256'][:12]} "
                f"(built at commit {self.commit[:12]}), and this tree's is "
                f"{self.llvm_source()['identity_sha256'][:12]}",
            ),
            (
                "another bootstrap config",
                self.llvm_build_record(bootstrap_config_sha256="d" * 64),
                "its build record is for another bootstrap config (dddddddddddd; this run's is "
                "bbbbbbbbbbbb)",
            ),
            (
                "other native tools",
                self.llvm_build_record(native_authority_sha256="8" * 64),
                "its build record is for another native tool and SDK authority (888888888888; "
                "this run's is cccccccccccc)",
            ),
            (
                "another host",
                self.llvm_build_record(host="other-host"),
                "its build record is for another host (other-host; this run's is test-host)",
            ),
            (
                "installed files that changed",
                self.llvm_build_record(output_fingerprint_sha256="0" * 64),
                "its installed files are not the ones its build record fingerprints: they changed "
                "after that build",
            ),
        ):
            with self.subTest(label):
                observed = self.llvm_observation(present=True, record=record)
                status, events, printed, _mocks = self.main_around_llvm(seal, observed)
                self.assertEqual(status, 1)
                self.assertNotIn("run_xpy_build", events)
                self.assertEqual(events[-1], "recover_seed_stage0_quarantine")
                self.assertIn(f"  - {where} is there and x.py will use it, and {reason}\n", printed)
                # ... and, without the flag, a line of the record and no more.
                status, events, printed, _mocks = self.main_around_llvm(everyday, observed)
                self.assertEqual(status, 0, printed)
                self.assertIn("run_xpy_build", events)
                self.assertIn(
                    f"  its identity cannot be stated: {where} is there and x.py will use it, "
                    f"and {reason}\n",
                    printed,
                )

        # A FINISHED BUILD whose receipt does not state the identity fails
        # under the flag (the verifier is what reads the receipt), with the
        # stage0 put back; the fresh-seed verification before it is unchanged.
        status, events, printed, mocks = self.main_around_llvm(
            seal,
            self.llvm_observation(),
            verify_stage_tool_provenance=lambda *_args, **kwargs: "require_llvm_identity" not in kwargs,
        )
        self.assertEqual(status, 1)
        self.assertEqual(
            events[-3:],
            [
                "verify_stage_tool_provenance",
                "verify_stage_tool_provenance",
                "recover_seed_stage0_quarantine",
            ],
        )
        self.assertIn(
            "\nBuild completed, but its receipt does not state the identity of the LLVM the stage "
            "carries (--require-llvm-identity). The reason is above and in the receipt's "
            "llvm_identity.reasons.\n"
            "No single command applies here: something changed while x.py ran, or x.py built over an "
            "LLVM that was there. Run the same command again; it then refuses before x.py starts and "
            "names what stands in the way, with the command that removes it:\n"
            "    python3 scripts/recreate_bootstrap.py --stage 2 --require-seed --fresh-seed "
            "--no-register --require-llvm-identity\n",
            printed,
        )
        self.assertNotIn("maybe_register_rustup_toolchain", events)
        # Without --fresh-seed the flag is the only verification.
        status, events, printed, mocks = self.main_around_llvm(
            ["--stage", "2", "--no-register", "--require-llvm-identity"], self.llvm_observation()
        )
        self.assertEqual(status, 0, printed)
        self.assertEqual(
            mocks["verify_stage_tool_provenance"].call_args_list,
            [call(checkout, self.host, 2, require_llvm_identity=True)],
        )

        # The flag is for a Stage2+ build (or the verifier): asked of anything
        # that writes no receipt, it is refused rather than ignored.
        for argv in (
            ["--stage", "1", "--require-llvm-identity"],
            ["--check", "--require-llvm-identity"],
            ["--no-build", "--require-llvm-identity"],
        ):
            with self.subTest(argv=argv):
                status, events, printed, _mocks = self.main_around_llvm(argv, old_directory)
                self.assertEqual((status, events), (2, []))
                self.assertIn(
                    "\n--require-llvm-identity requires a Stage2+ build or --verify-stage-provenance; "
                    "it cannot be combined with --check, --no-build, or --stage 0/1.\n",
                    printed,
                )
        # With the verifier it is that verification's requirement.
        status, events, printed, mocks = self.main_around_llvm(
            ["--verify-stage-provenance", "--require-llvm-identity"], old_directory
        )
        self.assertEqual((status, events), (0, ["verify_stage_tool_provenance"]))
        self.assertEqual(
            mocks["verify_stage_tool_provenance"].call_args,
            call(
                checkout,
                self.host,
                2,
                require_immutable_lineage=False,
                require_public_release=False,
                require_llvm_identity=True,
            ),
        )

        # A BUILD THAT FAILS after x.py started is where an LLVM built from
        # nothing would be left without its record: both failing exits hand
        # what was observed to the step that leaves it, and their exit status
        # is the build's own.
        for label, results, expected in (
            ("x.py fails", {"run_xpy_build": 3}, 3),
            ("the ay install fails", {"install_ay_solver": False}, 1),
        ):
            with self.subTest(label):
                observed = self.llvm_observation()
                status, events, printed, mocks = self.main_around_llvm(seal, observed, **results)
                self.assertEqual(status, expected)
                self.assertEqual(
                    events[-2:],
                    ["leave_llvm_build_record_after_failed_build", "recover_seed_stage0_quarantine"],
                )
                self.assertEqual(
                    mocks["leave_llvm_build_record_after_failed_build"].call_args,
                    call(
                        checkout,
                        self.host,
                        observed,
                        commit_before=self.commit,
                        config_path=Path("/checkout/bootstrap.toml"),
                        config_sha256="b" * 64,
                        build_authority_before={
                            "status": "ready",
                            "authority_sha256": "c" * 64,
                            "errors": [],
                        },
                        llvm_config=None,
                    ),
                )
                mocks["audit_stage_tool_provenance"].assert_not_called()
        status, events, printed, mocks = self.main_around_llvm(seal, self.llvm_observation())
        mocks["leave_llvm_build_record_after_failed_build"].assert_not_called()

    def llvm_checkout(self, root: Path) -> str:
        """Make the fixture tree `root` a git checkout whose HEAD holds the LLVM paths; its commit."""
        git = lambda *args: self.llvm_git(root, *args)  # noqa: E731
        git("init")
        git("config", "user.email", "trust-test@example.invalid")
        git("config", "user.name", "Trust Test")
        for path, text in (
            (root / "src" / "llvm-project" / "llvm" / "lib" / "Analysis.cpp", "int scev() { return 1; }\n"),
            (root / "src" / "bootstrap" / "llvm.rs", "// the cmake line\n"),
            (root / "src" / "version", "0.10.0\n"),
        ):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        git("add", "src")
        git("commit", "-m", "fixture")
        return git("rev-parse", "HEAD").strip()

    def llvm_directory_state(self, root: Path, out: Path | None = None) -> dict:
        """Every file and link under build/<host>/llvm (or `out`): bytes or target, and modification time."""
        state = {}
        out = self.llvm_out(root) if out is None else out
        for current, directories, files in os.walk(out):
            for name in (*directories, *files):
                path = Path(current) / name
                metadata = path.lstat()
                content = (
                    os.readlink(path)
                    if path.is_symlink()
                    else path.read_bytes() if path.is_file() else None
                )
                state[str(path.relative_to(out))] = (content, metadata.st_mtime_ns)
        return state

    def main_over_a_build_directory(
        self, root, stage_root, argv, *, x_py=None, x_py_exit=0, authority=None
    ):
        """main(argv) in the fixture checkout `root`, its LLVM steps REAL.

        Real: the observation of the LLVM before x.py (the config it reads, the
        directory it fingerprints, git), the audit that writes the receipt and
        the verification main() ends with. Replaced: what needs a machine
        (prerequisites, the seed, submodules, the config writer, the stage0
        quarantine, x.py, the ay install, rustup) and the four captures the
        audit's own fixture replaces. `x_py` stands for what x.py does to the
        build directory; `authority` is the native-authority capture's answer
        when it is not the fixture's (a build given `--llvm-config`). Returns
        (exit status, the replaced steps in order, what was printed, the mocks
        by name).
        """
        config = root / "bootstrap.toml"
        if not config.exists():
            # A config as the recreator writes one for a seed build, as far as
            # main() reads it: the stage0 mode it declares, and its LLVM.
            config.write_text(
                "# Trust bootstrap config (seed stage0 mode)\n[llvm]\ndownload-ci-llvm = false\n"
            )
        digest = hashlib.sha256(config.read_bytes()).hexdigest()
        events: list[str] = []
        captured: list[int] = []

        def step(name, result):
            return lambda *_args, **_kwargs: events.append(name) or result

        def bootstrap(*_args, **_kwargs):
            # Before x.py the seed is not extracted; x.py extracts it.
            captured.append(1)
            return self.bootstrap_lineage(digest=digest, hydrated=len(captured) > 1)

        def x_py_build(*_args, **_kwargs):
            events.append("run_xpy_build")
            if x_py is not None:
                x_py()
            return x_py_exit

        output = io.StringIO()
        with ExitStack() as stack:
            for name in (
                "ensure_python_311",
                "line_buffer_output",
                "print_prereqs",
                "ensure_submodules",
                "scrub_pat_from_remotes",
            ):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            for name, result in (
                ("atpkg_trust_sysroot", None),
                ("repo_root", root),
                ("host_triple", self.host),
                ("resolve_seed", True),
                ("check_prereqs", []),
                ("write_config", recreate_bootstrap.WrittenBootstrapConfig(config, digest)),
                ("capture_source_lineage", self.lineage()),
                (
                    "capture_build_authority",
                    self.build_authority() if authority is None else authority,
                ),
            ):
                stack.enter_context(patch.object(recreate_bootstrap, name, return_value=result))
            stack.enter_context(
                patch.object(recreate_bootstrap, "capture_bootstrap_lineage", side_effect=bootstrap)
            )
            stack.enter_context(
                patch.object(
                    recreate_bootstrap, "_capture_identity", side_effect=self.identity_capture(stage_root)
                )
            )
            mocks = {
                name: stack.enter_context(
                    patch.object(recreate_bootstrap, name, side_effect=step(name, result))
                )
                for name, result in (
                    ("quarantine_seed_stage0", None),
                    ("install_ay_solver", True),
                    ("discard_seed_stage0_quarantine", None),
                    ("recover_seed_stage0_quarantine", None),
                    ("maybe_register_rustup_toolchain", True),
                )
            }
            mocks["run_xpy_build"] = stack.enter_context(
                patch.object(recreate_bootstrap, "run_xpy_build", side_effect=x_py_build)
            )
            stack.enter_context(patch("sys.stdout", output))
            status = recreate_bootstrap.main(argv)
        return status, events, output.getvalue(), mocks

    def test_the_documented_build_command_is_unchanged_over_an_llvm_with_no_record(self):
        # CONSTRAINT (a), where it is easiest to break. `--require-seed
        # --fresh-seed` is the build command of README.md, INSTALL.md,
        # docs/BUILD_AND_INSTALL.md, docs/BOOTSTRAP_FROM_SCRATCH.md and
        # scripts/dev-bootstrap.sh, and every build directory that exists holds
        # an LLVM with no build record. The first version of this record
        # refused exactly that. Here main() runs with exactly those arguments
        # over a real build directory: it exits as it did, starts x.py as it
        # did, on an LLVM directory nobody touched, and writes the receipt it
        # wrote, with one more key.
        from unittest.mock import call

        reader = load_stage_receipt_reader()
        where = f"build/{self.host}/llvm"
        no_record = (
            "it holds no build record (.trust-llvm-build-record.json): it was built before the "
            "recreator wrote one, by a plain x.py build, or over a directory that was already there"
        )
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(str(Path(directory).resolve()))
            self.commit = self.llvm_checkout(root)
            self.install_llvm(root)
            receipt_path = stage_root / "tool-provenance.json"
            before = self.llvm_directory_state(root)
            self.assertEqual(
                sorted(before),
                [
                    ".llvm-stamp",
                    "bin",
                    "bin/llvm-config",
                    "bin/llvm-ranlib",
                    "build",
                    "build/CMakeCache.txt",
                    "include",
                    "include/llvm",
                    "include/llvm/Config.h",
                    "lib",
                    "lib/libLLVMCore.a",
                ],
            )
            seen_by_x_py: list[dict] = []

            status, events, printed, mocks = self.main_over_a_build_directory(
                root,
                stage_root,
                self.EVERYDAY_INVOCATION,
                x_py=lambda: seen_by_x_py.append(self.llvm_directory_state(root)),
            )
            self.assertEqual(status, 0, printed)
            # x.py was reached, with the arguments it has always been given,
            # and found the LLVM as it was: its stamp and every file, byte for
            # byte, none rewritten. So x.py reuses that LLVM, as before.
            self.assertEqual(
                events,
                [
                    "quarantine_seed_stage0",
                    "run_xpy_build",
                    "install_ay_solver",
                    "discard_seed_stage0_quarantine",
                    "maybe_register_rustup_toolchain",
                ],
            )
            self.assertEqual(
                mocks["run_xpy_build"].call_args,
                call(root, self.host, 2, None, [], seed_mode=True, seed_compiler=None),
            )
            self.assertEqual(seen_by_x_py, [before])
            # ... and so it is after the audit and the verification: nothing
            # was added either (no build record: this run did not build it).
            self.assertEqual(self.llvm_directory_state(root), before)
            self.assertNotIn("Refusing to build", printed)
            self.assertIn(
                "\nObserving the LLVM this build will carry:\n  mode: in-tree\n  source identity: ",
                printed,
            )
            self.assertIn(
                f"  {where}: present\n"
                f"  its identity cannot be stated: {where} is there and x.py will use it, and {no_record}\n",
                printed,
            )

            # THE RECEIPT: the status word this build has always earned, and the
            # fresh-seed verification main() ends with passed on it.
            receipt = json.loads(receipt_path.read_text())
            self.assertEqual(receipt["status"], "release-ready")
            self.assertEqual(
                receipt["status"],
                recreate_bootstrap._classify_receipt_status(
                    receipt["source_lineage"]["status"], receipt["bootstrap_lineage"]
                ),
            )
            self.assertEqual(receipt["recreator_invocation"]["argv"], self.EVERYDAY_INVOCATION)
            self.assertEqual(
                printed.count("  verified existing stage provenance (release-ready) -> "), 1
            )
            llvm = receipt["llvm_identity"]
            self.assertEqual(
                (llvm["mode"], llvm["provenance"], llvm["identity_stated"], llvm["build_record"]),
                ("in-tree", "reused", False, None),
            )
            self.assertEqual(llvm["reasons"], [f"{where} was reused, and {no_record}"])
            self.assertEqual(llvm["output_dirs"], [where])
            source = recreate_bootstrap.capture_llvm_source_identity(root)
            self.assertEqual(
                (source["clean"], llvm["source_paths"], llvm["source_identity_sha256"]),
                (True, source["paths"], source["identity_sha256"]),
            )

            # EVERY CONSUMER OF THAT WORD gets the answer it got: the verifier
            # bare and with each requirement it had, and promotion's reader.
            digest = receipt["bootstrap_lineage"]["config_sha256"]
            current = {"bootstrap": self.bootstrap_lineage(digest=digest), "llvm_source": source}
            for requirements in (
                {},
                {"require_immutable_lineage": True},
                {"require_public_release": True},
                {"require_immutable_lineage": True, "require_public_release": True},
            ):
                with self.subTest(requirements=requirements):
                    self.assertTrue(
                        self.verify_receipt(root, stage_root, self.lineage(), **current, **requirements)
                    )
            sealed_lines = reader.lines(stage_root, self.commit)
            self.assertIn("stage_receipt_status=release-ready", sealed_lines)
            self.assertIn("stage_receipt_llvm_identity=not-stated", sealed_lines)
            self.assertIn("stage_receipt_llvm_provenance=reused", sealed_lines)
            self.assertEqual(
                sealed_lines[-1], "stage_receipt_recreator_argv=--stage 2 --require-seed --fresh-seed"
            )
            # Only the requirement that asks for the identity refuses it.
            self.assertFalse(
                self.verify_receipt(
                    root, stage_root, self.lineage(), require_llvm_identity=True, **current
                )
            )
            self.assertEqual(self.llvm_directory_state(root), before)

            # But for that one key it is the receipt the same build got before
            # the record existed.
            del receipt["llvm_identity"]
            self.assertTrue(
                self.run_audit(
                    root,
                    stage_root,
                    invocation=self.EVERYDAY_INVOCATION,
                    bootstrap_before=self.bootstrap_lineage(digest=digest, hydrated=False),
                    bootstrap_after=self.bootstrap_lineage(digest=digest, hydrated=True),
                )
            )
            self.assertEqual(json.loads(receipt_path.read_text()), receipt)

            # THE SAME DIRECTORY, ASKED: with --require-llvm-identity the build
            # is refused before x.py, and still nothing in the directory moved.
            asked = [*self.EVERYDAY_INVOCATION, "--require-llvm-identity"]
            status, events, printed, mocks = self.main_over_a_build_directory(root, stage_root, asked)
            self.assertEqual(status, 1)
            self.assertEqual(events, ["quarantine_seed_stage0", "recover_seed_stage0_quarantine"])
            self.assertEqual(self.llvm_directory_state(root), before)
            self.assertIn(
                f"    rm -rf {root / where}\n"
                "(A fresh checkout or build directory does the same and leaves this one as it is.)\n"
                "Then run the same command again:\n"
                "    python3 scripts/recreate_bootstrap.py --stage 2 --require-seed --fresh-seed "
                "--require-llvm-identity\n",
                printed,
            )

            # The remedy, taken: x.py builds LLVM from nothing, the receipt
            # states it, and the run leaves the record a later run reuses it on.
            shutil.rmtree(root / where)
            status, events, printed, mocks = self.main_over_a_build_directory(
                root, stage_root, asked, x_py=lambda: self.install_llvm(root)
            )
            self.assertEqual(status, 0, printed)
            self.assertIn(f"  {where}: absent, so x.py builds LLVM in this run\n", printed)
            self.assertEqual(
                printed.count("  verified existing stage provenance (release-ready) -> "), 2
            )
            built = json.loads(receipt_path.read_text())["llvm_identity"]
            self.assertEqual(
                (built["provenance"], built["identity_stated"], built["reasons"]),
                ("built-in-this-run", True, []),
            )
            record_path = self.llvm_out(root) / ".trust-llvm-build-record.json"
            self.assertEqual(json.loads(record_path.read_text()), built["build_record"])
            self.assertEqual(built["build_record"]["built_at_commit"], self.commit)
            self.assertEqual(built["build_record"]["bootstrap_config_sha256"], digest)
            status, events, printed, mocks = self.main_over_a_build_directory(root, stage_root, asked)
            self.assertEqual(status, 0, printed)
            self.assertIn("run_xpy_build", events)
            self.assertIn(
                f"  {where}: present, with a build record that is evidence for this run (built at "
                f"commit {self.commit})\n",
                printed,
            )
            reused = json.loads(receipt_path.read_text())["llvm_identity"]
            self.assertEqual(
                (reused["provenance"], reused["identity_stated"], reused["build_record"]),
                ("reused", True, built["build_record"]),
            )

    def test_an_llvm_named_through_llvm_config_is_refused_under_the_flag_and_built_as_before_without_it(self):
        # THE WAY AROUND THE FLAG that the independent re-read of 2026-10-13
        # measured. An LLVM linked through `--llvm-config` was recorded as
        # stated whenever the build authority had bound the llvm-config
        # executable. So the very directory `--require-llvm-identity` refuses
        # (an old build/<host>/llvm with no build record) was accepted when it
        # was named through `--llvm-config`, and so was a copy of some
        # install elsewhere (docs/SEED_STAIRCASE.md freezes one that way): a
        # release-class receipt saying "identity stated", with this checkout's
        # own LLVM source ids beside it. Here main() runs over a real build
        # directory, as in the test above: WITH the flag such a build is
        # refused before x.py; WITHOUT it, it is built exactly as it was before
        # the record existed, and the record says external, not stated.
        from unittest.mock import call

        reader = load_stage_receipt_reader()
        where = f"build/{self.host}/llvm"
        reason = recreate_bootstrap.LLVM_EXTERNAL_REASON

        def the_old_in_tree_llvm(root):
            return self.install_llvm(root, b"llvm built at some other commit")

        def a_copy_elsewhere(root):
            copied = root.parent / "frozen-llvm"
            shutil.move(str(self.install_llvm(root, b"llvm built at some other commit")), str(copied))
            shutil.rmtree(copied / "build")
            return copied

        for label, place in (
            ("the old build/<host>/llvm, named through --llvm-config", the_old_in_tree_llvm),
            ("a copy of an LLVM install elsewhere", a_copy_elsewhere),
        ):
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(
                    str(Path(directory).resolve() / "checkout")
                )
                self.commit = self.llvm_checkout(root)
                llvm_root = place(root)
                llvm_config = str(llvm_root / "bin" / "llvm-config")
                receipt_path = stage_root / "tool-provenance.json"
                config = root / "bootstrap.toml"
                in_tree_config = (
                    "# Trust bootstrap config (seed stage0 mode)\n[llvm]\ndownload-ci-llvm = false\n"
                )

                def state():
                    return (
                        self.llvm_directory_state(root, llvm_root),
                        self.llvm_directory_state(root),
                    )

                before = state()
                self.assertIn("bin/llvm-config", before[0])
                in_the_build_directory = llvm_root == self.llvm_out(root)
                self.assertEqual(before[1] == before[0], in_the_build_directory)
                self.assertEqual(before[1] == {}, not in_the_build_directory)
                if in_the_build_directory:
                    # What the flag says of this directory when x.py is to use
                    # it as the in-tree LLVM: refused, remove it.
                    config.write_text(in_tree_config)
                    status, events, printed, _mocks = self.main_over_a_build_directory(
                        root, stage_root, [*self.EVERYDAY_INVOCATION, "--require-llvm-identity"]
                    )
                    self.assertEqual(status, 1)
                    self.assertIn(f"    rm -rf {root / where}\n", printed)
                # The config the recreator writes for `--llvm-config`, as far as
                # the observation reads it, and what the build authority binds.
                config.write_text(
                    in_tree_config + f'[target.{self.host}]\nllvm-config = "{llvm_config}"\n'
                )
                authority = {
                    **self.build_authority(),
                    "selected_llvm": {
                        "name": "llvm-config",
                        "status": "bound",
                        "resolved_local_path": llvm_config,
                        "resolved_real_path": llvm_config,
                        "sha256": hashlib.sha256(Path(llvm_config).read_bytes()).hexdigest(),
                        "identity": "22.1.0",
                    },
                }
                everyday = [*self.EVERYDAY_INVOCATION, "--llvm-config", llvm_config]
                asked = [*everyday, "--require-llvm-identity"]

                # WITH THE FLAG: refused before x.py, the stage0 put back,
                # nothing written, and no `rm` offered (nothing in this build
                # directory is the obstacle).
                status, events, printed, _mocks = self.main_over_a_build_directory(
                    root, stage_root, asked, authority=authority
                )
                self.assertEqual(status, 1, printed)
                self.assertEqual(events, ["quarantine_seed_stage0", "recover_seed_stage0_quarantine"])
                self.assertFalse(receipt_path.exists())
                self.assertEqual(state(), before)
                self.assertIn(
                    "\nObserving the LLVM this build will carry:\n"
                    "  mode: external\n"
                    f"  its identity cannot be stated: {reason}\n"
                    "\n"
                    "Refusing to build: --require-llvm-identity asks that this build state the identity of\n"
                    "the LLVM it carries, and it is known now that it could not:\n"
                    f"  - {reason}\n"
                    "No single command applies: nothing in this checkout or its build directory is in the\n"
                    "way, and nothing removed from them would help. The claim needs a build WITHOUT\n"
                    "--llvm-config, one that builds the in-tree LLVM (src/llvm-project) or reuses one with\n"
                    "the record of such a build. Run this command again without --llvm-config, and with\n"
                    f"--force-config if {config} names an llvm-config (it OVERWRITES that file).\n"
                    "Without --require-llvm-identity this build goes ahead on the LLVM --llvm-config names,\n"
                    "and its receipt says that the identity is not stated, and why.\n",
                    printed,
                )
                self.assertNotIn("rm -rf", printed)
                self.assertNotIn("the same command", printed)
                # This checkout's LLVM source ids are not printed beside it.
                self.assertNotIn("source identity: ", printed)

                # WITHOUT THE FLAG: the build origin/main runs. The same exit,
                # the same steps, the same x.py call, on files nobody touched.
                seen_by_x_py: list = []
                status, events, printed, mocks = self.main_over_a_build_directory(
                    root,
                    stage_root,
                    everyday,
                    authority=authority,
                    x_py=lambda: seen_by_x_py.append(state()),
                )
                self.assertEqual(status, 0, printed)
                self.assertEqual(
                    events,
                    [
                        "quarantine_seed_stage0",
                        "run_xpy_build",
                        "install_ay_solver",
                        "discard_seed_stage0_quarantine",
                        "maybe_register_rustup_toolchain",
                    ],
                )
                self.assertEqual(
                    mocks["run_xpy_build"].call_args,
                    call(root, self.host, 2, None, [], seed_mode=True, seed_compiler=None),
                )
                self.assertEqual(seen_by_x_py, [before])
                self.assertEqual(state(), before)
                self.assertNotIn("Refusing to build", printed)
                self.assertIn(f"  mode: external\n  its identity cannot be stated: {reason}\n", printed)
                self.assertNotIn("source identity: ", printed)
                self.assertIn(
                    "  llvm: external, linked through --llvm-config, identity NOT stated (no source "
                    f"identity describes it)\n    not stated: {reason}\n",
                    printed,
                )
                # The status word this build has always earned, verified once
                # by the fresh-seed verification main() ends with.
                receipt = json.loads(receipt_path.read_text())
                self.assertEqual(receipt["status"], "release-ready")
                self.assertEqual(
                    receipt["status"],
                    recreate_bootstrap._classify_receipt_status(
                        receipt["source_lineage"]["status"], receipt["bootstrap_lineage"]
                    ),
                )
                self.assertEqual(
                    printed.count("  verified existing stage provenance (release-ready) -> "), 1
                )
                self.assertEqual(receipt["recreator_invocation"]["argv"], everyday)
                self.assertEqual(receipt["build_authority"]["selected_llvm"], authority["selected_llvm"])
                # THE RECORD: external, never stated, and nothing of this
                # checkout or of its build directory beside it: no source id of
                # its src/llvm-project, no fingerprint of the in-tree LLVM that
                # may sit there, no build record.
                self.assertEqual(
                    receipt["llvm_identity"],
                    {
                        "schema": "trust.llvm-identity.v1",
                        "mode": "external",
                        "provenance": "external",
                        "identity_stated": False,
                        "reasons": [reason],
                        "source_identity_sha256": None,
                        "source_paths": [],
                        "output_dirs": [],
                        "output_fingerprint_sha256": None,
                        "build_record": None,
                    },
                )
                self.assertFalse((self.llvm_out(root) / ".trust-llvm-build-record.json").exists())

                # Every consumer of the status word answers as it did; the one
                # requirement that asks for the identity refuses, and so does
                # promotion's.
                digest = receipt["bootstrap_lineage"]["config_sha256"]
                current = {
                    "bootstrap": self.bootstrap_lineage(digest=digest),
                    "build_authority": authority,
                }
                for requirements in (
                    {},
                    {"require_immutable_lineage": True},
                    {"require_public_release": True},
                    {"require_immutable_lineage": True, "require_public_release": True},
                ):
                    with self.subTest(requirements=requirements):
                        self.assertTrue(
                            self.verify_receipt(
                                root, stage_root, self.lineage(), **current, **requirements
                            )
                        )
                output = io.StringIO()
                with patch("sys.stdout", output):
                    self.assertFalse(
                        self.verify_receipt(
                            root, stage_root, self.lineage(), require_llvm_identity=True, **current
                        )
                    )
                self.assertIn(
                    "  ERROR: the identity of the LLVM this stage carries is required "
                    f"(--require-llvm-identity) and this receipt does not state it: {reason}\n",
                    output.getvalue(),
                )
                sealed_lines = reader.lines(stage_root, self.commit)
                self.assertIn("stage_receipt_status=release-ready", sealed_lines)
                self.assertEqual(
                    [line for line in sealed_lines if line.startswith("stage_receipt_llvm")],
                    [
                        "stage_receipt_llvm=external",
                        "stage_receipt_llvm_identity=not-stated",
                        "stage_receipt_llvm_provenance=external",
                        "stage_receipt_llvm_source_sha256=not-recorded",
                        "stage_receipt_llvm_source_tree=not-recorded",
                        "stage_receipt_llvm_built_at_commit=not-recorded",
                        "stage_receipt_llvm_output_sha256=not-recorded",
                    ],
                )
                self.assertEqual(
                    reader.llvm_identity_unstated(stage_root),
                    "its tool-provenance.json says the identity is not stated (mode external, "
                    f"provenance external): {reason}",
                )
                self.assertEqual(state(), before)

                # But for the one key it is the receipt the same build got
                # before the record existed.
                del receipt["llvm_identity"]
                self.assertTrue(
                    self.run_audit(
                        root,
                        stage_root,
                        invocation=everyday,
                        bootstrap_before=self.bootstrap_lineage(digest=digest, hydrated=False),
                        bootstrap_after=self.bootstrap_lineage(digest=digest, hydrated=True),
                        build_authority=authority,
                    )
                )
                self.assertEqual(json.loads(receipt_path.read_text()), receipt)

    def test_no_state_of_the_build_directory_crashes_or_changes_the_documented_build_command(self):
        # The independent re-read of 2026-10-13 put 200000 `[` where the build
        # record of an old LLVM would be, and the documented command died with
        # a RecursionError out of the JSON parser: after the stage0 had been
        # set aside, before x.py, where origin/main builds and exits 0. The
        # record is all that is new by default, so NOTHING the build directory
        # holds may do that. Each state below is put into a real build
        # directory and main() runs with exactly the documented arguments: it
        # exits as it did, starts x.py as it did on files nobody touched, and
        # writes the receipt it wrote, with one more key that says "not
        # stated" and why. With `--require-llvm-identity` the same state is a
        # refusal before x.py, with the stage0 put back.
        from unittest.mock import call

        where = f"build/{self.host}/llvm"
        record_name = ".trust-llvm-build-record.json"
        everyday = self.EVERYDAY_INVOCATION
        asked = [*everyday, "--require-llvm-identity"]
        unusable = f"{where} was reused, and its build record is unusable: "
        unobserved = "the LLVM this build carries could not be observed: "
        deep = b"[" * 200000

        def write_record(data):
            return lambda root: (self.llvm_out(root) / record_name).write_bytes(data)

        def no_patches():
            return []

        def a_larger_bound():
            # So that the parser is what meets the file: nested deeper than its
            # stack on every Python the recreator runs on (measured 2026-10-13:
            # "Stack overflow (used 16352 kB) while decoding a JSON array" on
            # 3.14.6, "maximum recursion depth exceeded" on 3.9.6).
            return [patch.object(recreate_bootstrap, "LLVM_BUILD_RECORD_MAX_BYTES", 1 << 20)]

        def raising(name, error):
            return lambda: [patch.object(recreate_bootstrap, name, side_effect=error)]

        def failing_after_the_build():
            real = recreate_bootstrap.capture_llvm_output
            calls: list[int] = []

            def capture(*args, **kwargs):
                calls.append(1)
                if len(calls) > 1:
                    raise RecursionError("maximum recursion depth exceeded")
                return real(*args, **kwargs)

            return [patch.object(recreate_bootstrap, "capture_llvm_output", side_effect=capture)]

        rm = "    rm -rf "
        unreadable = "No single command applies: the recreator could not read what it needs to observe the\n"
        # (label, what is put there, what is replaced, the receipt's one
        #  reason or how it begins, mode and provenance, the flag's remedy)
        states = (
            (
                "the re-read's file: 200000 `[` where the build record would be",
                write_record(deep),
                no_patches,
                unusable + "it is 200000 bytes, more than the 65536 a build record is read up to",
                ("in-tree", "reused"),
                rm,
            ),
            (
                "that file under a larger bound: nested deeper than the JSON parser's stack",
                write_record(deep),
                a_larger_bound,
                unusable + "it could not be read as a build record: RecursionError: ",
                ("in-tree", "reused"),
                rm,
            ),
            (
                "a build record whose reading runs out of memory",
                write_record(b"{}\n"),
                raising("_llvm_build_record_errors", MemoryError()),
                unusable + "it could not be read as a build record: MemoryError",
                ("in-tree", "reused"),
                rm,
            ),
            (
                "a build record that is not UTF-8",
                write_record(b"\xff\xfe{}"),
                no_patches,
                unusable + "it is not JSON: ",
                ("in-tree", "reused"),
                rm,
            ),
            (
                "a listing that fails in a way nobody listed",
                lambda root: None,
                raising("capture_llvm_output", RuntimeError("boom")),
                unobserved + "RuntimeError: boom",
                ("unknown", "unknown"),
                unreadable,
            ),
            (
                "a listing that runs out of memory",
                lambda root: None,
                raising("capture_llvm_output", MemoryError()),
                unobserved + "MemoryError",
                ("unknown", "unknown"),
                unreadable,
            ),
            (
                "git that cannot be asked for the LLVM sources",
                lambda root: None,
                raising("capture_llvm_source_identity", subprocess.TimeoutExpired("git", 30)),
                unobserved + "TimeoutExpired: ",
                ("unknown", "unknown"),
                unreadable,
            ),
            (
                "a fault in what only reads the observation",
                lambda root: None,
                raising("llvm_identity_obstacle_rows", KeyError("output")),
                unobserved + "KeyError: 'output'",
                ("unknown", "unknown"),
                unreadable,
            ),
            (
                "a fault in what prints the observation",
                lambda root: None,
                raising("llvm_before_report", RecursionError("maximum recursion depth exceeded")),
                unobserved + "RecursionError: maximum recursion depth exceeded",
                ("unknown", "unknown"),
                unreadable,
            ),
            (
                "an observation that fails after the build",
                lambda root: None,
                failing_after_the_build,
                "the LLVM this build carries could not be observed after the build: RecursionError: "
                "maximum recursion depth exceeded",
                ("unknown", "unknown"),
                # Before x.py this is an LLVM with no record, and refused as one.
                rm,
            ),
        )
        labels = [row[0] for row in states]
        self.assertEqual(len(labels), len(set(labels)))
        for label, put, patches, reason, words, remedy in states:
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(str(Path(directory).resolve()))
                self.commit = self.llvm_checkout(root)
                self.install_llvm(root)
                put(root)
                receipt_path = stage_root / "tool-provenance.json"
                before = self.llvm_directory_state(root)
                seen_by_x_py: list[dict] = []

                with ExitStack() as stack:
                    for replaced in patches():
                        stack.enter_context(replaced)
                    status, events, printed, mocks = self.main_over_a_build_directory(
                        root,
                        stage_root,
                        everyday,
                        x_py=lambda: seen_by_x_py.append(self.llvm_directory_state(root)),
                    )
                # THE BUILD ORIGIN/MAIN RUNS: its exit, its steps in order, its
                # x.py call, on an LLVM directory nobody touched.
                self.assertEqual(status, 0, printed)
                self.assertEqual(
                    events,
                    [
                        "quarantine_seed_stage0",
                        "run_xpy_build",
                        "install_ay_solver",
                        "discard_seed_stage0_quarantine",
                        "maybe_register_rustup_toolchain",
                    ],
                )
                self.assertEqual(
                    mocks["run_xpy_build"].call_args,
                    call(root, self.host, 2, None, [], seed_mode=True, seed_compiler=None),
                )
                self.assertEqual(seen_by_x_py, [before])
                self.assertEqual(self.llvm_directory_state(root), before)
                self.assertNotIn("Refusing to build", printed)
                self.assertNotIn("Traceback", printed)
                # ... its status word, verified by its one verification ...
                receipt = json.loads(receipt_path.read_text())
                self.assertEqual((receipt["status"], receipt["errors"]), ("release-ready", []))
                self.assertEqual(
                    printed.count("  verified existing stage provenance (release-ready) -> "), 1
                )
                # ... and the record says what could not be said, and why.
                llvm = receipt["llvm_identity"]
                self.assertEqual(
                    (llvm["mode"], llvm["provenance"], llvm["identity_stated"], llvm["build_record"]),
                    (*words, False, None),
                )
                self.assertEqual(len(llvm["reasons"]), 1, llvm["reasons"])
                self.assertTrue(llvm["reasons"][0].startswith(reason), llvm["reasons"])
                self.assertIn(f"    not stated: {llvm['reasons'][0]}\n", printed)
                # But for that key it is origin/main's receipt.
                digest = receipt["bootstrap_lineage"]["config_sha256"]
                del receipt["llvm_identity"]
                self.assertTrue(
                    self.run_audit(
                        root,
                        stage_root,
                        invocation=everyday,
                        bootstrap_before=self.bootstrap_lineage(digest=digest, hydrated=False),
                        bootstrap_after=self.bootstrap_lineage(digest=digest, hydrated=True),
                    )
                )
                self.assertEqual(json.loads(receipt_path.read_text()), receipt)
                receipt_path.unlink()

                # ASKED, the same state is a refusal before x.py: the stage0
                # goes back, nothing is written, and the refusal carries its
                # command or says that none applies.
                with ExitStack() as stack:
                    for replaced in patches():
                        stack.enter_context(replaced)
                    status, events, printed, mocks = self.main_over_a_build_directory(
                        root, stage_root, asked
                    )
                self.assertEqual(status, 1, printed)
                self.assertEqual(events, ["quarantine_seed_stage0", "recover_seed_stage0_quarantine"])
                self.assertFalse(receipt_path.exists())
                self.assertEqual(self.llvm_directory_state(root), before)
                refusal = printed[printed.index("\nRefusing to build: ") :]
                self.assertIn(remedy, refusal)
                self.assertEqual("rm -rf" in refusal, remedy == rm, refusal)

        # WHATEVER THE REFUSAL'S OWN TEXT MEETS, the stage0 that was set aside
        # goes back: the exit this record added before x.py cannot leave it
        # aside, even by failing.
        recovered: list[str] = []
        with patch.object(
            recreate_bootstrap, "llvm_identity_refusal", side_effect=RuntimeError("boom")
        ), self.assertRaises(RuntimeError):
            self.main_around_llvm(
                self.SEAL_INVOCATION,
                self.llvm_observation(present=True),
                recover_seed_stage0_quarantine=lambda *_args, **_kwargs: recovered.append("put back"),
            )
        self.assertEqual(recovered, ["put back"])

    def test_a_build_that_fails_after_its_llvm_leaves_the_record_a_retry_reuses(self):
        # A seal attempt that builds LLVM from nothing and then fails (a
        # stage-1 crate, the ay install) never reaches the audit, which is what
        # leaves the build record. Without it the retry finds an LLVM directory
        # it cannot account for and, asked for the identity, is refused until
        # LLVM is built a second time.
        asked = self.SEAL_INVOCATION
        where = f"build/{self.host}/llvm"
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(str(Path(directory).resolve()))
            self.commit = self.llvm_checkout(root)
            record_path = self.llvm_out(root) / ".trust-llvm-build-record.json"
            status, events, printed, mocks = self.main_over_a_build_directory(
                root, stage_root, asked, x_py=lambda: self.install_llvm(root), x_py_exit=1
            )
            # The failure is the build's own, reported as it was.
            self.assertEqual(status, 1)
            self.assertEqual(
                events, ["quarantine_seed_stage0", "run_xpy_build", "recover_seed_stage0_quarantine"]
            )
            self.assertIn("\n`./x.py build` failed (exit 1).\n", printed)
            self.assertFalse((stage_root / "tool-provenance.json").exists())
            self.assertIn(
                f"  left the build record of the LLVM this run built ({where}, at commit "
                f"{self.commit[:12]}): a retry in this build directory can reuse it and state its "
                "identity\n",
                printed,
            )
            source = recreate_bootstrap.capture_llvm_source_identity(root)
            config_sha256 = hashlib.sha256((root / "bootstrap.toml").read_bytes()).hexdigest()
            self.assertEqual(
                json.loads(record_path.read_text()),
                {
                    "schema": "trust.llvm-build-record.v1",
                    "built_at_commit": self.commit,
                    "host": self.host,
                    "source_identity_sha256": source["identity_sha256"],
                    "source_paths": source["paths"],
                    "bootstrap_config_sha256": config_sha256,
                    "native_authority_sha256": "8" * 64,
                    "output_fingerprint_sha256": recreate_bootstrap.capture_llvm_output(
                        root, self.host
                    )["fingerprint_sha256"],
                },
            )
            # The retry is not refused, reuses the LLVM, and states it.
            status, events, printed, mocks = self.main_over_a_build_directory(root, stage_root, asked)
            self.assertEqual(status, 0, printed)
            self.assertIn("run_xpy_build", events)
            llvm = json.loads((stage_root / "tool-provenance.json").read_text())["llvm_identity"]
            self.assertEqual(
                (llvm["provenance"], llvm["identity_stated"]), ("reused", True)
            )
            self.assertEqual(llvm["build_record"], json.loads(record_path.read_text()))

        # The record is left on the audit's own conditions and no weaker one.
        def failed_build(root, **changes):
            before = changes.pop("before", None) or recreate_bootstrap.capture_llvm_before_build(
                root, self.host, None, root / "bootstrap.toml"
            )
            arguments = {
                "commit_before": self.commit,
                "config_path": root / "bootstrap.toml",
                "config_sha256": hashlib.sha256((root / "bootstrap.toml").read_bytes()).hexdigest(),
                "build_authority_before": self.build_authority(),
                "llvm_config": None,
                **changes.pop("arguments", {}),
            }
            changes.pop("x_py", lambda: self.install_llvm(root))()
            output = io.StringIO()
            with patch.object(
                recreate_bootstrap,
                "capture_build_authority",
                return_value=changes.pop("authority_after", self.build_authority()),
            ), patch("sys.stdout", output):
                self.assertIsNone(
                    recreate_bootstrap.leave_llvm_build_record_after_failed_build(
                        root, self.host, before, **arguments
                    )
                )
            self.assertEqual(changes, {})
            return output.getvalue()

        def unstamped(root):
            (self.install_llvm(root) / ".llvm-stamp").unlink()

        def edited(root):
            self.install_llvm(root)
            (root / "src" / "bootstrap" / "llvm.rs").write_text("// edited during the build\n")

        def reconfigured(root):
            self.install_llvm(root)
            (root / "bootstrap.toml").write_text("[llvm]\ndownload-ci-llvm = false\nassertions = true\n")

        def committed(root):
            self.install_llvm(root)
            (root / "notes.txt").write_text("elsewhere\n")
            self.llvm_git(root, "add", "notes.txt")
            self.llvm_git(root, "commit", "-m", "elsewhere")

        rejected_authority = {**self.build_authority(), "status": "rejected"}
        cases = (
            ("the build as it should be", {}, "  left the build record of the LLVM this run built"),
            ("x.py did not finish LLVM (no stamp)", {"x_py": unstamped}, ""),
            (
                "an LLVM input edited during the build",
                {"x_py": edited},
                "    something under src/bootstrap, src/llvm-project, src/version is staged, modified "
                "or untracked: HEAD's object ids are not what gets compiled\n",
            ),
            (
                "the config rewritten during the build",
                {"x_py": reconfigured},
                "    the bootstrap config or the native tool and SDK authority changed during the build\n",
            ),
            (
                "other native tools by the end of the build",
                {"authority_after": self.build_authority("7" * 64)},
                "    the bootstrap config or the native tool and SDK authority changed during the build\n",
            ),
            (
                "a native authority that is refused by the end of the build",
                {"authority_after": rejected_authority},
                "    the bootstrap config or the native tool and SDK authority changed during the build\n",
            ),
            (
                "HEAD moved during the build",
                {"x_py": committed},
                "    HEAD is not the commit the build started at (",
            ),
            (
                "the commit the build started at is not known",
                {"arguments": {"commit_before": ""}},
                "    HEAD is not the commit the build started at (unknown)\n",
            ),
        )
        for label, changes, said in cases:
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                self.commit = self.llvm_checkout(root)
                (root / "bootstrap.toml").write_text("[llvm]\ndownload-ci-llvm = false\n")
                changes = dict(changes)
                if "x_py" in changes:
                    changes["x_py"] = (lambda function: lambda: function(root))(changes["x_py"])
                printed = failed_build(root, **changes)
                record_path = self.llvm_out(root) / ".trust-llvm-build-record.json"
                self.assertEqual(record_path.exists(), label == "the build as it should be", printed)
                if said:
                    self.assertIn(said, printed)
                else:
                    self.assertEqual(printed, "")
                if not record_path.exists() and said:
                    self.assertIn(
                        "  the LLVM this run built gets no build record, so a retry cannot state its "
                        "identity:\n",
                        printed,
                    )
        # Never for an LLVM directory that was there before x.py (every build
        # in an existing build directory): nothing is asked, nothing is said.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.commit = self.llvm_checkout(root)
            (root / "bootstrap.toml").write_text("[llvm]\ndownload-ci-llvm = false\n")
            self.install_llvm(root)
            state = self.llvm_directory_state(root)
            with patch.object(recreate_bootstrap, "_git_bytes") as git, patch.object(
                recreate_bootstrap, "capture_build_authority"
            ) as authority:
                observed = recreate_bootstrap.capture_llvm_before_build
                with patch.object(
                    recreate_bootstrap, "capture_llvm_source_identity", return_value=self.llvm_source()
                ):
                    before = observed(root, self.host, None, root / "bootstrap.toml")
                self.assertEqual(failed_build(root, before=before, x_py=lambda: None), "")
                git.assert_not_called()
                authority.assert_not_called()
            self.assertEqual(self.llvm_directory_state(root), state)
        # And whatever goes wrong in it, the failure being reported stands.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.commit = self.llvm_checkout(root)
            (root / "bootstrap.toml").write_text("[llvm]\ndownload-ci-llvm = false\n")
            with patch.object(
                recreate_bootstrap, "write_llvm_build_record", side_effect=OSError("disk full")
            ):
                self.assertEqual(
                    failed_build(root),
                    "  (the build record of the LLVM this run built was not left: disk full)\n",
                )

    def stated_llvm_receipt(self, root: Path, stage_root: Path):
        verdict, receipt, printed = self.llvm_build(
            root,
            stage_root,
            x_py=lambda: self.install_llvm(root),
            invocation=self.SEED_INVOCATION,
        )
        self.assertTrue(verdict, printed)
        self.assertTrue(receipt["llvm_identity"]["identity_stated"])
        return receipt

    def malformed_llvm_records(self, good):
        record = good["build_record"]
        other = self.llvm_source(llvm_tree="9" * 40)
        rows = good["source_paths"]

        def with_(**changes):
            return {**good, **changes}

        def with_record(**changes):
            return {**good, "build_record": {**record, **changes}}

        unstated = {"identity_stated": False, "reasons": ["x.py left no completed in-tree LLVM build"]}
        not_in_tree = {"build_record": None, "output_dirs": [], "output_fingerprint_sha256": None}
        return (
            ("not an object", ["in-tree"], "llvm_identity is not an object"),
            (
                "a key the schema does not have",
                with_(built_by="x.py"),
                "llvm_identity does not hold exactly the keys build_record, identity_stated, mode, "
                "output_dirs, output_fingerprint_sha256, provenance, reasons, schema, "
                "source_identity_sha256, source_paths",
            ),
            (
                "a key missing",
                {key: value for key, value in good.items() if key != "reasons"},
                "llvm_identity does not hold exactly the keys ",
            ),
            (
                "another schema",
                with_(schema="trust.llvm-identity.v2"),
                "llvm_identity.schema is not trust.llvm-identity.v1",
            ),
            (
                "a mode outside the vocabulary",
                with_(mode="vendored"),
                "llvm_identity.mode is 'vendored', not one of in-tree, external, unknown",
            ),
            (
                "a mode that is not a word",
                with_(mode=["in-tree"]),
                "llvm_identity.mode is ['in-tree'], not one of in-tree, external, unknown",
            ),
            (
                "a provenance of another mode",
                with_(provenance="external"),
                "llvm_identity.provenance is 'external'; a record of mode in-tree says one of "
                "built-in-this-run, reused, changed-in-this-run, unknown",
            ),
            (
                "a flag that is a number",
                with_(identity_stated=1),
                "llvm_identity.identity_stated is neither true nor false",
            ),
            (
                "reasons that are one sentence, not a list",
                with_(reasons="none"),
                "llvm_identity.reasons is not a list of sentences",
            ),
            (
                "an empty reason",
                with_(identity_stated=False, reasons=[""], build_record=None),
                "llvm_identity.reasons is not a list of sentences",
            ),
            (
                "stated, with a reason against it",
                with_(reasons=["x.py left no completed in-tree LLVM build"]),
                "llvm_identity.identity_stated and llvm_identity.reasons disagree",
            ),
            (
                "not stated, and no reason given",
                with_(identity_stated=False, build_record=None),
                "llvm_identity.identity_stated and llvm_identity.reasons disagree",
            ),
            (
                "stated, with no source identity",
                with_(source_paths=[], source_identity_sha256=None),
                "llvm_identity states an identity without a source identity",
            ),
            (
                "a source row without its type",
                with_(source_paths=[{"path": "src/llvm-project", "oid": "3" * 40}]),
                "llvm_identity.source_paths holds a row that is not a path, an object type and an "
                "object id",
            ),
            (
                "an abbreviated object id",
                with_(source_paths=[{**row, "oid": row["oid"][:12]} for row in rows]),
                "llvm_identity.source_paths holds a row that is not a path, an object type and an "
                "object id",
            ),
            (
                "source rows out of order",
                with_(source_paths=list(reversed(rows))),
                "llvm_identity.source_paths is not sorted by path without a repeat",
            ),
            (
                "a source row twice",
                with_(source_paths=[rows[0], *rows]),
                "llvm_identity.source_paths is not sorted by path without a repeat",
            ),
            (
                "source rows without the LLVM tree",
                with_(source_paths=[row for row in rows if row["path"] != "src/llvm-project"]),
                "llvm_identity.source_paths does not name src/llvm-project",
            ),
            (
                "source rows that are no list",
                with_(source_paths={"src/llvm-project": "3" * 40}),
                "llvm_identity.source_paths is not a non-empty list",
            ),
            (
                "an identity that is not its rows'",
                with_(source_identity_sha256=other["identity_sha256"]),
                "llvm_identity.source_identity_sha256 is not the identity of "
                "llvm_identity.source_paths",
            ),
            (
                "an output fingerprint that is not one",
                with_(output_fingerprint_sha256="unknown"),
                "llvm_identity.output_fingerprint_sha256 is neither null nor a sha256",
            ),
            (
                "output directories that are one path, not a list",
                with_(output_dirs="build/test-host/llvm"),
                "llvm_identity.output_dirs is not a list of paths",
            ),
            (
                "an output directory with no name",
                with_(output_dirs=["build/test-host/llvm", ""]),
                "llvm_identity.output_dirs is not a list of paths",
            ),
            (
                "stated, in-tree, without the directories it fingerprints",
                with_(output_dirs=[]),
                "llvm_identity states the identity of an in-tree LLVM without its output",
            ),
            (
                "stated, in-tree, without a fingerprint",
                with_(output_fingerprint_sha256=None),
                "llvm_identity states the identity of an in-tree LLVM without its output",
            ),
            (
                "stated, in-tree, without a build record",
                with_(build_record=None),
                "llvm_identity states the identity of an in-tree LLVM without a build record",
            ),
            (
                "stated, of an LLVM that changed during the run",
                with_(provenance="changed-in-this-run"),
                "llvm_identity states the identity of an LLVM whose provenance is changed-in-this-run",
            ),
            (
                "not stated, quoting a build record",
                with_(**unstated),
                "llvm_identity quotes a build record for an identity it does not state",
            ),
            (
                "a build record for other sources",
                with_record(
                    source_paths=other["paths"], source_identity_sha256=other["identity_sha256"]
                ),
                "llvm_identity's build record is for another source identity than this receipt's",
            ),
            (
                "a build record for another output",
                with_record(output_fingerprint_sha256="0" * 64),
                "llvm_identity's build record is for another output than this receipt's",
            ),
            (
                "a build record for another host",
                with_record(host="other-host"),
                "llvm_identity's build record is for another host than this receipt's",
            ),
            (
                "a build record for another bootstrap config",
                with_record(bootstrap_config_sha256="0" * 64),
                "llvm_identity's build record is for another bootstrap config than this receipt's",
            ),
            (
                "a build record for other native tools",
                with_record(native_authority_sha256="0" * 64),
                "llvm_identity's build record is for another native tool and SDK authority than "
                "this receipt's",
            ),
            (
                "built in this run, by the record of another commit",
                with_record(built_at_commit="2" * 40),
                "llvm_identity says LLVM was built in this run, and its build record names another "
                "commit than this receipt's",
            ),
            (
                "a build record with a key more",
                with_record(built_by="x.py"),
                "the LLVM build record does not hold exactly the keys bootstrap_config_sha256, "
                "built_at_commit, host, native_authority_sha256, output_fingerprint_sha256, schema, "
                "source_identity_sha256, source_paths",
            ),
            (
                "a build record that is no object",
                with_(build_record="built"),
                "the LLVM build record is not an object",
            ),
            (
                "a build record of another schema",
                with_record(schema="trust.llvm-build-record.v2"),
                "the LLVM build record's schema is not trust.llvm-build-record.v1",
            ),
            (
                "a build record with an abbreviated commit",
                with_record(built_at_commit="1" * 12),
                "the LLVM build record's built_at_commit is not a full commit id",
            ),
            (
                "a build record without a host",
                with_record(host=""),
                "the LLVM build record's host is not a host triple",
            ),
            (
                "a build record whose config digest is not one",
                with_record(bootstrap_config_sha256="D" * 64),
                "the LLVM build record's bootstrap_config_sha256 is not a sha256",
            ),
            (
                "a build record whose identity is not its rows'",
                with_record(source_identity_sha256=other["identity_sha256"]),
                "the LLVM build record's source_identity_sha256 is not the identity of its "
                "source_paths",
            ),
            (
                "a build record whose rows are not rows",
                with_record(source_paths=[]),
                "the LLVM build record's source_paths is not a non-empty list",
            ),
            # An external LLVM (--llvm-config) is never stated, and nothing of
            # the checkout or the build directory stands beside it.
            (
                "an external LLVM that is stated",
                with_(mode="external", provenance="external", **not_in_tree),
                "llvm_identity states the identity of an external LLVM: which sources an LLVM "
                "linked through --llvm-config was built from is never established",
            ),
            (
                "an external LLVM with the checkout's source identity",
                with_(mode="external", provenance="external", **unstated, **not_in_tree),
                "llvm_identity of an external LLVM carries a source identity: this checkout's LLVM "
                "sources do not describe an LLVM linked through --llvm-config",
            ),
            (
                "an external LLVM with an in-tree output",
                with_(
                    mode="external",
                    provenance="external",
                    **unstated,
                    build_record=None,
                    source_paths=[],
                    source_identity_sha256=None,
                ),
                "llvm_identity of an external LLVM carries an in-tree output or build record",
            ),
            (
                "an external LLVM quoting a build record",
                with_(
                    mode="external",
                    provenance="external",
                    **unstated,
                    output_dirs=[],
                    output_fingerprint_sha256=None,
                    source_paths=[],
                    source_identity_sha256=None,
                ),
                "llvm_identity of an external LLVM carries an in-tree output or build record",
            ),
            (
                "an identity stated for an LLVM of unknown mode",
                with_(mode="unknown", provenance="unknown", **not_in_tree),
                "llvm_identity states the identity of an LLVM of unknown mode",
            ),
        )

    def test_a_malformed_llvm_record_is_refused_by_both_of_its_readers(self):
        # The verifier and promotion's reader hold the record to one rule: its
        # form, and its agreement with itself and with the receipt it is in.
        reader = load_stage_receipt_reader()
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            good_receipt = self.stated_llvm_receipt(root, stage_root)
        good = good_receipt["llvm_identity"]
        self.assertEqual(recreate_bootstrap._llvm_identity_errors(good, good_receipt), [])
        self.assertEqual(reader.llvm_identity_errors(good, good_receipt), [])
        rows = self.malformed_llvm_records(good)
        labels = [label for label, _record, _message in rows]
        self.assertEqual(len(labels), len(set(labels)))
        for label, record, message in rows:
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                self.stated_llvm_receipt(root, stage_root)
                receipt_path = stage_root / "tool-provenance.json"
                receipt = json.loads(receipt_path.read_text())
                receipt["llvm_identity"] = record
                receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
                output = io.StringIO()
                with patch("sys.stdout", output):
                    self.assertFalse(self.verify_receipt(root, stage_root, self.lineage()))
                self.assertIn(f"ERROR: {message}", output.getvalue())
                writers = recreate_bootstrap._llvm_identity_errors(record, receipt)
                self.assertTrue(any(error.startswith(message) for error in writers), writers)
                self.assertEqual(reader.llvm_identity_errors(record, receipt), writers)
                with self.assertRaises(reader.StageReceiptError) as refused:
                    reader.lines(stage_root, self.commit)
                self.assertIn(message, str(refused.exception))
        # One vocabulary, two files.
        for name in (
            "LLVM_IDENTITY_SCHEMA",
            "LLVM_SOURCE_IDENTITY_SCHEMA",
            "LLVM_BUILD_RECORD_SCHEMA",
            "LLVM_SOURCE_TREE",
            "LLVM_PROVENANCE_OF_MODE",
            "LLVM_IDENTITY_KEYS",
            "LLVM_BUILD_RECORD_KEYS",
        ):
            self.assertEqual(getattr(reader, name), getattr(recreate_bootstrap, name), name)
        self.assertEqual(set(good), set(reader.LLVM_IDENTITY_KEYS))
        self.assertEqual(set(good["build_record"]), set(reader.LLVM_BUILD_RECORD_KEYS))
        self.assertEqual(
            reader.llvm_source_identity_sha256(good["source_paths"]), good["source_identity_sha256"]
        )
        for record in (good["build_record"], {}, None, {**good["build_record"], "host": 7}):
            self.assertEqual(
                reader.llvm_build_record_errors(record),
                recreate_bootstrap._llvm_build_record_errors(record),
            )

    def test_the_verifier_re_derives_what_it_can_of_the_llvm_record(self):
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.stated_llvm_receipt(root, stage_root)
            receipt_path = stage_root / "tool-provenance.json"
            receipt_bytes = receipt_path.read_bytes()
            record_path = self.llvm_out(root) / ".trust-llvm-build-record.json"
            record_bytes = record_path.read_bytes()
            library = self.llvm_out(root) / "lib" / "libLLVMCore.a"
            library_bytes = library.read_bytes()

            def verified(expected, **verify):
                output = io.StringIO()
                with patch("sys.stdout", output):
                    self.assertEqual(
                        self.verify_receipt(root, stage_root, self.lineage(), **verify), expected
                    )
                self.assertEqual(receipt_path.read_bytes(), receipt_bytes)
                return output.getvalue()

            def refused(message, **verify):
                self.assertIn(f"  ERROR: {message}\n", verified(False, **verify))

            def build_directory_differs(message):
                # What the build directory no longer bears out. Before the
                # record existed the verifier asked nothing of that directory,
                # so without the requirement it says what it found and passes;
                # with it, the same finding is the error.
                printed = verified(True)
                self.assertIn(
                    f"  llvm, not verified (--require-llvm-identity makes it an error): {message}\n",
                    printed,
                )
                self.assertNotIn("ERROR", printed)
                verified(True, require_immutable_lineage=True, require_public_release=True)
                refused(message, require_llvm_identity=True)

            printed = verified(True)
            self.assertIn("  llvm: in-tree, built-in-this-run, identity stated (source identity ", printed)
            self.assertNotIn("not verified", printed)
            self.assertNotIn("not verified", verified(True, require_llvm_identity=True))
            # ALWAYS, the source identity from the tree it runs in: a commit
            # that changed an LLVM source since, or sources that are not HEAD's.
            # (The source closure the verifier has always compared differs then
            # too: such a receipt is not this tree's.)
            refused(
                "current LLVM source identity differs from the receipt",
                llvm_source=self.llvm_source(llvm_tree="9" * 40),
            )
            refused(
                "current LLVM source identity differs from the receipt",
                llvm_source=self.llvm_source(bootstrap_tree="9" * 40),
            )
            refused(
                "the LLVM sources differ from HEAD under a receipt that states their identity",
                llvm_source=self.llvm_source(clean=False),
            )
            # A tree git does not answer for NOW (its status timed out, say) has
            # no identity to compare the record's with. The verifier never made
            # that call before the record existed, so by default it is a
            # finding; under the requirement it is the error.
            unanswered = {
                "paths": [],
                "identity_sha256": None,
                "clean": False,
                "errors": ["could not record the state of the LLVM sources: timed out"],
            }
            finding = (
                "the LLVM source identity could not be recomputed: could not record the state of "
                "the LLVM sources: timed out"
            )
            printed = verified(True, llvm_source=unanswered)
            self.assertIn(
                f"  llvm, not verified (--require-llvm-identity makes it an error): {finding}\n", printed
            )
            verified(
                True, require_immutable_lineage=True, require_public_release=True, llvm_source=unanswered
            )
            refused(finding, require_llvm_identity=True, llvm_source=unanswered)
            # UNDER THE REQUIREMENT, the LLVM in the build directory as it is now.
            library.write_bytes(b"relinked after the receipt was written")
            build_directory_differs("current in-tree LLVM output differs from the receipt")
            library.write_bytes(library_bytes)
            self.assertNotIn("not verified", verified(True))
            # ... and the build record there, against the one the receipt quotes.
            edited = json.loads(record_bytes)
            edited["built_at_commit"] = "2" * 40
            record_path.write_text(json.dumps(edited, indent=2, sort_keys=True) + "\n")
            build_directory_differs(
                "the LLVM build record in the build directory is not the one the receipt quotes"
            )
            record_path.unlink()
            build_directory_differs(
                "the LLVM build record in the build directory is not the one the receipt quotes"
            )
            # ... WHATEVER is at that name now. The independent re-read's file,
            # 200000 `[`, is a finding like the others; the verifier used to
            # die on it, of a RecursionError out of the JSON parser. First as
            # the read refuses it (too large to be a record), then with the
            # parser meeting it.
            record_path.write_bytes(b"[" * 200000)
            build_directory_differs(
                "the LLVM build record in the build directory is not the one the receipt quotes"
            )
            with patch.object(recreate_bootstrap, "LLVM_BUILD_RECORD_MAX_BYTES", 1 << 20):
                self.assertEqual(
                    recreate_bootstrap.read_llvm_build_record(root, self.host)[0], None
                )
                self.assertTrue(
                    recreate_bootstrap.read_llvm_build_record(root, self.host)[1][0].startswith(
                        "it could not be read as a build record: RecursionError: "
                    )
                )
                build_directory_differs(
                    "the LLVM build record in the build directory is not the one the receipt quotes"
                )
            record_path.write_bytes(record_bytes)
            verified(True, require_llvm_identity=True)
            # And a directory that cannot be observed at all, for a reason
            # nobody listed: a finding, never an exception out of the verifier
            # (main() runs it at the end of the documented build).
            for error, said in (
                (RuntimeError("boom"), "RuntimeError: boom"),
                (MemoryError(), "MemoryError"),
                (PermissionError(13, "Permission denied"), "[Errno 13] Permission denied"),
            ):
                with self.subTest(said), patch.object(
                    recreate_bootstrap, "capture_llvm_output", side_effect=error
                ):
                    build_directory_differs(
                        f"the in-tree LLVM in the build directory could not be observed: {said}"
                    )
            verified(True, require_llvm_identity=True)

            # A receipt that does not state the identity: verified as it was
            # under every requirement it could meet before, refused by the one
            # that asks, with the receipt's own reason.
            receipt = json.loads(receipt_bytes)
            receipt["llvm_identity"].update(
                identity_stated=False,
                reasons=["the LLVM source identity changed during the build"],
                build_record=None,
            )
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            receipt_bytes = receipt_path.read_bytes()
            self.assertIn(
                "  llvm: in-tree, built-in-this-run, identity NOT stated (source identity ",
                verified(True),
            )
            verified(True, require_immutable_lineage=True, require_public_release=True)
            refused(
                "the identity of the LLVM this stage carries is required (--require-llvm-identity) "
                "and this receipt does not state it: the LLVM source identity changed during the build",
                require_llvm_identity=True,
            )
            # A receipt from before the record: the same.
            del receipt["llvm_identity"]
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            receipt_bytes = receipt_path.read_bytes()
            self.assertNotIn("llvm", verified(True))
            verified(True, require_immutable_lineage=True, require_public_release=True)
            refused(
                "the identity of the LLVM this stage carries is required (--require-llvm-identity) "
                "and this receipt holds no llvm_identity record: it was written before the recreator "
                "recorded one",
                require_llvm_identity=True,
            )

        # What it cannot re-derive, in its help: whether LLVM was built in the
        # receipt's run, and what the recorded output was compiled from.
        shown = io.StringIO()
        with patch.dict(os.environ, {"COLUMNS": "100000", "NO_COLOR": "1"}, clear=True), \
                patch.object(sys, "stdout", shown), self.assertRaises(SystemExit):
            recreate_bootstrap.parse_args(["--help"])
        text = " ".join(shown.getvalue().split())
        for sentence in (
            "Of the receipt's `llvm_identity` (the LLVM the stage carries) it always checks the "
            "form, the record's agreement with its receipt, and the source identity, recomputed "
            "from this tree's HEAD.",
            "It also recomputes the fingerprint of build/<host>/llvm (with build/<host>/lld) as it "
            "is now and compares the build record there with the one the receipt quotes; what "
            "differs is printed, and is an error only with --require-llvm-identity.",
            "It cannot recompute whether LLVM was built in the receipt's run or reused, nor that "
            "the files a build record fingerprints were compiled from the sources it names: both "
            "rest on a run having found no build/<host>/llvm before the x.py that produced it.",
            "A receipt written before that record existed is not asked for one either.",
            # ... and of an external LLVM, nothing at all.
            "Of an LLVM linked through --llvm-config (mode external) it recomputes nothing: such a "
            "record is never stated and holds no source identity, and what answers for the "
            "llvm-config executable is the build-authority comparison this verification always made.",
            # --llvm-config says so itself, where the choice is made.
            "The stage receipt records such an LLVM as external and never states its identity (the "
            "build binds the llvm-config executable, not what it points at), so "
            "--require-llvm-identity refuses it.",
            # What --fresh-seed does not do, where an operator reads it, and
            # that it refuses nothing for the LLVM.
            "It does not rebuild the in-tree LLVM: the receipt records which LLVM the stage "
            "carries, and --require-llvm-identity is what refuses one it cannot state.",
            # The flag: what it refuses, when, and what it costs.
            "--require-llvm-identity Require that the stage states the identity of the LLVM it "
            "carries: the flag for a build that will be sealed.",
            # ... and why x.py's own rebuild is not enough, as x.py is since 2026-10-13, in the
            # refusal's words; the script's description says the same.
            "x.py rebuilds the in-tree LLVM when HEAD:src/llvm-project moves from the tree "
            "recorded beside it, but it keeps an LLVM that cannot say what it was built from (one "
            "built before that record, whose own build header names no commit this checkout has), "
            "and a change to src/bootstrap, src/version or the bootstrap config rebuilds none, so "
            "a reused build directory can carry an LLVM built from other sources or with another "
            "recipe;",
            "x.py rebuilds LLVM when HEAD:src/llvm-project moves from the tree recorded beside it, "
            "but it keeps an LLVM that cannot say what it was built from (one built before that "
            "record, whose own build header names no commit this checkout has), and a change to "
            "its recipe or config rebuilds none, so a build that must not carry an LLVM of "
            "unstated origin (a seal) passes `--require-llvm-identity`",
            "the receipt records what could be established (`llvm_identity`) and, without this "
            "flag, nothing else about the build changes.",
            "the build is refused BEFORE x.py starts when it is already known that the identity "
            "could not be stated",
            "the bootstrap config does not itself say that the in-tree LLVM is linked; or the stage "
            "links an LLVM through --llvm-config, whose identity is never stated), with the command "
            "that fixes it or the statement that no single command does; and a finished build whose "
            "receipt does not state the identity fails.",
            "`--check` does not preview that refusal.",
            "With --verify-stage-provenance: the receipt must hold the record and state the "
            "identity, and build/<host>/llvm must still be what it fingerprints.",
            "Cost: an LLVM build from nothing once per build directory, and again after any change "
            "to src/llvm-project, src/bootstrap, src/version, the bootstrap config or the native "
            "tool and SDK authority the receipt binds, which is compared whole (a Homebrew "
            "self-update moves it).",
        ):
            self.assertIn(sentence, text)
        # What stopped being true on 2026-10-13 is not said any more, nor that x.py rebuilds
        # LLVM only where the directory says what it was built from: one x.py kept without
        # knowing (`adopted`) is rebuilt at the next committed change, like any other.
        self.assertNotIn("not rebuild the in-tree LLVM for a committed change", text)
        self.assertNotIn("not rebuild LLVM for a committed change", text)
        self.assertNotIn("only where the build directory says", text)
        self.assertNotIn("only in a build directory whose LLVM says", text)

    def test_promotion_names_the_llvm_a_receipt_says_its_stage_carries(self):
        reader = load_stage_receipt_reader()
        source = self.llvm_source()

        def llvm_lines(stage_root):
            lines = reader.lines(stage_root, self.commit)
            keys = [line.split("=", 1)[0] for line in lines]
            self.assertEqual(len(keys), len(set(keys)))
            for line in lines:
                self.assertRegex(line, r"\A[a-z0-9_]+=[ -~]+\Z")
            # They sit between the files that were compared and the command line.
            first = keys.index("stage_receipt_llvm")
            self.assertEqual(keys[first - 1], "stage_receipt_files_verified")
            self.assertEqual(keys[-1], "stage_receipt_recreator_argv")
            self.assertTrue(all(key.startswith("stage_receipt_llvm") for key in keys[first:-1]))
            return lines[first:-1]

        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            receipt = self.stated_llvm_receipt(root, stage_root)
            fingerprint = receipt["llvm_identity"]["output_fingerprint_sha256"]
            self.assertEqual(
                llvm_lines(stage_root),
                [
                    "stage_receipt_llvm=in-tree",
                    "stage_receipt_llvm_identity=stated",
                    "stage_receipt_llvm_provenance=built-in-this-run",
                    f"stage_receipt_llvm_source_sha256={source['identity_sha256']}",
                    f"stage_receipt_llvm_source_tree={'3' * 40}",
                    f"stage_receipt_llvm_built_at_commit={self.commit}",
                    f"stage_receipt_llvm_output_sha256={fingerprint}",
                ],
            )
            # Reused at a later commit, on the record that build left.
            first_commit, self.commit = self.commit, "5" * 40
            verdict, _receipt, printed = self.llvm_build(root, stage_root)
            self.assertTrue(verdict, printed)
            self.assertEqual(
                llvm_lines(stage_root),
                [
                    "stage_receipt_llvm=in-tree",
                    "stage_receipt_llvm_identity=stated",
                    "stage_receipt_llvm_provenance=reused",
                    f"stage_receipt_llvm_source_sha256={source['identity_sha256']}",
                    f"stage_receipt_llvm_source_tree={'3' * 40}",
                    f"stage_receipt_llvm_built_at_commit={first_commit}",
                    f"stage_receipt_llvm_output_sha256={fingerprint}",
                ],
            )
            # Reused with nothing that says what it was built from: the seal
            # says so, under the status word the receipt has (the word does
            # not depend on the LLVM, and promotion does not make it).
            (self.llvm_out(root) / ".trust-llvm-build-record.json").unlink()
            verdict, receipt, printed = self.llvm_build(
                root, stage_root, invocation=self.SEED_INVOCATION
            )
            self.assertTrue(verdict, printed)
            self.assertEqual(
                llvm_lines(stage_root),
                [
                    "stage_receipt_llvm=in-tree",
                    "stage_receipt_llvm_identity=not-stated",
                    "stage_receipt_llvm_provenance=reused",
                    f"stage_receipt_llvm_source_sha256={source['identity_sha256']}",
                    f"stage_receipt_llvm_source_tree={'3' * 40}",
                    "stage_receipt_llvm_built_at_commit=not-recorded",
                    f"stage_receipt_llvm_output_sha256={fingerprint}",
                ],
            )
            self.assertIn("stage_receipt_status=release-ready", reader.lines(stage_root, self.commit))

            # REQUIRING THE IDENTITY is a question of its own, which
            # `promote-toolchain.sh --require-llvm-identity` asks through this
            # reader: exit 3 and nothing on stdout for a stage that is
            # recordable and does not state its LLVM.
            def asked(*argv):
                out, err = io.BytesIO(), io.StringIO()
                with patch.object(sys, "stdout", SimpleNamespace(buffer=out)), patch.object(
                    sys, "stderr", err
                ):
                    status = reader.main([*argv, str(stage_root), self.commit])
                return status, out.getvalue().decode("utf-8"), err.getvalue()

            unstated = (
                "its tool-provenance.json says the identity is not stated (mode in-tree, provenance "
                f"reused): build/{self.host}/llvm was reused, and it holds no build record "
                "(.trust-llvm-build-record.json): it was built before the recreator wrote one, by "
                "a plain x.py build, or over a directory that was already there"
            )
            self.assertEqual(reader.llvm_identity_unstated(stage_root), unstated)
            recorded = "\n".join(reader.lines(stage_root, self.commit)) + "\n"
            self.assertEqual(asked(), (0, recorded, ""))
            self.assertEqual(
                asked("--require-llvm-identity"),
                (
                    3,
                    "",
                    f"stage_receipt_provenance: {stage_root} does not state which LLVM it carries: "
                    f"{unstated}\n",
                ),
            )
            # A receipt from before the record, and a stage with no receipt.
            receipt_path = stage_root / "tool-provenance.json"
            del receipt["llvm_identity"]
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            self.assertEqual(asked()[0], 0)
            status, out, err = asked("--require-llvm-identity")
            self.assertEqual((status, out), (3, ""))
            self.assertIn(
                "its tool-provenance.json holds no llvm_identity record: it was written by a "
                "recreator from before 2026-10-13\n",
                err,
            )
            receipt_path.unlink()
            self.assertEqual(asked(), (0, "stage_receipt=absent\n", ""))
            status, out, err = asked("--require-llvm-identity")
            self.assertEqual((status, out), (3, ""))
            self.assertIn(
                "it carries no tool-provenance.json: no build-time stage evidence was recorded, "
                "or the receipt was removed\n",
                err,
            )
            # A receipt that cannot be recorded at all is that refusal, asked or not.
            receipt_path.write_text("{}\n")
            self.assertEqual(asked()[0], 1)
            self.assertEqual(asked("--require-llvm-identity")[0], 1)
            # And one that states it passes, with the lines.
            receipt_path.unlink()
            shutil.rmtree(self.llvm_out(root))
            self.commit = first_commit
            self.stated_llvm_receipt(root, stage_root)
            self.assertEqual(reader.llvm_identity_unstated(stage_root), "")
            recorded = "\n".join(reader.lines(stage_root, self.commit)) + "\n"
            self.assertIn("stage_receipt_llvm_identity=stated\n", recorded)
            self.assertEqual(asked("--require-llvm-identity"), (0, recorded, ""))
            # The flag is the first argument or it is not the flag: an option
            # in another place is a usage error, never read as a directory or
            # dropped.
            self.assertEqual(asked("--require-llvm-identity", "extra")[0], 2)
            for misplaced in (
                [str(stage_root), "--require-llvm-identity", self.commit],
                [str(stage_root), self.commit, "--require-llvm-identity"],
            ):
                with patch.object(sys, "stderr", io.StringIO()) as usage:
                    self.assertEqual(reader.main(misplaced), 2)
                self.assertIn("usage: stage_receipt_provenance.py [--require-llvm-identity] ", usage.getvalue())
            # Nor is it the commit. In that place it was read as one until the
            # follow-up of 2026-10-13, and a stage without a receipt compares no
            # commit: `DIRECTORY --require-llvm-identity` printed
            # `stage_receipt=absent` and exited 0, without the check it names.
            # Nor is an empty word an operand: as the directory it was read as
            # the current one, and as the commit compared with none (the review
            # of the follow-up, 2026-10-13).
            bare = Path(directory) / "no-receipt"
            bare.mkdir()
            for misplaced in (
                [str(bare), "--require-llvm-identity"],
                [str(stage_root), "--require-llvm-identity"],
                ["--require-llvm-identity", str(bare), "-x"],
                ["", self.commit],
                [str(bare), ""],
                ["--require-llvm-identity", "", self.commit],
            ):
                with self.subTest(misplaced=misplaced):
                    out, usage = io.BytesIO(), io.StringIO()
                    with patch.object(sys, "stdout", SimpleNamespace(buffer=out)), patch.object(
                        sys, "stderr", usage
                    ):
                        status = reader.main(misplaced)
                    self.assertEqual((status, out.getvalue()), (2, b""))
                    self.assertIn("usage: stage_receipt_provenance.py [--require-llvm-identity] ", usage.getvalue())

        # No in-tree LLVM, and no source identity at all: every line still has a value.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage_root, invocation=self.SEED_INVOCATION))
            receipt_path = stage_root / "tool-provenance.json"
            receipt = json.loads(receipt_path.read_text())
            receipt["llvm_identity"] = {
                "schema": "trust.llvm-identity.v1",
                "mode": "unknown",
                "provenance": "unknown",
                "identity_stated": False,
                "reasons": ["could not record the LLVM source identity: not a git repository"],
                "source_identity_sha256": None,
                "source_paths": [],
                "output_dirs": [],
                "output_fingerprint_sha256": None,
                "build_record": None,
            }
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            self.assertEqual(
                llvm_lines(stage_root),
                [
                    "stage_receipt_llvm=unknown",
                    "stage_receipt_llvm_identity=not-stated",
                    "stage_receipt_llvm_provenance=unknown",
                    "stage_receipt_llvm_source_sha256=not-recorded",
                    "stage_receipt_llvm_source_tree=not-recorded",
                    "stage_receipt_llvm_built_at_commit=not-recorded",
                    "stage_receipt_llvm_output_sha256=not-recorded",
                ],
            )
            # An external LLVM (`--llvm-config`): named, NEVER stated, and no id
            # of the checkout's own src/llvm-project stands beside it, because
            # that tree is not what it was built from. The word is the
            # record's, never inferred from its shape.
            receipt["llvm_identity"].update(
                mode="external",
                provenance="external",
                reasons=[recreate_bootstrap.LLVM_EXTERNAL_REASON],
            )
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            self.assertEqual(
                llvm_lines(stage_root),
                [
                    "stage_receipt_llvm=external",
                    "stage_receipt_llvm_identity=not-stated",
                    "stage_receipt_llvm_provenance=external",
                    "stage_receipt_llvm_source_sha256=not-recorded",
                    "stage_receipt_llvm_source_tree=not-recorded",
                    "stage_receipt_llvm_built_at_commit=not-recorded",
                    "stage_receipt_llvm_output_sha256=not-recorded",
                ],
            )
            # `promote-toolchain.sh --require-llvm-identity` refuses it, with
            # the record's own reason.
            self.assertEqual(
                reader.llvm_identity_unstated(stage_root),
                "its tool-provenance.json says the identity is not stated (mode external, "
                f"provenance external): {recreate_bootstrap.LLVM_EXTERNAL_REASON}",
            )
            with patch.object(sys, "stdout", SimpleNamespace(buffer=io.BytesIO())), patch.object(
                sys, "stderr", io.StringIO()
            ):
                self.assertEqual(
                    reader.main(["--require-llvm-identity", str(stage_root), self.commit]), 3
                )
            # The shape the first version of this record gave such a stage
            # (stated, with the checkout's ids beside it) is not recorded at
            # all: promotion refuses the receipt, asked for the identity or not.
            receipt["llvm_identity"].update(
                identity_stated=True,
                reasons=[],
                source_identity_sha256=source["identity_sha256"],
                source_paths=source["paths"],
            )
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            with self.assertRaises(reader.StageReceiptError) as refused:
                reader.lines(stage_root, self.commit)
            self.assertIn("llvm_identity states the identity of an external LLVM", str(refused.exception))
            self.assertIn("llvm_identity of an external LLVM carries a source identity", str(refused.exception))
            # A receipt without the record: one line, and its own word.
            del receipt["llvm_identity"]
            receipt["status"] = "release-ready"
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            self.assertEqual(llvm_lines(stage_root), ["stage_receipt_llvm=not-recorded"])
            self.assertEqual(reader.LLVM_NOT_RECORDED, "not-recorded")
            self.assertNotIn(reader.LLVM_NOT_RECORDED, reader.LLVM_PROVENANCE_OF_MODE)

    def test_promotion_reads_the_receipt_this_script_writes(self):
        # scripts/promote-toolchain.sh names the stage receipt in a seal's
        # PROVENANCE through scripts/lib/stage_receipt_provenance.py. The fixture
        # for that reader's own test (promote_toolchain_test.sh) is written by
        # hand; this is the receipt the recreator really writes, read by it.
        reader = load_stage_receipt_reader()
        seed_before = self.bootstrap_lineage(hydrated=False, admission_status="internal-admitted")
        seed_after = self.bootstrap_lineage(hydrated=True, admission_status="internal-admitted")
        genesis = self.bootstrap_lineage(status="local_genesis")
        cases = (
            (
                "a fresh seed build",
                {"bootstrap_before": seed_before, "bootstrap_after": seed_after,
                 "invocation": self.SEED_INVOCATION},
                ["internal-release-ready", "seed", "true", "fresh-from-validated-archives",
                 "--stage 2 --require-seed --fresh-seed --no-register"],
            ),
            (
                "a seed that was already extracted",
                {"bootstrap_before": seed_after, "bootstrap_after": seed_after,
                 "invocation": ["--require-seed", "--llvm-config", "/opt/llvm 22/bin/llvm-config"]},
                ["candidate-ready", "seed", "true", "preexisting-unproven",
                 "--require-seed --llvm-config '/opt/llvm 22/bin/llvm-config'"],
            ),
            (
                "a genesis build",
                {"bootstrap_before": genesis, "bootstrap_after": genesis,
                 "invocation": ["--genesis"]},
                ["candidate-ready", "genesis", "false", "not-applicable", "--genesis"],
            ),
            (
                "a receipt written before the record existed",
                {"bootstrap_before": seed_before, "bootstrap_after": seed_after},
                ["internal-release-ready", "seed", "true", "fresh-from-validated-archives",
                 "not-recorded"],
            ),
            # A publicly promoted seed: the status is the receipt's word, not
            # the internal one a release status could be folded into.
            (
                "a public release build",
                {"bootstrap_before": self.bootstrap_lineage(hydrated=False),
                 "bootstrap_after": self.bootstrap_lineage(hydrated=True),
                 "invocation": self.SEED_INVOCATION},
                ["release-ready", "seed", "true", "fresh-from-validated-archives",
                 "--stage 2 --require-seed --fresh-seed --no-register"],
            ),
            # Trust-from-Trust and NOT a seed: the mode is not to be read off
            # the flag, and a build with no seed materialized none.
            (
                "a build from the stage0 an installed pack ships",
                {"bootstrap_before": self.atpkg_lineage(), "bootstrap_after": self.atpkg_lineage(),
                 "invocation": ["--stage", "2", "--no-register"]},
                ["candidate-ready", "atpkg", "true", "not-applicable",
                 "--stage 2 --no-register"],
            ),
            # A fresh seed whose selected host record is a fixed point of an
            # unpinned host chain (docs/PLAN.md PKG-S6): graded below a release,
            # and its PROVENANCE says what admitted that seed.
            (
                "a fresh seed build from a fixed-point host record",
                {"bootstrap_before": self.with_host_record(seed_before, "fixed-point"),
                 "bootstrap_after": self.with_host_record(seed_after, "fixed-point"),
                 "invocation": self.SEED_INVOCATION},
                ["unpinned-root-seed-ready", "seed", "true", "fresh-from-validated-archives",
                 "--stage 2 --require-seed --fresh-seed --no-register"],
            ),
        )
        self.assertEqual(
            {mode for _label, _audit, (_status, mode, *_rest) in cases}, set(reader.LINEAGE_OF_MODE)
        )
        self.assertEqual(
            {status for _label, _audit, (status, *_rest) in cases}, set(reader.ACCEPTED_STATUSES)
        )
        for label, audit, (status, mode, trust, materialization, argv) in cases:
            with self.subTest(label), tempfile.TemporaryDirectory() as directory, patch.object(
                recreate_bootstrap, "_atpkg_authority_ready",
                side_effect=lambda authority: authority == self.atpkg_lineage()["atpkg_authority"],
            ):
                root, stage_root, bindir, _tools_dir = self.layout(directory)
                self.assertTrue(self.run_audit(root, stage_root, **audit))
                receipt_path = stage_root / "tool-provenance.json"
                bound = len(recreate_bootstrap.STAGE_TOOL_PRODUCERS) + 4
                self.assertEqual(
                    reader.lines(stage_root, self.commit),
                    [
                        "stage_receipt=tool-provenance.json",
                        "stage_receipt_sha256="
                        + hashlib.sha256(receipt_path.read_bytes()).hexdigest(),
                        "stage_receipt_schema=trust.stage-tool-provenance.v2",
                        f"stage_receipt_status={status}",
                        f"stage_receipt_lineage_mode={mode}",
                        f"stage_receipt_trust_from_trust={trust}",
                        f"stage_receipt_seed_materialization={materialization}",
                        # Only the fixed-point kind adds lines; every other
                        # receipt's are what they were.
                        *(self.FIXED_POINT_PROVENANCE if status == "unpinned-root-seed-ready" else []),
                        f"stage_receipt_files_verified={bound}",
                        # None of these audits was handed an LLVM observation,
                        # as no audit was before 2026-10-13.
                        "stage_receipt_llvm=not-recorded",
                        f"stage_receipt_recreator_argv={argv}",
                    ],
                )
                # It is the receipt of THESE files: a tool that changed since, or
                # another commit, and promotion refuses it.
                with self.assertRaisesRegex(reader.StageReceiptError, "names source commit"):
                    reader.lines(stage_root, "2" * 40)
                (bindir / "ty").unlink()
                self.executable(bindir / "ty", b"rebuilt after the receipt was written")
                with self.assertRaisesRegex(reader.StageReceiptError, "for tool ty "):
                    reader.lines(stage_root, self.commit)

        # A receipt this script REJECTED is still written (and main() exits
        # nonzero); promotion refuses to record it.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, bindir, _tools_dir = self.layout(directory)
            (bindir / "rustdoc").unlink()
            output = io.StringIO()
            with patch("sys.stdout", output):
                self.assertFalse(self.run_audit(root, stage_root, invocation=self.SEED_INVOCATION))
            with self.assertRaisesRegex(reader.StageReceiptError, "its own writer rejected this stage"):
                reader.lines(stage_root, self.commit)

    def test_promotion_refuses_a_receipt_it_must_not_record(self):
        # One row per check of the reader, each on the receipt this script
        # writes with ONE thing wrong. promote_toolchain_test.sh drives a
        # handful of these through the sealing script itself; every check has
        # its row here, so none can be dropped unseen.
        reader = load_stage_receipt_reader()
        seed_before = self.bootstrap_lineage(hydrated=False, admission_status="internal-admitted")
        seed_after = self.bootstrap_lineage(hydrated=True, admission_status="internal-admitted")
        stage = f"build/{self.host}/stage2"

        def tool(receipt, name="ty"):
            return next(row for row in receipt["tools"] if row["name"] == name)

        def set_in(*keys_then_value):
            *keys, value = keys_then_value

            def mutate(receipt):
                target = receipt
                for key in keys[:-1]:
                    target = target[key]
                target[keys[-1]] = value
            return mutate

        def drop(*keys):
            def mutate(receipt):
                target = receipt
                for key in keys[:-1]:
                    target = target[key]
                del target[keys[-1]]
            return mutate

        def genesis_with_a_seed(receipt):
            receipt.update(status="candidate-ready", trust_from_trust=False)
            receipt["bootstrap_lineage"].update(
                mode="genesis", status="local_genesis", trust_from_trust=False
            )

        rows = (
            ("another schema", set_in("schema", "trust.stage-tool-provenance.v3"),
             "schema is 'trust.stage-tool-provenance.v3', not trust.stage-tool-provenance.v2"),
            ("no schema", drop("schema"), "schema is None, not trust.stage-tool-provenance.v2"),
            ("a status outside the vocabulary", set_in("status", "ready"),
             "status is 'ready', not one of candidate-ready, internal-release-ready, release-ready"),
            ("a status that is not a word", set_in("status", ["internal-release-ready"]),
             "status is ['internal-release-ready'], not one of"),
            ("rejected by its writer", set_in("status", "rejected"),
             "its own writer rejected this stage (status rejected)"),
            ("ready with a tool binding that is not",
             set_in("tool_binding_status", "rejected"),
             "status is internal-release-ready while tool_binding_status is 'rejected'"),
            ("ready with errors", set_in("errors", ["a tool was replaced"]),
             "status is internal-release-ready while errors is not the empty list"),
            ("another path scope", set_in("path_scope", "absolute"),
             "path_scope is not repository-root-relative"),
            ("a stage root that is not one", set_in("stage_root", "/tmp/stage2"),
             "stage_root is not build/<host>/stage<N>: '/tmp/stage2'"),
            ("no bootstrap lineage", drop("bootstrap_lineage"), "bootstrap_lineage is not an object"),
            ("another lineage schema",
             set_in("bootstrap_lineage", "schema", "trust.bootstrap-lineage.v2"),
             "bootstrap_lineage.schema is not trust.bootstrap-lineage.v1"),
            ("a lineage mode outside the vocabulary",
             set_in("bootstrap_lineage", "mode", "stock"),
             "bootstrap_lineage.mode is 'stock', not one of seed, atpkg, genesis"),
            ("a lineage mode that is not a word", set_in("bootstrap_lineage", "mode", ["seed"]),
             "bootstrap_lineage.mode is ['seed'], not one of seed, atpkg, genesis"),
            ("a seed lineage that is not Trust-from-Trust",
             set_in("bootstrap_lineage", "status", "local_genesis"),
             "bootstrap_lineage says mode seed with status 'local_genesis' and trust_from_trust "
             "True; a seed lineage is trust_from_trust with trust_from_trust True"),
            ("a lineage flag that is a number", set_in("bootstrap_lineage", "trust_from_trust", 1),
             "bootstrap_lineage says mode seed with status 'trust_from_trust' and trust_from_trust 1"),
            ("a lineage with errors",
             set_in("bootstrap_lineage", "errors", ["bootstrap configuration changed"]),
             "bootstrap_lineage.errors is not the empty list"),
            ("a receipt flag its lineage contradicts", set_in("trust_from_trust", False),
             "trust_from_trust disagrees with bootstrap_lineage.trust_from_trust"),
            ("a seed materialization outside the vocabulary",
             set_in("bootstrap_lineage", "validated_seed", "materialization_status", "fresh"),
             "bootstrap_lineage.validated_seed.materialization_status is 'fresh', not one of "
             "fresh-from-validated-archives, preexisting-unproven"),
            ("a seed lineage with no seed", set_in("bootstrap_lineage", "validated_seed", None),
             "bootstrap_lineage.validated_seed.materialization_status is None, not one of"),
            ("a genesis lineage with a seed", genesis_with_a_seed,
             "a genesis bootstrap_lineage carries a validated_seed"),
            ("release-ready on a seed that was already extracted",
             set_in("bootstrap_lineage", "validated_seed", "materialization_status",
                    "preexisting-unproven"),
             "status is internal-release-ready, which needs a freshly materialized Trust seed, "
             "while its lineage says mode seed, trust_from_trust true, seed materialization "
             "preexisting-unproven"),
            ("another commit", set_in("compiler", "source_commit", "2" * 40),
             "it names source commit '" + "2" * 40 + "'; this tree's compiler reports " + self.commit),
            ("tools that are not a list", set_in("tools", {}), "tools is not a non-empty list"),
            ("no tool rows", set_in("tools", []), "tools is not a non-empty list"),
            ("a tool row with no name", lambda receipt: tool(receipt).pop("name"),
             "] is not a named tool row"),
            ("a tool named twice", lambda receipt: receipt["tools"].append(dict(tool(receipt))),
             "tools names ty twice"),
            ("a tool hash that is not one", lambda receipt: tool(receipt).update(sha256="unknown"),
             "tools[ty].sha256 is not a sha256: 'unknown'"),
            ("a tool that is not bound", lambda receipt: tool(receipt).update(status="mismatch"),
             "tools[ty].status is 'mismatch'"),
            ("a bound tool whose producer has other bytes",
             lambda receipt: tool(receipt).update(producer_sha256="0" * 64),
             "tools[ty].status is 'bound' with producer_sha256 '" + "0" * 64 + "'"),
            ("another tool's bytes",
             lambda receipt: tool(receipt).update(sha256="0" * 64, producer_sha256="0" * 64),
             "it records sha256 " + "0" * 64 + f" for tool ty ({stage}/bin/ty); the file in "),
            ("a tool path outside the stage",
             lambda receipt: tool(receipt).update(path=f"build/{self.host}/stage1/bin/ty"),
             f"the path of tool ty is not under the receipt's stage_root {stage}"),
            ("a tool path that climbs out",
             lambda receipt: tool(receipt).update(path=f"{stage}/bin/../../stage1/bin/trustc"),
             "the path of tool ty is not a plain relative path"),
            ("a tool path that is the stage itself",
             lambda receipt: tool(receipt).update(path=f"{stage}/"),
             "the path of tool ty is not a plain relative path"),
            ("a tool path with a doubled separator",
             lambda receipt: tool(receipt).update(path=f"{stage}/bin//ty"),
             "the path of tool ty is not a plain relative path"),
            ("a tool path with a line break in it",
             lambda receipt: tool(receipt).update(path=f"{stage}/bin/ty\n"),
             "the path of tool ty is not a plain relative path"),
            ("a tool path that is not a string", lambda receipt: tool(receipt).update(path=None),
             f"the path of tool ty is not under the receipt's stage_root {stage}: None"),
            ("a tool the stage does not have",
             lambda receipt: tool(receipt).update(path=f"{stage}/bin/ty-of-another-build"),
             f"tool ty ({stage}/bin/ty-of-another-build) cannot be read in "),
            ("a tool path that is a directory",
             lambda receipt: tool(receipt).update(path=f"{stage}/bin"),
             f"tool ty ({stage}/bin) is not a regular file in "),
            ("no compiler", drop("compiler"), "compiler is not an object"),
            ("a compiler hash that is not one", set_in("compiler", "compiler_sha256", "0" * 63),
             "compiler.compiler_sha256 is not a sha256"),
            ("another compiler's bytes", set_in("compiler", "compiler_sha256", "0" * 64),
             "it records sha256 " + "0" * 64 + f" for the compiler ({stage}/bin/trustc)"),
            ("another rustc name", set_in("compiler", "compatibility_alias_sha256", "0" * 64),
             f"for the compiler's rustc name ({stage}/bin/rustc)"),
            ("no rustdoc name", drop("rustdoc_alias"), "rustdoc_alias is not an object"),
            ("another rustdoc name", set_in("rustdoc_alias", "sha256", "0" * 64),
             f"for the rustdoc name ({stage}/bin/rustdoc)"),
            ("no proc-macro helper", drop("proc_macro_helper"), "proc_macro_helper is not an object"),
            ("another proc-macro helper", set_in("proc_macro_helper", "sha256", "0" * 64),
             f"for the proc-macro helper ({stage}/libexec/trust-analyzer-proc-macro-srv)"),
        )
        labels = [label for label, _mutate, _message in rows]
        self.assertEqual(len(labels), len(set(labels)))
        for label, mutate, message in rows:
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                self.assertTrue(
                    self.run_audit(
                        root, stage_root, bootstrap_before=seed_before, bootstrap_after=seed_after,
                        invocation=self.SEED_INVOCATION,
                    )
                )
                receipt_path = stage_root / "tool-provenance.json"
                # Not vacuous: untouched, this receipt is one the reader records.
                self.assertEqual(len(reader.lines(stage_root, self.commit)), 10)
                receipt = json.loads(receipt_path.read_text())
                mutate(receipt)
                receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
                with self.assertRaises(reader.StageReceiptError) as refused:
                    reader.lines(stage_root, self.commit)
                self.assertIn(message, str(refused.exception))

        # What is wrong with the FILE rather than with a field of it.
        def as_text(text):
            return lambda receipt_path: receipt_path.write_text(text)

        def as_link(receipt_path):
            elsewhere = receipt_path.parent.parent / "receipt-of-another-stage.json"
            receipt_path.rename(elsewhere)
            receipt_path.symlink_to(elsewhere)

        def as_directory(receipt_path):
            receipt_path.unlink()
            receipt_path.mkdir()

        def repeating_a_key(receipt_path):
            receipt_path.write_text('{"status": "candidate-ready",' + receipt_path.read_text()[1:])

        files = (
            ("cut short", lambda receipt_path: receipt_path.write_text(receipt_path.read_text()[:400]),
             "it is not JSON"),
            ("not UTF-8", lambda receipt_path: receipt_path.write_bytes(b"\xff\xfe{}"), "it is not JSON"),
            ("a list", as_text("[]\n"), "it is not a JSON object"),
            ("a number that is not JSON", as_text('{"stage": NaN}\n'), "it holds NaN, which is not JSON"),
            ("a key twice", repeating_a_key, "it repeats the key 'status'"),
            ("a link to a receipt", as_link, "it is not a regular file"),
            ("a directory", as_directory, "it is not a regular file"),
        )
        for label, damage, message in files:
            with self.subTest(label), tempfile.TemporaryDirectory() as directory:
                root, stage_root, _bindir, _tools_dir = self.layout(directory)
                self.assertTrue(self.run_audit(root, stage_root, invocation=self.SEED_INVOCATION))
                receipt_path = stage_root / "tool-provenance.json"
                self.assertEqual(len(reader.lines(stage_root, self.commit)), 10)
                damage(receipt_path)
                with self.assertRaises(reader.StageReceiptError) as refused:
                    reader.lines(stage_root, self.commit)
                self.assertIn(message, str(refused.exception))

        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, _bindir, _tools_dir = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage_root, invocation=self.SEED_INVOCATION))
            receipt_path = stage_root / "tool-provenance.json"
            # The commit comes from the tree's own compiler: an abbreviated or
            # empty one is not something a receipt can be held to.
            for commit in ("", self.commit[:9], self.commit.upper().replace("1", "A")):
                with self.subTest(commit=commit), self.assertRaisesRegex(
                    reader.StageReceiptError, "is not a full object id"
                ):
                    reader.lines(stage_root, commit)
            with patch.object(reader, "MAX_RECEIPT_BYTES", receipt_path.stat().st_size - 1), \
                    self.assertRaisesRegex(reader.StageReceiptError, "bytes, more than"):
                reader.lines(stage_root, self.commit)
            # No receipt at all is not an error: the stage was not built by this script.
            receipt_path.unlink()
            self.assertEqual(reader.lines(stage_root, self.commit), ["stage_receipt=absent"])

        # The command line a seal's PROVENANCE runs: one exit status per outcome,
        # and a refusal prints the reason and no line to record.
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, bindir, _tools_dir = self.layout(directory)
            self.assertTrue(self.run_audit(root, stage_root, invocation=self.SEED_INVOCATION))

            def run_reader(*arguments):
                return subprocess.run(
                    [sys.executable, "-B", str(STAGE_RECEIPT_READER), *arguments],
                    capture_output=True, text=True, timeout=60, check=False,
                )

            recorded = run_reader(str(stage_root), self.commit)
            self.assertEqual((recorded.returncode, recorded.stderr), (0, ""))
            self.assertEqual(recorded.stdout.splitlines(), reader.lines(stage_root, self.commit))
            (bindir / "ty").unlink()
            self.executable(bindir / "ty", b"rebuilt after the receipt was written")
            refused = run_reader(str(stage_root), self.commit)
            self.assertEqual((refused.returncode, refused.stdout), (1, ""))
            self.assertIn("is not a receipt to record: it records sha256 ", refused.stderr)
            self.assertEqual(run_reader(str(stage_root)).returncode, 2)
            self.assertEqual(run_reader(str(stage_root / "absent"), self.commit).returncode, 2)

    def test_promotion_knows_the_words_this_script_gives_a_receipt(self):
        # The reader's vocabulary is closed, so a status or lineage word it does
        # not know stops a seal. Hold its lists to the two functions that choose
        # the words, in both directions.
        reader = load_stage_receipt_reader()
        seen = set()
        seeds = [None]
        for seed_status in ("validated", "validated-payloads"):
            for materialization in (*reader.SEED_MATERIALIZATIONS, None):
                for admission in ("public-promoted", "internal-admitted", "unadmitted"):
                    seeds.append(
                        {
                            "status": seed_status,
                            "materialization_status": materialization,
                            "admission_status": admission,
                        }
                    )
        # And by the kind of host record the seed capture selected: none (a
        # single-host ledger), a mint, or a fixed point (docs/PLAN.md PKG-S6).
        seeds += [
            self.with_host_record({"validated_seed": seed}, kind)["validated_seed"]
            for seed in seeds[1:] for kind in ("mint", "fixed-point")
        ]
        for source_status in ("immutable_release", "development_source"):
            for mode, (lineage_status, trust) in reader.LINEAGE_OF_MODE.items():
                for seed in seeds:
                    status = recreate_bootstrap._classify_receipt_status(
                        source_status, {"status": lineage_status, "validated_seed": seed}
                    )
                    seen.add(status)
                    if status in reader.RELEASE_STATUSES:
                        self.assertTrue(
                            reader.release_status_holds(
                                mode, trust, seed and seed["materialization_status"]
                            ),
                            (status, source_status, mode, seed),
                        )
                    fixed_point = seed is not None and "authority" in seed and (
                        reader.selected_host_record(seed, self.host)["schema"]
                        == reader.FIXED_POINT_HOST_RECORD_SCHEMA
                    )
                    # A fixed point never reaches a release status, and its
                    # grade is given to nothing else.
                    if fixed_point:
                        self.assertNotIn(status, reader.RELEASE_STATUSES, (source_status, mode, seed))
                    if status == reader.UNPINNED_ROOT_STATUS:
                        self.assertTrue(fixed_point, (source_status, mode, seed))
                        self.assertTrue(
                            reader.release_status_holds(mode, trust, seed["materialization_status"]),
                            (status, source_status, mode, seed),
                        )
        self.assertEqual(seen, {*reader.ACCEPTED_STATUSES, reader.REJECTED_STATUS})
        self.assertNotIn(reader.REJECTED_STATUS, reader.ACCEPTED_STATUSES)
        self.assertEqual(len(reader.ACCEPTED_STATUSES), len(set(reader.ACCEPTED_STATUSES)))
        self.assertLessEqual(set(reader.RELEASE_STATUSES), set(reader.ACCEPTED_STATUSES))

        seed_bound = recreate_bootstrap._bind_bootstrap_lineage(
            self.bootstrap_lineage(hydrated=False), self.bootstrap_lineage(hydrated=True)
        )
        preexisting = recreate_bootstrap._bind_bootstrap_lineage(
            self.bootstrap_lineage(hydrated=True), self.bootstrap_lineage(hydrated=True)
        )
        genesis_bound = recreate_bootstrap._bind_bootstrap_lineage(
            self.bootstrap_lineage(status="local_genesis"),
            self.bootstrap_lineage(status="local_genesis"),
        )
        atpkg = self.atpkg_lineage()
        with patch.object(recreate_bootstrap, "_atpkg_authority_ready", return_value=True):
            atpkg_bound = recreate_bootstrap._bind_bootstrap_lineage(atpkg, atpkg)
        bound_modes = set()
        for bound in (seed_bound, preexisting, genesis_bound, atpkg_bound):
            self.assertEqual(bound["errors"], [], bound)
            self.assertEqual(
                (bound["status"], bound["trust_from_trust"]),
                reader.LINEAGE_OF_MODE[bound["mode"]],
            )
            bound_modes.add(bound["mode"])
        self.assertEqual(bound_modes, set(reader.LINEAGE_OF_MODE))
        self.assertEqual(
            {
                seed_bound["validated_seed"]["materialization_status"],
                preexisting["validated_seed"]["materialization_status"],
            },
            set(reader.SEED_MATERIALIZATIONS),
        )
        self.assertEqual(
            seed_bound["validated_seed"]["materialization_status"], reader.FRESH_SEED
        )

    def test_a_fixed_point_seed_is_graded_below_every_release(self):
        """docs/PLAN.md PKG-S6: a build from a seed whose selected host record is
        the fixed-point kind is `unpinned-root-seed-ready`, which no release status
        names; a mint record, and a capture without host records, keep theirs."""
        reader = load_stage_receipt_reader()
        helper = recreate_bootstrap.seed_host_ledger_module()
        fp = helper.fixed_point_module()
        # Each side's words are its sources'.
        self.assertEqual(recreate_bootstrap.FIXED_POINT_HOST_RECORD_SCHEMA, helper.FIXED_POINT_SCHEMA)
        self.assertEqual(reader.FIXED_POINT_HOST_RECORD_SCHEMA, helper.FIXED_POINT_SCHEMA)
        self.assertEqual(reader.FIXED_POINT_ADMISSION_KIND, fp.KIND)
        self.assertEqual(reader.UNPINNED_ROOT_STATUS, recreate_bootstrap.UNPINNED_ROOT_SEED_READY)
        # The hosts a single-host ledger never admits are the native Linux hosts.
        self.assertEqual(recreate_bootstrap.LINUX_SEED_HOSTS, helper.initialization_module().LINUX_HOSTS)
        self.assertEqual(reader.LINUX_SEED_HOSTS, helper.initialization_module().LINUX_HOSTS)
        disclosed = {**dict(fp.DISCLOSURE), "stock_built_ancestor": fp.STOCK_ANCESTOR}
        for key, value in reader.FIXED_POINT_DISCLOSED:
            self.assertEqual(disclosed[key], value, key)
            self.assertIn(key, fp.DISCLOSED)
        # promote-toolchain.sh's --lineage check holds a root.pin_admission to the same words.
        promoter = (Path(__file__).resolve().parents[1] / "promote-toolchain.sh").read_text()
        literal = re.search(r"^fixed_point_disclosed = (\{.*?\})$", promoter, re.MULTILINE | re.DOTALL)
        self.assertIsNotNone(literal, "promote-toolchain.sh names no fixed_point_disclosed")
        self.assertEqual(ast.literal_eval(literal.group(1)), dict(reader.FIXED_POINT_DISCLOSED))
        self.assertIn(reader.UNPINNED_ROOT_STATUS, reader.ACCEPTED_STATUSES)
        self.assertNotIn(reader.UNPINNED_ROOT_STATUS, reader.RELEASE_STATUSES)

        def fresh(admission):
            return {"status": "trust_from_trust", "validated_seed": {
                "status": "validated", "materialization_status": reader.FRESH_SEED,
                "admission_status": admission}}

        def grade(lineage):
            return recreate_bootstrap._classify_receipt_status("immutable_release", lineage)

        for admission, release in (("internal-admitted", "internal-release-ready"),
                                   ("public-promoted", "release-ready")):
            with self.subTest(admission=admission):
                self.assertEqual(grade(fresh(admission)), release)
                self.assertEqual(grade(self.with_host_record(fresh(admission), "mint")), release)
        fixed = self.with_host_record(fresh("internal-admitted"), "fixed-point")
        self.assertEqual(grade(fixed), "unpinned-root-seed-ready")
        # A public promotion of an unpinned root is no grade at all.
        self.assertEqual(grade(self.with_host_record(fresh("public-promoted"), "fixed-point")), "rejected")
        self.assertEqual(grade(self.with_host_record(fresh("unadmitted"), "fixed-point")), "rejected")
        preexisting = copy.deepcopy(fixed)
        preexisting["validated_seed"]["materialization_status"] = "preexisting-unproven"
        self.assertEqual(grade(preexisting), "candidate-ready")
        self.assertEqual(recreate_bootstrap._classify_receipt_status("development_source", fixed),
                         "candidate-ready")
        # Host records that name no readable selected record: the kind is unknown,
        # and the grade is not guessed.
        for label, change in (
            ("another selected host", lambda records: records.update(selected_host="other-host")),
            ("records that are not a table", lambda records: records.update(records=[])),
            ("a record without a schema",
             lambda records: records["records"][self.host].pop("schema")),
            ("host records that are not a table", None),
        ):
            with self.subTest(label):
                changed = copy.deepcopy(fixed)
                ledger = changed["validated_seed"]["authority"]["seed_ledger"]
                if change is None:
                    ledger["host_records"] = ["not", "a", "table"]
                else:
                    change(ledger["host_records"])
                self.assertEqual(grade(changed), "rejected")

    def fixed_point_audit(self, directory: str, kind: str = "fixed-point"):
        """A fresh, internally admitted seed build whose seed capture selected a
        host record of `kind`: (root, stage_root, the bound-after lineage)."""
        before = self.with_host_record(
            self.bootstrap_lineage(hydrated=False, admission_status="internal-admitted"), kind)
        after = self.with_host_record(
            self.bootstrap_lineage(hydrated=True, admission_status="internal-admitted"), kind)
        root, stage_root, _bindir, _tools_dir = self.layout(directory)
        self.assertTrue(self.run_audit(root, stage_root, bootstrap_before=before, bootstrap_after=after,
                                       invocation=self.SEED_INVOCATION))
        return root, stage_root, after

    def test_a_fixed_point_receipt_is_no_immutable_lineage(self):
        reader = load_stage_receipt_reader()
        with tempfile.TemporaryDirectory() as directory:
            root, stage_root, after = self.fixed_point_audit(directory)
            receipt_path = stage_root / "tool-provenance.json"
            receipt = json.loads(receipt_path.read_text())
            self.assertEqual(receipt["status"], "unpinned-root-seed-ready")
            self.assertEqual(receipt["errors"], [])
            shown = io.StringIO()
            with patch("sys.stdout", shown):
                self.assertTrue(self.verify_receipt(root, stage_root, self.lineage(), bootstrap=after))
                self.assertFalse(self.verify_receipt(root, stage_root, self.lineage(), bootstrap=after,
                                                     require_immutable_lineage=True))
                self.assertFalse(self.verify_receipt(root, stage_root, self.lineage(), bootstrap=after,
                                                     require_public_release=True))
            self.assertIn("verified existing stage provenance (unpinned-root-seed-ready)", shown.getvalue())
            self.assertIn("immutable Trust-from-Trust lineage is required but this receipt is not an "
                          "immutable internal/public release", shown.getvalue())
            # The same receipt claiming a release status: the verifier re-derives
            # the grade, and promotion's reader refuses the pairing.
            for claimed in reader.RELEASE_STATUSES:
                with self.subTest(claimed=claimed):
                    receipt["status"] = claimed
                    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
                    refused = io.StringIO()
                    with patch("sys.stdout", refused):
                        self.assertFalse(self.verify_receipt(root, stage_root, self.lineage(), bootstrap=after))
                    self.assertIn("receipt readiness classification disagrees with current binding/lineage",
                                  refused.getvalue())
                    with self.assertRaisesRegex(
                            reader.StageReceiptError,
                            f"status is {claimed}, a release status, while its seed's selected host record "
                            "is the fixed-point kind"):
                        reader.lines(stage_root, self.commit)

    def test_promotion_reads_a_fixed_point_seed_and_refuses_its_contradictions(self):
        reader = load_stage_receipt_reader()
        with tempfile.TemporaryDirectory() as directory:
            _root, stage_root, _after = self.fixed_point_audit(directory)
            receipt_path = stage_root / "tool-provenance.json"
            original = receipt_path.read_text()
            lines = reader.lines(stage_root, self.commit)
            self.assertEqual(lines[3], "stage_receipt_status=unpinned-root-seed-ready")
            self.assertEqual(lines[7:9], self.FIXED_POINT_PROVENANCE)

            def record(receipt):
                return receipt["bootstrap_lineage"]["validated_seed"]["authority"]["seed_ledger"][
                    "host_records"]["records"][self.host]

            def disclose(key, value):
                return lambda receipt: record(receipt)["root_disclosure"].__setitem__(key, value)

            def host_records(receipt):
                return receipt["bootstrap_lineage"]["validated_seed"]["authority"]["seed_ledger"]["host_records"]

            def as_mint(*kept):
                """The selected record turned into a mint record that keeps `kept` of the
                fixed point's admission_kind and root_disclosure."""
                def mutate(receipt):
                    for key in ("admission_kind", "root_disclosure"):
                        if key not in kept:
                            record(receipt).pop(key)
                    record(receipt)["schema"] = "trust-seed-host-record-v1"
                return mutate

            def reselect(receipt):
                # The selection re-pointed at another host's mint record, with its grade.
                host_records(receipt)["records"]["aarch64-apple-darwin"] = {
                    "schema": "trust-seed-host-record-v1", "host": "aarch64-apple-darwin",
                    "mint": {"self_host_proof": "pass"}}
                host_records(receipt)["selected_host"] = "aarch64-apple-darwin"
                receipt["status"] = "internal-release-ready"

            def single_host(host):
                # A capture that held no host record (a single-host ledger), graded a release.
                def mutate(receipt):
                    receipt["host"] = host
                    receipt["bootstrap_lineage"]["validated_seed"]["authority"].pop("seed_ledger")
                    receipt["status"] = "internal-release-ready"
                return mutate

            mint_with_fixed_point_words = (
                "is a trust-seed-host-record-v1 record and carries the fixed-point kind's root_disclosure or "
                "admission_kind, which only that kind is admitted with")
            rows = (
                ("a mint record given the fixed-point grade", as_mint(),
                 "only a build from a seed whose selected host record is the fixed-point kind is given; "
                 "this receipt's seed is a trust-seed-host-record-v1 record"),
                ("a mint record that keeps the fixed point's disclosure", as_mint("root_disclosure"),
                 mint_with_fixed_point_words),
                ("a mint record that keeps the fixed point's admission kind", as_mint("admission_kind"),
                 mint_with_fixed_point_words),
                ("a mint record with both, graded a release",
                 lambda receipt: (as_mint("admission_kind", "root_disclosure")(receipt),
                                  receipt.update(status="internal-release-ready")),
                 mint_with_fixed_point_words),
                ("the selection re-pointed at another host's mint record, graded a release", reselect,
                 "host_records.selected_host is 'aarch64-apple-darwin', not this receipt's host 'test-host'"),
                ("a selected record that names another host",
                 lambda receipt: record(receipt).update(host="other-host"),
                 f"host_records.records['{self.host}'] says host 'other-host': the selected record is not "
                 "that host's"),
                ("a Linux seed with no host record, graded a release", single_host("aarch64-unknown-linux-gnu"),
                 "its seed lineage on aarch64-unknown-linux-gnu holds no host record (a single-host seed "
                 "ledger), which never admits a Linux host"),
                ("an x86_64 Linux seed with no host record, graded a release",
                 single_host("x86_64-unknown-linux-gnu"), "which never admits a Linux host"),
                ("no host records with the fixed-point grade",
                 lambda receipt: receipt["bootstrap_lineage"]["validated_seed"]["authority"].pop("seed_ledger"),
                 "this receipt's seed is no such record"),
                ("host records naming no readable selection",
                 lambda receipt: receipt["bootstrap_lineage"]["validated_seed"]["authority"]["seed_ledger"][
                     "host_records"].update(selected_host="other-host"),
                 "names no selected host record with a schema"),
                ("the grade on a seed that was already extracted",
                 lambda receipt: receipt["bootstrap_lineage"]["validated_seed"].update(
                     materialization_status="preexisting-unproven"),
                 "status is unpinned-root-seed-ready, which needs a freshly materialized Trust seed"),
                ("another admission kind", lambda receipt: record(receipt).update(admission_kind="genesis-root"),
                 "has admission_kind 'genesis-root', not fixed-point-unpinned-root"),
                ("no disclosure", lambda receipt: record(receipt).pop("root_disclosure"),
                 "carries no root_disclosure table"),
                ("a pinned root", disclose("root", "pinned"), "discloses root 'pinned'"),
                ("a pinned predecessor", disclose("predecessor_pin", "1" * 40),
                 "discloses predecessor_pin '" + "1" * 40 + "'"),
                ("a diverse double compile", disclose("double_compile_diverse", "true"),
                 "discloses double_compile_diverse 'true'"),
                ("a stock ancestor with a receipt", disclose("stock_built_ancestor", "recorded"),
                 "discloses stock_built_ancestor 'recorded'"),
                ("a disclosure line that is not one word", disclose("root", "unpinned-host-chain\nx=1"),
                 "discloses root 'unpinned-host-chain\\nx=1'"),
            )
            for label, mutate, message in rows:
                with self.subTest(label):
                    receipt = json.loads(original)
                    mutate(receipt)
                    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
                    with self.assertRaises(reader.StageReceiptError) as refused:
                        reader.lines(stage_root, self.commit)
                    self.assertIn(message, str(refused.exception))
            # Not vacuous: the same single-host capture on a host that is not Linux
            # (the format's own, as Darwin's was) still reads as a release.
            receipt = json.loads(original)
            single_host(self.host)(receipt)
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            self.assertIn("stage_receipt_status=internal-release-ready", reader.lines(stage_root, self.commit))
            receipt_path.write_text(original)
            self.assertEqual(reader.lines(stage_root, self.commit), lines)

        # A mint record's receipt reads as one whose capture held no host records:
        # the same ten lines, the receipt's own digest apart.
        read = {}
        for kind in ("mint", None):
            with tempfile.TemporaryDirectory() as directory:
                if kind is None:
                    root, stage_root, _bindir, _tools_dir = self.layout(directory)
                    self.assertTrue(self.run_audit(
                        root, stage_root,
                        bootstrap_before=self.bootstrap_lineage(hydrated=False, admission_status="internal-admitted"),
                        bootstrap_after=self.bootstrap_lineage(hydrated=True, admission_status="internal-admitted"),
                        invocation=self.SEED_INVOCATION))
                else:
                    _root, stage_root, _after = self.fixed_point_audit(directory, kind)
                read[kind] = reader.lines(stage_root, self.commit)
        self.assertEqual(len(read["mint"]), 10)
        self.assertEqual(read["mint"][3], "stage_receipt_status=internal-release-ready")
        self.assertEqual(read["mint"][:1] + read["mint"][2:], read[None][:1] + read[None][2:])


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

    def test_archive_binding_never_rewinds_compressed_seed_bytes(self):
        rewinds = []
        original = lzma.LZMAFile

        class ObservedLZMAFile(original):
            def seek(self, offset, whence=0):
                before = self.tell()
                after = super().seek(offset, whence)
                if after < before:
                    rewinds.append((before, after))
                return after

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pins, payloads = self.seed_archives(root, "test-host")
            errors = []
            with patch.object(lzma, "LZMAFile", ObservedLZMAFile):
                records, _bindings = recreate_bootstrap._capture_seed_archive_members(
                    root, "test-host", pins, payloads, errors
                )
            self.assertEqual(errors, [])
            self.assertEqual(len(records), 13)
            self.assertEqual(rewinds, [], "compressed seeks decompress the seed repeatedly")

    def test_decoded_seed_archive_matches_direct_tar_member_and_link_authority(self):
        for scenario in ("regular", "hardlink", "symlink", "duplicate", "missing", "directory"):
            with self.subTest(scenario=scenario), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                pins, payloads = self.seed_archives(root, "test-host")
                archive = root / str(payloads[0]["path"])
                with tarfile.open(archive, "r:xz") as bundle:
                    entries = [(member, bundle.extractfile(member).read()) for member in bundle]
                if scenario in ("hardlink", "symlink"):
                    alias = entries[1][0]
                    alias.size = 0
                    alias.type = tarfile.LNKTYPE if scenario == "hardlink" else tarfile.SYMTYPE
                    alias.linkname = entries[0][0].name if scenario == "hardlink" else "trustc"
                elif scenario == "duplicate":
                    entries.append(entries[0])
                elif scenario == "missing":
                    entries.pop(0)
                elif scenario == "directory":
                    entries[0][0].type = tarfile.DIRTYPE
                    entries[0][0].size = 0
                with tarfile.open(archive, "w:xz") as bundle:
                    for member, data in entries:
                        bundle.addfile(member, io.BytesIO(data) if member.isfile() else None)

                original_errors = []
                with patch.object(recreate_bootstrap, "_open_seekable_seed_archive",
                                  side_effect=lambda path: tarfile.open(path, "r:xz")):
                    original = recreate_bootstrap._capture_seed_archive_members(
                        root, "test-host", pins, payloads, original_errors
                    )
                decoded_errors = []
                decoded = recreate_bootstrap._capture_seed_archive_members(
                    root, "test-host", pins, payloads, decoded_errors
                )
                self.assertEqual(decoded, original)
                self.assertEqual(decoded_errors, original_errors)
                self.assertEqual(bool(decoded_errors), scenario in ("duplicate", "missing", "directory"))
                if scenario in ("hardlink", "symlink"):
                    bindings = decoded[1]
                    self.assertEqual(bindings["bin/trustc"]["member_sha256"],
                                     bindings["bin/rustc"]["member_sha256"])

    def test_corrupt_seed_compression_and_temporary_storage_failure_refuse(self):
        for scenario in ("invalid", "truncated", "storage"):
            with self.subTest(scenario=scenario), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                pins, payloads = self.seed_archives(root, "test-host")
                archive = root / str(payloads[0]["path"])
                if scenario == "invalid":
                    archive.write_bytes(b"invalid XZ archive")
                elif scenario == "truncated":
                    archive.write_bytes(archive.read_bytes()[:32])
                errors = []
                with ExitStack() as stack:
                    if scenario == "storage":
                        stack.enter_context(patch.object(recreate_bootstrap.tempfile, "TemporaryFile",
                                                         side_effect=OSError("no temporary space")))
                    records, bindings = recreate_bootstrap._capture_seed_archive_members(
                        root, "test-host", pins, payloads, errors
                    )
                self.assertTrue(any("could not inspect seed trustc archive" in error for error in errors))
                self.assertNotIn("bin/trustc", bindings)
                self.assertFalse(any(row["tool"] == "trustc" for row in records))

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
        for name, value in (
            ("CC", "/ambient/compiler"),
            ("CARGOFLAGS", "-Zgit=shallow-deps"),
            ("CARGOFLAGS_BOOTSTRAP", "--target injected"),
            ("CARGOFLAGS_NOT_BOOTSTRAP", "--config injected.toml"),
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory, patch.dict(
                os.environ, {name: value}, clear=True
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
                self.assertEqual(set(authority["ambient_overrides"]), {name})

    def test_build_authority_rejects_language_git_and_python_injection_namespaces(self):
        overrides = recreate_bootstrap._ambient_build_authority_overrides(
            {
                "TRUST_JOBS": "1",
                "LLVM_ZSTD_PC_DIR": "/ambient/native/metadata",
                "RUST_BOOTSTRAP_CONFIG": "/tmp/other.toml",
                "CARGOFLAGS": "-Zgit=shallow-deps",
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
                "LLVM_ZSTD_PC_DIR",
                "RUST_BOOTSTRAP_CONFIG",
                "CARGOFLAGS",
                "CARGOFLAGS_BOOTSTRAP",
                "BOOTSTRAP_SKIP_TARGET_SANITY",
                "GIT_DIR",
                "PYTHONPATH",
                "DYLD_INSERT_LIBRARIES",
            },
        )

    # How the `pkg-config` crate spells a per-target variable, read out of the
    # versions the lockfiles pin (Config::targeted_env_var: 0.3.31 lib.rs:621-630,
    # 0.3.33 lib.rs:650-659, 0.3.34 lib.rs:659-668; the same text in all three).
    # It tries, in this order, <NAME>_<target>, <NAME>_<target with `-` as `_`>,
    # HOST_<NAME> when the build script's HOST equals its TARGET and
    # TARGET_<NAME> when it does not, then <NAME>; and it is called for exactly
    # these names: the executable (`run`), the three handed on to the
    # executable (`command`: search path, replacement search path, sysroot),
    # and the switch that turns probing on for a cross target
    # (`target_supported`).
    PKG_CONFIG_CRATE_NAMES = (
        "PKG_CONFIG",
        "PKG_CONFIG_PATH",
        "PKG_CONFIG_LIBDIR",
        "PKG_CONFIG_SYSROOT_DIR",
        "PKG_CONFIG_ALLOW_CROSS",
    )

    @staticmethod
    def pkg_config_crate_spellings(name, target):
        return (
            f"{name}_{target}",
            f"{name}_{target.replace('-', '_')}",
            f"HOST_{name}",
            f"TARGET_{name}",
            name,
        )

    # What the binary reads itself and a build script only passes through
    # (pkgconf 3.0.8: cli/core.c, libpkgconf/client.c and pkg.c).
    PKG_CONFIG_BINARY_SWITCHES = (
        "PKG_CONFIG_PRELOADED_FILES",
        "PKG_CONFIG_SYSTEM_LIBRARY_PATH",
        "PKG_CONFIG_TOP_BUILD_DIR",
        "PKG_CONFIG_ZLIB_PREFIX",
    )

    def every_pkg_config_spelling(self):
        """Every name the pinned crate can read for the targets built here."""
        targets = {
            recreate_bootstrap.host_triple(),
            *recreate_bootstrap.APPLE_TARGETS,
            "x86_64-unknown-linux-gnu",
            "x86_64-pc-windows-msvc",
        }
        spellings = sorted(
            {
                spelling
                for name in self.PKG_CONFIG_CRATE_NAMES
                for target in targets
                for spelling in self.pkg_config_crate_spellings(name, target)
            }
        )
        # Not vacuous: the hyphen form, the underscore form, HOST_/TARGET_, bare.
        for expected in (
            "PKG_CONFIG_PATH_aarch64-apple-darwin",
            "PKG_CONFIG_PATH_aarch64_apple_darwin",
            "PKG_CONFIG_x86_64-apple-darwin",
            "PKG_CONFIG_x86_64_apple_darwin",
            "HOST_PKG_CONFIG",
            "TARGET_PKG_CONFIG_LIBDIR",
            "HOST_PKG_CONFIG_SYSROOT_DIR",
            "PKG_CONFIG_ALLOW_CROSS_x86_64_apple_darwin",
            "PKG_CONFIG_LIBDIR",
        ):
            self.assertIn(expected, spellings)
        self.assertGreater(len(spellings), 50)
        return spellings

    def test_every_pkg_config_spelling_a_build_script_reads_is_refused_and_scrubbed(self):
        """Not only the four bare names.

        Until 2026-10-12 `HOST_PKG_CONFIG_PATH=/elsewhere` or
        `PKG_CONFIG_aarch64_apple_darwin=/other/pkg-config` passed the capture
        and reached x.py: the first moves the search path of the pkg-config the
        receipt binds, the second runs a different binary altogether.
        """
        spellings = self.every_pkg_config_spelling()
        ambient = {
            name: "/ambient" for name in [*spellings, *self.PKG_CONFIG_BINARY_SWITCHES]
        }

        overrides = recreate_bootstrap._ambient_build_authority_overrides(
            {**ambient, "UNRELATED": "allowed", "PKGCONF": "allowed"}
        )
        self.assertEqual(sorted(overrides), sorted(ambient))

        bound = {
            "name": "tool",
            "status": "bound",
            "resolved_local_path": "/tool",
            "resolved_real_path": "/tool",
            "sha256": "a" * 64,
            "identity": "tool version",
        }
        for spelling in spellings:
            with self.subTest(refused=spelling), tempfile.TemporaryDirectory() as directory, patch.dict(
                os.environ, {spelling: "/ambient"}, clear=True
            ), patch.object(recreate_bootstrap, "which", return_value="/tool"), patch.object(
                recreate_bootstrap, "_native_tool_record", return_value=dict(bound)
            ), patch.object(recreate_bootstrap.platform, "system", return_value="Linux"):
                authority = recreate_bootstrap.capture_build_authority(
                    Path(directory).resolve(), "test-host", None
                )
                self.assertEqual(authority["status"], "rejected")
                self.assertEqual(
                    authority["errors"],
                    [f"ambient build-authority overrides are set: {spelling}"],
                )
                self.assertEqual(set(authority["ambient_overrides"]), {spelling})

        # ... and none of them crosses the process boundary into x.py.
        launched = {}

        def run(_command, *, env, cwd):
            launched.update(env)
            return SimpleNamespace(returncode=0)

        with tempfile.TemporaryDirectory() as directory, patch.dict(
            os.environ, {**ambient, "UNRELATED": "preserved"}, clear=True
        ), patch.object(recreate_bootstrap, "add_homebrew_library_path"), patch.object(
            recreate_bootstrap, "seed_verification_off_switch", return_value=None
        ), patch.object(recreate_bootstrap.subprocess, "run", side_effect=run), patch.object(
            sys, "stdout", io.StringIO()
        ):
            self.assertEqual(
                recreate_bootstrap.run_xpy_build(
                    Path(directory).resolve(), "test-host", 2, None, [], seed_mode=True
                ),
                0,
            )
        self.assertEqual(launched["UNRELATED"], "preserved")
        self.assertEqual(sorted(name for name in launched if "PKG_CONFIG" in name), [])

    @unittest.skipUnless(
        sys.version_info >= (3, 11), "the manifest graph reads Cargo.toml with tomllib"
    )
    def test_no_pkg_config_spelling_reaches_the_stage0_schema_probe(self):
        """The third child the recreator starts: the candidate stage0's own cargo.

        Selecting a stage0 runs `<candidate>/bin/cargo metadata` over this
        tree's manifests (stage0_refuses_tree_manifest). A `--check` gets there
        with whatever its caller exported, because a check goes on to the
        selection after a refusing capture. `cargo metadata --no-deps` runs no
        build script, so nothing reads these names there today; the rule is
        that no ambient build authority crosses into a child, and the probe
        applies it with the helper the capture and x.py use. This holds the
        probe to the same set, so that helper cannot be narrowed for one of
        the three without a test saying so.
        """
        ambient = {
            name: "/ambient"
            for name in [*self.every_pkg_config_spelling(), *self.PKG_CONFIG_BINARY_SWITCHES]
        }
        probed = []

        def probe(command, *, env, **_kwargs):
            probed.append((command, dict(env)))
            return SimpleNamespace(returncode=0, stderr="", stdout="")

        with tempfile.TemporaryDirectory() as directory, patch.dict(
            os.environ, {**ambient, "UNRELATED": "preserved"}, clear=True
        ), patch.object(recreate_bootstrap.subprocess, "run", side_effect=probe), patch.object(
            sys, "stdout", io.StringIO()
        ):
            root = Path(directory).resolve() / "checkout"
            root.mkdir()
            (root / "Cargo.toml").write_text("[workspace]\nmembers = []\n", encoding="utf-8")
            cargo = Path(directory).resolve() / "candidate" / "bin" / "cargo"
            cargo.parent.mkdir(parents=True)
            cargo.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            cargo.chmod(0o755)
            self.assertIsNone(
                recreate_bootstrap.stage0_refuses_tree_manifest(cargo.parent.parent, root)
            )
        # Not vacuous: the candidate's cargo really was started, on this tree.
        self.assertTrue(probed)
        for command, env in probed:
            self.assertEqual(command[:2], [str(cargo), "metadata"])
            self.assertEqual(env["UNRELATED"], "preserved")
            self.assertEqual(sorted(name for name in env if "PKG_CONFIG" in name), [])

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


class NativeToolPrerequisiteTests(unittest.TestCase):
    """The prerequisite report of a Stage2+ build is the native capture's answer.

    Until 2026-10-12 the report and the capture were two hand-kept lists. The
    check asked for cmake, ninja, a C compiler, git and python; the capture a
    Stage2+ provenance build runs later also demanded c++, ar, ld, nm, ranlib,
    strip, make, perl, pkg-config and sh. So `--check --stage 2 --require-seed
    --no-register` printed "prerequisites OK" on a Mac with no pkg-config, and
    the build with the same flags was refused two minutes in, after fetching
    the seed. Sharing one tool table (the first fix) left the capture's macOS
    list (xcrun, xcode-select, the xcrun-selected tools) and every refusal that
    is not a tool (ambient overrides, Cargo configuration, the developer
    directory, the SDK, the dylib closure) unreported. The report now runs the
    capture and prints what it answered, before the stage0 selection.

    These tests drive the real main() and the real capture_build_authority()
    against one scratch directory of stub tools, so they measure what a user
    is told, not how the two happen to be wired together.
    """

    HOST = "test-host"
    SEED_STAGE2 = ("--stage", "2", "--require-seed", "--no-register")
    # The capture's wording for a table tool it cannot bind, as its errors
    # carried it before any of this was shared. Every other error is "other".
    TOOL_REFUSAL = "required native build tool is not bound: "
    LLVM_REFUSAL = "explicit llvm-config is not bound"
    # Receipt rows: (name, identity arguments, required with in-tree LLVM,
    # required with --llvm-config). Both compiler workflows build native LLD.
    # Receipt content is hashed into authority_sha256.
    RECEIPT_ROWS = (
        ("cc", "--version", True, True),
        ("c++", "--version", True, True),
        ("ar", "--version", True, True),
        ("ld", "-v", True, True),
        ("nm", "--version", True, True),
        ("ranlib", "--version", True, True),
        ("strip", "--version", True, True),
        ("make", "--version", True, True),
        ("perl", "-v", True, True),
        ("cmake", "--version", True, True),
        ("ninja", "--version", True, True),
        ("pkg-config", "--version", True, True),
        ("sh", "--version", True, True),
        ("git", "--version", True, True),
        ("python", "--version", True, True),
        ("brew", "--version", False, False),
    )
    NATIVE_ROW_NAMES = {name for name, *_ in RECEIPT_ROWS} | {"llvm-config"}

    def setUp(self):
        self.actual_seed_wait = recreate_bootstrap._seed_transport().run_custodied_command
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        scratch = Path(temporary.name).resolve()
        self.bin = scratch / "bin"
        self.bin.mkdir()
        self.root = scratch / "checkout"
        self.root.mkdir()

    def install(self, *names):
        for name in names:
            tool = self.bin / name
            # Identity is the tool's own name and arguments, so a changed
            # identity probe shows up in the receipt row.
            tool.write_text('#!/bin/sh\necho "${0##*/} $*"\n', encoding="utf-8")
            tool.chmod(0o755)

    def install_only(self, *names):
        for tool in self.bin.iterdir():
            tool.unlink()
        self.install(*names)

    def table_tools(self):
        """Every tool the receipt table can bind from PATH on a stub machine."""
        return {name for name, *_ in self.RECEIPT_ROWS} - {"python", "brew"}

    def host(self, system="Linux", *, real_identity=False, environ=None):
        """A machine whose only tools are the stubs installed under self.bin."""

        def which(name):
            candidate = self.bin / name
            return str(candidate) if candidate.is_file() else None

        def fixed_git():
            candidate = self.bin / "git"
            return candidate if candidate.is_file() else None

        environment = {"PATH": str(self.bin)}
        environment.update(environ or {})
        stack = ExitStack()
        stack.enter_context(patch.dict(os.environ, environment, clear=True))
        stack.enter_context(patch.object(recreate_bootstrap, "which", side_effect=which))
        stack.enter_context(
            patch.object(recreate_bootstrap, "fixed_git_executable", side_effect=fixed_git)
        )
        stack.enter_context(
            patch.object(recreate_bootstrap, "find_python_ge_311", return_value=sys.executable)
        )
        stack.enter_context(patch.object(recreate_bootstrap, "find_rustup", return_value=None))
        stack.enter_context(
            patch.object(recreate_bootstrap.platform, "system", return_value=system)
        )
        if system == "Darwin":
            # A stub machine has no Homebrew. Without this the capture's Darwin
            # reading would bind the libgit2 keg of whatever Mac runs the test.
            stack.enter_context(
                patch.object(
                    recreate_bootstrap,
                    "_selected_homebrew_library_path",
                    return_value=(None, None),
                )
            )
        if not real_identity:
            stack.enter_context(
                patch.object(recreate_bootstrap, "tool_version", return_value="fixture 1.0")
            )
        return stack

    def capture(self, llvm_config=None, *, system="Linux", real_identity=False, environ=None):
        with self.host(system, real_identity=real_identity, environ=environ):
            return recreate_bootstrap.capture_build_authority(self.root, self.HOST, llvm_config)

    def split_errors(self, authority):
        """A capture answer as (table tools it refuses for, every other error)."""
        tools, other = set(), []
        for error in authority["errors"]:
            if error.startswith(self.TOOL_REFUSAL):
                tools.add(error[len(self.TOOL_REFUSAL):])
            elif error == self.LLVM_REFUSAL:
                tools.add("llvm-config")
            else:
                other.append(error)
        return tools, other

    def capture_refusals(self, llvm_config=None):
        """The tools the capture would refuse a build for on this machine.

        Under the Linux reading of a stub machine with a clean environment the
        capture has nothing but tools to refuse for. If it ever answers
        anything else, in any wording, the callers' expectations do not know
        about it and must fail rather than filter it out: a filter here is how
        a refusal with different wording once went unseen.
        """
        tools, other = self.split_errors(self.capture(llvm_config))
        self.assertEqual(other, [])
        return tools

    def run_main(
        self, *argv, system="Linux", mocked=(), environ=None, mode="seed", real_selection=False
    ):
        """Run main(); return (exit code, printed rows, output, mocks).

        The stage0 selection answers `mode` without looking, unless
        `real_selection`: then the real resolve_stage0_selection() reads
        self.root, and a seed validation it starts is the real child.
        """
        rows = []
        real_print = recreate_bootstrap.print_prereqs

        def record(prereqs):
            rows.extend(prereqs)
            real_print(prereqs)

        out = io.StringIO()
        with self.host(system, environ=environ) as stack:
            for name in ("ensure_python_311", "line_buffer_output"):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            stack.enter_context(
                patch.object(recreate_bootstrap, "repo_root", return_value=self.root)
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "host_triple", return_value=self.HOST)
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "print_prereqs", side_effect=record)
            )
            mocks = {}
            if not real_selection:
                # This fixture supplies a selected mode without actual seed bytes.
                # Runtime archive/dependency admission has its own boundary tests.
                stack.enter_context(patch.object(
                    recreate_bootstrap, "selected_seed_runtime_prereq",
                    return_value=recreate_bootstrap.Prereq(
                        "stage0 runtime", "/fixture/targo", "fixture runtime resolved", True, True
                    ),
                ))
                mocks["resolve_stage0_selection"] = stack.enter_context(
                    patch.object(
                        recreate_bootstrap,
                        "resolve_stage0_selection",
                        return_value=recreate_bootstrap.Stage0Selection(mode, None, None),
                    )
                )
            mocks.update(
                (name, stack.enter_context(patch.object(recreate_bootstrap, name, **kwargs)))
                for name, kwargs in mocked
            )
            stack.enter_context(patch.object(sys, "stdout", out))
            rc = recreate_bootstrap.main(list(argv))
        return rc, rows, out.getvalue(), mocks

    @staticmethod
    def is_refusal(row):
        # A row that is not a tool: a capture error printed under the table.
        return getattr(row, "capture_refusal", False)

    @classmethod
    def failing(cls, rows):
        return {row.name for row in rows if row.required and not row.ok}

    @classmethod
    def failing_tools(cls, rows):
        return {
            row.name
            for row in rows
            if row.required and not row.ok and not cls.is_refusal(row)
        }

    def assert_report_is_the_capture(self, rc, rows, out, authority):
        """One prerequisite report stands for exactly one capture answer.

        Tool by tool and refusal by refusal: nothing the capture refuses for is
        missing from the report, nothing in the report is something the capture
        would let through, and what is not a tool row is in the capture's words.
        """
        tools, other = self.split_errors(authority)
        self.assertEqual(self.failing_tools(rows) & self.NATIVE_ROW_NAMES, tools, out)
        self.assertEqual(
            sorted(row.detail for row in rows if self.is_refusal(row)), sorted(other), out
        )
        for error in other:
            self.assertIn(f"✗ {error}\n", out)
        # What the capture does not judge (rustup, selected seed runtime on macOS).
        elsewhere = self.failing_tools(rows) - self.NATIVE_ROW_NAMES
        refused = authority["status"] != "ready"
        self.assertEqual(refused, bool(authority["errors"]))
        self.assertEqual(rc, 1 if refused or elsewhere else 0, out)
        self.assertEqual("prerequisites OK" in out, rc == 0, out)

    def spying_capture(self, answers):
        real = recreate_bootstrap.capture_build_authority

        def capture(root, host, llvm_config):
            authority = real(root, host, llvm_config)
            answers.append(authority)
            return authority

        return ("capture_build_authority", {"side_effect": capture})

    def test_check_fails_for_exactly_the_tools_the_capture_would_refuse(self):
        """The drift guard: same flags, same machine, same verdict, tool by tool."""
        external_llvm = str(self.bin / "llvm-config")
        cases = (
            ("in-tree LLVM", self.SEED_STAGE2, None),
            ("external LLVM", self.SEED_STAGE2 + ("--llvm-config", external_llvm), external_llvm),
        )
        for label, flags, llvm_config in cases:
            self.install_only()
            demanded = self.capture_refusals(llvm_config)
            # Not vacuous: the capture really demands a set, with pkg-config in it.
            self.assertIn("pkg-config", demanded)
            self.assertTrue({"cmake", "ninja"}.issubset(demanded))
            self.assertGreater(len(demanded), 5)
            self.assertEqual("llvm-config" in demanded, llvm_config is not None)
            with self.subTest(llvm=label, installed="nothing"):
                rc, rows, out, _ = self.run_main("--check", *flags)
                self.assertEqual(rc, 1, out)
                self.assertEqual(self.failing(rows), demanded)
                self.assert_report_is_the_capture(rc, rows, out, self.capture(llvm_config))
            for missing in sorted(demanded):
                with self.subTest(llvm=label, missing=missing):
                    self.install_only(*(demanded - {missing}))
                    self.assertEqual(self.capture_refusals(llvm_config), {missing})
                    rc, rows, out, _ = self.run_main("--check", *flags)
                    self.assertEqual(rc, 1, out)
                    self.assertEqual(self.failing(rows), {missing})
                    self.assertNotIn("prerequisites OK", out)
            if os.geteuid() != 0:
                # On PATH is not bound: the capture hashes the file it records.
                with self.subTest(llvm=label, unreadable="ar"):
                    self.install_only(*demanded)
                    (self.bin / "ar").chmod(0)
                    self.assertEqual(self.capture_refusals(llvm_config), {"ar"})
                    rc, rows, out, _ = self.run_main("--check", *flags)
                    self.assertEqual(rc, 1, out)
                    self.assertEqual(self.failing(rows), {"ar"})
                    self.assertIn("found but cannot be bound", out)
            with self.subTest(llvm=label, installed="everything"):
                self.install_only(*demanded)
                self.assertEqual(self.capture_refusals(llvm_config), set())
                rc, rows, out, _ = self.run_main("--check", *flags)
                self.assertEqual(rc, 0, out)
                self.assertEqual(self.failing(rows), set())
                self.assertIn("--check: prerequisites OK (stage0 mode: seed).", out)
                # A check stays a check: nothing appears in the checkout.
                self.assertEqual(list(self.root.iterdir()), [])

    def test_generated_external_llvm_compiler_still_requires_lld_build_tools(self):
        import tomllib

        external = str(self.bin / "llvm-config")
        with self.host(), patch.object(sys, "stdout", io.StringIO()):
            written = recreate_bootstrap.write_config(
                self.root, self.HOST, False, external, seed_mode=True,
            )
        config = tomllib.loads(written.path.read_text(encoding="utf-8"))
        self.assertEqual(config["target"][self.HOST]["llvm-config"], external)
        self.assertEqual(config["profile"], "compiler")
        profile = tomllib.loads((SCRIPT.parent.parent /
            "src/bootstrap/defaults/bootstrap.compiler.toml").read_text(encoding="utf-8"))
        self.assertTrue(config.get("rust", {}).get("lld", profile["rust"]["lld"]))
        self.assertTrue(config["llvm"]["ninja"])
        self.assertFalse(config["llvm"]["download-ci-llvm"])

        for missing in ("cmake", "ninja"):
            with self.subTest(missing=missing):
                self.install_only(*((self.table_tools() | {"llvm-config"}) - {missing}))
                self.assertIn(missing, self.capture_refusals(external))
                with self.host():
                    short = recreate_bootstrap.check_prereqs(
                        external, seed_mode=True, root=self.root, host=self.HOST,
                        phase=recreate_bootstrap.PREREQS_BEFORE_SELECTION,
                    )
                row = next(row for row in short if row.name == missing)
                self.assertTrue(row.required)
                self.assertFalse(row.ok)

    def test_check_is_the_captures_verdict_under_a_darwin_reading(self):
        """The macOS half the shared tool table never covered.

        Under a Darwin reading the capture also wants xcrun, xcode-select, the
        tools `xcrun --find` selects inside the developer directory, an SDK and
        a dylib closure, each refused in its own wording. Before the report ran
        the capture, a machine with every table tool and no xcrun was told
        "prerequisites OK" and then refused by the capture.
        """
        table = self.table_tools()
        # What the capture answers for each stub machine besides table tools,
        # complete and in its own words. A refusal added to the macOS side, or
        # reworded, is not in these lists: the test fails until it is stated
        # here (the Linux reading has the same rule in capture_refusals()).
        no_dispatchers = [
            "xcrun or xcode-select is missing",
            "xcrun-selected otool is unavailable for dependency binding",
        ]
        selected = (
            "clang", "clang++", "ar", "ld", "nm", "ranlib", "strip", "git", "make",
            "otool", "python3",
        )
        selects_nothing = sorted(
            [
                "Darwin SDKSettings.json is missing, non-regular, or a symlink",
                "active Apple developer directory is outside the admitted roots",
                "selected Darwin SDK is outside the active developer directory",
                "xcode-select did not identify an absolute developer directory",
                "xcrun did not identify an absolute SDK directory",
                "xcrun-selected otool is unavailable for dependency binding",
                *(
                    f"xcrun-selected {name} is not bound inside the developer directory"
                    for name in selected
                ),
            ]
        )
        machines = (
            ("nothing installed", set(), table, no_dispatchers),
            ("every table tool, no xcrun or xcode-select", table, set(), no_dispatchers),
            (
                "every table tool, an xcrun that selects nothing",
                table | {"xcrun", "xcode-select"},
                set(),
                selects_nothing,
            ),
        )
        for label, installed, unbound, refusals in machines:
            with self.subTest(machine=label):
                self.install_only(*installed)
                authority = self.capture(system="Darwin")
                tools, other = self.split_errors(authority)
                self.assertEqual(tools, unbound)
                self.assertEqual(other, refusals)
                self.assertEqual(authority["status"], "rejected")
                rc, rows, out, _ = self.run_main("--check", *self.SEED_STAGE2, system="Darwin")
                self.assert_report_is_the_capture(rc, rows, out, authority)
                self.assertEqual(rc, 1, out)
                self.assertIn("--check: prerequisites NOT met (stage0 mode: seed).", out)
                if installed:
                    # Every table row is green, and the build is still refused:
                    # the state the shared table reported as "prerequisites OK".
                    self.assertFalse(self.failing_tools(rows) & self.NATIVE_ROW_NAMES)
                for refusal in refusals:
                    self.assertIn(f"✗ {refusal}\n", out)
                self.assertIn(f"{len(refusals)} native-authority refusal(s)", out)
                self.assertEqual(list(self.root.iterdir()), [])

    def test_a_refusal_in_words_the_report_never_heard_still_fails_it_verbatim(self):
        """No list of the capture's refusals exists outside the capture."""
        self.install_only(*self.table_tools())
        self.assertEqual(self.capture_refusals(), set())
        real = recreate_bootstrap.capture_build_authority

        def capture(root, host, llvm_config):
            authority = real(root, host, llvm_config)
            authority["errors"] = sorted([*authority["errors"], "m4 is missing"])
            authority["status"] = "rejected"
            return authority

        patched = (
            ("capture_build_authority", {"side_effect": capture}),
            # Never reached; inert so that a regression fails here, by assertion.
            ("ensure_submodules", {}),
            ("write_config", {"side_effect": AssertionError("the refused build wrote its config")}),
            ("run_xpy_build", {"side_effect": AssertionError("the refused build launched x.py")}),
        )
        for check in (("--check",), ()):
            with self.subTest(check=bool(check)):
                rc, rows, out, mocks = self.run_main(*check, *self.SEED_STAGE2, mocked=patched)
                self.assertEqual(rc, 1, out)
                mocks["ensure_submodules"].assert_not_called()
                self.assertIn("✗ m4 is missing\n", out)
                self.assertIn("1 native-authority refusal(s)", out)
                self.assertNotIn("prerequisites OK", out)
                self.assertEqual(self.failing_tools(rows), set())
                # The build stops there; the check goes on to name the stage0.
                self.assertEqual(mocks["resolve_stage0_selection"].called, bool(check))
        # A rejected capture can never read as a green report, whatever it says.
        silent = {"status": "rejected", "errors": [], "native_tools": [], "selected_llvm": None}
        rows = recreate_bootstrap.native_authority_prereqs(silent)
        self.assertTrue(rows)
        self.assertTrue(all(row.required and not row.ok for row in rows))

    def test_check_refuses_what_the_capture_refuses_that_is_not_a_tool(self):
        """Ambient overrides and unowned Cargo configuration, as the capture words them."""
        self.install_only(*self.table_tools())
        self.assertEqual(self.capture_refusals(), set())
        cases = (
            ("a compiler override", {"CC": "/ambient/cc", "RUSTFLAGS": "-Copt-level=0"}),
            ("a target-scoped pkg-config variable", {"PKG_CONFIG_PATH_x86_64_unknown_linux_gnu": "/x"}),
            ("a HOST_ pkg-config executable", {"HOST_PKG_CONFIG": "/other/pkg-config"}),
        )
        for label, environ in cases:
            with self.subTest(ambient=label):
                authority = self.capture(environ=environ)
                refusal = "ambient build-authority overrides are set: " + ", ".join(sorted(environ))
                self.assertEqual(authority["errors"], [refusal])
                rc, rows, out, _ = self.run_main("--check", *self.SEED_STAGE2, environ=environ)
                self.assert_report_is_the_capture(rc, rows, out, authority)
                self.assertEqual(rc, 1, out)
                self.assertIn(f"✗ {refusal}\n", out)
        with self.subTest(cargo="configuration at the bootstrap Cargo home"):
            owned = self.root / "build" / "bootstrap-cargo-home"
            owned.mkdir(parents=True)
            (owned / "config.toml").write_text("[build]\n", encoding="utf-8")
            authority = self.capture()
            self.assertEqual(len(authority["errors"]), 1)
            self.assertIn("unbound Cargo configuration would affect the build", authority["errors"][0])
            rc, rows, out, _ = self.run_main("--check", *self.SEED_STAGE2)
            self.assert_report_is_the_capture(rc, rows, out, authority)
            self.assertEqual(rc, 1, out)

    @unittest.skipUnless(sys.platform == "darwin", "the unmocked capture of a real macOS host")
    def test_on_a_real_mac_the_check_is_the_unmocked_captures_verdict(self):
        """No stub tools and no mocked platform: this host's own capture.

        It asserts agreement, not readiness, so it holds on a Mac with or
        without pkg-config: whatever the real capture answers inside `--check`
        (xcrun, the developer directory, the SDK, otool over every tool) is
        what the report says, and two refusals the old report could not show
        are really among the answers.
        """
        home = os.environ.get("HOME", "")
        real_path = os.environ.get("PATH", os.defpath)

        def check(environ):
            answers, rows = [], []
            real_capture = recreate_bootstrap.capture_build_authority
            real_print = recreate_bootstrap.print_prereqs

            def capture(root, host, llvm_config):
                answers.append(real_capture(root, host, llvm_config))
                return answers[-1]

            def record(prereqs):
                rows.extend(prereqs)
                real_print(prereqs)

            out = io.StringIO()
            with ExitStack() as stack:
                stack.enter_context(patch.dict(os.environ, environ, clear=True))
                for name in ("ensure_python_311", "line_buffer_output"):
                    stack.enter_context(patch.object(recreate_bootstrap, name))
                for name, kwargs in (
                    ("repo_root", {"return_value": self.root}),
                    # Not asked for with --no-register, so not looked for either.
                    ("find_rustup", {"return_value": None}),
                    ("capture_build_authority", {"side_effect": capture}),
                    ("print_prereqs", {"side_effect": record}),
                    (
                        "resolve_stage0_selection",
                        {"return_value": recreate_bootstrap.Stage0Selection("seed", None, None)},
                    ),
                ):
                    stack.enter_context(patch.object(recreate_bootstrap, name, **kwargs))
                stack.enter_context(patch.object(sys, "stdout", out))
                rc = recreate_bootstrap.main(["--check", *self.SEED_STAGE2])
            # The report asked the capture, once, and built on nothing else.
            self.assertEqual(len(answers), 1, out.getvalue())
            self.assertEqual(answers[0]["platform_toolchain"]["schema"],
                             "trust.darwin-platform-toolchain.v1")
            return rc, rows, out.getvalue(), answers[0]

        # This host's own tools, by link, so that PATH is exactly them: every
        # tool the table demands plus the two macOS dispatchers. (brew is left
        # out: the receipt records it when present and never asks for it.)
        wanted = [
            (tool.name, tool.candidates)
            for tool in recreate_bootstrap.NATIVE_BUILD_TOOLS
            if tool.requirement != recreate_bootstrap.NATIVE_TOOL_OPTIONAL
        ] + [("xcrun", ("xcrun",)), ("xcode-select", ("xcode-select",))]
        for name, candidates in wanted:
            found = next(
                filter(None, (shutil.which(candidate, path=real_path) for candidate in candidates)),
                None,
            )
            if found is not None:
                os.symlink(found, self.bin / name)
        self.assertTrue((self.bin / "xcrun").exists(), "a macOS host has /usr/bin/xcrun")
        scoped = "PKG_CONFIG_PATH_" + recreate_bootstrap.host_triple().replace("-", "_")
        with self.subTest(host="its own tools, plus one target-scoped pkg-config variable"):
            rc, rows, out, authority = check({"PATH": str(self.bin), "HOME": home, scoped: "/nowhere"})
            self.assert_report_is_the_capture(rc, rows, out, authority)
            self.assertEqual(rc, 1, out)
            self.assertIn(f"ambient build-authority overrides are set: {scoped}", authority["errors"])
            # xcrun resolved: the macOS list was really walked, not skipped.
            self.assertNotIn("xcrun or xcode-select is missing", authority["errors"])
            self.assertEqual(authority["platform_toolchain"]["xcrun"]["status"], "bound")
        with self.subTest(host="its own tools, xcrun hidden"):
            (self.bin / "xcrun").unlink()
            rc, rows, out, authority = check({"PATH": str(self.bin), "HOME": home})
            self.assert_report_is_the_capture(rc, rows, out, authority)
            self.assertEqual(rc, 1, out)
            self.assertIn("xcrun or xcode-select is missing", authority["errors"])
            self.assertIn("✗ xcrun or xcode-select is missing\n", out)
        self.assertEqual(list(self.root.iterdir()), [])

    def test_stage2_seed_check_names_a_missing_pkg_config_and_how_to_supply_it(self):
        """The 2026-10-12 machine: everything a Mac ships or brew installed, no pkg-config."""
        present = {name for name, *_ in self.RECEIPT_ROWS} - {"python", "brew", "pkg-config"}
        self.install_only(*present)
        expectations = (
            # (platform, text the report must carry, text it must not)
            (
                "Darwin",
                (
                    "`brew install pkgconf`",
                    "pkg-config on macOS",
                    # the trade-off, as the sources state it
                    "Homebrew's .pc",
                    "PKG_CONFIG_PATH",
                    "HOST_PKG_CONFIG*",
                    "refused as ambient build-authority",
                    "`--prefix`",
                    "LAST on PATH",
                    # the recipe that works: a plain pkgconf install has no
                    # file named pkg-config, so "pkgconf last on PATH" is the
                    # state the reader is already in
                    "linked as `pkg-config`",
                    "no file named `pkg-config`",
                    'ln -s ../bin/pkgconf "$P/pathbin/pkg-config"',
                    'PATH="$PATH:$P/pathbin"',
                ),
                # The public snapshot ships scripts/ and INSTALL.md, not docs/:
                # the printed note may not send its reader to a file under it.
                ("apt-get", "docs/", "private-prefix pkgconf last on PATH"),
            ),
            ("Linux", ("`apt-get install pkg-config`",), ("pkg-config on macOS", "brew install")),
            # No install hint is invented for a host the hints were not written for.
            ("Windows", ("missing — the Stage2+ provenance",), ("apt-get", "brew install")),
        )
        for system, expected, unexpected in expectations:
            with self.subTest(system=system):
                rc, rows, out, _ = self.run_main("--check", *self.SEED_STAGE2, system=system)
                self.assertEqual(rc, 1, out)
                self.assertNotIn("prerequisites OK", out)
                # The failing check still answers "which stage0 would this use".
                self.assertIn("--check: prerequisites NOT met (stage0 mode: seed).", out)
                # libgit2 is a host fact under the Darwin reading, not this
                # test's; so are the capture's macOS refusals on a stub machine
                # without xcrun, which are not tool rows (the Darwin-reading
                # test above holds the report to them).
                self.assertEqual(self.failing_tools(rows) - {"stage0 runtime"}, {"pkg-config"})
                row = next(row for row in rows if row.name == "pkg-config")
                self.assertIsNone(row.path)
                self.assertTrue(row.required)
                self.assertIn("missing", row.detail)
                self.assertIn("the Stage2+ provenance receipt binds it", row.detail)
                self.assertRegex(out, r"✗ pkg-config +\(not found\)")
                self.assertIn("required prerequisite(s) missing", out)
                # Wrapping is not content: compare against the report as one line.
                report = " ".join(out.split())
                for text in expected:
                    self.assertIn(text, report)
                for text in unexpected:
                    self.assertNotIn(text, report)
                # Nor by its bare name: what the snapshot ships about these
                # prerequisites is in two files, the only Markdown a report
                # may name.
                self.assertLessEqual(
                    set(re.findall(r"[\w./-]+\.md\b", report)), {"README.md", "INSTALL.md"}, report
                )
        # Supplying one, and nothing else, is what turns the same check green.
        self.install("pkg-config")
        rc, rows, out, _ = self.run_main("--check", *self.SEED_STAGE2)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.failing(rows), set())
        self.assertIn("--check: prerequisites OK (stage0 mode: seed).", out)

    def test_only_invocations_that_run_the_capture_are_held_to_its_tool_set(self):
        # What the check asked for before the lists were joined, and still asks
        # of a build that never captures; none of the capture-only tools.
        self.install_only("cmake", "ninja", "cc", "git")
        capture_only = self.capture_refusals()
        self.assertIn("pkg-config", capture_only)
        self.assertFalse(capture_only & {"cmake", "ninja", "cc", "git"})
        legacy_rows = ["cmake", "ninja", "C compiler", "git", "python ≥ 3.11", "rustup"]
        answers = []
        build = (
            ("ensure_submodules", {}),
            (
                "write_config",
                {
                    "return_value": recreate_bootstrap.WrittenBootstrapConfig(
                        self.root / "bootstrap.toml", "a" * 64
                    )
                },
            ),
            ("run_xpy_build", {"return_value": 0}),
            ("install_ay_solver", {"return_value": True}),
            ("capture_source_lineage", {}),
            ("capture_bootstrap_lineage", {}),
            self.spying_capture(answers),
        )

        # No capture: not refused, and told nothing new.
        for flags in (
            ("--stage", "0"),
            ("--stage", "1"),
            ("--stage", "1", "--no-build"),
            ("--stage", "2", "--no-build"),
        ):
            with self.subTest(check=flags):
                rc, rows, out, _ = self.run_main(
                    "--check", "--require-seed", "--no-register", *flags,
                    mocked=(self.spying_capture(answers),),
                )
                self.assertEqual(rc, 0, out)
                self.assertEqual([row.name for row in rows], legacy_rows)
                self.assertEqual(self.failing(rows), set())
                # One table, after the selection, as before.
                self.assertLess(out.index("Selecting stage0 authority:"), out.index("Prerequisites:"))
        # ... and the invocations themselves really never reach the capture.
        for flags, runs_xpy in ((("--stage", "1"), True), (("--stage", "2", "--no-build"), False)):
            with self.subTest(build=flags):
                rc, _rows, out, mocks = self.run_main(
                    "--require-seed", "--no-register", *flags, mocked=build
                )
                self.assertEqual(rc, 0, out)
                self.assertEqual(mocks["run_xpy_build"].called, runs_xpy)
        self.assertEqual(answers, [])

        # Capture: the same machine is refused, by the check and by the build's
        # own prerequisite phase. That phase is now the capture itself, run
        # once and read-only; nothing else of the build runs, not even the
        # stage0 selection (a build fetches the seed there).
        with self.subTest(check=self.SEED_STAGE2):
            rc, rows, out, _ = self.run_main(
                "--check", *self.SEED_STAGE2, mocked=(self.spying_capture(answers),)
            )
            self.assertEqual(rc, 1, out)
            self.assertEqual(self.failing(rows), capture_only)
            self.assertEqual(len(answers), 1)
            self.assert_report_is_the_capture(rc, rows, out, answers.pop())
        with self.subTest(build=self.SEED_STAGE2):
            rc, rows, out, mocks = self.run_main(*self.SEED_STAGE2, mocked=build)
            self.assertEqual(rc, 1, out)
            self.assertEqual(self.failing(rows), capture_only)
            self.assertEqual(len(answers), 1)
            self.assertEqual(answers.pop()["status"], "rejected")
            for name, _kwargs in build:
                if name != "capture_build_authority":
                    mocks[name].assert_not_called()
            mocks["resolve_stage0_selection"].assert_not_called()
            self.assertNotIn("Selecting stage0 authority", out)
            self.assertEqual(list(self.root.iterdir()), [])

    def test_a_stage2_build_is_refused_before_it_selects_or_fetches_a_stage0(self):
        """What does not depend on the stage0 mode is decided before selecting one.

        The selection is where a build fetches the seed archives. The 2026-10-12
        build fetched nine of them and was then refused for a tool it could
        have been told about first.
        """
        events = []
        real_capture = recreate_bootstrap.capture_build_authority

        def step(name, result=None):
            def run(*_args, **_kwargs):
                events.append(name)
                return result
            return {"side_effect": run}

        def capture(root, host, llvm_config):
            events.append("capture")
            return real_capture(root, host, llvm_config)

        def flow(mode):
            return (
                (
                    "resolve_stage0_selection",
                    step("select", recreate_bootstrap.Stage0Selection(mode, None, None)),
                ),
                ("capture_build_authority", {"side_effect": capture}),
                ("ensure_submodules", step("submodules")),
                ("ensure_local_genesis_stage0", step("genesis-adapter")),
                (
                    "write_config",
                    step(
                        "config",
                        recreate_bootstrap.WrittenBootstrapConfig(
                            self.root / "bootstrap.toml", "a" * 64
                        ),
                    ),
                ),
                (
                    "capture_source_lineage",
                    step("source", {"status": "candidate", "closure_sha256": "c" * 64, "errors": []}),
                ),
                (
                    "capture_bootstrap_lineage",
                    step(
                        "bootstrap",
                        {
                            "status": "candidate", "mode": mode, "config_sha256": "a" * 64,
                            "config_path": "bootstrap.toml", "errors": [],
                        },
                    ),
                ),
                # Stop at launch: this fixture never executes a compiler.
                ("run_xpy_build", step("xpy", 7)),
            )

        def run(*argv, mode="seed"):
            del events[:]
            rc, rows, out, _ = self.run_main(*argv, mocked=flow(mode), mode=mode)
            return rc, rows, out, list(events)

        everything = self.table_tools()
        with self.subTest("a machine that can build: preview, select, ..., bind, launch"):
            self.install_only(*everything)
            rc, rows, out, order = run(*self.SEED_STAGE2)
            self.assertEqual(rc, 7, out)
            self.assertEqual(
                order,
                ["capture", "select", "submodules", "config", "source", "bootstrap", "capture", "xpy"],
            )
            self.assertLess(out.index("Prerequisites:"), out.index("Selecting stage0 authority:"))
        with self.subTest("a missing native tool: refused before the selection"):
            self.install_only(*(everything - {"pkg-config"}))
            rc, rows, out, order = run(*self.SEED_STAGE2)
            self.assertEqual(rc, 1, out)
            self.assertEqual(order, ["capture"])
            self.assertEqual(self.failing(rows), {"pkg-config"})
            self.assertNotIn("Selecting stage0 authority", out)
            self.assertIn("1 required prerequisite(s) missing", out)
            # The check with the same flags goes on, read-only, to name the
            # mode, and says what is unmet once, at the end, where it is read.
            rc, rows, out, order = run("--check", *self.SEED_STAGE2)
            self.assertEqual(rc, 1, out)
            self.assertEqual(order, ["capture", "select"])
            self.assertEqual(self.failing(rows), {"pkg-config"})
            self.assertLess(
                out.index("Selecting stage0 authority:"),
                out.index("1 required prerequisite(s) missing"),
            )
            self.assertTrue(
                out.endswith("\n--check: prerequisites NOT met (stage0 mode: seed).\n"), out
            )
            # A check that finds no stage0 has still said what else is unmet.
            refused = (
                (
                    "resolve_stage0_selection",
                    {"side_effect": RuntimeError("pinned Trust seed unavailable")},
                ),
            )
            rc, rows, out, _ = self.run_main("--check", *self.SEED_STAGE2, mocked=refused)
            self.assertEqual(rc, 1, out)
            self.assertEqual(self.failing(rows), {"pkg-config"})
            self.assertLess(
                out.index("Stage0 selection refused: pinned Trust seed unavailable"),
                out.index("1 required prerequisite(s) missing"),
            )
            self.assertNotIn("stage0 mode:", out)
        with self.subTest("a missing rustup that the build must register with: the same"):
            self.install_only(*everything)
            rc, rows, out, order = run("--stage", "2", "--require-seed")
            self.assertEqual(rc, 1, out)
            self.assertEqual(order, ["capture"])
            self.assertEqual(self.failing(rows), {"rustup"})
        with self.subTest("rows only the selected mode decides stay after the selection"):
            self.install_only(*everything)
            rc, rows, out, order = run("--stage", "2", "--genesis", "--no-register", mode="genesis")
            self.assertEqual(rc, 1, out)
            self.assertEqual(order, ["capture", "select"])
            self.assertEqual(self.failing(rows), {"rustc", "cargo"})
            heading = "Prerequisites of the selected stage0 mode (genesis):"
            self.assertLess(out.index("Selecting stage0 authority:"), out.index(heading))
            self.assertLess(out.index(heading), out.index("✗ rustc"))
            self.install("rustc", "cargo")
            rc, rows, out, order = run("--stage", "2", "--genesis", "--no-register", mode="genesis")
            self.assertEqual(rc, 7, out)
            self.assertEqual(order[:3], ["capture", "select", "submodules"])
        with self.subTest("a build that never captures keeps its order"):
            # Stage 0/1 and --no-build print what they always printed, byte for
            # byte: the selection first, then one table. Deliberately unchanged.
            self.install_only(*(everything - {"cmake"}))
            rc, rows, out, order = run("--stage", "1", "--require-seed", "--no-register")
            self.assertEqual(rc, 1, out)
            self.assertEqual(order, ["select"])
            self.assertEqual(self.failing(rows), {"cmake"})
            self.assertLess(out.index("Selecting stage0 authority:"), out.index("Prerequisites:"))
            self.assertNotIn("stage0 mode:", out)

    def test_a_failing_check_prints_the_stage0_mode_only_where_its_help_says(self):
        """`--check`'s help says when a `stage0 mode` line ends the report.

        It used to say "whether or not the report passes". That holds for the
        capturing check only. A stage 0/1 or --no-build check keeps the output
        it always had (the change that added the line was required to leave
        those byte-identical), and a refused selection has no mode to name.
        """
        legacy = (
            ("--stage", "0"),
            ("--stage", "1"),
            ("--stage", "1", "--no-build"),
            ("--stage", "2", "--no-build"),
        )
        every = (*legacy, ("--stage", "2"))
        refused = (
            (
                "resolve_stage0_selection",
                {"side_effect": RuntimeError("pinned Trust seed unavailable")},
            ),
        )
        passing_end = "--check: prerequisites OK (stage0 mode: seed)."
        failing_end = "--check: prerequisites NOT met (stage0 mode: seed)."
        printed = []

        def check(*flags, mocked=()):
            rc, rows, out, _ = self.run_main(
                "--check", "--require-seed", "--no-register", *flags, mocked=mocked
            )
            printed.append(out)
            return rc, rows, out

        self.install_only(*(self.table_tools() - {"cmake"}))
        for flags in legacy:
            with self.subTest(failing_and_never_capturing=flags):
                rc, rows, out = check(*flags)
                self.assertEqual(rc, 1, out)
                self.assertEqual(self.failing(rows), {"cmake"})
                # What this check ended with before the line existed.
                self.assertTrue(
                    out.endswith(
                        "\n1 required prerequisite(s) missing. Install them and re-run.\n"
                    ),
                    out,
                )
                self.assertNotIn("stage0 mode", out)
        with self.subTest(failing_and_capturing=("--stage", "2")):
            rc, rows, out = check("--stage", "2")
            self.assertEqual(rc, 1, out)
            self.assertEqual(self.failing(rows), {"cmake"})
            self.assertTrue(out.endswith(f"\n{failing_end}\n"), out)
        for flags in every:
            with self.subTest(selection_refused=flags):
                rc, _rows, out = check(*flags, mocked=refused)
                self.assertEqual(rc, 1, out)
                self.assertIn("Stage0 selection refused: pinned Trust seed unavailable", out)
                self.assertNotIn("stage0 mode", out)
        self.install("cmake")
        for flags in every:
            with self.subTest(passing=flags):
                rc, _rows, out = check(*flags)
                self.assertEqual(rc, 0, out)
                self.assertTrue(out.endswith(f"\n{passing_end}\n"), out)

        # The help states that, and the lines it quotes are lines printed above.
        shown = io.StringIO()
        with patch.dict(
            os.environ, {"COLUMNS": "100000", "NO_COLOR": "1"}, clear=True
        ), patch.object(sys, "stdout", shown), self.assertRaises(SystemExit) as stopped:
            recreate_bootstrap.parse_args(["--help"])
        self.assertEqual(stopped.exception.code, 0)
        text = " ".join(shown.getvalue().split())
        self.assertNotIn("whether or not the report passes", text)
        quoted = re.findall(r"`(--check: prerequisites [^`]*)`", text)
        self.assertEqual(
            sorted(quoted),
            sorted(end.replace("seed", "<mode>") for end in (passing_end, failing_end)),
            text,
        )
        for quote in quoted:
            self.assertIn(quote.replace("<mode>", "seed") + "\n", "".join(printed))
        self.assertIn(
            "a failing --stage 0/1 or --no-build check prints no `stage0 mode` line, and "
            "neither does a check whose stage0 selection is refused.",
            text,
        )

    def test_selected_seed_runtime_refusal_precedes_build_and_success_needs_no_keg(self):
        """The selected seed's dependencies decide; Homebrew presence does not."""
        self.install_only(*self.table_tools())
        ready = self.capture()
        accepted = ("capture_build_authority", {"return_value": ready})
        never = tuple(
            (name, {"side_effect": AssertionError(f"refused build reached {name}")})
            for name in ("ensure_submodules", "write_config", "run_xpy_build")
        )
        for mode in ("seed", "atpkg"):
            for flags in (self.SEED_STAGE2, ("--stage", "1", "--require-seed", "--no-register")):
                for okay in (False, True):
                    runtime = ("selected_seed_runtime_prereq", {"return_value":
                        recreate_bootstrap.Prereq("stage0 runtime", "/fixture/targo",
                            "resolved" if okay else "missing libgit2", True, okay)})
                    with self.subTest(mode=mode, flags=flags, okay=okay):
                        rc, rows, out, mocks = self.run_main(
                            "--check", *flags, system="Darwin",
                            mocked=(accepted, runtime), mode=mode,
                        )
                        self.assertEqual(rc, 0 if okay else 1, out)
                        self.assertEqual(self.failing(rows), set() if okay else {"stage0 runtime"})
                        mocks["selected_seed_runtime_prereq"].assert_called_once()
                        self.assertNotIn("libgit2", [row.name for row in rows])
                    if not okay:
                        rc, rows, out, _ = self.run_main(
                            *flags, system="Darwin", mocked=(accepted, runtime, *never), mode=mode,
                        )
                        self.assertEqual(rc, 1, out)
                        self.assertEqual(self.failing(rows), {"stage0 runtime"})
        self.assertEqual(list(self.root.iterdir()), [])

    def test_a_stage2_report_still_asks_for_a_python_that_can_run_the_build(self):
        """`python ≥ 3.11` is not one of the capture's rows and must not go with them.

        The capture binds the interpreter that is running (its `python` row).
        The interpreter x.py and the sub-scripts need, one with tomllib, is
        looked for separately. It does not depend on the stage0 mode, so a
        Stage2+ report decides it in its first table, before the selection.
        """
        self.install_only(*self.table_tools())
        name = "python ≥ 3.11"
        absent = (("find_python_ge_311", {"return_value": None}),)
        never = tuple(
            (step, {"side_effect": AssertionError(f"the refused build reached {step}")})
            for step in ("ensure_submodules", "write_config", "run_xpy_build")
        )
        with self.subTest("found"):
            rc, rows, out, _ = self.run_main("--check", *self.SEED_STAGE2)
            self.assertEqual(rc, 0, out)
            # After the capture's own rows, which end with its `python`.
            self.assertEqual([row.name for row in rows][-3:], ["python", name, "rustup"])
            row = rows[-2]
            self.assertEqual((row.path, row.required, row.ok), (sys.executable, True, True))
            self.assertLess(out.index(f"✓ {name}"), out.index("Selecting stage0 authority:"))
        with self.subTest("not found: the check fails for it, in the first table"):
            rc, rows, out, _ = self.run_main("--check", *self.SEED_STAGE2, mocked=absent)
            self.assertEqual(rc, 1, out)
            self.assertEqual(self.failing(rows), {name})
            row = next(row for row in rows if row.name == name)
            self.assertEqual(
                (row.path, row.detail), (None, "missing — install python@3.11 or newer")
            )
            self.assertLess(out.index(f"✗ {name}"), out.index("Selecting stage0 authority:"))
            self.assertTrue(
                out.endswith("\n--check: prerequisites NOT met (stage0 mode: seed).\n"), out
            )
        with self.subTest("not found: the build is refused before it selects a stage0"):
            rc, rows, out, mocks = self.run_main(*self.SEED_STAGE2, mocked=(*absent, *never))
            self.assertEqual(rc, 1, out)
            self.assertEqual(self.failing(rows), {name})
            mocks["resolve_stage0_selection"].assert_not_called()
            self.assertNotIn("Selecting stage0 authority", out)
            self.assertEqual(list(self.root.iterdir()), [])
        with self.subTest("not found: an invocation that never captures asks for it too"):
            rc, rows, out, _ = self.run_main(
                "--check", "--stage", "1", "--require-seed", "--no-register", mocked=absent
            )
            self.assertEqual(rc, 1, out)
            self.assertEqual(self.failing(rows), {name})

    def test_one_table_and_one_condition_feed_the_capture_and_the_check(self):
        names = [name for name, *_ in self.RECEIPT_ROWS]
        external_llvm = str(self.bin / "llvm-config")
        self.install_only(*(set(names) - {"python"}), "llvm-config")
        record_keys = {
            "name", "resolved_local_path", "status", "resolved_real_path",
            "sha256", "identity", "required",
        }
        for llvm_config, column in ((None, 2), (external_llvm, 3)):
            with self.subTest(llvm_config=llvm_config):
                authority = self.capture(llvm_config, real_identity=True)
                tools = authority["native_tools"]
                # Names, order, identity arguments and record shape stay fixed;
                # required flags follow the compiler workflow's tool policy.
                self.assertEqual([tool["name"] for tool in tools], names)
                self.assertEqual(
                    [tool["required"] for tool in tools],
                    [row[column] for row in self.RECEIPT_ROWS],
                )
                for tool, (name, arguments, *_required) in zip(tools, self.RECEIPT_ROWS):
                    self.assertEqual(set(tool), record_keys, name)
                    self.assertEqual(tool["status"], "bound", name)
                    if name == "python":
                        self.assertEqual(tool["resolved_local_path"], sys.executable)
                    else:
                        self.assertEqual(tool["resolved_local_path"], str(self.bin / name))
                        self.assertEqual(tool["identity"], f"{name} {arguments}")
                selected_llvm = authority["selected_llvm"]
                if llvm_config is None:
                    self.assertIsNone(selected_llvm)
                else:
                    self.assertEqual(selected_llvm["name"], "llvm-config")
                    self.assertEqual(selected_llvm["identity"], "llvm-config --version")
                # Nor did the receipt's shape: the fields that are hashed, and
                # the three that are not.
                self.assertEqual(
                    set(authority),
                    {
                        "schema", "host", "ambient_overrides", "ambient_cargo_configs",
                        "cargo_environment", "native_tools", "selected_llvm",
                        "platform_toolchain", "sdk", "dynamic_dependencies",
                        "derived_library_paths", "status", "authority_sha256", "errors",
                    },
                )
                self.assertEqual(authority["ambient_overrides"], {})
                self.assertEqual(authority["status"], "ready")
        # One table ...
        self.assertEqual([tool.name for tool in recreate_bootstrap.NATIVE_BUILD_TOOLS], names)
        with self.host():
            rows = recreate_bootstrap.check_prereqs(
                seed_mode=True, native_authority=True, root=self.root, host=self.HOST
            )
        native_rows = [row.name for row in rows if row.name in names]
        # ... read in receipt order by the check; brew is recorded, never asked for.
        self.assertEqual(native_rows, [name for name in names if name != "brew"])
        # ... and one condition for "this invocation runs the capture".
        for stage, no_build, captures in (
            (0, False, False), (1, False, False), (2, False, True), (3, False, True),
            (0, True, False), (1, True, False), (2, True, False),
        ):
            self.assertEqual(
                recreate_bootstrap.provenance_build_requested(stage, no_build=no_build),
                captures,
                (stage, no_build),
            )

    def macos_capture_names(self):
        """What the capture names under a Darwin reading beyond the table.

        Read out of its own refusals on a stub machine, so a tool added to the
        macOS list is a tool the documents must name.
        """
        self.install_only()
        _tools, other = self.split_errors(self.capture(system="Darwin"))
        self.assertIn("xcrun or xcode-select is missing", other)
        self.install_only("xcrun", "xcode-select")
        _tools, other = self.split_errors(self.capture(system="Darwin"))
        selected = set()
        for error in other:
            found = re.fullmatch(
                r"xcrun-selected (\S+) is not bound inside the developer directory", error
            )
            if found:
                selected.add(found.group(1))
        self.assertGreater(len(selected), 5, other)
        self.assertIn("otool", selected)
        return selected | {"xcrun", "xcode-select"}

    def test_macos_docs_name_every_tool_a_stage2_build_binds(self):
        macos = self.macos_capture_names()
        self.install_only()
        # python is the running interpreter: always bound, never refused.
        demanded = self.capture_refusals() | {"python"} | macos
        self.assertIn("pkg-config", demanded)
        repository = SCRIPT.parent.parent
        sections = [(repository / "INSTALL.md", "### Native tools of the Stage 2 build")]
        # The public snapshot ships INSTALL.md and scripts/ but not docs/.
        if (repository / "docs").is_dir():
            sections.append(
                (
                    repository / "docs" / "BOOTSTRAP_FROM_SCRATCH.md",
                    "### Native tools of a Stage 2 build",
                )
            )
        for path, heading in sections:
            with self.subTest(document=path.name):
                text = path.read_text(encoding="utf-8")
                self.assertIn(heading + "\n", text)
                # To the next heading; a shell comment in a code block is `# `.
                section = re.split(
                    r"^#{2,3} ", text.split(heading + "\n", 1)[1], maxsplit=1, flags=re.M
                )[0]
                unnamed = sorted(name for name in demanded if f"`{name}`" not in section)
                self.assertEqual(unnamed, [], f"{path.name}: {heading}")
                # The private recipe is the one that works: the link step.
                self.assertIn("pathbin/pkg-config", section)
                self.assertNotIn("pkgconf built with a private `--prefix` and put last", section)
                if path.name == "INSTALL.md":
                    # It ships without docs/: it may not send a reader there for this.
                    self.assertNotIn("BOOTSTRAP_FROM_SCRATCH", section)

    def test_live_docs_quote_what_check_prints(self):
        """Documents that tell a reader what `--check` answers quote the script.

        A bare `--check` is a Stage 2 check. Since it reports the capture it
        can fail on a machine the docs present it as a plain report for, and
        the line they read the stage0 mode from must still be printed then.
        """
        self.install_only(*(self.table_tools() - {"pkg-config"}))
        rc, _rows, failing, _ = self.run_main("--check")
        self.assertEqual(rc, 1, failing)
        self.assertIn("--check: prerequisites NOT met (stage0 mode: seed).", failing)
        self.install("pkg-config")
        rc, _rows, passing, _ = self.run_main("--check", "--no-register")
        self.assertEqual(rc, 0, passing)
        self.assertIn("--check: prerequisites OK (stage0 mode: seed).", passing)
        printed = failing + passing
        repository = SCRIPT.parent.parent
        documents = [repository / "README.md"]
        if (repository / "docs").is_dir():
            documents += [
                repository / "docs" / "BOOTSTRAP_FROM_SCRATCH.md",
                repository / "docs" / "BUILD_AND_INSTALL.md",
            ]
        for path in documents:
            with self.subTest(document=path.name):
                text = " ".join(path.read_text(encoding="utf-8").split())
                # Each one says a failing check exits 1 and still names the mode ...
                self.assertIn("prerequisites NOT met (stage0 mode:", text)
                # ... and every `--check: ...` line it quotes is one the script prints.
                quoted = re.findall(r"`(--check: prerequisites [^`]*?)\(stage0 mode: [^`]*`", text)
                self.assertTrue(quoted, path.name)
                for quote in quoted:
                    self.assertIn(quote, printed)

    # -- a check leaves the checkout as it found it -------------------------
    #
    # `--check` says it writes nothing. Until 2026-10-12 a seed-mode check with
    # the pinned payloads on disk wrote scripts/__pycache__/*.pyc: its seed
    # validation is a Python child (check_seed_freshness.py) that imports
    # scripts/mint_seed_support.py to read the bootstrap config, and nothing
    # told that child not to cache what it imported. Every other test of
    # `--check` here answers the stage0 selection without running it, so none
    # of them started that child. These build a checkout the real selection and
    # the real child accept, and compare everything under it before and after.

    SEED_DATE = "2026-07-13"
    SEED_VERSION = "1.99.0-trust"
    # One archive per component check_seed_freshness.py requires
    # (validate_payload_inventory); trust-src is the one without a host.
    SEED_COMPONENTS = (
        "targo", "targo-trust", "tippy", "trust-analyzer", "trust-src", "trust-std",
        "trustc", "trustc-dev", "trustfmt",
    )
    # What the seed validation runs from the checkout: validate_seed() starts
    # the first, which imports its seed identity and native transport helpers
    # plus mint_seed_support (configured_seed_overrides, native_payload_host).
    # These are in the scope of the push lane that runs
    # this file (scripts/check_bootstrap_script_tests.sh) because this list
    # names them; scripts/tests/check_bootstrap_script_tests_test.py holds the
    # two lists together.
    SEED_VALIDATION_SCRIPTS = ("scripts/check_seed_freshness.py", "scripts/mint_seed_support.py",
                               "scripts/lib/native_serial.py", "scripts/lib/landing_targo.py",
                               "scripts/lib/seed_compiler_identity.py")

    def materialize_seed_checkout(self):
        """Make self.root a seed-mode checkout whose pinned seed validates.

        What resolve_stage0_selection() and check_seed_freshness.py read: the
        pins, one archive per required component of HOST with its SHA-256
        pinned, the channel manifest, the compat version, the script closure, and
        the bootstrap.toml this script's own writer generates for seed mode
        (with a stand-in for the `compiler` profile defaults it inherits). The
        config is what makes the child import mint_seed_support.
        """
        scripts = self.root / "scripts"
        scripts.mkdir()
        for name in self.SEED_VALIDATION_SCRIPTS:
            (self.root / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(SCRIPT.parent.parent / name, self.root / name)
        dist = self.root / "bootstrap" / "trust-stage0" / "dist" / self.SEED_DATE
        dist.mkdir(parents=True)
        manifest = dist / "channel-rust-trust.toml"
        manifest.write_bytes(b"fixture channel manifest\n")
        manifest_sha256 = hashlib.sha256(manifest.read_bytes()).hexdigest()
        pins = []
        for component in ("compiler", "rustfmt"):
            pins += [
                f"{component}_channel_manifest_hash={manifest_sha256}",
                f"{component}_git_commit_hash={'c' * 40}",
                f"{component}_date={self.SEED_DATE}",
                f"{component}_version={self.SEED_VERSION}",
            ]
        for component in self.SEED_COMPONENTS:
            host = "" if component == "trust-src" else f"-{self.HOST}"
            archive = dist / f"{component}-{self.SEED_VERSION}{host}.tar.xz"
            archive.write_bytes(f"fixture payload: {component}\n".encode("utf-8"))
            digest = hashlib.sha256(archive.read_bytes()).hexdigest()
            pins.append(f"dist/{self.SEED_DATE}/{archive.name}={digest}")
        source = self.root / "src"
        (source / "bootstrap" / "defaults").mkdir(parents=True)
        shutil.copyfile(SCRIPT.parent.parent / "src/bootstrap/stage0_identity.py", source / "bootstrap/stage0_identity.py")
        (source / "stage0").write_text("\n".join(pins) + "\n", encoding="utf-8")
        (source / "rust-compat-version").write_text("1.99.0\n", encoding="utf-8")
        (source / "bootstrap" / "defaults" / "bootstrap.compiler.toml").write_text(
            "[build]\nextended = true\n", encoding="utf-8"
        )
        with self.host(), patch.object(sys, "stdout", io.StringIO()):
            recreate_bootstrap.write_config(self.root, self.HOST, False, None, seed_mode=True)
        self.assertIn(
            b"(seed stage0 mode)", (self.root / "bootstrap.toml").read_bytes()
        )

    def test_agh_seed_fetch_still_runs_real_digest_validation(self):
        self.materialize_seed_checkout()
        ledger = self.root / "bootstrap/trust-stage0/seed-ledger.toml"
        ledger.write_text('[release]\nrepo = "owner/trust"\ntag = "exact-seed"\n')
        _, payloads = recreate_bootstrap.parse_stage0_pins(self.root)
        relative = next(iter(payloads))
        archive = ledger.parent / relative
        original = archive.read_bytes()
        real_run = subprocess.run
        real_seed_wait = recreate_bootstrap._seed_transport().run_custodied_command
        validations = []

        def validate(command, **options):
            options.update(capture_output=True, text=True)
            result = real_seed_wait(command, **options)
            validations.append(result)
            return result

        def transport(command, **options):
            if command[0] == "/tools/agh":
                archive.write_bytes(downloaded)
                return SimpleNamespace(returncode=0)
            return real_run(command, **options)

        for downloaded, expected in [(original, True), (b"wrong downloaded bytes", False)]:
            with self.subTest(valid_digest=expected):
                archive.unlink()
                with self.host(), patch.object(recreate_bootstrap, "which", return_value="/tools/agh"), \
                        patch.object(recreate_bootstrap.subprocess, "run", side_effect=transport), \
                        patch.object(recreate_bootstrap._seed_transport(), "run_custodied_command", side_effect=validate):
                    self.assertEqual(
                        recreate_bootstrap.resolve_seed(self.root, allow_fetch=True, host=self.HOST), expected
                    )
                self.assertEqual(validations[-1].returncode, 0 if expected else 1)
                if not expected:
                    self.assertIn("SHA-256 mismatch", validations[-1].stdout + validations[-1].stderr)

    def checkout_state(self):
        """Every entry under self.root, and the root itself.

        Kind, permissions and modification time of each, plus size and SHA-256
        of a file and the target of a link. A directory's modification time
        moves when an entry is created in it or removed from it, so a file
        written and deleted again shows too.
        """
        state = {}
        entries = [self.root]
        for directory, directories, files in os.walk(self.root):
            entries += [Path(directory, name) for name in (*directories, *files)]
        for path in entries:
            status = os.lstat(path)
            record = [stat.S_IFMT(status.st_mode), stat.S_IMODE(status.st_mode), status.st_mtime_ns]
            if stat.S_ISREG(status.st_mode):
                record += [status.st_size, hashlib.sha256(path.read_bytes()).hexdigest()]
            elif stat.S_ISLNK(status.st_mode):
                record.append(os.readlink(path))
            state[path.relative_to(self.root).as_posix()] = tuple(record)
        return state

    def assert_checkout_unchanged(self, before, what):
        after = self.checkout_state()
        changed = sorted(
            path for path in set(before) | set(after) if before.get(path) != after.get(path)
        )
        self.assertEqual(changed, [], f"{what} created or changed these under the checkout")

    def fixture_seed_child(self, command, **options):
        """Run real copied checker imports with explicit unit-only transport.

        The stub machine's seed is a shell fixture, not native compilation.
        No SDK/HELD marker or managed-package claim is manufactured here.
        """
        bridge = self.root.parent / "unit-seed-bridge"
        bridge.write_text('#!/bin/sh\nshift\nexec "$@"\n')
        bridge.chmod(0o700)
        driver = (
            "import runpy,sys,pathlib; "
            "script,bridge,*args=sys.argv[1:]; sys.argv=[script,*args]; "
            "body=runpy.run_path(script,run_name='seed_unit_fixture'); "
            "body['native_serial'].managed_serial_executor=lambda env:pathlib.Path(bridge); "
            "raise SystemExit(body['main']())"
        )
        return self.actual_seed_wait([sys.executable, "-c", driver, command[1], str(bridge), *command[2:]], **options)

    def run_freshness_check_unguarded(self, *arguments):
        """The seed validation child as it was started until 2026-10-12.

        The control of the tests below: the same script, interpreter and
        checkout, with nothing in the environment that stops Python from
        caching what it imports.
        """
        return self.fixture_seed_child(
            [sys.executable, str(self.root / "scripts" / "check_seed_freshness.py"), *arguments],
            cwd=self.root,
            env={"PATH": str(self.bin)},
            capture_output=True,
            text=True,
            timeout=120,
        )

    def assert_cached_bytecode_appeared(self, before):
        added = sorted(set(self.checkout_state()) - set(before))
        if any(path.startswith("scripts/__pycache__/mint_seed_support.") for path in added):
            return
        if getattr(sys, "pycache_prefix", None) is not None:
            # Apple's /usr/bin/python3 keeps every cache under
            # ~/Library/Caches/com.apple.python. Where the child runs under
            # such an interpreter nothing it does can reach the checkout.
            self.skipTest(
                "this interpreter caches bytecode outside the tree "
                f"(sys.pycache_prefix = {sys.pycache_prefix}), so the comparison held "
                "but could not have failed"
            )
        self.fail(
            "the unguarded child cached no bytecode in the checkout, so the comparison "
            f"proved nothing: {added}"
        )

    @unittest.skipUnless(
        sys.version_info >= (3, 11), "the stage0 selection reads bootstrap.toml with tomllib"
    )
    def test_a_seed_mode_check_leaves_the_checkout_as_it_found_it(self):
        self.materialize_seed_checkout()
        self.install_only(*self.table_tools())
        before = self.checkout_state()
        for flags in (self.SEED_STAGE2, ("--stage", "1", "--require-seed", "--no-register")):
            with self.subTest(flags=flags):
                rc, _rows, out, _ = self.run_main("--check", *flags, real_selection=True)
                # The real selection ran, validated the archives and chose them.
                self.assertIn("validating payload digests against src/stage0", out)
                self.assertIn("pinned archives validated", out)
                self.assertEqual(rc, 0, out)
                self.assertIn("--check: prerequisites OK (stage0 mode: seed).", out)
                self.assert_checkout_unchanged(before, f"--check {' '.join(flags)}")
        # With a hydrated stage0 of the pinned date the validation also compiles
        # a one-file crate with it: in the temporary directory, which it leaves
        # empty, as the `--check` help says. The stand-in compiler records
        # where it was run; that record is kept outside the checkout.
        scratch = self.root.parent
        temporary = scratch / "tmpdir"
        temporary.mkdir()
        probes = scratch / "stage0-probes"
        stage0 = self.root / "build" / self.HOST / "stage0"
        (stage0 / "bin").mkdir(parents=True)
        compiler = stage0 / "bin" / "rustc"
        compiler.write_text(
            "#!/bin/sh\n"
            'if [ "$1" = "-vV" ]; then\n'
            f"  printf 'commit-hash: {'c' * 40}\\ncommit-date: {self.SEED_DATE}\\n'\n"
            f"  printf 'release: {self.SEED_VERSION}\\n'\n"
            "  exit 0\n"
            "fi\n"
            'pwd -P >> "$STAGE0_PROBES"\n'
            'while [ "$#" -gt 1 ]; do\n'
            '  if [ "$1" = "-o" ]; then printf "fixture metadata\\n" > "$2"; fi\n'
            "  shift\n"
            "done\n",
            encoding="utf-8",
        )
        compiler.chmod(0o755)
        # Hydrated production probes bind these exact launcher bytes to the
        # selected pinned archive member, not merely its printed -vV identity.
        stem = f"trustc-{self.SEED_VERSION}-{self.HOST}"
        relative = f"dist/{self.SEED_DATE}/{stem}.tar.xz"
        archive = self.root / "bootstrap/trust-stage0" / relative
        payload = compiler.read_bytes()
        with tarfile.open(archive, "w:xz") as image:
            member = tarfile.TarInfo(f"{stem}/trustc/bin/trustc")
            member.size = len(payload)
            member.mode = 0o755
            image.addfile(member, io.BytesIO(payload))
        _, payloads = recreate_bootstrap.parse_stage0_pins(self.root)
        pin = self.root / "src/stage0"
        old = f"{relative}={payloads[relative]}"
        text = pin.read_text(encoding="utf-8")
        self.assertEqual(text.count(old), 1)
        pin.write_text(text.replace(old, f"{relative}={hashlib.sha256(archive.read_bytes()).hexdigest()}"), encoding="utf-8")
        pins, payloads = recreate_bootstrap.parse_stage0_pins(self.root)
        (stage0 / ".rustc-stamp").write_text(
            recreate_bootstrap.stage0_extraction_stamp({**pins, **payloads}), encoding="utf-8"
        )
        hydrated = self.checkout_state()
        with patch.object(recreate_bootstrap._seed_transport(), "run_custodied_command",
                          side_effect=self.fixture_seed_child):
            rc, _rows, out, _ = self.run_main(
                "--check", *self.SEED_STAGE2, real_selection=True,
                environ={"TMPDIR": str(temporary), "STAGE0_PROBES": str(probes)},
            )
        self.assertEqual(rc, 0, out)
        self.assertIn("pinned archives validated", out)
        self.assert_checkout_unchanged(hydrated, "--check with a hydrated stage0")
        (probe_directory,) = probes.read_text(encoding="utf-8").split()
        self.assertEqual(Path(probe_directory).parent, temporary)
        self.assertEqual(list(temporary.iterdir()), [])

        # Not vacuous: the same child, left to itself, does write here.
        unguarded = self.run_freshness_check_unguarded("--require-payloads", "--host", self.HOST)
        self.assertEqual(unguarded.returncode, 0, unguarded.stdout + unguarded.stderr)
        self.assert_cached_bytecode_appeared(hydrated)

    def test_check_help_promises_the_checkout_and_names_its_scratch_space(self):
        """What the two tests around this one hold `--check` to, as the help states it.

        Until 2026-10-12 it said "do not write anything", which the bytecode
        cache made false in the checkout and the two probes below make false
        outside it.
        """
        shown = io.StringIO()
        with patch.dict(
            os.environ, {"COLUMNS": "100000", "NO_COLOR": "1"}, clear=True
        ), patch.object(sys, "stdout", shown), self.assertRaises(SystemExit) as stopped:
            recreate_bootstrap.parse_args(["--help"])
        self.assertEqual(stopped.exception.code, 0)
        text = " ".join(shown.getvalue().split())
        self.assertNotIn("do not write anything", text)
        for sentence in (
            "a check creates, changes and removes nothing in it, not even a Python bytecode cache",
            "Its only scratch space is the temporary directory (TMPDIR), in directories it "
            "removes before it returns: the throwaway Cargo home of the atpkg manifest-schema "
            "probe, the selected seed Targo snapshot used for runtime inspection, and the "
            "one-file crate the seed validation compiles when the hydrated stage0 carries "
            "the pinned date.",
            # What the promise does not reach, by name: an independent audit of
            # a Stage 2 seed-mode check on a Mac (2026-10-12) saw it start
            # `brew --prefix libgit2` twice, `rustup --version` once and the
            # hydrated stage0's rustc twice, none of which the first wording
            # of this sentence named. "among them": the list is not complete.
            "Not covered: whatever the interpreter, or a tool the check runs (among them "
            "git, cargo, rustup, brew, atpkg, xcrun, the hydrated stage0 compiler and each "
            "native build tool it identifies), keeps for itself outside the checkout.",
            "With --verify-stage-provenance that verification runs instead of a check.",
        ):
            self.assertIn(sentence, text)
        # Every scratch owner must be named in the check's help contract.
        validation = SCRIPT.with_name("check_seed_freshness.py").read_text(encoding="utf-8")
        for source, users in ((SCRIPT.read_text(encoding="utf-8"), 4), (validation, 1)):
            # Each source's own mentions: the recreator's four are the seed
            # runtime inspection and the schema probe, which the help names,
            # and the submodule materialization's container and the transfer
            # directory _agh_transfer_paths gives Agh, which a check never
            # reaches (main() returns before ensure_submodules(), and
            # fetch-source-pin is a command of its own).
            self.assertEqual(
                len(re.findall(r"\btempfile\.(?:TemporaryDirectory|mkdtemp|mkstemp|NamedTemporaryFile)\(", source)),
                users,
            )

    def test_the_lineage_freshness_check_leaves_the_checkout_as_it_found_it(self):
        """The same child on the `--verify-stage-provenance` path.

        capture_validated_seed_lineage() starts it without `--host`, so it
        imports mint_seed_support (native_payload_host) whatever the checkout
        holds, and `--verify-stage-provenance` is documented read-only too.
        """
        self.materialize_seed_checkout()
        before = self.checkout_state()
        with self.host():
            lineage = recreate_bootstrap.capture_validated_seed_lineage(self.root, self.HOST)
        # The child ran to a verdict (which one depends on the machine: the
        # fixture's payloads are HOST's, and without `--host` it wants the
        # native host's).
        freshness = lineage["authority"]["freshness_check"]
        self.assertIn(freshness["exit_code"], (0, 1), freshness)
        self.assert_checkout_unchanged(before, "the lineage capture's freshness check")
        unguarded = self.run_freshness_check_unguarded("--require-payloads")
        self.assertIn(unguarded.returncode, (0, 1), unguarded.stdout + unguarded.stderr)
        self.assert_cached_bytecode_appeared(before)

    def test_python_children_a_check_can_reach_are_told_not_to_cache_bytecode(self):
        """Each one's environment, where the recreator hands it over.

        Every check runs the interpreter search (check_prereqs() asks it for
        its `python ≥ 3.11` row; under python < 3.11 ensure_python_311() asks
        it too, before `--check` is even parsed) and a seed-mode check runs
        the seed validation. Both children are read off subprocess.run here,
        where each is started, so that the environment each is handed is seen
        and not only what it then leaves in the checkout.
        """
        seen = []

        def record(command, **options):
            seen.append((command, options.get("env")))
            return SimpleNamespace(stdout="(3, 14)\n", stderr="", returncode=0)

        with patch.dict(os.environ, {"PATH": str(self.bin)}, clear=True), patch.object(
            recreate_bootstrap, "which", return_value=None
        ), patch.object(recreate_bootstrap.subprocess, "run", side_effect=record), patch.object(
            recreate_bootstrap._seed_transport(), "run_custodied_command", side_effect=record
        ):
            self.assertEqual(recreate_bootstrap.find_python_ge_311(), sys.executable)
            self.assertTrue(recreate_bootstrap.validate_seed(self.root, self.HOST))
            # Nothing of the caller's environment is replaced by it.
            self.assertNotIn("PYTHONDONTWRITEBYTECODE", os.environ)
        self.assertEqual(
            [command[:2] for command, _ in seen],
            [
                [sys.executable, "-c"],
                [sys.executable, str(self.root / "scripts" / "check_seed_freshness.py")],
            ],
        )
        for command, environment in seen:
            with self.subTest(command=command[:2]):
                self.assertEqual(
                    environment, {"PATH": str(self.bin), "PYTHONDONTWRITEBYTECODE": "1"}
                )

    def test_the_seed_host_ledger_helper_is_loaded_without_a_bytecode_cache(self):
        """The one checkout module the recreator loads into its own process.

        `--verify-stage-provenance` reaches it (a seed ledger with host
        records). The script is loaded here from a copy in a scratch directory,
        beside a copy of the helper, because the real scripts/ directory may
        already hold a current cache, which would hide a write.
        """
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copyfile(SCRIPT.with_name("seed_host_ledger.py"), scripts / "seed_host_ledger.py")
        # The cache beside the source, whatever the interpreter running this
        # test was told (`-B`, PYTHONDONTWRITEBYTECODE, a cache prefix as on
        # Apple's /usr/bin/python3): both are read at import time.
        beside_the_source = patch.object(sys, "pycache_prefix", None)
        for writes_bytecode in (True, False):
            with self.subTest(interpreter_writes_bytecode=writes_bytecode), patch.object(
                recreate_bootstrap, "__file__", str(scripts / "recreate_bootstrap.py")
            ), beside_the_source, patch.object(sys, "dont_write_bytecode", not writes_bytecode):
                helper = recreate_bootstrap.seed_host_ledger_module()
                self.assertTrue(callable(helper.select_host_record))
                self.assertEqual(
                    sorted(path.name for path in scripts.iterdir()), ["seed_host_ledger.py"]
                )
                # The caller's setting is put back, whichever it was.
                self.assertEqual(sys.dont_write_bytecode, not writes_bytecode)
        # Not vacuous: loaded the ordinary way, the helper is cached here.
        with beside_the_source, patch.object(sys, "dont_write_bytecode", False):
            spec = importlib.util.spec_from_file_location(
                "seed_host_ledger_control", scripts / "seed_host_ledger.py"
            )
            spec.loader.exec_module(importlib.util.module_from_spec(spec))
        self.assertTrue(any((scripts / "__pycache__").glob("seed_host_ledger.*.pyc")))


@unittest.skipUnless(sys.version_info >= (3, 11), "atpkg metadata requires tomllib")
class AtpkgStage0AuthorityTests(unittest.TestCase):
    @staticmethod
    def authority_snapshot(identity="original"):
        authority = {
            "evidence_class": "local-offline-tree-match",
            "fresh_signature_replay": False,
            "release_authority": False,
            "trusted_computing_base": ["local-atpkg-verifier", "local-status.toml-tree-root"],
            "pack": {"test_identity": identity},
            "verifier": {"test_identity": identity},
            "measured_tree_root": "a" * 64,
        }
        return {
            "schema": "trust.atpkg-stage0-authority.v1",
            "status": "local-verified",
            "authority": authority,
            "authority_sha256": hashlib.sha256(
                json.dumps(authority, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest(),
            "errors": [],
        }

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.prefix = self.root / "pkg"
        self.pack = self.prefix / "store/trust/42"
        (self.pack / "bin").mkdir(parents=True)
        (self.prefix / "bin").mkdir()
        (self.pack.parent / "current").symlink_to(self.pack, target_is_directory=True)
        self.table = {}
        for key, name in recreate_bootstrap.ATPKG_STAGE0_TOOLS.items():
            path = self.pack / "bin" / name
            path.write_bytes(f"fixture {name}".encode())
            path.chmod(0o755)
            self.table[key] = str(path)
        (self.pack / "bin/targo").write_bytes(b"fixture targo")
        (self.pack / "bin/targo").chmod(0o755)
        for name in ("trustc", "targo", "trustdoc", "trustfmt", "targo-tippy"):
            shim = self.prefix / "bin" / name
            shim.write_text(f'#!/bin/sh\nexec \'{self.pack / "bin" / name}\' "$@"\n')
            shim.chmod(0o755)
        self.status_path = self.prefix / "status.toml"
        self.status_path.write_text(
            'schema = 1\n[programs.trust]\ninstalled_build = 42\ntree_root = "' + "a" * 64 + '"\n'
        )
        self.verifier = self.root / "atpkg"
        self.verifier.write_bytes(b"fixture verifier")
        self.verifier.chmod(0o755)
        self.verify_result = SimpleNamespace(
            returncode=0, stdout="atpkg: trust build 42 OK (matches signed tree_root)\n", stderr=""
        )
        self.tree_result = SimpleNamespace(returncode=0, stdout="a" * 64 + "\n", stderr="")
        self.during_verify = None
        self.calls = []
        stack = self.enterContext(ExitStack())
        stack.enter_context(patch.object(recreate_bootstrap, "_atpkg_prefix", return_value=self.prefix))
        stack.enter_context(patch.object(recreate_bootstrap.shutil, "which", return_value=str(self.verifier)))
        stack.enter_context(patch.object(recreate_bootstrap.subprocess, "run", side_effect=self.run_verifier))

    def run_verifier(self, argv, **kwargs):
        self.calls.append(argv)
        self.assertEqual(argv[0], str(self.verifier))
        if argv[1:] == ["verify", "trust"]:
            if self.during_verify is not None:
                self.during_verify()
            return self.verify_result
        self.assertEqual(argv[1:], ["tree-root", str(self.pack)])
        return self.tree_result

    def capture(self, table=None):
        return recreate_bootstrap._capture_atpkg_stage0_authority(self.table if table is None else table)

    def select(self, *argv):
        return recreate_bootstrap.resolve_stage0_selection(
            self.root, recreate_bootstrap.parse_args(list(argv))
        )

    def config(self, mode, *, legacy=False):
        path = self.root / ("config.toml" if legacy else "bootstrap.toml")
        content = f"# ({mode} stage0 mode)\n[build]\n"
        if mode == "atpkg":
            content += "\n".join(f'{key} = "{value}"' for key, value in self.table.items())
        elif mode == "genesis":
            content += 'rustc = "/fixture/genesis-stage0/bin/trustc"\n'
        path.write_text(content)
        return path

    def test_selection_local_atpkg_skips_unused_archives_and_retains_exact_pack(self):
        with patch.object(recreate_bootstrap, "resolve_seed") as seed:
            selected = self.select("--require-seed", "--no-fetch")
        seed.assert_not_called()
        self.assertEqual(selected.mode, "atpkg")
        self.assertEqual(selected.atpkg_root, self.pack)
        self.assertTrue(recreate_bootstrap._atpkg_authority_ready(selected.atpkg_authority))
        with patch.object(recreate_bootstrap, "atpkg_trust_sysroot", side_effect=AssertionError("must not reselect")), patch.object(
            recreate_bootstrap, "find_python_ge_311", return_value=sys.executable
        ):
            config = recreate_bootstrap.write_config(self.root, "test-host", False, selection=selected).path
        import tomllib
        table = tomllib.loads(config.read_text())["build"]
        self.assertEqual({key: table[key] for key in self.table}, self.table)
        self.assertIn("(atpkg stage0 mode)", config.read_text())

    def test_selection_fresh_seed_forces_archives_and_writer_never_reselects_atpkg(self):
        with patch.object(recreate_bootstrap, "atpkg_trust_sysroot", side_effect=AssertionError("fresh must not probe atpkg")), patch.object(
            recreate_bootstrap, "resolve_seed", return_value=True
        ) as seed, patch.object(recreate_bootstrap, "find_python_ge_311", return_value=sys.executable):
            selected = self.select("--fresh-seed", "--require-seed", "--no-fetch")
            config = recreate_bootstrap.write_config(self.root, "test-host", False, selection=selected).path
        seed.assert_called_once_with(self.root, allow_fetch=False, host=recreate_bootstrap.host_triple(),
                                     use_store=True)
        self.assertEqual(selected.mode, "seed")
        self.assertIn("(seed stage0 mode)", config.read_text())
        self.assertNotIn(str(self.pack), config.read_text())

    def test_no_atpkg_skips_discovery_but_requires_explicit_config_replacement(self):
        with patch.object(recreate_bootstrap, "atpkg_trust_sysroot", side_effect=AssertionError("no discovery")), patch.object(
            recreate_bootstrap, "resolve_seed", return_value=True
        ) as seed:
            self.assertEqual(self.select("--no-atpkg", "--require-seed").mode, "seed")
            seed.assert_called_once()
            seed.reset_mock()
            config = self.config("atpkg")
            before = config.read_bytes()
            with self.assertRaisesRegex(RuntimeError, "--no-atpkg excludes"):
                self.select("--no-atpkg", "--require-seed")
            seed.assert_not_called()
            self.assertEqual(config.read_bytes(), before)
            self.assertEqual(self.select("--no-atpkg", "--require-seed", "--force-config").mode, "seed")

    def test_active_schema_refusal_uses_archives_not_a_different_staged_pack(self):
        refusal = (self.root / "Cargo.toml", "unknown field `future_key`")
        with patch.object(recreate_bootstrap, "stage0_refuses_tree_manifest", return_value=refusal) as probe, patch.object(
            recreate_bootstrap, "resolve_seed", return_value=True
        ) as seed:
            self.assertEqual(self.select("--require-seed").mode, "seed")
            probe.assert_called_once_with(self.pack, self.root)
            seed.assert_called_once()
            seed.reset_mock()
            self.config("atpkg")
            with self.assertRaisesRegex(RuntimeError, "manifest schema"):
                self.select("--require-seed")
            seed.assert_not_called()

    def test_schema_capability_never_replaces_rejected_local_authority(self):
        self.verify_result.stdout = "not the exact tree match"
        with patch.object(recreate_bootstrap, "stage0_refuses_tree_manifest") as probe, patch.object(
            recreate_bootstrap, "resolve_seed", return_value=True
        ):
            self.assertEqual(self.select("--require-seed").mode, "seed")
        probe.assert_not_called()

    def test_selection_preserves_existing_seed_mode_and_bytes(self):
        config = self.config("seed")
        original = config.read_bytes()
        with patch.object(recreate_bootstrap, "resolve_seed", return_value=True), patch.object(
            recreate_bootstrap, "atpkg_trust_sysroot", side_effect=AssertionError("must keep config mode")
        ):
            selected = self.select("--require-seed", "--check")
            identity = recreate_bootstrap.write_config(self.root, "test-host", False, selection=selected)
            self.assertEqual(identity.path, config)
            self.assertEqual(identity.sha256, hashlib.sha256(original).hexdigest())
        self.assertEqual(selected.mode, "seed")
        self.assertEqual(config.read_bytes(), original)

    def test_selection_reads_the_stage1_seed_switch_of_the_existing_config(self):
        # DC-16c: `rust.trust-stage1-seed = false` keeps atpkg's store out of the seed too.
        config = self.config("seed")
        config.write_text(config.read_text() + "[rust]\ntrust-stage1-seed = false\n")
        with patch.object(recreate_bootstrap, "resolve_seed", return_value=True) as seed:
            self.assertEqual(self.select("--require-seed").mode, "seed")
        self.assertIs(seed.call_args.kwargs["use_store"], False)

    def test_selection_existing_seed_unavailable_never_silently_falls_back(self):
        self.config("seed")
        with patch.object(recreate_bootstrap, "resolve_seed", return_value=False):
            with self.assertRaisesRegex(RuntimeError, "refusing genesis fallback"):
                self.select("--no-fetch")

    def test_selection_rejected_existing_atpkg_never_falls_back_or_fetches(self):
        self.config("atpkg")
        self.verify_result.stdout = "atpkg: trust uses a wired sysroot\n"
        with patch.object(recreate_bootstrap, "resolve_seed") as seed:
            with self.assertRaisesRegex(RuntimeError, "atpkg authority rejected"):
                self.select("--require-seed")
        seed.assert_not_called()

    def test_selection_rejected_new_atpkg_can_use_validated_archives_only(self):
        self.verify_result.stdout = "not an exact tree match\n"
        with patch.object(recreate_bootstrap, "resolve_seed", return_value=True) as seed:
            self.assertEqual(self.select("--require-seed").mode, "seed")
        seed.assert_called_once_with(self.root, allow_fetch=True, host=recreate_bootstrap.host_triple(),
                                     use_store=True)
        with patch.object(recreate_bootstrap, "resolve_seed", return_value=False):
            with self.assertRaisesRegex(RuntimeError, "refusing genesis fallback"):
                self.select("--require-seed")

    def test_selection_existing_mode_conflicts_refuse_before_resolution(self):
        config = self.config("atpkg")
        with patch.object(recreate_bootstrap, "resolve_seed") as seed:
            for argv in (("--fresh-seed", "--require-seed"), ("--genesis",)):
                with self.subTest(argv=argv), self.assertRaisesRegex(RuntimeError, "use --force-config"):
                    self.select(*argv)
            config.write_text('# (genesis stage0 mode)\n[build]\nrustc = "/fixture/genesis-stage0/bin/trustc"\n')
            with self.assertRaisesRegex(RuntimeError, "use --genesis deliberately"):
                self.select("--require-seed")
            self.assertEqual(self.select("--genesis").mode, "genesis")
        seed.assert_not_called()

    def test_selection_force_legacy_config_reuses_path_without_creating_second_config(self):
        config = self.config("genesis", legacy=True)
        selected = self.select("--force-config", "--require-seed")
        with patch.object(recreate_bootstrap, "find_python_ge_311", return_value=sys.executable):
            written = recreate_bootstrap.write_config(self.root, "test-host", True, selection=selected)
        self.assertEqual(written.path, config)
        self.assertEqual(written.sha256, hashlib.sha256(config.read_bytes()).hexdigest())
        self.assertIn("(atpkg stage0 mode)", config.read_text())
        self.assertFalse((self.root / "bootstrap.toml").exists())

    def test_selection_refuses_ambiguous_malformed_or_symlink_configs(self):
        config = self.config("seed")
        legacy = self.config("seed", legacy=True)
        with patch.object(recreate_bootstrap, "resolve_seed") as seed:
            with self.assertRaisesRegex(RuntimeError, "both bootstrap.toml and config.toml"):
                self.select("--force-config")
            legacy.unlink()
            for content in (b"invalid = [", b"[build]\n", b"\xff"):
                config.write_bytes(content)
                with self.subTest(content=content), self.assertRaisesRegex(RuntimeError, "use --force-config"):
                    self.select()
            config.unlink()
            config.symlink_to(self.root / "absent-target")
            with self.assertRaisesRegex(RuntimeError, "non-symlink"):
                self.select("--force-config")
        seed.assert_not_called()

    def test_selection_concurrent_config_change_is_not_overwritten(self):
        config = self.config("genesis")
        selected = self.select("--force-config", "--require-seed")
        config.write_bytes(b"user concurrent edit")
        with self.assertRaisesRegex(RuntimeError, "changed after stage0 selection"):
            recreate_bootstrap.write_config(self.root, "test-host", True, selection=selected)
        self.assertEqual(config.read_bytes(), b"user concurrent edit")

    def test_selection_check_is_read_only_no_archives_or_stock_prerequisites(self):
        with ExitStack() as stack:
            for name in ("ensure_python_311", "line_buffer_output", "print_prereqs"):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            stack.enter_context(patch.object(recreate_bootstrap, "repo_root", return_value=self.root))
            prereqs = stack.enter_context(patch.object(recreate_bootstrap, "check_prereqs", return_value=[]))
            seed = stack.enter_context(patch.object(recreate_bootstrap, "resolve_seed"))
            writes = [stack.enter_context(patch.object(recreate_bootstrap, name)) for name in (
                "write_config", "ensure_submodules", "ensure_local_genesis_stage0", "run_xpy_build"
            )]
            self.assertEqual(recreate_bootstrap.main(["--check", "--require-seed", "--no-register"]), 0)
        self.assertTrue(prereqs.call_args.kwargs["seed_mode"])
        seed.assert_not_called()
        for mutation in writes:
            mutation.assert_not_called()
        self.assertFalse((self.root / "bootstrap.toml").exists())

    def test_selection_authority_drift_refuses_before_build(self):
        selected = self.select("--require-seed")
        changed = copy.deepcopy(selected.atpkg_authority)
        changed["authority"]["measured_tree_root"] = "b" * 64
        changed["authority_sha256"] = hashlib.sha256(
            json.dumps(changed["authority"], sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        with ExitStack() as stack:
            for name in ("ensure_python_311", "line_buffer_output", "print_prereqs", "ensure_submodules"):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            stack.enter_context(patch.object(recreate_bootstrap, "write_config", return_value=recreate_bootstrap.WrittenBootstrapConfig(
                self.root / "bootstrap.toml", "a" * 64
            )))
            stack.enter_context(patch.object(recreate_bootstrap, "repo_root", return_value=self.root))
            stack.enter_context(patch.object(recreate_bootstrap, "resolve_stage0_selection", return_value=selected))
            stack.enter_context(patch.object(recreate_bootstrap, "check_prereqs", return_value=[]))
            stack.enter_context(patch.object(recreate_bootstrap, "capture_source_lineage", return_value={
                "status": "candidate", "closure_sha256": "a" * 64,
            }))
            stack.enter_context(patch.object(recreate_bootstrap, "capture_bootstrap_lineage", return_value={
                "status": "local_atpkg", "mode": "atpkg", "config_sha256": "a" * 64,
                "config_path": "bootstrap.toml",
                "atpkg_authority": changed, "errors": [],
            }))
            run = stack.enter_context(patch.object(recreate_bootstrap, "run_xpy_build"))
            self.assertEqual(recreate_bootstrap.main(["--require-seed", "--no-register"]), 1)
        run.assert_not_called()

    def test_selected_compiler_probe_never_uses_unrelated_extracted_stage0(self):
        driver = self.pack / "bin/trustc"
        with patch.object(recreate_bootstrap.subprocess, "run", return_value=SimpleNamespace(
            returncode=0, stdout=b"    -Z trust-verify=val -- verification\n"
        )) as probe:
            self.assertEqual(recreate_bootstrap.seed_verification_off_switch(
                self.root, "test-host", {}, compiler=driver
            ), "flag")
        self.assertEqual(probe.call_args.args[0], [str(driver), "-Z", "help"])

    def test_selection_same_mode_config_drift_after_write_refuses_before_build(self):
        def mutate_config(*_args):
            config = self.root / "bootstrap.toml"
            config.write_text(config.read_text() + '\n# concurrent config change\n')
            return {"status": "candidate", "closure_sha256": "a" * 64}

        with ExitStack() as stack:
            for name in ("ensure_python_311", "line_buffer_output", "print_prereqs", "ensure_submodules"):
                stack.enter_context(patch.object(recreate_bootstrap, name))
            stack.enter_context(patch.object(recreate_bootstrap, "repo_root", return_value=self.root))
            stack.enter_context(patch.object(recreate_bootstrap, "find_python_ge_311", return_value=sys.executable))
            stack.enter_context(patch.object(recreate_bootstrap, "check_prereqs", return_value=[]))
            stack.enter_context(patch.object(recreate_bootstrap, "capture_source_lineage", side_effect=mutate_config))
            run = stack.enter_context(patch.object(recreate_bootstrap, "run_xpy_build"))
            self.assertEqual(recreate_bootstrap.main(["--require-seed", "--no-register"]), 1)
        run.assert_not_called()
        self.assertIn("concurrent config change", (self.root / "bootstrap.toml").read_text())

    def test_selection_matching_atpkg_config_and_authority_launch_selected_compiler(self):
        cases = [(2, [], False), (0, ["compiler/rustc"], True),
                 (1, ["compiler/rustc"], True),
                 (1, ["compiler/rustc", "--set", "rust.debug=true"], False),
                 (1, ["compiler/rustc", "--config", "custom.toml"], False)]
        for stage, extra, owned in cases:
            with self.subTest(stage=stage, extra=extra), ExitStack() as stack:
                for name in ("ensure_python_311", "line_buffer_output", "print_prereqs", "ensure_submodules"):
                    stack.enter_context(patch.object(recreate_bootstrap, name))
                stack.enter_context(patch.object(recreate_bootstrap, "repo_root", return_value=self.root))
                stack.enter_context(patch.object(recreate_bootstrap, "find_python_ge_311", return_value=sys.executable))
                stack.enter_context(patch.object(recreate_bootstrap, "check_prereqs", return_value=[]))
                stack.enter_context(patch.object(recreate_bootstrap, "capture_source_lineage", return_value={
                    "status": "candidate", "closure_sha256": "a" * 64,
                }))
                stack.enter_context(patch.object(recreate_bootstrap, "capture_build_authority", return_value={
                    "status": "ready", "authority_sha256": "b" * 64,
                }))
                stack.enter_context(patch.object(
                    recreate_bootstrap, "capture_llvm_before_build",
                    return_value=StageToolProvenanceTests.llvm_observation(),
                ))
                # Stop at launch; this fixture never executes a compiler or installer.
                run = stack.enter_context(patch.object(recreate_bootstrap, "run_xpy_build", return_value=7))
                seed = stack.enter_context(patch.object(recreate_bootstrap, "resolve_seed"))
                arguments = ["--stage", str(stage), "--require-seed", "--no-register"]
                if extra:
                    arguments += ["--", *extra]
                self.assertEqual(recreate_bootstrap.main(arguments), 7)
            run.assert_called_once()
            self.assertTrue(run.call_args.kwargs["seed_mode"])
            self.assertEqual(run.call_args.kwargs["seed_compiler"], self.pack / "bin/trustc")
            if owned:
                config = self.root / "bootstrap.toml"
                self.assertEqual(run.call_args.kwargs["normal_config"],
                                 recreate_bootstrap.WrittenBootstrapConfig(
                                     config, hashlib.sha256(config.read_bytes()).hexdigest()))
            else:
                self.assertNotIn("normal_config", run.call_args.kwargs)
            seed.assert_not_called()

    def test_exact_active_pack_is_offline_local_evidence(self):
        snapshot = self.capture()
        self.assertTrue(recreate_bootstrap._atpkg_authority_ready(snapshot), snapshot)
        authority = snapshot["authority"]
        self.assertFalse(authority["fresh_signature_replay"])
        self.assertFalse(authority["release_authority"])
        self.assertEqual(authority["pack"]["build"], 42)
        self.assertEqual(set(authority["pack"]["configured_tools"]), set(self.table))
        self.assertEqual(authority["verifier"]["sha256"], hashlib.sha256(b"fixture verifier").hexdigest())
        self.assertEqual(len(self.calls), 2)

    def test_selector_uses_current_not_newest_staged_pack(self):
        staged = self.pack.parent / "999/bin"
        staged.mkdir(parents=True)
        for name in recreate_bootstrap.ATPKG_STAGE0_TOOLS.values():
            (staged / name).write_bytes(b"newer but not active")
            (staged / name).chmod(0o755)
        self.assertEqual(recreate_bootstrap.atpkg_trust_sysroot(), self.pack)
        self.assertEqual(self.calls, [])
        (self.pack.parent / "current").unlink()
        self.assertIsNone(recreate_bootstrap.atpkg_trust_sysroot())

    def test_verifier_symlink_preserves_multicall_invocation_path(self):
        executable = self.verifier
        alias = self.root / "aliases/atpkg"
        alias.parent.mkdir()
        alias.symlink_to(executable)
        self.verifier = alias
        with patch.object(recreate_bootstrap.shutil, "which", return_value=str(alias)):
            result = self.capture()
        self.assertEqual(result["status"], "local-verified", result)
        self.assertEqual(result["authority"]["verifier"]["resolved_real_path"], str(executable))
        self.assertEqual([argv[0] for argv in self.calls], [str(alias), str(alias)])

    def test_every_configured_tool_is_required_and_exact_before_verification(self):
        for key in self.table:
            for replacement in (None, "/ambient/stock", str(self.pack) + "-spoof/bin/trustc"):
                with self.subTest(key=key, replacement=replacement):
                    table = dict(self.table)
                    if replacement is None:
                        del table[key]
                    else:
                        table[key] = replacement
                    result = self.capture(table)
                    self.assertEqual(result["status"], "rejected")
                    self.assertIn(key, result["errors"][0])
        self.assertEqual(self.calls, [])

    def test_symlink_escape_and_missing_tool_fail_before_verification(self):
        tool = self.pack / "bin/trustfmt"
        original = tool.read_bytes()
        tool.unlink()
        self.assertEqual(self.capture()["status"], "rejected")
        outside = self.root / "ambient-formatter"
        outside.write_bytes(original)
        outside.chmod(0o755)
        tool.symlink_to(outside)
        self.assertEqual(self.capture()["status"], "rejected")
        self.assertEqual(self.calls, [])

    def test_nonexecutable_tool_is_not_a_usable_stage0(self):
        (self.pack / "bin/targo-tippy").chmod(0o644)
        self.assertIsNone(recreate_bootstrap.atpkg_trust_sysroot())
        self.assertEqual(self.capture()["status"], "rejected")

    def test_legacy_symlink_shims_are_supported(self):
        for shim in (self.prefix / "bin").iterdir():
            shim.unlink()
            shim.symlink_to(self.pack / "bin" / shim.name)
        self.assertEqual(self.capture()["status"], "local-verified")

    def test_mixed_active_shims_are_rejected_even_outside_required_roster(self):
        other = self.pack.parent / "43/bin/clean"
        other.parent.mkdir(parents=True)
        other.write_bytes(b"other build")
        other.chmod(0o755)
        extra = self.prefix / "bin/clean"
        extra.symlink_to(other)
        self.assertEqual(self.capture()["status"], "rejected")
        self.assertEqual(self.calls, [])

    def test_missing_or_mispointed_required_shim_is_rejected(self):
        shim = self.prefix / "bin/trustdoc"
        shim.unlink()
        self.assertEqual(self.capture()["status"], "rejected")
        shim.symlink_to(self.pack / "bin/trustc")
        self.assertEqual(self.capture()["status"], "rejected")

    def test_extra_shim_cannot_traverse_or_name_a_foreign_store(self):
        other = self.root / "foreign/store/trust/42/bin/clean"
        other.parent.mkdir(parents=True)
        other.write_bytes(b"foreign pack")
        other.chmod(0o755)
        extra = self.prefix / "bin/clean"
        for target in (other, self.pack / "../42/bin/trustc"):
            with self.subTest(target=target):
                extra.symlink_to(target)
                self.assertEqual(self.capture()["status"], "rejected")
                extra.unlink()

    def test_zero_exit_is_not_authority_without_exact_match(self):
        for stdout, stderr, rc in (
            ("", "", 0),
            ("atpkg: trust build 42 OK (rustup-linked sysroot bundle; verified at install)", "", 0),
            ("atpkg: trust build 43 OK (matches signed tree_root)", "", 0),
            (self.verify_result.stdout, "unexpected warning", 0),
            (self.verify_result.stdout, "", 1),
        ):
            with self.subTest(stdout=stdout, stderr=stderr, rc=rc):
                self.verify_result = SimpleNamespace(returncode=rc, stdout=stdout, stderr=stderr)
                self.assertEqual(self.capture()["status"], "rejected")
        self.assertEqual(len(self.calls), 5)

    def test_explicit_tree_root_must_match_selected_local_record(self):
        for stdout, stderr, rc in (("b" * 64, "", 0), ("a" * 64, "", 1), ("a" * 64, "error", 0)):
            with self.subTest(stdout=stdout, stderr=stderr, rc=rc):
                self.tree_result = SimpleNamespace(returncode=rc, stdout=stdout, stderr=stderr)
                self.assertEqual(self.capture()["status"], "rejected")

    def test_wired_sysroot_is_rejected_even_if_verifier_would_claim_match(self):
        (self.pack / "toolchain").symlink_to(self.root, target_is_directory=True)
        self.assertEqual(self.capture()["status"], "rejected")
        self.assertEqual(self.calls, [])

    def test_invalid_or_wrong_build_status_fails_closed(self):
        for content in (
            "[broken",
            'schema = 1\n[programs.trust]\ninstalled_build = 43\ntree_root = "' + "a" * 64 + '"',
            'schema = 1\n[programs.trust]\ninstalled_build = 42\ntree_root = ""',
            'schema = 2\n[programs.trust]\ninstalled_build = 42\ntree_root = "' + "a" * 64 + '"',
            'schema = true\n[programs.trust]\ninstalled_build = 42\ntree_root = "' + "a" * 64 + '"',
            'schema = 1\n[programs.trust]\ninstalled_build = true\ntree_root = "' + "a" * 64 + '"',
        ):
            with self.subTest(content=content):
                self.status_path.write_text(content)
                self.assertEqual(self.capture()["status"], "rejected")
        self.assertEqual(self.calls, [])

    def test_verifier_and_tool_replacement_during_capture_are_rejected(self):
        for path in (self.verifier, self.pack / "bin/cargo"):
            with self.subTest(path=path):
                old = path.read_bytes()
                self.during_verify = lambda: path.write_bytes(b"changed during capture")
                self.assertEqual(self.capture()["status"], "rejected")
                path.write_bytes(old)

    def test_status_root_and_current_changes_during_capture_are_rejected(self):
        original = self.status_path.read_text()
        self.during_verify = lambda: self.status_path.write_text(original.replace("a" * 64, "b" * 64))
        self.assertEqual(self.capture()["status"], "rejected")
        self.status_path.write_text(original)
        def remove_current():
            (self.pack.parent / "current").unlink()
        self.during_verify = remove_current
        self.assertEqual(self.capture()["status"], "rejected")

    def test_path_verifier_selection_cannot_change_during_capture(self):
        with patch.object(
            recreate_bootstrap.shutil, "which", side_effect=[str(self.verifier), "/other/atpkg"]
        ):
            self.assertEqual(self.capture()["status"], "rejected")

    def test_unrelated_status_diagnostics_do_not_change_pack_identity(self):
        first = self.capture()
        self.status_path.write_text(
            'schema = 1\nupdated_at = "later"\n[programs.trust]\ninstalled_build = 42\n'
            'state = "diagnostics changed"\ntree_root = "' + "a" * 64 + '"\n'
            '[programs.other]\ninstalled_build = 99\n'
        )
        self.assertEqual(first, self.capture())

    def test_lineage_binds_local_atpkg_without_minting_genesis_or_release(self):
        config = self.root / "bootstrap.toml"
        config.write_text(
            "# (atpkg stage0 mode)\n[build]\n"
            + "\n".join(f'{key} = "{value}"' for key, value in self.table.items())
        )
        before = recreate_bootstrap.capture_bootstrap_lineage(self.root, "test-host")
        after = recreate_bootstrap.capture_bootstrap_lineage(self.root, "test-host")
        bound = recreate_bootstrap._bind_bootstrap_lineage(before, after)
        self.assertEqual(bound["status"], "local_atpkg", bound)
        self.assertTrue(bound["trust_from_trust"])
        self.assertTrue(bound["stable_across_build"])
        self.assertTrue(bound["atpkg_authority"]["stable_across_build"])
        self.assertEqual(recreate_bootstrap._classify_receipt_status("immutable_release", bound), "candidate-ready")

        for change in ("replacement", "missing", "forged", "release"):
            with self.subTest(change=change):
                changed = copy.deepcopy(after)
                if change == "replacement":
                    changed["atpkg_authority"] = self.authority_snapshot("replacement")
                elif change == "missing":
                    changed["atpkg_authority"] = None
                elif change == "forged":
                    changed["atpkg_authority"]["authority_sha256"] = "0" * 64
                else:
                    changed["atpkg_authority"]["authority"]["release_authority"] = True
                self.assertEqual(recreate_bootstrap._bind_bootstrap_lineage(before, changed)["status"], "rejected")


@unittest.skipUnless(sys.version_info >= (3, 11), "atpkg metadata requires tomllib")
class MintedPinRetiresAtpkgStage0Tests(unittest.TestCase):
    """D12 (d): the first minted re-pin retires the atpkg stage0 mode and the genesis fallback.

    The fixture is AtpkgStage0AuthorityTests' verified local pack, so every
    refusal below is the ledger's doing, not a pack that failed its checks.
    """

    setUp = AtpkgStage0AuthorityTests.setUp
    run_verifier = AtpkgStage0AuthorityTests.run_verifier
    select = AtpkgStage0AuthorityTests.select
    config = AtpkgStage0AuthorityTests.config
    LEDGER_HEAD = 'scope = "internal"\n[release]\nrepo = "owner/trust"\ntag = "trust-stage0-fixture"\n'

    def ledger(self, text):
        path = self.root / "bootstrap/trust-stage0/seed-ledger.toml"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def mint(self, shape="single"):
        if shape == "single":
            return self.ledger(self.LEDGER_HEAD + '[release.mint]\npinned_seed_commit = "' + "a" * 40 + '"\n')
        return self.ledger(
            'scope = "internal"\n[release]\nrepo = "owner/trust"\n'
            '[release.hosts."aarch64-apple-darwin"]\ntag = "t"\n'
            '[release.hosts."aarch64-apple-darwin".mint]\npinned_seed_commit = "' + "a" * 40 + '"\n'
        )

    def select_quietly(self, *argv):
        out = io.StringIO()
        with patch("sys.stdout", out):
            selected = self.select(*argv)
        return selected, out.getvalue()

    def test_ledger_reading(self):
        minted = recreate_bootstrap.minted_seed_pin
        self.assertIsNone(minted(self.root), "no ledger: an old checkout, not a minted pin")
        self.ledger(self.LEDGER_HEAD)
        self.assertIsNone(minted(self.root), "a release without a mint is not a minted pin")
        self.ledger('scope = "internal"\n')
        self.assertIsNone(minted(self.root))
        self.mint()
        self.assertIn("[release.mint]", minted(self.root))
        self.mint("hosts")
        self.assertIn('[release.hosts."aarch64-apple-darwin".mint]', minted(self.root))
        self.ledger(self.LEDGER_HEAD.replace("[release]\n", "[release]\nhosts = 1\n"))
        self.assertIn("read as a minted pin", minted(self.root))
        self.ledger('scope = "internal"\n[release]\n[release.hosts]\nx = 1\n')
        self.assertIn('[release.hosts."x"] is not a table', minted(self.root))
        for broken in (b"[release\n", b"\xff"):
            with self.subTest(broken=broken):
                self.ledger("").write_bytes(broken)
                self.assertIn("cannot be read", minted(self.root))
        ledger = self.ledger("")
        ledger.unlink()
        target = self.root / "elsewhere.toml"
        target.write_text(self.LEDGER_HEAD)
        ledger.symlink_to(target)
        self.assertIn("not a regular file", minted(self.root))

    def test_a_fixed_point_record_is_a_pin_without_a_mint(self):
        # A ledger whose only host record is a fixed point (docs/PLAN.md PKG-S6)
        # has no mint table anywhere, and still pins the seed.
        minted = recreate_bootstrap.minted_seed_pin
        table = '[release.hosts."aarch64-unknown-linux-gnu"]\nschema = "trust-seed-fixed-point-host-record-v1"\n'
        self.ledger(self.LEDGER_HEAD + table)
        self.assertIsNone(minted(self.root), "a host table with neither a mint nor a disclosure is unchanged")
        self.ledger(self.LEDGER_HEAD + table
                    + '[release.hosts."aarch64-unknown-linux-gnu".root_disclosure]\nroot = "unpinned-host-chain"\n')
        reason = minted(self.root)
        self.assertIn('[release.hosts."aarch64-unknown-linux-gnu".root_disclosure]', reason)
        self.assertIn("fixed point", reason)
        # ... and retires the atpkg mode and the genesis fallback as a mint does.
        with patch.object(
            recreate_bootstrap, "atpkg_trust_sysroot", side_effect=AssertionError("retired: no discovery")
        ), patch.object(
            recreate_bootstrap, "_capture_atpkg_stage0_authority", side_effect=AssertionError("retired")
        ), patch.object(recreate_bootstrap, "resolve_seed", return_value=True) as seed:
            selected, out = self.select_quietly("--require-seed")
        self.assertEqual(selected.mode, "seed")
        seed.assert_called_once()
        self.assertIn("atpkg stage0 mode retired (D12 (d))", out)
        with patch.object(recreate_bootstrap, "resolve_seed", return_value=False), self.assertRaisesRegex(
            RuntimeError, r"refusing genesis fallback: D12 \(d\)"
        ):
            self.select_quietly()

    def test_unminted_ledger_keeps_the_atpkg_mode(self):
        # Path P of the pending pack cut (release-train handoff §1.0) seeds from it.
        self.ledger(self.LEDGER_HEAD)
        with patch.object(recreate_bootstrap, "resolve_seed") as seed:
            selected, out = self.select_quietly("--require-seed", "--no-fetch")
        seed.assert_not_called()
        self.assertEqual(selected.mode, "atpkg")
        self.assertEqual(selected.atpkg_root, self.pack)
        self.assertNotIn("D12 (d)", out)

    def test_minted_pin_selects_the_pin_without_discovering_a_pack(self):
        for shape in ("single", "hosts"):
            with self.subTest(shape=shape):
                self.mint(shape)
                for argv in ((), ("--require-seed",), ("--require-seed", "--no-fetch"), ("--check",)):
                    with self.subTest(argv=argv), patch.object(
                        recreate_bootstrap, "atpkg_trust_sysroot", side_effect=AssertionError("retired: no discovery")
                    ), patch.object(
                        recreate_bootstrap, "_capture_atpkg_stage0_authority", side_effect=AssertionError("retired")
                    ), patch.object(recreate_bootstrap, "resolve_seed", return_value=True) as seed:
                        selected, out = self.select_quietly(*argv)
                        self.assertEqual(selected.mode, "seed")
                        seed.assert_called_once()
                        self.assertIn("atpkg stage0 mode retired (D12 (d))", out)
                        self.assertNotIn(str(self.pack), out)

    def test_minted_pin_refuses_an_atpkg_config_until_it_is_regenerated(self):
        self.mint()
        config = self.config("atpkg")
        before = config.read_bytes()
        with patch.object(recreate_bootstrap, "resolve_seed", return_value=True) as seed, patch.object(
            recreate_bootstrap, "_capture_atpkg_stage0_authority", side_effect=AssertionError("retired")
        ):
            for argv in ((), ("--require-seed",), ("--no-atpkg", "--require-seed"), ("--fresh-seed", "--require-seed")):
                with self.subTest(argv=argv), self.assertRaisesRegex(
                    RuntimeError, r"atpkg stage0 mode, which D12 \(d\) retires.*--force-config"
                ):
                    self.select(*argv)
            seed.assert_not_called()
            self.assertEqual(config.read_bytes(), before)
            with patch.object(recreate_bootstrap, "atpkg_trust_sysroot", side_effect=AssertionError("retired")):
                selected, _ = self.select_quietly("--force-config", "--require-seed")
            self.assertEqual(selected.mode, "seed")
        with patch.object(recreate_bootstrap, "find_python_ge_311", return_value=sys.executable):
            written = recreate_bootstrap.write_config(self.root, "test-host", True, selection=selected)
        text = written.path.read_text()
        self.assertIn("(seed stage0 mode)", text)
        self.assertNotIn(str(self.pack), text)

    def test_minted_pin_refuses_the_genesis_fallback_but_not_explicit_genesis(self):
        self.mint()
        with patch.object(recreate_bootstrap, "resolve_seed", return_value=False) as seed:
            for argv in ((), ("--no-fetch",), ("--no-atpkg",)):
                with self.subTest(argv=argv), self.assertRaisesRegex(
                    RuntimeError, r"refusing genesis fallback: D12 \(d\).*--genesis"
                ):
                    self.select_quietly(*argv)
            with self.assertRaisesRegex(RuntimeError, "refusing genesis fallback"):
                self.select_quietly("--require-seed")
            self.assertEqual(seed.call_count, 4)
            selected, _ = self.select_quietly("--genesis")
        self.assertEqual(selected.mode, "genesis")

    def test_unminted_ledger_keeps_the_genesis_fallback(self):
        # Retiring the fallback is D12 (d)'s, at the mint; today's behaviour stays until then.
        self.ledger(self.LEDGER_HEAD)
        with patch.object(recreate_bootstrap, "atpkg_trust_sysroot", return_value=None), patch.object(
            recreate_bootstrap, "resolve_seed", return_value=False
        ):
            selected, out = self.select_quietly()
        self.assertEqual(selected.mode, "genesis")
        self.assertIn("genesis fallback", out)


@unittest.skipUnless(sys.version_info >= (3, 11), "bootstrap lineage requires tomllib")
class BootstrapLineageTests(unittest.TestCase):
    def test_seed_marker_refuses_each_historical_stage0_override(self):
        historical_keys = {"rustc", "cargo", "rustdoc", "rustfmt", "cargo-clippy"}
        self.assertEqual(recreate_bootstrap.STAGE0_OVERRIDE_KEYS, historical_keys)
        with tempfile.TemporaryDirectory() as directory, patch.object(
            recreate_bootstrap, "capture_validated_seed_lineage"
        ) as seed:
            root = Path(directory)
            for key in sorted(historical_keys):
                content = f'# (seed stage0 mode)\n[build]\n{key} = "/external/tool"\n'.encode()
                (root / "bootstrap.toml").write_bytes(content)
                with self.subTest(key=key):
                    snapshot = recreate_bootstrap.capture_bootstrap_lineage(root, "test-host")
                    self.assertEqual(snapshot["status"], "rejected")
                    self.assertEqual(snapshot["mode"], "unknown")
                    self.assertEqual(snapshot["declared_stage0_overrides"], [key])
            seed.assert_not_called()

    def test_genesis_config_uses_the_cargo_compatibility_identity(self):
        import tomllib

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = recreate_bootstrap.write_config(
                root,
                "test-host",
                force=True,
                seed_mode=False,
            ).path
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


class AyBcpFeatureSpellingTests(unittest.TestCase):
    """`install_ay_solver`'s rebuild must ask for the feature ay DECLARES.

    These vectors are the same five that pin
    `ay_bootstrap_cargo_args_for_manifest` in
    src/bootstrap/src/core/build_steps/tool/tests.rs. The two implementations
    build the same crate from the same pin, so they must not be able to select
    different capabilities.
    """

    @staticmethod
    def _ay_dir(directory: str, manifest: str) -> Path:
        crate = Path(directory) / "crates" / "ay"
        crate.mkdir(parents=True)
        (crate / "Cargo.toml").write_text(manifest, encoding="utf-8")
        return Path(directory)

    def _assert_spelling(self, manifest: str, expected: str) -> None:
        with tempfile.TemporaryDirectory() as directory:
            self.assertEqual(
                recreate_bootstrap.ay_bcp_cargo_features(self._ay_dir(directory, manifest)),
                expected,
            )

    def test_new_spelling_manifest_selects_unsafe_bcp(self):
        self._assert_spelling("[features]\nunsafe-bcp = []\ncli = []\n", "cli,unsafe-bcp")

    def test_old_spelling_manifest_selects_raw_pointer_bcp(self):
        self._assert_spelling(
            "[features]\nraw-pointer-bcp = []\ncli = []\n", "cli,raw-pointer-bcp"
        )

    def test_unreadable_manifest_fails_safe_to_the_current_spelling(self):
        with tempfile.TemporaryDirectory() as directory:
            # No crates/ay/Cargo.toml at all.
            self.assertEqual(
                recreate_bootstrap.ay_bcp_cargo_features(Path(directory)), "cli,unsafe-bcp"
            )

    def test_mid_rename_manifest_declaring_both_prefers_the_new_spelling(self):
        self._assert_spelling(
            "[features]\nraw-pointer-bcp = []\nunsafe-bcp = []\n", "cli,unsafe-bcp"
        )

    def test_key_outside_the_features_table_cannot_spoof_the_capability(self):
        self._assert_spelling(
            'unsafe-bcp = "0.1"\n[features]\nraw-pointer-bcp = []\ncli = []\n',
            "cli,raw-pointer-bcp",
        )

    def test_comment_only_declaration_does_not_count(self):
        self._assert_spelling(
            "[features]\n# unsafe-bcp = []\nraw-pointer-bcp = []\ncli = []\n",
            "cli,raw-pointer-bcp",
        )


class AdmittedXpyCpuShareTests(unittest.TestCase):
    def _launch(self, environment, jobs=None):
        with tempfile.TemporaryDirectory() as directory, patch.dict(
            os.environ, environment, clear=True
        ), patch.object(recreate_bootstrap, "add_homebrew_library_path"), patch.object(
            recreate_bootstrap, "seed_verification_off_switch", return_value=None
        ), patch.object(recreate_bootstrap.subprocess, "run") as run, patch.object(
            sys, "stdout", io.StringIO()
        ):
            run.return_value = SimpleNamespace(returncode=0)
            recreate_bootstrap.run_xpy_build(
                Path(directory).resolve(), "test-host", 1, jobs,
                ["compiler/rustc", "library/std"], seed_mode=True,
            )
            return run.call_args

    def test_admitted_share_reaches_actual_bootstrap_cap_with_overrides_scrubbed(self):
        spec = importlib.util.spec_from_file_location(
            "cpu_share_actual_bootstrap", SCRIPT.parents[1] / "src/bootstrap/bootstrap.py"
        )
        bootstrap = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(bootstrap)
        for jobs, expected in [(None, "6"), (100, "6"), (2, "2")]:
            with self.subTest(jobs=jobs):
                call = self._launch({
                    "BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "6",
                    "RUSTC": "/unbound/compiler", "RUSTFLAGS": "--cfg=unbound",
                    "CARGO_BUILD_RUSTC": "/other/compiler", "CARGO_TARGET_DIR": "/other/target",
                    "CARGO_BUILD_DEP_INFO_BASEDIR": "/other/base", "UNRELATED": "retained",
                }, jobs)
                env = call.kwargs["env"]
                self.assertEqual(env["BUILD_SLOT_HELD"], "1")
                self.assertEqual(env["CARGO_BUILD_JOBS"], "6")
                self.assertEqual(bootstrap.bootstrap_jobs("32", jobs, env), expected)
                for key in ("RUSTC", "RUSTFLAGS", "CARGO_BUILD_RUSTC", "CARGO_TARGET_DIR",
                            "CARGO_BUILD_DEP_INFO_BASEDIR"):
                    self.assertNotIn(key, env)
                self.assertEqual(env["UNRELATED"], "retained")

    def test_zero_padded_share_is_canonical_before_actual_bootstrap(self):
        spec = importlib.util.spec_from_file_location(
            "canonical_cpu_share_bootstrap", SCRIPT.parents[1] / "src/bootstrap/bootstrap.py"
        )
        bootstrap = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(bootstrap)
        call = self._launch({"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "0" * 5000 + "6"}, 100)
        env = call.kwargs["env"]
        self.assertEqual(env["CARGO_BUILD_JOBS"], "6")
        self.assertEqual(bootstrap.bootstrap_jobs("32", 100, env), "6")

    def test_missing_or_invalid_admitted_share_refuses_before_xpy(self):
        for share in (None, "", "0", "-1", "1.0", "4294967296", "١"):
            with self.subTest(share=share), tempfile.TemporaryDirectory() as directory:
                environment = {"BUILD_SLOT_HELD": "1"}
                if share is not None:
                    environment["CARGO_BUILD_JOBS"] = share
                with patch.dict(os.environ, environment, clear=True), patch.object(
                    recreate_bootstrap.subprocess, "run"
                ) as run:
                    with self.assertRaisesRegex(RuntimeError, "positive u32 CARGO_BUILD_JOBS"):
                        recreate_bootstrap.run_xpy_build(
                            Path(directory).resolve(), "test-host", 1, 1, [], seed_mode=False
                        )
                    run.assert_not_called()

    def test_unadmitted_jobs_stay_scrubbed_and_valid_cpu_ceiling_is_not_tool_authority(self):
        for marker in (None, "0", "yes"):
            with self.subTest(marker=marker):
                environment = {"CARGO_BUILD_JOBS": "invalid"}
                if marker is not None:
                    environment["BUILD_SLOT_HELD"] = marker
                env = self._launch(environment).kwargs["env"]
                self.assertNotIn("CARGO_BUILD_JOBS", env)
                self.assertIn("CARGO_BUILD_JOBS",
                              recreate_bootstrap._ambient_build_authority_overrides(environment))
        # The positive held CPU ceiling cannot choose a compiler or any flags.
        # Capture and producer must both accept it for the same normal build.
        overrides = recreate_bootstrap._ambient_build_authority_overrides({
            "BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "6"
        })
        self.assertNotIn("CARGO_BUILD_JOBS", overrides)


class AtpkgStage0Tests(unittest.TestCase):
    """The atpkg-delivered trust pack is the PREFERRED stage0 and is resolved
    BEFORE the checked-in seed, so a machine that has it never fetches or
    validates seed payloads and never needs a host rustc/cargo."""

    host = "test-host"

    @staticmethod
    def selection_for_pack(root, pack):
        snapshot = AtpkgStage0AuthorityTests.authority_snapshot()
        snapshot["authority"]["pack"]["pack_local_path"] = str(pack)
        snapshot["authority_sha256"] = hashlib.sha256(json.dumps(
            snapshot["authority"], sort_keys=True, separators=(",", ":")
        ).encode()).hexdigest()
        return recreate_bootstrap.Stage0Selection("atpkg", None, None, snapshot)

    def _main(self, argv, *, atpkg, extra_patches=()):
        stack = ExitStack()
        with stack:
            stack.enter_context(patch.object(recreate_bootstrap, "ensure_python_311"))
            stack.enter_context(patch.object(recreate_bootstrap, "line_buffer_output"))
            stack.enter_context(
                patch.object(recreate_bootstrap, "repo_root", return_value=Path("/checkout"))
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "host_triple", return_value=self.host)
            )
            stack.enter_context(
                patch.object(recreate_bootstrap, "atpkg_trust_sysroot", return_value=atpkg)
            )
            resolve_seed = stack.enter_context(
                patch.object(recreate_bootstrap, "resolve_seed", return_value=False)
            )
            stack.enter_context(patch.object(
                recreate_bootstrap, "_capture_atpkg_stage0_authority",
                return_value=self.selection_for_pack(Path("/checkout"), atpkg).atpkg_authority,
            ))
            check_prereqs = stack.enter_context(
                patch.object(recreate_bootstrap, "check_prereqs", return_value=[])
            )
            stack.enter_context(patch.object(recreate_bootstrap, "print_prereqs"))
            for target, kwargs in extra_patches:
                stack.enter_context(patch.object(recreate_bootstrap, target, **kwargs))
            out = io.StringIO()
            stack.enter_context(patch.object(sys, "stdout", out))
            rc = recreate_bootstrap.main(argv)
        return rc, out.getvalue(), resolve_seed, check_prereqs

    def test_atpkg_pack_is_resolved_before_the_seed_and_without_a_host_rust(self):
        rc, out, resolve_seed, check_prereqs = self._main(
            ["--check"], atpkg=Path("/pkg/store/trust/6808")
        )
        self.assertEqual(rc, 0)
        self.assertIn("stage0 mode: atpkg", out)
        resolve_seed.assert_not_called()
        # seed_mode=True is what keeps stock rustc/cargo OFF the prerequisite list.
        self.assertTrue(check_prereqs.call_args.kwargs["seed_mode"])

    def test_require_seed_is_satisfied_by_the_atpkg_pack(self):
        rc, out, resolve_seed, _ = self._main(
            ["--check", "--require-seed"], atpkg=Path("/pkg/store/trust/6808")
        )
        self.assertEqual(rc, 0)
        self.assertIn("stage0 mode: atpkg", out)
        resolve_seed.assert_not_called()

    def test_no_atpkg_falls_back_to_the_checked_in_seed(self):
        rc, out, resolve_seed, _ = self._main(
            ["--check", "--no-atpkg", "--require-seed"], atpkg=Path("/pkg/store/trust/6808")
        )
        self.assertEqual(rc, 1)
        resolve_seed.assert_called_once()
        self.assertIn("refusing genesis fallback", out)

    def test_genesis_flag_overrides_the_atpkg_pack(self):
        rc, out, resolve_seed, check_prereqs = self._main(
            ["--check", "--genesis"], atpkg=Path("/pkg/store/trust/6808")
        )
        self.assertEqual(rc, 0)
        self.assertIn("stage0 mode: genesis", out)
        resolve_seed.assert_not_called()
        self.assertFalse(check_prereqs.call_args.kwargs["seed_mode"])

    def test_build_probes_the_atpkg_driver_for_its_off_switch(self):
        """run_xpy_build must ask the CONFIGURED stage0 which off-switch it
        speaks. The probe used to look only at build/<host>/stage0, which an
        atpkg stage0 never populates, so the build ran with no off-switch."""
        seen = {}
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name).resolve()

        def fake_probe(_root, _host, _env, *, compiler=None):
            seen["trustc"] = compiler
            return "flag"

        with patch.dict(os.environ, {}, clear=True), patch.object(
            recreate_bootstrap, "add_homebrew_library_path"
        ), patch.object(
            recreate_bootstrap, "seed_verification_off_switch", side_effect=fake_probe
        ), patch.object(recreate_bootstrap.subprocess, "run") as run:
            run.return_value = SimpleNamespace(returncode=0)
            rc = recreate_bootstrap.run_xpy_build(
                root,
                self.host,
                2,
                None,
                [],
                seed_mode=True,
                seed_compiler=Path("/pkg/store/trust/6808/bin/trustc"),
            )
        self.assertEqual(rc, 0)
        self.assertEqual(seen["trustc"], Path("/pkg/store/trust/6808/bin/trustc"))
        env = run.call_args.kwargs["env"]
        self.assertEqual(env["RUSTFLAGS_BOOTSTRAP"], "-Ztrust-verify=off")
        self.assertEqual(env["CARGO_HOME"], str(root / "build/bootstrap-cargo-home"))

    def test_off_switch_probe_uses_the_given_driver_path(self):
        with tempfile.TemporaryDirectory() as directory:
            trustc = Path(directory) / "store" / "bin" / "trustc"
            trustc.parent.mkdir(parents=True)
            trustc.write_text("#!/bin/sh\necho '    -Z trust-verify=val'\n")
            trustc.chmod(0o755)
            self.assertEqual(
                recreate_bootstrap.seed_verification_off_switch(
                    Path(directory), self.host, dict(os.environ), compiler=trustc
                ),
                "flag",
            )
            # The default location is the hydrated seed, which is absent here.
            self.assertIsNone(
                recreate_bootstrap.seed_verification_off_switch(
                    Path(directory), self.host, dict(os.environ)
                )
            )

    def test_the_recreator_keeps_its_own_bounds(self):
        # The patience above is the fixtures', never the recreator's: what the
        # recreator hands subprocess.run is still its own 10 s and 30 s.
        self.assertIs(subprocess.run, _patient_run)
        with tempfile.TemporaryDirectory() as directory:
            trustc = Path(directory) / "trustc"
            trustc.write_text("#!/bin/sh\n")
            completed = SimpleNamespace(returncode=0, stdout="", stderr="")
            with patch.object(recreate_bootstrap.subprocess, "run", return_value=completed) as run:
                recreate_bootstrap.tool_version("/fixture/tool")
                self.assertEqual(run.call_args.kwargs["timeout"], 10)
                recreate_bootstrap._capture_identity(Path("/fixture/tool"), ("--version",))
                self.assertEqual(run.call_args.kwargs["timeout"], 30)
                run.return_value = SimpleNamespace(returncode=0, stdout=b"")
                recreate_bootstrap.seed_verification_off_switch(
                    Path(directory), self.host, {}, compiler=trustc
                )
                self.assertEqual(run.call_args.kwargs["timeout"], 30)
        self.assertIs(subprocess.run, _patient_run)

    def test_write_config_renders_the_atpkg_block_it_is_given(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(sys, "stdout", io.StringIO()):
                path = recreate_bootstrap.write_config(
                    root,
                    "aarch64-apple-darwin",
                    False,
                    seed_mode=True,
                    selection=self.selection_for_pack(root, Path("/pkg/store/trust/6808")),
                )
            text = path.path.read_text()
            self.assertIn("(atpkg stage0 mode)", text)
            self.assertIn('rustc = "/pkg/store/trust/6808/bin/trustc"', text)
            self.assertIn('cargo = "/pkg/store/trust/6808/bin/cargo"', text)
            # The generated config inherits the compiler profile's allowlist.
            self.assertNotRegex(text, r"(?m)^tools\s*=")
            self.assertIn("extended = true", text)
            # Both Apple architectures on an Apple host.
            self.assertIn(
                'target = ["aarch64-apple-darwin", "x86_64-apple-darwin"]', text
            )

    def test_write_config_seed_block_when_no_atpkg_pack_is_given(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(sys, "stdout", io.StringIO()):
                path = recreate_bootstrap.write_config(
                    root, "x86_64-unknown-linux-gnu", False, seed_mode=True
                )
            text = path.path.read_text()
            self.assertIn("(seed stage0 mode)", text)
            self.assertNotIn("(atpkg stage0 mode)", text)
            self.assertNotRegex(text, r'(?m)^rustc\s*=')
            self.assertNotRegex(text, r"(?m)^target\s*=")

    def test_a_linux_config_links_rust_with_the_building_compilers_own_lld(self):
        # GNU ld could not link main's stage-2 librustc_driver on aarch64 Linux
        # (LINUX-SEED-LLD-1): every Linux seed-mode config names the compiler's own lld.
        line = 'bootstrap-override-lld = "self-contained"'

        def written(system, host, **kwargs):
            with tempfile.TemporaryDirectory() as directory, \
                    patch.object(recreate_bootstrap.platform, "system", return_value=system), \
                    patch.object(sys, "stdout", io.StringIO()):
                text = recreate_bootstrap.write_config(Path(directory), host, False, **kwargs).path.read_text()
            return text

        linux = written("Linux", "aarch64-unknown-linux-gnu", seed_mode=True)
        self.assertIn("\ndeny-warnings = false\n# Trust: every Rust link goes through the building compiler's own "
                      f"rust-lld, never GNU ld,\n# which cannot link the stage-2 librustc_driver on aarch64 Linux "
                      f"(LINUX-SEED-LLD-1).\n{line}\n\n[install]\n", linux)
        import tomllib

        rust = tomllib.loads(linux)["rust"]
        self.assertEqual(rust["bootstrap-override-lld"], "self-contained")
        # Not in genesis mode, not on Darwin, and Darwin's bytes are what they were.
        self.assertNotIn(line, written("Linux", "aarch64-unknown-linux-gnu", seed_mode=False))
        darwin = written("Darwin", "aarch64-apple-darwin", seed_mode=True)
        self.assertNotIn(line, darwin)
        self.assertIn("\ndeny-warnings = false\n\n[install]\n", darwin)

    def test_an_atpkg_stage0_links_with_its_own_lld_only_when_it_ships_one(self):
        host = "aarch64-unknown-linux-gnu"
        with tempfile.TemporaryDirectory() as directory:
            pack = Path(directory) / "pack"
            tools = pack / "lib" / "rustlib" / host / "bin"
            with patch.object(recreate_bootstrap.platform, "system", return_value="Linux"):
                self.assertTrue(recreate_bootstrap.links_with_own_lld("seed", None, host))
                self.assertFalse(recreate_bootstrap.links_with_own_lld("genesis", None, host))
                self.assertFalse(recreate_bootstrap.links_with_own_lld("atpkg", pack, host))
                (tools / "gcc-ld").mkdir(parents=True)
                (tools / "rust-lld").write_text("")
                self.assertFalse(recreate_bootstrap.links_with_own_lld("atpkg", pack, host))
                (tools / "gcc-ld" / "ld.lld").write_text("")
                self.assertTrue(recreate_bootstrap.links_with_own_lld("atpkg", pack, host))
                self.assertFalse(recreate_bootstrap.links_with_own_lld("seed", None, "aarch64-apple-darwin"))
            with patch.object(recreate_bootstrap.platform, "system", return_value="Darwin"):
                self.assertFalse(recreate_bootstrap.links_with_own_lld("seed", None, host))

    def test_write_config_refuses_an_atpkg_pack_outside_seed_mode(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(RuntimeError, "lacks exact local candidate authority"):
                recreate_bootstrap.write_config(
                    Path(directory),
                    self.host,
                    False,
                    seed_mode=False,
                    selection=recreate_bootstrap.Stage0Selection("atpkg", None, None),
                )


class LLVMZstdInputConfigTests(unittest.TestCase):
    HOST = "test-host"

    def write(self, root, force=False, **kwargs):
        with patch.object(recreate_bootstrap.platform, "system", return_value="Unknown"), \
                patch.object(recreate_bootstrap, "find_python_ge_311", return_value=sys.executable), \
                patch.object(sys, "stdout", io.StringIO()):
            return recreate_bootstrap.write_config(root, self.HOST, force, seed_mode=True, **kwargs)

    def test_explicit_metadata_directory_round_trips_spaces_and_quotes(self):
        import tomllib
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            metadata = root / 'native "zstd" metadata'
            metadata.mkdir()
            (metadata / "libzstd.pc").write_text("Name: zstd\n")
            written = self.write(root, llvm_zstd_pkg_config_dir=str(metadata))
            config = tomllib.loads(written.path.read_text())
            self.assertEqual(config["target"][self.HOST]["llvm-zstd-pkg-config-dir"], str(metadata))
            self.assertNotIn("PKG_CONFIG_PATH", written.path.read_text())

    def test_missing_or_relative_metadata_refuses_before_config_write(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            empty = root / "empty"
            empty.mkdir()
            for invalid in ("relative", str(root / "absent"), str(empty)):
                with self.subTest(path=invalid), self.assertRaisesRegex(RuntimeError, "containing libzstd.pc"):
                    self.write(root, llvm_zstd_pkg_config_dir=invalid)
                self.assertFalse((root / "bootstrap.toml").exists())

    def test_existing_config_cannot_silently_ignore_a_new_dependency(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = self.write(root)
            before = original.path.read_bytes()
            metadata = root / "metadata"
            metadata.mkdir()
            (metadata / "libzstd.pc").write_text("Name: zstd\n")
            with self.assertRaisesRegex(RuntimeError, "different LLVM zstd input"):
                self.write(root, llvm_zstd_pkg_config_dir=str(metadata))
            self.assertEqual(original.path.read_bytes(), before)
            selected = self.write(root, force=True, llvm_zstd_pkg_config_dir=str(metadata))
            reused = self.write(root, llvm_zstd_pkg_config_dir=str(metadata))
            self.assertEqual(selected.sha256, reused.sha256)

    def test_cli_preserves_explicit_native_dependency_input(self):
        path = '/native zstd/metadata'
        args = recreate_bootstrap.parse_args(["--llvm-zstd-pkg-config-dir", path])
        self.assertEqual(args.llvm_zstd_pkg_config_dir, path)
        with patch.object(sys, "stderr", io.StringIO()), self.assertRaises(SystemExit):
            recreate_bootstrap.parse_args(["--llvm-zstd-pkg-config-dir", ""])


class DarwinNativeCompilerConfigTests(unittest.TestCase):
    def external_llvm(self, root, *, clang_version="23.1.5", with_clang=True, clang_exit=0,
                      lld_version="23.1.5", with_lld=True, lld_exit=0):
        # Metadata-only executable fixtures for config selection, not LLVM or
        # compiler qualification. The actual static LLVM link has its own run.
        tools = root / "external llvm" / "bin"
        tools.mkdir(parents=True)
        config = tools / "llvm-config"
        config.write_text("#!/bin/sh\nif [ \"$1\" = --bindir ]; then\n"
                          f"  printf '%s\\n' '{tools}'\nelse\n  printf '23.1.5\\n'\nfi\n")
        config.chmod(0o755)
        if with_clang:
            clang = tools / "clang"
            clang.write_text(f"#!/bin/sh\nprintf 'clang version {clang_version}\\n'\nexit {clang_exit}\n")
            clang.chmod(0o755)
        if with_lld:
            linker = tools / "ld64.lld"
            linker.write_text(f"#!/bin/sh\nprintf 'LLD {lld_version}\\n'\nexit {lld_exit}\n")
            linker.chmod(0o755)
        return config, tools / "clang"

    def generated(self, root, host, llvm_config=None):
        with patch.object(recreate_bootstrap.platform, "system", return_value="Darwin"), \
                patch.object(recreate_bootstrap, "find_python_ge_311", return_value=sys.executable), \
                patch.object(sys, "stdout", io.StringIO()):
            return recreate_bootstrap.write_config(
                root, host, False, llvm_config=llvm_config, seed_mode=True)

    def test_generated_apple_config_selects_native_compilers_before_cold_bootstrap(self):
        # Read with the actual Python bootstrap parser: these values must
        # reach build_bootstrap_cmd's CC_<build>, CXX_<build>, etc. export.
        path = SCRIPT.parents[1] / "src/bootstrap/bootstrap.py"
        spec = importlib.util.spec_from_file_location("darwin_writer_bootstrap", path)
        bootstrap = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(bootstrap)
        expected = {"cc": "/usr/bin/clang", "cxx": "/usr/bin/clang++",
                    "linker": "/usr/bin/clang", "ar": "/usr/bin/ar", "ranlib": "/usr/bin/ranlib"}
        for host in recreate_bootstrap.APPLE_TARGETS:
            with self.subTest(host=host), tempfile.TemporaryDirectory() as directory:
                written = self.generated(Path(directory), host)
                text = written.path.read_text()
                for target in recreate_bootstrap.APPLE_TARGETS:
                    for key, value in expected.items():
                        self.assertEqual(
                            bootstrap.RustBuild.get_toml_static(text, key, "target." + target), value,
                            (host, target, key))
                self.assertNotIn("SDKROOT", text)
                self.assertNotIn("CFLAGS", text)

    def test_native_compiler_selection_keeps_the_explicit_external_llvm(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            llvm, clang = self.external_llvm(root)
            written = self.generated(root, "aarch64-apple-darwin", str(llvm))
            import tomllib
            config = tomllib.loads(written.path.read_text())
            target = config["target"]["aarch64-apple-darwin"]
            self.assertEqual(target.get("cc"), "/usr/bin/clang")
            self.assertEqual(target.get("cxx"), "/usr/bin/clang++")
            self.assertEqual(target["llvm-config"], str(llvm))
            self.assertEqual(target["linker"], str(clang))
            self.assertEqual(config["llvm"]["use-linker"], str(clang.with_name("ld64.lld")))
            cross = config["target"]["x86_64-apple-darwin"]
            self.assertEqual(cross["cc"], "/usr/bin/clang")
            self.assertEqual(cross["linker"], str(clang))
            self.assertNotIn("llvm-config", cross)
            self.assertEqual(config["rust"]["codegen-backends"], ["llvm", "trust-cg"])
            self.assertEqual(config["build"]["target"], list(recreate_bootstrap.APPLE_TARGETS))
            self.assertNotIn("rustflags", target)
            self.assertNotIn("rustflags", cross)

    def test_external_llvm_without_its_driver_refuses_before_writing_config(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            llvm, _ = self.external_llvm(root, with_clang=False)
            with self.assertRaisesRegex(RuntimeError, "matching executable Clang driver"):
                self.generated(root, "aarch64-apple-darwin", str(llvm))
            self.assertFalse((root / "bootstrap.toml").exists())

    def test_external_llvm_without_its_native_linker_refuses_before_writing_config(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            llvm, _ = self.external_llvm(root, with_lld=False)
            with self.assertRaisesRegex(RuntimeError, "matching executable Mach-O linker"):
                self.generated(root, "aarch64-apple-darwin", str(llvm))
            self.assertFalse((root / "bootstrap.toml").exists())

    def test_external_llvm_native_linker_version_mismatch_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            llvm, _ = self.external_llvm(root, lld_version="21.1.0")
            with self.assertRaisesRegex(RuntimeError, "no system-linker fallback"):
                self.generated(root, "aarch64-apple-darwin", str(llvm))
            self.assertFalse((root / "bootstrap.toml").exists())

    def test_failed_native_linker_probe_cannot_authorize_matching_version_text(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            llvm, _ = self.external_llvm(root, lld_exit=1)
            with self.assertRaisesRegex(RuntimeError, "matching executable Mach-O linker"):
                self.generated(root, "aarch64-apple-darwin", str(llvm))
            self.assertFalse((root / "bootstrap.toml").exists())

    def test_external_llvm_driver_version_mismatch_does_not_fall_back_to_apple(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            llvm, _ = self.external_llvm(root, clang_version="22.1.0")
            with self.assertRaisesRegex(RuntimeError, "no system-linker fallback"):
                self.generated(root, "aarch64-apple-darwin", str(llvm))
            self.assertFalse((root / "bootstrap.toml").exists())

    def test_failed_driver_probe_cannot_authorize_the_matching_version_text(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            llvm, _ = self.external_llvm(root, clang_exit=1)
            with self.assertRaisesRegex(RuntimeError, "matching executable Clang driver"):
                self.generated(root, "aarch64-apple-darwin", str(llvm))
            self.assertFalse((root / "bootstrap.toml").exists())

    def test_external_llvm_launcher_uses_reported_bindir_not_its_own_parent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            llvm, clang = self.external_llvm(root)
            launcher = root / "llvm-config-launcher"
            launcher.write_text(llvm.read_text())
            launcher.chmod(0o755)
            written = self.generated(root, "aarch64-apple-darwin", str(launcher))
            import tomllib
            target = tomllib.loads(written.path.read_text())["target"]["aarch64-apple-darwin"]
            self.assertEqual(target["linker"], str(clang))

    def test_external_llvm_relative_or_multiple_bindirs_refuse_before_writing(self):
        for output in ("relative/bin", "/first\\n/second"):
            with self.subTest(output=output), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                llvm, _ = self.external_llvm(root)
                llvm.write_text("#!/bin/sh\nif [ \"$1\" = --bindir ]; then\n"
                                f"  printf '{output}\\n'\nelse\n  printf '23.1.5\\n'\nfi\n")
                with self.assertRaisesRegex(RuntimeError, "one absolute bindir"):
                    self.generated(root, "aarch64-apple-darwin", str(llvm))
                self.assertFalse((root / "bootstrap.toml").exists())

    def test_non_apple_target_does_not_gain_apple_tool_settings(self):
        with tempfile.TemporaryDirectory() as directory:
            written = self.generated(Path(directory), "aarch64-unknown-linux-gnu")
            import tomllib
            config = tomllib.loads(written.path.read_text())
            self.assertNotIn("target", config)
            self.assertNotIn("target", config["build"])

    def test_reusing_an_existing_config_preserves_its_explicit_compiler(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = root / "bootstrap.toml"
            content = ('# (seed stage0 mode)\n[build]\n'
                       '[target.aarch64-apple-darwin]\ncc = "/selected/clang"\n')
            config.write_text(content)
            with patch.object(recreate_bootstrap, "_native_tool_record",
                              side_effect=AssertionError("existing config must not rediscover LLVM")):
                written = self.generated(root, "aarch64-apple-darwin", "/unavailable/llvm-config")
            self.assertEqual(config.read_text(), content)
            self.assertEqual(written.sha256, hashlib.sha256(content.encode()).hexdigest())


class GeneratedCompilerProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = SCRIPT.parent.parent
        spec = importlib.util.spec_from_file_location(
            "recreate_bootstrap_preflight", cls.root / "tools/preflight.py"
        )
        assert spec is not None and spec.loader is not None
        cls.preflight = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = cls.preflight
        spec.loader.exec_module(cls.preflight)
        cls.facts = cls.preflight.read_bootstrap_facts(cls.root)

    def effective_config(self, overrides=(), *, host="aarch64-unknown-linux-gnu"):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        with patch.object(sys, "stdout", io.StringIO()):
            written = recreate_bootstrap.write_config(
                root, host, False, seed_mode=True
            )
        self.preflight._TOML_CACHE.clear()
        config, _, error = self.preflight.resolve_bootstrap_config(
            self.root, str(written.path), list(overrides), root, {}
        )
        self.assertIsNone(error)
        return config

    def test_generated_config_inherits_complete_public_tool_selection(self):
        config = self.effective_config()
        self.assertEqual(config["profile"], "compiler")
        self.assertIn("trustup", config["build"]["tools"])
        # `rust-src` is install.rs's source-component selector; upstream 162423
        # retired `src`, which selects nothing.
        self.assertTrue(
            {"trustc-dev", "rust-src", "trust-llvm-tools"} <= set(config["build"]["tools"])
        )
        self.assertNotIn("src", config["build"]["tools"])
        self.assertIn("rust-src", self.facts.install_selectors)
        model = self.preflight.build_tool_model(self.root, config, self.facts)
        self.assertTrue(model.usable)
        # Cargo is a compatibility alias installed with Targo, rather than a
        # distinct tools-list selection. Check all the public tool producers.
        for tool in recreate_bootstrap.STAGE_TOOL_PRODUCERS.keys() - {"cargo"}:
            with self.subTest(tool=tool):
                # Trustdoc's install names come from a shared array which the
                # preflight model does not expand; query its explicit tool gate.
                selected = model.tool_enabled(tool) if tool == "trustdoc" else model.selected(tool)
                self.assertIs(selected, True)

    def test_explicit_allowlist_replaces_inherited_selection(self):
        config = self.effective_config(('build.tools=["targo"]',))
        self.assertEqual(config["build"]["tools"], ["targo"])
        model = self.preflight.build_tool_model(self.root, config, self.facts)
        self.assertIs(model.selected("targo"), True)
        for tool in ("trustup", "clean", "ty"):
            with self.subTest(tool=tool):
                self.assertIs(model.selected(tool), False)

    def test_generated_config_inherits_llvm_targets_independently_of_std_targets(self):
        # A compiler that ships Apple std still needs the other LLVM backends
        # for ordinary cross-target queries in the complete compiletest suite.
        for host in ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu"):
            with self.subTest(host=host):
                config = self.effective_config(host=host)
                self.assertNotIn("targets", config["llvm"])
                self.assertNotIn("experimental-targets", config["llvm"])
                if host.endswith("-apple-darwin"):
                    self.assertEqual(
                        config["build"]["target"], list(recreate_bootstrap.APPLE_TARGETS)
                    )
                else:
                    self.assertNotIn("target", config["build"])

    def test_explicit_llvm_target_selection_remains_available(self):
        config = self.effective_config(
            ('llvm.targets="AArch64"', 'llvm.experimental-targets=""'),
            host="aarch64-apple-darwin",
        )
        self.assertEqual(config["llvm"]["targets"], "AArch64")
        self.assertEqual(config["llvm"]["experimental-targets"], "")
        self.assertEqual(config["build"]["target"], list(recreate_bootstrap.APPLE_TARGETS))


class ExpectedPublicToolsTests(unittest.TestCase):
    def test_writer_and_verifier_share_one_closed_set_including_rustdoc(self):
        expected = recreate_bootstrap.expected_public_stage_tools()
        self.assertIn("rustdoc", expected)
        self.assertIn("rustc", expected)
        self.assertIn("trustc", expected)
        self.assertTrue(set(recreate_bootstrap.STAGE_TOOL_PRODUCERS) <= expected)

    def test_optional_tools_are_neither_required_nor_stock_spellings(self):
        optional = set(recreate_bootstrap.OPTIONAL_STAGE_TOOL_PRODUCERS)
        self.assertEqual(optional, {"trust-miri", "targo-miri"})
        self.assertFalse(optional & recreate_bootstrap.expected_public_stage_tools())
        self.assertEqual(
            recreate_bootstrap.stage_tool_producers_for(set()),
            recreate_bootstrap.STAGE_TOOL_PRODUCERS,
        )


class StageToolProducersMatchBootstrapTests(unittest.TestCase):
    """The provenance audit binds each public stage tool to the tools-bin
    artifact bootstrap actually restores it from, read from `tool.rs` itself.

    Until 2026-09-29 the Trust Cargo's package, library and binary were all
    named `cargo`, so its tools-bin artifact was a file called `cargo` and this
    map bound both `targo` and `cargo` to it. The artifact is `targo` now. A map
    left pointing at `cargo` reports every fresh stage as missing its Targo
    producer, and in an old build directory it binds the stage's `targo` to a
    stale pre-rename file instead of the one bootstrap installed.
    """

    @classmethod
    def setUpClass(cls):
        root = SCRIPT.parent.parent
        spec = importlib.util.spec_from_file_location(
            "recreate_bootstrap_producer_preflight", root / "tools/preflight.py"
        )
        assert spec is not None and spec.loader is not None
        cls.preflight = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = cls.preflight
        spec.loader.exec_module(cls.preflight)
        cls.facts = cls.preflight.read_bootstrap_facts(root)

    def test_every_restored_public_tool_names_bootstraps_own_artifact(self):
        restored = {entry.install: entry.src for entry in self.facts.sysroot_bins}
        self.assertIn("targo", restored, "tool.rs restoration table did not parse")
        checked = 0
        for public, producer in recreate_bootstrap.STAGE_TOOL_PRODUCERS.items():
            if public in restored:
                checked += 1
                with self.subTest(public=public):
                    self.assertEqual(producer, restored[public])
        self.assertGreater(checked, 5)

    def test_producer_generation_follows_bootstraps_distribution_contract(self):
        body = self.preflight.fn_body(self.facts.src, "get_tool_target_compiler")
        self.assertIsNotNone(body)
        compact = re.sub(r"\s+", "", body)
        self.assertIn("(target_compiler.host,target_compiler.stage-1)", compact)
        output = self.preflight.fn_body(self.facts.src, "output_compiler_for_tool")
        self.assertIsNotNone(output)
        self.assertIn("Compiler::new(build_compiler.stage+1,target)", re.sub(r"\s+", "", output))
        private = self.preflight.fn_body(self.facts.src, "build_compiler_from_stage")
        self.assertIsNotNone(private)
        self.assertIn("builder.compiler(stage-1,builder.config.host_target)", re.sub(r"\s+", "", private))

        # Include the final directory owner: ToolBuild passes OUTPUT stage N
        # and Session adds one and the target. Checking N-1/N alone missed
        # this composition; accepting flat output would select an older cut.
        copy = self.preflight.fn_body(self.facts.src, "copy_link_tool_bin")
        self.assertIsNotNone(copy)
        self.assertIn(
            "builder.tools_dir(output_compiler,target).join(exe(name,target))",
            re.sub(r"\s+", "", copy),
        )
        session = (SCRIPT.parent.parent / "src/bootstrap/src/core/session.rs").read_text()
        directory = self.preflight.fn_body(session, "tools_dir")
        self.assertIsNotNone(directory)
        self.assertEqual(
            re.sub(r"\s+", "", directory),
            'letout=tools_bin_dir(&self.out,build_compiler,target);'
            't!(fs::create_dir_all(&out));out',
        )
        target_directory = self.preflight.fn_body(session, "tools_bin_dir")
        self.assertIsNotNone(target_directory)
        self.assertEqual(
            re.sub(r"\s+", "", target_directory),
            'out.join(build_compiler.host).join('
            'format!("stage{}-tools-bin",build_compiler.stage+1)).join(target.triple)',
        )

    def test_the_cargo_alias_is_bound_to_the_artifact_bootstrap_aliases(self):
        body = self.preflight.fn_body(self.facts.src, "upstream_compat_bin_for_tool_source")
        self.assertIsNotNone(body)
        arms = re.findall(r'"([^"]+)"\s*=>\s*Some\("([^"]+)"\)', body)
        aliased_sources = {source for source, alias in arms if alias == "cargo"}
        self.assertEqual(
            aliased_sources, {recreate_bootstrap.STAGE_TOOL_PRODUCERS["cargo"]}
        )

    def test_the_trust_cargo_and_its_cargo_alias_are_the_targo_artifact(self):
        producers = recreate_bootstrap.STAGE_TOOL_PRODUCERS
        self.assertEqual(producers["targo"], "targo")
        self.assertEqual(producers["cargo"], "targo")
        self.assertNotIn("cargo", producers.values())


class Stage0ManifestCapabilityTests(unittest.TestCase):
    """A stage0 must PARSE this tree, not merely carry a compiler.

    `[trust]` is Trust's own manifest table and `targo-trust` reads it with
    unknown fields DENIED, so a pack published before a key the tree uses
    resolves fine, gets selected, and then dies inside dependency resolution
    about 90 seconds into the build. Selection has to ask.
    """

    SCHEMA_REFUSAL = (
        "error: unknown field `compiler_timeout_secs`, expected one of `enabled`, "
        "`level`, `timeout_ms`\n"
        "    --> first-party/ty/Cargo.toml:3151:1\n"
    )
    UNRELATED_FAILURE = (
        "error: failed to get `rustc-hash` as a dependency\n"
        "Caused by:\n  network failure: could not resolve host\n"
    )

    def _tree(self, root: Path) -> None:
        """A checkout whose only build-graph `[trust]` manifest is ty's."""
        (root / "Cargo.toml").write_text(
            '[workspace]\nmembers = ["crates/plain"]\nexclude = ["first-party/ty"]\n'
        )
        (root / "first-party" / "ty").mkdir(parents=True)
        (root / "first-party" / "ty" / "Cargo.toml").write_text(
            '[package]\nname = "ty"\n[workspace]\n\n[trust]\ncompiler_timeout_secs = 43200\n'
        )
        # Plain manifest, no `[trust]` table: never probed.
        (root / "crates" / "plain").mkdir(parents=True)
        (root / "crates" / "plain" / "Cargo.toml").write_text(
            '[package]\nname = "plain"\n[dependencies]\nty = { path = "../../first-party/ty" }\n'
        )
        # Unreferenced trees: the path spelling does not decide reachability.
        for pruned in ("examples/demo", "tests/fixture", "build/host", "vendor/foreign"):
            directory = root / pruned
            directory.mkdir(parents=True)
            (directory / "Cargo.toml").write_text(
                '[package]\nname = "pruned"\n\n[trust]\ncompiler_timeout_secs = 1\n'
            )

    def _pack(self, store, build, *, stderr):
        """An atpkg store entry whose `cargo` behaves as directed."""
        pack = store / build
        binaries = pack / "bin"
        binaries.mkdir(parents=True)
        for name in ("trustc", "trustdoc"):
            (binaries / name).write_text("#!/bin/sh\nexit 0\n")
            (binaries / name).chmod(0o755)
        cargo = binaries / "cargo"
        if stderr is None:
            cargo.write_text("#!/bin/sh\nexit 0\n")
        else:
            body = stderr.replace("'", "'\\''")
            cargo.write_text(f"#!/bin/sh\nprintf '%s' '{body}' >&2\nexit 101\n")
        cargo.chmod(0o755)
        return pack

    def test_probe_set_is_the_build_graph_trust_manifests_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self._tree(root)
            probes = recreate_bootstrap.stage0_trust_manifest_probes(root)
            self.assertEqual(
                [str(p.relative_to(root.resolve())) for p in probes],
                ["first-party/ty/Cargo.toml"],
            )

    def _manifest(self, root, relative, content):
        path = root / relative / "Cargo.toml"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path.resolve()

    def _trust_package(self, name="fixture"):
        return f'[package]\nname = "{name}"\n[workspace]\n[trust]\nunknown_future_key = true\n'

    def _probe_paths(self, root):
        return {str(path.relative_to(root.resolve()))
                for path in recreate_bootstrap.stage0_trust_manifest_probes(root)}

    def test_standalone_control_is_unreachable_until_declared_as_a_dependency(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self._tree(root)
            fixture = "reports/qualified/controls/unknown-key"
            self._manifest(root, fixture, self._trust_package())
            self.assertNotIn(fixture + "/Cargo.toml", self._probe_paths(root))
            manifest = root / "crates/plain/Cargo.toml"
            manifest.write_text(manifest.read_text() +
                                f'control = {{ path = "../../{fixture}" }}\n')
            self.assertIn(fixture + "/Cargo.toml", self._probe_paths(root))

    def test_quoted_and_inline_trust_tables_are_not_missed_by_text_spelling(self):
        for table in ('["trust"]\nunknown_future_key = true\n',
                      'trust = { unknown_future_key = true }\n'):
            with self.subTest(table=table), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                self._manifest(root, ".", table + '[package]\nname = "root"\n[workspace]\n')
                self.assertEqual(self._probe_paths(root), {"Cargo.toml"})

    def test_all_declared_dependency_kinds_and_inherited_paths_remain_visible(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self._tree(root)
            entries = {
                "normal": "reports/normal", "build": "tests/build",
                "dev": "examples/dev", "target": "reports/target",
                "optional": "examples/optional", "inherited": "tests/inherited",
            }
            for name, path in entries.items():
                self._manifest(root, path, self._trust_package(name))
            root_manifest = root / "Cargo.toml"
            root_manifest.write_text(root_manifest.read_text() +
                '\n[workspace.dependencies]\ninherited = { path = "tests/inherited" }\n')
            member = root / "crates/plain/Cargo.toml"
            member.write_text(member.read_text() +
                'normal = { path = "../../reports/normal" }\n'
                'optional = { path = "../../examples/optional", optional = true }\n'
                'inherited = { workspace = true }\n'
                '[build-dependencies]\nbuild = { path = "../../tests/build" }\n'
                '[dev-dependencies]\ndev = { path = "../../examples/dev" }\n'
                '[target.\'cfg(windows)\'.dependencies]\ntarget = { path = "../../reports/target" }\n')
            self.assertTrue({path + "/Cargo.toml" for path in entries.values()}
                            <= self._probe_paths(root))

    def test_workspace_globs_excludes_explicit_members_and_override_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self._manifest(root, ".", '[workspace]\nmembers = ["members/*", "tests/explicit"]\n'
                'exclude = ["members/excluded", "tests/explicit"]\n'
                '[patch.crates-io]\npatched = { path = "reports/patched" }\n'
                '[replace]\n"replaced:0.1.0" = { path = "examples/replaced" }\n')
            for path in ("members/included", "members/excluded", "tests/explicit",
                         "reports/patched", "examples/replaced", "reports/unrelated"):
                self._manifest(root, path, self._trust_package(path.replace("/", "-")))
            self.assertEqual(self._probe_paths(root), {
                "members/included/Cargo.toml", "tests/explicit/Cargo.toml",
                "reports/patched/Cargo.toml", "examples/replaced/Cargo.toml",
            })

    def test_external_dependency_workspace_does_not_admit_unrelated_members_or_dev_deps(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self._tree(root)
            ty = root / "first-party/ty/Cargo.toml"
            ty.write_text(ty.read_text().replace('[workspace]', '[workspace]\nmembers = ["unused"]') +
                '\n[dev-dependencies]\nunused = { path = "unused" }\n')
            self._manifest(root, "first-party/ty/unused", self._trust_package())
            self.assertEqual(self._probe_paths(root), {"first-party/ty/Cargo.toml"})

    def test_root_config_patch_precedence_and_path_override_are_reachable(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self._manifest(root, ".", '[workspace]\nmembers = []\n'
                '[patch.crates-io]\nselected = { path = "reports/superseded" }\n')
            for path in ("reports/superseded", "tests/effective", "examples/path-override"):
                self._manifest(root, path, self._trust_package())
            (root / ".cargo").mkdir()
            (root / ".cargo/config.toml").write_text('paths = ["examples/path-override"]\n'
                '[patch.crates-io]\nselected = { path = "tests/effective" }\n')
            self.assertEqual(self._probe_paths(root), {
                "tests/effective/Cargo.toml", "examples/path-override/Cargo.toml",
            })

    def test_explicit_workspace_owner_binds_inherited_path(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self._tree(root)
            member = root / "crates/plain/Cargo.toml"
            member.write_text(member.read_text() + 'remote = { path = "../../other/member" }\n')
            self._manifest(root, "other/member", '[package]\nname = "remote"\nworkspace = "../../owner"\n'
                '[dependencies]\nlinked = { workspace = true }\n')
            self._manifest(root, "owner", '[workspace]\nmembers = ["../other/member"]\n'
                '[workspace.dependencies]\nlinked = { path = "../reports/linked" }\n')
            self._manifest(root, "reports/linked", self._trust_package())
            self.assertIn("reports/linked/Cargo.toml", self._probe_paths(root))

    def test_shared_member_keeps_each_bootstrap_workspace_inheritance_context(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            outer = self._manifest(root, ".", '[workspace]\nmembers = ["nested/shared"]\n'
                '[workspace.dependencies]\nlinked = { path = "reports/outer" }\n')
            inner = self._manifest(root, "nested", '[workspace]\nmembers = ["shared"]\n'
                '[workspace.dependencies]\nlinked = { path = "../tests/inner" }\n')
            shared = self._manifest(root, "nested/shared", '[package]\nname = "shared"\n'
                '[dependencies]\nlinked = { workspace = true }\n')
            outer_target = self._manifest(root, "reports/outer", self._trust_package("outer"))
            inner_target = self._manifest(root, "tests/inner", self._trust_package("inner"))
            graph = recreate_bootstrap._Stage0ManifestGraph(root)
            self.assertEqual(graph.owner(shared), inner)
            reached = graph.collect([outer, shared])
            self.assertTrue({outer_target, inner_target} <= reached)

    def test_recipe_roots_are_source_derived_and_new_literal_roots_cannot_disappear(self):
        root = SCRIPT.parent.parent
        roots = {str(path.relative_to(root)) for path in recreate_bootstrap.stage0_bootstrap_manifest_roots(root)}
        source = (root / "src/bootstrap/src/core/build_steps/tool.rs").read_text()
        # Independent census of every literal tool path in the source, including
        # optional tools: existing bootstrap configurations need not match the
        # recreator's generated docs=false configuration.
        graph = recreate_bootstrap._Stage0ManifestGraph(root)
        reached = graph.collect(recreate_bootstrap.stage0_bootstrap_manifest_roots(root))
        for path in re.findall(r'\bpath:\s*"([^"]+)"', source):
            manifest = (root / path / "Cargo.toml").resolve()
            if manifest.is_file():
                self.assertTrue(manifest in reached, path)
        self.assertTrue({"Cargo.toml", "library/Cargo.toml", "src/bootstrap/Cargo.toml",
                         "first-party/ty/crates/tla-cli/Cargo.toml", "targo-trust/Cargo.toml",
                         "src/tools/error_index_generator/Cargo.toml", "src/tools/rustbook/Cargo.toml"} <= roots)
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory)
            recipe = fixture / "src/bootstrap/src/core/build_steps/tool.rs"
            recipe.parent.mkdir(parents=True)
            recipe.write_text('fn ensure_default_verifier_tool_bins() { ToolBuild { path: "reports/new", } }\n'
                              'fn ensure_user_facing_tools() { ToolBuild { path: "tests/new", } }\n')
            for path in ("reports/new", "tests/new"):
                self._manifest(fixture, path, self._trust_package())
            self.assertEqual(len(recreate_bootstrap.stage0_bootstrap_manifest_roots(fixture)), 2)
            recipe.write_text(recipe.read_text() +
                'bootstrap_tool!(New, "examples/added", "new";);\n')
            self._manifest(fixture, "examples/added", self._trust_package())
            self.assertEqual(len(recreate_bootstrap.stage0_bootstrap_manifest_roots(fixture)), 3)
            recipe.write_text(recipe.read_text().replace('"reports/new"', 'dynamic_path'))
            with self.assertRaisesRegex(RuntimeError, "nonliteral ToolBuild"):
                recreate_bootstrap.stage0_bootstrap_manifest_roots(fixture)

    def test_cargo_membership_exposes_implicit_member_dev_edge(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self._tree(root)
            implicit = self._manifest(root, "implicit", '[package]\nname = "implicit"\n'
                '[dev-dependencies]\ncontrol = { path = "../reports/control" }\n')
            control = self._manifest(root, "reports/control", self._trust_package())
            entry = root / "Cargo.toml"
            member = root / "crates/plain/Cargo.toml"
            member.write_text(member.read_text() + 'implicit = { path = "../../implicit" }\n')
            self.assertIn("reports/control/Cargo.toml", self._probe_paths(root),
                          "offline fallback must also retain implicit-member dev dependencies")
            pack = self._pack(root / "store", "active", stderr=None)
            calls = []
            def metadata(argv, **kwargs):
                manifest = Path(argv[-1])
                calls.append(manifest)
                if manifest == entry:
                    return SimpleNamespace(returncode=0, stderr="", stdout=json.dumps({
                        "workspace_root": str(root), "workspace_members": ["plain", "implicit"],
                        "packages": [{"id": "plain", "manifest_path": str(member)},
                                     {"id": "implicit", "manifest_path": str(implicit)}],
                    }))
                return SimpleNamespace(returncode=0, stderr="", stdout="")
            with patch.object(recreate_bootstrap.subprocess, "run", side_effect=metadata):
                self.assertIsNone(recreate_bootstrap.stage0_refuses_tree_manifest(pack, root))
            self.assertIn(control, calls)

    def test_offline_failure_still_probes_active_schema_and_preserves_every_input(self):
        for prefix in ("reports", "tests", "examples"):
            with self.subTest(prefix=prefix), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                self._tree(root)
                control = self._manifest(root, prefix + "/control", self._trust_package())
                member = root / "crates/plain/Cargo.toml"
                member.write_text(member.read_text() + f'control = {{ path = "../../{prefix}/control" }}\n')
                (root / "Cargo.lock").write_text("# preserved lock\nversion = 4\n")
                (root / "bootstrap.toml").write_text('# preserved bootstrap config\n')
                (root / ".cargo").mkdir()
                (root / ".cargo/config.toml").write_text('[net]\noffline = true\n')
                pack = self._pack(root / "store", "active", stderr=None)
                before = {path: path.read_bytes() for path in root.rglob("*") if path.is_file()}
                def metadata(argv, **kwargs):
                    manifest = Path(argv[-1])
                    error = self.UNRELATED_FAILURE
                    if manifest == control:
                        error = f'error: unknown field `unknown_future_key`\n --> {control}:7:1\n'
                    return SimpleNamespace(returncode=101, stderr=error, stdout="")
                with patch.object(recreate_bootstrap.subprocess, "run", side_effect=metadata):
                    refused = recreate_bootstrap.stage0_refuses_tree_manifest(pack, root)
                self.assertEqual(refused[0], control)
                self.assertEqual(before, {path: path.read_bytes() for path in root.rglob("*") if path.is_file()})

    def test_unrelated_workspace_diagnostic_never_replaces_selected_candidate(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self._tree(root)
            control = self._manifest(root, "reports/unused", self._trust_package())
            pack = self._pack(root / "store", "active", stderr=None)
            output = io.StringIO()
            refusal = f'error: unknown field `unknown_future_key`\n --> {control}:7:1\n'
            with patch.object(recreate_bootstrap, "_capture_atpkg_pack", return_value={"pack_local_path": str(pack)}), patch.object(
                recreate_bootstrap.subprocess, "run", return_value=SimpleNamespace(returncode=101, stderr=refusal)
            ), patch.object(sys, "stdout", output):
                self.assertEqual(recreate_bootstrap.atpkg_trust_sysroot(root), pack)
            self.assertIn("INCONCLUSIVE (not a compatibility proof)", output.getvalue())

    def test_local_symlink_escape_refuses_instead_of_hiding_an_edge(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "checkout"
            root.mkdir()
            self._tree(root)
            outside = self._manifest(Path(directory), "outside", self._trust_package())
            (root / "external").symlink_to(outside.parent, target_is_directory=True)
            member = root / "crates/plain/Cargo.toml"
            member.write_text(member.read_text() + 'external = { path = "../../external" }\n')
            with self.assertRaisesRegex(RuntimeError, "escapes checkout"):
                self._probe_paths(root)

    def test_schema_probe_is_locked_offline_and_uses_disposable_owned_home(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "checkout"
            root.mkdir()
            self._tree(root)
            pack = self._pack(Path(directory) / "store", "8571", stderr=None)
            before = sorted(str(p.relative_to(root)) for p in root.rglob('*'))
            observed = {}
            def probe(argv, **kwargs):
                observed.update(argv=argv, **kwargs)
                self.assertTrue(Path(kwargs['env']['CARGO_HOME']).is_dir())
                return SimpleNamespace(returncode=0, stderr='')
            with patch.dict(os.environ, {'CARGO_HOME': '/unbound/home', 'RUSTC': '/unbound/compiler'}), patch.object(
                recreate_bootstrap.subprocess, 'run', side_effect=probe
            ):
                self.assertIsNone(recreate_bootstrap.stage0_refuses_tree_manifest(pack, root))
            self.assertEqual(observed['argv'][0], str(pack / 'bin/cargo'))
            self.assertIn('--locked', observed['argv'])
            self.assertIn('--offline', observed['argv'])
            self.assertEqual(observed['cwd'], root)
            self.assertNotIn('RUSTC', observed['env'])
            self.assertNotEqual(observed['env']['CARGO_HOME'], '/unbound/home')
            self.assertFalse(Path(observed['env']['CARGO_HOME']).exists())
            self.assertEqual(before, sorted(str(p.relative_to(root)) for p in root.rglob('*')))

    def test_schema_probe_refuses_unbound_ancestor_configuration_before_child(self):
        with tempfile.TemporaryDirectory() as directory:
            parent = Path(directory)
            root = parent / 'checkout'
            root.mkdir()
            self._tree(root)
            (parent / '.cargo').mkdir()
            config = parent / '.cargo/config.toml'
            config.write_text('[build]\nrustc = "/unbound/compiler"\n')
            before = config.read_bytes()
            pack = self._pack(parent / 'store', '8571', stderr=None)
            with patch.object(recreate_bootstrap.subprocess, 'run') as child:
                with self.assertRaisesRegex(RuntimeError, 'Cargo authority rejected'):
                    recreate_bootstrap.stage0_refuses_tree_manifest(pack, root)
            child.assert_not_called()
            self.assertEqual(config.read_bytes(), before)

    def test_schema_refusal_is_reported_with_the_manifest_and_the_message(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "checkout"
            root.mkdir()
            self._tree(root)
            pack = self._pack(Path(directory) / "store", "8571", stderr=self.SCHEMA_REFUSAL)
            refusal = recreate_bootstrap.stage0_refuses_tree_manifest(pack, root)
            self.assertIsNotNone(refusal)
            manifest, message = refusal
            self.assertEqual(manifest.name, "Cargo.toml")
            self.assertIn("first-party/ty", str(manifest))
            self.assertIn("unknown field `compiler_timeout_secs`", message)

    def test_an_unrelated_cargo_failure_never_rejects_a_pack(self):
        """A network or lockfile failure says nothing about the manifest schema.

        Rejecting on it would leave the machine with no stage0 at all, which is
        strictly worse than selecting a pack that would have worked.
        """
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "checkout"
            root.mkdir()
            self._tree(root)
            pack = self._pack(Path(directory) / "store", "8571", stderr=self.UNRELATED_FAILURE)
            self.assertIsNone(recreate_bootstrap.stage0_refuses_tree_manifest(pack, root))

    def test_a_parsing_pack_is_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "checkout"
            root.mkdir()
            self._tree(root)
            pack = self._pack(Path(directory) / "store", "8571", stderr=None)
            self.assertIsNone(recreate_bootstrap.stage0_refuses_tree_manifest(pack, root))

    def _store(self, home: Path) -> Path:
        store = home / "Library" / "Application Support" / "aterm" / "pkg" / "store" / "trust"
        store.mkdir(parents=True)
        return store

    def test_a_newer_refusing_pack_does_not_shadow_an_older_parsing_one(self):
        with tempfile.TemporaryDirectory() as directory:
            home = Path(directory) / "home"
            root = Path(directory) / "checkout"
            root.mkdir()
            self._tree(root)
            store = self._store(home)
            self._pack(store, "8571", stderr=self.SCHEMA_REFUSAL)
            older = self._pack(store, "6808", stderr=None)
            # Capability never authorizes staged-pack selection. The older
            # parsing pack is the captured active/current identity here.
            with patch.object(recreate_bootstrap, "_capture_atpkg_pack", return_value={
                "pack_local_path": str(older)
            }):
                self.assertEqual(recreate_bootstrap.atpkg_trust_sysroot(root), older)

    def test_every_pack_refusing_returns_none_and_names_the_options(self):
        with tempfile.TemporaryDirectory() as directory:
            home = Path(directory) / "home"
            root = Path(directory) / "checkout"
            root.mkdir()
            self._tree(root)
            store = self._store(home)
            packs = [self._pack(store, build, stderr=self.SCHEMA_REFUSAL)
                     for build in ("8571", "8560")]
            out = io.StringIO()
            for active in packs:
                with self.subTest(active=active.name), patch.object(
                    recreate_bootstrap, "_capture_atpkg_pack",
                    return_value={"pack_local_path": str(active)},
                ), patch.object(sys, "stdout", out):
                    self.assertIsNone(recreate_bootstrap.atpkg_trust_sysroot(root))
            printed = out.getvalue()
            self.assertIn("REFUSES this tree's manifests", printed)
            self.assertIn("8571", printed)
            self.assertIn("8560", printed)
            self.assertIn("unknown field `compiler_timeout_secs`", printed)
            # v7/D3: a refusal carries the fix, with options.
            self.assertIn("--require-seed", printed)
            self.assertIn("--no-atpkg", printed)
            self.assertIn("atpkg update", printed)

    def test_without_a_root_selection_is_unprobed_and_takes_the_current(self):
        """No checkout means no schema probe, never a staged-pack fallback."""
        with tempfile.TemporaryDirectory() as directory:
            home = Path(directory) / "home"
            store = self._store(home)
            older = self._pack(store, "6808", stderr=None)
            newest = self._pack(store, "8571", stderr=self.SCHEMA_REFUSAL)
            for current in (newest, older):
                with self.subTest(current=current.name), patch.object(
                    recreate_bootstrap, "_capture_atpkg_pack",
                    return_value={"pack_local_path": str(current)},
                ), patch.object(recreate_bootstrap, "stage0_refuses_tree_manifest") as probe:
                    self.assertEqual(recreate_bootstrap.atpkg_trust_sysroot(), current)
                    probe.assert_not_called()


@unittest.skipUnless(sys.version_info >= (3, 11), "mint configuration requires tomllib")
class MintConfigurationBoundaryTests(unittest.TestCase):
    """Real config evaluation, seed admission/freshness and LLVM capture owners."""

    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location(
            "mint_seed_support_for_config_test", SCRIPT.with_name("mint_seed_support.py")
        )
        assert spec is not None and spec.loader is not None
        cls.mint = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = cls.mint
        spec.loader.exec_module(cls.mint)

    @staticmethod
    def mint_host_tables(seed: Path, host: str, fixture) -> list[str]:
        """Write `host`'s mint receipt, surface and record beside the archives that
        seed_archives wrote (the surface's entrypoints are those archives' members),
        and return the ledger's [release.hosts] tables for it."""
        helper = recreate_bootstrap.seed_host_ledger_module()
        pins = {}
        for line in (seed.parent.parent / "src/stage0").read_text().splitlines():
            key, _, value = line.partition("=")
            pins[key] = value
        source_version = fixture.version.removesuffix("-trust")
        receipt = "".join(f"{key}={value}\n" for key, value in {
            "schema": "trust-seed-mint-v1", "source_commit": "c" * 40, "source_commit_date": fixture.date,
            "source_version": source_version, "host": host,
            "pinned_seed_commit": "b" * 40, "pinned_seed_date": "2026-07-01",
            "pinned_seed_compiler_sha256": "1" * 64, "pinned_seed_driver_sha256": "2" * 64,
            "ddc_seed_relation": "pin-ancestor", "ddc_seed_commit": "d" * 40, "ddc_seed_date": "2026-06-30",
            "ddc_seed_lineage": "trust", "ddc_seed_compiler_sha256": "3" * 64,
            "ddc_seed_driver_sha256": "4" * 64, "ddc_build_driver": "the pinned seed's cargo, in both builds",
            "ddc_scope": "<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std",
            "stage2_tree_sha256_pinned_seed": "5" * 64, "stage2_tree_sha256_ddc_seed": "5" * 64,
            "ddc_verdict": "identical", "lineage_disjoint_anchor": "none", "self_host_proof": "pass",
        }.items()) + f"compiler_file={'6' * 64} bin/trustc\n"
        content = {"rustc": "trustc", "cargo": "targo"}
        surface = {
            "schema": "trust-self-host-seed-surface-v1", "source_version": source_version, "host": host,
            "tool_versions": {name: f"{name} {fixture.version}" for name in ("trustc", "targo", "trustfmt")},
            "entrypoint_sha256": {
                name: hashlib.sha256(f"seed:bin:{content.get(name, name)}".encode()).hexdigest()
                for name in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt")
            },
            "tree": {"sha256": "7" * 64},
        }
        proofs = (receipt.encode(), (json.dumps(surface, sort_keys=True) + "\n").encode())
        for relative, payload in zip(helper.proof_paths(host), proofs):
            (seed / relative).parent.mkdir(parents=True, exist_ok=True)
            (seed / relative).write_bytes(payload)
        record = helper.make_host_record(pins, host, *proofs)
        (seed / helper.record_path(host)).write_bytes(helper.record_bytes(record))
        return helper.render_host_tables({host: record})

    def seed_checkout(self, root):
        mint = self.mint

        host = mint.detected_host()
        fixture = SeedAuthorityTests()
        pins, payloads = fixture.seed_archives(root, host)
        dist = root / "bootstrap/trust-stage0/dist" / fixture.date
        for component in ("trust-src", "trust-std"):
            suffix = "" if component == "trust-src" else f"-{host}"
            archive = dist / f"{component}-{fixture.version}{suffix}.tar.xz"
            with tarfile.open(archive, "w:xz"):
                pass
            digest = recreate_bootstrap._sha256_file(archive)
            payloads.append({"path": archive.relative_to(root).as_posix(), "pinned_sha256": digest})
        manifest = dist / "channel-rust-trust.toml"
        manifest.write_bytes(b"fixture channel manifest\n")
        manifest_sha = recreate_bootstrap._sha256_file(manifest)
        for component in ("compiler", "rustfmt"):
            pins.update({
                f"{component}_date": fixture.date,
                f"{component}_version": fixture.version,
                f"{component}_git_commit_hash": "c" * 40,
                f"{component}_channel_manifest_hash": manifest_sha,
            })
        source = root / "src"
        defaults = source / "bootstrap/defaults"
        defaults.mkdir(parents=True)
        shutil.copyfile(SCRIPT.parent.parent / "src/bootstrap/bootstrap.py", source / "bootstrap/bootstrap.py")
        shutil.copyfile(SCRIPT.parent.parent / "src/bootstrap/stage0_identity.py", source / "bootstrap/stage0_identity.py")
        (defaults / "bootstrap.compiler.toml").write_text(
            '[build]\nextended = true\npatch-binaries-for-nix = false\n[llvm]\nassertions = true\n'
        )
        (source / "rust-compat-version").write_text("1.101.0\n")
        (source / "version").write_text("1.101.0\n")
        (source / "llvm-project").mkdir()
        (source / "llvm-project/CMakeLists.txt").write_text("# fixture LLVM source\n")
        (source / "stage0").write_text("\n".join([
            *(f"{key}={value}" for key, value in pins.items()),
            *(f"{row['path'].removeprefix('bootstrap/trust-stage0/')}={row['pinned_sha256']}" for row in payloads),
        ]) + "\n")
        (dist.parent.parent / "seed-ledger.toml").write_text(
            'scope = "internal"\npromotion_decision = "admit-internal"\n'
            'signatures = ["internal-admission-only"]\nchecksums = '
            + json.dumps([f"sha256:{row['pinned_sha256']}" for row in payloads]) + '\n'
            '[artifact_root]\nkind = "fixture"\n[release]\n'
            f'date = "{fixture.date}"\ncompiler_version = "{fixture.version}"\n'
            f'compiler_git_commit_hash = "{"c" * 40}"\nchannel_manifest_hash = "{manifest_sha}"\n'
            f'host_triple = "{host}"\nvisibility = "private"\n'
            '[release.reported_product_identities]\n'
            f'trustc = "trustc {fixture.version}"\ntargo = "targo {fixture.version}"\n'
            f'trustfmt = "trustfmt {fixture.version}"\n'
            # The host's own mint record, as the committed ledger carries it: a
            # single-host ledger never admits a Linux host (LINUX_SEED_HOSTS), and
            # this host is the machine's own.
            + "\n".join(self.mint_host_tables(dist.parent.parent, host, fixture)) + "\n"
        )
        scripts = root / "scripts"
        scripts.mkdir()
        for name in ("scripts/check_seed_freshness.py", "scripts/mint_seed_support.py",
                     "scripts/lib/native_serial.py", "scripts/lib/landing_targo.py",
                     "scripts/lib/seed_compiler_identity.py"):
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(SCRIPT.parent.parent / name, root / name)
        return host

    def commit(self, root):
        for args in (("init", "-q"), ("add", "."), ("commit", "-qm", "fixture")):
            subprocess.run([
                "git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.com",
                "-c", f"core.hooksPath={os.devnull}", *args,
            ], cwd=root, check=True, capture_output=True)

    def test_unmarked_flat_and_recursive_configs_reach_real_seed_and_llvm_owners(self):
        mint = self.mint

        for recursive in (False, True):
            with self.subTest(recursive=recursive), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                host = self.seed_checkout(root)
                config = root / "mint.toml"
                if recursive:
                    config.write_text('include = ["one.toml", "two.toml"]\n')
                    (root / "one.toml").write_text('[llvm]\nassertions = false\n')
                    (root / "two.toml").write_text('include = ["nested.toml"]\n[llvm]\nassertions = true\n')
                    (root / "nested.toml").write_text('profile = "compiler"\n[llvm]\ndownload-ci-llvm = true\n')
                else:
                    config.write_text('[build]\npatch-binaries-for-nix = false\n[llvm]\ndownload-ci-llvm = true\n')
                self.commit(root)
                context = mint.mint_configuration_context(root, config, host, jobs=6)
                self.assertEqual(context["xpy_config_overrides"]["build.jobs"], 6)
                malformed = recreate_bootstrap.capture_bootstrap_lineage(
                    root, host, config_path=config, mint_configuration=[],
                )
                self.assertEqual(malformed["status"], "rejected")
                self.assertTrue(any("not an object" in error for error in malformed["errors"]))
                build = root / "build/pack-mint-fixture"
                # The recreator still requires its own declared mode and rejects
                # recursive includes; only the explicit mint context changes that.
                plain = recreate_bootstrap.capture_bootstrap_lineage(root, host, config_path=config)
                self.assertEqual(plain["status"], "rejected")
                bootstrap = recreate_bootstrap.capture_bootstrap_lineage(
                    root, host, config_path=config, build_root=build, mint_configuration=context,
                )
                self.assertEqual(bootstrap["status"], "seed-validated-pending-hydration", bootstrap["errors"])
                self.assertEqual(bootstrap["errors"], [])
                self.assertEqual(bootstrap["validated_seed"]["admission_status"], "internal-admitted")
                self.assertEqual(bootstrap["config_sha256"], context["fingerprint"])
                self.assertEqual(bootstrap["config_file_sha256"], recreate_bootstrap._sha256_file(config))
                with patch.object(recreate_bootstrap, "_nixos_host", return_value=True):
                    nix = recreate_bootstrap.capture_bootstrap_lineage(
                        root, host, config_path=config, build_root=build, mint_configuration=context,
                    )
                if recursive:
                    # Python does not see a profile named through an include;
                    # its stage0 extraction must not silently patch the seed.
                    self.assertEqual(nix["status"], "rejected")
                    self.assertTrue(any("explicit root-config" in error for error in nix["errors"]))
                else:
                    self.assertEqual(nix["status"], "seed-validated-pending-hydration", nix["errors"])
                    config.write_text('[build]\npatch-binaries-for-nix = false # Python sees a literal suffix\n')
                    commented = mint.mint_configuration_context(root, config, host)
                    with patch.object(recreate_bootstrap, "_nixos_host", return_value=True):
                        refused = recreate_bootstrap.capture_bootstrap_lineage(
                            root, host, config_path=config, build_root=build, mint_configuration=commented,
                        )
                    self.assertEqual(refused["status"], "rejected")
                    self.assertTrue(any("explicit root-config" in error for error in refused["errors"]))
                    config.write_text('[build]\npatch-binaries-for-nix = false\n[llvm]\ndownload-ci-llvm = true\n')
                llvm = recreate_bootstrap.capture_llvm_before_build(
                    root, host, None, config, build_root=build, mint_configuration=context,
                )
                self.assertEqual((llvm["mode"], llvm["mode_reasons"]), ("in-tree", []))
                self.assertTrue(llvm["source"]["clean"], llvm["source"]["errors"])
                self.assertFalse(llvm["output"]["present"])
                self.assertEqual(recreate_bootstrap.capture_llvm_before_build(
                    root, host, None, config, build_root=build,
                )["mode"], "unknown")
                if recursive:
                    self.assertEqual(len(context["configuration_closure"]["files"]), 5)
                    self.assertTrue(mint.effective_bootstrap_config(root, config)["llvm"]["assertions"])
                    (root / "nested.toml").write_text('profile = "compiler"\n[llvm]\nassertions = false\n')
                    changed = recreate_bootstrap.capture_bootstrap_lineage(
                        root, host, config_path=config, build_root=build, mint_configuration=context,
                    )
                    self.assertEqual(changed["status"], "rejected")
                    self.assertTrue(any("differs" in error for error in changed["errors"]))

    def test_mint_context_refuses_tool_overrides_and_external_llvm_in_includes_and_profiles(self):
        mint = self.mint

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = root / "mint.toml"
            config.write_text('include = ["included.toml"]\n')
            included = root / "included.toml"
            for selector in mint.STAGE0_SELECTORS:
                included.write_text(f'[build]\n{selector} = "/forbidden/tool"\n')
                with self.subTest(selector=selector), self.assertRaisesRegex(mint.WorkflowError, f"build.{selector}"):
                    mint.mint_configuration_context(root, config, "test-host")
            included.write_text('[target.test-host]\nllvm-config = "/external/llvm-config"\n')
            with self.assertRaisesRegex(mint.WorkflowError, "external.*llvm-config"):
                mint.mint_configuration_context(root, config, "test-host")
            defaults = root / "src/bootstrap/defaults"
            defaults.mkdir(parents=True)
            included.write_text('profile = "compiler"\n')
            (defaults / "bootstrap.compiler.toml").write_text('[target.test-host]\nllvm-config = "/profile/llvm-config"\n')
            with self.assertRaisesRegex(mint.WorkflowError, "external.*llvm-config"):
                mint.mint_configuration_context(root, config, "test-host")
            (defaults / "bootstrap.compiler.toml").write_text('[llvm]\nassertions = false\n')
            before = mint.mint_configuration_context(root, config, "test-host")
            (defaults / "bootstrap.compiler.toml").write_text('[llvm]\nassertions = true\n')
            after = mint.mint_configuration_context(root, config, "test-host")
            self.assertNotEqual(before["fingerprint"], after["fingerprint"])

    def test_native_capture_still_refuses_undeclared_compiler_controls_without_mocks(self):
        with tempfile.TemporaryDirectory() as directory, patch.dict(
            os.environ, {"PATH": "", "RUSTFLAGS": "-C link-arg=injected"}, clear=True,
        ):
            # Empty PATH also makes platform tools unavailable; the assertion
            # pins the independent override refusal from the real native owner.
            native = recreate_bootstrap.capture_build_authority(Path(directory), "test-host", None)
            self.assertEqual(native["status"], "rejected")
            self.assertIn("RUSTFLAGS", native["ambient_overrides"])
            self.assertTrue(any("ambient build-authority overrides" in error for error in native["errors"]))


class MintStageEvidenceTests(unittest.TestCase):
    """A real custom-root LLVM observation, tool audit, re-verifier and seal reader.

    Source/seed/native platform observations use the existing synthetic fixtures;
    archive admission and native-tool capture have their own adversarial suites.
    LLVM bytes, stage/producer bytes, receipt writing and both readers are real.
    """

    def test_mint_observes_its_own_build_and_strict_promotion_reads_the_receipt(self):
        spec = importlib.util.spec_from_file_location(
            "mint_seed_support_for_stage_evidence_test", SCRIPT.with_name("mint_seed_support.py")
        )
        assert spec is not None and spec.loader is not None
        mint = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = mint
        spec.loader.exec_module(mint)

        fixture = StageToolProvenanceTests()
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = Path(directory) / "checkout"
            (root / "build").mkdir(parents=True)
            build = root / "build/pack-mint-fixture"
            stage = build / fixture.host / "stage2"
            config = root / "mint-config.toml"
            config.write_text('[build]\nsubmodules = false\n[llvm]\ndownload-ci-llvm = false\n')
            cargo = root / "build/private-cargo"
            cargo.mkdir()
            environment = {
                "CARGO_HOME": str(cargo), "RUSTUP_HOME": str(root / "build/private-rustup"),
                "SOURCE_DATE_EPOCH": "123", "CARGO_NET_OFFLINE": "true",
                "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
            }
            library = clean_lean_fixture(root)
            lean_environment = {
                "CLEAN_OLEAN_PINNED_LEAN_LIB": str(library), "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1",
            }
            environment.update(lean_environment)
            stack.enter_context(patch.dict(os.environ, environment, clear=True))
            stack.enter_context(patch.object(mint, "stage_evidence_owner", return_value=recreate_bootstrap))
            stack.enter_context(patch.object(recreate_bootstrap, "capture_source_lineage", return_value=fixture.lineage()))
            stack.enter_context(patch.object(recreate_bootstrap, "capture_llvm_source_identity", return_value=fixture.llvm_source()))

            def bootstrap(_root, _host, *, build_root, config_path, mint_configuration):
                self.assertEqual((build_root, config_path), (build, config))
                result = fixture.bootstrap_lineage(hydrated=build.exists(), admission_status="internal-admitted")
                result["config_path"] = "mint-config.toml"
                result["config_sha256"] = mint_configuration["fingerprint"]
                result["config_file_sha256"] = hashlib.sha256(config.read_bytes()).hexdigest()
                result["mint_configuration"] = mint_configuration
                return result

            def authority(_root, _host, _llvm, *, cargo_home, declared_environment, mint_configuration):
                self.assertEqual((cargo_home, declared_environment), (cargo, environment))
                self.assertEqual(mint_configuration["clean_lean_inputs"]["environment"], lean_environment)
                return {**fixture.build_authority(), "clean_lean_inputs": mint_configuration["clean_lean_inputs"]}

            stack.enter_context(patch.object(recreate_bootstrap, "capture_bootstrap_lineage", side_effect=bootstrap))
            stack.enter_context(patch.object(recreate_bootstrap, "capture_build_authority", side_effect=authority))
            stack.enter_context(patch.object(recreate_bootstrap, "_capture_identity", side_effect=fixture.identity_capture(stage)))
            # An unrelated default-layout LLVM must supply no evidence for this mint.
            decoy = fixture.install_llvm(root, b"unrelated default build")
            observation = mint.capture_mint_stage_evidence(root, build, config, fixture.host, jobs=6)
            self.assertFalse(observation["llvm_before"]["output"]["present"])
            observation_path = root / "build/observation.json"
            mint.write_json_exclusive(observation_path, observation)
            donor = Path(directory) / "donor"
            fixture.layout(str(donor))
            fixture.install_llvm(donor, b"mint LLVM")
            build.mkdir()
            shutil.move(str(donor / "build" / fixture.host), build / fixture.host)
            self.assertTrue(decoy.exists())
            with self.assertRaisesRegex(mint.WorkflowError, "another build, config, host or closed environment"):
                mint.finish_mint_stage_evidence(root, build, config, fixture.host, observation_path, jobs=4)
            with patch("sys.stdout", io.StringIO()):
                mint.finish_mint_stage_evidence(root, build, config, fixture.host, observation_path, jobs=6)
            receipt = json.loads((stage / "tool-provenance.json").read_text())
            self.assertEqual(receipt["writer"], "scripts/mint_and_prove_seed.sh")
            self.assertNotIn("recreator_invocation", receipt)
            self.assertEqual(receipt["status"], "internal-release-ready")
            self.assertTrue(receipt["llvm_identity"]["identity_stated"])
            self.assertEqual(
                receipt["llvm_identity"]["build_record"]["bootstrap_config_sha256"],
                observation["mint_configuration"]["fingerprint"],
            )
            self.assertEqual(receipt["llvm_identity"]["provenance"], "built-in-this-run")
            self.assertEqual(receipt["llvm_identity"]["output_dirs"], [f"build/pack-mint-fixture/{fixture.host}/llvm"])
            reader = load_stage_receipt_reader()
            self.assertEqual(reader.llvm_identity_unstated(stage), "")
            lines = reader.lines(stage, fixture.commit)
            self.assertIn("stage_receipt_writer=scripts/mint_and_prove_seed.sh", lines)
            self.assertIn("stage_receipt_llvm_identity=stated", lines)
            self.assertIn("stage_receipt_recreator_argv=not-recorded", lines)

            original_receipt = (stage / "tool-provenance.json").read_bytes()
            for container in (receipt["build_authority"]["clean_lean_inputs"],
                              receipt["bootstrap_lineage"]["mint_configuration"]["clean_lean_inputs"]):
                previous_flags = container["oracle_identity"][1]
                container["oracle_identity"][1] = bool(previous_flags)
                (stage / "tool-provenance.json").write_text(json.dumps(receipt))
                with patch("sys.stdout", io.StringIO()):
                    self.assertFalse(recreate_bootstrap.verify_stage_tool_provenance(
                        root, fixture.host, 2, build_root=build, config_path=config, cargo_home=cargo,
                        declared_environment=environment, require_immutable_lineage=True, require_llvm_identity=True,
                        mint_configuration=observation["mint_configuration"],
                    ))
                container["oracle_identity"][1] = previous_flags
            (stage / "tool-provenance.json").write_bytes(original_receipt)

            # The read-only verifier and sealed-tree reader both catch replacements.
            (stage / "bin/targo").write_bytes(b"replaced after the build")
            with patch("sys.stdout", io.StringIO()):
                self.assertFalse(recreate_bootstrap.verify_stage_tool_provenance(
                    root, fixture.host, 2, build_root=build, config_path=config, cargo_home=cargo,
                    declared_environment=environment, require_immutable_lineage=True, require_llvm_identity=True,
                    mint_configuration=observation["mint_configuration"],
                ))
            with self.assertRaises(reader.StageReceiptError):
                reader.lines(stage, fixture.commit)
            with self.assertRaisesRegex(mint.WorkflowError, "unstarted build"):
                mint.capture_mint_stage_evidence(root, build, config, fixture.host)

    def test_custom_seed_root_does_not_read_an_unrelated_default_stage0(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "build/test-host/stage0/bin").mkdir(parents=True)
            (root / "build/test-host/stage0/bin/trustc").write_bytes(b"unrelated compiler")
            result = recreate_bootstrap._capture_seed_compiler_identity(
                root, "test-host", {}, {}, {}, build_root=root / "build/pack-mint-fixture",
            )
            self.assertEqual(result["status"], "not-materialized")
            self.assertEqual(result["stage0_root"], "build/pack-mint-fixture/test-host/stage0")

    def test_declared_mint_native_environment_is_bound_and_other_overrides_still_refuse(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = Path(directory)
            cargo = root / "build/private-cargo"
            cargo.mkdir(parents=True)
            library = root / "native-library"
            library.mkdir()
            (library / "libinput.so").write_bytes(b"first native input")
            declared = {
                "CARGO_HOME": str(cargo), "RUSTUP_HOME": str(root / "build/private-rustup"),
                "SOURCE_DATE_EPOCH": "123", "CARGO_NET_OFFLINE": "true",
                "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                "LIBRARY_PATH": str(library),
            }
            Path(declared["RUSTUP_HOME"]).mkdir()
            stack.enter_context(patch.dict(os.environ, declared, clear=True))
            stack.enter_context(patch.object(recreate_bootstrap.platform, "system", return_value="Linux"))
            stack.enter_context(patch.object(recreate_bootstrap, "bind_native_build_tools", return_value=[]))
            before = recreate_bootstrap.capture_build_authority(root, "test-host", None)
            self.assertEqual(before["status"], "rejected")

            def capture(environment=declared):
                return recreate_bootstrap.capture_build_authority(
                    root, "test-host", None, cargo_home=cargo, declared_environment=environment,
                )

            before = capture()
            self.assertEqual(before["status"], "ready", before["errors"])
            self.assertEqual(before["ambient_overrides"], {})
            self.assertIn("LIBRARY_PATH", before["declared_native_library_paths"])
            self.assertEqual(recreate_bootstrap.capture_build_authority(
                root, "test-host", None, declared_environment=declared,
            )["status"], "rejected")
            (library / "libinput.so").write_bytes(b"changed native input")
            self.assertNotEqual(capture()["authority_sha256"], before["authority_sha256"])
            with patch.dict(os.environ, {"RUSTFLAGS": "-C link-arg=injected"}):
                self.assertEqual(capture()["status"], "rejected")
                self.assertEqual(capture({**declared, "RUSTFLAGS": os.environ["RUSTFLAGS"]})["status"], "rejected")
            self.assertEqual(capture({**declared, "CARGO_HOME": "/another/home"})["status"], "rejected")



@unittest.skipUnless(os.name == "posix" and hasattr(os, "O_NOFOLLOW"), "POSIX directory custody")
class EmptyLlvmPreservationPortabilityTests(unittest.TestCase):
    def test_unsupported_platform_refuses_without_accessing_a_directory(self):
        with patch.object(recreate_bootstrap.sys, "platform", "unsupported"):
            with self.assertRaisesRegex(RuntimeError, "atomic exclusive rename"):
                recreate_bootstrap._empty_llvm_exclusive_rename(-1)


class EmptyLlvmDirectoryModeTests(unittest.TestCase):
    """Every directory on the empty-LLVM custody path is opened by one rule: owned by this
    user and writable by no one else, whatever the umask that made it."""

    def test_a_directory_others_can_write_is_refused_and_a_private_one_opens(self):
        with tempfile.TemporaryDirectory() as temporary:
            build = Path(temporary) / "build"
            build.mkdir()
            for mode in (0o775, 0o757, 0o777):
                build.chmod(mode)
                with self.subTest(mode=oct(mode)), self.assertRaisesRegex(
                        RuntimeError, "requires an owned, non-writable-by-others directory: "):
                    recreate_bootstrap._open_empty_llvm_directory(build)
            for mode in (0o755, 0o700):
                build.chmod(mode)
                with self.subTest(mode=oct(mode)):
                    os.close(recreate_bootstrap._open_empty_llvm_directory(build))
            link = Path(temporary) / "link"
            link.symlink_to(build)
            with self.assertRaises(OSError):
                recreate_bootstrap._open_empty_llvm_directory(link)


@unittest.skipUnless(sys.platform == "darwin", "Darwin exclusive-rename custody controls")
class EmptyLlvmPreservationTests(unittest.TestCase):
    host = "test-host"

    def setUp(self):
        # These are real native owner/retirement controls, not a mocked lease.
        # Select the manager independently of the compiler or legacy PATH CLI.
        selected = os.environ.get("TARGO_COMPONENT_MANAGER") or os.environ.get("TRUST_BUILD_TREE_MANAGER_TARGO")
        self.assertTrue(selected, "supply an actual v2 TARGO_COMPONENT_MANAGER for native custody controls")
        self.manager = str(Path(selected).resolve(strict=True))
        manager_environment = patch.dict(os.environ, {"TRUST_BUILD_TREE_MANAGER_TARGO": self.manager})
        manager_environment.start()
        self.addCleanup(manager_environment.stop)
        temporary = tempfile.TemporaryDirectory(prefix="owned-empty-llvm-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.config = self.root / "bootstrap.toml"
        self.config.write_text("[llvm]\ndownload-ci-llvm = false\n")
        self.output = self.root / "build" / self.host / "llvm"
        self.output.mkdir(parents=True)
        self.retained = self.output.with_name(recreate_bootstrap.EMPTY_LLVM_PRESERVATION)

    def preserve(self, llvm_config=None):
        return recreate_bootstrap.preserve_empty_llvm_for_fresh_seed(
            self.root, self.host, llvm_config, self.config,
        )

    def identity(self, path):
        return recreate_bootstrap._empty_llvm_stat(path.lstat())

    def lock(self, *args):
        environment = {k: v for k, v in os.environ.items() if not k.startswith("TRUST_BUILD_LOCK_")}
        environment["TRUST_REPO"] = str(self.root)
        return subprocess.run([self.manager, "trust", "repo", "lock",
                               *args, "--repo-root", str(self.root)],
                              env=environment, capture_output=True, text=True, check=True, timeout=30)

    def assert_free(self):
        self.assertEqual(self.lock("status").stdout, "trust build-tree lock: free\n")
        self.assertFalse(os.path.lexists(self.root / ".trust-build-lock"))

    def test_explicit_missing_relative_or_symlink_manager_never_falls_back(self):
        before = self.identity(self.output)
        alias = self.root / "manager-alias"
        alias.symlink_to(self.manager)
        for candidate in ("relative-manager", str(self.root / "absent-manager"), str(alias)):
            with self.subTest(manager=candidate), patch.dict(
                    os.environ, {"TRUST_BUILD_TREE_MANAGER_TARGO": candidate}):
                with self.assertRaisesRegex(RuntimeError, "physical executable path"):
                    self.preserve()
            self.assertEqual(self.identity(self.output), before)
            self.assertFalse(self.retained.exists())
        self.assert_free()

    def test_real_empty_inode_is_retained_before_actual_strict_absence_observation(self):
        before = self.identity(self.output)
        self.assertEqual(self.preserve(), self.retained / "llvm")
        self.assertFalse(os.path.lexists(self.output))
        after = self.identity(self.retained / "llvm")
        for key in before:
            if key != "st_ctime_ns":
                self.assertEqual(before[key], after[key], key)
        self.assertEqual(list((self.retained / "llvm").iterdir()), [])
        self.assertEqual(stat.S_IMODE(self.retained.stat().st_mode), 0o700)
        intent = json.loads((self.retained / "intent.json").read_text())
        completed = json.loads((self.retained / "completed.json").read_text())
        self.assertEqual(intent["before"], before)
        self.assertEqual(completed["after"], after)
        self.assertEqual(completed["intent_sha256"], hashlib.sha256((self.retained / "intent.json").read_bytes()).hexdigest())
        with patch.object(recreate_bootstrap, "capture_llvm_source_identity", return_value=StageToolProvenanceTests.llvm_source()):
            observed = recreate_bootstrap.capture_llvm_before_build(self.root, self.host, None, self.config)
        self.assertFalse(observed["output"]["present"])
        self.assertEqual(recreate_bootstrap.llvm_identity_obstacle_rows(
            observed, host=self.host, config_sha256="b" * 64, native_authority_sha256="c" * 64), [])
        self.assert_free()

    def test_completed_absent_retry_rechecks_same_retained_inode_without_writing(self):
        self.preserve()
        before = {p.name: (self.identity(p), p.read_bytes() if p.is_file() else None) for p in self.retained.iterdir()}
        self.assertEqual(self.preserve(), self.retained / "llvm")
        self.assertEqual(before, {p.name: (self.identity(p), p.read_bytes() if p.is_file() else None) for p in self.retained.iterdir()})
        self.assert_free()

    def test_nonempty_outputs_including_hidden_worktree_stamp_and_links_are_not_moved(self):
        for name in ("payload", ".hidden", ".llvm-stamp", "build/object", "link"):
            with self.subTest(name=name):
                entry = self.output / name
                entry.parent.mkdir(parents=True, exist_ok=True)
                if name == "link":
                    entry.symlink_to(self.config)
                else:
                    entry.write_bytes(b"retained")
                before = self.identity(self.output)
                self.assertIsNone(self.preserve())
                self.assertEqual(self.identity(self.output), before)
                self.assertFalse(self.retained.exists())
                self.assertTrue(entry.exists())
                if entry.is_symlink() or entry.is_file():
                    entry.unlink()
                if name == "build/object":
                    entry.parent.rmdir()
        self.assert_free()

    def test_missing_output_and_parents_create_nothing(self):
        self.output.rmdir()
        self.assertIsNone(self.preserve())
        self.assertFalse(self.retained.exists())
        self.output.parent.rmdir()
        self.assertIsNone(self.preserve())
        self.assertFalse(self.output.parent.exists())
        self.assert_free()

    def test_external_unknown_and_included_configs_do_not_mutate(self):
        for text, llvm in (("[llvm]\ndownload-ci-llvm=true\n", None),
                           ('include="other.toml"\n', None),
                           (f'[target.{self.host}]\nllvm-config="/external/llvm-config"\n', "/external/llvm-config")):
            with self.subTest(text=text):
                self.config.write_text(text)
                before = self.identity(self.output)
                self.assertIsNone(self.preserve(llvm))
                self.assertEqual(self.identity(self.output), before)
                self.assertFalse(self.retained.exists())
        self.assert_free()

    def test_symlink_output_and_host_do_not_follow_or_move_other_directories(self):
        outside = self.root / "outside"
        outside.mkdir()
        before = self.identity(outside)
        self.output.rmdir()
        self.output.symlink_to(outside, target_is_directory=True)
        with self.assertRaises(OSError):
            self.preserve()
        self.assertTrue(self.output.is_symlink())
        self.output.unlink()
        self.output.parent.rmdir()
        self.output.parent.symlink_to(outside, target_is_directory=True)
        with self.assertRaises(OSError):
            self.preserve()
        self.assertEqual(self.identity(outside), before)
        self.assertEqual(list(outside.iterdir()), [])
        self.assert_free()

    def test_unsanctioned_build_link_is_refused(self):
        build = self.root / "build"
        actual = self.root / "other-build"
        build.rename(actual)
        build.symlink_to(actual, target_is_directory=True)
        before = self.identity(actual / self.host / "llvm")
        with self.assertRaisesRegex(RuntimeError, "unsanctioned"):
            self.preserve()
        self.assertEqual(self.identity(actual / self.host / "llvm"), before)

    def test_sanctioned_noindex_build_link_keeps_existing_policy(self):
        build = self.root / "build"
        actual = self.root / recreate_bootstrap.BUILD_NOINDEX
        build.rename(actual)
        build.symlink_to(actual, target_is_directory=True)
        before = self.identity(self.output)
        self.preserve()
        self.assertEqual(self.identity(self.retained / "llvm")["st_ino"], before["st_ino"])
        self.assertTrue(build.is_symlink())
        self.assert_free()

    def test_unowned_or_writable_output_is_refused_without_preservation(self):
        before = self.identity(self.output)
        with patch.object(recreate_bootstrap.os, "geteuid", return_value=os.geteuid() + 1):
            with self.assertRaisesRegex(RuntimeError, "requires an owned"):
                self.preserve()
        self.assertEqual(self.identity(self.output), before)
        self.output.chmod(0o777)
        with self.assertRaisesRegex(RuntimeError, "requires an owned"):
            self.preserve()
        self.assertFalse(self.retained.exists())
        self.assert_free()

    def test_existing_normal_lease_is_not_adopted_from_ambient_token(self):
        token = self.lock("acquire", "--kind", "measurement", "--purpose", "other owner",
                          "--pid", str(os.getpid()), "--wait", "0").stdout.strip()
        try:
            original_info = (self.root / ".trust-build-lock/info").read_bytes()
            before = self.identity(self.output)
            with patch.dict(os.environ, {"TRUST_BUILD_LOCK_TOKEN": token}):
                with self.assertRaisesRegex(RuntimeError, "requires its own normal build lease"):
                    self.preserve()
            self.assertEqual((self.root / ".trust-build-lock/info").read_bytes(), original_info)
            self.assertEqual(self.identity(self.output), before)
            self.assertFalse(self.retained.exists())
        finally:
            self.lock("release", token)
        self.assert_free()

    def test_nonempty_output_keeps_original_flow_without_a_recovery_lock_owner(self):
        (self.output / "existing-output").write_bytes(b"leave to strict validator")
        before = self.identity(self.output)
        with patch.dict(os.environ, {"TARGO": str(self.root / "missing-targo")}):
            self.assertIsNone(self.preserve())
        self.assertEqual(self.identity(self.output), before)
        self.assertFalse(self.retained.exists())

    def test_missing_normal_lock_owner_refuses_before_mutation(self):
        before = self.identity(self.output)
        with patch.dict(os.environ, {"TARGO": str(self.root / "missing-targo")}):
            os.environ.pop("TRUST_BUILD_TREE_MANAGER_TARGO", None)
            with self.assertRaisesRegex(RuntimeError, "requires its own normal build lease"):
                self.preserve()
        self.assertEqual(self.identity(self.output), before)
        self.assertFalse(self.retained.exists())

    def test_cancelled_before_rename_retains_intent_and_refuses_retry(self):
        original = recreate_bootstrap._empty_llvm_json
        def interrupted(directory, name, value=None, **kwargs):
            payload = original(directory, name, value, **kwargs)
            if name == "intent.json" and value is not None:
                raise KeyboardInterrupt
            return payload
        before = self.identity(self.output)
        with patch.object(recreate_bootstrap, "_empty_llvm_json", side_effect=interrupted):
            with self.assertRaises(KeyboardInterrupt):
                self.preserve()
        self.assertEqual(self.identity(self.output), before)
        intent = (self.retained / "intent.json").read_bytes()
        with self.assertRaisesRegex(RuntimeError, "incomplete or unexpected"):
            self.preserve()
        self.assertEqual((self.retained / "intent.json").read_bytes(), intent)
        self.assert_free()

    def test_cancelled_after_rename_preserves_inode_and_refuses_incomplete_retry(self):
        original = recreate_bootstrap._empty_llvm_json
        def interrupted(directory, name, value=None, **kwargs):
            if name == "completed.json" and value is not None:
                raise KeyboardInterrupt
            return original(directory, name, value, **kwargs)
        before = self.identity(self.output)
        with patch.object(recreate_bootstrap, "_empty_llvm_json", side_effect=interrupted):
            with self.assertRaises(KeyboardInterrupt):
                self.preserve()
        self.assertFalse(self.output.exists())
        self.assertEqual(self.identity(self.retained / "llvm")["st_ino"], before["st_ino"])
        with self.assertRaisesRegex(RuntimeError, "incomplete or unexpected"):
            self.preserve()
        self.assert_free()

    def test_rename_failure_keeps_source_and_existing_intent(self):
        before = self.identity(self.output)
        with patch.object(recreate_bootstrap, "_empty_llvm_exclusive_rename",
                          return_value=unittest.mock.Mock(side_effect=PermissionError("refused"))):
            with self.assertRaises(PermissionError):
                self.preserve()
        self.assertEqual(self.identity(self.output), before)
        self.assertTrue((self.retained / "intent.json").is_file())
        self.assertFalse((self.retained / "llvm").exists())
        self.assert_free()

    def test_changed_source_after_intent_refuses_before_rename(self):
        original = recreate_bootstrap._empty_llvm_json
        def changed(directory, name, value=None, **kwargs):
            payload = original(directory, name, value, **kwargs)
            if name == "intent.json" and value is not None:
                (self.output / "late-input").write_bytes(b"must not move")
            return payload
        with patch.object(recreate_bootstrap, "_empty_llvm_json", side_effect=changed):
            with self.assertRaisesRegex(RuntimeError, "changed before preservation"):
                self.preserve()
        self.assertEqual((self.output / "late-input").read_bytes(), b"must not move")
        self.assertFalse((self.retained / "llvm").exists())
        self.assert_free()

    def test_second_empty_directory_never_overwrites_preserved_evidence(self):
        self.preserve()
        kept = self.identity(self.retained / "llvm")
        self.output.mkdir()
        current = self.identity(self.output)
        with self.assertRaisesRegex(RuntimeError, "another empty LLVM"):
            self.preserve()
        self.assertEqual(self.identity(self.output), current)
        self.assertEqual(self.identity(self.retained / "llvm"), kept)
        self.assert_free()

    def test_new_nonempty_output_never_inherits_preservation_as_build_evidence(self):
        self.preserve()
        self.output.mkdir()
        (self.output / "unbound").write_bytes(b"not a watched build")
        self.assertIsNone(self.preserve())
        owner = StageToolProvenanceTests("test_require_llvm_identity_refuses_before_x_py_and_no_other_flag_does")
        observed = owner.observe_llvm(self.root)
        self.assertTrue(observed["output"]["present"])
        self.assertTrue(recreate_bootstrap.llvm_identity_obstacle_rows(observed, host=self.host,
                        config_sha256="b" * 64, native_authority_sha256="c" * 64))
        self.assert_free()

    def test_nonempty_output_after_completed_history_preserves_all_existing_custody_bytes(self):
        self.preserve()
        historical = {str(p.relative_to(self.retained)): (self.identity(p), p.read_bytes() if p.is_file() else None)
                      for p in [self.retained, *self.retained.iterdir()]}
        self.output.mkdir()
        payload = self.output / "genuine-next-build-output"
        payload.write_bytes(b"strict LLVM observer must decide this output")
        before = self.identity(self.output)
        content = (self.identity(payload), payload.read_bytes())
        self.assertIsNone(self.preserve())
        self.assertEqual(self.identity(self.output), before)
        self.assertEqual((self.identity(payload), payload.read_bytes()), content)
        self.assertEqual(historical, {str(p.relative_to(self.retained)): (self.identity(p), p.read_bytes() if p.is_file() else None)
                                     for p in [self.retained, *self.retained.iterdir()]})
        self.assertFalse((self.retained / "refused.json").exists())
        self.assert_free()

    def test_modified_or_foreign_preservation_records_refuse(self):
        self.preserve()
        intent = self.retained / "intent.json"
        data = json.loads(intent.read_text())
        data["original"] = "/foreign/build/test-host/llvm"
        intent.write_text(json.dumps(data))
        with self.assertRaisesRegex(RuntimeError, "foreign or malformed"):
            self.preserve()
        self.assertFalse(self.output.exists())
        self.assertEqual(list((self.retained / "llvm").iterdir()), [])
        self.assert_free()

    def test_changed_preserved_inode_or_additional_container_entries_refuse(self):
        self.preserve()
        (self.retained / "llvm" / "unexpected").write_bytes(b"do not erase")
        with self.assertRaisesRegex(RuntimeError, "inode changed"):
            self.preserve()
        self.assertEqual((self.retained / "llvm" / "unexpected").read_bytes(), b"do not erase")
        (self.retained / "extra").write_bytes(b"retained")
        with self.assertRaisesRegex(RuntimeError, "incomplete or unexpected"):
            self.preserve()
        self.assertEqual((self.retained / "extra").read_bytes(), b"retained")
        self.assert_free()

    def test_destination_created_after_intent_is_not_overwritten(self):
        original = recreate_bootstrap._empty_llvm_json
        existing = {}
        def inserted(directory, name, value=None, **kwargs):
            payload = original(directory, name, value, **kwargs)
            if name == "intent.json" and value is not None:
                destination = self.retained / "llvm"
                destination.mkdir()
                existing.update(self.identity(destination))
            return payload
        before = self.identity(self.output)
        with patch.object(recreate_bootstrap, "_empty_llvm_json", side_effect=inserted):
            with self.assertRaisesRegex(RuntimeError, "destination changed"):
                self.preserve()
        self.assertEqual(self.identity(self.output), before)
        self.assertEqual(self.identity(self.retained / "llvm"), existing)
        self.assert_free()

    def test_destination_inserted_at_actual_rename_boundary_is_never_overwritten(self):
        import ctypes

        real_rename = os.rename
        real_cdll = ctypes.CDLL
        inserted = []
        before = self.identity(self.output)

        def insert():
            destination = self.retained / "llvm"
            destination.mkdir(mode=0o700)
            inserted.append(self.identity(destination))

        def ordinary(*args, **kwargs):
            insert()
            return real_rename(*args, **kwargs)

        def library(*args, **kwargs):
            actual = real_cdll(*args, **kwargs)
            exclusive = actual.renameatx_np

            def boundary(*arguments):
                insert()
                return exclusive(*arguments)

            # The real functions still perform every syscall. Only schedule
            # creation of an owned destination at the last call boundary.
            actual.renameatx_np = boundary
            return actual

        with patch.object(recreate_bootstrap.os, "rename", side_effect=ordinary), \
                patch.object(ctypes, "CDLL", side_effect=library):
            with self.assertRaises(FileExistsError):
                self.preserve()
        self.assertEqual(len(inserted), 1)
        self.assertEqual(self.identity(self.output), before)
        self.assertEqual(self.identity(self.retained / "llvm"), inserted[0])
        self.assertEqual(sorted(p.name for p in self.retained.iterdir()), ["intent.json", "llvm"])
        self.assert_free()

    def real_rename_boundary(self, schedule):
        import ctypes

        real_cdll = ctypes.CDLL

        def library(*args, **kwargs):
            actual = real_cdll(*args, **kwargs)
            exclusive = actual.renameatx_np

            def boundary(*arguments):
                self.assertTrue(os.path.lexists(self.root / ".trust-build-lock"))
                schedule()
                return exclusive(*arguments)

            actual.renameatx_np = boundary
            return actual

        return patch.object(ctypes, "CDLL", side_effect=library)

    def test_container_replacement_at_actual_rename_boundary_refuses_without_completion(self):
        displaced = self.retained.with_name(self.retained.name + ".displaced-owned")
        before = self.identity(self.output)
        replacement = {}

        def swap():
            self.retained.rename(displaced)
            self.retained.mkdir(mode=0o700)
            replacement.update(self.identity(self.retained))

        with self.real_rename_boundary(swap):
            with self.assertRaisesRegex(RuntimeError, "path.*changed"):
                self.preserve()
        self.assertFalse(self.output.exists())
        self.assertEqual(self.identity(displaced / "llvm")["st_ino"], before["st_ino"])
        self.assertEqual(self.identity(self.retained), replacement)
        self.assertFalse((self.retained / "llvm").exists())
        self.assertFalse((displaced / "completed.json").exists())
        self.assertTrue((displaced / "intent.json").is_file())
        self.assert_free()

    def test_host_and_build_replacement_at_real_move_refuse_without_completion(self):
        for level in ("host", "build"):
            with self.subTest(level=level):
                selected = self.output.parent if level == "host" else self.root / "build"
                displaced = selected.with_name(selected.name + ".displaced-owned")
                original_retained = displaced / self.retained.name if level == "host" else displaced / self.host / self.retained.name
                before = self.identity(self.output)
                replacement = {}

                def swap():
                    selected.rename(displaced)
                    selected.mkdir(mode=0o700)
                    replacement.update(self.identity(selected))

                try:
                    with self.real_rename_boundary(swap):
                        with self.assertRaisesRegex(RuntimeError, "path.*changed"):
                            self.preserve()
                    self.assertEqual(self.identity(selected), replacement)
                    self.assertFalse((original_retained / "completed.json").exists())
                    self.assertTrue((original_retained / "intent.json").is_file())
                    self.assertEqual(self.identity(original_retained / "llvm")["st_ino"], before["st_ino"])
                    self.assert_free()
                finally:
                    # Only this owned test fixture is reset between schedules;
                    # the production operation performs no rollback/deletion.
                    shutil.rmtree(selected)
                    displaced.rename(selected)
                    shutil.rmtree(self.retained)
                    self.output.mkdir()

    def test_root_replacement_refuses_and_preserves_primary_error_and_own_lease(self):
        selected = self.root
        displaced = selected.with_name(selected.name + ".displaced-owned")
        self.addCleanup(lambda: shutil.rmtree(displaced) if displaced.exists() else None)
        before = self.identity(self.output)

        def swap():
            selected.rename(displaced)
            selected.mkdir(mode=0o700)

        with self.real_rename_boundary(swap):
            with self.assertRaisesRegex(RuntimeError, "path.*changed") as raised:
                self.preserve()
        self.assertTrue(any("release also failed" in note for note in raised.exception.__notes__))
        moved = displaced / "build" / self.host / self.retained.name
        self.assertEqual(self.identity(moved / "llvm")["st_ino"], before["st_ino"])
        self.assertFalse((moved / "completed.json").exists())
        self.assertEqual(list(selected.iterdir()), [])
        # A replaced checkout spelling cannot release its displaced lease.
        # Retain it on refusal, then explicitly release only this test's exact
        # token at its real owned displaced location before fixture teardown.
        info = displaced / ".trust-build-lock" / "info"
        token = next(row.partition("=")[2] for row in info.read_text().splitlines() if row.startswith("token="))
        self.root = displaced
        try:
            self.lock("release", token)
            self.assert_free()
        finally:
            self.root = selected

    def test_sanctioned_alias_replacement_at_move_cannot_redirect_custody(self):
        build = self.root / "build"
        noindex = self.root / recreate_bootstrap.BUILD_NOINDEX
        build.rename(noindex)
        build.symlink_to(recreate_bootstrap.BUILD_NOINDEX, target_is_directory=True)
        displaced_link = self.root / "build.displaced-link"
        destination = noindex / self.host / self.retained.name

        def swap():
            build.rename(displaced_link)
            build.mkdir(mode=0o700)

        with self.real_rename_boundary(swap):
            with self.assertRaisesRegex(RuntimeError, "path.*changed"):
                self.preserve()
        self.assertFalse((destination / "completed.json").exists())
        self.assertTrue((destination / "llvm").is_dir())
        self.assertEqual(list(build.iterdir()), [])
        self.assertEqual(os.readlink(displaced_link), recreate_bootstrap.BUILD_NOINDEX)
        self.assert_free()

    def test_container_swap_at_completion_entry_cannot_write_a_completion(self):
        original = recreate_bootstrap._empty_llvm_json
        displaced = self.retained.with_name(self.retained.name + ".displaced-owned")

        def swap(directory, name, value=None, **kwargs):
            if name == "completed.json" and value is not None:
                self.retained.rename(displaced)
                self.retained.mkdir(mode=0o700)
            return original(directory, name, value, **kwargs)

        with patch.object(recreate_bootstrap, "_empty_llvm_json", side_effect=swap):
            with self.assertRaisesRegex(RuntimeError, "path.*changed"):
                self.preserve()
        self.assertFalse((displaced / "completed.json").exists())
        self.assertTrue((displaced / "intent.json").is_file())
        self.assertTrue((displaced / "llvm").is_dir())
        self.assertEqual(list(self.retained.iterdir()), [])
        self.assert_free()

    def test_container_swap_after_record_write_marks_refusal_and_retry_cannot_accept_it(self):
        original = recreate_bootstrap._empty_llvm_json
        displaced = self.retained.with_name(self.retained.name + ".displaced-owned")

        def swap(directory, name, value=None, **kwargs):
            payload = original(directory, name, value, **kwargs)
            if name == "completed.json" and value is not None:
                self.retained.rename(displaced)
                self.retained.mkdir(mode=0o700)
            return payload

        with patch.object(recreate_bootstrap, "_empty_llvm_json", side_effect=swap):
            with self.assertRaisesRegex(RuntimeError, "path.*changed"):
                self.preserve()
        self.assertEqual(sorted(p.name for p in displaced.iterdir()),
                         ["completed.json", "intent.json", "llvm", "refused.json"])
        refusal = json.loads((displaced / "refused.json").read_text())
        self.assertEqual(refusal["schema"], "trust.empty-llvm-preservation-refused.v1")
        # Even restoring this owned test spelling cannot adopt a completion
        # whose final custody checks refused. Production never restores it.
        self.retained.rmdir()
        displaced.rename(self.retained)
        with self.assertRaisesRegex(RuntimeError, "incomplete or unexpected"):
            self.preserve()
        self.assert_free()

    def test_retry_container_swap_during_record_read_refuses(self):
        self.preserve()
        original = recreate_bootstrap._empty_llvm_json
        displaced = self.retained.with_name(self.retained.name + ".displaced-owned")

        def swap(directory, name, value=None, **kwargs):
            payload = original(directory, name, value, **kwargs)
            if name == "intent.json" and value is None:
                self.retained.rename(displaced)
                self.retained.mkdir(mode=0o700)
            return payload

        with patch.object(recreate_bootstrap, "_empty_llvm_json", side_effect=swap):
            with self.assertRaisesRegex(RuntimeError, "path.*changed"):
                self.preserve()
        self.assertTrue((displaced / "completed.json").is_file())
        self.assertEqual(list(self.retained.iterdir()), [])
        self.assert_free()

    def test_container_swap_at_real_lease_release_boundary_refuses_success(self):
        real_run = subprocess.run
        displaced = self.retained.with_name(self.retained.name + ".displaced-owned")

        def swap(argv, **kwargs):
            result = real_run(argv, **kwargs)
            if argv[4] == "release":
                self.assertEqual(result.returncode, 0)
                self.retained.rename(displaced)
                self.retained.mkdir(mode=0o700)
            return result

        with patch.object(recreate_bootstrap.subprocess, "run", side_effect=swap):
            with self.assertRaisesRegex(RuntimeError, "path.*changed"):
                self.preserve()
        self.assertTrue((displaced / "llvm").is_dir())
        self.assertTrue((displaced / "refused.json").is_file())
        self.assertEqual(list(self.retained.iterdir()), [])
        self.assert_free()

    def test_unsupported_exclusive_rename_refuses_before_preservation_state(self):
        import ctypes

        before = self.identity(self.output)
        with patch.object(recreate_bootstrap.sys, "platform", "unsupported"):
            with self.assertRaisesRegex(RuntimeError, "atomic exclusive rename"):
                self.preserve()
        self.assertEqual(self.identity(self.output), before)
        self.assertFalse(self.retained.exists())
        for failure in (AttributeError("missing API"), OSError("unavailable library")):
            with self.subTest(failure=failure), patch.object(ctypes, "CDLL", side_effect=failure):
                with self.assertRaisesRegex(RuntimeError, "atomic exclusive rename APIs"):
                    self.preserve()
            self.assertEqual(self.identity(self.output), before)
            self.assertFalse(self.retained.exists())
        self.assert_free()

    def test_volume_capability_refusal_precedes_any_preservation_mutation(self):
        import ctypes
        import errno

        actual_cdll = ctypes.CDLL
        before = self.identity(self.output)
        for failure in ("unsupported", "invalid", "truncated", "query-error"):
            def library(*args, **kwargs):
                actual = actual_cdll(*args, **kwargs)
                query = actual.fgetattrlist

                def attributes(*arguments):
                    result = query(*arguments)
                    self.assertEqual(result, 0)
                    values = ctypes.cast(arguments[2], ctypes.POINTER(ctypes.c_uint32))
                    if failure == "query-error":
                        ctypes.set_errno(errno.ENOTSUP)
                        return -1
                    if failure == "unsupported":
                        values[2] &= ~0x00080000
                    elif failure == "invalid":
                        values[6] &= ~0x00080000
                    else:
                        values[0] -= 4
                    return result

                actual.fgetattrlist = attributes
                return actual

            with self.subTest(failure=failure), patch.object(ctypes, "CDLL", side_effect=library):
                with self.assertRaises((RuntimeError, OSError)):
                    self.preserve()
            self.assertEqual(self.identity(self.output), before)
            self.assertFalse(self.retained.exists())
        self.assert_free()

    def test_unsafe_host_and_relative_checkout_cannot_move_output(self):
        before = self.identity(self.output)
        for host in ("../escape", "/absolute", "", ".", ".."):
            with self.subTest(host=host), self.assertRaisesRegex(RuntimeError, "unsafe host"):
                recreate_bootstrap.preserve_empty_llvm_for_fresh_seed(self.root, host, None, self.config)
        with self.assertRaisesRegex(RuntimeError, "absolute owned checkout"):
            recreate_bootstrap.preserve_empty_llvm_for_fresh_seed(Path("."), self.host, None, self.config)
        self.assertEqual(self.identity(self.output), before)
        self.assertFalse(self.retained.exists())

    def test_changed_parent_after_lock_acquisition_refuses_before_preservation(self):
        real_run = subprocess.run
        old_parent = self.output.parent.with_name("old-parent")
        before = self.identity(self.output)
        def changed(argv, **kwargs):
            result = real_run(argv, **kwargs)
            if argv[4] == "acquire":
                self.output.parent.rename(old_parent)
                self.output.parent.mkdir()
            return result
        with patch.object(recreate_bootstrap.subprocess, "run", side_effect=changed):
            with self.assertRaisesRegex(RuntimeError, "parent changed"):
                self.preserve()
        self.assertEqual(self.identity(old_parent / "llvm"), before)
        self.assertFalse(self.retained.exists())
        self.assert_free()

    def test_release_refusal_cannot_turn_completed_preservation_into_success(self):
        real_run = subprocess.run
        release_token = []
        def refused(argv, **kwargs):
            if argv[4] == "release":
                release_token.append(argv[5])
                return subprocess.CompletedProcess(argv, 4, "", "forced release refusal")
            return real_run(argv, **kwargs)
        try:
            with patch.object(recreate_bootstrap.subprocess, "run", side_effect=refused):
                with self.assertRaisesRegex(RuntimeError, "lease release refused"):
                    self.preserve()
            self.assertFalse(self.output.exists())
            self.assertTrue((self.retained / "completed.json").is_file())
        finally:
            if release_token:
                self.lock("release", release_token[0])
        self.assert_free()

    def test_cancellation_remains_primary_when_release_also_refuses(self):
        real_run = subprocess.run
        release_token = []
        def refused(argv, **kwargs):
            if argv[4] == "release":
                release_token.append(argv[5])
                return subprocess.CompletedProcess(argv, 4, "", "forced release refusal")
            return real_run(argv, **kwargs)
        try:
            with patch.object(recreate_bootstrap.subprocess, "run", side_effect=refused), \
                    patch.object(recreate_bootstrap, "_empty_llvm_json", side_effect=KeyboardInterrupt):
                with self.assertRaises(KeyboardInterrupt) as raised:
                    self.preserve()
            self.assertTrue(any("release also failed" in note for note in raised.exception.__notes__))
            self.assertTrue(self.output.is_dir())
        finally:
            if release_token:
                self.lock("release", release_token[0])
        self.assert_free()

    def test_main_preservation_failure_reports_retained_path_and_cannot_start_build(self):
        owner = StageToolProvenanceTests("test_require_llvm_identity_refuses_before_x_py_and_no_other_flag_does")
        failure = RuntimeError("recovery refused")
        failure.add_note("Preserve all recovery state at /owned/retained-empty-llvm")
        with patch.object(recreate_bootstrap, "preserve_empty_llvm_for_fresh_seed", side_effect=failure):
            status, _, printed, mocks = owner.main_around_llvm(owner.SEAL_INVOCATION, owner.llvm_observation())
        self.assertEqual(status, 1)
        self.assertIn("Preserve all recovery state at /owned/retained-empty-llvm", printed)
        mocks["recover_seed_stage0_quarantine"].assert_called_once()
        for name in ("capture_llvm_before_build", "run_xpy_build", "audit_stage_tool_provenance"):
            mocks[name].assert_not_called()

    def test_parent_durability_failure_happens_before_original_inode_moves(self):
        real_fsync = os.fsync
        parent = self.identity(self.output.parent)
        before = self.identity(self.output)
        def refused(descriptor):
            metadata = os.fstat(descriptor)
            if (metadata.st_dev, metadata.st_ino) == (parent["st_dev"], parent["st_ino"]):
                raise OSError("parent durability unavailable")
            return real_fsync(descriptor)
        with patch.object(recreate_bootstrap.os, "fsync", side_effect=refused):
            with self.assertRaisesRegex(OSError, "parent durability unavailable"):
                self.preserve()
        self.assertTrue(self.output.is_dir())
        self.assertEqual(self.identity(self.output), before)
        self.assertFalse((self.retained / "llvm").exists())
        self.assertTrue((self.retained / "intent.json").is_file())
        self.assert_free()

    def test_main_calls_recovery_only_for_strict_fresh_seed_builds(self):
        owner = StageToolProvenanceTests("test_require_llvm_identity_refuses_before_x_py_and_no_other_flag_does")
        for argv, expected in ((owner.SEAL_INVOCATION, True), (owner.SEED_INVOCATION, False),
                               (["--stage", "2", "--require-seed", "--require-llvm-identity"], False),
                               (["--check", *owner.SEED_INVOCATION], False),
                               (["--no-build", "--require-seed"], False)):
            with self.subTest(argv=argv), patch.object(recreate_bootstrap, "preserve_empty_llvm_for_fresh_seed") as preserve:
                status, _, _, _ = owner.main_around_llvm(argv, owner.llvm_observation())
                self.assertEqual(status, 0)
                self.assertEqual(preserve.call_count, int(expected))


class Stage0IdentitySourceLoaderTests(unittest.TestCase):
    def test_timestamp_valid_stale_pyc_cannot_replace_bound_identity_source(self):
        import py_compile
        import runpy
        with tempfile.TemporaryDirectory() as directory, patch.object(sys, "pycache_prefix", None):
            root = Path(directory)
            script = root / "scripts/recreate_bootstrap.py"
            script.parent.mkdir()
            shutil.copyfile(SCRIPT, script)
            identity = root / "src/bootstrap/stage0_identity.py"
            identity.parent.mkdir(parents=True)
            good = b'def extraction_stamp(*args): return "actual source owner"\n'
            stale = b'raise RuntimeError("unbound cached identity executed")\n'
            length = max(len(good), len(stale))
            good, stale = good.ljust(length, b" "), stale.ljust(length, b" ")
            identity.write_bytes(stale)
            stamp = identity.stat().st_mtime_ns
            cached = Path(py_compile.compile(str(identity), doraise=True))
            cached_before = cached.read_bytes()
            identity.write_bytes(good)
            os.utime(identity, ns=(stamp, stamp))
            bound_before = identity.read_bytes()
            loaded = runpy.run_path(str(script), run_name="identity_source_loader_control")
            self.assertEqual(loaded["stage0_extraction_stamp"](), "actual source owner")
            self.assertEqual(identity.read_bytes(), bound_before)
            self.assertEqual(cached.read_bytes(), cached_before)
            self.assertTrue(cached.is_file())


class AghSourceTransportTests(unittest.TestCase):
    """Real local Git objects behind a substituted Agh executor; no network."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.server = self.root / "server"
        self.server.mkdir()
        self.git(self.server, "init", "--quiet", "--template=", "--initial-branch=main")
        self.git(self.server, "config", "user.name", "source-test")
        self.git(self.server, "config", "user.email", "source@test.invalid")
        (self.server / "source").write_text("first")
        self.git(self.server, "add", "source")
        self.git(self.server, "commit", "--quiet", "-m", "first")
        self.first = self.git(self.server, "rev-parse", "HEAD")
        (self.server / "source").write_text("second")
        self.git(self.server, "commit", "--quiet", "-am", "second")
        self.second = self.git(self.server, "rev-parse", "HEAD")
        self.destination = self.root / "objects.git"
        self.git(self.root, "init", "--bare", "--quiet", "--template=", str(self.destination))
        self.agh = self.root / "agh"
        self.agh.write_text("#!/bin/sh\nexit 0\n")
        self.agh.chmod(0o700)
        self.calls = []
        self.ref = "refs/agh/source-test"

    def git(self, cwd, *args):
        return subprocess.check_output(
            ["git", "-c", "protocol.file.allow=always", "-C", str(cwd), *args],
            env=recreate_bootstrap._provenance_git_environment(),
            stderr=subprocess.DEVNULL, text=True,
        ).strip()

    def acquire(self, argv, environment):
        self.calls.append((argv, environment))
        self.assertEqual(argv[:4], [str(self.agh), "repo", "fetch", "fixture/source"])
        self.assertEqual(argv[4], str(self.destination))
        self.git(self.destination, "fetch", "--quiet", "--no-tags", str(self.server),
                 argv[6] + ":" + argv[8])

    def fetch(self, source=None, *, url="https://github.com/fixture/source.git", private_ref=None,
              execute=None, checkout_cache=None, **options):
        with patch.object(recreate_bootstrap, "which", return_value=str(self.agh)):
            return recreate_bootstrap._agh_source_fetch(
                url, self.destination, source or self.second, private_ref or self.ref,
                execute=execute or self.acquire, checkout_cache=checkout_cache, **options,
            )

    def scratch_agh(self, steps: int, *, then_sleep: bool = False) -> Path:
        """An Agh stand-in that writes its transfer under TMPDIR, as agh 0.206.0 does, and moves
        the commit into the destination only afterwards. With no TMPDIR it writes elsewhere,
        where agh 0.206.0 wrote when the recreator gave it none: the system temporary folder."""
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir(exist_ok=True)
        body = self.root / "scratch-agh.py"
        body.write_text(
            "import os, subprocess, sys, time\n"
            f"scratch = os.environ.get('TMPDIR') or {str(elsewhere)!r}\n"
            "work = os.path.join(scratch, '.ubd', 'agh-git-fixture.noindex', 'scratch.git')\n"
            "os.makedirs(work, exist_ok=True)\n"
            "with open(os.path.join(work, 'tmp_pack'), 'wb') as pack:\n"
            f"    for _ in range({steps}):\n"
            "        pack.write(b'x' * 4096)\n"
            "        pack.flush()\n"
            "        time.sleep(0.1)\n"
            + ("time.sleep(600)\n" if then_sleep else "")
            + f"subprocess.run([{shutil.which('git')!r}, '-c', 'protocol.file.allow=always', '-C', sys.argv[4],\n"
            f"                'fetch', '--quiet', '--no-tags', {str(self.server)!r}, sys.argv[6] + ':' + sys.argv[8]],\n"
            "               check=True)\n")
        agh = self.root / "scratch-agh"
        agh.write_text(f"#!/bin/sh\nexec {shlex.quote(sys.executable)} -I {shlex.quote(str(body))} \"$@\"\n")
        agh.chmod(0o700)
        return agh

    def scratch_fetch(self, agh: Path, parent: Path) -> tuple[list, object]:
        """_agh_source_fetch through the real process owner, under a one-second stall window."""
        bounds = []
        real = recreate_bootstrap._SubmoduleProgress

        def bound(label, paths):
            bounds.append(real(label, paths, window=1.0))
            return bounds[-1]
        with patch.object(recreate_bootstrap, "which", return_value=str(agh)), \
                patch.object(recreate_bootstrap, "_SubmoduleProgress", bound), \
                patch.object(sys, "stderr", io.StringIO()):
            try:
                return bounds, recreate_bootstrap._agh_source_fetch(
                    "https://github.com/fixture/source.git", self.destination, self.second, self.ref,
                    scratch_parent=parent)
            except BaseException as error:
                return bounds, error

    def test_agh_writing_only_in_its_scratch_is_watched_there_and_its_scratch_removed(self):
        # agh 0.206.0 does a checkout closure's whole download in its own scratch under TMPDIR
        # and moves it into the destination when it is complete. Watching the destination alone,
        # the bound ended alabsystems/clean's fetch three times on 2026-11-16 and 2026-11-17
        # while it received 12.5 MB/s: "0.0 bytes/s over its last 600 s".
        parent = self.root / "scratch-parent"
        parent.mkdir()
        bounds, record = self.scratch_fetch(self.scratch_agh(40), parent)  # four windows of steady writes
        self.assertIsInstance(record, dict, record)
        self.assertEqual(record["commit"], self.second)
        [bound] = bounds
        self.assertEqual(bound.paths[0], self.destination)
        self.assertEqual(bound.paths[1].parent, parent.resolve())
        self.assertGreaterEqual(bound.received, 30 * 4096)
        # A transfer that completed leaves no scratch, and nothing is left elsewhere.
        self.assertEqual(list(parent.iterdir()), [])
        self.assertEqual(list((self.root / "elsewhere").iterdir()), [])
        self.assertEqual(self.git(self.destination, "rev-parse", self.ref), self.second)

    def test_an_agh_ended_for_too_little_progress_keeps_its_scratch_in_its_callers_folder(self):
        parent = self.root / "scratch-parent"
        parent.mkdir()
        bounds, error = self.scratch_fetch(self.scratch_agh(1, then_sleep=True), parent)
        self.assertIsInstance(error, recreate_bootstrap._SubmoduleStalled)
        self.assertRegex(str(error), r"^Agh's fetch of fixture/source showed too little progress: 4096 bytes observed")
        # What it wrote is kept, in the folder its caller reclaims, not the system temporary
        # directory, where ended Aghs had left 556 scratch directories, 30.7 GB, by 2026-11-17.
        [scratch] = parent.iterdir()
        self.assertEqual(bounds[0].paths, (self.destination, scratch.resolve()))
        self.assertEqual((scratch / ".ubd/agh-git-fixture.noindex/scratch.git/tmp_pack").stat().st_size, 4096)
        self.assertEqual(list((self.root / "elsewhere").iterdir()), [])
        self.assertEqual(self.git(self.destination, "for-each-ref"), "")

    def test_an_injected_executor_makes_its_own_transfer_directory(self):
        with self.assertRaisesRegex(RuntimeError, "makes its own transfer directory"):
            self.fetch(execute=lambda *_: self.fail("Agh started"), scratch_parent=self.root)
    def test_private_transfer_growth_counts_and_unrelated_growth_still_stalls(self):
        observed = []
        def transport(argv, *, environment, progress, **kwargs):
            scratch = Path(environment["TMPDIR"]).resolve()
            observed.append(scratch)
            self.assertEqual(progress.paths, (self.destination, scratch))
            if os.name != "nt":
                self.assertEqual(scratch.stat().st_mode & 0o777, 0o700)
            now = [0.0]
            progress._clock = lambda: now[0]
            progress.begin()
            # Only Agh's private pack grows. Its destination and output remain still.
            (scratch / "incoming.pack").write_bytes(b"x" * 12000)
            now[0] += progress.window
            progress.check(argv)
            self.assertEqual(progress.received, 12000)
            # A sibling outside both owned paths cannot keep a stalled transfer alive.
            (self.root / "unrelated.pack").write_bytes(b"y" * 12000)
            now[0] += progress.window
            with self.assertRaises(recreate_bootstrap._SubmoduleStalled):
                progress.check(argv)
            self.acquire(argv, environment)
            return subprocess.CompletedProcess(argv, 0)
        with patch.object(recreate_bootstrap, "which", return_value=str(self.agh)), \
             patch.object(recreate_bootstrap, "_run_submodule_update_process", side_effect=transport):
            record = recreate_bootstrap._agh_source_fetch(
                "https://github.com/fixture/source.git", self.destination, self.second, self.ref)
        self.assertEqual(record["commit"], self.second)
        self.assertFalse(observed[0].exists())

    def test_failed_transfer_keeps_its_private_files_and_counts_nested_destination_once(self):
        observed = []
        def interrupted(argv, *, environment, progress, **kwargs):
            scratch = Path(environment["TMPDIR"])
            observed.append(scratch)
            self.assertEqual(progress.paths, (self.destination,))
            (scratch / "incoming.pack").write_bytes(b"unfinished")
            return subprocess.CompletedProcess(argv, -9)

        with patch.object(tempfile, "tempdir", str(self.destination)), \
             patch.object(recreate_bootstrap, "which", return_value=str(self.agh)), \
             patch.object(recreate_bootstrap, "_run_submodule_update_process", side_effect=interrupted), \
             patch("sys.stderr", new_callable=io.StringIO) as diagnostics:
            with self.assertRaisesRegex(RuntimeError, "exit -9"):
                recreate_bootstrap._agh_source_fetch(
                    "https://github.com/fixture/source.git", self.destination, self.second, self.ref)
        self.assertEqual((observed[0] / "incoming.pack").read_bytes(), b"unfinished")
        self.assertIn(str(observed[0]), diagnostics.getvalue())

    def test_checkout_cache_keeps_exact_source_and_private_destination(self):
        record = self.fetch(checkout_cache=self.server)
        self.assertEqual(record["commit"], self.second)
        argv, _ = self.calls[0]
        self.assertEqual(argv[5:], ["--ref", self.second, "--into", self.ref,
                                   "--checkout-closure", "--checkout-cache", str(self.server)])
        with self.assertRaisesRegex(RuntimeError, "exact immutable source commit"):
            self.fetch("refs/heads/main", checkout_cache=self.server)
        self.assertEqual(len(self.calls), 1)

    def test_exact_owner_routing_preserves_lexical_client_and_reads_the_ref(self):
        target = self.root / "multicall-program"
        self.agh.rename(target)
        self.agh.symlink_to(target)
        with patch.dict(os.environ, {"GH_TOKEN": "FIXTURE_NOT_A_SECRET", "GITHUB_TOKEN": "FIXTURE_NOT_A_SECRET"}):
            record = self.fetch()
        self.assertEqual(record["commit"], self.second)
        self.assertEqual(record["program"]["executable"], str(self.agh))
        self.assertEqual(record["program"]["resolved"], str(target))
        self.assertEqual(len(self.calls), 1)
        argv, env = self.calls[0]
        self.assertEqual(argv[5:], ["--ref", self.second, "--into", self.ref,
                                   "--checkout-closure"])
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(env["GIT_TERMINAL_PROMPT"], "0")
        self.assertNotIn("GH_TOKEN", env)
        self.assertNotIn("GITHUB_TOKEN", env)

    def test_full_branch_and_optional_dot_git_url_resolve_through_same_owner(self):
        record = self.fetch("refs/heads/main", url="https://github.com/fixture/source")
        self.assertEqual(record["repository"], "fixture/source")
        self.assertEqual(record["commit"], self.second)
        self.assertEqual(self.calls[0][0][5:],
                         ["--ref", "refs/heads/main", "--into", self.ref])

    def test_wrong_immutable_revision_refuses_even_after_successful_transport(self):
        def wrong(argv, env):
            self.git(self.destination, "fetch", "--quiet", "--no-tags", str(self.server),
                     self.first + ":" + argv[8])
        with self.assertRaisesRegex(RuntimeError, "differs from the requested immutable"):
            self.fetch(execute=wrong)

    def test_missing_agh_does_not_select_gh_or_a_git_fallback(self):
        selected = []
        def absent(name):
            selected.append(name)
            return None
        with patch.object(recreate_bootstrap, "which", side_effect=absent):
            with self.assertRaisesRegex(RuntimeError, "owner-routed Agh is required"):
                recreate_bootstrap._agh_source_fetch(
                    "https://github.com/fixture/source.git", self.destination,
                    self.second, self.ref, execute=self.acquire,
                )
        self.assertEqual(selected, ["agh"])
        self.assertEqual(self.calls, [])

    def test_refused_agh_has_no_fallback_and_does_not_create_a_commit_ref(self):
        def refusal(_argv, _env):
            raise RuntimeError("fixture Agh operation refused")
        with self.assertRaisesRegex(RuntimeError, "fixture Agh operation refused"):
            self.fetch(execute=refusal)
        self.assertEqual(self.git(self.destination, "for-each-ref"), "")

    def test_failed_executor_refuses_even_when_the_exact_ref_exists(self):
        def failed(argv, env):
            self.acquire(argv, env)
            return subprocess.CompletedProcess(argv, 19)

        with self.assertRaisesRegex(RuntimeError, r"owner-routed Agh source fetch failed \(exit 19\)"):
            self.fetch(execute=failed)
        self.assertEqual(self.git(self.destination, "rev-parse", self.ref), self.second)

    def test_changed_client_refuses_before_any_selected_commit_is_used(self):
        def change(argv, env):
            self.acquire(argv, env)
            self.agh.write_text("#!/bin/sh\nexit 1\n")
        with self.assertRaisesRegex(RuntimeError, "transport changed during acquisition"):
            self.fetch(execute=change)

    def test_untrusted_url_and_ref_grammar_refuse_before_client_selection(self):
        for url in [
            "https://github.com.evil/fixture/source.git",
            "https://user:FIXTURE@github.com/fixture/source.git",
            "https://github.com/fixture/source.git?access_token=FIXTURE",
            "https://github.com/fixture/source.git#FIXTURE",
            "https://github.com/../source.git",
        ]:
            with self.subTest(url=url), patch.object(recreate_bootstrap, "which") as which:
                with self.assertRaises(RuntimeError):
                    recreate_bootstrap._agh_source_fetch(url, self.destination, self.second, self.ref, execute=self.acquire)
                which.assert_not_called()
        for ref in ["refs/heads/main", "refs/agh/.hidden", "refs/agh/../main", "refs/agh/name.lock"]:
            with self.subTest(ref=ref), patch.object(recreate_bootstrap, "which") as which:
                with self.assertRaises(RuntimeError):
                    recreate_bootstrap._agh_source_fetch(
                        "https://github.com/fixture/source.git", self.destination,
                        self.second, ref, execute=self.acquire,
                    )
                which.assert_not_called()
        self.assertEqual(self.calls, [])

    def test_checkout_closure_refuses_a_mutable_source_before_transport(self):
        with patch.object(recreate_bootstrap, "which", return_value=str(self.agh)):
            with self.assertRaisesRegex(RuntimeError, "exact immutable source commit"):
                recreate_bootstrap._agh_source_fetch(
                    "https://github.com/fixture/source.git", self.destination,
                    "refs/heads/main", self.ref, execute=self.acquire,
                    checkout_closure=True,
                )
        self.assertEqual(self.calls, [])
        self.assertEqual(self.git(self.destination, "for-each-ref"), "")

    def test_pin_repair_dispatch_requires_local_root_after_successful_provider(self):
        self.fetch()
        tree = self.git(self.destination, "rev-parse", self.second + "^{tree}")
        tree_path = self.destination / "objects" / tree[:2] / tree[2:]
        original_tree = tree_path.read_bytes()
        tree_path.unlink()
        private_ref = "refs/agh/trust-source-pins/" + self.second
        arguments = ["fetch-source-pin", "--url", "https://github.com/fixture/source.git",
                     "--directory", str(self.destination), "--pin", self.second]
        calls = []

        def provider(command, **kwargs):
            # Only transfer is substituted; both the independent private-ref
            # and no-lazy-fetch root-tree checks use genuine local Git objects.
            calls.append((command, kwargs))
            self.git(self.destination, "update-ref", private_ref, self.second)
            return subprocess.CompletedProcess(command, 0)

        with patch.object(recreate_bootstrap, "which", return_value=str(self.agh)), \
                patch.object(recreate_bootstrap, "_run_submodule_update_process", side_effect=provider), \
                patch.object(recreate_bootstrap, "host_triple", side_effect=AssertionError("bootstrap setup")), \
                patch("sys.stderr", new_callable=io.StringIO) as errors:
            self.assertEqual(recreate_bootstrap.main(arguments), 2)
            self.assertIn("root tree is not locally readable", errors.getvalue())
            self.assertFalse(tree_path.exists())
            tree_path.write_bytes(original_tree)
            self.assertEqual(recreate_bootstrap.main(arguments), 0)
        self.assertEqual(len(calls), 2)
        for command, kwargs in calls:
            self.assertEqual(command[5:], ["--ref", self.second, "--into", private_ref,
                                           "--checkout-closure"])
            # No total: the repair's fetch ends only for lack of progress in the checkout it fills.
            self.assertIsNone(kwargs["timeout_seconds"])
            private = Path(kwargs["environment"]["TMPDIR"]).resolve()
            self.assertEqual(kwargs["progress"].paths, (Path(command[4]), private))
            self.assertFalse(private.exists())
            self.assertEqual((kwargs["progress"].window, kwargs["progress"].floor),
                             (recreate_bootstrap.SUBMODULE_STALL_WINDOW_SECONDS,
                              recreate_bootstrap.SUBMODULE_FLOOR_BYTES_PER_SECOND))
            self.assertIsNone(kwargs["credential_gh"])

    def test_native_exact_pin_fetch_asks_agh_for_no_filtered_closure(self):
        # A store other checkouts read must not receive the blob-filtered
        # selected-checkout closure (scripts/submodule_sync.sh, shared store).
        private_ref = "refs/agh/trust-source-pins/" + self.second
        calls = []

        def provider(command, **kwargs):
            calls.append(command)
            self.git(self.destination, "fetch", "--quiet", "--no-tags", str(self.server),
                     self.second + ":" + private_ref)
            return subprocess.CompletedProcess(command, 0)

        with patch.object(recreate_bootstrap, "which", return_value=str(self.agh)), \
                patch.object(recreate_bootstrap, "_run_submodule_update_process", side_effect=provider):
            self.assertEqual(recreate_bootstrap.fetch_source_pin_main([
                "--url", "https://github.com/fixture/source.git", "--directory", str(self.destination),
                "--pin", self.second, "--native-exact",
            ]), 0)
        self.assertEqual([command[5:] for command in calls],
                         [["--ref", self.second, "--into", private_ref]])
        with patch.object(recreate_bootstrap, "which", return_value=str(self.agh)):
            with self.assertRaisesRegex(RuntimeError, "native exact fetch takes no checkout closure"):
                recreate_bootstrap._agh_source_fetch(
                    "https://github.com/fixture/source.git", self.destination, self.second,
                    self.ref, execute=self.acquire, checkout_closure=True, native_exact=True,
                )
        self.assertEqual(self.calls, [])

    def test_pin_repair_preserves_a_conflicting_existing_private_ref(self):
        self.fetch()
        private_ref = "refs/agh/trust-source-pins/" + self.second
        self.git(self.destination, "update-ref", private_ref, self.first)
        with patch.object(recreate_bootstrap, "_agh_source_fetch") as fetch, \
                patch("sys.stderr", new_callable=io.StringIO) as errors:
            result = recreate_bootstrap.fetch_source_pin_main([
                "--url", "https://github.com/fixture/source.git", "--directory", str(self.destination),
                "--pin", self.second,
            ])
        self.assertEqual(result, 2)
        self.assertIn("names another commit", errors.getvalue())
        fetch.assert_not_called()
        self.assertEqual(self.git(self.destination, "rev-parse", private_ref), self.first)


class SeedCheckerPlatformDispatchTests(unittest.TestCase):
    def test_windows_preserves_checker_options_without_posix_owner(self):
        transport = recreate_bootstrap._seed_transport()
        for capture, text in ((False, True), (True, False), (True, True)):
            result = subprocess.CompletedProcess(["checker"], 0, stdout=b"observed")
            env = {"CHECKER_METADATA": "only"}
            with self.subTest(capture=capture, text=text), \
                    patch.object(recreate_bootstrap.sys, "platform", "win32"), \
                    patch.object(transport.landing_targo, "resource_fds", return_value=()), \
                    patch.object(transport, "run_custodied_command", side_effect=AssertionError("POSIX owner")), \
                    patch.object(recreate_bootstrap.subprocess, "run", return_value=result) as run:
                actual = recreate_bootstrap._run_seed_checker(
                    ["checker"], env=env, cwd="selected", capture_output=capture, text=text)
                self.assertIs(actual, result)
                run.assert_called_once_with(["checker"], env=env, cwd="selected",
                                            capture_output=capture, text=text)

    def test_windows_refuses_advertised_descriptors_before_launch(self):
        transport = recreate_bootstrap._seed_transport()
        with patch.object(recreate_bootstrap.sys, "platform", "win32"), \
                patch.object(transport.landing_targo, "resource_fds", return_value=(7,)), \
                patch.object(recreate_bootstrap.subprocess, "run", side_effect=AssertionError("lost custody")):
            with self.assertRaisesRegex(RuntimeError, "cannot inherit"):
                recreate_bootstrap._run_seed_checker(["checker"], env={}, cwd="selected")

    def test_posix_admission_failure_never_falls_back_to_direct_launch(self):
        transport = recreate_bootstrap._seed_transport()
        with patch.object(recreate_bootstrap.sys, "platform", "linux"), \
                patch.object(transport, "run_custodied_command", side_effect=RuntimeError("unavailable")), \
                patch.object(recreate_bootstrap.subprocess, "run", side_effect=AssertionError("fallback")):
            with self.assertRaisesRegex(RuntimeError, "unavailable"):
                recreate_bootstrap._run_seed_checker(["checker"], env={}, cwd="selected")

    def test_direct_checker_capture_keeps_real_local_bytes(self):
        # Simulated routing on this host, not Windows runtime qualification.
        with tempfile.TemporaryDirectory() as scratch, \
                patch.object(recreate_bootstrap.sys, "platform", "win32"):
            for text in (False, True):
                result = recreate_bootstrap._run_seed_checker(
                    [sys.executable, "-B", "-c", "import sys;sys.stdout.buffer.write(bytes([206,187,10]))"],
                    env={}, cwd=scratch, text=text)
                self.assertEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "λ\n" if text else "λ\n".encode())



class ConfigurationOnlySourcePreparation(unittest.TestCase):
    def test_ordinary_no_build_preserves_full_first_party_preparation(self):
        root = Path("/owned/source")
        with patch.object(recreate_bootstrap, "ensure_submodules") as materialize:
            recreate_bootstrap.prepare_first_party_sources(root, no_build=True)
        materialize.assert_called_once_with(root)

    def test_full_preparation_retires_only_its_old_deferred_scope(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            marker = root / "build/tool-source-preparation/targo-build-tool.json"
            marker.parent.mkdir(parents=True)
            marker.write_text("old deferred control")
            with patch.object(recreate_bootstrap, "ensure_submodules", side_effect=RuntimeError("missing source")):
                with self.assertRaises(RuntimeError):
                    recreate_bootstrap.prepare_first_party_sources(root, no_build=True)
            self.assertEqual(marker.read_text(), "old deferred control")
            with patch.object(recreate_bootstrap, "ensure_submodules"):
                recreate_bootstrap.prepare_first_party_sources(root, no_build=True)
            self.assertFalse(marker.exists())

    def test_explicit_tool_scope_requires_graph_inspection(self):
        root = Path("/owned/source")
        inspector = Path("/selected/targo")
        with patch.object(recreate_bootstrap, "ensure_submodules") as materialize, \
                patch.object(recreate_bootstrap, "inspect_tool_source_graph") as graph:
            recreate_bootstrap.prepare_first_party_sources(root, no_build=True,
                tool="targo-build-tool", inspector=inspector)
        materialize.assert_not_called()
        graph.assert_called_once_with(root, "targo-build-tool", inspector)

    def test_actual_build_cannot_use_tool_only_deferral(self):
        with self.assertRaises(RuntimeError):
            recreate_bootstrap.prepare_first_party_sources(Path("/owned/source"), no_build=False,
                tool="targo-build-tool", inspector=Path("/selected/targo"))

    def test_real_build_retains_full_first_party_materialization(self):
        root = Path("/owned/source")
        with patch.object(recreate_bootstrap, "ensure_submodules") as materialize:
            recreate_bootstrap.prepare_first_party_sources(root, no_build=False)
        materialize.assert_called_once_with(root)

class BridgeSourceWitnessTests(unittest.TestCase):
    """Real cold selected objects, without the deleted producer commit/history."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="bridge-source-witness-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.source, self.root = self.base / "source", self.base / "root"
        self.child = self.root / "first-party/trust-ir"
        for repository in (self.source, self.root, self.child):
            repository.mkdir(parents=True)
            self.git(repository, "init", "-q", "-b", "main")
            self.git(repository, "config", "user.name", "Witness fixture")
            self.git(repository, "config", "user.email", "witness@example.invalid")
        producer = self.source / "lean/trust_ir-semantics"
        producer.mkdir(parents=True)
        (producer / "lakefile.lean").write_text("import Lake\n")
        (producer / "lean-toolchain").write_text("leanprover/lean4:v4.30.0-rc2\n")
        (producer / "Basic.lean").write_text("def original := 1\n")
        (self.source / "unrelated").write_text("original root\n")
        self.git(self.source, "add", ".")
        self.git(self.source, "commit", "-qm", "old source")
        self.old = self.git(self.source, "rev-parse", "HEAD").decode().strip()
        self.old_tree = self.git(self.source, "rev-parse", "HEAD^{tree}").decode().strip()
        self.old_raw = self.git(self.source, "cat-file", "commit", self.old)
        self.tree_raw = self.git(self.source, "cat-file", "tree", self.old_tree)
        (self.source / "unrelated").write_text("mapped public root\n")
        self.git(self.source, "add", ".")
        tree = self.git(self.source, "write-tree").decode().strip()
        self.selected = self.git(self.source, "commit-tree", tree, "-m", "mapped public source").decode().strip()
        objects = {self.selected: "commit", tree: "tree"}
        for row in self.git(self.source, "ls-tree", "-r", "-t", "-z", tree).split(b"\0"):
            if row:
                fields = row.partition(b"\t")[0].split()
                objects[fields[2].decode()] = fields[1].decode()
        for oid, kind in objects.items():
            raw = self.git(self.source, "cat-file", kind, oid)
            self.assertEqual(self.git(self.child, "hash-object", "-w", "-t", kind, "--stdin", data=raw).decode().strip(), oid)
        self.git(self.child, "update-ref", "refs/heads/main", self.selected)
        self.git(self.child, "reset", "--hard", "-q", self.selected)
        (self.root / ".gitmodules").write_text('[submodule "ir"]\npath = first-party/trust-ir\nurl = https://github.com/alabsystems/trust-ir.git\n')
        self.git(self.root, "config", "submodule.ir.url", "https://github.com/alabsystems/trust-ir.git")
        self.manifest = self.root / "crates/trust-clean/fixtures/trustir-oleans/MANIFEST.toml"
        self.manifest.parent.mkdir(parents=True)
        self.manifest.write_text(f'[provenance]\ntrustir_commit = "{self.old}"\n[source_reuse]\nselected_trustir_commit = "{self.selected}"\n')
        prefix = self.root / "data/bridge-source-witnesses/trust-ir/objects"
        self.commit_file, self.tree_file = prefix / "commit" / self.old, prefix / "tree" / self.old_tree
        for file, raw in ((self.commit_file, self.old_raw), (self.tree_file, self.tree_raw)):
            file.parent.mkdir(parents=True)
            file.write_bytes(raw)
        self.git(self.root, "add", ".gitmodules", "data", "crates")
        self.git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{self.selected},first-party/trust-ir")
        self.git(self.root, "commit", "-qm", "selected source and raw witnesses")
        self.assert_missing(self.old)
        self.assert_missing(self.old_tree)

    @staticmethod
    def git(repository, *args, data=None):
        env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        env.update(GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1", GIT_ALLOW_PROTOCOL="", GIT_OPTIONAL_LOCKS="0")
        done = subprocess.run(["git", "-C", str(repository), *args], input=data, capture_output=True, env=env)
        if done.returncode:
            raise AssertionError((args, done.returncode, done.stderr))
        return done.stdout

    def assert_missing(self, oid):
        self.assertEqual(self.git(self.child, "cat-file", "--batch-check", data=(oid + "\n").encode()), (oid + " missing\n").encode())

    def books(self):
        return [(self.git(repo, "rev-parse", "HEAD"), self.git(repo, "for-each-ref"),
                 (repo / ".git/config").read_bytes(), (repo / ".git/index").read_bytes(),
                 self.git(repo, "status", "--porcelain=v1", "--untracked-files=no")) for repo in (self.root, self.child)]

    def materialize(self):
        return recreate_bootstrap.materialize_bridge_source_witnesses(self.root)

    def test_cold_mapped_source_restores_only_two_objects_without_history_or_ref_changes(self):
        before = self.books()
        self.assertEqual(self.materialize(), 2)
        self.assertEqual(self.git(self.child, "cat-file", "commit", self.old), self.old_raw)
        self.assertEqual(self.git(self.child, "cat-file", "tree", self.old_tree), self.tree_raw)
        self.assertEqual(self.git(self.child, "ls-tree", "-r", self.old, "--", "lean/trust_ir-semantics"),
                         self.git(self.child, "ls-tree", "-r", self.selected, "--", "lean/trust_ir-semantics"))
        self.assertEqual(self.books(), before)
        self.assertEqual(self.materialize(), 0)
        self.assertEqual(self.books(), before)

    def test_complete_submodule_graph_still_uses_existing_materialization_owner(self):
        before = self.books()
        recreate_bootstrap.ensure_submodules(self.root)
        self.assertEqual(self.git(self.child, "cat-file", "commit", self.old), self.old_raw)
        self.assertEqual(self.books(), before)

    def test_bad_commit_and_root_tree_hashes_refuse_before_writing_any_object(self):
        for file in (self.commit_file, self.tree_file):
            with self.subTest(path=file.name):
                original = file.read_bytes()
                file.write_bytes(original + b"tampered\n")
                self.git(self.root, "add", str(file))
                before = self.books()
                with self.assertRaisesRegex(RuntimeError, "canonical type/object hash differs"):
                    self.materialize()
                self.assert_missing(self.old)
                self.assert_missing(self.old_tree)
                self.assertEqual(self.books(), before)
                file.write_bytes(original)
                self.git(self.root, "add", str(file))

    @unittest.skipUnless(os.name == "posix", "symlink fixture")
    def test_indexed_symlink_cannot_supply_witness_bytes(self):
        self.commit_file.unlink()
        self.commit_file.symlink_to(self.tree_file)
        self.git(self.root, "add", str(self.commit_file))
        with self.assertRaisesRegex(RuntimeError, "indexed regular blob"):
            self.materialize()
        self.assert_missing(self.old)

    def test_missing_root_witness_refuses_before_commit_object_is_written(self):
        self.git(self.root, "rm", "-q", str(self.tree_file))
        with self.assertRaisesRegex(RuntimeError, "indexed regular blob"):
            self.materialize()
        self.assert_missing(self.old)

    def test_wrong_selection_cannot_attach_data_to_another_gitlink(self):
        self.manifest.write_text(self.manifest.read_text().replace(self.selected, "a" * 40))
        self.git(self.root, "add", str(self.manifest))
        with self.assertRaisesRegex(RuntimeError, "selection differs"):
            self.materialize()
        self.assert_missing(self.old)

    def test_existing_corrupt_object_is_refused_without_rewriting_it(self):
        import zlib
        self.assertEqual(self.materialize(), 2)
        path = self.child / ".git/objects" / self.old[:2] / self.old[2:]
        wrong = self.old_raw[:-1] + b"x"
        encoded = zlib.compress(f"commit {len(wrong)}\0".encode() + wrong)
        mode = stat.S_IMODE(path.stat().st_mode)
        path.chmod(mode | 0o200)
        path.write_bytes(encoded)
        path.chmod(mode)
        with self.assertRaisesRegex(RuntimeError, "original object bytes differ"):
            self.materialize()
        self.assertEqual(path.read_bytes(), encoded)

    def test_other_submodule_owner_is_not_bypassed(self):
        lock = self.root / ".git/trust-bootstrap-submodules.lock"
        lock.write_text("another owner\n")
        with self.assertRaisesRegex(RuntimeError, "another submodule materialization owns"):
            self.materialize()
        self.assertEqual(lock.read_text(), "another owner\n")
        self.assert_missing(self.old)

    def test_index_mutation_during_object_write_refuses_and_preserves_the_change(self):
        actual = subprocess.run
        changed = []
        def mutate(args, **kwargs):
            if "hash-object" in args and not changed:
                changed.append(True)
                file = self.root / "concurrent"
                file.write_text("preserve concurrent source\n")
                self.git(self.root, "add", "concurrent")
            return actual(args, **kwargs)
        with patch.object(recreate_bootstrap.subprocess, "run", side_effect=mutate), self.assertRaisesRegex(RuntimeError, "bookends changed"):
            self.materialize()
        self.assertEqual((self.root / "concurrent").read_text(), "preserve concurrent source\n")
        self.assertIn(b"concurrent", self.git(self.root, "ls-files", "--", "concurrent"))

    def test_default_sync_is_read_only_and_explicit_fetch_restores_source_data(self):
        sync = SCRIPT.with_name("submodule_sync.sh")
        env = dict(os.environ, PATH=str(Path(sys.executable).parent) + os.pathsep + os.environ.get("PATH", ""))
        for flags in (("--offline", "--quiet"), ("--fetch", "--quiet")):
            done = subprocess.run(["bash", str(sync), *flags, "--root", str(self.root)], env=env, capture_output=True)
            self.assertEqual(done.returncode, 0, done.stderr)
            if "--offline" in flags:
                self.assert_missing(self.old)
        self.assertEqual(self.git(self.child, "cat-file", "commit", self.old), self.old_raw)


if __name__ == "__main__":
    unittest.main()
