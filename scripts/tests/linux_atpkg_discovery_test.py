#!/usr/bin/env python3
"""Native default discovery controls; all external processes are mocked/refused."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


def load_script(name):
    path = Path(__file__).resolve().parents[1] / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def forbid_processes():
    stack = contextlib.ExitStack()
    for name in ("Popen", "run", "call", "check_call", "check_output"):
        stack.enter_context(mock.patch.object(
            subprocess, name, side_effect=AssertionError("external process forbidden")
        ))
    return stack


with forbid_processes():
    recreate = load_script("recreate_bootstrap")
    mint = load_script("mint_seed_support")


class NativeAtpkgDiscoveryTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.task_home = Path(temp.name).resolve()
        self.stack = self.enterContext(contextlib.ExitStack())
        self.stack.enter_context(mock.patch.object(Path, "home", return_value=self.task_home))
        self.stack.enter_context(mock.patch.object(recreate.platform, "system", return_value="Linux"))
        self.stack.enter_context(forbid_processes())

    def fixture_pack(self, system="Linux", *, aside=False):
        relative = "Library/Application Support/aterm/pkg" if system == "Darwin" else ".local/share/aterm/pkg"
        prefix = self.task_home / relative
        pack = prefix / "store/trust/42"
        (pack / "bin").mkdir(parents=True)
        (prefix / "bin").mkdir()
        (pack.parent / "current").symlink_to(pack, target_is_directory=True)
        for name in set(recreate.ATPKG_STAGE0_TOOLS.values()) | {"targo"}:
            tool = pack / "bin" / name
            tool.write_bytes(f"inert {name}".encode())
            tool.chmod(0o755)
        for name in ("trustc", "targo", "trustdoc", "trustfmt", "targo-tippy"):
            shim = prefix / "bin" / name
            shim.write_text(f'#!/bin/sh\nexec \'{pack / "bin" / name}\' "$@"\n')
            shim.chmod(0o755)
        (prefix / "status.toml").write_text(
            'schema = 1\n[programs.trust]\ninstalled_build = 42\ntree_root = "' + "a" * 64 + '"\n'
        )
        if aside:
            physical = pack.with_name(f"{pack.name}.noindex")
            pack.rename(physical)
            pack.symlink_to(physical.name, target_is_directory=True)
        return prefix, pack

    def test_linux_default_is_the_actual_atpkg_prefix(self):
        self.assertEqual(recreate._atpkg_prefix(), self.task_home / ".local/share/aterm/pkg")

    def test_mac_default_preserves_existing_layout(self):
        with mock.patch.object(recreate.platform, "system", return_value="Darwin"):
            self.assertEqual(recreate._atpkg_prefix(), self.task_home / "Library/Application Support/aterm/pkg")

    def test_unsupported_platform_does_not_guess_a_store(self):
        with mock.patch.object(recreate.platform, "system", return_value="Plan9"):
            with self.assertRaisesRegex(ValueError, "unsupported native"):
                recreate._atpkg_prefix()
            with self.assertRaisesRegex(mint.WorkflowError, "unsupported native"):
                mint.default_ddc_seed(self.task_home)

    def test_environment_cannot_redirect_default_store(self):
        with mock.patch.dict(os.environ, {"ATPKG_BIN": "/untrusted/bin", "XDG_DATA_HOME": "/untrusted", "PATH": "/untrusted"}):
            self.assertEqual(recreate._atpkg_prefix(), self.task_home / ".local/share/aterm/pkg")

    def test_capture_selects_active_linux_pack_not_newer_staged_pack(self):
        _, pack = self.fixture_pack()
        (pack.parent / "9999").mkdir()
        actual = recreate._capture_atpkg_pack()
        self.assertEqual(actual["pack_local_path"], str(pack))
        self.assertEqual(actual["build"], 42)

    def test_mac_capture_still_uses_active_mac_pack(self):
        _, pack = self.fixture_pack("Darwin")
        with mock.patch.object(recreate.platform, "system", return_value="Darwin"):
            self.assertEqual(recreate._capture_atpkg_pack()["pack_local_path"], str(pack))

    def test_laid_aside_pack_retains_logical_tool_selection(self):
        _, pack = self.fixture_pack("Darwin", aside=True)
        physical = pack.with_name("42.noindex")
        paths = {key: str(pack / "bin" / name) for key, name in recreate.ATPKG_STAGE0_TOOLS.items()}
        with mock.patch.object(recreate.platform, "system", return_value="Darwin"):
            capture = recreate._capture_atpkg_pack(paths)
        self.assertEqual(capture["build"], 42)
        self.assertEqual(capture["pack_local_path"], str(pack))
        self.assertEqual(capture["pack_physical_path"], str(physical))
        self.assertEqual(capture["configured_tools"]["rustc"]["selected_local_path"], paths["rustc"])
        self.assertEqual(capture["configured_tools"]["rustc"]["resolved_real_path"], str(physical / "bin/trustc"))

    def test_unowned_or_chained_pack_alias_refuses(self):
        _, pack = self.fixture_pack(aside=True)
        physical = pack.with_name("42.noindex")
        pack.with_name("other").symlink_to(physical.name, target_is_directory=True)
        pack.with_name("43.noindex").mkdir()
        for target in (physical, "other", "43.noindex"):
            with self.subTest(target=target):
                pack.unlink()
                pack.symlink_to(target, target_is_directory=True)
                with self.assertRaisesRegex(ValueError, "numbered store pack|owned .noindex"):
                    recreate._capture_atpkg_pack()

        pack.unlink()
        physical.rename(pack.with_name("43"))
        physical.symlink_to("43", target_is_directory=True)
        pack.symlink_to(physical.name, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "numbered store pack|owned .noindex"):
            recreate._capture_atpkg_pack()

    def test_linux_mixed_shims_still_refuse(self):
        prefix, _ = self.fixture_pack()
        (prefix / "bin/trustc").write_text('#!/bin/sh\nexec /untrusted/trustc "$@"\n')
        with self.assertRaisesRegex(ValueError, "active shim disagrees"):
            recreate._capture_atpkg_pack()

    def test_linux_status_must_still_match_active_pack(self):
        prefix, _ = self.fixture_pack()
        status = prefix / "status.toml"
        status.write_text(status.read_text().replace("installed_build = 42", "installed_build = 99"))
        with self.assertRaisesRegex(ValueError, "status build/tree_root"):
            recreate._capture_atpkg_pack()

    def test_linux_authority_remains_local_candidate_not_release(self):
        _, pack = self.fixture_pack(aside=True)
        verifier = self.task_home / "atpkg"
        verifier.write_bytes(b"inert verifier")
        verifier.chmod(0o755)

        def verify(argv, **_kwargs):
            self.assertEqual(argv[0], str(verifier))
            if argv[1:] == ["verify", "trust"]:
                return SimpleNamespace(returncode=0, stdout="atpkg: trust build 42 OK (matches signed tree_root)\n", stderr="")
            self.assertEqual(argv[1:], ["tree-root", str(pack.with_name("42.noindex"))])
            return SimpleNamespace(returncode=0, stdout="a" * 64 + "\n", stderr="")

        with mock.patch.object(recreate.shutil, "which", return_value=str(verifier)), mock.patch.object(subprocess, "run", side_effect=verify):
            snapshot = recreate._capture_atpkg_stage0_authority(None)
        self.assertTrue(recreate._atpkg_authority_ready(snapshot), snapshot)
        authority = snapshot["authority"]
        self.assertEqual(authority["evidence_class"], "local-offline-tree-match")
        self.assertIs(authority["fresh_signature_replay"], False)
        self.assertIs(authority["release_authority"], False)

    def test_fresh_seed_never_consults_even_complete_linux_pack(self):
        self.fixture_pack()
        args = recreate.parse_args(["--fresh-seed", "--require-seed", "--no-fetch", "--host", "aarch64-unknown-linux-gnu"])
        with mock.patch.object(recreate, "atpkg_trust_sysroot", side_effect=AssertionError("fresh seed must use pin")), mock.patch.object(recreate, "resolve_seed", return_value=False) as resolve, contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaisesRegex(RuntimeError, "refusing genesis fallback"):
                recreate.resolve_stage0_selection(self.task_home, args)
        resolve.assert_called_once_with(self.task_home, allow_fetch=False, host="aarch64-unknown-linux-gnu", use_store=True)

    def test_ddc_search_uses_platform_default_and_excludes_current_pin(self):
        for system, relative in (("Linux", ".local/share/aterm/pkg"), ("Darwin", "Library/Application Support/aterm/pkg")):
            with self.subTest(system=system):
                store = self.task_home / relative / "store/trust"
                for build in ("41", "42", "99"):
                    (store / build).mkdir(parents=True)
                (store / "current").symlink_to(store / "99", target_is_directory=True)
                (store / "100").symlink_to(store / "42", target_is_directory=True)

                def identity(candidate, _description):
                    return {"commit": "a" * 40 if candidate.name == "99" else "b" * 40}

                with mock.patch.object(mint.platform, "system", return_value=system), mock.patch.object(mint, "read_stage0_pin", return_value={"compiler_git_commit_hash": "a" * 40}), mock.patch.object(mint, "compiler_identity", side_effect=identity) as probe:
                    self.assertEqual(mint.default_ddc_seed(self.task_home), store / "42")
                    self.assertEqual([call.args[0].name for call in probe.call_args_list], ["99", "42"])

    def test_ddc_discovery_does_not_invent_a_candidate(self):
        with mock.patch.object(mint, "read_stage0_pin", return_value={"compiler_git_commit_hash": "a" * 40}), mock.patch.object(mint, "compiler_identity", side_effect=AssertionError("no candidate to probe")):
            with self.assertRaisesRegex(mint.WorkflowError, "no --ddc-seed given"):
                mint.default_ddc_seed(self.task_home)


if __name__ == "__main__":
    with forbid_processes():
        unittest.main(verbosity=2)
