#!/usr/bin/env python3
"""Behavioral regressions for the mint's declared native build-helper boundary."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts import mint_seed_support as support


HOST = "aarch64-apple-darwin"


def executable(path: Path, body: str = "exit 0\n") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("#!/bin/sh\n" + body, encoding="utf-8")
    path.chmod(0o755)
    return path


class SafePathTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.tools = self.root / "tools"
        self.tools.mkdir()
        for name in support.build_helper_names(HOST):
            executable(self.tools / name)
        self.python = executable(self.root / "selected-python", "printf selected-python\n")
        self.output = self.root / "safe-bin"
        self.manifest = self.root / "safe-path.json"

    def admit(self, path=None, host=HOST):
        report = support.create_sanitized_path(
            path or str(self.tools), self.output, host, self.python,
        )
        support.write_json_exclusive(self.manifest, report)
        return report

    def revalidate(self):
        support.revalidate_sanitized_path(self.output, self.manifest)

    def test_unrelated_app_atomic_replacement_is_not_an_input(self):
        bundle = executable(self.root / "App.app/Contents/MacOS/aterm", "printf old-app\n")
        alias = self.tools / "agh"
        alias.symlink_to(bundle)
        executable(self.tools / "node")
        # No enumeration/hash of unrelated executables, including unreadable
        # files and a broken symlink, is necessary for declared helper admission.
        executable(self.tools / "sudo").chmod(0o111)
        (self.tools / "unrelated-cycle").symlink_to("unrelated-cycle")
        report = self.admit()
        before = self.manifest.read_bytes()
        replacement = executable(bundle.with_name("aterm-new"), "printf new-app\n")
        old_inode = bundle.stat().st_ino
        replacement.replace(bundle)
        self.assertNotEqual(old_inode, bundle.stat().st_ino)
        alias.unlink()
        alias.symlink_to(self.root / "missing-app")
        executable(self.tools / "new-cli")
        self.revalidate()
        self.assertEqual(before, self.manifest.read_bytes())
        self.assertEqual(set(report["admitted"]), set(support.build_helper_names(HOST)))
        for name in ("agh", "aterm", "node", "sudo", "new-cli", "unrelated-cycle"):
            self.assertFalse((self.output / name).is_symlink())
            self.assertNotIn(name, report["admitted"])

    def test_declared_helper_replacement_with_identical_bytes_is_rejected(self):
        self.admit()
        original = self.tools / "cc"
        replacement = executable(self.root / "new-cc")
        self.assertEqual(original.read_bytes(), replacement.read_bytes())
        replacement.replace(original)
        with self.assertRaisesRegex(support.WorkflowError, "target changed \\(inode\\)"):
            self.revalidate()

    def test_same_size_mtime_content_tampering_is_rejected(self):
        self.admit()
        helper = self.tools / "cc"
        before = helper.stat()
        helper.write_bytes(helper.read_bytes().replace(b"exit 0", b"exit 9"))
        os.utime(helper, ns=(before.st_atime_ns, before.st_mtime_ns))
        self.assertEqual(before.st_size, helper.stat().st_size)
        with self.assertRaisesRegex(support.WorkflowError, "target changed \\(sha256\\)"):
            self.revalidate()

    def test_mode_tampering_is_rejected_even_when_still_executable(self):
        self.admit()
        (self.tools / "cc").chmod(0o700)
        with self.assertRaisesRegex(support.WorkflowError, "target changed \\(mode\\)"):
            self.revalidate()

    def test_lost_execute_permission_is_rejected(self):
        self.admit()
        (self.tools / "cc").chmod(0o644)
        with self.assertRaisesRegex(support.WorkflowError, "executable regular file"):
            self.revalidate()

    def test_target_replaced_by_directory_is_rejected(self):
        self.admit()
        (self.tools / "cc").unlink()
        (self.tools / "cc").mkdir()
        with self.assertRaisesRegex(support.WorkflowError, "executable regular file"):
            self.revalidate()

    def test_first_executable_wins_and_unused_later_helper_can_update(self):
        first = self.root / "first"
        chosen = executable(first / "cc", "printf first-cc\n")
        report = self.admit(os.pathsep.join((str(first), str(self.tools))))
        self.assertEqual(report["admitted"]["cc"]["path"], str(chosen))
        executable(self.tools / "cc", "printf second-cc-updated\n")
        self.revalidate()
        result = subprocess.run([str(self.output / "cc")], check=True, capture_output=True)
        self.assertEqual(result.stdout, b"first-cc")

    def test_upstream_alias_retarget_keeps_the_actual_admitted_input(self):
        provider = executable(self.root / "provider/cc", "printf admitted-provider\n")
        alias = self.tools / "cc"
        alias.unlink()
        alias.symlink_to(provider)
        self.admit()
        alias.unlink()
        alias.symlink_to(executable(self.root / "other/cc", "printf other-provider\n"))
        self.revalidate()
        result = subprocess.run([str(self.output / "cc")], check=True, capture_output=True)
        self.assertEqual(result.stdout, b"admitted-provider")

    def test_nonexecutable_directory_and_dangling_link_do_not_shadow(self):
        first = self.root / "first"
        first.mkdir()
        (first / "cc").mkdir()
        executable(first / "git").chmod(0o644)
        (first / "ninja").symlink_to("missing")
        os.mkfifo(first / "make")
        report = self.admit(os.pathsep.join((str(first), str(self.tools))))
        for name in ("cc", "git", "ninja", "make"):
            self.assertEqual(report["admitted"][name]["path"], str(self.tools / name))

    def test_missing_declared_helper_refuses_without_partial_path(self):
        (self.tools / "ninja").unlink()
        with self.assertRaisesRegex(support.WorkflowError, "declared build helper 'ninja'"):
            self.admit()
        self.assertFalse(self.output.exists())

    def test_gmp_m4_probe_runs_under_the_private_path(self):
        # GMP requires argument counting and radix eval before accepting m4.
        # The old profile omitted m4 even when the host provided a usable one.
        import shutil
        m4 = shutil.which("m4")
        if m4 is None:
            self.skipTest("native m4 unavailable on this test host")
        helper = self.tools / "m4"
        helper.unlink(missing_ok=True)
        helper.symlink_to(Path(m4).resolve())
        self.admit()
        probe = self.root / "gmp-probe.m4"
        probe.write_text("define(`count',`$#')ifelse(count(x),1,`ifelse(eval(9,9),10,`good',`bad')',`bad')\n")
        result = subprocess.run(["/bin/sh", "-c", 'm4 "$1"', "gmp-probe", str(probe)],
                                env={"PATH": str(self.output)}, capture_output=True,
                                text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "good\n")
        self.revalidate()

    def test_unreadable_first_helper_refuses_instead_of_using_later_one(self):
        first = executable(self.root / "first/cc")
        digest = support.sha256_file

        def read(path):
            if path == first:
                raise PermissionError("fixture denies read")
            return digest(path)

        with mock.patch.object(support, "sha256_file", side_effect=read):
            with self.assertRaisesRegex(support.WorkflowError, "cannot authenticate.*first/cc"):
                self.admit(os.pathsep.join((str(first.parent), str(self.tools))))

    def test_rust_names_and_resolved_targets_are_excluded(self):
        rust_names = (
            "rustc", "rustdoc", "rustfmt", "rustup", "cargo", "cargo-clippy", "clippy-driver",
            "miri", "sccache", "tcargo", "trust", "trustc", "trustdoc", "trustfmt", "targo",
            "tippy", "trustup", "rust-analyzer", "rustc-nightly", "rustfmt-old", "clippy-old",
            "targo-old", "tcargo-old", "tippy-old", "trust-analyzer",
        )
        for name in rust_names:
            executable(self.tools / name)
        self.admit()
        for name in rust_names:
            self.assertFalse((self.output / name).exists(), name)
        self.revalidate()

    def test_first_helper_alias_to_rust_frontend_refuses(self):
        rust = executable(self.root / "ambient/trustc")
        first = self.root / "first"
        first.mkdir()
        (first / "cc").symlink_to(rust)
        with self.assertRaisesRegex(support.WorkflowError, "forbidden Rust-family tool"):
            self.admit(os.pathsep.join((str(first), str(self.tools))))

    def test_helper_inside_stock_tree_refuses(self):
        stock = executable(self.root / ".rustup/toolchains/stock/bin/cc")
        with self.assertRaisesRegex(support.WorkflowError, "forbidden Rust-family tool"):
            self.admit(os.pathsep.join((str(stock.parent), str(self.tools))))

    def test_selected_python_binds_both_names_and_ignores_ambient_python(self):
        report = self.admit()
        for name in support.PYTHON_BUILD_HELPERS:
            self.assertEqual(report["admitted"][name]["path"], str(self.python))
            result = subprocess.run([str(self.output / name)], check=True, capture_output=True)
            self.assertEqual(result.stdout, b"selected-python")
            executable(self.tools / name, "printf wrong-python-updated\n")
        self.revalidate()

    def test_selected_python_tampering_is_rejected(self):
        self.admit()
        executable(self.python, "printf tampered-python\n")
        with self.assertRaisesRegex(support.WorkflowError, "sanitized PATH target changed"):
            self.revalidate()

    def test_missing_relative_and_rust_python_refuse(self):
        for candidate in (self.root / "missing-python", Path("python3"),
                          executable(self.root / "ambient/rustup")):
            with self.subTest(python=candidate), self.assertRaises(support.WorkflowError):
                support.create_sanitized_path(str(self.tools), self.output, HOST, candidate)

    def test_invalid_path_components_refuse(self):
        for path in ("", str(self.tools) + os.pathsep, ".", "relative/bin", "/bad\npath", "/bad\x00path"):
            with self.subTest(path=path), self.assertRaises(support.WorkflowError):
                self.admit(path=path if path else os.pathsep)
        self.assertFalse(self.output.exists())

    def test_unsupported_host_refuses(self):
        for host in ("aarch64-pc-windows-msvc", "riscv64-unknown-linux-gnu", "garbage"):
            with self.subTest(host=host), self.assertRaises(support.WorkflowError):
                self.admit(host=host)

    def test_linux_profiles_have_a_closed_gnu_native_surface(self):
        for host in ("x86_64-unknown-linux-gnu", "aarch64-unknown-linux-musl"):
            with self.subTest(host=host):
                names = support.build_helper_names(host)
                self.assertIn("gcc", names)
                self.assertIn("g++", names)
                self.assertIn("ldd", names)
                self.assertNotIn("xcrun", names)
                self.assertFalse(any(support.rust_family_name(name) for name in names))

    def test_native_build_lock_protocol_needs_no_private_path_helpers(self):
        targo = shutil.which(os.environ.get("TARGO", "targo"))
        self.assertIsNotNone(targo, "the real native Targo provider is required")
        bare = self.root / "bare-bin"
        bare.mkdir()
        got = subprocess.run([targo, "trust", "repo", "lock", "--protocol"],
                             env={"PATH": str(bare), "HOME": str(self.root)},
                             capture_output=True, text=True, timeout=30)
        self.assertEqual(got.returncode, 0, got.stderr)
        self.assertEqual(got.stdout, "trust-build-tree-manager-v2\n")

    def test_build_lock_issues_a_token_under_the_private_path(self):
        # The real native owner must work under the mint's admitted private
        # PATH, without the retired shell lock or a helper-generated nonce.
        targo = shutil.which(os.environ.get("TARGO", "targo"))
        self.assertIsNotNone(targo, "the real native Targo provider is required")
        tools = self.root / "host-tools"
        tools.mkdir()
        search = os.pathsep.join((os.environ.get("PATH", ""), "/usr/bin", "/bin", "/usr/sbin", "/sbin"))
        for name in support.build_helper_names(HOST):
            if name in support.PYTHON_BUILD_HELPERS:
                continue
            real = shutil.which(name, path=search)
            if real is None or support.forbidden_tool_path(Path(real)):
                executable(tools / name)
            else:
                (tools / name).symlink_to(real)
        support.create_sanitized_path(str(tools), self.output, HOST, Path(sys.executable))
        repo = self.root / "repo"
        (repo / "build").mkdir(parents=True)
        env = {"PATH": str(self.output), "HOME": str(self.root), "TRUST_REPO": str(repo)}
        acquired = subprocess.run(
            [targo, "trust", "repo", "lock", "acquire", "--kind", "build", "--purpose", "private PATH test",
             "--pid", str(os.getpid()), "--wait", "0"],
            env=env, capture_output=True, text=True, timeout=120)
        self.assertEqual(acquired.returncode, 0, acquired.stderr)
        token = acquired.stdout.strip()
        self.assertTrue(token, "the lock issued an empty token: " + acquired.stderr)
        released = subprocess.run([targo, "trust", "repo", "lock", "release", token],
                                  env=env, capture_output=True, text=True, timeout=120)
        self.assertEqual(released.returncode, 0, released.stderr)

    def test_native_build_lock_issues_and_releases_its_actual_token_without_helpers(self):
        targo = shutil.which(os.environ.get("TARGO", "targo"))
        self.assertIsNotNone(targo, "the real native Targo provider is required")
        bare = self.root / "bare-bin"
        bare.mkdir()
        repo = self.root / "repo"
        repo.mkdir()
        env = {"PATH": str(bare), "HOME": str(self.root), "TRUST_REPO": str(repo)}
        got = subprocess.run(
            [targo, "trust", "repo", "lock", "acquire", "--kind", "build",
             "--pid", str(os.getpid()), "--wait", "0"],
            env=env, capture_output=True, text=True, timeout=30,
        )
        self.assertEqual(got.returncode, 0, got.stderr)
        token = got.stdout.strip()
        self.assertTrue(token, "a native acquisition cannot issue an empty token")
        self.assertIn("token=" + token + "\n", (repo / ".trust-build-lock/info").read_text())
        released = subprocess.run([targo, "trust", "repo", "lock", "release", token],
                                  env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(released.returncode, 0, released.stderr)
        self.assertFalse((repo / ".trust-build-lock").exists())

    def test_each_supported_profile_can_be_admitted_and_revalidated(self):
        for host in ("aarch64-apple-darwin", "x86_64-apple-darwin",
                     "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu",
                     "aarch64-unknown-linux-musl", "x86_64-unknown-linux-musl"):
            with self.subTest(host=host):
                tools = self.root / host
                for name in support.build_helper_names(host):
                    executable(tools / name)
                output = self.root / (host + "-safe")
                manifest = self.root / (host + ".json")
                report = support.create_sanitized_path(str(tools), output, host, self.python)
                support.write_json_exclusive(manifest, report)
                support.revalidate_sanitized_path(output, manifest)

    def test_actual_shell_admission_passes_host_and_selected_python_to_cli(self):
        owner = (ROOT / "scripts/mint_and_prove_seed.sh").read_text(encoding="utf-8")
        fragment = "SAFE_BIN=" + owner.split("\nSAFE_BIN=", 1)[1].split("\nrun_clean()", 1)[0]
        subprocess.run(["/bin/bash", "-eu", "-c", fragment], check=True, capture_output=True,
                       env={"WORK": str(self.root), "PATH": str(self.tools), "HOST": HOST,
                            "PYTHON_BIN": sys.executable,
                            "HELPER": str(ROOT / "scripts/mint_seed_support.py")})
        report = json.loads(self.manifest.read_text(encoding="utf-8"))
        self.assertEqual(report["host"], HOST)
        self.assertEqual(report["python"], str(Path(sys.executable).resolve()))
        self.revalidate()

    def test_added_entry_refuses(self):
        self.admit()
        (self.output / "cargo").symlink_to(self.python)
        with self.assertRaisesRegex(support.WorkflowError, "entry set changed"):
            self.revalidate()

    def test_missing_entry_refuses(self):
        self.admit()
        (self.output / "cc").unlink()
        with self.assertRaisesRegex(support.WorkflowError, "entry set changed"):
            self.revalidate()

    def test_entry_replaced_with_regular_file_refuses(self):
        self.admit()
        (self.output / "cc").unlink()
        executable(self.output / "cc")
        with self.assertRaisesRegex(support.WorkflowError, "no longer a symlink"):
            self.revalidate()

    def test_manifest_unknown_profile_or_undeclared_name_refuses(self):
        original = self.admit()
        for mutation in ("schema", "profile", "name", "python"):
            changed = json.loads(json.dumps(original))
            if mutation in ("schema", "profile"):
                changed[mutation] = "unknown"
            elif mutation == "name":
                changed["admitted"]["../outside"] = changed["admitted"].pop("cc")
            else:
                changed["python"] = "/other/python"
            self.manifest.write_text(json.dumps(changed), encoding="utf-8")
            with self.subTest(mutation=mutation), self.assertRaises(support.WorkflowError):
                self.revalidate()


if __name__ == "__main__":
    unittest.main()
