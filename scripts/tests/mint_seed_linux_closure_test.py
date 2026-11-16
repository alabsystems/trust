#!/usr/bin/env python3
"""Pure Linux mint dispatch controls; inert ELF headers, no tool execution."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import struct
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("mint_linux_support", ROOT / "scripts/mint_seed_support.py")
assert SPEC and SPEC.loader
support = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(support)
HOST = "aarch64-unknown-linux-gnu"
COMMIT = "a" * 40
VERSION = "0.10.0"


class LinuxMintClosureTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.tmp = Path(temporary.name).resolve()
        self.seed = self.tmp / "build" / HOST / "stage0"
        self.system = self.tmp / "system"
        self.system.mkdir()
        self.loader = self.system / "ld-linux-aarch64.so.1"
        self.libc = self.system / "libc.so.6"
        self.foreign = self.tmp / "foreign.so"
        self.internal = self.seed / "lib" / "internal.so"
        self.extra = self.seed / "libexec" / "extra-tool"
        for path in [self.loader, self.libc, self.foreign, self.internal, self.extra,
                     *(self.seed / "bin" / name for name in
                       ("trustc", "rustc", "cargo", "targo", "trustfmt", "trustdoc"))]:
            path.parent.mkdir(parents=True, exist_ok=True)
            head = bytearray(20)
            head[:7] = b"\x7fELF\x02\x01\x01"
            struct.pack_into("<H", head, 18, 183)
            path.write_bytes(head)
            path.chmod(0o700)
        self.foreign_extra = False
        self.commands = []
        self.linux = support.linux_seed_support()
        patches = [
            mock.patch.object(support.platform, "system", return_value="Linux"),
            mock.patch.object(support, "native_host", return_value=HOST),
            mock.patch.object(support, "linux_seed_support", return_value=self.linux),
            mock.patch.object(self.linux, "is_system", side_effect=lambda p: p.is_relative_to(self.system)),
            mock.patch.object(self.linux, "metadata", side_effect=self.metadata),
            mock.patch.object(self.linux, "command", side_effect=self.command),
            mock.patch("subprocess.Popen", side_effect=AssertionError("no real tool may execute")),
        ]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

    def metadata(self, path, host):
        self.linux.native_elf(path, host)
        return {"interpreter": str(self.loader) if path.parent.name in ("bin", "libexec") else None,
                "dynamic": True, "needed": [1, 2]}

    def command(self, argv, *, role="elf-metadata"):
        self.assertEqual(role, "elf-loader")
        self.assertEqual(argv[:2], [str(self.loader), "--list"])
        binary = Path(argv[2])
        self.commands.append(binary)
        provider = self.foreign if self.foreign_extra and binary == self.extra else self.internal
        return (f"libc.so.6 => {self.libc} (0x1)\n"
                f"libinternal.so => {provider} (0x2)\n")

    def test_full_surface_internal_and_system_dependencies_are_bound(self):
        receipt = support.foreign_load_commands(self.seed, [])
        self.assertTrue(receipt["checked"])
        self.assertEqual(receipt["format"], "elf")
        self.assertFalse(receipt["unresolved"])
        self.assertIn(self.extra, self.commands)
        self.assertIn(str(self.internal), receipt["observations"])
        self.assertIn(str(self.libc), receipt["observations"])
        self.linux.unchanged(receipt)
        self.internal.write_bytes(self.internal.read_bytes() + b"tamper")
        with self.assertRaisesRegex(ValueError, "runtime input changed"):
            self.linux.unchanged(receipt)

    def test_foreign_dependency_of_extra_tool_is_refused(self):
        self.foreign_extra = True
        with self.assertRaisesRegex(support.WorkflowError, "extra-tool.*foreign.so"):
            support.foreign_load_commands(self.seed, [])

    def test_wrong_elf_platform_is_refused_without_native_execution(self):
        self.extra.write_bytes(b"\x7fELF" + bytes(16))
        with self.assertRaisesRegex(support.WorkflowError, "ELF platform differs"):
            support.foreign_load_commands(self.seed, [])
        self.assertFalse(self.commands)

    def test_mac_provider_override_is_not_silently_accepted_on_linux(self):
        with self.assertRaisesRegex(support.WorkflowError, "Linux --seed-dylib-path is unsupported"):
            support.foreign_load_commands(self.seed, [self.system])
        self.assertFalse(self.commands)

    def test_ddc_cli_checks_external_only_closure_before_compiler_identity(self):
        (self.seed / "bin" / "trustc").unlink()
        output = self.tmp / "ddc.json"
        def identity(*args):
            self.assertTrue(self.commands)
            return {"sysroot": str(self.seed), "relation": "lineage-disjoint", "commit": COMMIT,
                    "date": "2026-07-09", "lineage": "stock", "compiler": "bin/rustc"}
        with mock.patch.object(support, "ddc_seed_identity", side_effect=identity), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(support.main(["ddc-seed", "--root", str(self.tmp), "--seed", str(self.seed),
                                           "--host", HOST, "--output", str(output)]), 0)
        receipt = support.load_json(output, "fixture")["foreign_loads"]
        self.assertEqual(receipt["admission"], "external-bootstrap-root-only")
        self.assertFalse(receipt["counts_as_trust_stage0_evidence"])

    def test_pinned_stage0_checks_closure_before_identity_probe(self):
        pin = {"compiler_date": "2026-07-13", "compiler_git_commit_hash": COMMIT}
        (self.seed / ".rustc-stamp").write_text(support.stage0_extraction_stamp(pin))
        def identity(*args):
            self.assertTrue(self.commands)
            return {"host": HOST, "commit": COMMIT, "date": "2026-07-13"}
        with mock.patch.object(support, "read_stage0_pin", return_value=pin), \
                mock.patch.object(support, "compiler_identity", side_effect=identity):
            receipt = support.pinned_stage0_identity(self.tmp, self.tmp / "build", HOST)
        self.assertTrue(receipt["foreign_loads"]["checked"])

    def probe(self, argv, **kwargs):
        self.assertTrue(self.commands, "ELF closure must precede candidate execution")
        name = Path(argv[0]).name
        if name == "trustc" and argv[1:] == ["-vV"]:
            output = (f"trustc fixture\nbinary: trustc\ncommit-hash: {COMMIT}\nhost: {HOST}\n"
                      f"trust: {VERSION}+g{COMMIT[:9]}\n")
        elif name == "trustc" and argv[1:] == ["--print", "sysroot"]:
            output = str(self.seed)
        elif name == "targo":
            output = (f"targo fixture\ntrust-repo-commit-hash: {COMMIT}\nhost: {HOST}\n"
                      f"trust: {VERSION}+g{COMMIT[:9]}\n")
        elif name == "trustfmt":
            output = "trustfmt fixture"
        else:
            self.fail(f"unexpected inert identity probe: {argv}")
        return SimpleNamespace(returncode=0, stdout=output)

    def test_installed_seed_retains_full_runtime_receipt_before_probes(self):
        with mock.patch.object(support.subprocess, "run", side_effect=self.probe) as probes, \
                mock.patch.object(support.shutil, "which", side_effect=AssertionError("no optional ldd")):
            receipt = support.validate_seed(self.seed, VERSION, HOST)
        self.assertTrue(receipt["linux_runtime_closure"]["checked"])
        self.assertEqual(probes.call_count, 4)
        self.assertIn(str(self.extra), receipt["linux_runtime_closure"]["observations"])

    def test_installed_seed_probe_environment_matches_checked_loader_despite_injection(self):
        injected = {"LD_PRELOAD": "/unobserved/preload.so",
                    "LD_LIBRARY_PATH": "/unobserved/lib", "LD_AUDIT": "/unobserved/audit.so",
                    "GLIBC_TUNABLES": "glibc.cpu.hwcaps=-fixture",
                    "LD_DEBUG": "libs", "LD_TRACE_LOADED_OBJECTS": "1"}
        observed = []
        def probe(argv, **kwargs):
            observed.append(dict(kwargs["env"]))
            self.assertEqual(kwargs["env"], self.linux.ENV)
            self.assertTrue(set(injected).isdisjoint(kwargs["env"]))
            return self.probe(argv, **kwargs)
        with mock.patch.dict(support.os.environ, injected), \
                mock.patch.object(support.subprocess, "run", side_effect=probe):
            receipt = support.validate_seed(self.seed, VERSION, HOST)
            self.assertTrue(all(support.os.environ[key] == value for key, value in injected.items()))
        self.assertEqual(len(observed), 4)
        self.assertTrue(receipt["linux_runtime_closure"]["checked"])

    def test_installed_seed_foreign_provider_refuses_before_any_probe(self):
        self.foreign_extra = True
        with mock.patch.object(support.subprocess, "run") as probes, \
                self.assertRaisesRegex(support.WorkflowError, "undeclared foreign providers"):
            support.validate_seed(self.seed, VERSION, HOST)
        probes.assert_not_called()

    def test_darwin_path_keeps_existing_receipt_and_does_not_load_linux_helper(self):
        with mock.patch.object(support.platform, "system", return_value="Darwin"), \
                mock.patch.object(support, "linux_seed_support", side_effect=AssertionError("not Linux")):
            self.assertEqual(support.foreign_load_commands(self.seed, []), {"checked": True, "foreign": []})


if __name__ == "__main__":
    unittest.main()
