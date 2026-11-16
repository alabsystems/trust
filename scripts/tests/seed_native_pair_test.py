#!/usr/bin/env python3
"""Native seed pair identity controls; all process probes are inert stand-ins."""
from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("seed_pair_support", ROOT / "scripts/mint_seed_support.py")
assert SPEC and SPEC.loader
support = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(support)
VERSION = "0.10.0"
COMMIT = "a" * 40
HOST = "aarch64-unknown-linux-gnu"


def identities(commit=COMMIT, host=HOST, product=VERSION + "+g" + COMMIT[:9]):
    compiler = (
        f"rustc 1.99.0-dev (trustc {product})\n"
        f"binary: trustc\ncommit-hash: {commit}\ncommit-date: 2026-10-03\n"
        f"host: {host}\nrelease: 1.99.0-dev\ntrust: {product}"
    )
    targo = (
        f"targo 1.99.0-dev (targo {product})\nrelease: 1.99.0-dev\n"
        f"trust: {product}\ncommit-hash: {'b' * 40}\n"
        f"trust-repo-commit-hash: {commit}\nhost: {host}"
    )
    return compiler, targo


class NativeSeedPairTests(unittest.TestCase):
    def setUp(self):
        guard = mock.patch("subprocess.Popen", side_effect=AssertionError("no real process may execute"))
        guard.start()
        self.addCleanup(guard.stop)

    def pair(self, compiler, frontend, version=VERSION, host=HOST):
        return support.native_seed_tool_pair(compiler, frontend, version, host)

    def refuses(self, compiler, frontend, fragment):
        with self.assertRaisesRegex(support.WorkflowError, fragment):
            self.pair(compiler, frontend)

    def test_exact_native_hosts_and_both_git_hash_formats(self):
        for host in (HOST, "x86_64-unknown-linux-musl", "aarch64-apple-darwin"):
            for commit in ("a" * 40, "c" * 64):
                with self.subTest(host=host, commit=commit):
                    pair = self.pair(*identities(commit, host), host=host)
                    self.assertEqual(pair["source_commit"], commit)
                    self.assertEqual(pair["host"], host)

    def test_own_targo_git_commit_cannot_replace_parent_trust_binding(self):
        compiler, frontend = identities()
        self.assertEqual(self.pair(compiler, frontend)["source_commit"], COMMIT)
        self.refuses(compiler, frontend.replace(COMMIT, "b" * 40), "different Trust source")

    def test_absent_unbound_malformed_and_different_parent_bindings_refuse(self):
        compiler, frontend = identities()
        for binding in ("unbound", "", "b" * 40, "a" * 39, "A" * 40):
            with self.subTest(binding=binding):
                self.refuses(compiler, frontend.replace("trust-repo-commit-hash: " + COMMIT,
                             "trust-repo-commit-hash: " + binding), "different Trust source")
        self.refuses(compiler, "\n".join(line for line in frontend.splitlines()
                     if not line.startswith("trust-repo-commit-hash:")), "different Trust source")

    def test_noncanonical_compiler_commits_refuse_even_if_both_report_them(self):
        for commit in ("a" * 41, "a" * 63, "A" * 40, "unbound", "a" * 39):
            with self.subTest(commit=commit):
                self.refuses(*identities(commit), "exact source commit")

    def test_duplicate_identity_fields_refuse_even_if_values_match(self):
        compiler, frontend = identities()
        for key, value in (("commit-hash", COMMIT), ("host", HOST), ("trust", VERSION)):
            with self.subTest(tool="trustc", key=key):
                self.refuses(compiler + f"\n{key}: {value}", frontend, "duplicate identity field")
        for key, value in (("trust-repo-commit-hash", COMMIT), ("host", HOST), ("trust", VERSION)):
            with self.subTest(tool="targo", key=key):
                self.refuses(compiler, frontend + f"\n{key}: {value}", "duplicate identity field")

    def test_repeatable_frontend_capabilities_do_not_change_native_pair_identity(self):
        compiler, frontend = identities()
        capabilities = (
            "\ncache-integrity: build-script-control-output-v1"
            "\ncache-integrity: compiled-build-script-executable-v1"
            "\ncache-integrity: build-script-generated-tree-v1"
        )
        self.assertEqual(self.pair(compiler, frontend + capabilities),
                         self.pair(compiler, frontend))

    def test_repeatable_capabilities_cannot_hide_missing_or_duplicate_identity(self):
        compiler, frontend = identities()
        frontend += (
            "\ncache-integrity: build-script-control-output-v1"
            "\ncache-integrity: compiled-build-script-executable-v1"
        )
        self.refuses(compiler, frontend.replace("trust-repo-commit-hash: " + COMMIT,
                     "cache-integrity: " + COMMIT), "different Trust source")
        for key, value in (("trust-repo-commit-hash", COMMIT), ("host", HOST),
                           ("trust", VERSION)):
            with self.subTest(key=key):
                self.refuses(compiler, frontend + f"\n{key}: {value}",
                             "duplicate identity field")

    def test_cross_host_or_unreported_frontend_host_refuses(self):
        compiler, frontend = identities()
        self.refuses(compiler, frontend.replace(HOST, "aarch64-apple-darwin"), "native host identity")
        self.refuses(compiler, frontend.replace("host: " + HOST, "target: " + HOST), "native host identity")

    def test_compatibility_version_or_banner_cannot_authorize_wrong_product(self):
        compiler, frontend = identities()
        self.refuses(compiler.replace("trust: " + VERSION, "trust: 0.9.0"), frontend,
                     "exact Trust product version")
        self.refuses(compiler, frontend.replace("trust: " + VERSION, "trust: 0.9.0"),
                     "product version differs")
        self.refuses(compiler, frontend.replace("trust: " + VERSION + "+g" + COMMIT[:9],
                                               "trust: " + VERSION), "product version differs")

    def test_compatibility_frontdoors_do_not_gain_native_pair_authority(self):
        compiler, frontend = identities()
        self.refuses(compiler.replace("binary: trustc", "binary: rustc"), frontend,
                     "not the Trust-native")
        self.refuses(compiler, frontend.replace("targo ", "cargo ", 1), "not the Trust-native")

    def validate_fixture(self, tmp, compiler, frontend, calls=None):
        seed = Path(tmp) / "seed"
        (seed / "bin").mkdir(parents=True)
        for name in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt"):
            path = seed / "bin" / name
            path.write_bytes(("inert fixture " + name).encode())
            path.chmod(0o700)
        calls = [] if calls is None else calls

        def probe(argv, **kwargs):
            calls.append(argv)
            self.assertEqual(kwargs["timeout"], 30)
            name = Path(argv[0]).name
            if name == "trustc" and argv[1:] == ["-vV"]:
                output = compiler
            elif name == "trustc" and argv[1:] == ["--print", "sysroot"]:
                output = str(seed)
            elif name == "targo" and argv[1:] == ["--version", "--verbose"]:
                output = frontend
            elif name == "trustfmt" and argv[1:] == ["--version"]:
                output = "trustfmt 1.9.0-trust"
            else:
                self.fail(f"unadmitted inert probe: {argv}")
            return SimpleNamespace(returncode=0, stdout=output)

        with mock.patch.object(support.subprocess, "run", side_effect=probe), \
                mock.patch.object(support.shutil, "which", return_value=None), \
                mock.patch.object(support.platform, "system", return_value="Linux"), \
                mock.patch.object(support, "foreign_load_commands", return_value={
                    "checked": True, "format": "elf", "fixture": "identity-only"
                }) as runtime:
            result = support.validate_seed(seed, VERSION, HOST)
            runtime.assert_called_once_with(seed, [])
        return result, calls

    def test_real_validation_seam_retains_verbose_parent_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            compiler, frontend = identities()
            result, calls = self.validate_fixture(tmp, compiler, frontend)
            self.assertEqual(result["native_tool_pair"], self.pair(compiler, frontend))
            self.assertEqual(result["tool_versions"]["targo"], frontend)
            self.assertEqual(len(result["entrypoint_sha256"]), 6)
            self.assertTrue(result["tree"]["sha256"])
            self.assertIn([str(Path(tmp) / "seed/bin/targo"), "--version", "--verbose"], calls)

    def test_validation_rejects_unbound_pair_before_formatter_or_loader_work(self):
        with tempfile.TemporaryDirectory() as tmp:
            compiler, frontend = identities()
            calls = []
            with self.assertRaisesRegex(support.WorkflowError, "different Trust source"):
                self.validate_fixture(tmp, compiler, frontend.replace(COMMIT, "unbound"), calls)
            self.assertEqual([Path(argv[0]).name for argv in calls], ["trustc", "trustc", "targo"])

    def native_data(self, seed, compiler=None, frontend=None):
        pair = identities()
        return {
            ("trustc", ("-vV",)): ((pair[0] if compiler is None else compiler).encode(), b""),
            ("trustc", ("--print", "sysroot")): (str(seed).encode(), b""),
            ("targo", ("--version", "--verbose")): ((pair[1] if frontend is None else frontend).encode(), b""),
            ("trustfmt", ("--version",)): (b"trustfmt 1.9.0-trust\n", b""),
        }

    def test_fixed_native_probe_data_uses_the_ordinary_semantics_without_a_process(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp) / "seed"
            seed.mkdir()
            with mock.patch.object(support.subprocess, "run") as process:
                result = support.native_seed_probe_data(seed, VERSION, HOST, self.native_data(seed))
            process.assert_not_called()
            self.assertEqual(result["native_tool_pair"], self.pair(*identities()))
            self.assertEqual(result["tool_versions"]["trustfmt"], "trustfmt 1.9.0-trust")
            self.assertEqual(set(result), {"native_tool_pair", "tool_versions"})

    def test_native_probe_data_refuses_missing_extra_nonbyte_and_truncated_populations(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp) / "seed"
            seed.mkdir()
            original = self.native_data(seed)
            for key in original:
                partial = dict(original)
                del partial[key]
                with self.assertRaisesRegex(support.WorkflowError, "exactly the four"):
                    support.native_seed_probe_data(seed, VERSION, HOST, partial)
            extra = dict(original)
            extra[("cargo", ("--version",))] = b"different invocation"
            with self.assertRaisesRegex(support.WorkflowError, "exactly the four"):
                support.native_seed_probe_data(seed, VERSION, HOST, extra)
            for invalid in ("text instead of original bytes", b"x" * (65536 + 1), b"\xff"):
                with self.subTest(invalid_type=type(invalid).__name__):
                    changed = dict(original)
                    changed[("trustfmt", ("--version",))] = (invalid, b"")
                    with self.assertRaises(support.WorkflowError):
                        support.native_seed_probe_data(seed, VERSION, HOST, changed)
            for incomplete in (b"stdout only", (b"stdout",), (b"stdout", b"", b"extra")):
                changed = dict(original)
                changed[("trustfmt", ("--version",))] = incomplete
                with self.assertRaisesRegex(support.WorkflowError, "both bounded original"):
                    support.native_seed_probe_data(seed, VERSION, HOST, changed)

    def test_native_probe_data_preserves_sysroot_and_pair_refusals(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp) / "seed"
            seed.mkdir()
            data = self.native_data(seed)
            data[("trustc", ("--print", "sysroot"))] = (str(Path(tmp)).encode(), b"")
            with self.assertRaisesRegex(support.WorkflowError, "escaped its installed sysroot"):
                support.native_seed_probe_data(seed, VERSION, HOST, data)
            data = self.native_data(seed, frontend=identities()[1].replace(COMMIT, "unbound"))
            with self.assertRaisesRegex(support.WorkflowError, "different Trust source"):
                support.native_seed_probe_data(seed, VERSION, HOST, data)

    def test_ordinary_validation_still_refuses_bad_host_before_any_later_probe(self):
        with tempfile.TemporaryDirectory() as tmp:
            compiler, frontend = identities()
            calls = []
            with self.assertRaisesRegex(support.WorkflowError, "host does not match"):
                self.validate_fixture(tmp, compiler.replace(HOST, "aarch64-apple-darwin"), frontend, calls)
            self.assertEqual([argv[1:] for argv in calls], [["-vV"]])

    def test_native_probe_data_cannot_hide_contradictory_identity_or_errors_on_stderr(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp) / "seed"
            seed.mkdir()
            key = ("trustc", ("-vV",))
            for stderr in (b"host: foreign-host\n", b"error: native probe failed\n", b"warning: retained\n"):
                data = self.native_data(seed)
                data[key] = (data[key][0], stderr)
                with self.assertRaisesRegex(support.WorkflowError, "stderr cannot be discarded"):
                    support.native_seed_probe_data(seed, VERSION, HOST, data)


if __name__ == "__main__":
    unittest.main()
