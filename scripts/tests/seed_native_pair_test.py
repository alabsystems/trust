#!/usr/bin/env python3
"""Native seed pair identity controls; all process probes are inert stand-ins."""
from __future__ import annotations

import hashlib
import importlib.util
import re
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
SOURCE_SPEC = importlib.util.spec_from_file_location("seed_pair_custody", ROOT / "scripts/seed_custody_source.py")
assert SOURCE_SPEC and SOURCE_SPEC.loader
custody = importlib.util.module_from_spec(SOURCE_SPEC)
SOURCE_SPEC.loader.exec_module(custody)
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

    def test_repeated_freshness_capabilities_do_not_change_native_pair_identity(self):
        # The shape every Targo has printed since 2026-11-10 (a243bae0a2): two
        # freshness lines. Refusing it stopped the da63c88b7b cut after its DDC.
        compiler, frontend = identities()
        capabilities = (
            "\nfreshness: rust-and-build-input-content-v1"
            "\nfreshness: compiler-filename-inventory-v1"
            "\ncache-integrity: build-script-control-output-v1"
            "\ncache-integrity: compiled-build-script-executable-v1"
        )
        self.assertEqual(self.pair(compiler, frontend + capabilities),
                         self.pair(compiler, frontend))

    def test_every_key_targo_repeats_is_a_named_repeatable_capability(self):
        cli = (ROOT / "src/tools/targo/src/bin/cargo/cli.rs").read_text(encoding="utf-8")
        start = cli.index('if cargo_binary_name() != "cargo" {')
        block = cli[start:cli.index("\n        }\n", start)]
        keys = re.findall(r'version_string\.push_str\("([a-z0-9-]+): ', block)
        repeated = {key for key in keys if keys.count(key) > 1}
        self.assertTrue(repeated, "no repeated Targo capability key found; update this reader")
        self.assertLessEqual(repeated, support.TARGO_REPEATABLE_CAPABILITIES)
        identity = {"trust", "commit-hash", "trust-repo-commit-hash", "host", "release"}
        self.assertFalse(support.TARGO_REPEATABLE_CAPABILITIES & identity)

    def test_repeatable_capabilities_cannot_hide_missing_or_duplicate_identity(self):
        compiler, frontend = identities()
        frontend += (
            "\nfreshness: rust-and-build-input-content-v1"
            "\nfreshness: compiler-filename-inventory-v1"
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

    def seed_fixture(self, tmp):
        seed = Path(tmp) / "seed"
        (seed / "bin").mkdir(parents=True)
        for name in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt"):
            path = seed / "bin" / name
            path.write_bytes(("inert fixture " + name).encode())
            path.chmod(0o700)
        return seed

    def validate_fixture(self, tmp, compiler, frontend, calls=None):
        seed = self.seed_fixture(tmp)
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

    def test_static_data_uses_all_six_entrypoints_without_runtime_or_identity_probes(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = self.seed_fixture(tmp)
            with mock.patch.object(support.platform, "system", return_value="Linux"), \
                    mock.patch.object(support, "foreign_load_commands",
                                      side_effect=AssertionError("runtime closure is separate")) as inspect, \
                    mock.patch.object(support.subprocess, "run") as process:
                data = support.seed_static_data(seed)
            inspect.assert_not_called()
            process.assert_not_called()
            self.assertEqual(set(data), {"entrypoint_sha256"})
            self.assertEqual(set(data["entrypoint_sha256"]),
                             {"trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt"})
            # Compatible aliases retain the same ordinary byte identity.
            for alias, target in (("rustc", "trustc"), ("cargo", "targo")):
                (seed / "bin" / alias).unlink()
                (seed / "bin" / alias).symlink_to(target)
            with mock.patch.object(support.platform, "system", return_value="Darwin"):
                aliases = support.seed_static_data(seed)
            self.assertEqual(aliases["entrypoint_sha256"]["cargo"], data["entrypoint_sha256"]["targo"])

    def test_static_data_refuses_missing_nonexecutable_escaped_or_broken_surface(self):
        for missing in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt"):
            with self.subTest(missing=missing), tempfile.TemporaryDirectory() as tmp:
                seed = self.seed_fixture(tmp)
                (seed / "bin" / missing).unlink()
                with self.assertRaisesRegex(support.WorkflowError, "missing required entrypoint"):
                    support.seed_static_data(seed)
        for fault in ("nonexecutable", "entrypoint-escape", "extra-link-escape", "broken-link"):
            with self.subTest(fault=fault), tempfile.TemporaryDirectory() as tmp:
                seed = self.seed_fixture(tmp)
                if fault == "nonexecutable":
                    (seed / "bin/trustfmt").chmod(0o600)
                else:
                    outside = Path(tmp) / "outside"
                    outside.write_bytes(b"unadmitted target")
                    outside.chmod(0o700)
                    link = seed / ("bin/trustfmt" if fault == "entrypoint-escape" else "extra")
                    if link.exists():
                        link.unlink()
                    link.symlink_to("absent" if fault == "broken-link" else outside)
                with self.assertRaises(support.WorkflowError):
                    support.seed_static_data(seed)

    def captured_loader(self, tmp):
        root = (Path(tmp) / "source").resolve()
        captures = {}
        for name in ("scripts/seed_custody_source.py", "scripts/mint_seed_support.py",
                     "src/bootstrap/stage0_identity.py"):
            raw = (ROOT / name).read_bytes()
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
            captures[name] = raw
        expected = {name: hashlib.sha256(raw).hexdigest() for name, raw in captures.items()}
        return custody.BoundSourceLoader(root, expected, captured_sources=captures)

    def test_captured_static_and_probe_data_reuses_canonical_checks_without_processes(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = self.seed_fixture(tmp)
            loader = self.captured_loader(tmp)
            with mock.patch("platform.system", return_value="Darwin"), \
                    mock.patch("subprocess.run") as process, \
                    mock.patch.object(custody.time, "monotonic", return_value=10):
                data = loader.seed_static_probe_data_from_capture(
                    seed, VERSION, HOST, self.native_data(seed), deadline=12)
            process.assert_not_called()
            self.assertEqual(set(data), {"entrypoint_sha256", "native_tool_pair", "tool_versions"})
            self.assertEqual(len(data["entrypoint_sha256"]), 6)
            self.assertEqual(data["native_tool_pair"], self.pair(*identities()))

    def test_captured_seed_data_preserves_missing_surface_without_loader_execution(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = self.seed_fixture(tmp)
            loader = self.captured_loader(tmp)
            helper = loader.module("seed_static_hostile", loader.root / "scripts/mint_seed_support.py")
            with mock.patch.object(custody.time, "monotonic", return_value=10), \
                    mock.patch.object(helper.platform, "system", return_value="Linux"), \
                    mock.patch.object(helper, "foreign_load_commands",
                                      side_effect=AssertionError("no loader closure in partial DATA")):
                data = loader.seed_static_probe_data_from_capture(
                    seed, VERSION, HOST, self.native_data(seed), deadline=12)
            self.assertNotIn("linux_runtime_closure", data)
            (seed / "bin/cargo").unlink()
            with mock.patch.object(custody.time, "monotonic", return_value=10):
                with self.assertRaisesRegex(helper.WorkflowError, "missing required entrypoint cargo"):
                    loader.seed_static_probe_data_from_capture(
                        seed, VERSION, HOST, self.native_data(seed), deadline=12)

    def test_captured_seed_data_refuses_missing_capture_and_original_endpoint_loss(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = self.seed_fixture(tmp)
            loader = self.captured_loader(tmp)
            uncaptured = custody.BoundSourceLoader(loader.root, loader.expected)
            with self.assertRaisesRegex(ValueError, "complete fixed captured graph"):
                uncaptured.seed_static_probe_data_from_capture(seed, VERSION, HOST, {}, deadline=12)
            for clock in ([12], [10, 10, 12]):
                with self.subTest(clock=clock), \
                        mock.patch("platform.system", return_value="Darwin"), \
                        mock.patch.object(custody.time, "monotonic", side_effect=clock):
                    with self.assertRaisesRegex(ValueError, "endpoint"):
                        loader.seed_static_probe_data_from_capture(
                            seed, VERSION, HOST, self.native_data(seed), deadline=12)

    def test_captured_seed_data_rechecks_source_after_ordinary_parser(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = self.seed_fixture(tmp)
            loader = self.captured_loader(tmp)
            path = loader.root / "scripts/mint_seed_support.py"
            helper = loader.module("seed_static_drift", path)
            original = helper.native_seed_probe_data

            def changed(*args):
                result = original(*args)
                path.write_bytes(path.read_bytes() + b"\n# changed during validation\n")
                return result

            with mock.patch("platform.system", return_value="Darwin"), \
                    mock.patch.object(custody.time, "monotonic", return_value=10), \
                    mock.patch.object(helper, "native_seed_probe_data", side_effect=changed):
                with self.assertRaisesRegex(ValueError, "executed source changed"):
                    loader.seed_static_probe_data_from_capture(
                        seed, VERSION, HOST, self.native_data(seed), deadline=12)

    def test_ordinary_validator_keeps_all_original_probes_then_loader_then_fingerprint(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = self.seed_fixture(tmp)
            outputs = self.native_data(seed)
            calls = []

            def run(argv, **kwargs):
                self.assertEqual(kwargs["timeout"], 30)
                calls.append((Path(argv[0]).name, tuple(argv[1:])))
                if argv[0] == "/fixture/otool":
                    return SimpleNamespace(returncode=0, stdout="ordinary loader DATA")
                raw, _ = outputs[(Path(argv[0]).name, tuple(argv[1:]))]
                return SimpleNamespace(returncode=0, stdout=raw.decode())

            fingerprint = support.seed_tree_fingerprint

            def final_tree(path):
                calls.append("final fingerprint")
                return fingerprint(path)

            with mock.patch.object(support.platform, "system", return_value="Darwin"), \
                    mock.patch.object(support.shutil, "which", return_value="/fixture/otool"), \
                    mock.patch.object(support.subprocess, "run", side_effect=run), \
                    mock.patch.object(support, "seed_tree_fingerprint", side_effect=final_tree):
                result = support.validate_seed(seed, VERSION, HOST)
            self.assertEqual(calls, [
                *outputs,
                ("otool", ("-L", str(seed / "bin/trustc"))),
                ("otool", ("-L", str(seed / "bin/targo"))),
                ("otool", ("-L", str(seed / "bin/trustfmt"))),
                "final fingerprint",
            ])
            self.assertEqual(len(result["loader_evidence"]), 3)
            self.assertEqual(result["tree"], fingerprint(seed))

    def test_captured_whole_surface_equals_the_ordinary_darwin_caller(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = self.seed_fixture(tmp)
            host = "aarch64-apple-darwin"
            outputs = self.native_data(seed, *identities(host=host))
            loader_outputs = {name: (
                f"{seed}/bin/{name}:\n /usr/lib/libSystem.B.dylib\n".encode(), b"")
                for name in ("trustc", "targo", "trustfmt")}

            def run(argv, **kwargs):
                self.assertEqual(kwargs["timeout"], 30)
                self.assertEqual(kwargs["env"]["LC_ALL"], "C")
                self.assertEqual(kwargs["env"]["LANG"], "C")
                raw, _ = (loader_outputs[Path(argv[-1]).name] if argv[0] == "/fixture/otool"
                          else outputs[(Path(argv[0]).name, tuple(argv[1:]))])
                return SimpleNamespace(returncode=0, stdout=raw.decode())

            loader = self.captured_loader(tmp)
            with mock.patch("platform.system", return_value="Darwin"), \
                    mock.patch("shutil.which", return_value="/fixture/otool"):
                with mock.patch.object(support.subprocess, "run", side_effect=run):
                    ordinary = support.validate_seed(seed, VERSION, host)
                with mock.patch("subprocess.run", side_effect=AssertionError("DATA executes nothing")), \
                        mock.patch.object(custody.time, "monotonic", return_value=10):
                    plan = loader.seed_loader_plan_from_capture(deadline=12)
                    captured = loader.seed_surface_data_from_capture(
                        seed, VERSION, host, outputs, plan["loader"], loader_outputs, deadline=12)
            self.assertEqual(plan, {"loader": "/fixture/otool",
                                    "programs": ["trustc", "targo", "trustfmt"]})
            self.assertEqual(captured, ordinary)
            self.assertEqual(captured["tree"], support.seed_tree_fingerprint(seed))
            self.assertNotIn(str(seed), str(captured["loader_evidence"]))

    def test_native_loader_absence_is_explicit_and_linux_cannot_skip_elf_checks(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = self.seed_fixture(tmp)
            with mock.patch.object(support.platform, "system", return_value="Darwin"), \
                    mock.patch.object(support.shutil, "which", return_value=None), \
                    mock.patch.object(support.subprocess, "run") as process:
                self.assertEqual(support.native_seed_loader_plan(), {"loader": None, "programs": []})
                data = support.native_seed_surface_data(
                    seed, VERSION, HOST, self.native_data(seed), None, {})
                self.assertEqual(data["loader_evidence"], {})
                with self.assertRaisesRegex(support.WorkflowError, "complete original population"):
                    support.native_seed_surface_data(seed, VERSION, HOST, self.native_data(seed),
                                                     None, {"trustc": (b"extra", b"")})
                process.assert_not_called()
            with mock.patch.object(support.platform, "system", return_value="Linux"), \
                    mock.patch.object(support, "foreign_load_commands") as elf:
                with self.assertRaisesRegex(support.WorkflowError, "only Darwin"):
                    support.native_seed_surface_data(seed, VERSION, HOST, {}, None, {})
                elf.assert_not_called()

    def test_native_whole_surface_refuses_missing_changed_or_contradictory_loader_data(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = self.seed_fixture(tmp)
            observations = {name: (b"ordinary loader data", b"")
                            for name in ("trustc", "targo", "trustfmt")}
            faults = []
            for name in observations:
                missing = dict(observations)
                del missing[name]
                faults.append(("/fixture/otool", missing))
                for streams in [(b"ok", b"contradiction"), (b"\xff", b""),
                                (b"x" * (64 * 1024 + 1), b""),
                                (b"/forbidden/.RUSTUP/toolchain", b""),
                                (b"C:\\GENESIS-STAGE0\\bin", b"")]:
                    changed = dict(observations)
                    changed[name] = streams
                    faults.append(("/fixture/otool", changed))
            faults += [(None, observations), ("/changed/otool", observations),
                       (True, observations), ("/fixture/otool", observations | {"cargo": (b"extra", b"")})]
            with mock.patch.object(support.platform, "system", return_value="Darwin"), \
                    mock.patch.object(support.shutil, "which", return_value="/fixture/otool"), \
                    mock.patch.object(support.subprocess, "run") as process:
                for selected, changed in faults:
                    with self.subTest(selected=selected, keys=list(changed)):
                        with self.assertRaises(support.WorkflowError):
                            support.native_seed_surface_data(seed, VERSION, HOST,
                                self.native_data(seed), selected, changed)
                process.assert_not_called()

    def test_new_surface_entries_recheck_all_three_captured_files_before_use(self):
        for relative in ("scripts/seed_custody_source.py", "scripts/mint_seed_support.py",
                         "src/bootstrap/stage0_identity.py"):
            for route in ("plan", "surface"):
                with self.subTest(relative=relative, route=route), tempfile.TemporaryDirectory() as tmp:
                    seed = self.seed_fixture(tmp)
                    loader = self.captured_loader(tmp)
                    path = loader.root / relative
                    path.write_bytes(path.read_bytes() + b"\n# changed original capture\n")
                    with mock.patch.object(custody.time, "monotonic", return_value=10), \
                            mock.patch("platform.system", return_value="Darwin"), \
                            mock.patch("shutil.which", return_value=None):
                        with self.assertRaisesRegex(ValueError, "original seed surface source changed"):
                            if route == "plan":
                                loader.seed_loader_plan_from_capture(deadline=12)
                            else:
                                loader.seed_surface_data_from_capture(seed, VERSION, HOST,
                                                                      self.native_data(seed), None, {},
                                                                      deadline=12)

    def test_surface_postcheck_catches_unexecuted_entry_drift_and_keeps_semantic_error_context(self):
        for failing in (False, True):
            with self.subTest(failing=failing), tempfile.TemporaryDirectory() as tmp:
                loader = self.captured_loader(tmp)
                helper = loader.module("surface_postcheck", loader.root / "scripts/mint_seed_support.py")
                entry = loader.root / "scripts/seed_custody_source.py"

                def plan():
                    entry.write_bytes(entry.read_bytes() + b"\n# loader entry changed during call\n")
                    if failing:
                        raise helper.WorkflowError("original semantic refusal")
                    return {"loader": None, "programs": []}

                with mock.patch.object(custody.time, "monotonic", return_value=10), \
                        mock.patch.object(helper, "native_seed_loader_plan", side_effect=plan):
                    with self.assertRaises(Exception) as raised:
                        loader.seed_loader_plan_from_capture(deadline=12)
                self.assertIsInstance(raised.exception, ValueError)
                self.assertIn("original seed surface source changed", str(raised.exception))
                if failing:
                    self.assertIsInstance(raised.exception.__context__, helper.WorkflowError)
                    self.assertIn("original semantic refusal", str(raised.exception.__context__))

    def test_surface_entries_preserve_original_endpoint_after_the_helper_returns(self):
        for route in ("plan", "surface"):
            with self.subTest(route=route), tempfile.TemporaryDirectory() as tmp:
                seed = self.seed_fixture(tmp)
                loader = self.captured_loader(tmp)
                helper = loader.module("surface_expired", loader.root / "scripts/mint_seed_support.py")
                clock = [10]

                def expired(*args):
                    clock[0] = 12
                    return {"data": "cannot escape the expired original endpoint"}

                method = "native_seed_loader_plan" if route == "plan" else "native_seed_surface_data"
                with mock.patch.object(custody.time, "monotonic", side_effect=lambda: clock[0]), \
                        mock.patch.object(helper, method, side_effect=expired):
                    with self.assertRaisesRegex(ValueError, "original endpoint expired"):
                        if route == "plan":
                            loader.seed_loader_plan_from_capture(deadline=12)
                        else:
                            loader.seed_surface_data_from_capture(seed, VERSION, HOST, {}, None, {}, deadline=12)


if __name__ == "__main__":
    unittest.main()
