#!/usr/bin/env python3
"""Real-FS development producer binding controls, not a compiler/SDK/ABI proof."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import runpy
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from scripts.tests.python_floor_test import old_interpreter

SCRIPT = Path(__file__).parents[1] / "retain_development_emission.py"
spec = importlib.util.spec_from_file_location("retain_development", SCRIPT)
retain = importlib.util.module_from_spec(spec)
spec.loader.exec_module(retain)
SURFACE = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")))
HOST = "aarch64-apple-darwin"
OTHER = "x86_64-apple-darwin"


@unittest.skipUnless(os.name == "posix", "interpreter re-exec is POSIX")
class DevelopmentRetentionPythonFloorTests(unittest.TestCase):
    def setUp(self):
        self.old = old_interpreter()
        if self.old is None or sys.version_info < (3, 11):
            self.skipTest("requires actual older and current Python interpreters")

    def test_old_cli_reaches_current_python_and_preserves_isolation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            launcher = root / "python3.12"
            arguments = root / "arguments"
            poison = root / "poison"
            poison.mkdir()
            marker = root / "unexpected-site-startup"
            (poison / "sitecustomize.py").write_text(
                f"from pathlib import Path\nPath({str(marker)!r}).write_text('executed')\n"
            )
            launcher.write_text(
                "#!/bin/sh\n"
                'case " $* " in *" -c "*) ;;\n'
                f'*) printf \'%s\\n\' "$@" > {shlex.quote(str(arguments))} ;;\n'
                "esac\n"
                f'exec {shlex.quote(sys.executable)} "$@"\n'
            )
            launcher.chmod(0o755)
            # A named but incompatible interpreter must not capture the run.
            stale = root / "python3.14"
            stale.write_text("#!/bin/sh\nexit 1\n")
            stale.chmod(0o755)
            result = subprocess.run(
                [self.old, "-I", "-S", "-B", str(SCRIPT), "--help"],
                env={**os.environ, "PATH": str(root), "PYTHONPATH": str(poison)},
                text=True, capture_output=True, timeout=30,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("--emission-result", result.stdout)
            self.assertEqual(arguments.read_text().splitlines(),
                             ["-I", "-S", "-B", str(SCRIPT), "--help"])
            self.assertFalse(marker.exists(), "version probe executed sitecustomize")
            self.assertFalse((poison / "__pycache__").exists())

    def test_old_cli_without_compatible_interpreter_refuses(self):
        with tempfile.TemporaryDirectory() as temporary:
            result = subprocess.run(
                [self.old, "-I", "-B", str(SCRIPT), "--help"],
                env={**os.environ, "PATH": temporary},
                text=True, capture_output=True, timeout=30,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("none found on PATH", result.stderr)
            self.assertNotIn("usage:", result.stdout)


class DevelopmentRetentionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.base = Path(self.temp.name).resolve()
        self.root = self.base / "source"
        self.root.mkdir()
        self.addCleanup(self.temp.cleanup)
        self.config(False)

    def config(self, full):
        (self.root / "bootstrap.toml").write_text('[build]\nbuild="' + HOST + '"\nhost=["' + HOST + '"]\ntarget=["' + HOST + '","' + OTHER + '"]\nfull-bootstrap = ' + str(full).lower() + '\n')

    def file(self, name, data=b"current producer", executable=False):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)
        if executable:
            p.chmod(0o755)
        return p

    def request(self, *tail):
        return ["python3.14", str(self.root / "x.py"), *tail]

    def entries(self, role, target, fields):
        return retain.stamp_entries(self.root, HOST, target, role, b"\0".join(fields) + b"\0")

    def fixture(self, full=False):
        self.config(full)
        stage = 2 if full else 1
        prefix = f"build/{HOST}/stage2"
        self.file("scripts/recreate_bootstrap.py", b"# unit fixture supplies actual complete surface maps, not native execution\n")
        self.file("x.py", b"# native constructor path fixture, never executed\n")
        entry = self.file(f"build/{HOST}/stage2-rustc/{HOST}/release/rustc-main", b"compiler built by C1")
        for name in ["trustc", "rustc"]:
            self.file(prefix + "/bin/" + name, entry.read_bytes(), True)
        actual = SURFACE["expected_public_stage_tools"]()
        producers = SURFACE["stage_tool_producers_for"](actual)
        for public, producer in producers.items():
            data = ("C1 public tool " + producer).encode()
            self.file(f"build/{HOST}/stage3-tools-bin/{HOST}/{producer}", data)
            self.file(prefix + "/bin/" + public, data, True)
        self.file(prefix + "/bin/rustdoc", (self.root / prefix / "bin/trustdoc").read_bytes(), True)
        server = b"C1 analyzer server"
        self.file(f"build/{HOST}/stage3-tools-bin/{HOST}/rust-analyzer-proc-macro-srv", server)
        self.file(prefix + "/libexec/trust-analyzer-proc-macro-srv", server)
        lld = b"actual native LLD producer"
        self.file(f"build/{HOST}/lld/bin/lld", lld)
        self.file(prefix + "/bin/rust-lld", lld, True)
        self.file(prefix + f"/lib/rustlib/{HOST}/bin/rust-lld", lld, True)
        driver = self.file(f"build/{HOST}/stage2-rustc/{HOST}/release/deps/librustc_driver-current.dylib", b"C1 driver")
        metadata = self.file(f"build/{HOST}/stage2-rustc/{HOST}/release/deps/librustc_driver-current.rmeta", b"C1 split metadata")
        self.file(f"build/{HOST}/stage2-rustc/{HOST}/release/.librustc-stamp", b"t" + os.fsencode(driver) + b"\0t" + os.fsencode(metadata) + b"\0")
        for p in [driver, metadata]:
            self.file(prefix + f"/lib/rustlib/{HOST}/lib/" + p.name, p.read_bytes())
        self.file(prefix + "/lib/" + driver.name, driver.read_bytes())
        generations = {1, stage}
        for generation in generations:
            for target in ([HOST, OTHER] if generation == stage else [HOST]):
                fields = []
                for crate in ["core", "alloc", "std", "compiler_builtins", "test", "proc_macro", "trust_bignum"]:
                    name = f"lib{crate}-s{generation}-{target}.rlib"
                    p = self.file(f"build/{HOST}/stage{generation}-std/{target}/dist/deps/" + name, f"Std{generation} {target} {crate}".encode())
                    fields.append(b"t" + os.fsencode(p))
                    if generation == stage:
                        self.file(prefix + f"/lib/rustlib/{target}/lib/" + name, p.read_bytes())
                if target == HOST:
                    name = f"libstd-runtime-s{generation}.dylib"
                    p = self.file(f"build/{HOST}/stage{generation}-std/{target}/dist/deps/" + name, f"Std{generation} runtime".encode())
                    fields.append(b"t" + os.fsencode(p))
                    if generation == stage:
                        self.file(prefix + f"/lib/rustlib/{target}/lib/" + name, p.read_bytes())
                    if generation == 1:
                        self.file(prefix + "/lib/" + name, p.read_bytes())
                self.file(f"build/{HOST}/stage{generation}-std/{target}/dist/.libstd-stamp", b"\0".join(fields) + b"\0")
        row = {"path": ".", "commit": "a" * 40, "tree": "b" * 40, "tracked_status": ""}
        self.emission = {"exit": 0, "ended_unix": time.time(), "source_bookends_equal": True,
                         "selected_public_commit": "a" * 40, "source_before": [row], "source_after": [row],
                         "bootstrap.toml": {"sha256": retain.digest(self.root / "bootstrap.toml")},
                         "phases": [{"phase": "emission", "exit": 0,
                                     "argv": self.request("build", "--stage", "1", "--jobs", "2", "trustc-dev")}]}
        self.record = self.base / "emission.json"
        self.record.write_text(json.dumps(self.emission))
        lineage = {"status": "immutable_release", "errors": [], "repositories": [
            {"path": ".", "head": "a" * 40, "head_tree": "b" * 40}]}
        self.owner = {"capture_source_lineage": lambda _: lineage,
                      "expected_public_stage_tools": SURFACE["expected_public_stage_tools"],
                      "stage_tool_producers_for": SURFACE["stage_tool_producers_for"]}
        self.output = self.base / "capture"
        self.argv = ["--repo-root", str(self.root), "--emission-result", str(self.record), "--host", HOST,
                     "--target", HOST, "--target", OTHER, "--output", str(self.output)]
        return prefix

    def capture(self):
        with patch.object(retain.runpy, "run_path", return_value=self.owner), contextlib.redirect_stdout(io.StringIO()):
            result = retain.main(self.argv)
        return result, json.loads((self.output / "RESULT.json").read_text())

    def test_native_request_distinguishes_producer_from_output(self):
        for alias in ["trustc-dev", "rustc-dev"]:
            row = retain.native_request(self.root, self.request("build", "--stage", "1", alias))
            self.assertEqual((row["producer_stage"], row["output_stage"]), (1, 2))

    def test_no_stage2_dist_install_default_or_override_reinterpretation(self):
        for args in [("build", "--stage", "2", "trustc-dev"), ("dist", "--stage", "1", "trustc-dev"),
                     ("install", "--stage", "1", "trustc-dev"), ("build", "trustc-dev"),
                     ("build", "--stage", "1", "trustc-dev", "compiler"),
                     ("build", "--stage", "1", "trustc-dev", "--set", "build.full-bootstrap=true"),
                     ("build", "--stage", "1", "trustc-dev", "--dry-run")]:
            with self.subTest(args=args), self.assertRaises(retain.Refusal):
                retain.native_request(self.root, self.request(*args))

    def test_explicit_false_and_true_preserve_native_std_generations(self):
        for full, stage in [(False, 1), (True, 2)]:
            self.config(full)
            self.assertEqual(retain.configuration(self.root)["public_std_stage"], stage)

    def test_unset_nonbool_or_recursive_config_cannot_guess_generation(self):
        for content in ['[build]\n', '[build]\nfull-bootstrap=1\n', '[build]\nfull-bootstrap="false"\n',
                        'include=["unknown.toml"]\n[build]\nfull-bootstrap=false\n']:
            (self.root / "bootstrap.toml").write_text(content)
            with self.subTest(content=content), self.assertRaises(retain.Refusal):
                retain.configuration(self.root)

    def test_exact_c1_rustc_and_both_std_generation_namespaces(self):
        for role, family, stage in [("compiler1-rustc", "rustc", 2), ("compiler1-std", "std", 1), ("compiler2-std", "std", 2)]:
            profile = "release" if family == "rustc" else "dist"
            path = self.root / f"build/{HOST}/stage{stage}-{family}/{OTHER}/{profile}/deps/current.rmeta"
            row = self.entries(role, OTHER, [b"t" + os.fsencode(path)])[0]
            self.assertEqual(row["producer_role"], role)

    def test_old_compiler0_and_wrong_target_stamps_refuse(self):
        wrong = self.root / f"build/{HOST}/stage1-rustc/{HOST}/release/deps/old.rmeta"
        with self.assertRaises(retain.Refusal):
            self.entries("compiler1-rustc", HOST, [b"t" + os.fsencode(wrong)])
        wrong = self.root / f"build/{HOST}/stage2-std/{HOST}/dist/deps/other.rlib"
        with self.assertRaises(retain.Refusal):
            self.entries("compiler2-std", OTHER, [b"t" + os.fsencode(wrong)])

    def test_normal_uplift_capture_binds_all_actual_public_roles(self):
        self.fixture(False)
        code, result = self.capture()
        self.assertEqual(code, 0, result.get("error"))
        self.assertEqual((result["producer_stage"], result["output_stage"], result["public_std_stage"]), (1, 2, 1))
        self.assertFalse(result["verified"])
        self.assertFalse(result["release_ready"])
        self.assertFalse((self.output / "sdk").exists())
        self.assertTrue(any("stage3-tools-bin" in row["source_relative"] for row in result["files"]))
        self.assertFalse(any("stage2-tools-bin" in row["source_relative"] for row in result["files"]))

    def test_full_bootstrap_retains_std2_and_separate_std1_runtime(self):
        self.fixture(True)
        code, result = self.capture()
        self.assertEqual(code, 0, result.get("error"))
        self.assertEqual(result["public_std_stage"], 2)
        roles = {role["producer_role"] for row in result["files"] for role in row["roles"]}
        self.assertTrue({"compiler1-rustc", "compiler1-std", "compiler2-std"} <= roles)

    def test_missing_split_private_metadata_is_not_a_pass(self):
        prefix = self.fixture()
        (self.root / prefix / f"lib/rustlib/{HOST}/lib/librustc_driver-current.rmeta").unlink()
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("current compiler metadata", result["error"])

    def test_old_installed_driver_cannot_match_current_producer(self):
        prefix = self.fixture()
        (self.root / prefix / "lib/librustc_driver-current.dylib").write_bytes(b"compiler0 old driver")
        self.emission["ended_unix"] = time.time()
        self.record.write_text(json.dumps(self.emission))
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("unbound compiler1 runtime", result["error"])

    def test_same_named_old_tool_bin_is_not_a_producer(self):
        prefix = self.fixture()
        (self.root / prefix / "bin/targo").write_bytes(b"old C0 targo")
        self.emission["ended_unix"] = time.time()
        self.record.write_text(json.dumps(self.emission))
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("producer mismatch", result["error"])

    def test_missing_full_library_member_refuses(self):
        prefix = self.fixture()
        path = next((self.root / prefix / f"lib/rustlib/{OTHER}/lib").glob('libtest-*.rlib'))
        path.unlink()
        code, result = self.capture()
        self.assertEqual(code, 1)

    def test_unbound_installed_library_cannot_hide_in_prefix(self):
        prefix = self.fixture()
        self.file(prefix + f"/lib/rustlib/{HOST}/lib/libunclaimed-stale.rmeta", b"unbound old metadata")
        self.emission["ended_unix"] = time.time()
        self.record.write_text(json.dumps(self.emission))
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("unbound current", result["error"])

    def test_source_build_noindex_alias_stays_logical(self):
        self.fixture()
        (self.root / "build").rename(self.root / "build.noindex")
        (self.root / "build").symlink_to("build.noindex")
        code, result = self.capture()
        self.assertEqual(code, 0, result.get("error"))
        self.assertTrue(all(row["source_relative"].startswith("build/") and row["physical_source_relative"].startswith("build.noindex/") for row in result["files"]))


    def test_configured_target_population_cannot_be_reduced(self):
        self.fixture()
        index = self.argv.index(OTHER)
        del self.argv[index - 1:index + 1]
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("host/targets differ", result["error"])

    def test_declared_native_host_cannot_be_reinterpreted(self):
        self.fixture()
        self.argv[self.argv.index("--host") + 1] = OTHER
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("host/targets differ", result["error"])

    def test_late_image_mutation_still_refuses_before_byte_binding(self):
        prefix = self.fixture()
        p = self.root / prefix / "bin/targo"
        when = int(self.emission["ended_unix"] * 1e9) + 1_000_000
        os.utime(p, ns=(when, when))
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("after emission", result["error"])

    def test_staged_native_dev_receipt_does_not_authenticate_external_inputs(self):
        prefix = self.fixture()
        archive = self.file(prefix + f"/lib/rustlib/{HOST}/lib/libzstd.a", b"actual staged native archive")
        data = {"schema": "trust.llvm-static-native-dev.v1", "library": "zstd", "kind": "static",
                "sha256": retain.digest(archive), "source": "/unread/external/provider"}
        self.file(prefix + f"/lib/rustlib/{HOST}/lib/trust-llvm-native-dev.json", json.dumps(data).encode())
        self.emission["ended_unix"] = time.time()
        self.record.write_text(json.dumps(self.emission))
        code, result = self.capture()
        self.assertEqual(code, 0, result.get("error"))
        self.assertTrue(result["native_development_binding"]["present"])
        self.assertFalse(result["native_development_binding"]["external_input_or_provider_reauthenticated"])
        self.assertFalse(result["verified"])

    def test_native_archive_without_receipt_cannot_hide_as_std(self):
        prefix = self.fixture()
        self.file(prefix + f"/lib/rustlib/{HOST}/lib/libzstd.a", b"unbound native archive")
        self.emission["ended_unix"] = time.time()
        self.record.write_text(json.dumps(self.emission))
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("unbound current", result["error"])

    def test_complete_installed_linker_flavors_retain_the_current_wrapper(self):
        prefix = self.fixture()
        wrapper = self.file(f"build/{HOST}/stage3-tools-bin/{HOST}/lld-wrapper", b"current C1 wrapper")
        names = ("ld.lld", "ld64.lld", "lld-link", "wasm-ld")
        for name in names:
            self.file(prefix + f"/lib/rustlib/{HOST}/bin/gcc-ld/" + name, wrapper.read_bytes(), True)
        self.emission["ended_unix"] = time.time()
        self.record.write_text(json.dumps(self.emission))
        code, result = self.capture()
        self.assertEqual(code, 0, result.get("error"))
        files = {row["source_relative"]: row for row in result["files"]}
        for name in names:
            installed = prefix + f"/lib/rustlib/{HOST}/bin/gcc-ld/" + name
            self.assertTrue(installed in files, "installed linker flavor lacks retained provenance: " + installed)
            self.assertEqual(files[installed]["sha256"], retain.digest(wrapper))
        self.assertIn(wrapper.relative_to(self.root).as_posix(), files)

    def refresh_emission(self):
        self.emission["bootstrap.toml"]["sha256"] = retain.digest(self.root / "bootstrap.toml")
        self.emission["ended_unix"] = time.time()
        self.record.write_text(json.dumps(self.emission))

    def native_llvm_fixture(self):
        prefix = self.fixture()
        provider = self.base / "declared-native-llvm"
        binaries = provider / "bin"
        binaries.mkdir(parents=True)
        config = binaries / "llvm-config"
        config.write_text("#!/bin/sh\nprintf '%s\\n' " + shlex.quote(str(binaries)) + "\n")
        config.chmod(0o755)
        (self.root / "bootstrap.toml").write_text((self.root / "bootstrap.toml").read_text()
            + f'\n[target.{HOST}]\nllvm-config = {json.dumps(str(config))}\n')
        for name in ("llvm-ar", "llvm-objcopy"):
            source = binaries / name
            source.write_bytes(("actual declared LLVM " + name).encode())
            self.file(prefix + f"/lib/rustlib/{HOST}/bin/" + name, source.read_bytes(), True)
        (binaries / "llvm-strip").symlink_to("llvm-objcopy")
        for name in ("rust-objcopy", "llvm-strip"):
            self.file(prefix + f"/lib/rustlib/{HOST}/bin/" + name, (binaries / "llvm-objcopy").read_bytes(), True)
        self.refresh_emission()
        return prefix, provider

    def test_installed_linker_cannot_borrow_the_native_lld_bytes(self):
        prefix = self.fixture()
        self.file(f"build/{HOST}/stage3-tools-bin/{HOST}/lld-wrapper", b"actual wrapper")
        for name in retain.LLD_FLAVORS:
            self.file(prefix + f"/lib/rustlib/{HOST}/bin/gcc-ld/" + name, b"wrong native LLD body", True)
        self.refresh_emission()
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("installed producer mismatch", result["error"])

    def test_partial_linker_flavor_population_is_refused(self):
        prefix = self.fixture()
        self.file(prefix + f"/lib/rustlib/{HOST}/bin/gcc-ld/ld.lld", b"one wrapper")
        self.refresh_emission()
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("linker flavor population differs", result["error"])

    def test_unknown_installed_native_tool_is_refused(self):
        prefix = self.fixture()
        self.file(prefix + f"/lib/rustlib/{HOST}/bin/unbound-native-tool", b"unbound executable", True)
        self.refresh_emission()
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("unknown installed native tool", result["error"])

    def test_declared_llvm_tools_and_resolved_aliases_are_retained(self):
        prefix, provider = self.native_llvm_fixture()
        code, result = self.capture()
        self.assertEqual(code, 0, result.get("error"))
        native = result["native_llvm_tool_inputs"]
        self.assertEqual(native["selection"]["root"], str(provider))
        self.assertEqual(len(native["selection"]["bindings"]), 4)
        self.assertEqual(len(native["files"]), 2)
        self.assertFalse(native["original_provider_build_authority"])
        self.assertTrue(any(row["alias"] == "llvm-objcopy" for row in native["selection"]["bindings"]))
        for row in native["files"]:
            retained = self.output / native["retained_directory"] / row["source_relative"]
            self.assertEqual(retained.read_bytes(), (provider / row["source_relative"]).read_bytes())

    def test_installed_llvm_mutant_is_refused(self):
        prefix, _ = self.native_llvm_fixture()
        self.file(prefix + f"/lib/rustlib/{HOST}/bin/llvm-ar", b"different LLVM provider", True)
        self.refresh_emission()
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("differs from selected provider", result["error"])

    def test_external_llvm_tool_alias_cannot_escape_its_provider(self):
        _, provider = self.native_llvm_fixture()
        outsider = self.base / "outside-tool"
        outsider.write_bytes(b"outside provider")
        (provider / "bin/llvm-strip").unlink()
        (provider / "bin/llvm-strip").symlink_to(outsider)
        self.refresh_emission()
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("alias escapes selected provider", result["error"])

    def test_post_emission_external_llvm_replacement_is_refused(self):
        _, provider = self.native_llvm_fixture()
        when = int(self.emission["ended_unix"] * 1e9) + 1_000_000_000
        os.utime(provider / "bin/llvm-ar", ns=(when, when))
        code, result = self.capture()
        self.assertEqual(code, 1)
        self.assertIn("after emission", result["error"])

    def test_llvm_alias_is_bound_by_observed_runtime_name(self):
        prefix = self.fixture()
        producer = self.file(f"build/{HOST}/llvm/lib/libLLVM-current.dylib", b"declared in-tree LLVM runtime")
        producer.with_name("libLLVM.dylib").symlink_to(producer.name)
        self.file(prefix + "/lib/libLLVM.dylib", producer.read_bytes())
        self.emission["ended_unix"] = time.time()
        self.record.write_text(json.dumps(self.emission))
        code, result = self.capture()
        self.assertEqual(code, 0, result.get("error"))
        self.assertTrue(any(row["link"] for row in result["native_runtime_aliases"]))


if __name__ == "__main__":
    unittest.main()
