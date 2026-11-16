"""Producer-input tests; real children are Python-only transport fixtures."""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import recreate_bootstrap as bootstrap
SPEC = importlib.util.spec_from_file_location("bootstrap_xpy", SCRIPTS / "bootstrap_xpy.py")
bootstrap_xpy = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bootstrap_xpy)
import mint_seed_support as mint
from mint_clean_lean_inputs_test import fixture


class BootstrapXpyEnvironmentTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.library = fixture(self.root)
        (self.root / "bootstrap.toml").write_text(
            "# (seed stage0 mode)\n[build]\n[rust]\ntrust-source-identity = false\n")
        self.selection = self.select(self.library, "inputs.json")
        self.calls = []

    def select(self, library, name):
        manifest = self.root / name
        manifest.write_text(json.dumps(mint.clean_lean_inputs(self.root, library), sort_keys=True))
        return bootstrap.CleanLeanSelection(
            manifest, library, hashlib.sha256(manifest.read_bytes()).hexdigest(),
        )

    def options(self, selection=None):
        selection = selection or self.selection
        return ["--clean-lean-manifest", str(selection.manifest),
                "--clean-lean-lib", str(selection.library),
                "--clean-lean-manifest-sha256", selection.sha256]

    def child(self, command, *, env, cwd):
        self.calls.append((command, dict(env), cwd))
        return SimpleNamespace(returncode=0)

    def config_identity(self):
        config = self.root / "bootstrap.toml"
        return bootstrap.WrittenBootstrapConfig(config, hashlib.sha256(config.read_bytes()).hexdigest())

    def contexts(self, environment=None):
        from contextlib import ExitStack
        stack = ExitStack()
        stack.enter_context(patch.dict(os.environ, environment or {}, clear=True))
        stack.enter_context(patch.object(bootstrap, "add_homebrew_library_path"))
        stack.enter_context(patch.object(bootstrap, "seed_verification_off_switch", return_value="flag"))
        stack.enter_context(patch.object(bootstrap.subprocess, "run", side_effect=self.child))
        return stack

    def test_recreator_build_and_normal_test_receive_the_same_bound_environment(self):
        ambient = {**self.selection.environment(self.root),
                   "BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "6",
                   "RUSTFLAGS": "hostile", "RUSTC": "/unselected/compiler",
                   "CARGOFLAGS": "-Zgit=shallow-deps",
                   "CARGOFLAGS_BOOTSTRAP": "--config injected.toml",
                   "CARGO_TARGET_TEST_RUSTFLAGS": "hostile", "UNRELATED": "kept"}
        with self.contexts(ambient), patch.object(bootstrap, "repo_root", return_value=self.root):
            self.assertEqual(bootstrap.run_xpy_build(
                self.root, "test-host", 1, 6, ["compiler/rustc", "library/std"],
                seed_mode=True, clean_lean=self.selection), 0)
            self.assertEqual(bootstrap_xpy.main([
                "--host", "test-host", "--stage", "1", "-j", "6", *self.options(),
                "test", "-vv", "--test-args=--help", "tests/run-make"]), 0)
        build, support = self.calls
        self.assertEqual(build[1], support[1])
        self.assertNotIn("CARGOFLAGS", support[1])
        self.assertNotIn("CARGOFLAGS_BOOTSTRAP", support[1])
        self.assertEqual(build[0][2], "build")
        self.assertEqual(support[0][2], "test")
        self.assertEqual(build[1]["CLEAN_OLEAN_PINNED_LEAN_LIB"], str(self.library))
        self.assertEqual(build[1]["CLEAN_OLEAN_REQUIRE_PINNED_LEAN"], "1")
        self.assertEqual(build[1]["CARGO_BUILD_JOBS"], "6")
        self.assertEqual(build[1]["CARGO_HOME"], str(self.root / "build/bootstrap-cargo-home"))
        self.assertEqual(build[1]["RUSTFLAGS_BOOTSTRAP"], bootstrap.BOOTSTRAP_COMPILER_VERIFICATION["flag"])
        for key in ("RUSTFLAGS", "RUSTC", "CARGO_TARGET_TEST_RUSTFLAGS"):
            self.assertNotIn(key, build[1])
        self.assertEqual(build[1]["UNRELATED"], "kept")

    def test_explicit_manager_reaches_xpy_without_becoming_compiler_authority(self):
        manager = "/explicit/physical/manager"
        ambient = {"TRUST_BUILD_TREE_MANAGER_TARGO": manager,
                   "RUSTC": "/unselected/compiler", "RUSTFLAGS": "hostile"}
        with self.contexts(ambient):
            self.assertEqual(bootstrap.run_xpy_build(
                self.root, "test-host", 1, 6, ["compiler/rustc"], seed_mode=True), 0)
        child = self.calls[0][1]
        self.assertEqual(child["TRUST_BUILD_TREE_MANAGER_TARGO"], manager)
        self.assertNotIn("RUSTC", child)
        self.assertNotIn("RUSTFLAGS", child)
        # This does not expand strict provenance's ambient-authority allowlist.
        self.assertIn("TRUST_BUILD_TREE_MANAGER_TARGO",
                      bootstrap._ambient_build_authority_overrides(ambient))

    @unittest.skipIf(sys.platform == "win32", "POSIX descriptor transport")
    def test_actual_python_child_keeps_matching_resource_values_and_live_descriptors(self):
        reader, writer = os.pipe()
        unrelated, unrelated_writer = os.pipe()
        self.addCleanup(os.close, reader)
        self.addCleanup(os.close, writer)
        self.addCleanup(os.close, unrelated)
        self.addCleanup(os.close, unrelated_writer)
        os.set_inheritable(unrelated, True)
        output = self.root / "observed-resource-transport.json"
        (self.root / "x.py").write_text(
            "import json,os\nfrom pathlib import Path\n"
            "names=json.loads(os.environ['PROBE_NAMES'])\n"
            "observed={name:os.environ[name] for name in names}\n"
            "observed['identities']={fd:[os.fstat(int(fd)).st_dev,os.fstat(int(fd)).st_ino] "
            "for fd in json.loads(os.environ['PROBE_FDS'])}\n"
            "try: os.fstat(int(os.environ['PROBE_UNRELATED_FD']))\n"
            "except OSError: observed['unrelated_closed']=True\n"
            "else: observed['unrelated_closed']=False\n"
            "observed['authority_scrubbed']=not any(name in os.environ for name in "
            "('RUSTC','RUSTFLAGS','TRUST_NO_VERIFY','CARGO_BUILD_RUSTC','SDKROOT','DEVELOPER_DIR'))\n"
            "Path(os.environ['PROBE_OUTPUT']).write_text(json.dumps(observed))\n"
        )
        for fixed in (str(reader), "requires-live-ancestor-v1"):
            with self.subTest(fixed=fixed):
                transport = {
                    "ATERM_SDK_LEASE_V3": str(reader),
                    "ATERM_WORKLOAD_HOST_STORE_FD_V1": str(reader),
                    "ATERM_WORKLOAD_CPU_FDS_V1": f"{reader},{writer}",
                    "BUILD_SLOT_FENCE_FDS": str(reader),
                    "TRUST_CPU_IMPLICIT_FD": str(reader),
                    "TRUST_CPU_HANDOFF": "opaque-original-python-fixture-data",
                    "TRUST_FIXED_ADMISSION_FD_V1": fixed,
                    "TRUST_FIXED_CLAIM_HANDOFF_V1": "opaque-original-fixed-fixture-data",
                    "CARGO_MAKEFLAGS": f"-j --jobserver-auth={reader},{writer}",
                    "CARGO_JOBSERVER_HANDOFF": "opaque-original-descendant-fixture-data",
                    # A present CARGO_MAKEFLAGS takes precedence; neither lower
                    # advertisement may be inspected or substituted for it.
                    "MAKEFLAGS": "--jobserver-auth=ignored,lower-priority",
                    "MFLAGS": "--jobserver-fds=also,ignored",
                }
                environment = {
                    **transport, "BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "1",
                    "PROBE_NAMES": json.dumps(list(transport)),
                    "PROBE_FDS": json.dumps([str(reader), str(writer)]),
                    "PROBE_UNRELATED_FD": str(unrelated), "PROBE_OUTPUT": str(output),
                    "RUSTC": "/unselected/compiler", "RUSTFLAGS": "hostile",
                    "TRUST_NO_VERIFY": "unselected", "CARGO_BUILD_RUSTC": "/other/compiler",
                    "SDKROOT": "/unselected/sdk", "DEVELOPER_DIR": "/unselected/developer",
                }
                with patch.dict(os.environ, environment, clear=True), \
                        patch.object(bootstrap, "add_homebrew_library_path"), \
                        patch.object(bootstrap, "seed_verification_off_switch", return_value="flag"):
                    self.assertEqual(bootstrap.run_xpy_build(
                        self.root, "test-host", 1, 1, [], seed_mode=True,
                        clean_lean=self.selection, normal_config=self.config_identity()), 0)
                observed = json.loads(output.read_text())
                self.assertEqual({name: observed[name] for name in transport}, transport)
                self.assertEqual(observed["identities"], {
                    str(fd): [os.fstat(fd).st_dev, os.fstat(fd).st_ino] for fd in (reader, writer)})
                self.assertTrue(observed["unrelated_closed"])
                self.assertTrue(observed["authority_scrubbed"])
                # Normal resource forwarding does not relax Stage2 provenance.
                self.assertTrue(set(transport) & set(
                    bootstrap._ambient_build_authority_overrides(environment)))

    def test_malformed_or_closed_resource_locators_refuse_before_child(self):
        reader, writer = os.pipe()
        os.close(reader)
        os.close(writer)
        cases = [
            {"TRUST_CPU_IMPLICIT_FD": str(reader)},
            {"TRUST_FIXED_ADMISSION_FD_V1": "not-a-descriptor"},
            {"TRUST_FIXED_ADMISSION_FD_V1": "requires-live-ancestor-v1"},
            {"TRUST_FIXED_ADMISSION_FD_V1": "requires-live-ancestor-v1",
             "TRUST_FIXED_CLAIM_HANDOFF_V1": ""},
            {"CARGO_MAKEFLAGS": "--jobserver-auth=malformed"},
            {"BUILD_SLOT_FENCE_FDS": "3,3"},
            {"ATERM_SDK_LEASE_V3": "not-a-descriptor"},
        ]
        for environment in cases:
            with self.subTest(environment=environment), self.contexts(environment):
                with self.assertRaisesRegex(RuntimeError, "row custody"):
                    bootstrap.run_xpy_build(self.root, "test-host", 1, 1, [], seed_mode=True)
        self.assertEqual(self.calls, [])

    def test_selected_gnu_advertisement_does_not_resurrect_lower_priority_flags(self):
        environment = {"CARGO_MAKEFLAGS": "", "MAKEFLAGS": "--jobserver-auth=malformed"}
        with self.contexts(environment):
            self.assertEqual(bootstrap.run_xpy_build(
                self.root, "test-host", 1, 1, [], seed_mode=True), 0)
        self.assertEqual(self.calls[0][1]["CARGO_MAKEFLAGS"], "")
        self.assertEqual(self.calls[0][1]["MAKEFLAGS"], environment["MAKEFLAGS"])

    def test_original_gnu_descendant_handoff_remains_with_its_advertisement(self):
        environment = {"CARGO_MAKEFLAGS": "", "CARGO_JOBSERVER_HANDOFF": "opaque-original-fixture"}
        with self.contexts(environment):
            self.assertEqual(bootstrap.run_xpy_build(
                self.root, "test-host", 1, 1, [], seed_mode=True), 0)
        self.assertEqual(self.calls[0][1].get("CARGO_JOBSERVER_HANDOFF"),
                         environment["CARGO_JOBSERVER_HANDOFF"])
        self.assertIn("CARGO_JOBSERVER_HANDOFF",
                      bootstrap._ambient_build_authority_overrides(environment))

    def test_undeclared_or_conflicting_clean_environment_refuses_before_child(self):
        for selection, environment in [
            (None, {"CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"}),
            (None, {"CLEAN_OLEAN_PINNED_LEAN_LIB": str(self.library)}),
            (self.selection, {"CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "0"}),
            (self.selection, {"CLEAN_OLEAN_PINNED_LEAN_LIB": "/other/lib/lean"}),
        ]:
            with self.subTest(environment=environment), self.contexts(environment):
                with self.assertRaisesRegex(RuntimeError, "ambient or differs"):
                    bootstrap.run_xpy_build(self.root, "test-host", 1, 1, [],
                                            seed_mode=True, clean_lean=selection)
        self.assertEqual(self.calls, [])

    def test_changed_installation_or_forged_manifest_refuses_before_child(self):
        original = self.selection.manifest.read_bytes()
        self.selection.manifest.write_bytes(original + b" ")
        with self.contexts(), self.assertRaisesRegex(RuntimeError, "manifest bytes changed"):
            bootstrap.run_xpy_build(self.root, "test-host", 1, 1, [], seed_mode=True,
                                    clean_lean=self.selection)
        self.selection.manifest.write_bytes(original)
        part = self.library / "Init.olean"
        part.write_bytes(part.read_bytes() + b"changed body; same world header")
        with self.contexts(), self.assertRaisesRegex(RuntimeError, "changed during"):
            bootstrap.run_xpy_build(self.root, "test-host", 1, 1, [], seed_mode=True,
                                    clean_lean=self.selection)
        self.assertEqual(self.calls, [])

    def test_source_oracle_change_is_not_a_path_only_selection(self):
        table = self.root / "first-party/clean/crates/clean-olean/lean_worlds.tsv"
        table.write_text(table.read_text() + "# source input changed\n")
        with self.contexts(), self.assertRaisesRegex(RuntimeError, "changed during"):
            bootstrap.run_xpy_build(self.root, "test-host", 1, 1, [], seed_mode=True,
                                    clean_lean=self.selection)
        self.assertEqual(self.calls, [])

    def test_deliberate_new_valid_selector_reaches_normal_xpy_as_new_input(self):
        installation = self.library.parent.parent
        other = self.root / "other-elan/toolchains" / installation.name
        shutil.copytree(installation, other)
        new = self.select(other / "lib/lean", "new-inputs.json")
        with self.contexts():
            for selection in (self.selection, new):
                self.assertEqual(bootstrap.run_xpy(self.root, "test-host", "test", 1, 1,
                    ["tests/run-make"], seed_mode=True, clean_lean=selection), 0)
        self.assertNotEqual(self.calls[0][1]["CLEAN_OLEAN_PINNED_LEAN_LIB"],
                            self.calls[1][1]["CLEAN_OLEAN_PINNED_LEAN_LIB"])
        self.assertTrue(all(call[0][2] == "test" for call in self.calls))

    def test_changed_inputs_during_child_cannot_report_success(self):
        def changed(command, *, env, cwd):
            self.child(command, env=env, cwd=cwd)
            part = self.library / "Init.olean"
            part.write_bytes(part.read_bytes() + b"changed during child")
            return SimpleNamespace(returncode=0)
        with self.contexts(), patch.object(bootstrap.subprocess, "run", side_effect=changed):
            with self.assertRaisesRegex(RuntimeError, "changed during"):
                bootstrap.run_xpy(self.root, "test-host", "test", 1, 1, [],
                                  seed_mode=True, clean_lean=self.selection)
        self.assertEqual(len(self.calls), 1)

    def test_partial_selection_or_provenance_use_refuses_before_stage0(self):
        with patch.object(bootstrap, "repo_root", return_value=self.root), \
                patch.object(bootstrap, "resolve_stage0_selection") as stage0:
            self.assertEqual(bootstrap.main([
                "--stage", "1", "--clean-lean-manifest", str(self.selection.manifest)]), 2)
            self.assertEqual(bootstrap.main(["--stage", "2", *self.options()]), 2)
            self.assertEqual(bootstrap.main(["--stage", "1", "--no-build", *self.options()]), 2)
            stage0.assert_not_called()

    def test_support_does_not_switch_missing_or_genesis_configuration(self):
        (self.root / "bootstrap.toml").unlink()
        with self.assertRaisesRegex(RuntimeError, "existing recreator"):
            bootstrap_xpy.configured_bootstrap(self.root)
        (self.root / "bootstrap.toml").write_text(
            "# (genesis stage0 mode) genesis-stage0\n[build]\n")
        with self.assertRaisesRegex(RuntimeError, "unambiguous Trust"):
            bootstrap_xpy.configured_bootstrap(self.root)

    def test_passthrough_cannot_override_owned_stage_or_configuration(self):
        overrides = [
            ["--stage", "2"], ["--stage=0"], ["--config", "/other/config.toml"],
            ["--config=/other/config.toml"], ["--src=/other/source"],
            ["--build", "other-host"], ["--build-dir=/other/build"],
            ["--host=other-host"], ["--skip-stage0-validation"],
            ["--set", "build.rustc=/other/compiler"],
            ["--set=build.test-stage=2"], ["--set", 'build = { cargo = "/other/cargo" }'],
            ["--set", "rust.trust-source-identity=true"],
        ]
        with self.contexts(), patch.object(bootstrap, "repo_root", return_value=self.root):
            for extra in overrides:
                with self.subTest(extra=extra):
                    self.assertEqual(bootstrap_xpy.main(
                        [*self.options(), "test", "tests/run-make", *extra]), 2)
        self.assertEqual(self.calls, [])

    def test_test_separator_preserves_payload_and_keeps_owned_jobs_outside(self):
        payload = ["--stage", "2", "--set=build.rustc=other", "--config", "test-config"]
        with self.contexts(), patch.object(bootstrap, "repo_root", return_value=self.root):
            self.assertEqual(bootstrap_xpy.main([
                "--stage", "0", "-j", "3", *self.options(), "test", "tests/run-make",
                "--", *payload]), 0)
        command = self.calls[0][0]
        separator = command.index("--")
        self.assertEqual(command[separator + 1:], payload)
        self.assertEqual(command[command.index("--stage") + 1], "0")
        self.assertEqual(command[command.index("-j") + 1], "3")
        self.assertLess(command.index("-j"), separator)
        # A leading -- is also the real x.py test separator, not a wrapper
        # decoration to discard as the recreator does for its own remainder.
        self.assertEqual(bootstrap.normal_xpy_arguments(["--", *payload]), ["--", *payload])

    def test_hyphen_valued_test_options_and_normal_xpy_options_are_preserved(self):
        extra = ["-vv", "--test-args", "--stage", "--compiletest-rustc-args", "--set",
                 "--test-args=--config", "--target=example-target", "tests/run-make"]
        with self.contexts(), patch.object(bootstrap, "repo_root", return_value=self.root):
            self.assertEqual(bootstrap_xpy.main([*self.options(), "test", *extra]), 0)
        expected = ["-vv", "--test-args=--stage", "--compiletest-rustc-args=--set",
                    "--test-args=--config", "--target=example-target", "tests/run-make"]
        self.assertEqual(self.calls[0][0][-len(expected):], expected)

    def test_selected_config_overrides_ambient_config_in_actual_python_parser(self):
        spec = importlib.util.spec_from_file_location(
            "bootstrap_xpy_python_parser", SCRIPTS.parent / "src/bootstrap/bootstrap.py")
        owner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(owner)
        with self.contexts({"RUST_BOOTSTRAP_CONFIG": "/other/config.toml"}), \
                patch.object(bootstrap, "repo_root", return_value=self.root):
            self.assertEqual(bootstrap_xpy.main(
                [*self.options(), "test", "-vv", "--test-args", "--config",
                 "tests/run-make"]), 0)
        command, env, _ = self.calls[0]
        self.assertEqual(owner.parse_args(command[2:]).config, str(self.root / "bootstrap.toml"))
        self.assertIn("--test-args=--config", command)
        self.assertNotIn("RUST_BOOTSTRAP_CONFIG", env)

    def test_supported_selected_build_argv_preserves_native_parser_inputs(self):
        for stage in (0, 1):
            with self.subTest(stage=stage), self.contexts(), \
                    patch.object(bootstrap, "repo_root", return_value=self.root):
                self.calls.clear()
                self.assertEqual(bootstrap.run_xpy_build(
                    self.root, "test-host", stage, 3, ["compiler/rustc"],
                    seed_mode=True, clean_lean=self.selection,
                    normal_config=self.config_identity()), 0)
                self.assertEqual(bootstrap_xpy.main([
                    "--host", "test-host", "--stage", str(stage), "-j", "3", *self.options(),
                    "build", "compiler/rustc"]), 0)
            recreator, support = (call[0] for call in self.calls)
            self.assertEqual(recreator, support)
            self.assertNotIn("--set", support)
            self.assertEqual(support[support.index("--config") + 1], str(self.root / "bootstrap.toml"))
            self.assertEqual(support[support.index("--stage") + 1], str(stage))

    def test_supported_frontend_preserves_full_and_native_test_arguments(self):
        cases = [("build", []), ("test", ["tests/run-make", "--test-args=--help"]),
                 ("test", ["tests/run-make", "--target=example-target"])]
        for command, extra in cases:
            with self.subTest(command=command, extra=extra), self.contexts(), \
                    patch.object(bootstrap, "repo_root", return_value=self.root):
                self.calls.clear()
                self.assertEqual(bootstrap_xpy.main([*self.options(), command, *extra]), 0)
            forwarded = self.calls[0][0]
            self.assertEqual(forwarded[2], command)
            for argument in extra:
                self.assertIn(argument, forwarded)
        with self.contexts():
            self.calls.clear()
            self.assertEqual(bootstrap.run_xpy_build(
                self.root, "test-host", 2, None, [], seed_mode=True), 0)
        stage2 = self.calls[0][0]
        self.assertEqual(stage2[5:7], ["--set", "rust.trust-source-identity=false"])
        self.assertEqual(stage2[stage2.index("--stage") + 1], "2")

    def test_normal_config_requires_explicit_false_in_selected_bytes(self):
        config = self.root / "bootstrap.toml"
        for value in ("", "trust-source-identity = true", 'trust-source-identity = "false"'):
            with self.subTest(value=value), self.contexts(), \
                    patch.object(bootstrap, "repo_root", return_value=self.root):
                config.write_text("# (seed stage0 mode)\n[build]\n[rust]\n" + value + "\n")
                self.calls.clear()
                self.assertEqual(bootstrap_xpy.main([*self.options(), "build", "compiler/rustc"]), 2)
                self.assertEqual(self.calls, [])
        inherited = self.root / "inherited.toml"
        inherited.write_text("[rust]\ntrust-source-identity = false\n")
        config.write_text('# (seed stage0 mode)\ninclude = ["inherited.toml"]\n[build]\n')
        with self.contexts(), patch.object(bootstrap, "repo_root", return_value=self.root):
            self.assertEqual(bootstrap_xpy.main([*self.options(), "build", "compiler/rustc"]), 2)
        self.assertEqual(self.calls, [])

    def test_bound_normal_config_cannot_be_overridden_at_shared_boundary(self):
        for extra in (["compiler/rustc", "--config=other"],
                      ["compiler/rustc", "--set", "rust.trust-source-identity=true"]):
            with self.subTest(extra=extra), self.contexts(), self.assertRaisesRegex(ValueError, "owned"):
                bootstrap.run_xpy_build(self.root, "test-host", 1, 1, extra, seed_mode=True,
                                        normal_config=self.config_identity())
        self.assertEqual(self.calls, [])

    def test_normal_config_drift_during_environment_or_child_cannot_succeed(self):
        config = self.root / "bootstrap.toml"
        original = config.read_bytes()
        identity = self.config_identity()
        def changed_environment(*_args, **_kwargs):
            config.write_bytes(original + b"\n# changed during environment\n")
            return {}
        with self.contexts(), patch.object(bootstrap, "xpy_environment", side_effect=changed_environment), \
                self.assertRaisesRegex(RuntimeError, "config bytes changed"):
            bootstrap.run_xpy_build(self.root, "test-host", 1, 1, ["compiler/rustc"],
                                    seed_mode=True, normal_config=identity)
        self.assertEqual(self.calls, [])
        config.write_bytes(original)
        def changed_child(command, *, env, cwd):
            self.child(command, env=env, cwd=cwd)
            config.write_bytes(original + b"\n# changed during child\n")
            return SimpleNamespace(returncode=0)
        with self.contexts(), patch.object(bootstrap.subprocess, "run", side_effect=changed_child), \
                self.assertRaisesRegex(RuntimeError, "config bytes changed"):
            bootstrap.run_xpy_build(self.root, "test-host", 1, 1, ["compiler/rustc"],
                                    seed_mode=True, normal_config=identity)
        self.assertEqual(len(self.calls), 1)


if __name__ == "__main__":
    unittest.main()
