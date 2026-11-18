#!/usr/bin/env python3
"""Bootstrap source controls; no resource, cache-readiness or proof admission."""
from __future__ import annotations

import os
import io
import json
import select
import shlex
import signal
import subprocess
import sys
import tempfile
import time
import types
from contextlib import ExitStack, redirect_stderr, redirect_stdout
import unittest
from pathlib import Path
from unittest.mock import Mock, call, patch

REPO = Path(__file__).resolve().parents[2]
HELPER = REPO / "scripts/bootstrap_dependency_closure.py"


def source_module(name, path):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    # These controls exercise source, including when an unrelated pyc exists.
    exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
    return module


closure = source_module("trust_dependency_closure_test_subject", HELPER)


class DependencyClosureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        # Resolved: macOS spells the temporary directory through the /var ->
        # /private/var symlink, and the helper compares resolved paths.
        self.root = Path(self.temporary.name).resolve()
        self.env = {"HOME": str(self.root), "CARGO_HOME": str(self.root / "cache")}
        self.write("scripts/recreate_bootstrap.py", (REPO / "scripts/recreate_bootstrap.py").read_text())
        self.driver = self.root / "bin/targo"
        self.write("bin/targo", "test driver source")
        self.write("src/bootstrap/src/core/metadata.rs", "")
        self.write("src/bootstrap/src/core/build_steps/compile.rs", "")
        self.write("src/bootstrap/src/core/build_steps/vendor.rs", """
pub fn default_paths_to_vendor(builder: &Builder<'_>) -> Vec<(PathBuf, Vec<&'static str>)> {
 let paths: Vec<(&str, Vec<&'static str>)> = vec![
  ("dist-only/Cargo.toml", vec![]),
 ];
 paths.into_iter().map(|(path, submodules)| (builder.src.join(path), submodules)).collect()
}
""")
        self.write("src/bootstrap/src/core/build_steps/tool.rs", '''
fn ensure_default_verifier_tool_bins() {
    ToolBuild { path: "first-party/ay/crates/ay", };
    ToolBuild { path: "first-party/ty/crates/tla-cli", };
    ToolBuild { path: "first-party/clean/crates/clean", };
}
fn ensure_user_facing_tools() {
    ToolBuild { path: "src/tools/targo", };
}
''')
        for manifest in (*closure._BASE_MANIFESTS,
                         "first-party/ay/crates/ay/Cargo.toml",
                         "first-party/ty/crates/tla-cli/Cargo.toml",
                         "first-party/clean/crates/clean/Cargo.toml",
                         "src/tools/targo/Cargo.toml", "dist-only/Cargo.toml"):
            self.write(manifest, "[workspace]\nmembers = []\n")
            self.write(str(Path(manifest).with_name("Cargo.lock")), "version = 4\n")

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def run_closure(self, **kwargs):
        return closure.dependency_closure(self.root, str(self.driver), self.env, **kwargs)

    def write_python_driver(self, source):
        # Trust: a managed interpreter path can contain spaces, which a POSIX
        # shebang cannot quote. Preserve exact argv through a shell exec shim.
        payload = self.driver.with_suffix(".py")
        payload.write_text(source)
        self.driver.write_text(
            "#!/bin/sh\nexec " + shlex.quote(sys.executable) + " "
            + shlex.quote(str(payload)) + ' "$@"\n'
        )
        self.driver.chmod(0o755)

    def test_recipe_reader_reaches_ty_separate_workspace_and_new_literal_recipe(self):
        self.write("new-backend/Cargo.toml", "[workspace]\n")
        recipe = self.root / closure._RECIPE_INPUTS[-1]
        recipe.write_text(recipe.read_text().replace(
            'ToolBuild { path: "src/tools/targo", };',
            'ToolBuild { path: "src/tools/targo", }; ToolBuild { path: "new-backend", };'))
        with patch.object(closure, "_fetch") as fetch:
            report = self.run_closure()
        selected = {row["manifest"] for row in report["completed_fetches"]}
        self.assertIn("first-party/ty/crates/tla-cli/Cargo.toml", selected)
        self.assertIn("new-backend/Cargo.toml", selected)
        self.assertEqual(fetch.call_count, len(selected))

    def test_native_planner_reuses_complete_reader_and_detects_transitive_changes(self):
        self.write("first-party/ty/crates/tla-cli/Cargo.toml",
                   '[package]\nname = "ty-test"\nversion = "0.1.0"\n'
                   '[dependencies]\nlocal = { path = "../../../local" }\n')
        transitive = self.write("first-party/local/Cargo.toml",
                                '[package]\nname = "local"\nversion = "0.1.0"\n')
        with patch.object(closure, "_fetch") as fetch:
            before = closure.recipe_plan(self.root, self.env)
            with patch.object(closure, "_fetch"):
                ordinary = self.run_closure()
            self.assertEqual(before["manifests"],
                             [row["manifest"] for row in ordinary["completed_fetches"]])
            self.assertNotIn("completed_fetches", before)
            self.assertNotIn("ready", before)
            transitive.write_text(transitive.read_text() + '# actual input change\n')
            after = closure.recipe_plan(self.root, self.env)
        fetch.assert_not_called()
        self.assertEqual(before["manifests"], after["manifests"])
        self.assertNotEqual(before["source_inputs_sha256"], after["source_inputs_sha256"])

    def test_native_planner_tracks_absent_cache_configuration(self):
        before = closure.recipe_plan(self.root, self.env)
        self.write("cache/config.toml", '[net]\noffline = true\n')
        after = closure.recipe_plan(self.root, self.env)
        self.assertNotEqual(before["source_inputs_sha256"], after["source_inputs_sha256"])
        self.assertEqual(before["source_inputs_count"], after["source_inputs_count"])

    def delegated_verifier_recipe(self):
        recipe = self.root / closure._RECIPE_INPUTS[-1]
        recipe.write_text(recipe.read_text().replace(
            "fn ensure_default_verifier_tool_bins()", "fn ensure_verifier_tool_bins()") + """
fn ensure_default_verifier_tool_bins() {
    ensure_verifier_tool_bins(builder, target_compiler, sysroot, false);
}
""")
        return recipe

    def test_thin_verifier_delegate_keeps_every_recipe_and_new_backend(self):
        recipe = self.delegated_verifier_recipe()
        self.write("new-backend/Cargo.toml", "[workspace]\n")
        recipe.write_text(recipe.read_text().replace(
            'ToolBuild { path: "first-party/ty/crates/tla-cli", };',
            'ToolBuild { path: "first-party/ty/crates/tla-cli", }; '
            'ToolBuild { path: "new-backend", };'))
        with patch.object(closure, "_fetch") as fetch:
            report = self.run_closure()
        self.assertEqual({row["manifest"] for row in report["completed_fetches"]}, {
            "Cargo.toml", "library/Cargo.toml", "src/bootstrap/Cargo.toml",
            "first-party/ay/crates/ay/Cargo.toml", "first-party/ty/crates/tla-cli/Cargo.toml",
            "first-party/clean/crates/clean/Cargo.toml", "src/tools/targo/Cargo.toml",
            "dist-only/Cargo.toml", "new-backend/Cargo.toml",
        })
        self.assertEqual(fetch.call_count, 9)

    def test_delegated_nonliteral_recipe_refuses_before_fetch(self):
        recipe = self.delegated_verifier_recipe()
        recipe.write_text(recipe.read_text().replace(
            'path: "first-party/ty/crates/tla-cli"', 'path: runtime_path'))
        with patch.object(closure, "_fetch") as fetch:
            with self.assertRaisesRegex(RuntimeError, "nonliteral ToolBuild path"):
                self.run_closure()
        fetch.assert_not_called()

    def test_unknown_verifier_forwarding_refuses_before_fetch(self):
        recipe = self.delegated_verifier_recipe()
        recipe.write_text(recipe.read_text().replace(
            "sysroot, false);", "sysroot, choose_at_runtime());"))
        with patch.object(closure, "_fetch") as fetch:
            with self.assertRaisesRegex(RuntimeError, "unsupported verifier assembly wrapper"):
                self.run_closure()
        fetch.assert_not_called()

    def test_duplicate_verifier_delegate_owner_refuses_before_fetch(self):
        recipe = self.delegated_verifier_recipe()
        recipe.write_text(recipe.read_text() + '\nfn ensure_verifier_tool_bins() {}\n')
        with patch.object(closure, "_fetch") as fetch:
            with self.assertRaisesRegex(RuntimeError, "ambiguous bootstrap recipe"):
                self.run_closure()
        fetch.assert_not_called()

    def test_string_or_nested_function_cannot_supply_delegate_owner(self):
        recipe = self.delegated_verifier_recipe()
        recipe.write_text(recipe.read_text().replace(
            "fn ensure_verifier_tool_bins()", "fn unrelated_tool_bins()") + r'''
const DECOY: &str = "fn ensure_verifier_tool_bins() { ToolBuild { path: \"decoy\", }; }";
fn unrelated() { fn ensure_verifier_tool_bins() { ToolBuild { path: "decoy", }; } }
''')
        with patch.object(closure, "_fetch") as fetch:
            with self.assertRaisesRegex(RuntimeError, "missing.*bootstrap recipe"):
                self.run_closure()
        fetch.assert_not_called()

    def test_each_entry_is_resolved_without_guessing_ancestor_lock_ownership(self):
        with patch.object(closure, "_fetch") as fetch:
            self.run_closure()
        paths = [call.args[0][-1] for call in fetch.call_args_list]
        self.assertEqual(len(paths), 8)
        self.assertIn(str(self.root / "Cargo.toml"), paths)
        self.assertIn(str(self.root / "src/bootstrap/Cargo.toml"), paths)
        self.assertIn(str(self.root / "first-party/ty/crates/tla-cli/Cargo.toml"), paths)

    def test_default_gate_is_locked_offline_fetch_and_retains_caller_cargo_home(self):
        self.env["CARGO_NET_OFFLINE"] = "false"
        with patch.object(closure, "_fetch") as fetch:
            self.run_closure()
        for call in fetch.call_args_list:
            command, cwd, environment, _end, progress = call.args
            self.assertIsNone(progress)  # no preparation hands this gate an item bound
            self.assertEqual(command[:4], [str(self.driver), "fetch", "--locked", "--offline"])
            self.assertEqual(cwd, self.root)
            self.assertEqual(environment["CARGO_NET_OFFLINE"], "true")
            self.assertEqual(environment["CARGO_HOME"], self.env["CARGO_HOME"])
            self.assertNotIn("--unverified", command)  # non-compilation verbs reject it
        self.assertEqual(self.env["CARGO_NET_OFFLINE"], "false")

    def test_absent_compat_home_binds_native_home_config_without_changing_caller_policy(self):
        del self.env["CARGO_HOME"]
        self.env.update(TARGO_HOME="native-cache", CARGO_BUILD_WARNINGS="")
        config = self.write("native-cache/config.toml", "[net]\noffline=true\n")
        with patch.object(closure, "_fetch") as fetch:
            report = self.run_closure()
        self.assertIsNotNone(report["source_inputs_sha256"][str(config)])
        self.assertIsNone(report["source_inputs_sha256"][str(self.root / ".cargo/config.toml")])
        for call in fetch.call_args_list:
            self.assertNotIn("CARGO_HOME", call.args[2])
            self.assertEqual(call.args[2]["TARGO_HOME"], "native-cache")
            self.assertEqual(call.args[2]["CARGO_BUILD_WARNINGS"], "")
        with patch.object(closure, "_fetch", side_effect=lambda *_: config.write_text("changed")):
            with self.assertRaisesRegex(closure.DependencyClosureError, "inputs changed"):
                self.run_closure()

    def test_prospectively_absent_native_home_config_cannot_appear_during_resolution(self):
        del self.env["CARGO_HOME"]
        self.env["TARGO_HOME"] = str(self.root / "native-cache")
        config = self.root / "native-cache/config"
        with patch.object(closure, "_fetch"):
            report = self.run_closure()
        self.assertIsNone(report["source_inputs_sha256"][str(config)])
        with patch.object(closure, "_fetch", side_effect=lambda *_: self.write("native-cache/config", "changed")):
            with self.assertRaisesRegex(closure.DependencyClosureError, "inputs changed"):
                self.run_closure()

    def test_present_compat_home_even_empty_keeps_native_alias_out_of_config_selection(self):
        config = self.write("native-cache/config.toml", "native alias must lose")
        self.env["TARGO_HOME"] = str(config.parent)
        for compatibility in ("", str(self.root / "compat-cache")):
            self.env["CARGO_HOME"] = compatibility
            with self.subTest(compatibility=compatibility), patch.object(closure, "_fetch") as fetch:
                report = self.run_closure()
            self.assertNotIn(str(config), report["source_inputs_sha256"])
            selected = self.root / ("compat-cache" if compatibility else ".cargo") / "config.toml"
            self.assertIn(str(selected), report["source_inputs_sha256"])
            self.assertTrue(all(call.args[2]["CARGO_HOME"] == compatibility for call in fetch.call_args_list))

    def test_explicit_preparation_rechecks_offline_under_identical_deadline(self):
        end = time.monotonic() + 30
        with patch.object(closure, "_fetch") as fetch:
            report = self.run_closure(prepare=True, deadline=end)
        self.assertEqual(len(report["completed_fetches"]), 16)
        self.assertTrue(all(call.args[3] == end for call in fetch.call_args_list))
        self.assertTrue(all("--offline" not in c.args[0] for c in fetch.call_args_list[:8]))
        self.assertTrue(all("--offline" in c.args[0] for c in fetch.call_args_list[8:]))

    def test_acquisition_returns_no_readiness_and_final_home_replays_every_recipe(self):
        end = time.monotonic() + 30
        with patch.object(closure, "_fetch") as fetch:
            acquired = closure.acquire_dependency_inputs(self.root, str(self.driver), self.env, deadline=end)
        self.assertIsInstance(acquired, closure.DependencyAcquisition)
        report = acquired.report()
        self.assertEqual(report["schema"], "trust.bootstrap-dependency-acquisition.v1")
        self.assertEqual(len(fetch.call_args_list), 8)
        self.assertTrue(all("--offline" not in c.args[0] and c.args[3] == end for c in fetch.call_args_list))
        final_env = {**self.env, "CARGO_HOME": str(self.root / "safe-handoff"), "CARGO_NET_OFFLINE": "true"}
        with patch.object(closure, "_fetch") as fetch:
            final = closure.dependency_closure(self.root, str(self.driver), final_env, deadline=end)
        self.assertEqual(len(fetch.call_args_list), 8)
        self.assertTrue(all("--offline" in c.args[0] and c.args[3] == end for c in fetch.call_args_list))
        self.assertEqual(final["manifests"], report["manifests"])
        self.assertEqual(final["manifest_policy_sha256"], report["manifest_policy_sha256"])
        for changed in ({**final_env, "RUSTC_WRAPPER": "/different"}, final_env):
            if changed is final_env:
                self.write("safe-handoff/config.toml", "[net]\nretry = 1\n")
            with patch.object(closure, "_fetch"):
                different = closure.dependency_closure(self.root, str(self.driver), changed, deadline=end)
            self.assertNotEqual(different["manifest_policy_sha256"], report["manifest_policy_sha256"])

    def test_acquisition_retains_source_config_driver_bookends_and_requires_explicit_home(self):
        for selected in ("Cargo.lock", "cache/config.toml", "bin/targo"):
            path = self.root / selected
            original = path.read_bytes() if path.exists() else None
            def change(*_args):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("changed during acquisition")
            with self.subTest(selected=selected), patch.object(closure, "_fetch", side_effect=change):
                with self.assertRaisesRegex(closure.DependencyClosureError, "inputs changed"):
                    closure.acquire_dependency_inputs(self.root, str(self.driver), self.env)
            if original is None:
                path.unlink()
            else:
                path.write_bytes(original)
        for home in (None, "", "relative"):
            env = dict(self.env)
            if home is None:
                env.pop("CARGO_HOME")
            else:
                env["CARGO_HOME"] = home
            with self.subTest(home=home), patch.object(closure, "_fetch") as fetch:
                with self.assertRaisesRegex(closure.DependencyClosureError, "explicit absolute Cargo home"):
                    closure.acquire_dependency_inputs(self.root, str(self.driver), env)
                fetch.assert_not_called()

    def test_prepare_respects_explicit_offline_policy_without_silent_network_override(self):
        self.env["CARGO_NET_OFFLINE"] = "true"
        with patch.object(closure, "_fetch") as fetch:
            self.run_closure(prepare=True)
        self.assertTrue(all(c.args[2]["CARGO_NET_OFFLINE"] == "true" for c in fetch.call_args_list))

    def test_dist_only_workspace_and_its_lock_and_recipe_are_bound(self):
        with patch.object(closure, "_fetch"):
            report = self.run_closure()
        self.assertIn({"manifest": "dist-only/Cargo.toml", "offline": True}, report["completed_fetches"])
        for path in ("dist-only/Cargo.lock", "src/bootstrap/src/core/build_steps/vendor.rs"):
            self.assertIsNotNone(report["source_inputs_sha256"][str(self.root / path)])
        with patch.object(closure, "_fetch", side_effect=lambda *_a: self.write("dist-only/Cargo.lock", "changed")):
            with self.assertRaisesRegex(closure.DependencyClosureError, "inputs changed"):
                self.run_closure()

    def test_transitive_local_member_is_bound_and_external_manifest_path_refuses(self):
        self.write("Cargo.toml", '[workspace]\nmembers = ["member"]\n')
        member = self.write("member/Cargo.toml", '[package]\nname = "member"\nversion = "0.1.0"\n')
        with patch.object(closure, "_fetch"):
            report = self.run_closure()
        self.assertIn(str(member), report["source_inputs_sha256"])
        with patch.object(closure, "_fetch", side_effect=lambda *_a: member.write_text('changed')):
            with self.assertRaisesRegex(closure.DependencyClosureError, "inputs changed"):
                self.run_closure()
        member.write_text('[package]\nname = "member"\nversion = "0.1.0"\n'
                          '[dependencies]\noutside = { path = "../../outside" }\n')
        with patch.object(closure, "_fetch") as fetch:
            with self.assertRaisesRegex(RuntimeError, "escapes checkout"):
                self.run_closure()
            fetch.assert_not_called()

    def test_missing_or_dynamic_dist_workspace_and_postprocessing_refuse(self):
        recipe = self.root / "src/bootstrap/src/core/build_steps/vendor.rs"
        original = recipe.read_text()
        for text in (original.replace('"dist-only/Cargo.toml"', "runtime_manifest"),
                     original.replace("paths.into_iter()", "paths.push(extra); paths.into_iter()"),
                     original.replace('"dist-only/Cargo.toml"', '"dist -only/Cargo.toml"'),
                     original.replace('"dist-only/Cargo.toml"', '"missing/Cargo.toml"')):
            recipe.write_text(text)
            with patch.object(closure, "_fetch") as fetch:
                with self.assertRaises(RuntimeError):
                    self.run_closure()
                fetch.assert_not_called()
        recipe.write_text(original)

    def test_comment_string_and_nested_function_decoys_do_not_supply_dist_recipe(self):
        recipe = self.root / "src/bootstrap/src/core/build_steps/vendor.rs"
        original = recipe.read_text()
        for text in ("/*" + original + "*/", "fn outer() {" + original + "}",
                     "const BRACE: char = '}'; fn outer() {" + original + "}",
                     'const DECOY: &str = "pub fn default_paths_to_vendor() {}";'):
            recipe.write_text(text)
            with patch.object(closure, "_fetch") as fetch:
                with self.assertRaisesRegex(RuntimeError, "dist vendor recipe"):
                    self.run_closure()
                fetch.assert_not_called()

    def test_locked_offline_argv_and_cache_sequence_with_executable_fixture(self):
        # A real executable fixture checks argv/env and cache handoff. On a Mac
        # each of these fetches runs under the per-fetch custodian.
        trace = self.root / "fetch-trace.jsonl"
        self.write_python_driver(
            "import json, os, pathlib, sys\n" +
            "args=sys.argv[1:]; assert args[:2] == ['fetch', '--locked']\n" +
            "assert '--manifest-path' in args and not any(x in args for x in ['build','check','update'])\n" +
            "cache=pathlib.Path(os.environ['CARGO_HOME']); cache.mkdir(exist_ok=True)\n" +
            "marker=cache/'fetched'\n" +
            "if '--offline' in args: assert marker.read_text() == 'locked' and os.environ['CARGO_NET_OFFLINE'] == 'true'\n" +
            "else: marker.write_text('locked')\n" +
            f"with open({str(trace)!r}, 'a') as f: f.write(json.dumps(args)+'\\n')\n")
        report = self.run_closure(prepare=True, deadline=time.monotonic() + 30)
        calls = [json.loads(line) for line in trace.read_text().splitlines()]
        self.assertEqual(len(calls), len(report["completed_fetches"]))
        self.assertTrue(all('--offline' not in args for args in calls[:8]))
        self.assertTrue(all('--offline' in args for args in calls[8:]))
        self.assertEqual((self.root / "dist-only/Cargo.lock").read_text(), "version = 4\n")

    def test_missing_authority_refuses_before_any_child(self):
        (self.root / closure._RECIPE_INPUTS[0]).unlink()
        with patch.object(closure, "_fetch") as fetch:
            with self.assertRaisesRegex(closure.DependencyClosureError, "authority is missing"):
                self.run_closure()
        fetch.assert_not_called()

    def fixed_recipe_helpers(self):
        path = self.root / closure._RECIPE_INPUTS[-1]
        path.write_text("""
fn ensure_default_verifier_tool_bins(builder: &Builder<'_>, target_compiler: Compiler, sysroot: &Path) {
    ensure_verifier_tool_bins(builder, target_compiler, sysroot, false);
}
fn ensure_verifier_tool_bins() {
    builder.ensure(targo_tool_build_recipe(build_compiler, target_compiler, target));
    ensure_sysroot_ay(builder, target_compiler, sysroot);
    let daemon = build_trustd_tool(builder, build_compiler, target_compiler, target);
    ToolBuild { path: "first-party/ty/crates/tla-cli", };
    ToolBuild { path: "first-party/clean/crates/clean", };
}
fn ensure_sysroot_ay() { builder.ensure(ay_tool_build_recipe(a, b, c, src)); }
fn ay_tool_build_recipe() -> ToolBuild { ToolBuild { path: "first-party/ay/crates/ay", } }
fn build_trustd_tool() { builder.ensure(trustd_tool_build_recipe(a, b, c)); }
fn trustd_tool_build_recipe() -> ToolBuild { ToolBuild { path: "crates/trust-coordinator", } }
fn targo_tool_build_recipe() -> ToolBuild { ToolBuild { path: "src/tools/targo", } }
fn ensure_user_facing_tools() { builder.ensure(targo_tool_build_recipe(a, b, c)); }
""")
        self.write("crates/trust-coordinator/Cargo.toml", "[workspace]\n")
        self.write("crates/trust-coordinator/Cargo.lock", "version=4\n")
        return path

    def test_fixed_wrapper_and_complete_shared_recipe_graph_are_retained(self):
        self.fixed_recipe_helpers()
        roots = {str(p.relative_to(self.root)) for p in closure.stage0_bootstrap_manifest_roots(self.root)}
        self.assertTrue({"src/tools/targo/Cargo.toml", "first-party/ay/crates/ay/Cargo.toml",
                         "first-party/ty/crates/tla-cli/Cargo.toml", "first-party/clean/crates/clean/Cargo.toml",
                         "crates/trust-coordinator/Cargo.toml"}.issubset(roots))

    def split_recipe_helpers(self):
        recipe = self.fixed_recipe_helpers()
        recipe.write_text(recipe.read_text().replace("sysroot, false);", "sysroot, true);", 1) + """
fn ensure_sysroot_verifier_prerequisites(builder: &Builder<'_>, target_compiler: Compiler, sysroot: &Path) {
    ensure_verifier_tool_bins(builder, target_compiler, sysroot, false);
}
""")
        return recipe

    def test_split_verifier_wrappers_keep_complete_manifest_population(self):
        self.fixed_recipe_helpers()
        legacy = closure.stage0_bootstrap_manifest_roots(self.root)
        self.split_recipe_helpers()
        self.assertEqual(closure.stage0_bootstrap_manifest_roots(self.root), legacy)
        with patch.object(closure, "_fetch") as fetch:
            report = self.run_closure()
        self.assertEqual({row["manifest"] for row in report["completed_fetches"]},
                         {str(path.relative_to(self.root)) for path in legacy})
        self.assertEqual(fetch.call_count, len(legacy))

    def test_split_verifier_wrapper_mutants_refuse_before_fetch(self):
        recipe = self.split_recipe_helpers()
        original = recipe.read_text()
        wrapper_error = "unsupported verifier assembly wrapper"
        for name, mutant, refusal in [
            ("computed completed flag", original.replace("sysroot, true);", "sysroot, select_flag());"),
             wrapper_error),
            ("completed wrapper uses prerequisites", original.replace("sysroot, true);", "sysroot, false);"),
             wrapper_error),
            ("prerequisites wrapper uses completed phase", original.replace("sysroot, false);", "sysroot, true);"),
             wrapper_error),
            ("prerequisites wrapper is absent",
             original.replace("fn ensure_sysroot_verifier_prerequisites", "fn unrelated_wrapper"),
             wrapper_error),
            ("prerequisites wrapper is ambiguous",
             original + "\nfn ensure_sysroot_verifier_prerequisites() {}\n", "ambiguous bootstrap recipe"),
            ("split wrapper has an inline recipe", original.replace(
                "ensure_verifier_tool_bins(builder, target_compiler, sysroot, true);",
                'ToolBuild { path: "src/tools/targo", };'), wrapper_error),
            ("delegate recurses through prerequisites", original.replace(
                "fn ensure_verifier_tool_bins() {",
                "fn ensure_verifier_tool_bins() { ensure_sysroot_verifier_prerequisites(builder, target_compiler, sysroot);"),
             "cyclic tool recipe graph"),
        ]:
            with self.subTest(name=name), patch.object(closure, "_fetch") as fetch:
                recipe.write_text(mutant)
                with self.assertRaisesRegex(RuntimeError, refusal):
                    self.run_closure()
                fetch.assert_not_called()

    def shared_trustup_recipe(self):
        recipe = self.fixed_recipe_helpers()
        recipe.write_text(recipe.read_text().replace(
            "fn ensure_user_facing_tools() { builder.ensure(targo_tool_build_recipe(a, b, c)); }",
            "fn ensure_user_facing_tools() { builder.ensure(targo_tool_build_recipe(a, b, c)); "
            "builder.ensure(trustup_tool_build_recipe(a, b, c)); }") +
            '\nfn trustup_tool_build_recipe() -> ToolBuild { '
            'ToolBuild { path: "src/tools/trustup", } }\n')
        self.write("src/tools/trustup/Cargo.toml", "[workspace]\n")
        self.write("src/tools/trustup/Cargo.lock", "version = 4\n")
        return recipe

    def test_shared_trustup_factory_extends_complete_offline_fetch_population(self):
        self.shared_trustup_recipe()
        with patch.object(closure, "_fetch") as fetch:
            report = self.run_closure()
        roots = {row["manifest"] for row in report["completed_fetches"]}
        self.assertIn("src/tools/trustup/Cargo.toml", roots)
        self.assertIn("src/tools/targo/Cargo.toml", roots)
        self.assertIn("crates/trust-coordinator/Cargo.toml", roots)
        self.assertEqual(fetch.call_count, len(roots))

    def test_shared_trustup_dynamic_path_or_unknown_factory_refuses_before_fetch(self):
        recipe = self.shared_trustup_recipe()
        original = recipe.read_text()
        mutants = [
            original.replace('ToolBuild { path: "src/tools/trustup", }',
                             'ToolBuild { path: selected_path, }; '
                             'ToolBuild { path: "literal-decoy", }'),
            original.replace('builder.ensure(trustup_tool_build_recipe(a, b, c))',
                             'builder.ensure(unknown_trustup_recipe(a, b, c))'),
        ]
        for mutant in mutants:
            recipe.write_text(mutant)
            with self.subTest(mutant=mutant[-180:]), patch.object(closure, "_fetch") as fetch:
                with self.assertRaises(RuntimeError):
                    self.run_closure()
                fetch.assert_not_called()

    def test_shared_trustup_missing_duplicate_or_recursive_factory_refuses(self):
        recipe = self.shared_trustup_recipe()
        original = recipe.read_text()
        for mutant in [
            original.replace("fn trustup_tool_build_recipe()", "fn missing_recipe()"),
            original + '\nfn trustup_tool_build_recipe() { ToolBuild { path: "decoy", } }\n',
            original.replace('ToolBuild { path: "src/tools/trustup", }',
                             'trustup_tool_build_recipe(); '
                             'ToolBuild { path: "src/tools/trustup", }'),
        ]:
            recipe.write_text(mutant)
            with self.subTest(mutant=mutant[-180:]), patch.object(closure, "_fetch") as fetch:
                with self.assertRaises(RuntimeError):
                    self.run_closure()
                fetch.assert_not_called()

    def test_nonliteral_path_in_shared_factory_refuses_even_with_literal_decoy(self):
        recipe = self.fixed_recipe_helpers()
        recipe.write_text(recipe.read_text().replace('ToolBuild { path: "src/tools/targo", }',
            'ToolBuild { tool: "path: \"decoy\",", path: selected_path, }'))
        with self.assertRaisesRegex(RuntimeError, "nonliteral ToolBuild path"):
            closure.stage0_bootstrap_manifest_roots(self.root)

    def test_raw_string_character_and_nested_comment_decoys_do_not_steer_shared_recipes(self):
        recipe = self.fixed_recipe_helpers()
        original = recipe.read_text()
        prefix = """const RAW: &str = r###"fn ensure_user_facing_tools() { ToolBuild { path: "decoy", } }"###;
const CHAR: char = '{';
/* outer { /* fn targo_tool_build_recipe() { } */ inner } */
"""
        recipe.write_text(prefix + original)
        paths = closure.stage0_bootstrap_manifest_roots(self.root)
        self.assertIn(self.root / "src/tools/targo/Cargo.toml", paths)
        self.assertFalse(any("decoy" in str(path) for path in paths))

    def test_unknown_factory_and_changed_wrapper_refuse(self):
        recipe = self.fixed_recipe_helpers()
        original = recipe.read_text()
        for text in (original.replace('targo_tool_build_recipe(build_compiler', 'unknown_tool_build_recipe(build_compiler'),
                     original.replace('sysroot, false);', 'sysroot, runtime_flag);')):
            recipe.write_text(text)
            with self.subTest(text=text[:100]), self.assertRaises(RuntimeError):
                closure.stage0_bootstrap_manifest_roots(self.root)

    def test_missing_or_ambiguous_shared_recipe_refuses(self):
        recipe = self.fixed_recipe_helpers()
        original = recipe.read_text()
        for text in (original.replace('fn targo_tool_build_recipe()', 'fn gone_targo_tool_build_recipe()'),
                     original + '\nfn targo_tool_build_recipe() { ToolBuild { path: "decoy", } }\n'):
            recipe.write_text(text)
            with self.subTest(text=text[-100:]), self.assertRaisesRegex(RuntimeError, "missing or ambiguous"):
                closure.stage0_bootstrap_manifest_roots(self.root)

    def source_graph(self):
        import ast
        owner = REPO / "scripts/recreate_bootstrap.py"
        node = next(n for n in ast.parse(owner.read_bytes()).body
                    if isinstance(n, ast.ClassDef) and n.name == "_Stage0ManifestGraph")
        namespace = {"Path": Path}
        exec(compile(ast.Module(body=[node], type_ignores=[]), str(owner), "exec"), namespace)
        return namespace["_Stage0ManifestGraph"](self.root)

    def dependency_workspace(self):
        self.write("Cargo.toml", '[workspace]\nmembers=["unrelated", "helper"]\nexclude=["selected"]\n'
                   '[workspace.dependencies]\ninherited={git="https://github.com/Owner/inherited",rev="' + "a"*40 + '"}\n')
        selected = self.write("selected/Cargo.toml", '[package]\nname="selected"\nversion="0.1.0"\n'
                   '[dependencies]\ninherited={workspace=true}\nhelper={path="../helper"}\n'
                   '[build-dependencies]\nbuild={git="https://github.com/Owner/build",rev="' + "b"*40 + '"}\n'
                   '[dev-dependencies]\ndev={git="https://github.com/Owner/dev",branch="main"}\n')
        self.write("helper/Cargo.toml", '[package]\nname="helper"\nversion="0.1.0"\n'
                   '[dependencies]\nleaf={git="https://github.com/Owner/leaf",rev="' + "c"*40 + '"}\n'
                   '[dev-dependencies]\nhelper_dev={git="https://github.com/Owner/helper-dev",branch="main"}\n')
        self.write("unrelated/Cargo.toml", '[package]\nname="unrelated"\nversion="0.1.0"\n'
                   '[dependencies]\nunrelated={git="https://github.com/Owner/unrelated",branch="main"}\n')
        return selected

    def test_dependency_root_retains_excluded_package_and_inherited_build_path_edges(self):
        selected = self.dependency_workspace()
        graph = self.source_graph()
        reached = graph.collect([selected], dependency_roots=True)
        self.assertIn(selected, reached)
        self.assertIn(self.root / "helper/Cargo.toml", reached)
        self.assertNotIn(self.root / "unrelated/Cargo.toml", reached)
        self.assertEqual({name for name, spec in graph.dependency_specs}, {"inherited", "helper", "build", "leaf"})
        inherited = dict(graph.dependency_specs)["inherited"]
        self.assertEqual(inherited["rev"], "a"*40)
        self.assertFalse(graph.inconclusive)

    def test_default_workspace_mode_retains_existing_members_and_dev_population(self):
        selected = self.dependency_workspace()
        graph = self.source_graph()
        reached = graph.collect([self.root / "Cargo.toml"])
        self.assertIn(self.root / "unrelated/Cargo.toml", reached)
        self.assertNotIn(selected, reached)
        self.assertIn("helper_dev", dict(graph.dependency_specs))
        self.assertIn("unrelated", dict(graph.dependency_specs))

    def test_dependency_root_missing_inheritance_and_missing_path_remain_inconclusive(self):
        selected = self.dependency_workspace()
        selected.write_text('[package]\nname="selected"\nversion="0.1.0"\n[dependencies]\n'
                            'undefined={workspace=true}\nmissing={path="../missing"}\n')
        graph = self.source_graph()
        graph.collect([selected], dependency_roots=True)
        self.assertTrue(any("undefined workspace dependency" in row for row in graph.inconclusive))
        self.assertTrue(any("missing/Cargo.toml" in row for row in graph.inconclusive))

    def test_dependency_spec_projection_resets_between_contexts(self):
        selected = self.dependency_workspace()
        graph = self.source_graph()
        graph.collect([self.root / "Cargo.toml"])
        self.assertIn("unrelated", dict(graph.dependency_specs))
        graph.collect([selected], dependency_roots=True)
        self.assertNotIn("unrelated", dict(graph.dependency_specs))
        self.assertEqual({name for name, spec in graph.dependency_specs}, {"inherited", "helper", "build", "leaf"})

    def test_nonliteral_assembly_recipe_refuses_instead_of_omitting_tool(self):
        recipe = self.root / closure._RECIPE_INPUTS[-1]
        recipe.write_text(recipe.read_text().replace('path: "src/tools/targo"', 'path: runtime_path'))
        with patch.object(closure, "_fetch") as fetch:
            with self.assertRaisesRegex(RuntimeError, "nonliteral ToolBuild path"):
                self.run_closure()
        fetch.assert_not_called()

    def test_literal_shared_assembly_recipe_keeps_complete_manifest_population(self):
        recipe = self.root / closure._RECIPE_INPUTS[-1]
        before = closure.stage0_bootstrap_manifest_roots(self.root)
        recipe.write_text(recipe.read_text().replace(
            "fn ensure_default_verifier_tool_bins() {",
            "fn ensure_default_verifier_tool_bins() { ensure_verifier_tool_bins(builder, target_compiler, sysroot, false); }\n"
            "fn ensure_verifier_tool_bins() {",
        ))
        self.assertEqual(closure.stage0_bootstrap_manifest_roots(self.root), before)
        with patch.object(closure, "_fetch") as fetch:
            report = self.run_closure()
        self.assertEqual(len(report["completed_fetches"]), len(before))
        self.assertEqual(fetch.call_count, len(before))

    def test_shared_assembly_recipe_refuses_missing_ambiguous_dynamic_or_recursive_owner(self):
        recipe = self.root / closure._RECIPE_INPUTS[-1]
        original = recipe.read_text()
        delegated = original.replace(
            "fn ensure_default_verifier_tool_bins() {",
            "fn ensure_default_verifier_tool_bins() { ensure_verifier_tool_bins(builder, target_compiler, sysroot, false); }\n"
            "fn ensure_verifier_tool_bins() {",
        )
        mutants = [
            delegated.replace("fn ensure_verifier_tool_bins()", "fn different_owner()"),
            delegated + '\nfn ensure_verifier_tool_bins() { ToolBuild { path: "src/tools/targo", }; }',
            delegated.replace("sysroot, false);", "sysroot, runtime_flag);"),
            delegated.replace('path: "first-party/ty/crates/tla-cli"', 'path: runtime_path'),
            original.replace(
                "fn ensure_default_verifier_tool_bins() {",
                "fn ensure_default_verifier_tool_bins() { ensure_verifier_tool_bins(builder, target_compiler, sysroot, false); }\n"
                "fn ensure_verifier_tool_bins() { ensure_verifier_tool_bins(builder, target_compiler, sysroot, false); }\n"
                "fn unreachable_recipe() {",
            ),
        ]
        for mutant in mutants:
            with self.subTest(mutant=mutants.index(mutant)):
                recipe.write_text(mutant)
                with patch.object(closure, "_fetch") as fetch:
                    with self.assertRaisesRegex(RuntimeError, "stage0 manifest roots:"):
                        self.run_closure()
                fetch.assert_not_called()

    def test_actual_source_shared_assembly_recipe_has_nonempty_declared_roots(self):
        # Inspect the actual source declarations, independent of whether this
        # checkout has yet materialized optional first-party worktrees.
        relative = closure._stage0_tool_recipe_paths((REPO / closure._RECIPE_INPUTS[-1]).read_text())
        for path in ["targo-trust/Cargo.toml", "first-party/ty/crates/tla-cli/Cargo.toml",
                     "first-party/clean/crates/clean/Cargo.toml", "src/tools/targo/Cargo.toml",
                     "src/tools/trustup/Cargo.toml"]:
            self.assertIn(path, relative)

    def test_mutually_recursive_shared_recipes_refuse_before_any_fetch(self):
        recipe = self.root / closure._RECIPE_INPUTS[-1]
        recipe.write_text('''
fn ensure_default_verifier_tool_bins() {
    ensure_verifier_tool_bins(builder, target_compiler, sysroot, false);
}
fn ensure_verifier_tool_bins() { build_trustd_tool(builder); }
fn build_trustd_tool() { ensure_verifier_tool_bins(builder); }
fn ensure_user_facing_tools() { ToolBuild { path: "src/tools/targo", }; }
''')
        with patch.object(closure, "_fetch") as fetch:
            with self.assertRaisesRegex(RuntimeError, "cyclic tool recipe graph"):
                self.run_closure()
        fetch.assert_not_called()

    def test_recipe_symlink_outside_source_refuses(self):
        with tempfile.TemporaryDirectory() as outside:
            ty = self.root / "first-party/ty/crates/tla-cli/Cargo.toml"
            external = Path(outside) / "Cargo.toml"
            external.write_text("[workspace]\n")
            ty.unlink()
            ty.symlink_to(external)
            with patch.object(closure, "_fetch") as fetch:
                with self.assertRaisesRegex(RuntimeError, "escapes checkout"):
                    self.run_closure()
            fetch.assert_not_called()

    def test_missing_locked_git_revision_is_a_refusal_not_skew_warning(self):
        with patch.object(closure, "_fetch", side_effect=closure.DependencyClosureError(
                "can't checkout ay b1b0b9de07af146c1244633189f92971a3347db9 in offline mode")):
            with self.assertRaisesRegex(closure.DependencyClosureError, "b1b0b9de"):
                self.run_closure()

    def test_missing_registry_archive_is_also_a_refusal(self):
        with patch.object(closure, "_fetch", side_effect=closure.DependencyClosureError(
                "failed to download libc: attempting HTTP request, but --offline specified")):
            with self.assertRaisesRegex(closure.DependencyClosureError, "--offline"):
                self.run_closure()

    def test_changed_ty_lock_refuses_instead_of_reporting_ready(self):
        def change(*_args):
            self.write("first-party/ty/crates/tla-cli/Cargo.lock", "version = 3\n")
        with patch.object(closure, "_fetch", side_effect=change):
            with self.assertRaisesRegex(closure.DependencyClosureError, "inputs changed"):
                self.run_closure()

    def test_added_cargo_home_config_refuses_instead_of_reusing_prior_authority(self):
        def change(*_args):
            self.write("cache/config.toml", "[net]\noffline = true\n")
        with patch.object(closure, "_fetch", side_effect=change):
            with self.assertRaisesRegex(closure.DependencyClosureError, "inputs changed"):
                self.run_closure()

    def test_changed_driver_bytes_refuse(self):
        with patch.object(closure, "_fetch", side_effect=lambda *_a: self.driver.write_text("new")):
            with self.assertRaisesRegex(closure.DependencyClosureError, "inputs changed"):
                self.run_closure()

    def test_missing_driver_refuses_before_any_fetch(self):
        self.driver.unlink()
        with patch.object(closure, "_fetch") as fetch:
            with self.assertRaisesRegex(closure.DependencyClosureError, "Targo is missing"):
                self.run_closure()
        fetch.assert_not_called()

    def test_relative_driver_is_interpreted_at_actual_build_cwd(self):
        with patch.object(closure, "_fetch") as fetch:
            closure.dependency_closure(self.root, "bin/targo", self.env)
        self.assertEqual(fetch.call_args.args[0][0], str(self.driver))

    def test_expired_original_budget_cannot_start_fetch(self):
        with patch.object(closure.subprocess, "Popen") as spawn, \
                patch.object(closure.os, "posix_spawn", create=True) as custodian:
            with self.assertRaisesRegex(closure.DependencyClosureError, "deadline exhausted"):
                self.run_closure(deadline=time.monotonic() - 1)
        spawn.assert_not_called()
        custodian.assert_not_called()

    def test_darwin_fetch_dispatches_only_to_the_retirement_custodian(self):
        # A Darwin fetch has one route: the per-fetch custodian, with the caller's
        # command, root, environment, deadline and item bound. It never starts a raw child.
        command, end, bound = ["targo", "fetch"], time.monotonic() + 30, object()
        with patch.object(closure.sys, "platform", "darwin"), \
                patch.object(closure.subprocess, "Popen") as spawn, \
                patch.object(closure.os, "posix_spawn", create=True) as native_spawn, \
                patch.object(closure, "_fetch_darwin") as custodian:
            closure._fetch(command, self.root, self.env, end)
            closure._fetch(command, self.root, self.env, end, bound)
        self.assertEqual(custodian.call_args_list, [call(command, self.root, self.env, end, None),
                                                    call(command, self.root, self.env, end, bound)])
        spawn.assert_not_called()
        native_spawn.assert_not_called()

    def test_darwin_without_custodian_primitives_refuses_before_child_dispatch(self):
        # No custodian, no child: each missing primitive refuses before birth. The
        # actual native child is harmless; it leaves this marker only if it ran.
        marker = self.root / "unowned-child-started"
        command = [sys.executable, "-c", f"from pathlib import Path; Path({str(marker)!r}).touch()"]
        cases = {
            "kqueue": lambda: patch.object(closure.select, "kqueue", None, create=True),
            "libproc": lambda: patch.object(closure, "_darwin_libproc", return_value=None),
            "sigchld": lambda: patch.object(closure.signal, "getsignal", return_value=closure.signal.SIG_IGN),
            "posix_spawn": lambda: patch.object(closure.os, "posix_spawn", None, create=True),
        }
        for name, missing in cases.items():
            with self.subTest(name), patch.object(closure.sys, "platform", "darwin"), missing():
                with self.assertRaisesRegex(closure.DependencyClosureError,
                                            "retirement custodian, unavailable here: .*no child was started"):
                    closure._fetch_darwin(command, self.root, self.env, time.monotonic() + 10)
            self.assertFalse(marker.exists(), f"a child ran without its custodian ({name})")

    def test_darwin_group_signals_only_while_the_custodian_is_unreaped(self):
        """Source-model control (any host): every killpg of the custodian's group
        precedes its reap, nothing is signalled after it, and no numeric PID but the
        pinned group is signalled. A census that never empties leaves it unreaped."""
        class Events:
            def __init__(self, exit_after):
                self.exit_after = exit_after
            def control(self, changes, count, timeout=None):
                if self.exit_after is None:
                    return []
                if isinstance(self.exit_after, BaseException):
                    raise self.exit_after
                return [types.SimpleNamespace(ident=54321, flags=0, fflags=closure.select.KQ_NOTE_EXIT
                                              if hasattr(closure.select, "KQ_NOTE_EXIT") else 1, data=0)]
            def close(self):
                pass

        scenarios = {
            "timeout": (None, [[54321, 77], [54321, 77], []], "total budget expired"),
            "interrupt": (KeyboardInterrupt(), [[54321, 77], [54321, 77], []], KeyboardInterrupt),
            # No custodian ran, so no report: the straggler is named in that refusal.
            "straggler": ("exit", [[77], [77], [77], [77], []], r"ended before reporting .*\[77\] was retired"),
            "never-empty": (None, None, "not retired"),
            # 70 forks 71 and exits between the listing and its state read; the
            # second listing exposes 71, so it is named and retired, not missed.
            "hidden-child": ("exit", [[54321, 70], [54321, 70, 71], [54321, 70, 71], [54321, 70, 71],
                                      [54321, 70, 71], []], r"ended before reporting .*\[71\] was retired"),
            # A census libproc cannot take is never an empty group: no reap.
            "census-fails": ("exit", OSError(1, "census refused"), "not retired"),
        }
        for name, (exit_after, censuses, outcome) in scenarios.items():
            with self.subTest(name), ExitStack() as stack:
                calls = []
                remaining = list(censuses) if isinstance(censuses, list) else None
                def members(lib, pgid, required=None):
                    calls.append(("census", pgid))
                    if isinstance(censuses, OSError):
                        raise censuses
                    if remaining is None:
                        return [77]
                    return remaining.pop(0) if len(remaining) > 1 else remaining[0]
                stack.enter_context(patch.object(closure.sys, "platform", "darwin"))
                stack.enter_context(patch.object(closure, "_darwin_prerequisites", return_value=object()))
                stack.enter_context(patch.object(closure, "_darwin_group_members", side_effect=members))
                stack.enter_context(patch.object(closure, "_darwin_live",
                                                 side_effect=lambda lib, pid: pid not in (54321, 70)))
                stack.enter_context(patch.object(closure.os, "posix_spawn", return_value=54321, create=True))
                stack.enter_context(patch.object(closure, "_darwin_kevent_exit",
                                                 side_effect=lambda e, pid, t: exit_after == "exit"))
                events = Events(exit_after if exit_after != "exit" else None)
                stack.enter_context(patch.object(closure.select, "kqueue", return_value=events, create=True))
                stack.enter_context(patch.object(closure.os, "killpg", create=True,
                                                 side_effect=lambda pgid, sig: calls.append(("killpg", pgid, sig))))
                stack.enter_context(patch.object(closure.os, "waitpid",
                                                 side_effect=lambda pid, flags: calls.append(("waitpid", pid)) or (pid, 0)))
                kill = stack.enter_context(patch.object(closure.os, "kill"))
                spawn = stack.enter_context(patch.object(closure.subprocess, "Popen"))
                end = time.monotonic() + (5.3 if name in ("timeout", "never-empty", "census-fails") else 30)
                if isinstance(outcome, type):
                    with self.assertRaises(outcome):
                        closure._fetch_darwin(["targo", "fetch"], self.root, self.env, end)
                else:
                    with self.assertRaisesRegex(closure.DependencyClosureError, outcome):
                        closure._fetch_darwin(["targo", "fetch"], self.root, self.env, end)
                kill.assert_not_called()
                spawn.assert_not_called()
                signals = [call for call in calls if call[0] == "killpg"]
                if name == "census-fails":
                    self.assertFalse([call for call in calls if call[0] == "waitpid"],
                                     "a group no census could read was reaped")
                    continue
                self.assertTrue(signals, "the live group was never signalled")
                self.assertTrue(all(call[1] == 54321 for call in signals))
                reaps = [index for index, call in enumerate(calls) if call[0] == "waitpid"]
                if name == "never-empty":
                    self.assertEqual(reaps, [], "a group that still lives was reaped")
                else:
                    self.assertEqual(len(reaps), 1)
                    self.assertFalse([call for call in calls[reaps[0]:] if call[0] == "killpg"],
                                     "a signal followed the reap")

    def fresh_home_clock(self, first_use_seconds):
        """A clock on which the first fetch's child takes `first_use_seconds`, as a cargo
        home holding only archives and git databases does while it materializes."""
        now = [time.monotonic()]
        child = Mock(pid=54321, returncode=None)
        waits = []

        def wait(timeout=None):
            waits.append(timeout)
            if len(waits) == 1:
                now[0] += first_use_seconds
            return 0

        child.wait.side_effect = wait
        # Model the retained Linux pidfd path, not unavailable Darwin custody.
        self.process_mocks("linux", child)
        stack = ExitStack()
        self.addCleanup(stack.close)
        stack.enter_context(patch.object(closure.time, "monotonic", side_effect=lambda: now[0]))
        stack.enter_context(redirect_stderr(io.StringIO()))
        return now

    def test_default_budget_admits_a_fresh_cargo_homes_first_use(self):
        # 190 s: the 182 s measured on m2 (2026-11-05) for a mint-shaped home, rounded up.
        self.fresh_home_clock(190.0)
        report = self.run_closure()
        self.assertEqual(len(report["completed_fetches"]), 8)
        self.assertEqual(closure.DEFAULT_BUDGET_SECONDS, 900.0)

    def test_the_former_180_second_budget_refuses_that_first_use(self):
        now = self.fresh_home_clock(190.0)
        with self.assertRaisesRegex(closure.DependencyClosureError, "deadline exhausted"):
            self.run_closure(deadline=now[0] + 180.0)

    def test_per_recipe_failure_is_reported_without_resetting_the_original_deadline(self):
        deadline = time.monotonic() + 20
        progress = io.StringIO()
        with patch.object(closure, "_fetch", side_effect=[None, closure.DependencyClosureError("custody unresolved")]) as fetch, \
                redirect_stderr(progress):
            with self.assertRaisesRegex(closure.DependencyClosureError, "2/16 caller-network-policy.*custody unresolved"):
                self.run_closure(prepare=True, deadline=deadline)
        self.assertEqual(fetch.call_count, 2)
        self.assertEqual([call.args[3] for call in fetch.call_args_list], [deadline, deadline])
        self.assertIn("1/16 caller-network-policy Cargo.toml: command exited zero; inputs unchanged", progress.getvalue())
        self.assertIn("2/16 caller-network-policy", progress.getvalue())
        self.assertIn("refused after", progress.getvalue())
        self.assertEqual(progress.getvalue().count("command exited zero; inputs unchanged"), 1)

    @unittest.skipUnless(hasattr(os, "pread"), "positional diagnostic reads unavailable")
    def test_pending_output_tail_is_bounded_and_does_not_move_the_writer_cursor(self):
        with tempfile.TemporaryFile() as output:
            output.write(b"prefix" + b"x" * 5000)
            output.flush()
            output.seek(17)
            tail = closure._diagnostic_tail_without_seeking(output)
            self.assertEqual(tail, "x" * 4096)
            self.assertEqual(output.tell(), 17)

    def test_broken_refusal_progress_preserves_the_original_custody_failure(self):
        class BrokenRefusalOutput:
            def write(self, text):
                if ": refused after" in text:
                    raise BrokenPipeError("diagnostic pipe closed")
                return len(text)

            def flush(self):
                pass

        original = closure.DependencyClosureError("original custody refusal")
        with patch.object(closure, "_fetch", side_effect=original), \
                redirect_stderr(BrokenRefusalOutput()):
            with self.assertRaisesRegex(closure.DependencyClosureError,
                                        "original custody refusal.*progress output failed") as caught:
                self.run_closure()
        self.assertIs(caught.exception.__cause__, original)

    def process_mocks(self, platform, child):
        """No real PID, pidfd, signal, or child wait is used by these controls."""
        stack = ExitStack()
        self.addCleanup(stack.close)
        mocks = {}
        stack.enter_context(patch.object(closure.sys, "platform", platform))
        stack.enter_context(patch.object(closure.signal, "getsignal", return_value=closure.signal.SIG_DFL))
        mocks["spawn"] = stack.enter_context(patch.object(closure.subprocess, "Popen", return_value=child))
        mocks["open"] = stack.enter_context(patch.object(closure.os, "pidfd_open", return_value=91, create=True))
        mocks["send"] = stack.enter_context(patch.object(closure.signal, "pidfd_send_signal", create=True))
        mocks["close"] = stack.enter_context(patch.object(closure.os, "close"))
        mocks["killpg"] = stack.enter_context(patch.object(closure.os, "killpg", create=True))
        mocks["kill"] = stack.enter_context(patch.object(closure.os, "kill"))
        return mocks

    def assert_no_numeric_signal(self, child, mocks):
        mocks["killpg"].assert_not_called()
        mocks["kill"].assert_not_called()
        child.kill.assert_not_called()

    def test_linux_timeout_uses_retained_pidfd_and_original_deadline(self):
        child = Mock(pid=54321, returncode=None)
        child.wait.side_effect = [subprocess.TimeoutExpired(["targo", "fetch"], 1), 0]
        mocks = self.process_mocks("linux", child)
        end = time.monotonic() + 6
        with self.assertRaises(subprocess.TimeoutExpired):
            closure._fetch(["targo", "fetch"], self.root, self.env, end)
        mocks["open"].assert_called_once_with(54321, 0)
        mocks["send"].assert_called_once_with(91, closure.signal.SIGKILL)
        mocks["close"].assert_called_once_with(91)
        self.assert_no_numeric_signal(child, mocks)
        self.assertLessEqual(child.wait.call_args.kwargs["timeout"], 6)

    def test_linux_already_reaped_on_interrupt_never_signals_reused_numeric_identity(self):
        child = Mock(pid=54321, returncode=None)
        events = []
        mocks = self.process_mocks("linux", child)
        mocks["open"].side_effect = lambda *_args: events.append("pidfd-open") or 91
        calls = 0
        def interrupted_wait(**_kwargs):
            nonlocal calls
            calls += 1
            events.append("wait")
            if calls == 1:
                # Model the gap AFTER waitpid reaped the original child but
                # BEFORE Popen stored its returncode. That PID/PGID may now
                # denote another process; returncode deliberately remains None.
                raise KeyboardInterrupt
            return 0
        child.wait.side_effect = interrupted_wait
        def original_identity_gone(*_args):
            events.append("pidfd-signal")
            raise ProcessLookupError("the retained original kernel process is gone")
        mocks["send"].side_effect = original_identity_gone
        with self.assertRaises(KeyboardInterrupt):
            closure._fetch(["targo", "fetch"], self.root, self.env, time.monotonic() + 6)
        self.assertEqual(events, ["pidfd-open", "wait", "pidfd-signal", "wait"])
        self.assert_no_numeric_signal(child, mocks)
        mocks["close"].assert_called_once_with(91)

    def test_pidfd_acquisition_failure_never_falls_back_to_numeric_signal(self):
        child = Mock(pid=54321, returncode=None)
        child.wait.return_value = 0
        mocks = self.process_mocks("linux", child)
        mocks["open"].side_effect = PermissionError("pidfd unavailable")
        with self.assertRaises(PermissionError):
            closure._fetch(["targo", "fetch"], self.root, self.env, time.monotonic() + 6)
        mocks["send"].assert_not_called()
        mocks["close"].assert_not_called()
        self.assert_no_numeric_signal(child, mocks)

    def test_linux_success_closes_pidfd_without_any_signal(self):
        child = Mock(pid=54321, returncode=None)
        child.wait.return_value = 0
        mocks = self.process_mocks("linux", child)
        closure._fetch(["targo", "fetch"], self.root, self.env, time.monotonic() + 6)
        mocks["open"].assert_called_once_with(54321, 0)
        mocks["close"].assert_called_once_with(91)
        mocks["send"].assert_not_called()
        self.assert_no_numeric_signal(child, mocks)

    def test_linux_custom_or_auto_reaping_sigchld_refuses_before_spawn(self):
        child = Mock(pid=54321, returncode=None)
        mocks = self.process_mocks("linux", child)
        with patch.object(closure.signal, "getsignal", return_value=closure.signal.SIG_IGN):
            with self.assertRaisesRegex(closure.DependencyClosureError, "default SIGCHLD custody"):
                closure._fetch(["targo", "fetch"], self.root, self.env, time.monotonic() + 6)
        mocks["spawn"].assert_not_called()
        self.assert_no_numeric_signal(child, mocks)

    def test_linux_missing_pidfd_api_refuses_before_spawn(self):
        child = Mock(pid=54321, returncode=None)
        mocks = self.process_mocks("linux", child)
        with patch.object(closure, "hasattr", side_effect=lambda obj, name:
                          name != "pidfd_open" and hasattr(obj, name), create=True):
            with self.assertRaisesRegex(closure.DependencyClosureError, "retained pidfd authority"):
                closure._fetch(["targo", "fetch"], self.root, self.env, time.monotonic() + 6)
        mocks["spawn"].assert_not_called()
        self.assert_no_numeric_signal(child, mocks)

    def test_exception_cleanup_cannot_append_wait_time_after_original_end(self):
        child = Mock(pid=54321, returncode=None)
        child.wait.side_effect = subprocess.TimeoutExpired(["fetch"], 5)
        mocks = self.process_mocks("linux", child)
        with patch.object(closure.time, "monotonic", side_effect=[100.0, 100.0, 111.0]):
            with self.assertRaisesRegex(closure.DependencyClosureError, "original deadline"):
                closure._fetch(["targo", "fetch"], self.root, self.env, 110.0)
        self.assertEqual(child.wait.call_count, 1)
        mocks["send"].assert_called_once_with(91, closure.signal.SIGKILL)
        mocks["close"].assert_called_once_with(91)
        self.assert_no_numeric_signal(child, mocks)

    def run_cli(self, *, mode="check", environment=None, targo=None, extra=()):
        output, diagnostic = io.StringIO(), io.StringIO()
        arguments = [str(HELPER), mode, "--repo-root", str(self.root),
                     "--targo", str(self.driver) if targo is None else targo, *extra]
        with patch.object(sys, "argv", arguments), \
                patch.dict(os.environ, self.env if environment is None else environment, clear=True), \
                redirect_stdout(output), redirect_stderr(diagnostic):
            result = closure.main()
        return result, output.getvalue(), diagnostic.getvalue()

    def test_cli_check_runs_the_complete_offline_recipe_envelope(self):
        with patch.object(closure, "_fetch") as fetch:
            result, output, _diagnostic = self.run_cli()
        self.assertEqual(result, 0)
        report = json.loads(output)
        expected = {str(path) for path in closure.stage0_bootstrap_manifest_roots(self.root)}
        self.assertEqual({call.args[0][-1] for call in fetch.call_args_list}, expected)
        self.assertEqual(len(report["completed_fetches"]), len(expected))
        self.assertTrue(all(call.args[0][:4] == [str(self.driver), "fetch", "--locked", "--offline"]
                            for call in fetch.call_args_list))
        # One CLI invocation supplies one original endpoint to every recipe.
        self.assertEqual(len({call.args[3] for call in fetch.call_args_list}), 1)

    @patch.object(closure.sys, "platform", "linux")
    def test_cli_disabled_legacy_opt_in_cannot_skip_missing_clean_git_input(self):
        def fetch(command, *_arguments):
            if "first-party/clean/" in command[-1]:
                raise closure.DependencyClosureError("missing locked Git backend in offline mode")

        with patch.object(closure, "_fetch", side_effect=fetch):
            result, output, diagnostic = self.run_cli(
                environment={**self.env, "TRUST_BOOTSTRAP_OFFLINE_CLOSURE": "0"})
        self.assertEqual(result, 1)
        self.assertEqual(output, "")
        self.assertIn("missing locked Git backend", diagnostic)
        self.assertIn("bootstrap dependency closure REFUSED:", diagnostic)
        self.assertIn("Prepare the SAME source and Cargo home", diagnostic)

    def test_cli_cancellation_is_not_translated_into_success_or_recovery(self):
        diagnostic = io.StringIO()
        arguments = [str(HELPER), "check", "--repo-root", str(self.root),
                     "--targo", str(self.driver)]
        with patch.object(sys, "argv", arguments), \
                patch.dict(os.environ, self.env, clear=True), \
                patch.object(closure, "_fetch", side_effect=KeyboardInterrupt) as fetch, \
                redirect_stderr(diagnostic):
            with self.assertRaises(KeyboardInterrupt):
                closure.main()
        self.assertEqual(fetch.call_count, 1)
        self.assertNotIn("Prepare the SAME source", diagnostic.getvalue())

    # Trust: explicit invalid empty policies reach the actual checker unchanged.
    # A recovery command also preserves absence against a different shell.
    @patch.object(closure.sys, "platform", "linux")
    def test_cli_warning_policy_presence_and_values_survive_fetch_and_recovery(self):
        policies = ({}, {"CARGO_BUILD_WARNINGS": "warn"},
                    {"CARGO_BUILD_WARNINGS": "deny"}, {"CARGO_BUILD_WARNINGS": ""},
                    {"TARGO_BUILD_WARNINGS": "deny"}, {"TARGO_BUILD_WARNINGS": ""},
                    {"CARGO_BUILD_WARNINGS": "", "TARGO_BUILD_WARNINGS": "warn"})
        for policy in policies:
            with self.subTest(policy=policy):
                with patch.object(closure, "_fetch", side_effect=closure.DependencyClosureError(
                        "explicit operator policy retained")) as fetch:
                    result, output, diagnostic = self.run_cli(environment={**self.env, **policy})
                self.assertEqual(result, 1)
                self.assertEqual(output, "")
                received = fetch.call_args.args[2]
                for key in ("CARGO_BUILD_WARNINGS", "TARGO_BUILD_WARNINGS"):
                    self.assertEqual(key in received, key in policy)
                    if key in policy:
                        self.assertEqual(received[key], policy[key])
                command = shlex.split(diagnostic.splitlines()[-1])
                self.assertEqual(command[:5],
                                 ["env", "-u", "CARGO_BUILD_WARNINGS", "-u", "TARGO_BUILD_WARNINGS"])
                assignments = []
                for word in command[5:]:
                    if word == sys.executable:
                        break
                    assignments.append(word)
                self.assertEqual(assignments, ["CARGO_HOME=" + self.env["CARGO_HOME"],
                                               *(key + "=" + policy[key] for key in
                                                 ("CARGO_BUILD_WARNINGS", "TARGO_BUILD_WARNINGS")
                                                 if key in policy)])

    # Trust: never guess a default cache when explaining a failed invocation.
    @patch.object(closure.sys, "platform", "linux")
    def test_cli_recovery_hint_binds_same_cargo_home_driver_and_python(self):
        cache_link = self.root / "literal cache link"
        cache_link.symlink_to(self.root / "actual cache", target_is_directory=True)
        for cargo_home in ("relative cache 'quoted'", str(cache_link), None, ""):
            with self.subTest(cargo_home=cargo_home):
                environment = {"HOME": str(self.root / "user home")}
                if cargo_home is not None:
                    environment["CARGO_HOME"] = cargo_home
                with patch.object(closure, "_fetch", side_effect=closure.DependencyClosureError("missing input")):
                    result, _output, diagnostic = self.run_cli(
                        environment=environment, targo="bin/targo")
                self.assertEqual(result, 1)
                if not cargo_home:
                    self.assertIn("no preparation command", diagnostic)
                    continue
                command = shlex.split(diagnostic.splitlines()[-1])
                expected = cargo_home if os.path.isabs(cargo_home) else str(self.root / cargo_home)
                self.assertEqual(command[5], "CARGO_HOME=" + expected)
                self.assertEqual(command[6:10], [sys.executable, "-I", "-S", "-B"])
                self.assertEqual(command[10:],
                                 [str(HELPER.resolve()), "prepare", "--repo-root", str(self.root),
                                  "--targo", str(self.driver)])

        result, _output, diagnostic = self.run_cli(environment={})
        self.assertEqual(result, 1)
        self.assertIn("CARGO_HOME and the user home are both unknown", diagnostic)
        self.assertIn("no preparation command", diagnostic)

    # Trust: exercise the printed argv without a shell, preserving literal input.
    def test_cli_recovery_hint_runs_from_another_directory_without_shell_expansion(self):
        allow = self.root / "allow-fetch"
        trace = self.root / "hint-fetch-trace"
        raw_home = "cache 'literal' $(touch OWNED_INJECTION)"
        expected = str(self.root / raw_home)
        self.write_python_driver(
            "import os, pathlib, sys\n"
            f"if not pathlib.Path({str(allow)!r}).exists(): sys.exit(17)\n"
            f"assert os.environ['CARGO_HOME'] == {expected!r}\n"
            "assert 'CARGO_BUILD_WARNINGS' not in os.environ\n"
            "assert os.environ['TARGO_BUILD_WARNINGS'] == ''\n"
            f"with open({str(trace)!r}, 'a') as f: f.write('fetch\\n')\n")
        result, _output, diagnostic = self.run_cli(
            environment={**self.env, "CARGO_HOME": raw_home, "TARGO_BUILD_WARNINGS": ""})
        self.assertEqual(result, 1)
        command = shlex.split(diagnostic.splitlines()[-1])
        allow.touch()
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir()
        child = subprocess.run(
            command, cwd=elsewhere,
            env={**self.env, "CARGO_HOME": "wrong cache", "CARGO_BUILD_WARNINGS": "deny",
                 "TARGO_BUILD_WARNINGS": "warn"},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)
        self.assertEqual(child.returncode, 0, child.stderr)
        self.assertEqual(len(trace.read_text().splitlines()),
                         2 * len(closure.stage0_bootstrap_manifest_roots(self.root)))
        self.assertFalse((elsewhere / "OWNED_INJECTION").exists())
        self.assertFalse((self.root / "OWNED_INJECTION").exists())

    @patch.object(closure.sys, "platform", "linux")
    def test_cli_unresolvable_root_keeps_original_refusal_without_a_recovery_command(self):
        loop = self.root / "looping-root"
        loop.symlink_to(loop, target_is_directory=True)
        with patch.object(closure, "_fetch") as fetch:
            result, output, diagnostic = self.run_cli(extra=("--repo-root", str(loop)))
        self.assertEqual(result, 1)
        self.assertEqual(output, "")
        self.assertTrue(diagnostic.startswith("bootstrap dependency closure REFUSED:"))
        self.assertIn("looping-root", diagnostic)
        self.assertIn("Recovery command unavailable; no preparation command can be bound", diagnostic)
        self.assertNotIn("Prepare the SAME source", diagnostic)
        fetch.assert_not_called()

    def test_cli_argument_errors_do_not_start_fetch(self):
        for extra in (("--timeout", "5"), ("--unknown-preparation-policy",)):
            with self.subTest(extra=extra), patch.object(closure, "_fetch") as fetch:
                with self.assertRaises(SystemExit) as caught:
                    self.run_cli(extra=extra)
                self.assertEqual(caught.exception.code, 2)
                fetch.assert_not_called()


    def test_one_source_census_bounds_glob_work_without_dropping_recipe_entries(self):
        self.write("Cargo.toml", '[workspace]\nmembers = ["members/*"]\n')
        members = [self.write(f"members/m{index}/Cargo.toml",
                              f'[package]\nname = "m{index}"\nversion = "0.1.0"\n')
                   for index in range(24)]
        original_glob = Path.glob
        scans = []

        def observed_glob(path, pattern, *args, **kwargs):
            if path == self.root and pattern == "members/*":
                scans.append(pattern)
            return original_glob(path, pattern, *args, **kwargs)

        with patch.object(Path, "glob", observed_glob):
            inputs = closure._source_inputs(
                self.root, [self.root / "Cargo.toml", *members], self.env)
        self.assertTrue(set(members).issubset(inputs))
        self.assertLessEqual(len(scans), 2)

    def test_changed_workspace_membership_refuses_the_same_source_collection(self):
        self.write("Cargo.toml", '[workspace]\nmembers = ["members/*"]\n')
        first = self.write("members/first/Cargo.toml",
                           '[package]\nname = "first"\nversion = "0.1.0"\n')
        original_read = Path.read_text
        changed = False

        def changing_read(path, *args, **kwargs):
            nonlocal changed
            result = original_read(path, *args, **kwargs)
            if path == first and not changed:
                changed = True
                self.write("members/later/Cargo.toml",
                           '[package]\nname = "later"\nversion = "0.1.0"\n')
            return result

        with patch.object(Path, "read_text", changing_read):
            with self.assertRaisesRegex(RuntimeError, "membership changed during source census"):
                closure._source_inputs(self.root, [self.root / "Cargo.toml"], self.env)
        self.assertTrue(changed)

    def test_changed_exclusion_alias_refuses_before_accepting_cached_prefix(self):
        self.write("Cargo.toml", '[workspace]\nmembers = ["members/*"]\nexclude = ["excluded"]\n')
        for name in ("first", "later"):
            self.write(f"members/{name}/Cargo.toml",
                       f'[package]\nname = "{name}"\nversion = "0.1.0"\n')
        alias = self.root / "excluded"
        alias.symlink_to("members/first", target_is_directory=True)
        original_resolve = Path.resolve
        changed = False

        def changing_resolve(path, *args, **kwargs):
            nonlocal changed
            result = original_resolve(path, *args, **kwargs)
            if path == alias and not changed:
                changed = True
                alias.unlink()
                alias.symlink_to("members/later", target_is_directory=True)
            return result

        with patch.object(Path, "resolve", changing_resolve):
            with self.assertRaisesRegex(RuntimeError, "member/exclusion path changed"):
                closure._source_inputs(self.root, [self.root / "Cargo.toml"], self.env)
        self.assertTrue(changed)

    def test_workspace_glob_symlink_escape_still_refuses(self):
        self.write("Cargo.toml", '[workspace]\nmembers = ["members/*"]\n')
        with tempfile.TemporaryDirectory() as directory:
            external = Path(directory).resolve()
            (external / "Cargo.toml").write_text('[package]\nname = "outside"\n')
            (self.root / "members").mkdir()
            (self.root / "members/outside").symlink_to(external, target_is_directory=True)
            with self.assertRaisesRegex(RuntimeError, "escapes checkout"):
                closure._source_inputs(self.root, [self.root / "Cargo.toml"], self.env)


class RecipeLexerComplexityTests(unittest.TestCase):
    def test_recipe_shadow_has_linear_source_copy_volume(self):
        class ObservedSource(str):
            copied = 0

            def __getitem__(self, key):
                result = super().__getitem__(key)
                if isinstance(key, slice):
                    self.copied += len(result)
                return result

        source = ObservedSource("let plain = value; let raw = r##\"inert { }\"##;\n" * 300)
        shadow = closure._stage0_rust_code(source)
        self.assertEqual(len(shadow), len(source))
        self.assertEqual(shadow.count("\n"), source.count("\n"))
        # This is an allocation-volume control, not a machine latency threshold.
        # The previous per-character suffix match copies many source lengths.
        self.assertLessEqual(source.copied, len(source) * 2)

    def test_offset_raw_and_escaped_character_end_positions_stay_exact(self):
        prefix = "fn keep<'a>(value: &'a str) { let first = 1; }\n"
        raw = 'br###"inert } r#\" decoy\n/* still inert */"###'
        char = r"'\u{7b}'"
        source = prefix + raw + "; let c = " + char + "; fn after() {}"
        blank = lambda text: "".join("\n" if c == "\n" else " " for c in text)
        expected = prefix + blank(raw) + "; let c = " + blank(char) + "; fn after() {}"
        self.assertEqual(closure._stage0_rust_code(source), expected)
        with self.assertRaisesRegex(RuntimeError, "unclosed raw recipe string"):
            closure._stage0_rust_code(prefix + 'br###"never closed')


class PreparationRequestTests(unittest.TestCase):
    """Source request construction only; every external execution is forbidden."""
    setUp = DependencyClosureTests.setUp
    write = DependencyClosureTests.write

    def inputs(self, *, deadline=None):
        self.end = time.monotonic() + 30 if deadline is None else deadline
        names = ("bootstrap_dependency_preparation.py", "bootstrap_dependency_closure.py",
                 "seed_custody_source.py", "seed_input_archives.py", "seed_input_records.py")
        for name in names:
            self.write("scripts/" + name, (REPO / "scripts" / name).read_text())
        owner = source_module("preparation_request_loader", self.root / "scripts/seed_custody_source.py")
        import hashlib
        expected = {"scripts/" + name: hashlib.sha256(
            (self.root / "scripts" / name).read_bytes()).hexdigest() for name in names}
        loader = owner.BoundSourceLoader(self.root, expected)
        subject = loader.module("preparation_request_subject",
                                self.root / "scripts/bootstrap_dependency_preparation.py")
        rows = []
        for path in sorted(self.root.rglob("*")):
            if path.is_symlink():
                row = subject.records.link(path, self.end)
            elif path.is_file():
                row, _ = subject.records.regular(path, self.end)
            else:
                continue
            rows.append({"path": path.relative_to(self.root).as_posix(), **row})
        view = subject.archives._CommittedSourceView(self.root, {".": rows}, self.end)
        return subject, view

    def request(self, subject, view, *, targo=None, environment=None):
        return subject.preparation_request(
            view, view, str(self.driver) if targo is None else targo,
            self.env if environment is None else environment, deadline=self.end)

    def no_processes(self):
        stack = ExitStack()
        self.addCleanup(stack.close)
        for name in ("run", "Popen", "check_output", "check_call", "call"):
            stack.enter_context(patch.object(subprocess, name,
                side_effect=AssertionError("request must not execute an external process")))
        return stack

    def test_complete_actual_recipe_population_is_derived_without_a_root_mirror(self):
        self.no_processes()
        for relative in closure._RECIPE_INPUTS:
            self.write(relative, (REPO / relative).read_text())

        class DeclaredRecipeFixture:
            # Fixture construction lets the maintained reader enumerate every
            # declaration before materializing synthetic manifests. The request
            # itself accepts only the real committed view created below.
            def path(_, path):
                return path
            def is_file(_, path):
                return path.name == "Cargo.toml" or path.is_file()
            def read_text(_, path):
                return path.read_text()

        roots = closure.stage0_bootstrap_manifest_roots(
            self.root, source_view=DeclaredRecipeFixture())
        self.assertEqual(len(roots), 55)
        self.assertIn(self.root / "crates/trust-certify/Cargo.toml", roots)
        for path in roots:
            self.write(str(path.relative_to(self.root)), "[workspace]\nmembers = []\n")
            self.write(str(path.with_name("Cargo.lock").relative_to(self.root)), "version = 4\n")
        subject, view = self.inputs()
        request = self.request(subject, view)
        self.assertEqual(request.manifests, tuple(roots))
        self.assertEqual(len(request.manifests) * len(request.passes), 110)
        self.assertEqual(request.passes, (subject.FetchPass.CALLER_NETWORK_POLICY,
                                         subject.FetchPass.OFFLINE))
        offline = subject.offline_check_request(view, view, str(self.driver), self.env, deadline=self.end)
        self.assertEqual(offline.manifests, request.manifests)
        self.assertEqual(offline.read_set, request.read_set)
        self.assertEqual(offline.deadline, request.deadline)
        self.assertEqual(offline.passes, (subject.FetchPass.OFFLINE,))
        self.assertEqual(len(offline.manifests) * len(offline.passes), 55)
        with self.assertRaisesRegex(ValueError, "unknown.*pass"):
            offline.environment_for(subject.FetchPass.CALLER_NETWORK_POLICY)
        request.recheck_selection()

    def test_new_optional_recipe_is_kept_and_missing_declared_root_refuses(self):
        self.no_processes()
        self.write("new-optional/Cargo.toml", "[workspace]\nmembers = []\n")
        self.write("new-optional/Cargo.lock", "version = 4\n")
        recipe = self.root / closure._RECIPE_INPUTS[-1]
        recipe.write_text(recipe.read_text() + '\nToolBuild { path: "new-optional", };\n')
        subject, view = self.inputs()
        self.assertIn(self.root / "new-optional/Cargo.toml", self.request(subject, view).manifests)
        (self.root / "new-optional/Cargo.toml").unlink()
        subject, view = self.inputs()
        with self.assertRaisesRegex(RuntimeError, "absent from committed"):
            self.request(subject, view)

    def test_exact_configured_driver_spelling_and_alias_are_retained(self):
        self.no_processes()
        (self.root / "bin/cargo").symlink_to("targo")
        subject, view = self.inputs()
        spelling = "bin/./cargo"
        request = self.request(subject, view, targo=spelling)
        self.assertEqual(request.configured_targo, spelling)
        self.assertEqual(request.targo_path, self.root / "bin/cargo")
        self.assertIn(self.root / "bin/cargo", request.read_set)
        self.assertIn(self.driver, request.read_set)

    def test_copied_environment_keeps_network_and_absent_or_empty_warning_policy(self):
        self.no_processes()
        subject, view = self.inputs()
        for overrides in ({}, {"RUSTFLAGS": "", "TRUST_DENY_WARNINGS": ""},
                          {"RUSTFLAGS": "-Dwarnings", "TRUST_DENY_WARNINGS": "0"}):
            with self.subTest(overrides=overrides):
                env = {**self.env, "CARGO_NET_OFFLINE": "false", **overrides}
                request = self.request(subject, view, environment=env)
                original = dict(env)
                env.clear()
                self.assertEqual(dict(request.environment), original)
                self.assertEqual(dict(request.environment_for(subject.FetchPass.CALLER_NETWORK_POLICY)), original)
                offline = request.environment_for(subject.FetchPass.OFFLINE)
                self.assertEqual(dict(offline), {**original, "CARGO_NET_OFFLINE": "true"})
                with self.assertRaises(TypeError):
                    offline["RUSTFLAGS"] = "changed"
        with self.assertRaisesRegex(ValueError, "unknown.*pass"):
            request.environment_for(True)

    def test_existing_offline_policy_stays_offline_in_both_passes(self):
        self.no_processes()
        subject, view = self.inputs()
        request = self.request(subject, view, environment={**self.env, "CARGO_NET_OFFLINE": "true"})
        self.assertTrue(all(request.environment_for(phase)["CARGO_NET_OFFLINE"] == "true"
                            for phase in request.passes))

    def test_request_read_set_binds_adapter_actual_loader_and_all_loaded_sources(self):
        self.no_processes()
        subject, view = self.inputs()
        request = self.request(subject, view)
        for name in ("bootstrap_dependency_preparation.py", "seed_custody_source.py",
                     "seed_input_archives.py", "seed_input_records.py",
                     "bootstrap_dependency_closure.py", "recreate_bootstrap.py"):
            self.assertIn(self.root / "scripts" / name, request.read_set)
        self.assertIn(self.root / "cache/config", request.read_set)
        self.assertIn(self.root / "cache/config.toml", request.read_set)
        with self.assertRaises(TypeError):
            json.dumps(request)
        self.assertFalse(hasattr(request, "argv"))
        self.assertFalse(hasattr(request, "execute"))

    def test_changed_adapter_or_actual_loader_refuses_original_request_recheck(self):
        self.no_processes()
        for name in ("bootstrap_dependency_preparation.py", "seed_custody_source.py"):
            with self.subTest(name=name):
                subject, view = self.inputs()
                request = self.request(subject, view)
                path = self.root / "scripts" / name
                path.write_text(path.read_text() + "\n# changed original input\n")
                with self.assertRaisesRegex(ValueError, "changed during selection"):
                    request.recheck_selection()

    def test_endpoint_is_mandatory_finite_current_and_within_existing_budget(self):
        self.no_processes()
        subject, view = self.inputs()
        with self.assertRaises(TypeError):
            subject.preparation_request(view, view, str(self.driver), self.env)
        for end in (True, float("nan"), float("inf"), time.monotonic() - 1,
                    time.monotonic() + closure.DEFAULT_BUDGET_SECONDS + 60):
            with self.subTest(end=end):
                view.end = end
                with self.assertRaisesRegex(ValueError, "deadline|budget"):
                    subject.preparation_request(view, view, str(self.driver), self.env, deadline=end)

    def test_different_or_expired_original_endpoint_cannot_be_renewed(self):
        self.no_processes()
        subject, view = self.inputs()
        request = self.request(subject, view)
        self.assertEqual(request.deadline, self.end)
        with patch.object(subject.records.time, "monotonic", return_value=self.end + 1):
            with self.assertRaisesRegex(ValueError, "deadline expired"):
                request.recheck_selection()
        view.end = self.end + 1
        with self.assertRaisesRegex(ValueError, "different original endpoint"):
            request.recheck_selection()

    def test_uncommitted_config_or_changed_lock_cannot_join_the_source_view(self):
        self.no_processes()
        subject, view = self.inputs()
        self.write(".cargo/config.toml", '[net]\noffline = true\n')
        with self.assertRaisesRegex(ValueError, "not committed source"):
            self.request(subject, view)
        (self.root / ".cargo/config.toml").unlink()
        subject, view = self.inputs()
        self.write("first-party/ty/crates/tla-cli/Cargo.lock", "version = 3\n")
        with self.assertRaisesRegex(ValueError, "changed during selection"):
            self.request(subject, view)

    def test_missing_workspace_lock_or_authority_refuses_before_a_request(self):
        self.no_processes()
        (self.root / "first-party/clean/crates/clean/Cargo.lock").unlink()
        subject, view = self.inputs()
        with self.assertRaisesRegex(RuntimeError, "no committed lockfile"):
            self.request(subject, view)
        (self.root / closure._RECIPE_INPUTS[0]).unlink()
        subject, view = self.inputs()
        with self.assertRaisesRegex(ValueError, "required committed bootstrap authority"):
            self.request(subject, view)

    def test_dynamic_recipe_and_escaped_manifest_edge_remain_refusals(self):
        self.no_processes()
        recipe = self.root / closure._RECIPE_INPUTS[-1]
        original = recipe.read_text()
        recipe.write_text(original.replace('path: "src/tools/targo"', 'path: runtime_path'))
        subject, view = self.inputs()
        with self.assertRaisesRegex(RuntimeError, "nonliteral"):
            self.request(subject, view)
        recipe.write_text(original)
        self.write("Cargo.toml", '[workspace]\nmembers = ["../outside"]\n')
        subject, view = self.inputs()
        with self.assertRaisesRegex((RuntimeError, ValueError), "escap|inconclusive"):
            self.request(subject, view)

    def test_paths_or_serialized_view_cannot_replace_the_existing_strict_view(self):
        self.no_processes()
        subject, view = self.inputs()
        for fake in (self.root, {"root": str(self.root), "end": self.end},
                     types.SimpleNamespace(root=self.root, end=self.end)):
            with self.subTest(fake=type(fake).__name__):
                with self.assertRaisesRegex(ValueError, "committed source view"):
                    subject.preparation_request(fake, view, str(self.driver), self.env,
                                                deadline=self.end)


class CapturedDependencySelectionTests(unittest.TestCase):
    """Captured-source DATA through the real selector; no native owner claim."""
    setUp = DependencyClosureTests.setUp
    write = DependencyClosureTests.write
    inputs = PreparationRequestTests.inputs
    no_processes = PreparationRequestTests.no_processes

    def capture(self):
        self.no_processes()
        self.env.setdefault('CARGO_NET_OFFLINE', 'true')
        subject, view = self.inputs()
        import hashlib
        names = ('seed_custody_source.py', 'bootstrap_dependency_preparation.py',
                 'seed_input_archives.py', 'seed_input_records.py',
                 'bootstrap_dependency_closure.py', 'recreate_bootstrap.py')
        sources = {'scripts/' + name:(self.root/'scripts'/name).read_bytes() for name in names}
        owner = source_module('captured_dependency_loader', self.root/'scripts/seed_custody_source.py')
        loader = owner.BoundSourceLoader(self.root,
            {name:hashlib.sha256(raw).hexdigest() for name, raw in sources.items()},
            captured_sources=sources)
        rows, reads = [], {}
        for path, row in view.files.items():
            name = path.relative_to(self.root).as_posix()
            rows.append({'path':name, **row})
            if name != 'bin/targo':
                reads[name] = {**{key:row[key] for key in ('kind', 'mode', 'bytes', 'sha256')},
                               'hex':path.read_bytes().hex()}
        # These are synthetic native-issuer observations only. The real Rust
        # constructor derives them from original Git plus retained guards.
        candidates = set()
        for path in view.files:
            if path.name == 'Cargo.toml':
                for parent in (path.parent, *path.parent.parents):
                    if not parent.is_relative_to(self.root): break
                    candidates.update(parent/name for name in (
                        'Cargo.toml', 'Cargo.lock', '.cargo/config', '.cargo/config.toml'))
        candidates.update(self.root/'cache'/name for name in ('config', 'config.toml'))
        for path in candidates:
            name = path.relative_to(self.root).as_posix()
            if name not in reads: reads[name] = {'kind':'absent'}
        return loader, {'schema':'trust-native-dependency-source-v1', 'root':str(self.root),
                        'repositories':{'.':rows}, 'reads':reads}

    def select(self, loader, capture):
        return loader.select_dependencies_from_capture(capture, 'bin/./targo', self.env,
                                                        deadline=self.end)

    def test_same_selector_keeps_complete_current_recipe_and_exact_driver(self):
        for name in closure._RECIPE_INPUTS:
            self.write(name, (REPO/name).read_text())
        class DeclaredFixture:
            def path(_, path): return path
            def is_file(_, path): return path.name == 'Cargo.toml' or path.is_file()
            def read_text(_, path): return path.read_text()
        roots = closure.stage0_bootstrap_manifest_roots(self.root, source_view=DeclaredFixture())
        self.assertEqual(len(roots), 55)
        self.assertIn(self.root / "crates/trust-certify/Cargo.toml", roots)
        for path in roots:
            self.write(str(path.relative_to(self.root)), '[workspace]\nmembers=[]\n')
            self.write(str(path.with_name('Cargo.lock').relative_to(self.root)), 'version=4\n')
        loader, capture = self.capture()
        result = self.select(loader, capture)
        self.assertEqual(result.manifests, tuple(roots))
        self.assertEqual(result.configured_targo, 'bin/./targo')
        self.assertEqual(len(result.passes), 1)
        self.assertEqual(result.deadline, self.end)
        self.assertIn(self.driver, result.unowned_input_paths)
        self.assertIn(self.root.parent/'.cargo/config', result.unowned_input_paths)
        result.recheck_selection()

    def test_required_metadata_only_manifest_cannot_fall_back_to_disk(self):
        loader, capture = self.capture()
        capture['reads'].pop('library/Cargo.toml')
        with self.assertRaisesRegex(ValueError, 'not physically captured'):
            self.select(loader, capture)

    def test_required_absence_without_native_anchor_refuses(self):
        loader, capture = self.capture()
        capture['reads'].pop('.cargo/config')
        with self.assertRaisesRegex(ValueError, 'not physically captured'):
            self.select(loader, capture)

    def test_missing_gitlink_and_duplicate_membership_refuse(self):
        loader, capture = self.capture()
        capture['repositories']['.'].append({'path':'missing-child', 'kind':'gitlink', 'mode':0})
        with self.assertRaisesRegex(ValueError, 'not completely expanded'):
            self.select(loader, capture)
        capture['repositories']['.'].pop()
        capture['repositories']['.'].append(dict(capture['repositories']['.'][0]))
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            self.select(loader, capture)

    def test_unexpected_code_graph_and_changed_captured_code_refuse(self):
        loader, capture = self.capture()
        loader._captured['scripts/extra.py'] = b'raise AssertionError()'
        with self.assertRaisesRegex(ValueError, 'unexpected captured code graph'):
            self.select(loader, capture)
        loader._captured.pop('scripts/extra.py')
        capture['reads']['scripts/seed_input_records.py']['hex'] = b'changed'.hex()
        with self.assertRaisesRegex(ValueError, 'bytes differ'):
            self.select(loader, capture)

    def test_captured_bytes_drive_reads_and_environment_is_copied(self):
        loader, capture = self.capture()
        self.env.update(CARGO_NET_OFFLINE='true', TRUST_DENY_WARNINGS='')
        request = self.select(loader, capture)
        # Original native owner must reject physical mutation after real child
        # closure. This DATA view never substitutes a pathname-content read.
        (self.root/'Cargo.lock').write_text('uncommitted replacement')
        request.recheck_selection()
        self.assertEqual(dict(request.environment)['TRUST_DENY_WARNINGS'], '')
        capture['reads']['Cargo.lock']['hex'] = ''
        request.recheck_selection()  # caller packet mutation cannot alter view

    def test_expired_endpoint_and_foreign_root_refuse(self):
        loader, capture = self.capture()
        with self.assertRaisesRegex(ValueError, 'bounded endpoint'):
            loader.select_dependencies_from_capture(capture, str(self.driver), self.env,
                                                     deadline=time.monotonic()-1)
        capture['root'] = str(self.root/'other')
        with self.assertRaisesRegex(ValueError, 'captured source DATA'):
            self.select(loader, capture)

    def test_present_required_link_uses_captured_literal_and_refuses_missing_target(self):
        loader, capture = self.capture()
        rows = capture['repositories']['.']
        for row in rows:
            if row['path'] == 'library/Cargo.toml':
                row.update(kind='symlink', mode=0o777, target='manifest-data')
        capture['reads']['library/Cargo.toml'] = {
            'kind':'symlink', 'mode':0o777, 'target':'manifest-data'}
        rows.append({'path':'library/manifest-data', 'kind':'file', 'mode':0o644,
                     'bytes':0, 'sha256':'0'*64})
        with self.assertRaisesRegex(ValueError, 'not physically captured'):
            self.select(loader, capture)

    def test_oversize_hex_and_invalid_modes_refuse_before_content_use(self):
        loader, capture = self.capture()
        capture['reads']['Cargo.lock']['mode'] = 0o4644
        with self.assertRaisesRegex(ValueError, 'file metadata'):
            self.select(loader, capture)
        capture['reads']['Cargo.lock']['mode'] = 0o644
        capture['reads']['Cargo.lock']['hex'] = '00' * (4*1024*1024 + 1)
        with self.assertRaisesRegex(ValueError, 'bytes exceed bound'):
            self.select(loader, capture)

    def test_native_offline_profile_does_not_coerce_caller_network_policy(self):
        loader, capture = self.capture()
        for value in (None, '', 'false'):
            if value is None: self.env.pop('CARGO_NET_OFFLINE', None)
            else: self.env['CARGO_NET_OFFLINE'] = value
            with self.assertRaisesRegex(ValueError, 'original offline policy'):
                self.select(loader, capture)

    def test_workspace_glob_without_native_membership_is_an_explicit_ownership_gap(self):
        self.write('Cargo.toml', '[workspace]\nmembers=["members/*"]\n')
        self.write('members/committed/Cargo.toml',
                   '[package]\nname="committed"\nversion="0.1.0"\n')
        self.write('members/untracked/Cargo.toml',
                   '[package]\nname="untracked"\nversion="0.1.0"\n')
        loader, capture = self.capture()
        # It already exists physically before selection, but is absent from
        # the native commit census. This packet is synthetic DATA, not custody.
        capture['repositories']['.'] = [row for row in capture['repositories']['.']
            if not row['path'].startswith('members/untracked/')]
        capture['reads'] = {name:item for name,item in capture['reads'].items()
            if not name.startswith('members/untracked/')}
        result = self.select(loader, capture)
        self.assertIn(self.root/'members/committed/Cargo.toml', result.source_inputs)
        self.assertNotIn(self.root/'members/untracked/Cargo.toml', result.source_inputs)
        self.assertIn(self.root/'members', result.unowned_input_paths)

    def test_committed_dangling_config_link_cannot_become_an_absent_input(self):
        loader, capture = self.capture()
        capture['repositories']['.'].append({'path':'.cargo/config',
            'kind':'symlink', 'mode':0o777, 'target':'missing-config'})
        capture['reads']['.cargo/config'] = {
            'kind':'symlink', 'mode':0o777, 'target':'missing-config'}
        capture['reads']['.cargo/missing-config'] = {'kind':'absent'}
        with self.assertRaisesRegex(ValueError, 'present literal link'):
            self.select(loader, capture)

    def physical_listing(self, directory):
        # Test DATA from the actual namespace. Production listings originate
        # only in the SAME snapshot's retained descriptor-relative guard.
        return [{'name':entry.name,
                 'kind':('symlink' if entry.is_symlink() else 'directory'
                         if entry.is_dir(follow_symlinks=False) else 'file')}
                for entry in os.scandir(directory)]

    def workspace_glob(self, pattern='members/*'):
        self.write('Cargo.toml', '[workspace]\nmembers=["' + pattern + '"]\n')
        if pattern == 'members/**':
            self.write('members/Cargo.toml', '[package]\nname="parent"\nversion="0.1.0"\n')
        self.write('members/committed/Cargo.toml',
                   '[package]\nname="committed"\nversion="0.1.0"\n')
        return self.capture()

    def test_second_pass_rejects_initial_untracked_matching_directory(self):
        loader, capture = self.workspace_glob()
        self.write('members/untracked/Cargo.toml',
                   '[package]\nname="untracked"\nversion="0.1.0"\n')
        discovery = self.select(loader, capture)
        self.assertIn(self.root/'members', discovery.unowned_input_paths)
        self.assertIn(self.root/'members', discovery.glob_input_paths)
        self.assertNotIn(self.driver, discovery.glob_input_paths)
        capture['listings'] = {'members':self.physical_listing(self.root/'members')}
        with self.assertRaisesRegex(ValueError, 'physical workspace glob membership differs'):
            self.select(loader, capture)

    def test_actual_matching_listing_discharges_only_glob_gap(self):
        loader, capture = self.workspace_glob()
        self.assertIn(self.root/'members', self.select(loader, capture).unowned_input_paths)
        capture['listings'] = {'members':self.physical_listing(self.root/'members')}
        result = self.select(loader, capture)
        self.assertNotIn(self.root/'members', result.unowned_input_paths)
        self.assertIn(self.driver, result.unowned_input_paths)
        self.assertIn(self.root.parent/'.cargo/config', result.unowned_input_paths)
        result.recheck_selection()

    def test_regular_files_matching_workspace_glob_remain_ignored(self):
        self.workspace_glob()
        self.write('members/note', 'ordinary committed file, not a Cargo member')
        loader, capture = self.capture()
        capture['listings'] = {'members':self.physical_listing(self.root/'members')}
        result = self.select(loader, capture)
        self.assertNotIn(self.root/'members', result.unowned_input_paths)
        result.recheck_selection()

    def test_same_pattern_ignores_nonmatching_names_but_rejects_changed_kinds(self):
        loader, capture = self.workspace_glob('members/comm*')
        self.write('members/other/Cargo.toml', 'not selected by this exact pattern')
        capture['listings'] = {'members':self.physical_listing(self.root/'members')}
        self.assertNotIn(self.root/'members', self.select(loader, capture).unowned_input_paths)
        for entry in capture['listings']['members']:
            if entry['name'] == 'committed': entry['kind'] = 'symlink'
        with self.assertRaisesRegex(ValueError, 'physical workspace glob membership differs'):
            self.select(loader, capture)

    def test_recursive_glob_requires_each_reached_listing(self):
        loader, capture = self.workspace_glob('members/**')
        capture['listings'] = {'members':self.physical_listing(self.root/'members')}
        discovery = self.select(loader, capture)
        self.assertIn(self.root/'members/committed', discovery.unowned_input_paths)
        capture['listings']['members/committed'] = self.physical_listing(self.root/'members/committed')
        self.assertNotIn(self.root/'members/committed', self.select(loader, capture).unowned_input_paths)

@unittest.skipUnless(sys.platform == "darwin", "the per-fetch custodian is the Darwin path")
class DarwinCustodianTests(unittest.TestCase):
    """Direct process-group diagnostic controls, never native admission.

    Stand-in fetches are this interpreter or /bin/sleep; no cargo runs. Each test
    keeps its own fixture Cargo home, so the fence and Cargo's GC lock are its own.
    """

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.env = {**os.environ, "CARGO_HOME": str(self.root / "cache")}
        self.lib = closure._darwin_libproc()

    def fetch(self, code, budget=30.0):
        return closure._fetch_darwin([sys.executable, "-I", "-c", code], self.root, self.env,
                              time.monotonic() + budget)

    def live(self, pgid):
        return [pid for pid in closure._darwin_group_members(self.lib, pgid, required=None)
                if closure._darwin_live(self.lib, pid)]

    def wait_for(self, path, seconds=10.0):
        stop = time.monotonic() + seconds
        while time.monotonic() < stop:
            if path.exists() and path.read_text().strip():
                return path.read_text().split()
            time.sleep(0.02)
        self.fail(f"{path.name} never appeared")

    def assert_lock_free(self, name):
        import fcntl
        fd = os.open(self.root / "cache" / name, os.O_RDWR)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        finally:
            os.close(fd)

    def driver(self, code, budget=120.0, *, pass_fds=()):
        """A separate helper process H' running the real `_fetch` on `code`."""
        program = (
            "import importlib.util, os, sys, time\n"
            "from pathlib import Path\n"
            f"spec = importlib.util.spec_from_file_location('closure', {str(HELPER)!r})\n"
            "c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)\n"
            f"c._fetch_darwin([sys.executable, '-I', '-c', {code!r}], Path({str(self.root)!r}),\n"
            f"         {self.env!r}, time.monotonic() + {budget})\n")
        child = subprocess.Popen([sys.executable, "-I", "-c", program], cwd=self.root,
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                 pass_fds=pass_fds)
        self.addCleanup(lambda: (child.poll() is None and child.kill(), child.wait()))
        return child

    def test_darwin_fetch_runs_under_a_custodian_and_reports_the_childs_own_status(self):
        # Fails before the custodian (the fetch was refused and the marker absent).
        ids = self.root / "ids"
        code = (f"import os; open({str(ids)!r}, 'w').write(f'{{os.getpgid(0)}} {{os.getppid()}}');"
                " raise SystemExit(5)")
        with self.assertRaisesRegex(closure.DependencyClosureError, "locked dependency fetch exited 5"):
            self.fetch(code)
        pgid, parent = map(int, ids.read_text().split())
        self.assertNotEqual(pgid, os.getpgid(0), "the fetch stayed in the helper's group")
        self.assertEqual(pgid, parent, "the fetch's group leader is not its parent, the custodian")
        self.assertEqual(self.live(pgid), [])
        self.fetch("pass")  # and a zero exit is a success

    def test_darwin_helper_termination_retires_the_fetch_cohort(self):
        # The landing gate retires a leg by SIGTERM then SIGKILL to the x.py group,
        # which holds the helper; a new-session fetch must not outlive it.
        import fcntl
        for sig in (signal.SIGTERM, signal.SIGKILL):
            with self.subTest(sig.name):
                read, write = os.pipe()
                try:
                    # The helper/custodian reserve 3..5. Popen passes this writer
                    # to H; the existing posix_spawn path then passes it to W/C.
                    writer = fcntl.fcntl(write, fcntl.F_DUPFD_CLOEXEC, 10)
                finally:
                    os.close(write)
                with os.fdopen(read, "rb", buffering=0) as retired:
                    ids = self.root / f"ids-{sig.name}"
                    code = ("import os, subprocess, time; p = subprocess.Popen(['/bin/sleep', '60']);"
                            f" os.write({writer}, b'1');"
                            f" open({str(ids)!r}, 'w').write(str(os.getpgid(0))); time.sleep(60)")
                    try:
                        helper = self.driver(code, pass_fds=(writer,))
                    finally:
                        os.close(writer)
                    (pgid,) = map(int, self.wait_for(ids))
                    self.assertEqual(retired.read(1), b"1", "the actual fetch did not inherit its writer")
                    self.assertEqual(select.select([retired], [], [], 0)[0], [],
                                     "retirement EOF appeared while the cohort was alive")
                    helper.send_signal(sig)
                    helper.wait(timeout=10)
                    stop = time.monotonic() + 3
                    while self.live(pgid) and time.monotonic() < stop:
                        time.sleep(0.02)
                    self.assertEqual(self.live(pgid), [], "the fetch cohort outlived its helper")
                    # libproc's absence/zombie observation can precede physical
                    # descriptor teardown. Require inherited-writer EOF within
                    # the SAME retirement bound before checking the real locks.
                    ready = select.select([retired], [], [], max(0.0, stop - time.monotonic()))[0]
                    self.assertTrue(ready, "the retired cohort still held its inherited writer")
                    self.assertEqual(retired.read(1), b"", "retirement did not establish physical EOF")
                    self.assert_lock_free(closure._DARWIN_FENCE)
                    self.assert_lock_free(closure._CARGO_MUTATE_LOCK)

    def test_darwin_custodian_loss_is_retired_by_the_pinned_helper(self):
        ids = self.root / "ids"
        code = ("import os, signal, subprocess, time; p = subprocess.Popen(['/bin/sleep', '60']);"
                f" open({str(ids)!r}, 'w').write(str(os.getpgid(0)));"
                " os.kill(os.getppid(), signal.SIGKILL); time.sleep(60)")
        calls = []
        real_killpg, real_waitpid = os.killpg, os.waitpid
        with patch.object(closure.os, "killpg", side_effect=lambda *a: calls.append(("killpg", a[0])) or real_killpg(*a)), \
                patch.object(closure.os, "waitpid", side_effect=lambda *a: calls.append(("waitpid", a[0])) or real_waitpid(*a)):
            with self.assertRaisesRegex(closure.DependencyClosureError, "custodian ended before reporting"):
                self.fetch(code)
        (pgid,) = map(int, ids.read_text().split())
        self.assertEqual(self.live(pgid), [])
        reap = calls.index(("waitpid", pgid))
        self.assertTrue(any(call == ("killpg", pgid) for call in calls[:reap]))
        self.assertFalse([call for call in calls[reap + 1:] if call[0] == "killpg"],
                         "a group was signalled after the custodian was reaped")

    def test_darwin_budget_expiry_retires_the_cohort_inside_the_original_deadline(self):
        ids = self.root / "ids"
        code = ("import os, subprocess, time; p = subprocess.Popen(['/bin/sleep', '60']);"
                f" open({str(ids)!r}, 'w').write(str(os.getpgid(0))); time.sleep(60)")
        end = time.monotonic() + 7
        with self.assertRaisesRegex(closure.DependencyClosureError, "total budget expired"):
            closure._fetch_darwin([sys.executable, "-I", "-c", code], self.root, self.env, end)
        self.assertLess(time.monotonic(), end + 0.5)
        (pgid,) = map(int, ids.read_text().split())
        self.assertEqual(self.live(pgid), [])

    def test_darwin_fetch_that_exits_beside_a_running_descendant_is_refused_and_retired(self):
        # A fetch that exits zero but leaves its group running is not a clean fetch
        # (the landing gate's abnormal_leftovers rule): named, retired, then refused.
        ids = self.root / "ids"
        code = ("import os, subprocess; p = subprocess.Popen(['/bin/sleep', '60']);"
                f" open({str(ids)!r}, 'w').write(f'{{os.getpgid(0)}} {{p.pid}}')")
        with self.assertRaisesRegex(closure.DependencyClosureError,
                                    r"left running descendants \[(\d+)\]; they were retired") as caught:
            self.fetch(code)
        pgid, sleeper = map(int, ids.read_text().split())
        self.assertIn(f"[{sleeper}]", str(caught.exception))
        self.assertEqual(self.live(pgid), [])
        self.assert_lock_free(closure._DARWIN_FENCE)
        self.assert_lock_free(closure._CARGO_MUTATE_LOCK)

    def test_darwin_custodian_deadline_retires_the_cohort_while_its_helper_is_stopped(self):
        # Only the custodian's own deadline can end a cohort whose helper is alive but
        # stopped: the helper cannot act, so an empty group here is the custodian's work.
        ids = self.root / "ids"
        code = ("import os, subprocess, time; p = subprocess.Popen(['/bin/sleep', '60']);"
                f" open({str(ids)!r}, 'w').write(str(os.getpgid(0))); time.sleep(60)")
        helper = self.driver(code, budget=10.0)  # the custodian's budget is about 4 s
        (pgid,) = map(int, self.wait_for(ids))
        helper.send_signal(signal.SIGSTOP)
        self.addCleanup(lambda: helper.poll() is None and helper.send_signal(signal.SIGCONT))
        stop = time.monotonic() + 8
        while self.live(pgid) and time.monotonic() < stop:
            time.sleep(0.05)
        self.assertIsNone(helper.poll(), "the helper ended, so it may have retired the group")
        self.assertEqual(self.live(pgid), [], "the custodian's deadline left its cohort running")
        # libproc can observe the final zombie before XNU finishes releasing
        # its file locks. Both locks must still become free inside the same
        # original deadline, without resuming the helper to perform cleanup.
        while True:
            try:
                self.assert_lock_free(closure._DARWIN_FENCE)
                self.assert_lock_free(closure._CARGO_MUTATE_LOCK)
                break
            except BlockingIOError:
                if time.monotonic() >= stop:
                    raise
                time.sleep(0.02)
        self.assertLess(time.monotonic(), stop, "custody locks outlived the original deadline")
        self.assertIsNone(helper.poll(), "the stopped helper must not release the locks")
        helper.send_signal(signal.SIGCONT)
        helper.wait(timeout=15)

    def test_darwin_interrupt_retires_before_reraising(self):
        ids = self.root / "ids"
        code = ("import os, time;"
                f" open({str(ids)!r}, 'w').write(str(os.getpgid(0))); time.sleep(60)")
        def interrupt(*_):
            raise KeyboardInterrupt
        previous = signal.signal(signal.SIGALRM, interrupt)
        self.addCleanup(signal.signal, signal.SIGALRM, previous)
        signal.setitimer(signal.ITIMER_REAL, 1.0)
        self.addCleanup(signal.setitimer, signal.ITIMER_REAL, 0)
        with self.assertRaises(KeyboardInterrupt):
            self.fetch(code)
        (pgid,) = map(int, ids.read_text().split())
        self.assertEqual(self.live(pgid), [], "the cohort was alive when the interrupt arrived")

    def test_darwin_orphaned_cohort_keeps_its_locks_and_the_next_fetch_refuses_before_birth(self):
        # Helper stopped and custodian killed: nobody can retire the cohort, so the
        # inherited fence must keep the next fetch from starting until it ends.
        ids, go, orphaned = self.root / "ids", self.root / "go", self.root / "orphaned"
        code = ("import os, signal, time\n"
                f"open({str(ids)!r}, 'w').write(str(os.getpgid(0)))\n"
                f"while not os.path.exists({str(go)!r}):\n    time.sleep(0.01)\n"
                "os.kill(os.getppid(), signal.SIGKILL)\n"
                f"open({str(orphaned)!r}, 'w').write('1')\ntime.sleep(6)\n")
        helper = self.driver(code)
        self.wait_for(ids)
        # Stop the helper before the custodian dies, so neither can retire the cohort.
        helper.send_signal(signal.SIGSTOP)
        self.addCleanup(lambda: helper.poll() is None and helper.send_signal(signal.SIGCONT))
        go.write_text("1")
        self.wait_for(orphaned)
        import fcntl
        with self.assertRaises(BlockingIOError):
            self.assert_lock_free(closure._CARGO_MUTATE_LOCK)
        marker = self.root / "second-fetch-ran"
        with self.assertRaisesRegex(closure.DependencyClosureError, "refused fence-held"):
            self.fetch(f"from pathlib import Path; Path({str(marker)!r}).touch()", budget=8.5)
        self.assertFalse(marker.exists(), "a fetch started beside an unretired cohort")
        stop = time.monotonic() + 15
        while time.monotonic() < stop:
            try:
                self.assert_lock_free(closure._DARWIN_FENCE)
                break
            except BlockingIOError:
                time.sleep(0.1)
        self.fetch(f"from pathlib import Path; Path({str(marker)!r}).touch()")
        self.assertTrue(marker.exists())

    def test_darwin_custodian_refuses_when_its_client_is_already_gone(self):
        import fcntl
        pipes = [*os.pipe(), *os.pipe()]
        # Above 5, so the DUP2s below are real duplications that clear close-on-exec.
        read, write, report_read, report_write = (fcntl.fcntl(fd, fcntl.F_DUPFD_CLOEXEC, 10) for fd in pipes)
        for fd in pipes:
            os.close(fd)
        os.close(write)  # the client is gone before the custodian starts
        marker = self.root / "orphan-fetch-ran"
        args = {"parent": os.getpid(), "root": str(self.root),
                "argv": [sys.executable, "-c", f"from pathlib import Path; Path({str(marker)!r}).touch()"],
                "cargo_home": str(self.root / "cache"), "fence": closure._DARWIN_FENCE,
                "mutate": closure._CARGO_MUTATE_LOCK, "defaults": [], "budget": 10}
        custodian = os.posix_spawn(
            sys.executable, [sys.executable, "-I", "-S", "-B", "-c", closure._CUSTODIAN_SOURCE, json.dumps(args)],
            os.environ, file_actions=[(os.POSIX_SPAWN_DUP2, read, 3), (os.POSIX_SPAWN_DUP2, report_write, 4),
                                      (os.POSIX_SPAWN_OPEN, 5, "/dev/null", os.O_WRONLY, 0)],
            setsid=True)
        os.close(read)
        os.close(report_write)
        _, status = os.waitpid(custodian, 0)
        record = os.read(report_read, 4096).decode()
        os.close(report_read)
        self.assertEqual(os.waitstatus_to_exitcode(status), 3)
        self.assertIn("refused client-gone", record)
        self.assertFalse(marker.exists())


class NativeDependencyEntryTests(unittest.TestCase):
    """Fixed body controls only; these fixtures issue no native owner/closure."""
    setUp = DependencyClosureTests.setUp
    write = DependencyClosureTests.write
    inputs = PreparationRequestTests.inputs
    no_processes = PreparationRequestTests.no_processes
    capture = CapturedDependencySelectionTests.capture

    def packet(self):
        import hashlib
        loader, snapshot = self.capture()
        packet = {'schema':'trust-native-dependency-selection-v1',
            'clock':'darwin-mach-uptime-raw-v1', 'end_ns':int(self.end * 1_000_000_000),
            'source_root':str(self.root), 'snapshot':snapshot,
            'sources':{name:{'hex':raw.hex(), 'sha256':hashlib.sha256(raw).hexdigest()}
                       for name, raw in loader._captured.items()},
            'configured_targo':'bin/./targo', 'environment':dict(self.env)}
        return type(loader).module.__globals__, packet

    def native_fixture(self, scope):
        # Exercise real directory checks using this test's actual readonly root
        # description. The nineteen native slots/ownership are NOT constructed.
        root = os.open(self.root, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        self.addCleanup(os.close, root)
        original_directory = scope['_native_directory']
        def directory(value, descriptor, label):
            self.assertEqual(descriptor, 6)
            return original_directory(value, root, label)
        stack = ExitStack()
        self.addCleanup(stack.close)
        stack.enter_context(patch.dict(scope, {'_native_directory':directory,
                                             '_native_descriptions':Mock()}))
        stack.enter_context(patch.object(sys, 'platform', 'darwin'))
        stack.enter_context(patch.object(time, 'CLOCK_UPTIME_RAW', 12345, create=True))
        stack.enter_context(patch.object(time, 'clock_gettime_ns',
                                        side_effect=lambda _:time.monotonic_ns()))
        return stack

    def invoke(self, scope, packet):
        return scope['_native_dependency_selection_packet'](json.dumps(packet).encode())

    def test_fixed_entry_returns_request_data_and_preserves_original_policy(self):
        scope, packet = self.packet()
        self.native_fixture(scope)
        packet['environment'].update(CARGO_HOME='', TARGO_HOME=str(self.root/'unused'),
                                     TRUST_DENY_WARNINGS='')
        result = json.loads(self.invoke(scope, packet))
        self.assertEqual(result.keys(), {'schema', 'configured_targo', 'targo_path', 'end_ns',
            'clock', 'manifests', 'source_inputs', 'read_set', 'glob_inputs', 'unowned_inputs'})
        self.assertEqual(result['configured_targo'], 'bin/./targo')
        self.assertEqual(result['end_ns'], packet['end_ns'])
        self.assertEqual(len(result['manifests']), 8)
        self.assertIn(str(self.root/'.cargo/config'), result['source_inputs'])
        self.assertNotIn(str(self.root/'unused/config'), result['source_inputs'])
        self.assertIn(str(self.driver), result['unowned_inputs'])
        self.assertIn(str(self.root.parent/'.cargo/config'), result['unowned_inputs'])
        self.assertEqual(packet['environment']['CARGO_HOME'], '')
        self.assertEqual(packet['environment']['TRUST_DENY_WARNINGS'], '')
        self.assertFalse(any(name in result for name in ('completed', 'native', 'seed', 'sdk')))

    def test_fixed_entry_keeps_full_current_recipe_population(self):
        for name in closure._RECIPE_INPUTS:
            self.write(name, (REPO/name).read_text())
        class DeclaredFixture:
            def path(_, path): return path
            def is_file(_, path): return path.name == 'Cargo.toml' or path.is_file()
            def read_text(_, path): return path.read_text()
        roots = closure.stage0_bootstrap_manifest_roots(self.root, source_view=DeclaredFixture())
        self.assertEqual(len(roots), 55)
        self.assertIn(self.root / "crates/trust-certify/Cargo.toml", roots)
        for path in roots:
            self.write(str(path.relative_to(self.root)), '[workspace]\nmembers=[]\n')
            self.write(str(path.with_name('Cargo.lock').relative_to(self.root)), 'version=4\n')
        scope, packet = self.packet()
        self.native_fixture(scope)
        result = json.loads(self.invoke(scope, packet))
        self.assertEqual(result['manifests'], [path.relative_to(self.root).as_posix() for path in roots])

    def test_duplicate_nonfinite_and_oversize_packets_refuse_before_body(self):
        scope, _ = self.packet()
        entry = scope['_native_dependency_selection_packet']
        for raw in (b'{"schema":1,"schema":2}', b'{"sources":{"x":1,"x":2}}'):
            with self.assertRaisesRegex(ValueError, 'duplicate'):
                entry(raw)
        for raw in (b'{"end_ns":NaN}', b'{"unused":{"number":1e999}}'):
            with self.assertRaisesRegex(ValueError, 'nonfinite'):
                entry(raw)
        with patch.dict(scope, {'MAX_NATIVE_SOURCE_PACKET':8}):
            with self.assertRaisesRegex(ValueError, 'packet exceeds bound'):
                entry(b'123456789')

    def test_expired_noninteger_and_wrong_clock_endpoints_refuse(self):
        scope, packet = self.packet()
        self.native_fixture(scope)
        for end in (0, True, time.monotonic_ns()-1, 2**64):
            packet['end_ns'] = end
            with self.assertRaisesRegex(ValueError, 'endpoint'):
                self.invoke(scope, packet)
        packet['end_ns'] = int(self.end*1_000_000_000)
        packet['clock'] = 'some-new-clock'
        with self.assertRaisesRegex(ValueError, 'fixed native'):
            self.invoke(scope, packet)

    def test_clock_mismatch_overbudget_and_late_expiry_cannot_return_data(self):
        scope, packet = self.packet()
        self.native_fixture(scope)
        with patch.object(time, 'clock_gettime_ns', return_value=0):
            with self.assertRaisesRegex(ValueError, 'clock differs'):
                self.invoke(scope, packet)
        packet['end_ns'] = time.monotonic_ns() + 901*1_000_000_000
        with self.assertRaisesRegex(ValueError, 'bounded endpoint'):
            self.invoke(scope, packet)
        packet['end_ns'] = int(self.end*1_000_000_000)
        values = [time.monotonic_ns(), time.monotonic_ns()+1_000_000_000, packet['end_ns']]
        with patch.object(time, 'clock_gettime_ns', side_effect=values):
            with self.assertRaisesRegex(ValueError, 'original endpoint expired'):
                self.invoke(scope, packet)

    def test_code_substitution_and_incomplete_graph_cannot_execute(self):
        import copy
        import hashlib
        scope, packet = self.packet()
        self.native_fixture(scope)
        changed = copy.deepcopy(packet)
        name = 'scripts/bootstrap_dependency_preparation.py'
        raw = b'raise AssertionError("substituted source executed")\n'
        changed['sources'][name] = {'hex':raw.hex(), 'sha256':hashlib.sha256(raw).hexdigest()}
        with self.assertRaisesRegex(ValueError, 'module source is not in live owner manifest'):
            self.invoke(scope, changed)
        packet['sources'].pop(name)
        with self.assertRaisesRegex(ValueError, 'six-code capture'):
            self.invoke(scope, packet)

    def test_bare_source_foreign_directory_and_output_overflow_refuse(self):
        scope, packet = self.packet()
        self.native_fixture(scope)
        with patch.dict(scope, {'MAX_NATIVE_SOURCE_RESULT':1}):
            with self.assertRaisesRegex(ValueError, 'output exceeds bound'):
                self.invoke(scope, packet)
        other = self.root/'other'; other.mkdir()
        packet['source_root'] = str(other)
        with self.assertRaisesRegex(ValueError, 'retained original directory'):
            self.invoke(scope, packet)
        packet['source_root'] = str(self.root)
        with patch.object(sys, 'platform', 'linux'):
            with self.assertRaisesRegex(ValueError, 'fixed native'):
                self.invoke(scope, packet)


if __name__ == "__main__":
    unittest.main()
