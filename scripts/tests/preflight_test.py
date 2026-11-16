#!/usr/bin/env python3
"""Focused controls for bootstrap-effective tool preflight configuration."""

from __future__ import annotations

import importlib.util
import hashlib
import io
import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from contextlib import ExitStack, contextmanager
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[2]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


preflight = load_module("trust_preflight", REPO_ROOT / "tools" / "preflight.py")
x_entry = load_module("trust_x_entry", REPO_ROOT / "x.py")


class FlushedProgress(io.StringIO):
    def __init__(self) -> None:
        super().__init__()
        self.flushed = ""

    def flush(self) -> None:
        self.flushed = self.getvalue()
        super().flush()


class BuildPhaseProgressTests(unittest.TestCase):
    # Exercise the real main orchestration without scanning the live source or
    # resolving dependencies. Each existing check observes its flushed start.
    PHASES = {
        "resolve_bootstrap_config": "bootstrap-config",
        "read_bootstrap_facts": "bootstrap-facts",
        "check_submodules": "submodules",
        "check_bootstrap_submodule_policy": "bootstrap-submodule-policy",
        "check_pin_regression": "pin-regression",
        "check_pin_behind_history": "pin-behind-history",
        "discover_workspaces": "workspace-discovery",
        "check_lockfiles_fast": "lockfiles-fast",
        "check_git_pin_cascade": "git-pin-cascade",
        "check_path_version_cascade": "path-version-cascade",
        "check_lock_mtimes": "lock-mtimes",
        "find_targo": "lockfiles-deep",
        "check_lockfiles_deep": "lockfiles-deep",
        "build_tool_model": "tool-model",
        "check_tools_allowlist": "tools-allowlist",
        "check_model_vs_sysroot": "model-vs-sysroot",
        "check_concurrent_build": "concurrent-build",
        "check_existing_sysroot": "existing-sysroot",
        "check_config_drift": "config-drift",
        "check_misc": "misc",
    }

    @contextmanager
    def invocation(self, *args, for_build=True, rc=0, failure=None, stderr=None):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = Path(directory).resolve()
            state = SimpleNamespace(
                root=root, verdict=root / "verdict", calls=[], mocks={},
                stdout=io.StringIO(), stderr=stderr if stderr is not None else FlushedProgress(),
                config={}, facts=object(), workspaces=[root / "workspace"], model=object(),
            )
            returns = {
                "resolve_bootstrap_config": (state.config, root / "bootstrap.toml", None),
                "read_bootstrap_facts": state.facts,
                "discover_workspaces": state.workspaces,
                "find_targo": "selected-targo",
                "build_tool_model": state.model,
            }

            def check(name):
                def call(*a, **kw):
                    state.calls.append(name)
                    if for_build and isinstance(state.stderr, FlushedProgress):
                        self.assertTrue(state.stderr.flushed.endswith(
                            f"preflight: phase {self.PHASES[name]} start\n"))
                    if failure is not None and name == "check_pin_behind_history":
                        raise failure
                    return returns.get(name)
                return call

            for name in self.PHASES:
                state.mocks[name] = stack.enter_context(
                    patch.object(preflight, name, side_effect=check(name)))

            def emit(report, elapsed, checks_run):
                state.calls.append("emit")
                self.assertFalse(state.verdict.exists(), "verdict preceded report emission")
                self.assertEqual(elapsed, 2.0, "existing report keeps wall-clock elapsed time")
                state.checks_run = checks_run
                print("existing report")
                return rc

            state.emit = stack.enter_context(
                patch.object(preflight.Report, "emit", autospec=True, side_effect=emit))
            state.monotonic = stack.enter_context(
                patch.object(preflight.time, "monotonic", side_effect=iter(range(1000))))
            stack.enter_context(patch.object(preflight.time, "time", side_effect=[40.0, 42.0]))
            stack.enter_context(patch.object(sys, "stdout", state.stdout))
            stack.enter_context(patch.object(sys, "stderr", state.stderr))
            argv = ["preflight", "--repo-root", str(root), "--no-color",
                    "--verdict-file", str(state.verdict)]
            if for_build:
                argv.append("--for-build")
            stack.enter_context(patch.object(sys, "argv", argv + list(args)))
            yield state

    def test_build_phases_preserve_all_check_order_and_report(self) -> None:
        with self.invocation() as state:
            self.assertEqual(preflight.main(), 0)
            self.assertEqual(state.calls, [name for name in self.PHASES
                                          if name not in ("find_targo", "check_lockfiles_deep")] + ["emit"])
            self.assertEqual(state.checks_run, [
                "1. SUBMODULE DRIFT", "2. LOCKFILE SKEW (non-mutating)",
                "2a. GIT-PIN CASCADE (submodule manifest -> parent lock)",
                "3. TOOLS ALLOWLIST AUDIT", "4. BUILD ENVIRONMENT",
            ])
            phases = [self.PHASES[name] for name in state.calls[:-1]]
            self.assertEqual(state.stderr.getvalue(), "".join(
                f"preflight: phase {phase} start\n"
                f"preflight: phase {phase} end elapsed=1.000s\n" for phase in phases))
            self.assertEqual(state.stderr.flushed, state.stderr.getvalue())
            self.assertEqual(state.stdout.getvalue(), "existing report\n")
            self.assertEqual(state.verdict.read_text(), "CLEAR\n")
            state.mocks["check_concurrent_build"].assert_called_once_with(
                state.root, unittest.mock.ANY, True)

    def test_progress_is_build_only_and_does_not_change_blocked_verdict(self) -> None:
        for for_build in (False, True):
            with self.subTest(for_build=for_build), self.invocation(
                "--only", "submodules", for_build=for_build, rc=1,
            ) as state:
                self.assertEqual(preflight.main(), 1)
                self.assertEqual(state.calls, list(self.PHASES)[:6] + ["emit"])
                self.assertEqual(state.checks_run, ["1. SUBMODULE DRIFT"])
                self.assertEqual(state.stdout.getvalue(), "existing report\n")
                self.assertEqual(state.verdict.read_text(), "BLOCKED\n")
                if not for_build:
                    self.assertEqual(state.stderr.getvalue(), "")
                    state.monotonic.assert_not_called()

    def test_deep_selection_keeps_resolver_arguments_and_precedence(self) -> None:
        for flags in ((), ("--deep-if-cached",), ("--deep",), ("--deep", "--deep-if-cached")):
            with self.subTest(flags=flags), self.invocation(
                "--only", "lockfiles", "--timeout", "17", "--jobs", "2",
                "--depth", "5", "--all-workspaces", "--targo", "requested-targo", *flags,
            ) as state:
                self.assertEqual(preflight.main(), 0)
                expected = ["resolve_bootstrap_config", "read_bootstrap_facts",
                            "discover_workspaces", "check_lockfiles_fast", "check_git_pin_cascade",
                            "check_path_version_cascade", "check_lock_mtimes"]
                if flags:
                    expected += ["find_targo", "check_lockfiles_deep"]
                    state.mocks["find_targo"].assert_called_once_with(state.root, "requested-targo")
                    state.mocks["check_lockfiles_deep"].assert_called_once_with(
                        state.root, state.workspaces, unittest.mock.ANY, "selected-targo", 17, 2,
                        cached_only="--deep" not in flags)
                else:
                    state.mocks["find_targo"].assert_not_called()
                    state.mocks["check_lockfiles_deep"].assert_not_called()
                self.assertEqual(state.calls, expected + ["emit"])
                state.mocks["discover_workspaces"].assert_called_once_with(
                    state.root, state.facts, 5, True)

    def test_check_exceptions_keep_identity_and_publish_no_verdict(self) -> None:
        for failure in (RuntimeError("check failed"), KeyboardInterrupt()):
            with self.subTest(failure=type(failure)), self.invocation(
                "--only", "submodules", failure=failure,
            ) as state:
                with self.assertRaises(type(failure)) as caught:
                    preflight.main()
                self.assertIs(caught.exception, failure)
                self.assertTrue(state.stderr.flushed.endswith(
                    "preflight: phase pin-behind-history end elapsed=1.000s\n"))
                state.emit.assert_not_called()
                self.assertFalse(state.verdict.exists())

    def test_progress_io_failure_cannot_change_verdict_or_mask_exception(self) -> None:
        for operation in ("write", "flush"):
            for error_type in (OSError, ValueError):
                for failure in (None, RuntimeError("original check failure")):
                    with self.subTest(operation=operation, error_type=error_type, failure=failure):
                        stderr = io.StringIO()
                        with patch.object(stderr, operation, side_effect=error_type("closed")), self.invocation(
                            "--only", "submodules", stderr=stderr, failure=failure,
                        ) as state:
                            if failure is None:
                                self.assertEqual(preflight.main(), 0)
                                self.assertEqual(state.verdict.read_text(), "CLEAR\n")
                            else:
                                with self.assertRaises(RuntimeError) as caught:
                                    preflight.main()
                                self.assertIs(caught.exception, failure)
                                state.emit.assert_not_called()
                                self.assertFalse(state.verdict.exists())


class PythonStartupIsolationTests(unittest.TestCase):
    def check_launcher(self, launcher: str) -> None:
        with tempfile.TemporaryDirectory() as directory:
            startup = Path(directory)
            marker = startup / "startup-ran"
            (startup / "sitecustomize.py").write_text(
                "import os\n"
                "with open(os.environ['TRUST_PREFLIGHT_STARTUP_MARKER'], 'w') as marker:\n"
                "    marker.write('sitecustomize executed')\n"
                "print('startup contaminated the preflight contract')\n",
                encoding="utf-8",
            )
            (startup / "tomllib.py").write_text(
                "raise RuntimeError('ambient tomllib shadow reached preflight')\n",
                encoding="utf-8",
            )
            environment = dict(os.environ)
            environment.update(
                PYTHONPATH=str(startup),
                TRUST_PREFLIGHT_STARTUP_MARKER=str(marker),
                PYTHONDONTWRITEBYTECODE="1",
            )
            result = subprocess.run(
                ["/bin/sh", str(REPO_ROOT / "tools" / launcher), "--help"],
                cwd=startup,
                env=environment,
                capture_output=True,
                text=True,
                timeout=15,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("usage:", result.stdout)
            self.assertNotIn("startup contaminated", result.stdout + result.stderr)
            self.assertFalse(marker.exists(), "sitecustomize executed before preflight")

    def test_shell_launcher_ignores_python_startup_and_module_shadow(self) -> None:
        self.check_launcher("preflight.sh")

    def test_polyglot_launcher_ignores_python_startup_and_module_shadow(self) -> None:
        self.check_launcher("preflight.py")


class EffectiveBootstrapConfigTests(unittest.TestCase):
    def setUp(self) -> None:
        preflight._TOML_CACHE.clear()

    def resolve(self, path: Path, *overrides: str):
        cfg, selected, error = preflight.resolve_bootstrap_config(
            REPO_ROOT,
            str(path),
            list(overrides),
            path.parent,
            {},
        )
        self.assertIsNone(error)
        self.assertEqual(selected.resolve(), path.resolve())
        return cfg

    def test_compiler_and_tools_profiles_select_all_backends(self) -> None:
        facts = preflight.read_bootstrap_facts(REPO_ROOT)
        with tempfile.TemporaryDirectory() as directory:
            config = Path(directory) / "bootstrap.toml"
            for profile in ("compiler", "tools"):
                config.write_text(f'profile = "{profile}"\n', encoding="utf-8")
                preflight._TOML_CACHE.clear()
                cfg = self.resolve(config)
                model = preflight.build_tool_model(REPO_ROOT, cfg, facts)
                self.assertTrue(model.selected("ay"), profile)
                self.assertTrue(model.selected("clean"), profile)
                self.assertTrue(model.selected("ty"), profile)

    def test_root_include_profile_and_set_precedence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            (directory / "nested.toml").write_text(
                '[rust]\nchannel = "nested"\n', encoding="utf-8"
            )
            (directory / "left.toml").write_text(
                'include = ["nested.toml"]\n'
                '[build]\ntools = ["left"]\nextended = true\n',
                encoding="utf-8",
            )
            (directory / "right.toml").write_text(
                '[build]\ntools = ["right"]\nextended = true\n', encoding="utf-8"
            )
            root = directory / "bootstrap.toml"
            root.write_text(
                'profile = "compiler"\n'
                'include = ["left.toml", "right.toml"]\n'
                '[build]\nextended = false\n',
                encoding="utf-8",
            )

            cfg = self.resolve(root)
            self.assertEqual(cfg["build"]["tools"], ["right"])
            self.assertFalse(cfg["build"]["extended"])
            self.assertEqual(cfg["rust"]["channel"], "nested")

            cfg = self.resolve(root, 'build.tools=["override"]')
            self.assertEqual(cfg["build"]["tools"], ["override"])
            self.assertFalse(cfg["build"]["extended"])

    def test_symlinked_paths_match_bootstrap_at_each_include_level(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            real_root = directory / "real-root"
            invocation = directory / "invocation"
            real_include = directory / "real-include"
            alias_include = directory / "alias-include"
            real_nested = directory / "real-nested"
            for path in (real_root, invocation, real_include, alias_include, real_nested):
                path.mkdir()

            (real_root / "bootstrap.toml").write_text(
                'include = ["child.toml", "../alias-include/fragment.toml"]\n',
                encoding="utf-8",
            )
            (real_root / "child.toml").write_text(
                '[build]\ntools = ["canonical-root-parent"]\n', encoding="utf-8"
            )
            (invocation / "child.toml").write_text(
                '[build]\ntools = ["lexical-root-parent"]\n', encoding="utf-8"
            )
            (real_include / "fragment.toml").write_text(
                'include = ["nested.toml"]\n', encoding="utf-8"
            )
            (real_include / "nested.toml").write_text(
                '[rust]\nchannel = "canonical-first-level-parent"\n', encoding="utf-8"
            )
            (real_nested / "nested.toml").write_text(
                'include = ["deep.toml"]\n'
                '[rust]\nchannel = "lexical-first-level-parent"\n',
                encoding="utf-8",
            )
            (real_nested / "deep.toml").write_text(
                '[dist]\ncompression-profile = "canonical-recursive-parent"\n',
                encoding="utf-8",
            )
            (alias_include / "deep.toml").write_text(
                '[dist]\ncompression-profile = "lexical-recursive-parent"\n',
                encoding="utf-8",
            )

            selected = invocation / "bootstrap.toml"
            included = alias_include / "fragment.toml"
            try:
                selected.symlink_to(real_root / "bootstrap.toml")
                included.symlink_to(real_include / "fragment.toml")
                (alias_include / "nested.toml").symlink_to(real_nested / "nested.toml")
            except (NotImplementedError, OSError) as error:
                self.skipTest(f"symlinks unavailable: {error}")

            cfg, path, error = preflight.resolve_bootstrap_config(
                REPO_ROOT, str(selected), [], invocation, {}
            )
            self.assertIsNone(error)
            self.assertEqual(path, (real_root / "bootstrap.toml").resolve())
            self.assertEqual(cfg["build"]["tools"], ["canonical-root-parent"])
            self.assertEqual(cfg["rust"]["channel"], "lexical-first-level-parent")
            self.assertEqual(
                cfg["dist"]["compression-profile"], "canonical-recursive-parent"
            )

    def test_environment_and_default_path_discovery(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            default = directory / "bootstrap.toml"
            environment = directory / "environment.toml"
            default.write_text('[build]\ntools=["default"]\n', encoding="utf-8")
            environment.write_text('[build]\ntools=["environment"]\n', encoding="utf-8")

            cfg, path, error = preflight.resolve_bootstrap_config(
                REPO_ROOT,
                None,
                [],
                directory,
                {"RUST_BOOTSTRAP_CONFIG": "environment.toml"},
            )
            self.assertIsNone(error)
            self.assertEqual(path.resolve(), environment.resolve())
            self.assertEqual(cfg["build"]["tools"], ["environment"])

            preflight._TOML_CACHE.clear()
            cfg, path, error = preflight.resolve_bootstrap_config(
                REPO_ROOT, None, [], directory, {}
            )
            self.assertIsNone(error)
            self.assertEqual(path.resolve(), default.resolve())
            self.assertEqual(cfg["build"]["tools"], ["default"])

    def test_explicit_config_beats_environment_and_default(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            default = directory / "bootstrap.toml"
            environment = directory / "environment.toml"
            explicit = directory / "explicit.toml"
            default.write_text('[build]\ntools=["default"]\n', encoding="utf-8")
            environment.write_text('[build]\ntools=["environment"]\n', encoding="utf-8")
            explicit.write_text('[build]\ntools=["explicit"]\n', encoding="utf-8")

            cfg, path, error = preflight.resolve_bootstrap_config(
                REPO_ROOT,
                "explicit.toml",
                [],
                directory,
                {"RUST_BOOTSTRAP_CONFIG": str(environment)},
            )
            self.assertIsNone(error)
            self.assertEqual(path.resolve(), explicit.resolve())
            self.assertEqual(cfg["build"]["tools"], ["explicit"])

    def test_close_negative_override_is_reported_blocking(self) -> None:
        facts = preflight.read_bootstrap_facts(REPO_ROOT)
        with tempfile.TemporaryDirectory() as directory:
            config = Path(directory) / "bootstrap.toml"
            config.write_text('profile = "compiler"\n', encoding="utf-8")
            cfg = self.resolve(config, 'build.tools=["targo"]')
            model = preflight.build_tool_model(REPO_ROOT, cfg, facts)
            report = preflight.Report(False)
            preflight.check_tools_allowlist(REPO_ROOT, cfg, facts, report, config, model)
            failures = "\n".join(
                finding.title for finding in report.findings
                if finding.severity == preflight.FAIL
            )
            self.assertIn("`clean` WILL BE SILENTLY OMITTED", failures)
            self.assertIn("`ty` WILL BE SILENTLY OMITTED", failures)

    def test_removing_either_backend_from_either_profile_is_blocking(self) -> None:
        facts = preflight.read_bootstrap_facts(REPO_ROOT)
        defaults = REPO_ROOT / "src" / "bootstrap" / "defaults"
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            for profile in ("compiler", "tools"):
                original = (defaults / f"bootstrap.{profile}.toml").read_text(encoding="utf-8")
                for backend in ("clean", "ty"):
                    mutated = original.replace(f', "{backend}"', "", 1)
                    self.assertNotEqual(mutated, original)
                    candidate = directory / f"{profile}-without-{backend}.toml"
                    candidate.write_text(mutated, encoding="utf-8")
                    preflight._TOML_CACHE.clear()
                    cfg = self.resolve(candidate)
                    model = preflight.build_tool_model(REPO_ROOT, cfg, facts)
                    self.assertFalse(model.selected(backend), f"{profile} without {backend}")
                    report = preflight.Report(False)
                    preflight.check_tools_allowlist(
                        REPO_ROOT, cfg, facts, report, candidate, model
                    )
                    failures = [
                        finding.title
                        for finding in report.findings
                        if finding.severity == preflight.FAIL
                    ]
                    self.assertTrue(
                        any(f"`{backend}` WILL BE SILENTLY OMITTED" in title for title in failures),
                        f"{profile} without {backend} must block",
                    )

    def test_committed_profiles_raise_no_false_typo_and_a_real_typo_still_warns(self) -> None:
        # `trustc-dev` and `rust-src` are not sysroot binaries: install.rs
        # consults them directly (`install!` + `Self::should_build`,
        # `tools.contains`). Until 2026-09-27 the audit knew only binary and
        # dist names, so both committed profiles drew "allowlist entries that
        # match no known tool (typo?)" on every preflight, telling the reader to
        # edit a correct file.
        #
        # The source-component selector was `src` until upstream 162423 renamed
        # it `rust-src` (ported in 60669f9fc2, rust-lang/rust bf9448e4). Since
        # 841e3c36da (2026-10-27) install.rs `Src` accepts the owned spelling
        # `trust-src` and `rust-src`, and its default-step gate also honours
        # the legacy `src` allowlist entry. So all three select the source
        # component. The "legacy" row pins that a profile naming `src` is not
        # called a typo while install.rs honours it; preflight reads that from
        # install.rs (the mutation control below), never from a fixed list.
        facts = preflight.read_bootstrap_facts(REPO_ROOT)
        self.assertIn("trustc-dev", facts.install_selectors)
        for selector in ("trust-src", "rust-src", "src"):
            self.assertIn(selector, facts.install_selectors)
        typo_title = "allowlist entries that match no known tool (typo?)"
        defaults = REPO_ROOT / "src" / "bootstrap" / "defaults"
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            for profile in ("compiler", "tools"):
                original = (defaults / f"bootstrap.{profile}.toml").read_text(encoding="utf-8")
                self.assertIn('"trustc-dev", "rust-src"', original)
                self.assertNotIn('"src"', original)
                for label, text, typo in (
                    ("committed", original, None),
                    ("typo", original.replace('"trustc-dev"', '"trustc-devv"', 1), "trustc-devv"),
                    ("legacy", original.replace('"rust-src"', '"src"', 1), None),
                ):
                    self.assertTrue(label == "committed" or text != original, (profile, label))
                    candidate = directory / f"{profile}-{label}.toml"
                    candidate.write_text(text, encoding="utf-8")
                    preflight._TOML_CACHE.clear()
                    cfg = self.resolve(candidate)
                    model = preflight.build_tool_model(REPO_ROOT, cfg, facts)
                    report = preflight.Report(False)
                    preflight.check_tools_allowlist(
                        REPO_ROOT, cfg, facts, report, candidate, model
                    )
                    typos = [
                        finding for finding in report.findings
                        if finding.severity == preflight.WARN and finding.title == typo_title
                    ]
                    if typo is None:
                        selected_installers = set(cfg["build"]["tools"]) & set(facts.install_selectors)
                        source = "src" if label == "legacy" else "rust-src"
                        self.assertTrue(
                            {"trustc-dev", source} <= selected_installers,
                            f"{profile} {label}: actual installer selections {sorted(selected_installers)}",
                        )
                        self.assertEqual(
                            typos, [], f"{profile} {label}: {[t.detail for t in typos]}"
                        )
                    else:
                        self.assertNotEqual(text, original, f"{profile}: ineffective {label} mutant")
                        self.assertEqual(len(typos), 1, (profile, label))
                        # Exact entries, not a substring: `src` is inside
                        # `rust-src`, so a substring check would also accept a
                        # warning about the correct selector.
                        self.assertEqual(typos[0].detail[0].split(", "), [typo], (profile, label))

    def test_install_selectors_follow_install_rs_not_a_fixed_list(self) -> None:
        # Mutation control for the selector derivation the committed-profile
        # test relies on. A hard-coded selector list in preflight would fail
        # either mutant:
        # - "pre-162423": install.rs back to the spelling before the rename, so
        #   `src` is the only source selector and `trust-src`/`rust-src` are
        #   unknown;
        # - "no legacy": install.rs stops honouring `src`, so `src` is unknown
        #   and the owned spellings stay.
        current = (REPO_ROOT / preflight.INSTALL_RS).read_text(encoding="utf-8")
        alias = 'run.alias("trust-src").alias("rust-src")'
        gates = {name: f't.contains("{name}")' for name in ("trust-src", "rust-src", "src")}
        self.assertEqual(current.count(alias), 1)
        for gate in gates.values():
            self.assertEqual(current.count(gate), 1, gate)
        pre_rename = (
            current.replace(alias, 'run.alias("src")')
            .replace(gates["trust-src"], gates["src"])
            .replace(gates["rust-src"], gates["src"])
        )
        no_legacy = current.replace(gates["src"], gates["rust-src"])
        for label, mutant, known, unknown in (
            ("pre-162423", pre_rename, {"src"}, {"trust-src", "rust-src"}),
            ("no legacy", no_legacy, {"trust-src", "rust-src"}, {"src"}),
        ):
            self.assertNotEqual(mutant, current, f"ineffective {label} mutant")
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                for relative, text in (
                    (preflight.TOOL_RS, None),
                    (preflight.DIST_RS, None),
                    (preflight.INSTALL_RS, mutant),
                ):
                    target = root / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    if text is None:
                        shutil.copy2(REPO_ROOT / relative, target)
                    else:
                        target.write_text(text, encoding="utf-8")
                facts = preflight.read_bootstrap_facts(root)
            for selector in known:
                self.assertIn(selector, facts.install_selectors, label)
            for selector in unknown:
                self.assertNotIn(selector, facts.install_selectors, label)
            self.assertIn("trustc-dev", facts.install_selectors, label)


class XPyForwardingTests(unittest.TestCase):
    def test_split_and_equals_forms_are_forwarded_before_double_dash(self) -> None:
        forwarded = x_entry._trust_preflight_config_args(
            [
                "--config",
                "../config/bootstrap.toml",
                "build",
                "--set=build.tools=[\"clean\",\"ty\"]",
                "--set",
                "build.extended=true",
                "--",
                "--set=ignored=true",
            ],
            "/work/tree",
        )
        self.assertEqual(
            forwarded,
            [
                "--bootstrap-cwd",
                "/work/tree",
                "--bootstrap-toml",
                "/work/config/bootstrap.toml",
                "--set",
                'build.tools=["clean","ty"]',
                "--set",
                "build.extended=true",
            ],
        )

    def test_equals_config_and_last_config_win(self) -> None:
        forwarded = x_entry._trust_preflight_config_args(
            ["--config=first.toml", "--config", "second.toml", "build"],
            "/work/tree",
        )
        self.assertEqual(forwarded[-2:], ["--bootstrap-toml", "/work/tree/second.toml"])


class RecursiveSubmoduleTests(unittest.TestCase):
    """Real nested Git worktrees, including staged drift hidden by status."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="trust-preflight-recursive-")
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.root = base / "super"
        self.parent = base / "parent"
        self.leaf = base / "leaf"
        for repo in (self.root, self.parent, self.leaf):
            repo.mkdir()
            self.git(repo, "init", "-q")
            self.git(repo, "config", "user.email", "preflight-test@example.invalid")
            self.git(repo, "config", "user.name", "Preflight test")
            self.git(repo, "commit", "-q", "--allow-empty", "-m", "initial")
        self.leaf_pin = self.git(self.leaf, "rev-parse", "HEAD")
        self.git(self.leaf, "commit", "-q", "--allow-empty", "-m", "later leaf")
        self.later_leaf = self.git(self.leaf, "rev-parse", "HEAD")
        for name in ("one", "two"):
            path = f"third_party/{name}"
            self.git(self.parent, "-c", "protocol.file.allow=always", "submodule",
                     "add", "-q", str(self.leaf), path)
            self.git(self.parent / path, "checkout", "-q", "--detach", self.leaf_pin)
        self.git(self.parent, "add", ".gitmodules", "third_party")
        self.git(self.parent, "commit", "-q", "-m", "nested pins")
        self.git(self.root, "-c", "protocol.file.allow=always", "submodule",
                 "add", "-q", str(self.parent), "first-party/parent")
        self.git(self.root, "commit", "-q", "-am", "parent pin")
        self.parent_checkout = self.root / "first-party/parent"
        self.nested = self.parent_checkout / "third_party/one"

    def git(self, repo: Path, *args: str) -> str:
        return subprocess.run(
            ["git", *args], cwd=repo, text=True, capture_output=True,
            timeout=20, check=True,
        ).stdout.strip()

    def initialise(self) -> None:
        self.git(self.root, "-c", "protocol.file.allow=always", "submodule",
                 "update", "-q", "--init", "--recursive")

    def report(self):
        report = preflight.Report(False)
        preflight.check_submodules(self.root, report)
        return report

    def assert_refused(self, report, text: str) -> None:
        failures = "\n".join(
            "\n".join([finding.title, *finding.detail]) for finding in report.findings
            if finding.severity == preflight.FAIL
        )
        self.assertIn(text, failures)
        self.assertFalse(any("submodules match" in f.title for f in report.findings))

    def test_uninitialised_nested_sources_cannot_report_all_synced(self) -> None:
        # Top-level status is clean even though both nested pins are absent.
        status = self.git(self.root, "submodule", "status")
        self.assertNotIn("third_party", status)
        report = self.report()
        self.assert_refused(report, "first-party/parent/third_party/one is NOT INITIALISED")
        self.assert_refused(report, "first-party/parent/third_party/two is NOT INITIALISED")
        self.assertFalse((self.nested / ".git").exists())

    def test_complete_nested_source_counts_every_module(self) -> None:
        self.initialise()
        report = self.report()
        self.assertFalse(any(f.severity == preflight.FAIL for f in report.findings))
        self.assertEqual(
            [f.title for f in report.findings if "submodules match" in f.title],
            ["all 3 recursive submodules match their pinned gitlink SHA"],
        )

    def test_nested_checkout_drift_is_refused(self) -> None:
        self.initialise()
        self.git(self.nested, "checkout", "-q", "--detach", self.later_leaf)
        report = self.report()
        self.assert_refused(report, "first-party/parent/third_party/one is AHEAD/BEHIND")
        self.assert_refused(report, self.leaf_pin)

    def test_staged_nested_drift_uses_immediate_parent_committed_pin(self) -> None:
        self.initialise()
        self.git(self.nested, "checkout", "-q", "--detach", self.later_leaf)
        self.git(self.parent_checkout, "add", "third_party/one")
        # Index-based status no longer has '+', but the parent commit still
        # pins the old leaf. Looking up this full path in the outer HEAD fails.
        report = self.report()
        self.assert_refused(report, "first-party/parent/third_party/one is off the COMMITTED pin")
        self.assert_refused(report, self.leaf_pin)
        self.assertTrue(any(
            "git -C first-party/parent restore --staged -- third_party/one" in f.fix
            for f in report.findings
        ))
        self.assertEqual(self.git(self.nested, "rev-parse", "HEAD"), self.later_leaf)

    def test_absent_parent_refuses_without_discovering_outer_git(self) -> None:
        self.git(self.root, "submodule", "deinit", "-q", "--", "first-party/parent")
        report = self.report()
        self.assert_refused(report, "first-party/parent is NOT INITIALISED")
        self.assertFalse((self.parent_checkout / ".git").exists())

    def test_failed_recursive_enumeration_is_not_a_warning_only(self) -> None:
        original = preflight.run

        def failing(command, **kwargs):
            if command == ["git", "submodule", "status", "--recursive"]:
                return 128, "", "unreadable nested repository"
            return original(command, **kwargs)

        with patch.object(preflight, "run", side_effect=failing):
            self.assert_refused(self.report(), "could not enumerate recursive submodule status")

    def test_malformed_recursive_record_refuses(self) -> None:
        original = preflight.run

        def malformed(command, **kwargs):
            if command == ["git", "submodule", "status", "--recursive"]:
                return 0, " malformed\n", ""
            return original(command, **kwargs)

        with patch.object(preflight, "run", side_effect=malformed):
            self.assert_refused(self.report(), "malformed recursive submodule status")


class ConcurrentBuildSiblingWorktreeTests(unittest.TestCase):
    """`check_concurrent_build` must see THIS checkout's builds and only those.

    Measured 2026-09-23: with worktrees `trust-wt` and `trust-wt-b2` side by side, a
    `bootstrap test` running in `trust-wt-b2` refused `x.py build` in `trust-wt`,
    because the root was matched as a bare substring of the sibling's path.
    """

    ROOT = Path("/work/trust-wt")

    def findings(self, *commands: str) -> list:
        rows = "\n".join(f"{900000 + i} 1 {cmd}" for i, cmd in enumerate(commands))
        rep = preflight.Report(color=False)
        with patch.object(preflight, "run", return_value=(0, rows + "\n", "")):
            preflight.check_concurrent_build(self.ROOT, rep, for_build=True)
        return [f for f in rep.findings if "ALREADY RUNNING" in f.title]

    def test_a_sibling_checkout_sharing_the_prefix_is_not_this_build(self) -> None:
        self.assertEqual(
            self.findings(
                "/work/trust-wt-b2/build/bootstrap/debug/bootstrap test --stage 1 crates/x",
                "/work/trust-wt.old/build/bootstrap/debug/bootstrap build --stage 1",
            ),
            [],
        )

    def test_this_checkouts_build_is_still_refused(self) -> None:
        # The negative twin: the same process shape INSIDE the root still blocks.
        found = self.findings("/work/trust-wt/build/bootstrap/debug/bootstrap build --stage 1")
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0].severity, preflight.FAIL)

    def test_the_root_itself_at_a_word_boundary_is_this_checkout(self) -> None:
        # A python-launched x.py whose command line names the root by an absolute path.
        found = self.findings("/usr/bin/python3 /work/trust-wt/x.py build --stage 1")
        self.assertEqual(len(found), 1)

    def test_names_this_checkout_path_boundaries(self) -> None:
        for cmd, want in self.BOUNDARY_TABLE:
            self.assertEqual(preflight.names_this_checkout(cmd, self.ROOT), want, cmd)

    # (cmd, names /work/trust-wt). Review 2026-09-29: the first rule was a LIST of
    # separators (`/`, whitespace, quotes), so the `=`, `:` and `,` rows -- the root
    # named and then followed by a character a directory name cannot continue with
    # -- were missed (fail open). The boundary is now the complement of the name
    # characters, the rule `scripts/submodule_sync.sh` enforces.
    BOUNDARY_TABLE = (
        ("x /work/trust-wt/build y", True),
        ("x /work/trust-wt y", True),
        ("x /work/trust-wt", True),
        ("x '/work/trust-wt' y", True),
        ('x "/work/trust-wt"/x.py y', True),
        ("x --remap-path-prefix=/work/trust-wt=/src y", True),
        ("x -L native=/work/trust-wt:/opt/lib y", True),
        ("x --roots /work/trust-wt,/elsewhere y", True),
        # a sibling first, this checkout later on the same line: still named
        ("x /work/trust-wt-b2/build /work/trust-wt/build", True),
        ("x /work/trust-wt-b2/build y", False),
        ("x /work/trust-wt.old/build y", False),
        ("x /work/trust-wt_old/build y", False),
        ("x /work/trust-wtx y", False),
        ("x /work/trust-w y", False),
    )

    def test_a_build_naming_the_root_before_equals_is_this_checkout(self) -> None:
        # End to end through `check_concurrent_build`: a cwd-relative x.py whose only
        # mention of the root is followed by `=` is reported, and its sibling twin
        # (`_old`, a name character) is not.
        found = self.findings(
            "/usr/bin/python3 x.py test --stage 1 --test-args"
            " --remap-path-prefix=/work/trust-wt=/src"
        )
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0].severity, preflight.FAIL)
        self.assertEqual(
            self.findings(
                "/work/trust-wt_old/build/bootstrap/debug/bootstrap build --stage 1",
                "/usr/bin/python3 x.py test --test-args"
                " --remap-path-prefix=/work/trust-wt_old=/src",
            ),
            [],
        )

    def test_mutation_the_separator_list_misses_the_equals_row(self) -> None:
        # Non-vacuity: the helper's own source with its boundary swapped back to the
        # first rule's separator list must miss the `=` / `:` / `,` rows and keep
        # every other row of the table. A rule the table cannot tell apart from the
        # old one would pass the boundary test while testing nothing new.
        import inspect
        import re as re_mod

        src = inspect.getsource(preflight.names_this_checkout)
        current = 'r"(?![A-Za-z0-9._-])"'
        old = 'r"(?=[/\\s\'\\"]|$)"'
        self.assertEqual(src.count(current), 1, "the boundary text moved; update this control")
        namespace: dict = {"re": re_mod, "Path": Path}
        exec(src.replace(current, old), namespace)
        mutant = namespace["names_this_checkout"]
        missed = [
            cmd
            for cmd, want in self.BOUNDARY_TABLE
            if mutant(cmd, self.ROOT) != want
        ]
        self.assertEqual(
            missed,
            [
                "x --remap-path-prefix=/work/trust-wt=/src y",
                "x -L native=/work/trust-wt:/opt/lib y",
                "x --roots /work/trust-wt,/elsewhere y",
            ],
        )


class BuildPinAncestryTests(unittest.TestCase):
    """Real Git graph controls; the publication checker is copied unchanged."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="trust-preflight-pin-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "super"
        self.sub = Path(self.temp.name) / "sub"
        for repo in (self.root, self.sub):
            repo.mkdir()
            self.git(repo, "init", "-q")
            self.git(repo, "config", "user.email", "preflight-test@example.invalid")
            self.git(repo, "config", "user.name", "Preflight test")
        self.git(self.sub, "commit", "-q", "--allow-empty", "-m", "sub one")
        self.old_pin = self.git(self.sub, "rev-parse", "HEAD")
        self.git(self.sub, "commit", "-q", "--allow-empty", "-m", "sub two")
        self.new_pin = self.git(self.sub, "rev-parse", "HEAD")
        self.git(self.root, "clone", "-q", str(self.sub), "first-party/m")
        (self.root / ".gitmodules").write_text(
            '[submodule "m"]\npath = first-party/m\n', encoding="utf-8"
        )
        (self.root / "scripts").mkdir()
        self.script = self.root / "scripts" / "check_pin_regression.sh"
        shutil.copyfile(REPO_ROOT / "scripts" / self.script.name, self.script)
        self.base = self.commit(self.old_pin, "base")
        self.set_head(self.base, self.old_pin)

    def git(self, repo: Path, *args: str, input: str | None = None) -> str:
        return subprocess.run(
            ["git", *args], cwd=repo, input=input, text=True, capture_output=True,
            timeout=20, check=True,
        ).stdout.strip()

    def commit(self, pin: str, message: str, *parents: str) -> str:
        self.git(self.root, "update-index", "--add", "--cacheinfo",
                 f"160000,{pin},first-party/m")
        tree = self.git(self.root, "write-tree")
        argv = ["commit-tree", tree]
        for parent in parents:
            argv += ["-p", parent]
        return self.git(self.root, *argv, "-m", message)

    def set_head(self, revision: str, pin: str) -> None:
        self.git(self.root, "update-ref", "refs/heads/build", revision)
        self.git(self.root, "symbolic-ref", "HEAD", "refs/heads/build")
        self.git(self.root / "first-party/m", "checkout", "-q", "--detach", pin)

    def remote(self, revision: str) -> None:
        self.git(self.root, "update-ref", "refs/remotes/origin/main", revision)

    def report(self):
        report = preflight.Report(False)
        preflight.check_pin_regression(self.root, report)
        return report

    def assert_cleared(self, report) -> None:
        self.assertEqual([f for f in report.findings if f.severity == preflight.FAIL], [])

    def assert_refused(self, report, text: str) -> None:
        failures = "\n".join(
            "\n".join([f.title, *f.detail]) for f in report.findings
            if f.severity == preflight.FAIL
        )
        self.assertIn(text, failures)

    def test_remote_advance_does_not_turn_historical_build_into_rollback(self) -> None:
        local = self.commit(self.old_pin, "local compiler work", self.base)
        self.set_head(local, self.old_pin)
        self.remote(self.base)
        before = preflight.build_pin_ranges(self.root)
        newer = self.commit(self.new_pin, "remote pin update", self.base)
        self.remote(newer)
        after = preflight.build_pin_ranges(self.root)
        self.assertEqual(before[:2], after[:2])
        self.assertEqual(after[1], [f"{self.base}..{local}"])
        self.assertIn(f"observed origin/main: {newer}", after[2])
        self.assert_cleared(self.report())

        # The SAME proposed publication would undo the newer destination pin.
        # The actual pre-push input and standalone default still refuse it.
        for argv, stdin in (
            (["--stdin"], f"refs/heads/build {local} refs/heads/main {newer}\n"),
            ([], None),
        ):
            result = subprocess.run(
                ["bash", str(self.script), *argv], cwd=self.root, input=stdin,
                capture_output=True, text=True, timeout=20,
            )
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("BACKWARD", result.stdout)
        self.assertEqual(self.script.read_bytes(),
                         (REPO_ROOT / "scripts" / self.script.name).read_bytes())

    def test_detached_ancestor_build_uses_its_own_commit(self) -> None:
        self.remote(self.commit(self.new_pin, "remote advance", self.base))
        self.git(self.root, "update-ref", "--no-deref", "HEAD", self.base)
        tip, ranges, _ = preflight.build_pin_ranges(self.root)
        self.assertEqual(tip, self.base)
        self.assertEqual(ranges, [f"{self.base}..{self.base}"])
        self.assert_cleared(self.report())

    def test_genuine_local_rollback_is_refused(self) -> None:
        updated = self.commit(self.new_pin, "advance", self.base)
        rolled_back = self.commit(self.old_pin, "unrelated work", updated)
        self.remote(updated)
        self.set_head(rolled_back, self.old_pin)
        self.assert_refused(self.report(), "BACKWARD")

    def test_forward_and_revert_then_restore_net_changes_pass(self) -> None:
        updated = self.commit(self.new_pin, "advance", self.base)
        self.remote(self.base)
        self.set_head(updated, self.new_pin)
        self.assert_cleared(self.report())
        rollback = self.commit(self.old_pin, "mistaken rollback", updated)
        repair = self.commit(self.new_pin, "repair", rollback)
        self.remote(updated)
        self.set_head(repair, self.new_pin)
        self.assert_cleared(self.report())

    def test_inherited_rollback_remains_visible_to_history_guard(self) -> None:
        updated = self.commit(self.new_pin, "advance", self.base)
        rollback = self.commit(self.old_pin, "mistaken rollback", updated)
        self.remote(rollback)
        self.set_head(rollback, self.old_pin)
        report = self.report()
        preflight.check_pin_behind_history(self.root, report)
        self.assert_refused(report, "STRICT ANCESTOR")

    def test_absent_remote_uses_parent_without_fetch(self) -> None:
        child = self.commit(self.old_pin, "offline work", self.base)
        self.set_head(child, self.old_pin)
        _, ranges, notes = preflight.build_pin_ranges(self.root)
        self.assertEqual(ranges, [f"{self.base}..{child}"])
        self.assertTrue(any("origin/main is absent" in note for note in notes))
        self.assert_cleared(self.report())

    def test_absent_remote_does_not_hide_local_rollback(self) -> None:
        updated = self.commit(self.new_pin, "advance", self.base)
        rollback = self.commit(self.old_pin, "mistaken rollback", updated)
        self.set_head(rollback, self.old_pin)
        self.assert_refused(self.report(), "BACKWARD")

    def test_unrelated_remote_uses_actual_parent(self) -> None:
        unrelated = self.commit(self.new_pin, "different root")
        local = self.commit(self.old_pin, "local work", self.base)
        self.remote(unrelated)
        self.set_head(local, self.old_pin)
        _, ranges, notes = preflight.build_pin_ranges(self.root)
        self.assertEqual(ranges, [f"{self.base}..{local}"])
        self.assertTrue(any("no common ancestry" in note for note in notes))
        self.assert_cleared(self.report())

    def test_offline_merge_checks_every_parent(self) -> None:
        older = self.commit(self.old_pin, "old side", self.base)
        newer = self.commit(self.new_pin, "new side", self.base)
        merged = self.commit(self.old_pin, "merge picked stale pin", older, newer)
        self.set_head(merged, self.old_pin)
        _, ranges, _ = preflight.build_pin_ranges(self.root)
        self.assertEqual(set(ranges), {f"{older}..{merged}", f"{newer}..{merged}"})
        self.assert_refused(self.report(), "BACKWARD")

    def test_criss_cross_checks_all_best_common_ancestors(self) -> None:
        older = self.commit(self.old_pin, "old side", self.base)
        newer = self.commit(self.new_pin, "new side", self.base)
        local = self.commit(self.old_pin, "local merge", older, newer)
        remote = self.commit(self.new_pin, "remote merge", newer, older)
        self.remote(remote)
        self.set_head(local, self.old_pin)
        _, ranges, _ = preflight.build_pin_ranges(self.root)
        self.assertEqual(set(ranges), {f"{older}..{local}", f"{newer}..{local}"})
        self.assert_refused(self.report(), "BACKWARD")

    def test_root_without_remote_reports_no_comparison(self) -> None:
        _, ranges, notes = preflight.build_pin_ranges(self.root)
        self.assertEqual(ranges, [])
        self.assertTrue(any("no available parent" in note for note in notes))
        self.assert_cleared(self.report())

    def test_shallow_cutoff_is_disclosed_not_called_true_root(self) -> None:
        child = self.commit(self.old_pin, "shallow boundary", self.base)
        self.set_head(child, self.old_pin)
        (self.root / ".git" / "shallow").write_text(child + "\n", encoding="ascii")
        _, ranges, notes = preflight.build_pin_ranges(self.root)
        self.assertEqual(ranges, [])
        self.assertTrue(any("shallow history" in note for note in notes))
        self.assertTrue(any("no available parent" in note for note in notes))

    def test_ref_change_during_check_does_not_change_the_audited_range(self) -> None:
        local = self.commit(self.old_pin, "local work", self.base)
        newer = self.commit(self.new_pin, "remote advance", self.base)
        self.set_head(local, self.old_pin)
        self.remote(self.base)
        actual_run = subprocess.run
        audited = []

        def move_remote(argv, **kwargs):
            if argv[0] == "bash":
                self.remote(newer)
                audited.append(argv[-1])
            return actual_run(argv, **kwargs)

        with patch.object(preflight.subprocess, "run", side_effect=move_remote):
            self.assert_cleared(self.report())
        self.assertEqual(audited, [f"{self.base}..{local}"])

    def test_changed_head_refuses_stale_assessment(self) -> None:
        local = self.commit(self.old_pin, "local work", self.base)
        next_head = self.commit(self.old_pin, "concurrent work", local)
        self.set_head(local, self.old_pin)
        self.remote(self.base)
        actual_run = subprocess.run

        def move_head(argv, **kwargs):
            if argv[0] == "bash":
                self.git(self.root, "update-ref", "refs/heads/build", next_head)
            return actual_run(argv, **kwargs)

        with patch.object(preflight.subprocess, "run", side_effect=move_head):
            self.assert_refused(self.report(), "HEAD changed")

    def test_git_failure_is_not_treated_as_absent_remote(self) -> None:
        actual_run = subprocess.run

        def fail_git(argv, **kwargs):
            if argv[:2] == ["git", "show-ref"]:
                return subprocess.CompletedProcess(argv, 128, "", "Git read failed")
            return actual_run(argv, **kwargs)

        with patch.object(preflight.subprocess, "run", side_effect=fail_git):
            self.assert_refused(self.report(), "could not be completed")

    def test_malformed_git_output_is_not_a_successful_comparison(self) -> None:
        self.remote(self.base)
        actual_run = subprocess.run

        def corrupt_git(argv, **kwargs):
            if argv[:2] == ["git", "merge-base"]:
                return subprocess.CompletedProcess(argv, 0, "not-a-commit\n", "")
            return actual_run(argv, **kwargs)

        with patch.object(preflight.subprocess, "run", side_effect=corrupt_git):
            self.assert_refused(self.report(), "invalid Git commit identity")

    def test_checker_timeout_is_not_a_successful_comparison(self) -> None:
        self.remote(self.base)
        actual_run = subprocess.run

        def time_out(argv, **kwargs):
            if argv[0] == "bash":
                raise subprocess.TimeoutExpired(argv, 60)
            return actual_run(argv, **kwargs)

        with patch.object(preflight.subprocess, "run", side_effect=time_out):
            self.assert_refused(self.report(), "could not be completed")

    def test_checker_error_is_not_misreported_as_pin_rollback(self) -> None:
        self.remote(self.base)
        actual_run = subprocess.run

        def fail_checker(argv, **kwargs):
            if argv[0] == "bash":
                return subprocess.CompletedProcess(argv, 2, "", "fixture checker error")
            return actual_run(argv, **kwargs)

        with patch.object(preflight.subprocess, "run", side_effect=fail_checker):
            self.assert_refused(self.report(), "checker did not complete")
            self.assert_refused(self.report(), "fixture checker error")


class PinHistoryBatchTests(unittest.TestCase):
    """Small real object stores preserve native Git history/ancestry semantics."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="trust-pin-history-batch-")
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.case = 0

    def git(self, repo: Path, *args: str, input: bytes | None = None) -> bytes:
        return subprocess.run(["git", *args], cwd=repo, input=input,
                              capture_output=True, timeout=20, check=True).stdout

    def graph(self, repo: Path, entries) -> list[str]:
        """Import private commits in one Git process; never touch a real ref."""
        marks = repo / ".git/fixture.marks"
        commands = bytearray()
        for index, (parents, files, message) in enumerate(entries, 1):
            commands.extend(f"commit refs/heads/c{index}\nmark :{index}\n"
                            f"committer Fixture <fixture@example.invalid> {1000000000 + index} +0000\n"
                            .encode())
            data = message.encode()
            commands.extend(f"data {len(data)}\n".encode() + data + b"\n")
            for offset, parent in enumerate(parents):
                commands.extend(f"{'from' if offset == 0 else 'merge'} :{parent + 1}\n".encode())
            commands.extend(b"deleteall\n")
            for name, mode, oid in files:
                quoted = json.dumps(name, ensure_ascii=False)
                if mode == "100644":
                    commands.extend(f"M 100644 inline {quoted}\ndata 1\nx\n".encode())
                else:
                    commands.extend(f"M {mode} {oid} {quoted}\n".encode())
            commands.extend(b"\n")
        self.git(repo, "fast-import", "--quiet", "--force", f"--export-marks={marks}",
                 input=bytes(commands))
        objects = dict(line.split() for line in marks.read_text().splitlines())
        return [objects[f":{index}"] for index in range(1, len(entries) + 1)]

    def fixture(self, subparents, states, *, path="first-party/m", messages=None,
                parents=None):
        self.case += 1
        root = self.directory / str(self.case)
        sub = root / path
        sub.mkdir(parents=True)
        for repo in (root, sub):
            self.git(repo, "init", "-q")
        pins = self.graph(sub, [(ps, [], f"sub {i}") for i, ps in enumerate(subparents)])
        entries = []
        for index, state in enumerate(states):
            files = []
            if isinstance(state, dict):
                files = [(name, "160000", pins[pin]) for name, pin in state.items()]
            elif isinstance(state, int):
                files = [(path, "160000", pins[state])]
            elif state == "file":
                files = [(path, "100644", "")]
            elif state == "tree":
                files = [(path + "/nested", "160000", pins[-1])]
            ps = parents[index] if parents is not None else ([index - 1] if index else [])
            message = messages[index] if messages is not None else f"super {index}"
            entries.append((ps, files, message))
        revisions = self.graph(root, entries)
        self.git(root, "symbolic-ref", "HEAD", f"refs/heads/c{len(entries)}")
        (root / ".gitmodules").write_text(
            f'[submodule "fixture"]\npath = {json.dumps(path, ensure_ascii=False)}\n')
        return root, sub, pins, revisions

    def report(self, root: Path):
        report = preflight.Report(False)
        calls = []
        actual = subprocess.run

        def observe(argv, **kwargs):
            calls.append(argv)
            return actual(argv, **kwargs)

        started = time.monotonic()
        with patch.object(preflight.subprocess, "run", side_effect=observe):
            preflight.check_pin_behind_history(root, report)
        self.measurement = (len(calls), time.monotonic() - started)
        return report.findings, calls

    def test_forward_history_has_bounded_git_processes(self) -> None:
        root, _, _, _ = self.fixture([[]] + [[i] for i in range(49)], list(range(50)))
        findings, calls = self.report(root)
        self.assertEqual(findings, [])
        self.assertLessEqual(len(calls), 12, f"one process per pin returned: {self.measurement}")
        self.assertFalse(any("ls-tree" in command or "merge-base" in command for command in calls))

    def test_fortieth_commit_is_included_but_forty_first_is_not(self) -> None:
        # cur=1; high-water=2 descends from it; pins 3..41 are on a sibling line.
        subparents = [[], [0], [1], [0]] + [[i] for i in range(3, 41)]
        for count, expected in ((38, True), (39, False)):
            root, _, _, revisions = self.fixture(subparents, [2, *range(3, 3 + count), 1])
            findings, _ = self.report(root)
            self.assertEqual(bool(findings), expected)
            if expected:
                self.assertEqual(findings[0].severity, preflight.FAIL)
                self.assertIn(revisions[0][:10], findings[0].detail[1])
                # Effective mutant: reducing the exact horizon loses this row.
                with patch.object(preflight, "PIN_HISTORY_LIMIT", 39):
                    mutant, _ = self.report(root)
                self.assertEqual(mutant, [])

    def test_deleted_file_tree_and_repeated_pins_preserve_the_recording_commit(self) -> None:
        root, _, pins, revisions = self.fixture(
            [[], [0]], [1, 0, 1, None, "file", "tree", 0])
        findings, _ = self.report(root)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, preflight.FAIL)
        self.assertIn(pins[1], findings[0].detail[1])
        self.assertIn(revisions[2][:10], findings[0].detail[1])

    def test_disclosure_window_and_nonancestor_pins_are_preserved(self) -> None:
        graph = [[], [0], [1], [2], [0]]
        for states, messages, severity in (
            ([4, 1], ["sibling", "current"], None),
            ([2, 1], ["high", "rollback\n\npin-rollback: first-party/m deliberate"], preflight.INFO),
            ([2, 1, 3, 1], ["high", "pin-rollback: first-party/m earlier disclosure",
                            "new high-water", "fresh undisclosed rollback"], preflight.FAIL),
        ):
            root, _, _, _ = self.fixture(graph, states, messages=messages)
            findings, _ = self.report(root)
            self.assertEqual([f.severity for f in findings], [] if severity is None else [severity])

    def test_literal_config_paths_and_uninitialized_or_nongitlink_heads(self) -> None:
        path = "first-party/solver [x]\n;$(touch not-executed)"
        root, sub, pins, _ = self.fixture([[], [0]], [1, 0], path=path)
        findings, _ = self.report(root)
        self.assertEqual(len(findings), 1)
        self.assertIn(path, findings[0].title)
        self.assertEqual(shlex.split(findings[0].fix[0]),
                         ["git", "-C", path, "checkout", pins[1][:12], "&&", "git", "add", path])
        self.assertFalse((root / "not-executed").exists())
        (sub / ".git").rename(sub / ".git-disabled")
        self.assertEqual(self.report(root)[0], [])
        for mode in (None, "file", "tree"):
            root, _, _, _ = self.fixture([[], [0]], [1, mode])
            self.assertEqual(self.report(root)[0], [])

        # A bracketed path must not import another repo's matching history.
        path = "first-party/m[ab]"
        root, _, _, _ = self.fixture([[], [0]],
                                    [{path: 0, "first-party/ma": 1},
                                     {path: 0, "first-party/ma": 0}], path=path)
        self.assertEqual(self.report(root)[0], [])

    def test_each_configured_repository_and_duplicate_population_is_checked(self) -> None:
        root, _, pins, _ = self.fixture([[], [0]], [1, 0])
        other = root / "first-party/n"
        other.mkdir()
        self.git(other, "init", "-q")
        other_pins = self.graph(other, [([], [], "other old"), ([0], [], "other new")])
        self.graph(root, [([], [("first-party/m", "160000", pins[1]),
                               ("first-party/n", "160000", other_pins[1])], "advance both"),
                          ([0], [("first-party/m", "160000", pins[0]),
                                 ("first-party/n", "160000", other_pins[0])], "rollback both")])
        with (root / ".gitmodules").open("a") as stream:
            stream.write('[submodule "second"]\npath = first-party/n\n'
                         '[submodule "duplicate"]\npath = first-party/m\n')
        findings, _ = self.report(root)
        self.assertEqual([f.severity for f in findings], [preflight.FAIL] * 3)
        self.assertEqual([f.title.split()[0] for f in findings],
                         ["first-party/m", "first-party/n", "first-party/m"])

    def test_native_merge_history_simplification_is_unchanged(self) -> None:
        for merge_pin, expected in ((1, False), (0, True)):
            root, _, _, _ = self.fixture(
                [[], [0], [1], [0]], [0, 2, 1, merge_pin],
                parents=[[], [0], [0], [1, 2]])
            findings, _ = self.report(root)
            self.assertEqual(bool(findings), expected)

    def test_batched_ancestry_matches_native_git_including_tags_and_missing_objects(self) -> None:
        root, sub, pins, _ = self.fixture([[], [0], [1], [2], [0]], [1])
        self.git(sub, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "tag", "-a", "alias", pins[1], "-m", "same commit under a tag")
        tag = self.git(sub, "rev-parse", "refs/tags/alias").decode().strip()
        blob = self.git(sub, "hash-object", "-w", "--stdin", input=b"not a commit").decode().strip()
        candidates = [*pins, tag, blob, "f" * 40]
        expected = {old for old in candidates if subprocess.run(
            ["git", "merge-base", "--is-ancestor", pins[1], old], cwd=sub,
            capture_output=True, timeout=20).returncode == 0}
        self.assertEqual(preflight._historical_descendants(sub, pins[1], candidates), expected)
        self.assertEqual(preflight._historical_descendants(sub, "f" * 40, candidates), set())

    def test_batch_failures_fall_back_without_losing_findings(self) -> None:
        root, _, _, _ = self.fixture([[], [0]], [1, 0])
        actual = subprocess.run
        for broken in ("--batch", "--batch-check", "rev-list", "malformed-batch"):
            def fail_batch(argv, **kwargs):
                if broken == "malformed-batch" and "--batch" in argv:
                    return subprocess.CompletedProcess(argv, 0, b"not a batch header\n", b"")
                if broken in argv:
                    return subprocess.CompletedProcess(argv, 128, b"", b"fixture batch error")
                return actual(argv, **kwargs)

            report = preflight.Report(False)
            with patch.object(preflight.subprocess, "run", side_effect=fail_batch):
                preflight.check_pin_behind_history(root, report)
            self.assertEqual([f.severity for f in report.findings], [preflight.FAIL], broken)


class PathVersionCascadeTests(unittest.TestCase):
    """A local-path crate outside the workspace moves its version.

    Pinned by the 2026-09-17 `crates/trust-spec-temporal` lock, which recorded
    ay 0.22 / clean 0.8 / ty 0.14 / trust-ir 0.13 after the pins moved on, while
    the fast tier reported every workspace textually consistent.
    """

    def setUp(self) -> None:
        for memo in (preflight._TOML_CACHE, preflight._WS_MANIFESTS, preflight._GRAPH,
                     preflight._WS_ROOT, preflight._BUILD_CRITICAL):
            memo.clear()
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name).resolve()
        self.ws = self.root / "ws"
        self.write("ext/b/Cargo.toml",
                   '[package]\nname = "b"\nversion = "0.2.0"\n')
        self.write("ext/c/Cargo.toml",
                   '[package]\nname = "c"\nversion.workspace = true\n')
        self.write("ext/Cargo.toml",
                   '[workspace]\nmembers = ["c"]\n[workspace.package]\nversion = "0.3.0"\n')
        self.write("ext/Cargo.lock", "version = 4\n")

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def write(self, rel_path: str, text: str) -> None:
        path = self.root / rel_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def workspace(self, lock_body: str, *, with_patch: bool = False) -> None:
        manifest = ('[package]\nname = "a"\nversion = "0.1.0"\n[workspace]\n'
                    '[dependencies]\nb = { path = "../ext/b" }\n')
        if with_patch:
            manifest += ('[patch."https://example.invalid/c.git"]\n'
                         'c = { path = "../ext/c" }\n')
        self.write("ws/Cargo.toml", manifest)
        self.write("ws/Cargo.lock",
                   'version = 4\n\n[[package]]\nname = "a"\nversion = "0.1.0"\n'
                   'dependencies = ["b"]\n\n' + lock_body)

    def findings(self):
        report = preflight.Report(False)
        preflight.check_path_version_cascade(self.root, [self.ws], report)
        return report.findings

    def test_aligned_path_dependency_is_quiet(self) -> None:
        self.workspace('[[package]]\nname = "b"\nversion = "0.2.0"\n')
        self.assertEqual(self.findings(), [])

    def test_stale_path_dependency_outside_the_workspace_is_reported(self) -> None:
        self.workspace('[[package]]\nname = "b"\nversion = "0.1.0"\n')
        found = self.findings()
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0].severity, preflight.WARN)  # no bootstrap step names it
        self.assertIn("b local=0.2.0 lock=0.1.0", "\n".join(found[0].detail))

    def test_applied_patch_target_version_is_compared(self) -> None:
        stale = ('[[package]]\nname = "b"\nversion = "0.2.0"\n\n'
                 '[[package]]\nname = "c"\nversion = "0.2.0"\n')
        self.workspace(stale, with_patch=True)
        found = self.findings()
        self.assertEqual(len(found), 1)
        self.assertIn("c local=0.3.0 lock=0.2.0  ([patch] target", "\n".join(found[0].detail))

        for memo in (preflight._TOML_CACHE, preflight._GRAPH):
            memo.clear()
        self.workspace(stale.replace('"c"\nversion = "0.2.0"', '"c"\nversion = "0.3.0"'),
                       with_patch=True)
        self.assertEqual(self.findings(), [])

    def test_unused_patch_row_version_is_compared(self) -> None:
        self.workspace('[[package]]\nname = "b"\nversion = "0.2.0"\n\n'
                       '[[patch.unused]]\nname = "c"\nversion = "0.2.0"\n', with_patch=True)
        found = self.findings()
        self.assertEqual(len(found), 1)
        self.assertIn("unused [patch] target", "\n".join(found[0].detail))

    def test_declined_patch_with_a_sourced_package_is_not_accused(self) -> None:
        self.workspace('[[package]]\nname = "b"\nversion = "0.2.0"\n\n'
                       '[[package]]\nname = "c"\nversion = "0.1.0"\n'
                       'source = "git+https://example.invalid/c.git?rev=abc#'
                       + "0" * 40 + '"\n', with_patch=True)
        self.assertEqual(self.findings(), [])

    def test_inherited_version_accepts_an_enclosing_workspace(self) -> None:
        # The repository root resolves a nested crate's `version.workspace`
        # against its own table; either ancestor's version is a valid lock entry.
        self.write("ext/b/Cargo.toml", '[package]\nname = "b"\nversion.workspace = true\n')
        self.write("Cargo.toml", '[workspace]\n[workspace.package]\nversion = "0.9.0"\n')
        self.workspace('[[package]]\nname = "b"\nversion = "0.9.0"\n')
        self.assertEqual(self.findings(), [])
        # ...but a version NEITHER workspace declares is still skew.
        for memo in (preflight._TOML_CACHE, preflight._GRAPH):
            memo.clear()
        self.workspace('[[package]]\nname = "b"\nversion = "0.8.0"\n')
        self.assertEqual(len(self.findings()), 1)


class LocalDependencyEdgeCascadeTests(unittest.TestCase):
    """Same-version local dependency removal must fail before Bootstrap compilation."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(dir=os.environ.get("TRUST_PREFLIGHT_FIXTURE_ROOT"))
        self.root = Path(self.tmp.name).resolve()
        self.ws = self.root / "src/tools/targo"
        self.runtime = self.root / "first-party/clean/crates/clean-runtime"
        self.write("src/bootstrap/src/core/build_steps/tool.rs", 'ToolBuild { path: "src/tools/targo" }')
        self.write("src/tools/targo/Cargo.toml",
                   '[package]\nname = "frontend"\nversion = "0.1.0"\n[workspace]\n'
                   '[dependencies]\nclean-runtime = { path = "../../../first-party/clean/crates/clean-runtime" }\n'
                   'cc = { path = "../../../support/cc" }\n')
        self.write("src/tools/targo/src/lib.rs", "pub fn fixture_marker() {}\n")
        self.write("first-party/clean/Cargo.toml",
                   '[workspace]\nmembers = ["crates/clean-runtime"]\n'
                   '[workspace.package]\nversion = "1.3.0"\n')
        self.write("first-party/clean/crates/clean-runtime/Cargo.toml",
                   '[package]\nname = "clean-runtime"\nversion.workspace = true\n')
        self.write("first-party/clean/crates/clean-runtime/src/lib.rs", "pub fn fixture_marker() {}\n")
        self.write("support/cc/Cargo.toml", '[package]\nname = "cc"\nversion = "1.0.0"\n[workspace]\n')
        self.write("support/cc/src/lib.rs", "pub fn fixture_marker() {}\n")
        self.lock()

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        for memo in (preflight._TOML_CACHE, preflight._WS_MANIFESTS, preflight._GRAPH,
                     preflight._WS_ROOT, preflight._BUILD_CRITICAL):
            memo.clear()

    def lock(self, edge=True, source=False):
        self.write("src/tools/targo/Cargo.lock", 'version = 4\n\n'
                   '[[package]]\nname = "frontend"\nversion = "0.1.0"\ndependencies = ["clean-runtime", "cc"]\n\n'
                   '[[package]]\nname = "clean-runtime"\nversion = "1.3.0"\n'
                   + ('source = "registry+https://example.invalid/index"\n' if source else '')
                   + ('dependencies = ["cc"]\n' if edge else '')
                   + '\n[[package]]\nname = "cc"\nversion = "1.0.0"\n')

    def findings(self):
        # Each check models a new read-only preflight process. A real offline resolver
        # refreshes Cargo.lock between checks, outside the prior process's TOML snapshot.
        for memo in (preflight._TOML_CACHE, preflight._WS_MANIFESTS, preflight._GRAPH,
                     preflight._WS_ROOT, preflight._BUILD_CRITICAL):
            memo.clear()
        with patch.dict(os.environ, {"CARGO_HOME": str(self.root / "cargo-home")}):
            report = preflight.Report(False)
            preflight.check_path_version_cascade(self.root, [self.ws], report)
        return report.findings

    def test_same_version_removed_build_dependency_blocks_nested_frontend(self):
        found = self.findings()
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0].severity, preflight.FAIL)
        self.assertIn("ORPHANED", found[0].title)
        self.assertIn("clean-runtime -> cc", "\n".join(found[0].detail))

    def test_coherent_lock_is_quiet(self):
        self.lock(edge=False)
        self.assertEqual(self.findings(), [])

    def test_normal_build_dev_and_all_target_aliases_are_a_conservative_union(self):
        original = (self.runtime / "Cargo.toml").read_text()
        for table in ("dependencies", "build-dependencies", "dev-dependencies",
                      "target.'cfg(unix)'.dependencies", "target.'cfg(windows)'.build-dependencies",
                      "target.'cfg(any())'.dev-dependencies"):
            optional = ", optional = true" if "dev-dependencies" not in table else ""
            self.write("first-party/clean/crates/clean-runtime/Cargo.toml", original
                       + f'[{table}]\nrenamed = {{ package = "cc", path = "../../../../support/cc"{optional} }}\n')
            manifest, _ = preflight.load_toml(self.runtime / "Cargo.toml")
            self.assertEqual(preflight.declared_local_dependency_names(self.root, self.runtime, manifest), {"cc"})
            self.assertEqual(self.findings(), [], table)

    def test_workspace_inherited_package_alias_is_preserved(self):
        root = self.root / "first-party/clean/Cargo.toml"
        self.write("first-party/clean/Cargo.toml", root.read_text()
                   + '[workspace.dependencies]\nrenamed = { package = "cc", path = "../../support/cc" }\n')
        manifest = self.runtime / "Cargo.toml"
        self.write("first-party/clean/crates/clean-runtime/Cargo.toml", manifest.read_text()
                   + "[target.'cfg(unix)'.build-dependencies]\nrenamed.workspace = true\n")
        parsed, _ = preflight.load_toml(manifest)
        self.assertEqual(preflight.declared_local_dependency_names(self.root, self.runtime, parsed), {"cc"})
        self.assertEqual(self.findings(), [])

    def test_unresolved_workspace_dependency_stays_unknown(self):
        manifest = self.runtime / "Cargo.toml"
        self.write("first-party/clean/crates/clean-runtime/Cargo.toml", manifest.read_text()
                   + '[dependencies]\nunknown.workspace = true\n')
        self.assertEqual(self.findings(), [])

    def test_conflicting_local_owners_stay_unknown(self):
        self.write("support/other/Cargo.toml", '[package]\nname = "clean-runtime"\nversion = "1.3.0"\n[workspace]\n')
        manifest = self.ws / "Cargo.toml"
        self.write("src/tools/targo/Cargo.toml", manifest.read_text()
                   + '[patch."https://example.invalid/clean.git"]\nother = { package = "clean-runtime", path = "../../../support/other" }\n')
        self.assertEqual(self.findings(), [])

    def test_sourced_package_is_never_judged_from_local_manifest(self):
        self.lock(source=True)
        self.assertEqual(self.findings(), [])

    def test_incomplete_local_graph_stays_unknown(self):
        manifest = self.ws / "Cargo.toml"
        self.write("src/tools/targo/Cargo.toml", manifest.read_text()
                   + 'missing = { path = "../../../absent", optional = true }\n')
        self.assertEqual(self.findings(), [])

    def test_malformed_manifest_shapes_remain_unknown_to_the_edge_check(self):
        # Real TOML parses successfully but has an invalid Cargo table shape. Leave its
        # existing manifest/resolver diagnostic intact, without a new Python exception.
        self.write("support/malformed/Cargo.toml",
                   'package = "invalid"\n[dependencies]\nalias.workspace = true\n')
        directory = self.root / "support/malformed"
        manifest, error = preflight.load_toml(directory / "Cargo.toml")
        self.assertIsNone(error)
        self.assertIsNone(preflight.declared_local_dependency_names(self.root, directory, manifest))
        for owner in ('workspace = "invalid"\n', '[workspace]\ndependencies = "invalid"\n'):
            self.write("support/owner/Cargo.toml", owner)
            self.write("support/malformed/Cargo.toml",
                       '[package]\nname = "malformed"\nversion = "1.0.0"\nworkspace = "../owner"\n'
                       '[dependencies]\nalias.workspace = true\n')
            manifest, _ = preflight.load_toml(directory / "Cargo.toml")
            self.assertIsNone(preflight.declared_local_dependency_names(self.root, directory, manifest))

    def test_genuine_targo_stale_and_coherent_nested_lock(self):
        tool = os.environ.get("TRUST_PREFLIGHT_TARGO") or shutil.which("targo")
        if not tool:
            self.skipTest("genuine declared Targo unavailable")
        tool = str(Path(tool).resolve(strict=True))
        compiler = Path(tool).with_name("trustc")
        self.assertTrue(compiler.is_file(), "the declared Targo must have its paired Trust compiler")
        providers = {name: dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())
                     for name, path in (("targo", Path(tool)), ("trustc", compiler))}
        env = dict(os.environ, CARGO_HOME=str(self.root / "cargo-home"),
                   CARGO_TARGET_DIR=str(self.root / "metadata-target.noindex"))
        for key in ("RUSTC", "CARGO_BUILD_RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                    "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"):
            env.pop(key, None)
        evidence = []
        success = False
        def run(*args):
            # Metadata is a read-only verb, not a compilation lane. SDK2 correctly rejects
            # --unverified there; use it only for the genuine-Targo version discriminator.
            lane = ["--unverified"] if args == ("--version",) else []
            argv = [tool, *lane, "--config", "build.rustc=" + json.dumps(str(compiler)), *args]
            before = (self.ws / "Cargo.lock").read_bytes() if (self.ws / "Cargo.lock").exists() else b""
            if os.name == "posix":
                # Preserve the canonical caller's genuine resource descriptors and cancellation
                # custody; a plain subprocess would retain their env markers but close the FDs.
                library = str(REPO_ROOT / "scripts/lib")
                if library not in sys.path:
                    sys.path.insert(0, library)
                import native_serial
                result = native_serial.run_custodied_command(argv, cwd=self.ws, env=env, timeout=60)
            else:
                result = subprocess.run(argv, cwd=self.ws, env=env, capture_output=True, text=True, timeout=60)
            after = (self.ws / "Cargo.lock").read_bytes() if (self.ws / "Cargo.lock").exists() else b""
            evidence.append(dict(argv=argv, exit=result.returncode, stdout=result.stdout, stderr=result.stderr,
                                 lock_before_sha256=hashlib.sha256(before).hexdigest(),
                                 lock_after_sha256=hashlib.sha256(after).hexdigest(),
                                 runtime_manifest=(self.runtime / "Cargo.toml").read_text()))
            return result
        try:
            version = run("--version")
            self.assertEqual(version.returncode, 0, version.stderr)
            self.assertIn("targo", version.stdout.lower())
            original = (self.runtime / "Cargo.toml").read_text()
            self.write("first-party/clean/crates/clean-runtime/Cargo.toml", original
                       + '[build-dependencies]\ncc = { path = "../../../../support/cc" }\n')
            (self.ws / "Cargo.lock").unlink()
            generated = run("metadata", "--offline", "--format-version", "1")
            self.assertEqual(generated.returncode, 0, generated.stderr)
            self.write("first-party/clean/crates/clean-runtime/Cargo.toml", original)
            stale = (self.ws / "Cargo.lock").read_bytes()
            refused = run("metadata", "--locked", "--offline", "--format-version", "1")
            self.assertNotEqual(refused.returncode, 0)
            self.assertIn("locked", refused.stderr)
            self.assertEqual((self.ws / "Cargo.lock").read_bytes(), stale)
            self.assertEqual(len(self.findings()), 1)
            refreshed = run("metadata", "--offline", "--format-version", "1")
            self.assertEqual(refreshed.returncode, 0, refreshed.stderr)
            fixed = (self.ws / "Cargo.lock").read_bytes()
            old, new = preflight.tomllib.loads(stale.decode()), preflight.tomllib.loads(fixed.decode())
            identities = lambda lock: {(p["name"], p["version"], p.get("source"), p.get("checksum")) for p in lock["package"]}
            self.assertEqual(identities(old), identities(new))
            self.assertEqual(self.findings(), [])
            coherent = run("metadata", "--locked", "--offline", "--format-version", "1")
            self.assertEqual(coherent.returncode, 0, coherent.stderr)
            self.assertEqual((self.ws / "Cargo.lock").read_bytes(), fixed)
            self.assertEqual(providers, {name: dict(row, sha256=hashlib.sha256(Path(row["path"]).read_bytes()).hexdigest())
                                         for name, row in providers.items()})
            success = True
        finally:
            output = os.environ.get("TRUST_PREFLIGHT_LOCK_EVIDENCE")
            if output:
                directory = Path(output); directory.mkdir(parents=True, exist_ok=False)
                (directory / "ACTUAL-METADATA.json").write_text(json.dumps(dict(success=success,
                    providers_before=providers,
                    providers_after={name: dict(row, sha256=hashlib.sha256(Path(row["path"]).read_bytes()).hexdigest())
                                     for name, row in providers.items()}, commands=evidence), indent=2) + "\n")
                if "stale" in locals():
                    (directory / "STALE-Cargo.lock").write_bytes(stale)
                if "fixed" in locals():
                    (directory / "COHERENT-Cargo.lock").write_bytes(fixed)


class ConfigPathPatchTests(unittest.TestCase):
    """A selected path patch and an older transitive Git package may coexist."""

    def setUp(self) -> None:
        for memo in (preflight._TOML_CACHE, preflight._WS_MANIFESTS, preflight._GRAPH,
                     preflight._WS_ROOT, preflight._BUILD_CRITICAL):
            memo.clear()
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name).resolve()
        self.ws = self.root / "ws"
        self.write("ws/Cargo.toml", '''[package]
name = "consumer"
version = "0.1.0"
[workspace]
[dependencies]
renamed = { package = "solver", version = "0.27.0", git = "https://example.invalid/solver.git", rev = "new" }
''')
        self.write("solver/Cargo.toml", '[package]\nname = "solver"\nversion = "0.27.0"\n')
        self.write("ws/.cargo/config.toml", '''[patch."https://example.invalid/solver.git"]
alias = { package = "solver", path = "../solver" }
''')
        self.lock()

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def write(self, name: str, content: str) -> None:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        preflight._TOML_CACHE.clear()

    def lock(self, edge: str = "solver 0.27.0", local: str = "0.27.0") -> None:
        self.write("ws/Cargo.lock", f'''version = 4
[[package]]
name = "consumer"
version = "0.1.0"
dependencies = ["{edge}"]
[[package]]
name = "solver"
version = "{local}"
[[package]]
name = "solver"
version = "0.26.0"
source = "git+https://example.invalid/solver.git?rev=old#old"
''')

    def findings(self):
        report = preflight.Report(False)
        preflight.check_lockfiles_fast(self.root, [self.ws], report)
        return [finding for finding in report.findings if finding.severity != preflight.INFO]

    def test_selected_config_path_patch_does_not_accuse_transitive_git_pin(self):
        self.assertEqual(self.findings(), [])

    def test_unselected_local_package_does_not_hide_stale_git_edge(self):
        self.lock(edge="solver 0.26.0")
        self.assertEqual(len(self.findings()), 1)

    def test_ambiguous_or_explicit_git_edge_does_not_count_as_path(self):
        for edge in ["solver", "solver 0.26.0 (git+https://example.invalid/solver.git?rev=old#old)"]:
            self.lock(edge=edge)
            self.assertEqual(len(self.findings()), 1, edge)

    def test_same_version_git_and_path_packages_need_an_unambiguous_local_edge(self):
        self.lock(edge="solver 0.27.0 (git+https://example.invalid/solver.git?rev=old#old)")
        lock = self.ws / "Cargo.lock"
        self.write("ws/Cargo.lock", lock.read_text().replace('version = "0.26.0"', 'version = "0.27.0"'))
        self.assertEqual(len(self.findings()), 1)
        self.write("ws/Cargo.lock", lock.read_text().replace(
            'solver 0.27.0 (git+https://example.invalid/solver.git?rev=old#old)', 'solver 0.27.0'))
        self.assertEqual(len(self.findings()), 1)

    def test_declined_patch_version_does_not_hide_missing_manifest_pin(self):
        self.write("solver/Cargo.toml", '[package]\nname = "solver"\nversion = "0.28.0"\n')
        self.lock(edge="solver 0.28.0", local="0.28.0")
        self.assertEqual(len(self.findings()), 1)

    def test_stale_path_lock_missing_target_and_wrong_name_remain_findings(self):
        self.lock(local="0.27.1", edge="solver 0.27.1")
        self.assertEqual(len(self.findings()), 1)
        self.lock()
        self.write("solver/Cargo.toml", '[package]\nname = "impostor"\nversion = "0.27.0"\n')
        self.assertEqual(len(self.findings()), 1)
        (self.root / "solver/Cargo.toml").unlink()
        preflight._TOML_CACHE.clear()
        self.assertEqual(len(self.findings()), 1)

    def test_absent_config_and_legacy_config_precedence(self):
        self.write("ws/.cargo/config", '[patch."https://example.invalid/unrelated.git"]\n')
        self.assertEqual(len(self.findings()), 1)
        (self.ws / ".cargo/config").unlink()
        self.assertEqual(self.findings(), [])
        (self.ws / ".cargo/config.toml").unlink()
        preflight._TOML_CACHE.clear()
        self.assertEqual(len(self.findings()), 1)

    def test_unknown_requirement_syntax_retains_finding(self):
        path = self.ws / "Cargo.toml"
        self.write("ws/Cargo.toml", path.read_text().replace('version = "0.27.0"', 'version = "0.27.*"'))
        self.assertEqual(len(self.findings()), 1)


class DeepLockCacheTests(unittest.TestCase):
    """Cached-only replay follows resolver inputs; explicit deep earns a verdict."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.ws = self.root / "ws"
        self.targo = sys.executable
        self.environ = patch.dict(os.environ, {"CARGO_HOME": str(self.root / "home")})
        self.environ.start()
        self.addCleanup(self.environ.stop)
        self.write("ws/Cargo.toml", '[package]\nname = "a"\nversion = "0.1.0"\n[workspace]\n')
        self.write("ws/Cargo.lock", "version = 4\n")

    def write(self, name: str, content: str) -> Path:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path

    def key(self) -> str:
        # Each real invocation has fresh process-local parsing and graph memos.
        for memo in (preflight._TOML_CACHE, preflight._WS_MANIFESTS, preflight._GRAPH,
                     preflight._WS_ROOT, preflight._BUILD_CRITICAL):
            memo.clear()
        return preflight._deep_cache_key(self.ws, self.targo)

    def cached(self, verdict: str = "clean") -> None:
        key = self.key()
        self.assertTrue(key)
        preflight.save_deep_cache(self.root, {
            "ws": {"key": key, "verdict": verdict, "msg": "old lock failure"},
        })

    def check(self, *, cached_only: bool = False, result=(0, "", "")):
        report = preflight.Report(False)
        with patch.object(preflight, "run", return_value=result) as resolver, \
                patch.object(preflight, "lock_severity", return_value=(preflight.FAIL, "fixture")):
            preflight.check_lockfiles_deep(
                self.root, [self.ws], report, self.targo, 7, 1, cached_only=cached_only)
        return report, resolver

    def test_explicit_deep_reprobes_both_cached_verdicts(self) -> None:
        for verdict in ("clean", "skew"):
            with self.subTest(verdict=verdict):
                self.cached(verdict)
                report, resolver = self.check()
                resolver.assert_called_once()
                self.assertFalse(any(f.severity == preflight.FAIL for f in report.findings))
                self.assertEqual(preflight.load_deep_cache(self.root)["ws"]["verdict"], "clean")

    def test_cached_only_replays_without_running_the_resolver(self) -> None:
        for verdict in ("clean", "skew"):
            with self.subTest(verdict=verdict):
                self.cached(verdict)
                report, resolver = self.check(cached_only=True)
                resolver.assert_not_called()
                failures = [f for f in report.findings if f.severity == preflight.FAIL]
                self.assertEqual(len(failures), int(verdict == "skew"))

    def test_fresh_inconclusive_result_retires_cached_skew(self) -> None:
        self.cached("skew")
        report, resolver = self.check(result=(127, "", "network unavailable"))
        resolver.assert_called_once()
        self.assertNotIn("ws", preflight.load_deep_cache(self.root))
        self.assertFalse(any(f.severity == preflight.FAIL for f in report.findings))
        self.assertTrue(any("INCONCLUSIVE" in f.title for f in report.findings))

    def test_workspace_failure_reports_its_cause_without_a_network_diagnosis(self) -> None:
        self.cached("skew")
        error = ("error: current package believes it's in a workspace when it's not:\n"
                 f"current: {self.ws / 'Cargo.toml'}\n"
                 f"workspace: {self.root / 'Cargo.toml'}\n"
                 "add an empty `[workspace]` table to the package's manifest.")
        report, resolver = self.check(result=(101, "", error))
        resolver.assert_called_once()
        finding = next(f for f in report.findings if "INCONCLUSIVE" in f.title)
        self.assertNotIn("network", finding.title)
        self.assertNotIn("registry", finding.title)
        diagnostic = "\n".join(finding.detail)
        for line in error.splitlines():
            self.assertIn(line, diagnostic)
        self.assertIn("rc=101", diagnostic)
        self.assertEqual(finding.severity, preflight.WARN)
        self.assertNotIn("ws", preflight.load_deep_cache(self.root))

    def test_wrapped_metadata_failure_preserves_the_final_cause(self) -> None:
        # A compiler command can dwarf the actual cause in Targo's outer error.
        error = ("error: process didn't exit successfully: " + "argument " * 1000
                 + "\nCaused by:\n  the required compiler executable was not found")
        report, _ = self.check(result=(101, "", error))
        finding = next(f for f in report.findings if "INCONCLUSIVE" in f.title)
        diagnostic = "\n".join(finding.detail)
        self.assertIn("error: process didn't exit successfully:", diagnostic)
        self.assertIn("the required compiler executable was not found", diagnostic)
        self.assertLess(len(diagnostic), 5000)

    def test_multiple_failed_probes_count_workspaces_and_keep_each_cause(self) -> None:
        second = self.root / "other"
        self.write("other/Cargo.toml", '[package]\nname = "b"\nversion = "0.1.0"\n[workspace]\n')
        self.write("other/Cargo.lock", "version = 4\n")
        report = preflight.Report(False)
        with patch.object(preflight, "run", side_effect=[
            (101, "", "error: first wrapper\nCaused by:\n  first package failure"),
            (127, "", "error: second wrapper\nCaused by:\n  second package failure"),
        ]):
            preflight.check_lockfiles_deep(
                self.root, [self.ws, second], report, self.targo, 7, 1)
        finding = next(f for f in report.findings if "INCONCLUSIVE" in f.title)
        self.assertTrue(finding.title.startswith("2 workspace(s)"))
        diagnostic = "\n".join(finding.detail)
        for context in ("ws: rc=101", "other: rc=127", "first package failure", "second package failure"):
            self.assertIn(context, diagnostic)

    def test_fresh_locked_failure_remains_blocking_and_cacheable(self) -> None:
        self.cached()
        report, resolver = self.check(result=(101, "", "error: lock file is out of date"))
        resolver.assert_called_once()
        self.assertEqual(sum(f.severity == preflight.FAIL for f in report.findings), 1)
        self.assertEqual(preflight.load_deep_cache(self.root)["ws"]["verdict"], "skew")

    def test_probe_receives_isolated_target_directory_and_existing_environment(self) -> None:
        with patch.dict(os.environ, {"CARGO_TARGET_DIR": str(self.root / "real-target"),
                                     "PREFLIGHT_CONTROL": "preserved"}):
            _, resolver = self.check()
        command = resolver.call_args.args[0]
        self.assertEqual(command, [self.targo, "metadata", "--locked", "--format-version", "1",
                                   "--manifest-path", str(self.ws / "Cargo.toml")])
        self.assertEqual(resolver.call_args.kwargs["cwd"], self.ws)
        self.assertEqual(resolver.call_args.kwargs["timeout"], 7)
        env = resolver.call_args.kwargs["env"]
        self.assertEqual(env["PREFLIGHT_CONTROL"], "preserved")
        self.assertNotEqual(env["CARGO_TARGET_DIR"], str(self.root / "real-target"))

    def test_run_passes_environment_to_the_actual_child(self) -> None:
        rc, out, err = preflight.run(
            [sys.executable, "-c", "import os; print(os.environ['PREFLIGHT_CONTROL'])"],
            env={"PREFLIGHT_CONTROL": "isolated child"})
        self.assertEqual((rc, out.strip(), err), (0, "isolated child", ""))

    def test_virtual_root_and_manifest_bytes_change_the_key_without_mtime_changes(self) -> None:
        self.write("ws/Cargo.toml", '[workspace]\nmembers = ["member"]\nresolver = "2"\n')
        path = self.write("ws/member/Cargo.toml", '[package]\nname = "a"\nversion = "0.1.0"\n')
        before = self.key()
        stat = path.stat()
        path.write_text(path.read_text().replace("0.1.0", "0.2.0"))
        os.utime(path, ns=(stat.st_atime_ns, stat.st_mtime_ns))
        self.assertNotEqual(before, self.key())
        before = self.key()
        root = self.ws / "Cargo.toml"
        root.write_text(root.read_text().replace('resolver = "2"', 'resolver = "3"'))
        self.assertNotEqual(before, self.key())

    def test_workspace_ancestor_and_cargo_home_config_bytes_invalidate_replay(self) -> None:
        for name in ("ws/.cargo/config.toml", ".cargo/config", "home/config.toml"):
            with self.subTest(config=name):
                self.cached()
                path = self.write(name, "[net]\noffline = true\n")
                report, resolver = self.check(cached_only=True)
                resolver.assert_not_called()
                self.assertTrue(any("0 cached" in f.title for f in report.findings))
                before = self.key()
                stat = path.stat()
                path.write_text("[net]\noffline = false\n")
                os.utime(path, ns=(stat.st_atime_ns, stat.st_mtime_ns))
                self.assertNotEqual(before, self.key())

    def test_config_include_and_legacy_selection_follow_cargo(self) -> None:
        self.write("ws/.cargo/config.toml", 'include = ["included.toml"]\n')
        included = self.write("ws/.cargo/included.toml", "[net]\noffline = true\n")
        before = self.key()
        included.write_text("[net]\noffline = false\n")
        self.assertNotEqual(before, self.key())
        self.write("ws/.cargo/config", "[net]\noffline = true\n")
        before = self.key()
        included.write_text("[net]\noffline = true\n")
        self.assertEqual(before, self.key())

    def test_native_home_config_and_explicit_compatibility_precedence(self) -> None:
        native = self.write("native-home/config.toml", "[net]\nretry = 1\n")
        default = self.root / "default-user"
        cases = ((None, native),
                 ("", default / ".cargo/config.toml"),
                 (str(self.root / "compat-home"), self.root / "compat-home/config.toml"))
        for value, selected in cases:
            with self.subTest(cargo_home=value), \
                    patch.dict(os.environ, {"TARGO_HOME": str(native.parent)}), \
                    patch.object(preflight.Path, "home", return_value=default):
                if value is None:
                    os.environ.pop("CARGO_HOME", None)
                else:
                    os.environ["CARGO_HOME"] = value
                before = self.key()
                self.assertTrue(before)
                native.write_text(native.read_text() + "\n# changed native config\n")
                if value is None:
                    self.assertNotEqual(before, self.key())
                else:
                    self.assertEqual(before, self.key())
                before = self.key()
                selected.parent.mkdir(parents=True, exist_ok=True)
                selected.write_text(selected.read_text() + "\n# selected config changed\n"
                                    if selected.exists() else "[net]\nretry = 2\n")
                self.assertNotEqual(before, self.key())

    def test_native_home_keeps_older_seed_and_compatibility_default_home_in_the_key(self) -> None:
        native = self.write("native-home/config.toml", "[net]\nretry = 1\n")
        default_config = self.write("default-user/.cargo/config.toml", "[net]\nretry = 1\n")
        with patch.dict(os.environ, {"TARGO_HOME": str(native.parent)}), \
                patch.object(preflight.Path, "home", return_value=default_config.parent.parent):
            os.environ.pop("CARGO_HOME", None)
            self.cached()
            # Older native seeds and the Cargo identity still discover this
            # home. Their unchanged executable stat must not preserve a verdict
            # after an input the actual resolver reads has changed.
            default_config.write_text("[net]\nretry = 2\n")
            report, resolver = self.check(cached_only=True)
            resolver.assert_not_called()
            self.assertTrue(any("0 cached" in f.title for f in report.findings))
            before = self.key()
            native.write_text("[net]\nretry = 2\n")
            self.assertNotEqual(before, self.key(), "new native tools discover the native home")

    def test_manifest_and_config_patch_targets_include_their_local_dependencies(self) -> None:
        for owner in ("ws/Cargo.toml", "ws/.cargo/config.toml"):
            with self.subTest(owner=owner):
                path = self.root / owner
                original = path.read_text() if path.exists() else ""
                self.write(owner, original + '[patch.crates-io]\nb = { path = "../b" }\n')
                patch_target = self.write("b/Cargo.toml", '[package]\nname = "b"\nversion = "0.1.0"\n'
                                          '[dependencies]\nc = { path = "../c", optional = true }\n')
                target = self.write("c/Cargo.toml", '[package]\nname = "c"\nversion = "0.1.0"\n')
                before = self.key()
                self.assertTrue(before)
                patch_target.write_text(patch_target.read_text().replace("0.1.0", "0.2.0"))
                self.assertNotEqual(before, self.key())
                before = self.key()
                target.write_text(target.read_text().replace("0.1.0", "0.2.0"))
                self.assertNotEqual(before, self.key())
                self.write(owner, original)

    def test_inherited_patch_workspace_manifest_changes_the_key(self) -> None:
        path = self.ws / "Cargo.toml"
        path.write_text(path.read_text() + '[patch.crates-io]\nb = { path = "../ext/b" }\n')
        self.write("ext/b/Cargo.toml", '[package]\nname = "b"\nversion.workspace = true\n')
        owner = self.write("ext/Cargo.toml", '[workspace]\nmembers = ["b"]\n'
                           '[workspace.package]\nversion = "0.1.0"\n')
        before = self.key()
        self.assertTrue(before)
        owner.write_text(owner.read_text().replace("0.1.0", "0.2.0"))
        self.assertNotEqual(before, self.key())

    def test_symlinked_config_keeps_the_discovered_relative_path_anchor(self) -> None:
        self.write("shared/config.toml", '[patch.crates-io]\nb = { path = "../b" }\n')
        self.write("b/Cargo.toml", '[package]\nname = "b"\nversion = "0.1.0"\n')
        config = self.ws / ".cargo/config.toml"
        config.parent.mkdir()
        config.symlink_to(self.root / "shared/config.toml")
        self.assertTrue(self.key())  # resolving relative to shared/ would miss b

    def test_optional_include_appearance_and_malformed_inputs_disable_stale_replay(self) -> None:
        self.write("ws/.cargo/config.toml", 'include = [{ path = "extra.toml", optional = true }]\n')
        before = self.key()
        self.assertTrue(before)
        included = self.write("ws/.cargo/extra.toml", "[net]\noffline = true\n")
        self.assertNotEqual(before, self.key())
        included.write_text('include = ["config.toml"]\n')
        self.assertEqual(self.key(), "")
        for text in ("[patch]\ncrates-io = false\n", 'paths = "unknown-shape"\n',
                     'include = "unknown-shape"\n'):
            self.write("ws/.cargo/config.toml", text)
            self.assertEqual(self.key(), "")

    def test_missing_patch_target_or_exhausted_walk_never_mints_a_cache_key(self) -> None:
        path = self.ws / "Cargo.toml"
        path.write_text(path.read_text() + '[patch.crates-io]\nb = { path = "../missing" }\n')
        self.assertEqual(self.key(), "")
        self.write("missing/Cargo.toml", '[package]\nname = "b"\nversion = "0.1.0"\n')
        with patch.object(preflight, "GRAPH_CAP", 1):
            self.assertEqual(self.key(), "")


class ConcurrentBuildTests(unittest.TestCase):
    """`check_concurrent_build` must see a build of THIS checkout only.

    2026-09-24: the root was matched as a bare substring, so a stage-2 build in
    the sibling checkout `<home>/trust-land/toolchain-build` (its own
    build dir and lock) blocked every build of `<home>/trust`.
    """

    ROOT = Path("<home>/trust")

    def findings_for(self, ps_rows: list[str]):
        ps = "\n".join(ps_rows)
        rep = preflight.Report(color=False)
        with patch.object(preflight, "run", return_value=(0, ps, "")):
            preflight.check_concurrent_build(self.ROOT, rep, for_build=True)
        return [f for f in rep.findings if f.severity == preflight.FAIL]

    def test_a_sibling_checkout_sharing_a_path_prefix_is_not_this_build(self) -> None:
        rows = ["47898 1 <home>/trust-land/toolchain-build/build/bootstrap/debug/bootstrap build --stage 2"]
        self.assertEqual(self.findings_for(rows), [])

    def test_a_build_of_this_checkout_is_reported(self) -> None:
        rows = ["47898 1 build/bootstrap/debug/bootstrap build --stage 1"]
        self.assertEqual(len(self.findings_for(rows)), 1)


if __name__ == "__main__":
    unittest.main()
