#!/usr/bin/env python3
"""Focused controls for bootstrap-effective tool preflight configuration."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


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


if __name__ == "__main__":
    unittest.main()
