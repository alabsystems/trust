#!/usr/bin/env python3
"""Regression controls for developer-product selection and recorded test execution.

The fast diagnostic profile retains the scoped library lane and seal controls.
Ordinary pushes use the smaller live verifier/input-integrity profile; source
owners run focused compilation and behavioral tests before committing.

These fixtures verify package selection, feature-specific targets, conservative
scope, recorded binary execution, interruption, budgets and failure grading
without compiling the compiler or treating missing tests as a pass.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import signal
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "check_crates_tests_scoped.py"
HARNESS = REPO_ROOT / "tests" / "run_trust_comprehensive_harness.sh"
sys.path.insert(0, str(REPO_ROOT / "scripts/lib"))
from test_python import fixture_shebang
SEAL_TEST = "scripts/tests/seal_driver_sysrootcheck_test.sh"


def load_lane():
    spec = importlib.util.spec_from_file_location("check_crates_tests_scoped", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def profile_rows(profile="fast"):
    out = subprocess.run(
        ["bash", str(HARNESS), "--list", profile],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True,
    ).stdout
    rows = []
    for line in out.splitlines():
        parts = line.split("\t")
        if len(parts) >= 5:
            rows.append({"id": parts[0], "required": parts[2], "command": parts[4]})
    return rows


class HarnessProfileTest(unittest.TestCase):
    def test_fast_profile_keeps_the_scoped_crates_tests_lane(self):
        rows = [r for r in profile_rows() if "scripts/check_crates_tests_scoped.py" in r["command"]]
        self.assertTrue(rows, "no fast row runs scripts/check_crates_tests_scoped.py (TRUST-16)")
        for row in rows:
            self.assertEqual(row["required"], "true", row)
            self.assertIn("--push-context", row["command"], row)
            # scoped.* rows run LAST in the hook, after the sub-second lanes.
            self.assertTrue(row["id"].startswith("scoped."), row)

    def test_fast_profile_keeps_the_seal_self_test(self):
        rows = [
            r for r in profile_rows()
            if re.search(re.escape(SEAL_TEST) + r"(?![\w./-])", r["command"])
        ]
        self.assertTrue(rows, f"no fast row runs {SEAL_TEST} (TRUST-17)")
        self.assertTrue(all(r["required"] == "true" for r in rows), rows)


class PlanTest(unittest.TestCase):
    def setUp(self):
        self.lane = load_lane()
        self.members = {
            "crates/trust-router": "trust-router",
            "crates/trust-types": "trust-types",
            "crates/trust-clean": "trust-clean",
        }

    def test_also_members_add_to_the_touched_ones_and_never_remove(self):
        # scripts/land_gate.py passes the members a change REACHES (2026-10-14).
        plan = self.lane.plan_for(["crates/trust-types/src/lib.rs"], self.members, ["crates/own"],
                                  also_dirs=["crates/trust-router", "crates/own", "crates/nope"])
        self.assertEqual(plan.packages, ["trust-router", "trust-types"])
        self.assertEqual(plan.own_workspaces, ["crates/own"])
        self.assertIn("crates/nope", plan.unattributed)
        # The touched member's feature runs are still planned, and the added one's too.
        self.assertTrue(any(pkg == "trust-router" for pkg, _tail in plan.feature_runs))
        self.assertTrue(any(pkg == "trust-types" for pkg, _tail in plan.feature_runs))

    def test_a_crate_built_only_for_another_os_is_named_not_run_here(self):
        # crates/trust-worker-linux's library is `#![cfg(target_os = "linux")]`: on
        # macOS its tests cannot compile, so the run could only fail (the landing
        # gate's run, 2026-10-15: "could not compile `trust-worker-linux` (test
        # \"launcher\")"). It is taken out and named; on Linux it stays.
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "crates/linux-only/src").mkdir(parents=True)
            (root / "crates/linux-only/src/lib.rs").write_text('#![cfg(target_os = "linux")]\npub fn f() {}\n')
            (root / "crates/everywhere/src").mkdir(parents=True)
            (root / "crates/everywhere/src/lib.rs").write_text("pub fn g() {}\n")
            members = {"crates/everywhere": "everywhere"}
            plan = self.lane.plan_for([], members, ["crates/linux-only"],
                                      also_dirs=["crates/linux-only", "crates/everywhere"])
            self.lane.apply_host_limits(plan, root, members, host_os="macos")
            self.assertEqual(plan.own_workspaces, [])
            self.assertEqual(plan.packages, ["everywhere"])
            self.assertEqual([d for d, _ in plan.host_limited], ["crates/linux-only"])
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.lane.print_plan(plan)
            self.assertIn("crates/linux-only: NOT RUN on this host", out.getvalue())
            plan = self.lane.plan_for([], members, ["crates/linux-only"], also_dirs=["crates/linux-only"])
            self.lane.apply_host_limits(plan, root, members, host_os="linux")
            self.assertEqual(plan.own_workspaces, ["crates/linux-only"])
            self.assertEqual(plan.host_limited, [])

    def test_native_default_inventory_excludes_compiler_members(self):
        metadata = {
            "workspace_members": ["library", "compiler"],
            "workspace_default_members": ["library"],
            "packages": [
                {"id": "library", "name": "trust-types", "manifest_path": str(REPO_ROOT / "crates/trust-types/Cargo.toml")},
                {"id": "compiler", "name": "trust-witness", "manifest_path": str(REPO_ROOT / "crates/trust-witness/Cargo.toml")},
            ],
        }
        self.assertEqual(self.lane.workspace_members(metadata), {"crates/trust-types": "trust-types"})
        for defaults in (None, [], ["outside"]):
            with self.subTest(defaults=defaults), self.assertRaises(RuntimeError):
                self.lane.workspace_members(dict(metadata, workspace_default_members=defaults))

    def test_a_member_whose_name_another_package_carries_is_named_by_its_id(self):
        # crates/trust-sha2-compat is `sha2`; `-p sha2` was refused as ambiguous and
        # the whole run recorded 0 test binaries (the landing gate, 2026-10-14).
        meta = {"workspace_members": ["path+file:///r/crates/trust-sha2-compat#sha2@0.10.100",
                                      "path+file:///r/crates/trust-types#0.1.0"],
                "packages": [{"id": "path+file:///r/crates/trust-sha2-compat#sha2@0.10.100", "name": "sha2"},
                             {"id": "path+file:///r/crates/trust-types#0.1.0", "name": "trust-types"}]}
        lock = ('[[package]]\nname = "sha2"\nversion = "0.10.9"\n\n[[package]]\nname = "sha2"\n'
                'version = "0.10.100"\n\n[[package]]\nname = "trust-types"\nversion = "0.1.0"\n')
        meta["workspace_default_members"] = list(meta["workspace_members"])
        specs = self.lane.package_specs(meta, lock)
        self.assertEqual(specs, {"sha2": "path+file:///r/crates/trust-sha2-compat#sha2@0.10.100"})
        plan = self.lane.plan_for([], {"crates/trust-sha2-compat": "sha2", **self.members}, [],
                                  also_dirs=["crates/trust-sha2-compat", "crates/trust-types"])
        plan.specs = specs
        main = [c for c in plan.commands() if "--tests" in c][0]
        self.assertIn("path+file:///r/crates/trust-sha2-compat#sha2@0.10.100", main)
        self.assertIn("trust-types", main)
        self.assertNotIn("sha2", main[main.index("-p") + 1:main.index("-p") + 2])

    def test_router_change_plans_the_ay_backend_lib_run(self):
        plan = self.lane.plan_for(["crates/trust-router/src/lib.rs"], self.members, [])
        commands = [" ".join(c) for c in plan.commands()]
        self.assertIn(
            "targo --unverified test -Zfeature-unification --config resolver.feature-unification=\"selected\" --manifest-path Cargo.toml --locked --no-fail-fast "
            "-p trust-router --tests",
            commands,
        )
        self.assertIn(
            "targo --unverified test -Zfeature-unification --config resolver.feature-unification=\"selected\" --manifest-path Cargo.toml --locked --no-fail-fast "
            "-p trust-router --features ay-backend --lib",
            commands,
        )
        # One command per tail in the live table, after the default run.
        self.assertEqual(
            commands[1:],
            ["targo --unverified test -Zfeature-unification --config resolver.feature-unification=\"selected\" --manifest-path Cargo.toml --locked --no-fail-fast "
             "-p trust-router " + " ".join(tail) for tail in self.lane.FEATURE_RUNS["trust-router"]],
        )

    def test_router_setter_target_is_selected_for_direct_and_reached_members(self):
        expected = [
            "targo", "--unverified", "test", "-Zfeature-unification", "--config",
            'resolver.feature-unification="selected"', "--manifest-path", "Cargo.toml",
            "--locked", "--no-fail-fast", "-p", "trust-router", "--features", "ay-backend",
            "--test", "setter_assert_refute_lane", "--target-dir",
            "crates/target-scoped-feature-tests.noindex/trust-router-ay-backend",
        ]
        cases = [
            (["crates/trust-router/src/lib.rs"], []),
            (["crates/trust-router/tests/setter_assert_refute_lane.rs"], []),
            (["docs/changed.md"], ["crates/trust-router"]),
        ]
        for paths, also in cases:
            with self.subTest(paths=paths, also=also):
                plan = self.lane.plan_for(paths, self.members, [], also_dirs=also)
                self.assertEqual(plan.commands().count(expected), 1)
                recorded = self.lane.with_runner_config(expected, "RECORD_DIR")
                self.assertEqual(recorded[:-2], expected)
                self.assertEqual(recorded[-2], "--config")
                self.assertIn("RECORD_DIR", recorded[-1])
                self.assertIn((expected, self.lane.MEMBERS), plan.attributed_commands())

        unrelated = self.lane.plan_for(["crates/trust-clean/src/lib.rs"], self.members, [])
        self.assertNotIn(expected, unrelated.commands())

    def test_touched_members_share_one_default_run(self):
        # feature_runs={}: the subject is the default-feature command, whatever
        # FEATURE_RUNS holds for these members (the next test reads the table).
        # No instruments: a trust-types change also moves the missing-obligation
        # ratchet's subject (see the instrument tests), and its Cargo.toml the
        # TOML corpus gates' (see the corpus tests), neither of which is this test's.
        plan = self.lane.plan_for(
            ["crates/trust-types/src/a.rs", "crates/trust-clean/tests/b.rs", "crates/trust-types/Cargo.toml"],
            self.members, [], feature_runs={}, instruments=(), corpus_instruments=(),
        )
        self.assertEqual(plan.packages, ["trust-clean", "trust-types"])
        self.assertEqual(plan.feature_runs, [])
        self.assertEqual(
            [" ".join(c) for c in plan.commands()],
            ["targo --unverified test -Zfeature-unification --config resolver.feature-unification=\"selected\" --manifest-path Cargo.toml --locked --no-fail-fast "
             "-p trust-clean -p trust-types --tests"],
        )

    def test_each_touched_members_tails_follow_the_one_default_run(self):
        # No instruments, as above: their order is the instrument tests' subject.
        plan = self.lane.plan_for(
            ["crates/trust-types/src/a.rs", "crates/trust-clean/tests/b.rs"], self.members, [],
            instruments=(),
        )
        tails = [(pkg, tail) for pkg in ("trust-clean", "trust-types")
                 for tail in self.lane.FEATURE_RUNS.get(pkg, [])]
        self.assertEqual(plan.feature_runs, tails)
        commands = plan.commands()
        self.assertEqual(len(commands), 1 + len(tails))
        self.assertEqual(commands[0][-5:], ["-p", "trust-clean", "-p", "trust-types", "--tests"])
        for command, (pkg, tail) in zip(commands[1:], tails):
            self.assertEqual(command[-(2 + len(tail)):], ["-p", pkg, *tail])

    def test_out_of_scope_paths_are_disclosed_not_tested(self):
        plan = self.lane.plan_for(
            [
                "docs/VALIDATION_LADDER.md",
                "Cargo.lock",
                "crates/trust-thir-lower/src/lib.rs",
                "first-party/ay",
                "crates/README.md",
            ],
            self.members, [],
        )
        self.assertTrue(plan.empty())
        self.assertEqual(plan.workspace_files, ["Cargo.lock"])
        self.assertEqual([name for name, _ in plan.excluded], ["trust-thir-lower"])
        self.assertEqual(plan.first_party, ["first-party/ay"])
        self.assertEqual(plan.unattributed, ["crates/README.md"])

    def test_own_workspace_crate_runs_against_its_own_manifest(self):
        plan = self.lane.plan_for(
            ["crates/trust-spec-temporal/src/lib.rs"], self.members, ["crates/trust-spec-temporal"]
        )
        self.assertEqual(
            [" ".join(c) for c in plan.commands()],
            ["targo --unverified test -Zfeature-unification --config resolver.feature-unification=\"selected\" --manifest-path crates/trust-spec-temporal/Cargo.toml "
             "--locked --no-fail-fast --tests"],
        )

    def test_own_workspace_roots_finds_trust_spec_temporal(self):
        self.assertIn("crates/trust-spec-temporal", self.lane.own_workspace_roots(REPO_ROOT))

    def test_feature_runs_name_real_features(self):
        for pkg, tails in self.lane.FEATURE_RUNS.items():
            manifest = (REPO_ROOT / "crates" / pkg / "Cargo.toml").read_text(encoding="utf-8")
            section = manifest.split("\n[features]\n", 1)
            self.assertEqual(len(section), 2, f"{pkg} has no [features] table")
            features = section[1].split("\n[", 1)[0]
            for tail in tails:
                for i, arg in enumerate(tail):
                    if arg == "--features":
                        for feature in tail[i + 1].split(","):
                            self.assertRegex(
                                features, rf"(?m)^{re.escape(feature)}\s*=",
                                f"FEATURE_RUNS names {pkg}/{feature}, which its Cargo.toml no longer defines",
                            )


    def test_feature_runs_build_only_the_lib_or_isolate_the_integration_target(self):
        # Every record pass builds before any binary runs, so a feature tail
        # that built bins would replace target/debug/<bin> under the default
        # run's integration tests, which exec it by CARGO_BIN_EXE_<bin>.
        builds_more = {"--tests", "--test", "--bins", "--bin", "--all-targets",
                       "--benches", "--bench", "--examples", "--example", "--doc"}
        for pkg, tails in self.lane.FEATURE_RUNS.items():
            for tail in tails:
                if "--lib" in tail:
                    self.assertFalse(builds_more & set(tail), (pkg, tail))
                    continue
                self.assertEqual(pkg, "trust-router")
                self.assertEqual(tail, [
                    "--features", "ay-backend", "--test", "setter_assert_refute_lane",
                    "--target-dir",
                    "crates/target-scoped-feature-tests.noindex/trust-router-ay-backend",
                ])
                source = (REPO_ROOT / "crates" / pkg / "tests" / (tail[3] + ".rs")).read_text()
                self.assertIn('#![cfg(feature = "ay-backend")]', source)
                self.assertIn("#[test]", source)

    def test_targo_trust_is_built_iff_a_consumer_is_touched(self):
        members = dict(self.members, **{"crates/trust-integration-tests": "trust-integration-tests"})
        for paths, want in (
            (["crates/trust-integration-tests/tests/binary_to_trust_ir_e2e.rs"], True),
            (["crates/trust-integration-tests/src/lib.rs", "crates/trust-router/src/lib.rs"], True),
            (["crates/trust-router/src/lib.rs", "crates/trust-types/src/a.rs"], False),
            (["targo-trust/src/main.rs", "docs/notes.md"], False),
        ):
            with self.subTest(paths=paths):
                plan = self.lane.plan_for(paths, members, [])
                self.assertEqual(plan.needs_targo_trust(), want)
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    self.lane.print_plan(plan)
                self.assertEqual("prebuild: targo-trust" in out.getvalue(), want, out.getvalue())

    def test_binary_fixture_only_changes_run_the_consumer_and_prebuild(self):
        tail = ["--test", "binary_to_trust_ir_e2e"]
        for path in (
            "tests/fixtures/binary_decomp/x86_64-load-elf.hex",
            "tests/fixtures/binary_decomp/regenerate_exec_entry_elf.sh",
        ):
            with self.subTest(path=path):
                plan = self.lane.plan_for([path], self.members, [])
                self.assertEqual(plan.packages, [])
                self.assertEqual(plan.instrument_runs, [("trust-integration-tests", tail)])
                self.assertFalse(plan.empty())
                self.assertTrue(plan.needs_targo_trust())
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    self.lane.print_plan(plan)
                self.assertIn("prebuild: targo-trust, whose copy the tests of trust-integration-tests", out.getvalue())
                self.assertIn("-p trust-integration-tests --test binary_to_trust_ir_e2e", " ".join(plan.commands()[0]))

    def test_binary_fixture_host_touch_uses_the_default_run_once(self):
        members = dict(self.members, **{"crates/trust-integration-tests": "trust-integration-tests"})
        plan = self.lane.plan_for([
            "tests/fixtures/binary_decomp/x86_64-load-elf.hex",
            "crates/trust-integration-tests/tests/binary_to_trust_ir_e2e.rs",
        ], members, [])
        self.assertEqual(plan.packages, ["trust-integration-tests"])
        self.assertEqual(plan.instrument_runs, [])
        self.assertEqual(len(plan.commands()), 1)
        self.assertTrue(plan.needs_targo_trust())

    def test_binary_fixture_instrument_survives_also_members(self):
        members = dict(self.members, **{"crates/trust-integration-tests": "trust-integration-tests"})
        plan = self.lane.plan_for(["tests/fixtures/binary_decomp/x86_64-load-elf.hex"],
                                  members, [], also_dirs=["crates/trust-integration-tests"])
        self.assertIn(("trust-integration-tests", ["--test", "binary_to_trust_ir_e2e"]), plan.instrument_runs)
        self.assertTrue(plan.needs_targo_trust())

    def test_library_only_instrument_does_not_prebuild_the_cli(self):
        plan = self.lane.plan_for(["proofs/codegen-equivalence/g16_multiplier_equivalence.lean"],
                                  self.members, [])
        self.assertTrue(plan.instrument_runs)
        self.assertFalse(plan.needs_targo_trust())
        unrelated = self.lane.plan_for(["docs/binary_decomp/x86_64-load-elf.hex"], self.members, [])
        self.assertTrue(unrelated.empty())

    def test_the_targo_trust_path_is_the_bin_artifacts_executable(self):
        def artifact(name, kind, exe):
            return json.dumps({"reason": "compiler-artifact", "target": {"name": name, "kind": kind},
                               "executable": exe}) + "\n"
        messages = [
            "   Compiling targo-trust v0.10.0\n", "[1, 2]\n", "{\"reason\": \"build-script-executed\"}\n",
            artifact("targo-trust", ["lib"], None),
            artifact("other", ["bin"], "/t/debug/other"),
            artifact("targo-trust", ["bin"], "/t/first/targo-trust"),
            artifact("targo-trust", ["bin"], "/t/elsewhere/targo-trust"),
            # Not a bin, though it names an executable: a check of the name alone
            # would take it.
            artifact("targo-trust", ["lib"], "/t/debug/libtargo_trust.so"),
            json.dumps({"reason": "build-finished", "success": True}) + "\n",
        ]
        # The last bin message is cargo's final word on the file.
        self.assertEqual(self.lane.targo_trust_executable(messages), "/t/elsewhere/targo-trust")
        self.assertIsNone(self.lane.targo_trust_executable(messages[:5]))

    def test_every_crates_reader_of_targo_trust_bin_is_a_declared_consumer(self):
        # A member whose tests read the variable but is not declared would get
        # no build, and its tests would fail on every push that touches it.
        def grep(pattern):
            return subprocess.run(["git", "grep", "-l", "-e", pattern, "--", "crates/"], cwd=REPO_ROOT,
                                  capture_output=True, text=True, check=False).stdout.split()
        readers = grep(self.lane.TARGO_TRUST_VAR)
        self.assertEqual({path.split("/")[1] for path in readers}, set(self.lane.TARGO_TRUST_CONSUMERS),
                         readers)
        # And the search the variable replaced is gone, not merely unused.
        self.assertEqual(grep("find_targo_trust_binary"), [])

    def test_a_vcgen_only_change_runs_the_missing_obligation_ratchet(self):
        # 2026-09-30: `1f3b181649` changed trust-vcgen alone and left the
        # ratchet (a trust-ir-bridge test whose subject is trust-vcgen's output)
        # red on main, because the push planned only `-p trust-vcgen`.
        members = dict(self.members, **{"crates/trust-vcgen": "trust-vcgen",
                                        "crates/trust-ir-bridge": "trust-ir-bridge"})
        plan = self.lane.plan_for(["crates/trust-vcgen/src/generate/numeric_panic.rs"], members, [])
        self.assertIn(
            "targo --unverified test -Zfeature-unification --config resolver.feature-unification=\"selected\" --manifest-path Cargo.toml --locked --no-fail-fast "
            "-p trust-ir-bridge --lib -- flip::missing_obligation_ratchet::",
            [" ".join(c) for c in plan.commands()],
        )
        # A fixture-only change moves the ratchet's corpus, and, being a JSON
        # document, trust-json's (test_a_json_document_anywhere_runs_the_json_corpus_gate).
        plan = self.lane.plan_for(["crates/trust-clean/fixtures/x/dump.json"], members, [])
        self.assertEqual(plan.instrument_runs, [
            ("trust-ir-bridge", ["--lib", "--", "flip::missing_obligation_ratchet::"]),
            ("trust-json", ["--test", "acceptance_gate"]),
        ])

    def test_a_touched_host_is_not_run_twice(self):
        members = dict(self.members, **{"crates/trust-vcgen": "trust-vcgen",
                                        "crates/trust-ir-bridge": "trust-ir-bridge"})
        plan = self.lane.plan_for(
            ["crates/trust-vcgen/src/lib.rs", "crates/trust-ir-bridge/src/flip.rs"], members, []
        )
        self.assertEqual(plan.instrument_runs, [])
        self.assertIn("trust-ir-bridge", plan.packages)

    def test_a_host_only_also_members_adds_keeps_its_instrument_run(self):
        # LAND-GATE-HOOKLESS-1 round 2 (D3, 2026-11-02): the hookless land gate
        # hands the lane the landing range AND the reached members. A reached
        # host the range does not touch keeps its instrument run, so the
        # instrument rules (instrument_problem) still judge it; a member run
        # alone is judged by the zero-test rule, which an #[ignore]d required
        # test passes.
        members = dict(self.members, **{"crates/trust-vcgen": "trust-vcgen",
                                        "crates/trust-ir-bridge": "trust-ir-bridge"})
        ratchet = ("trust-ir-bridge", ["--lib", "--", "flip::missing_obligation_ratchet::"])
        plan = self.lane.plan_for(["crates/trust-vcgen/src/lib.rs"], members, [],
                                  also_dirs=["crates/trust-ir-bridge"])
        self.assertIn("trust-ir-bridge", plan.packages)
        self.assertIn(ratchet, plan.instrument_runs)
        # A host the range touches is still left to its default run.
        plan = self.lane.plan_for(["crates/trust-vcgen/src/lib.rs", "crates/trust-ir-bridge/src/flip.rs"], members,
                                  [], also_dirs=["crates/trust-ir-bridge"])
        self.assertNotIn(ratchet, plan.instrument_runs)

    def test_the_record_pass_hands_cargo_the_runner_before_the_filter(self):
        # The instrument's tail ends in `-- <filter>`: a `--config` after the
        # `--` reaches the test binary, cargo runs nothing through RECORDER, and
        # the lane CANNOT JUDGE (measured on 59ed95327d, exit 2, for a
        # trust-types-only push).
        members = dict(self.members, **{"crates/trust-vcgen": "trust-vcgen",
                                        "crates/trust-ir-bridge": "trust-ir-bridge"})
        plan = self.lane.plan_for(["crates/trust-types/src/lib.rs"], members, [], feature_runs={})
        instrument = [c for c in plan.commands() if "--" in c]
        self.assertEqual(len(instrument), 1, plan.commands())
        recorded = self.lane.with_runner_config(instrument[0], "RECORD_DIR")
        at = recorded.index("--")
        self.assertEqual(recorded[at - 2], "--config", recorded)
        self.assertIn("RECORD_DIR", recorded[at - 1])
        self.assertEqual(recorded[at:], ["--", "flip::missing_obligation_ratchet::"])
        # A command with no `--` keeps the runner at its end.
        plain = [c for c in plan.commands() if "--" not in c][0]
        self.assertEqual(self.lane.with_runner_config(plain, "R")[:-2], plain)

    def test_every_planned_command_gets_the_runner_among_cargos_arguments(self):
        # Every live tail (FEATURE_RUNS and CROSS_CRATE_INSTRUMENTS) planned at
        # once: in each recorded command `--config` precedes any `--`, and what
        # follows the `--` is the command's own, untouched.
        members = dict(self.members)
        members.update({f"crates/{pkg}": pkg for pkg in self.lane.FEATURE_RUNS})
        paths = [f"crates/{pkg}/src/lib.rs" for pkg in self.lane.FEATURE_RUNS]
        hosts = {host for _, host, _ in self.lane.CROSS_CRATE_INSTRUMENTS}
        hosts |= {host for _, _, host, _ in self.lane.CORPUS_INSTRUMENTS}
        paths += [prefixes[0] + "x" for prefixes, _, _ in self.lane.CROSS_CRATE_INSTRUMENTS]
        paths += [f"docs/x{suffix}" for suffix, _, _, _ in self.lane.CORPUS_INSTRUMENTS]
        paths = [p for p in paths if not any(p.startswith(f"crates/{h}/") for h in hosts)]
        plan = self.lane.plan_for(paths, {d: n for d, n in members.items() if n not in hosts}, [])
        commands = plan.commands()
        self.assertTrue(any("--" in c for c in commands), commands)  # the filtered shape is planned
        for cmd in commands:
            recorded = self.lane.with_runner_config(cmd, "RECORD_DIR")
            # The runner's `--config` is the last one: the member feature scope's comes first.
            at = max(i for i, word in enumerate(recorded) if word == "--config")
            end = cmd.index("--") if "--" in cmd else len(cmd)
            self.assertEqual(at, end, recorded)  # cargo's last own argument, before any `--`
            self.assertEqual(recorded[:at] + recorded[at + 2:], cmd, recorded)

    def test_every_targo_build_and_test_names_the_member_feature_scope_after_its_verb(self):
        # TARGO-MEMBER-FEATURE-SCOPE-1. aterm's atpkg `targo` shim (aterm a1679bf032,
        # 2026-11-06) puts `--config resolver.feature-unification="workspace"` before
        # the verb of an `--unverified` test or dev build, and `-Zfeature-unification`
        # after it, unless the call names that flag. Over the root workspace,
        # `-p trust-vcgen --tests` then took the compiler's features (38 compiler
        # units) and failed in rustc_macros' build script. Every Targo build and
        # test this lane runs (the default run, each feature tail, each instrument,
        # each own-workspace crate, the targo-trust prebuild, and each as recorded)
        # names the scope right after its verb, and no later word of cargo's own
        # names another unification.
        members = dict(self.members)
        members.update({f"crates/{pkg}": pkg for pkg in self.lane.FEATURE_RUNS})
        paths = [f"crates/{pkg}/src/lib.rs" for pkg in self.lane.FEATURE_RUNS]
        hosts = {host for _, host, _ in self.lane.CROSS_CRATE_INSTRUMENTS}
        hosts |= {host for _, _, host, _ in self.lane.CORPUS_INSTRUMENTS}
        paths += [prefixes[0] + "x" for prefixes, _, _ in self.lane.CROSS_CRATE_INSTRUMENTS]
        paths += ["crates/trust-spec-temporal/src/lib.rs"]
        paths = [p for p in paths if not any(p.startswith(f"crates/{h}/") for h in hosts)]
        plan = self.lane.plan_for(paths, {d: n for d, n in members.items() if n not in hosts},
                                  ["crates/trust-spec-temporal"])
        self.assertTrue(plan.packages and plan.feature_runs and plan.instrument_runs
                        and plan.own_workspaces, plan.commands())
        self.assertEqual(self.lane.MEMBER_FEATURE_SCOPE,
                         ["-Zfeature-unification", "--config", 'resolver.feature-unification="selected"'])
        commands = plan.commands() + [self.lane.TARGO_TRUST_BUILD]
        for cmd in commands + [self.lane.with_runner_config(c, "RECORD_DIR") for c in commands]:
            with self.subTest(cmd=" ".join(cmd)):
                own = cmd[:cmd.index("--")] if "--" in cmd else cmd
                self.assertEqual(own[:2], ["targo", "--unverified"])
                self.assertIn(own[2], ("test", "build"))
                self.assertEqual(own[3:6], self.lane.MEMBER_FEATURE_SCOPE)
                self.assertEqual([w for w in own if w.startswith("-Z")].count("-Zfeature-unification"), 1)
                unifications = [own[i + 1] for i, w in enumerate(own[:-1])
                                if w == "--config" and own[i + 1].startswith("resolver.")]
                self.assertEqual(unifications, ['resolver.feature-unification="selected"'])

    def test_an_unrelated_change_runs_no_instrument(self):
        plan = self.lane.plan_for(["crates/trust-router/src/lib.rs"], self.members, [])
        self.assertEqual(plan.instrument_runs, [])

    def test_cross_crate_instruments_select_real_tests(self):
        # Every instrument must select real tests, whether an inline lib module
        # or a whole integration target. Its declared input directories exist.
        for prefixes, host, tail in self.lane.CROSS_CRATE_INSTRUMENTS:
            if (prefixes, host, tail) in self.lane.TARGO_TRUST_INSTRUMENTS:
                self.assertIn(host, self.lane.TARGO_TRUST_CONSUMERS)
                self.assertEqual(len(tail), 2, (host, tail))
                self.assertEqual(tail[0], "--test", (host, tail))
                source = (REPO_ROOT / "crates" / host / "tests" / f"{tail[1]}.rs").read_text(encoding="utf-8")
                self.assertIn("#[test]", source, (host, tail))
            else:
                self.assertIn("--lib", tail, (host, tail))
                self.assertEqual(tail[-2], "--", (host, tail))
                path = tail[-1].rstrip(":").split("::")
                self.assertEqual(len(path), 2, f"{host}: {tail[-1]} is not <file>::<module>::")
                source = (REPO_ROOT / "crates" / host / "src" / f"{path[0]}.rs").read_text(encoding="utf-8")
                start = source.find(f"mod {path[1]} {{")
                self.assertGreaterEqual(start, 0, f"{host}: no `mod {path[1]}` in src/{path[0]}.rs")
                self.assertIn("#[test]", source[start:], f"{host}: `{tail[-1]}` selects no #[test]")
            for prefix in prefixes:
                self.assertTrue((REPO_ROOT / prefix).is_dir(), f"{host}: subject {prefix} does not exist")

    def test_a_trust_lean_change_runs_the_prelude_source_digest(self):
        # 2026-10-09 (Beyond-TLA B1a, B1A-D35): trust-model-prelude's PRELUDE_DIGEST
        # covers the Trust/*.lean files that trust-spec-temporal owns, so a push
        # editing one of them alone must run the digest check, and the check it
        # selects must be the source-digest test itself, not only the ignored
        # re-bless printer (an #[ignore] test satisfies a bare `#[test]` search).
        hosted = [(prefixes, tail) for prefixes, host, tail in self.lane.CROSS_CRATE_INSTRUMENTS
                  if host == "trust-model-prelude"]
        self.assertEqual(hosted, [(("crates/trust-spec-temporal/clean/Trust/",),
                                   ["--lib", "--", "tests::digest::"])])
        members = dict(self.members, **{"crates/trust-model-prelude": "trust-model-prelude"})
        own = ["crates/trust-spec-temporal"]
        for lean in ("Temporal.lean", "FiniteModel.lean", "Model/Value.lean"):
            plan = self.lane.plan_for([f"crates/trust-spec-temporal/clean/Trust/{lean}"], members, own)
            self.assertEqual(plan.instrument_runs,
                             [("trust-model-prelude", ["--lib", "--", "tests::digest::"])], lean)
            self.assertEqual(plan.own_workspaces, own, lean)
            self.assertIn(
                "targo --unverified test -Zfeature-unification --config resolver.feature-unification=\"selected\" --manifest-path Cargo.toml --locked --no-fail-fast "
                "-p trust-model-prelude --lib -- tests::digest::",
                [" ".join(c) for c in plan.commands()],
            )
        # A trust-spec-temporal Rust change does not move the digest's subject.
        plan = self.lane.plan_for(["crates/trust-spec-temporal/src/lib.rs"], members, own)
        self.assertEqual(plan.instrument_runs, [])
        source = (REPO_ROOT / "crates/trust-model-prelude/src/tests.rs").read_text(encoding="utf-8")
        module = source[source.find("mod digest {"):]
        at = module.find("fn source_digest_matches()")
        self.assertGreaterEqual(at, 0, "tests::digest::source_digest_matches is gone")
        attrs = module[:at].rsplit("}", 1)[-1]
        self.assertIn("#[test]", attrs)
        # Any `ignore`, not only a literal `#[ignore`: `#[cfg_attr(debug_assertions,
        # ignore)]` (the release-only form, B1A-D42) would skip it on the debug push
        # lane just as silently.
        self.assertNotIn("ignore", attrs, "source_digest_matches must run by default")

    # -- CORPUS_INSTRUMENTS (2026-10-08) -------------------------------------
    # trust-json's acceptance gate and trust-toml's corpus differentials pin every
    # checked-in `*.json` / `*.toml` outside first-party/ and vendor/. A push
    # adding one to trust-vcgen's fixtures or to reports/ planned neither, and
    # trust-json's membership test was red on main on 563 such documents.

    def test_a_json_document_anywhere_runs_the_json_corpus_gate(self):
        for path in ("crates/trust-vcgen/tests/fixtures/new_mir.json",
                     "reports/source-integrations/r.json", "x.json"):
            with self.subTest(path=path):
                plan = self.lane.plan_for([path], self.members, [], instruments=())
                self.assertEqual(plan.instrument_runs, [("trust-json", ["--test", "acceptance_gate"])])
                self.assertIn(
                    "targo --unverified test -Zfeature-unification --config resolver.feature-unification=\"selected\" --manifest-path Cargo.toml --locked --no-fail-fast "
                    "-p trust-json --test acceptance_gate",
                    [" ".join(c) for c in plan.commands()],
                )

    def test_a_toml_document_anywhere_runs_the_toml_corpus_gates(self):
        plan = self.lane.plan_for(["library/core/Cargo.toml"], self.members, [], instruments=())
        self.assertEqual(plan.instrument_runs, [
            ("trust-toml", ["--test", "differential_corpus", "--test", "serialize_differential"]),
        ])

    def test_documents_outside_the_corpora_run_no_corpus_gate(self):
        # The manifests' own exclusions, a different suffix, and a suffix that
        # is only a substring.
        plan = self.lane.plan_for(
            ["first-party/clean/x.json", "vendor/serde/Cargo.toml", "docs/a.jsonl",
             "docs/b.json.md", "docs/toml.md"],
            self.members, [], instruments=(),
        )
        self.assertEqual(plan.instrument_runs, [])
        self.assertTrue(plan.empty())

    def test_a_touched_corpus_host_is_not_run_twice(self):
        members = dict(self.members, **{"crates/trust-json": "trust-json"})
        plan = self.lane.plan_for(
            ["crates/trust-json/tests/corpus_manifest.txt", "reports/r.json"], members, [],
            instruments=(),
        )
        self.assertEqual(plan.instrument_runs, [])
        self.assertIn("trust-json", plan.packages)

    def test_corpus_instruments_name_every_manifest_reader(self):
        # Each tail is `--test <target>` pairs naming EXACTLY the host's test
        # targets that read tests/corpus_manifest.txt: a reader left out never
        # runs on a document push, and a name that is no target fails the build.
        # The suffix and the exclusions are the ones the host's rule spells.
        for suffix, outside, host, tail in self.lane.CORPUS_INSTRUMENTS:
            with self.subTest(host=host):
                crate = REPO_ROOT / "crates" / host
                self.assertEqual(tail[0::2], ["--test"] * (len(tail) // 2), tail)
                self.assertEqual(len(tail) % 2, 0, tail)
                readers = sorted(
                    p.stem for p in (crate / "tests").glob("*.rs")
                    if "corpus_manifest.txt" in p.read_text(encoding="utf-8")
                )
                self.assertTrue(readers, f"{host}: no test target reads tests/corpus_manifest.txt")
                self.assertEqual(sorted(tail[1::2]), readers, f"{host}: the tail must name every reader")
                rules = [(crate / "tests" / f"{name}.rs").read_text(encoding="utf-8")
                         for name in tail[1::2]]
                self.assertTrue(any(f'"*{suffix}"' in rule for rule in rules),
                                f"{host}: no reader lists `*{suffix}` with git ls-files")
                for prefix in outside:
                    self.assertTrue(any(f'"{prefix}"' in rule for rule in rules),
                                    f"{host}: no reader excludes {prefix}")
                # No bin target: a `--test` build would rebuild it beside run 1.
                self.assertFalse((crate / "src" / "main.rs").exists(), host)
                self.assertFalse((crate / "src" / "bin").exists(), host)
                self.assertNotIn("[[bin]]", (crate / "Cargo.toml").read_text(encoding="utf-8"), host)

    def test_run_alone_names_real_test_targets(self):
        for name in self.lane.RUN_ALONE:
            self.assertTrue(list(REPO_ROOT.glob(f"crates/*/tests/{name}.rs")),
                            f"RUN_ALONE names {name}, which is no longer a test target under crates/")


@unittest.skipUnless(shutil.which("targo"), "no `targo` on PATH: the scope is measured on Targo's unit graph")
class MemberFeatureScopeLiveTest(unittest.TestCase):
    """TARGO-MEMBER-FEATURE-SCOPE-1, measured on the `targo` the lane runs.

    A three-member workspace: `narrow` and `wider` both depend on `shared`, and
    only `wider` turns on `shared/wide`. Under the words aterm's atpkg shim adds
    (`--config resolver.feature-unification="workspace"` right before the verb,
    `-Zfeature-unification` right after it), a command naming no scope gives
    `-p narrow` the workspace's union, `wide` included: the positive control,
    so a scoped run that shows no `wide` is a fact about the scope, not about
    an instrument that cannot see one. The lane's own commands, under the same
    words, keep `shared` at what `narrow` selects. Unit graphs only: nothing
    is compiled. Its own CARGO_HOME, so no user config takes part."""

    WIDENING_CONFIG = ["--config", 'resolver.feature-unification="workspace"']
    WIDENING_FLAG = "-Zfeature-unification"
    MANIFESTS = {
        "Cargo.toml": '[workspace]\nresolver = "2"\nmembers = ["narrow", "wider", "shared"]\n',
        "shared/Cargo.toml": ('[package]\nname = "shared"\nversion = "0.1.0"\nedition = "2021"\n\n'
                              '[features]\nwide = []\n'),
        "narrow/Cargo.toml": ('[package]\nname = "narrow"\nversion = "0.1.0"\nedition = "2021"\n\n'
                              '[dependencies]\nshared = { path = "../shared" }\n'),
        "wider/Cargo.toml": ('[package]\nname = "wider"\nversion = "0.1.0"\nedition = "2021"\n\n'
                             '[dependencies]\nshared = { path = "../shared", features = ["wide"] }\n'),
    }

    def setUp(self):
        self.lane = load_lane()
        self.tmp = tempfile.TemporaryDirectory()
        scratch = Path(self.tmp.name)
        self.root = scratch / "ws"
        for rel, text in self.MANIFESTS.items():
            manifest = self.root / rel
            (manifest.parent / "src").mkdir(parents=True, exist_ok=True)
            manifest.write_text(text, encoding="utf-8")
            if rel != "Cargo.toml":
                (manifest.parent / "src" / "lib.rs").write_text("", encoding="utf-8")
        self.env = dict(os.environ, CARGO_HOME=str(scratch / "cargo-home"),
                        CARGO_TARGET_DIR=str(scratch / "target"))
        self.env.pop("TARGO_TARGET_DIR", None)
        # The lane's commands are --locked: the lock its own `targo metadata` call writes.
        done = subprocess.run(["targo", "metadata", "--format-version", "1", "--offline"],
                              cwd=self.root, env=self.env, capture_output=True, text=True, timeout=600)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertTrue((self.root / "Cargo.lock").is_file())

    def tearDown(self):
        self.tmp.cleanup()

    def widened(self, cmd):
        """`cmd` with the shim's words around its verb (`targo --unverified <verb>`)."""
        return cmd[:2] + self.WIDENING_CONFIG + [cmd[2], self.WIDENING_FLAG] + cmd[3:]

    def shared_features(self, cmd):
        """The features of `shared` in `cmd`'s unit graph."""
        done = subprocess.run(cmd + ["--offline", "--unit-graph", "-Zunstable-options"], cwd=self.root,
                              env=self.env, capture_output=True, text=True, timeout=600)
        self.assertEqual(done.returncode, 0, (cmd, done.stderr))
        graph = json.loads(done.stdout)
        self.assertEqual(graph["version"], 1)
        units = [u for u in graph["units"] if u["target"]["name"] == "shared"]
        self.assertTrue(units, f"no unit of `shared` in the graph of {cmd}")
        return set().union(*(u["features"] for u in units))

    def test_the_lanes_commands_keep_a_members_features_where_a_wrapper_widens_them(self):
        bare = ["targo", "--unverified", "test", "--manifest-path", "Cargo.toml", "--locked",
                "--no-fail-fast", "-p", "narrow", "--tests"]
        self.assertIn("wide", self.shared_features(self.widened(bare)))  # the positive control
        plan = self.lane.Plan()
        plan.packages = ["narrow"]
        (test, _credit), = plan.attributed_commands()
        build = self.lane.TARGO_TRUST_BUILD[:6] + ["--manifest-path", "Cargo.toml", "--locked", "-p", "narrow"]
        self.assertIn("wide", self.shared_features(self.widened(build[:3] + build[6:])))
        for cmd in (test, build):
            with self.subTest(cmd=" ".join(cmd)):
                self.assertEqual(self.shared_features(cmd), set())
                self.assertEqual(self.shared_features(self.widened(cmd)), set())
                # A wrapper that ignores the opt-out and puts its `--config` before the verb.
                self.assertEqual(self.shared_features(cmd[:2] + self.WIDENING_CONFIG + cmd[2:]), set())


class FeatureTargetDirectoryTest(unittest.TestCase):
    def setUp(self):
        self.lane = load_lane()
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.plan = self.lane.Plan()

    def target(self, value):
        self.plan.feature_runs.append(("trust-router", ["--test", "setter_assert_refute_lane",
                                                       "--target-dir", value]))

    def problem(self, metadata):
        return self.lane.feature_target_directory_problem(self.plan, metadata, self.root)

    def test_equal_relative_and_normalized_paths_refuse_without_creating_them(self):
        self.target("feature/../default-target")
        self.assertIn("feature target directory collides",
                      self.problem({"target_directory": str(self.root / "default-target")}))
        self.assertEqual(list(self.root.iterdir()), [], "resolution must not create target dirs")

    def test_distinct_paths_allow_the_existing_plan(self):
        self.target("feature-target")
        self.assertIsNone(self.problem({"target_directory": str(self.root / "default-target")}))

    def test_absent_case_aliases_refuse_without_creating_either_directory(self):
        self.target("Feature-Parent/Feature-Target")
        self.assertIn("feature target directory collides", self.problem({
            "target_directory": str(self.root / "feature-parent" / "feature-target"),
        }))
        self.assertEqual(list(self.root.iterdir()), [])

    def test_symlink_aliases_refuse_even_with_an_absent_final_directory(self):
        actual = self.root / "actual"
        actual.mkdir()
        alias = self.root / "alias"
        alias.symlink_to(actual, target_is_directory=True)
        for default, feature in [(actual, alias), (alias, actual)]:
            with self.subTest(default=default, feature=feature):
                self.plan.feature_runs.clear()
                self.target(str(feature / "not-built-yet"))
                self.assertIn("feature target directory collides",
                              self.problem({"target_directory": str(default / "not-built-yet")}))
        self.assertFalse((actual / "not-built-yet").exists())

    def test_existing_case_aliases_refuse_when_the_filesystem_aliases_them(self):
        target = self.root / "Target"
        target.mkdir()
        alias = self.root / "target"
        if not alias.exists():
            self.skipTest("case-sensitive filesystem")
        self.target(str(alias))
        self.assertIn("feature target directory collides",
                      self.problem({"target_directory": str(target)}))

    def test_missing_or_malformed_authority_refuses_only_when_required(self):
        self.target("feature-target")
        for metadata in [{}, *[{"target_directory": value} for value in
                              [None, False, 7, [], {}, "", "relative-target", str(self.root / "bad\0path")]]]:
            with self.subTest(metadata=metadata):
                self.assertIn("metadata target_directory", self.problem(metadata))
                self.plan.feature_runs = [("trust-router", ["--features", "ay-backend", "--lib"])]
                self.assertIsNone(self.problem(metadata), "library-only plans need no target-dir authority")
                self.plan.feature_runs.clear()
                self.target("feature-target")

    def test_unresolvable_symlink_refuses(self):
        (self.root / "loop").symlink_to("loop", target_is_directory=True)
        self.target("loop/target")
        self.assertIn("cannot resolve", self.problem({"target_directory": str(self.root / "default")}))

    def test_every_target_is_checked_and_equals_spelling_is_supported(self):
        self.target("separate-target")
        self.plan.feature_runs.append(("trust-router", ["--target-dir=default-target"]))
        self.assertIn("feature target directory collides",
                      self.problem({"target_directory": str(self.root / "default-target")}))

    def test_test_arguments_are_not_cargo_target_directory_options(self):
        self.plan.feature_runs.append(("trust-router", ["--lib", "--", "--target-dir", "filter"]))
        self.assertIsNone(self.problem({}))

    def test_missing_or_invalid_explicit_path_refuses(self):
        for tail in [["--target-dir"], ["--target-dir="], ["--target-dir", "bad\0path"]]:
            with self.subTest(tail=tail):
                self.plan.feature_runs = [("trust-router", tail)]
                self.assertIn("feature target directory",
                              self.problem({"target_directory": str(self.root / "default-target")}))


class RangeTest(unittest.TestCase):
    def setUp(self):
        self.lane = load_lane()

    def test_pushed_refs(self):
        # An update is the two-dot TREE diff, a new branch the three-dot diff
        # since its fork from origin/main, a deletion nothing.
        z = "0" * 40
        refs = "\n".join([
            f"refs/heads/a {'1' * 40} refs/heads/a {'2' * 40}",
            f"refs/heads/new {'3' * 40} refs/heads/new {z}",
            f"(delete) {z} refs/heads/gone {'4' * 40}",
        ])
        ranges, reading = self.lane.resolve_ranges(True, None, refs)
        self.assertEqual(ranges, [f"{'2' * 40}..{'1' * 40}", f"origin/main...{'3' * 40}"])
        self.assertIn("pushed refs", reading)
        self.assertIn("2 update(s)", reading)

    def test_unset_push_refs_widen_and_say_so(self):
        ranges, reading = self.lane.resolve_ranges(True, None, "")
        self.assertEqual(ranges, ["origin/main...HEAD"])
        self.assertIn("standing", reading)
        _, reading = self.lane.resolve_ranges(True, None, f"(delete) {'0' * 40} refs/heads/g {'4' * 40}")
        self.assertIn("only deletions or malformed lines", reading)

    def test_explicit_range_stays_three_dot(self):
        for spelled in ("A..B", "A...B"):
            ranges, reading = self.lane.resolve_ranges(False, spelled, "ignored")
            self.assertEqual(ranges, ["A...B"], spelled)
            self.assertIn("explicit --range", reading)
        self.assertEqual(self.lane.resolve_ranges(False, "..", "")[0], ["origin/main...HEAD"])


# A fake `targo` that speaks cargo's side of the lane's record protocol: for
# `--unverified test`, print `Running ...` for each binary FAKE_TARGO_BINARIES
# names and hand it to the `target.'cfg(all())'.runner` from `--config`, with
# the environment and working directory cargo would give it. Python, not bash,
# so the runner's TOML array parses as the JSON it is.
FAKE_TARGO = """#!/usr/bin/env python3
import json, os, subprocess, sys
args = sys.argv[1:]
if args[:1] == ["metadata"]:
    sys.stdout.write(open(os.environ["FAKE_TARGO_METADATA"]).read())
    sys.exit(0)
if args[:1] == ["--warm-up"]:
    sys.exit(0)
if args[:1] != ["--unverified"]:
    sys.exit(64)
if args[1:2] == ["--version"]:
    print("targo 0.0.0-fake")
    sys.exit(0)
# TARGO-MEMBER-FEATURE-SCOPE-1: the words a real Targo needs right after the
# verb to build `-p X` with the features its selection asks for, under a wrapper
# that widens them to the workspace's. A build or test without them is refused,
# as the widened graph fails on a compiler crate's build script, so every run
# here checks every command the lane sends. They are dropped before the log.
SCOPE = ["-Zfeature-unification", "--config", 'resolver.feature-unification="selected"']
if args[2:5] != SCOPE:
    sys.stderr.write("fake targo: no member feature scope after the verb: " + " ".join(args) + "\\n")
    sys.exit(65)
args = args[:2] + args[5:]
if args[1:2] == ["build"]:  # the targo-trust prebuild: text on stderr, JSON on stdout
    with open(os.environ["FAKE_TARGO_LOG"], "a") as fh:
        fh.write(" ".join(args) + "\\n")
    mode = os.environ.get("FAKE_TARGO_TRUST", "ok")
    if mode == "fail":
        # A wrapper's own text on stdout, beside cargo's JSON: shown on a failure.
        print("targo: a line on stdout that is not cargo JSON")
        print(json.dumps({"reason": "build-finished", "success": False}))
        sys.stderr.write("error: could not compile `targo-trust` (bin \\"targo-trust\\")\\n")
        sys.exit(101)
    if mode == "sleep":
        if os.environ.get("FAKE_TARGO_TRUST_PIDFILE"):  # the build's pid, for the interrupt tests
            with open(os.environ["FAKE_TARGO_TRUST_PIDFILE"], "w") as fh:
                fh.write(str(os.getpid()))
        os.execvp("sleep", ["sleep", "30"])
    sys.stderr.write("   Compiling targo-trust v0.10.0\\n")
    msgs = [{"reason": "compiler-artifact", "target": {"name": "trust-types", "kind": ["lib"]},
             "executable": None}]
    if mode != "no-artifact":
        msgs.append({"reason": "compiler-artifact", "target": {"name": "targo-trust", "kind": ["bin"]},
                     "executable": os.environ["FAKE_TARGO_TRUST_EXE"]})
    msgs.append({"reason": "build-finished", "success": True})
    for msg in msgs:
        print(json.dumps(msg))
    sys.exit(0)
if os.environ.get("FAKE_TARGO_RELINK"):  # a sibling build relinks the target dir's targo-trust
    with open(os.environ["FAKE_TARGO_TRUST_EXE"], "w") as fh:
        fh.write("relinked by a sibling build\\n")
# Cargo's end of options: what follows the first `--` is the test binary's,
# handed to it after its path, and never read as cargo's own `--config` (a real
# cargo hands a `--config` there to libtest, which refuses it).
passed = []
if "--" in args:
    at = args.index("--")
    args, passed = args[:at], args[at + 1:]
runner = []
if "--config" in args:
    at = args.index("--config")
    runner = json.loads(args[at + 1].split("=", 1)[1])
    del args[at:at + 2]
with open(os.environ["FAKE_TARGO_LOG"], "a") as fh:
    fh.write(" ".join(["--unverified"] + args[1:] + (["--"] + passed if passed else [])) + "\\n")
build = os.environ.get("FAKE_TARGO_BUILD", "ok")
if build == "fail":
    print("error: could not compile `trust-router` (test \\"gate\\")", flush=True)
    sys.exit(101)
if build == "sleep":
    if os.environ.get("FAKE_TARGO_PIDFILE"):  # the build's pid, for the interrupt tests
        with open(os.environ["FAKE_TARGO_PIDFILE"], "w") as fh:
            fh.write(str(os.getpid()))
    os.execvp("sleep", ["sleep", "30"])
env = dict(os.environ, CARGO_PKG_NAME=os.environ.get("FAKE_TARGO_PKG_NAME", "trust-router"),
           CARGO_MANIFEST_DIR=os.environ["FAKE_TARGO_PKG"])
if build != "no-dyld":
    env["DYLD_FALLBACK_LIBRARY_PATH"] = "/fake/target/debug/deps"
if os.environ.get("FAKE_TARGO_SCRUB"):  # a cargo that does not hand this variable on
    env.pop(os.environ["FAKE_TARGO_SCRUB"], None)
worst = 0
binaries = os.environ.get("FAKE_TARGO_BINARIES", "")
if os.environ.get("FAKE_TARGO_BINARIES_BY_FEATURES"):  # one member's tails, each its own executable
    features = args[args.index("--features") + 1] if "--features" in args else ""
    table = json.loads(os.environ["FAKE_TARGO_BINARIES_BY_FEATURES"])
    # A filtered (instrument) command may be keyed by its filter, `-- <filter>`.
    filtered = " ".join(["--"] + passed)
    binaries = table[filtered] if passed and filtered in table else table[features]
# The package cargo runs each binary for, when one command tests two members.
pkg_by_binary = json.loads(os.environ.get("FAKE_TARGO_PKG_BY_BINARY", "{}"))
for name in filter(None, binaries.split(",")):
    exe = os.path.join(os.environ["FAKE_TARGO_BINDIR"], name)
    print("     Running tests/%s.rs (%s)" % (name.rsplit("-", 1)[0], exe), flush=True)
    if build == "bypass":  # a cargo that ignores the runner and runs the binary itself
        runner = []
    benv = dict(env, CARGO_PKG_NAME=pkg_by_binary[name]) if name in pkg_by_binary and "CARGO_PKG_NAME" in env else env
    if subprocess.run(runner + [exe] + passed, cwd=os.environ["FAKE_TARGO_PKG"], env=benv).returncode:
        worst = 101
if build == "partial":  # it recorded the binaries, then another target failed to build
    print("error: could not compile `trust-router` (test \\"other\\")", flush=True)
    worst = 101
sys.exit(worst)
"""

# The fake test binaries. Each is a script run by this interpreter, not
# /bin/sh: macOS strips DYLD_* from a SIP-protected executable's environment,
# and ENV_PROBE must see the one the fake cargo set. LIBTEST speaks libtest's
# side: `running N tests`, one line per test, the closing `test result:`, and
# exit 0 or 101.
LIBTEST = """
def libtest(results):
    print("running %d tests" % len(results))
    for name, ok in results:
        print("test %s ... %s" % (name, "ok" if ok else "FAILED"))
    failed = sum(1 for _, ok in results if not ok)
    print("\\ntest result: %s. %d passed; %d failed; 0 ignored; 0 measured; 0 filtered out; "
          "finished in 0.01s" % ("FAILED" if failed else "ok", len(results) - failed, failed))
    sys.exit(101 if failed else 0)
"""
GATE = """
listed, fresh = sys.argv[0][-2:]  # 'f'ailed or '0' ok, per test
libtest([("mod_a::listed", listed != "f"), ("mod_b::fresh", fresh != "f")])
"""
ABORT = """
print("thread 'main' panicked at src/main.rs:1:1: a harness = false check failed")
sys.exit(134)
"""
# Died mid-run, each right after its known-red failure: SIGKILL (jetsam, the
# OOM killer) and a test that calls process::exit(101). The tests after it
# (mod_b::after) never report.
KILLED = """
import os, signal
print("running 2 tests\\ntest mod_a::listed ... FAILED", flush=True)
os.kill(os.getpid(), signal.SIGKILL)
"""
EXITED = """
print("running 2 tests\\ntest mod_a::listed ... FAILED", flush=True)
sys.exit(101)
"""
PAIR = """
import os, time
me = os.path.basename(sys.argv[0]).split("-")[0]
other = {"left": "right", "right": "left"}[me]
rendezvous = os.environ["FAKE_PAIR_DIR"]
open(os.path.join(rendezvous, me), "w").close()
deadline = time.monotonic() + float(os.environ.get("FAKE_PAIR_WAIT", "20"))
while time.monotonic() < deadline:
    if os.path.exists(os.path.join(rendezvous, other)):
        libtest([("rendezvous", True)])
    time.sleep(0.05)
libtest([("rendezvous", False)])
"""
# Fails when another copy of itself is running: it holds an exclusive lock
# file for two seconds, as a fixed temp path would be held.
SOLO = """
import os, time
lock = os.path.join(os.environ["FAKE_PAIR_DIR"], "solo.lock")
try:
    os.close(os.open(lock, os.O_CREAT | os.O_EXCL))
except FileExistsError:
    libtest([("alone", False)])
time.sleep(2)
os.unlink(lock)
libtest([("alone", True)])
"""
# Not libtest (a `harness = false` target that exits 0 passes on its exit code).
ENV_PROBE = """
import json, os
print("PROBE " + json.dumps({"argv": sys.argv, "cwd": os.getcwd(), "env": dict(os.environ)}))
print("test probe ... ok")
"""
# With FAKE_SLEEPER_PIDS set it records its pid there, so a test can find
# exactly the sleepers its own lane started (never another run's on the host).
SLEEPER = """
import os, time
if os.environ.get("FAKE_SLEEPER_PIDS"):
    with open(os.path.join(os.environ["FAKE_SLEEPER_PIDS"], str(os.getpid())), "w") as fh:
        fh.write(str(os.getpid()))
time.sleep(60)
"""
# Records WHEN it started (wall clock), for the barrier tests.
STAMP = """
import os, time
with open(os.path.join(os.environ["FAKE_STAMP_DIR"], str(os.getpid())), "w") as fh:
    fh.write(repr(time.time()))
libtest([("stamped", True)])
"""
# A consumer test: reads the targo-trust TRUST_TARGO_TRUST_BIN names, as the
# real ones run it, and fails when there is none.
TARGO_TRUST_PROBE = """
import json, os
path = os.environ.get("TRUST_TARGO_TRUST_BIN", "")
body = open(path, encoding="utf-8").read() if os.path.isfile(path) else None
print("TTPROBE " + json.dumps({"path": path, "body": body}))
libtest([("runs_targo_trust", body is not None)])
"""
# A libtest binary with nothing to run: a lib whose tests a feature compiles
# out, or a bin target with none. libtest says `running 0 tests`, `test result:
# ok. 0 passed`, and exits 0.
EMPTY = """
libtest([])
"""
# A libtest binary whose only test is #[ignore]d: it says `running 1 test` and
# exits 0, and judged nothing.
IGNORED = """
print("running 1 test\\ntest mod_a::later ... ignored\\n")
print("test result: ok. 0 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.00s")
"""
# trust-model-prelude's source-digest test, passing (B1A-14a).
DIGEST = """
libtest([("tests::digest::source_digest_matches", True)])
"""
FAKE_BINARIES = {
    # gate-<16 hex>: the last two digits say how mod_a::listed and
    # mod_b::fresh end ('f'ailed / '0' ok). All three are the binary `gate`
    # to parse_results, which strips the hash, so the test key is gate::<test>.
    "gate-00000000000000f0": GATE,  # listed fails, fresh passes
    "gate-00000000000000ff": GATE,  # both fail
    "gate-0000000000000000": GATE,  # both pass
    "gate-1000000000000000": GATE,  # both pass: another executable, the same key
    "gate-2000000000000000": GATE,  # both pass: a third
    "abort-0000000000000001": ABORT,
    "left-0000000000000002": PAIR,
    "right-0000000000000003": PAIR,
    "probe-0000000000000004": ENV_PROBE,
    "sleeper-0000000000000005": SLEEPER,
    "solo-0000000000000006": SOLO,
    "killed-0000000000000007": KILLED,
    "exited-0000000000000008": EXITED,
    "stamp-0000000000000009": STAMP,
    "ttprobe-000000000000000a": TARGO_TRUST_PROBE,
    "empty-000000000000000b": EMPTY,
    "ignored-000000000000000c": IGNORED,
    "digest-000000000000000d": DIGEST,
}
MODES = {  # mode -> (FAKE_TARGO_BUILD, binaries cargo would run)
    "pass": ("ok", ["gate-0000000000000000"]),
    "fail": ("fail", []),
    "sleep": ("sleep", []),
    "known": ("ok", ["gate-00000000000000f0"]),
    "new": ("ok", ["gate-00000000000000ff"]),
    "stale": ("ok", ["gate-0000000000000000"]),
    "crash": ("ok", ["gate-00000000000000f0", "abort-0000000000000001"]),
    "killed": ("ok", ["killed-0000000000000007"]),
    "exited": ("ok", ["exited-0000000000000008"]),
    "record-rc": ("partial", ["gate-00000000000000f0"]),
    "pair": ("ok", ["left-0000000000000002", "right-0000000000000003"]),
    "solo": ("ok", ["solo-0000000000000006"]),
    "probe": ("ok", ["probe-0000000000000004"]),
    "hang": ("ok", ["gate-0000000000000000", "sleeper-0000000000000005"]),
    "no-dyld": ("no-dyld", ["gate-0000000000000000"]),
    "bypass": ("bypass", ["gate-00000000000000f0"]),
    "stamp": ("ok", ["stamp-0000000000000009"]),
    "ttprobe": ("ok", ["ttprobe-000000000000000a"]),
}


class FakeTargo:
    """The fake `targo` and its binaries, written and first-exec'd once.

    The first exec of a newly written executable costs 6-10 s on a loaded
    macOS host (it is scanned before it runs). Paying it here, logging nothing,
    keeps it off a run's wall-clock budget: the budget tests give the lane
    seconds, and those seconds must reach the run."""

    _dir = None

    @classmethod
    def directory(cls) -> Path:
        if cls._dir is None:
            cls._dir = tempfile.TemporaryDirectory()
            root = Path(cls._dir.name)
            (root / "bin").mkdir()
            preamble = fixture_shebang()
            files = {root / "targo": preamble + FAKE_TARGO.partition("\n")[2]}
            for name, body in FAKE_BINARIES.items():
                files[root / "bin" / name] = (
                    preamble + "import sys\n"
                    f"if sys.argv[1:] == ['--warm-up']:\n    sys.exit(0)\n{LIBTEST}{body}"
                )
            for path, text in files.items():
                path.write_text(text, encoding="utf-8")
                path.chmod(path.stat().st_mode | stat.S_IEXEC)
                subprocess.run([str(path), "--warm-up"], env={"PATH": os.environ["PATH"]},
                               capture_output=True, check=False, timeout=120)
        return Path(cls._dir.name)


class ExactInterpreterLauncherTest(unittest.TestCase):
    def test_original_interpreter_with_spaces_and_quotes_runs_actual_fixture_binaries(self):
        with tempfile.TemporaryDirectory(prefix="exact python ' path ") as directory:
            interpreter = Path(directory) / "original python ' executable"
            interpreter.symlink_to(Path(sys.executable).resolve())
            with mock.patch.object(sys, "executable", str(interpreter)), mock.patch.object(FakeTargo, "_dir", None):
                root = FakeTargo.directory()
                owned = FakeTargo._dir
            self.addCleanup(owned.cleanup)
            for executable in (root / "targo", root / "bin/gate-00000000000000f0"):
                result = subprocess.run([str(executable), "--warm-up"], capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                selected = Path(executable.read_text().splitlines()[0][2:])
                self.assertFalse(any(character.isspace() for character in str(selected)))
                self.assertEqual(selected.resolve(), interpreter.resolve())


class MainBase(unittest.TestCase):
    """main() end to end, with a fake `targo` and a fixed changed-path set."""

    def setUp(self):
        self.lane = load_lane()
        self.lane.changed_paths = lambda ranges: ["crates/trust-router/src/lib.rs"]
        # These tests count commands, builds and binary runs for one touched
        # member with ONE feature tail. Pin that fixture in this test's copy of
        # the table (plan_for's default is the same dict) instead of reading
        # the live FEATURE_RUNS, whose router tails PlanTest checks.
        self.lane.FEATURE_RUNS.clear()
        self.lane.FEATURE_RUNS["trust-router"] = [["--features", "ay-backend", "--lib"]]
        self.tmp = tempfile.TemporaryDirectory()
        tmp = Path(self.tmp.name)
        fake = FakeTargo.directory()
        manifest = str(REPO_ROOT / "crates" / "trust-router" / "Cargo.toml")
        meta = tmp / "meta.json"
        meta.write_text(json.dumps({
            "workspace_members": ["router-id"], "workspace_default_members": ["router-id"],
            "packages": [{"id": "router-id", "name": "trust-router", "manifest_path": manifest}],
            # LANE_DRIVER subprocesses load the actual feature registry, so
            # provide Cargo's authoritative path as real metadata does.
            "target_directory": str(tmp / "default-target"),
        }), encoding="utf-8")
        self.log = tmp / "calls.log"
        self.pkg = tmp / "pkg"
        self.pkg.mkdir()
        (tmp / "pair").mkdir()
        self.saved = dict(os.environ)
        os.environ["PATH"] = f"{fake}{os.pathsep}{os.environ['PATH']}"
        os.environ.update(
            FAKE_TARGO_METADATA=str(meta), FAKE_TARGO_LOG=str(self.log),
            FAKE_TARGO_BINDIR=str(fake / "bin"), FAKE_TARGO_PKG=str(self.pkg),
            FAKE_PAIR_DIR=str(tmp / "pair"), TRUST_CRATES_TESTS_JOBS="4",
        )
        if os.environ.get("BUILD_SLOT_HELD") == "1":
            # Only this inert fake-Cargo subject gets synthetic policy inputs;
            # the outer suite retains its genuine admission (possibly 1 CPU).
            # These older scenarios exercise a four-binary pool. Dedicated
            # managed-budget controls below choose their own shares and pools.
            os.environ.update(CARGO_BUILD_JOBS="6", RUST_TEST_THREADS="6")

    def tearDown(self):
        os.environ.clear()
        os.environ.update(self.saved)
        self.tmp.cleanup()

    def run_main(self, mode, budget="60", jobs=None):
        os.environ["FAKE_TARGO_BUILD"], binaries = MODES[mode]
        os.environ["FAKE_TARGO_BINARIES"] = ",".join(binaries)
        os.environ["TRUST_CRATES_TESTS_BUDGET_S"] = budget
        if jobs is not None:
            os.environ["TRUST_CRATES_TESTS_JOBS"] = jobs
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = self.lane.main(["--range", "origin/main..HEAD"])
        calls = self.log.read_text(encoding="utf-8").splitlines() if self.log.exists() else []
        return rc, out.getvalue(), calls


class FeatureTargetDirectoryMainTest(MainBase):
    def setUp(self):
        super().setUp()
        self.feature_target = Path(self.tmp.name) / "feature-target"
        self.lane.FEATURE_RUNS["trust-router"].append([
            "--features", "ay-backend", "--test", "setter_assert_refute_lane",
            "--target-dir", str(self.feature_target),
        ])

    def target_metadata(self, value):
        path = Path(os.environ["FAKE_TARGO_METADATA"])
        metadata = json.loads(path.read_text(encoding="utf-8"))
        metadata["target_directory"] = value
        path.write_text(json.dumps(metadata), encoding="utf-8")

    def test_collision_refuses_before_any_build_despite_distinct_env_guess(self):
        self.target_metadata(str(self.feature_target))
        os.environ["CARGO_TARGET_DIR"] = str(Path(self.tmp.name) / "other-target")
        rc, out, calls = self.run_main("pass")
        self.assertEqual(rc, 2, out)
        self.assertIn("CANNOT JUDGE", out)
        self.assertIn("feature target directory collides", out)
        self.assertEqual(calls, [], "neither default nor feature tests may build")
        self.assertNotIn("--- started:", out)

    def test_collision_also_precedes_the_targo_trust_prebuild(self):
        self.target_metadata(str(self.feature_target))
        self.lane.TARGO_TRUST_CONSUMERS = ("trust-router",)
        with mock.patch.object(self.lane, "prebuild_targo_trust") as prebuild:
            rc, out, calls = self.run_main("pass")
        self.assertEqual(rc, 2, out)
        prebuild.assert_not_called()
        self.assertIn("feature target directory collides", out)
        self.assertEqual(calls, [])

    def test_absent_case_alias_refuses_before_any_build(self):
        self.target_metadata(str(self.feature_target.parent / self.feature_target.name.upper()))
        self.assertFalse(self.feature_target.exists())
        rc, out, calls = self.run_main("pass")
        self.assertEqual(rc, 2, out)
        self.assertIn("feature target directory collides", out)
        self.assertEqual(calls, [])
        self.assertFalse(self.feature_target.exists())

    def test_invalid_or_missing_metadata_builds_nothing(self):
        path = Path(os.environ["FAKE_TARGO_METADATA"])
        metadata = json.loads(path.read_text(encoding="utf-8"))
        del metadata["target_directory"]
        path.write_text(json.dumps(metadata), encoding="utf-8")
        # Begin without target_directory; each later subcase
        # supplies a malformed authority rather than a usable absolute path.
        for value in [None, "", "relative-target", 7]:
            with self.subTest(value=value):
                if value is not None:
                    self.target_metadata(value)
                rc, out, calls = self.run_main("pass")
                self.assertEqual(rc, 2, out)
                self.assertIn("metadata target_directory", out)
                self.assertEqual(calls, [])

    def test_library_only_plan_still_runs_without_target_directory_metadata(self):
        self.lane.FEATURE_RUNS["trust-router"].pop()
        path = Path(os.environ["FAKE_TARGO_METADATA"])
        metadata = json.loads(path.read_text(encoding="utf-8"))
        del metadata["target_directory"]
        path.write_text(json.dumps(metadata), encoding="utf-8")
        rc, out, calls = self.run_main("pass")
        self.assertEqual(rc, 0, out)
        self.assertEqual(len(calls), 2, calls)

    def test_distinct_authoritative_directory_keeps_every_planned_run(self):
        default_target = str(Path(self.tmp.name) / "default-target")
        os.environ["CARGO_TARGET_DIR"] = default_target
        self.target_metadata(default_target)
        rc, out, calls = self.run_main("pass")
        self.assertEqual(rc, 0, out)
        self.assertEqual(len(calls), 3, calls)
        self.assertIn("--tests", calls[0])
        self.assertIn("--features ay-backend --lib", calls[1])
        self.assertIn("--test setter_assert_refute_lane --target-dir", calls[2])
        self.assertIn("3/3 run(s) passed", out)


class MainTest(MainBase):
    def test_green_runs_both_router_lanes(self):
        rc, out, calls = self.run_main("pass")
        self.assertEqual(rc, 0, out)
        self.assertEqual(len(calls), 2, calls)
        self.assertTrue(any("--features ay-backend --lib" in c for c in calls), calls)
        self.assertIn("2/2 run(s) passed", out)
        # No consumer of targo-trust is touched, so nothing else is built.
        self.assertFalse([c for c in calls if c.split()[1:2] == ["build"]], calls)
        self.assertNotIn("targo-trust", out)
        # Each command's binary ran once, from the pool, not from cargo.
        self.assertEqual(out.count("test mod_b::fresh ... ok"), 2, out)

    def test_a_failing_build_fails_the_lane(self):
        rc, out, _ = self.run_main("fail")
        self.assertEqual(rc, 1, out)
        self.assertIn("FAILED WITHOUT A TEST FAILURE", out)

    def test_budget_exhaustion_is_not_judged_never_green(self):
        # This control must reach the slow build. Give metadata/host fixture
        # setup no logical time, then run the real build against the unchanged
        # one-second budget. BarrierTest covers expiry before the wait.
        clock = mock.Mock(wraps=time)
        epoch = time.monotonic()
        build_started = None
        clock.monotonic.side_effect = lambda: (
            epoch if build_started is None else epoch + time.monotonic() - build_started
        )
        build = self.lane.run_with_deadline
        pidfile = Path(self.tmp.name) / "budget-build.pid"
        os.environ["FAKE_TARGO_PIDFILE"] = str(pidfile)

        def start_the_build(cmd, deadline, env=None):
            nonlocal build_started
            self.assertIsNone(build_started, "no command may follow the expired build")
            build_started = time.monotonic()
            return build(cmd, deadline, env)

        t0 = time.monotonic()
        with mock.patch.object(self.lane, "time", clock), \
                mock.patch.object(self.lane, "run_with_deadline", start_the_build):
            rc, out, calls = self.run_main("sleep", budget="1")
        self.assertLess(time.monotonic() - t0, 20, "the deadline did not kill the build")
        self.assertEqual(rc, 3, out)
        self.assertIn("NOT JUDGED", out)
        self.assertIn("not run:", out)
        self.assertEqual(len(calls), 1, calls)
        self.assertTrue(pidfile.exists(), "the slow build must actually start")
        with self.assertRaises(ProcessLookupError, msg="the expired build outlived the lane"):
            os.kill(int(pidfile.read_text()), 0)

    def test_a_binary_still_running_at_the_deadline_is_not_judged(self):
        # main()'s side: a pool that did not finish is NOT JUDGED, never a
        # pass, and names what it did not finish. (RecordTest drives
        # run_binaries itself against a real process and a real deadline.)
        def out_of_time(binaries, jobs, deadline):
            for binary in binaries:
                if "gate-" in binary.display:
                    binary.rc = 0
            return False
        self.lane.run_binaries = out_of_time
        rc, out, _ = self.run_main("hang")
        self.assertEqual(rc, 3, out)
        self.assertIn("NOT JUDGED", out)
        self.assertIn("not run to completion:", out)
        self.assertIn("sleeper-0000000000000005", out)
        self.assertNotIn("not run to completion: Running tests/gate.rs", out)

    def test_cargo_in_disguise_cannot_judge(self):
        fake = Path(self.tmp.name) / "disguise"
        fake.mkdir()
        (fake / "targo").write_text(
            "#!/usr/bin/env bash\n"
            "[ \"$1\" = metadata ] && { cat \"$FAKE_TARGO_METADATA\"; exit 0; }\n"
            "echo \"error: unexpected argument '--unverified' found\" >&2; exit 1\n",
            encoding="utf-8",
        )
        (fake / "targo").chmod(0o755)
        os.environ["PATH"] = f"{fake}{os.pathsep}{os.environ['PATH']}"
        rc, out, _ = self.run_main("pass")
        self.assertEqual(rc, 2, out)
        self.assertIn("not Targo", out)

    def test_jobs_must_be_a_positive_integer(self):
        for jobs in ("0", "-1", "four"):
            with self.subTest(jobs=jobs):
                rc, out, calls = self.run_main("pass", jobs=jobs)
                self.assertEqual(rc, 2, out)
                self.assertIn("TRUST_CRATES_TESTS_JOBS", out)
                self.assertEqual(calls, [], "judged nothing, so built nothing")

    def test_binaries_run_concurrently_and_one_job_is_serial(self):
        # left and right each pass only if the other is running at the same
        # time: proof of concurrency that no timing threshold decides.
        os.environ["FAKE_PAIR_WAIT"] = "20"
        rc, out, _ = self.run_main("pair", jobs="2")
        self.assertEqual(rc, 0, out)
        self.assertEqual(out.count("test rendezvous ... ok"), 4, out)  # 2 binaries x 2 commands
        # Negative control: one job runs them one at a time, so neither meets.
        for leftover in Path(os.environ["FAKE_PAIR_DIR"]).iterdir():
            leftover.unlink()
        os.environ["FAKE_PAIR_WAIT"] = "1"
        rc, out, _ = self.run_main("pair", jobs="1")
        self.assertEqual(rc, 1, out)
        self.assertIn("NEW FAILURE: left::rendezvous", out)

    def test_one_executable_recorded_twice_never_runs_beside_itself(self):
        # Both commands record the same solo binary; at four jobs its two runs
        # would overlap and collide on its lock file (RecordTest has the
        # control showing two copies at different paths do).
        rc, out, _ = self.run_main("solo", jobs="4")
        self.assertEqual(rc, 0, out)
        self.assertEqual(out.count("test alone ... ok"), 2, out)

    def test_a_run_alone_binary_never_shares_the_pool(self):
        # left, declared RUN_ALONE, runs after the pool drains, so right waits
        # for it in vain; at two jobs, undeclared, both meet (the test above).
        self.lane.RUN_ALONE = {"left": "fixture"}
        os.environ["FAKE_PAIR_WAIT"] = "1"
        rc, out, _ = self.run_main("pair", jobs="2")
        self.assertEqual(rc, 1, out)
        self.assertIn("running 2 test binaries alone (RUN_ALONE): left", out)
        self.assertIn("NEW FAILURE: right::rendezvous", out)
        self.assertNotIn("NEW FAILURE: left::rendezvous", out)

    def test_each_binary_gets_cargos_argv_directory_and_environment(self):
        os.environ["FAKE_LANE_MARKER"] = "from the lane's own environment"
        rc, out, _ = self.run_main("probe")
        self.assertEqual(rc, 0, out)
        probes = [json.loads(line[len("PROBE "):]) for line in out.splitlines() if line.startswith("PROBE ")]
        self.assertEqual(len(probes), 2, out)
        for probe in probes:
            self.assertEqual(len(probe["argv"]), 1, probe["argv"])  # nothing of the recorder
            self.assertTrue(probe["argv"][0].endswith("probe-0000000000000004"), probe["argv"])
            self.assertEqual(Path(probe["cwd"]).resolve(), self.pkg.resolve())
            env = probe["env"]
            self.assertEqual(env["CARGO_PKG_NAME"], "trust-router")
            self.assertEqual(env["CARGO_MANIFEST_DIR"], str(self.pkg))
            self.assertEqual(env["FAKE_LANE_MARKER"], "from the lane's own environment")
            if sys.platform == "darwin":
                self.assertEqual(env["DYLD_FALLBACK_LIBRARY_PATH"], "/fake/target/debug/deps")
            leaked = [k for k, v in env.items() if "crates-tests-record." in v or "json.dump" in v]
            self.assertEqual(leaked, [], "the record pass leaked into the replayed environment")

    def test_a_binary_cargo_ran_itself_cannot_judge(self):
        # Its failure would reach only cargo's exit code, never the ratchet.
        rc, out, _ = self.run_main("bypass")
        self.assertEqual(rc, 2, out)
        self.assertIn("announced 1 test binaries but handed 0 to the runner", out)

    @unittest.skipUnless(sys.platform == "darwin", "SIP strips DYLD_* only on macOS")
    def test_a_record_stripped_of_dyld_cannot_judge(self):
        rc, out, _ = self.run_main("no-dyld")
        self.assertEqual(rc, 2, out)
        self.assertIn("DYLD_FALLBACK_LIBRARY_PATH", out)


class ManagedThreadBudgetTest(MainBase):
    """Drive real fake-Cargo records and their executed children, not helper arithmetic."""

    def setUp(self):
        super().setUp()
        # Synthetic policy inputs are scoped to this inert fake-Cargo fixture;
        # the outer test process itself must have genuine build-slot admission.
        os.environ.update(BUILD_SLOT_HELD="1", CARGO_BUILD_JOBS="6", RUST_TEST_THREADS="6")

    def run_recorded_probes(self, jobs="3"):
        recorded = []
        load = self.lane.load_invocations

        def capture(record_dir, output):
            binaries = load(record_dir, output)
            # Snapshot before replay: a post-record env rewrite must not pass.
            recorded.extend({"argv": list(b.argv), "cwd": b.cwd, "env": dict(b.env)} for b in binaries)
            return binaries

        mode = ("ok", ["probe-0000000000000004", "gate-0000000000000000", "gate-1000000000000000"])
        with mock.patch.dict(MODES, {"thread-budget": mode}), \
                mock.patch.object(self.lane, "load_invocations", side_effect=capture):
            rc, out, calls = self.run_main("thread-budget", jobs=jobs)
        probes = [json.loads(line[len("PROBE "):]) for line in out.splitlines() if line.startswith("PROBE ")]
        return rc, out, calls, recorded, probes

    def assert_recorded_allowance(self, expected, jobs="3"):
        rc, out, calls, recorded, probes = self.run_recorded_probes(jobs)
        self.assertEqual(rc, 0, out)
        self.assertEqual(len(calls), 2, calls)
        self.assertEqual(len(recorded), 6, out)  # three binaries in both unchanged commands
        self.assertEqual(len(probes), 2, out)
        self.assertEqual(out.count("test mod_b::fresh ... ok"), 4, out)
        for record in recorded:
            self.assertEqual(record["env"].get("RUST_TEST_THREADS"), expected,
                             {"argv": record["argv"], "RUST_TEST_THREADS": record["env"].get("RUST_TEST_THREADS")})
        for probe in probes:
            matches = [r for r in recorded if r["argv"] == probe["argv"]]
            self.assertTrue(matches, probe["argv"])
            for record in matches:
                changed = sorted(k for k in record["env"].keys() | probe["env"].keys()
                                 if record["env"].get(k) != probe["env"].get(k))
                self.assertEqual(changed, [], "Cargo environment keys changed during replay")
            self.assertEqual(Path(probe["cwd"]).resolve(), self.pkg.resolve())
        return out

    def test_managed_six_three_records_two_before_cargo_and_replays_exactly(self):
        out = self.assert_recorded_allowance("2")
        self.assertIn("recording RUST_TEST_THREADS=2 before Cargo", out)
        self.assertEqual(os.environ["RUST_TEST_THREADS"], "6", "do not mutate the caller's preference")

    def test_smaller_inherited_one_is_retained(self):
        os.environ["RUST_TEST_THREADS"] = "1"
        self.assert_recorded_allowance("1")

    def test_single_binary_pool_allows_six(self):
        self.assert_recorded_allowance("6", jobs="1")

    def test_one_cpu_share_with_one_binary_records_one(self):
        os.environ["CARGO_BUILD_JOBS"] = "1"
        self.assert_recorded_allowance("1", jobs="1")

    def test_two_cpu_share_with_two_binaries_records_one_each(self):
        os.environ["CARGO_BUILD_JOBS"] = "2"
        self.assert_recorded_allowance("1", jobs="2")

    def test_unset_preference_gets_the_pool_allowance(self):
        os.environ.pop("RUST_TEST_THREADS")
        self.assert_recorded_allowance("2")
        self.assertNotIn("RUST_TEST_THREADS", os.environ)

    def test_floor_division_leaves_the_remainder_unused(self):
        self.assert_recorded_allowance("1", jobs="4")

    def test_measured_default_pool_is_used_before_recording(self):
        os.environ.pop("TRUST_CRATES_TESTS_JOBS")
        with mock.patch.object(self.lane, "default_jobs", return_value=3):
            self.assert_recorded_allowance("2", jobs=None)

    def test_run_alone_retains_the_original_recorded_allowance(self):
        self.lane.RUN_ALONE = {"probe": "fixture"}
        out = self.assert_recorded_allowance("2")
        self.assertIn("running 2 test binaries alone (RUN_ALONE): probe", out)

    def assert_refused_without_build_or_replay(self, name, value, jobs="3"):
        if value is None:
            os.environ.pop(name, None)
        else:
            os.environ[name] = value
        rc, out, calls, recorded, probes = self.run_recorded_probes(jobs)
        self.assertEqual(rc, 2, out)
        self.assertIn(name, out)
        self.assertEqual(calls, [], "invalid managed inputs must start no build")
        self.assertEqual(recorded, [], out)
        self.assertEqual(probes, [], out)

    def test_invalid_managed_cpu_share_refuses_before_build(self):
        for raw in (None, "", "0", "-1", "six", "1.5", " 6", "+6", "６", "9" * 5000):
            with self.subTest(raw=repr(raw)[:40]):
                self.assert_refused_without_build_or_replay("CARGO_BUILD_JOBS", raw)

    def test_invalid_managed_libtest_preference_refuses_before_build(self):
        for raw in ("", "0", "-1", "six", "1.5", " 6", "+6", "６", "9" * 5000):
            with self.subTest(raw=repr(raw)[:40]):
                self.assert_refused_without_build_or_replay("RUST_TEST_THREADS", raw)

    def test_invalid_managed_pool_override_refuses_before_build(self):
        for raw in ("0", "-1", "three", "1.5", " 3", "+3", "３", "9" * 5000):
            with self.subTest(raw=repr(raw)[:40]):
                self.assert_refused_without_build_or_replay("TRUST_CRATES_TESTS_JOBS", raw, jobs=raw)

    def test_pool_override_cannot_exceed_the_admitted_share(self):
        self.assert_refused_without_build_or_replay("TRUST_CRATES_TESTS_JOBS", "7", jobs="7")

    def test_cargo_losing_the_chosen_allowance_refuses_before_replay(self):
        os.environ["FAKE_TARGO_SCRUB"] = "RUST_TEST_THREADS"
        rc, out, calls, recorded, probes = self.run_recorded_probes()
        self.assertEqual(rc, 2, out)
        self.assertIn("recorded RUST_TEST_THREADS differs", out)
        self.assertEqual(len(calls), 1, calls)
        self.assertEqual(len(recorded), 3, out)
        self.assertTrue(all("RUST_TEST_THREADS" not in r["env"] for r in recorded))
        self.assertEqual(probes, [], "a record that lost the allowance must never run")

    def test_unmanaged_environment_and_larger_pool_are_unchanged(self):
        os.environ.pop("BUILD_SLOT_HELD")
        os.environ["CARGO_BUILD_JOBS"] = "not a managed share"
        out = self.assert_recorded_allowance("6", jobs="7")
        self.assertNotIn("managed libtest allowance", out)

    def test_unmanaged_absent_preference_remains_absent(self):
        os.environ.pop("BUILD_SLOT_HELD")
        os.environ.pop("RUST_TEST_THREADS")
        self.assert_recorded_allowance(None)


class TwoTailTest(MainBase):
    """One member with TWO feature tails, as trust-router has had since
    2026-10-01. Each tail builds its own lib executable, and binary_name keys
    them all alike (`gate` here, `trust_router` there), so the lane must judge
    each command on its own binaries."""

    TAILS = {"": "gate-0000000000000000", "ay-backend": "gate-1000000000000000",
             "ay-certify,carcara-crosscheck": "gate-2000000000000000"}

    def setUp(self):
        super().setUp()
        self.lane.FEATURE_RUNS["trust-router"] = [
            ["--features", "ay-backend", "--lib"],
            ["--features", "ay-certify,carcara-crosscheck", "--lib"],
        ]

    def run_tails(self, **override):
        os.environ["FAKE_TARGO_BINARIES_BY_FEATURES"] = json.dumps(dict(self.TAILS, **override))
        return self.run_main("pass")

    def test_each_tail_runs_its_own_executable_once(self):
        rc, out, calls = self.run_tails()
        self.assertEqual(rc, 0, out)
        self.assertEqual(len(calls), 3, calls)
        self.assertIn("3/3 run(s) passed", out)
        self.assertEqual(out.count("test mod_b::fresh ... ok"), 3, out)
        for exe in self.TAILS.values():  # each recorded once, run once from the pool
            self.assertEqual(out.count(f"--- started: {exe}\n"), 1, out)

    def test_a_failure_in_one_tail_fails_that_command_only(self):
        rc, out, _ = self.run_tails(**{"ay-certify,carcara-crosscheck": "gate-00000000000000f0"})
        self.assertEqual(rc, 1, out)
        self.assertIn("NEW FAILURE: gate::mod_a::listed", out)
        self.assertIn("1/3 run(s) FAILED", out)
        failed = [line for line in out.splitlines() if line.startswith("--- FAIL")]
        self.assertEqual(len(failed), 1, out)
        self.assertIn("--features ay-certify,carcara-crosscheck --lib", failed[0])
        self.assertEqual(len([line for line in out.splitlines() if line.startswith("--- PASS")]), 2, out)


class FilteredRunTest(MainBase):
    """A planned command whose tail ends in `-- <filter>`, as each
    CROSS_CRATE_INSTRUMENTS command does, end to end. The fake cargo reads
    `--config` only before `--`, as cargo does, so a record pass that appends
    the runner after the filter (the spelling 7a0197f40a replaced) hands cargo
    no runner and CANNOT JUDGE here as it did on a real push. Before 2026-10-01
    the fake read `--config` anywhere, and no test here could see that."""

    def setUp(self):
        super().setUp()
        self.lane.CROSS_CRATE_INSTRUMENTS[:] = [
            (("crates/trust-router/",), "trust-ir-bridge", ["--lib", "--", "mod_a::"]),
        ]
        self.lane.FEATURE_RUNS.clear()

    def test_the_filtered_command_is_recorded_and_replayed_with_its_filter(self):
        rc, out, calls = self.run_main("probe")
        self.assertEqual(rc, 0, out)
        self.assertNotIn("CANNOT JUDGE", out)
        self.assertEqual(len(calls), 2, calls)
        self.assertTrue(calls[1].endswith("-p trust-ir-bridge --lib -- mod_a::"), calls)
        self.assertIn("2/2 run(s) passed", out)
        probes = [json.loads(line[len("PROBE "):]) for line in out.splitlines() if line.startswith("PROBE ")]
        # The --tests run hands the binary nothing; the filtered run, its filter.
        self.assertEqual(sorted(p["argv"][1:] for p in probes), [[], ["mod_a::"]], out)

    def test_a_runner_after_the_filter_cannot_judge(self):
        # The mutation 7a0197f40a fixed: never a vacuous pass, and caught here.
        self.lane.with_runner_config = lambda cmd, record_dir: cmd + ["--config", self.lane.runner_config(record_dir)]
        rc, out, _ = self.run_main("probe")
        self.assertEqual(rc, 2, out)
        self.assertIn("announced 1 test binaries but handed 0 to the runner", out)


class ZeroTestRuleTest(MainBase):
    """ZERO TESTS IS NOT A PASS (2026-10-09). A touched crate whose runs
    REPORTED no test (passed + failed on libtest's closing line, over the
    default run and its FEATURE_RUNS tails) makes an otherwise green lane exit
    3, NOT JUDGED, naming it. Before the rule, trust-ny-bridge, whose 28 tests
    are all behind `ny`, printed PASS on every push that touched it: its one lib
    binary said `running 0 tests` / `test result: ok. 0 passed` and exited 0.
    The rule is per crate in TOTAL, never per binary."""

    EMPTY = "empty-000000000000000b"
    PASSING = "gate-0000000000000000"

    def setUp(self):
        super().setUp()
        self.lane.FEATURE_RUNS.clear()
        self.lane.CROSS_CRATE_INSTRUMENTS[:] = []
        self.lane.CORPUS_INSTRUMENTS[:] = []
        self.members("zero-member")
        self.lane.changed_paths = lambda ranges: ["crates/zero-member/src/lib.rs"]

    def members(self, *names):
        """The metadata names these synthetic members (crates/<name>), each
        package in the fake cargo's environment: the first by default."""
        packages = [{"id": f"{n}-id", "name": n, "manifest_path": str(REPO_ROOT / "crates" / n / "Cargo.toml")}
                    for n in names]
        Path(os.environ["FAKE_TARGO_METADATA"]).write_text(json.dumps({
            "workspace_members": [p["id"] for p in packages], "workspace_default_members": [p["id"] for p in packages], "packages": packages,
        }), encoding="utf-8")
        os.environ["FAKE_TARGO_PKG_NAME"] = names[0]

    def run_binaries(self, by_features, pkg_by_binary=None):
        os.environ["FAKE_TARGO_BINARIES_BY_FEATURES"] = json.dumps(by_features)
        os.environ["FAKE_TARGO_PKG_BY_BINARY"] = json.dumps(pkg_by_binary or {})
        return self.run_main("pass")

    def test_a_member_whose_only_binary_ran_zero_tests_is_not_judged(self):
        rc, out, calls = self.run_binaries({"": self.EMPTY})
        self.assertEqual(rc, 3, out)
        self.assertEqual(len(calls), 1, calls)
        self.assertIn("running 0 tests", out)  # what the binary said, and libtest's exit 0
        self.assertIn("--- PASS (1 binaries", out)  # the run itself is green ...
        self.assertIn("NO TEST JUDGED: zero-member", out)  # ... and judged nothing
        self.assertIn("NOT JUDGED: 1/1 run(s) exited green", out)
        self.assertIn("reported no test: zero-member.", out)
        self.assertNotIn("run(s) passed", out)

    def test_a_member_with_a_passing_test_is_unaffected(self):
        rc, out, _ = self.run_binaries({"": self.PASSING})
        self.assertEqual(rc, 0, out)
        self.assertIn("tests reported per touched crate (libtest's passed + failed, over all its runs): "
                      "zero-member 2", out)
        self.assertNotIn("NOT JUDGED", out)
        self.assertNotIn("NO TEST JUDGED", out)
        self.assertIn("1/1 run(s) passed", out)

    def test_an_empty_binary_beside_a_real_one_is_not_a_finding(self):
        # Per member, never per binary: a bin target's unit-test binary says
        # `running 0 tests` as a matter of course.
        rc, out, _ = self.run_binaries({"": f"{self.EMPTY},{self.PASSING}"})
        self.assertEqual(rc, 0, out)
        self.assertIn("zero-member 2", out)

    def test_a_feature_tail_that_reports_a_test_judges_the_member(self):
        # trust-ny-bridge's shape once it has its `ny` tail: the default run
        # compiles nothing, the tail compiles the tests. The total counts.
        self.lane.FEATURE_RUNS["zero-member"] = [["--features", "ny", "--lib"]]
        rc, out, calls = self.run_binaries({"": self.EMPTY, "ny": "gate-1000000000000000"})
        self.assertEqual(rc, 0, out)
        self.assertEqual(len(calls), 2, calls)
        self.assertIn("zero-member 2", out)
        # Control: the same tail compiling nothing is still not judged.
        rc, out, _ = self.run_binaries({"": self.EMPTY, "ny": self.EMPTY})
        self.assertEqual(rc, 3, out)
        self.assertIn("NOT JUDGED: 2/2 run(s) exited green", out)

    def test_ignored_tests_judge_nothing(self):
        # `running 1 test`, but libtest's closing line counts 0 passed, 0 failed.
        rc, out, _ = self.run_binaries({"": "ignored-000000000000000c"})
        self.assertEqual(rc, 3, out)
        self.assertIn("NO TEST JUDGED: zero-member", out)

    def test_only_the_empty_member_is_named(self):
        self.members("trust-router", "zero-member")
        self.lane.changed_paths = lambda ranges: ["crates/trust-router/src/lib.rs", "crates/zero-member/src/lib.rs"]
        rc, out, calls = self.run_binaries(
            {"": f"{self.PASSING},{self.EMPTY}"}, {self.PASSING: "trust-router", self.EMPTY: "zero-member"})
        self.assertEqual(rc, 3, out)
        self.assertEqual(calls, ["--unverified test --manifest-path Cargo.toml --locked --no-fail-fast "
                                 "-p trust-router -p zero-member --tests"])
        self.assertIn("trust-router 2, zero-member 0", out)
        self.assertIn("reported no test: zero-member.", out)
        self.assertNotIn("NO TEST JUDGED: trust-router", out)

    def test_a_red_run_stays_red_beside_an_empty_member(self):
        self.members("trust-router", "zero-member")
        self.lane.changed_paths = lambda ranges: ["crates/trust-router/src/lib.rs", "crates/zero-member/src/lib.rs"]
        failing = "gate-00000000000000ff"
        rc, out, _ = self.run_binaries({"": f"{failing},{self.EMPTY}"},
                                       {failing: "trust-router", self.EMPTY: "zero-member"})
        self.assertEqual(rc, 1, out)
        self.assertIn("NEW FAILURE: gate::mod_a::listed", out)
        self.assertIn("NO TEST JUDGED: zero-member", out)  # still said
        self.assertNotIn("NOT JUDGED", out)  # red outranks not judged

    def test_a_record_that_names_no_package_credits_nobody(self):
        # Fail closed: a binary the lane cannot attribute counts for no member.
        os.environ["FAKE_TARGO_SCRUB"] = "CARGO_PKG_NAME"
        rc, out, _ = self.run_binaries({"": self.PASSING})
        self.assertEqual(rc, 3, out)
        self.assertIn("zero-member 0", out)

    def test_an_instrument_run_credits_no_touched_member(self):
        # Its host is not touched (a touched host is in the default run), and
        # its subject is another member's output: its tests are not the member's.
        self.lane.CROSS_CRATE_INSTRUMENTS[:] = [
            (("crates/zero-member/",), "trust-ir-bridge", ["--lib", "--", "mod_b::"]),
        ]
        # Even a binary cargo ran for that member (it never is: the host is
        # another member) counts for nobody when an instrument ran it.
        rc, out, calls = self.run_binaries({"": self.EMPTY, "-- mod_b::": self.PASSING},
                                           {self.PASSING: "zero-member"})
        self.assertEqual(len(calls), 2, calls)
        self.assertIn("test mod_b::fresh ... ok", out)
        self.assertTrue(calls[1].endswith("-p trust-ir-bridge --lib -- mod_b::"), calls)
        self.assertEqual(rc, 3, out)
        self.assertIn("zero-member 0", out)

    def test_an_instrument_run_that_judges_nothing_fails(self):
        # B1A-14a (the M0 review's finding 7): libtest exits 0 on `running 0
        # tests` and on a run of only #[ignore]d tests, and no member is credited
        # for an instrument run, so the run itself must report a test.
        self.lane.CROSS_CRATE_INSTRUMENTS[:] = [
            (("crates/zero-member/",), "trust-ir-bridge", ["--lib", "--", "mod_b::"]),
        ]
        for nothing in (self.EMPTY, "ignored-000000000000000c"):
            rc, out, calls = self.run_binaries({"": self.PASSING, "-- mod_b::": nothing})
            self.assertTrue(calls[-1].endswith("-p trust-ir-bridge --lib -- mod_b::"), calls)
            self.assertEqual(rc, 1, out)
            self.assertIn("INSTRUMENT JUDGED NOTHING (its binaries reported 0 tests (passed + failed): "
                          "its filter matched nothing): ", out)
            self.assertIn("-p trust-ir-bridge --lib -- mod_b::", out)
        rc, out, _ = self.run_binaries({"": self.PASSING, "-- mod_b::": self.PASSING})
        self.assertEqual(rc, 0, out)
        self.assertNotIn("INSTRUMENT JUDGED NOTHING", out)

    def test_the_prelude_digest_instrument_needs_its_own_test(self):
        # The D35 seam's push-time check (B1A-14a): a digest run whose binary
        # reported other tests, but not `tests::digest::source_digest_matches ...
        # ok` (renamed, cfg-gated, ignored), fails.
        self.assertEqual(self.lane.INSTRUMENT_REQUIRED_PASSES,
                         {"trust-model-prelude": ("tests::digest::source_digest_matches",)})
        self.lane.CROSS_CRATE_INSTRUMENTS[:] = [
            (("crates/zero-member/",), "trust-model-prelude", ["--lib", "--", "tests::digest::"]),
        ]
        rc, out, calls = self.run_binaries({"": self.PASSING, "-- tests::digest::": self.PASSING})
        self.assertTrue(calls[1].endswith("-p trust-model-prelude --lib -- tests::digest::"), calls)
        self.assertEqual(rc, 1, out)
        self.assertIn("`test tests::digest::source_digest_matches ... ok` is not in its output", out)
        rc, out, _ = self.run_binaries({"": self.PASSING, "-- tests::digest::": self.EMPTY})
        self.assertEqual(rc, 1, out)
        rc, out, _ = self.run_binaries({"": self.PASSING, "-- tests::digest::": "digest-000000000000000d"})
        self.assertEqual(rc, 0, out)
        self.assertIn("test tests::digest::source_digest_matches ... ok", out)

    def test_an_instrument_only_push_names_no_crate(self):
        # A push that moves only an instrument's subject outside crates/ touches
        # no crate: the per-crate line is not printed with an empty list.
        self.lane.CROSS_CRATE_INSTRUMENTS[:] = [
            (("tests/js262/",), "trust-ir-bridge", ["--lib", "--", "mod_b::"]),
        ]
        self.lane.changed_paths = lambda ranges: ["tests/js262/case.js"]
        rc, out, calls = self.run_binaries({"-- mod_b::": self.PASSING})
        self.assertEqual(len(calls), 1, calls)
        self.assertTrue(calls[0].endswith("-p trust-ir-bridge --lib -- mod_b::"), calls)
        self.assertEqual(rc, 0, out)
        self.assertNotIn("tests reported per touched crate", out)
        self.assertIn("1/1 run(s) passed", out)

    def test_an_own_workspace_crate_that_reports_no_test_is_not_judged(self):
        self.lane.changed_paths = lambda ranges: ["crates/trust-spec-temporal/src/lib.rs"]
        rc, out, calls = self.run_binaries({"": self.EMPTY})
        self.assertEqual(calls, ["--unverified test --manifest-path crates/trust-spec-temporal/Cargo.toml "
                                 "--locked --no-fail-fast --tests"])
        self.assertEqual(rc, 3, out)
        self.assertIn("reported no test: crates/trust-spec-temporal.", out)
        rc, out, _ = self.run_binaries({"": self.PASSING})
        self.assertEqual(rc, 0, out)
        self.assertIn("crates/trust-spec-temporal 2", out)

    def test_reported_tests_reads_what_each_binary_said(self):
        def binary(output, rc=0):
            b = self.lane.Binary({"argv": ["x"], "cwd": ".", "env": {}}, "     Running x (x)")
            b.output, b.rc = output, rc
            return b
        closing = "test result: {}. {} passed; {} failed; 3 ignored; 0 measured; 5 filtered out; finished in 0.1s\n"
        self.assertEqual(self.lane.reported_tests(binary("running 0 tests\n\n" + closing.format("ok", 0, 0))), 0)
        self.assertEqual(self.lane.reported_tests(binary("running 9 tests\n" + closing.format("FAILED", 4, 2), 101)), 6)
        # A libtest run that never closed reports nothing (binary_problem fails it).
        self.assertEqual(self.lane.reported_tests(binary("running 2 tests\ntest a ... ok\n", None)), 0)
        # A `harness = false` binary is one test: its exit code is the verdict.
        self.assertEqual(self.lane.reported_tests(binary("conformance: 412 steps agree\n")), 1)
        # The binary's own closing line counts, not a child's echoed before it.
        self.assertEqual(self.lane.reported_tests(binary(
            "running 1 test\n" + closing.format("ok", 7, 0) + "test outer ... ok\n\n" + closing.format("ok", 1, 0))), 1)


class BarrierTest(MainBase):
    """TRUST_CRATES_TESTS_RUN_AFTER (2026-09-30): the lane builds, then waits for
    the barrier before any test binary starts; the wait is printed and is not
    charged to the budget; only `run` runs; a stop, an owner that is gone, or
    no barrier within the bound is NOT JUDGED with no binary run. Unset, the
    lane never mentions a barrier. scripts/tests/pre_push_overlap_scoped_test.sh
    holds the hook's side."""

    def setUp(self):
        super().setUp()
        self.stamps = Path(self.tmp.name) / "stamps"
        self.stamps.mkdir()
        os.environ["FAKE_STAMP_DIR"] = str(self.stamps)
        self.barrier = Path(self.tmp.name) / "barrier"
        self.released_at = None
        self.built_at_release = None

    def release_later(self, delay, text="run"):
        """Write the barrier whole after `delay` s, as the hook does (rename)."""
        def write():
            self.built_at_release = len(self.log.read_text().splitlines()) if self.log.exists() else 0
            part = self.barrier.with_suffix(".part")
            part.write_text(text + "\n", encoding="utf-8")
            self.released_at = time.time()
            part.rename(self.barrier)
        timer = threading.Timer(delay, write)
        timer.start()
        self.addCleanup(timer.cancel)
        return timer

    def release_at_the_wait(self):
        """Release only after both real record passes reach the real waiter.

        Starting a timer before main() races metadata and process startup: it
        can publish the barrier before either build has started on a busy host.
        The short timer publishes the barrier asynchronously; no assertion
        depends on how long building or thread scheduling takes.
        """
        wait = self.lane.wait_for_barrier

        def synchronized_wait(*args):
            self.assertEqual(len(self.log.read_text().splitlines()), 2,
                             "both commands must finish recording before the wait")
            self.assertEqual(self.stamped(), [], "no binary may start before the wait")
            timer = self.release_later(0.1)
            try:
                return wait(*args)
            finally:
                timer.cancel()
                timer.join()

        self.lane.wait_for_barrier = synchronized_wait

    def stamped(self):
        return [float(p.read_text()) for p in self.stamps.iterdir()]

    def test_without_the_variable_the_lane_is_unchanged(self):
        os.environ.pop("TRUST_CRATES_TESTS_RUN_AFTER", None)
        with mock.patch.object(self.lane, "wait_for_barrier") as wait:
            rc, out, _ = self.run_main("stamp")
        wait.assert_not_called()
        self.assertEqual(rc, 0, out)
        # Warnings can quote a checkout path containing "barrier". Observe the
        # protocol messages and the real wait call, not arbitrary path bytes.
        self.assertNotRegex(out, r"(?m)^(?:waiting for the barrier|crates-tests:.*\bbarrier\b|"
                                 r"NOT JUDGED: the barrier)")
        self.assertEqual(len(self.stamped()), 2, out)

    def test_no_test_binary_starts_before_the_barrier(self):
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER"] = str(self.barrier)
        self.release_at_the_wait()
        rc, out, _ = self.run_main("stamp")
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.built_at_release, 2, "both commands build before the barrier")
        stamps = self.stamped()
        self.assertEqual(len(stamps), 2, out)
        self.assertTrue(all(t >= self.released_at for t in stamps),
                        f"a binary started before the barrier: {stamps} < {self.released_at}")
        self.assertRegex(out, r"crates-tests: waited [0-9]+s at the barrier \(it says 'run'\), "
                              r"not charged to the 60s budget")
        self.assertRegex(out, r"run\(s\) passed in [0-9]+s \(and [0-9]+s waiting at the barrier\)")

    def test_the_wait_is_not_charged_to_the_budget(self):
        # Keep actual metadata, record passes and stamped binary execution, with
        # the fixture's normal 60 s watchdog. Add 65 s only to this lane's clock
        # during the barrier: charging that wait must exhaust even the whole
        # budget. A fixed offset after the wait leaves every real subprocess's
        # remaining timeout unchanged iff main credits exactly the reported wait.
        # Patching the module binding avoids changing the shared time module.
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER"] = str(self.barrier)
        self.release_at_the_wait()
        clock = mock.Mock(wraps=time)
        offset = 0.0
        clock.monotonic.side_effect = lambda: time.monotonic() + offset
        deadlines = []
        ceilings = []
        reported_wait = []
        pool_deadlines = []
        build, wait, run = (self.lane.run_with_deadline, self.lane.wait_for_barrier,
                            self.lane.run_binaries)

        def record(cmd, deadline, env=None):
            deadlines.append(deadline)
            ceilings.append(deadline._ceiling_at)
            return build(cmd, deadline, env)

        def advance_at_the_barrier(*args):
            nonlocal offset
            go, waited, why = wait(*args)
            self.assertTrue(go, why)
            offset += 65.0
            reported_wait.append(waited + 65.0)
            return go, reported_wait[-1], why

        def run_with_the_exact_credit(binaries, jobs, deadline):
            self.assertEqual(len(deadlines), 2)
            self.assertIs(deadlines[0], deadlines[1])
            self.assertEqual(ceilings[0], ceilings[1])
            self.assertEqual(len(reported_wait), 1)
            self.assertIs(deadline, deadlines[0], "the lane has one bound")
            self.assertEqual(deadline._ceiling_at, ceilings[0] + reported_wait[0],
                             "only the actual reported wait may extend the original ceiling")
            pool_deadlines.append(deadline)
            return run(binaries, jobs, deadline)

        with mock.patch.object(self.lane, "time", clock), \
                mock.patch.object(self.lane, "run_with_deadline", record), \
                mock.patch.object(self.lane, "wait_for_barrier", advance_at_the_barrier), \
                mock.patch.object(self.lane, "run_binaries", run_with_the_exact_credit):
            rc, out, _ = self.run_main("stamp")
        self.assertEqual(rc, 0, out)
        self.assertNotIn("NOT JUDGED", out)
        self.assertEqual(len(pool_deadlines), 1, out)
        self.assertGreater(reported_wait[0], 60, out)
        self.assertEqual(self.built_at_release, 2, out)
        self.assertEqual(len(self.stamped()), 2, out)

    def test_the_wait_is_credited_exactly_never_more(self):
        # The other bound: the deadline moves by the wait and no further. Budget
        # 8 s, barrier after 3 s, a binary that sleeps 60 s: credited exactly,
        # the deadline kills it about 8 s after the lane started its own work
        # (~11 s wall), NOT JUDGED; over-credited, it would run on (or pass).
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER"] = str(self.barrier)
        self.release_later(3.0)
        t0 = time.monotonic()
        rc, out, _ = self.run_main("hang", budget="8")
        elapsed = time.monotonic() - t0
        self.assertEqual(rc, 3, out)
        self.assertIn("NOT JUDGED", out)
        # 3 s wait + 8 s budget + the kill's grace and slack; a minute of
        # credit (or an hour) would let the 60 s sleeper run far past this.
        self.assertLess(elapsed, 3 + 8 + 25, out)

    def test_a_stop_runs_no_binary(self):
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER"] = str(self.barrier)
        self.release_later(0.5, "stop")
        rc, out, _ = self.run_main("stamp")
        self.assertEqual(rc, 3, out)
        self.assertIn("NOT JUDGED: the barrier did not say `run`", out)
        self.assertIn("built, not run:", out)
        self.assertEqual(self.stamped(), [], out)

    def test_an_owner_that_is_gone_ends_the_wait(self):
        gone = subprocess.Popen(["true"])
        gone.wait()
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER"] = str(self.barrier)
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER_OWNER"] = str(gone.pid)
        # Bounded, so a lane that ignores its owner fails here in 30 s rather
        # than hanging the suite for DEFAULT_RUN_AFTER_MAX_S (4 h).
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER_MAX_S"] = "30"
        t0 = time.monotonic()
        rc, out, _ = self.run_main("stamp")
        self.assertLess(time.monotonic() - t0, 20)
        self.assertEqual(rc, 3, out)
        self.assertIn(f"pid {gone.pid}, which was to release it, is gone", out)
        self.assertEqual(self.stamped(), [], out)

    def test_a_live_owner_keeps_the_wait(self):
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER"] = str(self.barrier)
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER_OWNER"] = str(os.getpid())
        self.release_later(1.0)
        rc, out, _ = self.run_main("stamp")
        self.assertEqual(rc, 0, out)
        self.assertEqual(len(self.stamped()), 2, out)

    def test_a_barrier_that_never_comes_is_bounded(self):
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER"] = str(self.barrier)
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER_MAX_S"] = "1"
        rc, out, _ = self.run_main("stamp")
        self.assertEqual(rc, 3, out)
        self.assertIn("it did not appear within TRUST_CRATES_TESTS_RUN_AFTER_MAX_S=1s", out)
        self.assertEqual(self.stamped(), [], out)

    def test_a_build_out_of_budget_never_reaches_the_barrier(self):
        # The budget still bounds the lane's own work: only the wait is free.
        os.environ["TRUST_CRATES_TESTS_RUN_AFTER"] = str(self.barrier)
        rc, out, _ = self.run_main("sleep", budget="1")
        self.assertEqual(rc, 3, out)
        self.assertNotIn("waiting for the barrier", out)


# Runs the lane in a process of its own (signal handlers are per process), with
# the fake targo on PATH and a fixed changed-path set.
LANE_DRIVER = """
import importlib.util, sys
spec = importlib.util.spec_from_file_location("lane", sys.argv[1])
lane = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lane)
lane.changed_paths = lambda ranges: ["crates/trust-router/src/lib.rs"]
sys.exit(lane.main(["--range", "origin/main..HEAD"]))
"""


def _signals_at_default():
    """Start the lane as an interactive shell would: INT, TERM and HUP at their
    default disposition. A shell runs an asynchronous command with INT ignored,
    and the lane leaves an inherited ignore in place on purpose
    (`forwarding_signals`). Without this, a run of this selftest from a
    background job (a `git push` started with `&`, whose hook runs this lane)
    sent INT to a lane that could not receive it, and the test timed out. The
    tests are about the lane's forwarding, not about the disposition its parent
    handed it."""
    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, signal.SIG_DFL)


# This suite's own INT and HUP as it started: Python's KeyboardInterrupt handler
# and the default, or SIG_IGN when it inherited them ignored.
_SUITE_SIGNALS = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGHUP)}


class InterruptTest(MainBase):
    """An INT, TERM or HUP to the lane reaches the process groups it started
    (cargo's, each test binary's: sessions of their own), and the lane exits
    128+signal, NOT JUDGED, leaving nothing running."""

    def start_lane(self, mode, inherit_signals=False, **env):
        """The lane, with INT, TERM and HUP at their defaults; with
        inherit_signals, with this suite's own (an ignored one stays ignored
        across the exec)."""
        os.environ["FAKE_TARGO_BUILD"], binaries = MODES[mode]
        os.environ["FAKE_TARGO_BINARIES"] = ",".join(binaries)
        os.environ["TRUST_CRATES_TESTS_BUDGET_S"] = "120"
        os.environ.update(env)
        proc = subprocess.Popen([sys.executable, "-c", LANE_DRIVER, str(SCRIPT)],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                preexec_fn=None if inherit_signals else _signals_at_default)
        self.addCleanup(lambda: proc.poll() is None and proc.kill())
        return proc

    @staticmethod
    def wait_for(path, seconds=60):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            if path.exists() and path.read_text().strip():
                return True
            time.sleep(0.05)
        return False

    def test_an_interrupt_during_the_build_leaves_nothing_running(self):
        for sig in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(sig=sig.name):
                pidfile = Path(self.tmp.name) / f"build-{sig.name}.pid"
                proc = self.start_lane("sleep", FAKE_TARGO_PIDFILE=str(pidfile))
                self.assertTrue(self.wait_for(pidfile), "the build never started")
                build = int(pidfile.read_text())
                proc.send_signal(sig)
                out, _ = proc.communicate(timeout=30)
                self.assertEqual(proc.returncode, 128 + sig, out)
                self.assertIn(f"interrupted ({sig.name})", out)
                with self.assertRaises(ProcessLookupError, msg=f"the build {build} outlived the lane"):
                    os.kill(build, 0)

    def test_an_interrupt_at_the_barrier_ends_the_wait(self):
        stamps = Path(self.tmp.name) / "stamps"
        stamps.mkdir()
        barrier = Path(self.tmp.name) / "barrier"
        proc = self.start_lane("stamp", FAKE_STAMP_DIR=str(stamps), TRUST_CRATES_TESTS_RUN_AFTER=str(barrier))
        assert proc.stdout is not None
        for line in proc.stdout:
            if line.startswith("waiting for the barrier"):
                break
        proc.send_signal(signal.SIGTERM)
        out, _ = proc.communicate(timeout=30)
        self.assertEqual(proc.returncode, 128 + signal.SIGTERM, out)
        self.assertEqual(list(stamps.iterdir()), [], "a binary ran")

    def test_an_interrupt_while_binaries_run_leaves_none_running(self):
        # The sleeper records its pid in a directory of this test's own, so a
        # sleeper another run of this suite left on the host is never counted.
        pids = Path(self.tmp.name) / "sleepers"
        pids.mkdir()
        proc = self.start_lane("hang", FAKE_SLEEPER_PIDS=str(pids))
        assert proc.stdout is not None
        for line in proc.stdout:
            if "--- started: sleeper-0000000000000005" in line:
                break
        deadline = time.monotonic() + 30
        while not list(pids.iterdir()) and time.monotonic() < deadline:
            time.sleep(0.05)
        time.sleep(0.2)
        sleepers = [int(p.name) for p in pids.iterdir()]
        self.assertTrue(sleepers, "the sleeper binary never started")
        proc.send_signal(signal.SIGINT)
        out, _ = proc.communicate(timeout=30)
        self.assertEqual(proc.returncode, 128 + signal.SIGINT, out)
        for pid in sleepers:
            with self.assertRaises(ProcessLookupError, msg=f"test binary {pid} outlived the lane"):
                os.kill(pid, 0)


class InheritsIgnoredInterrupts:
    """Mixin: each lane starts from this suite with its INT and HUP ignored, as a
    suite run from a background job (bash ignores INT in `... &` without job
    control: a pre-push started with `&`) or under nohup (HUP) has them; what it
    forks inherits them in turn, across exec.

    Ignored across the start only, then put back: held for the whole test, the
    ignore made the suite itself swallow a Ctrl-C, or the one SIGINT the
    pre-push hook's interrupt_lanes sends a lane it stops, and run on to OK
    (review of 2026-10-02: rc 0 after a group INT, where InterruptTest stopped
    with 130 at once). An INT that lands inside the start itself, a fork and
    an exec, is still dropped."""

    def start_lane(self, *args, **kwargs):
        held = [(sig, signal.signal(sig, signal.SIG_IGN)) for sig in (signal.SIGINT, signal.SIGHUP)]
        try:
            return super().start_lane(*args, **kwargs)
        finally:
            for sig, handler in held:
                signal.signal(sig, handler)


class InheritedIgnoredInterruptTest(InheritsIgnoredInterrupts, InterruptTest):
    """InterruptTest's cases again, each lane started while this suite's INT and
    HUP are ignored: each interrupt still reaches the lane, which start_lane
    starts with the defaults (_signals_at_default). Before 3a6a97cf07 the INT
    cases timed out in such a suite, the lane having inherited INT ignored,
    and fast.crates-tests-scoped-selftest was red for every pre-push run from
    a background job; nothing in a foreground run showed it. These cases do.

    And the lane's own side (forwarding_signals): a lane that inherits INT
    ignored keeps it ignored, as POSIX keeps a background job's, and TERM still
    stops it with nothing left running. That is why start_lane must hand it the
    defaults, and the control that INT really is ignored here."""

    def test_the_suite_itself_stays_interruptible(self):
        # The ignore is the lane start's alone: before it and after it this
        # suite has the INT and HUP it started with, so a Ctrl-C still stops it.
        def own():
            return {sig: signal.getsignal(sig) for sig in _SUITE_SIGNALS}

        self.assertEqual(own(), _SUITE_SIGNALS, "this test began with INT or HUP changed")
        pidfile = Path(self.tmp.name) / "build.pid"
        proc = self.start_lane("sleep", FAKE_TARGO_PIDFILE=str(pidfile))
        self.assertEqual(own(), _SUITE_SIGNALS, "starting the lane left INT or HUP changed")
        self.assertTrue(self.wait_for(pidfile), "the build never started")
        proc.send_signal(signal.SIGTERM)
        out, _ = proc.communicate(timeout=30)
        self.assertEqual(proc.returncode, 128 + signal.SIGTERM, out)

    def test_a_lane_that_inherits_int_ignored_drops_it(self):
        # At the barrier the lane has nothing running: an INT it handled would
        # end it at once (130, no binary run). Dropped, the lane goes on to run
        # its binaries (one per command it planned: how many is the real
        # FEATURE_RUNS table's business, so it is counted, not assumed) once
        # the barrier says `run`, and passes.
        # This suite is the barrier's owner, as the hook is a real lane's: an
        # interrupted suite runs no cleanup, and this lane outlives the INT, so
        # without an owner it waited out the default bound (4 h) for a barrier
        # nobody would write. With one it stops once this suite is gone.
        stamps = Path(self.tmp.name) / "stamps"
        stamps.mkdir()
        barrier = Path(self.tmp.name) / "barrier"
        proc = self.start_lane("stamp", inherit_signals=True, FAKE_STAMP_DIR=str(stamps),
                               TRUST_CRATES_TESTS_RUN_AFTER=str(barrier),
                               TRUST_CRATES_TESTS_RUN_AFTER_OWNER=str(os.getpid()))
        assert proc.stdout is not None
        seen = []
        for line in proc.stdout:
            seen.append(line)
            if line.startswith("waiting for the barrier"):
                break
        self.assertTrue(seen and seen[-1].startswith("waiting for the barrier"), "".join(seen))
        proc.send_signal(signal.SIGINT)
        time.sleep(0.5)
        self.assertIsNone(proc.poll(), "the lane ended on an INT it inherited ignored")
        part = barrier.with_suffix(".part")
        part.write_text("run\n", encoding="utf-8")
        part.rename(barrier)
        out, _ = proc.communicate(timeout=60)
        out = "".join(seen) + out
        self.assertEqual(proc.returncode, 0, out)
        self.assertNotIn("interrupted", out)
        planned = sum(line.startswith("building and recording: ") for line in out.splitlines())
        self.assertGreater(planned, 0, out)
        self.assertIn(f"{planned}/{planned} run(s) passed", out)
        self.assertEqual(len(list(stamps.iterdir())), planned, out)

    def test_a_lane_that_inherits_int_ignored_still_stops_on_term(self):
        pidfile = Path(self.tmp.name) / "build.pid"
        proc = self.start_lane("sleep", inherit_signals=True, FAKE_TARGO_PIDFILE=str(pidfile))
        self.assertTrue(self.wait_for(pidfile), "the build never started")
        build = int(pidfile.read_text())
        proc.send_signal(signal.SIGTERM)
        out, _ = proc.communicate(timeout=30)
        self.assertEqual(proc.returncode, 128 + signal.SIGTERM, out)
        self.assertIn("interrupted (SIGTERM)", out)
        with self.assertRaises(ProcessLookupError, msg=f"the build {build} outlived the lane"):
            os.kill(build, 0)


# A signal that arrives after a process was forked but before the lane tracked
# it: Popen is wrapped so that it sends the lane SIGTERM right after the fork
# (and, in a pool thread, dawdles a second before returning, as a GIL switch
# can). The process it started ("sleep 30", a session of its own) must still be
# reached: the lane exits 143 and leaves nothing running.
RACE_DRIVER = """
import importlib.util, os, signal, subprocess, sys, threading, time
spec = importlib.util.spec_from_file_location("lane", sys.argv[1])
lane = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lane)
pidfile, where = sys.argv[2], sys.argv[3]
real = subprocess.Popen
class Racing(real):
    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        with open(pidfile, "w") as fh:
            fh.write(str(self.pid))
        os.kill(os.getpid(), signal.SIGTERM)
        if where == "pool":
            time.sleep(1.0)
subprocess.Popen = Racing
deadline = time.monotonic() + 60
with lane.forwarding_signals():
    if where == "main":
        lane.run_with_deadline(["sleep", "30"], deadline)
    else:
        binary = lane.Binary({"argv": ["sleep", "30"], "cwd": "/", "env": dict(os.environ)}, "sleep")
        worker = threading.Thread(target=lane.run_one, args=(binary, deadline))
        worker.start()
        worker.join()
sys.exit(0)
"""


class SpawnRaceTest(unittest.TestCase):
    def test_a_signal_between_fork_and_tracking_still_reaches_the_child(self):
        for where in ("main", "pool"):
            with self.subTest(where=where), tempfile.TemporaryDirectory() as tmp:
                pidfile = Path(tmp) / "child.pid"
                proc = subprocess.run([sys.executable, "-c", RACE_DRIVER, str(SCRIPT), str(pidfile), where],
                                      capture_output=True, text=True, timeout=60)
                out = proc.stdout + proc.stderr
                self.assertTrue(pidfile.exists(), out)
                child = int(pidfile.read_text())
                try:
                    time.sleep(0.2)
                    self.assertEqual(proc.returncode, 128 + signal.SIGTERM, out)
                    with self.assertRaises(ProcessLookupError, msg=f"{where}: child {child} outlived the lane"):
                        os.kill(child, 0)
                finally:
                    with contextlib.suppress(ProcessLookupError, PermissionError):
                        os.killpg(child, signal.SIGKILL)



# Every real group signal in this driver first proves the leader is still our
# waitable direct child. A missing reservation is recorded, and the dangerous
# signal is withheld: these tests demonstrate ordering, never actual PID reuse.
SIGNAL_CUSTODY_DRIVER = r"""
import importlib.util, json, os, signal, subprocess, sys, threading, time
from pathlib import Path
spec = importlib.util.spec_from_file_location("lane", sys.argv[1])
lane = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lane)
mode, directory = sys.argv[2], Path(sys.argv[3])
for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
    signal.signal(sig, lane._forward_and_exit)
real_killpg = os.killpg
first = True

def observed_signal(pgid, sig):
    global first
    if first and mode == "signal-race":
        first = False
        # Stop the child while the signal caller owns its observation-to-send
        # critical section, and give a concurrent normal waiter time to run.
        os.waitid(os.P_PID, pgid, os.WEXITED | os.WNOWAIT | os.WNOHANG)
        real_killpg(pgid, signal.SIGTERM)
        time.sleep(.1)
    try:
        os.waitid(os.P_PID, pgid, os.WEXITED | os.WNOWAIT | os.WNOHANG)
        reserved = True
    except ChildProcessError:
        reserved = False
    with (directory / "signals").open("a") as out:
        out.write(json.dumps([pgid, sig, reserved]) + "\n")
    if reserved:
        real_killpg(pgid, sig)

lane.os.killpg = observed_signal
lane.KILL_GRACE_S = .15
ready = directory / "ready"
child = ("import signal,time; from pathlib import Path; "
         + ("signal.signal(signal.SIGTERM,signal.SIG_IGN); " if mode == "repeated" else "")
         + "Path(" + repr(str(ready)) + ").write_text('ready'); time.sleep(8)")
if mode in ("descendant", "timeout-descendant"):
    grand_ready = directory / "grand-ready"
    grand = ("import signal,time; from pathlib import Path; "
             "signal.signal(signal.SIGTERM,signal.SIG_IGN); "
             "Path(" + repr(str(grand_ready)) + ").write_text('ready'); time.sleep(3)")
    child = ("import subprocess,sys,time; from pathlib import Path; "
             "p=subprocess.Popen([sys.executable,'-c'," + repr(grand) + "]); "
             "Path(" + repr(str(directory / "grand-pid")) + ").write_text(str(p.pid)); "
             "exec(" + repr("while not Path(" + repr(str(grand_ready)) + ").exists(): time.sleep(.01)") + "); "
             "Path(" + repr(str(ready)) + ").write_text('ready'); time.sleep(8)")
proc = lane._spawn([sys.executable, "-c", child],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
(directory / "pid").write_text(str(proc.pid))
limit = time.monotonic() + 5
while not ready.exists():
    assert time.monotonic() < limit, "child never started"
    time.sleep(.01)
wait = getattr(lane, "_wait", lambda proc, timeout: proc.wait(timeout=timeout))
if mode in ("retired", "worker-race", "main-reap"):
    observed_signal(proc.pid, signal.SIGTERM)
    if mode == "worker-race":
        consumed, release = threading.Event(), threading.Event()
        real_wait = proc.wait
        def paused_wait(*args, **kwargs):
            result = real_wait(*args, **kwargs)
            consumed.set()
            assert release.wait(2), "retirement release never arrived"
            return result
        proc.wait = paused_wait
        worker = threading.Thread(target=lambda: wait(proc, timeout=5))
        worker.start()
        assert consumed.wait(5), "worker never reaped"
        threading.Timer(.1, release.set).start()
    elif mode == "main-reap":
        real_wait = proc.wait
        def interrupted_wait(*args, **kwargs):
            result = real_wait(*args, **kwargs)
            os.kill(os.getpid(), signal.SIGTERM)
            return result
        proc.wait = interrupted_wait
        wait(proc, timeout=5)
    else:
        wait(proc, timeout=5)
elif mode in ("live-worker", "signal-race"):
    started = threading.Event()
    def worker_wait():
        started.set()
        wait(proc, timeout=5)
    threading.Thread(target=worker_wait).start()
    assert started.wait(2)
if mode == "timeout-descendant":
    lane._kill_group(proc)
    raise SystemExit(0)
if mode == "repeated":
    real_sleep = time.sleep
    interrupted = False
    def interrupt_during_grace(seconds):
        global interrupted
        if not interrupted and lane._STOPPING.is_set():
            interrupted = True
            os.kill(os.getpid(), signal.SIGINT)
        real_sleep(seconds)
    lane.time.sleep = interrupt_during_grace
with lane.forwarding_signals():
    lane._forward_and_exit(signal.SIGTERM, None)
"""


class SignalCustodyTest(unittest.TestCase):
    def assert_reserved_cancellation(self, mode):
        with tempfile.TemporaryDirectory() as tmp:
            proc = subprocess.run(
                [sys.executable, "-c", SIGNAL_CUSTODY_DRIVER, str(SCRIPT), mode, tmp],
                capture_output=True, text=True, timeout=20, preexec_fn=_signals_at_default,
            )
            out = proc.stdout + proc.stderr
            events = [json.loads(line) for line in (Path(tmp) / "signals").read_text().splitlines()]
            pid = int((Path(tmp) / "pid").read_text())
            grand_file = Path(tmp) / "grand-pid"
            if grand_file.exists():
                grand = int(grand_file.read_text())
                def exists():
                    try:
                        os.kill(grand, 0)
                        return True
                    except ProcessLookupError:
                        return False
                limit = time.monotonic() + 1
                while exists() and time.monotonic() < limit:
                    time.sleep(.01)
                survived_cleanup = exists()
                # A broken candidate is never cleaned by an unpinned signal:
                # this fixture descendant has its own short natural lifetime.
                limit = time.monotonic() + 5
                while exists() and time.monotonic() < limit:
                    time.sleep(.02)
                self.assertFalse(exists(), "fixture descendant did not naturally close")
                self.assertFalse(survived_cleanup, "TERM-ignoring descendant outlived cancellation")
            self.assertEqual(proc.returncode, 0 if mode == "timeout-descendant" else 128 + signal.SIGTERM, out)
            if mode != "timeout-descendant":
                self.assertIn("NOT JUDGED", out)
            self.assertTrue(events, out)
            self.assertTrue(all(reserved for _pid, _sig, reserved in events), events)
            self.assertTrue(any(sig == signal.SIGTERM for _pid, sig, _reserved in events), events)
            if mode in ("repeated", "timeout-descendant"):
                self.assertEqual([sig for _pid, sig, _reserved in events],
                                 [signal.SIGTERM, signal.SIGKILL], events)
            with self.assertRaises(ProcessLookupError, msg=f"owned child {pid} survived: {out}"):
                os.kill(pid, 0)

    def test_cancellation_finishes_group_signals_before_reaping(self):
        self.assert_reserved_cancellation("handler")

    def test_a_worker_retired_before_untrack_cannot_be_signalled(self):
        self.assert_reserved_cancellation("retired")

    def test_cancellation_serializes_with_worker_wait_return(self):
        self.assert_reserved_cancellation("worker-race")

    def test_a_signal_during_main_thread_reap_is_deferred_until_retirement(self):
        self.assert_reserved_cancellation("main-reap")

    def test_live_worker_cannot_reap_cancellation_owned_pin(self):
        self.assert_reserved_cancellation("live-worker")

    def test_worker_cannot_reap_between_identity_observation_and_signal(self):
        self.assert_reserved_cancellation("signal-race")

    def test_terminal_leader_stays_pinned_until_ignoring_descendant_is_killed(self):
        self.assert_reserved_cancellation("descendant")

    def test_normal_timeout_keeps_pin_until_ignoring_descendant_is_killed(self):
        self.assert_reserved_cancellation("timeout-descendant")

    def test_a_second_signal_cannot_reenter_cleanup(self):
        self.assert_reserved_cancellation("repeated")

    def test_admission_observes_exit_without_reaping_before_group_signal(self):
        lane = load_lane()
        with tempfile.TemporaryDirectory() as tmp:
            real_spawn = lane._spawn
            calls = []
            real_killpg = os.killpg
            def spawn(*args, **kwargs):
                proc = real_spawn(["/bin/sh", "-c", "exit 7"], **kwargs)
                # Deliberately observe a completed but unreaped real child.
                limit = time.monotonic() + 5
                while os.waitid(os.P_PID, proc.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT) is None:
                    self.assertLess(time.monotonic(), limit)
                    time.sleep(.01)
                return proc
            def checked_signal(pid, sig):
                try:
                    os.waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
                    reserved = True
                except ChildProcessError:
                    reserved = False
                calls.append(reserved)
                if reserved:
                    real_killpg(pid, sig)
            with mock.patch.object(lane, "_spawn", spawn), mock.patch.object(lane.os, "killpg", checked_signal):
                outcome, why = lane._probe("unused", dict(os.environ), tmp, "absent-fifo", time.monotonic() + 5)
            self.assertEqual(outcome, "misbehaved", why)
            self.assertTrue(calls, why)
            self.assertTrue(all(calls), calls)
            self.assertEqual(lane._LIVE, set())

    def test_nondefault_sigchld_refuses_before_spawning(self):
        lane = load_lane()
        saved = signal.getsignal(signal.SIGCHLD)
        try:
            signal.signal(signal.SIGCHLD, lambda *_: None)
            with mock.patch.object(lane.subprocess, "Popen") as spawn:
                with self.assertRaisesRegex(OSError, "default SIGCHLD"):
                    lane._spawn(["unused"])
                spawn.assert_not_called()
        finally:
            signal.signal(signal.SIGCHLD, saved)


class TargoTrustPrebuildTest(unittest.TestCase):
    """main() end to end for a touched TARGO_TRUST_CONSUMERS member: MainTest's
    fake `targo`, which also answers the prebuild with cargo's JSON messages."""

    BUILD = ("--unverified build --manifest-path targo-trust/Cargo.toml --bin targo-trust "
             "--locked --message-format json-render-diagnostics")

    def setUp(self):
        self.case = MainTest("test_green_runs_both_router_lanes")
        self.case.setUp()
        self.case.lane.changed_paths = lambda ranges: [
            "crates/trust-integration-tests/tests/binary_to_trust_ir_e2e.rs"]
        tmp = Path(self.case.tmp.name)
        manifest = str(REPO_ROOT / "crates" / "trust-integration-tests" / "Cargo.toml")
        (tmp / "meta.json").write_text(json.dumps({
            "workspace_members": ["it-id"], "workspace_default_members": ["it-id"],
            "packages": [{"id": "it-id", "name": "trust-integration-tests", "manifest_path": manifest}],
        }), encoding="utf-8")
        # Where the fake cargo "links" targo-trust: the shared target dir's file.
        self.built = tmp / "target" / "debug" / "targo-trust"
        self.built.parent.mkdir(parents=True)
        self.built.write_text("built from this tree\n", encoding="utf-8")
        os.environ.update(FAKE_TARGO_TRUST_EXE=str(self.built), FAKE_TARGO_PKG_NAME="trust-integration-tests")

    def tearDown(self):
        self.case.tearDown()

    def test_the_tests_run_a_private_copy_of_what_cargo_built(self):
        # A stale value in the lane's environment is replaced, and a sibling
        # build that relinks the target dir's file after the prebuild (the
        # record pass, here) does not reach the tests.
        os.environ["TRUST_TARGO_TRUST_BIN"] = "/stale/target/debug/targo-trust"
        # The artifact message remains authoritative even with a shared target
        # default: a target/profile/config can place the actual binary elsewhere.
        os.environ["CARGO_TARGET_DIR"] = str(Path(self.case.tmp.name) / "other-shared-target")
        os.environ["FAKE_TARGO_RELINK"] = "1"
        rc, out, calls = self.case.run_main("ttprobe")
        self.assertEqual(rc, 0, out)
        self.assertEqual(calls[0], self.BUILD, calls)
        self.assertEqual(len(calls), 2, calls)
        self.assertTrue(calls[1].startswith("--unverified test "), calls)
        probes = [json.loads(line[len("TTPROBE "):]) for line in out.splitlines() if line.startswith("TTPROBE ")]
        self.assertEqual(len(probes), 1, out)
        handed = Path(probes[0]["path"])
        self.assertEqual(handed.name, "targo-trust")
        self.assertNotEqual(handed.parent.resolve(), self.built.parent.resolve())
        self.assertEqual(self.built.read_text(encoding="utf-8"), "relinked by a sibling build\n")
        self.assertEqual(probes[0]["body"], "built from this tree\n")
        self.assertIn(f"--- targo-trust: built {self.built} (exit 0, ", out)
        # A good build's output is held: it is the same cached warnings every run.
        self.assertIn("1 lines of build output are shown only on a failure", out)
        self.assertNotIn("Compiling targo-trust v0.10.0", out)
        self.assertIn(f"the tests get the copy TRUST_TARGO_TRUST_BIN={handed}", out)
        self.assertIn(f"TRUST_TARGO_TRUST_BIN={handed} is in the record of each of 1 consumer test binaries", out)
        self.assertFalse(handed.exists(), "the private copy outlived the lane")

    def test_fixture_only_instrument_builds_and_records_the_private_copy(self):
        self.case.lane.changed_paths = lambda ranges: ["tests/fixtures/binary_decomp/x86_64-load-elf.hex"]
        rc, out, calls = self.case.run_main("ttprobe")
        self.assertEqual(rc, 0, out)
        self.assertEqual(len(calls), 2, calls)
        self.assertEqual(calls[0], self.BUILD, calls)
        self.assertIn("-p trust-integration-tests --test binary_to_trust_ir_e2e", calls[1])
        probes = [json.loads(line[len("TTPROBE "):]) for line in out.splitlines() if line.startswith("TTPROBE ")]
        self.assertEqual(len(probes), 1, out)
        self.assertEqual(probes[0]["body"], "built from this tree\n")
        self.assertNotEqual(Path(probes[0]["path"]).parent, self.built.parent)
        self.assertFalse(Path(probes[0]["path"]).exists())

    def test_fixture_only_instrument_refuses_a_record_without_the_copy(self):
        self.case.lane.changed_paths = lambda ranges: ["tests/fixtures/binary_decomp/x86_64-load-elf.hex"]
        os.environ["FAKE_TARGO_SCRUB"] = "TRUST_TARGO_TRUST_BIN"
        rc, out, calls = self.case.run_main("ttprobe")
        self.assertEqual(rc, 2, out)
        self.assertIn("is missing from the record", out)
        self.assertNotIn("TTPROBE ", out)
        self.assertEqual(len(calls), 2, calls)

    def test_fixture_and_cli_changes_do_not_claim_the_consumer_was_not_run(self):
        self.case.lane.changed_paths = lambda ranges: [
            "tests/fixtures/binary_decomp/x86_64-load-elf.hex", "targo-trust/src/main.rs"]
        rc, out, calls = self.case.run_main("ttprobe")
        self.assertEqual(rc, 0, out)
        self.assertNotIn("NOT RUN: the tests of trust-integration-tests", out)
        self.assertEqual(len(calls), 2, calls)

    def test_a_failed_targo_trust_build_is_red_and_runs_no_test(self):
        os.environ["FAKE_TARGO_TRUST"] = "fail"
        rc, out, calls = self.case.run_main("ttprobe")
        self.assertEqual(rc, 1, out)
        self.assertIn("could not compile `targo-trust`", out)  # cargo's own text, shown
        # stdout's lines that are not cargo's JSON are shown too; its JSON is not.
        self.assertIn("targo: a line on stdout that is not cargo JSON", out)
        self.assertNotIn('"reason": "build-finished"', out)
        self.assertIn("targo-trust FAILED TO BUILD (exit 101)", out)
        self.assertEqual(calls, [self.BUILD])
        self.assertNotIn("SKIP", out)

    def test_a_build_whose_messages_name_no_targo_trust_bin_cannot_judge(self):
        os.environ["FAKE_TARGO_TRUST"] = "no-artifact"
        rc, out, calls = self.case.run_main("ttprobe")
        self.assertEqual(rc, 2, out)
        self.assertIn("no compiler-artifact message named the targo-trust bin", out)
        self.assertIn("Compiling targo-trust v0.10.0", out)  # the held output, shown
        self.assertEqual(calls, [self.BUILD])

    def test_a_record_without_the_copy_cannot_judge_and_runs_no_test(self):
        # A cargo or targo that stops handing the variable on: the record says
        # so before any test runs, instead of every consumer test failing on
        # its missing-variable panic (or passing on an ambient value).
        os.environ["FAKE_TARGO_SCRUB"] = "TRUST_TARGO_TRUST_BIN"
        rc, out, calls = self.case.run_main("ttprobe")
        self.assertEqual(rc, 2, out)
        self.assertIn("CANNOT JUDGE", out)
        self.assertRegex(out, r"TRUST_TARGO_TRUST_BIN=\S+ is missing from the record of \S*ttprobe-")
        self.assertNotIn("TTPROBE ", out)
        self.assertEqual(len(calls), 2, calls)

    def test_without_the_prebuild_the_consumer_fails(self):
        # Control: the consumer fails when nothing hands it targo-trust, so the
        # green above is the prebuild's.
        self.case.lane.Plan.needs_targo_trust = lambda plan: False
        os.environ.pop("TRUST_TARGO_TRUST_BIN", None)
        rc, out, calls = self.case.run_main("ttprobe")
        self.assertEqual(rc, 1, out)
        self.assertIn("NEW FAILURE: ttprobe::runs_targo_trust", out)
        self.assertNotIn(self.BUILD, calls)

    def test_a_targo_trust_change_without_a_consumer_names_the_tests_not_run(self):
        # The consumers' tests run targo-trust, so a targo-trust/ change reaches
        # them; the lane plans from crates/ paths, and says what it left out.
        not_run = "NOT RUN: the tests of trust-integration-tests run targo-trust, which this push changes"
        for paths, want, skipped in (
            (["targo-trust/src/main.rs"], True, True),
            (["docs/notes.md"], False, True),
            (["targo-trust/src/main.rs", "crates/trust-integration-tests/src/lib.rs"], False, False),
        ):
            with self.subTest(paths=paths):
                self.case.lane.changed_paths = lambda ranges, paths=paths: paths
                out = io.StringIO()
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
                    rc = self.case.lane.main(["--range", "origin/main..HEAD", "--plan"])
                self.assertEqual(rc, 0, out.getvalue())
                self.assertEqual(not_run in out.getvalue(), want, out.getvalue())
                self.assertEqual("cannot be broken" in out.getvalue(), skipped and not want, out.getvalue())
        # Beside a planned member that is not a consumer, the line is printed too.
        def router_only(paths, members, roots):
            plan = self.case.lane.Plan()
            plan.packages = ["trust-router"]
            return plan
        self.case.lane.changed_paths = lambda ranges: ["targo-trust/src/main.rs", "crates/trust-router/src/lib.rs"]
        self.case.lane.plan_for = router_only
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = self.case.lane.main(["--range", "origin/main..HEAD", "--plan"])
        self.assertEqual(rc, 0, out.getvalue())
        self.assertIn(not_run, out.getvalue())
        self.assertIn("would run: targo --unverified test", out.getvalue())
        self.assertNotIn("would build", out.getvalue())
        self.assertFalse(self.case.log.exists(), "--plan built something")

    def test_plan_names_the_prebuild_and_builds_nothing(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = self.case.lane.main(["--range", "origin/main..HEAD", "--plan"])
        self.assertEqual(rc, 0, out.getvalue())
        # The plan names the command as sent; the fake logs it without the scope it checked.
        self.assertIn("would build: targo --unverified build -Zfeature-unification --config "
                      'resolver.feature-unification="selected" --manifest-path targo-trust/Cargo.toml '
                      "--bin targo-trust --locked --message-format json-render-diagnostics", out.getvalue())
        self.assertFalse(self.case.log.exists(), "--plan built something")

    def test_the_budget_bounds_the_targo_trust_build(self):
        # The prebuild is charged to the lane's one budget: a build that
        # outlasts it is killed and the lane is NOT JUDGED (exit 3), never a
        # failure (1) and never a pass; no command after it starts.
        # Give metadata/host fixture preparation no logical time so this
        # control reaches the real build with its unchanged one-second budget.
        clock = mock.Mock(wraps=time)
        epoch = time.monotonic()
        build_started = None
        clock.monotonic.side_effect = lambda: (
            epoch if build_started is None else epoch + time.monotonic() - build_started
        )
        build = self.case.lane.run_with_deadline

        def start_the_build(cmd, deadline, **kwargs):
            nonlocal build_started
            self.assertIsNone(build_started, "no command may follow the expired prebuild")
            self.assertIsInstance(deadline, self.case.lane.TimeBound)
            self.assertEqual(deadline._ceiling_at, epoch + 1)
            build_started = time.monotonic()
            return build(cmd, deadline, **kwargs)

        os.environ["FAKE_TARGO_TRUST"] = "sleep"
        pidfile = Path(self.case.tmp.name) / "targo-trust-build.pid"
        os.environ["FAKE_TARGO_TRUST_PIDFILE"] = str(pidfile)
        t0 = time.monotonic()
        with mock.patch.object(self.case.lane, "time", clock), \
                mock.patch.object(self.case.lane, "run_with_deadline", start_the_build):
            rc, out, calls = self.case.run_main("ttprobe", budget="1")
        self.assertEqual(rc, 3, out)
        self.assertLess(time.monotonic() - t0, 25, out)  # not the fake build's 30 s
        self.assertRegex(out, r"NOT JUDGED: the [0-9]+s budget ran out building targo-trust")
        self.assertIn("  not run: targo --unverified test -Zfeature-unification --config resolver.feature-unification=\"selected\" --manifest-path Cargo.toml", out)
        self.assertIn("Nothing above counts as a pass.", out)
        self.assertEqual(calls, [self.BUILD])
        self.assertNotIn("TTPROBE ", out)
        self.assertTrue(pidfile.exists(), "the build never started")
        build = int(pidfile.read_text())
        with self.assertRaises(ProcessLookupError, msg=f"the targo-trust build {build} outlived its budget"):
            os.kill(build, 0)
        self.assertEqual(self.case.lane._LIVE, set())

    def test_a_copy_the_budget_stops_is_not_judged(self):
        # The copy is charged to the same budget as the build: when it runs
        # out there (clone_or_copy -> False), the lane is NOT JUDGED (exit 3),
        # never a failure (1), and no test command starts.
        with mock.patch.object(self.case.lane, "clone_or_copy", lambda src, dst, deadline: False):
            rc, out, calls = self.case.run_main("ttprobe")
        self.assertEqual(rc, 3, out)
        self.assertRegex(out, r"NOT JUDGED: the [0-9]+s budget ran out copying targo-trust")
        self.assertIn("Nothing above counts as a pass.", out)
        self.assertEqual(calls, [self.BUILD])
        self.assertNotIn("TTPROBE ", out)


# Runs the lane in a process of its own, like LANE_DRIVER, for a push that
# touches trust-integration-tests (a TARGO_TRUST_CONSUMERS member).
PREBUILD_LANE_DRIVER = """
import importlib.util, sys
spec = importlib.util.spec_from_file_location("lane", sys.argv[1])
lane = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lane)
lane.changed_paths = lambda ranges: ["crates/trust-integration-tests/tests/binary_to_trust_ir_e2e.rs"]
sys.exit(lane.main(["--range", "origin/main..HEAD"]))
"""


class PrebuildInterruptTest(unittest.TestCase):
    """main's interrupt model holds for the targo-trust prebuild: an INT or TERM
    to the lane while targo-trust builds reaches that build (a session of its
    own, so only forwarding reaches it), and the lane's scratch directories,
    the private one meant for the copy included, are gone when it exits
    128+signal. The same after the copy is made, during the record pass."""

    def setUp(self):
        self.prebuild = TargoTrustPrebuildTest("test_plan_names_the_prebuild_and_builds_nothing")
        self.prebuild.setUp()
        self.addCleanup(self.prebuild.tearDown)
        self.tmp = Path(self.prebuild.case.tmp.name)
        # The lane's own TMPDIR, so its scratch directories are this test's to count.
        self.lane_tmp = self.tmp / "lane-tmp"
        self.lane_tmp.mkdir()

    def start_lane(self, **env):
        os.environ["FAKE_TARGO_BUILD"], binaries = MODES["ttprobe"]
        os.environ["FAKE_TARGO_BINARIES"] = ",".join(binaries)
        os.environ.update(TRUST_CRATES_TESTS_BUDGET_S="120", TMPDIR=str(self.lane_tmp), **env)
        proc = subprocess.Popen([sys.executable, "-c", PREBUILD_LANE_DRIVER, str(SCRIPT)],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                preexec_fn=_signals_at_default)
        self.addCleanup(lambda: proc.poll() is None and proc.kill())
        return proc

    def scratch(self, prefix="crates-tests-"):
        return sorted(p.name for p in self.lane_tmp.glob(prefix + "*"))

    def interrupt(self, proc, sig, pid):
        proc.send_signal(sig)
        out, _ = proc.communicate(timeout=30)
        self.assertEqual(proc.returncode, 128 + sig, out)
        self.assertIn(f"interrupted ({sig.name}); passed it to 1 running process group(s)", out)
        with self.assertRaises(ProcessLookupError, msg=f"{pid} outlived the lane"):
            os.kill(pid, 0)
        self.assertEqual(self.scratch(), [], f"a scratch directory outlived the lane:\n{out}")
        self.assertNotIn("TTPROBE ", out)
        return out

    def test_an_interrupt_during_the_targo_trust_build(self):
        for sig in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(sig=sig.name):
                pidfile = self.tmp / f"targo-trust-build-{sig.name}.pid"
                proc = self.start_lane(FAKE_TARGO_TRUST="sleep", FAKE_TARGO_TRUST_PIDFILE=str(pidfile))
                self.assertTrue(InterruptTest.wait_for(pidfile), "the targo-trust build never started")
                self.assertEqual(len(self.scratch("crates-tests-targo-trust.")), 1, self.scratch())
                out = self.interrupt(proc, sig, int(pidfile.read_text()))
                self.assertIn("building targo-trust for trust-integration-tests", out)
                self.assertNotIn("building and recording", out)

    def test_an_interrupt_in_the_record_pass_removes_the_copy(self):
        pidfile = self.tmp / "record.pid"
        proc = self.start_lane(FAKE_TARGO_BUILD="sleep", FAKE_TARGO_PIDFILE=str(pidfile))
        self.assertTrue(InterruptTest.wait_for(pidfile), "the record pass never started")
        private = self.scratch("crates-tests-targo-trust.")
        self.assertEqual(len(private), 1, self.scratch())
        self.assertEqual([p.name for p in (self.lane_tmp / private[0]).iterdir()], ["targo-trust"])
        self.assertEqual(len(self.scratch("crates-tests-record.")), 1, self.scratch())
        out = self.interrupt(proc, signal.SIGTERM, int(pidfile.read_text()))
        self.assertIn("--- targo-trust: built ", out)


class PrebuildInheritedIgnoredInterruptTest(InheritsIgnoredInterrupts, PrebuildInterruptTest):
    """PrebuildInterruptTest's cases again, each lane started while this suite's
    INT and HUP are ignored (InheritedIgnoredInterruptTest): before 3a6a97cf07
    the INT during the targo-trust build timed out in such a suite."""


# A signal right after the scratch directory is made, before the lane has
# recorded it: tempfile.mkdtemp is wrapped to send the lane SIGTERM as it
# returns. The directory must still be removed, and the lane exit 143.
SCRATCH_RACE_DRIVER = """
import importlib.util, os, signal, sys, tempfile
spec = importlib.util.spec_from_file_location("lane", sys.argv[1])
lane = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lane)
real = tempfile.mkdtemp
def racing(*args, **kwargs):
    path = real(*args, **kwargs)
    with open(sys.argv[2], "w") as fh:
        fh.write(path)
    os.kill(os.getpid(), signal.SIGTERM)
    return path
tempfile.mkdtemp = racing
with lane.forwarding_signals():
    with lane._scratch_dir("crates-tests-race."):
        pass
sys.exit(0)
"""


class ScratchRaceTest(unittest.TestCase):
    def test_a_signal_between_mkdtemp_and_recording_still_removes_the_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            made = Path(tmp) / "made"
            proc = subprocess.run([sys.executable, "-c", SCRATCH_RACE_DRIVER, str(SCRIPT), str(made)],
                                  capture_output=True, text=True, timeout=60,
                                  env=dict(os.environ, TMPDIR=tmp))
            out = proc.stdout + proc.stderr
            self.assertTrue(made.exists(), out)
            self.assertEqual(proc.returncode, 128 + signal.SIGTERM, out)
            self.assertFalse(Path(made.read_text()).exists(), f"the scratch directory outlived the lane: {out}")


class CopyTest(unittest.TestCase):
    """clone_or_copy hands the tests a COPY: its own file, never a symlink or a
    hard link to the target dir's binary, which a sibling build may relink."""

    def setUp(self):
        self.lane = load_lane()
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.src = Path(self.tmp.name) / "target" / "debug" / "targo-trust"
        self.src.parent.mkdir(parents=True)
        self.src.write_bytes(b"built from this tree\n")
        self.src.chmod(0o755)
        self.dst = Path(self.tmp.name) / "private" / "targo-trust"
        self.dst.parent.mkdir()

    def assert_a_real_copy(self):
        self.assertFalse(self.dst.is_symlink(), "a symlink to the target dir's binary")
        src, dst = os.stat(self.src), os.stat(self.dst)
        self.assertNotEqual((dst.st_dev, dst.st_ino), (src.st_dev, src.st_ino), "a hard link, not a copy")
        self.assertEqual(self.dst.read_bytes(), b"built from this tree\n")
        self.assertTrue(os.access(self.dst, os.X_OK), "the copy lost its mode")
        # A sibling build relinking the target dir's file in place.
        self.src.write_bytes(b"relinked by a sibling build\n")
        self.assertEqual(self.dst.read_bytes(), b"built from this tree\n")

    def test_off_macos_it_is_a_real_copy(self):
        def no_cp(*args, **kwargs):
            raise AssertionError(f"off macOS nothing is spawned: {args}")
        with mock.patch.object(self.lane.sys, "platform", "linux"), \
                mock.patch.object(self.lane, "_spawn", no_cp):
            self.assertTrue(self.lane.clone_or_copy(str(self.src), str(self.dst), time.monotonic() + 60))
        self.assert_a_real_copy()

    @unittest.skipUnless(sys.platform == "darwin", "cp -c is the macOS branch")
    def test_on_macos_it_is_a_clone_made_by_a_tracked_cp(self):
        spawned = []
        real = self.lane._spawn

        def spy(cmd, **kwargs):
            spawned.append(cmd)
            return real(cmd, **kwargs)
        with mock.patch.object(self.lane, "_spawn", spy):
            self.assertTrue(self.lane.clone_or_copy(str(self.src), str(self.dst), time.monotonic() + 60))
        self.assertEqual(spawned, [["cp", "-c", "-p", str(self.src), str(self.dst)]])
        self.assertEqual(self.lane._LIVE, set())
        self.assert_a_real_copy()

    @unittest.skipUnless(sys.platform == "darwin", "cp -c is the macOS branch")
    def test_on_macos_a_time_bound_copy_closes_its_redirected_stderr(self):
        real = self.lane._spawn
        stderr_files = []

        def tracked(cmd, **kwargs):
            self.assertEqual(kwargs["stdout"], subprocess.DEVNULL)
            stderr_files.append(kwargs["stderr"])
            return real(cmd, **kwargs)

        with mock.patch.object(self.lane, "_spawn", tracked):
            self.assertTrue(self.lane.clone_or_copy(
                str(self.src), str(self.dst), self.lane.TimeBound(60, 30)))
        self.assertEqual(len(stderr_files), 1)
        self.assertTrue(stderr_files[0].closed)
        self.assertEqual(self.lane._LIVE, set())
        self.assert_a_real_copy()

    @unittest.skipUnless(sys.platform == "darwin", "cp -c is the macOS branch")
    def test_on_macos_a_cp_past_the_deadline_is_killed_and_reports_false(self):
        real = self.lane._spawn
        started = []
        stderr_files = []

        def slow_cp(cmd, **kwargs):
            self.assertEqual(kwargs["stdout"], subprocess.DEVNULL)
            stderr_files.append(kwargs["stderr"])
            proc = real(["sleep", "30"], **kwargs)
            started.append(proc)
            return proc
        t0 = time.monotonic()
        with mock.patch.object(self.lane, "_spawn", slow_cp):
            self.assertFalse(self.lane.clone_or_copy(str(self.src), str(self.dst), time.monotonic() + 1))
        self.assertLess(time.monotonic() - t0, 20)  # not the 30 s sleep
        self.assertEqual(len(started), 1)
        self.assertIsNotNone(started[0].poll(), "the cp outlived its deadline")
        # DEVNULL and an explicit file do not populate Popen's PIPE handles.
        # Check the file actually handed to the child, after its context exits.
        self.assertIsNone(started[0].stdout)
        self.assertIsNone(started[0].stderr)
        self.assertEqual(len(stderr_files), 1)
        self.assertTrue(stderr_files[0].closed, "the expired copy retained its stderr file")
        self.assertEqual(self.lane._LIVE, set())

    def test_a_copy_that_fails_raises(self):
        missing = str(Path(self.tmp.name) / "missing")
        for platform in sorted({sys.platform, "linux"}):
            with self.subTest(platform=platform), mock.patch.object(self.lane.sys, "platform", platform):
                with self.assertRaises(OSError):
                    self.lane.clone_or_copy(missing, str(self.dst), time.monotonic() + 60)
        self.assertEqual(self.lane._LIVE, set())


def _macho(flags=0x20002, platform=0, segment=b"__TEXT", signed=True, filetype=2, magic=0xFEEDFACF,
           extra_cd_flags=None):
    """A synthetic thin Mach-O: one segment command and (if signed) an
    LC_CODE_SIGNATURE pointing at a SuperBlob whose CodeDirectory carries
    `flags` and `platform` (and, with `extra_cd_flags`, a second one in the
    first alternate slot, as a multi-digest signature has). Only what
    admissible() reads is real."""
    import struct
    seg = struct.pack("<II16s", 0x19, 72, segment) + bytes(48)
    sig_cmd = struct.pack("<IIII", 0x1D, 16, 0, 0)
    cmds = seg + (sig_cmd if signed else b"")
    body = struct.pack("<IiiIIIII", magic, 0x0100000C, 0, filetype, 2 if signed else 1, len(cmds), 0, 0) + cmds
    cd = struct.pack(">IIIIIIIIIBBBBI", 0xFADE0C02, 44, 0x20400, flags, 0, 0, 0, 0, 0, 32, 2, platform, 12, 0)
    if extra_cd_flags is None:
        blob = struct.pack(">III", 0xFADE0CC0, 12 + 8 + len(cd), 1) + struct.pack(">II", 0, 20) + cd
    else:
        alt = struct.pack(">IIIIIIIIIBBBBI", 0xFADE0C02, 44, 0x20400, extra_cd_flags, 0, 0, 0, 0, 0, 32, 2, platform, 12, 0)
        blob = (struct.pack(">III", 0xFADE0CC0, 12 + 16 + len(cd) + len(alt), 2)
                + struct.pack(">II", 0, 28) + struct.pack(">II", 0x1000, 28 + len(cd)) + cd + alt)
    if signed:
        off = len(body)
        body = body[:32 + 72] + struct.pack("<IIII", 0x1D, 16, off, len(blob)) + body[32 + 72 + 16:]
        body += blob
    return body


class AdmissionTest(unittest.TestCase):
    """ONE AT A TIME THROUGH MACOS'S FIRST-EXEC CHECK (2026-10-09): what is
    probed, that a probe runs none of the program, and that admission changes
    when a binary starts, never what runs or how it is judged."""

    def setUp(self):
        self.lane = load_lane()
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def _file(self, name, data, mode=0o755):
        path = self.dir / name
        path.write_bytes(data)
        path.chmod(mode)
        return str(path)

    def test_only_an_ad_hoc_thin_executable_is_probed(self):
        # The probe relies on dyld honouring DYLD_INSERT_LIBRARIES. Everything
        # that could make dyld ignore it, or is not what the linker makes of a
        # cargo test binary, is refused, and then nothing is probed.
        admissible = self.lane.admissible
        self.assertIsNone(admissible(self._file("adhoc", _macho())))
        self.assertIsNone(admissible(self._file("adhoc-only", _macho(flags=0x2))))
        refused = {
            "runtime": _macho(flags=0x20002 | 0x10000),   # hardened runtime
            "restrict": _macho(flags=0x20002 | 0x800),    # CS_RESTRICT
            "apple": _macho(flags=0x0),                   # not ad hoc (an Apple signature)
            "platform": _macho(platform=1),               # a platform binary
            "restricted": _macho(segment=b"__RESTRICT"),  # dyld's __RESTRICT segment
            "unsigned": _macho(signed=False),
            "dylib": _macho(filetype=6),
            "fat": _macho(magic=0xBEBAFECA),
            "script": b"#!/bin/sh\necho ran\n",
            # Two CodeDirectories: the kernel enforces the strongest-hash one,
            # which here carries the hardened runtime the primary does not.
            "multi-digest": _macho(extra_cd_flags=0x20002 | 0x10000),
            "multi-digest-same": _macho(extra_cd_flags=0x20002),
        }
        for name, data in refused.items():
            self.assertIsNotNone(admissible(self._file(name, data)), name)
        self.assertIsNotNone(admissible(self._file("setuid", _macho(), 0o4755)), "setuid")
        self.assertIsNotNone(admissible(str(self.dir / "missing")))

    def test_a_refused_executable_is_never_started(self):
        marker = self.dir / "ran"
        script = self._file("script", f"#!/bin/sh\ntouch '{marker}'\n".encode())
        outcome, why = self.lane.admit_one(script, {}, str(self.dir), time.monotonic() + 30)
        self.assertEqual(outcome, "skipped")
        self.assertIn("Mach-O", why)
        self.assertFalse(marker.exists(), "a refused executable was started")

    def test_a_probe_that_is_not_stopped_in_dyld_misbehaves(self):
        # /bin/echo and /usr/bin/true are SIP-protected, so dyld drops DYLD_*
        # and they run: exactly what admissible() exists to prevent. Forced
        # past it here, the probe must say so, never "admitted": echo prints
        # its argv, true just exits. (Tools, not a fresh file: a newly written
        # executable would itself wait in macOS's check.)
        for tool in ("/bin/echo", "/usr/bin/true"):
            with mock.patch.object(self.lane, "admissible", return_value=None):
                outcome, why = self.lane.admit_one(tool, {}, str(self.dir), time.monotonic() + 30)
            self.assertEqual(outcome, "misbehaved", f"{tool}: {why}")

    def test_the_probe_execs_a_hard_link_in_its_own_directory(self):
        # The check's cost grows with the directory a file is exec'd from;
        # crates/target/debug/deps is huge. The probe names the SAME file from
        # the private directory, and the link is gone afterwards.
        exe = self._file("deps-0123456789abcdef", _macho())
        probes = self.dir / "probes"
        probes.mkdir()
        seen = []

        def probe(target, env, directory, fifo, deadline):
            seen.append((target, os.path.samefile(target, exe), Path(target).parent == probes))
            return "admitted", ""

        with mock.patch.object(self.lane, "_probe", side_effect=probe):
            self.assertEqual(self.lane.admit_one(exe, {}, str(probes), time.monotonic() + 30)[0], "admitted")
        [(target, same, private)] = seen
        self.assertNotEqual(target, exe)
        self.assertTrue(same, "the probe must exec the binary's own file")
        self.assertTrue(private, "the link must be in the probe's directory")
        self.assertFalse(os.path.lexists(target), "the link outlived the probe")
        self.assertTrue(os.path.exists(exe))

    def test_without_a_link_the_probe_execs_the_binary_itself(self):
        exe = self._file("deps-0123456789abcdef", _macho())
        seen = []

        def probe(target, env, directory, fifo, deadline):
            seen.append(target)
            return "admitted", ""

        with mock.patch.object(self.lane, "_probe", side_effect=probe), \
                mock.patch.object(self.lane.os, "link", side_effect=OSError(18, "cross-device link")):
            self.assertEqual(self.lane.admit_one(exe, {}, str(self.dir), time.monotonic() + 30)[0], "admitted")
        self.assertEqual(seen, [exe])

    @unittest.skipUnless(sys.platform == "darwin", "macOS's first-exec check")
    def test_a_real_probe_is_stopped_in_dyld_and_runs_nothing(self):
        trustc = shutil.which("trustc")
        if not trustc:
            self.skipTest("no trustc on PATH to link a fresh executable")
        src = self.dir / "fresh.rs"
        src.write_text('fn main() { println!("the program ran"); }\n', encoding="utf-8")
        exe = self.dir / "fresh"
        build = subprocess.run([trustc, "-O", str(src), "-o", str(exe)], capture_output=True, text=True,
                               timeout=300)
        if build.returncode or not exe.exists():
            self.skipTest(f"trustc did not link the probe target: {build.stderr[-300:]}")
        self.assertIsNone(self.lane.admissible(str(exe)))
        probes = self.dir / "probes"
        probes.mkdir()
        outcome, why = self.lane.admit_one(str(exe), {"PATH": "/usr/bin"}, str(probes),
                                           time.monotonic() + 45)
        if outcome == "deadline":  # the host's queue is long: say so, judge nothing
            self.skipTest("macOS's first-exec check did not clear within 45s on this host")
        self.assertEqual(outcome, "admitted", why)
        ran = subprocess.run([str(exe)], capture_output=True, text=True, timeout=60)
        self.assertEqual(ran.stdout, "the program ran\n", "the real run must be untouched")

    def _binaries(self, names):
        # Never exec'd: run_one is replaced (_patched), so no fresh executable
        # waits in macOS's check here.
        return [self.lane.Binary({"argv": [str(self.dir / name)], "cwd": str(self.dir), "env": {}},
                                 f"     Running {name}") for name in names]

    def _patched(self, admit, run_one=None):
        def ran(binary, deadline):
            binary.rc, binary.output = 0, "running 0 tests\n\ntest result: ok. 0 passed; 0 failed;\n"
        self.lane.ADMIT_PLATFORM = sys.platform
        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch.object(self.lane, "admit_one", side_effect=admit))
        stack.enter_context(mock.patch.object(self.lane, "run_one", side_effect=run_one or ran))
        return stack

    def test_admission_is_one_at_a_time_in_order_and_before_each_start(self):
        events, lock, inside = [], threading.Lock(), [0]

        def admit(exe, env, directory, deadline):
            with lock:
                inside[0] += 1
                events.append(("admit", Path(exe).name, inside[0]))
            time.sleep(0.2)
            with lock:
                inside[0] -= 1
                events.append(("admitted", Path(exe).name, inside[0]))
            return "admitted", ""

        binaries = self._binaries([f"b{i}-000000000000000{i}" for i in range(6)])

        def run_one(binary, deadline):
            with lock:
                events.append(("start", Path(binary.argv[0]).name, None))
            binary.rc, binary.output = 0, "running 0 tests\n\ntest result: ok. 0 passed; 0 failed;\n"

        with self._patched(admit, run_one), contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertTrue(self.lane.run_binaries(binaries, 4, time.monotonic() + 60))
        self.assertTrue(all(b.rc == 0 for b in binaries))
        self.assertEqual(max(n for kind, _, n in events if kind == "admit"), 1, "two probes at once")
        admitted = [name for kind, name, _ in events if kind == "admitted"]
        # The pool's order (biggest first; these are all size 0, so cargo's).
        self.assertEqual(admitted, [Path(b.argv[0]).name for b in binaries])
        for kind, name, _ in events:
            if kind == "start":
                self.assertIn(("admitted", name), [(k, n) for k, n, _ in events[:events.index((kind, name, None))]],
                              f"{name} started before it was admitted")
        self.assertIn("6 admitted of 6 executables", out.getvalue())

    def test_a_deadline_during_admission_starts_nothing_and_is_not_judged(self):
        def admit(exe, env, directory, deadline):
            time.sleep(max(deadline - time.monotonic(), 0))
            return "deadline", "the budget ran out during macOS's first-exec check"

        binaries = self._binaries(["slow-0000000000000001", "next-0000000000000002"])
        with self._patched(admit), contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(self.lane.run_binaries(binaries, 2, time.monotonic() + 1))
        self.assertTrue(all(b.rc is None for b in binaries), "a binary started after the deadline")

    def test_misbehaviour_stops_admission_and_the_binaries_still_run(self):
        calls = []

        def admit(exe, env, directory, deadline):
            calls.append(exe)
            return "misbehaved", "the probe was not stopped in dyld ('ran')"

        binaries = self._binaries(["a-0000000000000001", "b-0000000000000002", "c-0000000000000003"])
        with self._patched(admit), contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertTrue(self.lane.run_binaries(binaries, 2, time.monotonic() + 60))
        self.assertEqual(len(calls), 1, "admission went on after a probe misbehaved")
        self.assertTrue(all(b.rc == 0 for b in binaries))
        self.assertIn("admission STOPPED", out.getvalue())

    def test_turned_off_it_probes_nothing(self):
        binaries = self._binaries(["a-0000000000000001"])
        def probed(*_):
            raise AssertionError("probed with admission off")

        with self._patched(probed), mock.patch.dict(os.environ, {"TRUST_CRATES_TESTS_ADMIT": "0"}), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertTrue(self.lane.run_binaries(binaries, 1, time.monotonic() + 60))
        self.assertEqual(binaries[0].rc, 0)
        self.assertNotIn("first-exec admission", out.getvalue())

    # A probe's own limits. These run /bin/sh in the probe's place (_spawn is
    # redirected), never a freshly written file, which would itself wait in
    # macOS's check.
    def _probe_as_shell(self, script, deadline_s=60, **limits):
        real_spawn = self.lane._spawn

        def spawn(cmd, **kwargs):
            return real_spawn(["/bin/sh", "-c", script], **kwargs)

        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch.object(self.lane, "_spawn", side_effect=spawn))
        for name, value in limits.items():
            stack.enter_context(mock.patch.object(self.lane, name, value))
        t0 = time.monotonic()
        with stack:
            outcome, why = self.lane._probe("/bin/sh", {}, str(self.dir), str(self.dir / "fifo"),
                                            time.monotonic() + deadline_s)
        return outcome, why, time.monotonic() - t0

    def test_a_probe_whose_dyld_never_reaches_the_fifo_stops_admission_early(self):
        # dyld ran (the check is over) but its line is not the one expected:
        # another wording, another spelling of the path. One such probe must
        # not hold every worker until the deadline.
        outcome, why, took = self._probe_as_shell(
            'echo "dyld[$$]: open path \\"x\\""; exec sleep 60', ADMIT_DYLD_MAX_S=1.0)
        self.assertEqual(outcome, "misbehaved", why)
        self.assertIn("did not reach the FIFO", why)
        self.assertLess(took, 20, "the probe was held past its own ceiling")

    def test_a_probe_held_past_its_ceiling_stops_admission(self):
        outcome, why, took = self._probe_as_shell("exec sleep 60", ADMIT_PROBE_MAX_S=1.0)
        self.assertEqual(outcome, "misbehaved", why)
        self.assertIn("after 1s", why)
        self.assertLess(took, 20)

    def test_a_probe_killed_by_someone_else_is_not_a_deadline(self):
        outcome, why, took = self._probe_as_shell("kill -9 $$")
        self.assertEqual(outcome, "misbehaved", why)
        self.assertIn("exit -9", why)
        self.assertLess(took, 20)

    def test_a_probe_at_the_deadline_is_a_deadline(self):
        outcome, why, _ = self._probe_as_shell("exec sleep 60", deadline_s=1)
        self.assertEqual(outcome, "deadline", why)

    def test_a_probe_that_is_not_reaped_does_not_hold_the_lane(self):
        # SIGKILLed while the kernel holds it, a probe might not be reaped
        # until syspolicyd lets it go. The lane waits ADMIT_REAP_S, no longer.
        # The custody check needs an actual waitable child, never an invented
        # PID. Only the reap-timeout boundary is simulated; KILL is real and
        # the fixture then consumes the real child exactly once.
        proc = self.lane._spawn(["/bin/sleep", "8"], stdout=subprocess.PIPE)
        real_killpg = os.killpg
        try:
            with mock.patch.object(self.lane, "_spawn", return_value=proc), \
                    mock.patch.object(self.lane, "_wait", side_effect=subprocess.TimeoutExpired("probe", 0.1)), \
                    mock.patch.object(self.lane.os, "killpg", wraps=real_killpg) as killpg, \
                    mock.patch.object(self.lane, "ADMIT_PROBE_MAX_S", 0.5), \
                    mock.patch.object(self.lane, "ADMIT_REAP_S", 0.1):
                outcome, why = self.lane._probe("/bin/sh", {}, str(self.dir), str(self.dir / "fifo"),
                                              time.monotonic() + 60)
            self.assertEqual(outcome, "misbehaved", why)
            self.assertIn("not reaped", why)
            killpg.assert_called_with(proc.pid, signal.SIGKILL)
        finally:
            proc.wait(timeout=10)
            self.lane._untrack(proc)
            proc.stdout.close()

    def test_an_interrupted_lane_makes_no_link(self):
        exe = self._file("deps-0123456789abcdef", _macho())
        probes = self.dir / "probes"
        probes.mkdir()
        self.lane._STOPPING.set()
        try:
            with mock.patch.object(self.lane, "_probe", side_effect=AssertionError("probed")):
                outcome, _ = self.lane.admit_one(exe, {}, str(probes), time.monotonic() + 30)
        finally:
            self.lane._STOPPING.clear()
        self.assertEqual(outcome, "deadline")
        self.assertEqual([p.name for p in probes.iterdir() if p.name.startswith("admit-")], [])

    def test_an_error_inside_admission_stops_it_and_every_binary_runs(self):
        calls = []

        def admit(exe, env, directory, deadline):
            calls.append(exe)
            raise OSError(13, "Permission denied")

        binaries = self._binaries(["a-0000000000000001", "b-0000000000000002", "c-0000000000000003"])
        with self._patched(admit), contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertTrue(self.lane.run_binaries(binaries, 2, time.monotonic() + 60))
        self.assertEqual(len(calls), 1, "admission went on after an error")
        self.assertTrue(all(b.rc == 0 for b in binaries))
        self.assertIn("1 failed of 3 executables", out.getvalue())
        self.assertIn("admission STOPPED at a-0000000000000001: PermissionError", out.getvalue())

    def test_after_a_misbehaving_probe_the_log_never_says_nothing_ran(self):
        def admit(exe, env, directory, deadline):
            return "misbehaved", "the probe ended before it was stopped in dyld (exit 0)"

        binaries = self._binaries(["a-0000000000000001"])
        with self._patched(admit), contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertTrue(self.lane.run_binaries(binaries, 1, time.monotonic() + 60))
        self.assertNotIn("no probe ran any code", out.getvalue())
        self.assertIn("may have run its binary's code once", out.getvalue())

    def test_off_macos_it_probes_nothing(self):
        binaries = self._binaries(["a-0000000000000001"])

        def probed(*_):
            raise AssertionError("probed off macOS")

        with self._patched(probed), contextlib.redirect_stdout(io.StringIO()) as out:
            self.lane.ADMIT_PLATFORM = "not-" + sys.platform
            self.assertTrue(self.lane.run_binaries(binaries, 1, time.monotonic() + 60))
        self.assertEqual(binaries[0].rc, 0)
        self.assertNotIn("first-exec admission", out.getvalue())

    def test_only_0_turns_it_off(self):
        self.lane.ADMIT_PLATFORM = sys.platform
        for value, enabled in (("0", False), ("1", True), ("false", True), ("off", True), ("", True)):
            with mock.patch.dict(os.environ, {"TRUST_CRATES_TESTS_ADMIT": value}):
                self.assertEqual(self.lane.Admission([], time.monotonic()).enabled, enabled, repr(value))


class RecordTest(unittest.TestCase):
    def test_the_recorder_saves_cargos_order_argv_directory_and_environment(self):
        lane = load_lane()
        runner = json.loads(lane.runner_config("RECORD_DIR").split("=", 1)[1])
        self.assertEqual(runner[0], sys.executable)
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as pkg:
            env = {"PATH": os.environ["PATH"], "CARGO_PKG_NAME": "p", "ODD": "a b\nc \u00e9"}
            for argv in (["/deps/a-1"], ["/deps/b-2", "--exact"]):
                args = [tmp if a == "RECORD_DIR" else a for a in runner] + argv
                subprocess.run(args, cwd=pkg, env=env, check=True, timeout=60)
            names = sorted(os.listdir(tmp))
            self.assertEqual(names, ["000000.json", "000001.json"])
            second = json.loads((Path(tmp) / names[1]).read_text(encoding="utf-8"))
            self.assertEqual(second["argv"], ["/deps/b-2", "--exact"])
            self.assertEqual(Path(second["cwd"]).resolve(), Path(pkg).resolve())
            for key, value in env.items():
                self.assertEqual(second["env"][key], value, key)

    def test_the_deadline_kills_a_running_binary_and_skips_the_rest(self):
        lane = load_lane()
        env = dict(os.environ)
        sleeper = lane.Binary({"argv": ["sleep", "60"], "cwd": os.getcwd(), "env": env}, "sleeper")
        queued = lane.Binary({"argv": ["true"], "cwd": os.getcwd(), "env": env}, "queued")
        t0 = time.monotonic()
        with contextlib.redirect_stdout(io.StringIO()) as out:
            finished = lane.run_binaries([sleeper, queued], 1, time.monotonic() + 1)
        self.assertLess(time.monotonic() - t0, 20, "the deadline did not kill the binary")
        self.assertFalse(finished)
        self.assertIsNone(sleeper.rc)
        self.assertIsNone(queued.rc, "a binary queued behind the deadline must not start")
        self.assertIn("KILLED at the deadline", out.getvalue())

    def test_a_binary_that_cannot_start_fails(self):
        lane = load_lane()
        gone = lane.Binary({"argv": ["/nonexistent/deps/gone-0123456789abcdef"], "cwd": os.getcwd(),
                            "env": dict(os.environ)}, "     Running tests/gone.rs (gone-0123456789abcdef)")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(lane.run_binaries([gone], 1, time.monotonic() + 60))
        self.assertEqual(gone.rc, 127)
        ok, report, rc = lane.judge_command(0, [gone], {})
        self.assertFalse(ok)
        self.assertEqual(rc, 101)
        self.assertTrue(any("BINARY FAILED OUTSIDE ITS TEST LINES" in line for line in report), report)

    def _python(self, lane, code, name="py"):
        return lane.Binary({"argv": [sys.executable, "-c", code], "cwd": os.getcwd(),
                            "env": dict(os.environ)}, name)

    def test_a_child_holding_the_output_costs_the_grace_not_the_budget(self):
        # The binary exits at once; a child it started keeps its stdout open.
        # The pool waits for the binary, as cargo does, then OUTPUT_GRACE_S.
        lane = load_lane()
        lane.OUTPUT_GRACE_S = 1
        leaker = self._python(lane, (
            "import subprocess, sys\n"
            "print('running 1 test\\ntest t ... ok\\n\\ntest result: ok. 1 passed; 0 failed;', flush=True)\n"
            "subprocess.Popen(['sleep', '8'])\n"))
        t0 = time.monotonic()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(lane.run_binaries([leaker], 1, time.monotonic() + 60))
        self.assertLess(time.monotonic() - t0, 6, "waited for the child's EOF, not the binary")
        self.assertEqual(leaker.rc, 0)
        self.assertIn("still held its output open", leaker.output)
        self.assertIsNone(lane.binary_problem(leaker))

    def test_a_hung_binary_with_a_detached_child_is_not_judged_within_the_grace(self):
        # At the deadline the binary's group is killed; a child in a session of
        # its own survives, holding the output open. The lane still returns.
        lane = load_lane()
        lane.OUTPUT_GRACE_S = 1
        hung = self._python(lane, (
            "import subprocess, time\n"
            "subprocess.Popen(['sleep', '8'], start_new_session=True)\n"
            "print('running 1 test', flush=True)\n"
            "time.sleep(60)\n"))
        t0 = time.monotonic()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(lane.run_binaries([hung], 1, time.monotonic() + 1))
        self.assertLess(time.monotonic() - t0, 8, "the lane waited on the detached child")
        self.assertIsNone(hung.rc)

    def test_killing_a_group_whose_leader_already_exited_is_no_error(self):
        # macOS answers killpg on a zombie-only group with EPERM.
        lane = load_lane()
        proc = subprocess.Popen(["true"], start_new_session=True)
        time.sleep(1)  # exited, not reaped: a zombie leading its own group
        lane._kill_group(proc)
        proc.wait(timeout=10)

    def test_one_executable_never_runs_beside_itself(self):
        lane = load_lane()
        fake = FakeTargo.directory() / "bin" / "solo-0000000000000006"
        with tempfile.TemporaryDirectory() as tmp:
            env = dict(os.environ, FAKE_PAIR_DIR=tmp)
            copy = Path(tmp) / "solo-copy-0000000000000009"
            copy.write_bytes(fake.read_bytes())
            copy.chmod(0o755)
            subprocess.run([str(copy), "--warm-up"], capture_output=True, check=False, timeout=120)
            for paths, collide in (([fake, fake], False), ([fake, copy], True)):
                runs = [lane.Binary({"argv": [str(p)], "cwd": tmp, "env": env}, str(p)) for p in paths]
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertTrue(lane.run_binaries(runs, 2, time.monotonic() + 60))
                # Control: two different files do run at once, and collide.
                self.assertEqual(any(b.rc != 0 for b in runs), collide, [b.output for b in runs])

    def test_the_biggest_binary_starts_first(self):
        lane = load_lane()
        with tempfile.TemporaryDirectory() as tmp:
            order = Path(tmp) / "order"
            binaries = []
            for name, padding in (("small", 0), ("big", 4096)):
                exe = Path(tmp) / name
                exe.write_text(f"#!/bin/sh\necho {name} >> '{order}'\n" + "#" * padding + "\n", encoding="utf-8")
                exe.chmod(0o755)
                binaries.append(lane.Binary({"argv": [str(exe)], "cwd": tmp, "env": dict(os.environ)}, name))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(lane.run_binaries(binaries, 1, time.monotonic() + 60))
            self.assertEqual(order.read_text(encoding="utf-8").split(), ["big", "small"])

    def test_default_jobs_is_at_least_one(self):
        self.assertGreaterEqual(load_lane().default_jobs(), 1)

    def _host_budget(self):
        sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
        import host_budget  # the lane imports the same module object
        return host_budget

    def test_default_jobs_stays_at_the_measured_four_on_a_bigger_host(self):
        # 8 jobs turned a wall-clock assertion red on 2026-09-29; a 32-core,
        # 256 GiB unmanaged host with room to spare must not get there by
        # default. The managed small-share controls exercise admission caps.
        lane = load_lane()
        hb = self._host_budget()
        big = hb.Host("Darwin", 32, 256 * 2**30, 200 * 2**30, "test", 1.0)
        with mock.patch.dict(os.environ, {"BUILD_SLOT_HELD": ""}), \
                mock.patch.object(lane.os, "cpu_count", return_value=32), \
                mock.patch.object(hb, "measure", return_value=big):
            self.assertEqual(lane.default_jobs(), 4)

    def test_default_jobs_reads_the_memory_available_now(self):
        # 2026-10-14: sized from scripts/lib/host_budget.py's crates-test plan
        # against the memory AVAILABLE, not the host's total: the same big host
        # with a neighbour holding all but 20 GiB gets one binary at a time.
        lane = load_lane()
        hb = self._host_budget()
        busy = hb.Host("Darwin", 32, 256 * 2**30, 20 * 2**30, "test", 1.0)
        with mock.patch.object(lane.os, "cpu_count", return_value=32), \
                mock.patch.object(hb, "measure", return_value=busy):
            self.assertEqual(lane.default_jobs(), 1)

    def test_default_jobs_on_an_unmeasurable_host_is_one(self):
        lane = load_lane()
        hb = self._host_budget()
        with mock.patch.object(lane.os, "cpu_count", return_value=32), \
                mock.patch.object(hb, "measure", side_effect=hb.HostUnmeasurable("no vm_stat")):
            self.assertEqual(lane.default_jobs(), 1)


ZERO = "0" * 40
OUT_OF_SCOPE = "docs/notes.md"
ALPHA_LIB = "crates/alpha/src/lib.rs"
BETA_LIB = "crates/beta/src/lib.rs"


class TimeBoundTest(unittest.TestCase):
    """CRATES-TIME-1 (2026-10-28; scripts/lib/crates_tests_time.py): one time
    bound for the hook's lane and the land gate's leg, from the crates each run
    tests; a hung binary still ends the lane NOT JUDGED (the stall bound); a
    lane that is slow but still moving is never stopped for being slow; and the
    ceiling still ends one that moves forever. Measured cause: the flat 1200 s
    refused three pushes of a 3-member change on a loaded host (macOS's
    first-exec admission alone took up to 1157 s of it) while the same tree's
    gate leg ran under 8640 s and passed."""

    BOUND_VARS = ("TRUST_CRATES_TESTS_BUDGET_S", "TRUST_CRATES_TESTS_STALL_S")

    def setUp(self):
        self.lane = load_lane()
        self.saved = {k: os.environ.pop(k) for k in self.BOUND_VARS if k in os.environ}

    def tearDown(self):
        for k in self.BOUND_VARS:
            os.environ.pop(k, None)
        os.environ.update(self.saved)

    @staticmethod
    def _members(n):
        return {f"crates/m{i:02d}": f"m{i:02d}" for i in range(n)}

    def _python(self, code, name):
        return self.lane.Binary({"argv": [sys.executable, "-c", code], "cwd": os.getcwd(),
                                 "env": dict(os.environ)}, name)

    def _leftover_pidfile(self):
        """A file a test's leftover process writes its pid to; it is SIGKILLed
        at cleanup, so no stand-in outlives the test."""
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        pidfile = os.path.join(tmp.name, "leftover.pid")

        def kill():
            with contextlib.suppress(OSError, ValueError):
                os.kill(int(Path(pidfile).read_text().strip()), signal.SIGKILL)
        self.addCleanup(kill)
        return pidfile

    def test_the_hook_and_the_gate_get_one_bound_for_n_members(self):
        # The hook's lane plans the members a push touches; the land gate's leg
        # hands the lane the members a change reaches (--also-members, no
        # diff). For as many members, both get one bound, and never less than
        # either caller's rule before it (hook: a flat 1200 s; gate: max(1200,
        # 240 s x members)). Negative control: the hook's old flat 1200 s fails
        # here from 6 members on.
        for n in (1, 3, 5, 6, 36, 90):
            with self.subTest(members=n):
                members = self._members(n)
                hook = self.lane.plan_for([f"{d}/src/lib.rs" for d in members], members, [])
                gate = self.lane.plan_for([], members, [], also_dirs=list(members))
                self.assertEqual((hook.crates(), gate.crates()), (n, n))
                h, g = self.lane.plan_time_bound(hook, {}), self.lane.plan_time_bound(gate, {})
                self.assertEqual(h, g, "the hook and the land gate get different bounds")
                self.assertGreaterEqual(h[0], max(1200, 240 * n))
                self.assertGreater(h[1], 0)
                self.assertLessEqual(h[1], h[0], "a stall bound past the ceiling never fires")

    def test_a_caller_override_replaces_the_ceiling_for_either_caller(self):
        members = self._members(3)
        env = {"TRUST_CRATES_TESTS_BUDGET_S": "5400", "TRUST_CRATES_TESTS_STALL_S": "60"}
        for plan in (self.lane.plan_for([f"{d}/src/lib.rs" for d in members], members, []),
                     self.lane.plan_for([], members, [], also_dirs=list(members))):
            budget, stall, line = self.lane.plan_time_bound(plan, env)
            self.assertEqual((budget, stall), (5400, 60))
            self.assertIn("TRUST_CRATES_TESTS_BUDGET_S", line)
        for bad in ("0", "-5", "1.5", "soon"):
            with self.subTest(value=bad), self.assertRaises(ValueError):
                self.lane.plan_time_bound(plan, {"TRUST_CRATES_TESTS_STALL_S": bad})

    def test_an_instrument_host_counts_once(self):
        plan = self.lane.Plan()
        plan.packages = ["a", "b"]
        plan.instrument_runs = [("a", ["--lib"]), ("c", ["--lib"]), ("c", ["--test", "x"])]
        plan.own_workspaces = ["crates/own"]
        self.assertEqual(plan.crates(), 4)

    def test_a_hung_binary_ends_the_lane_not_judged_by_the_stall_bound(self):
        # Prints once, then hangs: with a ceiling of ten minutes the stall bound
        # (2 s) still kills it, the lane is not finished, and the binary queued
        # behind it never starts.
        hung = self._python("import time\nprint('running 1 test', flush=True)\ntime.sleep(60)\n", "hung")
        queued = self._python("pass\n", "queued")
        bound = self.lane.TimeBound(600, 2)
        t0 = time.monotonic()
        with contextlib.redirect_stdout(io.StringIO()) as out:
            finished = self.lane.run_binaries([hung, queued], 1, bound)
        self.assertLess(time.monotonic() - t0, 30, "the stall bound did not end the hung binary")
        self.assertFalse(finished)
        self.assertIsNone(hung.rc)
        self.assertIsNone(queued.rc, "a binary queued behind a stall must not start")
        self.assertLessEqual(bound.left(), 0)
        self.assertIn("STALLED", bound.why())
        self.assertIn("KILLED at the deadline", out.getvalue())

    def test_a_binary_that_keeps_printing_is_never_stopped_for_being_slow(self):
        # Six seconds of a line every 0.2 s, under a 2 s stall bound: it runs to
        # the end. (Under a fixed 2 s total, the old rule, it is killed.)
        code = ("import time\nprint('running 1 test', flush=True)\n"
                "for i in range(30):\n    time.sleep(0.2)\n    print(f'tick {i}', flush=True)\n"
                "print('test t ... ok\\n\\ntest result: ok. 1 passed; 0 failed;', flush=True)\n")
        slow = self._python(code, "slow")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(self.lane.run_binaries([slow], 1, self.lane.TimeBound(600, 2)))
        self.assertEqual(slow.rc, 0, slow.output)
        fixed = self._python(code, "fixed")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(self.lane.run_binaries([fixed], 1, time.monotonic() + 2))
        self.assertIsNone(fixed.rc)

    def test_the_ceiling_ends_a_lane_that_never_stops_printing(self):
        # A minute of a line every 0.1 s (finite, so a lane that ignores its
        # ceiling fails here rather than hanging the suite).
        chatter = self._python("import time\nfor i in range(600):\n    print('tick', flush=True)\n"
                               "    time.sleep(0.1)\n", "chatter")
        bound = self.lane.TimeBound(3, 600)
        t0 = time.monotonic()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(self.lane.run_binaries([chatter], 1, bound))
        self.assertLess(time.monotonic() - t0, 30, "the ceiling did not end the chatter")
        self.assertIsNone(chatter.rc)
        self.assertEqual(bound.why(), "the 3s budget ran out")

    def test_a_silent_build_is_bounded_by_the_ceiling_not_the_stall(self):
        # The record pass and the targo-trust build (run_with_deadline): one
        # rustc silent for long on a loaded host, or cargo waiting on another
        # build's lock, is latency, not a hang (review N4 of f51164ad14). A
        # build silent for 5 s under a 2 s stall bound runs to its end, and the
        # stall clock starts again when it ends; a silent build that never ends
        # is stopped by the ceiling.
        bound = self.lane.TimeBound(600, 2)
        with contextlib.redirect_stdout(io.StringIO()):
            rc, output = self.lane.run_with_deadline([sys.executable, "-c", "import time\ntime.sleep(5)\n"], bound)
        self.assertEqual(rc, 0, output)
        self.assertGreater(bound.left(), 1, "the stall clock did not start again when the build ended")
        bound = self.lane.TimeBound(4, 1)
        t0 = time.monotonic()
        with contextlib.redirect_stdout(io.StringIO()):
            rc, _ = self.lane.run_with_deadline([sys.executable, "-c", "import time\ntime.sleep(60)\n"], bound)
        self.assertIsNone(rc)
        self.assertLess(time.monotonic() - t0, 30, "the ceiling did not end the silent build")
        self.assertEqual(bound.why(), "the 4s budget ran out")

    def test_an_admitted_executable_is_progress(self):
        # One worker; the first binary is silent for 5 s while admission carries
        # the next eleven through macOS's check, 0.5 s each. Each admission is
        # progress, so a 3 s stall bound does not fire; without it, it would.
        lane = self.lane
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        names = [f"b{i:02d}-{i:016x}" for i in range(12)]
        binaries = [lane.Binary({"argv": [str(Path(tmp.name) / n)], "cwd": tmp.name, "env": {}},
                                f"     Running {n}") for n in names]

        def admit(exe, env, directory, deadline):
            time.sleep(0.5)
            return "admitted", ""

        def run_one(binary, deadline):
            # As the real run_one: its end is progress (its start is not), and
            # it kills a binary the bound runs out on (rc stays None).
            if binary is binaries[0]:
                quiet_until = time.monotonic() + 5
                while time.monotonic() < quiet_until:
                    if lane._left(deadline) <= 0:
                        return
                    time.sleep(0.05)
            binary.rc, binary.output = 0, "running 0 tests\n\ntest result: ok. 0 passed; 0 failed;\n"
            lane._progress(deadline)

        lane.ADMIT_PLATFORM = sys.platform
        os.environ.pop(lane.ADMIT_ENV, None)
        bound = lane.TimeBound(600, 3)
        with mock.patch.object(lane, "admit_one", side_effect=admit), \
                mock.patch.object(lane, "run_one", side_effect=run_one), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(lane.run_binaries(binaries, 1, bound))
        self.assertTrue(all(b.rc == 0 for b in binaries))

    def test_a_binary_ending_is_progress(self):
        # Five binaries that print nothing and take 1 s each, one at a time,
        # admission off: only their ends are progress, and a 3 s
        # stall bound must not fire across 5 s of them.
        os.environ[self.lane.ADMIT_ENV] = "0"
        self.addCleanup(os.environ.pop, self.lane.ADMIT_ENV, None)
        quiet = [self._python("import time\ntime.sleep(1)\n", f"quiet-{i}") for i in range(5)]
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(self.lane.run_binaries(quiet, 1, self.lane.TimeBound(600, 3)))
        self.assertEqual([b.rc for b in quiet], [0] * 5)

    def test_a_leftover_process_printing_does_not_hide_a_hang(self):
        # Review finding (f51164ad14): "hung" prints once and hangs silently;
        # "leaver" exits 0 at once, leaving a child that keeps writing to its
        # output every 0.3 s for ~40 s. Lines read after leaver ended are not
        # progress, so the 3 s stall bound ends the hang, not the 600 s ceiling.
        # Without the fix the leftover's lines kept the stall clock alive until
        # its loop ended.
        os.environ[self.lane.ADMIT_ENV] = "0"
        self.addCleanup(os.environ.pop, self.lane.ADMIT_ENV, None)
        hung = self._python("import time\nprint('running 1 test', flush=True)\ntime.sleep(60)\n", "hung")
        pidfile = self._leftover_pidfile()
        leaver = self.lane.Binary({"argv": ["/bin/sh", "-c",
                                            "(i=0; while [ $i -lt 130 ]; do echo tick; i=$((i+1)); sleep 0.3; done) & "
                                            f"echo $! > '{pidfile}'; "
                                            "printf 'running 0 tests\\n\\ntest result: ok. 0 passed; 0 failed;\\n'"],
                                   "cwd": os.getcwd(), "env": dict(os.environ)}, "leaver")
        bound = self.lane.TimeBound(600, 3)
        t0 = time.monotonic()
        with contextlib.redirect_stdout(io.StringIO()):
            finished = self.lane.run_binaries([hung, leaver], 2, bound)
        took = time.monotonic() - t0
        self.assertFalse(finished)
        self.assertIsNone(hung.rc)
        self.assertEqual(leaver.rc, 0, leaver.output)
        self.assertLess(took, 25, f"a leftover process's lines held the stall bound off for {took:.0f}s")
        self.assertIn("STALLED", bound.why())

    def test_a_build_leftover_printing_is_not_progress(self):
        # run_with_deadline (the record pass, targo-trust's build): nothing a
        # build prints is progress, so a process it left behind holding its
        # output open cannot keep the stall bound off the binaries after it.
        # The command leaves a child printing every 0.1 s for over a minute and
        # exits; run_with_deadline returns once its readers' 30 s join gives
        # up, while the child still prints, and the bound must still run out
        # on schedule after that.
        bound = self.lane.TimeBound(600, 2)
        pidfile = self._leftover_pidfile()
        cmd = ["/bin/sh", "-c", "(i=0; while [ $i -lt 700 ]; do echo tick; i=$((i+1)); sleep 0.1; done) 2>/dev/null & "
                                f"echo $! > '{pidfile}'; echo built"]
        # (messages=: cargo's JSON mode, which shows nothing, so the leftover's
        # lines do not reach the suite's own output after the call returns.)
        rc, _ = self.lane.run_with_deadline(cmd, bound, messages=[])
        self.assertEqual(rc, 0)
        deadline = time.monotonic() + 10
        while bound.left() > 0 and time.monotonic() < deadline:
            time.sleep(0.1)
        self.assertLessEqual(bound.left(), 0, "a build's leftover process kept the stall bound alive")
        self.assertIn("STALLED", bound.why())

    def test_the_barrier_wait_restarts_the_stall_clock(self):
        bound = self.lane.TimeBound(5, 1)
        time.sleep(1.5)
        self.assertLessEqual(bound.left(), 0)
        bound.extend(1.5)
        self.assertGreater(bound.left(), 0.5)


class TimeBoundMainTest(MainBase):
    def test_a_hung_binary_ends_main_not_judged_and_names_the_stall(self):
        os.environ["TRUST_CRATES_TESTS_STALL_S"] = "2"
        t0 = time.monotonic()
        rc, out, _ = self.run_main("hang", budget="600")
        self.assertLess(time.monotonic() - t0, 40, out)
        self.assertEqual(rc, 3, out)
        self.assertIn("NOT JUDGED: the lane STALLED", out)
        self.assertIn("not run to completion:", out)
        self.assertIn("crates-tests: time bound: stops after 2s with nothing progressing", out)

    def test_the_bound_line_names_the_rule_when_no_caller_sets_one(self):
        os.environ.pop("TRUST_CRATES_TESTS_STALL_S", None)
        os.environ["FAKE_TARGO_BUILD"], binaries = MODES["pass"]
        os.environ["FAKE_TARGO_BINARIES"] = ",".join(binaries)
        os.environ.pop("TRUST_CRATES_TESTS_BUDGET_S", None)
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = self.lane.main(["--range", "origin/main..HEAD"])
        self.assertEqual(rc, 0, out.getvalue())
        self.assertRegex(out.getvalue(), r"time bound: stops after 1800s with nothing progressing \(default; "
                                         r"TRUST_CRATES_TESTS_STALL_S replaces it\), or after 14400s in all "
                                         r"\(max\(14400, 900 s x 1 crate\(s\)\)")

    def test_a_bad_bound_cannot_judge(self):
        os.environ["TRUST_CRATES_TESTS_STALL_S"] = "soon"
        rc, out, calls = self.run_main("pass")
        self.assertEqual(rc, 2, out)
        self.assertIn("TRUST_CRATES_TESTS_STALL_S must be an integer", out)
        self.assertEqual(calls, [], "a lane that cannot bound itself built something")


class PushScopeTest(unittest.TestCase):
    """The lane's SCOPE against real git, in a throwaway repository.

    Each case builds a repository with two `crates/` members (alpha, beta),
    points the lane's REPO_ROOT at it, and runs main() with `--plan` and a fake
    `targo` whose only job is `targo metadata`: nothing is built or tested.
    "Ran" means the lane got past its scope decision and planned `-p <member>`;
    "skipped" means it printed `SKIPPED: `, which the harness grades SKIP.

    The cases are the defects scripts/check_compiler_targets_build.sh and
    scripts/check_completion_gate_tests.sh had fixed in b882c0a672 and
    3db0e0b0fd, which this lane still had until 2026-09-27: a pushed update read
    `<remote>...<local>` (since the merge base), so a force push that DROPS a
    crates/ change, or a rewind, skipped; rename detection listed a file moved
    out of a member only under its new path; a non-ASCII path came back
    C-quoted and matched no `crates/` prefix; a submodule-ignore setting hid a
    gitlink. A range that cannot be diffed must be red, never a skip.
    """

    def setUp(self):
        self.lane = load_lane()
        self.temp = tempfile.TemporaryDirectory()
        self.repo = Path(self.temp.name).resolve() / "repo"
        self.saved = dict(os.environ)
        # No operator config, and no GIT_DIR/GIT_INDEX_FILE or push context from
        # an enclosing pre-push hook: those would point the lane's git calls at
        # the real repository.
        for key in list(os.environ):
            if key.startswith(("GIT_", "TRUST_PUSH")):
                del os.environ[key]
        os.environ.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        os.environ["PATH"] = f"{FakeTargo.directory()}{os.pathsep}{os.environ['PATH']}"
        meta = Path(self.temp.name) / "meta.json"
        meta.write_text(json.dumps({
            "workspace_members": ["alpha-id", "beta-id"], "workspace_default_members": ["alpha-id", "beta-id"],
            "packages": [
                {"id": f"{n}-id", "name": n, "manifest_path": str(self.repo / "crates" / n / "Cargo.toml")}
                for n in ("alpha", "beta")
            ],
        }), encoding="utf-8")
        os.environ["FAKE_TARGO_METADATA"] = str(meta)
        os.environ["FAKE_TARGO_LOG"] = str(Path(self.temp.name) / "calls.log")
        self.git_raw("init", "--quiet", "--initial-branch=main", str(self.repo))
        self.git("config", "user.name", "scope-test")
        self.git("config", "user.email", "scope-test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        # git's defaults, set so the controls below cannot drift with them.
        self.git("config", "diff.renames", "true")
        self.git("config", "core.quotePath", "true")
        self.base = self.commit({
            "README.md": "fixture\n",
            OUT_OF_SCOPE: "notes\n",
            "Cargo.toml": '[workspace]\nmembers = ["crates/alpha", "crates/beta"]\ndefault-members = ["crates/alpha", "crates/beta"]\n',
            "crates/alpha/Cargo.toml": '[package]\nname = "alpha"\n',
            "crates/beta/Cargo.toml": '[package]\nname = "beta"\n',
            ALPHA_LIB: "pub fn alpha() -> u32 { 1 }\n" * 8,
            BETA_LIB: "pub fn beta() -> u32 { 2 }\n" * 8,
        }, "base")
        self.git("update-ref", "refs/remotes/origin/main", self.base)
        self.lane.REPO_ROOT = self.repo

    def tearDown(self):
        os.environ.clear()
        os.environ.update(self.saved)
        self.temp.cleanup()

    # -- fixture helpers ----------------------------------------------------

    def git_raw(self, *args, check=True):
        return subprocess.run(
            ["git", *args], text=True, capture_output=True, check=check, timeout=30,
        ).stdout.strip()

    def git(self, *args, check=True):
        return self.git_raw("-C", str(self.repo), *args, check=check)

    def commit(self, files, message):
        for path, content in files.items():
            target = self.repo / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")
            self.git("add", "--", path)
        self.git("commit", "--quiet", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def branch(self, name, start, files, message):
        self.git("checkout", "--quiet", "-B", name, start)
        return self.commit(files, message)

    @staticmethod
    def ref_line(ref, local, remote):
        return f"{ref} {local} {ref} {remote}"

    def run_lane(self, *args, pushed=None):
        if pushed is None:
            os.environ.pop("TRUST_PUSHED_REFS", None)
        else:
            os.environ["TRUST_PUSHED_REFS"] = pushed
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = self.lane.main([*args, "--plan"])
        return rc, out.getvalue()

    def test_fixture_only_real_git_range_selects_the_binary_instrument(self):
        host = "trust-integration-tests"
        manifest = f"crates/{host}/Cargo.toml"
        base = self.commit({manifest: f'[package]\nname = "{host}"\n'}, "consumer")
        meta_path = Path(self.temp.name) / "meta.json"
        meta = json.loads(meta_path.read_text())
        meta["workspace_members"].append("integration-id")
        meta["workspace_default_members"].append("integration-id")
        meta["packages"].append({"id": "integration-id", "name": host,
                                 "manifest_path": str(self.repo / manifest)})
        meta_path.write_text(json.dumps(meta))
        tip = self.commit({"tests/fixtures/binary_decomp/x86_64-load-elf.hex": "00\n"}, "fixture")
        rc, out = self.run_lane("--range", f"{base}..{tip}")
        self.assertEqual(rc, 0, out)
        self.assertNotIn("SKIPPED:", out)
        self.assertIn("prebuild: targo-trust, whose copy the tests of trust-integration-tests", out)
        self.assertIn("-p trust-integration-tests --test binary_to_trust_ir_e2e", out)

    def assert_runs(self, result, *members):
        rc, out = result
        self.assertIsNone(re.search(r"(?m)^\s*SKIPPED: ", out), f"SKIPPED where in scope:\n{out}")
        self.assertEqual(rc, 0, out)
        match = re.search(r"(?m)^in scope: \d+ crates/ member\(s\): (.*)$", out)
        self.assertIsNotNone(match, f"no member planned:\n{out}")
        self.assertEqual(match.group(1).split(", "), sorted(members), out)
        self.assertIn("would run: ", out)

    def assert_skipped(self, result):
        rc, out = result
        self.assertEqual(rc, 0, out)
        self.assertRegex(out, r"(?m)^SKIPPED: ")
        self.assertNotIn("would run: ", out)

    def assert_red_not_skipped(self, result, fragment):
        rc, out = result
        self.assertNotEqual(rc, 0, f"an undiffable range must be red:\n{out}")
        self.assertIsNone(re.search(r"(?m)^\s*SKIPPED: ", out), out)
        self.assertIn(fragment, out)

    # -- (1) the subject of a pushed update is its tree diff ------------------

    def test_a_force_push_that_drops_a_crates_change_runs_that_member(self):
        for dropped in ("edit", "add"):
            with self.subTest(dropped=dropped):
                path = ALPHA_LIB if dropped == "edit" else "crates/alpha/src/added_on_remote.rs"
                remote = self.branch(f"remote-{dropped}", self.base, {path: "remote only\n"}, "alpha work")
                forced = self.branch(f"forced-{dropped}", self.base, {OUT_OF_SCOPE: "rewritten\n"}, "docs")
                # Control: since the merge base the push adds only the docs.
                self.assertEqual(
                    self.git("diff", "--no-renames", "--name-only", f"{remote}...{forced}"), OUT_OF_SCOPE
                )
                rc, out = result = self.run_lane(
                    "--push-context", pushed=self.ref_line("refs/heads/topic", forced, remote)
                )
                self.assert_runs(result, "alpha")
                self.assertIn(f"{remote}..{forced}", out)
                self.assertNotIn(f"{remote}...{forced}", out)

    def test_a_rewind_runs_the_member_it_takes_back(self):
        # local is an ancestor of remote: the three-dot diff is empty.
        remote = self.branch("rewound", self.base, {BETA_LIB: "landed\n"}, "beta work")
        self.git("checkout", "--quiet", "-B", "rewound", self.base)
        self.assertEqual(self.git("diff", "--name-only", f"{remote}...{self.base}"), "")
        self.assert_runs(
            self.run_lane("--push-context", pushed=self.ref_line("refs/heads/rewound", self.base, remote)),
            "beta",
        )

    def test_a_fast_forward_docs_push_still_skips(self):
        # Control: for a fast-forward the tree diff is the merge-base diff. The
        # remote already has the alpha change, so a docs commit on top skips,
        # though origin/main...HEAD (the fallback) would run.
        remote = self.branch("ff", self.base, {ALPHA_LIB: "landed\n"}, "alpha")
        local = self.commit({OUT_OF_SCOPE: "docs on top\n"}, "docs")
        self.assert_skipped(self.run_lane("--push-context", pushed=self.ref_line("refs/heads/ff", local, remote)))
        code = self.commit({BETA_LIB: "more\n"}, "beta")
        self.assert_runs(
            self.run_lane("--push-context", pushed=self.ref_line("refs/heads/ff", code, local)), "beta"
        )

    def test_a_push_of_a_document_outside_crates_runs_its_corpus_gate(self):
        # 2026-10-08: the lane SKIPPED every push with no crates/ path, so a
        # reports/*.json (or a tests/js262/ change, a CROSS_CRATE_INSTRUMENTS
        # subject) reached no gate that measures it.
        remote = self.branch("doc", self.base, {OUT_OF_SCOPE: "docs\n"}, "docs")
        local = self.commit({"reports/r.json": "{}\n"}, "report")
        rc, out = self.run_lane("--push-context", pushed=self.ref_line("refs/heads/doc", local, remote))
        self.assertEqual(rc, 0, out)
        self.assertIsNone(re.search(r"(?m)^\s*SKIPPED: ", out), out)
        self.assertIn("cross-crate instrument: trust-json --test acceptance_gate", out)
        self.assertIn("would run: ", out)

    def test_a_new_branch_is_judged_since_its_fork(self):
        # New branches keep origin/main...<local>, pinned both ways: the
        # two-dot origin/main..<local> would run (a) and skip (b).
        landed = self.branch("main2", self.base, {ALPHA_LIB: "landed\n"}, "landed")
        self.git("update-ref", "refs/remotes/origin/main", landed)
        stale = self.branch("stale", self.base, {OUT_OF_SCOPE: "docs\n"}, "docs")
        rc, out = result = self.run_lane("--push-context", pushed=self.ref_line("refs/heads/stale", stale, ZERO))
        self.assert_skipped(result)
        self.assertIn(f"origin/main...{stale}", out)
        pick = self.branch("pick", self.base, {ALPHA_LIB: "landed\n", OUT_OF_SCOPE: "docs\n"}, "pick")
        self.assertEqual(self.git("diff", "--name-only", f"origin/main..{pick}"), OUT_OF_SCOPE)
        self.assert_runs(
            self.run_lane("--push-context", pushed=self.ref_line("refs/heads/pick", pick, ZERO)), "alpha"
        )

    def test_explicit_range_and_standing_reading_stay_three_dot(self):
        self.branch("topic", self.base, {BETA_LIB: "x\n"}, "beta")
        rc, out = result = self.run_lane("--range", f"{self.base}..HEAD")
        self.assert_runs(result, "beta")
        self.assertIn(f"SUBJECT (explicit --range): {self.base}...HEAD", out)
        rc, out = result = self.run_lane("--push-context")
        self.assert_runs(result, "beta")
        self.assertIn("origin/main...HEAD", out)

    # -- (2) attribution survives moves, odd paths and ignore settings -----------

    def test_a_move_out_of_a_member_attributes_the_old_member(self):
        self.git("checkout", "--quiet", "-B", "move-out", self.base)
        self.git("mv", ALPHA_LIB, "docs/alpha_lib.rs")
        moved = self.commit({}, "move out of alpha")
        # Control: rename detection lists only the new, out-of-scope path.
        self.assertEqual(self.git("diff", "--name-only", f"{self.base}...HEAD"), "docs/alpha_lib.rs")
        self.assert_runs(self.run_lane(), "alpha")
        self.assert_runs(
            self.run_lane("--push-context", pushed=self.ref_line("refs/heads/move-out", moved, self.base)),
            "alpha",
        )
        # Across members: both the member it left and the one it joined.
        self.git("checkout", "--quiet", "-B", "move-across", self.base)
        self.git("mv", ALPHA_LIB, "crates/beta/src/from_alpha.rs")
        self.commit({}, "move alpha -> beta")
        self.assert_runs(self.run_lane(), "alpha", "beta")

    def test_a_non_ascii_path_is_attributed(self):
        self.branch("accent", self.base, {"crates/alpha/src/é.rs": "fn e() {}\n"}, "accent")
        # Control: without -z git C-quotes the path, leading quote included.
        self.assertTrue(self.git("diff", "--name-only", f"{self.base}...HEAD").startswith('"'))
        self.assert_runs(self.run_lane(), "alpha")

    def test_a_submodule_ignore_setting_does_not_hide_a_gitlink_in_a_member(self):
        # No member holds a gitlink today; if one ever does, a moved pin under
        # crates/<member>/ is that member's change, and diff.ignoreSubmodules
        # must not hide it (first-party/ pins are only disclosed, never tested).
        self.git("checkout", "--quiet", "-B", "pin", self.base)
        self.git("update-index", "--add", "--cacheinfo", f"160000,{self.base},crates/alpha/vendored")
        self.commit({}, "gitlink in alpha")
        self.git("config", "diff.ignoreSubmodules", "all")
        self.assertEqual(self.git("diff", "--name-only", f"{self.base}...HEAD"), "")
        self.assert_runs(self.run_lane(), "alpha")

    # -- (3) a range that cannot be diffed is red, never a skip ----------------

    def test_an_undiffable_range_is_red_never_skipped(self):
        docs = self.branch("docs", self.base, {OUT_OF_SCOPE: "docs\n"}, "docs")
        # A force push over a remote tip this clone never fetched.
        missing = "1" * 40
        bad = self.ref_line("refs/heads/docs", docs, missing)
        self.assert_red_not_skipped(self.run_lane("--push-context", pushed=bad), "could NOT READ")
        # One good range does not launder a bad one in the same push.
        good = self.ref_line("refs/heads/docs", docs, self.base)
        self.assert_skipped(self.run_lane("--push-context", pushed=good))
        self.assert_red_not_skipped(self.run_lane("--push-context", pushed=good + "\n" + bad), "could NOT READ")
        # No merge base for an explicit range.
        self.git("checkout", "--quiet", "--orphan", "orphan")
        orphan = self.commit({}, "unrelated history")
        self.git("checkout", "--quiet", "-f", "docs")
        self.assert_red_not_skipped(self.run_lane("--range", f"{orphan}..HEAD"), "could NOT READ")
        # No origin/main under the standing reading.
        self.git("update-ref", "-d", "refs/remotes/origin/main")
        self.assert_red_not_skipped(self.run_lane(), "could NOT READ")


class KnownRedTest(unittest.TestCase):
    """The known-red ratchet: listed failures are excused, new ones and stale rows fail."""

    def test_parse_results_keys_failures_by_binary(self):
        lane = load_lane()
        failed, passed = lane.parse_results(
            "     Running unittests src/lib.rs (crates/target/debug/deps/trust_router-8a42b0c1d2e3f405)\n"
            "test incremental_ay::tests::x ... FAILED\n"
            "test coordinator::tests::y ... ok\n"
            "     Running tests/formula_compat_gate.rs (crates/target/debug/deps/formula_compat_gate-16262473aa93c5dd)\n"
            "test retained_formula_families_route_to_compatible_backends ... FAILED\n"
        )
        self.assertEqual(failed, {
            "trust_router::incremental_ay::tests::x",
            "formula_compat_gate::retained_formula_families_route_to_compatible_backends",
        })
        self.assertEqual(passed, {"trust_router::coordinator::tests::y"})

    def test_known_red_file_rows_and_flaky_tag(self):
        lane = load_lane()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "known.txt"
            path.write_text(
                "# comment\n\ngate::mod_a::listed  # pre-existing on main (owner: t-new-tests)\n"
                "gate::mod_c::slow  # load-sensitive [flaky]\n", encoding="utf-8")
            self.assertEqual(lane.load_known_red(path), {"gate::mod_a::listed": False, "gate::mod_c::slow": True})

    def _main_with(self, mode, known):
        case = MainTest("test_green_runs_both_router_lanes")
        case.setUp()
        try:
            case.lane.load_known_red = lambda path: known
            return case.run_main(mode)
        finally:
            case.tearDown()

    def test_a_listed_failure_is_excused(self):
        rc, out, _ = self._main_with("known", {"gate::mod_a::listed": False})
        self.assertEqual(rc, 0, out)
        self.assertIn("known red", out)

    def test_an_unlisted_failure_fails_the_lane(self):
        rc, out, _ = self._main_with("new", {"gate::mod_a::listed": False})
        self.assertEqual(rc, 1, out)
        self.assertIn("NEW FAILURE: gate::mod_b::fresh", out)

    def test_a_crashed_binary_is_not_excused_by_another_binarys_known_red(self):
        rc, out, _ = self._main_with("crash", {"gate::mod_a::listed": False})
        self.assertEqual(rc, 1, out)
        self.assertIn("BINARY FAILED OUTSIDE ITS TEST LINES (exit 134 with no libtest run", out)
        self.assertIn("abort-0000000000000001", out)
        # Why the per-binary check exists: cargo's one exit code over the same
        # output is excused by the gate's listed failure alone.
        text = (
            "     Running tests/gate.rs (d/gate-00000000000000f0)\n"
            "test mod_a::listed ... FAILED\ntest mod_b::fresh ... ok\n"
            "     Running tests/abort.rs (d/abort-0000000000000001)\n"
            "thread 'main' panicked at src/main.rs:1:1: a harness = false check failed\n"
        )
        self.assertTrue(load_lane().judge(101, text, {"gate::mod_a::listed": False})[0])
        # Control: the gate alone, with its listed failure, is still excused.
        rc, out, _ = self._main_with("known", {"gate::mod_a::listed": False})
        self.assertEqual(rc, 0, out)
        self.assertNotIn("BINARY FAILED", out)

    def test_a_binary_that_dies_after_a_known_red_line_fails(self):
        # Each prints its listed failure, then dies before its second test
        # reports: SIGKILL (jetsam or the OOM killer under the pool) and a
        # process::exit(101). judge() alone excuses both, on the listed line.
        for mode, binary, why in (("killed", "killed", "exit -9 is not libtest's 0 or 101"),
                                  ("exited", "exited", "exit 101 without libtest's closing")):
            with self.subTest(mode=mode):
                known = {f"{binary}::mod_a::listed": False}
                rc, out, _ = self._main_with(mode, known)
                self.assertEqual(rc, 1, out)
                self.assertIn(f"known red (listed in tests/known-red/crates-tests.txt): {binary}::mod_a::listed", out)
                self.assertIn(why, out)
                text = f"     Running tests/{binary}.rs (d/{binary}-0000000000000007)\ntest mod_a::listed ... FAILED\n"
                self.assertTrue(load_lane().judge(101, text, known)[0], "the hole this closes")

    def test_a_failed_record_pass_is_not_excused_by_a_known_red(self):
        # The build-and-record pass runs no test, so its exit code is never a
        # test failure; before, the gate's listed failure excused it.
        rc, out, _ = self._main_with("record-rc", {"gate::mod_a::listed": False})
        self.assertEqual(rc, 1, out)
        self.assertIn("THE BUILD-AND-RECORD PASS EXITED 101", out)
        self.assertIn("known red (listed", out)

    def test_binary_problem_holds_each_binary_to_libtests_contract(self):
        lane = load_lane()
        ran = "running 2 tests\n"
        ok_end = "\ntest result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n"
        bad_end = "\ntest result: FAILED. 1 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out\n"
        two_bad = "\ntest result: FAILED. 0 passed; 2 failed; 0 ignored; 0 measured; 0 filtered out\n"
        cases = [
            (0, ran + "test a ... ok\ntest b ... ok\n" + ok_end, None),
            (101, ran + "test a ... FAILED\ntest b ... ok\n" + bad_end, None),
            (101, ran + "test a - should panic ... FAILED\ntest b ... ok\n" + bad_end, None),
            (0, "", None),  # harness = false, exit 0
            (-9, ran + "test a ... FAILED\n", "not libtest's 0 or 101"),
            (134, ran + "test a ... ok\n", "not libtest's 0 or 101"),
            (101, ran + "test a ... FAILED\n", "without libtest's closing `test result: FAILED.`"),
            (0, ran + "test a ... ok\n", "without libtest's closing `test result: ok.`"),
            (0, ran + "test a ... FAILED\n" + bad_end, "without libtest's closing `test result: ok.`"),
            (101, ran + "test a ... FAILED\ntest b ... [child]FAILED\n" + two_bad, "libtest counted 2 failure(s), the lane read 1"),
            (101, ran + "test a ... ok\n" + bad_end, "no test failure the lane could read"),
            (134, "thread 'main' panicked\n", "no libtest run"),
        ]
        for rc, output, want in cases:
            with self.subTest(rc=rc, output=output):
                binary = lane.Binary({"argv": ["d/t-0123456789abcdef"], "cwd": ".", "env": {}},
                                     "     Running tests/t.rs (d/t-0123456789abcdef)")
                binary.rc, binary.output = rc, output
                problem = lane.binary_problem(binary)
                if want is None:
                    self.assertIsNone(problem)
                else:
                    self.assertIsNotNone(problem)
                    self.assertIn(want, problem)

    def test_a_should_panic_failure_is_read_and_keyed(self):
        failed, passed = load_lane().parse_results(
            "     Running tests/t.rs (d/t-0123456789abcdef)\n"
            "test m::panics - should panic ... FAILED\ntest m::also - should panic ... ok\n")
        self.assertEqual((failed, passed), ({"t::m::panics"}, {"t::m::also"}))

    def test_a_binary_whose_output_ends_mid_line_does_not_swallow_the_next(self):
        lane = load_lane()
        first = lane.Binary({"argv": ["d/a-0123456789abcdef"], "cwd": ".", "env": {}},
                            "     Running tests/a.rs (d/a-0123456789abcdef)")
        second = lane.Binary({"argv": ["d/b-0123456789abcdef"], "cwd": ".", "env": {}},
                             "     Running tests/b.rs (d/b-0123456789abcdef)")
        first.rc, first.output = 0, "no newline at the end"
        second.rc, second.output = 101, "running 1 test\ntest x ... FAILED\n\ntest result: FAILED. 0 passed; 1 failed;\n"
        ok, report, _ = lane.judge_command(0, [first, second], {"a::x": False})
        self.assertFalse(ok, report)
        self.assertIn("NEW FAILURE: b::x", report)

    def test_a_listed_test_that_passes_is_a_stale_row(self):
        rc, out, _ = self._main_with("stale", {"gate::mod_a::listed": False})
        self.assertEqual(rc, 1, out)
        self.assertIn("STALE KNOWN-RED ROW", out)
        rc, out, _ = self._main_with("stale", {"gate::mod_a::listed": True})
        self.assertEqual(rc, 0, out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
