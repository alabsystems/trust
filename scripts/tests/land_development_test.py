#!/usr/bin/env python3
"""Explicit development scope, real caller and refusal controls (no Rust builds)."""
import argparse
import contextlib
import io
from pathlib import Path
import sys
import json
import copy
import hashlib
import inspect
import os
import tempfile
import shutil
import subprocess
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lib"))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import land_gate as gate
import land_development as development
import land_select as ls
from scripts.tests import land_gate_test as fixtures


class DevelopmentCustodyTests(unittest.TestCase):
    def test_actual_leg_retains_only_advertised_descriptors(self):
        descriptors = [*os.pipe(), *os.pipe(), *os.pipe()]
        gnu_read, gnu_write, lease_read, lease_write, other_read, _other_write = descriptors
        try:
            os.set_inheritable(other_read, True)
            env = {"PATH": os.defpath,
                   "CARGO_MAKEFLAGS": f"--jobserver-auth={gnu_read},{gnu_write}",
                   "TRUST_CPU_IMPLICIT_FD": str(lease_read), "ATERM_SDK_LEASE_V3": str(lease_write)}
            actual = {fd: [os.fstat(fd).st_dev, os.fstat(fd).st_ino] for fd in descriptors[:-1]}
            probe = ("import os,sys,json\nexpected=json.loads(sys.argv[1])\n"
                     "for fd in sys.argv[2:6]:\n s=os.fstat(int(fd));assert [s.st_dev,s.st_ino]==expected[fd]\n"
                     "try:\n s=os.fstat(int(sys.argv[6]))\n"
                     "except OSError: pass\n"
                     "else: assert [s.st_dev,s.st_ino]!=expected[sys.argv[6]],'unadvertised fd leaked'\n"
                     "print('LEG-DESCRIPTORS-RETAINED')\n")
            command = [sys.executable, "-c", probe, json.dumps(actual), *map(str, descriptors[:-1])]
            leg = fixtures.leg(id="push-rows", command=command)
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                output = io.StringIO()
                with mock.patch.object(gate, "REPO_ROOT", root), \
                     mock.patch.object(gate, "leg_environment", return_value=env), \
                     contextlib.redirect_stdout(io.StringIO()):
                    result = gate._run_one(leg, command, output, {}, (1, 2), root)
                self.assertEqual(result, 0, output.getvalue())
                self.assertIn("LEG-DESCRIPTORS-RETAINED", output.getvalue())
        finally:
            for fd in descriptors:
                os.close(fd)

    def test_closed_advertised_leg_locator_refuses_before_spawning(self):
        read, write = os.pipe()
        os.close(read)
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                env = {"PATH": os.defpath, "ATERM_SDK_LEASE_V3": str(read)}
                command = [sys.executable, "-c", "raise SystemExit('must not run')"]
                leg = fixtures.leg(id="push-rows", command=command)
                with mock.patch.object(gate, "REPO_ROOT", root), \
                     mock.patch.object(gate, "leg_environment", return_value=env), \
                     mock.patch.object(gate.subprocess, "Popen", side_effect=AssertionError("must not spawn")) as spawn:
                    with self.assertRaisesRegex(RuntimeError, "descriptor is not live"):
                        gate._run_one(leg, command, io.StringIO(), {}, (1, 2), root)
                spawn.assert_not_called()
        finally:
            os.close(write)


class TestMethodOwnershipTests(unittest.TestCase):
    SOURCE = ("import unittest\nFLAG = 1\n"
              "class CoverageLegTests(unittest.TestCase):\n"
              "    def test_budget(self):\n        self.assertEqual(5, 5)\n"
              "    def fixture(self):\n        return 1\n"
              "class UnknownTests(unittest.TestCase):\n"
              "    def test_other(self):\n        self.assertTrue(True)\n")

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        files = dict(fixtures.FILES, **{development.TEST_BODY_PROGRAM: self.SOURCE})
        self.base = fixtures.make_repo(self.root, files, symlinks={})

    def scoped(self, source):
        (self.root / development.TEST_BODY_PROGRAM).write_text(source)
        environment = dict(os.environ, **fixtures.FIXTURE_GIT_ENV)
        for arguments in (("add", "-A"), ("commit", "-qm", "method fixture", "--allow-empty")):
            subprocess.run(["git", "-C", str(self.root), *arguments], env=environment,
                           check=True, capture_output=True)
        head = ls.git(str(self.root), "rev-parse", "HEAD").decode().strip()
        graph = ls.build_graph(ls.TreeIndex.load(str(self.root), head))
        selected = ls.select(graph, self.base, [development.TEST_BODY_PROGRAM])
        return development.scope(graph, selected)

    def test_actual_method_body_selects_its_class_and_full_diagnostics_stay_full(self):
        scope = self.scoped(self.SOURCE.replace("assertEqual(5, 5)", "assertEqual(2, 2)"))
        self.assertFalse(scope.errors)
        self.assertEqual(scope.tests, ["scripts.tests.land_gate_test.CoverageLegTests"])
        self.assertEqual(ls.validation_test_modules([development.TEST_BODY_PROGRAM]),
                         ["scripts.tests.land_development_test", "scripts.tests.land_gate_test"])

    def test_registered_new_classes_and_methods_have_executed_owners(self):
        added = self.SOURCE + ("class DiscoverySnapshotTests(unittest.TestCase):\n"
                               "    def test_new_snapshot(self):\n        self.assertTrue(True)\n")
        scope = self.scoped(added)
        self.assertFalse(scope.errors)
        self.assertEqual(scope.tests, ["scripts.tests.land_gate_test.DiscoverySnapshotTests"])
        added = self.SOURCE.replace("    def fixture(self):",
                                    "    def test_more(self):\n        self.assertTrue(True)\n"
                                    "    def fixture(self):")
        scope = self.scoped(added)
        self.assertFalse(scope.errors)
        self.assertEqual(scope.tests, ["scripts.tests.land_gate_test.CoverageLegTests"])

    def test_publication_dispatch_and_outcome_changes_run_their_complete_owners(self):
        for owner in ("FailFastTests", "CacheOutcomeTests"):
            with self.subTest(owner=owner):
                source = self.SOURCE + (f"class {owner}(unittest.TestCase):\n"
                                        "    def test_publication(self):\n        self.assertTrue(True)\n")
                scope = self.scoped(source)
                self.assertFalse(scope.errors)
                module = "scripts.tests.land_gate_test." + owner
                self.assertEqual(scope.tests, [module])
                self.assertIn(module, development.PROGRAM_TESTS["scripts/land_gate.py"])

    def test_unknown_structural_and_fixture_changes_refuse(self):
        changed = self.SOURCE.replace("assertEqual(5, 5)", "assertEqual(2, 2)")
        for source in (changed.replace("FLAG = 1", "FLAG = 2"), "import sys\n" + changed,
                       changed.replace("return 1", "return 2"),
                       changed.replace("test_budget(self)", "test_budget(self, other=None)"),
                       changed.replace("assertTrue(True)", "assertTrue(False)"),
                       changed + "class NewTests(unittest.TestCase):\n    def test_new(self): pass\n"):
            with self.subTest(source=source):
                self.assertTrue(self.scoped(source).errors)

    def test_missing_syntax_and_empty_changed_population_refuse(self):
        for source in (self.SOURCE, self.SOURCE + "# comment only\n", self.SOURCE + "invalid syntax!\n",
                       self.SOURCE.replace("    def test_budget(self):\n        self.assertEqual(5, 5)\n", "")):
            with self.subTest(source=source):
                self.assertTrue(self.scoped(source).errors)

    def test_exact_gate_first_bootstrap_orders_both_owners_and_rejects_other_structure(self):
        source = "import host_budget\nimport land_gate\n" + self.SOURCE + (
            "class DiscoverySnapshotTests(unittest.TestCase):\n"
            "    def test_snapshot(self): self.assertTrue(True)\n"
            "class ScalerTests(unittest.TestCase):\n"
            "    def test_scale(self): self.assertTrue(True)\n")
        self.scoped(source)
        self.base = ls.git(str(self.root), "rev-parse", "HEAD").decode().strip()
        gate_first = source.replace("import host_budget\nimport land_gate\n", "import land_gate\nimport host_budget\n")
        scope = self.scoped(gate_first)
        self.assertFalse(scope.errors)
        self.assertEqual(scope.tests, ["scripts.tests.land_gate_test.DiscoverySnapshotTests",
                                       "scripts.tests.land_gate_test.ScalerTests"])
        self.assertTrue(self.scoped(gate_first.replace("import host_budget", "import host_budget as budget")).errors)
        self.assertTrue(self.scoped("import sys\n" + gate_first).errors)
        self.scoped(gate_first)
        self.base = ls.git(str(self.root), "rev-parse", "HEAD").decode().strip()
        self.assertTrue(self.scoped(source).errors)


def skip_if_lapsed(test: unittest.TestCase, row: dict) -> None:
    """A row marked `lapsed` grants nothing and claims no currency: a landing
    moved one of its pins without renewing it, and said so in the row
    (LEDGER-PIN-CURRENCY-AT-LANDING-1). Its live-tree checks wait for the
    renewal that deletes the marker; a blob that differs is never a skip."""
    if "lapsed" in row:
        test.skipTest(f"{row['file']} is lapsed: {row['lapsed'][:160]}")


class BootstrapFixtureAuditTests(unittest.TestCase):
    SOURCE = "src/bootstrap/src/utils/trust_source_identity/tests.rs"

    def test_guard_only_change_expires_all_three_exact_bootstrap_audits(self):
        root = Path(__file__).resolve().parents[2]
        rows = {row["file"]: row for row in ls.tomllib.loads((root / ls.AUDITS_FILE).read_text())["audit"]}
        guard = "src/bootstrap/src/utils/exec.rs"
        for source in (self.SOURCE, "src/bootstrap/src/core/build_steps/install/wp/transaction.rs",
                       "src/bootstrap/src/utils/trust_repo_cache.rs"):
            with self.subTest(source=source):
                row = rows[source]
                skip_if_lapsed(self, row)
                self.assertIn(guard, [pin["file"] for pin in row["premises"]])
                files = {path: (root / path).read_bytes() for path in [source, *(p["file"] for p in row["premises"])]}
                entries = {path: ("100644", hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest())
                           for path, data in files.items()}
                graph = ls.Graph(ls.TreeIndex(str(root), "fixture", "fixture", entries), {}, {}, [], {}, {})
                self.assertTrue(ls.audit_holds(graph, source, row))
                # The caller and every other premise stay byte-identical.
                graph.index.entries[guard] = ("100644", "0" * 40)
                self.assertFalse(ls.audit_holds(graph, source, row))

    def test_cache_caller_only_changes_expire_its_reviewed_row(self):
        root = Path(__file__).resolve().parents[2]
        source = "src/bootstrap/src/utils/trust_repo_cache.rs"
        row = next(row for row in ls.tomllib.loads((root / ls.AUDITS_FILE).read_text())["audit"]
                   if row["file"] == source)
        skip_if_lapsed(self, row)
        files = {path: (root / path).read_bytes() for path in [source, *(p["file"] for p in row["premises"])]}
        entries = {path: ("100644", hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest())
                   for path, data in files.items()}
        # llvm.rs's callers of this file moved partly into its child modules
        # (LLVM-RS-FILELENGTH-1); BOOTSTRAP-AUDIT-RENEWAL-2 pins all four.
        for caller in ("src/bootstrap/src/core/build_steps/repo.rs",
                       "src/bootstrap/src/core/build_steps/frontend_runtime.rs",
                       "src/bootstrap/src/core/build_steps/llvm.rs",
                       "src/bootstrap/src/core/build_steps/llvm/source_recipe.rs",
                       "src/bootstrap/src/core/build_steps/llvm/reuse_evidence.rs",
                       "src/bootstrap/src/core/build_steps/llvm/cmake_plan.rs",
                       "src/bootstrap/src/core/build_steps/llvm/installed_outputs.rs"):
            with self.subTest(caller=caller):
                self.assertIn(caller, files)
                graph = ls.Graph(ls.TreeIndex(str(root), "fixture", "fixture", dict(entries)), {}, {}, [], {}, {})
                self.assertTrue(ls.audit_holds(graph, source, row))
                graph.index.entries[caller] = ("100644", "0" * 40)
                self.assertFalse(ls.audit_holds(graph, source, row))

    def graph(self):
        root = Path(__file__).resolve().parents[2]
        raw = (root / ls.AUDITS_FILE).read_bytes()
        row = next(row for row in ls.tomllib.loads(raw.decode())["audit"] if row["file"] == self.SOURCE)
        skip_if_lapsed(self, row)
        files = {self.SOURCE: (root / self.SOURCE).read_bytes(),
                 "docs/DECISION_QUEUE.md": (root / "docs/DECISION_QUEUE.md").read_bytes()}
        files.update({pin["file"]: (root / pin["file"]).read_bytes() for pin in row["premises"]})
        entries = {path: ("100644", hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest())
                   for path, data in files.items()}
        graph = ls.Graph(ls.TreeIndex(str(root), "fixture", "fixture", entries),
                         {"src/bootstrap": ls.Package("src/bootstrap", "bootstrap"),
                          "src/tools/targo": ls.Package("src/tools/targo", "targo")}, {}, [], {}, {})
        with mock.patch.object(ls, "AUDITS_OVERRIDE", raw):
            audits = ls.load_audits(graph)
        self.assertIn(self.SOURCE, audits)
        self.assertTrue(ls.audit_holds(graph, self.SOURCE, audits[self.SOURCE]))
        return graph, audits, files

    def test_reviewed_real_reads_listings_and_foreign_compilation_survive(self):
        graph, audits, files = self.graph()
        package = graph.packages["src/bootstrap"]
        ls._scan_one(graph, package, self.SOURCE, files, audits, set())
        self.assertTrue(any(r.target == "scripts" and not r.listing for r in package.reads))
        self.assertTrue(any(r.target == "*.rs" and not r.listing for r in package.reads))
        self.assertTrue(any(r.target == "docs" and r.listing for r in package.reads))
        self.assertFalse(any(r.target == "docs/DECISION_QUEUE.md" for r in package.reads))
        self.assertIn("src/tools/targo", package.deps)
        self.assertIn("src/tools/targo", package.foreign)
        self.assertFalse(package.history)

    def fixture_scope(self, expired=False):
        graph, audits, files = self.graph()
        if expired:
            audits[self.SOURCE]["lapsed"] = "2026-11-13 control: independent review is absent"
        package = graph.packages["src/bootstrap"]
        graph.blob_cache.update(files)
        ls._scan_one(graph, package, self.SOURCE, files, audits, set())
        # The real conservative path harvests every compiled package literal
        # after a walk. Use the actual source and every exact premise, so a
        # scratch GitCtx path cannot silently become a repository content read.
        ls._harvest_package_literals(graph, package,
                                    ["docs", "scripts", "src", "tests", "reports", "compiler",
                                     "library", "first-party"], audits)
        path = "docs/DECISION_QUEUE.md"
        selected = ls.Selection("base", graph.index.rev, [path], [], in_place={path})
        return graph, selected

    def test_actual_fixture_prose_keeps_broad_bootstrap_check_diagnostic(self):
        graph, selected = self.fixture_scope()
        scoped = development.scope(graph, selected)
        self.assertFalse(scoped.errors or scoped.packages)
        broad = fixtures.leg(id="bootstrap-tests", reasons=["repository listing diagnostics"])
        gate.development_legs(graph, selected, [broad], 1)
        self.assertTrue(broad.selected and broad.diagnostic_only)

    def test_actual_fixture_audit_expiry_restores_conservative_bootstrap_scope(self):
        graph, selected = self.fixture_scope(expired=True)
        package = graph.packages["src/bootstrap"]
        reads = [read for read in package.reads if read.target == "docs/DECISION_QUEUE.md"]
        self.assertTrue(reads)
        self.assertTrue(all(not read.listing for read in reads))
        scoped = development.scope(graph, selected)
        self.assertFalse(scoped.errors)
        self.assertEqual(scoped.packages, ["src/bootstrap"])

    def test_actual_fixture_keeps_direct_content_and_source_owners(self):
        for cls in ("compile", "runtime"):
            with self.subTest(cls=cls):
                graph, selected = self.fixture_scope()
                graph.packages["src/bootstrap"].reads.append(
                    ls.Read(cls, "docs/DECISION_QUEUE.md", True, "direct-reader control"))
                scoped = development.scope(graph, selected)
                self.assertFalse(scoped.errors)
                self.assertEqual(scoped.packages, ["src/bootstrap"])
        graph, _ = self.fixture_scope()
        selected = ls.Selection("base", graph.index.rev, [self.SOURCE], [])
        scoped = development.scope(graph, selected)
        self.assertFalse(scoped.errors)
        self.assertEqual(scoped.packages, ["src/bootstrap"])

    def test_every_exact_source_or_premise_change_restores_conservative_scanning(self):
        graph, audits, files = self.graph()
        row = audits[self.SOURCE]
        self.assertIn("src/bootstrap/src/core/build_steps/test/compiler_fixture.rs",
                      [pin["file"] for pin in row["premises"]])
        self.assertIn("src/bootstrap/src/core/config/config.rs", [pin["file"] for pin in row["premises"]])
        for path in [self.SOURCE, *(pin["file"] for pin in row["premises"])]:
            with self.subTest(path=path):
                changed = copy.deepcopy(graph)
                changed.index.entries[path] = ("100644", "0" * 40)
                self.assertFalse(ls.audit_holds(changed, self.SOURCE, row))
                package = changed.packages["src/bootstrap"]
                # This index deliberately names an absent changed object. Check
                # dispatch to the ordinary scanner; real immutable-tree expiry
                # and restored reads are exercised by EscapeAuditTests.
                with mock.patch.object(ls, "_scan_file", return_value=False) as ordinary:
                    ls._scan_one(changed, package, self.SOURCE, files, audits, set())
                ordinary.assert_called_once()


class TargoTestSupportAuditTests(unittest.TestCase):
    SOURCE = "src/tools/targo/crates/cargo-test-support/src/lib.rs"
    OWNER = "src/tools/targo/crates/cargo-test-support"
    PROCESS = "src/tools/targo/crates/cargo-util/src/process_builder/mod.rs"

    def graph(self):
        root = Path(__file__).resolve().parents[2]
        raw = (root / ls.AUDITS_FILE).read_bytes()
        row = next(row for row in ls.tomllib.loads(raw.decode())["audit"] if row["file"] == self.SOURCE)
        skip_if_lapsed(self, row)
        files = {path: (root / path).read_bytes()
                 for path in [self.SOURCE, *(pin["file"] for pin in row["premises"])]}
        entries = {path: ("100644", hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest())
                   for path, data in files.items()}
        graph = ls.Graph(ls.TreeIndex(str(root), "fixture", "fixture", entries),
                         {self.OWNER: ls.Package(self.OWNER, "cargo-test-support")}, {}, [], {}, {})
        graph.blob_cache.update(files)
        with mock.patch.object(ls, "AUDITS_OVERRIDE", raw):
            audits = ls.load_audits(graph)
        self.assertIn(self.SOURCE, audits)
        return graph, audits, files

    def test_current_reader_and_all_premises_hold_the_exact_review(self):
        graph, audits, files = self.graph()
        self.assertIn(self.PROCESS, [pin["file"] for pin in audits[self.SOURCE]["premises"]])
        self.assertTrue(ls.audit_holds(graph, self.SOURCE, audits[self.SOURCE]))
        package = graph.packages[self.OWNER]
        ls._scan_one(graph, package, self.SOURCE, files, audits, set())
        self.assertEqual([(read.cls, read.target, read.test_only, read.listing) for read in package.reads],
                         [("runtime", "src/tools/targo/tests", False, False)])
        self.assertFalse(package.history or package.unresolved)

    def test_every_actual_source_or_premise_edit_restores_conservative_git_scan(self):
        graph, audits, files = self.graph()
        self.assertTrue(ls.audit_holds(graph, self.SOURCE, audits[self.SOURCE]))
        for path in files:
            with self.subTest(path=path):
                changed = copy.deepcopy(graph)
                changed_files = dict(files)
                changed_files[path] += b"\n// exact audit expiry control\n"
                data = changed_files[path]
                changed.index.entries[path] = ("100644", hashlib.sha1(
                    b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest())
                changed.blob_cache.update(changed_files)
                self.assertFalse(ls.audit_holds(changed, self.SOURCE, audits[self.SOURCE]))
                package = changed.packages[self.OWNER]
                ls._scan_one(changed, package, self.SOURCE, changed_files, audits, set())
                self.assertTrue(package.history)
                self.assertTrue(any("runs git" in read.target for read in package.unresolved))

    def test_real_template_tree_remains_a_runtime_content_input(self):
        graph, audits, files = self.graph()
        self.assertTrue(ls.audit_holds(graph, self.SOURCE, audits[self.SOURCE]))
        package = graph.packages[self.OWNER]
        ls._scan_one(graph, package, self.SOURCE, files, audits, set())
        inputs, unresolved, history = ls.leg_inputs(graph, {self.OWNER}, ("compile", "runtime"), True)
        self.assertFalse(unresolved or history)
        self.assertTrue(ls.reaches("src/tools/targo/tests/testsuite/add/in/Cargo.toml", inputs))
        self.assertFalse(ls.reaches("docs/unrelated.md", inputs))


class ControllerFeatureOwnershipTests(unittest.TestCase):
    OLD = ('[workspace]\n[package]\nname="trust-resource-controller"\nversion="0.1.0"\n'
           '[dependencies]\nlibc={version="0.2",optional=true}\n'
           '[features]\ndefault=["channel"]\nchannel=[]\n'
           'client=["channel","dep:libc"]\nprobe-scheduler=["client"]\n')
    NEW = ('[workspace]\n[package]\nname="trust-resource-controller"\nversion="0.1.0"\n'
           '[dependencies]\nlibc={version="0.2",optional=true}\n'
           '[features]\ndefault=["channel"]\nchannel=[]\n'
           'bootstrap-receiver=["channel","dep:libc"]\n'
           'client=["bootstrap-receiver"]\nprobe-scheduler=["client"]\n')

    def fixture(self, root, new=None, old_source="pub fn original() {}\n", build_script=False, old=None):
        owner = development.CONTROLLER_COMPONENT
        files = {"Cargo.toml": '[workspace]\nmembers=["src/tools/compiletest"]\n',
                 owner + "/Cargo.toml": self.OLD if old is None else old, owner + "/src/lib.rs": old_source,
                 "src/tools/compiletest/Cargo.toml": '[package]\nname="compiletest"\nversion="0.1.0"\n'
                 '[dependencies]\ncontroller={package="trust-resource-controller",path="../../../crates/trust-resource-controller"}\n',
                 "src/tools/compiletest/src/lib.rs": "pub fn original() {}\n"}
        files.update({recipe + "/rmake.rs": "fn main() {}\n" for recipe in development.INTEGRATION_RECIPES})
        if isinstance(build_script, str):
            files[owner + "/build.rs"] = build_script
        base = fixtures.make_repo(root, files, {})
        (root / owner / "Cargo.toml").write_text(self.NEW if new is None else new)
        if build_script is True:
            (root / owner / "build.rs").write_text("fn main() {}\n")
        fixtures.git_in(root, "add", ".")
        fixtures.git_in(root, "commit", "-qm", "feature activation change")
        return base, ls.TreeIndex.load(str(root), "HEAD")

    def test_additive_receiver_keeps_all_native_cohorts_and_actual_stage1_recipes(self):
        with tempfile.TemporaryDirectory(prefix="controller-feature-owner-") as tmp:
            root = Path(tmp)
            base, index = self.fixture(root)
            self.assertTrue(development.controller_feature_extension(index, base))
            with mock.patch.object(gate, "REPO_ROOT", root), \
                    mock.patch.object(gate, "compute", side_effect=AssertionError("full discovery forbidden")):
                graph, selected, _ = gate.compute_discovery(base, "HEAD", False, None,
                                                           gate.DiscoveryProfile.DEVELOPMENT)
                self.assertIsInstance(selected, gate.DeclaredDevelopmentSelection)
                landing = gate.LandingRange(base, selected.head, "local", True, tuple(selected.changed), "")
                legs = gate.declared_development_legs(graph, selected, 2, fixtures.HOOK_OFF, landing)
            cohorts = [leg for leg in legs if leg.id.startswith("development-package-trust-resource-controller-")]
            self.assertTrue(all(leg.force_run and "--lib" in leg.command for leg in cohorts))
            # The optional-helper closure supplements, never replaces, the
            # independently compiled DTO/receiver/minimal-client boundaries.
            minimal = [leg for leg in cohorts if "--all-features" not in leg.command]
            activated = {tuple(leg.command[leg.command.index("--features") + 1:])
                         if "--features" in leg.command else () for leg in minimal}
            self.assertEqual(activated, {(), ("bootstrap-receiver",), ("client",)})
            self.assertTrue(any("--all-features" in leg.command for leg in cohorts))
            recipe = next(leg for leg in legs if leg.id == "development-recipes")
            self.assertTrue(recipe.needs_stage1 and recipe.force_run)
            self.assertEqual(set(recipe.run_targets), set(development.INTEGRATION_RECIPES))
            self.assertIn("--all-rows", next(leg.command for leg in legs if leg.id == "push-rows"))
            self.assertTrue(next(leg for leg in legs if leg.id == "compiler-check").diagnostic_only)

    def test_package_dependency_activation_default_and_unowned_features_refuse(self):
        cases = {
            "dependency": self.NEW.replace('version="0.2"', 'version="0.3"'),
            "type change": self.NEW.replace('optional=true', 'optional=1'),
            "package": self.NEW.replace('version="0.1.0"', 'version="0.2.0"'),
            "default": self.NEW.replace('default=["channel"]', 'default=["client"]'),
            "lost activation": self.NEW.replace('bootstrap-receiver=["channel","dep:libc"]',
                                                 'bootstrap-receiver=["channel"]'),
            "unknown cohort": self.NEW + 'unowned=[]\n',
            "cyclic": self.NEW.replace('channel=[]', 'channel=["client"]'),
        }
        for label, manifest in cases.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory(prefix="controller-feature-refuse-") as tmp:
                base, index = self.fixture(Path(tmp), manifest)
                self.assertFalse(development.controller_feature_extension(index, base))
                self.assertFalse(development.has_declared_source_ownership(index,
                                 [development.CONTROLLER_COMPONENT + "/Cargo.toml"], base))

    def test_implicit_optional_dependency_feature_cannot_silently_disappear(self):
        old = self.OLD.replace('[features]', 'unused={version="1",optional=true}\n[features]')
        new = old + 'bootstrap-receiver=["dep:unused"]\n'
        with tempfile.TemporaryDirectory(prefix="controller-feature-implicit-") as tmp:
            base, index = self.fixture(Path(tmp), new, old=old)
            self.assertFalse(development.controller_feature_extension(index, base))

    def test_reviewed_identity_script_is_owned_only_while_its_exact_body_is_unchanged(self):
        script = (Path(__file__).resolve().parents[2] / development.CONTROLLER_COMPONENT / "build.rs").read_text()
        with tempfile.TemporaryDirectory(prefix="controller-reviewed-build-") as tmp:
            root = Path(tmp)
            base, index = self.fixture(root, build_script=script)
            self.assertTrue(development.controller_feature_extension(index, base))
            path = root / development.CONTROLLER_COMPONENT / "build.rs"
            path.write_text(script + '\nfn extra_reader() { let _ = std::env::vars_os(); }\n')
            fixtures.git_in(root, "add", ".")
            fixtures.git_in(root, "commit", "-qm", "additional build inputs")
            self.assertFalse(development.controller_feature_extension(ls.TreeIndex.load(str(root), "HEAD"), base))

    def test_existing_dormant_cfg_or_build_script_cannot_gain_fast_ownership(self):
        for source, build in (('#[cfg(feature="bootstrap-receiver")] pub fn dormant() {}\n', False),
                              ('const NAME: &str = "CARGO_FEATURE_BOOTSTRAP_RECEIVER";\n', False),
                              ("pub fn original() {}\n", True)):
            with self.subTest(source=source, build=build), tempfile.TemporaryDirectory(prefix="controller-feature-cfg-") as tmp:
                base, index = self.fixture(Path(tmp), old_source=source, build_script=build)
                self.assertFalse(development.controller_feature_extension(index, base))


class OracleCitationOwnershipTests(unittest.TestCase):
    OWNER = "crates/example/src/lib.rs"
    SOURCE = "crates/example/src/checks.rs"
    FUNCTION = "actual_refusal"
    ORIGINAL = (OWNER + "|" + "a" * 40 + "|2026-11-11|reviewed decision|"
                "Unchanged claim. ENFORCED-BY: checks::tests::actual_refusal\n")
    REPAIRED = ORIGINAL.replace("checks::tests::actual_refusal", SOURCE + "::actual_refusal")

    def revision(self, root, changed=None, source=None, owner=None, symlink=False, baseline_source=None):
        files = dict(fixtures.FILES)
        files.update({development.ORACLE_WAIVERS: self.ORIGINAL,
                      self.OWNER: "pub fn unchanged() {}\n",
                      self.SOURCE: baseline_source or "#[cfg(test)] mod tests { #[test] fn actual_refusal() { assert!(true); } }\n",
                      "scripts/check_frozen_files.sh": "#!/bin/sh\nexit 0\n"})
        base = fixtures.make_repo(root, files, {})
        (root / development.ORACLE_WAIVERS).write_text(self.REPAIRED if changed is None else changed)
        if source is not None:
            (root / self.SOURCE).write_text(source)
        if owner is not None:
            (root / self.OWNER).write_text(owner)
        if symlink:
            (root / self.SOURCE).unlink()
            (root / self.SOURCE).symlink_to("lib.rs")
        fixtures.git_in(root, "add", "-A")
        fixtures.git_in(root, "commit", "-qm", "citation ownership fixture", "--allow-empty")
        return base, ls.TreeIndex.load(str(root), "HEAD")

    def test_only_locator_changes_have_an_owner_and_full_diagnostics_remain_global(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, index = self.revision(Path(tmp))
            self.assertTrue(development.oracle_citation_repair(index, base))
            graph = ls.build_manifest_graph(index)
            selected = ls.select(graph, base, [development.ORACLE_WAIVERS])
            self.assertTrue(selected.everything)
            scope = development.scope(graph, selected)
            self.assertFalse(scope.errors, scope.errors)
            self.assertTrue(scope.oracle_citations)
            self.assertIn("scripts.tests.land_development_test.OracleCitationOwnershipTests", scope.tests)
            self.assertTrue(development.may_have_scope([development.ORACLE_WAIVERS]))
            self.assertFalse(development.oracle_citation_repair(index, "missing-object"))

    def test_claim_pin_function_row_and_unrelated_source_changes_refuse(self):
        changes = [self.REPAIRED.replace("Unchanged claim", "A stronger claim"),
                   self.REPAIRED.replace("a" * 40, "b" * 40),
                   self.REPAIRED.replace("2026-11-11", "2026-11-12"),
                   self.REPAIRED.replace("reviewed decision", "different decision"),
                   self.REPAIRED.replace("actual_refusal", "unrelated_test"),
                   self.REPAIRED + self.REPAIRED,
                   self.REPAIRED.replace("crates/example/", "crates/unrelated/"),
                   self.REPAIRED.replace("src/checks.rs", "src/../src/checks.rs"),
                   self.REPAIRED.replace("\n", " \n"),
                   self.ORIGINAL]
        for changed in changes:
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as tmp:
                base, index = self.revision(Path(tmp), changed=changed)
                self.assertFalse(development.oracle_citation_repair(index, base))
                graph = ls.build_manifest_graph(index)
                selected = ls.select(graph, base, [development.ORACLE_WAIVERS])
                self.assertTrue(development.scope(graph, selected).errors)
        for delta in ({"source": "#[test] fn actual_refusal() {}\n"},
                      {"owner": "pub fn changed() {}\n"}, {"symlink": True},
                      {"baseline_source": "mod tests { #[test] fn actual_refusal() {} }\n"
                                          "mod unrelated { #[test] fn actual_refusal() {} }\n"}):
            with self.subTest(delta=delta), tempfile.TemporaryDirectory() as tmp:
                base, index = self.revision(Path(tmp), **delta)
                self.assertFalse(development.oracle_citation_repair(index, base))

    def test_owner_requires_fresh_oracle_selftest_and_all_push_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, index = self.revision(Path(tmp))
            graph = ls.build_manifest_graph(index)
            selected = ls.select(graph, base, [development.ORACLE_WAIVERS])
            push = fixtures.leg(id="push-rows", command=["reader", "push-rows"])
            legs = gate.development_legs(graph, selected, [push], 1)
            self.assertTrue(push.selected)
            self.assertTrue(push.force_run)
            self.assertIn("--all-rows", push.command)
            actual = next(leg for leg in legs if leg.id == "development-oracle-freeze-selftest")
            self.assertTrue(actual.selected)
            self.assertTrue(actual.force_run)
            self.assertEqual(actual.command, ["bash", "scripts/check_frozen_files.sh", "--selftest"])
            self.assertIn(ls.EVERYTHING, actual.inputs)


class LocalGitBridgeOwnershipTests(unittest.TestCase):
    def revision(self, root, path, old, new):
        files = {path: old.decode("utf-8"),
                 development.LOCAL_GIT_CORE + "/Cargo.toml": '[package]\nname="targo-core"\nversion="0.1.0"\n',
                 development.LOCAL_GIT_WORKSPACE + "/Cargo.toml": '[package]\nname="targo"\nversion="0.1.0"\n',
                 development.LOCAL_GIT_FIXTURE: "fn native_fixture() {}\n"}
        base = fixtures.make_repo(root, files, {})
        (root / path).write_bytes(new)
        fixtures.git_in(root, "add", ".")
        fixtures.git_in(root, "commit", "-qm", "native DATA bridge")
        return base, ls.TreeIndex.load(str(root), "HEAD")

    def test_only_export_or_unchanged_registry_body_can_share_native_data_owner(self):
        declaration = development.LOCAL_GIT_REGISTRY_DECL
        examples = [
            (development.LOCAL_GIT_EXPORT, b"mod local_import;\n", b"mod local_import;\n" + development.LOCAL_GIT_SNAPSHOT_EXPORT),
            (development.LOCAL_GIT_REGISTRY, declaration + b"\n    id.display_index()\n}\n",
             b"pub(crate) " + declaration + b"\n    id.display_index()\n}\n"),
        ]
        for path, old, new in examples:
            for extra in (b"", b"\nfn unrelated_runtime() {}\n"):
                with self.subTest(path=path, extra=extra), tempfile.TemporaryDirectory(prefix="native-data-bridge-") as tmp:
                    base, index = self.revision(Path(tmp), path, old, new + extra)
                    expected = None if extra else development.LOCAL_GIT_CORE
                    self.assertEqual(development.local_git_bridge_owner(index, base, path), expected)
                    self.assertEqual(development.local_git_owner(path, index, base), expected)
                    self.assertIsNone(development.local_git_bridge_owner(index, None, path))
                    # The real compiler-consuming CLI owner retains ordinary
                    # reachability; registration never waives its prerequisites.
                    self.assertFalse(development.has_declared_source_ownership(index, [path], base))

    def test_fetch_registration_requires_both_options_and_only_the_native_delegate(self):
        arguments, dispatch = development.LOCAL_GIT_FETCH_ADDITIONS
        old = (b'fn cli() -> Command {\n    subcommand("fetch")\n}\n'
               b'fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {\n'
               b'    let ws = args.workspace(gctx)?;\n\n    Ok(())\n}\n')
        new = old.replace(b'    subcommand("fetch")\n', b'    subcommand("fetch")\n' + arguments)
        new = new.replace(b'    Ok(())', dispatch + b'    Ok(())')
        for altered in (new, new.replace(arguments, b""), new.replace(dispatch, b""),
                        new + b"\nfn unrelated_fetch() {}\n", new.replace(arguments, arguments * 2)):
            with self.subTest(exact=altered == new), tempfile.TemporaryDirectory(prefix="native-data-fetch-") as tmp:
                base, index = self.revision(Path(tmp), development.LOCAL_GIT_FETCH, old, altered)
                self.assertEqual(development.local_git_bridge_owner(index, base, development.LOCAL_GIT_FETCH),
                                 development.LOCAL_GIT_WORKSPACE if altered == new else None)

    def test_registered_bridge_selects_both_whole_fresh_native_cohorts(self):
        path = development.LOCAL_GIT_EXPORT
        with tempfile.TemporaryDirectory(prefix="native-data-bridge-") as tmp:
            old = b"mod local_import;\n"
            base, index = self.revision(Path(tmp), path, old, old + development.LOCAL_GIT_SNAPSHOT_EXPORT)
            graph = fixtures.Fixture.graph()
            graph.index = index
            for owner, name in ((development.LOCAL_GIT_CORE, "targo-core"),
                                (development.LOCAL_GIT_WORKSPACE, "targo")):
                graph.packages[owner] = ls.Package(owner, name)
            graph.packages[development.LOCAL_GIT_WORKSPACE].deps.add(development.LOCAL_GIT_CORE)
            selection = ls.Selection(base, index.rev, [path], [])
            scope = development.scope(graph, selection)
            self.assertFalse(scope.errors)
            self.assertTrue(scope.local_git_import)
            legs = gate.development_legs(graph, selection, [], 2)
            self.assertEqual({leg.id for leg in legs},
                             {development.LOCAL_GIT_CORE_LEG, development.LOCAL_GIT_FIXTURE_LEG})
            self.assertTrue(all(leg.force_run for leg in legs))
            self.assertTrue(all("vendored-openssl,vendored-libgit2" in leg.command for leg in legs))
            native = next(leg for leg in legs if leg.id == development.LOCAL_GIT_FIXTURE_LEG)
            self.assertIn(development.LOCAL_GIT_CORE, native.inputs)

    def test_unregistered_fetch_or_registry_logic_and_nonregular_sources_refuse(self):
        for path in (development.LOCAL_GIT_FETCH, development.LOCAL_GIT_REGISTRY):
            with self.subTest(path=path), tempfile.TemporaryDirectory(prefix="native-data-bridge-") as tmp:
                base, index = self.revision(Path(tmp), path, b"fn original() {}\n", b"fn modified() {}\n")
                self.assertIsNone(development.local_git_bridge_owner(index, base, path))
                index.entries[path] = ("120000", index.entries[path][1])
                self.assertIsNone(development.local_git_bridge_owner(index, base, path))


class CensusDevelopmentOwnershipTests(unittest.TestCase):
    PYTHON_INPUTS = ("scripts/compiletest_census.py", "scripts/tests/compiletest_census_test.py")
    RUST_INPUTS = tuple("src/tools/compiletest/src/" + name for name in
                        ("census.rs", "census/tests.rs", "executor.rs", "lib.rs"))

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="census-development-owner-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        files = {
            "Cargo.toml": ('[workspace]\nmembers=["src/tools/compiletest"]\n'
                           'default-members=["src/tools/compiletest"]\n'),
            "src/tools/compiletest/Cargo.toml":
                '[package]\nname="compiletest"\nversion="0.1.0"\n',
        }
        files.update({path: "# census Python fixture\n" for path in self.PYTHON_INPUTS})
        files.update({path: "// census Rust fixture\n" for path in self.RUST_INPUTS})
        for recipe in (*development.INTEGRATION_RECIPES, development.EXIT_RECIPE):
            files[recipe + "/rmake.rs"] = "fn main() {}\n"
        fixtures.make_repo(self.root, files, {})
        patch = mock.patch.object(gate, "REPO_ROOT", self.root)
        patch.start()
        self.addCleanup(patch.stop)

    def changed(self, paths):
        base = fixtures.git_in(self.root, "rev-parse", "HEAD")
        for path in paths:
            file = self.root / path
            file.parent.mkdir(parents=True, exist_ok=True)
            with file.open("a") as output:
                output.write("# changed census input\n" if path.endswith(".py")
                             else "// changed census input\n")
        fixtures.git_in(self.root, "add", ".")
        fixtures.git_in(self.root, "commit", "-qm", "census ownership fixture")
        return base

    def test_reader_and_fixture_select_their_real_tests_without_a_full_scan(self):
        for path in self.PYTHON_INPUTS:
            with self.subTest(path=path):
                base = self.changed([path])
                with mock.patch.object(ls, "build_graph", side_effect=AssertionError("full scan forbidden")):
                    graph, selection, _ = gate.compute_discovery(
                        base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
                self.assertIsInstance(selection, gate.DeclaredDevelopmentSelection)
                scope = development.scope(graph, selection)
                self.assertEqual(scope.errors, [])
                self.assertEqual(scope.tests, ["scripts.tests.compiletest_census_test"])
                self.assertEqual(scope.tests, ls.validation_test_modules([path]))
                self.assertEqual(scope.packages, [])
                self.assertEqual(scope.recipes, [])

    def test_mixed_actual_census_paths_keep_bootstrap_and_recipe_checks(self):
        # The source repair changed these four Rust inputs and its Python
        # regression. Keep the existing complete execution-component owner;
        # a Python registration must not replace the actual native checks.
        base = self.changed([*self.RUST_INPUTS, self.PYTHON_INPUTS[1]])
        graph, selection, _ = gate.compute_discovery(
            base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
        self.assertNotIsInstance(selection, gate.DeclaredDevelopmentSelection)
        scope = development.scope(graph, selection)
        self.assertEqual(scope.errors, [])
        self.assertEqual(scope.tests, ["scripts.tests.compiletest_census_test"])
        self.assertEqual(scope.packages, ["src/tools/compiletest"])
        expected_recipes = sorted((*development.INTEGRATION_RECIPES, development.EXIT_RECIPE))
        self.assertEqual(scope.recipes, expected_recipes)
        legs = gate.development_legs(graph, selection, [fixtures.leg(id="push-rows")], 2)
        validation = next(leg for leg in legs if leg.id == "development-validation-tests")
        self.assertIn("scripts.tests.compiletest_census_test", validation.command)
        compiletest = next(leg for leg in legs if leg.id == "development-package-compiletest")
        self.assertEqual(compiletest.command, gate._xpy_test_cmd(["src/tools/compiletest"], 2))
        self.assertTrue(compiletest.needs_stage1 and compiletest.force_run)
        recipes = next(leg for leg in legs if leg.id == "development-recipes")
        self.assertEqual(recipes.run_targets, expected_recipes)
        self.assertTrue(recipes.needs_stage1 and recipes.force_run)
        push = next(leg for leg in legs if leg.id == "push-rows")
        self.assertTrue(push.force_run)
        self.assertIn("--all-rows", push.command)

    def test_neighbouring_census_programs_and_fixtures_still_refuse(self):
        for path in ("scripts/compiletest_census_neighbour.py",
                     "scripts/tests/compiletest_census_neighbour_test.py"):
            with self.subTest(path=path):
                base = self.changed([path])
                with mock.patch.object(ls, "build_graph", side_effect=AssertionError("full scan forbidden")), \
                        mock.patch.object(ls, "build_manifest_graph", side_effect=AssertionError("manifest scan forbidden")):
                    with self.assertRaisesRegex(gate.LandingUnjudged, "unsupported changed owner/input"):
                        gate.compute_discovery(base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)


class DevelopmentDiscoveryPreflightTests(unittest.TestCase):
    UNOWNED = (
        "src/bootstrap/bootstrap.py",
        "src/bootstrap/bootstrap_test.py",
        "src/bootstrap/Cargo.toml",
        "src/bootstrap/build.rs",
        "src/bootstrap/src/main.rs",
        "src/bootstrap/src/bin/main.rs",
        "compiler/rustc_mir_transform/src/trust_verify/tests/native_wp_source.rs",
        "crates/trust-router/Cargo.toml",
        "crates/trust-router/src/full_verification/native_trust_ir/index.rs",
        "crates/trust-types/src/result/native_body_wp.rs",
        "crates/trust-types/tests/fixtures/native_body_wp_current_v2_transport.json",
        "crates/trust-disasm/harness/native-invariant/Cargo.lock",
        "unknown/program.py",
        "Cargo.toml",
    )

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="development-preflight-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.base = fixtures.make_repo(self.root, {
            "Cargo.toml": '[workspace]\nmembers=["crates/base"]\ndefault-members=["crates/base"]\n',
            "crates/base/Cargo.toml": '[package]\nname="base"\nversion="0.1.0"\n',
            "crates/base/src/lib.rs": "pub fn baseline() {}\n",
            "scripts/land_gate.py": "# registered execution program\n",
        }, {})
        root_patch = mock.patch.object(gate, "REPO_ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)

    def commit(self, path, text="changed input\n"):
        base = fixtures.git_in(self.root, "rev-parse", "HEAD")
        source = self.root / path
        source.parent.mkdir(parents=True, exist_ok=True)
        with source.open("a") as output:
            output.write(text)
        fixtures.git_in(self.root, "add", ".")
        fixtures.git_in(self.root, "commit", "-qm", "changed input")
        return base

    def test_actual_unsupported_source_paths_refuse_before_any_graph_or_harvest(self):
        with mock.patch.object(ls, "build_graph", side_effect=AssertionError("full scan forbidden")) as full, \
                mock.patch.object(ls, "build_manifest_graph", side_effect=AssertionError("manifest graph forbidden")) as manifest, \
                mock.patch.object(ls, "_harvest_package_literals", side_effect=AssertionError("harvest forbidden")) as harvest:
            for path in self.UNOWNED:
                with self.subTest(path=path):
                    base = self.commit(path)
                    with self.assertRaisesRegex(gate.LandingUnjudged, "unsupported changed owner/input") as error:
                        gate.compute_discovery(base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
                    self.assertIn(path, str(error.exception))
            gitlink = "first-party/trust-ir"
            base = fixtures.git_in(self.root, "rev-parse", "HEAD")
            fixtures.git_in(self.root, "update-index", "--add", "--cacheinfo", "160000", base, gitlink)
            fixtures.git_in(self.root, "commit", "-qm", "IR pin input")
            with self.assertRaisesRegex(gate.LandingUnjudged, gitlink):
                gate.compute_discovery(base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
        full.assert_not_called()
        manifest.assert_not_called()
        harvest.assert_not_called()

    def test_bootstrap_library_and_registered_inputs_keep_their_existing_discovery(self):
        # Passing the negative filter grants no owner or skipped check. Keep
        # library sources, snapshots, registered validators and prose eligible
        # for their existing discovery while refusing Python/executable inputs.
        for path in ("src/bootstrap/src/core/build_steps/tool.rs",
                     "src/bootstrap/src/core/builder/snapshots/x_check.snap",
                     "tools/preflight.py",
                     "README.md"):
            with self.subTest(path=path):
                base = self.commit(path)
                _, _, changed = gate.development_discovery_inputs(base, "HEAD")
                self.assertEqual(changed, [path])

    def test_each_existing_build_slot_regression_module_selects_complete_owner_suite(self):
        expected={"scripts.tests.build_slot_test","scripts.tests.build_slot_quiet_test",
                  "scripts.tests.build_slot_recovery_test","scripts.tests.build_slot_cpu_bridge_test",
                  "scripts.tests.check_bootstrap_script_tests_test"}
        for path in ("scripts/tests/build_slot_cpu_bridge_test.py",
                     "scripts/tests/build_slot_quiet_test.py",
                     "scripts/tests/build_slot_recovery_test.py"):
            with self.subTest(path=path):
                base=self.commit(path,"# private admission regression fixture\n")
                graph,selection,_=gate.compute_discovery(
                    base,"HEAD",False,None,gate.DiscoveryProfile.DEVELOPMENT)
                self.assertIsInstance(selection,gate.DeclaredDevelopmentSelection)
                scope=development.scope(graph,selection)
                self.assertEqual(scope.errors,[])
                self.assertEqual(set(scope.tests),expected)
                self.assertEqual(set(ls.validation_test_modules([path])),expected)

    def test_build_slot_owner_does_not_admit_unknown_test_or_program_neighbours(self):
        for path in ("scripts/tests/build_slot_unknown_test.py",
                     "scripts/tests/other_private_pool_test.py","scripts/build-slot-neighbour"):
            with self.subTest(path=path):
                base=self.commit(path,"# unknown neighbour\n")
                with mock.patch.object(ls,"build_graph",side_effect=AssertionError("full scan forbidden")), \
                     mock.patch.object(ls,"build_manifest_graph",side_effect=AssertionError("manifest scan forbidden")):
                    with self.assertRaisesRegex(gate.LandingUnjudged,"unsupported changed owner/input"):
                        gate.compute_discovery(base,"HEAD",False,None,gate.DiscoveryProfile.DEVELOPMENT)

    def test_preflight_program_and_fixture_select_existing_complete_program_tests(self):
        for path in ("tools/preflight.py", "scripts/tests/preflight_test.py"):
            with self.subTest(path=path):
                base = self.commit(path, "# Bootstrap preflight execution source\n")
                graph, selection, _ = gate.compute_discovery(
                    base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
                self.assertIsInstance(selection, gate.DeclaredDevelopmentSelection)
                scope = development.scope(graph, selection)
                self.assertEqual(scope.errors, [])
                self.assertEqual(scope.tests, ls.validation_test_modules([path]))
                self.assertEqual(scope.packages, [])
                self.assertEqual(scope.recipes, [])

    def test_preflight_program_registration_does_not_admit_neighbouring_paths(self):
        for path in ("tools/preflight-neighbour.py", "scripts/tests/preflight_neighbour_test.py"):
            with self.subTest(path=path):
                base = self.commit(path, "# unregistered Bootstrap preflight neighbour\n")
                with mock.patch.object(ls, "build_graph", side_effect=AssertionError("full scan forbidden")), \
                     mock.patch.object(ls, "build_manifest_graph", side_effect=AssertionError("manifest scan forbidden")):
                    with self.assertRaisesRegex(gate.LandingUnjudged, "unsupported changed owner/input"):
                        gate.compute_discovery(base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)

    def test_current_and_historical_plan_report_not_judged_before_budget_or_legs(self):
        base = self.commit(self.UNOWNED[0])
        head = fixtures.git_in(self.root, "rev-parse", "HEAD")
        landing = gate.LandingRange(base, head, "fixture", True, (self.UNOWNED[0],), "")
        with mock.patch.object(gate, "read_landing", return_value=landing), \
                mock.patch.object(gate, "compute", side_effect=AssertionError("full discovery forbidden")) as full, \
                mock.patch.object(ls, "build_manifest_graph", side_effect=AssertionError("manifest graph forbidden")), \
                mock.patch.object(gate.host_budget, "measure", side_effect=AssertionError("budget forbidden")), \
                mock.patch.object(gate, "build_legs", side_effect=AssertionError("legs forbidden")):
            for requested_head in ("HEAD", head):
                with self.subTest(head=requested_head), contextlib.redirect_stdout(io.StringIO()) as output:
                    code = gate.cmd_plan(argparse.Namespace(base=base, head=requested_head,
                                                           development=True, verify_graph=False))
                self.assertEqual(code, 2)
                self.assertIn("NOT JUDGED", output.getvalue())
                self.assertIn("No graph or leg is judged", output.getvalue())
        full.assert_not_called()

    def test_run_refuses_unsupported_source_before_discovery_or_execution(self):
        base = self.commit(self.UNOWNED[0])
        with mock.patch.object(gate, "checkout_problem", return_value=None), \
                mock.patch.object(gate.host_budget, "measure", return_value=fixtures.host(28, 128, 100)), \
                mock.patch.object(gate, "compute", side_effect=AssertionError("full discovery forbidden")) as full, \
                mock.patch.object(gate, "build_legs", side_effect=AssertionError("legs forbidden")), \
                mock.patch.object(gate, "run_leg", side_effect=AssertionError("execution forbidden")) as execute, \
                contextlib.redirect_stdout(io.StringIO()) as output:
            code = gate.cmd_run(argparse.Namespace(base=base, development=True, only=None))
        self.assertEqual(code, 2)
        self.assertIn("NOT JUDGED", output.getvalue())
        self.assertIn("No leg or push ran", output.getvalue())
        full.assert_not_called()
        execute.assert_not_called()

    def test_registered_run_uses_shared_discovery_and_keeps_uncontained_diagnostics(self):
        base = self.commit("scripts/land_gate.py")
        head = fixtures.git_in(self.root, "rev-parse", "HEAD")
        landing = gate.LandingRange("f" * 40, head, "fixture", False, None, "main moved")
        selected = []
        original = gate.compute_discovery

        class ReachedLegSelection(BaseException):
            pass

        def discover(*args, **kwargs):
            result = original(*args, **kwargs)
            selected.append(result)
            return result

        with mock.patch.object(gate, "checkout_problem", return_value=None), \
                mock.patch.object(gate.host_budget, "measure", return_value=fixtures.host(28, 128, 100)), \
                mock.patch.object(gate, "compute_discovery", side_effect=discover) as discovery, \
                mock.patch.object(gate, "compute", side_effect=AssertionError("full scan forbidden")) as full, \
                mock.patch.object(ls, "build_graph", side_effect=AssertionError("full graph forbidden")) as graph, \
                mock.patch.object(ls, "_harvest_package_literals", side_effect=AssertionError("harvest forbidden")) as harvest, \
                mock.patch.object(gate, "discover_landing", side_effect=AssertionError("contained landing forbidden")) as contained, \
                mock.patch.object(gate, "read_landing", return_value=landing) as read, \
                mock.patch.object(gate, "push_hook_state", return_value=fixtures.HOOK_OFF), \
                mock.patch.object(gate, "declared_development_legs", side_effect=ReachedLegSelection) as legs, \
                mock.patch.object(gate, "run_leg", side_effect=AssertionError("execution forbidden")) as execute, \
                contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(ReachedLegSelection):
                gate.cmd_run(argparse.Namespace(base=base, development=True, only=None))
        # Bind the call to the real signature, so how its caller spells it
        # (_compute_in_session now passes five arguments positionally and
        # progress by keyword) does not matter, and every parameter, the
        # keyword-only progress included, is pinned.
        discovery.assert_called_once()
        call = inspect.signature(original).bind(*discovery.call_args.args, **discovery.call_args.kwargs)
        call.apply_defaults()
        self.assertEqual(dict(call.arguments), {
            "base": base, "head": "HEAD", "verify": False, "previous": None,
            "profile": gate.DiscoveryProfile.DEVELOPMENT, "progress": None, "checkout": None})
        self.assertIsInstance(selected[0][1], gate.DeclaredDevelopmentSelection)
        read.assert_called_once_with(head=head)
        self.assertIs(legs.call_args.args[-1], landing)
        self.assertFalse(landing.contained)
        full.assert_not_called()
        graph.assert_not_called()
        harvest.assert_not_called()
        contained.assert_not_called()
        execute.assert_not_called()

    def test_run_retains_full_fallback_when_declared_reachability_is_unknown(self):
        base = self.commit("scripts/land_gate.py")

        class ReachedFullDiscovery(BaseException):
            pass

        with mock.patch.object(gate, "checkout_problem", return_value=None), \
                mock.patch.object(gate.host_budget, "measure", return_value=fixtures.host(28, 128, 100)), \
                mock.patch.object(gate, "declared_development_selection", side_effect=gate.DevelopmentReachabilityRequired), \
                mock.patch.object(gate, "compute", side_effect=ReachedFullDiscovery) as full, \
                mock.patch.object(gate, "run_leg", side_effect=AssertionError("execution forbidden")) as execute, \
                contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(ReachedFullDiscovery):
                gate.cmd_run(argparse.Namespace(base=base, development=True, only=None))
        full.assert_called_once_with(base, "HEAD", False, None)
        execute.assert_not_called()

    def test_run_keeps_declared_semantic_refusal_without_full_fallback_or_execution(self):
        base = self.commit("scripts/land_gate.py")
        with mock.patch.object(gate, "checkout_problem", return_value=None), \
                mock.patch.object(gate.host_budget, "measure", return_value=fixtures.host(28, 128, 100)), \
                mock.patch.object(gate, "declared_development_selection",
                                  side_effect=gate.LandingUnjudged("declared semantic refusal")), \
                mock.patch.object(gate, "compute", side_effect=AssertionError("fallback forbidden")) as full, \
                mock.patch.object(gate, "run_leg", side_effect=AssertionError("execution forbidden")) as execute, \
                contextlib.redirect_stdout(io.StringIO()) as output:
            code = gate.cmd_run(argparse.Namespace(base=base, development=True, only=None))
        self.assertEqual(code, 2)
        self.assertIn("declared semantic refusal", output.getvalue())
        full.assert_not_called()
        execute.assert_not_called()

    def test_dirty_run_refuses_before_development_preflight(self):
        self.commit("scripts/land_gate.py")
        (self.root / "scripts/land_gate.py").write_text("# uncommitted source\n")
        with mock.patch.object(gate, "development_discovery_inputs", side_effect=AssertionError("preflight forbidden")) as preflight, \
                contextlib.redirect_stderr(io.StringIO()) as output:
            code = gate.cmd_run(argparse.Namespace(base=self.base, development=True, only=None))
        self.assertEqual(code, 2)
        self.assertIn("uncommitted changes", output.getvalue())
        preflight.assert_not_called()

    def assert_empty_uncommitted_plan_refuses(self):
        self.assertEqual(fixtures.git_in(self.root, "rev-parse", "HEAD"), self.base)
        self.assertEqual(ls.changed_paths(str(self.root), self.base, "HEAD"), [])
        self.assertTrue(fixtures.git_in(self.root, "status", "--porcelain", "--untracked-files=no"))
        landing = gate.LandingRange(self.base, self.base, "fixture", True, (), "")
        with contextlib.ExitStack() as stack:
            discovery = [stack.enter_context(mock.patch.object(
                ls, name, side_effect=AssertionError(f"{name} discovery forbidden")))
                for name in ("build_graph", "build_manifest_graph", "_package_sources",
                             "scan_escapes", "_harvest_package_literals")]
            stack.enter_context(mock.patch.object(gate, "read_landing", return_value=landing))
            stack.enter_context(mock.patch.object(gate.host_budget, "measure",
                                                  side_effect=AssertionError("budget forbidden")))
            stack.enter_context(mock.patch.object(gate, "build_legs",
                                                  side_effect=AssertionError("legs forbidden")))
            output = stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            code = gate.cmd_plan(argparse.Namespace(base=self.base, head="HEAD",
                                                   development=True, verify_graph=False))
        self.assertEqual(code, 2)
        self.assertIn("NOT JUDGED", output.getvalue())
        self.assertIn("empty committed development subject", output.getvalue())
        self.assertIn("commit first", output.getvalue())
        self.assertIn("No graph or leg is judged", output.getvalue())
        for operation in discovery:
            operation.assert_not_called()

    def test_empty_current_development_plan_refuses_unstaged_subject_before_discovery(self):
        (self.root / "crates/base/src/lib.rs").write_text("pub fn uncommitted() {}\n")
        self.assert_empty_uncommitted_plan_refuses()

    def test_empty_current_development_plan_refuses_staged_merge_before_discovery(self):
        # The real failure was a --no-commit merge: HEAD and --base matched,
        # but the candidate source existed only in the merge's staged tree.
        fixtures.git_in(self.root, "switch", "-qc", "candidate")
        self.commit("crates/base/src/lib.rs", "pub fn candidate() {}\n")
        candidate = fixtures.git_in(self.root, "rev-parse", "HEAD")
        fixtures.git_in(self.root, "switch", "-q", "main")
        fixtures.git_in(self.root, "merge", "--no-ff", "--no-commit", "candidate")
        self.assertEqual(fixtures.git_in(self.root, "rev-parse", "MERGE_HEAD"), candidate)
        self.assertNotEqual(fixtures.git_in(self.root, "write-tree"),
                            fixtures.git_in(self.root, "rev-parse", "HEAD^{tree}"))
        self.assert_empty_uncommitted_plan_refuses()

    def test_empty_current_development_plan_refuses_index_change_with_reverted_worktree(self):
        source = self.root / "crates/base/src/lib.rs"
        original = source.read_text()
        source.write_text("pub fn staged_only() {}\n")
        fixtures.git_in(self.root, "add", "crates/base/src/lib.rs")
        source.write_text(original)
        # A worktree-versus-HEAD diff misses the pending index subject.
        self.assertEqual(fixtures.git_in(self.root, "diff", "HEAD", "--name-only"), "")
        self.assert_empty_uncommitted_plan_refuses()

    def add_submodule(self):
        temporary = tempfile.TemporaryDirectory(prefix="development-preflight-child-")
        self.addCleanup(temporary.cleanup)
        donor = Path(temporary.name)
        fixtures.make_repo(donor, {"src/lib.rs": "pub fn child() {}\n"}, {})
        fixtures.git_in(self.root, "-c", "protocol.file.allow=always", "submodule", "add", "-q",
                        str(donor), "first-party/fixture")
        fixtures.git_in(self.root, "commit", "-qm", "child fixture")
        self.base = fixtures.git_in(self.root, "rev-parse", "HEAD")
        return self.root / "first-party/fixture"

    def test_empty_current_development_subject_ignores_untracked_only_child(self):
        child = self.add_submodule()
        (child / "untracked.rs").write_text("fn untracked() {}\n")
        self.assertTrue(fixtures.git_in(self.root, "status", "--porcelain", "--untracked-files=no",
                                       "--ignore-submodules=none"))
        with mock.patch.object(gate, "compute", wraps=gate.compute) as full:
            graph, selection, base = gate.compute_discovery(
                self.base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
        full.assert_called_once_with(self.base, "HEAD", False, None)
        self.assertEqual((base, graph.index.rev, selection.changed), (self.base, self.base, []))

    def test_empty_current_development_plan_refuses_tracked_child_dirt_before_discovery(self):
        child = self.add_submodule()
        (child / "src/lib.rs").write_text("pub fn uncommitted_child() {}\n")
        self.assert_empty_uncommitted_plan_refuses()

    def test_empty_current_development_plan_refuses_changed_child_head_before_discovery(self):
        child = self.add_submodule()
        (child / "src/lib.rs").write_text("pub fn committed_child() {}\n")
        fixtures.git_in(child, "add", "src/lib.rs")
        fixtures.git_in(child, "commit", "-qm", "changed child")
        self.assert_empty_uncommitted_plan_refuses()

    def test_a_landing_bound_head_is_still_the_checkout_for_the_empty_subject_refusal(self):
        # discover_landing binds an implicit HEAD to the transaction's sha
        # (before.head) before discovery; the bound sha is still this
        # checkout, so a dirty tree with an empty committed diff is refused
        # before any scan, as for "HEAD". A sha a person states keeps full
        # discovery (explicit-current below).
        (self.root / "crates/base/src/lib.rs").write_text("pub fn unstaged() {}\n")
        head = fixtures.git_in(self.root, "rev-parse", "HEAD")
        with mock.patch.object(ls, "build_graph", side_effect=AssertionError("discovery forbidden")), \
                self.assertRaisesRegex(gate.LandingUnjudged, "empty committed development subject"):
            gate.compute_discovery(self.base, head, False, None, gate.DiscoveryProfile.DEVELOPMENT, checkout=True)
        session = gate.DiscoverySession()
        landing = gate.LandingRange(self.base, self.base, "fixture", True, (), "")
        with mock.patch.object(gate, "read_landing", return_value=landing), \
                mock.patch.object(gate, "compute_discovery", wraps=gate.compute_discovery) as discovery, \
                mock.patch.object(ls, "build_graph", side_effect=AssertionError("discovery forbidden")), \
                contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaisesRegex(gate.LandingUnjudged, "empty committed development subject"):
            gate.discover_landing(self.base, "HEAD", session=session, profile=gate.DiscoveryProfile.DEVELOPMENT)
        self.assertEqual(discovery.call_args.kwargs.get("checkout"), True)

    def test_empty_clean_untracked_and_explicit_historical_subjects_keep_full_discovery(self):
        for state in ("clean", "untracked", "explicit-current", "historical"):
            with self.subTest(state=state):
                head = "HEAD"
                if state == "untracked":
                    (self.root / "untracked.rs").write_text("fn untracked() {}\n")
                elif state == "explicit-current":
                    (self.root / "crates/base/src/lib.rs").write_text("pub fn unstaged() {}\n")
                    head = self.base
                elif state == "historical":
                    self.commit("scripts/land_gate.py")
                    (self.root / "scripts/land_gate.py").write_text("# unstaged current source\n")
                    head = self.base
                with mock.patch.object(gate, "compute", wraps=gate.compute) as full:
                    graph, selection, base = gate.compute_discovery(
                        self.base, head, False, None, gate.DiscoveryProfile.DEVELOPMENT)
                full.assert_called_once_with(self.base, head, False, None)
                self.assertEqual((base, graph.index.rev, selection.changed), (self.base, self.base, []))

    def test_empty_dirty_full_profile_keeps_full_discovery(self):
        (self.root / "crates/base/src/lib.rs").write_text("pub fn unstaged() {}\n")
        with mock.patch.object(gate, "compute", wraps=gate.compute) as full:
            graph, selection, base = gate.compute_discovery(
                self.base, "HEAD", False, None, gate.DiscoveryProfile.FULL)
        full.assert_called_once_with(self.base, "HEAD", False, None)
        self.assertEqual((base, graph.index.rev, selection.changed), (self.base, self.base, []))

    def test_nonempty_dirty_development_subject_keeps_existing_owner_refusal(self):
        self.commit(self.UNOWNED[0])
        (self.root / "crates/base/src/lib.rs").write_text("pub fn unstaged() {}\n")
        with self.assertRaisesRegex(gate.LandingUnjudged, "unsupported changed owner/input"):
            gate.compute_discovery(self.base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)

    def test_nonempty_dirty_development_subject_keeps_registered_check_selection(self):
        self.commit("scripts/land_gate.py")
        (self.root / "scripts/land_gate.py").write_text("# unstaged candidate\n")
        graph, selection, base = gate.compute_discovery(
            self.base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
        self.assertIsInstance(selection, gate.DeclaredDevelopmentSelection)
        self.assertEqual((base, selection.changed), (self.base, ["scripts/land_gate.py"]))
        scope = development.scope(graph, selection)
        self.assertEqual(scope.errors, [])
        self.assertEqual(scope.tests, sorted(development.PROGRAM_TESTS["scripts/land_gate.py"]))

    def test_possible_scope_preserves_full_discovery_and_semantic_refusals(self):
        # A path-only positive grants nothing. Locks, prose, recipes and
        # component manifests retain their existing full discovery path.
        paths = ("Cargo.lock", "docs/reach.md", "tests/run-make/new/rmake.rs",
                 "src/tools/compiletest/Cargo.toml")
        for path in paths:
            with self.subTest(path=path):
                base = self.commit(path)
                expected = object()
                with mock.patch.object(gate, "compute", return_value=expected) as full:
                    self.assertIs(gate.compute_discovery(
                        base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT), expected)
                full.assert_called_once_with(base, "HEAD", False, None)
        # A registered name with symlink mode must still undergo normal
        # discovery and fail its existing regular-source semantic check.
        base = fixtures.git_in(self.root, "rev-parse", "HEAD")
        source = self.root / "scripts/land_gate.py"
        source.unlink()
        source.symlink_to("../Cargo.toml")
        fixtures.git_in(self.root, "add", ".")
        fixtures.git_in(self.root, "commit", "-qm", "unsafe registered source")
        with mock.patch.object(gate, "compute", wraps=gate.compute) as full:
            graph, selection, _ = gate.compute_discovery(
                base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
        full.assert_called_once()
        self.assertFalse(development.has_declared_source_ownership(graph.index, selection.changed))
        self.assertTrue(any("not a regular file" in error for error in development.scope(graph, selection).errors))

    def test_full_profile_does_not_use_development_eligibility(self):
        base = self.commit(self.UNOWNED[0])
        expected = object()
        with mock.patch.object(gate, "development_discovery_inputs", side_effect=AssertionError("development filter forbidden")), \
                mock.patch.object(gate, "compute", return_value=expected) as full:
            self.assertIs(gate.compute_discovery(base, "HEAD", True, None, gate.DiscoveryProfile.FULL), expected)
        full.assert_called_once_with(base, "HEAD", True, None)


class ControllerDescriptorDevelopmentTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="development-controller-descriptors-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        owner = development.CONTROLLER_DESCRIPTORS
        self.base = fixtures.make_repo(self.root, {
            "Cargo.toml": f'[workspace]\nmembers=["{owner}"]\ndefault-members=["{owner}"]\n',
            owner + "/Cargo.toml": '[package]\nname="trust-resource-controller"\nversion="0.1.0"\n',
            owner + "/src/lib.rs": "mod descriptors;\n",
            owner + "/src/descriptors.rs": "pub fn descriptor() {}\n#[cfg(test)] mod tests;\n",
            owner + "/src/descriptors/tests.rs": "#[test] fn descriptor_control() {}\n",
            owner + "/src/bootstrap_graph.rs": "pub fn other() {}\n",
            "docs/DECISION_QUEUE.md": "# Decisions\n",
            "scripts/land_gate.py": "# gate fixture\n",
            "scripts/lib/land_development.py": "# development fixture\n",
            "scripts/tests/land_development_test.py": "# selector fixture\n",
        }, {})
        for source in development.CONTROLLER_DESCRIPTOR_SOURCES:
            with (self.root / source).open("a") as output:
                output.write("// descriptor source change\n")
        fixtures.git_in(self.root, "add", ".")
        fixtures.git_in(self.root, "commit", "-qm", "descriptor source fixture")
        self.graph = ls.build_manifest_graph(ls.TreeIndex.load(str(self.root), "HEAD"))
        self.changed = ls.changed_paths(str(self.root), self.base, self.graph.index.rev)
        self.selected = ls.Selection(self.base, self.graph.index.rev, self.changed, [])

    def test_real_descriptor_paths_select_only_the_fresh_all_features_filtered_leg(self):
        self.assertEqual(set(self.changed), development.CONTROLLER_DESCRIPTOR_SOURCES)
        self.assertTrue(development.may_have_scope(self.changed))
        self.assertTrue(development.has_declared_source_ownership(self.graph.index, self.changed))
        scoped = development.scope(self.graph, self.selected)
        self.assertFalse(scoped.errors or scoped.packages or scoped.recipes or scoped.local_git_import)
        self.assertTrue(scoped.controller_descriptors)
        with mock.patch.object(gate, "REPO_ROOT", self.root), \
                mock.patch.object(ls, "build_graph", side_effect=AssertionError("full scan forbidden")):
            graph, selection, base = gate.compute_discovery(
                self.base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
        self.assertEqual(base, self.base)
        self.assertIsInstance(selection, gate.DeclaredDevelopmentSelection)
        landing = gate.LandingRange(base, selection.head, "local", True, tuple(self.changed), "")
        legs = gate.declared_development_legs(graph, selection, 2, gate.PushHook(False, "fixture"), landing)
        descriptor = next(leg for leg in legs if leg.id == development.CONTROLLER_DESCRIPTOR_LEG)
        self.assertEqual(descriptor.command, [
            "targo", "--unverified", "test", "--locked", "--offline", "--manifest-path",
            development.CONTROLLER_DESCRIPTORS + "/Cargo.toml", "--all-features", "--lib", "descriptors::tests",
            "--", "--test-threads=1",
        ])
        self.assertTrue(descriptor.force_run)
        self.assertFalse(descriptor.cache_members or descriptor.prepare or descriptor.needs_stage1)
        self.assertEqual(descriptor.inputs, [development.CONTROLLER_DESCRIPTORS])
        self.assertTrue(next(leg for leg in legs if leg.id == "push-rows").force_run)
        self.assertIn("--all-rows", next(leg.command for leg in legs if leg.id == "push-rows"))
        self.assertTrue(next(leg for leg in legs if leg.id == "compiler-check").diagnostic_only)
        for name in ("tcb-panic-ratchet", "ir-cohort"):
            self.assertFalse(next(leg for leg in legs if leg.id == name).diagnostic_only)

    def test_descriptor_selector_and_decision_delta_retains_normal_prose_discovery_and_guards(self):
        for path in ("docs/DECISION_QUEUE.md", "scripts/land_gate.py", "scripts/lib/land_development.py",
                     "scripts/tests/land_development_test.py"):
            with (self.root / path).open("a") as output:
                output.write("# changed declaration\n")
        fixtures.git_in(self.root, "add", ".")
        fixtures.git_in(self.root, "commit", "-qm", "descriptor and declared validation inputs")
        with mock.patch.object(gate, "REPO_ROOT", self.root), \
                mock.patch.object(ls, "build_graph", wraps=ls.build_graph) as complete:
            graph, selected, base = gate.compute_discovery(
                self.base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
        complete.assert_called_once()
        self.assertNotIsInstance(selected, gate.DeclaredDevelopmentSelection)
        self.assertIn("docs/DECISION_QUEUE.md", selected.changed)
        self.assertFalse(development.has_declared_source_ownership(graph.index, selected.changed))
        scoped = development.scope(graph, selected)
        self.assertFalse(scoped.errors)
        self.assertTrue(scoped.controller_descriptors)
        self.assertTrue(set(development.SELECTOR_TESTS) <= set(scoped.tests))
        landing = gate.LandingRange(base, selected.head, "local", True, tuple(selected.changed), "")
        legs = gate.development_legs(graph, selected, [fixtures.leg(id="push-rows")], 2, landing)
        self.assertEqual(sum(leg.id == development.CONTROLLER_DESCRIPTOR_LEG for leg in legs), 1)
        self.assertTrue(any(leg.id == "development-validation-tests" for leg in legs))
        self.assertIn("--all-rows", next(leg.command for leg in legs if leg.id == "push-rows"))
        graph.packages[development.CONTROLLER_DESCRIPTORS].reads.append(
            ls.Read("compile", "docs/DECISION_QUEUE.md", False, "actual direct prose reader"))
        scoped = development.scope(graph, selected)
        self.assertFalse(scoped.errors)
        self.assertEqual(scoped.packages, [development.CONTROLLER_COMPONENT])
        legs = gate.development_legs(graph, selected, [], 2)
        self.assertTrue({"development-package-trust-resource-controller-" + cohort
                         for cohort in ("dto", "receiver", "client")} <= {leg.id for leg in legs})
        graph.packages["crates/unowned-reader"] = ls.Package("crates/unowned-reader", "unowned-reader")
        graph.packages["crates/unowned-reader"].reads.append(
            ls.Read("compile", "docs/DECISION_QUEUE.md", False, "actual unowned direct prose reader"))
        self.assertTrue(any("direct reader" in error for error in development.scope(graph, selected).errors))

    def test_actual_outgoing_descriptor_scope_is_added_once_without_hiding_unknown_inputs(self):
        landing = gate.LandingRange(self.base, self.graph.index.rev, "local", True, tuple(self.changed), "")
        for changed in ([], self.changed):
            with self.subTest(changed=changed):
                selected = ls.Selection(self.base, self.graph.index.rev, changed, [])
                legs = gate.development_legs(self.graph, selected, [], 2, landing)
                self.assertEqual([leg.id for leg in legs], [development.CONTROLLER_DESCRIPTOR_LEG])
        unknown = "crates/unowned-controller/src/bootstrap_graph.rs"
        landing = gate.LandingRange(self.base, self.graph.index.rev, "local", True, (unknown,), "")
        with self.assertRaisesRegex(RuntimeError, "no declared development component/test owner"):
            gate.development_legs(self.graph, self.selected, [], 2, landing)

    def test_other_controller_sources_use_complete_owner_and_never_descriptor_only(self):
        owner = development.CONTROLLER_DESCRIPTORS
        for path in (owner + "/src/lib.rs", owner + "/src/bootstrap_graph.rs",
                     owner + "/src/descriptors/helper.rs", owner + "/src/descriptors_extra.rs"):
            with self.subTest(path=path):
                selected = ls.Selection(self.base, self.graph.index.rev, [path], [])
                scoped = development.scope(self.graph, selected)
                self.assertTrue(development.may_have_scope([path]))
                self.assertFalse(scoped.errors or scoped.controller_descriptors)
                self.assertEqual(scoped.packages, [owner])
        manifest = owner + "/Cargo.toml"
        self.assertTrue(development.has_declared_source_ownership(self.graph.index, [manifest], self.base))
        selected = ls.Selection(self.base, self.graph.index.rev, [manifest], [],
                                cargo_impacts={manifest: {owner}})
        self.assertFalse(development.scope(self.graph, selected).errors)
        unknown = "crates/unowned-controller/Cargo.toml"
        self.assertFalse(development.may_have_scope([unknown]))
        self.assertTrue(development.scope(self.graph,
            ls.Selection(self.base, self.graph.index.rev, [unknown], [])).errors)
        with mock.patch.object(gate, "compute", return_value="full diagnostic") as complete:
            self.assertEqual(gate.compute_discovery(
                self.base, "HEAD", False, None, gate.DiscoveryProfile.FULL), "full diagnostic")
        complete.assert_called_once()

    def test_mixed_descriptor_and_receiver_sources_retain_both_complete_owners(self):
        owner = development.CONTROLLER_DESCRIPTORS
        changed = [*self.changed, owner + "/src/lib.rs"]
        selected = ls.Selection(self.base, self.graph.index.rev, changed, [])
        legs = gate.development_legs(self.graph, selected, [], 2)
        expected = {development.CONTROLLER_DESCRIPTOR_LEG,
                    *("development-package-trust-resource-controller-" + cohort
                      for cohort in ("dto", "receiver", "client", "all-features"))}
        self.assertTrue(expected <= {leg.id for leg in legs})
        self.assertTrue(all(leg.force_run and not leg.diagnostic_only for leg in legs))

    def test_missing_foreign_or_nonregular_descriptor_inputs_refuse(self):
        owner = development.CONTROLLER_DESCRIPTORS
        for path in (*sorted(development.CONTROLLER_DESCRIPTOR_SOURCES), owner + "/Cargo.toml"):
            for mode in (None, "120000", "160000"):
                with self.subTest(path=path, mode=mode):
                    graph = copy.deepcopy(self.graph)
                    if mode is None:
                        del graph.index.entries[path]
                    else:
                        graph.index.entries[path] = (mode, "0" * 40)
                    self.assertTrue(development.scope(graph, self.selected).errors)
        graph = copy.deepcopy(self.graph)
        graph.packages[owner].name = "another-controller"
        self.assertTrue(development.scope(graph, self.selected).errors)
        graph = copy.deepcopy(self.graph)
        graph.opaque[owner] = "unknown manifest"
        self.assertTrue(development.scope(graph, self.selected).errors)
        graph = copy.deepcopy(self.graph)
        graph.packages[owner + "/src"] = ls.Package(owner + "/src", "foreign-owner")
        self.assertTrue(development.scope(graph, self.selected).errors)
        graph = copy.deepcopy(self.graph)
        graph.index.entries[owner + "/src"] = ("120000", "0" * 40)
        self.assertFalse(development.has_declared_source_ownership(graph.index, self.changed))


class TargoNativeDevelopmentTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="development-targo-native-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.files = {
            "Cargo.toml": '[workspace]\nmembers=["crates/trust-certify"]\ndefault-members=["crates/trust-certify"]\n[workspace.package]\nversion="0.13.0"\n',
            development.LOCAL_GIT_WORKSPACE + "/Cargo.toml": '[package]\nname="targo"\nversion="0.1.0"\n[workspace]\nmembers=["crates/targo-core"]\n',
            development.LOCAL_GIT_CORE + "/Cargo.toml": '[package]\nname="targo-core"\nversion="0.1.0"\n',
            "crates/trust-certify/Cargo.toml": '[package]\nname="trust-certify"\nversion.workspace=true\n[target."cfg(unix)".dependencies]\ntrust-resource-provenance={path="../trust-resource-provenance"}\n',
            "crates/trust-resource-provenance/Cargo.toml": '[package]\nname="trust-resource-provenance"\nversion="0.13.0"\n[workspace]\n',
            development.TARGO_LOCK: 'version = 4\n[[package]]\nname="trust-certify"\nversion="0.13.0"\ndependencies=["other"]\n[[package]]\nname="trust-resource-provenance"\nversion="0.13.0"\n[[package]]\nname="other"\nversion="1.0.0"\nsource="registry+https://example.invalid/index"\nchecksum="exact-checksum"\n',
            development.TARGO_TRIAGEBOT: '[autolabel."Command-vendor"]\ntrigger_files=["src/bin/cargo/commands/vendor.rs", "src/ops/cargo_vendor.rs"]\n',
            "docs/DECISION_QUEUE.md": "# Decisions\n",
        }
        for path in (development.TARGO_CLEANUP_SOURCES | development.TARGO_NATIVE_CORE_SOURCES
                     | set(development.TARGO_NATIVE_TEST_SOURCES)) - set(development.TARGO_NATIVE_MODULE_MOVES.values()):
            self.files[path] = "// original source\n"
        self.files[development.TARGO_COMPILER_CONTEXT_VISIBILITY] = "// compiler context fixture\n" + "".join(
            f"\npub fn {name}<L: std::borrow::Borrow<layout::LayoutPaths>>() {{}}\n"
            for name in development.TARGO_PRIVATE_CONTEXT_HELPERS)
        self.base = fixtures.make_repo(self.root, self.files, {})
        self.current = set(self.files)

    def commit(self, changes=None, remove=()):
        files = dict(self.files, **(changes or {}))
        for path in remove:
            files.pop(path, None)
        for path in self.current - files.keys():
            (self.root / path).unlink()
        for path, value in files.items():
            destination = self.root / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(value)
        self.current = set(files)
        fixtures.git_in(self.root, "add", "-A")
        fixtures.git_in(self.root, "commit", "-qm", "native owner control", "--allow-empty")
        graph = ls.build_manifest_graph(ls.TreeIndex.load(str(self.root), "HEAD"))
        changed = ls.changed_paths(str(self.root), self.base, graph.index.rev)
        return graph, ls.Selection(self.base, graph.index.rev, changed, [])

    def cleanup(self):
        path = development.LOCAL_GIT_CORE + "/src/ops/cargo_clean.rs"
        return self.commit({path: "// compiler-free cleanup change\n"})

    def legs(self, graph, selection, landing=None):
        with mock.patch.object(gate, "host_triple", return_value="aarch64-apple-darwin"), \
                mock.patch.object(gate.platform, "system", return_value="Darwin"):
            return gate.development_legs(graph, selection, [], 2, landing)

    def assert_native_recipe(self, leg):
        self.assertEqual(leg.command.count("--features"), 1)
        self.assertEqual(leg.command[leg.command.index("--features") + 1], "all-static")
        for value in ('env.LZMA_API_STATIC.value="1"', 'env.LZMA_API_STATIC.force=true',
                      'env.LZMA_API_STATIC.relative=false'):
            self.assertIn(value, leg.command)
            self.assertEqual(leg.command[leg.command.index(value) - 1], "--config")

    def test_cleanup_core_and_frontend_have_distinct_real_exact_case_owners(self):
        graph, selection = self.cleanup()
        scoped = development.scope(graph, selection)
        self.assertFalse(scoped.errors or scoped.packages or scoped.local_git_import)
        self.assertTrue(scoped.targo_native_core and scoped.targo_cleanup)
        self.assertTrue(development.may_have_scope(selection.changed))
        self.assertTrue(development.has_declared_source_ownership(graph.index, selection.changed))
        legs = {leg.id: leg for leg in self.legs(graph, selection)}
        native, cleanup = legs[development.TARGO_NATIVE_CORE_LEG], legs[development.TARGO_CLEANUP_LEG]
        for leg, cases in ((native, development.TARGO_NATIVE_CORE_CASES), (cleanup, development.TARGO_CLEANUP_CASES)):
            self.assert_native_recipe(leg)
            self.assertTrue(leg.force_run)
            self.assertFalse(leg.cache_members or leg.prepare or leg.needs_stage1)
            self.assertEqual(leg.command[:7], ["targo", "--unverified", "test", "--locked", "--offline",
                                             "--manifest-path", "src/tools/targo/Cargo.toml"])
            self.assertEqual(leg.command[leg.command.index("--") + 1:], ["--exact", "--test-threads=1", *cases])
            self.assertNotIn("build.target=[]", leg.command)
            self.assertNotIn("--target", leg.command)
        self.assertEqual(len(set(development.TARGO_NATIVE_CORE_CASES)), 25)
        self.assertEqual(len(set(development.TARGO_CLEANUP_CASES)), 4)
        self.assertNotIn("fresh_kernel_component_child", " ".join(native.command))
        self.assertIn("native_math_hints_receive_fresh_kernel_checks_without_a_native_node_grant", " ".join(native.command))
        self.assertIn('env.TARGO_CLEAN_TEST_BINARY.value=""', cleanup.command)
        self.assertIn("env.TARGO_CLEAN_TEST_BINARY.force=true", cleanup.command)
        self.assertIn("env.TARGO_CLEAN_TEST_BINARY.relative=false", cleanup.command)
        frontend = development.LOCAL_GIT_WORKSPACE + "/src/bin/cargo/commands/clean.rs"
        graph, selection = self.commit({frontend: "// actual frontend change\n"})
        self.assertEqual([leg.id for leg in self.legs(graph, selection)], [development.TARGO_CLEANUP_LEG])

    def test_native_host_refuses_unsupported_cases_and_no_frontend_zero_test_library(self):
        graph, selection = self.cleanup()
        with mock.patch.object(gate, "host_triple", return_value="x86_64-unknown-linux-gnu"):
            with self.assertRaisesRegex(RuntimeError, "require aarch64-apple-darwin"):
                gate.development_legs(graph, selection, [], 2)
        for path in (development.LOCAL_GIT_WORKSPACE + "/src/lib.rs",
                     development.LOCAL_GIT_CORE + "/src/native_job_service/verification/unknown.rs",
                     development.LOCAL_GIT_CORE + "/src/resource_v3/unknown.rs"):
            with self.subTest(path=path):
                graph, selection = self.commit({path: "// unowned\n"})
                self.assertFalse(development.may_have_scope(selection.changed))
                self.assertFalse(development.has_declared_source_ownership(graph.index, selection.changed))
                self.assertTrue(development.scope(graph, selection).errors)

    def test_all_declared_native_components_and_real_module_moves_are_owned(self):
        changes = {path: "// owned native change\n" for path in development.TARGO_NATIVE_CORE_SOURCES}
        changes.update({new: self.files[old] for old, new in development.TARGO_LAYOUT_ONLY_MOVES.items()})
        path = development.TARGO_COMPILER_CONTEXT_VISIBILITY
        changes[path] = self.files[path].replace("\npub fn ", "\nfn ")
        graph, selection = self.commit(changes, development.TARGO_NATIVE_MODULE_MOVES)
        self.assertFalse(development.scope(graph, selection).errors)
        self.assertTrue(development.has_declared_source_ownership(graph.index, selection.changed))
        self.assertEqual([leg.id for leg in self.legs(graph, selection)], [development.TARGO_NATIVE_CORE_LEG])
        # Missing old sources cannot masquerade as a move without their exact
        # regular destination, and deleting an ordinary source is unsupported.
        old, new = next(iter(development.TARGO_NATIVE_MODULE_MOVES.items()))
        for path in (new, development.LOCAL_GIT_CORE + "/src/compiler/mod.rs"):
            with self.subTest(path=path):
                broken = copy.deepcopy(graph)
                del broken.index.entries[path]
                self.assertTrue(development.scope(broken, selection).errors)

    def test_general_compiler_module_only_owns_exact_context_visibility_repair(self):
        path = development.TARGO_COMPILER_CONTEXT_VISIBILITY
        original = self.files[path]
        private = original.replace("\npub fn ", "\nfn ")
        graph, selected = self.commit({path: private})
        self.assertFalse(development.scope(graph, selected).errors)
        self.assertEqual([leg.id for leg in self.legs(graph, selected)], [development.TARGO_NATIVE_CORE_LEG])
        for bad in (private + "// unrelated compiler policy\n", private.replace(" {}", " { changed_policy(); }", 1),
                    private.replace("\nfn ", "\npub(crate) fn ", 1),
                    original.replace("\npub fn ", "\nfn ", 1)):
            graph, selected = self.commit({path: bad})
            self.assertTrue(development.scope(graph, selected).errors)

    def test_context_visibility_accepts_only_remaining_prefix_when_peer_already_privatized_one(self):
        path = development.TARGO_COMPILER_CONTEXT_VISIBILITY
        original, original_base = self.files[path], self.base
        private = original.replace("\npub fn ", "\nfn ")
        for name in development.TARGO_PRIVATE_CONTEXT_HELPERS:
            self.base = original_base
            partial = original.replace("\npub fn " + name, "\nfn " + name, 1)
            graph, _selected = self.commit({path: partial})
            self.base = graph.index.rev
            graph, selected = self.commit({path: private})
            self.assertFalse(development.scope(graph, selected).errors, name)

    def test_unrelated_layout_only_modules_require_identical_bodies_and_actual_moves(self):
        for old, new in development.TARGO_LAYOUT_ONLY_MOVES.items():
            with self.subTest(source=old):
                graph, selected = self.commit({new: self.files[old]}, [old])
                self.assertFalse(development.scope(graph, selected).errors)
                graph, selected = self.commit({new: "// unrelated semantic change\n"}, [old])
                self.assertTrue(development.scope(graph, selected).errors)
                graph, selected = self.commit({old: "// changed in place\n"})
                self.assertTrue(development.scope(graph, selected).errors)
                graph, selected = self.commit({new: self.files[old]})
                self.assertTrue(development.scope(graph, selected).errors)

    def test_required_missing_opaque_foreign_linked_and_ambiguous_sources_refuse(self):
        graph, selection = self.cleanup()
        for path in (*development.TARGO_CLEANUP_SOURCES, *development.TARGO_NATIVE_TEST_SOURCES,
                     development.LOCAL_GIT_CORE + "/Cargo.toml", development.LOCAL_GIT_WORKSPACE + "/Cargo.toml"):
            for mode in (None, "120000", "160000"):
                with self.subTest(path=path, mode=mode):
                    broken = copy.deepcopy(graph)
                    if mode is None:
                        del broken.index.entries[path]
                    else:
                        broken.index.entries[path] = (mode, "0" * 40)
                    self.assertTrue(development.scope(broken, selection).errors)
        for mutation in ("opaque", "foreign", "ancestor", "case"):
            broken = copy.deepcopy(graph)
            owner = development.LOCAL_GIT_CORE
            if mutation == "opaque":
                broken.opaque[owner] = "unknown manifest"
            elif mutation == "foreign":
                broken.packages[owner + "/src"] = ls.Package(owner + "/src", "foreign")
            elif mutation == "ancestor":
                broken.index.entries[owner + "/src"] = ("120000", "0" * 40)
            else:
                broken.index.entries[owner + "/src/compiler/Layout.rs"] = ("100644", "0" * 40)
            broken.__dict__.pop("_index_spellings", None)
            self.assertTrue(development.scope(broken, selection).errors, mutation)

    def test_changed_core_example_compiles_its_actual_target_without_empty_libtest_credit(self):
        graph, selected = self.commit({development.TARGO_CORE_EXAMPLE: "fn main() {}\n"})
        scoped = development.scope(graph, selected)
        self.assertFalse(scoped.errors)
        self.assertTrue(scoped.targo_core_example)
        example, = self.legs(graph, selected)
        self.assertEqual(example.id, development.TARGO_CORE_EXAMPLE_LEG)
        self.assertEqual(example.command[:3], ["targo", "--unverified", "check"])
        self.assertEqual(example.command[-4:], ["-p", "targo-core", "--example", "trust_compiler_query"])
        self.assertTrue(example.force_run)
        self.assertNotIn("--lib", example.command)
        self.assertIn("--message-format=json", example.command)
        self.assert_native_recipe(example)

    def test_example_check_requires_actual_source_bound_nonempty_compiler_artifact(self):
        metadata = self.root / "actual-example.rmeta"
        metadata.write_bytes(b"fixture metadata")
        row = {"reason": "compiler-artifact", "target": {"name": "trust_compiler_query", "kind": ["example"],
                "src_path": str(self.root / development.TARGO_CORE_EXAMPLE)},
               "manifest_path": str(self.root / development.LOCAL_GIT_CORE / "Cargo.toml"),
               "filenames": [str(metadata)], "fresh": False, "trust_compile_kind": "host",
               "trust_compile_target": gate.host_triple(), "trust_compile_mode": "check",
               "trust_unit_identity_sha256": "a" * 64}
        with mock.patch.object(gate, "REPO_ROOT", self.root):
            self.assertEqual(gate.development_example_result(json.dumps(row), 0)[0], 0)
            for text, code in (("target filter specified, but no targets matched; this is a no-op", 0),
                               ("", 0), (json.dumps(row), 1), (json.dumps(row) + "\n" + json.dumps(row), 0)):
                self.assertNotEqual(gate.development_example_result(text, code)[0], 0)
            for key, value in (("filenames", []), ("filenames", [str(self.root / "absent")]),
                               ("manifest_path", "/foreign/Cargo.toml"), ("fresh", None),
                               ("trust_compile_kind", "target"), ("trust_compile_target", "foreign-host"),
                               ("trust_compile_mode", "build"), ("trust_unit_identity_sha256", "")):
                bad = dict(row, **{key: value})
                self.assertNotEqual(gate.development_example_result(json.dumps(bad), 0)[0], 0)
            bad = copy.deepcopy(row)
            bad["target"]["src_path"] = "/foreign/example.rs"
            self.assertNotEqual(gate.development_example_result(json.dumps(bad), 0)[0], 0)
            metadata.write_bytes(b"")
            # A checked binary can have no exported Rust metadata. The real
            # artifact message/unit identity, rather than byte size, owns it.
            self.assertEqual(gate.development_example_result(json.dumps(row), 0)[0], 0)
            alias = self.root / "symlink-example.rmeta"
            alias.symlink_to(metadata)
            self.assertNotEqual(gate.development_example_result(json.dumps(dict(row, filenames=[str(alias)])), 0)[0], 0)

    def test_declared_manifest_discovery_and_outgoing_scope_union_stay_source_bound(self):
        graph, selection = self.cleanup()
        with mock.patch.object(gate, "REPO_ROOT", self.root), \
                mock.patch.object(ls, "build_graph", side_effect=AssertionError("full scan forbidden")):
            _graph, declared, _base = gate.compute_discovery(
                self.base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
        self.assertIsInstance(declared, gate.DeclaredDevelopmentSelection)
        frontend = development.LOCAL_GIT_WORKSPACE + "/src/bin/cargo/commands/clean.rs"
        subject = ls.Selection(self.base, graph.index.rev, [frontend], [])
        landing = gate.LandingRange(self.base, graph.index.rev, "local", True, tuple(selection.changed), "")
        with mock.patch.object(gate, "landing_selection", return_value=selection):
            ids = [leg.id for leg in self.legs(graph, subject, landing)]
        self.assertEqual(ids.count(development.TARGO_CLEANUP_LEG), 1)
        self.assertEqual(ids.count(development.TARGO_NATIVE_CORE_LEG), 1)
        unowned = ls.Selection(self.base, graph.index.rev, ["unknown/outgoing.rs"], [])
        with mock.patch.object(gate, "landing_selection", return_value=unowned):
            with self.assertRaisesRegex(RuntimeError, "outgoing scope refused"):
                self.legs(graph, subject, landing)

    def unused_patch_order_base(self):
        header = '\n[[patch.unused]]\n'
        duplicate = 'name="trust-ir-conformance"\nversion="0.14.0"\n'
        other = ('name="unused-other"\nversion="1.0.0"\n'
                 'source="registry+https://example.invalid/unused"\nchecksum="retained-unused"\n'
                 '# [[patch.unused]] is comment data, not a row\n')
        last = 'name="unused-last"\nversion="2.0.0"\n'
        prefix = self.files[development.TARGO_LOCK]
        self.files[development.TARGO_LOCK] += ''.join(header + row for row in (
            duplicate, other, duplicate, duplicate, last))
        self.commit()
        self.base = fixtures.git_in(self.root, "rev-parse", "HEAD")
        return prefix + ''.join(header + row for row in (
            duplicate, last, duplicate, duplicate, other))

    def test_unused_patch_order_owns_only_full_row_permutation_with_duplicates(self):
        graph, selected = self.commit({development.TARGO_LOCK: self.unused_patch_order_base()})
        full = ls.select(graph, self.base, selected.changed)
        self.assertTrue(full.everything)
        scoped = development.scope(graph, full)
        self.assertFalse(scoped.errors)
        self.assertTrue(scoped.targo_native_core and scoped.targo_cleanup)
        self.assertEqual({leg.id for leg in self.legs(graph, full)},
                         {development.TARGO_NATIVE_CORE_LEG, development.TARGO_CLEANUP_LEG})
        full.everything.append("unresolved source input")
        self.assertIn("unresolved source input", development.scope(graph, full).errors)

    def test_unused_patch_order_composes_with_exact_build_input_and_sha2_repairs(self):
        changes = self.build_input_base(dangling_sha2=True)
        prefix = self.files[development.TARGO_LOCK]
        reordered = self.unused_patch_order_base()
        changes[development.TARGO_LOCK] += reordered[len(prefix):]
        graph, selected = self.commit(changes)
        self.assertTrue(development.targo_build_rs_repair(graph, self.base))
        self.assertFalse(development.scope(graph, ls.select(graph, self.base, selected.changed)).errors)
        changes[development.TARGO_LOCK] = changes[development.TARGO_LOCK].replace(
            'version="0.14.0"', 'version="0.14.1"', 1)
        graph, selected = self.commit(changes)
        self.assertFalse(development.targo_build_rs_repair(graph, self.base))
        self.assertTrue(development.scope(graph, selected).errors)

    def test_unused_patch_order_refuses_row_body_count_prefix_and_manifest_changes(self):
        good = self.unused_patch_order_base()
        header = '\n[[patch.unused]]\n'
        duplicate = header + 'name="trust-ir-conformance"\nversion="0.14.0"\n'
        bad = (good.replace(duplicate, '', 1), good + duplicate,
               good.replace('version="0.14.0"', 'version="0.14.1"', 1),
               good.replace('source="registry+https://example.invalid/unused"', 'source="git+https://example.invalid/unused"'),
               good.replace('checksum="retained-unused"', 'checksum="forged-unused"'),
               good.replace('checksum="retained-unused"', 'checksum="retained-unused"\nextra="new-field"'),
               good.replace('name="unused-other"\nversion="1.0.0"', 'version="1.0.0"\nname="unused-other"'),
               good.replace('checksum="exact-checksum"', 'checksum="forged-package"'),
               good.replace('dependencies=["other"]', 'dependencies=["other", "unexpected"]'),
               good.replace(header, '\n\n[[patch.unused]]\n', 1), good[:-1], '[malformed')
        for value in bad:
            with self.subTest(value=value):
                graph, selected = self.commit({development.TARGO_LOCK: value})
                self.assertTrue(development.scope(graph, selected).errors)
        for manifest in ("Cargo.toml", development.TARGO_MANIFEST, development.LOCAL_GIT_CORE + "/Cargo.toml"):
            graph, selected = self.commit({development.TARGO_LOCK: good, manifest: self.files[manifest] + '# unrelated\n'})
            self.assertTrue(development.scope(graph, selected).errors)
        graph, selected = self.commit({development.TARGO_LOCK: good})
        for path in (development.TARGO_LOCK, development.TARGO_MANIFEST, development.LOCAL_GIT_CORE + "/Cargo.toml"):
            for mode in (None, '120000', '160000'):
                broken = copy.deepcopy(graph)
                if mode is None:
                    del broken.index.entries[path]
                else:
                    broken.index.entries[path] = (mode, '0' * 40)
                self.assertTrue(development.scope(broken, selected).errors)
        graph.opaque[development.LOCAL_GIT_WORKSPACE] = 'unknown manifest'
        self.assertTrue(development.scope(graph, selected).errors)

    def test_unused_patch_order_refuses_header_like_text_inside_a_literal(self):
        good = self.unused_patch_order_base()
        marker = 'checksum="retained-unused"\n'
        literal = marker + 'note="""\n[[patch.unused]]\n"""\n'
        self.files[development.TARGO_LOCK] = self.files[development.TARGO_LOCK].replace(marker, literal)
        self.commit()
        self.base = fixtures.git_in(self.root, "rev-parse", "HEAD")
        graph, selected = self.commit({development.TARGO_LOCK: good.replace(marker, literal)})
        self.assertTrue(development.scope(graph, selected).errors)

    def restored_lock(self):
        return self.files[development.TARGO_LOCK].replace('dependencies=["other"]',
                                                        'dependencies=["other", "trust-resource-provenance"]')

    def test_exact_standalone_lock_restoration_is_owned_without_changing_full_cargo_semantics(self):
        graph, selection = self.commit({development.TARGO_LOCK: self.restored_lock()})
        self.assertTrue(development.targo_lock_restoration(graph, self.base))
        full = ls.select(graph, self.base, selection.changed)
        self.assertTrue(full.everything)
        self.assertNotIn(development.TARGO_LOCK, full.cargo_impacts)
        scoped = development.scope(graph, full)
        self.assertFalse(scoped.errors)
        self.assertTrue(scoped.targo_native_core and scoped.targo_cleanup)
        self.assertEqual(len(self.legs(graph, full)), 2)
        full.everything.append("unknown source reach")
        self.assertIn("unknown source reach", development.scope(graph, full).errors)






    def test_lock_versions_sources_metadata_extra_edges_manifests_and_unknown_owner_refuse(self):
        good = self.restored_lock()
        for bad in (good.replace('version = 4', 'version = 3'), good.replace('exact-checksum', 'forged'),
                    good.replace('version="1.0.0"', 'version="1.1.0"'), good.replace('registry+', 'git+'),
                    good.replace('"other", "trust-resource-provenance"', '"trust-resource-provenance"'),
                    good + '\n[[package]]\nname="extra"\nversion="1.0.0"\n',
                    good.replace('"other", "trust-resource-provenance"', '"other", "trust-resource-provenance", "extra"'),
                    good.replace('"other", "trust-resource-provenance"', '"other", "trust-resource-provenance", "trust-resource-provenance"'),
                    good.replace('name="trust-certify"', 'name="unknown-owner"'), '[malformed'):
            with self.subTest(bad=bad):
                graph, selected = self.commit({development.TARGO_LOCK: bad})
                self.assertFalse(development.targo_lock_restoration(graph, self.base))
                self.assertTrue(development.scope(graph, selected).errors)
        manifest = "crates/trust-certify/Cargo.toml"
        graph, selected = self.commit({development.TARGO_LOCK: good, manifest: self.files[manifest] + "# changed\n"})
        self.assertTrue(development.scope(graph, selected).errors)
        graph, selected = self.commit({development.TARGO_LOCK: good})
        for path in (development.TARGO_LOCK, manifest, "crates/trust-resource-provenance/Cargo.toml"):
            for mode in (None, "120000", "160000"):
                broken = copy.deepcopy(graph)
                if mode is None:
                    del broken.index.entries[path]
                else:
                    broken.index.entries[path] = (mode, "0" * 40)
                self.assertTrue(development.scope(broken, selected).errors)
        graph.opaque["crates/trust-certify"] = "unknown manifest"
        self.assertTrue(development.scope(graph, selected).errors)

    def sha2_lock_base(self):
        workspace = development.LOCAL_GIT_WORKSPACE + "/Cargo.toml"
        core = development.LOCAL_GIT_CORE + "/Cargo.toml"
        self.files[workspace] += '[workspace.package]\nversion="0.1.0"\n[workspace.dependencies]\nsha2="0.11.0"\n'
        self.files[core] = self.files[core].replace('version="0.1.0"', 'version.workspace=true')
        self.files[core] += '[dependencies]\nsha2.workspace=true\n'
        self.files[development.TARGO_LOCK] = self.restored_lock() + (
            '\n[[package]]\nname="targo-core"\nversion="0.1.0"\ndependencies=["other", "sha2 0.11.0"]\n'
            '[[package]]\nname="sha2"\nversion="0.11.1"\n'
            'source="registry+https://github.com/rust-lang/crates.io-index"\nchecksum="' + "f" * 64 + '"\n')
        self.commit()
        self.base = fixtures.git_in(self.root, "rev-parse", "HEAD")
        return self.files[development.TARGO_LOCK].replace('"sha2 0.11.0"', '"sha2 0.11.1"')

    def test_exact_dangling_sha2_edge_uses_existing_identity_without_changing_diagnostic_semantics(self):
        good = self.sha2_lock_base()
        graph, selection = self.commit({development.TARGO_LOCK: good})
        self.assertTrue(development.targo_sha2_lock_restoration(graph, self.base))
        self.assertFalse(development.targo_lock_restoration(graph, self.base))
        full = ls.select(graph, self.base, selection.changed)
        self.assertTrue(full.everything)
        self.assertFalse(development.scope(graph, full).errors)
        self.assertTrue(development.scope(graph, full).targo_native_core)
        self.assertTrue(development.scope(graph, full).targo_cleanup)

    def test_sha2_edge_owner_refuses_other_edges_identities_metadata_and_declaring_manifest_changes(self):
        good = self.sha2_lock_base()
        for bad in (good.replace('version = 4', 'version = 3'), good.replace("f" * 64, "e" * 64),
                    good.replace('version="0.11.1"', 'version="0.11.2"'),
                    good.replace('registry+https://github.com/rust-lang/crates.io-index', 'git+https://example.invalid/sha2'),
                    good.replace('"other", "sha2 0.11.1"', '"sha2 0.11.1"'),
                    good.replace('"other", "sha2 0.11.1"', '"other", "sha2 0.11.1", "extra"'),
                    good.replace('"other", "sha2 0.11.1"', '"other", "sha2 0.11.1", "sha2 0.11.1"'),
                    good.replace('name="targo-core"', 'name="foreign-core"'), '[malformed'):
            with self.subTest(bad=bad):
                graph, selected = self.commit({development.TARGO_LOCK: bad})
                self.assertFalse(development.targo_sha2_lock_restoration(graph, self.base))
                self.assertTrue(development.scope(graph, selected).errors)
        for manifest in (development.LOCAL_GIT_WORKSPACE + "/Cargo.toml", development.LOCAL_GIT_CORE + "/Cargo.toml"):
            graph, selected = self.commit({development.TARGO_LOCK: good, manifest: self.files[manifest] + "# changed\n"})
            self.assertFalse(development.targo_sha2_lock_restoration(graph, self.base))
        graph, selected = self.commit({development.TARGO_LOCK: good})
        for path in (development.TARGO_LOCK, development.LOCAL_GIT_WORKSPACE + "/Cargo.toml",
                     development.LOCAL_GIT_CORE + "/Cargo.toml"):
            for mode in (None, "120000", "160000"):
                broken = copy.deepcopy(graph)
                if mode is None:
                    del broken.index.entries[path]
                else:
                    broken.index.entries[path] = (mode, "0" * 40)
                self.assertFalse(development.targo_sha2_lock_restoration(broken, self.base))
        graph.opaque[development.LOCAL_GIT_CORE] = "unknown manifest"
        self.assertFalse(development.targo_sha2_lock_restoration(graph, self.base))

    def test_sha2_edge_owner_requires_a_dangling_reference_and_unique_declared_target(self):
        good = self.sha2_lock_base()
        original = self.files[development.TARGO_LOCK]
        for addition in ('\n[[package]]\nname="sha2"\nversion="0.11.0"\n',
                         '\n[[package]]\nname="sha2"\nversion="0.11.1"\nsource="git+https://example.invalid/sha2"\n',
                         '\n[[package]]\nname="targo-core"\nversion="0.2.0"\n'):
            with self.subTest(addition=addition):
                self.commit({development.TARGO_LOCK: original + addition})
                base = fixtures.git_in(self.root, "rev-parse", "HEAD")
                graph, selected = self.commit({development.TARGO_LOCK: good + addition})
                self.assertFalse(development.targo_sha2_lock_restoration(graph, base))
        workspace = development.LOCAL_GIT_WORKSPACE + "/Cargo.toml"
        core = development.LOCAL_GIT_CORE + "/Cargo.toml"
        for manifest, content in (
                (workspace, self.files[workspace].replace('sha2="0.11.0"', 'sha2="0.11.1"')),
                (core, self.files[core].replace('sha2.workspace=true', 'sha2="0.11.0"'))):
            with self.subTest(manifest=manifest):
                self.commit({development.TARGO_LOCK: original, manifest: content})
                base = fixtures.git_in(self.root, "rev-parse", "HEAD")
                graph, selected = self.commit({development.TARGO_LOCK: good, manifest: content})
                self.assertFalse(development.targo_sha2_lock_restoration(graph, base))

    def build_input_base(self, *, dangling_sha2=False):
        self.sha2_lock_base()
        manifest = development.TARGO_MANIFEST
        self.files[manifest] += ('build-rs={version="0.3.6",path="crates/build-rs"}\n'
                                 '[build-dependencies]\n')
        self.files[development.TARGO_BUILD_RS + "/Cargo.toml"] = (
            '[package]\nname="build-rs"\nversion="0.3.7"\n')
        self.files[development.TARGO_BUILD_RS + "/src/input.rs"] = "// unchanged local provider DATA\n"
        self.files[development.TARGO_BUILD_SCRIPT] = (
            '// unchanged prefix\nfn trust_std() {\n'
            '    println!("cargo::rerun-if-env-changed=RUSTC");\n'
            + development.TARGO_RUSTC_INPUT_BEFORE.decode() +
            '    let output = std::process::Command::new(compiler)\n'
            '        .arg("-vV").output().expect("read compiler identity");\n'
            '    assert!(output.status.success(), "compiler identity probe failed");\n'
            '    if output.stdout.starts_with(b"trust:") { println!("cargo::rustc-cfg=trust_std"); }\n'
            '}\nfn untouched() {}\n')
        self.files[development.TARGO_LOCK] += (
            '\n[[package]]\nname="targo"\nversion="0.1.0"\ndependencies=["other"]\n'
            '[[package]]\nname="build-rs"\nversion="0.3.7"\n')
        if not dangling_sha2:
            self.files[development.TARGO_LOCK] = self.files[development.TARGO_LOCK].replace(
                '"sha2 0.11.0"', '"sha2 0.11.1"')
        self.commit()
        self.base = fixtures.git_in(self.root, "rev-parse", "HEAD")
        return {
            manifest: self.files[manifest].replace('[build-dependencies]\n',
                                                   '[build-dependencies]\nbuild-rs.workspace = true\n'),
            development.TARGO_BUILD_SCRIPT: self.files[development.TARGO_BUILD_SCRIPT].replace(
                development.TARGO_RUSTC_INPUT_BEFORE.decode(), development.TARGO_RUSTC_INPUT_AFTER.decode()),
            development.TARGO_LOCK: self.files[development.TARGO_LOCK].replace(
                'name="targo"\nversion="0.1.0"\ndependencies=["other"]',
                'name="targo"\nversion="0.1.0"\ndependencies=["build-rs", "other"]').replace(
                    '"sha2 0.11.0"', '"sha2 0.11.1"'),
        }

    def test_exact_build_input_bundle_keeps_core25_cleanup4_and_diagnostic_scope(self):
        changes = self.build_input_base()
        graph, selected = self.commit(changes)
        self.assertTrue(development.targo_build_rs_repair(graph,self.base))
        self.assertTrue(development.has_declared_source_ownership(graph.index,selected.changed))
        full = ls.select(graph,self.base,selected.changed)
        self.assertTrue(full.everything or full.cargo_impacts)
        scoped = development.scope(graph,full)
        self.assertFalse(scoped.errors)
        self.assertTrue(scoped.targo_native_core and scoped.targo_cleanup)
        self.assertEqual({leg.id for leg in self.legs(graph,full)},
            {development.TARGO_NATIVE_CORE_LEG,development.TARGO_CLEANUP_LEG})
        self.assertEqual(len(set(development.TARGO_NATIVE_CORE_CASES)),25)
        self.assertEqual(len(set(development.TARGO_CLEANUP_CASES)),4)

    def test_build_input_bundle_composes_only_the_exact_existing_sha2_edge_repair(self):
        changes = self.build_input_base(dangling_sha2=True)
        graph, selected = self.commit(changes)
        self.assertTrue(development.targo_build_rs_repair(graph,self.base))
        self.assertFalse(development.targo_sha2_lock_restoration(graph,self.base))
        self.assertFalse(development.scope(graph,ls.select(graph,self.base,selected.changed)).errors)

    def test_build_input_bundle_refuses_partial_other_body_manifest_identity_and_edge_changes(self):
        changes = self.build_input_base(dangling_sha2=True)
        script, manifest, lock = development.TARGO_BUILD_SCRIPT,development.TARGO_MANIFEST,development.TARGO_LOCK
        bad = [dict(changes,**{script:changes[script]+'// extra body input\n'}),
               dict(changes,**{script:changes[script].replace('-vV','-V')}),
               dict(changes,**{script:changes[script].replace('build_rs::input::rustc()',
                   'std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into())')}),
               dict(changes,**{manifest:changes[manifest]+'# unrelated manifest delta\n'}),
               dict(changes,**{manifest:changes[manifest].replace('version="0.3.6"','version="0.3.7"')}),
               dict(changes,**{lock:changes[lock].replace('f'*64,'e'*64)}),
               dict(changes,**{lock:changes[lock].replace('version="0.3.7"','version="0.3.8"')}),
               dict(changes,**{lock:changes[lock].replace('["build-rs", "other"]','["build-rs", "build-rs", "other"]')}),
               dict(changes,**{lock:changes[lock].replace('["other", "sha2 0.11.1"]','["sha2 0.11.1"]')}),
               dict(changes,**{development.TARGO_BUILD_RS+'/src/input.rs':'// changed provider\n'}),
               dict(changes,**{development.TARGO_BUILD_RS+'/Cargo.toml':'[package]\nname="build-rs"\nversion="0.3.8"\n'})]
        bad += [{p:value for p,value in changes.items() if p!=omitted} for omitted in changes]
        for case in bad:
            with self.subTest(case=case):
                graph, selected = self.commit(case)
                self.assertFalse(development.targo_build_rs_repair(graph,self.base))
                self.assertTrue(development.scope(graph,selected).errors)

    def test_build_input_bundle_refuses_ambiguous_existing_local_identity_and_unsafe_inputs(self):
        changes = self.build_input_base()
        graph, selected = self.commit(changes)
        for path in (development.TARGO_MANIFEST,development.TARGO_BUILD_SCRIPT,development.TARGO_LOCK,
                     development.TARGO_BUILD_RS+'/Cargo.toml',development.TARGO_BUILD_RS+'/src/input.rs'):
            for mode in (None,'120000','160000'):
                broken = copy.deepcopy(graph)
                if mode is None:
                    del broken.index.entries[path]
                else:
                    broken.index.entries[path] = (mode,'0'*40)
                self.assertFalse(development.targo_build_rs_repair(broken,self.base))
        addition = '\n[[package]]\nname="build-rs"\nversion="0.3.7"\nsource="registry+https://example.invalid/index"\n'
        self.commit({development.TARGO_LOCK:self.files[development.TARGO_LOCK]+addition})
        base = fixtures.git_in(self.root,'rev-parse','HEAD')
        graph, _selected = self.commit(dict(changes,**{development.TARGO_LOCK:changes[development.TARGO_LOCK]+addition}))
        self.assertFalse(development.targo_build_rs_repair(graph,base))

    def test_vendor_trigger_requires_exact_real_regular_move_and_no_other_policy_delta(self):
        old = development.LOCAL_GIT_CORE + "/src/ops/cargo_vendor.rs"
        new = development.TARGO_NATIVE_MODULE_MOVES[old]
        trigger = self.files[development.TARGO_TRIAGEBOT].replace("src/ops/cargo_vendor.rs",
                                                                 "crates/targo-core/src/ops/cargo_vendor/mod.rs")
        changes = {development.TARGO_TRIAGEBOT: trigger, new: self.files[old]}
        graph, selected = self.commit(changes, [old])
        self.assertTrue(development.targo_vendor_trigger_move(graph, self.base))
        self.assertFalse(development.scope(graph, selected).errors)
        for patch, remove in (({development.TARGO_TRIAGEBOT: trigger}, []),
                              ({**changes, development.TARGO_TRIAGEBOT: trigger + "# other policy change\n"}, [old])):
            graph, selected = self.commit(patch, remove)
            self.assertFalse(development.targo_vendor_trigger_move(graph, self.base))
            self.assertTrue(development.scope(graph, selected).errors)

    def test_exact_required_native_populations_refuse_empty_partial_ignored_and_extra_summaries(self):
        for expected in (4, 25):
            good = f"test result: ok. {expected} passed; 0 failed; 0 ignored;"
            self.assertEqual(gate.development_test_result(good, 0, expected_count=expected)[0], 0)
            for text, code in (("", 0), (good, 1), (good.replace("0 ignored", "1 ignored"), 0),
                               (good.replace(f"{expected} passed", f"{expected - 1} passed"), 0),
                               (good.replace(f"{expected} passed", f"{expected + 1} passed"), 0),
                               (good.replace("0 failed", "1 failed"), 0), (good + "\n" + good, 0)):
                self.assertNotEqual(gate.development_test_result(text, code, expected_count=expected)[0], 0)

    def test_cleanup_runtime_refuses_any_ambient_binary_override(self):
        leg = fixtures.leg(id=development.TARGO_CLEANUP_LEG, command=["targo", "--unverified", "test"])
        for value in ("", "/prior/targo"):
            with mock.patch.object(gate, "leg_environment", return_value={"TARGO_CLEAN_TEST_BINARY": value}), \
                    mock.patch.object(gate.landing_targo, "capability_gap", side_effect=AssertionError("must refuse")):
                self.assertIn("unset TARGO_CLEAN_TEST_BINARY", gate.targo_unready(leg))

    def test_native_target_selection_empty_population_opaque_include_and_unreadable_config_refuse(self):
        with mock.patch.object(gate, "REPO_ROOT", self.root):
            for env in ({"CARGO_BUILD_TARGET": ""}, {"CARGO_BUILD_TARGET": "aarch64-apple-darwin"},
                        {"TARGO_BUILD_TARGET": "other"}, {"CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER": "/usr/bin/env"}):
                self.assertIsNotNone(gate.development_native_target_problem(env))
            directory = self.root / ".cargo"
            directory.mkdir()
            config = directory / "config.toml"
            for text in ('[build]\ntarget=[]\n', '[build]\ntarget="aarch64-apple-darwin"\n',
                         'include="opaque.toml"\n', '[broken', '[target."cfg(unix)"]\nrunner=["/usr/bin/env"]\n'):
                config.write_text(text)
                self.assertIsNotNone(gate.development_native_target_problem({}))
            config.write_text('[build]\njobs=1\n')
            self.assertIsNone(gate.development_native_target_problem({}))

    def test_direct_cleanup_keeps_actual_loader_env_and_fresh_external_scratch(self):
        # A real child stands in for Cargo only to assemble its test process
        # environment and TMPDIR config, then directly executes the built test.
        probe = ("import json,os,subprocess,sys\n"
                 "setting=next(x for x in sys.argv if x.startswith('env.TMPDIR.value='))\n"
                 "os.environ['TMPDIR']=json.loads(setting.split('=',1)[1])\n"
                 "assert 'env.TMPDIR.force=true' in sys.argv and 'env.TMPDIR.relative=false' in sys.argv\n"
                 "os.environ['DYLD_LIBRARY_PATH']='/exact/original/lib';os.environ['DYLD_FALLBACK_LIBRARY_PATH']='/exact/original/fallback'\n"
                 "subprocess.run([sys.executable,'-c',"
                 "\"import os,tempfile;assert os.environ['DYLD_LIBRARY_PATH']=='/exact/original/lib';assert os.environ['DYLD_FALLBACK_LIBRARY_PATH']=='/exact/original/fallback';print('NATIVE-SCRATCH='+tempfile.gettempdir());print('NATIVE-CWD='+os.getcwd())\"],check=True)\n")
        command = [sys.executable, "-c", probe, "--"]
        leg = fixtures.leg(id=development.TARGO_CLEANUP_LEG, command=command)
        output = io.StringIO()
        with mock.patch.object(gate, "REPO_ROOT", self.root), \
                mock.patch.object(gate, "leg_environment", return_value={"PATH": os.defpath}), \
                mock.patch.object(gate, "host_triple", return_value="aarch64-apple-darwin"), \
                contextlib.redirect_stdout(io.StringIO()):
            code = gate._run_one(leg, command, output, {}, (1, 2), self.root)
        self.assertEqual(code, 0, output.getvalue())
        log = output.getvalue()
        world = Path(next(line.split(": ", 1)[1] for line in log.splitlines()
                          if line.startswith("Native cleanup retained world root: ")))
        self.addCleanup(shutil.rmtree, world)
        self.assertFalse(world.is_relative_to(self.root.resolve()))
        self.assertIn("NATIVE-SCRATCH=" + str(world), log)
        self.assertIn("NATIVE-CWD=" + str(self.root.resolve()), log)
        self.assertNotIn('.runner=', log)
        self.assertNotIn("--target", log)
        again = io.StringIO()
        gate.development_native_command(leg, command, again)
        second = Path(again.getvalue().strip().split(": ", 1)[1])
        self.addCleanup(shutil.rmtree, second)
        self.assertNotEqual(world, second)


class TargoCheckoutLayoutTests(unittest.TestCase):
    """Source-predicate controls only; no handler or adapter behavior executes."""
    commit = TargoNativeDevelopmentTests.commit
    legs = TargoNativeDevelopmentTests.legs
    sha2_lock_base = TargoNativeDevelopmentTests.sha2_lock_base
    restored_lock = TargoNativeDevelopmentTests.restored_lock

    def setUp(self):
        TargoNativeDevelopmentTests.setUp(self)
        self.old = development.TARGO_CHECKOUT_LAYOUT_OLD
        self.new = development.TARGO_CHECKOUT_LAYOUT_NEW
        self.adapter = development.TARGO_CHECKOUT_LAYOUT_ADAPTER
        self.files[self.old] = 'const SOURCE: &[u8] = include_bytes!("checkout_inputs.rs");\n'
        self.files[self.adapter] = f'NATIVE_SOURCE = "{self.old}"\n# exact locator fixture\n'
        graph, _ = self.commit()
        self.base = graph.index.rev
        self.moved = self.files[self.old].replace('include_bytes!("checkout_inputs.rs")',
                                                 'include_bytes!("mod.rs")')
        self.locator = self.files[self.adapter].replace(self.old, self.new)

    def layout(self):
        return self.commit({self.new:self.moved, self.adapter:self.locator}, [self.old])

    def test_joint_layout_build_input_and_exact_sha2_edge_preserve_both_owners(self):
        changes = TargoNativeDevelopmentTests.build_input_base(self,dangling_sha2=True)
        changes.update({self.new:self.moved,self.adapter:self.locator})
        graph, selected = self.commit(changes,[self.old])
        self.assertTrue(development.targo_checkout_layout_move(graph,self.base))
        self.assertTrue(development.targo_build_rs_repair(graph,self.base))
        full = ls.select(graph,self.base,selected.changed)
        scoped = development.scope(graph,full)
        self.assertFalse(scoped.errors)
        self.assertTrue(scoped.targo_native_core and scoped.targo_cleanup)
        self.assertEqual(scoped.tests,[development.TARGO_CHECKOUT_LAYOUT_TEST])
        self.assertEqual({leg.id for leg in self.legs(graph,full)},
            {development.TARGO_NATIVE_CORE_LEG,development.TARGO_CLEANUP_LEG,"development-validation-tests"})

    def test_joint_owner_refuses_extra_manifest_body_edge_and_partial_build_repair(self):
        changes = TargoNativeDevelopmentTests.build_input_base(self,dangling_sha2=True)
        changes.update({self.new:self.moved,self.adapter:self.locator})
        bad = [dict(changes,**{development.TARGO_MANIFEST:changes[development.TARGO_MANIFEST]+'# extra\n'}),
               dict(changes,**{self.new:self.moved+'// body delta\n'}),
               dict(changes,**{development.TARGO_LOCK:changes[development.TARGO_LOCK].replace(
                   '["build-rs", "other"]','["build-rs", "other", "extra"]')}),
               {p:v for p,v in changes.items() if p!=development.TARGO_BUILD_SCRIPT},
               dict(changes,**{development.LOCAL_GIT_CORE+'/Cargo.toml':
                   self.files[development.LOCAL_GIT_CORE+'/Cargo.toml']+'# core delta\n'})]
        for case in bad:
            with self.subTest(case=case):
                graph, selected = self.commit(case,[self.old])
                self.assertTrue(development.scope(graph,ls.select(graph,self.base,selected.changed)).errors)

    def test_exact_layout_has_source_controls_and_existing_core_regressions_only(self):
        graph, selected = self.layout()
        self.assertTrue(development.targo_checkout_layout_move(graph, self.base))
        self.assertFalse(development.targo_checkout_layout_move(graph, graph.index.rev))
        self.assertTrue(development.may_have_scope(selected.changed))
        self.assertTrue(development.has_declared_source_ownership(graph.index, selected.changed))
        scoped = development.scope(graph, selected)
        self.assertFalse(scoped.errors)
        self.assertTrue(scoped.targo_native_core)
        self.assertFalse(scoped.targo_cleanup)
        self.assertEqual(scoped.tests, [development.TARGO_CHECKOUT_LAYOUT_TEST])
        legs = self.legs(graph, selected)
        self.assertEqual({leg.id for leg in legs},
                         {development.TARGO_NATIVE_CORE_LEG, "development-validation-tests"})
        core = next(leg for leg in legs if leg.id == development.TARGO_NATIVE_CORE_LEG)
        self.assertEqual(core.command[core.command.index("--") + 1:],
                         ["--exact", "--test-threads=1", *development.TARGO_NATIVE_CORE_CASES])
        self.assertEqual(len(development.TARGO_NATIVE_CORE_CASES), 25)
        self.assertEqual(len(development.TARGO_CLEANUP_CASES), 4)
        self.assertNotIn("scripts.tests.native_checkout_test", str([leg.command for leg in legs]))
        kind, why = ls.classify(graph, self.adapter)
        diagnostic = ls.Selection(self.base, graph.index.rev, selected.changed,
                                  [f"{self.adapter}: {why}"] if kind == "everything" else [])
        self.assertFalse(development.scope(graph, diagnostic).errors)
        unresolved = ls.Selection(self.base, graph.index.rev, selected.changed,
                                   ["unresolved diagnostic graph fact"])
        self.assertIn("unresolved diagnostic graph fact", development.scope(graph, unresolved).errors)

    def test_any_body_include_or_extra_locator_edit_refuses(self):
        for body, locator in (
                (self.moved + "// unrelated body change\n", self.locator),
                (self.files[self.old], self.locator),
                (self.moved.replace('"mod.rs"', '"other.rs"'), self.locator),
                (self.moved, self.locator + "# unrelated Python edit\n"),
                (self.moved, self.files[self.adapter]),
                (self.moved, self.locator.replace("/mod.rs", "/wrong.rs"))):
            with self.subTest(body=body, locator=locator):
                graph, selected = self.commit({self.new:body, self.adapter:locator}, [self.old])
                self.assertFalse(development.targo_checkout_layout_move(graph, self.base))
                self.assertTrue(development.scope(graph, selected).errors)
        graph, selected = self.commit({self.new:self.moved, self.adapter:self.locator})
        self.assertTrue(development.scope(graph, selected).errors, "a copy is not a move")

    def test_missing_nonregular_aliased_or_mode_changed_head_inputs_refuse(self):
        graph, selected = self.layout()
        for path in (self.new, self.adapter):
            for mode in (None, "120000", "160000", "100755"):
                with self.subTest(path=path, mode=mode):
                    broken = copy.deepcopy(graph)
                    if mode is None:
                        del broken.index.entries[path]
                    else:
                        broken.index.entries[path] = (mode, graph.index.entries[path][1])
                    self.assertTrue(development.scope(broken, selected).errors)
        for path in (self.old.replace("checkout_inputs", "Checkout_Inputs"),
                     self.new.replace("checkout_inputs", "Checkout_Inputs"),
                     self.adapter.replace("native_checkout", "Native_Checkout"),
                     development.LOCAL_GIT_CORE + "/src/ops"):
            with self.subTest(path=path):
                broken = copy.deepcopy(graph)
                broken.index.entries[path] = ("120000" if path.endswith("/ops") else "100644", "0" * 40)
                broken.__dict__.pop("_index_spellings", None)
                self.assertTrue(development.scope(broken, selected).errors)

    def test_missing_unsafe_or_preexisting_destination_in_base_refuses(self):
        graph, selected = self.layout()
        before = ls.TreeIndex.load(str(self.root), self.base)
        for path in (self.old, self.adapter):
            for mode in (None, "120000", "160000", "100755"):
                with self.subTest(path=path, mode=mode):
                    broken = copy.deepcopy(before)
                    if mode is None:
                        del broken.entries[path]
                    else:
                        broken.entries[path] = (mode, before.entries[path][1])
                    with mock.patch.object(ls.TreeIndex, "load", return_value=broken):
                        self.assertFalse(development.targo_checkout_layout_move(graph, self.base))
        for path in (self.old.replace("checkout_inputs", "Checkout_Inputs"),
                     self.new, self.new.replace("checkout_inputs", "Checkout_Inputs")):
            broken = copy.deepcopy(before)
            broken.entries[path] = ("100644", "0" * 40)
            with mock.patch.object(ls.TreeIndex, "load", return_value=broken):
                self.assertFalse(development.targo_checkout_layout_move(graph, self.base))

    def test_foreign_opaque_or_changed_manifest_owner_refuses(self):
        graph, selected = self.layout()
        for defect in ("opaque", "foreign", "manifest"):
            with self.subTest(defect=defect):
                broken = copy.deepcopy(graph)
                owner = development.LOCAL_GIT_CORE
                if defect == "opaque":
                    broken.opaque[owner] = "unknown manifest"
                elif defect == "foreign":
                    broken.packages[owner + "/src"] = ls.Package(owner + "/src", "foreign")
                else:
                    broken.index.entries[owner + "/Cargo.toml"] = ("100644", "0" * 40)
                self.assertTrue(development.scope(broken, selected).errors)

    def test_outgoing_scope_retains_exact_layout_and_unknown_input_refusal(self):
        graph, selected = self.layout()
        landing = gate.LandingRange(self.base, graph.index.rev, "local", True, tuple(selected.changed), "")
        empty = ls.Selection(self.base, graph.index.rev, [], [])
        self.assertEqual({leg.id for leg in self.legs(graph, empty, landing)},
                         {development.TARGO_NATIVE_CORE_LEG, "development-validation-tests"})
        unknown = development.LOCAL_GIT_CORE + "/src/ops/unowned.rs"
        landing = gate.LandingRange(self.base, graph.index.rev, "local", True,
                                    (*selected.changed, unknown), "")
        with self.assertRaisesRegex(RuntimeError, "no declared development component/test owner"):
            self.legs(graph, selected, landing)


class DevelopmentRetentionOwnerTests(unittest.TestCase):
    program_name = "retain_development_emission"

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="development-retention-owner-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.paths = (f"scripts/{self.program_name}.py",
                      f"scripts/tests/{self.program_name}_test.py")
        self.neighbour = f"scripts/{self.program_name}_extra.py"
        self.files = {
            "Cargo.toml": '[workspace]\nmembers=["crates/fixture"]\ndefault-members=["crates/fixture"]\n',
            "crates/fixture/Cargo.toml": '[package]\nname="fixture"\nversion="0.1.0"\n',
            "crates/fixture/src/lib.rs": "// graph input only; never compiled\n",
        }
        self.files.update({path:"# original source fixture\n" for path in (*self.paths, self.neighbour)})
        self.base = fixtures.make_repo(self.root, self.files, {})

    def changed(self, paths):
        for path, content in self.files.items():
            (self.root/path).write_text(content + ("# changed fixture\n" if path in paths else ""))
        fixtures.git_in(self.root, "add", "-A")
        fixtures.git_in(self.root, "commit", "-qm", "retention metadata owner control", "--allow-empty")
        graph = ls.build_manifest_graph(ls.TreeIndex.load(str(self.root), "HEAD"))
        changed = ls.changed_paths(str(self.root), self.base, graph.index.rev)
        self.assertEqual(set(changed), set(paths))
        return graph, ls.select(graph, self.base, changed)

    def test_exact_registered_retention_inputs_select_one_fresh_existing_suite(self):
        target = f"scripts.tests.{self.program_name}_test"
        for paths in ((self.paths[0],), (self.paths[1],), self.paths):
            with self.subTest(paths=paths):
                graph, selected = self.changed(paths)
                for path in paths:
                    self.assertEqual(ls.validation_test_modules([path]), [target])
                    self.assertEqual(ls.classify(graph, path)[0], "everything")
                scoped = development.scope(graph, selected)
                self.assertFalse(scoped.errors)
                self.assertEqual(scoped.tests, [target])
                self.assertTrue(development.has_declared_source_ownership(graph.index, paths))
                leg, = gate.development_legs(graph, selected, [], 1)
                self.assertEqual(leg.id, "development-validation-tests")
                self.assertEqual(leg.command, [sys.executable, "scripts/land_gate.py", "validation-tests", target])
                self.assertTrue(leg.force_run)
                self.assertFalse(leg.cache_members)
                selected.everything.append("unknown diagnostic graph fact")
                self.assertEqual(development.scope(graph, selected).errors, ["unknown diagnostic graph fact"])

    def test_unknown_retention_neighbour_remains_unowned_alone_or_in_union(self):
        for paths in ((self.neighbour,), (*self.paths, self.neighbour)):
            with self.subTest(paths=paths):
                graph, selected = self.changed(paths)
                self.assertNotIn(self.neighbour, development.PROGRAM_TESTS)
                self.assertFalse(development.may_have_scope(paths))
                self.assertFalse(development.has_declared_source_ownership(graph.index, paths))
                self.assertTrue(any(self.neighbour in error for error in development.scope(graph, selected).errors))
                with self.assertRaisesRegex(RuntimeError, "development scope refused"):
                    gate.development_legs(graph, selected, [], 1)


class DevelopmentVf5ProposalOwnerTests(DevelopmentRetentionOwnerTests):
    program_name = "produce_vf5_proposal"


class DevelopmentTrainOwnerTests(DevelopmentRetentionOwnerTests):
    program_name = "daily_toolchain_stage"

    def test_exact_registered_retention_inputs_select_one_fresh_existing_suite(self):
        # The producer has consumers beyond its own suite. Preserve the full
        # existing row-table selection, including for a test-only edit.
        program_tests = [
            "scripts.tests.check_bootstrap_script_tests_test", "scripts.tests.daily_dependency_git_selection_test",
            "scripts.tests.daily_toolchain_stage_test",
            "scripts.tests.python_floor_test", "scripts.tests.sdk_diagnostic_test",
        ]
        fixture_tests = program_tests[:3]
        for paths, expected in (((self.paths[0],), program_tests),
                                ((self.paths[1],), fixture_tests),
                                (self.paths, program_tests)):
            with self.subTest(paths=paths):
                graph, selected = self.changed(paths)
                self.assertEqual(ls.validation_test_modules(paths), expected)
                for path in paths:
                    self.assertEqual(ls.classify(graph, path)[0], "everything")
                scoped = development.scope(graph, selected)
                self.assertEqual(scoped.errors, [])
                self.assertEqual(scoped.tests, expected)
                self.assertTrue(development.has_declared_source_ownership(graph.index, paths))
                leg, = gate.development_legs(graph, selected, [], 1)
                self.assertEqual(leg.command, [sys.executable, "scripts/land_gate.py", "validation-tests", *expected])
                self.assertTrue(leg.force_run)
                self.assertFalse(leg.cache_members)
                selected.everything.append("unknown diagnostic graph fact")
                self.assertEqual(development.scope(graph, selected).errors, ["unknown diagnostic graph fact"])

    def test_actual_train_discovery_uses_its_declared_tests_without_a_full_rust_scan(self):
        self.changed(self.paths)
        with mock.patch.object(gate, "REPO_ROOT", self.root), \
             mock.patch.object(ls, "build_graph", side_effect=AssertionError("full Rust scan forbidden")):
            graph, selected, _ = gate.compute_discovery(
                self.base, "HEAD", False, None, gate.DiscoveryProfile.DEVELOPMENT)
        self.assertIsInstance(selected, gate.DeclaredDevelopmentSelection)
        self.assertEqual(development.scope(graph, selected).errors, [])
        self.assertEqual(development.scope(graph, selected).tests, ls.validation_test_modules(self.paths))


class DevelopmentScopeTests(unittest.TestCase):
    def test_real_compiler_selector_shell_caller(self):
        script = Path(__file__).with_name("compiler_check_selector_consult_test.sh")
        # The shell lane uses python3. Exercise it with this actual test
        # interpreter, even when the host's generic name is an uninstalled
        # platform shim rather than the selected managed Python.
        with tempfile.TemporaryDirectory(prefix="land-selector-python-") as directory:
            (Path(directory) / "python3").symlink_to(Path(sys.executable).resolve(strict=True))
            environment = dict(os.environ)
            environment["PATH"] = directory + os.pathsep + environment.get("PATH", os.defpath)
            result = subprocess.run(["bash", str(script)], capture_output=True, text=True, env=environment)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("all passed", result.stdout)

    def graph(self):
        graph = fixtures.Fixture.graph()
        for owner, name in (("src/jobserver_utils", "jobserver_utils"),
                            ("src/tools/compiletest", "compiletest"),
                            ("src/tools/run-make-support", "run_make_support"),
                            ("crates/trust-build-cpu", "trust-build-cpu"),
                            (development.CONTROLLER_COMPONENT, "trust-resource-controller"),
                            (development.PROVENANCE_COMPONENT, "trust-resource-provenance"),
                            (development.BUILD_TREE_COMPONENT, "trust-build-tree"),
                            (development.BOOTSTRAP_COMPONENT, "bootstrap")):
            graph.packages[owner] = ls.Package(owner, name)
        graph.packages["crates/trust-build-cpu"].deps.add("src/jobserver_utils")
        graph.packages[development.CONTROLLER_COMPONENT].deps.add("src/jobserver_utils")
        graph.packages[development.CONTROLLER_COMPONENT].deps.add(development.PROVENANCE_COMPONENT)
        graph.packages[development.BOOTSTRAP_COMPONENT].deps.add("src/jobserver_utils")
        graph.packages[development.BUILD_TREE_COMPONENT].deps.update({"crates/trust-build-cpu", "src/jobserver_utils"})
        graph.packages["src/tools/compiletest"].deps.add("src/jobserver_utils")
        graph.packages["src/tools/run-make-support"].deps.add("src/jobserver_utils")
        for recipe in development.INTEGRATION_RECIPES:
            graph.index.entries[recipe + "/rmake.rs"] = ("100644", "0" * 40)
        # Fixture.graph cached its original tracked spellings. This fixture
        # extends that index; derive spellings from the completed index.
        graph._index_spellings = None
        return graph

    def selection(self, graph, paths, everything=()):
        return ls.Selection("base", graph.index.rev, paths, list(everything))

    def test_controller_manifest_has_complete_owner_but_unknown_manifest_stays_refused(self):
        graph = self.graph()
        path = development.CONTROLLER_COMPONENT + "/Cargo.toml"
        kind, why = ls.classify(graph, path)
        self.assertEqual(kind, "everything")
        selected = self.selection(graph, [path], [f"{path}: {why}"])
        selected.cargo_impacts[path] = []
        scope = development.scope(graph, selected)
        self.assertFalse(scope.errors)
        self.assertEqual(scope.packages, [development.CONTROLLER_COMPONENT])
        unknown = "crates/unknown/Cargo.toml"
        kind, why = ls.classify(graph, unknown)
        selected = self.selection(graph, [unknown], [f"{unknown}: {why}"])
        selected.cargo_impacts[unknown] = []
        self.assertTrue(development.scope(graph, selected).errors)

    def test_controller_owner_runs_complete_standalone_feature_boundaries(self):
        graph = self.graph()
        owner = development.CONTROLLER_COMPONENT
        graph.packages[owner] = ls.Package(owner, "trust-resource-controller")
        selection = self.selection(graph, [owner + "/src/solver_bootstrap/receive.rs"])
        scope = development.scope(graph, selection)
        self.assertFalse(scope.errors)
        self.assertEqual(scope.packages, [owner])
        legs = gate.development_legs(graph, selection,
                                     [fixtures.leg(id="compiler-check"), fixtures.leg(id="push-rows")], 2)
        cohorts = [leg for leg in legs if leg.id.startswith("development-package-trust-resource-controller-")]
        required = {"dto": [], "receiver": ["--features", "bootstrap-receiver"],
                    "client": ["--features", "client"], "all-features": ["--all-features"]}
        by_id = {leg.id: leg for leg in cohorts}
        for cohort, features in required.items():
            leg = by_id["development-package-trust-resource-controller-" + cohort]
            self.assertEqual(leg.command, ["targo", "--unverified", "test", "--locked", "--offline",
                                          "--manifest-path", owner + "/Cargo.toml", "--lib", "--no-default-features", *features])
            self.assertTrue(leg.force_run)
            self.assertFalse(leg.diagnostic_only)
        self.assertTrue(next(leg for leg in legs if leg.id == "compiler-check").diagnostic_only)
        push = next(leg for leg in legs if leg.id == "push-rows")
        self.assertTrue(push.force_run)
        self.assertIn("--all-rows", push.command)

    def test_cpu_owner_runs_its_complete_library_without_claiming_compiler_diagnostics(self):
        graph = self.graph()
        selection = self.selection(graph, ["crates/trust-build-cpu/src/native_domain.rs"])
        scope = development.scope(graph, selection)
        self.assertFalse(scope.errors)
        self.assertEqual(scope.packages, ["crates/trust-build-cpu"])
        self.assertFalse(scope.recipes)
        legs = gate.development_legs(graph, selection,
                                     [fixtures.leg(id="compiler-check"), fixtures.leg(id="push-rows")], 2)
        self.assertTrue(next(leg for leg in legs if leg.id == "compiler-check").diagnostic_only)
        self.assertTrue(next(leg for leg in legs if leg.id == "development-package-trust-build-cpu").force_run)
        optional = next(leg for leg in legs if leg.id == "development-package-trust-build-cpu-all-features")
        self.assertIn("--all-features", optional.command)
        self.assertIn("--all-targets", optional.command)
        self.assertTrue(optional.force_run)
        self.assertFalse(optional.diagnostic_only)
        self.assertTrue({"crates/trust-build-cpu", "src/jobserver_utils"} <= set(optional.inputs))
        self.assertTrue(next(leg for leg in legs if leg.id == "push-rows").force_run)

    def test_jobserver_owner_keeps_close_only_and_gnu_client_boundaries(self):
        graph = self.graph()
        owner = "src/jobserver_utils"
        selected = self.selection(graph, [owner + "/src/fork_custody.rs"])
        scope = development.scope(graph, selected)
        self.assertFalse(scope.errors)
        self.assertTrue(set(development.INTEGRATION_RECIPES) <= set(scope.recipes))
        legs = gate.development_legs(graph, selected, [fixtures.leg(id="push-rows")], 2)
        for suffix, minimal in (("", False), ("-no-client", True)):
            leg = next(leg for leg in legs if leg.id == "development-package-jobserver_utils" + suffix)
            self.assertIn("--lib", leg.command)
            self.assertEqual("--no-default-features" in leg.command, minimal)
            self.assertIn(owner, leg.inputs)
            self.assertTrue(leg.force_run)
            self.assertFalse(leg.diagnostic_only)
        self.assertIn("--all-rows", next(leg for leg in legs if leg.id == "push-rows").command)

    def test_build_tree_admission_runs_each_library_boundary_with_original_closure(self):
        graph = self.graph()
        owner = development.BUILD_TREE_COMPONENT
        path = owner + "/src/admission/machine/runtime.rs"
        selected = self.selection(graph, [path])
        scope = development.scope(graph, selected)
        self.assertFalse(scope.errors)
        self.assertIn(owner, scope.packages)
        legs = gate.development_legs(graph, selected,
                                     [fixtures.leg(id="compiler-check"), fixtures.leg(id="push-rows")], 2)
        for cohort, feature in (("default", None), ("machine-admission", "machine-admission"),
                                ("native-exec", "native-exec")):
            leg = next(leg for leg in legs if leg.id == "development-package-trust-build-tree-" + cohort)
            self.assertIn("--lib", leg.command)
            self.assertNotIn("--all-features", leg.command)
            self.assertIn(owner + "/Cargo.toml", leg.command)
            self.assertEqual(leg.command[leg.command.index("--features") + 1] if "--features" in leg.command else None,
                             feature)
            self.assertTrue(leg.force_run)
            self.assertFalse(leg.diagnostic_only)
            self.assertFalse(leg.needs_stage1)
            self.assertTrue({owner, "crates/trust-build-cpu", "src/jobserver_utils"} <= set(leg.inputs))
        self.assertTrue(next(leg for leg in legs if leg.id == "compiler-check").diagnostic_only)
        self.assertIn("--all-rows", next(leg for leg in legs if leg.id == "push-rows").command)

    def test_build_tree_admission_owner_refuses_other_libraries_cli_and_manifests(self):
        owner = development.BUILD_TREE_COMPONENT
        for relative in ("src/main.rs", "src/bin/owner.rs", "src/BIN/owner.rs",
                         "src/lib.rs", "src/trust_repo_lock.rs", "Cargo.toml", "build.rs"):
            path = owner + "/" + relative
            with self.subTest(path=path):
                graph = self.graph()
                selected = self.selection(graph, [path])
                if relative == "Cargo.toml":
                    selected.cargo_impacts[path] = set()
                self.assertTrue(development.scope(graph, selected).errors)
                index = ls.TreeIndex("fixture", "head", "head", {path: ("100644", "1" * 40)})
                self.assertFalse(development.has_declared_source_ownership(index, [path]))

    def test_build_tree_readme_keeps_full_discovery_and_its_library_owner(self):
        owner = development.BUILD_TREE_COMPONENT
        path = owner + "/README.md"
        graph = self.graph()
        scope = development.scope(graph, self.selection(graph, [path]))
        self.assertFalse(scope.errors)
        self.assertIn(owner, scope.packages)
        index = ls.TreeIndex("fixture", "head", "head", {path: ("100644", "1" * 40)})
        self.assertFalse(development.has_declared_source_ownership(index, [path]))

    def test_bootstrap_source_runs_complete_standalone_library_and_retains_diagnostics(self):
        graph = self.graph()
        selection = self.selection(graph, ["src/bootstrap/src/core/build_steps/tool.rs"])
        scope = development.scope(graph, selection)
        self.assertFalse(scope.errors)
        self.assertEqual(scope.packages, [development.BOOTSTRAP_COMPONENT])
        self.assertFalse(scope.recipes)
        legs = gate.development_legs(graph, selection,
                                     [fixtures.leg(id="compiler-check"), fixtures.leg(id="push-rows")], 2)
        library = next(leg for leg in legs if leg.id == "development-package-bootstrap")
        self.assertEqual(library.command,
                         ["targo", "--unverified", "test", "--locked", "--offline",
                          "--manifest-path", "src/bootstrap/Cargo.toml", "--lib"])
        self.assertTrue(library.force_run)
        self.assertFalse(library.needs_stage1)
        self.assertTrue(next(leg for leg in legs if leg.id == "compiler-check").diagnostic_only)
        self.assertIn("--all-rows", next(leg for leg in legs if leg.id == "push-rows").command)
        selection.everything.append("unknown source reach")
        self.assertIn("unknown source reach", development.scope(graph, selection).errors)

    def test_bootstrap_library_owner_refuses_executables_and_manifest_changes(self):
        graph = self.graph()
        for path in ("src/bootstrap/src/bin/main.rs", "src/bootstrap/src/BIN/main.rs",
                     "src/bootstrap/src/main.rs", "src/bootstrap/src/Main.rs",
                     "src/bootstrap/Cargo.toml", "src/bootstrap/build.rs"):
            with self.subTest(path=path):
                selected = self.selection(graph, [path])
                if path.endswith("Cargo.toml"):
                    selected.cargo_impacts[path] = set()
                self.assertTrue(development.scope(graph, selected).errors)
                index = ls.TreeIndex("fixture", "head", "head", {path: ("100644", "1" * 40)})
                self.assertFalse(development.has_declared_source_ownership(index, [path]))
        for path in ("src/bootstrap/src/core/build_steps/tool.rs",
                     "src/bootstrap/src/core/builder/cli_paths/snapshots/x_check.snap"):
            with self.subTest(path=path):
                index = ls.TreeIndex("fixture", "head", "head", {path: ("100644", "1" * 40)})
                self.assertTrue(development.has_declared_source_ownership(index, [path]))
                self.assertFalse(development.scope(graph, self.selection(graph, [path])).errors)

    def test_full_graph_bootstrap_reason_keeps_its_actual_library_owner(self):
        graph = self.graph()
        path = "src/bootstrap/src/core/builder/cargo.rs"
        graph.index.entries[path] = ("100644", "1" * 40)
        selection = ls.select(graph, "base", [path])
        self.assertTrue(selection.everything)
        scope = development.scope(graph, selection)
        self.assertFalse(scope.errors)
        self.assertEqual(scope.packages, [development.BOOTSTRAP_COMPONENT])
        legs = gate.development_legs(graph, selection, [fixtures.leg(id="push-rows")], 2)
        library = next(leg for leg in legs if leg.id == "development-package-bootstrap")
        self.assertTrue(library.force_run)
        self.assertEqual(library.command[-2:], ["src/bootstrap/Cargo.toml", "--lib"])
        self.assertTrue(next(leg for leg in legs if leg.id == "push-rows").force_run)
        selection.everything.append("unknown provider/source reach")
        self.assertIn("unknown provider/source reach", development.scope(graph, selection).errors)

    def test_full_graph_bootstrap_reason_refuses_wrong_owner_opaque_and_indirect_inputs(self):
        path = "src/bootstrap/src/core/builder/cargo.rs"
        for mode in ("120000", "160000"):
            graph = self.graph()
            graph.index.entries[path] = (mode, "1" * 40)
            selected = ls.select(graph, "base", [path])
            self.assertTrue(development.scope(graph, selected).errors)
        graph = self.graph()
        graph.index.entries[path] = ("100644", "1" * 40)
        graph.opaque[development.BOOTSTRAP_COMPONENT] = "unknown manifest"
        self.assertTrue(development.scope(graph, ls.select(graph, "base", [path])).errors)
        graph = self.graph()
        graph.index.entries[path] = ("100644", "1" * 40)
        graph.packages["src/bootstrap/src/core"] = ls.Package("src/bootstrap/src/core", "foreign")
        self.assertTrue(development.scope(graph, ls.select(graph, "base", [path])).errors)

    def test_declared_data_owner_preserves_unknown_global_refusal(self):
        graph = self.graph()
        path = "scripts/ir_cohort_physical_read_set.json"
        kind, why = ls.classify(graph, path)
        self.assertEqual(kind, "everything")
        selection = self.selection(graph, [path], [f"{path}: {why}"])
        scope = development.scope(graph, selection)
        self.assertFalse(scope.errors)
        self.assertIn("scripts.tests.check_ledger_pins_test", scope.tests)
        selection.everything.append("unknown source reach")
        self.assertEqual(development.scope(graph, selection).errors, ["unknown source reach"])

    def test_native_domain_owner_does_not_hide_other_debt_api_changes(self):
        with tempfile.TemporaryDirectory(prefix="development-native-domain-") as directory:
            root = Path(directory)
            debt = "crates/trust-build-cpu/src/external_debt.rs"
            domain = "crates/trust-build-cpu/src/native_domain.rs"
            original = b"impl ExternalDebt {\n    pub fn reserved(&self) -> u32 { 0 }\n}\n"
            base = fixtures.make_repo(root, {debt: original.decode(), domain: "// original\n"}, {})
            added = original.replace(b"\n}", development.RETAINED_IDENTITY_ACCESSOR + b"\n}")
            (root / debt).write_bytes(added)
            (root / domain).write_text("// domain ledger binding\n")
            fixtures.git_in(root, "add", ".")
            fixtures.git_in(root, "commit", "-qm", "private identity accessor and domain binding")
            graph = self.graph()
            graph.index = ls.TreeIndex.load(str(root), "HEAD")
            graph.packages["src/tools/compiletest"].deps.add("crates/trust-build-cpu")
            changed = ls.changed_paths(str(root), base, "HEAD")
            selection = ls.Selection(base, graph.index.rev, changed, [])
            scope = development.scope(graph, selection)
            self.assertEqual(scope.packages, ["crates/trust-build-cpu"])
            self.assertFalse(scope.recipes)
            (root / debt).write_bytes(added.replace(b"{ 0 }", b"{ 1 }"))
            fixtures.git_in(root, "add", ".")
            fixtures.git_in(root, "commit", "-qm", "actual different public debt behavior")
            graph.index = ls.TreeIndex.load(str(root), "HEAD")
            scope = development.scope(graph, ls.Selection(base, graph.index.rev, changed, []))
            self.assertIn("src/tools/compiletest", scope.packages)
            self.assertTrue(set(development.INTEGRATION_RECIPES) <= set(scope.recipes))

    def test_provenance_source_runs_complete_targets_and_real_declared_consumers(self):
        graph = self.graph()
        owner = development.PROVENANCE_COMPONENT
        path = owner + "/src/process/owned_group.rs"
        graph.index.entries[path] = ("100644", "1" * 40)
        graph._index_spellings = None
        selected = self.selection(graph, [path])
        self.assertTrue(development.has_declared_source_ownership(graph.index, [path]))
        scope = development.scope(graph, selected)
        self.assertFalse(scope.errors)
        self.assertIn(owner, scope.packages)
        self.assertIn(development.CONTROLLER_COMPONENT, scope.packages)
        old = [fixtures.leg(id="push-rows")]
        legs = gate.development_legs(graph, selected, old, 1)
        target = next(leg for leg in legs if leg.id == "development-package-trust-resource-provenance")
        self.assertTrue(target.force_run)
        self.assertIn(owner, target.targets)
        self.assertIn("--all-targets", target.command)
        self.assertIn("--all-features", target.command)
        self.assertIn("--locked", target.command)
        self.assertIn("--offline", target.command)
        self.assertNotIn("--", target.command)
        self.assertNotIn("--lib", target.command)
        self.assertIn(owner, target.inputs)
        self.assertTrue(all(leg.force_run for leg in legs
                            if leg.id.startswith("development-package-trust-resource-controller-")))
        push = next(leg for leg in legs if leg.id == "push-rows")
        self.assertTrue(push.force_run)
        self.assertIn("--all-rows", push.command)
        selected.everything.append("unknown native process reader")
        self.assertIn("unknown native process reader", development.scope(graph, selected).errors)
        graph.opaque[owner] = "unknown provenance manifest"
        self.assertTrue(development.scope(graph, self.selection(graph, [path])).errors)
        graph.opaque.pop(owner)
        neighbour = owner + "/src/unregistered.py"
        graph.index.entries[neighbour] = ("100644", "2" * 40)
        graph._index_spellings = None
        self.assertFalse(development.has_declared_source_ownership(graph.index, [neighbour]))
        self.assertTrue(development.scope(graph, self.selection(graph, [neighbour])).errors)

    def test_changed_execution_component_gets_full_library_tests_and_normal_recipes(self):
        graph = self.graph()
        selection = self.selection(graph, ["src/jobserver_utils/src/lib.rs"])
        scope = development.scope(graph, selection)
        self.assertFalse(scope.errors)
        self.assertEqual(set(scope.packages), development.COMPONENTS - {development.PROVENANCE_COMPONENT})
        self.assertEqual(scope.recipes, sorted(development.INTEGRATION_RECIPES))
        old = [fixtures.leg(id=name) for name in ("push-rows", "compiler-check", "validation-tests", "tcb-panic-ratchet", "ir-cohort")]
        legs = gate.development_legs(graph, selection, old, 2)
        commands = [leg.command for leg in legs if leg.id.startswith("development-package-")]
        self.assertTrue(all("scheduler" not in command for command in commands))
        standalone = [command for command in commands if "x.py" not in command]
        self.assertTrue(all("--locked" in command and ("--lib" in command or "--all-targets" in command)
                            for command in standalone))
        for component in set(scope.packages) - {development.CONTROLLER_COMPONENT, "src/tools/compiletest"}:
            self.assertTrue(any(component + "/Cargo.toml" in command
                                or ("-p" in command and graph.packages[component].name in command)
                                for command in standalone), component)
        compiletest = next(leg for leg in legs if leg.id == "development-package-compiletest")
        self.assertTrue(compiletest.needs_stage1 and compiletest.force_run)
        self.assertIn("x.py", compiletest.command)
        self.assertIn("src/tools/compiletest", compiletest.command)
        self.assertNotIn("TEST_RUSTC", compiletest.env)
        controller_commands = [command for command in commands
                               if development.CONTROLLER_COMPONENT + "/Cargo.toml" in command]
        self.assertTrue(all("--no-default-features" in command for command in controller_commands))
        self.assertTrue(any("--all-features" in command for command in controller_commands))
        push = next(leg for leg in legs if leg.id == "push-rows")
        self.assertTrue(push.force_run)
        self.assertIn("--all-rows", push.command)
        self.assertTrue(next(leg for leg in legs if leg.id == "compiler-check").diagnostic_only)
        self.assertFalse(next(leg for leg in legs if leg.id == "ir-cohort").diagnostic_only)

    def test_base_head_cannot_omit_larger_actual_supported_push_checks(self):
        graph = self.graph()
        subject = self.selection(graph, [])
        pushed = self.selection(graph, ["src/tools/compiletest/src/lib.rs"])
        landing = gate.LandingRange("actual-main", graph.index.rev, "origin", True, tuple(pushed.changed), "")
        with mock.patch.object(gate, "landing_selection", return_value=pushed):
            legs = gate.development_legs(graph, subject, [], 1, landing)
        self.assertIn("development-package-compiletest", [leg.id for leg in legs])
        self.assertIn("development-recipes", [leg.id for leg in legs])

    def test_base_head_with_unsupported_actual_push_refuses_and_overlap_deduplicates(self):
        graph = self.graph()
        subject = self.selection(graph, ["src/tools/compiletest/src/lib.rs"])
        landing = gate.LandingRange("actual-main", graph.index.rev, "origin", True, tuple(subject.changed), "")
        with mock.patch.object(gate, "landing_selection", return_value=subject):
            legs = gate.development_legs(graph, subject, [], 1, landing)
        ids = [leg.id for leg in legs]
        self.assertEqual(ids.count("development-package-compiletest"), 1)
        with mock.patch.object(gate, "landing_selection", return_value=self.selection(graph, ["unknown/outgoing"])):
            with self.assertRaisesRegex(RuntimeError, "outgoing scope refused"):
                gate.development_legs(graph, self.selection(graph, []), [], 1, landing)

    def test_unknown_owner_and_global_inputs_refuse_instead_of_omission(self):
        graph = self.graph()
        for path in ("compiler/rustc_b/src/lib.rs", "unclassified/source.rs", "Cargo.lock", "first-party/trust-ir"):
            with self.subTest(path=path):
                self.assertTrue(development.scope(graph, self.selection(graph, [path])).errors)
        self.assertTrue(development.scope(graph, self.selection(graph, [], ["unknown feature/source delta"])).errors)

    def test_local_git_outgoing_selects_only_its_native_suites(self):
        graph = self.graph()
        for owner, name in ((development.LOCAL_GIT_CORE, "targo-core"),
                            (development.LOCAL_GIT_WORKSPACE, "targo")):
            graph.packages[owner] = ls.Package(owner, name)
            graph.index.entries[owner + "/Cargo.toml"] = ("100644", "0" * 40)
        graph.index.entries[development.LOCAL_GIT_FIXTURE] = ("100644", "0" * 40)
        importer = development.LOCAL_GIT_IMPORT + "pack_stream.rs"
        selected = self.selection(graph, [importer, development.LOCAL_GIT_FIXTURE])
        self.assertTrue(development.may_have_scope(selected.changed))
        scoped = development.scope(graph, selected)
        self.assertTrue(scoped.local_git_import)
        self.assertFalse(scoped.errors or scoped.packages or scoped.recipes)
        landing = gate.LandingRange("actual-main", graph.index.rev, "origin", True, tuple(selected.changed), "")
        existing = [fixtures.leg(id=name) for name in ("push-rows", "native-targo-tests")]
        with mock.patch.object(gate, "landing_selection", return_value=selected):
            legs = gate.development_legs(graph, self.selection(graph, []), existing, 2, landing)
        self.assertEqual({leg.id for leg in legs}, {
            "push-rows", "native-targo-tests", development.LOCAL_GIT_CORE_LEG, development.LOCAL_GIT_FIXTURE_LEG,
        })
        by_id = {leg.id: leg for leg in legs}
        self.assertTrue(by_id["native-targo-tests"].diagnostic_only)
        self.assertIn("--all-rows", by_id["push-rows"].command)
        core, fixture = by_id[development.LOCAL_GIT_CORE_LEG], by_id[development.LOCAL_GIT_FIXTURE_LEG]
        for leg in (core, fixture):
            self.assertTrue(leg.force_run)
            self.assertEqual(leg.command[:7], [
                "targo", "--unverified", "test", "--locked", "--offline", "--manifest-path",
                "src/tools/targo/Cargo.toml",
            ])
        self.assertIn("sources::git::local_import", core.command)
        for leg in (core, fixture):
            self.assertIn("vendored-openssl,vendored-libgit2", leg.command)
        self.assertEqual(fixture.command[7:11], ["-p", "targo", "--test", "local_git_source_cache"])
        self.assertIn('env.TARGO_LOCAL_SOURCE_TEST_BINARY.value=""', fixture.command)
        self.assertIn("env.TARGO_LOCAL_SOURCE_TEST_BINARY.force=true", fixture.command)
        self.assertIn("env.TARGO_LOCAL_SOURCE_TEST_BINARY.relative=false", fixture.command)
        del graph.index.entries[development.LOCAL_GIT_FIXTURE]
        self.assertTrue(development.scope(graph, self.selection(graph, [importer])).errors)
        unrelated = development.LOCAL_GIT_CORE + "/src/sources/git/source.rs"
        self.assertFalse(development.may_have_scope([unrelated]))
        self.assertTrue(development.scope(graph, self.selection(graph, [unrelated])).errors)

    def test_local_git_runtime_refuses_binary_override_before_probing_targo(self):
        leg = fixtures.leg(id=development.LOCAL_GIT_FIXTURE_LEG, command=["targo", "--unverified", "test"])
        for override in ("/prior/targo", ""):
            with self.subTest(override=override), \
                    mock.patch.object(gate, "leg_environment", return_value={"TARGO_LOCAL_SOURCE_TEST_BINARY": override}), \
                    mock.patch.object(gate.landing_targo, "capability_gap", side_effect=AssertionError("must refuse")):
                self.assertIn("unset TARGO_LOCAL_SOURCE_TEST_BINARY", gate.targo_unready(leg))

    def test_local_git_native_profile_requires_real_original_tools_but_not_unused_docs(self):
        original = str(Path(sys.executable).resolve())
        for leg_id in (development.LOCAL_GIT_CORE_LEG, development.LOCAL_GIT_FIXTURE_LEG):
            leg = fixtures.leg(id=leg_id, command=["targo", "--unverified", "test"])
            env = {"MAKE": original, "RUSTC": original}
            with mock.patch.object(gate, "leg_environment", return_value=env), \
                    mock.patch.object(gate.landing_targo, "capability_gap", return_value=None) as probe:
                self.assertIsNone(gate.targo_unready(leg))
                probe.assert_called_once()
            required = ["MAKE", *(["RUSTC"] if leg_id == development.LOCAL_GIT_FIXTURE_LEG else [])]
            for name in required:
                for bad in (None, "", "relative", "/absent/original-tool"):
                    bad_env = dict(env)
                    if bad is None:
                        bad_env.pop(name)
                    else:
                        bad_env[name] = bad
                    with self.subTest(leg=leg_id, name=name, bad=bad), \
                            mock.patch.object(gate, "leg_environment", return_value=bad_env), \
                            mock.patch.object(gate.landing_targo, "capability_gap", side_effect=AssertionError("unavailable tool must refuse before probe")):
                        self.assertIn(name, gate.targo_unready(leg))

    def test_original_make_path_identity_preserves_spaces_without_executing_it(self):
        with tempfile.TemporaryDirectory(prefix="original MAKE path ") as directory:
            program = Path(directory) / "make"
            program.write_bytes(b"original native input")
            with mock.patch.dict(os.environ, {"MAKE": str(program)}, clear=True), \
                    mock.patch.object(gate, "_bootstrap_target_tables", return_value={}), \
                    mock.patch.object(gate, "closure_parts", return_value=[("file", str(program))]) as closure:
                self.assertEqual(gate.toolchain_overrides(), [("MAKE", str(program))])
                self.assertEqual(gate.override_tool_parts(), [("file", str(program))])
                closure.assert_called_once_with(str(program))
                before = gate.part_identity("file", str(program))
                program.write_bytes(b"changed original native input bytes")
                self.assertNotEqual(before, gate.part_identity("file", str(program)),
                                    "same MAKE locator cannot preserve old byte evidence")

    def test_known_raw_prose_reader_refuses_uncovered_scope(self):
        graph = self.graph()
        graph.packages["compiler/rustc_b"].reads.append(ls.Read("compile", "docs/new-input.md", False, "actual reader"))
        scope = development.scope(graph, self.selection(graph, ["docs/new-input.md"]))
        self.assertTrue(any("direct reader" in error for error in scope.errors))

    def test_prose_only_component_reader_gets_fresh_component_and_recipe_checks(self):
        graph = self.graph()
        graph.packages["src/tools/compiletest"].reads.append(ls.Read("compile", "docs/tool-input.md", False, "actual reader"))
        scope = development.scope(graph, self.selection(graph, ["docs/tool-input.md"]))
        self.assertFalse(scope.errors)
        self.assertEqual(scope.packages, ["src/tools/compiletest"])
        self.assertEqual(scope.recipes, sorted(development.INTEGRATION_RECIPES))

    def test_prose_component_reader_uses_same_case_folding_as_diagnostics(self):
        graph = self.graph()
        graph.packages["src/tools/compiletest"].reads.append(ls.Read("compile", "DOCS/TOOL-INPUT.md", False, "actual reader"))
        scope = development.scope(graph, self.selection(graph, ["docs/tool-input.md"]))
        self.assertFalse(scope.errors)
        self.assertEqual(scope.packages, ["src/tools/compiletest"])

    def test_runtime_directory_potential_stays_diagnostic_but_exact_glob_compile_reads_require_check(self):
        for cls, target, required in (("runtime", "docs", False), ("runtime", "docs/new-input.md", True),
                                      ("runtime", "docs/*.md", True), ("compile", "docs", True)):
            with self.subTest(cls=cls, target=target):
                graph = self.graph()
                graph.packages["compiler/rustc_b"].reads = [ls.Read(cls, target, False, "controlled reader")]
                selection = self.selection(graph, ["docs/new-input.md"])
                self.assertEqual(bool(development.scope(graph, selection).errors), required)
                broad = fixtures.leg(id="compiler-check", reasons=[target + " reaches it"])
                if not required:
                    gate.development_legs(graph, selection, [broad], 1)
                    self.assertTrue(broad.selected)
                    self.assertTrue(broad.diagnostic_only)
                    self.assertIn(target, broad.reasons[0])

    def test_prose_listing_only_reader_ignores_only_in_place_content_change(self):
        graph = self.graph()
        graph.packages["compiler/rustc_b"].reads = [ls.Read("compile", "docs/listing-new.md", False, "listing", listing=True)]
        selection = self.selection(graph, ["docs/listing-new.md"])
        self.assertTrue(development.scope(graph, selection).errors)
        selection.in_place.add("docs/listing-new.md")
        self.assertFalse(development.scope(graph, selection).errors)

    def test_runtime_file_link_reader_keeps_exact_source_dependency(self):
        graph = self.graph()
        # The fixture's real tracked crates/linker/data.md points to docs/linked.md.
        graph.packages["compiler/rustc_b"].reads = [ls.Read("runtime", "crates/linker/data.md", False, "file link")]
        self.assertTrue(development.scope(graph, self.selection(graph, ["docs/linked.md"])).errors)

    def test_unresolved_diagnostics_remain_selected_and_visible(self):
        graph = self.graph()
        selection = self.selection(graph, ["src/tools/compiletest/src/lib.rs"])
        broad = fixtures.leg(id="compiler-check", reasons=["inputs unresolved: actual product reader"])
        legs = gate.development_legs(graph, selection, [broad], 1)
        self.assertTrue(broad.selected)
        self.assertTrue(broad.diagnostic_only)
        self.assertIn("unresolved", broad.reasons[0])

    def test_conservative_consumers_are_diagnostics_not_coverage_claims(self):
        graph = self.graph()
        selection = self.selection(graph, ["Cargo.lock", "src/tools/compiletest/Cargo.toml"])
        selection.cargo_impacts = {path: {"src/tools/compiletest", "compiler/rustc_b"} for path in selection.changed}
        scope = development.scope(graph, selection)
        self.assertFalse(scope.errors)
        self.assertEqual(scope.packages, ["src/tools/compiletest"])

    def test_selector_self_change_has_focused_policy_and_cache_custody_tests(self):
        graph = self.graph()
        scope = development.scope(graph, self.selection(graph, ["scripts/lib/land_select.py"]))
        self.assertFalse(scope.errors)
        self.assertIn("scripts.tests.land_development_test", scope.tests)
        self.assertIn("scripts.tests.land_gate_test.CheckoutBindingTests", scope.tests)
        self.assertIn("scripts.tests.land_gate_test.CacheKeyTests", scope.tests)
        # The row table the selector builds its validation tables from has the
        # selector's owner: an edit to it is an edit to the selector's data.
        self.assertEqual(ls.LAND_ROWS_FILE, "gates/land.toml")
        self.assertTrue(development.may_have_scope([ls.LAND_ROWS_FILE]))
        self.assertFalse(development.may_have_scope(["gates/other.toml"]))
        table = development.scope(graph, self.selection(graph, [ls.LAND_ROWS_FILE]))
        self.assertFalse(table.errors)
        self.assertEqual(table.tests, scope.tests)
        self.assertIn("scripts.tests.land_gate_test.ValidationDependencyTests", table.tests)
        self.assertIn("scripts.tests.land_gate_test.DiscoverySnapshotTests", table.tests)

    def test_live_transport_programs_select_their_actual_controls(self):
        graph = self.graph()
        for path, tests in (("scripts/land_gate.py", ("scripts.tests.land_gate_row_custody_test",)),
                            ("scripts/tests/land_gate_row_custody_test.py", ("scripts.tests.land_gate_row_custody_test",)),
                            ("scripts/lib/remote_tips.py", ("scripts.tests.remote_tips_agh_test", "scripts.tests.remote_tips_shallow_test"))):
            with self.subTest(path=path):
                scope = development.scope(graph, self.selection(graph, [path]))
                self.assertFalse(scope.errors)
                self.assertTrue(set(tests) <= set(scope.tests))

    def test_native_recipe_population_preserves_linux_only_semantics(self):
        portable = ("tests/run-make/parallel-rustc-no-overwrite",)
        self.assertEqual(development.integration_recipes("darwin"), portable)
        self.assertEqual(development.integration_recipes("linux"),
                         portable + ("tests/run-make/jobserver-error",))
        self.assertEqual(development.integration_recipes("linux2"),
                         development.integration_recipes("linux"))

    def test_byte_identical_trust_recipe_move_requires_complete_original_inventory(self):
        graph = self.graph()
        old = "tests/run-make/frontend-token/"
        new = "tests/run-make/trust-frontend-token/"
        before = self.graph()
        before.index.entries[old + "rmake.rs"] = ("100644", "a" * 40)
        before.index.entries[old + "input.rs"] = ("100644", "b" * 40)
        for name in ("rmake.rs", "input.rs"):
            graph.index.entries[new + name] = before.index.entries[old + name]
        with mock.patch.object(ls.TreeIndex, "load", return_value=before.index):
            self.assertEqual(development.trust_recipe_move(graph, "base", old + "input.rs"),
                             new.rstrip("/"))
            graph.index.entries[new + "input.rs"] = ("100644", "c" * 40)
            self.assertIsNone(development.trust_recipe_move(graph, "base", old + "rmake.rs"))
            graph.index.entries[new + "input.rs"] = before.index.entries[old + "input.rs"]
            graph.index.entries[new + "extra.rs"] = ("100644", "d" * 40)
            self.assertIsNone(development.trust_recipe_move(graph, "base", old + "rmake.rs"))
            del graph.index.entries[new + "extra.rs"]
            before.index.entries[new + "preexisting.rs"] = ("100644", "e" * 40)
            self.assertIsNone(development.trust_recipe_move(graph, "base", old + "rmake.rs"))

    def test_missing_normal_recipe_refuses(self):
        graph = self.graph()
        del graph.index.entries[development.INTEGRATION_RECIPES[0] + "/rmake.rs"]
        self.assertTrue(development.scope(graph, self.selection(graph, ["src/tools/compiletest/src/lib.rs"])).errors)

    def test_real_exit_recipe_requirement_tracks_introduced_source_inputs(self):
        graph = self.graph()
        selected = self.selection(graph, ["src/tools/compiletest/src/lib.rs"])
        self.assertFalse(development.scope(graph, selected).errors)
        graph.index.entries[development.SCHEDULER_MODULE] = ("100644", "0" * 40)
        self.assertTrue(development.scope(graph, selected).errors)
        graph.index.entries[development.EXIT_RECIPE + "/rmake.rs"] = ("100644", "0" * 40)
        self.assertIn(development.EXIT_RECIPE, development.scope(graph, selected).recipes)
        del graph.index.entries[development.SCHEDULER_MODULE]
        self.assertIn(development.EXIT_RECIPE, development.scope(graph, selected).recipes)

    def test_changed_execution_source_symlink_refuses(self):
        graph = self.graph()
        path = "src/tools/compiletest/src/foreign.rs"
        graph.index.entries[path] = ("120000", "0" * 40)
        self.assertTrue(development.scope(graph, self.selection(graph, [path])).errors)

    def test_empty_ignored_missing_and_failed_native_suites_refuse(self):
        for text, code in (("", 0), ("test result: ok. 0 passed; 0 failed; 9 ignored;", 0),
                           ("test result: ok. 0 passed; 0 failed; 0 ignored;", 0),
                           ("test result: ok. 3 passed; 0 failed; 0 ignored;\ntest result: ok. 0 passed; 0 failed; 0 ignored;", 0),
                           ("test result: FAILED. 3 passed; 1 failed; 0 ignored;", 0),
                           ("test result: ok. 3 passed; 0 failed; 0 ignored;", 1)):
            with self.subTest(text=text, code=code):
                self.assertNotEqual(gate.development_test_result(text, code)[0], 0)
        self.assertEqual(gate.development_test_result("test result: ok. 3 passed; 0 failed; 0 ignored;", 0)[0], 0)
        self.assertNotEqual(gate.development_test_result(
            "test result: ok. 3 passed; 0 failed; 1 ignored;", 0, all_required=True)[0], 0)

    def test_helpers_are_bound_to_gate_identity_and_audited_reader_set(self):
        for name in ("scripts/lib/land_manifest.py", "scripts/lib/land_development.py"):
            self.assertIn(name, gate.GATE_FILES)
            self.assertIn(name, gate.IR_DIAGNOSTIC_READERS)

    def test_source_main_needs_refuses_unknown_and_does_not_claim_compiler_pass(self):
        graph = self.graph()
        for changed, expected in ((["src/tools/compiletest/src/lib.rs"], 1), (["unknown/input"], 2)):
            with mock.patch.object(ls.TreeIndex, "load", return_value=graph.index), \
                 mock.patch.object(ls, "build_graph", return_value=graph), \
                 mock.patch.object(ls, "changed_paths", return_value=changed), \
                 mock.patch.object(gate, "git", return_value="base"), \
                 mock.patch.object(gate, "verify_graph", side_effect=AssertionError("not a full diagnostic")):
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    rc = gate.cmd_needs(argparse.Namespace(leg="compiler-check", base="base", head="HEAD", development=True, verify_graph=True))
                self.assertEqual(rc, expected, output.getvalue())
                if expected == 1:
                    self.assertIn("diagnostic SKIP", output.getvalue())
                    self.assertIn("no full compiler-check PASS", output.getvalue())

    def test_all_rows_call_has_no_diagnostic_coverage_exemptions(self):
        push = gate.LandingPush("a" * 40, "b" * 40, "origin")
        rows = [gate.PushRow("verify.executes", "true", "actual verifier")]
        with mock.patch.object(gate, "landing_push", return_value=push), \
             mock.patch.object(gate, "push_profile_rows", return_value=rows), \
             mock.patch.object(gate, "PushQuarantine"), \
             mock.patch.object(gate, "uncovered_rows", side_effect=AssertionError("no coverage exemptions")), \
             mock.patch.object(gate, "run_push_rows", return_value=0) as execute, \
             mock.patch.object(gate, "push_refs_readers", return_value=frozenset()), \
             mock.patch.object(gate, "checkout_problem", return_value=None):
            self.assertEqual(gate.cmd_push_rows(argparse.Namespace(all_rows=True)), 0)
            self.assertEqual(execute.call_args.args[0], rows)
            self.assertEqual(execute.call_args.kwargs["covered"], [])

    def run_profile(self, *, moved_main=False, moved_input=False, declared_recipe=False, observed=None):
        graph = fixtures.Fixture.graph()
        selection = self.selection(graph, ["docs/README.md"])
        if declared_recipe:
            selection = gate.DeclaredDevelopmentSelection(selection.base, selection.head, selection.changed, [])
        calls, boundaries = [], []
        with tempfile.TemporaryDirectory(prefix="development-run-") as temporary, contextlib.ExitStack() as stack:
            root = Path(temporary)
            changed = [False]
            marker, stamp = root / "owned-child-ran", root / "stage1-stamp.json"
            if declared_recipe:
                stamp.write_text(json.dumps({"key": "existing", "rustc": ["controlled-artifact"]}))

            def declared_legs(*args, **kwargs):
                legs = [fixtures.leg(id=name) for name in ("push-rows", "ir-cohort", "tcb-panic-ratchet")]
                recipe = fixtures.leg(id="development-recipes", needs_stage1=True,
                                      command=[sys.executable, "-c", "pass"])
                for leg in [*legs, recipe]:
                    leg.force_run = True
                return [*legs, recipe]

            landing = gate.LandingRange("a" * 40, graph.index.rev, "origin", not moved_main,
                                        ("docs/README.md",), "remote main moved" if moved_main else "")

            def source(expected=None, **kwargs):
                boundaries.append((expected, kwargs))
                return "tracked input moved" if changed[0] else None

            def execute(leg, run_dir, *args, **kwargs):
                calls.append(leg.id)
                if declared_recipe and leg.id == "development-recipes":
                    subprocess.run([sys.executable, "-c", "from pathlib import Path; import sys; Path(sys.argv[1]).write_text('ran')",
                                    str(marker)], check=True, timeout=5)
                log = run_dir / (leg.id + ".log")
                log.write_text("actual fixture process completed\n")
                if moved_input:
                    changed[0] = True
                return 0, .01, str(log), False

            for name, value in (
                ("git", lambda *a, **kw: ""), ("checkout_problem", source),
                ("compute", lambda *a, **kw: (graph, selection, "base")),
                ("development_discovery_inputs", lambda *a, **kw: (selection.base, graph.index, selection.changed)),
                ("read_landing", lambda *a, **kw: landing),
                ("push_hook_state", lambda *a, **kw: fixtures.HOOK_OFF),
                ("build_legs", lambda *a, **kw: [fixtures.leg(id=name) for name in
                                               ("push-rows", "compiler-check", "ir-cohort", "tcb-panic-ratchet")]),
                ("toolchain_identity", lambda: {}), ("common_dir", lambda: root),
                ("global_fingerprint", lambda *a, **kw: "exact-fixture-inputs"),
                ("stage1_key", lambda *a, **kw: "stage"),
                ("rustc_identity", lambda: ["controlled-artifact"] if declared_recipe else None),
                ("run_leg", execute),
            ):
                stack.enter_context(mock.patch.object(gate, name, value))
            if declared_recipe:
                stack.enter_context(mock.patch.object(gate, "declared_development_legs", declared_legs))
                stack.enter_context(mock.patch.object(gate, "xpy_unready", return_value=None))
                stack.enter_context(mock.patch.object(gate, "stage1_stamp_path", return_value=stamp))
                stack.enter_context(mock.patch.object(gate, "stage1_reusable", side_effect=AssertionError("no computed readset: stamp query forbidden")))
                stack.enter_context(mock.patch.object(development, "recipe_result", return_value=(0, "controlled execution; no compiler qualification")))
            stack.enter_context(mock.patch.object(gate.host_budget, "measure", return_value=fixtures.host(28, 128, 100)))
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = gate.cmd_run(argparse.Namespace(base="base", development=True, only=None, no_cache=True, dry_run=False))
            records = list(root.rglob("record.json"))
            record = json.loads(records[0].read_text()) if records else None
            if observed is not None:
                observed.update(child_ran=marker.is_file(), stamp_exists=stamp.exists())
        return code, calls, boundaries, output.getvalue(), record

    def test_declared_recipe_executes_owned_child_without_importing_or_publishing_stage1_stamp(self):
        observed = {}
        code, calls, _, output, record = self.run_profile(declared_recipe=True, observed=observed)
        self.assertEqual(code, 0, output)
        self.assertEqual(calls.count("development-recipes"), 1)
        self.assertTrue(observed["child_ran"])
        self.assertFalse(observed["stamp_exists"])
        entry = record["legs"]["development-recipes"]
        self.assertIn("stamp disabled", entry["stage1"])
        self.assertNotIn("--keep-stage", entry["command"])

    def test_actual_development_run_keeps_live_rows_and_never_reports_diagnostic_pass(self):
        code, calls, boundaries, output, record = self.run_profile()
        self.assertEqual(code, 0, output)
        self.assertEqual(set(calls), {"push-rows", "ir-cohort", "tcb-panic-ratchet"})
        self.assertTrue(all(not options.get("ir_diagnostic") for _, options in boundaries))
        self.assertEqual(record["profile"], "development")
        self.assertIn("NOT RUN", record["legs"]["compiler-check"]["outcome"])
        self.assertIn("DEVELOPMENT CHECKS PASSED", output)
        self.assertNotIn("LAND-GATE: GREEN", output)

    def test_development_run_keeps_independent_checks_when_main_moves(self):
        code, calls, _, output, record = self.run_profile(moved_main=True)
        self.assertEqual(code, 2, output)
        self.assertEqual(set(calls), {"ir-cohort", "tcb-panic-ratchet"})
        self.assertIn("NOT JUDGED", record["legs"]["push-rows"]["outcome"])
        self.assertIn("DEVELOPMENT SOURCE CHECKS PASSED; LANDING NOT JUDGED", output)

    def test_development_run_refuses_input_movement_and_publishes_no_pass(self):
        code, calls, _, output, record = self.run_profile(moved_input=True)
        self.assertEqual(code, 2, output)
        self.assertTrue(calls)
        self.assertTrue(all(entry["outcome"] != "PASS" for entry in record["legs"].values()))


class DevelopmentRecipeCensusTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="development-source-")
        self.addCleanup(temporary.cleanup)
        self.source_root = Path(temporary.name).resolve()
        (self.source_root / "build").mkdir()

    def events(self):
        self.targets = [*development.INTEGRATION_RECIPES, development.EXIT_RECIPE]
        count = len(self.targets)
        schema = "trust.compiletest.case-events/v1"
        rows = [{"schema": schema, "type": "invocation", "argv": ["--suite", "run-make", "--mode", "run-make", "--target", "aarch64-apple-darwin", "--host", "aarch64-apple-darwin", "--stage-id", "stage1-aarch64-apple-darwin", "--src-root", str(self.source_root), "--rustc-path", str(self.source_root/"build/host/stage1/bin/trustc"), "--compile-lib-path", str(self.source_root/"build/host/stage0/lib"), "--run-lib-path", str(self.source_root/"build/host/stage1/lib"), "--run-make-support-rlib", str(self.source_root/"build/bootstrap-seed-tools/deps/libsupport.rlib"), "--run-make-support-rmeta", str(self.source_root/"build/bootstrap-seed-tools/deps/libsupport.rmeta")]},
                {"schema": schema, "type": "suite", "event": "started", "selected_count": count, "test_count": count}]
        for target in self.targets:
            for event in ("started", "ok"):
                rows.append({"schema": schema, "type": "test", "event": event, "name": "[run-make] " + target})
        rows.append({"schema": schema, "type": "suite", "event": "ok", "selected_count": count,
                     "executed_count": count, "terminal_count": count, "passed": count, "failed": 0,
                     "ignored": 0, "protocol_valid": True, "protocol_error": None})
        return rows

    def grade(self, rows, starts=1, streams=1, code=0, duplicate_target=False):
        with tempfile.TemporaryDirectory(prefix="development-cases-") as temporary:
            root = Path(temporary)
            for index in range(streams):
                actual = json.loads(json.dumps(rows))
                if index and not duplicate_target:
                    argv = actual[0]["argv"]
                    argv[argv.index("--target")+1] = "x86_64-apple-darwin"
                    argv[argv.index("--stage-id")+1] = "stage1-x86_64-apple-darwin"
                (root / f"compiletest-events-123-{index}.jsonl").write_text("".join(json.dumps(row) + "\n" for row in actual))
            log = "".join(f"Testing stage1 with compiletest suite=run-make mode=run-make ({target})\n" for target in ["aarch64-apple-darwin", "x86_64-apple-darwin"][:starts])
            return development.recipe_result(root, self.targets, log, code, self.source_root, "aarch64-apple-darwin")

    def test_each_selected_recipe_must_pass_in_every_started_target(self):
        rows = self.events()
        self.assertEqual(self.grade(rows)[0], 0)
        self.assertEqual(self.grade(rows, starts=2, streams=2)[0], 0)

    def test_sanctioned_noindex_build_and_host_aliases_keep_the_case_population(self):
        for absolute in (False, True):
            with self.subTest(absolute=absolute), tempfile.TemporaryDirectory() as temporary:
                self.source_root = Path(temporary).resolve()
                physical = self.source_root / "build.noindex"
                physical.mkdir()
                (physical / "aarch64-apple-darwin").mkdir()
                (physical / "host").symlink_to("aarch64-apple-darwin", target_is_directory=True)
                (self.source_root / "build").symlink_to(
                    physical if absolute else "build.noindex", target_is_directory=True
                )
                code, reason = self.grade(self.events())
                self.assertEqual(code, 0, reason)

    def test_foreign_arbitrary_and_chained_build_aliases_refuse(self):
        for layout in ("foreign", "other-inside", "chained-noindex", "dangling", "cycle"):
            with self.subTest(layout=layout), tempfile.TemporaryDirectory() as temporary:
                parent = Path(temporary).resolve()
                self.source_root = parent / "source"
                self.source_root.mkdir()
                target = self.source_root / "other" if layout == "other-inside" else parent / "foreign"
                target.mkdir()
                if layout == "chained-noindex":
                    (self.source_root / "build.noindex").symlink_to(target, target_is_directory=True)
                    target = self.source_root / "build.noindex"
                elif layout == "dangling":
                    target = self.source_root / "build.noindex"
                elif layout == "cycle":
                    (self.source_root / "build.noindex").mkdir()
                    target = self.source_root / "build"
                (self.source_root / "build").symlink_to(target, target_is_directory=True)
                self.assertNotEqual(self.grade(self.events())[0], 0)

    def test_a_linked_build_tree_is_the_checkout_and_its_outside_is_not(self):
        # Preserve main's real linked-tree positive and foreign-tool negative
        # using the same owned source fixture as the other recipe controls.
        with tempfile.TemporaryDirectory(prefix="development-linked-build-") as temporary:
            self.source_root = Path(temporary).resolve()
            (self.source_root / "build.noindex").mkdir()
            (self.source_root / "build").symlink_to("build.noindex")
            self.assertEqual(self.grade(self.events())[0], 0)
            outside = self.events()
            argv = outside[0]["argv"]
            argv[argv.index("--rustc-path") + 1] = str(self.source_root / "elsewhere/stage1/bin/trustc")
            self.assertNotEqual(self.grade(outside)[0], 0)

    def test_empty_ignored_filtered_missing_duplicate_and_wrong_population_refuse(self):
        for change in ("all-ignored", "partial", "empty", "duplicate-start", "duplicate-terminal", "missing-start", "forged-counts", "wrong-name", "wrong-schema", "wrong-mode"):
            with self.subTest(change=change):
                rows = self.events()
                if change == "all-ignored":
                    for row in rows[2:-1]:
                        if row["event"] == "ok": row["event"] = "ignored"
                    rows[-1].update(passed=0, ignored=len(self.targets), executed_count=0)
                elif change == "partial":
                    rows = rows[:4] + [rows[-1]]
                    rows[1].update(test_count=1, selected_count=1)
                    rows[-1].update(selected_count=1, terminal_count=1, executed_count=1, passed=1)
                elif change == "empty": rows = rows[:2] + [rows[-1]]
                elif change == "duplicate-start": rows.insert(3, dict(rows[2]))
                elif change == "duplicate-terminal": rows.insert(4, dict(rows[3]))
                elif change == "missing-start": del rows[2]
                elif change == "forged-counts": rows[-1]["passed"] = True
                elif change == "wrong-name": rows[2]["name"] += "-unrelated"
                elif change == "wrong-schema": rows[3]["schema"] = "unknown/v1"
                elif change == "wrong-mode": rows[0]["argv"][rows[0]["argv"].index("--mode")+1] = "ui"
                self.assertNotEqual(self.grade(rows)[0], 0)

    def test_missing_target_stream_and_nonzero_command_refuse(self):
        rows = self.events()
        self.assertNotEqual(self.grade(rows, starts=2, streams=1)[0], 0)
        self.assertNotEqual(self.grade(rows, streams=0)[0], 0)
        self.assertNotEqual(self.grade(rows, code=1)[0], 0)
        self.assertNotEqual(self.grade(rows, starts=2, streams=2, duplicate_target=True)[0], 0)

    def test_wrong_checkout_host_target_stage_and_support_headers_refuse(self):
        for flag in ("--src-root", "--host", "--target", "--stage-id", "--rustc-path", "--run-make-support-rlib"):
            for mutation in ("missing", "duplicate", "wrong"):
                with self.subTest(flag=flag, mutation=mutation):
                    rows = self.events()
                    argv = rows[0]["argv"]
                    index = argv.index(flag)
                    if mutation == "missing": del argv[index:index+2]
                    elif mutation == "duplicate": argv.extend(argv[index:index+2])
                    else: argv[index+1] = "/unrelated/checkout" if "path" in flag or "root" in flag or "rlib" in flag else "unrelated-target"
                    self.assertNotEqual(self.grade(rows)[0], 0)


class ToolNameGuideDevelopmentTests(unittest.TestCase):
    def graph(self):
        graph = fixtures.Fixture.graph()
        graph.packages[development.TOOL_NAME_OWNER] = ls.Package(development.TOOL_NAME_OWNER, "trust-release")
        graph.packages["targo-trust"] = ls.Package("targo-trust", "targo-trust")
        graph.index.entries[development.TOOL_NAME_GUIDE] = ("100644", "1" * 40)
        for path, blob in development.TOOL_NAME_READER_PINS.items():
            graph.index.entries[path] = ("100644", blob)
        graph.__dict__.pop("_index_spellings", None)
        return graph

    def audits(self):
        return {site.removesuffix(" (audited)"): {
            "blob": development.TOOL_NAME_READER_PINS[site.removesuffix(" (audited)")],
            "class": cls, "test_only": True, "reads": [development.TOOL_NAME_GUIDE],
            "premises": [{"file": "crates/trust-release/src/lib.rs",
                          "blob": development.TOOL_NAME_READER_PINS["crates/trust-release/src/lib.rs"]}],
        } for _owner, cls, site in development.TOOL_NAME_READERS}

    def scope(self, graph, paths=None):
        with mock.patch.object(ls, "load_audits", return_value=self.audits()):
            return development.scope(graph, ls.Selection("base", graph.index.rev,
                                                        paths or [development.TOOL_NAME_GUIDE], []))

    def add_reader(self, graph, owner, cls, site):
        graph.packages[owner].reads.append(ls.Read(cls, development.TOOL_NAME_GUIDE, True, site))

    def test_each_exact_audited_reader_selects_actual_native_target(self):
        for owner, cls, site in development.TOOL_NAME_READERS:
            with self.subTest(site=site):
                graph = self.graph()
                self.add_reader(graph, owner, cls, site)
                result = self.scope(graph)
                self.assertFalse(result.errors)
                self.assertTrue(result.tool_name_guide)
                selected = ls.Selection("base", graph.index.rev, [development.TOOL_NAME_GUIDE], [])
                existing = [fixtures.leg(id="compiler-check"), fixtures.leg(id="push-rows")]
                with mock.patch.object(ls, "load_audits", return_value=self.audits()):
                    legs = gate.development_legs(graph, selected, existing, 1)
                leg = next(leg for leg in legs if leg.id == development.TOOL_NAME_LEG)
                self.assertEqual(leg.command, ["targo", "--unverified", "test", "--locked", "--offline",
                    "--manifest-path", "crates/trust-release/Cargo.toml", "--test", "tool_name_source_inputs",
                    "--", "--test-threads=1"])
                self.assertTrue(leg.force_run)
                self.assertFalse(leg.diagnostic_only)
                self.assertTrue(existing[0].diagnostic_only)
                self.assertTrue(existing[1].force_run)

    def test_unknown_reader_in_same_or_foreign_package_still_refuses(self):
        for owner, cls, site in (("targo-trust", "runtime", "new reader"),
                                 ("targo-trust", "compile", "new include"),
                                 (development.TOOL_NAME_OWNER, "runtime", "new reader"),
                                 ("compiler/rustc_b", "compile", "new reader")):
            with self.subTest(owner=owner, cls=cls):
                graph = self.graph()
                known = sorted(development.TOOL_NAME_READERS)[0]
                self.add_reader(graph, *known)
                self.add_reader(graph, owner, cls, site)
                self.assertTrue(self.scope(graph).errors)

    def test_changed_missing_nonregular_or_aliased_inputs_refuse(self):
        for path in (development.TOOL_NAME_GUIDE, *development.TOOL_NAME_READER_PINS):
            for defect in ("missing", "symlink", "alias", "changed"):
                if defect == "changed" and path == development.TOOL_NAME_GUIDE:
                    continue  # Changed guide bytes are the input this actual-file check owns.
                with self.subTest(path=path, defect=defect):
                    graph = self.graph()
                    self.add_reader(graph, *sorted(development.TOOL_NAME_READERS)[0])
                    if defect == "missing":
                        del graph.index.entries[path]
                    elif defect == "alias":
                        graph.index.entries[path.upper()] = graph.index.entries[path]
                    else:
                        graph.index.entries[path] = ("120000" if defect == "symlink" else "100644", "0" * 40)
                    self.assertTrue(self.scope(graph).errors)

    def test_changed_guide_and_exact_test_source_are_owned_but_other_docs_are_not(self):
        graph = self.graph()
        self.add_reader(graph, *sorted(development.TOOL_NAME_READERS)[0])
        graph.index.entries[development.TOOL_NAME_GUIDE] = ("100644", "2" * 40)
        self.assertFalse(self.scope(graph).errors)
        self.assertFalse(self.scope(graph, [development.TOOL_NAME_TEST]).errors)
        other = "docs/other.md"
        graph.index.entries[other] = ("100644", "0" * 40)
        graph.packages["targo-trust"].reads.append(ls.Read("runtime", other, True, "new reader"))
        self.assertTrue(self.scope(graph, [other]).errors)

    def test_lapsed_or_wrong_class_audit_refuses(self):
        for defect in ("lapsed", "class", "test_only", "reads"):
            graph = self.graph()
            owner, cls, site = sorted(development.TOOL_NAME_READERS)[0]
            self.add_reader(graph, owner, cls, site)
            audits = self.audits()
            audit = audits[site.removesuffix(" (audited)")]
            audit[defect] = {"lapsed": "changed", "class": "other", "test_only": False, "reads": []}[defect]
            with mock.patch.object(ls, "load_audits", return_value=audits):
                selection = ls.Selection("base", graph.index.rev, [development.TOOL_NAME_GUIDE], [])
                self.assertTrue(development.scope(graph, selection).errors)

    def test_missing_discovery_read_cannot_remove_the_actual_guide_check(self):
        graph = self.graph()
        scope = self.scope(graph)
        self.assertFalse(scope.errors)
        self.assertTrue(scope.tool_name_guide)
        for source in self.audits():
            audits = self.audits()
            del audits[source]
            with mock.patch.object(ls, "load_audits", return_value=audits):
                selection = ls.Selection("base", graph.index.rev, [development.TOOL_NAME_GUIDE], [])
                self.assertTrue(development.scope(graph, selection).errors)

    def test_dependency_remapping_already_on_main_refuses_a_guide_only_candidate(self):
        graph = self.graph()
        manifest = "targo-trust/Cargo.toml"
        source = (Path(__file__).resolve().parents[2] / manifest).read_bytes()
        remapped = source.replace(b'trust-release = { path = "../crates/trust-release" }',
                                  b'trust-release = { path = "../other-reader" }', 1)
        self.assertNotEqual(source, remapped, "the actual caller manifest must bind the reviewed reader")
        oid = hashlib.sha1(b"blob " + str(len(remapped)).encode() + b"\0" + remapped).hexdigest()
        graph.index.entries[manifest] = ("100644", oid)
        self.add_reader(graph, *sorted(development.TOOL_NAME_READERS)[0])
        result = self.scope(graph)  # Only the guide is changed by this candidate.
        self.assertTrue(result.errors, "a preexisting namespace remapping must not inherit qualification")

    def test_namespace_shadow_or_config_redirect_before_candidate_refuses(self):
        changes = {
            "Cargo.toml": b'\n[replace]\n"trust-release:0.13.0" = { path = "another-reader" }\n',
            "targo-trust/src/main.rs": b"extern crate another_reader as trust_release;\n",
            "targo-trust/src/release_cli/mod.rs": b"use crate::another_reader as trust_release;\n",
            ".cargo/config.toml": b'\npaths = ["another-reader"]\n',
        }
        for path, delta in changes.items():
            with self.subTest(path=path):
                graph = self.graph()
                original = (Path(__file__).resolve().parents[2] / path).read_bytes()
                source = delta + original if path == ".cargo/config.toml" else original + delta
                graph.index.entries[path] = ("100644", hashlib.sha1(
                    b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest())
                self.assertTrue(self.scope(graph).errors)
        for path in (*development.TOOL_NAME_ABSENT_CONFIGS, "targo-trust/.cargo", "TARGO-TRUST/.CARGO/config.toml"):
            with self.subTest(path=path):
                graph = self.graph()
                graph.index.entries[path] = ("120000" if path.endswith(".cargo") else "100644", "0" * 40)
                self.assertTrue(self.scope(graph).errors)

    def test_ambient_source_resolution_refusal_precedes_native_execution(self):
        leg = fixtures.leg(id=development.TOOL_NAME_LEG, command=["targo", "--unverified", "test"])
        with mock.patch.object(gate, "leg_environment", return_value={}), \
             mock.patch.object(gate, "development_native_target_problem", return_value=None), \
             mock.patch.object(gate, "lock_redirect", return_value="ambient source redirect refused"), \
             mock.patch.object(gate.landing_targo, "capability_gap", side_effect=AssertionError("must refuse first")):
            self.assertEqual(gate.targo_unready(leg), "ambient source redirect refused")

    def test_untracked_local_caller_config_refuses_without_a_probe(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            local = root / "targo-trust" / ".cargo"
            local.mkdir(parents=True)
            with mock.patch.object(gate, "REPO_ROOT", root), \
                 mock.patch.object(gate, "lock_redirect", return_value=None):
                self.assertIsNone(gate.development_tool_name_resolution_problem({}))
                override = local / "config.toml"
                override.write_text('paths = ["../another-reader"]\n')
                self.assertIn("reviewed absent config", gate.development_tool_name_resolution_problem({}))
                override.unlink()
                local.rmdir()
                local.symlink_to(root, target_is_directory=True)
                self.assertIn("must not be redirected", gate.development_tool_name_resolution_problem({}))

    def test_native_target_runner_preflight_and_exact_case_count_remain_required(self):
        leg = fixtures.leg(id=development.TOOL_NAME_LEG, command=["targo", "--unverified", "test"])
        with mock.patch.object(gate, "leg_environment", return_value={}), \
             mock.patch.object(gate, "development_native_target_problem", return_value="configured target refused"), \
             mock.patch.object(gate.landing_targo, "capability_gap", side_effect=AssertionError("must refuse first")):
            self.assertEqual(gate.targo_unready(leg), "configured target refused")
        for passed, ignored, ok in ((4, 0, True), (0, 0, False), (3, 0, False), (4, 1, False), (5, 0, False)):
            summary = f"test result: ok. {passed} passed; 0 failed; {ignored} ignored; 0 measured; 0 filtered out;\n"
            self.assertEqual(gate.development_test_result(summary, 0, expected_count=development.TOOL_NAME_CASES)[0] == 0, ok)


class GrepBudgetTests(unittest.TestCase):
    def launches(self, environment):
        graph = fixtures.Fixture.graph()
        result = subprocess.CompletedProcess([], 2, b"", b"controlled grep refusal")
        with mock.patch.dict(os.environ, environment, clear=True), \
             mock.patch.object(ls.subprocess, "run", return_value=result) as run, \
             mock.patch.object(ls, "_folds_into_ascii", return_value=("\u017f",)):
            self.assertIsNone(ls._git_grep(graph, ["-l", "-z", "-F", "-e", "needle"], ["*.rs"]))
            ls.scan_escapes(graph)
            self.assertTrue(ls._ui_folds_into_ascii(graph, "tests/ui"))
        self.assertEqual(run.call_count, 3)
        return [call.args[0] for call in run.call_args_list]

    def test_all_selector_greps_obey_the_actual_held_share(self):
        for argv in self.launches({"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "2"}):
            self.assertIn("grep.threads=2", argv)
            self.assertEqual(argv[argv.index("grep.threads=2") - 1], "-c")

    def test_unmanaged_queries_use_the_measured_host_despite_a_caller_jobs_hint(self):
        # Git's per-logical-core pool, as every unmanaged plan measures the host
        # (LAND-GREP-ADMISSION-2): a serial query made `plan` outlast main's motion.
        for argv in self.launches({"CARGO_BUILD_JOBS": "128"}):
            self.assertIn("grep.threads=0", argv)
            self.assertEqual(argv[argv.index("grep.threads=0") - 1], "-c")
            self.assertNotIn("grep.threads=128", argv)
            self.assertNotIn("grep.threads=1", argv)

    def test_invalid_held_admission_never_launches_git(self):
        graph = fixtures.Fixture.graph()
        for value in ("", "0", "invalid"):
            with self.subTest(value=value), \
                 mock.patch.dict(os.environ, {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": value}, clear=True), \
                 mock.patch.object(ls.subprocess, "run") as run:
                with self.assertRaises(gate.host_budget.AdmissionInvalid):
                    ls._git_grep(graph, ["-l", "-F", "-e", "needle"], ["*.rs"])
                run.assert_not_called()

    def test_actual_result_population_is_unchanged_by_the_thread_ceiling(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            head = fixtures.make_repo(root, {"a.rs": 'const A: &str = "needle";\n',
                                            "binary.RS": "// \0needle\n",
                                            "space name.rs": "// needle\n",
                                            "not-rust.txt": "needle\n"}, {})
            graph = fixtures.Fixture.graph()
            graph.index.repo, graph.index.rev = str(root), head
            populations = []
            # Isolate the advertised budget, while retaining the actual Git
            # selected to create this repository. An empty PATH can select a
            # nonfunctional OS installer shim instead of that dependency.
            selected_path = os.environ.get("PATH", os.defpath)
            for environment in ({"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "1"},
                                {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "2"},
                                {}):  # unmanaged: Git's per-core pool
                with mock.patch.dict(os.environ, {"PATH": selected_path, **environment}, clear=True):
                    output = ls._git_grep(graph, ["-l", "-z", "-w", "-F", "-e", "needle"], [":(icase)*.rs"])
                self.assertIsNotNone(output)
                populations.append(set(ls._grep_listed(graph, output)))
            self.assertEqual(populations, [{"a.rs", "binary.RS", "space name.rs"}] * 3)


class MacroSpellingReuseTests(unittest.TestCase):
    @contextlib.contextmanager
    def repository(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            files = {
                "pkg/src/seed.rs": "macro_rules! seed { () => { mod item; } }\n",
                "pkg/src/first.rs": "macro_rules! wrap { () => { seed!(); } }\n",
                "pkg/src/late.rs": "macro_rules! later { () => { wrap!(); } }\n",
                "pkg/src/alias.rs": "use crate::later as renamed; macro_rules! final_wrap { () => { renamed!(); } }\n",
                "pkg/src/word_only.rs": "// seed\nmacro_rules! delayed { () => { later!(); } }\n",
                "pkg/src/preparsed.rs": "macro_rules! pre { () => { seed!(); } } macro_rules! has_late { () => { renamed!(); } }\n",
                "pkg/src/odd.r\u017f": "macro_rules! odd_wrap { () => { final_wrap!(); } }\n",
                "pkg/src/[literal]*.rs": "macro_rules! wildcard_name { () => { seed!(); } }\n",
            }
            head = fixtures.make_repo(root, files, {})
            yield lambda: ls.Graph(ls.TreeIndex.load(str(root), head), {"pkg": ls.Package("pkg", "pkg")}, {}, [], {}, {})

    def test_actual_fixed_point_matches_full_queries_and_keeps_late_calls(self):
        with self.repository() as fresh:
            baseline = fresh()
            with mock.patch.object(ls, "_macro_spelling_exclusions", return_value=[]):
                expected = ls._module_macro_spelling(baseline, {"pkg/src/seed.rs": ["seed"]})
            graph = fresh()
            queries = []
            original = ls._git_grep
            def query(g, args, paths):
                state = g.__dict__["_macro_spelling"]
                for path in paths[1:]:
                    name = path.removeprefix(":(exclude,literal)")
                    self.assertIn(name, state["calls"])
                    self.assertIn(name, state["spelt"].get(g.owner(name), set()))
                queries.append(list(paths))
                return original(g, args, paths)
            with mock.patch.object(ls, "_git_grep", side_effect=query):
                actual = ls._module_macro_spelling(graph, {"pkg/src/seed.rs": ["seed"]})
            self.assertEqual(actual, expected)
            self.assertTrue(any(len(paths) > 1 for paths in queries))
            self.assertIn("delayed", actual[1]["pkg/src/word_only.rs"])
            self.assertIn("odd_wrap", actual[1]["pkg/src/odd.r\u017f"])
            wrapped = ls._wrapped({"seed"}, actual[1].values())
            self.assertTrue({"later", "renamed", "final_wrap", "has_late", "delayed", "odd_wrap"} <= wrapped)
            helper = ls._macro_spelling_exclusions
            with mock.patch.object(ls, "_macro_spelling_exclusions",
                                   side_effect=lambda g, state: helper(g, state, byte_limit=100)):
                partial = ls._module_macro_spelling(fresh(), {"pkg/src/seed.rs": ["seed"]})
            self.assertEqual(partial, expected)

    def test_owner_change_and_unparsed_words_cannot_be_excluded(self):
        with self.repository() as fresh:
            graph = fresh()
            parsed, word = "pkg/src/first.rs", "pkg/src/word_only.rs"
            state = {"calls": {parsed: {}}, "spelt": {"old-owner": {parsed}, "pkg": {word}}}
            self.assertEqual(ls._macro_spelling_exclusions(graph, state), [])
            state["spelt"]["pkg"].add(parsed)
            self.assertEqual(ls._macro_spelling_exclusions(graph, state), [":(exclude,literal)" + parsed])
            graph.packages["pkg/src"] = ls.Package("pkg/src", "new-owner")
            self.assertEqual(ls._macro_spelling_exclusions(graph, state), [])

    def test_literal_exclusion_bytes_are_bounded_and_zero_is_full_baseline(self):
        with self.repository() as fresh:
            graph = fresh()
            names = list(graph.index.entries)
            state = {"calls": dict.fromkeys(names, {}), "spelt": {"pkg": set(names)}}
            self.assertEqual(ls._macro_spelling_exclusions(graph, state, byte_limit=0), [])
            result = ls._macro_spelling_exclusions(graph, state, byte_limit=100)
            self.assertTrue(result)
            self.assertLessEqual(sum(len(os.fsencode(path)) + 1 for path in result), 100)
            self.assertTrue(all(path.startswith(":(exclude,literal)") for path in result))

    def test_failed_later_query_still_refuses_the_complete_result(self):
        with self.repository() as fresh:
            graph = fresh()
            original = ls._git_grep
            count = [0]
            def query(*args):
                count[0] += 1
                return original(*args) if count[0] == 1 else None
            with mock.patch.object(ls, "_git_grep", side_effect=query):
                self.assertIsNone(ls._module_macro_spelling(graph, {"pkg/src/seed.rs": ["seed"]}))
            self.assertTrue(graph.__dict__["_macro_spelling"]["failed"])


class MacroWordPatternTests(unittest.TestCase):
    def test_only_bounded_ascii_identifiers_use_the_literal_union(self):
        self.assertEqual(ls._macro_word_patterns(["seed", "_", "A0"]), ["-E", "-e", "seed|_|A0"])
        for names in ([], ["\u00f1"], ["seed", "\u017f"], ["a.b"], ["x|y"], ["-e"], ["a\nb"]):
            with self.subTest(names=names):
                self.assertEqual(ls._macro_word_patterns(names),
                                 ["-F", *(arg for name in names for arg in ("-e", name))])
        self.assertEqual(ls._macro_word_patterns(["seed"], byte_limit=4), ["-F", "-e", "seed"])
        self.assertEqual(ls._macro_word_patterns(["seed"], byte_limit=5), ["-E", "-e", "seed"])

    def test_real_git_union_matches_fixed_words_at_every_boundary(self):
        names = ["a", "ab", "_", "seed", "seed_long", "A0"]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            # Prefixes, suffixes, punctuation, Unicode/invalid-byte boundaries,
            # binary NUL and mixed-case extensions all use Git's actual -w.
            tokens = ["a", "ab", "abc", "xa", "a0", "_", "__", "seed", "seed_long",
                      "seed_longer", "xseed", "seedx", "A0", "a0", "A00", "\u00f1seed", "seed\u00f1"]
            files = {f"cases/{i}.RS": text + "\n" for i, text in enumerate(tokens)}
            files.update({"space name.rs": "/*seed*/\n", "[literal]*.rs": "!ab!\n",
                          "no-match.rs": "z\n", "not-rust.txt": "seed\n"})
            fixtures.make_repo(root, files, {})
            for path, data in {"cases/binary.rs": b"\0seed\0", "cases/invalid.rs": b"\xffseed\xfe"}.items():
                (root / path).write_bytes(data)
            fixtures.git_in(root, "add", ".")
            fixtures.git_in(root, "commit", "-qm", "raw boundary fixtures")
            graph = fixtures.Fixture.graph()
            graph.index.repo = str(root)
            graph.index.rev = fixtures.git_in(root, "rev-parse", "HEAD").strip()
            fixed = ["-F", *(arg for name in names for arg in ("-e", name))]
            outputs = [ls._git_grep(graph, ["-l", "-z", "-w", *patterns], [":(icase)*.rs"])
                       for patterns in (fixed, ls._macro_word_patterns(names))]
            self.assertIsNotNone(outputs[0])
            self.assertEqual(outputs[0], outputs[1])

    def test_actual_fixed_point_and_callgraph_equal_original_fixed_queries(self):
        fixture = MacroSpellingReuseTests()
        with fixture.repository() as fresh:
            names = {"pkg/src/seed.rs": ["seed"]}
            with mock.patch.object(ls, "_macro_word_patterns",
                                   side_effect=lambda words: ["-F", *(a for n in words for a in ("-e", n))]):
                expected = ls._module_macro_spelling(fresh(), names)
            self.assertEqual(ls._module_macro_spelling(fresh(), names), expected)

    def test_union_query_failure_does_not_fall_back_to_a_success(self):
        fixture = MacroSpellingReuseTests()
        with fixture.repository() as fresh:
            with mock.patch.object(ls, "_git_grep", return_value=None) as query:
                self.assertIsNone(ls._module_macro_spelling(fresh(), {"pkg/src/seed.rs": ["seed"]}))
            self.assertEqual(query.call_count, 1)
            self.assertIn("-E", query.call_args.args[1])


class ValidationSelectionTests(unittest.TestCase):
    def test_every_program_this_module_imports_and_the_ledger_it_pins_select_it(self):
        # It drives land_select (audit_holds, scan_escapes, build_graph) and
        # land_gate (development_legs, cmd_run, cmd_push_rows), builds on
        # land_gate_test's fixtures, and BootstrapFixtureAuditTests read three
        # rows of the escape-audit ledger. A change to any of them must run it.
        root = Path(__file__).resolve().parents[2]
        imported = [Path(module.__file__).resolve().relative_to(root).as_posix()
                    for module in (development, gate, ls, fixtures)]
        self.assertEqual(sorted(imported), ["scripts/land_gate.py", "scripts/lib/land_development.py",
                                            "scripts/lib/land_select.py", "scripts/tests/land_gate_test.py"])
        for path in (*imported, ls.AUDITS_FILE, ls.LAND_ROWS_FILE, "scripts/tests/land_development_test.py"):
            with self.subTest(path=path):
                self.assertIn("scripts.tests.land_development_test", ls.validation_test_modules([path]))


if __name__ == "__main__":
    unittest.main()
