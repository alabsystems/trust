#!/usr/bin/env python3
"""Hostile committed-tree controls for bounded Cargo landing inputs."""
import copy
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lib"))
import land_manifest as lm
import land_select as ls


class ManifestDeltaTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="land-manifest-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.files = {
            "Cargo.toml": '[workspace]\nmembers=["crates/*"]\ndefault-members=["crates/*"]\nresolver="2"\n',
            "Cargo.lock": 'version = 4\n\n[[package]]\nname="tool"\nversion="0.1.0"\n\n[[package]]\nname="jobs"\nversion="0.1.0"\n\n[[package]]\nname="other"\nversion="0.1.0"\n',
            "crates/tool/Cargo.toml": '[package]\nname="tool"\nversion="0.1.0"\n',
            "crates/jobs/Cargo.toml": '[package]\nname="jobs"\nversion="0.1.0"\n[features]\ndefault=["client"]\nclient=[]\n',
            "crates/other/Cargo.toml": '[package]\nname="other"\nversion="0.1.0"\n',
            "crates/tool/src/lib.rs": '#[test] fn t() {}\n',
            "crates/jobs/src/lib.rs": '#[test] fn t() {}\n',
            "crates/other/src/lib.rs": '#[test] fn t() {}\n',
        }
        self.git("init", "-q")
        self.base = self.commit(self.files)

    def git(self, *args):
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
        return subprocess.check_output(["git", "-c", "maintenance.auto=false", "-C", str(self.root), *args], env=env, stderr=subprocess.PIPE).decode().strip()

    def commit(self, files):
        for name, value in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(value)
        self.git("add", ".")
        self.git("commit", "-qm", "fixture", "--allow-empty")
        return self.git("rev-parse", "HEAD")

    def addition(self):
        new = copy.copy(self.files)
        new["crates/tool/Cargo.toml"] += '[dependencies]\njobs={path="../jobs",version="=0.1.0"}\n'
        new["Cargo.lock"] = new["Cargo.lock"].replace('name="tool"\nversion="0.1.0"', 'name="tool"\nversion="0.1.0"\ndependencies=["jobs"]')
        return new

    def scope(self, files):
        head = self.commit(files)
        graph = ls.build_graph(ls.TreeIndex.load(str(self.root), head))
        changed = ls.changed_paths(str(self.root), self.base, head)
        return graph, changed, lm.scoped_inputs(graph, self.base, changed)

    def test_exact_existing_local_edges_route_owner_and_feature_activation(self):
        graph, changed, impacts = self.scope(self.addition())
        self.assertEqual(impacts, {"Cargo.lock": {"crates/tool", "crates/jobs"}, "crates/tool/Cargo.toml": {"crates/tool", "crates/jobs"}})
        selection = ls.select(graph, self.base, changed)
        self.assertEqual(selection.everything, [])
        self.assertTrue(selection.per_crate["crates-tests"]["crates/tool"].selected)
        self.assertTrue(selection.per_crate["crates-tests"]["crates/jobs"].selected)
        self.assertFalse(selection.per_crate["crates-tests"]["crates/other"].selected)
        # A raw lock reader and an unresolved reader still see the exact path.
        self.assertTrue(ls._decide_inputs(selection, "raw", {"Cargo.lock"}, {"Cargo.lock"}, [], None, graph).selected)
        self.assertTrue(ls._decide_inputs(selection, "unknown", {ls.EVERYTHING}, {ls.EVERYTHING}, ["unknown"], None, graph).selected)

    def test_activated_dependency_reaches_its_other_consumers(self):
        # The new edge may change a shared feature instance. Never restrict the
        # impact to only the two changed manifest/lock owners.
        old = copy.copy(self.files)
        old["crates/other/Cargo.toml"] += '[dependencies]\njobs={path="../jobs",default-features=false}\n'
        self.base = self.commit(old)
        new = self.addition()
        new["crates/other/Cargo.toml"] = old["crates/other/Cargo.toml"]
        graph, changed, _ = self.scope(new)
        self.assertTrue(ls.select(graph, self.base, changed).per_crate["crates-tests"]["crates/other"].selected)

    def test_unknown_or_global_delta_keeps_global_selection(self):
        mutations = {
            "workspace": lambda f: f.__setitem__("Cargo.toml", f["Cargo.toml"].replace('resolver="2"', 'resolver="3"')),
            "feature": lambda f: f.__setitem__("crates/tool/Cargo.toml", f["crates/tool/Cargo.toml"] + '[features]\ndefault=[]\n'),
            "new-edge-features": lambda f: f.__setitem__("crates/tool/Cargo.toml", f["crates/tool/Cargo.toml"].replace('version="=0.1.0"', 'version="=0.1.0",features=["client"]')),
            "optional": lambda f: f.__setitem__("crates/tool/Cargo.toml", f["crates/tool/Cargo.toml"].replace('version="=0.1.0"', 'version="=0.1.0",optional=true')),
            "pin": lambda f: f.__setitem__("crates/tool/Cargo.toml", f["crates/tool/Cargo.toml"].replace('version="=0.1.0"', 'version="=0.2.0"')),
            "git-source": lambda f: f.__setitem__("crates/tool/Cargo.toml", f["crates/tool/Cargo.toml"].replace('path="../jobs"', 'git="https://example.invalid/jobs"')),
            "target-identity": lambda f: f.__setitem__("crates/jobs/Cargo.toml", f["crates/jobs/Cargo.toml"].replace('version="0.1.0"', 'version="0.2.0"')),
            "checksum": lambda f: f.__setitem__("Cargo.lock", f["Cargo.lock"].replace('name="jobs"', 'checksum="forged"\nname="jobs"')),
            "new-package": lambda f: f.__setitem__("Cargo.lock", f["Cargo.lock"] + '\n[[package]]\nname="new"\nversion="1"\n'),
            "duplicate-package": lambda f: f.__setitem__("Cargo.lock", f["Cargo.lock"] + '\n[[package]]\nname="jobs"\nversion="0.1.0"\n'),
            "extra-lock-edge": lambda f: f.__setitem__("Cargo.lock", f["Cargo.lock"].replace('dependencies=["jobs"]', 'dependencies=["jobs","other"]')),
            "wrong-lock-owner": lambda f: f.__setitem__("Cargo.lock", f["Cargo.lock"].replace('name="tool"\nversion="0.1.0"\ndependencies=["jobs"]', 'name="tool"\nversion="0.1.0"').replace('name="other"\nversion="0.1.0"', 'name="other"\nversion="0.1.0"\ndependencies=["jobs"]')),
            "lock-version": lambda f: f.__setitem__("Cargo.lock", f["Cargo.lock"].replace('version = 4', 'version = 3')),
            "malformed": lambda f: f.__setitem__("Cargo.lock", '[broken'),
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name):
                new = self.addition()
                mutate(new)
                graph, changed, impacts = self.scope(new)
                self.assertEqual(impacts, {})
                self.assertTrue(ls.select(graph, self.base, changed).everything)

    def test_no_lock_delta_and_unavailable_base_do_not_waive_manifests(self):
        new = self.addition()
        new["Cargo.lock"] = self.files["Cargo.lock"]
        graph, changed, impacts = self.scope(new)
        self.assertEqual(impacts, {})
        self.assertTrue(ls.select(graph, self.base, changed).everything)
        self.assertEqual(lm.scoped_inputs(graph, "not-a-revision", ["Cargo.lock", "crates/tool/Cargo.toml"]), {})

    def test_original_path_traversal_cannot_hide_symlink_or_untracked_parent(self):
        for prefix in ("untracked", "link"):
            with self.subTest(prefix=prefix):
                link = self.root / "crates/tool/link"
                if not link.is_symlink():
                    link.symlink_to("../../../foreign/deep")
                self.base = self.commit(self.files)
                new = self.addition()
                new["crates/tool/Cargo.toml"] = new["crates/tool/Cargo.toml"].replace('../jobs', prefix + '/../../jobs')
                graph, changed, impacts = self.scope(new)
                self.assertEqual(impacts, {})
                self.assertTrue(ls.select(graph, self.base, changed).everything)

    def test_transitive_feature_activation_reaches_unrelated_consumer(self):
        old = copy.copy(self.files)
        old["crates/leaf/Cargo.toml"] = '[package]\nname="leaf"\nversion="0.1.0"\n[features]\nactive=[]\n'
        old["crates/leaf/src/lib.rs"] = '#[test] fn t() {}\n'
        old["crates/jobs/Cargo.toml"] += '[dependencies]\nleaf={path="../leaf",default-features=false}\n'
        old["crates/jobs/Cargo.toml"] = old["crates/jobs/Cargo.toml"].replace('client=[]', 'client=["leaf/active"]')
        old["crates/other/Cargo.toml"] += '[dependencies]\nleaf={path="../leaf",default-features=false}\n'
        old["Cargo.lock"] += '\n[[package]]\nname="leaf"\nversion="0.1.0"\n'
        self.base = self.commit(old)
        new = copy.copy(old)
        new["crates/tool/Cargo.toml"] += '[dependencies]\njobs={path="../jobs",version="=0.1.0"}\n'
        new["Cargo.lock"] = new["Cargo.lock"].replace('name="tool"\nversion="0.1.0"', 'name="tool"\nversion="0.1.0"\ndependencies=["jobs"]')
        graph, changed, impacts = self.scope(new)
        self.assertIn("crates/leaf", impacts["Cargo.lock"])
        self.assertTrue(ls.select(graph, self.base, changed).per_crate["crates-tests"]["crates/other"].selected)

    def test_registry_git_and_target_build_dev_consumers_are_not_lost(self):
        for source in ("registry+https://example.invalid/index", "git+https://example.invalid/leaf#1234"):
            for table in ("dependencies", "build-dependencies", "dev-dependencies", 'target."cfg(windows)".dependencies'):
                with self.subTest(source=source, table=table):
                    old = copy.copy(self.files)
                    old["crates/jobs/Cargo.toml"] = old["crates/jobs/Cargo.toml"].replace('client=[]', 'client=["leaf/active"]')
                    old["crates/jobs/Cargo.toml"] += '[dependencies]\nleaf={version="1",optional=true}\n'
                    old["crates/other/Cargo.toml"] += f'[{table}]\nleaf={{version="1",default-features=false}}\n'
                    old["Cargo.lock"] = old["Cargo.lock"].replace('name="jobs"\nversion="0.1.0"', 'name="jobs"\nversion="0.1.0"\ndependencies=["leaf"]')
                    old["Cargo.lock"] += f'\n[[package]]\nname="leaf"\nversion="1.0.0"\nsource="{source}"\n'
                    self.base = self.commit(old)
                    new = copy.copy(old)
                    new["crates/tool/Cargo.toml"] += '[dependencies]\njobs={path="../jobs",version="=0.1.0"}\n'
                    new["Cargo.lock"] = new["Cargo.lock"].replace('name="tool"\nversion="0.1.0"', 'name="tool"\nversion="0.1.0"\ndependencies=["jobs"]')
                    graph, changed, impacts = self.scope(new)
                    self.assertIn("crates/other", impacts["Cargo.lock"])
                    self.assertTrue(ls.select(graph, self.base, changed).per_crate["crates-tests"]["crates/other"].selected)



class ExistingLocalLockRepairTests(unittest.TestCase):
    def setUp(self):
        self.fixture = ManifestDeltaTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        self.path = "src/tools/targo/Cargo.lock"
        self.files = dict(self.fixture.files)
        self.files.update({
            "crates/tool/Cargo.toml": '[package]\nname="tool"\nversion="0.1.0"\n[target.\'cfg(unix)\'.dependencies]\njobs={path="../jobs"}\n',
            "src/tools/targo/Cargo.toml": '[workspace]\nmembers=["crates/targo-core"]\n[package]\nname="targo"\nversion="0.1.0"\n',
            "src/tools/targo/src/lib.rs": 'pub fn driver() {}\n',
            "src/tools/targo/crates/targo-core/Cargo.toml": '[package]\nname="targo-core"\nversion="0.1.0"\n',
            "src/tools/targo/crates/targo-core/src/lib.rs": 'pub fn core() {}\n',
            "src/tools/targo/tests/local_git_source_cache.rs": '#[test] fn native_sources() {}\n',
        })
        self.files[self.path] = self.files["Cargo.lock"] + '\n[[package]]\nname="targo"\nversion="0.1.0"\n\n[[package]]\nname="targo-core"\nversion="0.1.0"\n'
        self.base = self.fixture.commit(self.files)

    def repair(self):
        files = dict(self.files)
        files[self.path] = files[self.path].replace('name="tool"\nversion="0.1.0"', 'name="tool"\nversion="0.1.0"\ndependencies=["jobs"]')
        return files

    def graph(self, files):
        head = self.fixture.commit(files)
        return ls.build_manifest_graph(ls.TreeIndex.load(str(self.root), head))

    def test_actual_committed_missing_edge_is_proved_without_narrowing_diagnostics(self):
        graph = self.graph(self.repair())
        self.assertTrue(lm.existing_local_lock_repair(graph, self.base, self.path))
        self.assertEqual(ls.classify(graph, self.path)[0], "everything")
        sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
        import land_development as development
        import land_gate as gate
        kind, why = ls.classify(graph, self.path)
        selected = ls.Selection(self.base, graph.index.rev, [self.path], [f"{self.path}: {why}"])
        scoped = development.scope(graph, selected)
        self.assertFalse(scoped.errors)
        self.assertTrue(scoped.local_git_import)
        # Native Targo now registers this lock path as a discovery candidate.
        # The immutable repair proof and unknown-input refusals below still
        # decide ownership; a candidate is not a successful scope judgment.
        self.assertTrue(development.has_declared_source_ownership(graph.index, [self.path], self.base))
        legs = gate.development_legs(graph, selected, [], 2)
        self.assertEqual({leg.id for leg in legs}, {development.LOCAL_GIT_CORE_LEG, development.LOCAL_GIT_FIXTURE_LEG})
        self.assertTrue(all(leg.force_run and not leg.diagnostic_only for leg in legs))
        selected.everything.append("unresolved foreign compiler reader")
        self.assertIn("unresolved foreign compiler reader", development.scope(graph, selected).errors)
        selected.changed.append("compiler/unowned/src/lib.rs")
        self.assertTrue(development.scope(graph, selected).errors)

    def test_inherited_version_requires_original_unique_workspace_package(self):
        base = dict(self.files)
        base['Cargo.toml'] += '[workspace.package]\nversion="0.1.0"\n'
        base['crates/tool/Cargo.toml'] = base['crates/tool/Cargo.toml'].replace('version="0.1.0"', 'version.workspace=true')
        self.base = self.fixture.commit(base)
        new = dict(base); new[self.path] = self.repair()[self.path]
        self.assertTrue(lm.existing_local_lock_repair(self.graph(new), self.base, self.path))
        new['Cargo.toml'] = new['Cargo.toml'].replace('version="0.1.0"', 'version="0.2.0"')
        self.assertFalse(lm.existing_local_lock_repair(self.graph(new), self.base, self.path))
        base['Cargo.toml'] = self.files['Cargo.toml']
        self.base = self.fixture.commit(base)
        new = dict(base); new[self.path] = self.repair()[self.path]
        self.assertFalse(lm.existing_local_lock_repair(self.graph(new), self.base, self.path))

    def test_external_identity_metadata_removal_or_undeclared_edges_refuse(self):
        changes = {
            "new-package": lambda s: s + '\n[[package]]\nname="new"\nversion="1"\n',
            "version": lambda s: s.replace('name="jobs"\nversion="0.1.0"', 'name="jobs"\nversion="0.2.0"'),
            "checksum": lambda s: s.replace('name="jobs"', 'checksum="forged"\nname="jobs"'),
            "source": lambda s: s.replace('name="jobs"', 'source="registry+https://example.invalid"\nname="jobs"'),
            "extra-edge": lambda s: s.replace('dependencies=["jobs"]', 'dependencies=["jobs","other"]'),
            "duplicate-edge": lambda s: s.replace('dependencies=["jobs"]', 'dependencies=["jobs","jobs"]'),
            "lock-version": lambda s: s.replace('version = 4', 'version = 3'),
        }
        for label, change in changes.items():
            with self.subTest(label=label):
                files = self.repair(); files[self.path] = change(files[self.path])
                self.assertFalse(lm.existing_local_lock_repair(self.graph(files), self.base, self.path))
        self.assertFalse(lm.existing_local_lock_repair(self.graph(self.files), self.base, self.path))

    def test_changed_manifest_workspace_configuration_and_indirection_refuse(self):
        for path, text in (
            ("crates/tool/Cargo.toml", self.files["crates/tool/Cargo.toml"] + '# owner changed\n'),
            ("crates/jobs/Cargo.toml", self.files["crates/jobs/Cargo.toml"] + '# target changed\n'),
            ("src/tools/targo/Cargo.toml", self.files["src/tools/targo/Cargo.toml"] + '# workspace changed\n'),
            (".cargo/config.toml", '[build]\nrustflags=["--cfg", "changed"]\n'),
        ):
            with self.subTest(path=path):
                files = self.repair(); files[path] = text
                self.assertFalse(lm.existing_local_lock_repair(self.graph(files), self.base, self.path))
        graph = self.graph(self.repair())
        graph.index.entries[self.path] = ("120000", graph.index.entries[self.path][1])
        self.assertFalse(lm.existing_local_lock_repair(graph, self.base, self.path))
        self.assertFalse(lm.existing_local_lock_repair(graph, "unknown-base", self.path))

    def test_existing_old_edge_cannot_be_removed_during_catchup(self):
        base = dict(self.files)
        base[self.path] = base[self.path].replace('name="other"\nversion="0.1.0"', 'name="other"\nversion="0.1.0"\ndependencies=["jobs"]')
        self.base = self.fixture.commit(base)
        self.assertFalse(lm.existing_local_lock_repair(self.graph(self.repair()), self.base, self.path))

    def test_symlink_dotdot_and_absolute_dependency_paths_never_prove_locality(self):
        for spelling in ('../alias/../jobs', '/crates/jobs', '../../outside/jobs'):
            with self.subTest(spelling=spelling):
                base = dict(self.files)
                base['crates/tool/Cargo.toml'] = base['crates/tool/Cargo.toml'].replace('../jobs', spelling)
                alias = self.root / 'crates/alias'
                if alias.is_symlink(): alias.unlink()
                os.symlink('jobs', alias)
                self.base = self.fixture.commit(base)
                new = dict(base)
                new[self.path] = self.repair()[self.path]
                self.assertFalse(lm.existing_local_lock_repair(self.graph(new), self.base, self.path))

if __name__ == "__main__":
    unittest.main()
