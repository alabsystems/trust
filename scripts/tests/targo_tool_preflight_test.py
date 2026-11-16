#!/usr/bin/env python3
"""Selected frontend preparation never becomes compiler-source readiness."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

xpy = load('tool_preflight_xpy', ROOT / 'x.py')
preflight = load('tool_preflight_owner', ROOT / 'tools/preflight.py')
prepare = load('tool_preparation_owner', ROOT / 'scripts/recreate_bootstrap.py')

class ToolPreflight(unittest.TestCase):
    def test_exact_recipe_only(self):
        recipe = ['build', '--stage', '1', '-j', '6', 'targo-build-tool']
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder)
            self.assertEqual(xpy._trust_preflight_tool_args(recipe,root), [])
            marker=root/'build/tool-source-preparation/targo-build-tool.json'
            marker.parent.mkdir(parents=True)
            marker.write_text('{}')
            self.assertEqual(xpy._trust_preflight_tool_args(recipe,root), ['--selected-tool', 'targo-build-tool'])
            self.assertFalse(preflight.validate_standalone_tool_sources(root,preflight.Report(False)))
            for changed in [recipe + ['compiler/rustc'], ['install'] + recipe[1:],
                            recipe[:-1] + ['compiler/rustc'], recipe + ['--set', 'x=y'],
                            ['build', '--stage', '2'] + recipe[3:]]:
                self.assertEqual(xpy._trust_preflight_tool_args(changed,root), [])

    def fixture(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name).resolve()
        for relative in ['src/bootstrap', 'src/tools/targo']:
            directory = root / relative
            directory.mkdir(parents=True)
            (directory / 'Cargo.toml').write_text('[package]\nname="fixture"\n')
            (directory / 'Cargo.lock').write_text('version = 3\n')
        inspector = root / 'inspector'
        inspector.write_text('actual test-bound inspector bytes')
        document = {'version': 1, 'packages': [{'manifest_path': str(root / 'src/tools/targo/Cargo.toml')}]}
        success = types.SimpleNamespace(returncode=0, stdout=json.dumps(document).encode(), stderr=b'')
        with mock.patch.object(prepare.subprocess, 'run', return_value=success):
            prepare.inspect_tool_source_graph(root, 'targo-build-tool', inspector)
        return root, success

    def test_reinspection_required_and_changed_lock_refused(self):
        root, success = self.fixture()
        with mock.patch.object(preflight.subprocess, 'run', return_value=success) as run:
            self.assertTrue(preflight.validate_standalone_tool_sources(root, preflight.Report(False)))
            self.assertEqual(run.call_count, 2)
        (root / 'src/bootstrap/Cargo.lock').write_text('changed')
        with mock.patch.object(preflight.subprocess, 'run') as run:
            self.assertFalse(preflight.validate_standalone_tool_sources(root, preflight.Report(False)))
            run.assert_not_called()

    def test_metadata_firstparty_and_changed_inspector_refused(self):
        root, _ = self.fixture()
        dependency = root / 'first-party/required/Cargo.toml'
        dependency.parent.mkdir(parents=True)
        dependency.write_text('[package]')
        reply = types.SimpleNamespace(returncode=0, stderr=b'', stdout=json.dumps({
            'version': 1, 'packages': [{'manifest_path': str(dependency)}]}).encode())
        with mock.patch.object(preflight.subprocess, 'run', return_value=reply):
            self.assertFalse(preflight.validate_standalone_tool_sources(root, preflight.Report(False)))
        (root / 'inspector').write_text('changed')
        with mock.patch.object(preflight.subprocess, 'run') as run:
            self.assertFalse(preflight.validate_standalone_tool_sources(root, preflight.Report(False)))
            run.assert_not_called()

    def test_only_absent_unrelated_firstparty_deferred(self):
        output = '-'+ 'a'*40 + ' first-party/clean\n-' + 'b'*40 + ' library/required\n'
        report = preflight.Report(False)
        with mock.patch.object(preflight, 'run', return_value=(0, output, '')):
            preflight.check_submodules(Path('/fixture'), report, deferred_first_party=True)
        self.assertTrue(any('unrelated source deferred' in f.title for f in report.findings))
        self.assertTrue(any(f.severity == preflight.FAIL for f in report.findings))

if __name__ == '__main__':
    unittest.main()
