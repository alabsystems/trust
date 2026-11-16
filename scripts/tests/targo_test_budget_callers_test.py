#!/usr/bin/env python3
"""Inert command-plan regressions; never compile Rust or qualify an SDK."""
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile
import types
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[1]


def load(name, filename):
    module = types.ModuleType(name)
    module.__file__ = str(SCRIPTS / filename)
    sys.modules[name] = module
    exec(compile(Path(module.__file__).read_bytes(), module.__file__, 'exec'), module.__dict__)
    return module


api = load('budget_test_component', 'sdk_targo_component.py')
witness = load('budget_test_witness', 'sdk_targo_transport_witness.py')


class TargoTestBudgetCallers(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='inert-targo-plan-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.log = self.root / 'argv.jsonl'
        self.recorder = self.root / 'targo'
        record = ('import json,os,sys\n'
                  'with open(os.environ["INERT_TARGO_PLAN_LOG"],"a") as out:'
                  'out.write(json.dumps(sys.argv[1:])+"\\n")\n')
        self.recorder.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable)
                                 + ' -c ' + shlex.quote(record) + ' "$@"\n')
        self.recorder.chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.root) + os.pathsep + os.environ.get('PATH', ''),
                        INERT_TARGO_PLAN_LOG=str(self.log), PYTHONDONTWRITEBYTECODE='1')

    def recorded(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def assert_owned_budget(self, argv):
        self.assertEqual(argv[:5], ['--unverified', 'test', '--config', 'build.test-jobs=1', '--manifest-path'])
        self.assertEqual(argv.count('build.test-jobs=1'), 1)
        self.assertFalse(any(arg.startswith('--test-threads') for arg in argv))

    def test_bridge_lane_actual_shell_preserves_its_exact_test_selection(self):
        result = subprocess.run(['bash', str(SCRIPTS / 'trust_bridge_replay_lane.sh')],
                                env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(self.recorded()), 1)
        argv = self.recorded()[0]
        self.assert_owned_budget(argv)
        self.assertEqual(argv[argv.index('-p'):], ['-p', 'trust-clean', '--test', 'lean_clean_bridge'])

    def test_monitor_actual_helper_preserves_list_and_exact_ignored_selectors(self):
        source = (SCRIPTS / 'stage2_certified_monitor_e2e.sh').read_text()
        helper = re.search(r'^common_targo_test\(\) \{\n.*?^\}\n', source, re.M | re.S)
        self.assertIsNotNone(helper)
        invocation = re.search(r'^    common_targo_test "\$test_name" -- .*?\\$', source, re.M)
        self.assertIsNotNone(invocation)
        # Run the maintained helper and its actual E2E call, using only a
        # recorder in place of Targo. No test/SDK success is inferred from it.
        code = '\n'.join([
            'set -euo pipefail',
            'CLEAN_TARGO_ENV=(env)',
            'TARGO=' + shlex.quote(str(self.recorder)),
            'MANIFEST="/owned source/Cargo.toml"',
            'TARGET_DIR="/owned target"',
            'TARGO_TRUST_SHIPPED_FEATURES="faithful"',
            'test_name="tests::frozen_control"',
            helper.group(0),
            'common_targo_test -- --list',
            invocation.group(0).strip().removesuffix('\\').rstrip(),
        ])
        result = subprocess.run(['bash', '-c', code], env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = self.recorded(); self.assertEqual(len(calls), 2)
        for argv in calls:
            self.assert_owned_budget(argv)
            self.assertEqual(argv[argv.index('--features') + 1], 'faithful')
            self.assertIn('--locked', argv); self.assertIn('--offline', argv)
        self.assertEqual(calls[0][calls[0].index('--'):], ['--', '--list'])
        self.assertEqual(calls[1][calls[1].index('tests::frozen_control'):],
                         ['tests::frozen_control', '--', '--exact', '--ignored', '--nocapture'])

    def test_transport_producer_plans_only_test_budgets_and_keeps_native_refusals(self):
        subject, source, project = map(Path, ['/owned sdk', '/owned source', '/owned mini'])
        commands = witness.transport_commands(api, subject, source, project)
        self.assertEqual([row['name'] for row in commands], list(api.CONTROLS))
        for row in commands[:2]:
            self.assertEqual(len(row['argv']), 1)
            argv = row['argv'][0]
            self.assertEqual(argv[0], str(subject / 'bin/targo'))
            self.assert_owned_budget(argv[1:])
            self.assertEqual(argv[argv.index('-p'):], ['-p', 'jobserver_utils', '--lib',
                             'transport_witness_tests::' + row['name'], '--', '--exact', '--nocapture'])
        self.assertEqual(commands[2]['argv'][0][-2:], ['positive', str(subject / 'bin/trustc')])
        self.assertEqual([argv[-2:] for argv in commands[3]['argv']],
                         [[mode, str(subject / 'bin/trustc')] for mode in ['missing', 'malformed']])
        for row in commands[2:]:
            for argv in row['argv']:
                self.assertEqual(argv[1:3], ['--unverified', 'run'])
                self.assertNotIn('--config', argv)

    def test_witness_pins_the_exact_independent_validator(self):
        self.assertEqual(witness.VALIDATOR_SHA256, api.sha256((SCRIPTS / 'sdk_targo_component.py').read_bytes()))
        self.assertEqual(witness.owner().CONTROLS, api.CONTROLS)
        with mock.patch.object(witness, 'VALIDATOR_SHA256', 'f' * 64):
            with self.assertRaisesRegex(ValueError, 'native validator source changed'):
                witness.owner()


if __name__ == '__main__':
    unittest.main()
