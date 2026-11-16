#!/usr/bin/env python3
"""Shipped frontend protocol controls, using the ordinary gate's actual probe."""
import base64
import hashlib
import json
from pathlib import Path
import runpy
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'qualify_targo_resource.py'
qualify = runpy.run_path(str(SCRIPT))['qualify']


class ShippedTargoResourceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve() / 'sdk'
        (self.root / 'bin').mkdir(parents=True)
        for name in ('trustc', 'rustc'):
            (self.root / 'bin' / name).write_text('retained compiler bytes\n')

    def frontend(self, response, *, mutate=False, action=None):
        program = '''import json, pathlib, sys
if sys.argv[1] == '--resource-capabilities':
    assert sys.argv[2] == '--'
    assert sys.argv[3] == '--unverified'
    assert sys.argv[4] in ('check', 'test')
    manifest = pathlib.Path(sys.argv[sys.argv.index('--manifest-path') + 1])
    assert manifest.is_file() and manifest.parent == pathlib.Path.cwd()
    MUTATE
    print(RESPONSE)
elif sys.argv[1:] in (['--unverified', '--version'], ['--version']):
    print('targo 0.0.0-fixture')
elif sys.argv[1:] == ['trust', 'doctor', '--format', 'json']:
    print('{"ready":true}')
else:
    raise SystemExit('unexpected invocation; no compiler may be started')
'''.replace('RESPONSE', repr(response)).replace(
            'MUTATE', action or (f"pathlib.Path({str(self.root / 'bin/trustc')!r}).write_text('changed compiler')" if mutate else 'pass'))
        # The fixture body sits outside bin/ (the qualifier inventories bin/targo, trustc and
        # rustc) and bin/targo is a /bin/sh launcher: a `#!` line cannot name an interpreter
        # whose path holds a space (atpkg's python lives under "Application Support"), and
        # the kernel then reports the launcher itself as missing.
        body = self.root.parent / 'targo-fixture.py'
        body.write_text(program)
        path = self.root / 'bin/targo'
        path.write_text(f'#!/bin/sh\nexec {shlex.quote(sys.executable)} {shlex.quote(str(body))} "$@"\n')
        path.chmod(0o755)
        return path

    def test_stale_frontend_passes_lane_and_doctor_but_not_resource_contract(self):
        path = self.frontend('{"version":2,"cpu_workers":true,"supports_invocation":true}')
        for args in (['--unverified', '--version'], ['trust', 'doctor', '--format', 'json']):
            self.assertEqual(subprocess.run([str(path), *args], capture_output=True).returncode, 0)
        result = qualify(self.root)
        self.assertFalse(result['passed'])
        self.assertIn('invalid capability response', result['refusal'])
        self.assertTrue(result['inputs_stable'])
        self.assertEqual(result['opening_cohort'], result['closing_cohort'])
        self.assertEqual(result['opening_qualifier'], result['closing_qualifier'])
        self.assertTrue(result['observations'][0]['capture_complete'])
        response = base64.b64decode(result['observations'][0]['stdout_base64'])
        self.assertEqual(json.loads(response)['version'], 2)

    def test_malformed_duplicate_untyped_unknown_and_old_replies_refuse(self):
        for response in ('not json', '[]', '{}',
                         '{"version":3,"cpu_workers":true,"supports_invocation":true,"supports_invocation":false}',
                         '{"version":true,"cpu_workers":true,"supports_invocation":true}',
                         '{"version":3,"cpu_workers":1,"supports_invocation":true}',
                         '{"version":3,"cpu_workers":true,"supports_invocation":1}',
                         '{"version":3,"cpu_workers":true,"supports_invocation":true,"extra":false}',
                         '{"version":3,"cpu_workers":false,"supports_invocation":true}',
                         '{"version":1,"cpu_workers":true,"supports_invocation":true}'):
            with self.subTest(response=response):
                self.frontend(response)
                self.assertFalse(qualify(self.root)['passed'])

    def test_typed_unsupported_is_recorded_as_fixed_without_any_execution_grant(self):
        for cpu in (False, True):
            self.frontend(json.dumps(dict(version=3, cpu_workers=cpu, supports_invocation=False)))
            result = qualify(self.root)
            self.assertTrue(result['passed'], result)
            self.assertEqual(result['opening_cohort'], result['closing_cohort'])
            self.assertEqual([row['supported_boundary'] for row in result['observations']], ['fixed', 'fixed'])
            self.assertEqual([row['command'][2] for row in result['observations']], ['check', 'test'])
            for row in result['observations']:
                self.assertEqual(row['argv'], [row['command'][0], '--resource-capabilities', '--', *row['command'][1:]])
                self.assertEqual(row['exit'], 0)
            self.assertIn('no compile', result['scope'])

    def test_native_response_is_observation_not_sdk_or_resource_authority(self):
        self.frontend('{"version":3,"cpu_workers":true,"supports_invocation":true}')
        result = qualify(self.root)
        self.assertTrue(result['passed'], result)
        self.assertEqual(result['observations'][0]['supported_boundary'], 'native-workers-v2')
        self.assertEqual(result['opening_cohort']['bin/targo']['sha256'],
                         hashlib.sha256((self.root / 'bin/targo').read_bytes()).hexdigest())

    def test_runtime_refusal_cannot_become_fixed_unsupported(self):
        self.frontend('{"version":3,"cpu_workers":true,"supports_invocation":true,"runtime_refusal":"paired SDK helper unavailable"}')
        result = qualify(self.root)
        self.assertFalse(result['passed'])
        self.assertIn('paired SDK helper unavailable', result['refusal'])
        self.assertNotIn('supported_boundary', result['observations'][0])

    def test_cohort_change_during_query_refuses(self):
        self.frontend('{"version":3,"cpu_workers":false,"supports_invocation":false}', mutate=True)
        result = qualify(self.root)
        self.assertFalse(result['passed'])
        self.assertIn('cohort changed', result['refusal'])

    def test_qualifier_source_change_during_query_refuses(self):
        replica = self.root.parent / 'qualifier/scripts'
        (replica / 'lib').mkdir(parents=True)
        for source in (SCRIPT, SCRIPT.with_name('build-slot'), SCRIPT.with_name('lib') / 'landing_targo.py'):
            target = replica / ('lib/landing_targo.py' if source.name == 'landing_targo.py' else source.name)
            shutil.copy2(source, target)
        helper = replica / SCRIPT.name
        self.frontend('{"version":3,"cpu_workers":false,"supports_invocation":false}',
                      action=f'p=pathlib.Path({str(helper)!r}); p.write_text(p.read_text()+"\\n# fixture edit\\n")')
        result = runpy.run_path(str(helper))['qualify'](self.root)
        self.assertFalse(result['passed'])
        self.assertEqual(result['opening_cohort'], result['closing_cohort'])
        self.assertNotEqual(result['opening_qualifier'], result['closing_qualifier'])

    def test_timeout_marks_stream_capture_incomplete_and_closes_books(self):
        self.frontend('{"version":3,"cpu_workers":false,"supports_invocation":false}',
                      action='import time; time.sleep(3)')
        result = qualify(self.root)
        self.assertFalse(result['passed'])
        self.assertTrue(result['inputs_stable'])
        self.assertIn('timed out', result['refusal'])
        self.assertFalse(result['observations'][0]['capture_complete'])
        self.assertNotIn('stdout_base64', result['observations'][0])

    def test_receipt_cannot_write_into_sdk_or_overwrite_an_epoch(self):
        self.frontend('{"version":3,"cpu_workers":false,"supports_invocation":false}')
        inside = self.root / 'receipt.json'
        result = subprocess.run([sys.executable, '-I', '-S', '-B', str(SCRIPT),
                                 '--sysroot', str(self.root), '--receipt', str(inside)], capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(inside.exists())
        outside = self.root.parent / 'receipt.json'
        command = [sys.executable, '-I', '-S', '-B', str(SCRIPT), '--sysroot', str(self.root), '--receipt', str(outside)]
        self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
        before = outside.read_bytes()
        self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)
        self.assertEqual(outside.read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
