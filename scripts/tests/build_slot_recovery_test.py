#!/usr/bin/env python3
"""Real-lock recovery controls in private fixtures; no machine-domain changes."""
import fcntl
import json
import importlib.machinery
import importlib.util
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
from build_slot_test import isolate_resource_environment

GATE = Path(__file__).resolve().parents[1] / 'build-slot'
LAUNCHER = r'''
import importlib.machinery, importlib.util, pathlib, sys
loader = importlib.machinery.SourceFileLoader('recovery_gate', sys.argv[1])
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
root = pathlib.Path(sys.argv[2])
gate.NCPU = gate.MEASURED_NCPU = 12
gate.ADOPTION_DIR = str(root / 'adopted')
gate.cpu_capacity_directory = lambda: str(root / 'native')
gate.available_gib = lambda: 128
gate.worktree_lock_path = lambda: str(root / 'worktree.lock')
try:
    sys.exit(gate.main(sys.argv[3:]))
except gate.AdmissionTimeout:
    print('admission wait timed out; no command was started', file=sys.stderr)
    sys.exit(2)
except gate.CpuBridgeUnavailable as error:
    print('CPU admission refused: ' + str(error), file=sys.stderr)
    sys.exit(2)
'''


class RecoveryTests(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        self.tmp = tempfile.TemporaryDirectory(prefix='build-slot-recovery-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.pool = self.root / 'legacy'
        self.pool.mkdir(mode=0o700)
        self.native = self.root / 'native'
        self.native.mkdir(mode=0o700)
        rows = ['trust-build-cpu-v1 slots=12']
        for i in range(12):
            p = self.native / f'slot-{i:08x}'
            p.touch(mode=0o600)
            m = p.stat()
            rows.append(f'slot={i} dev={m.st_dev} ino={m.st_ino}')
        (self.native / 'pool').write_text('\n'.join(rows) + '\n')
        (self.native / 'pool').chmod(0o600)
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(('ATERM_', 'BUILD_SLOT_', 'TARGO_'))
                    and k not in ('CARGO_BUILD_JOBS', 'BUILD_SLOTS')}
        self.env.update(BUILD_SLOT_DIR=str(self.pool), BUILD_SLOTS='3', BUILD_SLOT_MEM_GB='1')
        self.targo = self.root / 'targo'
        program = self.root / 'fixture.py'
        program.write_text("import json,sys\nfrom pathlib import Path\n"
                           "if '--resource-capabilities' in sys.argv:\n"
                           " print(json.dumps(dict(version=3,cpu_workers=True,supports_invocation=True)))\n"
                           "else:\n Path(sys.argv[-1]).touch()\n")
        self.targo.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable)
                              + ' -I -B ' + shlex.quote(str(program)) + ' "$@"\n')
        self.targo.chmod(0o700)

    def invoke(self, *options, native=False, name='started', env=None, delay=0):
        marker = self.root / name
        command = ([str(self.targo), '--unverified', 'test', str(marker)] if native else
                   [sys.executable, '-c', 'from pathlib import Path; import sys,time; time.sleep(float(sys.argv[2])); Path(sys.argv[1]).touch()', str(marker), str(delay)])
        result = subprocess.run([sys.executable, '-B', '-c', LAUNCHER, str(GATE), str(self.root),
                                 *options, '--', *command], cwd=self.root, env=env or self.env,
                                capture_output=True, text=True, timeout=5)
        return result, marker

    def lock(self, path, row=None):
        fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
        if row is not None:
            os.write(fd, json.dumps(row).encode())
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.addCleanup(os.close, fd)
        return fd

    def unlocked(self, path):
        fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
        try:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return True
            except BlockingIOError:
                return False
        finally:
            os.close(fd)

    def assert_released(self, held=()):
        self.assertFalse(list((self.pool / 'admission').glob('wait-*')))
        self.assertTrue(self.unlocked(self.root / 'worktree.lock'))
        self.assertTrue(self.unlocked(self.pool / 'admission.lock'))
        for slot in range(3):
            self.assertEqual(self.unlocked(self.pool / f'slot-{slot}'), slot not in held)

    def test_device_change_refuses_without_rewriting_or_waiting(self):
        manifest = self.native / 'pool'
        before_inodes = [p.stat().st_ino for p in sorted(self.native.glob('slot-*'))]
        text = manifest.read_text()
        dev = (self.native / 'slot-00000000').stat().st_dev
        text = text.replace(f'dev={dev} ', f'dev={dev + 1} ')
        manifest.write_text(text)
        for native in (False, True):
            with self.subTest(native=native):
                result, marker = self.invoke('--cpus', '1', native=native)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn(f'expected dev={dev + 1}', result.stderr)
                self.assertIn(f'observed dev={dev}', result.stderr)
                self.assertIn('machine authority recovery is required', result.stderr)
                self.assertFalse(marker.exists())
        self.assertEqual(manifest.read_text(), text)
        self.assertEqual([p.stat().st_ino for p in sorted(self.native.glob('slot-*'))], before_inodes)
        self.assert_released()

    def test_missing_manifest_refuses_without_creating_or_waiting(self):
        (self.native / 'pool').unlink()
        result, marker = self.invoke('--cpus', '1')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('native CPU accounting unavailable', result.stderr)
        self.assertFalse((self.native / 'pool').exists())
        self.assertFalse(marker.exists())
        self.assert_released()

    def test_native_timeout_releases_barrier_and_preserves_legacy_holder(self):
        peer = self.lock(self.pool / 'slot-0', dict(cpu_mode='fixed-v1', cpu_budget=2,
                         lease_id='a' * 32, pool_slots=3))
        # The v2 root cannot bypass this old participant despite free native slots.
        result, marker = self.invoke('--wait-timeout', '.3', native=True)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('legacy CPU drain', result.stderr)
        self.assertIn('admission wait timed out', result.stderr)
        self.assertFalse(marker.exists())
        self.assert_released(held=(0,))
        # Caller explicitly chooses a separate fixed request after the refusal.
        result, marker = self.invoke('--cpus', '1', '--wait-timeout', '2', name='fixed')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(marker.exists())
        self.assert_released(held=(0,))
        self.assertEqual(os.fstat(peer).st_ino, (self.pool / 'slot-0').stat().st_ino)

    def test_fixed_timeout_retires_ticket_and_keeps_peer_locks(self):
        for i in range(3):
            self.lock(self.pool / f'slot-{i}', dict(cpu_mode='fixed-v1', cpu_budget=1,
                      lease_id=str(i) * 32, pool_slots=3))
        result, marker = self.invoke('--cpus', '1', '--wait-timeout', '.2')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('admission wait timed out', result.stderr)
        self.assertFalse(marker.exists())
        self.assert_released(held=(0, 1, 2))

    def test_native_timeout_releases_transferred_fences_after_runtime_contention(self):
        runtime = self.pool / 'runtime-v2'
        runtime.mkdir(mode=0o700)
        for i in range(3):
            self.lock(runtime / f'slot-{i}', {})
        result, marker = self.invoke('--wait-timeout', '.2', native=True)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('admission wait timed out', result.stderr)
        self.assertFalse(marker.exists())
        self.assert_released()
        self.assertFalse(list((runtime / 'admission').glob('wait-*')))
        for i in range(3):
            self.assertFalse(self.unlocked(runtime / f'slot-{i}'))

    def test_timeout_does_not_bound_the_admitted_child(self):
        result, marker = self.invoke('--cpus', '1', '--wait-timeout', '2', delay=2.2)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(marker.exists())
        self.assert_released()

    def test_main_accounting_refusal_closes_fixed_claims_without_process_exit(self):
        loader = importlib.machinery.SourceFileLoader('recovery_in_process', str(GATE))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        gate = importlib.util.module_from_spec(spec)
        loader.exec_module(gate)
        (self.native / 'pool').unlink()
        with mock.patch.dict(os.environ, self.env, clear=True), \
             mock.patch.object(gate, 'NCPU', 12), \
             mock.patch.object(gate, 'MEASURED_NCPU', 12), \
             mock.patch.object(gate, 'ADOPTION_DIR', str(self.root / 'adopted')), \
             mock.patch.object(gate, 'cpu_capacity_directory', return_value=str(self.native)), \
             mock.patch.object(gate, 'available_gib', return_value=128), \
             mock.patch.object(gate, 'worktree_lock_path', return_value=str(self.root / 'worktree.lock')), \
             mock.patch.object(gate.subprocess, 'Popen') as child:
            with self.assertRaises(gate.CpuBridgeUnavailable):
                gate.main(['--cpus', '1', '--', 'must-not-start'])
            child.assert_not_called()
        self.assert_released()

    def test_nested_and_adopted_timeout_refuse_before_admission(self):
        result, marker = self.invoke('--wait-timeout', '1', env=dict(self.env, BUILD_SLOT_HELD='1'))
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('fresh admission outside the held slot', result.stderr)
        self.assertFalse(marker.exists())
        result = subprocess.run([sys.executable, '-B', '-c', LAUNCHER, str(GATE), str(self.root),
                                 '--wait-timeout', '1', 'adopt', str(os.getpid())],
                                cwd=self.root, env=self.env, capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('already running adopted job', result.stderr)
        self.assertFalse(list(self.pool.iterdir()))


if __name__ == '__main__':
    unittest.main()
