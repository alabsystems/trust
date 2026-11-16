#!/usr/bin/env python3
"""Bounded process-custody regressions; no compiler or SDK execution.

JOBSERVER_HARNESS_SOURCE may name the unchanged parent source for a RED control.
Only private start_new_session groups created by this test receive real signals.
"""
import importlib.util
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SOURCE = Path(os.environ.get('JOBSERVER_HARNESS_SOURCE',
                            Path(__file__).with_name('bootstrap_shim_jobserver_test.py')))
SPEC = importlib.util.spec_from_file_location('jobserver_harness', SOURCE)
HARNESS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(HARNESS)
REAL_POPEN = subprocess.Popen


class CleanupTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='jobserver-cleanup-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / 'home').mkdir()
        self.sdk = self.root / 'unused-sdk'

    def run_case(self, process, killpg):
        with mock.patch.object(HARNESS, 'SDK', self.sdk), \
             mock.patch.object(HARNESS.subprocess, 'Popen', return_value=process), \
             mock.patch.object(HARNESS.os, 'killpg', killpg):
            return HARNESS.run_one(self.root, 'case', self.sdk / 'bin/trustc', [],
                                   'cargo-pipe', controlled=False, root=self.root)

    def interrupted_case(self, error, *, finished=False, kill_error=None, reap_error=None):
        process = mock.Mock(pid=424242)
        process.wait.side_effect = [error, reap_error if reap_error is not None else 0]
        process.poll.return_value = 0 if finished else None
        group = {'descendant_live': True}

        def killpg(pid, sig):
            self.assertEqual((pid, sig), (process.pid, signal.SIGKILL))
            if kill_error is not None:
                raise kill_error
            group['descendant_live'] = False

        killer = mock.Mock(side_effect=killpg)
        with self.assertRaises(type(error)) as raised:
            self.run_case(process, killer)
        self.assertIs(raised.exception, error)
        self.assertEqual(process.wait.call_count, 2)
        process.wait.assert_any_call(timeout=15)
        process.wait.assert_any_call(timeout=5)
        process.poll.assert_not_called()
        killer.assert_called_once_with(process.pid, signal.SIGKILL)
        return group, raised.exception

    def test_timeout_kills_live_leader_group_and_reaps(self):
        group, _ = self.interrupted_case(subprocess.TimeoutExpired('owned', 15))
        self.assertFalse(group['descendant_live'])

    def test_timeout_kills_descendant_after_leader_finished(self):
        group, _ = self.interrupted_case(subprocess.TimeoutExpired('owned', 15), finished=True)
        self.assertFalse(group['descendant_live'])

    def test_interrupt_kills_descendant_after_leader_finished(self):
        group, _ = self.interrupted_case(KeyboardInterrupt('original'), finished=True)
        self.assertFalse(group['descendant_live'])

    def test_absent_group_still_reaps_and_preserves_timeout(self):
        self.interrupted_case(subprocess.TimeoutExpired('owned', 15),
                              kill_error=ProcessLookupError('already gone'))

    def test_signal_error_still_reaps_and_preserves_original(self):
        _, error = self.interrupted_case(KeyboardInterrupt('original'),
                                         kill_error=PermissionError('controlled failure'))
        self.assertTrue(any('process-group cleanup failed' in note
                            for note in error.__notes__))

    def test_reap_error_preserves_original_and_is_disclosed(self):
        _, error = self.interrupted_case(subprocess.TimeoutExpired('owned', 15),
                                         reap_error=subprocess.TimeoutExpired('cleanup', 5))
        self.assertTrue(any('child reap failed' in note for note in error.__notes__))

    def test_both_cleanup_errors_preserve_original(self):
        _, error = self.interrupted_case(KeyboardInterrupt('original'),
                                         kill_error=PermissionError('controlled failure'),
                                         reap_error=InterruptedError('controlled reap failure'))
        self.assertEqual(len(error.__notes__), 2)

    def test_popen_failure_does_not_signal_any_group(self):
        error = OSError('controlled spawn failure')
        with mock.patch.object(HARNESS, 'SDK', self.sdk), \
             mock.patch.object(HARNESS.subprocess, 'Popen', side_effect=error), \
             mock.patch.object(HARNESS.os, 'killpg') as killer:
            with self.assertRaises(OSError) as raised:
                HARNESS.run_one(self.root, 'case', self.sdk / 'bin/trustc', [],
                                 'cargo-pipe', controlled=False, root=self.root)
        self.assertIs(raised.exception, error)
        killer.assert_not_called()

    def test_normal_exit_does_not_signal_any_group(self):
        process = mock.Mock(pid=424242, returncode=0)
        process.wait.return_value = 0
        killer = mock.Mock()
        report = self.run_case(process, killer)
        self.assertEqual(report['exit_code'], 0)
        self.assertTrue(report['terminal_observed'])
        self.assertTrue(report['parent_fds_unchanged'])
        self.assertEqual(report['token_remains_hex'], '6a')
        process.wait.assert_called_once_with(timeout=15)
        process.poll.assert_not_called()
        killer.assert_not_called()

    @unittest.skipUnless(hasattr(os, 'fork'), 'requires Unix fork/process groups')
    def test_real_timeout_after_leader_exit_kills_owned_descendant(self):
        self.real_descendant_case(False)

    @unittest.skipUnless(hasattr(os, 'fork'), 'requires Unix fork/process groups')
    def test_real_interruption_after_leader_exit_kills_owned_descendant(self):
        self.real_descendant_case(True)

    def real_descendant_case(self, interrupt):
        # Child readiness is signaled only after fork. The child alone retains
        # stdout once its leader has been terminated/reaped; EOF observes its
        # actual exit without polling or signaling any unrelated process.
        source = '''import os, time
child = os.fork()
if child == 0:
    os.write(1, b"ready\\n")
    time.sleep(10)
    os._exit(0)
time.sleep(10)
'''
        process = REAL_POPEN([sys.executable, '-I', '-c', source],
                             stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                             stderr=subprocess.DEVNULL, start_new_session=True)
        original = KeyboardInterrupt('original owned interruption') if interrupt else None
        outer = self

        class WaitProxy:
            pid = process.pid
            first = True

            def poll(self):
                return process.poll()

            def wait(self, timeout=None):
                nonlocal original
                if not self.first:
                    return process.wait(timeout=timeout)
                self.first = False
                try:
                    process.wait(timeout=0.03)
                except subprocess.TimeoutExpired as timeout_error:
                    process.terminate()  # Our own immediate child only.
                    process.wait(timeout=2)
                    original = original if interrupt else timeout_error
                    raise original
                outer.fail('owned leader unexpectedly exited before the controlled timeout')

        descendant_finished = False
        try:
            ready, _, _ = select.select([process.stdout], [], [], 2)
            self.assertTrue(ready, 'owned descendant did not become ready')
            self.assertEqual(os.read(process.stdout.fileno(), 6), b'ready\n')
            proxy = WaitProxy()
            # Real group signal, only the PGID created immediately above.
            actual_killpg = os.killpg
            with self.assertRaises(KeyboardInterrupt if interrupt else subprocess.TimeoutExpired) as raised:
                self.run_case(proxy, actual_killpg)
            self.assertIs(raised.exception, original)
            self.assertEqual(process.returncode, -signal.SIGTERM)
            ready, _, _ = select.select([process.stdout], [], [], 0.5)
            self.assertTrue(ready, 'owned descendant survived cleanup after its leader exited')
            self.assertEqual(os.read(process.stdout.fileno(), 1), b'')
            descendant_finished = True
        finally:
            # This test owns this start_new_session group; never use a PID
            # obtained from an ambient process list or another worker.
            try:
                if not descendant_finished:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                process.wait(timeout=2)
            finally:
                process.stdout.close()


if __name__ == '__main__':
    unittest.main(verbosity=2)
