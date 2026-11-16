"""Pure and inert Linux child fixtures only; no compiler/producer/admission."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import selectors
import signal
import socket
import sys
import tempfile
import time
import types
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'scripts/seed_custody_source.py'
module = types.ModuleType('fixture_source_loader')
module.__file__ = str(BASE)
exec(compile(BASE.read_bytes(), str(BASE), 'exec', dont_inherit=True), module.__dict__)
HASHES = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
          for p in (ROOT / 'scripts').glob('*.py')}
loader = module.BoundSourceLoader(ROOT, HASHES)
commands = loader.module('fixture_observed_commands', ROOT / 'scripts/seed_observed_commands.py')
events = loader.module('fixture_observed_events', ROOT / 'scripts/seed_observed_events.py')
io = commands.io
# A dedicated runner can shorten this fixture owner, never extend its cap.
# Ordinary unittest discovery also gets one finite endpoint at import time.
UNIT_END = min(time.monotonic() + 165,
               float(os.environ.get('P03_TEST_ORIGINAL_END', 'inf')))


class CustodyTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='p03-', dir='/tmp')
        self.root = Path(self.temporary.name)
        self.runners, self.observers = [], []

    def tearDown(self):
        # This fixture supervisor holds its own original finite unit endpoint.
        # It retires ONLY exact child handles created by this test, with pidfds.
        for runner in self.runners:
            children = {id(c): c for c in [*runner.active.values(), *runner.quarantine.values()]}
            for child in children.values():
                if child.child is not None and child.child.returncode is None:
                    fd = child.pidfd
                    own = fd is None
                    if own:
                        fd = os.pidfd_open(child.child.pid, 0)
                    try:
                        try:
                            signal.pidfd_send_signal(fd, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        with selectors.DefaultSelector() as wait:
                            wait.register(fd, selectors.EVENT_READ)
                            self.assertTrue(wait.select(io.remaining(UNIT_END)))
                        child.child.wait(timeout=io.remaining(UNIT_END))
                    finally:
                        if own:
                            os.close(fd)
                child.close_handles()
        for observer in self.observers:
            for child in observer.active.values():
                for name in ('pidfd', 'executable_fd', 'launcher_fd'):
                    if child.get(name) is not None:
                        os.close(child[name])
        self.temporary.cleanup()

    def runner(self, duration=4, cleanup=6, emit=None):
        started = time.monotonic()
        work_end, cleanup_end = min(started + duration, UNIT_END - 2), min(started + cleanup, UNIT_END - 1)
        identity = io.process(os.getpid())
        observer = events.AuxiliaryObserver(worker_pid=os.getpid(), worker_start=identity['start'],
            cgroup=identity['cgroup'], started=started, work_end=work_end, cleanup_end=cleanup_end, spool_root=self.root / f'logs-{len(self.runners)}')
        self.observers.append(observer)
        runner = commands.ObservedCommands(started=started, work_end=work_end, cleanup_end=cleanup_end,
            spool_root=self.root / f'logs-{len(self.runners)}', emit=emit or observer.accept)
        self.runners.append(runner)
        return runner, observer

    def child(self, runner, body, *, maximum=65536, seconds=2, environment=None):
        return runner.open_object_reader('native-resource', 'seed_native_resources.query',
            ['/usr/bin/python3', '-I', '-S', '-B', '-c', body], self.root,
            environment or {'PATH': '/usr/bin:/bin', 'LC_ALL': 'C'}, maximum=maximum, seconds=seconds)

    def test_01_real_gated_child_parent_fd_and_complete_chunks(self):
        runner, observer = self.runner()
        child = self.child(runner, 'import sys;sys.stdout.buffer.write(b"alpha\\nbeta")')
        self.assertIsNotNone(child.pidfd)
        self.assertIsNotNone(observer.active[0]['pidfd'])
        self.assertIsNotNone(observer.active[0]['executable_fd'])
        self.assertEqual(child.read_object_line(), b'alpha\n')
        self.assertEqual(child.read_object_exact(4), b'beta')
        row = child.finish_observed_child()
        self.assertEqual(row['returncode'], 0)
        self.assertEqual(runner.read_output(row), b'alpha\nbeta')
        self.assertEqual([json.loads(b)['kind'] for b in observer.chunks],
                         ['aux-issued', 'aux-start', 'aux-go', 'aux-exit'])
        self.assertFalse(observer.finish(runner.finish())['scope_closed'])

    def test_02_stderr_is_bounded_separately_and_combined(self):
        runner, observer = self.runner()
        child = self.child(runner, 'import os;os.write(1,b"out");os.write(2,b"err")', maximum=6)
        row = child.finish_observed_child()
        self.assertEqual(runner.read_output(row), b'out')
        self.assertEqual(runner.read_output(row, 'stderr'), b'err')
        self.assertEqual(observer.finish(runner.finish())['chunks'], 4)

    def test_03_live_overflow_keeps_exact_cap_and_poison(self):
        runner, observer = self.runner()
        child = self.child(runner, 'import os,time;os.write(1,b"x"*8192);time.sleep(30)', maximum=1024)
        with self.assertRaises(io.CustodyFailure):
            child.finish_observed_child()
        self.assertTrue(runner.poisoned)
        self.assertEqual(child.stdout.length, 1024)
        self.assertTrue(child.stdout.truncated)
        self.assertTrue(child.reaped)
        self.assertTrue(observer.poisoned)
        with self.assertRaises(io.Refusal):
            runner.finish()

    def test_04_combined_stream_cap_is_not_twice_per_stream(self):
        runner, _ = self.runner()
        child = self.child(runner, 'import os;os.write(1,b"a"*600);os.write(2,b"b"*600)', maximum=1000)
        with self.assertRaises(io.CustodyFailure):
            child.finish_observed_child()
        self.assertEqual(child.stdout.length + child.stderr.length, 1000)

    def test_05_original_work_timeout_uses_only_original_cleanup(self):
        runner, observer = self.runner(duration=.3, cleanup=1)
        cleanup_end = runner.cleanup_end
        child = self.child(runner, 'import time;time.sleep(30)', seconds=.05)
        with self.assertRaises(io.CustodyFailure):
            child.read_object_exact(1)
        self.assertEqual(runner.cleanup_end, cleanup_end)
        self.assertTrue(child.reaped)
        self.assertLess(time.monotonic(), cleanup_end)
        self.assertTrue(observer.poisoned)

    def test_06_already_expired_work_cannot_spawn_or_regain_finish(self):
        runner, _ = self.runner(duration=.02, cleanup=1)
        time.sleep(.03)
        with mock.patch.object(commands.subprocess, 'Popen', side_effect=AssertionError('must not spawn')):
            with self.assertRaises(io.CustodyFailure):
                self.child(runner, 'pass')
        self.assertTrue(runner.poisoned)
        with self.assertRaises(io.Refusal):
            runner.finish()

    def test_07_pidfd_acquisition_failure_denies_target_and_keeps_handle(self):
        runner, observer = self.runner()
        marker = self.root / 'must-not-run'
        with mock.patch.object(io.os, 'pidfd_open', side_effect=OSError('injected pidfd failure')):
            with self.assertRaises(io.CustodyFailure):
                self.child(runner, f'from pathlib import Path;Path({str(marker)!r}).write_text("bad")')
        self.assertFalse(marker.exists())
        self.assertIn(0, runner.quarantine)
        self.assertIsNotNone(runner.quarantine[0].child)
        self.assertIsNone(runner.quarantine[0].pidfd)
        self.assertEqual(observer.quarantined[0]['reported_pid'],runner.quarantine[0].child.pid)
        self.assertIsNone(observer.quarantined[0]['observed_start'])
        self.assertTrue(observer.poisoned)
        self.assertTrue(runner.poisoned)

    def test_08_parent_pidfd_failure_cannot_ack_or_release_gate(self):
        runner, observer = self.runner()
        original, calls = os.pidfd_open, []
        marker = self.root / 'must-not-run'
        def second_fails(pid, flags=0):
            calls.append(pid)
            if len(calls) == 2:
                raise OSError('parent pidfd injected failure')
            return original(pid, flags)
        with mock.patch.object(io.os, 'pidfd_open', side_effect=second_fails):
            with self.assertRaises(io.CustodyFailure):
                self.child(runner, f'from pathlib import Path;Path({str(marker)!r}).write_text("bad")')
        self.assertFalse(marker.exists())
        self.assertTrue(observer.poisoned)
        self.assertTrue(runner.poisoned)
        self.assertIn(0, observer.active)

    def test_09_preexisting_auto_reap_refuses_before_spawn(self):
        previous = signal.signal(signal.SIGCHLD, signal.SIG_IGN)
        try:
            with mock.patch.object(commands.subprocess, 'Popen', side_effect=AssertionError('must not spawn')):
                with self.assertRaises(io.Refusal):
                    self.runner()
        finally:
            signal.signal(signal.SIGCHLD, previous)

    def test_10_expired_cleanup_does_not_signal_or_append_time(self):
        runner, _ = self.runner()
        child = self.child(runner, 'import time;time.sleep(30)')
        runner.cleanup_end = time.monotonic() - 1  # Adverse expired original context.
        with mock.patch.object(signal, 'pidfd_send_signal') as send:
            child.abort('injected original expiry')
        self.assertFalse(send.called)
        self.assertIn(0, runner.quarantine)
        self.assertFalse(child.reaped)

    def test_11_request_bytes_are_retained_not_candidate_asserted(self):
        runner, observer = self.runner()
        child = self.child(runner, 'import os;raw=os.read(0,4);os.write(1,raw[::-1])')
        child.write_input(b'abcd')
        self.assertEqual(child.read_object_exact(4), b'dcba')
        row = child.finish_observed_child()
        self.assertEqual(Path(row['stdin']['path']).read_bytes(), b'abcd')
        self.assertEqual(row['stdin']['sha256'], hashlib.sha256(b'abcd').hexdigest())
        self.assertEqual(observer.finish(runner.finish())['chunks'], 4)

    def test_12_short_object_is_refused_and_poisoned(self):
        runner, _ = self.runner()
        child = self.child(runner, 'import os;os.write(1,b"abc")')
        with self.assertRaises(io.CustodyFailure):
            child.read_object_exact(4)
        self.assertTrue(runner.poisoned)

    def test_13_object_header_limit_is_live(self):
        runner, _ = self.runner()
        child = self.child(runner, 'import os,time;os.write(1,b"a"*100);time.sleep(30)')
        with self.assertRaises(io.CustodyFailure):
            child.read_object_line(16)
        self.assertTrue(child.reaped)

    def test_14_ack_failure_sticks_and_denies_inner_exec(self):
        chunks = []
        def reject_start(chunk):
            chunks.append(chunk)
            if chunk['rows'][0]['kind'] == 'aux-start':
                raise ValueError('original parent rejects start')
        runner, _ = self.runner(emit=reject_start)
        marker = self.root / 'must-not-run'
        with self.assertRaises(io.CustodyFailure):
            self.child(runner, f'from pathlib import Path;Path({str(marker)!r}).write_text("bad")')
        self.assertFalse(marker.exists())
        self.assertTrue(runner.poisoned)
        with self.assertRaises(io.Refusal):
            runner.finish()

    def test_15_budget_failure_before_popen_is_irreversible(self):
        runner, _ = self.runner()
        runner.account.commands = io.MAX_COMMANDS
        with mock.patch.object(commands.subprocess, 'Popen', side_effect=AssertionError('must not spawn')):
            with self.assertRaises(io.CustodyFailure):
                self.child(runner, 'pass')
        with self.assertRaises(io.Refusal):
            runner.finish()

    def test_16_invalid_role_or_callsite_poisons(self):
        runner, _ = self.runner()
        with self.assertRaises(io.CustodyFailure):
            runner.open_object_reader('git', 'candidate.claim', ['/usr/bin/true'], self.root, {}, maximum=1)
        self.assertTrue(runner.poisoned)

    def test_17_more_than_512_chunks_are_preserved_and_incomplete_refuses(self):
        runner, observer = self.runner(duration=8, cleanup=10)
        spec = io.validate_request('native-resource', 'seed_native_resources.query',
                                   ['/usr/bin/true'], self.root, {}, 1, 1)
        for number in range(600):
            runner.account.command()
            runner.event('aux-issued', command=number, spec=spec,
                         command_end=min(time.monotonic() + 1, runner.work_end))
        self.assertEqual(len(observer.chunks), 600)
        self.assertEqual(observer.account.commands, 600)
        with self.assertRaises(io.Refusal):
            observer.finish(runner.summary())

    def test_18_event_byte_overflow_prevents_later_finish(self):
        runner, _ = self.runner()
        runner.account.event_bytes = io.EVENT_BYTES
        with self.assertRaises(io.CustodyFailure):
            self.child(runner, 'pass')
        self.assertTrue(runner.poisoned)
        with self.assertRaises(io.Refusal):
            runner.finish()

    def test_19_target_env_cannot_run_loader_code_before_gate(self):
        captured = []
        def reject_start(chunk):
            row = chunk['rows'][0]
            if row['kind'] == 'aux-start':
                raw = Path(f"/proc/{row['identity']['pid']}/environ").read_bytes()
                actual = dict(part.decode().split('=',1) for part in raw.split(b'\0') if part)
                captured.append(actual)
                self.assertEqual(actual, commands.LAUNCH_ENV)
                self.assertNotIn('LD_PRELOAD', actual)
                raise ValueError('deny before target loader')
        runner, _ = self.runner(emit=reject_start)
        with self.assertRaises(io.CustodyFailure):
            self.child(runner, 'pass', environment={'LD_PRELOAD': '/unbound/does-not-exist.so'})
        self.assertEqual(len(captured), 1)

    def test_20_fast_elf_runs_only_after_actual_parent_join(self):
        runner, observer = self.runner()
        row = runner.run_observed('native-resource', 'seed_native_resources.query',
                                 ['/usr/bin/true'], self.root, {}, maximum=1)
        self.assertEqual(row['returncode'], 0)
        self.assertEqual(observer.finish(runner.finish())['chunks'], 4)

    def test_21_daemon_peer_socket_rows_and_original_timeout(self):
        runner, observer = self.runner()
        sock = runner.root / 's'
        body = ('import socket,sys; s=socket.socket(socket.AF_UNIX);s.bind(sys.argv[1]);s.listen(1);'
                'c,_=s.accept();r=c.recv(64);c.sendall(b\'PONG\\n{"version":"fixture"}\\n\');'
                'c.close();s.close();__import__("time").sleep(30)')
        child = runner.open_object_reader('historical-daemon', 'seed_historical_surface.daemon',
            ['/usr/bin/python3','-I','-S','-B','-c',body,str(sock)], self.root, {}, maximum=1024, seconds=2)
        row = child.run_daemon_session(sock)
        self.assertEqual(row['status_raw'], b'{"version":"fixture"}')
        self.assertEqual(row['child']['stdin']['bytes'], 0)
        self.assertEqual(Path(row['socket_request']['path']).read_bytes(), b'PING\nSTATUS\n')
        self.assertEqual(Path(row['socket_response']['path']).read_bytes(), b'PONG\n{"version":"fixture"}\n')
        self.assertFalse(observer.finish(runner.finish())['completed_capability'])

    def test_22_daemon_slow_drip_cannot_renew_absolute_endpoint(self):
        runner, _ = self.runner(duration=1, cleanup=2)
        sock = runner.root / 's'
        body = ('import socket,sys,time;s=socket.socket(socket.AF_UNIX);s.bind(sys.argv[1]);s.listen(1);'
                'c,_=s.accept();c.recv(64);c.sendall(b"PONG\\n{");time.sleep(30)')
        child = runner.open_object_reader('historical-daemon', 'seed_historical_surface.daemon',
            ['/usr/bin/python3','-I','-S','-B','-c',body,str(sock)], self.root, {}, maximum=1024, seconds=.15)
        with self.assertRaises(io.CustodyFailure):
            child.run_daemon_session(sock)
        self.assertTrue(runner.poisoned)
        self.assertTrue(child.reaped)
        self.assertEqual(Path(child.socket_response.path).read_bytes(), b'PONG\n{')

    def test_23_no_callback_or_receipt_flag_can_complete_custody(self):
        runner, observer = self.runner()
        forged = {'commands':0,'events':0,'event_bytes':0,'stdio_bytes':0,'poisoned':False,
                  'active':[],'quarantine':[],'scope_closed':True,'completed_capability':True}
        with self.assertRaises(io.Refusal):
            observer.finish(forged)
        self.assertFalse(runner.finish()['completed_capability'])
        self.assertFalse(hasattr(commands, 'ClosedProducerObservation'))

    def test_24_descendant_holding_pipe_is_not_direct_child_closure(self):
        runner, _ = self.runner(duration=.5, cleanup=1)
        body = ('import os,time;pid=os.fork();'
                'time.sleep(5) if pid==0 else None;'
                'os._exit(0)')
        child = self.child(runner, body, seconds=.1)
        with self.assertRaises(io.CustodyFailure):
            child.finish_observed_child()
        self.assertTrue(child.reaped)
        self.assertTrue(runner.poisoned)
        self.assertFalse(runner.summary()['scope_closed'])
        # Its inert grandchild stays in this ORIGINAL finite test unit; systemd
        # owns the group's final closure. No numeric descendant signal occurs.

    def test_25_parent_executable_size_cannot_be_zero_or_short(self):
        runner, _ = self.runner()
        fd, row = io.open_executable('/usr/bin/true', runner.work_end)
        try:
            for count in (0, row['bytes']-1, True):
                bad = {**row, 'bytes':count, 'sha256':hashlib.sha256(b'').hexdigest()}
                with self.assertRaises(io.Refusal):
                    io.verify_retained(fd, bad, runner.work_end)
        finally:
            os.close(fd)

    def test_26_private_daemon_path_traversal_and_ancestor_alias_refuse(self):
        for literal in ('../ambient.sock', 'link/ambient.sock'):
            runner, _ = self.runner()
            (runner.root / 'link').symlink_to(self.root, target_is_directory=True)
            endpoint = runner.root / literal
            child = runner.open_object_reader('historical-daemon', 'seed_historical_surface.daemon',
                ['/usr/bin/python3','-I','-S','-B','-c','import time;time.sleep(30)',str(endpoint)],
                self.root, {}, maximum=1024)
            with mock.patch.object(child,'_pump',wraps=child._pump) as pump:
                with self.assertRaisesRegex(io.CustodyFailure,'endpoint is not the exact private bound path'):
                    child.run_daemon_session(endpoint)
                self.assertFalse(pump.called)
            self.assertTrue(runner.poisoned)

    def test_27_target_elf_inherits_default_sigpipe(self):
        runner, observer = self.runner()
        row = runner.run_observed('native-resource', 'seed_native_resources.query',
            ['/usr/bin/cat','/proc/self/status'], self.root, {}, maximum=65536)
        status = runner.read_output(row).decode()
        ignored = int(next(line.split()[1] for line in status.splitlines() if line.startswith('SigIgn:')),16)
        self.assertEqual(ignored & (1 << (signal.SIGPIPE-1)), 0)
        observer.finish(runner.finish())

    def test_28_actual_parent_chunks_are_complete_exclusive_and_canonical(self):
        runner, observer = self.runner()
        row = runner.run_observed('native-resource','seed_native_resources.query',
            ['/usr/bin/true'],self.root,{},maximum=1)
        observer.finish(runner.finish())
        manifest = observer.capture_auxiliary_chunks(self.root/'retained-chunks')
        self.assertEqual(manifest['events'],4)
        self.assertEqual(len(manifest['chunks']),4)
        for number, chunk in enumerate(manifest['chunks']):
            data = (self.root/'retained-chunks'/chunk['name']).read_bytes()
            self.assertEqual(data,observer.chunks[number])
            self.assertEqual(hashlib.sha256(data).hexdigest(),chunk['sha256'])
            self.assertEqual(len(data),chunk['bytes'])
        with self.assertRaises(io.Refusal):
            observer.capture_auxiliary_chunks(self.root/'retained-chunks')
        self.assertFalse(manifest['completed_capability'])

    def test_29_parent_chunk_capture_uses_only_original_cleanup_end(self):
        runner, observer = self.runner()
        observer.cleanup_end = time.monotonic()-1
        with self.assertRaises(io.Refusal):
            observer.capture_auxiliary_chunks(self.root/'must-not-exist')
        self.assertFalse((self.root/'must-not-exist').exists())

    def test_30_missing_go_chunk_cannot_complete_parent_ledger(self):
        runner, observer = self.runner()
        def omit_go(chunk):
            if chunk['rows'][0]['kind'] != 'aux-go':
                observer.accept(chunk)
        runner.emit = omit_go
        with self.assertRaises(io.CustodyFailure):
            self.child(runner,'pass').finish_observed_child()
        self.assertTrue(observer.poisoned)
        self.assertTrue(runner.poisoned)
        with self.assertRaises(io.Refusal):
            observer.finish(runner.summary())

    def test_31_original_shared_stdio_budget_cannot_be_exceeded(self):
        runner, _ = self.runner()
        runner.account.stdio_bytes = io.STDIO_BYTES-3
        child = self.child(runner,'import os;os.write(1,b"abcdef")')
        with self.assertRaises(io.CustodyFailure):
            child.finish_observed_child()
        self.assertEqual(child.stdout.length,3)
        self.assertEqual(runner.account.stdio_bytes,io.STDIO_BYTES)
        self.assertTrue(child.stdout.truncated)

    def test_32_semantic_phase_is_bound_before_target_gate(self):
        runner, observer = self.runner()
        marker = self.root/'phase-target'
        original_emit = runner.emit
        def inspect_issued(chunk):
            if chunk['rows'][0]['kind']=='aux-issued':
                self.assertEqual(chunk['rows'][0]['spec']['semantic_phase'],'external-bootstrap')
                self.assertFalse(marker.exists())
            original_emit(chunk)
        runner.emit = inspect_issued
        child = runner.open_object_reader('semantic-producer','WorkerContext.command',
            ['/usr/bin/python3','-I','-S','-B','-c',f'from pathlib import Path;Path({str(marker)!r}).touch()'],
            self.root,{},maximum=1024,input_pipe=False,semantic_phase='external-bootstrap')
        self.assertEqual(observer.semantic_child('external-bootstrap',child.child.pid,child.identity['start']),0)
        child.finish_observed_child()
        self.assertTrue(marker.exists())
        observer.finish(runner.finish())

    def test_33_wrong_semantic_phase_cannot_launch_target(self):
        runner, observer = self.runner()
        with mock.patch.object(commands.subprocess,'Popen',side_effect=AssertionError('must not spawn')):
            with self.assertRaises(io.CustodyFailure):
                runner.open_object_reader('semantic-producer','WorkerContext.command',['/usr/bin/true'],
                    self.root,{},maximum=1,input_pipe=False,semantic_phase='candidate-self-host')
        self.assertTrue(runner.poisoned)
        self.assertTrue(observer.poisoned)


if __name__ == '__main__':
    unittest.main(verbosity=2)
