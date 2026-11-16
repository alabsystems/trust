"""Original parent RAM ledger for complete auxiliary chunks and child pidfds.

This never issues a completed capability. Caller must still prove original
worker/launcher/native-scope closure and connect every family verifier.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import selectors
import re
import stat
import time

HERE = Path(__file__).resolve().parent
io = __trust_source_loader__.module('trust_seed_observed_io', HERE / 'seed_observed_io.py')


class AuxiliaryObserver:
    def __init__(self, *, worker_pid, worker_start, cgroup, started, work_end, cleanup_end, spool_root):
        self.worker_pid, self.worker_start, self.cgroup = worker_pid, worker_start, cgroup
        self.started, self.work_end, self.cleanup_end = started, work_end, cleanup_end
        self.root = Path(spool_root)
        self.account = io.Account()
        self.chunks, self.issued, self.active, self.reaped = [], {}, {}, {}
        self.poisoned = False
        self.quarantined, self.semantic_count = {}, 0

    def accept(self, chunk):
        try:
            self._accept(chunk)
        except BaseException:
            self.poisoned = True
            raise

    def _accept(self, chunk):
        io.remaining(self.cleanup_end)
        worker = io.process(self.worker_pid)
        io.require(worker['start'] == self.worker_start and worker['cgroup'] == self.cgroup,
                   'actual original worker identity changed')
        io.require(type(chunk) is dict and set(chunk) == {'rows', 'bytes', 'sha256'}
                   and type(chunk['rows']) is list and len(chunk['rows']) == 1,
                   'auxiliary chunk shape/count is not complete')
        row = chunk['rows'][0]
        raw = io.encoded(row)
        io.require(chunk['bytes'] == len(raw) and chunk['sha256'] == hashlib.sha256(raw).hexdigest(),
                   'auxiliary chunk byte/hash join failed')
        io.require(row['aux_sequence'] == self.account.events
                   and row['original_started'] == self.started
                   and row['original_work_end'] == self.work_end
                   and row['original_cleanup_end'] == self.cleanup_end
                   and self.started <= row['at'] <= time.monotonic() < self.cleanup_end,
                   'auxiliary order or original endpoints changed')
        self.account.event(raw)
        kind, number = row['kind'], row['command']
        if kind == 'aux-issued':
            io.require(row['at'] < self.work_end and number == self.account.commands and self.account.commands < io.MAX_COMMANDS,
                       'auxiliary issued outside original work/order')
            self.account.commands += 1
            spec = row['spec']
            checked = io.validate_request(spec['role'], spec['callsite'], spec['argv'], spec['cwd'],
                                          spec['environment'], spec['stdio_maximum'], spec['seconds_cap'])
            io.require(all(spec[k] == v for k, v in checked.items())
                       and self.started < row['command_end'] <= self.work_end,
                       'auxiliary fixed command binding failed')
            if spec['role'] == 'semantic-producer':
                contract = __trust_source_loader__.module('trust_producer_contract',HERE/'seed_producer_contract.py')
                io.require(self.semantic_count < len(contract.COMMANDS)
                           and spec['semantic_phase'] == contract.COMMANDS[self.semantic_count],
                           'actual semantic phase is not fixed before target execution')
                self.semantic_count += 1
            else:
                io.require(spec.get('semantic_phase') is None, 'auxiliary commandeered a semantic phase')
            self.issued[number] = row
        elif kind == 'aux-start':
            io.require(number in self.issued and number not in self.active and number not in self.reaped,
                       'auxiliary start is missing/duplicate')
            identity = row['identity']
            held = {'identity': dict(identity), 'pidfd': None, 'executable_fd': None, 'launcher_fd': None, 'went': False}
            self.active[number] = held  # Retain exact claimed identity on acquisition failure.
            held['pidfd'] = os.pidfd_open(identity['pid'], 0)
            actual = io.process(identity['pid'])
            io.require(all(actual[k] == identity[k] for k in ('pid', 'parent', 'start', 'cgroup'))
                       and actual['parent'] == self.worker_pid
                       and actual['cgroup'] == self.cgroup and actual['state'] != 'Z',
                       'actual child start/parent/cgroup differs before gate')
            spec = self.issued[number]['spec']
            fdpath = Path(f"/proc/{identity['pid']}/fd/{row['executable_fd']}")
            expected_argv = ['/usr/bin/python3','-I','-S','-B','-c',io.ENTRY,
                str(row['executable_fd']),str(row['gate_fd']),str(self.worker_pid),str(row['launcher_fd']),
                json.dumps([spec['argv'],spec['environment']],separators=(',',':'))]
            actual_argv = Path(f"/proc/{identity['pid']}/cmdline").read_bytes().split(b'\0')
            io.require(actual_argv == [a.encode() for a in expected_argv] + [b'']
                       and spec['entry_sha256'] == hashlib.sha256(io.ENTRY.encode()).hexdigest(),
                       'actual child shim argv/source identity differs before GO')
            actual_environment = Path(f"/proc/{identity['pid']}/environ").read_bytes().split(b'\0')
            expected_environment = {'PATH':'/usr/bin:/bin','HOME':'/','LANG':'C','LC_ALL':'C'}
            io.require(sorted(v for v in actual_environment if v)
                       == sorted((k+'='+v).encode() for k,v in expected_environment.items()),
                       'actual gated launcher environment is not fixed/clean')
            stdin = Path(f"/proc/{identity['pid']}/fd/0").stat()
            io.require(spec['stdin_kind'] in ('pipe','devnull')
                       and (stat.S_ISFIFO(stdin.st_mode) if spec['stdin_kind'] == 'pipe'
                            else stat.S_ISCHR(stdin.st_mode) and stdin.st_rdev == os.stat('/dev/null').st_rdev),
                       'actual child stdin kind differs from fixed request')
            gate = Path(f"/proc/{identity['pid']}/fd/{row['gate_fd']}").stat()
            io.require(stat.S_ISFIFO(gate.st_mode), 'actual pre-exec gate is not a pipe')
            held['executable_fd'] = os.open(fdpath, os.O_RDONLY | os.O_CLOEXEC | os.O_NONBLOCK)
            endpoint = self.issued[number]['command_end']
            io.verify_retained(held['executable_fd'], spec['executable'], endpoint)
            held['launcher_fd'] = os.open(f"/proc/{identity['pid']}/exe", os.O_RDONLY | os.O_CLOEXEC)
            io.verify_retained(held['launcher_fd'], spec['launcher'], endpoint)
            io.require(row['launcher'] == spec['launcher'], 'gated child launcher binding differs')
        elif kind == 'aux-go':
            held = self.active.get(number)
            io.require(held is not None and not held['went'] and held['pidfd'] is not None
                       and row['pid'] == held['identity']['pid'] and row['start'] == held['identity']['start']
                       and row['at'] < self.work_end, 'auxiliary gate release is unbound/repeated/late')
            held['went'] = True
        elif kind == 'aux-quarantine':
            io.require(number in self.issued and row['requires_original_scope_custody'] is True,
                       'quarantined child lacks its original issued command')
            self.quarantined[number] = row
            self.poisoned = True
        elif kind == 'aux-exit':
            self._exit(number, row)
        else:
            raise io.Refusal('unknown auxiliary event')
        self.chunks.append(bytes(raw))  # Immutable actual parent-held bytes, never candidate paths.

    def _exit(self, number, row):
        held = self.active.get(number)
        io.require(held is not None and row['pid'] == held['identity']['pid']
                   and row['start'] == held['identity']['start'] and row['scope_closed'] is False,
                   'auxiliary exit lacks original child authority')
        io.require(row['direct_reaped'] is True and held['pidfd'] is not None,
                   'auxiliary direct child was not reaped')
        with selectors.DefaultSelector() as wait:
            wait.register(held['pidfd'], selectors.EVENT_READ)
            io.require(wait.select(0), 'retained original child pidfd is not exited')
        try:
            current = io.process(held['identity']['pid'])
        except FileNotFoundError:
            current = None
        io.require(current is None or current['start'] != held['identity']['start'],
                   'original child remains unreaped (numeric PID absence is not identity authority)')
        io.require(type(row['returncode']) is int and (row['error'] is not None or held['went']),
                   'successful auxiliary omitted actual GO/exit status')
        total = 0
        for name in ('stdout', 'stderr', 'stdin', 'socket_request', 'socket_response'):
            stream = row[name]
            if stream is None:
                io.require(name.startswith('socket_'), 'required stdio receipt is missing')
                continue
            io.require(type(stream) is dict
                       and set(stream) == {'path','bytes','observed_bytes','sha256','truncated'}
                       and type(stream['sha256']) is str and re.fullmatch('[0-9a-f]{64}', stream['sha256'])
                       and type(stream['truncated']) is bool
                       and type(stream['bytes']) is int and stream['bytes'] >= 0
                       and stream['observed_bytes'] >= stream['bytes'], 'auxiliary stdio account malformed')
            self._verify_stream(number, name, stream)
            total += stream['bytes']
        output_total = row['stdout']['bytes'] + row['stderr']['bytes']
        io.require(output_total <= self.issued[number]['spec']['stdio_maximum']
                   and self.account.stdio_bytes + total <= io.STDIO_BYTES, 'auxiliary shared stdio account exceeded')
        self.account.stdio_bytes += total
        self.reaped[number] = row
        self.active.pop(number)
        for name in ('pidfd', 'executable_fd', 'launcher_fd'):
            if held[name] is not None:
                os.close(held[name])
        if row['error'] is not None or any(row[s] is not None and row[s]['truncated']
                                             for s in ('stdout', 'stderr', 'stdin', 'socket_request', 'socket_response')):
            self.poisoned = True

    def _verify_stream(self, number, name, row):
        expected = self.root / f'{number:06d}.{name.replace("_", "-")}'
        io.require(row['path'] == str(expected) and expected.parent.resolve(strict=True) == self.root,
                   'auxiliary stream path escapes original private spool')
        fd = os.open(expected, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK)
        try:
            before = os.fstat(fd)
            io.require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1
                       and before.st_size == row['bytes'] <= io.STDIO_BYTES, 'actual stream file differs')
            offset, value = 0, hashlib.sha256()
            while offset < row['bytes']:
                io.remaining(self.cleanup_end)
                block = os.read(fd, min(65536, row['bytes'] - offset))
                io.require(block, 'actual stream file truncated')
                offset += len(block)
                value.update(block)
            io.require(io.key(os.fstat(fd)) == io.key(before)
                       and value.hexdigest() == row['sha256'], 'actual stream digest changed')
        finally:
            os.close(fd)

    def semantic_child(self, phase, pid, start):
        matches = [number for number, held in self.active.items()
                   if held['went'] and held['identity']['pid'] == pid and held['identity']['start'] == start
                   and self.issued[number]['spec'].get('semantic_phase') == phase]
        io.require(len(matches) == 1, 'semantic child lacks its exact pre-G auxiliary phase binding')
        return matches[0]

    def negative_snapshot(self):
        return {'events':self.account.events,'commands':self.account.commands,'poisoned':self.poisoned,
                'active':{str(k):{'identity':v['identity'],'pidfd_retained':v['pidfd'] is not None}
                          for k,v in self.active.items()},
                'quarantined':{str(k):v for k,v in self.quarantined.items()},'scope_closed':False}

    def capture_auxiliary_chunks(self, root):
        io.remaining(self.cleanup_end)
        root = Path(root)
        io.require(root.is_absolute() and root.resolve(strict=False) == root and not root.exists(),
                   'auxiliary chunk root must be fresh and canonical')
        root.mkdir(mode=0o700)
        references = []
        for number, raw in enumerate(self.chunks):
            io.remaining(self.cleanup_end)
            sha = hashlib.sha256(raw).hexdigest()
            path = root / f'{number:06d}-{sha}.json'
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
            try:
                view = memoryview(raw)
                while view:
                    count = os.write(fd, view)
                    io.require(count > 0, 'auxiliary chunk short write')
                    view = view[count:]
                os.fsync(fd)
            finally:
                os.close(fd)
            references.append({'name':path.name,'bytes':len(raw),'sha256':sha})
        fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)
        io.remaining(self.cleanup_end)
        return {'root':str(root),'events':self.account.events,'chunks':references,
                'merkle_sha256':hashlib.sha256(io.encoded(references)).hexdigest(),
                'scope_closed':False,'completed_capability':False}

    def finish(self, summary):
        io.remaining(self.cleanup_end)
        io.require(not self.poisoned and not self.active
                   and set(self.issued) == set(self.reaped)
                   and summary['poisoned'] is False and summary['active'] == summary['quarantine'] == []
                   and summary['scope_closed'] is False and summary['completed_capability'] is False
                   and summary['commands'] == self.account.commands
                   and summary['events'] == self.account.events
                   and summary['event_bytes'] == self.account.event_bytes
                   and summary['stdio_bytes'] == self.account.stdio_bytes,
                   'complete auxiliary closure/count join failed')
        return {'chunks': len(self.chunks), 'sha256': hashlib.sha256(b''.join(self.chunks)).hexdigest(),
                'direct_children_reaped': True, 'scope_closed': False, 'completed_capability': False}
