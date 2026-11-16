"""Original-context, gated auxiliary children; no completed capability exists.

Only the source-bound WorkerContext constructs this runner. Its emit function
transports data to the original parent; its return value cannot close custody.
All endpoint values are the original absolute limits, never retry grants.
"""
from __future__ import annotations
import hashlib
import json
import math
import os
from pathlib import Path
import selectors
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
io = __trust_source_loader__.module('trust_seed_observed_io', HERE / 'seed_observed_io.py')
Refusal, CustodyFailure = io.Refusal, io.CustodyFailure
LAUNCH_ENV = {'PATH': '/usr/bin:/bin', 'HOME': '/', 'LANG': 'C', 'LC_ALL': 'C'}


class ObservedCommands:
    def __init__(self, *, started, work_end, cleanup_end, spool_root, emit):
        io.require(all(type(v) in (int, float) and math.isfinite(v)
                       for v in (started, work_end, cleanup_end))
                   and started <= time.monotonic() < work_end <= cleanup_end,
                   'original work/cleanup endpoint tuple is invalid')
        io.preflight()
        root = Path(spool_root)
        io.require(root.is_absolute() and root.resolve(strict=False) == root and not root.exists(),
                   'auxiliary spool root must be fresh and canonical')
        root.mkdir(mode=0o700)
        self.started, self.work_end, self.cleanup_end = started, work_end, cleanup_end
        self.root, self.emit, self.account = root, emit, io.Account()
        self.owner = io.process(os.getpid())
        self.active, self.quarantine, self.errors = {}, {}, []
        self.poisoned = False

    def poison(self, error):
        self.poisoned = True
        if len(self.errors) < 64:
            self.errors.append(str(error)[:1000])

    def quarantine_child(self, child, error):
        self.quarantine[child.number] = child
        self.poison(error)
        child.quarantine_notice = {'command':child.number,'reported_pid':child.child.pid,
            'observed_start':child.identity['start'] if child.identity else None,
            'pidfd_acquired':child.pidfd is not None,'direct_reaped':child.reaped,
            'requires_original_scope_custody':True,'error':str(error)[:1000]}
        try:
            io.remaining(self.cleanup_end)
            self.event('aux-quarantine', **child.quarantine_notice)
        except BaseException as transport_error:
            self.poison(transport_error)  # Exact child/notice remain in RAM; no restart/reset.

    def event(self, kind, **row):
        value = {'kind': kind, 'at': time.monotonic(), 'original_started': self.started,
                 'original_work_end': self.work_end, 'original_cleanup_end': self.cleanup_end,
                 'aux_sequence': self.account.events, **row}
        raw = io.encoded(value)
        self.account.event(raw)
        # A complete row is a canonical bounded chunk. Parent RAM retains every
        # acknowledged chunk, independent of the 512 semantic-event account.
        self.emit({'rows': [value], 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()})
        return value

    def open_object_reader(self, role, callsite, argv, cwd, environment, *, maximum, seconds=60, input_pipe=True, semantic_phase=None):
        child = None
        try:
            io.require(not self.poisoned, 'original auxiliary custody is permanently poisoned')
            io.remaining(self.work_end)
            actual_owner = io.process(os.getpid())
            io.require(all(actual_owner[k] == self.owner[k] for k in ('pid', 'parent', 'start', 'cgroup')),
                       'original worker identity changed')
            spec = io.validate_request(role, callsite, argv, cwd, environment, maximum, seconds)
            number = self.account.command()
            spec['stdin_kind'] = 'pipe' if input_pipe else 'devnull'
            spec['semantic_phase'] = semantic_phase
            child = ChildReader(self, number, spec)
            self.active[number] = child
            child.start()
            return child
        except BaseException as error:
            self.poison(error)
            if child is not None:
                child.abort(error)
            raise CustodyFailure(str(error), self) from error

    def run_observed(self, role, callsite, argv, cwd, environment, *, maximum, seconds=60):
        child = self.open_object_reader(role, callsite, argv, cwd, environment,
                                        maximum=maximum, seconds=seconds, input_pipe=False)
        return child.finish_observed_child()

    def read_output(self, receipt, stream='stdout', maximum=65536):
        io.require(stream in ('stdout', 'stderr') and type(maximum) is int
                   and 0 <= maximum <= io.STDIO_BYTES, 'invalid retained-output request')
        row = receipt[stream]
        path = Path(row['path'])
        io.require(path.parent == self.root and not row['truncated'] and row['bytes'] <= maximum,
                   'retained output path/limit failed')
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
        try:
            before = os.fstat(fd)
            io.require(before.st_size == row['bytes'], 'retained output size changed')
            data = bytearray()
            while len(data) < row['bytes']:
                io.remaining(self.work_end)
                block = os.read(fd, min(65536, row['bytes'] - len(data)))
                io.require(block, 'retained output truncated')
                data.extend(block)
            io.require(io.key(os.fstat(fd)) == io.key(before)
                       and hashlib.sha256(data).hexdigest() == row['sha256'], 'retained output bytes changed')
            return bytes(data)
        finally:
            os.close(fd)

    def copy_output(self, receipt, output):
        row = receipt['stdout']
        path = Path(row['path'])
        io.require(path.parent == self.root and not row['truncated'], 'unbound output copy')
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
        value, length = hashlib.sha256(), 0
        try:
            while length < row['bytes']:
                io.remaining(self.work_end)
                block = os.read(fd, min(65536, row['bytes'] - length))
                io.require(block, 'retained semantic output truncated')
                io.require(output.write(block) == len(block), 'semantic output short write')
                length += len(block)
                value.update(block)
            io.require(os.fstat(fd).st_size == length and value.hexdigest() == row['sha256'],
                       'retained semantic output changed')
        finally:
            os.close(fd)

    def summary(self):
        return {'schema': 'trust.rootseed.auxiliary-summary.v1', 'commands': self.account.commands,
                'events': self.account.events, 'event_bytes': self.account.event_bytes,
                'stdio_bytes': self.account.stdio_bytes, 'poisoned': self.poisoned,
                'active': sorted(self.active), 'quarantine': sorted(self.quarantine),
                'errors': list(self.errors), 'direct_children_reaped': not self.active,
                'scope_closed': False, 'completed_capability': False}

    def finish(self):
        io.require(not self.poisoned and not self.active and not self.quarantine,
                   'auxiliary failures/children remain in original custody')
        io.remaining(self.work_end)
        return self.summary()  # Data only; never a RootSeed or reader capability.


class ChildReader:
    def __init__(self, owner, number, spec):
        self.owner, self.number, self.spec = owner, number, spec
        self.command_end = min(owner.work_end, time.monotonic() + spec['seconds_cap'])
        self.child = self.pidfd = self.executable_fd = self.launcher_fd = None
        self.gate_write = self.gate_read = None
        self.selector = selectors.DefaultSelector()
        self.stdout = self.stderr = self.stdin_log = None
        self.socket_request = self.socket_response = None
        self.identity = None
        self.cursor = 0
        self.exited = self.reaped = self.finished = False
        self.receipt = None
        self.quarantine_notice = None

    def start(self):
        io.preflight()
        io.remaining(self.command_end)
        self.executable_fd, executable = io.open_executable(self.spec['argv'][0], self.command_end)
        self.launcher_fd, launcher = io.open_executable('/usr/bin/python3', self.command_end)
        self.spec.update(executable=executable, launcher=launcher,
                         entry_sha256=hashlib.sha256(io.ENTRY.encode()).hexdigest())
        self.owner.event('aux-issued', command=self.number, spec=self.spec, command_end=self.command_end)
        self.stdout = io.Spool(self.owner.root, f'{self.number:06d}.stdout', self.spec['stdio_maximum'], self.owner.account)
        self.stderr = io.Spool(self.owner.root, f'{self.number:06d}.stderr', self.spec['stdio_maximum'], self.owner.account)
        self.stdin_log = io.Spool(self.owner.root, f'{self.number:06d}.stdin', io.STDIO_BYTES, self.owner.account)
        self.gate_read, self.gate_write = os.pipe2(os.O_CLOEXEC)
        argv = ['/usr/bin/python3', '-I', '-S', '-B', '-c', io.ENTRY,
                str(self.executable_fd), str(self.gate_read), str(os.getpid()), str(self.launcher_fd),
                json.dumps([self.spec['argv'], self.spec['environment']], separators=(',', ':'))]
        io.remaining(self.command_end)
        self.child = subprocess.Popen(argv, executable=f'/proc/self/fd/{self.launcher_fd}',
            cwd=self.spec['cwd'], env=LAUNCH_ENV,
            stdin=subprocess.PIPE if self.spec['stdin_kind'] == 'pipe' else subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT if self.spec['merge_stderr'] else subprocess.PIPE, close_fds=True,
            pass_fds=(self.executable_fd, self.launcher_fd, self.gate_read))
        # No poll(), wait(), signal(), communicate(), callback or stream wait is
        # permitted between retaining the exact Popen and this pidfd attempt.
        self.pidfd = os.pidfd_open(self.child.pid, 0)
        self.identity = io.process(self.child.pid)
        io.require(self.identity['parent'] == os.getpid()
                   and self.identity['cgroup'] == self.owner.owner['cgroup'], 'child left original worker scope')
        io.remaining(self.command_end)
        self.owner.event('aux-start', command=self.number, identity=self.identity,
                         executable_fd=self.executable_fd, gate_fd=self.gate_read, launcher_fd=self.launcher_fd, launcher=launcher)
        io.recheck_executable(self.executable_fd, executable)
        io.recheck_executable(self.launcher_fd, launcher)
        io.remaining(self.command_end)
        os.write(self.gate_write, b'G')
        os.close(self.gate_write)
        self.gate_write = None
        os.close(self.gate_read)
        self.gate_read = None
        for name in ('stdout', 'stderr'):
            stream = getattr(self.child, name)
            if stream is None:
                continue
            os.set_blocking(stream.fileno(), False)
            self.selector.register(stream, selectors.EVENT_READ, name)
        if self.child.stdin is not None:
            os.set_blocking(self.child.stdin.fileno(), False)
        self.selector.register(self.pidfd, selectors.EVENT_READ, 'pidfd')
        self.owner.event('aux-go', command=self.number, pid=self.child.pid, start=self.identity['start'])

    def _pump(self, end):
        for item, _mask in self.selector.select(min(.05, io.remaining(end))):
            if item.data == 'pidfd':
                self.exited = True
                self.selector.unregister(self.pidfd)
                continue
            stream = item.fileobj
            budget = min(self.spec['stdio_maximum'] - self.stdout.length - self.stderr.length,
                         io.STDIO_BYTES - self.owner.account.stdio_bytes)
            block = os.read(stream.fileno(), min(65536, max(0, budget) + 1))
            if not block:
                self.selector.unregister(stream)
                stream.close()
                continue
            spool = getattr(self, item.data)
            spool.retain(block[:max(0, budget)])
            if len(block) > budget:
                spool.observed += len(block) - max(0, budget)
                spool.truncated = True
                raise Refusal('live combined stdio cap exceeded; retained bytes remain bounded')

    def write_input(self, raw):
        try:
            io.remaining(self.command_end)
            io.require(self.child.stdin is not None, 'command has fixed DEVNULL input')
            io.require(type(raw) is bytes and len(raw) <= 65536, 'object request exceeds finite input bound')
            io.require(self.owner.account.stdio_bytes + len(raw) <= io.STDIO_BYTES,
                       'object input exceeds shared retained I/O account')
            view = memoryview(raw)
            while view:
                io.remaining(self.command_end)
                try:
                    count = os.write(self.child.stdin.fileno(), view)
                    io.require(count > 0, 'zero child input write')
                    self.stdin_log.retain(bytes(view[:count]))
                    view = view[count:]
                except BlockingIOError:
                    self._pump(self.command_end)
        except BaseException as error:
            self.abort(error)
            raise CustodyFailure(str(error), self.owner) from error

    def read_object_exact(self, size):
        try:
            io.remaining(self.command_end)
            io.require(type(size) is int and 0 <= size <= 1024 * 1024,
                       'object read must be chunked at one MiB')
            while self.stdout.length - self.cursor < size:
                io.remaining(self.command_end)
                io.require(not self.child.stdout.closed, 'object stream ended before declared bytes')
                self._pump(self.command_end)
            io.remaining(self.command_end)
            data = os.pread(self.stdout.fd, size, self.cursor)
            io.require(len(data) == size, 'retained object spool changed')
            self.cursor += size
            return data
        except BaseException as error:
            self.abort(error)
            raise CustodyFailure(str(error), self.owner) from error

    def read_object_line(self, maximum=65536):
        try:
            io.require(type(maximum) is int and 0 < maximum <= 65536, 'object header line cap failed')
            while True:
                io.remaining(self.command_end)
                raw = os.pread(self.stdout.fd, min(maximum + 1, self.stdout.length - self.cursor), self.cursor)
                cut = raw.find(b'\n')
                if cut >= 0:
                    io.require(cut + 1 <= maximum, 'object header exceeds cap')
                    self.cursor += cut + 1
                    return raw[:cut + 1]
                io.require(len(raw) <= maximum and not self.child.stdout.closed,
                           'object header truncated or exceeds cap')
                self._pump(self.command_end)
        except BaseException as error:
            self.abort(error)
            raise CustodyFailure(str(error), self.owner) from error

    def finish_observed_child(self):
        if self.finished:
            return self.receipt
        try:
            if self.child.stdin is not None:
                self.child.stdin.close()
            while not self.exited or any(k.data != 'pidfd' for k in self.selector.get_map().values()):
                self._pump(self.command_end)
            self.child.wait(timeout=io.remaining(self.command_end))
            self.reaped = True
            io.recheck_executable(self.executable_fd, self.spec['executable'])
            return self._finish(None)
        except BaseException as error:
            self.abort(error)
            raise CustodyFailure(str(error), self.owner) from error

    def _finish(self, error):
        for spool in (self.stdout, self.stderr, self.stdin_log, self.socket_request, self.socket_response):
            if spool is not None:
                spool.close()
        row = {'command': self.number, 'pid': self.child.pid if self.child else None,
               'start': self.identity['start'] if self.identity else None,
               'returncode': self.child.returncode if self.child else None,
               'direct_reaped': self.reaped, 'scope_closed': False,
               'stdout': self.stdout.row() if self.stdout else None,
               'stderr': self.stderr.row() if self.stderr else None,
               'stdin': self.stdin_log.row() if self.stdin_log else None,
               'socket_request': self.socket_request.row() if self.socket_request else None,
               'socket_response': self.socket_response.row() if self.socket_response else None,
               'error': None if error is None else str(error)[:1000]}
        self.owner.event('aux-exit', **row)
        self.receipt = row
        if self.reaped:
            self.owner.active.pop(self.number, None)
            self.close_handles()
        else:
            self.owner.quarantine[self.number] = self
        self.finished = self.reaped
        return row

    def abort(self, error):
        self.owner.poison(error)
        if self.gate_write is not None:
            os.close(self.gate_write)  # EOF denies inner exec, including pidfd failure.
            self.gate_write = None
        if self.child is None:
            self.owner.active.pop(self.number, None)
            self.close_handles()
            return
        if self.pidfd is None:
            self.owner.quarantine_child(self, error)
            return  # Exact Popen/FDs retained for original scope supervisor.
        try:
            io.remaining(self.owner.cleanup_end)
            try:
                signal.pidfd_send_signal(self.pidfd, signal.SIGKILL)
            except ProcessLookupError:
                pass
            with selectors.DefaultSelector() as wait:
                wait.register(self.pidfd, selectors.EVENT_READ)
                io.require(wait.select(io.remaining(self.owner.cleanup_end)), 'child did not exit before original cleanup end')
            self.child.wait(timeout=io.remaining(self.owner.cleanup_end))
            self.reaped = True
            self._finish(error)
        except BaseException as cleanup_error:
            self.owner.poison(cleanup_error)
            self.owner.quarantine_child(self, cleanup_error)

    def close_handles(self):
        self.selector.close()
        for spool in (self.stdout, self.stderr, self.stdin_log, self.socket_request, self.socket_response):
            if spool is not None:
                spool.close()
        if self.child is not None:
            for name in ('stdin', 'stdout', 'stderr'):
                stream = getattr(self.child, name)
                if stream is not None and not stream.closed:
                    stream.close()
        for name in ('pidfd', 'executable_fd', 'launcher_fd', 'gate_read', 'gate_write'):
            fd = getattr(self, name)
            if fd is not None:
                os.close(fd)
                setattr(self, name, None)

    def run_daemon_session(self, path):
        """Fixed historical PING/STATUS exchange, not a candidate callback."""
        import errno
        import socket
        import struct
        try:
            self.socket_request = io.Spool(self.owner.root, f'{self.number:06d}.socket-request', 12, self.owner.account)
            self.socket_response = io.Spool(self.owner.root, f'{self.number:06d}.socket-response', 65552, self.owner.account)
            path = Path(path)
            io.require(path.is_absolute() and path.resolve(strict=False) == path
                       and path.parent.resolve(strict=True) == path.parent
                       and path.parent.is_relative_to(self.owner.root) and str(path) in self.spec['argv']
                       and len(os.fsencode(path)) < 108, 'daemon endpoint is not the exact private bound path')
            while not path.exists():
                self._pump(self.command_end)
                io.require(not self.exited, 'daemon exited before its private endpoint')
            io.require(not path.is_symlink(), 'daemon endpoint became a symlink')
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as stream:
                stream.setblocking(False)
                status = stream.connect_ex(str(path))
                io.require(status in (0, errno.EINPROGRESS, errno.EAGAIN), 'daemon connect failed')
                if status:
                    with selectors.DefaultSelector() as wait:
                        wait.register(stream, selectors.EVENT_WRITE)
                        while not wait.select(0):
                            self._pump(self.command_end)
                    io.require(stream.getsockopt(socket.SOL_SOCKET, socket.SO_ERROR) == 0, 'daemon connect error')
                pid, uid, gid = struct.unpack('3i', stream.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))
                current = io.process(pid)
                io.require(pid == self.child.pid and uid == os.geteuid()
                           and current['start'] == self.identity['start']
                           and current['cgroup'] == self.identity['cgroup'], 'daemon peer is not exact retained child')
                pending, raw = memoryview(b'PING\nSTATUS\n'), bytearray()
                while pending:
                    io.remaining(self.command_end)
                    try:
                        count = stream.send(pending)
                        io.require(count > 0, 'daemon request short write')
                        self.socket_request.retain(bytes(pending[:count]))
                        pending = pending[count:]
                    except BlockingIOError:
                        self._pump(self.command_end)
                while raw.count(b'\n') < 2:
                    io.remaining(self.command_end)
                    try:
                        block = stream.recv(min(4096, 65552 - len(raw) + 1))
                        io.require(block, 'daemon reply is truncated')
                        self.socket_response.retain(block)
                        raw.extend(block)
                        io.require(len(raw) <= 65552, 'daemon reply exceeds fixed cap')
                    except BlockingIOError:
                        self._pump(self.command_end)
                io.require(raw.startswith(b'PONG\n') and raw.endswith(b'\n') and raw.count(b'\n') == 2,
                           'daemon fixed reply framing changed')
            io.remaining(self.command_end)
            signal.pidfd_send_signal(self.pidfd, signal.SIGTERM)
            receipt = self.finish_observed_child()
            return {'pid': pid, 'uid': uid, 'gid': gid, 'status_raw': bytes(raw[5:-1]),
                    'socket_request': self.socket_request.row(), 'socket_response': self.socket_response.row(),
                    'child': receipt, 'scope_closed': False}
        except BaseException as error:
            self.abort(error)
            raise CustodyFailure(str(error), self.owner) from error
