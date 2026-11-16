"""Linux byte/identity primitives for original-context auxiliary custody.

These observations neither confine filesystem reads nor close a native scope.
The caller's original external supervisor remains mandatory around Popen itself.
"""
from __future__ import annotations
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import stat
import time

MAX_EXECUTABLE = 4 * 2**30
MAX_VECTOR = 128 * 1024
MAX_EVENT = 256 * 1024
EVENT_BYTES = 16 * 2**20
STDIO_BYTES = 48 * 2**20
MAX_COMMANDS = 4096
MAX_EVENTS = 4 * MAX_COMMANDS
ROLE_CAPS = {
    'git': 48 * 2**20, 'resolver': 16 * 2**20, 'systemd-state': 65536,
    'compiler-identity': 65536, 'historical-probe': 65536,
    'historical-daemon': 65536, 'native-resource': 4 * 2**20,
    'elf-metadata': 4 * 2**20, 'elf-loader': 4 * 2**20,
    'namespace-child': 48 * 2**20, 'semantic-producer': 48 * 2**20,
}
CALLSITES = {
    'git': 'initialize.git', 'systemd-state': 'produce_linux_root_seed.owner_binding', 'resolver': 'seed_resolution_catalog.capture_resolved_entry',
    'compiler-identity': 'mint_seed_support.compiler_identity',
    'historical-probe': 'seed_historical_surface.probe',
    'historical-daemon': 'seed_historical_surface.daemon',
    'native-resource': 'seed_native_resources.query', 'elf-metadata': 'seed_linux.metadata',
    'elf-loader': 'seed_linux.loader', 'namespace-child': 'seed_execution_launcher.command',
    'semantic-producer': 'WorkerContext.command',
}
# This literal shim is source-bound as part of this module. The same PID blocks
# on a parent-only pipe until both custodians have observed it, then fexecves
# the retained ELF FD. No candidate code or shell runs before that gate.
ENTRY = '''import os,sys,json,signal
fd,gate,parent,launcher=map(int,sys.argv[1:5])
argv,environment=json.loads(sys.argv[5])
os.close(launcher)
os.set_inheritable(fd,False)
allowed=os.getppid()==parent and os.read(gate,1)==b'G'
os.close(gate)
if not allowed: os._exit(125)
for name in ('SIGPIPE','SIGXFZ','SIGXFSZ'):
 value=getattr(signal,name,None)
 if value is not None: signal.signal(value,signal.SIG_DFL)
os.execve(fd,argv,environment)
'''


class Refusal(ValueError):
    pass


class CustodyFailure(Refusal):
    """Retains the exact child owner; never authorizes release or numeric kill."""
    def __init__(self, message, owner):
        super().__init__(message)
        self.owner = owner


def require(value, message):
    if not value:
        raise Refusal(message)


def remaining(end):
    require(type(end) in (int, float) and math.isfinite(end), 'no original finite endpoint')
    left = end - time.monotonic()
    require(left > 0, 'original endpoint expired')
    return left


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True,
                      allow_nan=False).encode() + b'\n'


def key(st):
    return (st.st_dev, st.st_ino, st.st_mode, st.st_size, st.st_mtime_ns, st.st_ctime_ns)


def process(pid):
    raw = Path(f'/proc/{pid}/stat').read_text()
    fields = raw[raw.rfind(')') + 2:].split()
    require(len(fields) >= 20, 'actual child stat is incomplete')
    rows = Path(f'/proc/{pid}/cgroup').read_text().splitlines()
    unified = [r[3:] for r in rows if r.startswith('0::')]
    require(len(unified) == 1 and unified[0].startswith('/'), 'actual child cgroup is absent')
    return {'pid': pid, 'parent': int(fields[1]), 'start': fields[19],
            'state': fields[0], 'cgroup': unified[0]}


def open_executable(literal, end):
    remaining(end)
    named = Path(literal)
    require(named.is_absolute() and len(named.parts) <= 64, 'executable must be an absolute bound path')
    actual = named.resolve(strict=True)
    before = actual.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_mode & 0o111
            and not before.st_mode & (stat.S_ISUID | stat.S_ISGID)
            and 0 < before.st_size <= MAX_EXECUTABLE, 'unadmitted executable file')
    fd = os.open(actual, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        require(key(os.fstat(fd)) == key(before), 'executable changed before open')
        value, total, head = hashlib.sha256(), 0, b''
        while True:
            remaining(end)
            block = os.read(fd, 1024 * 1024)
            if not block:
                break
            if not head:
                head = block[:4]
            total += len(block)
            require(total <= MAX_EXECUTABLE, 'executable grew past bound')
            value.update(block)
        require(head == b'\x7fELF', 'fixed entry supports ELF executable FDs only')
        require(total == before.st_size and key(os.fstat(fd)) == key(before)
                and key(actual.lstat()) == key(before) and named.resolve(strict=True) == actual,
                'executable changed during binding')
        os.lseek(fd, 0, os.SEEK_SET)
        row = {'literal': str(named), 'canonical': str(actual), 'key': list(key(before)),
               'sha256': value.hexdigest(), 'bytes': total}
        return fd, row
    except BaseException:
        os.close(fd)
        raise


def recheck_executable(fd, row):
    require(list(key(os.fstat(fd))) == row['key']
            and list(key(Path(row['canonical']).lstat())) == row['key']
            and Path(row['literal']).resolve(strict=True) == Path(row['canonical']),
            'held executable or literal resolution changed')


def verify_retained(fd, row, end):
    actual = os.fstat(fd)
    require(type(row['bytes']) is int and 0 < row['bytes'] == actual.st_size <= MAX_EXECUTABLE
            and stat.S_ISREG(actual.st_mode) and actual.st_mode & 0o111
            and not actual.st_mode & (stat.S_ISUID | stat.S_ISGID)
            and list(key(actual)) == row['key'],
            'parent-held executable identity changed')
    offset, value = 0, hashlib.sha256()
    while offset < row['bytes']:
        remaining(end)
        block = os.pread(fd, min(1024 * 1024, row['bytes'] - offset), offset)
        require(block, 'parent-held executable truncated')
        value.update(block)
        offset += len(block)
    require(list(key(os.fstat(fd))) == row['key'] and value.hexdigest() == row['sha256'],
            'independent parent-held executable bytes differ')


def validate_request(role, callsite, argv, cwd, environment, maximum, seconds):
    require(role in ROLE_CAPS and callsite == CALLSITES[role],
            'unknown fixed auxiliary role/callsite')
    require(type(argv) in (list, tuple) and argv and all(type(a) is str and '\0' not in a for a in argv),
            'argv must be an exact string vector')
    require(type(environment) is dict and all(type(k) is str and type(v) is str
            and k and '=' not in k and '\0' not in k + v for k, v in environment.items()),
            'environment must be the exact finite string map')
    require(type(maximum) is int and 0 < maximum <= ROLE_CAPS[role], 'role output bound failed')
    require(type(seconds) in (int, float) and math.isfinite(seconds) and 0 < seconds <= 86400,
            'command cap is not finite')
    cwd = Path(cwd)
    require(cwd.is_absolute() and cwd.resolve(strict=True) == cwd and cwd.is_dir(),
            'cwd is not an exact canonical directory')
    require(len(encoded([list(argv), str(cwd), environment])) <= MAX_VECTOR,
            'command vector/environment exceeds bound')
    return {'role': role, 'callsite': callsite, 'argv': list(argv), 'cwd': str(cwd),
            'environment': dict(environment), 'stdio_maximum': maximum, 'seconds_cap': seconds,
            'merge_stderr': role in ('semantic-producer', 'compiler-identity')}


def preflight():
    require(hasattr(os, 'pidfd_open') and hasattr(signal, 'pidfd_send_signal')
            and os.execve in os.supports_fd, 'stable child/ELF-FD execution is unavailable')
    require(signal.getsignal(signal.SIGCHLD) == signal.SIG_DFL,
            'SIGCHLD must retain actual waitable children; no auto-reap handler')


class Account:
    def __init__(self):
        self.events = self.event_bytes = self.stdio_bytes = self.commands = 0

    def command(self):
        require(self.commands < MAX_COMMANDS and self.events + 4 <= MAX_EVENTS,
                'auxiliary complete command/event account exhausted before spawn')
        self.commands += 1
        return self.commands - 1

    def event(self, raw):
        require(len(raw) <= MAX_EVENT and self.events < MAX_EVENTS
                and self.event_bytes + len(raw) <= EVENT_BYTES, 'auxiliary event account exhausted')
        self.events += 1
        self.event_bytes += len(raw)


class Spool:
    def __init__(self, root, name, maximum, account):
        self.path = Path(root) / name
        self.fd = os.open(self.path, os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
        self.maximum, self.account = maximum, account
        self.length = self.observed = 0
        self.sha = hashlib.sha256()
        self.truncated = self.closed = False

    def retain(self, block):
        self.observed += len(block)
        available = min(self.maximum - self.length, STDIO_BYTES - self.account.stdio_bytes)
        saved = block[:max(0, available)]
        if saved:
            view = memoryview(saved)
            while view:
                amount = os.write(self.fd, view)
                require(amount > 0, 'spool short write')
                view = view[amount:]
            self.sha.update(saved)
            self.length += len(saved)
            self.account.stdio_bytes += len(saved)
        self.truncated |= len(saved) != len(block)
        require(not self.truncated, 'live stdio hard retention limit exceeded')

    def row(self):
        return {'path': str(self.path), 'bytes': self.length, 'observed_bytes': self.observed,
                'sha256': self.sha.hexdigest(), 'truncated': self.truncated}

    def close(self):
        if not self.closed:
            os.fsync(self.fd)
            os.close(self.fd)
            self.closed = True
