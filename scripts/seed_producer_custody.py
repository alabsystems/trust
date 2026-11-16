#!/usr/bin/env python3
"""Connected live observation for original629; this stage grants NO RootSeed.

The trusted native controller calls observe() with its ORIGINAL already-held
four resource FDs and original deadline. There is deliberately no receipt-file
or general CLI entry point that can manufacture a completed-run capability.
The worker entry point is used only by that controller's actual owned scope.
"""
from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import re
import secrets
import shutil
import socket
import stat
import struct
import subprocess
import sys
import time
import types

MAX_PACKET = 1024 * 1024
MAX_EVENTS = 512
BOUND_FILES = (
    'CANDIDATE.json', 'INPUT-CLOSURE.json', 'stage2-self-host.json', 'stage2-ddc.json',
    'stage2-archive-rebuild.json', 'external-candidate-tree.json',
    'full-native-tree.json', 'packaged-native-tree.json', 'native-source-exclusions.json',
    'full-tools.json', 'packaged-native-tools.json', 'seed-surface.json',
    'inputs-before.json', 'inputs-after.json', 'common-inputs.json',
    'cargo-home-inputs.json', 'canonical-seed-installation-inputs.json',
    'native-runtime.json', 'packaged-native-runtime.json', 'seed-runtime.json',
)
ROOT629 = '629729f69eefb1cfe6ed766c6c01ee38aa7b0484'
_ENV = {'PATH': '/usr/bin:/bin', 'HOME': str(Path.home()), 'LANG': 'C', 'LC_ALL': 'C',
        'XDG_RUNTIME_DIR': f'/run/user/{os.getuid()}',
        'DBUS_SESSION_BUS_ADDRESS': f'unix:path=/run/user/{os.getuid()}/bus'}
_ISSUER = object()
_CLOSED = {}


def require(value, message):
    if not value:
        raise ValueError(message)


def remaining(end):
    value = end - time.monotonic()
    require(math.isfinite(value) and value > 0, 'original producer deadline expired')
    return value


def proc(pid):
    text = Path(f'/proc/{pid}/stat').read_text()
    fields = text[text.rfind(')') + 2:].split()
    return {'pid': pid, 'state': fields[0], 'parent': int(fields[1]), 'start': fields[19]}


def group(pid):
    rows = Path(f'/proc/{pid}/cgroup').read_text().splitlines()
    rows = [row[3:] for row in rows if row.startswith('0::')]
    require(len(rows) == 1 and rows[0].startswith('/'), 'no unique actual cgroup')
    return rows[0]


def regular(path, maximum=4 * 1024 * 1024):
    path = Path(path)
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_size <= maximum,
            'not a bounded regular file: ' + str(path))
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    try:
        key = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        require(key(os.fstat(fd)) == key(before), 'file changed before capture')
        data = bytearray()
        while len(data) <= maximum:
            block = os.read(fd, min(65536, maximum + 1 - len(data)))
            if not block:
                break
            data.extend(block)
        require(len(data) == before.st_size and key(os.fstat(fd)) == key(before)
                and key(path.lstat()) == key(before), 'file changed during capture')
        return bytes(data)
    finally:
        os.close(fd)


def digest(path, end):
    # Streaming bounded by the same original wall budget; never deserialize a
    # candidate's digest assertion as an actual file observation.
    path = Path(path)
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), 'artifact is not a regular file')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    value = hashlib.sha256()
    total = 0
    try:
        key = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        require(key(os.fstat(fd)) == key(before), 'artifact changed before open')
        while True:
            remaining(end)
            block = os.read(fd, 1024 * 1024)
            if not block:
                break
            total += len(block)
            value.update(block)
        require(total == before.st_size and key(os.fstat(fd)) == key(before)
                and key(path.lstat()) == key(before), 'artifact changed during capture')
        return value.hexdigest()
    finally:
        os.close(fd)


def exclusive(path, value):
    data = (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
    try:
        with os.fdopen(fd, 'wb', closefd=False) as output:
            output.write(data)
            output.flush()
            os.fsync(fd)
    finally:
        os.close(fd)


def send(channel, value, end):
    data = json.dumps(value, sort_keys=True, separators=(',', ':')).encode()
    require(len(data) <= MAX_PACKET, 'live event exceeds finite packet bound')
    channel.settimeout(remaining(end))
    require(channel.send(data) == len(data), 'partial live packet')


def receive(channel, end):
    channel.settimeout(remaining(end))
    data, ancillary, flags, address = channel.recvmsg(MAX_PACKET)
    require(data and not ancillary and not (flags & socket.MSG_TRUNC), 'missing or truncated live packet')
    return json.loads(data)


def git_directory(source):
    dot = source / '.git'
    if dot.is_dir() and not dot.is_symlink():
        return dot.resolve(strict=True)
    data = regular(dot, 4096).decode()
    require(data.startswith('gitdir: ') and data.endswith('\n') and data.count('\n') == 1,
            'source Git directory is not an owned canonical worktree')
    path = Path(data[8:-1])
    return (source / path).resolve(strict=True) if not path.is_absolute() else path.resolve(strict=True)


class OriginalLeaseCustody:
    """Actual inherited admission, never acquired or renewed by this helper.

    A trusted resource controller supplies its open FDs directly in memory.
    Constructing this object does not admit a heavy job: build-slot is still
    called normally in the native scope. It does not close/release these FDs.
    """
    def __init__(self, *, source, cargo_home, work, started, deadline, roles, source_hashes,
                 orchestration_root, extra_source_hashes=None):
        self.source, self.cargo_home, self.work = map(Path, (source, cargo_home, work))
        self.root = Path(orchestration_root)
        self.started, self.end = started, deadline
        require(type(started) in (int, float) and type(deadline) in (int, float)
                and math.isfinite(started) and math.isfinite(deadline)
                and 180 < deadline - started <= 86400 and started <= time.monotonic() < deadline,
                'original admission/deadline is invalid')
        for path in (self.source, self.cargo_home, self.root):
            require(path == path.resolve(strict=True), 'input root is not canonical')
        require(self.work == self.work.resolve(strict=False) and not self.work.exists(),
                'work root is not fresh and canonical')
        require(self.work.parent.resolve(strict=True).is_relative_to(self.source / 'build'),
                'work root escapes isolated source build directory')
        require(set(roles) == {'host', 'cargo', 'target', 'source'}, 'v2 requires all four original roles')
        self.roles = {name: (Path(path), fd) for name, (path, fd) in roles.items()}
        self.owner = proc(os.getpid())
        self.boot_id = Path('/proc/sys/kernel/random/boot_id').read_text().strip()
        require(re.fullmatch('[0-9a-f-]{36}', self.boot_id), 'kernel boot identity is absent')
        self.hashes, self.extra = dict(source_hashes), dict(extra_source_hashes or {})
        mandatory = {'scripts/seed_producer_custody.py','scripts/seed_custody_source.py',
                     'scripts/seed_producer_contract.py','scripts/produce_linux_root_seed.py',
                     'scripts/seed_input_records.py','scripts/seed_input_committed.py',
                     'scripts/seed_input_archives.py','scripts/seed_input_closure.py',
                     'scripts/bootstrap_dependency_closure.py',
                     'scripts/initialize_linux_root_seed.py','scripts/mint_seed_support.py',
                     'scripts/seed_host_ledger.py','scripts/seed_root_initialization.py',
                     'scripts/seed_historical_surface.py','scripts/seed_initialization_cohort.py',
                     'scripts/seed_observed_commands.py','scripts/seed_observed_io.py',
                     'scripts/seed_observed_events.py','scripts/seed_observed_git.py',
                     'scripts/lib/seed_linux.py','scripts/build-slot',
                     'src/tools/trust-stage0-dist/prepare.py','bootstrap/trust-linux-root-initialization.json'}
        require(mandatory <= set(self.hashes), 'live owner manifest omits custom execution/policy source')
        require(all(type(name) is str and type(value) is str and re.fullmatch('[0-9a-f]{64}', value)
                    for name,value in self.hashes.items()), 'original source manifest is malformed')
        require(self.roles['host'][0] == Path(f'/tmp/ay-oom-guard-{os.getuid()}.lock'),
                'host lease is not canonical')
        require(self.roles['source'][0] == git_directory(self.source) / 'build-slot.lock',
                'source lease is not the real worktree build-slot lock')
        # These are the original controller's named resource leases, never
        # arbitrary newly-created substitute lock files from the candidate.
        self.frozen = self.recheck(initial=True)

    def recheck(self, initial=False):
        remaining(self.end)
        require(proc(os.getpid())['start'] == self.owner['start']
                and Path('/proc/sys/kernel/random/boot_id').read_text().strip() == self.boot_id,
                'actual kernel/lease owner changed')
        locks = Path('/proc/locks').read_text().splitlines()
        rows, identities = [], set()
        for role, (path, fd) in sorted(self.roles.items()):
            require(type(fd) is int and fd >= 0 and path.is_absolute() and path == path.resolve(strict=True),
                    'lease FD/path is malformed')
            named, opened = path.lstat(), os.fstat(fd)
            require(stat.S_ISREG(named.st_mode) and named.st_uid == os.getuid() and named.st_nlink == 1
                    and (named.st_dev, named.st_ino) == (opened.st_dev, opened.st_ino),
                    'actual original FD no longer owns named lease')
            key = f'{os.major(opened.st_dev):02x}:{os.minor(opened.st_dev):02x}:{opened.st_ino}'
            require(any(row.split()[1:6] == ['FLOCK', 'ADVISORY', 'WRITE', str(os.getpid()), key]
                        for row in locks), 'actual exclusive original lease is absent')
            identities.add((opened.st_dev, opened.st_ino))
            rows.append({'role': role, 'path': str(path), 'fd': fd,
                         'device': opened.st_dev, 'inode': opened.st_ino})
        require(len(identities) == 4, 'original lease roles alias one file')
        if not initial:
            require(rows == self.frozen, 'original lease custody changed')
        return rows

    def recheck_source(self):
        self.recheck()
        for relative, expected in self.hashes.items():
            path = self.root / relative
            require(path.resolve(strict=True) == path and path.is_relative_to(self.root), 'source manifest escapes')
            require(hashlib.sha256(regular(path)).hexdigest() == expected, 'orchestration source changed')
        for name, expected in self.extra.items():
            path = Path(name)
            require(path.is_absolute() and path.resolve(strict=True) == path, 'extra source path is not canonical')
            require(hashlib.sha256(regular(path)).hexdigest() == expected, 'extra executed source changed')


def state(unit, end):
    result = subprocess.run(['/usr/bin/systemctl', '--user', 'show', unit,
        '--property=LoadState,ActiveState,SubState,InvocationID,ControlGroup,MemoryMax,MemorySwapMax,TasksMax,RuntimeMaxUSec'],
        env=_ENV, capture_output=True, text=True, check=True, timeout=min(10, remaining(end)))
    return dict(row.split('=', 1) for row in result.stdout.splitlines() if '=' in row)


def scope_identity(unit, peer, custody):
    actual = state(unit, custody.end)
    cg = actual.get('ControlGroup', '')
    require(actual.get('LoadState') == 'loaded' and actual.get('ActiveState') == 'active'
            and re.fullmatch('[0-9a-f]{32}', actual.get('InvocationID', ''))
            and cg == group(peer) and cg.endswith('/' + unit), 'worker is not in actual newly owned scope')
    require(actual.get('MemoryMax') == str(32 * 2**30) and actual.get('MemorySwapMax') == '0'
            and actual.get('TasksMax') == '256', 'native scope resource bounds changed')
    # The worker's source-bound owner_binding additionally parses RuntimeMaxUSec
    # under the original whole-run bound; never accept an unbounded scope.
    require(actual.get('RuntimeMaxUSec') not in (None, '', 'infinity'), 'scope is not finite')
    return actual


class ClosedProducerObservation:
    """Non-deserializable capability for observed command closure, NOT admission."""
    __slots__ = ('_issuer', '_custody', '_record', '_used')

    def __init__(self, issuer, custody, record):
        require(issuer is _ISSUER, 'no public completed-run constructor')
        self._issuer, self._custody, self._record, self._used = issuer, custody, record, False
        _CLOSED[id(self)] = self

    def summary(self):
        return json.loads(json.dumps(self._record))


def closed_capability(capability):
    require(type(capability) is ClosedProducerObservation and _CLOSED.get(id(capability)) is capability
            and capability._issuer is _ISSUER and not capability._used,
            'need this issuer registry\'s unused live closed-run capability')
    capability._custody.recheck_source()
    return capability


def observe(custody, *, native_arguments, control_directory):
    """Execute real source-bound producer, keep original custody, verify closure.

    On any failure this function writes no positive capability and NEVER releases
    original FDs. Caller must retain its resource controller/supervisor on an
    uncertain scope. It must not interpret an exception as permission to exit or
    unlock. This API does not signal any process, reset units, or mint a grant.
    """
    require(type(custody) is OriginalLeaseCustody, 'actual original custody required')
    custody.recheck_source()
    require(shutil.disk_usage(custody.work.parent).free >= 160 * 2**30,
            'historical full producer needs its original 128GiB growth plus 32GiB reserve admission')
    control = Path(control_directory)
    require(control == control.resolve(strict=False) and not control.exists(), 'control root is not fresh')
    control.mkdir(mode=0o700)
    require(not control.is_relative_to(custody.source), 'control root must be outside worktree for normal build-slot')
    token = secrets.token_hex(32)
    unit = 'trust-original629-' + secrets.token_hex(12) + '.scope'
    worker = custody.root / 'scripts/seed_producer_custody.py'
    worker_sha = custody.hashes.get('scripts/seed_producer_custody.py')
    require(worker_sha and hashlib.sha256(regular(worker)).hexdigest() == worker_sha, 'worker source is unbound')
    native_arguments = list(native_arguments)
    allowed = {'source-root','std-source-archive','config','cargo-home','work-dir',
               'legacy-receipt','legacy-archives','legacy-manifest','host',
               'genesis-manifest','genesis-archives','genesis-sysroot',
               'ddc-manifest','ddc-archives','ddc-sysroot'}
    require(len(native_arguments) == 2 * len(allowed), 'all native arguments must be exact key/value pairs')
    arguments = dict(zip(native_arguments[::2], native_arguments[1::2]))
    require(set(arguments) == {'--' + name for name in allowed}, 'duplicate, abbreviated or unknown native argument')
    require(arguments['--source-root'] == str(custody.source)
            and arguments['--work-dir'] == str(custody.work)
            and arguments['--cargo-home'] == str(custody.cargo_home), 'actual producer roots differ from original grant')
    payload = {'schema': 'trust.root-producer-live-control.v1', 'token': token, 'root': str(custody.root),
               'hashes': custody.hashes, 'extra_sources': custody.extra, 'deadline': custody.end,
               'started': custody.started, 'work_end': custody.end - 120, 'cleanup_end': custody.end,
               'arguments': native_arguments, 'work': str(custody.work), 'source': str(custody.source),
               'cargo_home': str(custody.cargo_home)}
    exclusive(control / 'CONTROL.json', payload)
    listener = socket.socket(socket.AF_UNIX, socket.SOCK_SEQPACKET | socket.SOCK_CLOEXEC)
    process = channel = None
    record = {'schema': 'trust.original629-closed-observation.v1', 'boot_id': custody.boot_id,
              'uid': os.getuid(), 'admitted_root_seed': False,
              'counts_as_trust_stage0_evidence': False, 'source_commit': ROOT629, 'events': [],
              'native_arguments': dict(arguments), 'input_seals': []}
    try:
        listener.bind(str(control / 'events.sock'))
        listener.listen(1)
        # This leaves 120 seconds INSIDE the same original deadline for closure
        # and physical captures. There is no new deadline after scope exit.
        seconds = math.floor(remaining(custody.end) - 120)
        require(seconds > 0, 'original whole-run budget has no native room')
        argv = ['/usr/bin/systemd-run', '--user', '--scope', '--unit=' + unit,
                '--property=MemoryMax=32G', '--property=MemorySwapMax=0', '--property=TasksMax=256',
                '--property=RuntimeMaxSec=' + str(seconds), '--',
                '/usr/bin/python3', '-I', '-S', '-B', str(custody.root / 'scripts/build-slot'), '--mem-gb', '48', '--',
                '/usr/bin/python3', '-I', '-S', '-B', str(worker), '--worker', str(control)]
        log = open(control / 'worker.log', 'xb')
        try:
            process = subprocess.Popen(argv, cwd=control, env=_ENV, stdin=subprocess.DEVNULL,
                                       stdout=log, stderr=subprocess.STDOUT, close_fds=True)
            launch = proc(process.pid)
            listener.settimeout(remaining(custody.end))
            channel, address = listener.accept()
            credentials = struct.unpack('3i', channel.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))
            pid, uid, gid = credentials
            require(uid == os.getuid(), 'live peer has another UID')
            hello = receive(channel, custody.end)
            peer = proc(pid)
            require(hello == {'kind': 'hello', 'token': token, 'pid': pid, 'start': peer['start']},
                    'worker handshake differs from actual kernel peer')
            # The owned systemd-run/build-slot chain must actually lead to peer.
            ancestors, current = set(), peer
            for depth in range(32):
                ancestors.add(current['pid'])
                if current['pid'] == process.pid:
                    break
                require(current['parent'] > 1, 'worker is not descended from actual owned launcher')
                current = proc(current['parent'])
            require(process.pid in ancestors and proc(process.pid)['start'] == launch['start'],
                    'worker launch PID identity changed')
            actual = scope_identity(unit, pid, custody)
            cg = actual['ControlGroup']
            owner = {'schema': 'trust.linux-root-producer-owner.v2', 'host': None,
                     'started_monotonic': custody.started, 'deadline_monotonic': custody.end,
                     'lease_owner_pid': os.getpid(), 'lease_owner_start_ticks': custody.owner['start'],
                     'leases': custody.recheck(), 'cargo_lease_path': str(custody.roles['cargo'][0]),
                     'target_lease_path': str(custody.roles['target'][0]),
                     'source_lease_path': str(custody.roles['source'][0]), 'source_root': str(custody.source),
                     'cargo_home': str(custody.cargo_home), 'work_dir': str(custody.work),
                     'unit': unit, 'invocation_id': actual['InvocationID'], 'control_group': cg}
            # host is parsed and measured by the source-bound producer, then
            # independently checked against the Linux-only original policy.
            owner['host'] = hello_host(native_arguments)
            exclusive(control / 'OWNER.json', owner)
            send(channel, {'kind': 'go', 'token': token}, custody.end)
            auxiliary_module = canonical_loader(custody).module('trust_seed_observed_events',
                custody.root / 'scripts/seed_observed_events.py')
            auxiliary = auxiliary_module.AuxiliaryObserver(worker_pid=pid, worker_start=peer['start'],
                cgroup=cg, started=custody.started, work_end=custody.end - 120, cleanup_end=custody.end,
                spool_root=control / 'auxiliary')
            custody._auxiliary_live = auxiliary
            live_children = {}
            done = False
            while not done:
                custody.recheck()
                event = receive(channel, custody.end)
                if type(event) is dict and event.get('kind') == 'auxiliary-chunk':
                    require(event.get('token') == token and event.get('original_deadline') == custody.end
                            and event.get('aux_sequence') == auxiliary.account.events,
                            'auxiliary channel authentication/order changed')
                    auxiliary.accept(event.get('chunk'))
                    send(channel, {'aux_ack': event['aux_sequence']}, custody.end)
                    continue
                require(type(event) is dict and event.get('sequence') == len(record['events'])
                        and event.get('token') == token and len(record['events']) < MAX_EVENTS,
                        'live event order/authentication bound failed')
                require(event.get('original_deadline') == custody.end
                        and custody.started <= event.get('at', -1) <= time.monotonic() < custody.end,
                        'live event renewed original deadline or time')
                kind = event.get('kind')
                if kind == 'child-start':
                    child = proc(event['pid'])
                    require(child['start'] == event['start'] and child['parent'] == pid
                            and group(child['pid']) == cg and event['phase'] not in live_children,
                            'reported native child is not actual worker-owned scope member')
                    auxiliary.semantic_child(event['phase'],child['pid'],child['start'])
                    live_children[event['phase']] = child
                elif kind == 'child-reaped':
                    child = live_children.pop(event.get('phase'), None)
                    require(child is not None and event.get('pid') == child['pid']
                            and event.get('start') == child['start'] and event.get('returncode') == 0,
                            'native child failed or did not complete observed launch')
                    require(not Path(f'/proc/{child["pid"]}').exists(), 'native child not actually reaped')
                elif kind == 'input-seal':
                    stages = ('before','private-import','common-self-host','common-ddc','installers','after')
                    reference = event.get('reference')
                    require(len(record['input_seals']) < len(stages)
                            and event.get('stage') == stages[len(record['input_seals'])]
                            and type(reference) is dict and set(reference) == {'sha256','bytes'}
                            and type(reference['sha256']) is str and re.fullmatch('[0-9a-f]{64}', reference['sha256'])
                            and type(reference['bytes']) is int and 0 < reference['bytes'] <= 4 * 1024 * 1024
                            and not live_children, 'original physical input seal is missing/reordered/unbounded')
                    record['input_seals'].append({'stage':event['stage'],'reference':dict(reference)})
                elif kind == 'done':
                    require(len(record['input_seals']) == 6, 'actual producer omitted original physical input stages')
                    require(set(event.get('bound_files', {})) == set(BOUND_FILES)
                            and all(re.fullmatch('[0-9a-f]{64}', value) for value in event['bound_files'].values())
                            and re.fullmatch('[0-9a-f]{64}', event.get('native_pack_sha256', '')),
                            'live completion omitted actual retained file captures')
                    require(not live_children, 'producer completed with unclosed native child')
                    require(auxiliary.semantic_count == 17, 'original semantic phase count changed')
                    record['auxiliary_direct_observation'] = auxiliary.finish(event['auxiliary_summary'])
                    record['auxiliary_chunks'] = auxiliary.capture_auxiliary_chunks(control / 'auxiliary-chunks')
                    record['auxiliary_scope_complete'] = False
                    done = True
                else:
                    require(kind in ('span-begin', 'span-end'), 'unexpected live event')
                record['events'].append(event)
                send(channel, {'ack': event['sequence']}, custody.end)
            require(process.wait(timeout=remaining(custody.end)) == 0, 'actual owned launcher failed')
        finally:
            log.close()
        require(not Path(f'/proc/{pid}').exists(), 'native worker still exists after launcher reap')
        closed = state(unit, custody.end)
        require(closed.get('LoadState') == 'not-found' and not closed.get('InvocationID')
                and not closed.get('ControlGroup') and closed.get('ActiveState') == 'inactive'
                and not (Path('/sys/fs/cgroup') / cg.lstrip('/')).exists(),
                'native scope is active, failed-retained or physical closure is uncertain')
        custody.recheck_source()
        candidate = json.loads(regular(custody.work / 'CANDIDATE.json'))
        require(candidate.get('source_commit') == ROOT629 and candidate.get('passed') is True
                and candidate.get('phase_count') == 17 and candidate.get('admitted_root_seed') is False,
                'source-bound producer did not finish exact historical candidate')
        require(digest(custody.work / 'CANDIDATE.json', custody.end)
                == record['events'][-1]['bound_files']['CANDIDATE.json'], 'live candidate bytes changed before closure capture')
        record.update({'owner': owner, 'actual_worker': peer, 'actual_launcher': launch,
                       'actual_closed_unit': closed, 'native_cgroup_absent': cg,
                       'bound_files': record['events'][-1]['bound_files'],
                       'native_pack_sha256': record['events'][-1]['native_pack_sha256'],
                       'candidate_sha256': digest(custody.work / 'CANDIDATE.json', custody.end),
                       'worker_log_sha256': digest(control / 'worker.log', custody.end),
                       'completed_monotonic': time.monotonic(),
                       'remaining': 'physical input/package closure and canonical GENESIS transaction; no RootSeed admission'})
        exclusive(control / 'CLOSED-OBSERVATION.json', record)
        remaining(custody.end)
        return ClosedProducerObservation(_ISSUER, custody, record)
    except BaseException as error:
        # No broad pkill, no foreign unit reset, no renewed timeout. The original
        # controller retains its FDs and must supervise actual closure on failure.
        exclusive(control / 'NEGATIVE.json', {'passed': False, 'admitted_root_seed': False,
            'error': str(error), 'original_deadline': custody.end, 'unit': unit,
            'owned_launcher_pid': process.pid if process else None,
            'requires_original_owner_custody_until_actual_closure': True,
            'auxiliary_partial': custody._auxiliary_live.negative_snapshot() if hasattr(custody,'_auxiliary_live') else None})
        raise
    finally:
        if channel is not None:
            channel.close()
        listener.close()


def hello_host(arguments):
    require(arguments.count('--host') == 1, 'live controller must give one explicit native Linux host')
    index = arguments.index('--host')
    require(index + 1 < len(arguments), 'native host value is absent')
    host = arguments[index + 1]
    require(host in ('aarch64-unknown-linux-gnu', 'x86_64-unknown-linux-gnu'), 'not a supported Linux host')
    return host


class WorkerContext:
    def __init__(self, channel, payload, graph, loader, control):
        self.channel, self.payload, self.graph = channel, payload, graph
        self.sequence, self.active_span = 0, None
        module = loader.module('trust_seed_observed_commands', Path(payload['root']) / 'scripts/seed_observed_commands.py')
        self.observed = module.ObservedCommands(started=payload['started'], work_end=payload['work_end'],
            cleanup_end=payload['cleanup_end'], spool_root=Path(control) / 'auxiliary', emit=self.auxiliary_event)

    def event(self, kind, **values):
        value = {'kind': kind, 'sequence': self.sequence, 'token': self.payload['token'],
                 'at': time.monotonic(), 'original_deadline': self.payload['deadline'], **values}
        send(self.channel, value, self.payload['deadline'])
        require(receive(self.channel, self.payload['deadline']) == {'ack': self.sequence}, 'observer ACK changed')
        self.sequence += 1

    def auxiliary_event(self, chunk):
        sequence = chunk['rows'][0]['aux_sequence']
        send(self.channel, {'kind':'auxiliary-chunk', 'token':self.payload['token'],
             'original_deadline':self.payload['deadline'], 'aux_sequence':sequence, 'chunk':chunk},
             self.payload['cleanup_end'])
        require(receive(self.channel, self.payload['cleanup_end']) == {'aux_ack':sequence},
                'original auxiliary observer ACK changed')

    def auxiliary(self, role, callsite, argv, cwd, environment, *, maximum=65536, seconds=60, raw=False):
        receipt = self.observed.run_observed(role, callsite, argv, cwd, environment,
                                             maximum=maximum, seconds=seconds)
        stdout = self.observed.read_output(receipt, 'stdout', maximum)
        stderr = self.observed.read_output(receipt, 'stderr', maximum)
        return subprocess.CompletedProcess(argv, receipt['returncode'],
            stdout if raw else stdout.decode('utf-8'), stderr if raw else stderr.decode('utf-8'))

    def span_begin(self, name):
        require(self.active_span is None, 'nested span is not supported')
        self.graph.span(name)
        self.active_span = name
        self.event('span-begin', name=name)

    def span_end(self, name):
        require(self.active_span == name, 'actual span was not started')
        self.event('span-end', name=name)
        self.active_span = None

    def command(self, phase, argv, cwd, environment, output, timeout):
        self.graph.command(phase, argv, cwd, environment)
        child = self.observed.open_object_reader('semantic-producer', 'WorkerContext.command',
            argv, cwd, environment, maximum=48 * 2**20,
            seconds=timeout, input_pipe=False, semantic_phase=phase)
        self.event('child-start', phase=phase, argv=argv, cwd=str(cwd), environment=environment,
                   pid=child.child.pid, start=child.identity['start'])
        receipt = child.finish_observed_child()
        self.observed.copy_output(receipt, output)
        self.event('child-reaped', phase=phase, pid=receipt['pid'], start=receipt['start'],
                   returncode=receipt['returncode'])
        return receipt['returncode']


def worker(control):
    require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode,
            'live worker requires Python -I -S -B')
    control = Path(control)
    require(control == control.resolve(strict=True) and stat.S_IMODE(control.stat().st_mode) == 0o700,
            'live control root is not canonical private directory')
    payload = json.loads(regular(control / 'CONTROL.json'))
    remaining(payload['deadline'])
    root = Path(payload['root'])
    # This raw-byte bootstrap never asks SourceFileLoader for cached bytecode.
    path = root / 'scripts/seed_custody_source.py'
    raw = regular(path)
    require(hashlib.sha256(raw).hexdigest() == payload['hashes'].get('scripts/seed_custody_source.py'),
            'source loader bytes are not in original controller manifest')
    module = types.ModuleType('trust_custody_source')
    module.__file__ = str(path)
    exec(compile(raw, str(path), 'exec', dont_inherit=True), module.__dict__)
    loader = module.BoundSourceLoader(root, payload['hashes'], extra_sources=payload['extra_sources'])
    # Imports may inspect helpers before the socket handshake. They may not
    # fall back to standalone child execution in this worker's pending state.
    loader.begin_observed_execution()
    contract = loader.module('trust_producer_contract', root / 'scripts/seed_producer_contract.py')
    # Producer loads all custom helpers through this one canonical module cache.
    producer = loader.module('trust_live_producer', root / 'scripts/produce_linux_root_seed.py')
    channel = socket.socket(socket.AF_UNIX, socket.SOCK_SEQPACKET | socket.SOCK_CLOEXEC)
    channel.settimeout(remaining(payload['deadline']))
    channel.connect(str(control / 'events.sock'))
    identity = proc(os.getpid())
    send(channel, {'kind': 'hello', 'token': payload['token'], 'pid': os.getpid(), 'start': identity['start']}, payload['deadline'])
    require(receive(channel, payload['deadline']) == {'kind': 'go', 'token': payload['token']}, 'no actual owner GO')
    graph = contract.CommandGraph(Path(payload['source']), Path(payload['work']),
                                  hello_host(payload['arguments']), payload['deadline'], producer.xpy, root,
                                  producer.support.dist_producer_components(Path(payload['source'])))
    live = WorkerContext(channel, payload, graph, loader, control)
    producer.__trust_live_context__ = live
    # Context is installed before execution, not reconstructed from artifacts.
    loader.bind_observed_execution(live)
    argv = [*payload['arguments'], '--owner', str(control / 'OWNER.json')]
    require(producer.main(argv) == 0, 'actual native producer failed')
    require(live.active_span is None, 'producer returned inside live span')
    graph.finish()
    loader.recheck()
    bindings = {name: hashlib.sha256(regular(Path(payload['work']) / name)).hexdigest() for name in BOUND_FILES}
    native_pack = Path(payload['work']) / f'trust-native-{ROOT629[:12]}-{hello_host(payload["arguments"])}.tar.xz'
    live.event('done', bound_files=bindings, native_pack_sha256=digest(native_pack, payload['deadline']),
               auxiliary_summary=live.observed.finish())
    channel.close()


def canonical_loader(custody):
    """One parent-side module identity for all physical helper aliases."""
    if hasattr(custody, '_loader'):
        return custody._loader
    path = custody.root / 'scripts/seed_custody_source.py'
    raw = regular(path)
    require(hashlib.sha256(raw).hexdigest() == custody.hashes.get('scripts/seed_custody_source.py'),
            'physical source loader is unbound')
    module = types.ModuleType('trust_parent_custody_source')
    module.__file__ = str(path)
    exec(compile(raw, str(path), 'exec', dont_inherit=True), module.__dict__)
    custody._loader = module.BoundSourceLoader(custody.root, custody.hashes, extra_sources=custody.extra)
    return custody._loader


def physical_tree(root, end):
    """Same canonical records as stage2_manifest, with FD-relative nofollow IO.

    Every discovered directory is walked physically; literal symlink values are
    data, including the two policy-scoped source-root links. No link is followed
    to read a regular payload. This is a bounded post-close observation under
    retained exclusive cooperative custody, not an adversarial filesystem lock.
    """
    root = Path(root)
    require(root == root.resolve(strict=True) and root.is_dir(), 'physical artifact root is not canonical')
    first = root.lstat()
    records, size = [], 0
    def failed(error):
        raise error
    for directory, dirs, files, parent_fd in os.fwalk(root, follow_symlinks=False, onerror=failed):
        dirs.sort()
        files.sort()
        for name in (*dirs, *files):
            remaining(end)
            require(len(records) < 2_000_000, 'physical artifact exceeds existing member bound')
            metadata = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
            relative = (Path(directory) / name).relative_to(root).as_posix()
            if stat.S_ISLNK(metadata.st_mode):
                row = {'path': relative, 'kind': 'symlink', 'target': os.readlink(name, dir_fd=parent_fd)}
            elif stat.S_ISDIR(metadata.st_mode):
                row = {'path': relative, 'kind': 'directory', 'mode': stat.S_IMODE(metadata.st_mode)}
            else:
                require(stat.S_ISREG(metadata.st_mode), 'physical artifact contains special file')
                size += metadata.st_size
                require(size <= 64 * 2**30, 'physical artifact exceeds existing expanded-byte bound')
                fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC, dir_fd=parent_fd)
                value, length = hashlib.sha256(), 0
                try:
                    key = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
                    require(key(os.fstat(fd)) == key(metadata), 'physical artifact changed before open')
                    while True:
                        remaining(end)
                        block = os.read(fd, 1024 * 1024)
                        if not block:
                            break
                        length += len(block)
                        value.update(block)
                    require(length == metadata.st_size and key(os.fstat(fd)) == key(metadata)
                            and key(os.stat(name, dir_fd=parent_fd, follow_symlinks=False)) == key(metadata),
                            'physical artifact changed during read')
                finally:
                    os.close(fd)
                row = {'path': relative, 'kind': 'file', 'mode': stat.S_IMODE(metadata.st_mode),
                       'bytes': metadata.st_size, 'sha256': value.hexdigest()}
            again = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
            require((again.st_dev, again.st_ino, again.st_mode, again.st_size, again.st_mtime_ns, again.st_ctime_ns)
                    == (metadata.st_dev, metadata.st_ino, metadata.st_mode, metadata.st_size, metadata.st_mtime_ns, metadata.st_ctime_ns),
                    'physical entry changed during observation')
            records.append(row)
    require((root.lstat().st_dev, root.lstat().st_ino) == (first.st_dev, first.st_ino),
            'physical artifact root identity changed')
    return records


def verify_artifact_candidate(capability, *, output):
    """Consume a real closed observation; reopen DDC/rebuild/native artifacts.

    This is the first coherent end-to-end observation unit. It intentionally
    cannot call make_genesis or create a host record. Full input closure, all
    auxiliary process observations, canonical retained DDC/rebuild packaging and
    the ledger transaction are required before a future admitting capability.
    """
    cap = closed_capability(capability)
    cap._used = True
    custody, record = cap._custody, cap._record
    work, end = custody.work, custody.end
    closed = state(record['owner']['unit'], end)
    require(closed.get('LoadState') == 'not-found' and not closed.get('InvocationID')
            and not closed.get('ControlGroup')
            and not (Path('/sys/fs/cgroup') / record['native_cgroup_absent'].lstrip('/')).exists(),
            'physical verification cannot precede actual native closure')
    bindings = record['bound_files']
    documents = {}
    for name in BOUND_FILES:
        data = regular(work / name)
        require(hashlib.sha256(data).hexdigest() == bindings[name], 'retained live-captured evidence changed: ' + name)
        documents[name] = json.loads(data)
    require(documents['inputs-before.json'] == documents['inputs-after.json'],
            'actual producer input endpoints differ')
    loader = canonical_loader(custody)
    support = loader.module('trust_physical_support', custody.root / 'scripts/mint_seed_support.py')
    initialization = loader.module('trust_physical_initialization', custody.root / 'scripts/seed_root_initialization.py')
    physical_inputs = loader.module('trust_physical_input_closure', custody.root / 'scripts/seed_input_closure.py')
    input_coverage = physical_inputs.verify_closed_inputs(custody, record, documents, loader)
    host = record['owner']['host']
    left = initialization.tree_manifest(regular(work / 'stage2-self-host.json'), host)
    right = initialization.tree_manifest(regular(work / 'stage2-ddc.json'), host)
    rebuilt = initialization.tree_manifest(regular(work / 'stage2-archive-rebuild.json'), host)
    require(left == right == rebuilt, 'canonical retained DDC/archive-rebuild records disagree')
    joins = {}
    for name, manifest in [('comparison-ddc', right), ('comparison-archive-rebuild', rebuilt)]:
        rows = physical_tree(work / name / host / 'stage2', end)
        require(rows == manifest['records'], 'physical independent compiler tree differs from actual compared records')
        joins[name] = support.records_sha256(rows)
    for name in ('full-native-tree.json','packaged-native-tree.json','external-candidate-tree.json'):
        manifest = documents[name]
        require(manifest.get('schema') == 'trust-stage2-tree-v1'
                and support.records_sha256(manifest['records']) == manifest.get('sha256'),
                'retained artifact record digest is not canonical')
    native = physical_tree(work / 'comparison-build' / host / 'stage2', end)
    indexed = {row['path']: row for row in native}
    require(all(indexed.get(row['path']) == row for row in left['records']),
            'later dist/tool copies changed an original self-host kind/mode/byte/literal link')
    require(native == documents['full-native-tree.json']['records'], 'physical full-native tree changed')
    # Added native frontend files belong to full-native coverage, never to the
    # original compiler/std DDC comparison just checked above.
    projected, omitted = initialization.native_projection(documents['full-native-tree.json'], custody.source)
    installed = physical_tree(work / 'native-installation', end)
    require(installed == projected == documents['packaged-native-tree.json']['records'],
            'physical unpacked native artifact differs from exact policy projection')
    candidate = physical_tree(work / 'external-build' / host / 'stage2', end)
    require(candidate == documents['external-candidate-tree.json']['records'], 'common external candidate/driver changed')
    native_pack = work / f'trust-native-{ROOT629[:12]}-{host}.tar.xz'
    require(digest(native_pack, end) == record['native_pack_sha256'], 'actual live-produced native package changed')
    # Runtime-provider endpoints are reopened without running a new loader probe
    # outside the now-closed native scope. This preserves the observation grade.
    for filename in ('native-runtime.json', 'packaged-native-runtime.json', 'seed-runtime.json'):
        runtime = documents[filename]
        require(runtime.get('checked') is True and runtime.get('format') == 'elf'
                and runtime.get('observations') and not runtime.get('unresolved'), 'runtime observation is incomplete')
        for name, expected in runtime['observations'].items():
            if expected is None:
                require(not Path(name).exists() and not Path(name).is_symlink(), 'optional runtime endpoint appeared')
            else:
                require(digest(Path(name), end) == expected, 'actual runtime provider endpoint changed')
        for name, expected in runtime.get('links', {}).items():
            require(str(Path(name).resolve(strict=True)) == expected, 'actual runtime provider path changed')
    loader.recheck()
    custody.recheck_source()
    remaining(end)
    result = {'schema': 'trust.original629-physical-artifact-candidate.v1', 'passed_artifact_joins': True,
              'admitted_root_seed': False, 'counts_as_trust_stage0_evidence': False,
              'current_toolchain_qualification': False, 'source_commit': ROOT629,
              'closed_observation_sha256': hashlib.sha256(json.dumps(record, sort_keys=True).encode()).hexdigest(),
              'ddc_compiler_record_sha256': left['sha256'], 'physical_independent_trees': joins,
              'physical_full_native_sha256': support.records_sha256(native),
              'native_pack_sha256': record['native_pack_sha256'],
              'retained_source_root_links': omitted, 'original_deadline': end,
              'physical_input_coverage': input_coverage,
              'completed_monotonic': time.monotonic(),
              'remaining': ['resolve every typed physical-input refusal; complete closure remains false',
                            'bounded raw PID/log/timing for every auxiliary compiler/ELF/runtime probe',
                            'canonical persistent DDC/rebuild/package closure independent of original paths',
                            'canonical GENESIS/combined host-ledger transaction and trusted replay anchor']}
    exclusive(Path(output), result)
    remaining(end)
    return result


if __name__ == '__main__':
    require(len(sys.argv) == 3 and sys.argv[1] == '--worker',
            'no file-only controller/admission CLI; call observe with actual original lease FDs')
    worker(sys.argv[2])
