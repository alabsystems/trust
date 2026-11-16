"""Execute authenticated source bytes, never a timestamp-selected bytecode cache.

The live owner supplies this loader directly in memory. Artifacts cannot supply
its manifest. The standalone fallback in legacy helpers remains non-admitting.
"""
from __future__ import annotations
import hashlib
import math
import os
from pathlib import Path
import stat
import sys
import time
import types

MAX_SOURCE = 4 * 1024 * 1024
MAX_CAPTURED_SOURCES = 256
MAX_CAPTURED_BYTES = 32 * 1024 * 1024
MAX_NATIVE_SOURCE_PACKET = 320 * 1024 * 1024
MAX_NATIVE_SOURCE_RESULT = 64 * 1024 * 1024


def _native_endpoint(end_ns, label='native projection'):
    if type(end_ns) is not int or not 0 < end_ns < 2**64:
        raise ValueError(label + ' requires the original finite clock endpoint')
    raw_clock = getattr(time, 'CLOCK_UPTIME_RAW', None)
    if raw_clock is None:
        raise ValueError(label + ' requires its shared original uptime clock')
    before = time.clock_gettime_ns(raw_clock)
    sampled = time.monotonic_ns()
    after = time.clock_gettime_ns(raw_clock)
    if not before <= sampled <= after or after >= end_ns:
        raise ValueError(label + ' clock differs or original endpoint expired')
    end = end_ns / 1_000_000_000
    # Same projection conversion: rounding may only shorten the original end.
    while True:
        numerator, denominator = end.as_integer_ratio()
        if numerator * 1_000_000_000 <= end_ns * denominator:
            break
        end = math.nextafter(end, -math.inf)
    return end, raw_clock


def _native_directory(value, descriptor, label='native projection'):
    import fcntl
    if type(value) is not str:
        raise ValueError(label + ' requires its original canonical directory')
    path = Path(value)
    info = os.fstat(descriptor); named = path.lstat()
    if (not stat.S_ISDIR(info.st_mode) or not stat.S_ISDIR(named.st_mode)
            or path.resolve(strict=True) != path or info.st_mode & 0o022
            or info.st_uid != os.geteuid()
            or (info.st_dev, info.st_ino) != (named.st_dev, named.st_ino)
            or fcntl.fcntl(descriptor, fcntl.F_GETFL) & os.O_ACCMODE != os.O_RDONLY):
        raise ValueError(label + ' differs from the retained original directory')
    return path


def _native_descriptions(label='native projection'):
    # Exact original nineteen-slot shape. Shape creates no native owner.
    directories = {6, 7, 10, 14, 16, 18, 19, 20}
    for descriptor in range(3, 22):
        info = os.fstat(descriptor)
        kind = stat.S_ISFIFO if descriptor in (3, 4) else stat.S_ISDIR if descriptor in directories else stat.S_ISREG
        if not kind(info.st_mode):
            raise ValueError(label + ' lacks its complete original descriptor layout')


def _native_canonical_loader(root, sources, label):
    paths = {'scripts/seed_custody_source.py', 'scripts/mint_seed_support.py',
             'src/bootstrap/stage0_identity.py'}
    if type(sources) is not dict or sources.keys() != paths:
        raise ValueError(label + ' requires its complete fixed source capture')
    captured, expected = {}, {}
    for name, item in sources.items():
        if (type(item) is not dict or item.keys() != {'hex', 'sha256'}
                or type(item['hex']) is not str or len(item['hex']) > MAX_SOURCE * 2
                or type(item['sha256']) is not str or len(item['sha256']) != 64):
            raise ValueError(label + ' has invalid bounded source data')
        captured[name] = bytes.fromhex(item['hex']); expected[name] = item['sha256']
    return BoundSourceLoader(root, expected, captured_sources=captured)


def _native_seed_selection(packet):
    """Fixed SAME-source planner BODY; its result is only selection DATA.

    The resident retains its actual committed pin/code, archives, fresh producer,
    caller/private caches, SDK/GNU and original end through real native closure.
    Packet hashes and this result cannot construct or complete those owners.
    """
    label = 'native seed selection'
    if (type(packet) is not dict or packet.keys() != {
            'schema', 'source_root', 'host', 'pin', 'sources', 'end_ns', 'clock'}
            or packet['schema'] != 'trust-native-seed-selection-v1'
            or packet['clock'] != 'darwin-mach-uptime-raw-v1'
            or sys.platform != 'darwin'):
        raise ValueError('outside the fixed native seed selection profile')
    end, raw_clock = _native_endpoint(packet['end_ns'], label)
    _native_descriptions(label)
    root = _native_directory(packet['source_root'], 6, label)
    if type(packet['host']) is not str or len(packet['host']) > 128:
        raise ValueError('native seed selection requires its exact native host')
    pin = packet['pin']
    if (type(pin) is not dict or pin.keys() != {'hex', 'sha256'}
            or type(pin['hex']) is not str or len(pin['hex']) > MAX_SOURCE * 2
            or type(pin['sha256']) is not str or len(pin['sha256']) != 64):
        raise ValueError('native seed selection has invalid bounded pin DATA')
    raw = bytes.fromhex(pin['hex'])
    if hashlib.sha256(raw).hexdigest() != pin['sha256']:
        raise ValueError('native seed selection pin transport differs')
    loader = _native_canonical_loader(root, packet['sources'], label)
    result = loader.select_seed_archives_from_capture(raw, packet['host'], deadline=end)
    _native_directory(packet['source_root'], 6, label)
    if time.clock_gettime_ns(raw_clock) >= packet['end_ns']:
        raise ValueError('native seed selection original endpoint expired')
    return result


def _native_projection(packet):
    """Fixed interpreter entry DATA; only the native issuer supplies owners.

    The resident must retain its same source/config, archive population, fresh
    producer, physical/private caches, control SDK, GNU loan and real native
    closure. Descriptor shape and this packet create none of those capabilities.
    No CLI, installer, fetch, SDK/Seed conversion or release is provided here.
    """
    if (type(packet) is not dict or packet.keys() != {
            'schema', 'source_root', 'destination', 'top', 'commit', 'component',
            'sources', 'end_ns', 'clock'}
            or packet['schema'] != 'trust-native-component-projection-v1'
            or packet['clock'] != 'darwin-mach-uptime-raw-v1'
            or sys.platform != 'darwin'):
        raise ValueError('outside the fixed native projection packet profile')
    end_ns = packet['end_ns']
    end, raw_clock = _native_endpoint(end_ns)
    _native_descriptions()
    root = _native_directory(packet['source_root'], 6)
    destination = _native_directory(packet['destination'], 20)
    if any(type(packet[name]) is not str for name in ('top', 'commit', 'component')):
        raise ValueError('native projection requires its exact component selection')
    loader = _native_canonical_loader(root, packet['sources'], 'native projection')
    count = loader.project_for_preparation_fd(13, destination, packet['top'],
        packet['commit'], packet['component'], deadline=end)
    # Include the SAME original directory names after the canonical postcheck.
    _native_directory(packet['source_root'], 6); _native_directory(packet['destination'], 20)
    if time.clock_gettime_ns(raw_clock) >= end_ns:
        raise ValueError('native projection original endpoint expired')
    return count


def _native_dependency_selection(packet):
    """Fixed reader BODY returning DATA only, never native/Seed/SDK completion.

    The actual native issuer supplies captured code, snapshot and original
    guards. It retains/revalidates that SAME snapshot through real child closure
    and supplies external config/program custody. No packet authenticates itself.
    """
    label = 'native dependency selection'
    if (type(packet) is not dict or packet.keys() != {
            'schema', 'clock', 'end_ns', 'source_root', 'snapshot', 'sources',
            'configured_targo', 'environment'}
            or packet['schema'] != 'trust-native-dependency-selection-v1'
            or packet['clock'] != 'darwin-mach-uptime-raw-v1'
            or sys.platform != 'darwin'):
        raise ValueError('outside the fixed native dependency selection profile')
    end, raw_clock = _native_endpoint(packet['end_ns'], label)
    _native_descriptions(label)
    root = _native_directory(packet['source_root'], 6, label)
    sources = packet['sources']
    paths = {'scripts/' + name for name in (
        'seed_custody_source.py', 'bootstrap_dependency_preparation.py',
        'seed_input_archives.py', 'seed_input_records.py',
        'bootstrap_dependency_closure.py', 'recreate_bootstrap.py')}
    if type(sources) is not dict or sources.keys() != paths:
        raise ValueError('native dependency selection requires its exact six-code capture')
    captured, expected = {}, {}
    for name, item in sources.items():
        if (type(item) is not dict or item.keys() != {'hex', 'sha256'}
                or type(item['hex']) is not str or len(item['hex']) > MAX_SOURCE * 2
                or type(item['sha256']) is not str or len(item['sha256']) != 64):
            raise ValueError('native dependency selection has invalid bounded code DATA')
        captured[name] = bytes.fromhex(item['hex']); expected[name] = item['sha256']
    if (type(packet['configured_targo']) is not str
            or len(os.fsencode(packet['configured_targo'])) > 4096):
        raise ValueError('native dependency selection has invalid configured Targo spelling')
    loader = BoundSourceLoader(root, expected, captured_sources=captured)
    request = loader.select_dependencies_from_capture(packet['snapshot'], packet['configured_targo'],
                                                       packet['environment'], deadline=end)
    fields = {
        'manifests':[path.relative_to(root).as_posix() for path in request.manifests],
        'source_inputs':[str(path) for path in request.source_inputs],
        'read_set':[str(path) for path in request.read_set],
        'glob_inputs':[str(path) for path in request.glob_input_paths],
        'unowned_inputs':[str(path) for path in request.unowned_input_paths],
    }
    if any(len(values) > 8192 or any(len(os.fsencode(path)) > 4096 for path in values)
           for values in fields.values()):
        raise ValueError('native dependency selection result exceeds path bounds')
    _native_directory(packet['source_root'], 6, label)
    if time.clock_gettime_ns(raw_clock) >= packet['end_ns']:
        raise ValueError('native dependency selection original endpoint expired')
    return {'schema':'trust-native-dependency-selection-result-v1',
            'configured_targo':request.configured_targo, 'targo_path':str(request.targo_path),
            'end_ns':packet['end_ns'], 'clock':packet['clock'], **fields}


def _native_dependency_selection_packet(raw):
    """Bounded private stdin/stdout transport for the fixed native reader.

    The native payload reads at most MAX_NATIVE_SOURCE_PACKET+1 bytes before
    calling this body and writes only its returned bytes. There is no CLI or
    bare-source fallback. Native launch, original owners and closure stay native.
    """
    import json
    if type(raw) is not bytes or len(raw) > MAX_NATIVE_SOURCE_PACKET:
        raise ValueError('native dependency selection packet exceeds bound')
    def unique(items):
        result = {}
        for key, value in items:
            if key in result: raise ValueError('duplicate native source packet key')
            result[key] = value
        return result
    def nonfinite(value):
        raise ValueError('nonfinite native source packet number')
    def finite_float(value):
        result = float(value)
        if not math.isfinite(result): nonfinite(value)
        return result
    packet = json.loads(raw, object_pairs_hook=unique, parse_constant=nonfinite,
                        parse_float=finite_float)
    result = _native_dependency_selection(packet)
    output = json.dumps(result, sort_keys=True, separators=(',', ':'), allow_nan=False).encode() + b'\n'
    if len(output) > MAX_NATIVE_SOURCE_RESULT:
        raise ValueError('native dependency selection output exceeds bound')
    return output


def regular_bytes(path: Path) -> bytes:
    named = path.lstat()
    if not stat.S_ISREG(named.st_mode) or named.st_size > MAX_SOURCE:
        raise ValueError('source is not a bounded regular file')
    fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW | os.O_CLOEXEC)
    try:
        before = os.fstat(fd)
        key = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        if key(before) != key(named):
            raise ValueError('source changed before open')
        data = bytearray()
        while len(data) <= MAX_SOURCE:
            block = os.read(fd, min(65536, MAX_SOURCE + 1 - len(data)))
            if not block:
                break
            data.extend(block)
        if len(data) != before.st_size or key(os.fstat(fd)) != key(before) or key(path.lstat()) != key(before):
            raise ValueError('source changed during capture')
        return bytes(data)
    finally:
        os.close(fd)


class _PendingObservedExecution:
    def __getattr__(self, name):
        raise ValueError('original worker execution context is not installed')


class BoundSourceLoader:
    def select_seed_archives_from_capture(self, raw, host, *, deadline):
        """Execute the maintained parser/Bootstrap selection on retained DATA.

        Only the resident's SAME committed/physical owner supplies `raw`; this
        loader authenticates no pin or caller. The native factory must retain
        and recheck that owner through actual child closure before using rows.
        """
        paths = {'scripts/seed_custody_source.py', 'scripts/mint_seed_support.py',
                 'src/bootstrap/stage0_identity.py'}
        if (self._captured is None or self.extra_sources
                or self.expected.keys() != paths or self._captured.keys() != paths):
            raise ValueError('seed selection requires its complete fixed captured graph')
        if (type(deadline) not in (int, float) or not math.isfinite(deadline)
                or not time.monotonic() < deadline <= time.monotonic() + 900):
            raise ValueError('seed selection needs its original bounded endpoint')
        if type(host) is not str or len(host) > 128:
            raise ValueError('seed selection requires its exact native host')
        helper = self.module('trust_native_seed_selection', self.root / 'scripts/mint_seed_support.py')
        host = helper.native_host(host)
        result = helper.preparation_seed_archive_plan(raw, host)
        self.recheck()
        if time.monotonic() >= deadline:
            raise ValueError('seed selection original endpoint expired')
        return result

    def select_dependencies_from_capture(self, capture, targo, environment, *, deadline):
        """Run the maintained selector on original issuer-supplied source DATA.

        Only the native CommittedRepository capture supplies this packet in a
        resident operation. This method authenticates no packet or caller: the
        factory must retain/recheck that SAME native owner through real closure.
        External config/program custody remains separate; no fetch is executed.
        """
        import copy
        import time
        fields = {'schema', 'root', 'repositories', 'reads'}
        if (type(capture) is not dict or capture.keys() not in (fields, fields | {'listings'})
                or capture['schema'] != 'trust-native-dependency-source-v1'
                or capture['root'] != str(self.root) or self._captured is None):
            raise ValueError('dependency selection needs original captured source DATA and code')
        code = {'scripts/' + name for name in (
            'seed_custody_source.py', 'bootstrap_dependency_preparation.py',
            'seed_input_archives.py', 'seed_input_records.py',
            'bootstrap_dependency_closure.py', 'recreate_bootstrap.py')}
        if self._captured.keys() != code or self.extra_sources:
            raise ValueError('dependency selection has an unexpected captured code graph')
        if type(environment) is not dict or environment.get('CARGO_NET_OFFLINE') != 'true':
            raise ValueError('native dependency selection requires the original offline policy')
        if (type(deadline) not in (int, float) or not math.isfinite(deadline)
                or not time.monotonic() < deadline <= time.monotonic() + 900):
            raise ValueError('dependency selection needs its original bounded endpoint')
        subject = self.module('trust_native_dependency_preparation',
                              self.root / 'scripts/bootstrap_dependency_preparation.py')
        capture = copy.deepcopy(capture)
        repositories, reads = capture['repositories'], capture['reads']
        listings = capture.get('listings', {})
        if type(listings) is not dict or len(listings) > 8192:
            raise ValueError('captured source listing population exceeds bound')
        listing_bytes = 0
        for path, entries in listings.items():
            if path != '.': subject.records.relative(path)
            if entries is None: continue  # actual retained first-missing anchor
            if type(entries) is not list or len(entries) > 8192:
                raise ValueError('captured directory listing exceeds bound')
            names = set()
            for entry in entries:
                if (type(entry) is not dict or entry.keys() != {'name', 'kind'}
                        or type(entry['name']) is not str
                        or entry['kind'] not in ('file', 'directory', 'symlink', 'other')):
                    raise ValueError('invalid captured source directory entry')
                name = entry['name']
                subject.records.relative(name)
                if '/' in name or name in names or len(os.fsencode(name)) > 4096:
                    raise ValueError('invalid or duplicate captured source directory name')
                names.add(name)
                listing_bytes += len(os.fsencode(name)) + 128
                if listing_bytes > 512*1024*1024:
                    raise ValueError('captured directory retained bytes exceed bound')
        if type(repositories) is not dict or type(reads) is not dict or '.' not in repositories:
            raise ValueError('dependency selection has no complete original membership')
        seen, gitlinks = set(), set()
        for prefix, rows in repositories.items():
            if prefix != '.':
                subject.records.relative(prefix)
            if type(rows) is not list:
                raise ValueError('invalid original repository membership')
            for row in rows:
                if type(row) is not dict or row.get('kind') not in ('file', 'symlink', 'dir', 'gitlink'):
                    raise ValueError('invalid original repository member')
                subject.records.relative(row['path'])
                name = (Path(prefix) / row['path']).as_posix()
                if name in seen:
                    raise ValueError('duplicate original repository member')
                seen.add(name)
                if row['kind'] == 'gitlink':
                    gitlinks.add(name)
        if gitlinks != repositories.keys() - {'.'}:
            raise ValueError('original gitlink membership is not completely expanded')
        if len(seen) > 1_000_000 or len(reads) > 8192:
            raise ValueError('captured dependency source population exceeds bound')
        # Validate framing only. Native Git and retained physical originals are
        # the authority; hashes here detect transport disagreement, not lineage.
        total = 0
        for relative, item in reads.items():
            subject.records.relative(relative)
            if type(item) is not dict or item.get('kind') not in ('file', 'symlink', 'absent'):
                raise ValueError('invalid captured dependency source read')
            if item['kind'] == 'file':
                if item.keys() != {'kind', 'mode', 'bytes', 'sha256', 'hex'}:
                    raise ValueError('invalid captured dependency source file')
                if (type(item['mode']) is not int or item['mode'] not in (0o644, 0o755)
                        or type(item['bytes']) is not int or not 0 <= item['bytes'] <= MAX_SOURCE
                        or type(item['sha256']) is not str or len(item['sha256']) != 64):
                    raise ValueError('invalid captured dependency source file metadata')
                encoded = item.pop('hex')
                if type(encoded) is not str or len(encoded) > MAX_SOURCE * 2:
                    raise ValueError('captured dependency source bytes exceed bound')
                raw = bytes.fromhex(encoded)
                total += len(raw)
                if (len(raw) > MAX_SOURCE or total > 64 * 1024 * 1024
                        or len(raw) != item['bytes']
                        or hashlib.sha256(raw).hexdigest() != item['sha256']):
                    raise ValueError('captured dependency source bytes differ')
                item['raw'] = raw
            elif item['kind'] == 'symlink':
                if (item.keys() != {'kind', 'mode', 'target'} or type(item['target']) is not str
                        or type(item['mode']) is not int or item['mode'] != 0o777
                        or '\x00' in item['target'] or len(os.fsencode(item['target'])) > 4096):
                    raise ValueError('invalid captured dependency source link')
            elif item.keys() != {'kind'}:
                raise ValueError('invalid captured dependency source absence')
        view = subject.archives._CommittedSourceView(self.root, repositories, deadline,
                                                    captured_reads=reads, captured_listings=listings)
        # Code supplied to the actual loader is part of the very same physical
        # snapshot; a separate self-declared code graph cannot replace it.
        for name, raw in self._captured.items():
            if view._captured(self.root / name, 'file')['raw'] != raw:
                raise ValueError('dependency code differs from original source capture')
        return subject.offline_check_request(view, view, targo, environment, deadline=deadline)

    def __init__(self, root: Path, expected: dict[str, str], *, extra_sources=None,
                 captured_sources=None):
        if root.resolve(strict=True) != root:
            raise ValueError('source root must be canonical')
        self.root, self.expected, self.executed = root, dict(expected), {}
        self.extra_sources = dict(extra_sources or {})
        self._captured = None
        if captured_sources is not None:
            # Immutable original code DATA, supplied by the live native issuer
            # beside its real source/input owners. Neither bytes nor this
            # loader create an owner or authenticate an artifact's manifest.
            # Strict capture has no pathname-code fallback for missing modules.
            captured = dict(captured_sources)
            declared = self.expected | self.extra_sources
            if (self.expected.keys() & self.extra_sources.keys()
                    or not 0 < len(captured) <= MAX_CAPTURED_SOURCES
                    or captured.keys() != declared.keys()
                    or any(type(raw) is not bytes or len(raw) > MAX_SOURCE
                           for raw in captured.values())
                    or sum(map(len, captured.values())) > MAX_CAPTURED_BYTES):
                raise ValueError('captured source graph is incomplete or exceeds its bound')
            for name, raw in captured.items():
                if hashlib.sha256(raw).hexdigest() != declared[name]:
                    raise ValueError('captured source differs from live owner manifest: ' + name)
            self._captured = captured
        self.modules = {}
        self._context = None

    @property
    def context(self):
        return self._context

    def begin_observed_execution(self):
        if self._context is not None:
            raise ValueError('observed execution has already begun')
        self._context = _PendingObservedExecution()

    def bind_observed_execution(self, context):
        if (type(self._context) is not _PendingObservedExecution or context is None
                or isinstance(context, _PendingObservedExecution)):
            raise ValueError('observed execution context cannot be replaced or cleared')
        self._context = context

    def execute(self, path: str | Path, module: types.ModuleType) -> types.ModuleType:
        path = Path(path)
        if path.resolve(strict=True) != path:
            raise ValueError('module path must be canonical')
        relative = path.relative_to(self.root).as_posix() if path.is_relative_to(self.root) else str(path)
        expected = self.expected.get(relative) if path.is_relative_to(self.root) else self.extra_sources.get(str(path))
        raw = regular_bytes(path)
        actual = hashlib.sha256(raw).hexdigest()
        if expected != actual:
            raise ValueError('module source is not in live owner manifest: ' + relative)
        if self._captured is not None:
            raw = self._captured.get(relative)
            if type(raw) is not bytes or hashlib.sha256(raw).hexdigest() != expected:
                raise ValueError('original captured source is unavailable or changed: ' + relative)
        if path in self.modules:
            # A second alias must receive the original module object, including
            # its capability types, issuer and registry; do not execute it twice.
            canonical = self.modules[path]
            sys.modules[module.__name__] = canonical
            return canonical
        code = compile(raw, str(path), 'exec', dont_inherit=True)
        self.executed[relative] = actual
        module.__file__ = str(path)
        module.__source_sha256__ = actual
        module.__trust_source_loader__ = self
        module.__trust_live_context__ = self.context
        self.modules[path] = module
        sys.modules[module.__name__] = module
        try:
            exec(code, module.__dict__)
        except BaseException:
            self.modules.pop(path, None)
            self.executed.pop(relative, None)
            if sys.modules.get(module.__name__) is module:
                sys.modules.pop(module.__name__, None)
            raise
        return module

    def module(self, name: str, path: Path) -> types.ModuleType:
        return self.execute(path, types.ModuleType(name))

    def recheck(self) -> None:
        for relative, expected in self.executed.items():
            if hashlib.sha256(regular_bytes(Path(relative) if Path(relative).is_absolute() else self.root / relative)).hexdigest() != expected:
                raise ValueError('executed source changed: ' + relative)

    def extract_for_preparation_fd(self, archive_fd: int, destination: Path,
                                   top: str, commit: str, *, deadline: float) -> int:
        """Invoke ONLY the maintained extractor from its complete captured graph.

        The resident supplies this same loader beside its authentic code pins,
        original readonly archive, fresh output and actual native owners. This
        adapter does not authenticate its manifest, issue a seed/SDK, supervise
        a child, publish READY, or settle any resource. Its result is data only.
        The native hard end remains mandatory; this cooperative original end is
        passed unchanged to the existing descriptor extractor, with no timer reset.
        """
        return self._preparation_fd(archive_fd, destination, top, commit, deadline=deadline)

    def project_for_preparation_fd(self, archive_fd: int, destination: Path,
                                  top: str, commit: str, component: str, *, deadline: float) -> int:
        """Use the SAME maintained Bootstrap projection under this closed graph.

        The existing fresh destination and exact component meaning still come
        from the resident's real producer/source issuer. No installer, child,
        private Seed, READY, SDK or native closure is supplied by this adapter.
        """
        if not isinstance(component, str) or not component:
            raise ValueError('preparation requires its exact projected component')
        return self._preparation_fd(archive_fd, destination, top, commit,
                                    deadline=deadline, component=component)

    def _preparation_fd(self, archive_fd, destination, top, commit, *, deadline, component=None):
        paths = {'scripts/seed_custody_source.py', 'scripts/mint_seed_support.py',
                 'src/bootstrap/stage0_identity.py'}
        if (self._captured is None or self.extra_sources
                or self.expected.keys() != paths or self._captured.keys() != paths):
            raise ValueError('preparation requires the complete fixed captured extractor graph')
        if type(deadline) not in (int, float) or not math.isfinite(deadline):
            raise ValueError('preparation requires its original finite endpoint')

        def check():
            if time.monotonic() >= deadline:
                raise ValueError('original preparation endpoint expired')
            # Include the loader entry itself, rather than only modules it has
            # executed. There is no omitted-module or pathname-code fallback.
            for relative in sorted(paths):
                if hashlib.sha256(regular_bytes(self.root / relative)).hexdigest() != self.expected[relative]:
                    raise ValueError('original preparation source changed: ' + relative)
            self.recheck()
            if time.monotonic() >= deadline:
                raise ValueError('original preparation endpoint expired')

        check()
        helper = self.module('trust_native_preparation_extractor',
                             self.root / 'scripts/mint_seed_support.py')
        try:
            check()
            if component is not None:
                return helper.project_for_preparation_fd(
                    archive_fd, destination, top, commit, component, deadline=deadline)
            return helper.extract_for_preparation_fd(
                archive_fd, destination, top, commit, deadline=deadline)
        finally:
            # Preserve failed partial output and surface source/end drift even
            # when the canonical extractor itself failed. Native closure and
            # semantic postchecks remain the resident's separate obligations.
            check()
