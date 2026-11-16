"""Streaming archive-to-physical-source joins under the original owner end.

Never extracts a path or invokes an installer/compiler. A retained archive hash
must already come from live captured original inputs or committed Cargo.lock.
"""
from __future__ import annotations
import hashlib
import fnmatch
import json
import os
from pathlib import Path, PurePosixPath
import stat
import tarfile
import tomllib

HERE = Path(__file__).resolve().parent
records = __trust_source_loader__.module('trust_input_records', HERE / 'seed_input_records.py')
dependencies = __trust_source_loader__.module('trust_input_dependencies', HERE / 'bootstrap_dependency_closure.py')
require, remaining = records.require, records.remaining


class BoundedTarInfo(tarfile.TarInfo):
    original_end = None

    def metadata_bound(self, archive):
        remaining(self.original_end)
        count = getattr(archive, '_closure_metadata_count', 0) + 1
        expanded = getattr(archive, '_closure_metadata_bytes', 0) + self.size
        require(count <= records.ENTRY_LIMIT and expanded <= records.AGGREGATE_LIMIT,
                'archive extension metadata exceeds finite bound')
        archive._closure_metadata_count, archive._closure_metadata_bytes = count, expanded

    def _proc_pax(self, archive):
        self.metadata_bound(archive)
        require(0 <= self.size <= records.PROOF_LIMIT, 'archive PAX metadata exceeds proof bound')
        result = super()._proc_pax(archive)
        require(result is None or result.sparse is None, 'sparse archive inputs are unsupported')
        return result

    def _proc_sparse(self, archive):
        raise ValueError('sparse archive inputs are unsupported')

    def _proc_gnusparse_00(self, next, raw_headers):
        raise ValueError('sparse archive inputs are unsupported')

    def _proc_gnusparse_01(self, next, pax_headers):
        raise ValueError('sparse archive inputs are unsupported')

    def _proc_gnusparse_10(self, next, pax_headers, archive):
        raise ValueError('sparse archive inputs are unsupported')

    def _proc_gnulong(self, archive):
        self.metadata_bound(archive)
        require(0 <= self.size <= 65536, 'archive long-name metadata exceeds bound')
        return super()._proc_gnulong(archive)


def archive_rows(path, end):
    remaining(end)
    path = Path(path)
    named = path.lstat()
    require(stat.S_ISREG(named.st_mode) and 0 < named.st_size <= records.PAYLOAD_LIMIT,
            'archive is not a finite regular input')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    rows, total, seen = [], 0, set()
    bounded_info = type('OriginalEndpointTarInfo', (BoundedTarInfo,), {'original_end':end})
    try:
        require(records.key(os.fstat(fd)) == records.key(named), 'archive changed before open')
        with os.fdopen(fd, 'rb', closefd=False) as stream:
            with tarfile.open(fileobj=stream, mode='r|*', tarinfo=bounded_info) as archive:
                for member in archive:
                    remaining(end)
                    require(len(rows) < records.ENTRY_LIMIT, 'archive exceeds member bound')
                    name = member.name.removesuffix('/')
                    relative = records.relative(name)
                    require(name not in seen and not member.mode & 0o6000, 'duplicate/privileged archive entry')
                    seen.add(name)
                    row = {'path':name, 'mode':member.mode & 0o7777}
                    if member.isdir():
                        row['kind'] = 'dir'
                    elif member.issym():
                        require(type(member.linkname) is str and '\x00' not in member.linkname,
                                'invalid archive literal link')
                        row.update(kind='symlink', target=member.linkname)
                    elif member.islnk():
                        records.relative(member.linkname)
                        row.update(kind='hardlink', target=member.linkname)
                    else:
                        require(member.isfile() and 0 <= member.size <= records.PAYLOAD_LIMIT,
                                'archive special/oversize payload refused')
                        total += member.size
                        require(total <= records.PAYLOAD_LIMIT, 'archive expansion exceeds payload bound')
                        payload = archive.extractfile(member)
                        require(payload is not None, 'archive payload is missing')
                        digest, length = hashlib.sha256(), 0
                        with payload:
                            while True:
                                remaining(end)
                                block = payload.read(1024 * 1024)
                                if not block:
                                    break
                                length += len(block)
                                require(length <= member.size, 'archive payload exceeds declared length')
                                digest.update(block)
                        require(length == member.size, 'archive payload is truncated')
                        row.update(kind='file', bytes=length, sha256=digest.hexdigest())
                    rows.append(row)
        require(records.key(os.fstat(fd)) == records.key(named)
                and records.key(path.lstat()) == records.key(named), 'archive changed during payload observation')
    finally:
        os.close(fd)
    require(rows, 'archive has no payload')
    by_path = {row['path']:row for row in rows}
    for row in rows:
        if row['kind'] != 'hardlink':
            continue
        target, followed = row['target'], set()
        while True:
            require(target not in followed and len(followed) < 64 and target in by_path,
                    'archive hardlink is missing or cyclic')
            followed.add(target)
            bound = by_path[target]
            if bound['kind'] != 'hardlink':
                break
            target = bound['target']
        require(bound['kind'] == 'file' and row['mode'] == bound['mode'],
                'archive hardlink has an ambiguous mode or non-file target')
        row.update(kind='file', bytes=bound['bytes'], sha256=bound['sha256'], hardlink_to=target)
    return sorted(rows, key=lambda row:row['path'])


def archive_projection(archive, actual, end, *, prefix='', allowed_extra=()):
    """Exact file/link/mode payload plus only implied parent directories."""
    source = archive_rows(archive, end)
    actual = {row['path']:row for row in actual}
    require(len(actual) > 0, 'physical archive payload is absent')
    expected, parents = {}, {'.'}
    for row in source:
        if prefix:
            if row['path'] == prefix:
                continue
            if not row['path'].startswith(prefix + '/'):
                continue
            row = {**row, 'path':row['path'][len(prefix) + 1:]}
        name = row['path']
        expected[name] = row
        parts = PurePosixPath(name).parts
        parents.update(PurePosixPath(*parts[:i]).as_posix() for i in range(1,len(parts)))
    require(expected, 'selected archive projection is empty')
    for name, row in expected.items():
        remaining(end)
        plain = {key:value for key,value in row.items() if key != 'hardlink_to'}
        require(actual.get(name) == plain, 'archive payload differs from physical bytes/mode/literal link: ' + name)
    for name, row in actual.items():
        require(name in expected or (name in parents and row['kind'] == 'dir') or name in allowed_extra,
                'physical extracted source contains an unbound extra entry: ' + name)
    return expected


class _CommittedSourceView:
    """Recipe reads and globs are bounded by the already verified committed rows."""
    def __init__(self, root, repositories, end, *, captured_reads=None, captured_listings=None):
        self.root, self.end = Path(root), end
        remaining(end)
        require(self.root.resolve(strict=True) == self.root and self.root.is_dir()
                and not self.root.is_symlink(), 'committed source root is not canonical')
        # Native packets are DATA beside the live issuer's retained originals.
        # A strict capture has no pathname-content or inferred-absence fallback.
        self._captured_reads = None if captured_reads is None else dict(captured_reads)
        # Committed membership alone does not bind what ordinary Cargo's
        # workspace globs see physically. Record the actual reader reach so
        # the native factory cannot mistake a file-only capture for closure.
        self._glob_inputs = set()
        self._resolution_inputs = set()
        self._captured_listings = dict(captured_listings or {})
        self.files, self.links, self.directories = {}, {}, {self.root}
        for repository, rows in repositories.items():
            for row in rows:
                remaining(self.end)
                relative = (Path(repository) / row['path']).as_posix()
                records.relative(relative)
                path = self.root / relative
                self.directories.update(parent for parent in path.parents if parent.is_relative_to(self.root))
                if row['kind'] == 'file':
                    require(path not in self.files, 'repeated committed manifest source')
                    self.files[path] = row
                elif row['kind'] == 'symlink':
                    require(path not in self.links, 'repeated committed literal link')
                    self.links[path] = row
                elif row['kind'] == 'gitlink':
                    self.directories.add(path)
                elif row['kind'] == 'dir':
                    self.directories.add(path)
        self.children = {}
        for path in self.directories | set(self.links):
            remaining(self.end)
            if path != self.root:
                self.children.setdefault(path.parent, []).append(path)

    def path(self, path, *, reject_final_link=False):
        remaining(self.end)
        path = Path(path)
        require(path.is_absolute() and path.is_relative_to(self.root), 'recipe input escapes committed source')
        pending, current, followed = list(path.relative_to(self.root).parts), self.root, 0
        while pending:
            remaining(self.end)
            part = pending.pop(0)
            if part == '..':
                require(current in self.directories, 'recipe parent traverses an unbound directory')
                require(current != self.root, 'recipe input escapes committed source')
                current = current.parent
                continue
            if part == '.':
                continue
            candidate = current / part
            if candidate not in self.links:
                current = candidate
                continue
            require(not reject_final_link or pending,
                    'present literal link cannot be an absent dependency input: ' + str(candidate))
            followed += 1
            self._resolution_inputs.add(candidate)
            require(followed <= 64, 'committed recipe link depth exceeded')
            row = self.links[candidate]
            literal = (records.link(candidate, self.end) if self._captured_reads is None
                       else self._captured(candidate, 'symlink'))
            require(literal == {key:row[key] for key in ('kind', 'mode', 'target')},
                    'committed recipe link changed during selection')
            target = Path(row['target'])
            if target.is_absolute():
                require(target.is_relative_to(self.root), 'recipe link escapes committed source')
                current = self.root
                parts = target.relative_to(self.root).parts
            else:
                parts = target.parts
            pending = list(parts) + pending
        return current

    def is_file(self, path):
        return self.path(path) in self.files

    def is_dir(self, path):
        return self.path(path) in self.directories

    def read_text(self, path):
        path = self.path(path)
        require(path in self.files, 'recipe input is not a committed regular source file: ' + str(path))
        if self._captured_reads is None:
            row, raw = records.regular(path, self.end, maximum=records.PROOF_LIMIT)
        else:
            item = self._captured(path, 'file')
            raw = item['raw']
            row = {key:item[key] for key in ('kind', 'mode', 'bytes', 'sha256')}
        require(all(row[key] == self.files[path][key] for key in ('kind', 'mode', 'bytes', 'sha256')),
                'committed recipe/manifest changed during selection')
        return raw.decode('utf-8')

    def _captured(self, path, kind):
        remaining(self.end)
        item = self._captured_reads.get(path.relative_to(self.root).as_posix())
        require(item is not None and item['kind'] == kind,
                'required source read was not physically captured: ' + str(path))
        return item

    def require_absent(self, path):
        original = Path(path)
        path = self.path(path, reject_final_link=True)
        if self._captured_reads is None:
            require(not os.path.lexists(original), 'dependency input is not committed source: ' + str(original))
        else:
            self._captured(path, 'absent')

    def glob(self, directory, pattern):
        # Walk captured directory entries component by component. Explicit
        # aliases resolve through captured links; ** does not recurse through
        # symlinks, matching pathlib's default recursive-glob behavior.
        remaining(self.end)
        require(type(pattern) is str and pattern and not Path(pattern).is_absolute(),
                'invalid workspace member pattern')
        def children(current, token, *, recursive=False):
            self._glob_inputs.add(current)
            selected = [child for child in self.children.get(current, ())
                        if ((child not in self.links and child in self.directories) if recursive
                            else fnmatch.fnmatchcase(child.name, token))]
            key = current.relative_to(self.root).as_posix()
            if key in self._captured_listings:
                listing = self._captured_listings[key]
                require(listing is not None, 'committed glob directory is physically absent: ' + str(current))
                actual = {item['name']:item['kind'] for item in listing
                          if (item['kind'] == 'directory' if recursive else
                              item['kind'] in ('directory', 'symlink')
                              and fnmatch.fnmatchcase(item['name'], token))}
                expected = {child.name:('symlink' if child in self.links else 'directory')
                            for child in selected}
                require(actual == expected,
                        'physical workspace glob membership differs from committed source: ' + str(current))
            return selected
        def walk(current, tokens):
            remaining(self.end)
            if current not in self.directories:
                self._glob_inputs.add(current)
                key = current.relative_to(self.root).as_posix()
                require(key not in self._captured_listings or self._captured_listings[key] is None,
                        'uncommitted physical workspace glob directory: ' + str(current))
                return set()
            if not tokens:
                return {current}
            token, rest = tokens[0], tokens[1:]
            if token == '**':
                result = walk(current, rest)
                for child in children(current, token, recursive=True):
                    remaining(self.end)
                    if child not in self.links and child in self.directories:
                        result.update(walk(child, tokens))
                return result
            if not any(c in token for c in '*?['):
                return walk(self.path(current / token), rest)
            result = set()
            for child in children(current, token):
                remaining(self.end)
                if fnmatch.fnmatchcase(child.name, token):
                    result.update(walk(self.path(child), rest))
            return result
        return sorted(walk(self.path(directory), Path(pattern).parts))


def lock_inventory(source_roots, source_rows, end):
    """Select possible locks from the committed bootstrap recipe capability.

    Availability alone is not authority: both the recipe parser and manifest
    graph receive SHA-checked committed rows, never an unconstrained disk glob.
    No optional recipe is silently omitted because its lock is missing.
    """
    require(set(source_roots) == set(source_rows) == {'source', 'orchestration'},
            'original source and orchestration recipe inputs are required')
    views = {label: _CommittedSourceView(root, source_rows[label], end)
             for label, root in source_roots.items()}
    # The target can be the historical producer epoch. Execute the current
    # orchestration's hash-bound graph reader, not that epoch's older API.
    selected = {}
    for label, view in views.items():
        manifests = dependencies.stage0_bootstrap_manifest_roots(view.root, source_view=view)
        require(all(view.is_file(view.root / name) for name in dependencies._BASE_MANIFESTS),
                'original producer base manifest is absent from committed source')
        paths = dependencies._source_inputs(view.root, manifests, {}, source_view=view,
            graph_source_view=views['orchestration'], source_only=True, require_lockfiles=True)
        selected[label] = [path for path in paths if path.name == 'Cargo.lock' and view.is_file(path)]
        require(selected[label], 'original producer has no selected committed lockfiles')
    return views, selected


def lock_checksums(source_roots, source_rows, end):
    """Only source-declared producer manifests select registry lock authority."""
    views, selected = lock_inventory(source_roots, source_rows, end)
    pins = {}
    for label, paths in selected.items():
        for path in paths:
            parsed = tomllib.loads(views[label].read_text(path))
            for package in parsed.get('package', []):
                source = package.get('source', '')
                if not source.startswith(('registry+', 'sparse+')):
                    continue
                checksum = package.get('checksum')
                require(type(checksum) is str and len(checksum) == 64
                        and all(c in '0123456789abcdef' for c in checksum), 'registry package has no exact checksum')
                identity = package['name'] + '-' + package['version']
                records.relative(identity)
                require(identity not in pins or pins[identity] == checksum,
                        'ambiguous same-name registry lockfile checksums')
                pins[identity] = checksum
    return pins


def registry_sources(cargo, pins, end):
    root = cargo / 'registry/src'
    if not root.exists():
        return {'verified_packages':0, 'complete_used_dependency_universe':False}
    require(root.resolve(strict=True) == root and root.is_dir(), 'registry source root is not canonical')
    verified = []
    for registry in sorted(root.iterdir()):
        remaining(end)
        require(registry.is_dir() and not registry.is_symlink(), 'registry source provider is not a directory')
        records.relative(registry.name)
        for package in sorted(registry.iterdir()):
            remaining(end)
            require(package.is_dir() and not package.is_symlink() and package.name in pins,
                    'extracted registry package is not pinned by a committed lockfile')
            archive = cargo / 'registry/cache' / registry.name / (package.name + '.crate')
            observed, _ = records.regular(archive, end)
            require(observed['sha256'] == pins[package.name], 'registry archive differs from committed Cargo.lock')
            marker = package / '.cargo-ok'
            has_cargo_marker = os.path.lexists(marker)
            if has_cargo_marker:
                mode, raw_marker = records.regular(marker,end,maximum=1024)
                metadata = json.loads(raw_marker,object_pairs_hook=records.unique_object)
                require(type(metadata) is dict and set(metadata) == {'v'} and type(metadata['v']) is int
                        and metadata['v'] == 1 and not mode['mode'] & 0o111,
                        'registry generated Cargo marker is not the original supported v1 metadata')
            actual = records.tree(package, end)
            projected = archive_projection(archive, actual, end, prefix=package.name,
                                           allowed_extra=('.cargo-checksum.json','.cargo-ok'))
            checksum_path = package / '.cargo-checksum.json'
            if os.path.lexists(checksum_path):
                generated, raw = records.regular(checksum_path, end, maximum=records.PROOF_LIMIT)
                checksum = json.loads(raw, object_pairs_hook=records.unique_object)
                require(type(checksum) is dict and set(checksum) == {'package','files'}
                        and type(checksum['files']) is dict and not generated['mode'] & 0o111,
                        'registry generated checksum marker has extra fields or executable mode')
                require(checksum.get('package') == pins[package.name], 'Cargo checksum marker changes pinned archive identity')
                files = {name:row['sha256'] for name,row in projected.items() if row['kind'] == 'file'}
                require(checksum.get('files') == files, 'Cargo extracted source checksums differ from actual archive payloads')
            else:
                # Ordinary Targo extraction writes only .cargo-ok. The pinned
                # archive and complete physical projection above authenticate it.
                require(has_cargo_marker, 'registry source has no supported extraction marker')
            verified.append({'registry':registry.name,'package':package.name,'archive_sha256':pins[package.name],
                             'physical_tree_sha256':hashlib.sha256(records.encoded(actual)).hexdigest()})
    return {'verified_packages':len(verified), 'packages':verified,
            'complete_used_dependency_universe':False,
            'limitation':'No new claim for dependency resolution, Git objects, vendor sources or generated lockfiles.'}


def external_payload(archive, sysroot, component, host, end):
    """Recheck original archive payload modes/bytes/links, without a fresh probe."""
    top = archive.name.removesuffix('.tar.xz')
    inner = 'rust-std-' + host if component == 'rust-std' else component
    prefix = top + '/' + inner + '/'
    actual = {row['path']:row for row in records.tree(sysroot,end)}
    matched = 0
    for row in archive_rows(archive,end):
        if not row['path'].startswith(prefix):
            continue
        relative = row['path'][len(prefix):]
        if not relative or PurePosixPath(relative).parts[0] not in ('bin','lib','libexec'):
            continue
        observed = actual.get(relative)
        expected = {key:value for key,value in row.items() if key not in ('path','hardlink_to')}
        require(observed is not None and {key:value for key,value in observed.items() if key != 'path'} == expected,
                'original external sysroot archive payload byte/mode/literal link differs')
        matched += 1
    require(matched > 0, 'original external archive has no selected native payload')
    return {'component':component,'archive':str(archive),'matched_payloads':matched}
