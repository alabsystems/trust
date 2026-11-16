"""Finite canonical proof chunks and actual no-follow input observations.

A proof index is transport, never native admission or path authority. Callers
supply original owner-derived paths and the one original monotonic endpoint.
"""
from __future__ import annotations
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import stat
import time

PROOF_LIMIT = 4 * 1024 * 1024
AGGREGATE_LIMIT = 64 * 1024 * 1024
ENTRY_LIMIT = 2_000_000
PAYLOAD_LIMIT = 64 * 1024 * 1024 * 1024
CHUNK_TARGET = 1024 * 1024


def require(value, message):
    if not value:
        raise ValueError(message)


def remaining(end):
    require(type(end) in (int, float) and math.isfinite(end) and time.monotonic() < end,
            'original input-closure deadline expired')


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode() + b'\n'


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate proof JSON key')
        result[key] = value
    return result


def decode(raw):
    value = json.loads(raw, object_pairs_hook=unique_object,
                       parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite proof JSON')))
    require(encoded(value) == raw, 'input proof is not canonical JSON')
    return value


def key(st):
    return (st.st_dev, st.st_ino, st.st_mode, st.st_size, st.st_mtime_ns, st.st_ctime_ns)


def relative(value):
    require(type(value) is str and value and '\x00' not in value, 'invalid input relative path')
    path = PurePosixPath(value)
    require(not path.is_absolute() and str(path) == value
            and all(p not in ('', '.', '..') for p in path.parts), 'escaping input relative path')
    return path


def regular(path, end, *, maximum=None, object_algorithm=None):
    """Hash actual bytes; retain raw bytes only under an explicit finite bound."""
    remaining(end)
    path = Path(path)
    named = path.lstat()
    require(stat.S_ISREG(named.st_mode), 'input is not a regular file: ' + str(path))
    if maximum is not None:
        require(0 <= named.st_size <= maximum, 'input proof/file exceeds bound')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    content, raw, length = hashlib.sha256(), bytearray(), 0
    blob = hashlib.new(object_algorithm) if object_algorithm is not None else None
    try:
        require(key(os.fstat(fd)) == key(named), 'input changed before open')
        if blob is not None:
            blob.update(f'blob {named.st_size}\0'.encode())
        while True:
            remaining(end)
            block = os.read(fd, 1024 * 1024)
            if not block:
                break
            length += len(block)
            require(length <= PAYLOAD_LIMIT and (maximum is None or length <= maximum),
                    'input bytes exceed finite bound')
            content.update(block)
            if blob is not None:
                blob.update(block)
            if maximum is not None:
                raw.extend(block)
        require(length == named.st_size and key(os.fstat(fd)) == key(named)
                and key(path.lstat()) == key(named), 'input changed during observation')
    finally:
        os.close(fd)
    row = {'kind': 'file', 'mode': stat.S_IMODE(named.st_mode),
           'bytes': length, 'sha256': content.hexdigest()}
    if blob is not None:
        row['object_id'] = blob.hexdigest()
    return row, bytes(raw) if maximum is not None else None


def link(path, end):
    remaining(end)
    first = path.lstat()
    require(stat.S_ISLNK(first.st_mode), 'input literal link changed kind')
    target = os.readlink(path)
    require(key(path.lstat()) == key(first), 'input literal link changed during read')
    return {'kind': 'symlink', 'mode': stat.S_IMODE(first.st_mode), 'target': target}


def resolution(path, end):
    """Retain every literal resolution link, including directory components."""
    path = Path(path)
    require(path.is_absolute() and '..' not in path.parts, 'input binding must be absolute without dot-dot')
    todo, current, links = list(path.parts[1:]), Path('/'), []
    while todo:
        remaining(end)
        current = current / todo.pop(0)
        st = current.lstat()
        if stat.S_ISLNK(st.st_mode):
            require(len(links) < 64, 'input path resolution exceeds finite link bound')
            row = {'path': str(current), **link(current, end)}
            links.append(row)
            target = Path(row['target'])
            combined = target if target.is_absolute() else current.parent / target
            # normpath is lexical only; all resulting components are observed.
            combined = Path(os.path.normpath(combined))
            todo = list(combined.parts[1:]) + todo
            current = Path('/')
        else:
            require(not todo or stat.S_ISDIR(st.st_mode), 'input parent is not a directory')
    require(current.resolve(strict=True) == current, 'input resolution is not canonical')
    for row in links:
        require({'path': row['path'], **link(Path(row['path']), end)} == row,
                'input resolution link changed')
    return current, links


def binding(path, end, *, maximum=None):
    resolved, links = resolution(path, end)
    row, raw = regular(resolved, end, maximum=maximum)
    require(resolution(path, end) == (resolved, links), 'input resolution changed during capture')
    return {'declared': str(path), 'resolved': str(resolved), 'links': links, **row}, raw


def tree(root, end):
    """Complete physical subtree, exact modes and literal links, no following."""
    remaining(end)
    root = Path(root)
    require(root.is_absolute() and root.resolve(strict=True) == root
            and stat.S_ISDIR(root.lstat().st_mode), 'input tree is not a canonical real directory')
    identities, rows, total = {}, [], 0
    for base, directories, files, parent_fd in os.fwalk(root, topdown=True, follow_symlinks=False):
        remaining(end)
        directories.sort()
        files.sort()
        parent = Path(base)
        st = os.fstat(parent_fd)
        require(stat.S_ISDIR(st.st_mode) and key(parent.lstat()) == key(st), 'input directory changed')
        name = parent.relative_to(root).as_posix()
        identities[parent] = key(st)
        rows.append({'path': name, 'kind': 'dir', 'mode': stat.S_IMODE(st.st_mode)})
        require(len(rows) <= ENTRY_LIMIT, 'input tree exceeds entry bound')
        for name in sorted((*directories, *files)):
            remaining(end)
            path = parent / name
            st = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
            if stat.S_ISDIR(st.st_mode):
                continue
            if stat.S_ISLNK(st.st_mode):
                row = link(path, end)
            else:
                require(stat.S_ISREG(st.st_mode), 'special input file is refused')
                total += st.st_size
                require(total <= PAYLOAD_LIMIT, 'input tree exceeds payload bound')
                row, _ = regular(path, end)
            require(key(path.lstat()) == key(st), 'input tree entry changed')
            rows.append({'path': path.relative_to(root).as_posix(), **row})
            require(len(rows) <= ENTRY_LIMIT, 'input tree exceeds entry bound')
    for path, observed in identities.items():
        remaining(end)
        require(key(path.lstat()) == observed, 'input directory changed during enumeration')
    rows.sort(key=lambda row: row['path'])
    return rows


class MetadataBudget:
    """One unique-file aggregate for ALL indexes/chunks and legacy bound proofs."""
    def __init__(self, end):
        self.end, self.files, self.total = end, {}, 0

    def read(self, path):
        row, raw = regular(path, self.end, maximum=PROOF_LIMIT)
        named = str(path)
        if named in self.files:
            require(self.files[named] == row, 'proof changed between references')
        else:
            self.total += len(raw)
            require(self.total <= AGGREGATE_LIMIT, 'aggregate input proof bound exceeded')
            self.files[named] = row
        return raw


class ChunkStore:
    def __init__(self, root, end, *, create=False, budget=None):
        self.root, self.end = Path(root), end
        if create:
            self.root.mkdir(mode=0o700)
        require(self.root.resolve(strict=True) == self.root and stat.S_ISDIR(self.root.lstat().st_mode)
                and not self.root.is_symlink(),
                'input proof store is not canonical')
        self.budget = budget if budget is not None else MetadataBudget(end)

    def put(self, value):
        remaining(self.end)
        raw = encoded(value)
        require(len(raw) <= PROOF_LIMIT, 'one input proof exceeds 4MiB')
        sha = hashlib.sha256(raw).hexdigest()
        path = self.root / (sha + '.json')
        if path.exists():
            require(self.budget.read(path) == raw, 'canonical proof chunk changed')
        else:
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
            try:
                with os.fdopen(fd, 'wb', closefd=False) as stream:
                    stream.write(raw)
                    stream.flush()
                    os.fsync(fd)
            finally:
                os.close(fd)
            require(self.budget.read(path) == raw, 'proof chunk write was incomplete')
        return {'sha256': sha, 'bytes': len(raw)}

    def get(self, reference):
        require(type(reference) is dict and set(reference) == {'sha256', 'bytes'}
                and type(reference['sha256']) is str and re.fullmatch('[0-9a-f]{64}', reference['sha256'])
                and type(reference['bytes']) is int and 0 < reference['bytes'] <= PROOF_LIMIT,
                'invalid canonical chunk reference')
        raw = self.budget.read(self.root / (reference['sha256'] + '.json'))
        require(len(raw) == reference['bytes'] and hashlib.sha256(raw).hexdigest() == reference['sha256'],
                'input chunk digest/size differs')
        return decode(raw)

    def rows(self, rows):
        chunks, group, size = [], [], 0
        for row in rows:
            length = len(encoded(row))
            require(length <= CHUNK_TARGET, 'single physical row exceeds canonical chunk bound')
            if group and size + length > CHUNK_TARGET:
                chunks.append(self.put(group))
                group, size = [], 0
            group.append(row)
            size += length
        if group:
            chunks.append(self.put(group))
        return {'entries': len(rows), 'chunks': chunks,
                'merkle_sha256': hashlib.sha256(encoded(chunks)).hexdigest()}

    def read_rows(self, manifest):
        require(type(manifest) is dict and set(manifest) == {'entries', 'chunks', 'merkle_sha256'}
                and type(manifest['entries']) is int and 0 <= manifest['entries'] <= ENTRY_LIMIT
                and type(manifest['chunks']) is list and len(manifest['chunks']) <= ENTRY_LIMIT,
                'invalid physical row manifest')
        require(hashlib.sha256(encoded(manifest['chunks'])).hexdigest() == manifest['merkle_sha256'],
                'physical row Merkle root differs')
        result = []
        for chunk in manifest['chunks']:
            rows = self.get(chunk)
            require(type(rows) is list and rows, 'empty/invalid row chunk')
            result.extend(rows)
            require(len(result) <= manifest['entries'], 'physical row chunk exceeds declared count')
        require(len(result) == manifest['entries'], 'physical row count differs')
        # The writer's fixed chunk boundaries are canonical as well as the JSON.
        require(self._references(result) == manifest['chunks'], 'noncanonical physical row chunk partition')
        return result

    @staticmethod
    def _references(rows):
        chunks, group, size = [], [], 0
        for row in rows:
            length = len(encoded(row))
            require(length <= CHUNK_TARGET, 'single physical row exceeds canonical chunk bound')
            if group and size + length > CHUNK_TARGET:
                raw = encoded(group)
                chunks.append({'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw)})
                group, size = [], 0
            group.append(row)
            size += length
        if group:
            raw = encoded(group)
            chunks.append({'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw)})
        return chunks
