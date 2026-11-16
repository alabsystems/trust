"""Bounded replay of raw Git payload files; no subprocess or object callbacks.

The original owner/P03 supplies exact locked revisions and retains reader
custody. This layer verifies actual bytes, not where an object reader ran.
"""
import hashlib
import math
import os
from pathlib import Path
import stat

HERE = Path(__file__).resolve().parent
byte = __trust_source_loader__.module('trust_dependency_bytes', HERE / 'seed_dependency_bytes.py')
require = byte.require


def checked_account(account):
    require(type(account) is byte.Account and type(account.end) in (int, float)
            and math.isfinite(account.end), 'missing finite original shared Account')
    require(type(account.bytes) is int and 0 <= account.bytes <= byte.LIMIT_BYTES
            and type(account.entries) is int and 0 <= account.entries <= byte.LIMIT_ENTRIES,
            'invalid shared authentication counters')
    account.debit()
    return account


def original_account(record):
    require(type(record) is dict and type(record.get('work_end_monotonic')) in (int, float)
            and math.isfinite(record['work_end_monotonic']), 'missing finite original endpoint')
    return checked_account(byte.Account(dict(record)))


class RetainedObjects:
    """One canonical flat directory of SHA1-named raw payloads, never Git DB IO."""
    def __init__(self, root, account):
        self.account = checked_account(account)
        self.root = Path(root)
        require(self.root.is_absolute() and self.root.resolve(strict=True) == self.root
                and stat.S_ISDIR(self.root.lstat().st_mode), 'aliased raw object root')
        self.initial = byte.identity(self.root.lstat())
        self.files, self.used = {}, {}
        with os.scandir(self.root) as entries:
            for entry in entries:
                account.debit(entries=1)
                require(byte.HEX40.fullmatch(entry.name), 'unknown raw object store entry')
                info = entry.stat(follow_symlinks=False)
                require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1
                        and info.st_size <= byte.LIMIT_FILE_BYTES, 'unsafe raw object payload')
                self.files[entry.name] = byte.identity(info)
        require(byte.identity(self.root.lstat()) == self.initial, 'raw object root changed during census')

    def read(self, oid, kind, source=None):
        require(type(oid) is str and byte.HEX40.fullmatch(oid)
                and kind in ('commit', 'tree', 'blob') and oid in self.files,
                'missing or unsupported exact raw object')
        self.account.debit(entries=1)
        path = self.root / oid
        named = path.lstat()
        maximum = byte.LIMIT_FILE_BYTES if kind == 'blob' else byte.LIMIT_OBJECT_METADATA_BYTES
        require(byte.identity(named) == self.files[oid] and named.st_size <= maximum,
                'raw object identity or metadata bound changed')
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
        raw = bytearray() if kind != 'blob' else None
        digest = hashlib.sha256()
        git = hashlib.sha1(kind.encode() + b' ' + str(named.st_size).encode() + b'\0')
        source_fd = None
        try:
            require(byte.identity(os.fstat(fd)) == self.files[oid], 'raw object changed before open')
            if source is not None:
                source = Path(source)
                before = source.lstat()
                require(stat.S_ISREG(before.st_mode) and before.st_size == named.st_size,
                        'checkout blob type or extent differs')
                source_fd = os.open(source, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
                require(byte.identity(os.fstat(source_fd)) == byte.identity(before), 'checkout changed before open')
            length = 0
            while True:
                self.account.debit()
                block = os.read(fd, 1024**2)
                if not block:
                    break
                length += len(block)
                self.account.debit(len(block))
                require(length <= named.st_size, 'raw object has trailing bytes')
                git.update(block)
                digest.update(block)
                if raw is not None:
                    raw.extend(block)
                if source_fd is not None:
                    require(self._source_bytes(source_fd, len(block)) == block, 'checkout differs from raw blob')
            require(length == named.st_size and git.hexdigest() == oid, 'partial or hash-mismatched raw object')
            require(byte.identity(os.fstat(fd)) == self.files[oid]
                    and byte.identity(path.lstat()) == self.files[oid], 'raw object changed during read')
            if source_fd is not None:
                require(not os.read(source_fd, 1) and byte.identity(os.fstat(source_fd)) == byte.identity(before)
                        and byte.identity(source.lstat()) == byte.identity(before), 'checkout changed during blob comparison')
        finally:
            os.close(fd)
            if source_fd is not None:
                os.close(source_fd)
        row = dict(kind=kind, bytes=length, sha256=digest.hexdigest())
        require(oid not in self.used or self.used[oid] == row, 'raw object has competing kind/extent')
        self.used[oid] = row
        return (bytes(raw) if raw is not None else None), dict(row)

    def _source_bytes(self, fd, count):
        result = bytearray()
        while len(result) < count:
            self.account.debit()
            block = os.read(fd, count - len(result))
            require(block, 'partial checkout blob')
            self.account.debit(len(block))
            result.extend(block)
        return bytes(result)

    def finish(self):
        self.account.debit()
        require(set(self.files) == set(self.used), 'orphan or unused retained raw object')
        observed = {}
        with os.scandir(self.root) as entries:
            for entry in entries:
                self.account.debit(entries=1)
                observed[entry.name] = byte.identity(entry.stat(follow_symlinks=False))
        require(observed == self.files and byte.identity(self.root.lstat()) == self.initial,
                'raw object store domain or identity changed')
        return {oid: dict(row) for oid, row in sorted(self.used.items())}
