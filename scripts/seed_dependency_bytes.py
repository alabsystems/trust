"""Bounded dependency byte primitives. No process creation or seed admission."""
import hashlib
import json
import os
from contextlib import contextmanager
from pathlib import Path, PurePosixPath
import re
import stat
import tarfile
import time
LIMIT_BYTES = 16 * 1024**3
LIMIT_ENTRIES = 1_000_000
LIMIT_FILE_BYTES = 512 * 1024**2
LIMIT_OBJECT_METADATA_BYTES = 16 * 1024**2
HEX40 = re.compile(r'[0-9a-f]{40}')
HEX64 = re.compile(r'[0-9a-f]{64}')


def require(value, message):
    if not value:
        raise RuntimeError('Dependency admission: ' + message)


def walk_error(error):
    raise error


def strict_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=pairs,
                      parse_constant=lambda _: require(False, 'non-JSON constant'))


def relative_path(value):
    path = PurePosixPath(value)
    require(isinstance(value, str) and value and not path.is_absolute()
            and str(path) == value and all(p not in ('', '.', '..', '.git') for p in path.parts)
            and not any(ord(c) < 32 or ord(c) == 127 for c in value), 'noncanonical source path')
    return path


def contained_plain(path, root):
    require(path.is_relative_to(root), 'source path escaped its admitted root')
    current = root
    require(current.is_dir() and not current.is_symlink(), 'aliased admitted root')
    for part in path.relative_to(root).parts:
        current /= part
        require(not current.is_symlink(), 'symlink in dependency authority path')
    require(path.resolve() == path, 'noncanonical dependency authority path')


def identity(value):
    # Reading may update atime; it cannot change these source-identity fields.
    return (value.st_dev, value.st_ino, value.st_mode, value.st_nlink,
            value.st_size, value.st_mtime_ns, value.st_ctime_ns)


class Account:
    def __init__(self, record):
        self.end = record['work_end_monotonic']
        self.bytes = 0
        self.entries = 0

    def debit(self, count=0, entries=0):
        require(time.monotonic() < self.end, 'original preparation endpoint expired')
        self.bytes += count
        self.entries += entries
        require(self.bytes <= LIMIT_BYTES and self.entries <= LIMIT_ENTRIES,
                'bounded authentication census exceeded')

    def left(self):
        self.debit()
        return self.end - time.monotonic()

    def hash_file(self, path):
        before = path.lstat()
        require(stat.S_ISREG(before.st_mode) and before.st_size <= LIMIT_FILE_BYTES,
                'missing, special or oversized dependency file')
        digest = hashlib.sha256()
        with path.open('rb') as handle:
            require(identity(os.fstat(handle.fileno())) == identity(before), 'opened dependency identity changed')
            while chunk := handle.read(1024**2):
                self.debit(len(chunk))
                digest.update(chunk)
            require(identity(os.fstat(handle.fileno())) == identity(before), 'dependency changed while hashing')
        require(identity(path.lstat()) == identity(before), 'dependency pathname changed while hashing')
        return digest.hexdigest()

    def metadata_file(self, path):
        before = path.lstat()
        require(stat.S_ISREG(before.st_mode) and before.st_size <= LIMIT_OBJECT_METADATA_BYTES,
                'special or oversized dependency metadata')
        with path.open('rb') as handle:
            require(identity(os.fstat(handle.fileno())) == identity(before), 'opened metadata identity changed')
            data = handle.read(LIMIT_OBJECT_METADATA_BYTES + 1)
            self.debit(len(data))
            require(len(data) == before.st_size and identity(os.fstat(handle.fileno())) == identity(before)
                    and identity(path.lstat()) == identity(before), 'dependency metadata changed while reading')
        return data


def source_files(root, account, git=False):
    files, directories = {}, set()
    for base, dirs, names in os.walk(root, followlinks=False, onerror=walk_error):
        account.debit(entries=len(dirs) + len(names))
        if git and Path(base) == root:
            dirs[:] = [d for d in dirs if d != '.git']
            names = [n for n in names if n != '.git']
        for name in dirs + names:
            path = Path(base) / name
            relative = str(path.relative_to(root))
            relative_path(relative)
            mode = path.lstat().st_mode
            require(stat.S_ISDIR(mode) or stat.S_ISREG(mode) or stat.S_ISLNK(mode),
                    'special dependency source entry')
            if stat.S_ISDIR(mode):
                directories.add(relative)
            else:
                files[relative] = path
    return files, directories


def cargo_marker(files, expected, account):
    marker = files.pop('.cargo-ok', None)
    require(marker is not None and not marker.is_symlink()
            and account.metadata_file(marker) == expected, 'missing or unknown Targo extraction marker')
    return account.hash_file(marker)


@contextmanager
def authenticated_archive(path, checksum, account):
    """Keep the checksum's regular file open through the actual tar parse."""
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and 0 <= before.st_size <= LIMIT_FILE_BYTES,
            'missing, special or oversized registry archive')
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    with os.fdopen(os.open(path, flags), 'rb') as handle:
        require(identity(os.fstat(handle.fileno())) == identity(before),
                'opened registry archive identity changed')
        digest = hashlib.sha256()
        while chunk := handle.read(1024**2):
            account.debit(len(chunk))
            digest.update(chunk)
        require(digest.hexdigest() == checksum,
                'registry archive differs from Cargo.lock checksum')
        require(identity(os.fstat(handle.fileno())) == identity(before)
                and identity(path.lstat()) == identity(before),
                'registry archive changed while hashing')
        require(handle.seek(0) == 0, 'registry archive cannot rewind its authenticated descriptor')
        yield handle, identity(before)
        require(identity(os.fstat(handle.fileno())) == identity(before)
                and identity(path.lstat()) == identity(before),
                'registry archive changed while parsing')


def registry_package(package, locked, cache, directory, account):
    root = Path(package['manifest_path']).parent
    contained_plain(root, cache / 'registry/src')
    parts = root.relative_to(cache / 'registry/src').parts
    expected_name = package['name'] + '-' + package['version']
    require(len(parts) == 2 and parts[1] == expected_name, 'ambiguous registry root')
    checksum = locked.get('checksum')
    require(isinstance(checksum, str) and HEX64.fullmatch(checksum), 'missing locked package checksum')
    archive = cache / 'registry/cache' / parts[0] / (expected_name + '.crate')
    contained_plain(archive, cache / 'registry/cache')
    expected, modes, directories, member_names = {}, {}, set(), set()
    with authenticated_archive(archive, checksum, account) as (archive_stream, archive_identity), \
            tarfile.open(fileobj=archive_stream, mode='r|gz') as members:
        for member in members:
            account.debit(entries=1)
            path = relative_path(member.name.rstrip('/') if member.isdir() else member.name)
            require(path.parts[0] == expected_name and str(path) not in member_names,
                    'archive member escaped its exact package root')
            member_names.add(str(path))
            if len(path.parts) == 1:
                require(member.isdir(), 'archive member has no package-relative path')
                continue
            name = str(PurePosixPath(*path.parts[1:]))
            directories.update(str(p) for p in PurePosixPath(name).parents if str(p) != '.')
            if member.isdir():
                directories.add(name)
                continue
            require(member.isfile() and name not in expected
                    and name not in ('.cargo-ok', '.cargo-checksum.json')
                    and 0 <= member.size <= LIMIT_FILE_BYTES,
                    'unsupported, duplicate or oversized registry archive member')
            content = members.extractfile(member)
            require(content is not None, 'missing archive member bytes')
            digest = hashlib.sha256()
            total = 0
            with content:
                while chunk := content.read(1024**2):
                    account.debit(len(chunk))
                    total += len(chunk)
                    digest.update(chunk)
            require(total == member.size, 'incomplete archive member')
            expected[name] = digest.hexdigest()
            modes[name] = bool(member.mode & 0o111)
    files, actual_directories = source_files(root, account)
    marker = cargo_marker(files, b'{"v":1}', account)
    supplied_checksum = files.pop('.cargo-checksum.json', None)
    checksum_record = dict(files=expected, package=checksum)
    if supplied_checksum is not None:
        require(not supplied_checksum.is_symlink()
                and strict_json(account.metadata_file(supplied_checksum)) == checksum_record,
                'supplied .cargo-checksum.json differs from authenticated archive')
    require(set(files) == set(expected) and actual_directories == directories,
            'registry source is incomplete or has unaccounted files/directories')
    for name, digest in expected.items():
        require(not files[name].is_symlink() and account.hash_file(files[name]) == digest
                and bool(files[name].lstat().st_mode & 0o111) == modes[name],
                'registry source file differs from authenticated .cargo-checksum.json')
    # Ordinary Targo extracts .cargo-ok, not vendor checksum manifests. Keep
    # the authenticated vendor-shaped manifest in evidence, never in the cache.
    destination = directory / (hashlib.sha256(str(root).encode()).hexdigest() + '.cargo-checksum.json')
    destination.write_text(json.dumps(checksum_record, sort_keys=True, indent=2) + '\n')
    return dict(kind='registry', source=package['source'], root=str(root), archive=str(archive),
                locked_checksum=checksum, archive_identity=archive_identity,
                cargo_marker_sha256=marker, files=len(expected),
                checksum_manifest=str(destination), checksum_manifest_sha256=account.hash_file(destination))
