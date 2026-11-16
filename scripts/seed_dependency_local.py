"""Locked local-manifest bytes from explicit independently trusted projection.

Resolver metadata must be captured/authenticated by the original owner. This
validator does not execute a resolver or admit candidate metadata as authority.
"""
import hashlib
import json
import os
from pathlib import Path
import stat
import tomllib
HERE = Path(__file__).resolve().parent
byte = __trust_source_loader__.module('trust_dependency_bytes', HERE / 'seed_dependency_bytes.py')
require, relative_path, identity = byte.require, byte.relative_path, byte.identity
contained_plain, HEX64 = byte.contained_plain, byte.HEX64
LIMIT_FILE_BYTES = byte.LIMIT_FILE_BYTES
LIMIT_OBJECT_METADATA_BYTES = byte.LIMIT_OBJECT_METADATA_BYTES
objects = __trust_source_loader__.module('trust_dependency_objects', HERE / 'seed_dependency_objects.py')


def local_source_projection(value, source, account):
    """Copy a concrete controller-trusted physical source projection.

    This data must come from the owner's independently frozen full-source
    roster under its retained source lease, never candidate package metadata.
    The optional projection is invocation-local authority, not portable seed
    admission. Only regular source rows can authenticate a local manifest.
    """
    require(type(value) is dict and set(value) == {'schema', 'source_root', 'rows'},
            'invalid trusted local-source projection wrapper')
    require(value['schema'] == 'trust.native-local-source-projection.v1'
            and type(value['source_root']) is str
            and value['source_root'] == str(source)
            and source.is_absolute() and source.resolve(strict=True) == source
            and source.is_dir() and not source.is_symlink(),
            'local projection does not bind the fixed canonical source root')
    supplied = value['rows']
    require(type(supplied) is dict and supplied, 'missing concrete full-source roster')
    rows = {}
    for name, row in supplied.items():
        account.debit(entries=1)
        require(type(name) is str, 'non-text local source roster path')
        relative_path(name)
        require(type(row) is dict and row
                and all(type(key) is str and type(item) in (str, int, bool, type(None))
                        for key, item in row.items()),
                'local source row is not concrete scalar projection data')
        require(type(row.get('kind')) is int
                and row['kind'] in (stat.S_IFREG, stat.S_IFDIR, stat.S_IFLNK)
                and type(row.get('mode')) is int and 0 <= row['mode'] <= 0o7777,
                'unsupported local projection source type or mode')
        if row['kind'] == stat.S_IFREG:
            require(set(row) == {'kind', 'mode', 'bytes', 'sha256'}
                    and type(row['bytes']) is int and 0 <= row['bytes'] <= LIMIT_FILE_BYTES
                    and type(row['sha256']) is str and HEX64.fullmatch(row['sha256']),
                    'invalid regular local-source projection row')
        # Scalar copies detach the admitted roster from later caller mutation;
        # no callbacks, custom mapping objects or duck-typed capabilities enter.
        rows[name] = dict(row)
    encoded = json.dumps(rows, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()
    account.debit(len(encoded))
    return rows, dict(schema=value['schema'], source_root=str(source), rows=len(rows),
                      roster_sha256=hashlib.sha256(encoded).hexdigest(),
                      authority='independently frozen controller physical source roster; retained source lease',
                      portable_admission=False)


def projected_local_file(path, source, rows, account):
    """Hash exact regular source bytes through one retained opened descriptor."""
    require(isinstance(path, Path) and path.is_absolute(), 'local source path is not absolute')
    contained_plain(path, source)
    name = str(path.relative_to(source))
    relative_path(name)
    row = rows.get(name)
    require(row is not None and row['kind'] == stat.S_IFREG
            and set(row) == {'kind', 'mode', 'bytes', 'sha256'},
            'local source file is absent from the trusted regular projection')
    current, ancestors = source, []
    for part in (None, *path.relative_to(source).parts[:-1]):
        if part is not None:
            current /= part
        observed = current.lstat()
        require(stat.S_ISDIR(observed.st_mode), 'symlink or non-directory local ancestor')
        ancestors.append((current, identity(observed)))
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode)
            and stat.S_IMODE(before.st_mode) == row['mode']
            and before.st_size == row['bytes']
            and before.st_size <= LIMIT_OBJECT_METADATA_BYTES,
            'local source file type, mode or byte extent differs from projection')
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK
    with os.fdopen(os.open(path, flags), 'rb') as handle:
        require(identity(os.fstat(handle.fileno())) == identity(before),
                'opened local source identity differs from named projection file')
        data = handle.read(LIMIT_OBJECT_METADATA_BYTES + 1)
        account.debit(len(data))
        require(len(data) == before.st_size
                and hashlib.sha256(data).hexdigest() == row['sha256']
                and identity(os.fstat(handle.fileno())) == identity(before)
                and identity(path.lstat()) == identity(before),
                'local source bytes or physical identity differ from frozen projection')
        for ancestor, expected in ancestors:
            require(identity(ancestor.lstat()) == expected,
                    'local source ancestor changed around authentication')
        contained_plain(path, source)
    return data, dict(path=name, kind=row['kind'], mode=row['mode'], bytes=row['bytes'],
                      sha256=row['sha256'], physical_identity=identity(before),
                      ancestor_identities=[dict(path=str(path.relative_to(source)) if path != source else '.',
                                               physical_identity=observed)
                                           for path, observed in ancestors])


def locked_packages(raw):
    require(type(raw) is bytes and len(raw) <= LIMIT_OBJECT_METADATA_BYTES, 'invalid bounded lock bytes')
    document = tomllib.loads(raw.decode('utf-8'))
    require(type(document.get('package')) is list and document['package'], 'lock lacks package domain')
    result = {}
    for row in document['package']:
        require(type(row) is dict and type(row.get('name')) is str and row['name']
                and type(row.get('version')) is str and row['version']
                and (row.get('source') is None or type(row['source']) is str), 'invalid locked package identity')
        key = row['name'], row['version'], row.get('source')
        require(key not in result, 'ambiguous locked package identity')
        result[key] = row
    return result


def verify_locked_local(metadata_bytes, expected_metadata_sha256, lock_path, source,
                        projection, expected_projection_sha256, account):
    """Validate physical local bytes, never independently authenticate a resolver.

    Both expected digests and projection must come from the original owner/P03
    command and frozen-source authority. No workspace-membership fallback or
    candidate-selected manifest/version-inheritance algorithm is used.
    """
    objects.checked_account(account)
    require(type(metadata_bytes) is bytes and len(metadata_bytes) <= LIMIT_OBJECT_METADATA_BYTES
            and type(expected_metadata_sha256) is str and HEX64.fullmatch(expected_metadata_sha256)
            and hashlib.sha256(metadata_bytes).hexdigest() == expected_metadata_sha256,
            'resolved metadata bytes differ from original owner binding')
    account.debit(len(metadata_bytes))
    source, lock_path = Path(source), Path(lock_path)
    rows, summary = local_source_projection(projection, source, account)
    require(type(expected_projection_sha256) is str and HEX64.fullmatch(expected_projection_sha256)
            and summary['roster_sha256'] == expected_projection_sha256,
            'local projection differs from independently frozen owner roster')
    require(lock_path.name == 'Cargo.lock', 'local authority lock is not Cargo.lock')
    lock, observation = projected_local_file(lock_path, source, rows, account)
    locked = locked_packages(lock)
    metadata = byte.strict_json(metadata_bytes)
    require(type(metadata) is dict and type(metadata.get('packages')) is list, 'resolver package domain missing')
    selected, identifiers, observations, other_sources = [], set(), {lock_path: observation}, 0
    for package in metadata['packages']:
        account.debit(entries=1)
        require(type(package) is dict and type(package.get('id')) is str
                and package['id'] not in identifiers and type(package.get('name')) is str
                and type(package.get('version')) is str and 'source' in package
                and (package['source'] is None or type(package['source']) is str),
                'duplicate or invalid resolved package identity')
        identifiers.add(package['id'])
        key = package['name'], package['version'], package['source']
        require(key in locked, 'resolved package absent from unchanged exact lock tuple')
        if package['source'] is not None:
            other_sources += 1
            continue
        name = package.get('manifest_path')
        require(type(name) is str, 'missing local manifest path')
        path = Path(name)
        require(path.name == 'Cargo.toml' and str(path) == name and path not in observations,
                'noncanonical or duplicate local manifest')
        _, observed = projected_local_file(path, source, rows, account)
        observations[path] = observed
        selected.append(dict(id=package['id'], name=key[0], version=key[1], source=None,
                             manifest=observed))
    for path, before in observations.items():
        _, after = projected_local_file(path, source, rows, account)
        require(after == before, 'locked local source changed during validation')
    account.debit()
    return dict(schema='trust.seed-dependency.locked-local-bytes.v1',
                metadata_sha256=expected_metadata_sha256, projection=summary,
                lock=observations[lock_path], local_packages=selected,
                other_source_packages_not_validated=other_sources)
