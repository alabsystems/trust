"""Exact recursive raw-object/source replay, with no process launches.

P03 must independently bind actual reader/resolver/owner custody. Raw retained
objects are untrusted transport until their complete locked graph is checked.
"""
import copy
import hashlib
import os
from pathlib import Path, PurePosixPath
import stat
from urllib.parse import parse_qs, urlsplit

HERE = Path(__file__).resolve().parent
byte = __trust_source_loader__.module('trust_dependency_bytes', HERE / 'seed_dependency_bytes.py')
objects = __trust_source_loader__.module('trust_dependency_objects', HERE / 'seed_dependency_objects.py')
paths = __trust_source_loader__.module('trust_dependency_git_paths', HERE / 'seed_dependency_git_paths.py')
require = byte.require
MAX_GITLINK_DEPTH = 16
MAX_GIT_REPOSITORIES = 1024
MAX_SOURCE_PATH_BYTES = 4096


def tree_entries(raw, account):
    """Reject invalid names before path normalization; require Git byte order."""
    require(type(raw) is bytes, 'tree payload must be actual bytes')
    cursor, names, previous = 0, set(), None
    result = []
    while cursor < len(raw):
        account.debit(entries=1)
        space, nul = raw.find(b' ', cursor), raw.find(b'\0', cursor)
        require(cursor < space < nul and nul + 21 <= len(raw), 'malformed or partial raw Git tree')
        mode, name = raw[cursor:space], raw[space + 1:nul]
        require(mode in (b'40000', b'100644', b'100755', b'120000', b'160000'), 'unsupported raw Git tree mode')
        require(name and len(name) <= MAX_SOURCE_PATH_BYTES
                and name not in (b'.', b'..', b'.git') and b'/' not in name
                and not any(c < 32 or c == 127 for c in name) and name not in names,
                'invalid or duplicate raw Git tree name')
        key = name + (b'/' if mode == b'40000' else b'')
        require(previous is None or previous < key, 'noncanonical Git tree byte order')
        names.add(name)
        previous = key
        result.append((mode.decode('ascii'), os.fsdecode(name), raw[nul + 1:nul + 21].hex()))
        cursor = nul + 21
    return result


class ObjectGraph:
    def __init__(self, retained):
        require(type(retained) is objects.RetainedObjects, 'concrete raw object store required')
        self.objects, self.account = retained, retained.account
        self.repositories = {}

    def repository(self, revision, relative='.', depth=0, parent=None):
        self.account.debit(entries=1)
        self.account.debit(len(os.fsencode(relative)))
        require(len(os.fsencode(relative)) <= MAX_SOURCE_PATH_BYTES, 'recursive source path exceeds bound')
        require(type(revision) is str and byte.HEX40.fullmatch(revision)
                and depth <= MAX_GITLINK_DEPTH and len(self.repositories) < MAX_GIT_REPOSITORIES,
                'recursive repository revision/count/depth bound failed')
        require(relative not in self.repositories, 'duplicate recursive repository path')
        raw, _ = self.objects.read(revision, 'commit')
        first = raw.split(b'\n', 1)[0]
        require(b'\n\n' in raw and first.startswith(b'tree ') and len(first) == 45
                and byte.HEX40.fullmatch(first[5:].decode('ascii')), 'commit lacks exact first root tree')
        headers = raw.split(b'\n\n', 1)[0].splitlines()
        require(sum(line.startswith(b'tree ') for line in headers) == 1, 'ambiguous commit tree header')
        row = dict(commit=revision, tree=first[5:].decode('ascii'), parent=parent,
                   leaves={}, directories=[], gitlinks={})
        self.repositories[relative] = row
        self._tree(row)
        resolve_graph_links(row, self.objects, self.account)
        for name, child in row['gitlinks'].items():
            child_path = str(PurePosixPath(relative) / name)
            self.repository(child, child_path, depth + 1, relative)
        return row

    def _tree(self, repository):
        pending = [(repository['tree'], PurePosixPath())]
        directories = set()
        while pending:
            oid, prefix = pending.pop()
            raw, _ = self.objects.read(oid, 'tree')
            for mode, name, child in tree_entries(raw, self.account):
                length = len(os.fsencode(str(prefix))) + len(os.fsencode(name)) + 1
                self.account.debit(length)
                require(length <= MAX_SOURCE_PATH_BYTES, 'complete source path exceeds bound')
                relative = str(prefix / name)
                byte.relative_path(relative)
                require(relative not in repository['leaves'] and relative not in directories,
                        'duplicate complete source path')
                if mode == '40000':
                    directories.add(relative)
                    pending.append((child, prefix / name))
                elif mode == '160000':
                    directories.add(relative)
                    repository['gitlinks'][relative] = child
                    repository['leaves'][relative] = dict(mode=mode, git_commit=child)
                else:
                    _, blob = self.objects.read(child, 'blob')
                    repository['leaves'][relative] = dict(mode=mode, git_blob=child, **blob)
        repository['directories'] = sorted(directories)


def replay_git_objects(revision, raw_root, account):
    """Verify all retained source bytes without Git/worktree/PID/process input."""
    retained = objects.RetainedObjects(raw_root, account)
    graph = ObjectGraph(retained)
    graph.repository(revision)
    raw_objects = retained.finish()
    return dict(schema='trust.seed-dependency.raw-git-graph.v1', root_commit=revision,
                repositories=copy.deepcopy(graph.repositories), objects=raw_objects)


def resolve_graph_links(repository, retained, account):
    """Reviewed component-order link algorithm, without filesystem shortcuts."""
    expected, directories = repository['leaves'], set(repository['directories'])
    targets = {name: retained_bytes(retained, leaf['git_blob'], account)
               for name, leaf in expected.items() if leaf['mode'] == '120000'}
    for original in targets:
        pending, resolved, links, endpoint = list(reversed(PurePosixPath(original).parts)), [], [], None
        while pending:
            account.debit(entries=1)
            part = pending.pop()
            require(part != '.git', 'Git symlink enters excluded metadata')
            if part in ('', '.'):
                continue
            if part == '..':
                require(resolved, 'Git symlink leaves the authenticated checkout')
                resolved.pop()
                continue
            current = '/'.join([*resolved, part])
            account.debit(len(os.fsencode(current)))
            if current in directories:
                require(current not in repository['gitlinks'], 'Git symlink enters recursive provider')
                resolved.append(part)
                continue
            row = expected.get(current)
            require(row is not None, 'Git symlink enters unauthenticated source or generated metadata')
            if row['mode'] == '120000':
                require(len(links) < 40, 'Git symlink chain exceeds bounded follow limit')
                target = targets[current]
                account.debit(len(target), entries=target.count(b'/') + 1)
                text = os.fsdecode(target)
                require(text and not text.startswith('/')
                        and not any(ord(c) < 32 or ord(c) == 127 for c in text),
                        'absolute, empty or control-bearing Git symlink target')
                links.append(current)
                pending.extend(reversed(text.split('/')))
                continue
            require(row['mode'] in ('100644', '100755') and not pending,
                    'Git symlink traverses a non-directory or lacks committed endpoint')
            endpoint = current
        require(endpoint is not None, 'Git symlink has no authenticated regular committed endpoint')
        expected[original]['resolved_tracked_source'] = endpoint
        expected[original]['symlink_chain'] = links


def observed_head(gitdir, account):
    """Parse one ordinary direct HEAD or one exact internal branch ref."""
    raw = account.metadata_file(gitdir / 'HEAD')
    if len(raw) == 41 and raw.endswith(b'\n') and byte.HEX40.fullmatch(raw[:-1].decode('ascii')):
        return raw[:-1].decode('ascii')
    require(raw.startswith(b'ref: refs/heads/') and raw.endswith(b'\n') and raw.count(b'\n') == 1,
            'unsupported symbolic HEAD authority')
    name = raw[5:-1].decode('utf-8')
    byte.relative_path(name)
    path = gitdir / name
    if os.path.lexists(path):
        paths.plain_directory_chain(path.parent, gitdir, account)
        value = account.metadata_file(path)
        require(len(value) == 41 and value.endswith(b'\n') and byte.HEX40.fullmatch(value[:-1].decode('ascii')),
                'invalid direct HEAD branch ref')
        return value[:-1].decode('ascii')
    packed = account.metadata_file(gitdir / 'packed-refs')
    refs = {}
    for line in packed.splitlines():
        account.debit(entries=1)
        if line.startswith(b'#'):
            continue
        require(not line.startswith(b'^'), 'peeled packed ref authority is unsupported')
        fields = line.split(b' ')
        require(len(fields) == 2 and byte.HEX40.fullmatch(fields[0].decode('ascii')), 'malformed packed ref')
        reference = fields[1].decode('utf-8')
        byte.relative_path(reference)
        require(reference.startswith('refs/') and reference not in refs, 'duplicate or invalid packed ref')
        refs[reference] = fields[0].decode('ascii')
    require(name in refs, 'HEAD branch has no actual ref')
    return refs[name]


def _physical_repository(checkout, row, retained, account, gitdir):
    require(observed_head(gitdir, account) == row['commit'], 'actual HEAD differs from locked revision')
    expected = copy.deepcopy(row['leaves'])
    targets, observations = {}, {}
    for name, leaf in expected.items():
        account.debit(entries=1)
        actual = checkout / name
        paths.plain_directory_chain(actual.parent, checkout, account)
        first = byte.identity(actual.lstat())
        if leaf['mode'] == '160000':
            paths.plain_directory_chain(actual, checkout, account)
        elif leaf['mode'] == '120000':
            # Symlink blobs are bounded metadata, not arbitrary file content.
            target = retained_bytes(retained, leaf['git_blob'], account)
            paths.observed_git_link(actual, target, account)
            targets[name] = target
        else:
            info = actual.lstat()
            require(stat.S_ISREG(info.st_mode) and bool(info.st_mode & 0o111) == (leaf['mode'] == '100755'),
                    'checkout source type or executable bit differs')
            retained.read(leaf['git_blob'], 'blob', actual)
        require(byte.identity(actual.lstat()) == first, 'source leaf changed around raw-object comparison')
        observations[name] = first
    files, directories = paths.git_worktree_files(checkout, row['gitlinks'], account)
    marker = byte.cargo_marker(files, b'', account)
    require(set(files) == set(expected) - set(row['gitlinks'])
            and directories == set(row['directories']), 'incomplete or untracked checkout source domain')
    paths.authenticated_git_symlinks(checkout, expected, directories, targets, account)
    for name in ['.', '.cargo-ok', *sorted(directories)]:
        account.debit(entries=1)
        observations[name] = byte.identity((checkout / name).lstat())
    return dict(leaves=expected, cargo_marker_sha256=marker, identities=observations)


def retained_bytes(retained, oid, account):
    """Read a bounded link blob through its independently verified descriptor."""
    path = retained.root / oid
    require(path.lstat().st_size <= byte.LIMIT_OBJECT_METADATA_BYTES, 'oversized tracked link blob')
    retained.read(oid, 'blob')
    before = path.lstat()
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    try:
        require(byte.identity(os.fstat(fd)) == retained.files[oid], 'tracked link changed before retained read')
        raw = bytearray()
        while len(raw) <= before.st_size:
            account.debit()
            part = os.read(fd, min(65536, before.st_size + 1 - len(raw)))
            if not part:
                break
            account.debit(len(part))
            raw.extend(part)
        require(len(raw) == before.st_size and byte.identity(os.fstat(fd)) == retained.files[oid]
                and byte.identity(path.lstat()) == retained.files[oid], 'tracked link retained bytes changed')
        return bytes(raw)
    finally:
        os.close(fd)


def verify_git_checkout(checkout, revision, raw_root, account):
    """Join raw locked graph with actual recursively contained GitDB/worktree."""
    objects.checked_account(account)
    checkout = Path(checkout)
    require(checkout.is_absolute() and checkout.resolve(strict=True) == checkout, 'aliased fixed checkout root')
    retained = objects.RetainedObjects(raw_root, account)
    graph = ObjectGraph(retained)
    graph.repository(revision)
    physical, databases, worktrees = {}, set(), set()
    for relative, row in graph.repositories.items():
        parent = None
        if relative != '.':
            require(row['parent'] in physical, 'recursive physical provider lacks original parent')
            parent = Path(physical[row['parent']]['gitdir'])
        root = checkout / relative
        gitdir, before = paths.git_database(root, checkout, parent, account)
        wi = (root.lstat().st_dev, root.lstat().st_ino)
        di = (gitdir.lstat().st_dev, gitdir.lstat().st_ino)
        require(wi not in worktrees and di not in databases, 'recursive GitDB/worktree cycle or alias')
        worktrees.add(wi)
        databases.add(di)
        evidence = _physical_repository(root, row, retained, account, gitdir)
        after_dir, after = paths.git_database(root, checkout, parent, account)
        require(after_dir == gitdir and after == before, 'recursive physical Git authority changed')
        physical[relative] = dict(gitdir=str(gitdir), authority=before, source=evidence,
                                  parent_gitdir=str(parent) if parent is not None else None)
    for relative, captured in physical.items():
        root = checkout / relative
        parent = Path(captured['parent_gitdir']) if captured['parent_gitdir'] is not None else None
        gitdir, authority = paths.git_database(root, checkout, parent, account)
        require(str(gitdir) == captured['gitdir'] and authority == captured['authority'],
                'recursive physical authority changed before final replay')
        for name, expected in captured['source']['identities'].items():
            account.debit(entries=1)
            require(byte.identity((root / name).lstat()) == expected,
                    'recursive physical source changed before final replay')
    raw_objects = retained.finish()
    return dict(schema='trust.seed-dependency.physical-git-bytes.v1', root_commit=revision,
                repositories=copy.deepcopy(graph.repositories), physical=physical, objects=raw_objects)


def verify_locked_git(package, lock_bytes, checkout, raw_root, account):
    """Join original-owner resolver/lock identity to exact Git object sources.

    The caller must independently bind package metadata and lock bytes to its
    actual source/reader authority. This function does not issue that authority.
    """
    objects.checked_account(account)
    require(type(package) is dict and all(type(package.get(k)) is str
            for k in ('name', 'version', 'source', 'manifest_path')), 'invalid locked Git package')
    require(type(lock_bytes) is bytes and len(lock_bytes) <= byte.LIMIT_OBJECT_METADATA_BYTES,
            'invalid bounded original Git lock bytes')
    account.debit(len(lock_bytes))
    local = __trust_source_loader__.module('trust_dependency_local', HERE / 'seed_dependency_local.py')
    locked = local.locked_packages(lock_bytes)
    key = package['name'], package['version'], package['source']
    require(key in locked and package['source'].startswith('git+'), 'Git package differs from exact lock tuple')
    parsed = urlsplit(package['source'][4:])
    revision = parsed.fragment
    query = parse_qs(parsed.query, strict_parsing=True, keep_blank_values=True)
    require(byte.HEX40.fullmatch(revision) and query == {'rev': [revision]}
            and parsed.scheme == 'https' and parsed.hostname and not parsed.username and not parsed.password,
            'Git dependency is not an exact immutable declared revision')
    checkout, manifest = Path(checkout), Path(package['manifest_path'])
    require(manifest.name == 'Cargo.toml' and str(manifest) == package['manifest_path'], 'noncanonical Git manifest')
    byte.contained_plain(manifest, checkout)
    result = verify_git_checkout(checkout, revision, raw_root, account)
    matches = []
    for relative, row in result['repositories'].items():
        root = checkout / relative
        if manifest.is_relative_to(root):
            name = str(manifest.relative_to(root))
            if name in row['leaves'] and row['leaves'][name]['mode'] in ('100644', '100755'):
                matches.append(relative)
    require(len(matches) == 1, 'resolved Git manifest is not an exact committed regular leaf')
    return dict(schema='trust.seed-dependency.locked-git-bytes.v1',
                package=dict(name=key[0], version=key[1], source=key[2]), source=result)
