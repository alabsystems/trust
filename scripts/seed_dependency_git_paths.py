"""Existing recursive checkout/GitDB and tracked-symlink checks, process-free."""
import hashlib
import os
from pathlib import Path, PurePosixPath
import re
import stat
HERE = Path(__file__).resolve().parent
byte = __trust_source_loader__.module('trust_dependency_bytes', HERE / 'seed_dependency_bytes.py')
require, relative_path, identity = byte.require, byte.relative_path, byte.identity
walk_error = byte.walk_error


def plain_directory_chain(path, root, account):
    require(path.is_absolute() and root.is_absolute() and path.is_relative_to(root),
            'Git authority leaves its fixed checkout root')
    current, rows = root, []
    for part in (None, *path.relative_to(root).parts):
        account.debit(entries=1)
        if part is not None:
            require(part not in ('', '.', '..'), 'noncanonical Git authority component')
            current /= part
        observed = current.lstat()
        require(stat.S_ISDIR(observed.st_mode), 'Git authority traverses symlink or non-directory')
        rows.append((str(current), identity(observed)))
    require(path.resolve(strict=True) == path, 'aliased Git authority directory')
    return rows


def plain_gitfile_target(checkout, text, root, account):
    require(text and not text.startswith('/')
            and not any(ord(char) < 32 or ord(char) == 127 for char in text),
            'Gitfile requires a relative control-free internal GitDB path')
    current = checkout
    for part in text.split('/'):
        account.debit(entries=1)
        if part in ('', '.'):
            continue
        if part == '..':
            require(current != root and current.parent.is_relative_to(root),
                    'Gitfile escapes the fixed checkout root')
            current = current.parent
        else:
            current /= part
            require(stat.S_ISDIR(current.lstat().st_mode),
                    'Gitfile traverses symlink or non-directory GitDB authority')
    plain_directory_chain(current, root, account)
    return current


def safe_git_config(data, checkout, gitdir, root, account):
    # Bounded ordinary clone configs only. A config include, alternate object
    # command, promisor/lazy fetch or worktree redirection is not an exemption.
    text = data.decode('utf-8')
    section, subsection, seen, core = None, None, set(), {}
    allowed = {'core': {'repositoryformatversion', 'bare', 'filemode',
                        'logallrefupdates', 'autocrlf', 'ignorecase', 'precomposeunicode', 'worktree'},
               'remote': {'url', 'fetch', 'pushurl'},
               'branch': {'remote', 'merge'},
               'submodule': {'url', 'active'}}
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith(('#', ';')):
            continue
        require(not line.endswith('\\'), 'continued Git config is unsupported')
        if line.startswith('['):
            match = re.fullmatch(r'\[([A-Za-z][A-Za-z0-9-]*)(?: "([^"\\]*)")?\]', line)
            require(match is not None, 'unsupported Git config section syntax')
            section, subsection = match[1].lower(), match[2]
            require(section in allowed and ((section == 'core') == (subsection is None)),
                    'unsupported Git config authority section')
            continue
        match = re.fullmatch(r'([A-Za-z][A-Za-z0-9-]*)\s*=\s*(.*)', line)
        require(match is not None and section in allowed, 'unsupported Git config assignment')
        key, value = match[1].lower(), match[2]
        require(key in allowed[section] and (section, subsection, key) not in seen,
                'unknown or duplicate Git config authority')
        seen.add((section, subsection, key))
        if section == 'core':
            core[key] = value.lower()
            if key == 'worktree':
                require('"' not in value and '\\' not in value
                        and plain_gitfile_target(gitdir, value, root, account) == checkout,
                        'core.worktree is not the exact contained submodule worktree')
                continue
            require((key == 'repositoryformatversion' and value == '0')
                    or (key in ('bare', 'autocrlf') and value.lower() == 'false')
                    or (key in ('filemode', 'logallrefupdates', 'ignorecase', 'precomposeunicode')
                        and value.lower() in ('true', 'false')),
                    'unsupported core Git object/worktree format')
        elif section == 'submodule' and key == 'active':
            require(value.lower() in ('true', 'false'), 'unsupported submodule active value')
    require(core.get('repositoryformatversion') == '0' and core.get('bare') == 'false',
            'GitDB is not an ordinary SHA1 nonbare checkout')


def git_database(checkout, root, parent_gitdir, account):
    worktree_chain = plain_directory_chain(checkout, root, account)
    marker = checkout / '.git'
    before = marker.lstat()
    if stat.S_ISDIR(before.st_mode):
        gitdir = marker
        marker_row = dict(kind='directory', identity=identity(before))
    else:
        require(parent_gitdir is not None and stat.S_ISREG(before.st_mode),
                'top-level or special Gitfile authority is unsupported')
        data = account.metadata_file(marker)
        require(len(data) <= 4096 and data.startswith(b'gitdir: ') and data.endswith(b'\n')
                and data.count(b'\n') == 1, 'malformed bounded submodule Gitfile')
        target = data[len(b'gitdir: '):-1].decode('utf-8')
        gitdir = plain_gitfile_target(checkout, target, root, account)
        modules = parent_gitdir / 'modules'
        require(gitdir != modules and gitdir.is_relative_to(modules),
                'submodule Gitfile is not under its immediate parent GitDB/modules')
        require(identity(marker.lstat()) == identity(before), 'Gitfile changed while binding GitDB')
        marker_row = dict(kind='gitfile', identity=identity(before),
                          sha256=hashlib.sha256(data).hexdigest(), target=target)
    database_chain = plain_directory_chain(gitdir, root, account)
    require((gitdir / 'objects').is_dir() and not (gitdir / 'objects').is_symlink(),
            'GitDB has no contained ordinary object store')
    safe_git_config(account.metadata_file(gitdir / 'config'), checkout, gitdir, root, account)
    snapshot = {}
    for base, dirs, files in os.walk(gitdir, followlinks=False, onerror=walk_error):
        account.debit(entries=len(dirs) + len(files))
        for name in sorted(dirs + files):
            path = Path(base) / name
            relative = str(path.relative_to(gitdir))
            relative_path(relative)
            info = path.lstat()
            require(stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode),
                    'symlink or special file in GitDB authority')
            parts = PurePosixPath(relative).parts
            require(name not in ('commondir', 'config.worktree')
                    and not (len(parts) >= 3 and parts[-3:] == ('objects', 'info', 'alternates'))
                    and not (len(parts) >= 2 and parts[-2:] == ('info', 'grafts'))
                    and not (name.endswith('.promisor') and 'objects' in parts),
                    'external/worktree/alternate/graft/promisor GitDB authority is unsupported')
            row = dict(identity=identity(info))
            if stat.S_ISREG(info.st_mode) and 'objects' not in parts:
                row['sha256'] = hashlib.sha256(account.metadata_file(path)).hexdigest()
            snapshot[relative] = row
    require('HEAD' in snapshot and 'config' in snapshot, 'GitDB lacks HEAD/config authority')
    require(identity(marker.lstat()) == identity(before), 'Git authority marker changed during census')
    return gitdir, dict(checkout=str(checkout), gitdir=str(gitdir), marker=marker_row,
                        worktree_chain=worktree_chain, database_chain=database_chain,
                        metadata=snapshot)


def git_worktree_files(root, gitlinks, account):
    """Census parent-owned paths; each pruned Gitlink has its own full census."""
    files, directories = {}, set()
    for base, dirs, names in os.walk(root, followlinks=False, onerror=walk_error):
        account.debit(entries=len(dirs) + len(names))
        if Path(base) == root:
            dirs[:] = [name for name in dirs if name != '.git']
            names = [name for name in names if name != '.git']
        for name in dirs + names:
            path = Path(base) / name
            relative = str(path.relative_to(root))
            relative_path(relative)
            mode = path.lstat().st_mode
            require(stat.S_ISDIR(mode) or stat.S_ISREG(mode) or stat.S_ISLNK(mode),
                    'special Git worktree source entry')
            if stat.S_ISDIR(mode):
                directories.add(relative)
            else:
                files[relative] = path
        dirs[:] = [name for name in dirs
                   if str((Path(base) / name).relative_to(root)) not in gitlinks]
    return files, directories


def observed_git_link(path, target, account):
    before = path.lstat()
    require(stat.S_ISLNK(before.st_mode) and before.st_size == len(target),
            'Git symlink identity differs from its authenticated blob')
    account.debit(len(target))
    require(os.fsencode(os.readlink(path)) == target
            and identity(path.lstat()) == identity(before),
            'Git symlink target changed while observing it')
    return identity(before)


def authenticated_git_symlinks(checkout, expected, directories, targets, account):
    """Resolve committed file aliases only through the authenticated raw tree.

    Process components in kernel order, expanding each link before any following
    '..'. The generated marker and excluded .git data have no admitted row.
    Directory aliases and missing endpoints are unsupported, never exemptions.
    """
    for original in targets:
        account.debit(len(os.fsencode(original)), entries=1)
        pending = list(reversed(PurePosixPath(original).parts))
        resolved, links = [], []
        endpoint, hops = None, 0
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
            account.debit(sum(len(os.fsencode(p)) + 1 for p in resolved)
                          + len(os.fsencode(part)))
            current = '/'.join([*resolved, part])
            if current in directories:
                actual = checkout / current
                require(actual.is_dir() and not actual.is_symlink(),
                        'authenticated Git directory changed during link resolution')
                resolved.append(part)
                continue
            row = expected.get(current)
            require(row is not None, 'Git symlink enters unauthenticated source or generated metadata')
            if row['mode'] == '120000':
                hops += 1
                require(hops <= 40, 'Git symlink chain exceeds the bounded follow limit')
                target = targets[current]
                observed = observed_git_link(checkout / current, target, account)
                account.debit(len(target))
                # Count before splitting/copying: the hop bound does not bound
                # a target with many components. Repeated work stays charged.
                account.debit(entries=target.count(b'/') + 1)
                text = os.fsdecode(target)
                require(text and not text.startswith('/')
                        and not any(ord(c) < 32 or ord(c) == 127 for c in text),
                        'absolute, empty or control-bearing Git symlink target')
                links.append((current, target, observed))
                pending.extend(reversed(text.split('/')))
                continue
            require(row['mode'] in ('100644', '100755') and not pending,
                    'Git symlink traverses a non-directory or has no regular committed endpoint')
            endpoint = current
        require(endpoint is not None,
                'Git symlink has no authenticated regular committed endpoint')
        actual_endpoint = checkout / endpoint
        require(actual_endpoint.is_file() and not actual_endpoint.is_symlink()
                and (checkout / original).resolve(strict=True) == actual_endpoint,
                'actual Git symlink resolution differs from its authenticated tree')
        for current, target, observed in links:
            require(observed_git_link(checkout / current, target, account) == observed,
                    'Git symlink chain identity changed during resolution')
        expected[original]['resolved_tracked_source'] = endpoint
        expected[original]['symlink_chain'] = [current for current, _, _ in links]
