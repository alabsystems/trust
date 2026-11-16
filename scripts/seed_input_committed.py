"""Reconstruct Git's committed Merkle tree from actual source input bytes.

No Git executable or object-cache assertion is used by post-close validation.
The live capture supplies exact commit-object bytes and the committed/index
projection; recursive gitlinks must each have their own physical repository.
"""
from __future__ import annotations
import hashlib
import os
from pathlib import Path
import re
import stat

HERE = Path(__file__).resolve().parent
records = __trust_source_loader__.module('trust_input_records', HERE / 'seed_input_records.py')
require, remaining = records.require, records.remaining


def object_id(kind, raw, algorithm):
    value = hashlib.new(algorithm)
    value.update(f'{kind} {len(raw)}\0'.encode() + raw)
    return value.hexdigest()


def tree_id(entries, algorithm):
    """Git tree order compares a directory as its name followed by '/'."""
    root = {}
    for row in entries:
        path = records.relative(row['path'])
        branch = root
        for part in path.parts[:-1]:
            branch = branch.setdefault(part, {})
            require(type(branch) is dict, 'source path collides with a committed leaf')
        require(path.name not in branch and row['git_mode'] in ('100644','100755','120000','160000'),
                'duplicate or invalid committed source leaf')
        require(type(row['object_id']) is str and re.fullmatch('[0-9a-f]{40}|[0-9a-f]{64}', row['object_id']),
                'invalid source Git object')
        branch[path.name] = ('leaf', row)

    def visit(branch):
        payloads = []
        for name, value in branch.items():
            raw_name = os.fsencode(name)
            require(b'\0' not in raw_name and b'/' not in raw_name, 'invalid Git tree leaf')
            directory = type(value) is dict
            leaf = None if directory else value[1]
            mode, oid = ('40000', visit(value)) if directory else (leaf['git_mode'], leaf['object_id'])
            require(len(oid) == hashlib.new(algorithm).digest_size * 2, 'mixed source object algorithms')
            payloads.append((raw_name + (b'/' if directory else b''),
                             mode.encode() + b' ' + raw_name + b'\0' + bytes.fromhex(oid)))
        return object_id('tree', b''.join(payload for _, payload in sorted(payloads)), algorithm)

    return visit(root)


def committed_rows(root, entries, commit, tree, raw_commit, end):
    remaining(end)
    root = Path(root)
    require(root.resolve(strict=True) == root and root.is_dir(), 'source repository root is not canonical')
    require(re.fullmatch('[0-9a-f]{40}|[0-9a-f]{64}', commit) is not None,
            'source repository commit is malformed')
    algorithm = 'sha1' if len(commit) == 40 else 'sha256'
    require(object_id('commit', raw_commit, algorithm) == commit
            and raw_commit.startswith(b'tree ' + tree.encode() + b'\n'),
            'source commit object does not authenticate the captured tree')
    require(type(entries) is list and 0 < len(entries) <= records.ENTRY_LIMIT,
            'source repository entry bound failed')
    result, parents, total = [], {Path('.')}, 0
    for entry in entries:
        remaining(end)
        require(type(entry) is dict and set(entry) == {'path','git_mode','object_id'},
                'invalid source committed leaf projection')
        rel = records.relative(entry['path'])
        parents.update(Path(*rel.parts[:i]) for i in range(1, len(rel.parts)))
        named = root.joinpath(*rel.parts)
        require(all(not parent.is_symlink() for parent in named.parents if parent.is_relative_to(root)),
                'source tracked parent became a link')
        mode = entry['git_mode']
        if mode == '160000':
            require(named.resolve(strict=True) == named and named.is_dir(), 'source gitlink is not an actual provider')
            observed = {'kind':'gitlink', 'mode':stat.S_IMODE(named.lstat().st_mode)}
        elif mode == '120000':
            observed = records.link(named, end)
            literal = os.fsencode(observed['target'])
            require(object_id('blob', literal, algorithm) == entry['object_id'],
                    'source literal link differs from its committed blob')
        else:
            require(mode in ('100644','100755'), 'unsupported committed source mode')
            observed, _ = records.regular(named, end, object_algorithm=algorithm)
            require(observed.pop('object_id') == entry['object_id']
                    and observed['mode'] & 0o111 == int(mode, 8) & 0o111,
                    'source bytes/executable bits differ from the committed blob')
            total += observed['bytes']
            require(total <= records.PAYLOAD_LIMIT, 'source repository exceeds payload bound')
        result.append({**entry, **observed})
    require(tree_id(entries, algorithm) == tree, 'tracked source projection does not reconstruct committed tree')
    directory_rows = []
    for parent in sorted(parents, key=str):
        remaining(end)
        named = root / parent
        st = named.lstat()
        require(stat.S_ISDIR(st.st_mode) and not named.is_symlink(), 'tracked source parent is not a directory')
        directory_rows.append({'path':parent.as_posix(), 'kind':'dir', 'mode':stat.S_IMODE(st.st_mode)})
    return {'commit':commit, 'tree':tree, 'commit_object_hex':raw_commit.hex(),
            'files':sorted(result, key=lambda row:row['path']), 'directories':directory_rows}


def verify_repository(root, capture, store, end):
    rows = store.read_rows(capture['files'])
    directories = store.read_rows(capture['directories'])
    projection = [{key:row[key] for key in ('path','git_mode','object_id')} for row in rows]
    raw = bytes.fromhex(capture['commit_object_hex'])
    actual = committed_rows(root, projection, capture['commit'], capture['tree'], raw, end)
    require(actual['files'] == rows and actual['directories'] == directories,
            'physical committed source file/mode/literal link/parent differs after closure')
    return rows


def verify_providers(root, captures, store, end, expected_commit):
    require(type(captures) is list and captures, 'recursive physical source proof is missing')
    by_path = {}
    all_rows = {}
    for capture in captures:
        remaining(end)
        relative = capture['repository']
        require(relative == '.' or records.relative(relative), 'invalid source provider root')
        require(relative not in by_path, 'duplicate source provider root')
        by_path[relative] = capture
    require('.' in by_path and by_path['.']['commit'] == expected_commit, 'source root commit differs from original owner')
    wanted = {'.':expected_commit}
    pending = ['.']
    while pending:
        relative = pending.pop()
        require(relative in by_path and by_path[relative]['commit'] == wanted[relative],
                'recursive source provider is absent or differs from original gitlink')
        rows = verify_repository(root / relative, by_path[relative], store, end)
        all_rows[relative] = rows
        for row in rows:
            if row['kind'] == 'gitlink':
                child = (Path(relative) / row['path']).as_posix()
                require(child not in wanted, 'recursive source provider is repeated')
                wanted[child] = row['object_id']
                pending.append(child)
    require(set(by_path) == set(wanted), 'source proof invents an unconnected provider')
    return all_rows
