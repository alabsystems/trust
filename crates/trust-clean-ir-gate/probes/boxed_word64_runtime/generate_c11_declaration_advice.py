#!/usr/bin/env python3
"""Untrusted exact declaration/span advice from retained complete Clang DATA.
Lean parses source characters and derives types; these annotations authorize
nothing. All macro alternatives are retained (no guessed conditional selection).
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def produce(capture, out):
    out.mkdir()
    book = json.loads((capture / 'DEPENDENCIES_BEFORE.json').read_text())
    result = json.loads((capture / 'RESULT.json').read_text())
    ast_raw = (capture / 'typed-ast.out').read_bytes()
    assert sha(ast_raw) == result['complete_ast']
    ast = json.loads(ast_raw)
    header = (capture / 'runtime/include/clean_runtime.h').read_bytes()
    assert sha(header) == result['header']
    nodes = {}

    def walk(node):
        if node.get('kind') == 'TypedefDecl' and node.get('name') in {
            'uint8_t', 'uint16_t', 'uint32_t', 'clean_obj_header', 'clean_obj'
        }:
            assert node['name'] not in nodes
            nodes[node['name']] = node
        for child in node.get('inner', []):
            walk(child)

    walk(ast)
    rows = []
    owners = {}
    for name, node in nodes.items():
        if name.startswith('clean_obj'):
            raw = header
            owner = 'runtime/include/clean_runtime.h'
        else:
            matches = [(owner, data) for owner, data in book.items()
                       if owner.endswith('/_' + name + '.h')]
            assert len(matches) == 1
            owner, data = matches[0]
            raw = (capture / 'source-dependencies' / data['sha256']).read_bytes()
            assert sha(raw) == data['sha256'] and len(raw) == data['bytes']
        begin = node['range']['begin']['offset']
        end = node['range']['end']['offset'] + node['range']['end']['tokLen']
        assert raw[end:end + 1] == b';'
        end += 1
        fragment = raw[begin:end]
        assert fragment.startswith(b'typedef ') and name.encode() in fragment
        owners[owner] = raw
        rows.append({'name': name, 'owner': owner, 'owner_sha256': sha(raw),
                     'begin': begin, 'end': end, 'raw': fragment.decode('utf-8'),
                     'sha256': sha(fragment), 'clang_advice': node})
    for suffix in ['stdbool.h', 'stdatomic.h']:
        matches = [(owner, data) for owner, data in book.items()
                   if owner.endswith('/' + suffix)]
        assert len(matches) == 1
        owner, data = matches[0]
        raw = (capture / 'source-dependencies' / data['sha256']).read_bytes()
        assert sha(raw) == data['sha256'] and len(raw) == data['bytes']
        owners[owner] = raw
    owners['runtime/include/clean_runtime.h'] = header
    wanted = {'bool', 'true', 'false', 'atomic_load_explicit', 'atomic_fetch_add_explicit',
              'atomic_fetch_sub_explicit', 'atomic_thread_fence', 'CLEAN_RC_STICKY_DROP', 'CLEAN_RC_STICKY'}
    for owner, raw in owners.items():
        offset = 0
        for line in raw.splitlines(keepends=True):
            match = re.match(rb'#\s*define\s+([A-Za-z_][A-Za-z_0-9]*)', line)
            if match and match[1].decode() in wanted:
                rows.append({'name': match[1].decode(), 'owner': owner,
                             'owner_sha256': sha(raw), 'begin': offset,
                             'end': offset + len(line), 'raw': line.decode('utf-8'),
                             'sha256': sha(line), 'scope': 'all alternatives; branch activation UNPROVED'})
            offset += len(line)
    owner_dir = out / 'owners'
    owner_dir.mkdir()
    for owner, raw in owners.items():
        (owner_dir / sha(raw)).write_bytes(raw)
    (out / 'DECLARATIONS.json').write_text(json.dumps(rows, indent=2) + '\n')
    lines = ['-- Copyright 2026 Andrew Yates | Apache-2.0', 'import C11HeaderDeclarations',
             'namespace C11ActualDeclarationData', 'open C11HeaderDeclarations C11HeaderTyping']
    counts = {}
    for row in rows:
        name = row['name']
        index = counts.get(name, 0)
        counts[name] = index + 1
        key = name + '_' + str(index)
        lines += [f'def {key} : String := {json.dumps(row["raw"], ensure_ascii=False)}']
    lines += ['end C11ActualDeclarationData', '']
    (out / 'C11ActualDeclarationData.lean').write_text('\n'.join(lines))
    files = {str(p.relative_to(out)): sha(p.read_bytes()) for p in sorted(out.rglob('*')) if p.is_file()}
    (out / 'INDEX.json').write_text(json.dumps({'files': files, 'capture_ast_sha256': sha(ast_raw),
        'producer_sha256': sha(Path(__file__).read_bytes()),
        'scope': 'untrusted exact complete declaration spans and owner DATA, no active-TU or typing claim'}, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    produce(args.capture, args.out)
