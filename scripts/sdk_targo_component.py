# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Andrew Yates
#!/usr/bin/env python3
"""Explicit native Targo/cargo pair in a NEW SDK copy; never a compiler mint.

No command runs at import. Native qualification and whole-stage readiness remain
separate. The independent inspector returns the sole typed frontend overlay.
"""
from __future__ import annotations

import base64
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass

SCHEMA = 'trust.sdk-targo-component.v1'
INSTALL_SCHEMA = 'trust.sdk-targo-install.v1'
QUALIFIED_SCHEMA = 'trust.sdk-targo-qualified.v1'
RECORD = 'TARGO-COMPONENT.json'
DETAILS = 'TARGO-COMPONENT.evidence'
QUALIFIED = 'TARGO-QUALIFIED.json'
ALIASES = ('targo', 'cargo')
COMPILER_SOURCE = '82bb867eddb94599f68194f701c766f2b6f5a02f'
COMPILER_SHA256 = '5d505579da7eeaac54868d794d5e7fb4c142de28ebf06c35d3dbb92d07a3671e'
PORT_BASE = '32a1d954b4e6024194976d8cb9b9642fee49242c'
CAUSAL_FIX = '00d02c75809a974263b66e4ab2dabfc443bc0625'
HOST = 'aarch64-apple-darwin'
PRODUCTION_PATHS = frozenset((
    'src/jobserver_utils/src/lib.rs',
    'src/tools/targo/crates/targo-core/src/compiler/compilation.rs',
    'src/tools/targo/crates/targo-core/src/ops/cargo_run.rs',
))
TEST_PATH = 'src/jobserver_utils/src/tests/transport_witnesses.rs'
DOC_PATH = 'docs/DECISION_QUEUE.md'
LOCKS = frozenset(('Cargo.lock', 'src/tools/targo/Cargo.lock'))
BASE_SOURCE_PATHS = frozenset((
    'crates/trust-coordinator/src/coordinator.rs',
    'crates/trust-resource-controller/Cargo.lock',
    'crates/trust-resource-controller/Cargo.toml',
    'crates/trust-resource-controller/examples/probe-scheduler-control.rs',
    'crates/trust-resource-controller/src/client.rs',
    'crates/trust-resource-controller/src/client/probe_scheduler.rs',
    'crates/trust-resource-controller/src/client/sdk.rs', DOC_PATH,
    'scripts/tests/doctor_probe_custody_test.py', 'targo-trust/Cargo.toml',
    'targo-trust/src/main.rs', 'targo-trust/src/pipeline/probe.rs',
    'targo-trust/src/pipeline/run.rs', 'targo-trust/src/probe_scheduler.rs',
    'targo-trust/src/tool_identity.rs',
))
CONTROLS = (
    'descendant_owner_recovers_exact_pipe_without_replenishing_borrowed_credit',
    'descendant_clone_retains_recovery_until_last_scheduler_owner_drops',
    'native_targo_run_keeps_selected_recovery_owner',
    'native_targo_run_refuses_unavailable_or_malformed_transport',
)
TRANSPORT_SOURCE_SHA256 = 'cc84dcdd76c821c9ab65164e4edbcf1183a4dd7dc36d100df69d0e73cdfa9e64'
PREPARED_FILES = frozenset((
    'base-stage-authority.json', 'base-inventory.json', 'source-relation.json',
    'build.context.json', 'build.result.json', 'build.stdout.jsonl', 'build.stderr',
    'compiler-version.stdout', 'compiler-version.stderr',
    'targo-version.stdout', 'targo-version.stderr', 'cargo-version.stdout', 'cargo-version.stderr',
    'image.json', 'image.codesign.stdout', 'image.codesign.stderr',
    'transport.context.json', 'transport.result.json', 'transport.stdout', 'transport.stderr',
))
INSTALLED_FILES = PREPARED_FILES | {'installation.json', 'installed-inventory.json'}
ALL_FILES = INSTALLED_FILES | {
    'native-doctor.stdout', 'native-doctor.stderr',
    'native-targo-version.stdout', 'native-targo-version.stderr',
    'native-cargo-version.stdout', 'native-cargo-version.stderr',
    'native-qualified.context.json', 'native-qualified.result.json', 'native-inventory.json',
}
MAX_RECORD = 32 << 20
MAX_BINARY = 1 << 30
CANONICAL_MODULE = '_trust_sdk_native_targo_component_v1'
_SEAL = object()


class Refusal(ValueError):
    pass


def require(value, reason):
    if not value:
        raise Refusal(reason)


def keys(value, expected, label):
    require(type(value) is dict and set(value) == set(expected), label + ' fields differ')


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def digest(value):
    require(type(value) is str and re.fullmatch('[0-9a-f]{64}', value), 'invalid digest')
    return value


def commit(value):
    require(type(value) is str and re.fullmatch('[0-9a-f]{40}', value), 'invalid Git OID')
    return value


def relative(value):
    require(type(value) is str and value and '\\' not in value and '\0' not in value,
            'invalid relative path')
    p = PurePosixPath(value)
    require(not p.is_absolute() and all(x not in ('', '.', '..') for x in value.split('/')),
            'relative path traverses')
    return value


def absolute(value):
    require(type(value) is str and Path(value).is_absolute() and '..' not in Path(value).parts,
            'invalid observed absolute path')
    return value


def hash_map(value, expected=None):
    require(type(value) is dict and bool(value), 'empty hash map')
    if expected is not None:
        require(set(value) == set(expected), 'hash map key set differs')
    for name, hashed in value.items():
        relative(name)
        digest(hashed)
    return value


def zero(value):
    require(type(value) is int and value == 0, 'exit is not typed actual0')


def unique(pairs):
    result = {}
    for name, value in pairs:
        require(name not in result, 'duplicate JSON field: ' + name)
        result[name] = value
    return result


def parse(raw):
    try:
        value = json.loads(raw, object_pairs_hook=unique)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise Refusal('invalid JSON') from error
    require(type(value) is dict, 'record is not an object')
    return value


def physical_directory(path):
    p = Path(path)
    require(p.is_absolute() and '..' not in p.parts and p.resolve(strict=True) == p,
            'directory is not physical')
    require(stat.S_ISDIR(p.lstat().st_mode), 'directory is linked or not a directory')
    return p


def regular(path, bound=MAX_RECORD):
    p = Path(path)
    require(p.is_absolute() and '..' not in p.parts, 'file path is not absolute')
    physical_directory(p.parent)
    before = p.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_size <= bound, 'file linked/large/nonregular')
    identity = lambda x: (x.st_dev, x.st_ino, x.st_mode, x.st_size, x.st_mtime_ns, x.st_ctime_ns)
    with os.fdopen(os.open(p, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0)), 'rb') as stream:
        opened = os.fstat(stream.fileno())
        require(identity(opened) == identity(before), 'file changed before open')
        raw = stream.read(bound + 1)
        require(len(raw) <= bound and identity(opened) == identity(os.fstat(stream.fileno()))
                == identity(p.lstat()), 'file changed while read')
    return raw


def document(path, expected=None):
    raw = regular(path)
    if expected is not None:
        require(sha256(raw) == digest(expected), 'record digest differs')
    return parse(raw), raw


class Evidence:
    """Fixed role names and a single immutable byte read per local reference."""
    def __init__(self, directory):
        self.root = physical_directory(directory)
        self.cache = {}

    def read(self, reference, name, bound=MAX_RECORD):
        require(name in ALL_FILES, 'unknown evidence role')
        keys(reference, ('path', 'sha256'), 'fixed reference')
        require(reference['path'] == name, 'reference is not its fixed local role')
        expected = digest(reference['sha256'])
        if name not in self.cache:
            self.cache[name] = regular(self.root / name, bound)
        raw = self.cache[name]
        require(len(raw) <= bound and sha256(raw) == expected, 'evidence bytes differ')
        return raw

    def json(self, reference, name):
        return parse(self.read(reference, name))

    def literal(self, name):
        require(name in ALL_FILES, 'unknown evidence role')
        if name not in self.cache:
            self.cache[name] = regular(self.root / name)
        return self.cache[name]

    def complete(self, expected):
        require(set(p.name for p in self.root.iterdir()) == set(expected),
                'missing or unexpected component evidence file')
        require(all(stat.S_ISREG(p.lstat().st_mode) for p in self.root.iterdir()),
                'linked or nonregular evidence')


def retirement(value):
    keys(value, ('completed', 'actual_exit', 'owned_command_drained'), 'retirement')
    zero(value['actual_exit'])
    require(value['completed'] is True and value['owned_command_drained'] is True,
            'command ownership not retired')


def strings(value):
    require(type(value) is list and bool(value) and all(type(x) is str for x in value),
            'invalid argument/string list')
    return value


def phase(value, name, evidence, prefix=None):
    keys(value, ('name', 'exit', 'argv', 'stdout', 'stderr'), 'phase')
    require(value['name'] == name, 'phase role differs')
    zero(value['exit'])
    strings(value['argv'])
    stem = name if prefix is None else prefix
    return {s: evidence.read(value[s], stem + '.' + s) for s in ('stdout', 'stderr')}


def tool_map(root):
    root = physical_directory(root)
    directory = physical_directory(root / 'bin')
    paths = [p for p in directory.iterdir() if not (p.is_dir() and not p.is_symlink())]
    helper = root / 'libexec/trust-analyzer-proc-macro-srv'
    if os.path.lexists(helper):
        paths.append(helper)
    result = {}
    for p in sorted(paths):
        require(p.name not in result, 'duplicate tool basename')
        result[p.name] = sha256(regular(p, MAX_BINARY))
    require(all(x in result for x in (*ALIASES, 'trustc', 'targo-trust')), 'required tool absent')
    return result


def inventory(root):
    root = physical_directory(root)
    hierarchy = physical_directory(root.parent)
    require(set(p.name for p in hierarchy.iterdir()) == {root.name, 'rustc-private-sysroots'}
            and root.name != 'rustc-private-sysroots', 'SDK/private hierarchy has unexpected roots')
    physical_directory(hierarchy / 'rustc-private-sysroots')
    rows = []
    def visit(directory):
        for p in sorted(directory.iterdir()):
            rel = p.relative_to(hierarchy).as_posix()
            if rel in (root.name + '/' + name for name in (RECORD, DETAILS, QUALIFIED)):
                continue
            relative(rel)
            info = p.lstat()
            row = {'path': rel, 'mode': stat.S_IMODE(info.st_mode)}
            if stat.S_ISLNK(info.st_mode):
                row.update(kind='symlink', target=os.readlink(p))
            elif stat.S_ISDIR(info.st_mode):
                row['kind'] = 'directory'
                rows.append(row)
                visit(p)
                continue
            else:
                require(stat.S_ISREG(info.st_mode), 'unsupported inventory entry')
                raw = regular(p, MAX_BINARY)
                row.update(kind='file', bytes=len(raw), sha256=sha256(raw))
            rows.append(row)
    visit(hierarchy)
    return {'schema': 'trust.sdk-component-inventory.v1',
            'entries': sorted(rows, key=lambda row: row['path'])}


def inventory_shape(value):
    keys(value, ('schema', 'entries'), 'inventory')
    require(value['schema'] == 'trust.sdk-component-inventory.v1' and type(value['entries']) is list,
            'inventory schema differs')
    seen = []
    for row in value['entries']:
        require(type(row) is dict, 'inventory row absent')
        relative(row.get('path'))
        kind = row.get('kind')
        fields = {'path', 'kind', 'mode'}
        fields |= {'bytes', 'sha256'} if kind == 'file' else ({'target'} if kind == 'symlink' else set())
        keys(row, fields, 'inventory row')
        require(kind in ('file', 'directory', 'symlink'), 'inventory kind differs')
        require(type(row['mode']) is int and 0 <= row['mode'] <= 0o777, 'inventory mode invalid')
        if kind == 'file':
            require(type(row['bytes']) is int and row['bytes'] >= 0, 'inventory size invalid')
            digest(row['sha256'])
        elif kind == 'symlink':
            require(type(row['target']) is str and '\0' not in row['target'], 'link target invalid')
        seen.append(row['path'])
    require(seen == sorted(set(seen)), 'inventory duplicate/order differs')
    roots = {name.split('/')[0] for name in seen}
    require('rustc-private-sysroots' in roots and len(roots) == 2,
            'inventory must bind one SDK plus its sibling private hierarchy')
    return value


def inventory_stage(value):
    inventory_shape(value)
    roots = {row['path'].split('/')[0] for row in value['entries']}
    return (roots - {'rustc-private-sysroots'}).pop()


def pair_inventory(before, after, artifact):
    inventory_shape(before)
    inventory_shape(after)
    old = {r['path']: r for r in before['entries']}
    new = {r['path']: r for r in after['entries']}
    stage = inventory_stage(before)
    require(inventory_stage(after) == stage, 'SDK hierarchy basename changed')
    require(set(old) == set(new), 'inventory entry set changed')
    for name in old:
        if name in (stage + '/bin/targo', stage + '/bin/cargo'):
            require(new[name] == {'path': name, 'kind': 'file', 'mode': artifact['mode'],
                                  'bytes': artifact['bytes'], 'sha256': artifact['sha256']},
                    'alias artifact inventory differs')
        else:
            require(new[name] == old[name], 'unrelated/private/frontend/WP/Lean entry changed: ' + name)


def native_image(raw, host):
    """Read only load commands; a declared image report is never native ABI authority."""
    require(host == HOST and len(raw) >= 32, 'unsupported native image host/length')
    magic, cpu, subtype, kind, count, size, flags, reserved = struct.unpack_from('<8I', raw)
    require(magic == 0xfeedfacf and cpu == 0x100000c and subtype == 0 and kind == 2,
            'image is not thin ARM64 Mach-O executable')
    require(size <= len(raw) - 32 and count <= size // 8, 'Mach-O command bounds differ')
    at, end = 32, 32 + size
    libraries, signature = [], False
    for _ in range(count):
        require(at + 8 <= end, 'truncated Mach-O command')
        command, length = struct.unpack_from('<2I', raw, at)
        require(length >= 8 and length % 4 == 0 and at + length <= end, 'invalid Mach-O command size')
        require(command not in (0x27, 0x8000001c), 'loader environment/rpath is not admitted')
        if command in (0xc, 0x18, 0x80000018, 0x8000001f, 0x20, 0x80000023, 0xe):
            require(length >= 12, 'truncated library command')
            offset = struct.unpack_from('<I', raw, at + 8)[0]
            require(12 <= offset < length, 'invalid native string offset')
            chunk = raw[at + offset:at + length]
            require(b'\0' in chunk, 'unterminated native string')
            name = chunk.split(b'\0', 1)[0].decode('utf-8')
            if command == 0xe:
                require(name == '/usr/lib/dyld', 'non-system native loader')
            else:
                require(name.startswith(('/usr/lib/', '/System/Library/Frameworks/'))
                        and '..' not in PurePosixPath(name).parts, 'non-system native library')
                libraries.append(name)
        if command == 0x1d:
            require(length == 16, 'invalid code-signature command')
            offset, length_data = struct.unpack_from('<2I', raw, at + 8)
            require(length_data > 0 and offset <= len(raw) and length_data <= len(raw) - offset,
                    'code-signature bytes outside image')
            signature = True
        at += length
    require(at == end, 'native command count/size mismatch')
    return sorted(set(libraries)), signature


def _source_shape(source):
    keys(source, ('base', 'port_base', 'commit', 'tree', 'root', 'files', 'production_delta',
                  'test_delta', 'documentation_delta', 'outside_delta_sha256', 'locks',
                  'gitlinks', 'relation'), 'source')
    require(source['base'] == COMPILER_SOURCE and source['port_base'] == PORT_BASE,
            'source base differs')
    commit(source['commit']); commit(source['tree']); absolute(source['root'])
    hash_map(source['files'], BASE_SOURCE_PATHS | PRODUCTION_PATHS | {TEST_PATH})
    hash_map(source['production_delta'], PRODUCTION_PATHS)
    hash_map(source['test_delta'], (TEST_PATH,))
    hash_map(source['documentation_delta'], (DOC_PATH,))
    hash_map(source['locks'], LOCKS)
    require(type(source['gitlinks']) is dict, 'gitlinks absent')
    for path, oid in source['gitlinks'].items():
        relative(path); commit(oid)
    digest(source['outside_delta_sha256'])
    for values in (source['production_delta'], source['test_delta'], source['documentation_delta']):
        require(all(source['files'].get(k) == v for k, v in values.items()), 'source readset incomplete')


def record_shape(record):
    keys(record, ('schema', 'status', 'name', 'aliases', 'base', 'source', 'artifact',
                  'build', 'transport', 'retained_inputs_unchanged'), 'component')
    require(record['schema'] == SCHEMA and record['status'] == 'prepared'
            and record['name'] == 'targo' and record['aliases'] == list(ALIASES)
            and record['retained_inputs_unchanged'] is True, 'component identity differs')
    base = record['base']
    keys(base, ('compiler_source', 'host', 'compiler_sha256', 'mint_sha256',
                'frontend_component_sha256', 'frontend_qualified_sha256', 'frontend_artifact_sha256',
                'stage_binding_sha256', 'original_pair', 'before_tools', 'stage_authority', 'inventory'), 'base')
    require(base['compiler_source'] == COMPILER_SOURCE and base['host'] == HOST
            and base['compiler_sha256'] == COMPILER_SHA256, 'base compiler/host differs')
    for name in ('compiler_sha256', 'mint_sha256', 'frontend_component_sha256',
                 'frontend_qualified_sha256', 'frontend_artifact_sha256', 'stage_binding_sha256'):
        digest(base[name])
    hash_map(base['original_pair'], ALIASES); hash_map(base['before_tools'])
    require(base['original_pair']['targo'] == base['original_pair']['cargo'], 'original aliases differ')
    require(all(base['before_tools'].get(k) == v for k, v in base['original_pair'].items())
            and base['before_tools'].get('trustc') == base['compiler_sha256']
            and base['before_tools'].get('targo-trust') == base['frontend_artifact_sha256'],
            'base tool identities differ')
    _source_shape(record['source'])
    artifact = record['artifact']
    keys(artifact, ('sha256', 'bytes', 'mode', 'system_libraries'), 'artifact')
    digest(artifact['sha256'])
    require(type(artifact['bytes']) is int and 0 < artifact['bytes'] <= MAX_BINARY
            and artifact['mode'] == 0o755 and type(artifact['mode']) is int, 'artifact size/mode differs')
    strings(artifact['system_libraries'])
    require(artifact['system_libraries'] == sorted(set(artifact['system_libraries'])), 'library census differs')
    return record


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def _recipe(value):
    keys(value, ('mode', 'static_policy', 'source_recipe_sha256', 'config_sha256'), 'recipe')
    require(value['mode'] == 'ToolTarget' and value['static_policy'] in ('ordinary-vendored', 'all-static'),
            'unsupported Targo recipe')
    digest(value['source_recipe_sha256']); digest(value['config_sha256'])


def _source_relation(record, evidence):
    source = record['source']
    relation = evidence.json(source['relation'], 'source-relation.json')
    keys(relation, ('schema', 'compiler_source', 'port_base', 'candidate_commit', 'candidate_tree',
                    'causal_fix_commit', 'production_delta_before', 'production_delta_after',
                    'test_delta', 'documentation_delta', 'protected_tree_before_sha256',
                    'protected_tree_after_sha256', 'locks_before', 'locks_after',
                    'gitlinks_before', 'gitlinks_after', 'source_readset_sha256', 'completed'), 'source relation')
    require(relation['schema'] == 'trust.native-targo-source-relation.v1'
            and relation['compiler_source'] == source['base']
            and relation['port_base'] == source['port_base']
            and relation['candidate_commit'] == source['commit']
            and relation['candidate_tree'] == source['tree']
            and relation['causal_fix_commit'] == CAUSAL_FIX and relation['completed'] is True,
            'source relation identity differs')
    hash_map(relation['production_delta_before'], PRODUCTION_PATHS)
    for field, wanted in (('production_delta_after', 'production_delta'), ('test_delta', 'test_delta'),
                          ('documentation_delta', 'documentation_delta')):
        require(relation[field] == source[wanted], 'source delta relation differs')
    require(relation['protected_tree_before_sha256'] == relation['protected_tree_after_sha256']
            == source['outside_delta_sha256'], 'protected tracked source changed')
    require(relation['locks_before'] == relation['locks_after'] == source['locks'], 'lockfiles changed')
    require(relation['gitlinks_before'] == relation['gitlinks_after'] == source['gitlinks'], 'gitlinks changed')
    require(relation['source_readset_sha256'] == sha256(canonical(source['files'])), 'source readset differs')


def _version(raw, source, name, release=None, product=None):
    lines = raw.decode('utf-8').splitlines()
    require(lines and lines[0].startswith(name + ' '), 'native version branding differs')
    require([x for x in lines if x.startswith('commit-hash: ')] == ['commit-hash: ' + source],
            'native version own source differs')
    if release is not None:
        require([x for x in lines if x.startswith('release: ')] == ['release: ' + release],
                'native version retained release differs')
    require([x for x in lines if x.startswith('trust-repo-commit-hash: ')]
            == ['trust-repo-commit-hash: ' + source], 'native Trust source binding differs')
    if product is not None:
        require([x for x in lines if x.startswith('trust: ')] == ['trust: ' + product],
                'native product version differs')


def version_environment(value, source):
    keys(value, ('CFG_VER_HASH', 'CFG_COMMIT_HASH', 'CFG_SHORT_COMMIT_HASH',
                 'CFG_COMMIT_DATE', 'CFG_RELEASE', 'CFG_TRUST_VERSION'), 'version environment')
    require(value['CFG_VER_HASH'] == value['CFG_COMMIT_HASH'] == source
            and value['CFG_SHORT_COMMIT_HASH'] == source[:9]
            and type(value['CFG_COMMIT_DATE']) is str
            and re.fullmatch(r'[0-9]{4}-[0-9]{2}-[0-9]{2}', value['CFG_COMMIT_DATE'])
            and type(value['CFG_RELEASE']) is str and bool(value['CFG_RELEASE'])
            and type(value['CFG_TRUST_VERSION']) is str and bool(value['CFG_TRUST_VERSION']),
            'source-owned version tuple differs')
    return value


def _build(record, evidence):
    base, source, artifact, built = (record[k] for k in ('base', 'source', 'artifact', 'build'))
    keys(built, ('compiler', 'target', 'argv', 'features', 'recipe', 'context', 'result',
                 'cargo_json', 'cargo_stderr', 'compiler_version', 'targo_version', 'cargo_version', 'image'), 'build')
    keys(built['compiler'], ('source', 'sha256', 'observed_path', 'sysroot_inventory_sha256'), 'build compiler')
    require(built['compiler']['source'] == base['compiler_source']
            and built['compiler']['sha256'] == base['compiler_sha256'], 'build compiler is not retained82')
    absolute(built['compiler']['observed_path'])
    require(built['target'] == base['host'], 'build target differs')
    strings(built['features']); require(built['features'] == sorted(set(built['features'])), 'features not canonical')
    _recipe(built['recipe'])
    context = evidence.json(built['context'], 'build.context.json')
    keys(context, ('schema', 'source_commit', 'source_tree', 'port_base', 'source_root',
                   'target_directory', 'original_artifact_path', 'compiler', 'frontend', 'host',
                   'argv', 'features', 'recipe', 'input_inventory_sha256', 'lock_sha256',
                   'generated_lean_manifest_sha256', 'version_environment'), 'build context')
    require(context['schema'] == 'trust.native-targo-build-context.v1'
            and context['source_commit'] == source['commit'] and context['source_tree'] == source['tree']
            and context['port_base'] == source['port_base'] and context['source_root'] == source['root']
            and context['host'] == base['host'], 'build source/frame differs')
    for field in ('source_root', 'target_directory', 'original_artifact_path'):
        absolute(context[field])
    require(Path(context['original_artifact_path']).is_relative_to(Path(context['target_directory'])),
            'artifact not in declared target')
    keys(context['compiler'], ('observed_path', 'source_commit', 'sha256', 'observed_sysroot',
                               'sysroot_inventory_sha256'), 'observed build compiler')
    compiler = context['compiler']
    absolute(compiler['observed_path']); absolute(compiler['observed_sysroot'])
    require(compiler['source_commit'] == base['compiler_source']
            and compiler['sha256'] == base['compiler_sha256']
            and Path(compiler['observed_path']) == Path(compiler['observed_sysroot']) / 'bin/trustc'
            and compiler['observed_path'] == built['compiler']['observed_path']
            and compiler['sysroot_inventory_sha256'] == built['compiler']['sysroot_inventory_sha256']
            == base['inventory']['sha256'] == context['input_inventory_sha256'], 'build input ABI/compiler differs')
    keys(context['frontend'], ('observed_path', 'sha256'), 'build-driving frontend')
    absolute(context['frontend']['observed_path'])
    require(context['frontend']['sha256'] == base['before_tools']['targo']
            and Path(context['frontend']['observed_path']) == Path(compiler['observed_sysroot']) / 'bin/targo',
            'build frontend is not retained SDK Targo')
    require(context['lock_sha256'] == source['locks']['src/tools/targo/Cargo.lock'], 'build lock differs')
    digest(context['generated_lean_manifest_sha256'])
    version_env = version_environment(context['version_environment'], source['commit'])
    require(context['features'] == built['features'] and context['recipe'] == built['recipe'], 'build recipe differs')
    requested = ['all-static'] if built['recipe']['static_policy'] == 'all-static' else ['vendored-openssl', 'vendored-libgit2']
    argv = [context['frontend']['observed_path'], '--unverified', 'build', '--release', '--locked', '--offline',
            '--manifest-path', str(Path(source['root']) / 'src/tools/targo/Cargo.toml'), '--bin', 'targo',
            '--features', ','.join(requested), '--message-format=json-render-diagnostics']
    require(built['argv'] == context['argv'] == argv, 'build is not exact direct Targo recipe')
    require(set(requested) <= set(built['features']), 'canonical vendored features absent')
    result = evidence.json(built['result'], 'build.result.json')
    keys(result, ('schema', 'source_commit', 'source_tree', 'artifact_sha256', 'compiler_sha256',
                  'argv', 'context_sha256', 'cargo_json_sha256', 'exit', 'completed', 'retirement'), 'build result')
    zero(result['exit']); retirement(result['retirement'])
    require(result['schema'] == 'trust.native-targo-build-result.v1'
            and result['source_commit'] == source['commit'] and result['source_tree'] == source['tree']
            and result['artifact_sha256'] == artifact['sha256']
            and result['compiler_sha256'] == base['compiler_sha256']
            and result['argv'] == argv and result['completed'] is True
            and result['context_sha256'] == built['context']['sha256'], 'actual build result differs')
    raw = evidence.read(built['cargo_json'], 'build.stdout.jsonl')
    require(result['cargo_json_sha256'] == sha256(raw), 'Cargo JSON result binding differs')
    evidence.read(built['cargo_stderr'], 'build.stderr')
    executables = []
    for line in raw.splitlines():
        if not line.startswith(b'{'):
            continue
        item = parse(line)
        if item.get('reason') == 'compiler-artifact' and item.get('target', {}).get('name') == 'targo' \
                and item.get('executable') is not None:
            require(item.get('target', {}).get('kind') == ['bin'] and item.get('profile', {}).get('test') is False,
                    'artifact is not non-test native Targo binary')
            require(sorted(item.get('features', [])) == built['features'], 'artifact feature population differs')
            executables.append(item['executable'])
    require(executables == [context['original_artifact_path']], 'missing/ambiguous/foreign Cargo artifact')
    version = phase(built['compiler_version'], 'compiler-version', evidence)['stdout']
    require(built['compiler_version']['argv'] == [compiler['observed_path'], '-vV']
            and ('commit-hash: ' + base['compiler_source']) in version.decode().splitlines()
            and [x for x in version.decode().splitlines() if x.startswith('release: ')]
            == ['release: ' + version_env['CFG_RELEASE']],
            'retained compiler version differs')
    for name in ALIASES:
        observed = phase(built[name + '_version'], name + '-version', evidence)
        require(built[name + '_version']['argv'][1:] == ['--version', '--verbose']
                and Path(built[name + '_version']['argv'][0]).name == name,
                'version phase does not select its canonical alias')
        _version(observed['stdout'], source['commit'], name, version_env['CFG_RELEASE'],
                 version_env['CFG_TRUST_VERSION'])
    return context


def transport_manifest(source_root):
    return ('[package]\nname = "native-targo-custody-witness"\nversion = "0.0.0"\n'
            'edition = "2024"\n[workspace]\n[dependencies]\n'
            'jobserver_utils = { path = ' + json.dumps(str(Path(source_root) / 'src/jobserver_utils')) + ' }\n'
            'libc = "0.2"\n').encode()


def _pipe_identity(value):
    require(type(value) is list and len(value) == 4
            and all(type(x) is int and 0 <= x < 1 << 64 for x in value), 'pipe identity is not four u64s')
    return value


def transport_observation(number, outputs, context, original_pipe=None):
    """Derive finite observations from actual retained raw child output, not a supplied object."""
    subject = context['selected_subject']
    if number < 2:
        code, raw, _ = outputs[0]
        case = 'transport_witness_tests::' + CONTROLS[number]
        require(code == 0 and re.search(rb'(?m)^test ' + re.escape(case.encode()) + rb' \.\.\. ok\r?$', raw)
                and b'1 passed; 0 failed; 0 ignored;' in raw, 'missing exact single owner-test pass')
        return {'kind': 'source-test', 'test_case': case, 'passed': 1, 'failed': 0, 'ignored': 0}
    reports = []
    for code, raw, _ in outputs:
        lines = [line[len(b'NATIVE_TARGO_CUSTODY '):] for line in raw.splitlines()
                 if line.startswith(b'NATIVE_TARGO_CUSTODY ')]
        require(len(lines) == 1, 'missing/ambiguous actual mini-child observation')
        reports.append((code, parse(lines[0])))
    if number == 2:
        code, child = reports[0]
        keys(child, ('kind', 'observed_pipe', 'available_before', 'available_after', 'compiler_exit',
                     'compiler_stdout_hex', 'compiler_stderr_hex', 'sysroot', 'marker'), 'positive mini observation')
        zero(code); zero(child['compiler_exit']); zero(child['available_before']); zero(child['available_after'])
        require(child['kind'] == 'native-run' and child['marker'] == 'native-targo-custody-positive-v1'
                and child['sysroot'] == subject
                and _pipe_identity(child['observed_pipe']) == _pipe_identity(original_pipe),
                'mini did not retain the original selected scheduler/compiler')
        streams = []
        for name in ('compiler_stdout_hex', 'compiler_stderr_hex'):
            value = child[name]
            require(type(value) is str and len(value) % 2 == 0 and re.fullmatch('[0-9a-f]*', value),
                    'mini raw compiler stream is not canonical hex')
            streams.append(bytes.fromhex(value))
        require(streams[0].decode('utf-8').strip() == subject, 'plain compiler child selected another sysroot')
        return {**{k: v for k, v in child.items() if k not in ('compiler_stdout_hex', 'compiler_stderr_hex')},
                'child_exit': code, 'original_pipe': original_pipe,
                'compiler_stdout_sha256': sha256(streams[0]), 'compiler_stderr_sha256': sha256(streams[1])}
    cases = []
    for mode, (code, child) in zip(('missing', 'malformed'), reports):
        expected = {'mode': mode, 'child_exit': 75,
                    'reason': 'checked-import-' + ('unavailable' if mode == 'missing' else 'error'),
                    'compiler_started': False, 'marker': False}
        require(type(code) is int and code == 75 and canonical(child) == canonical(expected),
                'negative child did not refuse before starting compiler')
        cases.append(child)
    require(len(cases) == 2, 'negative child population differs')
    return {'kind': 'native-run-refusal', 'cases': cases}


def _transport(record, evidence):
    transport, source, base, artifact = (record[k] for k in ('transport', 'source', 'base', 'artifact'))
    keys(transport, ('context', 'result', 'stdout', 'stderr', 'controls'), 'transport')
    require(transport['controls'] == list(CONTROLS), 'transport control population differs')
    context = evidence.json(transport['context'], 'transport.context.json')
    keys(context, ('schema', 'source_commit', 'artifact_sha256', 'compiler_sha256',
                   'base_stage_binding_sha256', 'selected_subject', 'aliases', 'compiler', 'frontend',
                   'subject_inventory_sha256', 'witness', 'commands'), 'transport context')
    require(context['schema'] == 'trust.native-targo-transport-context.v1'
            and context['source_commit'] == source['commit'] and context['artifact_sha256'] == artifact['sha256']
            and context['compiler_sha256'] == base['compiler_sha256']
            and context['base_stage_binding_sha256'] == base['stage_binding_sha256'], 'transport subject/context differs')
    subject = Path(absolute(context['selected_subject']))
    require(context['aliases'] == {name: {'observed_path': str(subject / 'bin' / name), 'sha256': artifact['sha256']}
                                   for name in ALIASES}
            and context['compiler'] == {'observed_path': str(subject / 'bin/trustc'),
                                        'source_commit': base['compiler_source'], 'sha256': base['compiler_sha256']}
            and context['frontend'] == {'observed_path': str(subject / 'bin/targo-trust'),
                                        'sha256': base['frontend_artifact_sha256']}, 'transport selected tools differ')
    before = evidence.json(base['inventory'], 'base-inventory.json')
    prospective = parse(canonical(before))
    stage = inventory_stage(before)
    require(subject.name == stage, 'prospective sandbox renamed the SDK hierarchy')
    for row in prospective['entries']:
        if row['path'] in (stage + '/bin/targo', stage + '/bin/cargo'):
            row.update(kind='file', mode=artifact['mode'], bytes=artifact['bytes'], sha256=artifact['sha256'])
    pair_inventory(before, prospective, artifact)
    require(context['subject_inventory_sha256'] == sha256(canonical(prospective)),
            'transport prospective sandbox changed another input')
    witness = context['witness']
    keys(witness, ('project_root', 'source_sha256', 'manifest_sha256'), 'transport witness')
    project = Path(absolute(witness['project_root']))
    require(witness['source_sha256'] == TRANSPORT_SOURCE_SHA256
            and witness['manifest_sha256'] == sha256(transport_manifest(source['root'])), 'mini witness source differs')
    test = [str(subject / 'bin/targo'), '--unverified', 'test', '--config', 'build.test-jobs=1', '--manifest-path',
            str(Path(source['root']) / 'Cargo.toml'), '--locked', '--offline', '-p', 'jobserver_utils', '--lib']
    run = [str(subject / 'bin/targo'), '--unverified', 'run', '--locked', '--offline',
           '--manifest-path', str(project / 'Cargo.toml'), '--bin', 'native-targo-custody-witness', '--']
    expected_commands = [{'name': name, 'argv': [test + ['transport_witness_tests::' + name, '--',
                                                        '--exact', '--nocapture']]}
                         for name in CONTROLS[:2]]
    expected_commands += [{'name': CONTROLS[2], 'argv': [run + ['positive', str(subject / 'bin/trustc')]]},
                          {'name': CONTROLS[3], 'argv': [run + [mode, str(subject / 'bin/trustc')]
                                                       for mode in ('missing', 'malformed')]}]
    require(context['commands'] == expected_commands, 'transport commands differ from exact owning/witness route')
    result = evidence.json(transport['result'], 'transport.result.json')
    keys(result, ('schema', 'source_commit', 'artifact_sha256', 'compiler_sha256', 'context_sha256',
                  'stdout_sha256', 'stderr_sha256', 'controls',
                  'completed', 'retirement'), 'transport result')
    require(result['schema'] == 'trust.native-targo-transport.v1'
            and result['source_commit'] == source['commit'] and result['artifact_sha256'] == artifact['sha256']
            and result['compiler_sha256'] == base['compiler_sha256'] and result['completed'] is True,
            'transport result subject differs')
    retirement(result['retirement'])
    raw = {stream: evidence.read(transport[stream], 'transport.' + stream) for stream in ('stdout', 'stderr')}
    require(result['context_sha256'] == transport['context']['sha256']
            and all(result[stream + '_sha256'] == sha256(raw[stream]) for stream in raw),
            'transport context/raw digest differs')
    frames = {stream: [parse(line) for line in data.splitlines()] for stream, data in raw.items()}
    flattened = [(row['name'], index, argv) for row in expected_commands for index, argv in enumerate(row['argv'])]
    require(all(len(rows) == len(flattened) for rows in frames.values()), 'missing/extra raw transport command')
    for stream in frames:
        for frame, (name, index, argv) in zip(frames[stream], flattened):
            keys(frame, ('name', 'index', 'argv', 'exit', 'raw_base64'), 'raw transport frame')
            require(frame['name'] == name and type(frame['index']) is int and frame['index'] == index
                    and frame['argv'] == argv and type(frame['exit']) is int and 0 <= frame['exit'] < 128
                    and type(frame['raw_base64']) is str, 'raw command frame identity differs')
            try:
                frame['raw'] = base64.b64decode(frame['raw_base64'], validate=True)
            except ValueError as error:
                raise Refusal('raw stream is not base64') from error
    require(type(result['controls']) is list and len(result['controls']) == len(CONTROLS), 'transport controls absent')
    offset = 0
    for number, (row, command) in enumerate(zip(result['controls'], expected_commands)):
        keys(row, ('name', 'exit', 'argv', 'observed'), 'transport control')
        zero(row['exit'])
        require(row['name'] == command['name'] and row['argv'] == command['argv'], 'control argv/name differs')
        outputs = []
        for index in range(offset, offset + len(command['argv'])):
            out, err = frames['stdout'][index], frames['stderr'][index]
            require(out['exit'] == err['exit'], 'stdout/stderr child status differs')
            outputs.append((out['exit'], out['raw'], err['raw']))
        offset += len(command['argv'])
        original = row['observed'].get('original_pipe') if type(row['observed']) is dict else None
        observed = transport_observation(number, outputs, context, original)
        require(canonical(row['observed']) == canonical(observed), 'finite transport observation differs from raw')


def _base(record, evidence):
    base = record['base']
    authority = evidence.json(base['stage_authority'], 'base-stage-authority.json')
    require(authority.get('schema') == 'trust-sdk-wp-component-ready-v1'
            and authority.get('ready') is True and authority.get('status') == 'strict-qualified'
            and authority.get('source') == authority.get('compiler_commit') == base['compiler_source']
            and authority.get('host') == base['host'], 'base stage authority identity differs')
    immutable = dict(authority)
    immutable.pop('gate_only', None)
    require(sha256(canonical(immutable)) == base['stage_binding_sha256'], 'base immutable binding differs')
    frontend = authority.get('frontend_qualified')
    require(type(frontend) is dict and frontend.get('component_sha256') == base['frontend_component_sha256']
            and frontend.get('qualification_sha256') == base['frontend_qualified_sha256']
            and frontend.get('replacement_sha256') == base['frontend_artifact_sha256'],
            'base frontend selection differs')
    tools = authority.get('executables_sha256')
    require(type(tools) is dict and all(base['before_tools'].get(k) == v for k, v in tools.items()),
            'base stage tool map differs')
    before = inventory_shape(evidence.json(base['inventory'], 'base-inventory.json'))
    stage_name = Path(absolute(authority.get('stage_path'))).name
    require(stage_name == inventory_stage(before), 'hierarchy basename differs from bound base-stage authority')
    return before


def _image(record, evidence, payload):
    artifact, base, built = record['artifact'], record['base'], record['build']
    require(sha256(payload) == artifact['sha256'] and len(payload) == artifact['bytes'], 'payload differs')
    libraries, signature = native_image(payload, base['host'])
    require(libraries == artifact['system_libraries'], 'native library closure differs')
    image = evidence.json(built['image'], 'image.json')
    keys(image, ('schema', 'artifact_sha256', 'bytes', 'mode', 'host', 'format', 'cpu_type', 'file_type',
                 'system_libraries', 'code_signature_present', 'codesign'), 'image')
    require(image['schema'] == 'trust.native-targo-image.v1' and image['artifact_sha256'] == artifact['sha256']
            and image['bytes'] == artifact['bytes'] and type(image['bytes']) is int
            and image['mode'] == artifact['mode'] and type(image['mode']) is int
            and image['host'] == base['host'] and image['format'] == 'mach-o64-le'
            and type(image['cpu_type']) is int and image['cpu_type'] == 16777228
            and type(image['file_type']) is int and image['file_type'] == 2
            and image['system_libraries'] == libraries and image['code_signature_present'] is signature,
            'native image report differs from bytes')
    phase(image['codesign'], 'artifact-code-signature', evidence, 'image.codesign')
    context = evidence.json(built['context'], 'build.context.json')
    require(image['codesign']['argv'] == ['/usr/bin/codesign', '--verify', '--strict',
                                         context['original_artifact_path']],
            'signature phase used another image or command')


def prepared(record_path, expected, evidence_directory, artifact_path):
    record, raw = document(record_path, expected)
    record_shape(record)
    evidence = Evidence(evidence_directory)
    evidence.complete(PREPARED_FILES)
    _base(record, evidence)
    _source_relation(record, evidence)
    _build(record, evidence)
    _transport(record, evidence)
    payload = regular(artifact_path, MAX_BINARY)
    require(stat.S_IMODE(Path(artifact_path).lstat().st_mode) == 0o755, 'payload mode differs')
    _image(record, evidence, payload)
    return record, raw, evidence, payload


def _git(root, *args):
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    env.update(GIT_ALLOW_PROTOCOL='file', GIT_NO_REPLACE_OBJECTS='1', GIT_NO_LAZY_FETCH='1')
    return subprocess.check_output(['/usr/bin/git', '-C', str(root), *args], env=env, timeout=60)


def _git_file(root, oid, path):
    return _git(root, 'show', commit(oid) + ':' + relative(path))


def _protected_tree(root, oid):
    excluded = PRODUCTION_PATHS | {TEST_PATH, DOC_PATH}
    rows = []
    for raw in _git(root, 'ls-tree', '-rz', '--full-tree', commit(oid)).split(b'\0'):
        if not raw:
            continue
        metadata, path_raw = raw.split(b'\t', 1)
        mode, kind, hashed = metadata.decode().split()
        path = path_raw.decode('utf-8')
        if path not in excluded:
            rows.append([path, mode, hashed])
    return sha256(canonical(sorted(rows)))


def validate_source(record, source_root, evidence):
    """Preparation-only actual Git closure check. Installed inspection uses copied evidence."""
    root = physical_directory(source_root)
    source = record['source']
    require(str(root) == source['root'] and _git(root, 'rev-parse', 'HEAD').decode().strip() == source['commit'],
            'source root/HEAD differs')
    require(not _git(root, 'status', '--porcelain=v1').strip(), 'source is not committed clean')
    require(_git(root, 'rev-parse', 'HEAD^{tree}').decode().strip() == source['tree'], 'source tree differs')
    context = evidence.json(record['build']['context'], 'build.context.json')
    require(context['version_environment']['CFG_COMMIT_DATE']
            == _git(root, 'show', '-s', '--format=%cs', source['commit']).decode().strip(),
            'version tuple date is not actual source commit date')
    require(context['version_environment']['CFG_TRUST_VERSION']
            == _git_file(root, PORT_BASE, 'src/version').decode().strip(),
            'native product version is not protected source value')
    actual_paths = set(_git(root, 'diff', '--name-only', source['base'], source['commit']).decode().splitlines())
    require(actual_paths == set(source['files']), 'complete cumulative source diff differs')
    for path, value in source['files'].items():
        require(sha256(_git_file(root, source['commit'], path)) == value, 'source file bytes differ')
    changed = set(_git(root, 'diff', '--name-only', PORT_BASE, source['commit']).decode().splitlines())
    require(changed == PRODUCTION_PATHS | {TEST_PATH, DOC_PATH}, 'port changes another tracked path')
    require(_protected_tree(root, PORT_BASE) == _protected_tree(root, source['commit'])
            == source['outside_delta_sha256'], 'outside-delta tracked tree changed')
    relation = evidence.json(source['relation'], 'source-relation.json')
    for path, value in relation['production_delta_before'].items():
        require(sha256(_git_file(root, PORT_BASE, path)) == value, 'port before source differs')
    for path, value in source['locks'].items():
        require(sha256(_git_file(root, PORT_BASE, path)) == sha256(_git_file(root, source['commit'], path)) == value,
                'source lockfile changed')
    recipe = 'src/bootstrap/src/core/build_steps/tool.rs'
    require(sha256(_git_file(root, PORT_BASE, recipe)) == record['build']['recipe']['source_recipe_sha256'],
            'source-owned Targo recipe changed')
    gitlinks = {}
    def collect(repo, prefix, oid):
        for raw in _git(repo, 'ls-tree', '-rz', '--full-tree', oid).split(b'\0'):
            if not raw.startswith(b'160000 '):
                continue
            metadata, name = raw.split(b'\t', 1)
            path = name.decode()
            selected = metadata.decode().split()[2]
            full = prefix + path
            relative(full)
            child = physical_directory(root / full)
            require(Path(_git(child, 'rev-parse', '--show-toplevel').decode().strip()) == child
                    and _git(child, 'rev-parse', 'HEAD').decode().strip() == selected
                    and not _git(child, 'status', '--porcelain=v1').strip(),
                    'unmaterialized/changed source gitlink: ' + full)
            gitlinks[full] = selected
            collect(child, full + '/', selected)
    collect(root, '', source['commit'])
    require(gitlinks == source['gitlinks'], 'tracked gitlink closure differs')


def _base_files(record, root):
    base = record['base']
    require(sha256(regular(root / 'bin/trustc', MAX_BINARY)) == base['compiler_sha256'], 'compiler bytes differ')
    require(sha256(regular(root / 'bin/targo-trust', MAX_BINARY)) == base['frontend_artifact_sha256'],
            'retained frontend bytes differ')
    require(sha256(regular(root / 'FRONTEND-COMPONENT.json')) == base['frontend_component_sha256']
            and sha256(regular(root / 'FRONTEND-QUALIFIED.json')) == base['frontend_qualified_sha256'],
            'retained frontend authority changed')
    frontend, _ = document(root / 'FRONTEND-COMPONENT.json', base['frontend_component_sha256'])
    require(frontend.get('name') == 'targo-trust' and frontend.get('schema') == 'trust.sdk-frontend-component.v2'
            and frontend.get('base', {}).get('compiler_source') == base['compiler_source']
            and frontend.get('base', {}).get('original_mint', {}).get('sha256') == base['mint_sha256'],
            'mint/compiler/frontend selections differ')
    built, _ = document(root / 'FRONTEND-COMPONENT.evidence/build.json',
                        frontend['build_receipt']['sha256'])
    table = built['generated_inputs']['clean_olean_manifest']
    require(table['original']['sha256'] == table['candidate']['sha256'],
            'retained frontend Lean table differs')
    return digest(table['original']['sha256'])


def validate_prepared(record_path, expected, source_root, base_stage, evidence_directory, artifact_path):
    record, raw, evidence, payload = prepared(record_path, expected, evidence_directory, artifact_path)
    validate_source(record, source_root, evidence)
    stage = physical_directory(base_stage)
    require(tool_map(stage) == record['base']['before_tools'], 'base tools changed')
    require(inventory(stage) == _base(record, evidence), 'base/private/Lean/WP inventory changed')
    lean_table = _base_files(record, stage)
    context = evidence.json(record['build']['context'], 'build.context.json')
    require(context['generated_lean_manifest_sha256'] == lean_table, 'retained Lean datum changed')
    require(Path(context['compiler']['observed_sysroot']) == stage
            and Path(context['frontend']['observed_path']) == stage / 'bin/targo', 'build used another SDK')
    artifact = Path(artifact_path)
    target = physical_directory(context['target_directory'])
    require(all(not target.is_relative_to(p) and not p.is_relative_to(target)
                for p in (physical_directory(source_root), stage.parent)),
            'owned build target overlaps source or retained SDK/private hierarchy')
    require(artifact.resolve(strict=True) == artifact and artifact.is_relative_to(target)
            and str(artifact) == context['original_artifact_path'], 'producer artifact not original owned target output')
    for name in ALIASES:
        program = Path(record['build'][name + '_version']['argv'][0])
        require(sha256(regular(program, MAX_BINARY)) == record['artifact']['sha256'],
                'version phase used another image')
    return record, raw, evidence, payload


def _atomic(path, raw, *, replace=False):
    path = Path(path)
    physical_directory(path.parent)
    require(not path.is_symlink(), 'atomic destination linked')
    if not replace:
        require(not os.path.lexists(path), 'atomic destination exists')
    fd, temporary = tempfile.mkstemp(prefix='.native-targo-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        if replace:
            os.replace(temporary, path)
        else:
            os.link(temporary, path)
            os.unlink(temporary)
        directory = os.open(path.parent, os.O_RDONLY | getattr(os, 'O_DIRECTORY', 0))
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.lexists(temporary):
            os.unlink(temporary)


def _json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def install(record_path, expected, source_root, base_stage, evidence_directory, artifact_path, destination):
    """Only a new, exact whole-copy input can be modified. No eligibility is minted."""
    record, raw, evidence, payload = validate_prepared(
        record_path, expected, source_root, base_stage, evidence_directory, artifact_path)
    destination = physical_directory(destination)
    originals = [physical_directory(base_stage).parent, physical_directory(source_root),
                 physical_directory(evidence_directory), Path(artifact_path).parent.resolve(strict=True)]
    require(destination.stat().st_uid == os.geteuid() and destination.stat().st_mode & 0o022 == 0,
            'new copy is not privately owned')
    require(all(not destination.is_relative_to(p) and not p.is_relative_to(destination) for p in originals),
            'new copy overlaps original inputs')
    require(not any(os.path.lexists(destination / p) for p in (RECORD, DETAILS, QUALIFIED)),
            'new component metadata already exists')
    before = tool_map(destination)
    before_inventory = inventory(destination)
    require(before == record['base']['before_tools'] and before_inventory == _base(record, evidence),
            'whole copy differs before replacement')
    _base_files(record, destination)
    details = destination / DETAILS
    details.mkdir(mode=0o700)
    for name in sorted(PREPARED_FILES):
        _atomic(details / name, evidence.literal(name))
    _atomic(destination / RECORD, raw)
    intent = {'schema': INSTALL_SCHEMA, 'component_sha256': expected, 'complete': False}
    _atomic(details / 'installation.json', _json_bytes(intent))
    # Actual original and candidate inputs are checked again before the first replacement.
    validate_prepared(record_path, expected, source_root, base_stage, evidence_directory, artifact_path)
    require(inventory(destination) == before_inventory and tool_map(destination) == before,
            'copy changed before pair replacement')
    for name in ALIASES:
        target = destination / 'bin' / name
        require(stat.S_ISREG(target.lstat().st_mode), 'alias target is not regular')
        _atomic(target, payload, replace=True)
        os.chmod(target, record['artifact']['mode'])
    after = tool_map(destination)
    expected_after = dict(before, **{name: record['artifact']['sha256'] for name in ALIASES})
    require(after == expected_after, 'only canonical pair may change')
    after_inventory = inventory(destination)
    pair_inventory(before_inventory, after_inventory, record['artifact'])
    validate_prepared(record_path, expected, source_root, base_stage, evidence_directory, artifact_path)
    inventory_raw = _json_bytes(after_inventory)
    _atomic(details / 'installed-inventory.json', inventory_raw)
    installed = {'schema': INSTALL_SCHEMA, 'component_sha256': expected,
                 'compiler_source': record['base']['compiler_source'], 'mint_sha256': record['base']['mint_sha256'],
                 'frontend_component_sha256': record['base']['frontend_component_sha256'],
                 'before_tools': before, 'after_tools': after,
                 'before_inventory_sha256': record['base']['inventory']['sha256'],
                 'after_inventory': {'path': 'installed-inventory.json', 'sha256': sha256(inventory_raw)},
                 'complete': True}
    _atomic(details / 'installation.json', _json_bytes(installed), replace=True)
    require(sha256(regular(destination / RECORD)) == expected, 'installed record changed')
    return installed


def _installed(destination, expected):
    destination = physical_directory(destination)
    record, raw = document(destination / RECORD, expected)
    record_shape(record)
    evidence = Evidence(destination / DETAILS)
    before_inventory = _base(record, evidence)
    _source_relation(record, evidence)
    _build(record, evidence)
    _transport(record, evidence)
    payload = regular(destination / 'bin/targo', MAX_BINARY)
    _image(record, evidence, payload)
    for name in ALIASES:
        path = destination / 'bin' / name
        require(stat.S_IMODE(path.lstat().st_mode) == record['artifact']['mode']
                and regular(path, MAX_BINARY) == payload, 'canonical aliases differ')
    lean_table = _base_files(record, destination)
    require(evidence.json(record['build']['context'], 'build.context.json')['generated_lean_manifest_sha256']
            == lean_table, 'installed retained Lean datum changed')
    installed = parse(evidence.literal('installation.json'))
    keys(installed, ('schema', 'component_sha256', 'compiler_source', 'mint_sha256',
                     'frontend_component_sha256', 'before_tools', 'after_tools',
                     'before_inventory_sha256', 'after_inventory', 'complete'), 'installation')
    base = record['base']
    expected_after = dict(base['before_tools'], **{k: record['artifact']['sha256'] for k in ALIASES})
    require(installed['schema'] == INSTALL_SCHEMA and installed['component_sha256'] == expected
            and installed['compiler_source'] == base['compiler_source']
            and installed['mint_sha256'] == base['mint_sha256']
            and installed['frontend_component_sha256'] == base['frontend_component_sha256']
            and installed['before_tools'] == base['before_tools'] and installed['after_tools'] == expected_after
            and installed['before_inventory_sha256'] == base['inventory']['sha256']
            and installed['complete'] is True, 'installation failed/partial/foreign')
    after_inventory = evidence.json(installed['after_inventory'], 'installed-inventory.json')
    pair_inventory(before_inventory, after_inventory, record['artifact'])
    require(inventory(destination) == after_inventory and tool_map(destination) == expected_after,
            'actual installed namespace differs')
    return record, installed, evidence


def _doctor(report, subject):
    require(report.get('ready') is True, 'new native doctor not ready')
    compiler = report.get('compiler')
    require(type(compiler) is dict and compiler.get('trust_verify') is True
            and compiler.get('json_transport') is True, 'doctor lacks actual compiler capability')
    trustc = str(Path(subject) / 'bin/trustc')
    require(compiler.get('path') == compiler.get('linked_toolchain_path') == trustc
            and compiler.get('discovery_source') == 'sibling_trustc'
            and compiler.get('linked_toolchain_status') == 'visible', 'doctor selected another compiler')
    daily = compiler.get('daily_driver')
    require(type(daily) is dict and daily.get('ready') is True
            and daily.get('linked_targo_path') == str(Path(subject) / 'bin/targo')
            and daily.get('linked_targo_trust_path') == str(Path(subject) / 'bin/targo-trust'),
            'doctor selected another native pair/frontend')


def _qualified(record, installed, evidence, value):
    keys(value, ('schema', 'status', 'name', 'component_sha256', 'installation_sha256',
                 'compiler_source', 'compiler_sha256', 'mint_sha256', 'frontend_component_sha256',
                 'frontend_artifact_sha256', 'artifact_sha256', 'doctor', 'targo_version', 'cargo_version',
                 'context', 'result', 'inventory', 'completed'), 'qualified native Targo')
    base, source, artifact = (record[k] for k in ('base', 'source', 'artifact'))
    require(value['schema'] == QUALIFIED_SCHEMA and value['status'] == 'qualified' and value['name'] == 'targo'
            and value['component_sha256'] == installed['component_sha256']
            and value['installation_sha256'] == sha256(evidence.literal('installation.json'))
            and value['completed'] is True and value['artifact_sha256'] == artifact['sha256'],
            'native qualification identity differs')
    for field in ('compiler_source', 'compiler_sha256', 'mint_sha256',
                  'frontend_component_sha256', 'frontend_artifact_sha256'):
        require(value[field] == base[field], 'qualification base differs: ' + field)
    context = evidence.json(value['context'], 'native-qualified.context.json')
    keys(context, ('schema', 'source_commit', 'component_sha256', 'installation_sha256',
                   'selected_subject', 'compiler', 'aliases', 'frontend', 'mint_sha256',
                   'base_stage_binding_sha256', 'commands'), 'qualification context')
    require(context['schema'] == 'trust.native-targo-qualified-context.v1'
            and context['source_commit'] == source['commit']
            and context['component_sha256'] == value['component_sha256']
            and context['installation_sha256'] == value['installation_sha256']
            and context['mint_sha256'] == base['mint_sha256']
            and context['base_stage_binding_sha256'] == base['stage_binding_sha256'],
            'qualification context identity differs')
    subject = Path(absolute(context['selected_subject']))
    require(context['compiler'] == {'observed_path': str(subject / 'bin/trustc'),
                                   'source_commit': base['compiler_source'], 'sha256': base['compiler_sha256']},
            'qualified compiler identity differs')
    require(context['aliases'] == {k: {'observed_path': str(subject / 'bin' / k), 'sha256': artifact['sha256']}
                                   for k in ALIASES}, 'qualified aliases differ')
    require(context['frontend'] == {'observed_path': str(subject / 'bin/targo-trust'),
                                    'component_sha256': base['frontend_component_sha256'],
                                    'artifact_sha256': base['frontend_artifact_sha256']},
            'qualified frontend differs')
    keys(context['commands'], ('doctor', 'targo_version', 'cargo_version'), 'qualified command set')
    expected_commands = {'doctor': [str(subject / 'bin/targo'), 'trust', 'doctor', '--format', 'json'],
                         'targo_version': [str(subject / 'bin/targo'), '--version', '--verbose'],
                         'cargo_version': [str(subject / 'bin/cargo'), '--version', '--verbose']}
    require(context['commands'] == expected_commands, 'qualified commands differ')
    for field, role in (('doctor', 'native-doctor'), ('targo_version', 'native-targo-version'),
                        ('cargo_version', 'native-cargo-version')):
        streams = phase(value[field], role, evidence)
        require(value[field]['argv'] == expected_commands[field], 'qualified phase argv differs')
        if field == 'doctor':
            _doctor(parse(streams['stdout']), subject)
        else:
            build_context = evidence.json(record['build']['context'], 'build.context.json')
            _version(streams['stdout'], source['commit'], field.removesuffix('_version'),
                     build_context['version_environment']['CFG_RELEASE'],
                     build_context['version_environment']['CFG_TRUST_VERSION'])
    result = evidence.json(value['result'], 'native-qualified.result.json')
    keys(result, ('schema', 'source_commit', 'component_sha256', 'artifact_sha256', 'compiler_sha256',
                  'context_sha256', 'installation_sha256', 'inventory_sha256', 'phase_names',
                  'exit', 'completed', 'retirement'), 'qualification result')
    zero(result['exit']); retirement(result['retirement'])
    require(result['schema'] == 'trust.native-targo-qualified-result.v1'
            and result['source_commit'] == source['commit'] and result['completed'] is True
            and result['component_sha256'] == value['component_sha256']
            and result['artifact_sha256'] == artifact['sha256'] and result['compiler_sha256'] == base['compiler_sha256']
            and result['context_sha256'] == value['context']['sha256']
            and result['installation_sha256'] == value['installation_sha256']
            and result['phase_names'] == ['native-doctor', 'native-targo-version', 'native-cargo-version'],
            'qualification actual result differs')
    observed = evidence.json(value['inventory'], 'native-inventory.json')
    require(result['inventory_sha256'] == value['inventory']['sha256']
            and observed == evidence.json(installed['after_inventory'], 'installed-inventory.json'),
            'qualification inventory changed')
    return observed


def qualify(destination, expected, qualification_path, qualification_evidence):
    """Bind actual fixed raw results supplied by the canonical owning operator, not wrapper status."""
    record, installed, evidence = _installed(destination, expected)
    require(not os.path.lexists(Path(destination) / QUALIFIED), 'qualification already exists')
    value, raw = document(qualification_path)
    staged = Evidence(qualification_evidence)
    staged.complete(ALL_FILES - INSTALLED_FILES)
    context = staged.json(value['context'], 'native-qualified.context.json')
    require(context.get('selected_subject') == str(destination),
            'new qualification belongs to another subject')
    for name in sorted(ALL_FILES - INSTALLED_FILES):
        require(not os.path.lexists(evidence.root / name), 'qualification evidence already exists')
        _atomic(evidence.root / name, staged.literal(name))
    evidence = Evidence(evidence.root)
    observed = _qualified(record, installed, evidence, value)
    require(inventory(destination) == observed, 'subject changed during qualification')
    _atomic(Path(destination) / QUALIFIED, raw)
    return {'component_qualified': True, 'whole_stage_ready': False, 'component_sha256': expected}


@dataclass(frozen=True)
class _ValidatedNativeTargoOverlay:
    old_targo: str
    old_cargo: str
    replacement: str
    mint: str
    compiler_source: str
    compiler_sha256: str
    frontend_component: str
    frontend_artifact: str
    destination: str
    inventory_sha256: str
    _seal: object


def _canonical_owner():
    """One private overlay type even when an existing raw-byte loader named this module differently."""
    path = Path(__file__).resolve(strict=True)
    raw = regular(path)
    hashed = sha256(raw)
    old = sys.modules.get(CANONICAL_MODULE)
    if old is not None:
        require(getattr(old, '__source_sha256__', None) == hashed
                and getattr(old, '__file__', None) == str(path), 'native component owner changed')
        return old
    import types
    owner = types.ModuleType(CANONICAL_MODULE)
    owner.__file__ = str(path)
    owner.__source_sha256__ = hashed
    sys.modules[CANONICAL_MODULE] = owner
    try:
        exec(compile(raw, str(path), 'exec'), owner.__dict__)
    except BaseException:
        sys.modules.pop(CANONICAL_MODULE, None)
        raise
    return owner


def inspect_native_targo(destination, expected):
    """Independent full native-component validation; deliberately never calls frontend validator."""
    record, installed, evidence = _installed(destination, expected)
    qualified, _ = document(Path(destination) / QUALIFIED)
    observed = _qualified(record, installed, evidence, qualified)
    require(inventory(destination) == observed, 'qualified actual inventory differs')
    evidence.complete(ALL_FILES)
    base = record['base']
    owner = _canonical_owner()
    return owner._ValidatedNativeTargoOverlay(
        base['original_pair']['targo'], base['original_pair']['cargo'], record['artifact']['sha256'],
        base['mint_sha256'], base['compiler_source'], base['compiler_sha256'],
        base['frontend_component_sha256'], base['frontend_artifact_sha256'],
        str(physical_directory(destination)), sha256(canonical(observed)), owner._SEAL)


def project_verified_tool_map(overlay, destination, actual, historical, *, mint, compiler_source,
                              compiler_sha256, frontend_component, frontend_artifact):
    require(type(overlay) is _ValidatedNativeTargoOverlay and overlay._seal is _SEAL,
            'native tool overlay lacks validated private authority')
    require(str(physical_directory(destination)) == overlay.destination
            and sha256(canonical(inventory(destination))) == overlay.inventory_sha256,
            'native overlay belongs to another or changed installed stage')
    require((overlay.mint, overlay.compiler_source, overlay.compiler_sha256,
             overlay.frontend_component, overlay.frontend_artifact)
            == (mint, compiler_source, compiler_sha256, frontend_component, frontend_artifact),
            'native overlay belongs to another mint/compiler/frontend')
    require(type(actual) is dict and type(historical) is dict
            and historical.get('targo') == overlay.old_targo and historical.get('cargo') == overlay.old_cargo
            and actual.get('targo') == actual.get('cargo') == overlay.replacement,
            'native overlay pair differs from historical/actual namespace')
    projected = dict(actual)
    projected.update(targo=overlay.old_targo, cargo=overlay.old_cargo)
    return projected


def _current_operational_owner():
    """Separate local operational judgement; never a historical SDK overlay."""
    import types
    path = Path(__file__).resolve(strict=True).with_name('sdk_targo_current_component.py')
    raw = regular(path)
    module = types.ModuleType('_trust_current_targo_operational')
    module.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), module.__dict__)
    return module


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] in ('prepare-current', 'qualify-current', 'inspect-current'):
        return _current_operational_owner().main(argv, sys.modules[__name__])
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('validate', 'install', 'qualify', 'inspect'))
    parser.add_argument('--record', type=Path)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--source-root', type=Path)
    parser.add_argument('--base-stage', type=Path)
    parser.add_argument('--evidence', type=Path)
    parser.add_argument('--artifact', type=Path)
    parser.add_argument('--destination', type=Path)
    parser.add_argument('--qualification', type=Path)
    parser.add_argument('--qualification-evidence', type=Path)
    args = parser.parse_args(argv)
    try:
        digest(args.sha256)
        if args.command in ('validate', 'install'):
            require(all(x is not None for x in (args.record, args.source_root, args.base_stage,
                                               args.evidence, args.artifact)), 'preparation input missing')
            if args.command == 'validate':
                record, raw, _, _ = validate_prepared(args.record, args.sha256, args.source_root,
                                                      args.base_stage, args.evidence, args.artifact)
                value = {'prepared_validated': True, 'component_sha256': sha256(raw),
                         'artifact_sha256': record['artifact']['sha256'], 'whole_stage_ready': False}
            else:
                require(args.destination is not None, 'new destination missing')
                value = install(args.record, args.sha256, args.source_root, args.base_stage,
                                args.evidence, args.artifact, args.destination)
        elif args.command == 'qualify':
            require(all(x is not None for x in (args.destination, args.qualification,
                                               args.qualification_evidence)), 'actual qualification input missing')
            value = qualify(args.destination, args.sha256, args.qualification, args.qualification_evidence)
        else:
            require(args.destination is not None, 'installed destination missing')
            overlay = inspect_native_targo(args.destination, args.sha256)
            value = {'component_qualified': True, 'component_sha256': args.sha256,
                     'artifact_sha256': overlay.replacement, 'whole_stage_ready': False}
    except (Refusal, OSError, subprocess.SubprocessError, UnicodeError) as error:
        print('native Targo component refused: ' + str(error), file=sys.stderr)
        return 3
    print(json.dumps(value, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
