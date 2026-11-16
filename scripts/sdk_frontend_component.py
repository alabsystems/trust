#!/usr/bin/env python3
"""Explicit, separately built targo-trust replacement in a new prospective seal.

Prepared input permits installation only. Actual post-install doctor evidence is
required by installed_binding; neither state changes the original mint history.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import struct
import subprocess
import sys
import types
import tempfile

SCHEMA = 'trust.sdk-frontend-component.v2'
QUALIFIED_SCHEMA = 'trust.sdk-frontend-qualified.v2'
INSTALL_SCHEMA = 'trust.sdk-frontend-install.v2'
NAME = 'targo-trust'
RECORD = 'FRONTEND-COMPONENT.json'
DETAILS = 'FRONTEND-COMPONENT.evidence'
QUALIFIED = 'FRONTEND-QUALIFIED.json'
NATIVE_TARGO_MODULE = '_trust_sdk_native_targo_component_v1'
NATIVE_TARGO_SOURCE_SHA256 = '23957eb0eae05d2ba3c4e7183ab4cb6c3f7f27c3139ca0eb5a1e20b828c82038'
WP_NAMES = frozenset(('trust-wp', 'trust-wp-driver', 'trust-wp-rustc', 'targo-trust-wp', 'cargo-trust-wp'))
CONTROL_NAMES = frozenset((
    'test_old_plain_child_refuses_then_real_explicit_pipe_succeeds',
    'test_nested_original_gnu_transport_stays_live',
    'test_sdk_present_unrelated_sentinel_absent_and_parent_flags_unchanged',
    'test_malformed_or_partial_gnu_and_sdk_fail_before_probe',
))
SOURCE_PATHS = frozenset((
    'crates/trust-resource-controller/Cargo.toml',
    'crates/trust-resource-controller/Cargo.lock',
    'crates/trust-resource-controller/examples/probe-scheduler-control.rs',
    'crates/trust-resource-controller/src/client.rs',
    'crates/trust-resource-controller/src/client/sdk.rs',
    'crates/trust-resource-controller/src/client/probe_scheduler.rs',
    'targo-trust/Cargo.toml', 'targo-trust/src/main.rs',
    'targo-trust/src/pipeline/probe.rs', 'targo-trust/src/probe_scheduler.rs', 'targo-trust/src/tool_identity.rs',
    'scripts/tests/doctor_probe_custody_test.py', 'docs/DECISION_QUEUE.md',
    'crates/trust-coordinator/src/coordinator.rs', 'targo-trust/src/pipeline/run.rs',
))
SHARED_SOURCE_PATHS = frozenset(path for path in SOURCE_PATHS if path.startswith('crates/trust-resource-controller/'))
RELATION_PATHS = frozenset(('docs/DECISION_QUEUE.md', 'targo-trust/src/pipeline/probe.rs', 'targo-trust/src/probe_scheduler.rs'))
ORACLE_RELATION_PATHS = RELATION_PATHS | {'targo-trust/src/main.rs', 'targo-trust/src/tool_identity.rs',
    'crates/trust-coordinator/src/coordinator.rs', 'targo-trust/src/pipeline/run.rs'}
FEATURES = ('trust-mc-in-process', 'trust-wp-in-process', 'trust-vc-in-process', 'ay-backend', 'ay-certify')
IDENTITY_CONTROLS = (
    'ordinary_build_keeps_its_same_source_binding',
    'retained_binding_refuses_malformed_or_unbound_metadata',
    'native_oracle_admission_keeps_the_exact_selected_compiler',
    'retained_daemon_binding_keeps_observed_release_and_oracle_commit',
    'retained_daemon_binding_refuses_missing_or_malformed_release',
)
MAX_RECORD = 32 << 20


class Refusal(ValueError):
    pass


def require(value, message):
    if not value:
        raise Refusal(message)


def keys(value, expected, where):
    require(isinstance(value, dict) and set(value) == set(expected), 'closed fields differ: ' + where)


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def digest(value):
    require(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value), 'invalid sha256')
    return value


def commit(value):
    require(isinstance(value, str) and re.fullmatch('[0-9a-f]{40}', value), 'invalid commit')
    return value


def regular(path, maximum=None):
    path = Path(path)
    require(path.is_absolute() and '..' not in path.parts, 'file path must be absolute without traversal')
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), 'file must be regular, not a link: ' + str(path))
    with os.fdopen(os.open(path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0)), 'rb') as stream:
        opened = os.fstat(stream.fileno())
        identity = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        require(identity(opened) == identity(before), 'file replaced before open')
        require(maximum is None or opened.st_size <= maximum, 'file exceeds bound')
        raw = stream.read() if maximum is None else stream.read(maximum + 1)
        require(maximum is None or len(raw) <= maximum, 'file grew beyond bound')
        require(identity(opened) == identity(os.fstat(stream.fileno())) == identity(path.lstat()), 'file changed while read')
    return raw


def unique(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, 'duplicate JSON field: ' + key)
        out[key] = value
    return out


def document(path, expected=None):
    raw = regular(path, MAX_RECORD)
    require(expected is None or sha256(raw) == digest(expected), 'record hash differs: ' + str(path))
    value = json.loads(raw, object_pairs_hook=unique)
    require(isinstance(value, dict), 'record must be object')
    return value, raw


def reference(value):
    keys(value, ('path', 'sha256'), 'reference')
    return document(Path(value['path']), value['sha256'])


def binary(path, expected):
    raw = regular(path, 1 << 30)
    require(sha256(raw) == digest(expected), 'binary hash differs: ' + str(path))
    require(os.access(path, os.X_OK), 'binary not executable')
    return raw


def tool_map(stage):
    root = stage / 'bin'
    require(root.is_dir() and not root.is_symlink(), 'bin must be real directory')
    paths = [path for path in sorted(root.iterdir()) if not (path.is_dir() and not path.is_symlink())]
    helper = stage / 'libexec/trust-analyzer-proc-macro-srv'
    if os.path.lexists(helper):
        paths.append(helper)
    result = {}
    for path in paths:
        require(path.name not in result, 'duplicate tool name across bin/libexec')
        result[path.name] = sha256(regular(path, 1 << 30))
    require(NAME in result and 'trustc' in result, 'base tool map incomplete')
    return result


def phase(value, name):
    keys(value, ('name', 'exit', 'stdout', 'stderr'), 'actual phase')
    require(value['name'] == name and type(value['exit']) is int and value['exit'] == 0, 'actual phase failed or incomplete: ' + name)
    result = {}
    for stream in ('stdout', 'stderr'):
        row = value[stream]
        keys(row, ('path', 'sha256'), 'raw stream')
        raw = regular(Path(row['path']), MAX_RECORD)
        require(sha256(raw) == digest(row['sha256']), 'raw stream hash differs')
        result[stream] = raw
    return result


_GIT_OWNER = None


def raw_git(root, *arguments):
    """Preparation-only raw objects through the canonical provenance owner."""
    global _GIT_OWNER
    if _GIT_OWNER is None:
        path = Path(__file__).resolve().parent / 'recreate_bootstrap.py'
        raw = regular(path, MAX_RECORD)
        owner = types.ModuleType('frontend_raw_git_owner')
        owner.__file__ = str(path)
        sys.modules[owner.__name__] = owner
        try:
            exec(compile(raw, str(path), 'exec'), owner.__dict__)
        except BaseException:
            sys.modules.pop(owner.__name__, None)
            raise
        _GIT_OWNER = owner
    owner = _GIT_OWNER
    owner._reject_local_git_execution_authority(root)
    environment = owner._provenance_git_environment()
    environment.update(GIT_GRAFT_FILE=os.devnull, GIT_NO_LAZY_FETCH='1', GIT_ALLOW_PROTOCOL='')
    result = subprocess.run(owner._controlled_git_command(['--no-replace-objects', '-C', str(root), *arguments]),
                            env=environment, capture_output=True, timeout=30)
    require(result.returncode == 0, 'raw-object Git refused ' + arguments[0])
    return result.stdout


def source_identity(value, base):
    keys(value, ('root', 'commit', 'base', 'tree', 'files'), 'repair source')
    root = Path(value['root'])
    require(root.is_absolute() and root.resolve(strict=True) == root, 'repair root not physical absolute path')
    require(value['base'] == base, 'repair source base differs from compiler source')
    git = lambda *a: raw_git(root, *a)
    require(git('rev-parse', 'HEAD').decode().strip() == commit(value['commit']), 'repair HEAD differs')
    require(not git('status', '--porcelain=v1').strip(), 'repair source not clean')
    git('merge-base', '--is-ancestor', base, value['commit'])
    require(git('rev-parse', 'HEAD^{tree}').decode().strip() == commit(value['tree']), 'repair tree differs')
    files = value['files']
    require(isinstance(files, dict) and files and set(files) <= SOURCE_PATHS, 'repair readset outside narrow frontend owner')
    require(set(git('diff', '--name-only', base, value['commit']).decode().splitlines()) == set(files), 'repair readset incomplete')
    content = {}
    for path, expected in files.items():
        raw = regular(root / path, MAX_RECORD)
        require(sha256(raw) == digest(expected) and raw == git('show', value['commit'] + ':' + path), 'source bytes differ: ' + path)
        content[path] = raw
    return content


def witness_relation(record, controls):
    source = record['source']; witness = controls['witness']
    root = Path(source['root'])
    git = lambda *a: raw_git(root, *a)
    old = commit(controls['source_commit'])
    require(git('rev-parse', old + '^{tree}').decode().strip() == commit(controls['source_tree']), 'witness source tree differs')
    git('merge-base', '--is-ancestor', source['base'], old)
    files = witness['source_files']
    require(isinstance(files, dict) and files and set(files) <= SOURCE_PATHS, 'witness source readset owner differs')
    require(set(git('diff', '--name-only', source['base'], old).decode().splitlines()) == set(files), 'witness source readset incomplete')
    for path, expected in files.items():
        require(sha256(git('show', old + ':' + path)) == digest(expected), 'witness source bytes differ')
    if old == source['commit']:
        require(controls['source_relation'] is None and files == source['files'], 'same-source witness readset differs')
        return None
    relation, raw = reference(controls['source_relation'])
    keys(relation, ('schema', 'witness_source', 'frontend_source', 'base', 'shared_files', 'changed_files', 'reviewed_change_kind', 'reviewer'), 'reviewed source relation')
    require(relation['schema'] == 'trust.sdk-frontend-source-relation.v1' and relation['witness_source'] == old and relation['frontend_source'] == source['commit'] and relation['base'] == source['base'], 'source relation endpoints differ')
    require(relation['reviewed_change_kind'] in ('test-only-and-documentation', 'reviewed-compile-time-oracle-binding') and isinstance(relation['reviewer'], str) and relation['reviewer'], 'source relation lacks explicit source review')
    git('merge-base', '--is-ancestor', old, source['commit'])
    changed = set(git('diff', '--name-only', old, source['commit']).decode().splitlines())
    allowed = ORACLE_RELATION_PATHS if relation['reviewed_change_kind'] == 'reviewed-compile-time-oracle-binding' else RELATION_PATHS
    require(changed and changed <= allowed and set(relation['changed_files']) == changed, 'source relation changes owning production files')
    for path, hashes in relation['changed_files'].items():
        keys(hashes, ('before_sha256', 'after_sha256'), 'reviewed delta')
        if hashes['before_sha256'] is None:
            require(path == 'targo-trust/src/tool_identity.rs' and not git('ls-tree', old, '--', path), 'reviewed missing source differs')
        else:
            require(sha256(git('show', old + ':' + path)) == digest(hashes['before_sha256']), 'source relation before bytes differ')
        require(sha256(git('show', source['commit'] + ':' + path)) == digest(hashes['after_sha256']), 'source relation after bytes differ')
    shared = {}
    for path in SHARED_SOURCE_PATHS:
        before = git('show', old + ':' + path); after = git('show', source['commit'] + ':' + path)
        require(before == after, 'shared witness production changed')
        shared[path] = sha256(before)
    require(relation['shared_files'] == shared, 'shared production readset differs')
    return raw


def native_image(payload, host):
    """Inspect the actual thin executable/load commands, never declared strings.

    Constants/layout are from the installed Apple SDK mach-o/loader.h and
    mach/machine.h. This is native image identity, not execution evidence.
    """
    cpu = {'aarch64-apple-darwin': 0x0100000c, 'x86_64-apple-darwin': 0x01000007}.get(host)
    require(cpu is not None, 'frontend native image target unsupported by this contract')
    require(len(payload) >= 32 and payload[:4] == b'\xcf\xfa\xed\xfe', 'frontend is not thin little-endian Mach-O64')
    _, actual_cpu, _, kind, count, size, _, _ = struct.unpack_from('<8I', payload)
    require(actual_cpu == cpu and kind == 2, 'frontend native architecture/type differs')
    require(0 < count <= 4096 and 8 <= size <= len(payload) - 32, 'frontend load-command bounds invalid')
    offset, end, libraries = 32, 32 + size, []
    for _ in range(count):
        require(offset + 8 <= end, 'frontend load command truncated')
        command, length = struct.unpack_from('<2I', payload, offset)
        require(length >= 8 and length % 8 == 0 and offset + length <= end, 'frontend load-command size invalid')
        command &= 0x7fffffff
        if command in (0xc, 0x18, 0x1f, 0x20, 0x23, 0xe, 0x27):
            require(length >= 12, 'frontend string load command truncated')
            start = struct.unpack_from('<I', payload, offset + 8)[0]
            minimum = 24 if command in (0xc, 0x18, 0x1f, 0x20, 0x23) else 12
            require(minimum <= start < length, 'frontend native string offset invalid')
            data = payload[offset + start:offset + length]
            terminator = data.find(b'\0')
            require(terminator >= 0, 'frontend native string unterminated')
            name = data[:terminator].decode('utf-8')
            require(command != 0x27, 'frontend embeds loader environment')
            if command == 0xe:
                require(name == '/usr/lib/dyld', 'frontend loader is not system dyld')
            else:
                require(name.startswith(('/usr/lib/', '/System/Library/Frameworks/')) and '..' not in Path(name).parts and Path(name).as_posix() == name, 'frontend links non-system native library')
                libraries.append(name)
        offset += length
    require(offset == end and libraries, 'frontend image has invalid load-command census')
    return libraries


def canonical_recipe(record, built):
    argv = built['argv']
    require(argv == [argv[0], '--unverified', 'build', '--release', '--locked', '--offline',
                     '--manifest-path', str(Path(record['source']['root']) / 'targo-trust/Cargo.toml'),
                     '--features', ','.join(FEATURES), '--bin', NAME], 'frontend recipe differs from canonical five-feature build')
    require(Path(argv[0]).is_absolute(), 'frontend build tool must be absolute')


def record_shape(record):
    keys(record, ('schema', 'status', 'name', 'base', 'source', 'build_receipt', 'artifact', 'transport_qualification', 'identity_qualification', 'retained_inputs_unchanged'), 'component')
    require(record['schema'] == SCHEMA and record['status'] == 'prepared' and record['name'] == NAME and record['retained_inputs_unchanged'] is True, 'wrong prepared frontend identity')
    base = record['base']
    keys(base, ('compiler_source', 'host', 'compiler_sha256', 'original_stage', 'original_mint', 'accepted_stage_provenance', 'original_targo_trust_sha256', 'existing_tool_sha256'), 'base')
    commit(base['compiler_source']); digest(base['compiler_sha256']); digest(base['original_targo_trust_sha256'])
    require(isinstance(base['host'], str) and bool(re.fullmatch('[A-Za-z0-9_]+(?:-[A-Za-z0-9_]+)+', base['host'])), 'target host invalid')
    for value in (base['original_mint'], base['accepted_stage_provenance'], record['build_receipt'], record['transport_qualification']):
        keys(value, ('path', 'sha256'), 'component evidence reference'); digest(value['sha256'])
        require(isinstance(value['path'], str) and Path(value['path']).is_absolute() and '..' not in Path(value['path']).parts, 'component reference path invalid')
    files = base['existing_tool_sha256']
    require(isinstance(files, dict) and NAME in files and 'trustc' in files, 'base tool map incomplete')
    for name, value in files.items():
        require(isinstance(name, str) and name not in ('', '.', '..') and Path(name).name == name and '/' not in name and '\\' not in name, 'base tool name invalid')
        digest(value)
    require(files[NAME] == base['original_targo_trust_sha256'] and files['trustc'] == base['compiler_sha256'], 'base tool map identities differ')
    source = record['source']
    keys(source, ('root', 'commit', 'base', 'tree', 'files'), 'repair source')
    commit(source['commit']); commit(source['base']); commit(source['tree'])
    require(source['base'] == base['compiler_source'] and isinstance(source['files'], dict) and source['files'] and set(source['files']) <= SOURCE_PATHS, 'source owner/base differs')
    for value in source['files'].values(): digest(value)
    artifact = record['artifact']
    keys(artifact, ('path', 'sha256', 'bytes', 'system_libraries'), 'replacement artifact')
    digest(artifact['sha256'])
    require(type(artifact['bytes']) is int and 0 < artifact['bytes'] <= 1 << 30, 'artifact size invalid')
    require(isinstance(artifact['path'], str) and Path(artifact['path']).is_absolute(), 'artifact path not absolute')
    libraries = artifact['system_libraries']
    require(isinstance(libraries, list) and libraries and len(libraries) == len(set(libraries)) and all(isinstance(x, str) and x.startswith(('/usr/lib/', '/System/Library/Frameworks/')) and '..' not in Path(x).parts for x in libraries), 'artifact has non-system native libraries')


def receipts_shape(record, built, controls):
    keys(built, ('source_commit', 'compiler', 'target', 'argv', 'environment', 'context', 'compiler_version_phase', 'retained_compiler_version_phase', 'version_phase', 'image_phase', 'generated_inputs', 'target_directory', 'lock_sha256', 'artifact_sha256', 'retained_inputs_unchanged', 'phases'), 'build receipt')
    require(built['source_commit'] == record['source']['commit'] and built['target'] == record['base']['host'] and built['artifact_sha256'] == record['artifact']['sha256'] and built['retained_inputs_unchanged'] is True, 'build identity differs')
    canonical_recipe(record, built)
    keys(built['context'], ('path', 'sha256'), 'build context reference'); digest(built['context']['sha256'])
    compiler_version = built['compiler_version_phase']
    keys(compiler_version, ('name', 'exit', 'argv', 'stdout', 'stderr'), 'build compiler version phase')
    require(compiler_version['name'] == 'build-compiler-version' and type(compiler_version['exit']) is int and compiler_version['exit'] == 0 and compiler_version['argv'] == [built['compiler']['path'], '-vV'], 'build compiler observation not actual bound0')
    retained_version = built['retained_compiler_version_phase']
    keys(retained_version, ('name', 'exit', 'argv', 'stdout', 'stderr'), 'retained compiler version phase')
    require(retained_version['name'] == 'retained-compiler-version' and type(retained_version['exit']) is int and retained_version['exit'] == 0 and retained_version['argv'] == [str(Path(record['base']['original_stage']) / 'bin/trustc'), '-vV'], 'retained compiler observation not actual bound0')
    for stream in ('stdout', 'stderr'):
        keys(retained_version[stream], ('path', 'sha256'), 'retained compiler raw reference')
        digest(retained_version[stream]['sha256'])
    environment = built['environment']
    require(isinstance(environment, dict) and environment.get('CFG_VER_HASH') == record['source']['commit'] and environment.get('CFG_TRUST_ORACLE_HOST') == '1' and environment.get('CFG_TRUST_ORACLE_COMPILER_HASH') == record['base']['compiler_source'] and environment.get('CLEAN_OLEAN_REQUIRE_PINNED_LEAN') == '1' and isinstance(environment.get('ELAN_HOME'), str) and Path(environment['ELAN_HOME']).is_absolute(), 'canonical frontend identity environment missing')
    require(isinstance(environment.get('CFG_RELEASE'), str) and bool(re.fullmatch(r'[0-9]+\.[0-9]+\.[0-9]+(?:-[A-Za-z0-9][A-Za-z0-9.-]*)?', environment['CFG_RELEASE'])), 'canonical retained compiler release missing')
    require(all(isinstance(k, str) and (re.fullmatch('CFG_[A-Z0-9_]+', k) or k in ('CLEAN_OLEAN_REQUIRE_PINNED_LEAN', 'CLEAN_OLEAN_PINNED_LEAN_LIB', 'ELAN_HOME', 'LEAN_CC', 'LZMA_API_STATIC', 'PKG_CONFIG')) and isinstance(v, str) and v for k, v in environment.items()), 'canonical identity environment malformed')
    for name in ('CLEAN_OLEAN_PINNED_LEAN_LIB', 'PKG_CONFIG'):
        require(name not in environment or (Path(environment[name]).is_absolute() and '..' not in Path(environment[name]).parts), 'native build input path invalid')
    require('LZMA_API_STATIC' not in environment or environment['LZMA_API_STATIC'] == '1', 'native static-link policy differs')
    signature = built['image_phase']
    keys(signature, ('name', 'exit', 'argv', 'stdout', 'stderr'), 'native signature phase')
    require(signature['name'] == 'artifact-code-signature' and type(signature['exit']) is int and signature['exit'] == 0 and signature['argv'] == ['/usr/bin/codesign', '--verify', '--strict', record['artifact']['path']], 'native signature inspection not actual bound0')
    version = built['version_phase']
    keys(version, ('name', 'exit', 'stdout', 'stderr'), 'frontend version phase')
    require(version['name'] == 'frontend-version' and type(version['exit']) is int and version['exit'] == 0, 'frontend version not actual0')
    keys(controls, ('source_commit', 'source_tree', 'source_relation', 'witness', 'controls', 'phases'), 'transport qualification')
    commit(controls['source_commit']); commit(controls['source_tree'])
    witness = controls['witness']
    keys(witness, ('path', 'sha256', 'compiler', 'features', 'source_files', 'target', 'argv', 'lock_sha256'), 'transport witness')
    digest(witness['sha256'])
    require(witness['target'] == record['base']['host'] and witness['features'] == ['probe-scheduler'], 'witness feature/target differs')
    for value in (built, witness):
        keys(value['compiler'], ('path', 'sha256', 'source', 'sysroot'), 'actual build compiler')
        digest(value['compiler']['sha256']); commit(value['compiler']['source']); digest(value['lock_sha256'])
        for path in (value['compiler']['path'], value['compiler']['sysroot']):
            require(isinstance(path, str) and Path(path).is_absolute() and '..' not in Path(path).parts, 'actual compiler location invalid')
        require(isinstance(value['argv'], list) and value['argv'] and all(isinstance(x, str) and x for x in value['argv']) and '--locked' in value['argv'] and '--offline' in value['argv'], 'build recipe not locked and offline')
    require(isinstance(controls['controls'], list) and len(controls['controls']) == len(CONTROL_NAMES) and set(controls['controls']) == CONTROL_NAMES, 'required transport controls missing')
    for value, name in ((built, 'frontend-build'), (controls, 'probe-transport-controls')):
        require(isinstance(value['phases'], list) and len(value['phases']) == 1, 'actual phase set differs')
        item = value['phases'][0]
        keys(item, ('name', 'exit', 'stdout', 'stderr'), 'actual phase')
        require(item['name'] == name and type(item['exit']) is int and item['exit'] == 0, 'actual phase failed or incomplete: ' + name)
        for stream in ('stdout', 'stderr'):
            keys(item[stream], ('path', 'sha256'), 'actual raw reference'); digest(item[stream]['sha256'])


def original_mint_root(record, source_root):
    """Bind the line-oriented mint and accepted original producer namespace."""
    base = record['base']
    source_root = Path(source_root)
    require(source_root.is_absolute() and source_root.resolve(strict=True) == source_root, 'original source root not physical')
    receipt, _ = reference(base['accepted_stage_provenance'])
    require(receipt.get('schema') == 'trust.stage-tool-provenance.v2' and receipt.get('status') == 'internal-release-ready' and receipt.get('errors') == [] and receipt.get('path_scope') == 'repository-root-relative', 'original accepted producer receipt invalid')
    stage_relative = Path(receipt.get('stage_root', ''))
    require(not stage_relative.is_absolute() and '..' not in stage_relative.parts and stage_relative.parts[-2:] == (base['host'], 'stage2'), 'accepted original stage producer path invalid')
    stage = source_root / stage_relative
    require(stage.resolve(strict=True) == stage == Path(base['original_stage']), 'accepted original producer stage differs')
    require(receipt.get('host') == base['host'] and receipt.get('compiler', {}).get('source_commit') == base['compiler_source'], 'accepted original producer identity differs')
    mint = Path(base['original_mint']['path'])
    require(mint.name == 'trust-seed-mint' and mint.parent.resolve(strict=True) == mint.parent == stage.parent.parent, 'original mint outside accepted producer root')
    raw = regular(mint, MAX_RECORD)
    require(sha256(raw) == digest(base['original_mint']['sha256']), 'original mint hash differs')
    expected = {'schema': 'trust-seed-mint-v1', 'source_commit': base['compiler_source'], 'host': base['host'], 'ddc_verdict': 'identical', 'self_host_proof': 'pass'}
    wanted = set(expected) | {'stage2_tree_sha256_pinned_seed', 'stage2_tree_sha256_ddc_seed'}
    values = {}; frontend = []
    for line in raw.decode('utf-8').splitlines():
        if not line or line.startswith('#'):
            continue
        name, separator, value = line.partition('=')
        require(bool(separator), 'original mint line malformed')
        if name in wanted:
            require(name not in values, 'original mint identity duplicated')
            values[name] = value
        if name == 'compiler_file' and value.endswith(' bin/' + NAME):
            frontend.append(value)
    require(all(values.get(k) == v for k, v in expected.items()), 'original mint identity differs')
    tree = digest(values.get('stage2_tree_sha256_pinned_seed'))
    require(values.get('stage2_tree_sha256_ddc_seed') == tree, 'original mint DDC trees differ')
    require(frontend == [base['original_targo_trust_sha256'] + ' bin/' + NAME], 'original mint frontend differs')
    return mint.parent


def generated_inputs(record, built, source_root):
    keys(built['generated_inputs'], ('clean_olean_manifest',), 'generated input census')
    target = Path(built['target_directory'])
    require(target.is_absolute() and target.resolve(strict=True) == target, 'actual build target directory not physical')
    original_build = original_mint_root(record, source_root)
    require(not target.is_relative_to(original_build) and not original_build.is_relative_to(target), 'build target overlaps original mint')
    row = built['generated_inputs']['clean_olean_manifest']
    keys(row, ('original', 'candidate', 'original_mint_sha256'), 'generated olean manifest')
    require(row['original_mint_sha256'] == record['base']['original_mint']['sha256'], 'generated baseline mint differs')
    data = []
    for role in ('original', 'candidate'):
        ref = row[role]
        keys(ref, ('path', 'sha256', 'bytes'), 'actual generated input')
        path = Path(ref['path'])
        expected_root = original_build / record['base']['host'] / 'stage2-tools' if role == 'original' else target
        require(path.resolve(strict=True).is_relative_to(expected_root), 'generated input outside its actual producer root')
        raw = regular(path, MAX_RECORD)
        require(type(ref['bytes']) is int and len(raw) == ref['bytes'] and sha256(raw) == digest(ref['sha256']), 'actual generated input differs')
        data.append(raw)
    require(data[0] == data[1], 'embedded generated olean inputs differ from original mint')


def producer_validation(record, built, controls, identity_result):
    """Portable producer attestation; no private source or decision-log content."""
    canonical = lambda value: sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())
    relation = controls['source_relation']
    return {'schema': 'trust.sdk-frontend-producer-validation.v2', 'status': 'prepared-validated',
            'source': record['source']['commit'], 'source_tree': record['source']['tree'],
            'source_readset_sha256': canonical(record['source']['files']),
            'witness_source': controls['source_commit'], 'witness_tree': controls['source_tree'],
            'witness_readset_sha256': canonical(controls['witness']['source_files']),
            'source_relation_sha256': relation['sha256'] if relation is not None else None,
            'build_receipt_sha256': record['build_receipt']['sha256'],
            'build_context_sha256': built['context']['sha256'],
            'identity_witness_sha256': record['identity_qualification']['result']['sha256'],
            'identity_source_review_sha256': record['identity_qualification']['source_review']['sha256'],
            'identity_observed_artifact_sha256': identity_result['subject_artifact']['sha256'],
            'identity_harness_sha256': identity_result['harness']['sha256'],
            'identity_scope': 'Same-source/configuration witness; not execution of replacement bytes or post-install doctor qualification.',
            'transport_receipt_sha256': record['transport_qualification']['sha256'],
            'generated_inputs': built['generated_inputs'],
            'build_lock_sha256': built['lock_sha256'], 'witness_lock_sha256': controls['witness']['lock_sha256'],
            'compiler_source': record['base']['compiler_source'],
            'retained_compiler_release': built['environment']['CFG_RELEASE'],
            'retained_compiler_version_sha256': built['retained_compiler_version_phase']['stdout']['sha256'],
            'compiler_sha256': record['base']['compiler_sha256'],
            'original_frontend_sha256': record['base']['original_targo_trust_sha256'],
            'replacement_sha256': record['artifact']['sha256'],
            'original_mint_sha256': record['base']['original_mint']['sha256'],
            'accepted_stage_provenance_sha256': record['base']['accepted_stage_provenance']['sha256'],
            'scope': 'Producer source/recipe validation attestation, not independently repeated private-source validation or runtime qualification.'}


def identity_witness(record, value, built):
    keys(value, ('exit', 'context', 'phases', 'harness', 'subject_artifact', 'source_unchanged', 'subject_unchanged', 'scope'), 'identity witness result')
    require(type(value['exit']) is int and value['exit'] == 0 and value['source_unchanged'] is True and value['subject_unchanged'] is True, 'identity witness did not finish successfully')
    context, _ = reference(value['context'])
    require(context.get('compiler') == built['compiler'], 'identity witness compiler differs from observed build compiler')
    keys(context, ('schema', 'harness_source', 'subject', 'compiler', 'environment', 'features', 'target'), 'same-source identity context')
    require(context['schema'] == 'trust.frontend-identity-witness.v2', 'identity context schema differs')
    subject = context.get('subject', {})
    require(subject == {'source_commit': record['source']['commit'], 'tree': record['source']['tree'], 'artifact': record['artifact']} and value['subject_artifact'] == record['artifact'], 'identity witness subject differs')
    harness_source = context.get('harness_source', {})
    root = Path(harness_source['root']); old = record['source']['commit']; new = commit(harness_source['commit'])
    keys(harness_source, ('root', 'commit', 'tree', 'files'), 'same-source identity harness')
    require(new == old and harness_source['tree'] == record['source']['tree'] and harness_source['files'] == record['source']['files'], 'identity witness is not the same source/tree/readset')
    require(root.is_absolute() and root.resolve(strict=True) == root, 'identity harness root not physical')
    git = lambda *a: raw_git(root, *a)
    require(git('rev-parse', 'HEAD').decode().strip() == new and not git('status', '--porcelain=v1').strip(), 'identity harness source not frozen')
    require(git('rev-parse', new + '^{tree}').decode().strip() == harness_source['tree'], 'identity harness tree differs')
    git('merge-base', '--is-ancestor', old, new)
    require(not git('diff', '--name-only', old, new).strip(), 'same-source identity witness has a source delta')
    files = harness_source['files']
    require(isinstance(files, dict) and set(files) == set(git('diff', '--name-only', record['base']['compiler_source'], new).decode().splitlines()), 'identity harness readset incomplete')
    for name, expected in files.items():
        require(sha256(git('show', new + ':' + name)) == digest(expected) and sha256(regular(root / name, MAX_RECORD)) == expected, 'identity harness source bytes differ')
    require(context['environment'] == built['environment'] and context['features'] == list(FEATURES) and context['target'] == record['base']['host'], 'identity subject configuration differs')
    harness = value['harness']
    keys(harness, ('path', 'sha256', 'bytes'), 'actual identity harness')
    payload = binary(Path(harness['path']), harness['sha256'])
    require(type(harness['bytes']) is int and len(payload) == harness['bytes'], 'identity harness size differs')
    expected_names = ('oracle-binding-controls', 'frontend-owning-tippy', 'artifact-system-libraries', 'artifact-code-signature')
    phases = value['phases']
    require(isinstance(phases, list) and tuple(row.get('phase') for row in phases) == expected_names, 'identity witness phases incomplete')
    controls_output = None
    for row in phases:
        require(type(row.get('exit')) is int and row['exit'] == 0 and isinstance(row.get('argv'), list) and row['argv'], 'identity witness phase not actual0')
        for stream in ('stdout', 'stderr'):
            ref = row[stream]; keys(ref, ('path', 'sha256'), 'identity raw stream')
            raw = regular(Path(ref['path']), MAX_RECORD)
            require(sha256(raw) == digest(ref['sha256']), 'identity raw stream differs')
            if row['phase'] == 'oracle-binding-controls' and stream == 'stdout':
                controls_output = raw
    artifacts = set()
    for line in controls_output.decode('utf-8').splitlines():
        try:
            item = json.loads(line)
        except ValueError:
            continue
        if isinstance(item, dict) and item.get('reason') == 'compiler-artifact' and item.get('target', {}).get('name') == NAME and item.get('profile', {}).get('test') is True and item.get('executable'):
            artifacts.add(item['executable'])
    require(artifacts == {harness['path']}, 'identity harness not bound to actual Cargo artifact')
    require(all(name.encode() in controls_output for name in IDENTITY_CONTROLS) and b'5 passed; 0 failed' in controls_output, 'identity controls vacuous or incomplete')
    canonical = lambda item: sha256(json.dumps(item, sort_keys=True, separators=(',', ':')).encode())
    return context, {'artifact_source': old, 'artifact_sha256': value['subject_artifact']['sha256'], 'harness_source': new, 'source_tree': harness_source['tree'], 'source_readset_sha256': canonical(files)}


def prepared(record_path, expected, source_root, stage, compiler_source):
    record, raw = document(record_path, expected)
    record_shape(record)
    base = record['base']
    require(base['compiler_source'] == commit(compiler_source), 'target compiler source differs')
    require(Path(base['original_stage']).resolve(strict=True) == stage.resolve(strict=True), 'original stage differs')
    receipt, receipt_raw = reference(base['accepted_stage_provenance'])
    original_mint_root(record, source_root)
    reader = Path(__file__).resolve().parent / 'lib/stage_receipt_provenance.py'
    namespace = {'__name__': 'frontend_original_stage_reader', '__file__': str(reader)}
    exec(compile(reader.read_bytes(), str(reader), 'exec'), namespace)
    namespace['lines'](stage, compiler_source,
        receipt_path=Path(base['accepted_stage_provenance']['path']),
        receipt_sha256=base['accepted_stage_provenance']['sha256'], source_root=source_root)
    require(receipt.get('host') == base['host'], 'accepted target host differs')
    require(sha256(regular(stage / 'bin/trustc')) == base['compiler_sha256'], 'target compiler bytes differ')
    binary(stage / 'bin' / NAME, base['original_targo_trust_sha256'])
    require(tool_map(stage) == base['existing_tool_sha256'], 'original tool map changed')
    source_identity(record['source'], compiler_source)
    artifact = record['artifact']
    payload = binary(Path(artifact['path']), artifact['sha256'])
    require(len(payload) == artifact['bytes'], 'artifact size differs')
    require(native_image(payload, base['host']) == artifact['system_libraries'], 'declared native libraries differ from image')
    built, built_raw = reference(record['build_receipt'])
    controls, controls_raw = reference(record['transport_qualification'])
    identity = record['identity_qualification']
    keys(identity, ('result', 'source_review'), 'identity qualification references')
    identity_result, identity_raw = reference(identity['result'])
    review, _ = reference(identity['source_review'])
    _, reviewed_relation = identity_witness(record, identity_result, built)
    require(review.get('schema') == 'trust.identity-harness-source-review.v2' and review.get('clear') is True and review.get('all_source_lock_feature_inputs_and_gitlinks_identical') is True and all(review.get(key) == value for key, value in reviewed_relation.items()), 'identity source review differs from actual same-source harness relation')
    receipts_shape(record, built, controls)
    generated_inputs(record, built, source_root)
    context, _ = reference(built['context'])
    require(context.get('source_commit') == record['source']['commit'] and context.get('source_tree') == record['source']['tree'] and context.get('files') == record['source']['files'], 'actual build source context differs')
    require(context.get('target_directory') == built['target_directory'], 'actual build target context differs')
    require(context.get('environment') == built['environment'] and context.get('target') == base['host'] and context.get('features') == list(FEATURES), 'actual canonical build context differs')
    require(context.get('compiler', {}).get('path') == built['compiler']['path'] and context.get('compiler', {}).get('sha256') == built['compiler']['sha256'], 'actual build compiler context differs')
    compiler_streams = {}
    for stream in ('stdout', 'stderr'):
        row = built['compiler_version_phase'][stream]
        keys(row, ('path', 'sha256'), 'actual compiler raw reference')
        compiler_streams[stream] = regular(Path(row['path']), MAX_RECORD)
        require(sha256(compiler_streams[stream]) == digest(row['sha256']), 'actual compiler raw differs')
    compiler_version_identity(compiler_streams['stdout'], built['compiler']['source'])
    retained_streams = {}
    for stream in ('stdout', 'stderr'):
        row = built['retained_compiler_version_phase'][stream]
        retained_streams[stream] = regular(Path(row['path']), MAX_RECORD)
        require(sha256(retained_streams[stream]) == digest(row['sha256']), 'retained compiler raw differs')
    require(retained_compiler_identity(retained_streams['stdout'], compiler_source) == built['environment']['CFG_RELEASE'], 'build release differs from retained compiler observation')
    binary(Path(built['compiler']['path']), built['compiler']['sha256'])
    lock_raw = regular(Path(record['source']['root']) / 'Cargo.lock', MAX_RECORD)
    require(sha256(lock_raw) == built['lock_sha256'], 'build source lock differs')
    build_streams = phase(built['phases'][0], 'frontend-build')
    version_streams = phase(built['version_phase'], 'frontend-version')
    signature_streams = {}
    for stream in ('stdout', 'stderr'):
        keys(built['image_phase'][stream], ('path', 'sha256'), 'signature raw reference')
        content = regular(Path(built['image_phase'][stream]['path']), MAX_RECORD)
        require(sha256(content) == digest(built['image_phase'][stream]['sha256']), 'signature raw differs')
        signature_streams[stream] = content
    version_identity(version_streams['stdout'], record['source']['commit'], compiler_source, built['environment']['CFG_RELEASE'])
    witness = controls['witness']
    binary(Path(witness['path']), witness['sha256'])
    binary(Path(witness['compiler']['path']), witness['compiler']['sha256'])
    witness_lock = regular(Path(record['source']['root']) / 'crates/trust-resource-controller/Cargo.lock', MAX_RECORD)
    require(sha256(witness_lock) == witness['lock_sha256'], 'witness lock differs')
    relation_raw = witness_relation(record, controls)
    control_streams = phase(controls['phases'][0], 'probe-transport-controls')
    evidence = {'build.json': built_raw, 'transport.json': controls_raw, 'identity-witness.json': identity_raw}
    if relation_raw is not None:
        evidence['source-relation.json'] = relation_raw
    for label, streams in [('compiler-version', compiler_streams), ('oracle-compiler-version', retained_streams), ('version', version_streams), ('signature', signature_streams), ('transport', control_streams)]:
        for name, content in streams.items():
            evidence[label + '.' + name] = content
    validation = producer_validation(record, built, controls, identity_result)
    return record, raw, payload, evidence, validation


def atomic_new(path, raw, mode=0o644, *, replace=False):
    fd, temporary = tempfile.mkstemp(prefix='.frontend-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(raw); stream.flush(); os.fsync(stream.fileno()); os.fchmod(stream.fileno(), mode)
        if replace:
            os.replace(temporary, path)
        else:
            os.link(temporary, path)
    finally:
        if os.path.lexists(temporary):
            os.unlink(temporary)


def install(record_path, expected, source_root, stage, compiler_source, destination):
    record, raw, payload, evidence, validation = prepared(record_path, expected, source_root, stage, compiler_source)
    require(destination.is_absolute() and destination.is_dir() and not destination.is_symlink() and destination.resolve(strict=True) == destination, 'new destination must be physical directory')
    original = stage.resolve(strict=True)
    require(not destination.is_relative_to(original) and not original.is_relative_to(destination), 'destination overlaps original stage')
    require(not Path(record_path).resolve(strict=True).is_relative_to(destination), 'component input inside destination')
    before = tool_map(destination)
    require(set(before) - set(record['base']['existing_tool_sha256']) <= WP_NAMES | {'dsymutil'}, 'unexpected added destination tools')
    require(sha256(regular(destination / 'tool-provenance.json', MAX_RECORD)) == record['base']['accepted_stage_provenance']['sha256'], 'destination accepted receipt differs')
    require(before[NAME] == record['base']['original_targo_trust_sha256'], 'will not replace a mismatched frontend')
    require(before['trustc'] == record['base']['compiler_sha256'], 'destination compiler differs')
    require(all(before.get(k) == v for k, v in record['base']['existing_tool_sha256'].items()), 'other original tool differs before install')
    require(not any(os.path.lexists(destination / p) for p in (RECORD, DETAILS, QUALIFIED)), 'component evidence already exists')
    target = destination / 'bin' / NAME
    require(not target.is_symlink() and target.parent.resolve(strict=True) == target.parent, 'frontend destination linked')
    original_sha256 = sha256(regular(target, 1 << 30))
    details = destination / DETAILS
    details.mkdir()
    for name, content in evidence.items():
        atomic_new(details / name, content)
    validation_raw = (json.dumps(validation, sort_keys=True, indent=2) + '\n').encode()
    atomic_new(details / 'producer-validation.json', validation_raw)
    expected_after = dict(before, **{NAME: record['artifact']['sha256']})
    installation = {'schema': INSTALL_SCHEMA, 'component_sha256': expected, 'compiler_source': compiler_source, 'before': before, 'after': expected_after, 'source': record['source']['commit'], 'producer_validation_sha256': sha256(validation_raw), 'scope': 'Prepared prospective seal only; no doctor or promotion qualification.'}
    atomic_new(details / 'installation.json', (json.dumps(installation, sort_keys=True, indent=2) + '\n').encode())
    # Recheck both input and copied original immediately before replacement.
    prepared(record_path, expected, source_root, stage, compiler_source)
    require(tool_map(destination) == before and sha256(regular(target)) == original_sha256, 'destination changed before replacement')
    atomic_new(target, payload, 0o755, replace=True)
    atomic_new(destination / RECORD, raw)
    require(tool_map(destination) == expected_after, 'destination tools changed during install')
    require(tool_map(stage) == record['base']['existing_tool_sha256'], 'original stage changed during install')
    return installation


def compiler_version_identity(stdout, source):
    lines = stdout.decode('utf-8').splitlines()
    require('binary: trustc' in lines, 'build compiler is not observed Trust compiler')
    require([line for line in lines if line.startswith('commit-hash: ')] == ['commit-hash: ' + source], 'build compiler source differs from observed binary')


def retained_compiler_identity(stdout, source):
    compiler_version_identity(stdout, source)
    lines = stdout.decode('utf-8').splitlines()
    require([line for line in lines if line.startswith('binary:')] == ['binary: trustc'], 'retained compiler binary identity absent or duplicate')
    require([line for line in lines if line.startswith('commit-hash:')] == ['commit-hash: ' + source], 'retained compiler source absent or duplicate')
    releases = [line for line in lines if line.startswith('release:')]
    require(len(releases) == 1 and releases[0].startswith('release: '), 'retained compiler release absent, duplicate or malformed')
    release = releases[0][len('release: '):]
    require(bool(re.fullmatch(r'[0-9]+\.[0-9]+\.[0-9]+(?:-[A-Za-z0-9][A-Za-z0-9.-]*)?', release)), 'retained compiler release absent, duplicate or malformed')
    return release


def version_identity(stdout, source, oracle_compiler, oracle_release):
    text = stdout.decode('utf-8')
    lines = text.splitlines()
    require(lines and lines[0].startswith('targo-trust '), 'frontend version identity absent')
    hashes = [line for line in lines if line.startswith('trust-repo-commit-hash:')]
    require(hashes == ['trust-repo-commit-hash: ' + source], 'frontend version source unbound or different')
    oracle = [line for line in lines if line.startswith('trust-oracle-compiler-commit-hash:')]
    require(oracle == ['trust-oracle-compiler-commit-hash: ' + oracle_compiler], 'frontend oracle compiler identity differs')
    releases = [line for line in lines if line.startswith('trust-oracle-compiler-release:')]
    require(releases == ['trust-oracle-compiler-release: ' + oracle_release], 'frontend oracle release differs')


def _copied_document(destination, name, expected):
    return document(destination / DETAILS / name, expected)


def inspect_installed(destination, compiler_source, expected):
    return _inspect_installed(destination, compiler_source, expected)


def _inspect_installed(destination, compiler_source, expected, native=None):
    """Validate installed PREPARED bytes, without granting runtime eligibility."""
    require(destination.is_absolute() and destination.resolve(strict=True) == destination and not destination.is_symlink(), 'installed destination not physical')
    record, raw = document(destination / RECORD, expected)
    record_shape(record)
    keys(record, ('schema', 'status', 'name', 'base', 'source', 'build_receipt', 'artifact', 'transport_qualification', 'identity_qualification', 'retained_inputs_unchanged'), 'installed component')
    require(record['schema'] == SCHEMA and record['status'] == 'prepared' and record['name'] == NAME and record['retained_inputs_unchanged'] is True, 'installed prepared identity differs')
    base = record['base']
    require(base['compiler_source'] == commit(compiler_source), 'installed compiler source differs')
    source = record['source']
    require(source['base'] == compiler_source, 'installed repair source base differs')
    commit(source['commit']); commit(source['tree'])
    require(isinstance(source['files'], dict) and source['files'] and set(source['files']) <= SOURCE_PATHS, 'installed source readset differs')
    receipt, _ = document(destination / 'tool-provenance.json', base['accepted_stage_provenance']['sha256'])
    require(receipt.get('compiler', {}).get('source_commit') == compiler_source and receipt.get('host') == base['host'], 'installed original receipt source differs')
    artifact = record['artifact']
    payload = binary(destination / 'bin' / NAME, artifact['sha256'])
    require(type(artifact['bytes']) is int and len(payload) == artifact['bytes'], 'installed frontend length differs')
    require(native_image(payload, base['host']) == artifact['system_libraries'], 'installed native image identity differs')
    require(sha256(regular(destination / 'bin/trustc')) == base['compiler_sha256'], 'installed compiler changed')
    built, _ = _copied_document(destination, 'build.json', record['build_receipt']['sha256'])
    controls, _ = _copied_document(destination, 'transport.json', record['transport_qualification']['sha256'])
    receipts_shape(record, built, controls)
    identity_result, _ = _copied_document(destination, 'identity-witness.json', record['identity_qualification']['result']['sha256'])
    require(type(identity_result.get('exit')) is int and identity_result['exit'] == 0 and identity_result.get('source_unchanged') is True and identity_result.get('subject_unchanged') is True and identity_result.get('subject_artifact') == artifact, 'attested identity witness not successful for this same-source subject')
    require(built['source_commit'] == source['commit'], 'copied build source differs')
    if controls['source_commit'] == source['commit']:
        require(controls['source_relation'] is None and controls['witness']['source_files'] == source['files'], 'copied same-source witness differs')
    else:
        relation, _ = _copied_document(destination, 'source-relation.json', controls['source_relation']['sha256'])
        require(relation['witness_source'] == controls['source_commit'] and relation['frontend_source'] == source['commit'] and relation['base'] == source['base'] and relation['reviewed_change_kind'] in ('test-only-and-documentation', 'reviewed-compile-time-oracle-binding'), 'copied source relation differs')
        require(set(relation['shared_files']) == SHARED_SOURCE_PATHS, 'attested shared witness readset differs')
    require(built['target'] == base['host'] and built['artifact_sha256'] == artifact['sha256'] and built['retained_inputs_unchanged'] is True, 'copied build identity differs')
    require(set(controls['controls']) == CONTROL_NAMES and len(controls['controls']) == len(CONTROL_NAMES), 'copied witness source/control set differs')
    for label, value, phase_name in [('transport', controls, 'probe-transport-controls')]:
        require(isinstance(value['phases'], list) and len(value['phases']) == 1, 'copied phase set differs')
        actual = value['phases'][0]
        keys(actual, ('name', 'exit', 'stdout', 'stderr'), 'copied phase')
        require(actual['name'] == phase_name and type(actual['exit']) is int and actual['exit'] == 0, 'copied phase not actual0')
        for stream in ('stdout', 'stderr'):
            regular_ref = actual[stream]
            keys(regular_ref, ('path', 'sha256'), 'copied raw reference')
            require(sha256(regular(destination / DETAILS / (label + '.' + stream), MAX_RECORD)) == digest(regular_ref['sha256']), 'copied raw stream differs')
    for stream in ('stdout', 'stderr'):
        row = built['compiler_version_phase'][stream]
        keys(row, ('path', 'sha256'), 'build compiler raw reference')
        require(sha256(regular(destination / DETAILS / ('compiler-version.' + stream), MAX_RECORD)) == digest(row['sha256']), 'copied build compiler observation differs')
    compiler_version_identity(regular(destination / DETAILS / 'compiler-version.stdout', MAX_RECORD), built['compiler']['source'])
    for stream in ('stdout', 'stderr'):
        row = built['retained_compiler_version_phase'][stream]
        require(sha256(regular(destination / DETAILS / ('oracle-compiler-version.' + stream), MAX_RECORD)) == digest(row['sha256']), 'copied retained compiler observation differs')
    require(retained_compiler_identity(regular(destination / DETAILS / 'oracle-compiler-version.stdout', MAX_RECORD), compiler_source) == built['environment']['CFG_RELEASE'], 'copied retained compiler release differs')
    for stream in ('stdout', 'stderr'):
        raw_ref = built['image_phase'][stream]
        keys(raw_ref, ('path', 'sha256'), 'signature raw reference')
        require(sha256(regular(destination / DETAILS / ('signature.' + stream), MAX_RECORD)) == digest(raw_ref['sha256']), 'copied signature inspection differs')
    version = built['version_phase']
    for stream in ('stdout', 'stderr'):
        keys(version[stream], ('path', 'sha256'), 'frontend version raw reference')
        require(sha256(regular(destination / DETAILS / ('version.' + stream), MAX_RECORD)) == digest(version[stream]['sha256']), 'copied version stream differs')
    version_identity(regular(destination / DETAILS / 'version.stdout', MAX_RECORD), source['commit'], compiler_source, built['environment']['CFG_RELEASE'])
    installation, _ = document(destination / DETAILS / 'installation.json')
    keys(installation, ('schema', 'component_sha256', 'compiler_source', 'before', 'after', 'source', 'producer_validation_sha256', 'scope'), 'installation')
    require(installation['schema'] == INSTALL_SCHEMA and installation['component_sha256'] == expected and installation['compiler_source'] == compiler_source and installation['source'] == source['commit'], 'installation binding differs')
    validation, _ = document(destination / DETAILS / 'producer-validation.json', installation['producer_validation_sha256'])
    require(validation == producer_validation(record, built, controls, identity_result), 'producer validation attestation differs')
    before, after = installation['before'], installation['after']
    require(isinstance(before, dict) and isinstance(after, dict) and set(before) == set(after), 'installation tool set differs')
    require(before.get(NAME) == base['original_targo_trust_sha256'] and after == dict(before, **{NAME: artifact['sha256']}), 'installation changed another tool')
    require(all(before.get(k) == v for k, v in base['existing_tool_sha256'].items()), 'installation original tool map differs')
    actual = tool_map(destination)
    if native is not None:
        owner, overlay = native
        try:
            actual = owner.project_verified_tool_map(
                overlay, destination, actual, after,
                mint=base['original_mint']['sha256'], compiler_source=compiler_source,
                compiler_sha256=base['compiler_sha256'], frontend_component=expected,
                frontend_artifact=artifact['sha256'])
        except owner.Refusal as error:
            raise Refusal(str(error)) from error
    require(all(actual.get(k) == v for k, v in after.items()) and set(actual) - set(after) <= WP_NAMES, 'installed tools changed or unexpected tool added')
    for value in (*before.values(), *after.values()):
        digest(value)
    return record, installation


def doctor_observation(report, subject):
    require(report.get('ready') is True, 'doctor is not typed ready:true')
    compiler = report.get('compiler')
    require(isinstance(compiler, dict), 'doctor compiler absent')
    require(compiler.get('trust_verify') is True and compiler.get('json_transport') is True, 'doctor verification/json capability not true')
    expected = str(subject / 'bin/trustc')
    require(compiler.get('path') == expected and compiler.get('linked_toolchain_path') == expected and compiler.get('discovery_source') == 'sibling_trustc' and compiler.get('linked_toolchain_status') == 'visible', 'doctor selected a different compiler')
    daily = compiler.get('daily_driver')
    require(isinstance(daily, dict) and daily.get('ready') is True and daily.get('linked_targo_path') == str(subject / 'bin/targo') and daily.get('linked_targo_trust_path') == str(subject / 'bin' / NAME), 'doctor selected a different SDK frontend')


def qualify(destination, compiler_source, expected, actual_exit, stdout_path, stderr_path, context_path):
    """Record only an actual successful doctor of the already installed subject.

    The canonical promoter owns capture and supplies the actual wait result.
    This never dispatches a process or upgrades prepared input by prediction.
    """
    record, installation = inspect_installed(destination, compiler_source, expected)
    require(type(actual_exit) is int and actual_exit == 0, 'doctor did not actually exit0')
    require(destination.resolve(strict=True) == destination, 'doctor subject not physical')
    for path in (stdout_path, stderr_path, context_path):
        require(path.resolve(strict=True).is_relative_to(destination / DETAILS), 'doctor evidence outside new seal')
    context, context_raw = document(context_path)
    keys(context, ('actual_exit', 'argv', 'cargo_home', 'cache_preparation', 'initially_empty'), 'doctor context')
    require(type(context['actual_exit']) is int and context['actual_exit'] == actual_exit and context['argv'] == [str(destination / 'bin/targo'), 'trust', 'doctor', '--format', 'json'], 'doctor command/context differs')
    require(context['initially_empty'] is True and Path(context['cargo_home']).is_absolute(), 'doctor cache preparation context absent')
    stdout = regular(stdout_path, MAX_RECORD); stderr = regular(stderr_path, MAX_RECORD)
    report = json.loads(stdout, object_pairs_hook=unique)
    require(isinstance(report, dict), 'doctor report is not object')
    doctor_observation(report, destination)
    require(not os.path.lexists(destination / QUALIFIED), 'frontend qualification already exists')
    for name in ('doctor.stdout', 'doctor.stderr', 'doctor.context.json'):
        require(not os.path.lexists(destination / DETAILS / name), 'doctor evidence already exists')
    atomic_new(destination / DETAILS / 'doctor.stdout', stdout)
    atomic_new(destination / DETAILS / 'doctor.stderr', stderr)
    atomic_new(destination / DETAILS / 'doctor.context.json', context_raw)
    reference_at = lambda name, raw: {'path': str(destination / DETAILS / name), 'sha256': sha256(raw)}
    value = {'schema': QUALIFIED_SCHEMA, 'status': 'qualified', 'component_sha256': expected,
             'source': record['source']['commit'], 'compiler_source': compiler_source,
             'host': record['base']['host'], 'subject': str(destination),
             'tool_sha256': installation['after'],
             'doctor_phase': {'name': 'doctor-report', 'exit': actual_exit,
                              'stdout': reference_at('doctor.stdout', stdout), 'stderr': reference_at('doctor.stderr', stderr),
                              'context': reference_at('doctor.context.json', context_raw)},
             'scope': 'Actual post-install full frontend doctor only; remaining promotion/WP/consumer gates have separate results.'}
    inspect_installed(destination, compiler_source, expected)
    atomic_new(destination / QUALIFIED, (json.dumps(value, indent=2) + '\n').encode())
    return value


def installed_binding(destination, compiler_source, expected):
    return _installed_binding(destination, compiler_source, expected)


def _installed_binding(destination, compiler_source, expected, native=None):
    """Require explicit component authority AND actual post-install qualification."""
    record, installation = _inspect_installed(destination, compiler_source, expected, native)
    value, qualified_raw = document(destination / QUALIFIED)
    keys(value, ('schema', 'status', 'component_sha256', 'source', 'compiler_source', 'host', 'subject', 'tool_sha256', 'doctor_phase', 'scope'), 'qualified frontend')
    require(value['schema'] == QUALIFIED_SCHEMA and value['status'] == 'qualified' and value['component_sha256'] == expected, 'frontend not qualified')
    require(value['source'] == record['source']['commit'] and value['compiler_source'] == compiler_source and value['host'] == record['base']['host'] and value['tool_sha256'] == installation['after'], 'qualified subject identity differs')
    subject = Path(value['subject'])
    require(subject.is_absolute() and '..' not in subject.parts, 'qualified subject is not absolute')
    actual = value['doctor_phase']
    keys(actual, ('name', 'exit', 'stdout', 'stderr', 'context'), 'doctor phase')
    require(actual['name'] == 'doctor-report' and type(actual['exit']) is int and actual['exit'] == 0, 'doctor phase not actual0')
    raw = {}
    for stream in ('stdout', 'stderr'):
        keys(actual[stream], ('path', 'sha256'), 'doctor raw reference')
        require(actual[stream]['path'] == str(subject / DETAILS / ('doctor.' + stream)), 'doctor raw subject differs')
        raw[stream] = regular(destination / DETAILS / ('doctor.' + stream), MAX_RECORD)
        require(sha256(raw[stream]) == digest(actual[stream]['sha256']), 'doctor raw hash differs')
    keys(actual['context'], ('path', 'sha256'), 'doctor context reference')
    require(actual['context']['path'] == str(subject / DETAILS / 'doctor.context.json'), 'doctor context subject differs')
    context, _ = document(destination / DETAILS / 'doctor.context.json', actual['context']['sha256'])
    keys(context, ('actual_exit', 'argv', 'cargo_home', 'cache_preparation', 'initially_empty'), 'doctor context')
    require(type(context['actual_exit']) is int and context['actual_exit'] == 0 and context['argv'] == [str(subject / 'bin/targo'), 'trust', 'doctor', '--format', 'json'] and context['initially_empty'] is True, 'doctor execution context differs')
    report = json.loads(raw['stdout'], object_pairs_hook=unique)
    require(isinstance(report, dict), 'doctor report is not object')
    doctor_observation(report, subject)
    return {'name': NAME, 'original_sha256': record['base']['original_targo_trust_sha256'],
            'replacement_sha256': record['artifact']['sha256'], 'source': record['source']['commit'],
            'component_sha256': expected, 'qualification_sha256': sha256(qualified_raw)}


def _native_targo_owner():
    """Load the one reviewed sibling implementation; callers cannot supply an overlay map."""
    path = Path(__file__).resolve(strict=True).with_name('sdk_targo_component.py')
    raw = regular(path, MAX_RECORD)
    require(sha256(raw) == NATIVE_TARGO_SOURCE_SHA256, 'native Targo validator source differs')
    existing = sys.modules.get(NATIVE_TARGO_MODULE)
    if existing is not None:
        require(getattr(existing, '__source_sha256__', None) == NATIVE_TARGO_SOURCE_SHA256
                and getattr(existing, '__file__', None) == str(path), 'native validator module differs')
        return existing
    owner = types.ModuleType(NATIVE_TARGO_MODULE)
    owner.__file__ = str(path)
    owner.__source_sha256__ = NATIVE_TARGO_SOURCE_SHA256
    sys.modules[NATIVE_TARGO_MODULE] = owner
    try:
        exec(compile(raw, str(path), 'exec'), owner.__dict__)
    except BaseException:
        sys.modules.pop(NATIVE_TARGO_MODULE, None)
        raise
    return owner


def installed_binding_with_native_targo(destination, compiler_source, expected, native_expected):
    """Require independent native qualification, then the unchanged full frontend history.

    This grants only the validated targo/cargo projection during historical tool-map
    comparison. Fresh combined-stage promotion/doctor/readiness remains separate.
    """
    owner = _native_targo_owner()
    try:
        overlay = owner.inspect_native_targo(destination, native_expected)
    except owner.Refusal as error:
        raise Refusal(str(error)) from error
    return _installed_binding(destination, compiler_source, expected, (owner, overlay))


def main(argv=None):
    class Once(argparse.Action):
        def __call__(self, parser, namespace, value, option_string=None):
            if getattr(namespace, self.dest, None) is not None:
                parser.error('duplicate ' + option_string)
            setattr(namespace, self.dest, value)

    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('command', choices=('validate', 'install', 'qualify', 'inspect'))
    p.add_argument('--record', action=Once, type=Path, required=True)
    p.add_argument('--sha256', action=Once, required=True)
    p.add_argument('--compiler-source', action=Once, required=True)
    p.add_argument('--source-root', action=Once, type=Path)
    p.add_argument('--stage', action=Once, type=Path)
    p.add_argument('--destination', action=Once, type=Path)
    p.add_argument('--actual-exit', action=Once, type=int)
    p.add_argument('--stdout', action=Once, type=Path)
    p.add_argument('--stderr', action=Once, type=Path)
    p.add_argument('--context', action=Once, type=Path)
    a = p.parse_args(argv)
    try:
        if a.command in ('validate', 'install'):
            require(a.source_root is not None and a.stage is not None, 'original source and stage required')
            require(a.actual_exit is None and a.stdout is None and a.stderr is None and a.context is None, 'prepared mode does not use runtime fields')
            if a.command == 'validate':
                require(a.destination is None, 'validate never installs')
                prepared(a.record, a.sha256, a.source_root, a.stage, a.compiler_source)
            else:
                require(a.destination is not None, 'install needs new destination')
                install(a.record, a.sha256, a.source_root, a.stage, a.compiler_source, a.destination)
        else:
            require(a.destination is not None and a.record == a.destination / RECORD, 'installed record must belong to destination')
            require(a.source_root is None and a.stage is None, 'installed mode does not reinterpret original source')
            if a.command == 'qualify':
                require(a.actual_exit is not None and a.stdout is not None and a.stderr is not None and a.context is not None, 'qualify needs actual runtime fields')
                qualify(a.destination, a.compiler_source, a.sha256, a.actual_exit, a.stdout, a.stderr, a.context)
            else:
                require(a.actual_exit is None and a.stdout is None and a.stderr is None and a.context is None, 'inspect does not use runtime fields')
                installed_binding(a.destination, a.compiler_source, a.sha256)
        print(json.dumps({'command': a.command, 'name': NAME, 'passed': True,
                          'scope': 'Prepared identity only' if a.command in ('validate', 'install') else 'Actual qualified frontend identity'}))
        return 0
    except (Refusal, OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print('frontend component refused: ' + str(error), file=__import__('sys').stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
