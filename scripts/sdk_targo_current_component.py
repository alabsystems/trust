#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Current-source native Targo with a retained operational SDK, never SDK authority.

The build compiler and operational compiler are different declared roles. This
contract cannot produce the historical native overlay or a verified tool map.
"""
from __future__ import annotations

import argparse
import importlib.util
import re
import types
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

SCHEMA = 'trust.local-targo-operational.v1'
RECORD = 'TARGO-OPERATIONAL.json'
EVIDENCE = 'TARGO-OPERATIONAL.evidence'
OPERATIONAL_SOURCE = '29ebb403de7a102850d6cb10a62d5cc3baf723ed'
OPERATIONAL_COMPILER = '0acc4862fe98d55f71585dd2e651ad166ce789f049d77b78dfe3d11112889c34'
HOST = 'aarch64-apple-darwin'
ALIASES = ('targo', 'cargo')
FILENAME_INVENTORY_CAPABILITY = 'freshness: compiler-filename-inventory-v1'
MAX_FILES = 100_000
MAX_BYTES = 1 << 30


def require(value, message):
    if not value:
        raise ValueError(message)



def require_filename_inventory_capability(raw):
    lines = raw.decode('utf-8').splitlines()
    require(lines.count(FILENAME_INVENTORY_CAPABILITY) == 1,
            'native filename-inventory capability is missing or ambiguous')
    versions = [line.removeprefix('encoded-dep-info-version: ') for line in lines
                if line.startswith('encoded-dep-info-version: ')]
    require(len(versions) == 1 and versions[0].isdigit() and 7 <= int(versions[0]) <= 255,
            'native filename-inventory cache format is unavailable')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode() + b'\n'


def physical(path):
    path = Path(path)
    require(path.is_absolute() and path.resolve(strict=True) == path and path.is_dir(),
            'directory must be physical and absolute')
    return path


def regular(path):
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_size <= MAX_BYTES, 'not a bounded regular file')
    with os.fdopen(os.open(path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0)), 'rb') as stream:
        opened = os.fstat(stream.fileno())
        identity = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        require(identity(before) == identity(opened), 'file changed before open')
        raw = stream.read(MAX_BYTES + 1)
        require(len(raw) <= MAX_BYTES and identity(opened) == identity(os.fstat(stream.fileno()))
                == identity(path.lstat()), 'file changed while read')
    return raw


def inventory(root):
    root = physical(root)
    rows = []
    def visit(directory):
        for path in sorted(directory.iterdir()):
            relative = path.relative_to(root).as_posix()
            if relative in (RECORD, EVIDENCE):
                continue
            value = path.lstat()
            row = {'path': relative, 'mode': stat.S_IMODE(value.st_mode)}
            if stat.S_ISLNK(value.st_mode):
                row.update(kind='symlink', target=os.readlink(path))
            elif stat.S_ISDIR(value.st_mode):
                row['kind'] = 'directory'
                rows.append(row)
                require(len(rows) <= MAX_FILES, 'inventory exceeds bound')
                visit(path)
                continue
            else:
                raw = regular(path)
                row.update(kind='file', bytes=len(raw), sha256=sha(raw))
            rows.append(row)
            require(len(rows) <= MAX_FILES, 'inventory exceeds bound')
    visit(root)
    return sorted(rows, key=lambda row: row['path'])


def git(root, *args):
    return subprocess.check_output(['/usr/bin/git', '-C', str(root), *args])


def source_identity(root):
    root = physical(root)
    require(not git(root, 'status', '--porcelain=v1').strip(), 'build source must be committed clean')
    return {'root': str(root), 'commit': git(root, 'rev-parse', 'HEAD').decode().strip(),
            'tree': git(root, 'rev-parse', 'HEAD^{tree}').decode().strip(),
            'recipe_sha256': sha(regular(root / 'src/bootstrap/src/core/build_steps/tool.rs')),
            'lock_sha256': sha(regular(root / 'src/tools/targo/Cargo.lock')),
            'config_sha256': sha(regular(root / 'bootstrap.toml'))}


def execute(argv, directory, environment, evidence, name):
    require(name.replace('-', '').isalnum(), 'phase name differs')
    # Reuse the maintained cooperative group forwarding/wait implementation.
    witness_path = Path(__file__).resolve().with_name('sdk_targo_transport_witness.py')
    witness = types.ModuleType('current_targo_wait_owner')
    witness.__file__ = str(witness_path)
    exec(compile(regular(witness_path), str(witness_path), 'exec'), witness.__dict__)
    flags = environment.get('CARGO_MAKEFLAGS', '')
    pairs = re.findall(r'(?:^|\s)--jobserver-(?:auth|fds)=([0-9]+),([0-9]+)(?=\s|$)', flags)
    require(not any('--jobserver-'+kind+'=' in flags for kind in ('auth','fds')) or bool(pairs),
            'unsupported inherited scheduler advertisement')
    require(not pairs or len(set(pairs)) == 1, 'inherited jobserver advertisements differ')
    descriptors = tuple(map(int, pairs[0])) if pairs else ()
    require(not descriptors or descriptors[0] != descriptors[1], 'scheduler descriptor roles alias')
    require(all(stat.S_ISFIFO(os.fstat(fd).st_mode) for fd in descriptors),
            'inherited scheduler descriptor is not a live pipe')
    class WaitAPI:
        @staticmethod
        def require(value, message):
            require(value, message)
    # observe_child forwards signals and waits for the exact group; no KILL or
    # successful retirement is fabricated after interruption.
    code, stdout, stderr, pending = witness.observe_child(WaitAPI, list(map(str, argv)),
                                                         environment, descriptors, cwd=directory)
    witness.require_normal_retirement(code, pending)
    streams = {}
    for suffix, raw in [('stdout', stdout), ('stderr', stderr)]:
        path = evidence / (name + '.' + suffix)
        require(not path.exists(), 'phase evidence already exists; use a new case namespace')
        path.write_bytes(raw)
        streams[suffix] = {'path': path.name, 'sha256': sha(raw)}
    row = {'argv': list(map(str, argv)), 'cwd': str(directory), 'exit': code,
           'stdout': streams['stdout'], 'stderr': streams['stderr'],
           'retired': True}
    require(row['retired'], 'signalled child gives no retired qualification')
    return row


def prepare(args, helper):
    source = physical(args.source_root)
    base = physical(args.base_sdk)
    require(sha(regular(base / 'bin/trustc')) == OPERATIONAL_COMPILER, 'operational compiler differs')
    before = inventory(base)
    source_before = source_identity(source)
    owner_root = Path(__file__).resolve().parents[1]
    require(owner_root == source, 'canonical collector must belong to its frozen source tree')
    producer_before = {'root': str(owner_root), 'commit': git(owner_root,'rev-parse','HEAD').decode().strip(),
                       'module_sha256':sha(regular(Path(__file__).resolve())),
                       'helper_sha256':sha(regular(Path(helper.__file__).resolve()))}
    destination = Path(args.destination)
    require(destination.is_absolute() and not destination.exists(), 'destination must be new and absolute')
    parent = physical(destination.parent)
    require(parent.stat().st_uid == os.getuid() and not parent.stat().st_mode & 0o022,
            'destination parent must be privately owned')
    require(not destination.is_relative_to(source) and not destination.is_relative_to(base),
            'new SDK overlaps inputs')
    evidence = Path(args.evidence)
    require(evidence.is_absolute() and not evidence.exists(), 'evidence directory must be new')
    evidence.mkdir(mode=0o700)
    jobs = os.environ.get('CARGO_BUILD_JOBS')
    require(jobs is not None and jobs.isdigit() and 0 < int(jobs) <= 256,
            'canonical build requires existing admitted CARGO_BUILD_JOBS')
    env = os.environ.copy()
    manager = Path(args.manager)
    require(manager.is_absolute() and manager.resolve(strict=True) == manager,
            'coordination helper must be a physical executable')
    manager_hash = sha(regular(manager))
    manager_probe = execute([str(manager),'trust','repo','lock','--protocol'], source, env,
                            evidence, 'manager-protocol')
    require(manager_probe['exit'] == 0 and regular(evidence/'manager-protocol.stdout')
            == b'trust-build-tree-manager-v2\n', 'coordination helper does not implement actual manager v2')
    env['TRUST_BUILD_TREE_MANAGER_TARGO'] = str(manager)
    command = [sys.executable, '-B', str(source / 'x.py'), 'build', '--stage', '1', '-j', jobs,
               'targo-build-tool']
    built = execute(command, source, env, evidence, 'canonical-build')
    require(built['exit'] == 0, 'canonical targo-build-tool failed; retained actual logs')
    require(sha(regular(manager)) == manager_hash, 'coordination helper changed during canonical build')
    built['manager'] = {'path':str(manager),'sha256':manager_hash,'protocol':manager_probe,
                        'role':'build-tree-coordination-only'}
    require(source_identity(source) == source_before, 'source/config changed during build')
    require(sha(regular(Path(__file__).resolve())) == producer_before['module_sha256']
            and sha(regular(Path(helper.__file__).resolve())) == producer_before['helper_sha256'],
            'collector changed during canonical execution')
    # The canonical recipe, not a caller's arbitrary binary, names its artifact.
    text = regular(evidence / 'canonical-build.stdout').decode(errors='strict')
    text += regular(evidence / 'canonical-build.stderr').decode(errors='strict')
    lines = [line for line in text.splitlines() if 'Engineering build-tool artifact: ' in line]
    require(len(lines) == 1, 'one canonical build-tool artifact observation required')
    value = lines[0].split('Engineering build-tool artifact: ', 1)[1]
    artifact = Path(value.split(' (cargo: ', 1)[0])
    require(artifact.is_absolute() and artifact.is_relative_to(source / 'build'),
            'canonical artifact is outside source build output')
    payload = regular(artifact)
    libraries, signed = helper.native_image(payload, HOST)
    require(signed, 'canonical native image lacks its development code signature')
    frontend_version = execute([str(artifact),'--version','--verbose'],source,env,evidence,'frontend-version')
    require(frontend_version['exit']==0,'canonical frontend capability observation failed')
    frontend_stdout=regular(evidence/'frontend-version.stdout')
    helper._version(frontend_stdout,source_before['commit'],'targo')
    require_filename_inventory_capability(frontend_stdout)
    built['frontend_version']=frontend_version
    builder_sdk = physical(source / 'build' / HOST / 'stage0')
    builder_compiler = builder_sdk / 'bin/trustc'
    builder_version = execute([str(builder_compiler), '-vV'], source, env, evidence, 'builder-version')
    require(builder_version['exit'] == 0, 'build compiler observation failed')
    text_version = regular(evidence / 'builder-version.stdout').decode()
    require('commit-hash: ' + helper.COMPILER_SOURCE in text_version,
            'canonical compiler0 is not the declared pinned seed')
    require(sha(regular(builder_compiler)) == helper.COMPILER_SHA256,
            'canonical compiler0 bytes differ from pinned seed compiler')
    built['compiler'] = {'path': str(builder_compiler), 'source': helper.COMPILER_SOURCE,
                         'sha256': helper.COMPILER_SHA256, 'version': builder_version,
                         'sdk_inventory_sha256': sha(encoded(inventory(builder_sdk)))}
    # Preserve actual producer dep-info bytes and the checksum-comment paths.
    # This records observed inputs; it is not a formal compiler read-completeness proof.
    readsets = []
    for dep in sorted((source / 'build' / HOST).rglob('*.d')):
        if '/stage0/' in str(dep):
            continue
        raw = regular(dep)
        if not raw.startswith(b'/') and b': ' not in raw:
            continue
        paths = []
        for line in raw.splitlines():
            match = re.fullmatch(rb'# checksum:[^ ]+ file_len:[0-9]+ (.*)', line)
            if match:
                path = Path(os.fsdecode(match[1]))
                if path.is_absolute() and path.is_file():
                    paths.append({'path': str(path), 'sha256': sha(regular(path))})
        name = 'readset-' + str(len(readsets)) + '.d'
        (evidence / name).write_bytes(raw)
        readsets.append({'path': str(dep), 'evidence': name, 'sha256': sha(raw),
                         'observed_inputs': paths})
    require(readsets, 'canonical build produced no observed read-set files')
    built['readsets'] = readsets
    # The isolated copy retains the complete SDK; only the native alias pair changes.
    subprocess.run(['/bin/cp', '-cR', str(base), str(destination)], check=True)
    require(inventory(destination) == before and inventory(base) == before,
            'new SDK copy/base differs before replacement')
    for name in ALIASES:
        path = destination / 'bin' / name
        require(stat.S_ISREG(path.lstat().st_mode), 'alias is not regular')
        path.unlink()
        path.write_bytes(payload)
        path.chmod(0o755)
    after = inventory(destination)
    expected = {row['path']: row for row in before}
    for name in ALIASES:
        expected['bin/' + name] = {'path': 'bin/' + name, 'kind': 'file', 'mode': 0o755,
                                  'bytes': len(payload), 'sha256': sha(payload)}
    require(after == sorted(expected.values(), key=lambda row: row['path']), 'non-alias SDK bytes changed')
    metadata = destination / EVIDENCE
    metadata.mkdir(mode=0o700)
    for path in evidence.iterdir():
        (metadata / path.name).write_bytes(regular(path))
    record = {'schema': SCHEMA, 'status': 'prepared', 'scope': 'ordinary-unverified-only',
              'whole_sdk_ready': False, 'verified_tool_map': False,
              'source': source_before, 'builder': built,
              'producer': producer_before,
              'base': {'root': str(base), 'compiler_source': OPERATIONAL_SOURCE,
                       'compiler_sha256': OPERATIONAL_COMPILER, 'inventory': before},
              'artifact': {'path': str(artifact), 'sha256': sha(payload), 'bytes': len(payload),
                           'system_libraries': libraries},
              'destination': str(destination), 'installed_inventory': after}
    raw = encoded(record)
    (destination / RECORD).write_bytes(raw)
    return {'prepared': True, 'component_sha256': sha(raw), 'destination': str(destination),
            'whole_sdk_ready': False, 'qualification': 'pending'}



RESOURCE_BUILD = r"""
use std::os::unix::fs::{FileTypeExt, MetadataExt};
fn main() {
    let flags = std::env::var("CARGO_MAKEFLAGS").expect("real scheduler advertisement");
    let mut pair = None;
    for item in flags.split_whitespace() {
        if let Some(value) = item.strip_prefix("--jobserver-auth=").or_else(|| item.strip_prefix("--jobserver-fds=")) {
            let values: Vec<_> = value.split(',').map(|v| v.parse::<i32>().unwrap()).collect();
            assert_eq!(values.len(),2);
            if let Some(old) = pair { assert_eq!(old,(values[0],values[1])); }
            pair = Some((values[0],values[1]));
        }
    }
    let (a,b) = pair.expect("inherited scheduler pipe");
    let first = std::fs::metadata(format!("/dev/fd/{a}")).unwrap();
    let second = std::fs::metadata(format!("/dev/fd/{b}")).unwrap();
    assert!(first.file_type().is_fifo() && second.file_type().is_fifo());
    // Darwin pipe endpoints have distinct inode identities. These are the
    // advertised inherited endpoints, not newly manufactured pipes/tokens.
    assert_ne!(a,b);
    let jobs: u32 = std::env::var("NUM_JOBS").unwrap().parse().unwrap();
    let output = format!("{{\"jobs\":{jobs},\"fifo\":true,\"device\":{},\"read_inode\":{},\"write_inode\":{}}}",first.dev(),first.ino(),second.ino());
    std::fs::write(std::path::Path::new(&std::env::var("OUT_DIR").unwrap()).join("operational-resource.json"),output).unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}
"""
MANIFEST = "[package]\nname='operational_probe'\nversion='0.0.0'\nedition='2021'\n[dependencies]\ndep={path='dep'}\n[workspace]\n"
DEP_MANIFEST = "[package]\nname='dep'\nversion='0.0.0'\nedition='2021'\n"
PARENT_SOURCE = 'pub fn answer()->u32{dep::answer()}\n'
INITIAL_SOURCE = 'pub fn answer()->u32{42}\n'
CHANGED_SOURCE = 'pub fn answer()->u32{43}\n'


def json_document(raw):
    def unique(pairs):
        value = {}
        for key, item in pairs:
            require(key not in value, 'duplicate JSON field')
            value[key] = item
        return value
    result = json.loads(raw, object_pairs_hook=unique)
    require(type(result) is dict, 'JSON role is not an object')
    return result


def artifact_rows(raw):
    return [value for line in raw.splitlines() if line.strip()
            and (value := json_document(line)).get('reason') == 'compiler-artifact']


def selected(rows, name):
    found = [row for row in rows if row['target']['name'] == name]
    require(len(found) == 1, 'one exact consumer artifact required: ' + name)
    return found[0]


def read_phase(evidence, phase):
    require(set(phase) == {'argv','cwd','exit','stdout','stderr','retired'}, 'phase fields differ')
    require(type(phase['exit']) is int and phase['retired'] is True, 'phase did not retire normally')
    streams = {}
    for role in ('stdout','stderr'):
        reference = phase[role]
        require(set(reference) == {'path','sha256'} and Path(reference['path']).name == reference['path'],
                'phase reference traverses')
        raw = regular(evidence / reference['path'])
        require(sha(raw) == reference['sha256'], 'phase stream changed')
        streams[role] = raw
    return streams


def expected_inventory(before, artifact):
    rows = {row['path']: row for row in before}
    require(len(rows) == len(before), 'duplicate SDK inventory role')
    for alias in ALIASES:
        rows['bin/'+alias] = {'path':'bin/'+alias,'kind':'file','mode':0o755,
                             'bytes':artifact['bytes'],'sha256':artifact['sha256']}
    return sorted(rows.values(), key=lambda row: row['path'])


def inspect_prepared(destination, expected, helper):
    destination = physical(destination)
    raw = regular(destination / RECORD)
    require(sha(raw) == expected, 'prepared component bytes differ')
    record = json_document(raw)
    require(set(record) == {'schema','status','scope','whole_sdk_ready','verified_tool_map','source',
                            'builder','producer','base','artifact','destination','installed_inventory'},
            'current component fields differ')
    require(record['schema'] == SCHEMA and record['status'] == 'prepared'
            and record['scope'] == 'ordinary-unverified-only' and record['whole_sdk_ready'] is False
            and record['verified_tool_map'] is False and record['destination'] == str(destination),
            'current component namespace/scope differs')
    require('frontend_version' in record['builder'],
            'native filename-inventory capability observation is missing; historical subset qualification is insufficient')
    source = record['source']
    require(source_identity(physical(source['root'])) == source, 'original source/config changed')
    base = record['base']
    require(base['compiler_source'] == OPERATIONAL_SOURCE and base['compiler_sha256'] == OPERATIONAL_COMPILER,
            'operational compiler role differs')
    original = physical(base['root'])
    require(inventory(original) == base['inventory'], 'original installed SDK changed')
    require(sha(regular(original / 'bin/trustc')) == OPERATIONAL_COMPILER
            and sha(regular(destination / 'bin/trustc')) == OPERATIONAL_COMPILER,
            'operational compiler bytes differ')
    producer=record['producer']
    require(set(producer)=={'root','commit','module_sha256','helper_sha256'},'collector source fields differ')
    owner=physical(producer['root'])
    require(owner == physical(source['root']), 'collector/source custody differs')
    for name,key in [('sdk_targo_current_component.py','module_sha256'),('sdk_targo_component.py','helper_sha256')]:
        require(sha(git(owner,'show',producer['commit']+':scripts/'+name))==producer[key],
                'collector bytes are not the declared committed source')
    artifact = record['artifact']
    require(type(artifact['bytes']) is int and artifact['bytes']>0,'artifact length differs')
    for alias in ALIASES:
        payload = regular(destination / 'bin' / alias)
        require(sha(payload) == artifact['sha256'] and len(payload) == artifact['bytes'],
                'native alias damaged or substituted')
        libraries, signed = helper.native_image(payload, HOST)
        require(signed and libraries == artifact['system_libraries'], 'native image policy differs')
    observed = inventory(destination)
    require(observed == record['installed_inventory'] == expected_inventory(base['inventory'], artifact),
            'compiler/std/SDK outside alias pair changed')
    evidence = physical(destination / EVIDENCE)
    build = record['builder']
    require(build['exit'] == 0 and build['retired'] is True
            and build['argv'][1:3] == ['-B',str(Path(source['root'])/'x.py')]
            and build['argv'][3:6] == ['build','--stage','1']
            and build['argv'][-1] == 'targo-build-tool', 'not the canonical tool-only build')
    # Extra build observations are separate from the actual process retirement.
    phase = {key:build[key] for key in ('argv','cwd','exit','stdout','stderr','retired')}
    streams = read_phase(evidence, phase)
    require(b'Engineering build-tool artifact: ' in streams['stdout'] + streams['stderr'],
            'canonical producer observation absent')
    frontend=build['frontend_version']
    require(frontend['argv']==[artifact['path'],'--version','--verbose']
            and frontend['cwd']==source['root'] and frontend['exit']==0,
            'frontend capability observation target differs')
    frontend_streams=read_phase(evidence,frontend)
    helper._version(frontend_streams['stdout'],source['commit'],'targo')
    require_filename_inventory_capability(frontend_streams['stdout'])
    manager=build['manager']
    require(set(manager)=={'path','sha256','protocol','role'}
            and manager['role']=='build-tree-coordination-only', 'coordination role differs')
    require(sha(regular(Path(manager['path'])))==manager['sha256'], 'coordination helper changed')
    require(manager['protocol']['argv']==[manager['path'],'trust','repo','lock','--protocol'],
            'coordination protocol observation target differs')
    manager_streams=read_phase(evidence,manager['protocol'])
    require(manager['protocol']['exit']==0 and manager_streams['stdout']==b'trust-build-tree-manager-v2\n',
            'coordination protocol differs')
    builder = build['compiler']
    require(builder['source'] == helper.COMPILER_SOURCE and builder['sha256'] == helper.COMPILER_SHA256,
            'build compiler confused with operational compiler')
    for item in build['readsets']:
        require(Path(item['evidence']).name == item['evidence'], 'read-set evidence traverses')
        require(sha(regular(evidence/item['evidence'])) == item['sha256'], 'observed read-set changed')
    return record, evidence


def qualify(args, helper):
    record, evidence = inspect_prepared(args.destination, args.sha256, helper)
    sdk = physical(args.destination)
    cases = Path(args.case_root)
    require(cases.is_absolute() and not cases.exists() and not cases.is_relative_to(sdk),
            'qualification cases must be new and outside SDK')
    require(re.fullmatch(r'/[A-Za-z0-9_./-]+', str(cases)) is not None,
            'compiler16387 qualification requires an unescaped ASCII target namespace')
    require(args.linker is not None, 'compiler16387 qualification requires an explicit native linker')
    linker=Path(args.linker)
    require(linker.is_absolute() and linker.resolve(strict=True)==linker,'named linker must be physical and absolute')
    require(linker.is_file() and os.access(linker,os.X_OK), 'named native linker is not executable')
    linker_fact={'path':str(linker),'sha256':sha(regular(linker)),
                 'scope':'configured-executable-content-access-only'}
    linker_config='target.'+HOST+'.linker='+json.dumps(str(linker))
    cases.mkdir(mode=0o700)
    env = os.environ.copy()
    for key in ('RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER'):
        require(not env.get(key), 'unsupported caller compiler channel: '+key)
    env.pop('RUSTDOC',None)
    env['RUSTC'] = str(sdk/'bin/trustc')
    namespace = 'q-' + sha(str(cases).encode())[:16]
    qualifier_root = Path(__file__).resolve().parents[1]
    require(not git(qualifier_root,'status','--porcelain=v1').strip(), 'qualification source must be committed clean')
    qualifier = {'root':str(qualifier_root), 'commit':git(qualifier_root,'rev-parse','HEAD').decode().strip(),
                 'files':{name:sha(regular(qualifier_root/'scripts'/name)) for name in
                          ('sdk_targo_component.py','sdk_targo_current_component.py','sdk_targo_transport_witness.py')}}
    phases = {}
    def run(name, argv, cwd, expected_exit=0):
        phase = execute(argv,cwd,env,evidence,namespace+'-'+name)
        phases[name] = phase
        require(phase['exit'] == expected_exit, 'qualification phase failed: '+name)
        return regular(evidence/phase['stdout']['path'])
    run('operational-compiler',[str(sdk/'bin/trustc'),'-vV'],cases)
    out = run('operational-sysroot',[str(sdk/'bin/trustc'),'--print','sysroot'],cases)
    require(Path(out.decode().strip()).resolve() == sdk, 'operational compiler selected another sysroot')
    observations = {}
    for alias in ALIASES:
        version = run(alias+'-version',[str(sdk/'bin'/alias),'--version','--verbose'],cases)
        helper._version(version,record['source']['commit'],alias)
        if alias=='targo':
            require_filename_inventory_capability(version)
        project = cases/(alias+' Ω space')
        (project/'src').mkdir(parents=True)
        (project/'dep/src').mkdir(parents=True)
        (project/'Cargo.toml').write_text(MANIFEST)
        (project/'src/lib.rs').write_text(PARENT_SOURCE if alias=='targo' else INITIAL_SOURCE)
        if alias=='targo':
            (project/'build.rs').write_text(RESOURCE_BUILD)
        (project/'dep/Cargo.toml').write_text(DEP_MANIFEST)
        leaf = project/'dep/src/lib.rs';leaf.write_text(INITIAL_SOURCE)
        # Literal escaped spelling is a different, wrong-byte filesystem path.
        decoy = Path(str(leaf).replace(' ','\\ '))
        require(decoy != leaf, 'escaped-path control aliases actual source')
        decoy.parent.mkdir(parents=True,exist_ok=True);decoy.write_text(INITIAL_SOURCE)
        env['CARGO_HOME'] = str(project/'home')
        env['CARGO_TARGET_DIR'] = str(cases/(alias+'-target'))
        prefix = [str(sdk/'bin'/alias)] + (['--unverified'] if alias == 'targo' else [])
        prefix += ['--config',linker_config]
        # Compatibility Cargo is explicitly a different invocation domain; no
        # verified/native-branded authority is inferred from the alias name.
        argv = prefix+['build','--lib','--offline','--message-format=json','-j','1']
        first = artifact_rows(run(alias+'-cold',argv,project))
        require(selected(first,'dep')['fresh'] is False,'cold dependency not compiled')
        require(selected(first,'operational_probe')['fresh'] is False,'cold consumer not compiled')
        argv.insert(argv.index('--offline'),'--locked')
        fresh = artifact_rows(run(alias+'-unchanged',argv,project))
        require(all(row['fresh'] is True for row in fresh),'unchanged consumer was rebuilt')
        before = leaf.stat()
        leaf.write_text(CHANGED_SOURCE);os.utime(leaf,ns=(before.st_atime_ns,before.st_mtime_ns))
        changed = artifact_rows(run(alias+'-source-changed',argv,project))
        source_detected=(selected(changed,'dep')['fresh'] is False and selected(changed,'operational_probe')['fresh'] is False)
        require(alias=='cargo' or source_detected,
                'native same-size/mtime actual source change hidden by escaped decoy')
        archive = next(path for path in selected(changed,'dep')['filenames'] if path.endswith('.rlib'))
        path = Path(archive);previous = path.stat();damaged = bytearray(regular(path));damaged[0] ^= 1
        path.write_bytes(damaged);os.utime(path,ns=(previous.st_atime_ns,previous.st_mtime_ns))
        repaired = artifact_rows(run(alias+'-output-damaged',argv,project))
        damage_detected=selected(repaired,'dep')['fresh'] is False
        require(alias=='cargo' or damage_detected,'native damaged dependency was reused')
        resource_fact=None
        if alias=='targo':
            resource_rows=list((cases/(alias+'-target')).rglob('operational-resource.json'))
            require(len(resource_rows)==1,'one actual resource observation required')
            resource=json_document(regular(resource_rows[0]))
            require(resource['fifo'] is True and type(resource['jobs']) is int and resource['jobs']==1,
                    'actual scheduler/resource observation differs')
            resource_raw=regular(resource_rows[0]);resource_name=namespace+'-'+alias+'-resource.json'
            require(not (evidence/resource_name).exists(),'resource evidence already exists')
            (evidence/resource_name).write_bytes(resource_raw)
            resource_fact={'path':resource_name,'sha256':sha(resource_raw)}
        observations[alias]={'resource':resource_fact,
                            'domain':'native-explicit-unverified' if alias=='targo' else 'cargo-compatibility-surface-only',
                            'source_control':'same-size-and-mtime-with-wrong-byte-escaped-decoy',
                            'damage_control':'same-size-and-mtime-archive-corruption',
                            'source_change_detected':source_detected,'damage_detected':damage_detected,
                            'content_output_authority':alias=='targo','resource_qualified':alias=='targo'}
    # A textual Make row cannot represent this LF input unambiguously. The
    # repaired native profile must compile it but refuse every reuse attempt.
    project=cases/'filename-control'
    (project/'src').mkdir(parents=True)
    (project/'Cargo.toml').write_text("[package]\nname='filename_probe'\nversion='0.0.0'\nedition='2021'\n[workspace]\n")
    (project/'src/main.rs').write_text('#[path='+json.dumps('leaf.rs\n')+'] mod leaf;\nfn main(){println!("{}",leaf::answer());}\n')
    leaf=project/'src/leaf.rs\n';decoy=project/'src/leaf.rs'
    leaf.write_text(INITIAL_SOURCE);decoy.write_text(INITIAL_SOURCE)
    original=leaf.stat()
    env['CARGO_HOME']=str(project/'home')
    env['CARGO_TARGET_DIR']=str(cases/'filename-target')
    prefix=[str(sdk/'bin/targo'),'--unverified','--config',linker_config]
    for step in ('cold','warm','changed','warm-changed'):
        if step=='changed':
            leaf.write_text(CHANGED_SOURCE)
            os.utime(leaf,ns=(original.st_atime_ns,original.st_mtime_ns))
            require(leaf.stat().st_size==original.st_size and leaf.stat().st_mtime_ns==original.st_mtime_ns,
                    'filename edit did not preserve size/mtime')
        argv=prefix+['build','--bin','filename_probe']+([] if step=='cold' else ['--locked'])+['--offline','--message-format=json','-j','1']
        raw_build=run('filename-'+step+'-build',argv,project)
        row=selected(artifact_rows(raw_build),'filename_probe')
        require(row['fresh'] is False,'ambiguous filename received native cache authority')
        if step!='cold':
            causes=[json_document(line).get('dirty_reason') for line in raw_build.splitlines() if line.strip()]
            require('content-fingerprint-unavailable' in causes,'ambiguous inventory typed refusal missing')
        executable=Path(row['executable'])
        require(executable.is_absolute() and executable.is_relative_to(cases/'filename-target'),
                'filename control executable outside owned target')
        expected=b'43\n' if step in ('changed','warm-changed') else b'42\n'
        require(run('filename-'+step+'-run',[str(executable)],project)==expected,
                'actual filename consumer reused stale source or decoy')
    require(regular(decoy)==INITIAL_SOURCE.encode(),'filename decoy changed')
    filename_inventory={'capability':FILENAME_INVENTORY_CAPABILITY,
                        'profile':'ambiguous-LF-input-always-rebuilds',
                        'actual_path':str(leaf),'decoy_path':str(decoy),
                        'edited_sha256':sha(regular(leaf)),'decoy_sha256':sha(regular(decoy)),
                        'same_size_mtime':True,'original_mtime_ns':original.st_mtime_ns}
    # Native Targo must retain its explicit-lane refusal; no verification mode
    # is silently enabled to make an operational qualification pass.
    refusal = execute([str(sdk/'bin/targo'),'build','--offline','--manifest-path',
                       str(cases/'targo Ω space/Cargo.toml')],cases,env,evidence,namespace+'-native-lane-refusal')
    phases['native-lane-refusal'] = refusal
    require(refusal['exit'] != 0,'native build acquired implicit unverified/verified authority')
    require(inventory(sdk)==record['installed_inventory'],'SDK changed during qualification')
    require(sha(regular(linker))==linker_fact['sha256'],'named linker changed during qualification')
    value = {'schema':SCHEMA+'.qualification','component_sha256':args.sha256,'destination':str(sdk),
             'scope':'native-unverified-with-cargo-surface-only','whole_sdk_ready':False,'verified_tool_map':False,
             'case_root':str(cases),'native_linker':linker_fact,'filename_inventory':filename_inventory,
             'limitations':['default-native-tools-unqualified','escaped-target-path-unqualified',
                            'no-subordinate-tool-library-or-proof-authority'], 'qualifier':qualifier,'phases':phases,'observations':observations,'inventory_sha256':sha(encoded(inventory(sdk)))}
    raw = encoded(value);(evidence/'qualification.json').write_bytes(raw)
    return {'component_sha256':args.sha256,'qualification_sha256':sha(raw),'operational_targo':str(sdk/'bin/targo'),
            'native_unverified_qualified':True,'cargo_resource_content_qualified':False,
            'required_config':linker_config,'required_target_namespace':'unescaped-ASCII',
            'whole_sdk_ready':False,'verified_tool_map':False}


def inspect_current(args,helper):
    record,evidence = inspect_prepared(args.destination,args.sha256,helper)
    raw = regular(evidence/'qualification.json')
    require(sha(raw)==args.qualification_sha256,'qualification bytes differ')
    value = json_document(raw)
    require(set(value)=={'schema','component_sha256','destination','scope','whole_sdk_ready',
                         'verified_tool_map','case_root','native_linker','filename_inventory','limitations','qualifier','phases','observations','inventory_sha256'},
            'qualification fields differ')
    require(value['schema']==SCHEMA+'.qualification' and value['component_sha256']==args.sha256
            and value['destination']==str(physical(args.destination)) and value['scope']=='native-unverified-with-cargo-surface-only'
            and value['whole_sdk_ready'] is False and value['verified_tool_map'] is False,
            'qualification namespace/authority differs')
    require(value['inventory_sha256']==sha(encoded(inventory(args.destination))),'qualified SDK changed')
    require(set(value['observations'])==set(ALIASES),'alias population differs')
    phases=value['phases']
    cases=Path(value['case_root'])
    namespace='q-'+sha(str(cases).encode())[:16]
    require(re.fullmatch(r'/[A-Za-z0-9_./-]+',str(cases)) is not None,'target namespace outside supported compiler profile')
    linker=value['native_linker']
    require(set(linker)=={'path','sha256','scope'} and linker['scope']=='configured-executable-content-access-only',
            'named linker scope differs')
    linker_path=Path(linker['path'])
    require(linker_path.is_absolute() and linker_path.resolve(strict=True)==linker_path,'named linker path differs')
    require(sha(regular(linker_path))==linker['sha256'] and os.access(linker_path,os.X_OK),'named linker changed')
    linker_config='target.'+HOST+'.linker='+json.dumps(str(linker_path))
    require(value['limitations']==['default-native-tools-unqualified','escaped-target-path-unqualified',
                                  'no-subordinate-tool-library-or-proof-authority'], 'operational limits differ')
    qualifier=value['qualifier']
    require(set(qualifier)=={'root','commit','files'}, 'qualifier source fields differ')
    require(set(qualifier['files'])=={'sdk_targo_component.py','sdk_targo_current_component.py','sdk_targo_transport_witness.py'},
            'qualifier source census differs')
    owner=physical(qualifier['root'])
    for name,digest in qualifier['files'].items():
        require(sha(git(owner,'show',qualifier['commit']+':scripts/'+name))==digest,
                'qualifier is not its declared committed source')
    require(cases.is_absolute() and not cases.is_relative_to(physical(args.destination)), 'case namespace differs')
    sdk=physical(args.destination)
    required={'operational-compiler','operational-sysroot','native-lane-refusal'}
    required|={alias+'-'+role for alias in ALIASES for role in ['version','cold','unchanged','source-changed','output-damaged']}
    required|={'filename-'+step+'-'+role for step in ('cold','warm','changed','warm-changed') for role in ('build','run')}
    require(set(phases)==required,'actual phase population differs')
    expected_argv={
        'operational-compiler':[str(sdk/'bin/trustc'),'-vV'],
        'operational-sysroot':[str(sdk/'bin/trustc'),'--print','sysroot'],
        'native-lane-refusal':[str(sdk/'bin/targo'),'build','--offline','--manifest-path',str(cases/'targo Ω space/Cargo.toml')],
    }
    for alias in ALIASES:
        prefix=[str(sdk/'bin'/alias)]+(['--unverified'] if alias=='targo' else [])
        prefix+=['--config',linker_config]
        for role in ('cold','unchanged','source-changed','output-damaged'):
            expected_argv[alias+'-'+role]=prefix+['build','--lib']+([] if role=='cold' else ['--locked'])+['--offline','--message-format=json','-j','1']
        expected_argv[alias+'-version']=[str(sdk/'bin'/alias),'--version','--verbose']
        observation=value['observations'][alias]
        require(set(observation)=={'resource','domain','source_control','damage_control',
                                   'source_change_detected','damage_detected','content_output_authority','resource_qualified'},
                'observation fields differ')
        require(observation['domain']==('native-explicit-unverified' if alias=='targo' else 'cargo-compatibility-surface-only')
                and observation['source_control']=='same-size-and-mtime-with-wrong-byte-escaped-decoy'
                and observation['damage_control']=='same-size-and-mtime-archive-corruption','alias control roles differ')
        require(observation['content_output_authority'] is (alias=='targo')
                and observation['resource_qualified'] is (alias=='targo'),'alias authority differs')
        require(type(observation['source_change_detected']) is bool and type(observation['damage_detected']) is bool,
                'alias mutation observations differ')
        if alias=='cargo':
            require(observation['resource'] is None,'Cargo surface has no resource qualification')
            continue
        require(observation['source_change_detected'] and observation['damage_detected'],'native mutation refusal missing')
        reference=observation['resource']
        require(reference['path']==namespace+'-'+alias+'-resource.json','resource evidence role differs')
        raw_resource=regular(evidence/reference['path'])
        require(sha(raw_resource)==reference['sha256'],'resource observation changed')
        resource=json_document(raw_resource)
        require(set(resource)=={'jobs','fifo','device','read_inode','write_inode'} and resource['fifo'] is True
                and type(resource['jobs']) is int and resource['jobs']==1
                and type(resource['device']) is int and type(resource['read_inode']) is int
                and type(resource['write_inode']) is int,'actual resource fields differ')
    control=value['filename_inventory']
    require(set(control)=={'capability','profile','actual_path','decoy_path','edited_sha256','decoy_sha256',
                           'same_size_mtime','original_mtime_ns'},'filename control fields differ')
    project=cases/'filename-control'
    leaf=project/'src/leaf.rs\n';decoy=project/'src/leaf.rs'
    require(control['capability']==FILENAME_INVENTORY_CAPABILITY
            and control['profile']=='ambiguous-LF-input-always-rebuilds'
            and control['actual_path']==str(leaf) and control['decoy_path']==str(decoy)
            and control['same_size_mtime'] is True,'filename control source/profile differs')
    require(sha(regular(leaf))==control['edited_sha256']==sha(CHANGED_SOURCE.encode())
            and sha(regular(decoy))==control['decoy_sha256']==sha(INITIAL_SOURCE.encode()),
            'filename actual edited source/decoy bytes differ')
    require(type(control['original_mtime_ns']) is int and leaf.stat().st_mtime_ns==control['original_mtime_ns']
            and leaf.stat().st_size==len(INITIAL_SOURCE.encode()),'filename edit metadata differs')
    for step in ('cold','warm','changed','warm-changed'):
        name='filename-'+step+'-build'
        expected_argv[name]=[str(sdk/'bin/targo'),'--unverified','--config',linker_config,
                             'build','--bin','filename_probe']+([] if step=='cold' else ['--locked'])+['--offline','--message-format=json','-j','1']
        streams=read_phase(evidence,phases[name])
        row=selected(artifact_rows(streams['stdout']),'filename_probe')
        require(row['fresh'] is False,'filename input received cache authority')
        executable=Path(row['executable'])
        require(executable.is_absolute() and executable.is_relative_to(cases/'filename-target'),
                'filename executable outside owned target')
        expected_argv['filename-'+step+'-run']=[str(executable)]
        if step!='cold':
            causes=[json_document(line).get('dirty_reason') for line in streams['stdout'].splitlines() if line.strip()]
            require('content-fingerprint-unavailable' in causes,'filename typed refusal missing')
    for name,phase in phases.items():
        require(phase['stdout']['path']==namespace+'-'+name+'.stdout'
                and phase['stderr']['path']==namespace+'-'+name+'.stderr', 'phase evidence namespace differs')
        require(phase['argv']==expected_argv[name], 'qualification command target/arguments differ')
        cwd=cases/'filename-control' if name.startswith('filename-') else cases
        if any(name.startswith(alias+'-') and not name.endswith('-version') for alias in ALIASES):
            cwd=cases/(name.split('-',1)[0]+' Ω space')
        require(phase['cwd']==str(cwd),'qualification command namespace differs')
        streams=read_phase(evidence,phase)
        require((phase['exit']!=0) if name=='native-lane-refusal' else (phase['exit']==0),'actual exit differs')
        if name=='operational-compiler':
            require(('commit-hash: '+OPERATIONAL_SOURCE).encode() in streams['stdout'],'operational compiler source differs')
        elif name=='operational-sysroot':
            require(Path(streams['stdout'].decode().strip()).resolve()==sdk,'operational sysroot differs')
        elif name=='native-lane-refusal':
            require(b'--unverified' in streams['stderr']+streams['stdout'],'not an actual native lane refusal')
        elif name.endswith('-version'):
            helper._version(streams['stdout'],record['source']['commit'],name.removesuffix('-version'))
            if name=='targo-version':
                require_filename_inventory_capability(streams['stdout'])
        elif name.startswith('filename-') and name.endswith('-run'):
            expected=b'43\n' if name in ('filename-changed-run','filename-warm-changed-run') else b'42\n'
            require(streams['stdout']==expected,'actual filename value/stale execution differs')
        elif name.endswith('-unchanged'):
            rows=artifact_rows(streams['stdout'])
            require(selected(rows,'dep')['fresh'] is True and selected(rows,'operational_probe')['fresh'] is True
                    and all(row['fresh'] is True for row in rows),'freshness control differs')
        elif name.endswith('-source-changed'):
            rows=artifact_rows(streams['stdout'])
            detected=selected(rows,'dep')['fresh'] is False and selected(rows,'operational_probe')['fresh'] is False
            require(detected is value['observations'][name.split('-',1)[0]]['source_change_detected'],
                    'source-change observation differs')
        elif name.endswith('-output-damaged'):
            detected=selected(artifact_rows(streams['stdout']),'dep')['fresh'] is False
            require(detected is value['observations'][name.split('-',1)[0]]['damage_detected'],'damage observation differs')
    return {'native_unverified_qualified':True,'cargo_resource_content_qualified':False,'operational_targo':str(physical(args.destination)/'bin/targo'),
            'compiler_source':OPERATIONAL_SOURCE,'frontend_source':record['source']['commit'],
            'required_config':linker_config,'required_target_namespace':'unescaped-ASCII',
            'whole_sdk_ready':False,'verified_tool_map':False}

def main(argv, helper):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['prepare-current', 'qualify-current', 'inspect-current'])
    parser.add_argument('--source-root', type=Path)
    parser.add_argument('--base-sdk', type=Path)
    parser.add_argument('--destination', type=Path, required=True)
    parser.add_argument('--evidence', type=Path)
    parser.add_argument('--sha256')
    parser.add_argument('--qualification-sha256')
    parser.add_argument('--case-root', type=Path)
    parser.add_argument('--manager', type=Path)
    parser.add_argument('--linker', type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == 'prepare-current':
            require(all(x is not None for x in (args.source_root, args.base_sdk, args.evidence, args.manager)),
                    'preparation inputs missing')
            result = prepare(args, helper)
        elif args.command == 'qualify-current':
            require(args.sha256 is not None and args.case_root is not None, 'qualification inputs missing')
            result = qualify(args,helper)
        else:
            require(args.sha256 is not None and args.qualification_sha256 is not None, 'inspection identities missing')
            result = inspect_current(args,helper)
        print(json.dumps(result, sort_keys=True))
        return 0
    except (ValueError, OSError, subprocess.SubprocessError, KeyError, TypeError, UnicodeError) as error:
        print('current Targo component refused: ' + str(error), file=sys.stderr)
        return 3
