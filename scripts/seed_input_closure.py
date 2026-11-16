"""Connected physical original-input closure; deliberately NON-ADMITTING.

Only the actual source-bound producer captures these stages. Post-close callers
must supply original in-memory owner arguments and authenticated live seals;
there is no candidate-path, catalog, receipt-file or standalone admission CLI.
"""
from __future__ import annotations
from enum import Enum
import hashlib
import os
from pathlib import Path
import tomllib

HERE = Path(__file__).resolve().parent
records = __trust_source_loader__.module('trust_input_records', HERE / 'seed_input_records.py')
committed = __trust_source_loader__.module('trust_input_committed', HERE / 'seed_input_committed.py')
archives = __trust_source_loader__.module('trust_input_archives', HERE / 'seed_input_archives.py')
require, remaining = records.require, records.remaining
STAGES = ('before','private-import','common-self-host','common-ddc','installers','after')
CACHE_TREES = ('registry/index','registry/cache','git/db','registry/src','git/checkouts')
class InputRefusal(str, Enum):
    GIT_AUTHORITY = 'REFUSED_GIT_OBJECT_AND_LOCKED_CHECKOUT_AUTHORITY_PENDING'
    IGNORED_SOURCE = 'REFUSED_IGNORED_GENERATED_INCLUDE_AND_BUILD_INPUT_DISCOVERY_PENDING'
    PYTHON_IMPORTS = 'REFUSED_NATIVE_BOOTSTRAP_TRANSITIVE_BYTECODE_AND_SOURCE_AUTH_PENDING'
    NATIVE_RESOURCES = 'REFUSED_COMPILER_BUILTIN_HEADERS_AND_LINKER_RESOURCE_DISCOVERY_PENDING'
    RESOLUTION = 'REFUSED_RESOLUTION_VENDOR_GENERATED_LOCK_AND_UNUSED_CACHE_UNIVERSE_PENDING'
    AUXILIARY_CUSTODY = 'REFUSED_RAW_PROBE_PID_LOG_AND_TIMING_OBSERVATIONS_PENDING'
    INSTALLED_UNION = 'REFUSED_FULL_INSTALLED_COMPONENT_UNION_AND_PORTABLE_CATALOG_PENDING'
    PORTABLE_ANCHOR = 'REFUSED_PORTABLE_COMMITTED_CATALOG_AND_ATOMIC_GENESIS_LEDGER_PENDING'


OPEN_FAMILIES = (
    ('git-dependency-authority', InputRefusal.GIT_AUTHORITY),
    ('ignored-generated-source-inputs', InputRefusal.IGNORED_SOURCE),
    ('bootstrap-python-imports', InputRefusal.PYTHON_IMPORTS),
    ('native-compiler-resources', InputRefusal.NATIVE_RESOURCES),
    ('complete-dependency-resolution', InputRefusal.RESOLUTION),
    ('auxiliary-process-custody', InputRefusal.AUXILIARY_CUSTODY),
    ('installed-canonical-union', InputRefusal.INSTALLED_UNION),
    ('portable-proof-anchor', InputRefusal.PORTABLE_ANCHOR),
)


def original_arguments(arguments):
    require(type(arguments) is dict and arguments and all(type(k) is str and type(v) is str
            and k.startswith('--') for k,v in arguments.items()), 'original native arguments are absent')
    return {key[2:].replace('-','_'):value for key,value in arguments.items()}


def immutable_plan(values, inputs, orchestration, end):
    """Paths derive from the original invocation plus source-bound input reads."""
    remaining(end)
    source = Path(values['source_root'])
    specs = [{'label':'base-config','kind':'file','path':values['config']},
             {'label':'shared-source-archive','kind':'file','path':values['std_source_archive']},
             {'label':'legacy-receipt','kind':'file','path':values['legacy_receipt']},
             {'label':'legacy-manifest','kind':'file','path':values['legacy_manifest']},
             {'label':'producer-interpreter','kind':'file','path':inputs['producer_interpreter']['path']}]
    _, raw = records.binding(Path(values['config']), end, maximum=records.PROOF_LIMIT)
    config = tomllib.loads(raw.decode('utf-8'))
    require(not config.get('include'), 'original base configuration must remain a single explicit file')
    for item in inputs['config']['files']:
        specs.append({'label':'config-include:' + item['relative_path'],'kind':'file',
                      'path':str(source / records.relative(item['relative_path']))})
    target = config.get('target', {}).get(inputs['authenticated']['host'], {})
    for name in ('llvm-config','cc','cxx','ar','ranlib','linker'):
        require(type(target.get(name)) is str and Path(target[name]).is_absolute(), 'native input tool must be explicit')
        specs.append({'label':'native-tool:' + name,'kind':'file','path':target[name]})
    llvm, _ = records.resolution(Path(target['llvm-config']), end)
    specs.append({'label':'llvm-tree','kind':'tree','path':str(llvm.parent.parent)})
    for role in ('genesis','ddc'):
        manifest = Path(values[role + '_manifest'])
        specs.extend(({'label':role + '-manifest','kind':'file','path':str(manifest)},
                      {'label':role + '-sysroot','kind':'tree','path':values[role + '_sysroot']}))
        _, raw = records.binding(manifest, end, maximum=records.PROOF_LIMIT)
        channel = tomllib.loads(raw.decode('utf-8'))
        for name in ('rustc','cargo','rust-std'):
            item = channel['pkg'][name]['target'][inputs['authenticated']['host']]
            filename = item['xz_url'].rsplit('/',1)[1]
            records.relative(filename)
            require('/' not in filename and item.get('available') is True, 'external archive selection differs')
            specs.append({'label':role + '-archive:' + name,'kind':'file',
                          'path':str(Path(values[role + '_archives']) / filename), 'expected_sha256':item['xz_hash']})
        runtime = inputs['authenticated']['external_roots'][role]['runtime']
        for name, expected in sorted(runtime['observations'].items()):
            specs.append({'label':role + '-runtime:' + name,'kind':'absent' if expected is None else 'file',
                          'path':name, **({} if expected is None else {'expected_sha256':expected})})
        for name in sorted(runtime.get('links', {})):
            specs.append({'label':role + '-runtime-link:' + name,'kind':'file','path':name})
    for relative, item in sorted(inputs['legacy_cohort_inputs']['archives'].items()):
        name = Path(relative).name
        records.relative(name)
        specs.append({'label':'legacy-archive:' + relative,'kind':'file',
                      'path':str(Path(values['legacy_archives']) / name),'expected_sha256':item['sha256']})
    supplier = Path(values['cargo_home'])
    for relative in ('registry/index','registry/cache','git/db'):
        specs.append({'label':'supplier-cache:' + relative,'kind':'optional-tree','path':str(supplier / relative)})
    require(len({spec['label'] for spec in specs}) == len(specs), 'duplicate original input family')
    for spec in specs:
        path = Path(spec['path'])
        require(path.is_absolute() and '..' not in path.parts, 'original input path is not absolute/canonical lexical input')
    return sorted(specs, key=lambda spec:spec['label'])


def common_plan(work):
    specs = [{'label':'private-cache:' + name,'kind':'optional-tree','path':str(work / 'cargo-home' / name)}
             for name in CACHE_TREES]
    specs += [{'label':'common-config:' + name,'kind':'file','path':str(work / ('bootstrap.' + name + '.toml'))}
              for name in ('base','external','self-host','ddc')]
    return sorted(specs + safe_plan(work), key=lambda spec:spec['label'])


def import_plan(work):
    return [{'label':'private-import:' + name,'kind':'optional-tree','path':str(work / 'cargo-home' / name)}
            for name in ('registry/index','registry/cache','git/db')]


def safe_plan(work):
    specs = [{'label':'safe-path','kind':'tree','path':str(work / 'safe-bin')}]
    # The safe directory's symlinks are transport; bind actual resolved tools too.
    for path in sorted((work / 'safe-bin').iterdir()):
        specs.append({'label':'safe-tool:' + path.name,'kind':'file','path':str(path)})
    return sorted(specs, key=lambda spec:spec['label'])


def installer_plan(work):
    return [{'label':'canonical-' + name,'kind':'tree','path':str(work / name)}
            for name in ('artifacts','unpack','prepared-native-only','prepared-cohort')]


def capture_specs(specs, store, end):
    result = []
    for spec in specs:
        remaining(end)
        path, kind = Path(spec['path']), spec['kind']
        captured = dict(spec)
        if kind == 'absent':
            require(not os.path.lexists(path), 'original optional input unexpectedly exists')
            captured['absent'] = True
        elif kind == 'optional-tree' and not os.path.lexists(path):
            captured['absent'] = True
        elif kind in ('tree','optional-tree'):
            captured['rows'] = store.rows(records.tree(path, end))
        else:
            require(kind == 'file', 'unknown original input family kind')
            captured['binding'], _ = records.binding(path, end)
            require('expected_sha256' not in spec or spec['expected_sha256'] == captured['binding']['sha256'],
                    'physical original archive/runtime differs from authenticated pin')
        result.append(captured)
    return result


def compare_specs(specs, captures, store, end, *, subset=False):
    require(len(specs) == len(captures), 'physical input family count differs')
    for spec, captured in zip(specs, captures):
        remaining(end)
        require({k:captured.get(k) for k in spec} == spec
                and set(captured) <= set(spec) | {'binding','rows','absent'},
                'input proof supplied a different path/family authority')
        if captured.get('absent') is True:
            require(set(captured) == set(spec) | {'absent'}, 'optional input proof has unexpected fields')
            require(spec['kind'] in ('absent','optional-tree') and not os.path.lexists(spec['path']),
                    'optional original input appeared after live capture')
        elif spec['kind'] == 'file':
            require(set(captured) == set(spec) | {'binding'}, 'file input proof has unexpected fields')
            observed, _ = records.binding(Path(spec['path']), end)
            require(observed == captured.get('binding'), 'physical original file/mode/resolution/literal link changed')
        else:
            require(set(captured) == set(spec) | {'rows'}, 'tree input proof has unexpected fields')
            require(spec['kind'] in ('tree','optional-tree') and 'rows' in captured, 'missing physical input tree')
            expected = store.read_rows(captured['rows'])
            observed = records.tree(Path(spec['path']), end)
            if subset:
                indexed = {row['path']:row for row in observed}
                require(all(indexed.get(row['path']) == row for row in expected),
                        'an original comparison-cache file/mode/literal link changed later')
            else:
                require(observed == expected, 'physical original input tree changed after closure')


class CaptureSession:
    def __init__(self, args, work, inputs, auth, end, live):
        require(live is not None and live.payload['deadline'] == end, 'physical capture requires actual live worker context')
        self.values = {name:str(getattr(args,name)) for name in
                       ('source_root','std_source_archive','config','cargo_home','legacy_receipt','legacy_archives',
                        'legacy_manifest','genesis_manifest','genesis_archives','genesis_sysroot',
                        'ddc_manifest','ddc_archives','ddc_sysroot')}
        self.work, self.inputs, self.auth, self.end, self.live = work, inputs, auth, end, live
        self.orchestration = HERE.parent
        self.plan = immutable_plan(self.values, inputs, self.orchestration, end)
        self.store = records.ChunkStore(work / 'physical-input-closure', end, create=True)
        self.stages = []
        self.snapshots = {}

    def source(self, root, expected):
        captures = []
        def collect(path, commit, tree, entries, raw):
            require(len(raw) <= records.PROOF_LIMIT // 2, 'source commit object exceeds chunk budget')
            data = committed.committed_rows(path, entries, commit, tree, raw, self.end)
            captures.append({'repository':path.relative_to(root).as_posix(),
                'commit':commit,'tree':tree,'commit_object_hex':data['commit_object_hex'],
                'files':self.store.rows(data['files']),'directories':self.store.rows(data['directories'])})
        summary = self.auth.source_snapshot(root, expected, physical=collect, deadline=self.end)
        return {'summary':summary,'repositories':captures}

    def imported_copy(self, captures):
        supplier = {item['label'].removeprefix('supplier-cache:'):item
                    for item in self.snapshots['before']['inputs'] if item['label'].startswith('supplier-cache:')}
        for item in captures:
            name = item['label'].removeprefix('private-import:')
            original = supplier[name]
            require(item.get('absent') == original.get('absent') and item.get('rows') == original.get('rows'),
                    'actual initial private Cargo copy differs from physical original supplier modes/bytes/links')

    def seal(self, stage):
        require(len(self.stages) < len(STAGES) and stage == STAGES[len(self.stages)], 'physical input stage is missing/reordered')
        remaining(self.end)
        snapshot = {'schema':'trust.original629-physical-input-stage.v1','stage':stage,
                    'original_deadline':self.end,'inputs':capture_specs(self.plan,self.store,self.end)}
        # Installer capture has no source/common compiler invocation of its own.
        if stage != 'installers':
            snapshot['source'] = self.source(Path(self.values['source_root']), self.inputs['authenticated']['source']['source_commit'])
            snapshot['orchestration'] = self.source(self.orchestration, self.inputs['orchestration']['source_commit'])
        if stage == 'private-import':
            snapshot['imported_cache'] = capture_specs(import_plan(self.work),self.store,self.end)
            snapshot['imported_tools'] = capture_specs(safe_plan(self.work),self.store,self.end)
            self.imported_copy(snapshot['imported_cache'])
        if stage in ('common-self-host','common-ddc','after'):
            snapshot['common'] = capture_specs(common_plan(self.work), self.store, self.end)
        if stage in ('installers','after'):
            snapshot['installers'] = capture_specs(installer_plan(self.work), self.store, self.end)
        if self.snapshots:
            require(snapshot['inputs'] == self.snapshots['before']['inputs'],
                    'immutable original inputs changed before another native phase')
        if stage != 'before' and stage != 'installers':
            require(snapshot['source'] == self.snapshots['before']['source']
                    and snapshot['orchestration'] == self.snapshots['before']['orchestration'],
                    'source universe changed before another original phase')
        if stage == 'common-ddc':
            require(snapshot['common'] == self.snapshots['common-self-host']['common'],
                    'comparison inputs changed; refuse BEFORE diverse DDC invocation')
        if stage == 'after':
            require(snapshot['installers'] == self.snapshots['installers']['installers'],
                    'canonical installer inputs changed during execution')
        reference = self.store.put(snapshot)
        self.snapshots[stage] = snapshot
        self.stages.append({'stage':stage,'reference':reference})
        self.live.event('input-seal', stage=stage, reference=reference)
        if stage == 'after':
            value = {'schema':'trust.original629-physical-input-index.v1','stages':self.stages,
                     'original_deadline':self.end,'admitted_root_seed':False,'counts_as_trust_stage0_evidence':False}
            raw = records.encoded(value)
            require(len(raw) <= records.PROOF_LIMIT, 'physical index exceeds proof bound')
            path = self.work / 'INPUT-CLOSURE.json'
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
            try:
                with os.fdopen(fd,'wb',closefd=False) as stream:
                    stream.write(raw)
                    stream.flush()
                    os.fsync(fd)
            finally:
                os.close(fd)
            self.store.budget.read(path)
            for parent in (self.store.root, self.work):
                directory = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
                try:
                    os.fsync(directory)
                finally:
                    os.close(directory)
        remaining(self.end)


def verify_closed_inputs(custody, record, documents, loader):
    """Private continuation of actual closed capability, never a JSON issuer."""
    work, end = custody.work, custody.end
    remaining(end)
    require(record['native_arguments']['--source-root'] == str(custody.source)
            and record['native_arguments']['--cargo-home'] == str(custody.cargo_home)
            and record['native_arguments']['--work-dir'] == str(work), 'original argument custody differs')
    budget = records.MetadataBudget(end)
    for name, expected in record['bound_files'].items():
        require(hashlib.sha256(budget.read(work / name)).hexdigest() == expected, 'live retained proof differs')
    index = records.decode(budget.read(work / 'INPUT-CLOSURE.json'))
    require(index.get('schema') == 'trust.original629-physical-input-index.v1'
            and index.get('original_deadline') == end and index.get('admitted_root_seed') is False
            and index.get('counts_as_trust_stage0_evidence') is False
            and index.get('stages') == record['input_seals']
            and tuple(item['stage'] for item in index['stages']) == STAGES,
            'physical proof index does not join original live seals/end')
    store = records.ChunkStore(work / 'physical-input-closure', end, budget=budget)
    snapshots = {}
    for item in index['stages']:
        snapshot = store.get(item['reference'])
        require(snapshot.get('schema') == 'trust.original629-physical-input-stage.v1'
                and snapshot.get('stage') == item['stage'] and snapshot.get('original_deadline') == end,
                'physical input stage differs from live seal/original end')
        snapshots[item['stage']] = snapshot
    before, after = snapshots['before'], snapshots['after']
    values = original_arguments(record['native_arguments'])
    inputs = documents['inputs-before.json']
    plan = immutable_plan(values, inputs, custody.root, end)
    require(all(snapshot['inputs'] == before['inputs'] for snapshot in snapshots.values()),
            'immutable original inputs changed between producer stages')
    compare_specs(plan, after['inputs'], store, end)
    source_rows = {}
    for name, root, expected in (
        ('source',custody.source,inputs['authenticated']['source']['source_commit']),
        ('orchestration',custody.root,inputs['orchestration']['source_commit'])):
        capture = after[name]
        expected_summary = inputs['authenticated']['source'] if name == 'source' else inputs['orchestration']
        require(capture['summary'] == expected_summary, 'physical source summary differs from original capture')
        require(all(snapshot[name] == before[name] for stage,snapshot in snapshots.items() if stage != 'installers'),
                'committed source universe changed between original phases')
        source_rows[name] = committed.verify_providers(root,capture['repositories'],store,end,expected)
    left, right = snapshots['common-self-host']['common'], snapshots['common-ddc']['common']
    require(left == right, 'original comparison legs did not receive identical complete captured cache/config/tool input trees')
    # Reopen the final universe exactly and the two equal original universes as
    # immutable subsets. New later packages get NO retroactive DDC-input credit.
    imported = snapshots['private-import']
    suppliers = {item['label'].removeprefix('supplier-cache:'):item for item in before['inputs']
                 if item['label'].startswith('supplier-cache:')}
    for item in imported['imported_cache']:
        original = suppliers[item['label'].removeprefix('private-import:')]
        require(item.get('absent') == original.get('absent') and item.get('rows') == original.get('rows'),
                'physical original supplier/private-copy provenance differs')
    compare_specs(import_plan(work),imported['imported_cache'],store,end,subset=True)
    compare_specs(safe_plan(work),imported['imported_tools'],store,end)
    common = common_plan(work)
    compare_specs(common, after['common'], store, end)
    compare_specs(common, left, store, end, subset=True)
    require(snapshots['installers']['installers'] == after['installers'],
            'canonical installer/archive/extracted payload changed during installer execution')
    compare_specs(installer_plan(work),after['installers'],store,end)
    pins = archives.lock_checksums({'source':custody.source,'orchestration':custody.root},source_rows,end)
    registry = archives.registry_sources(work / 'cargo-home',pins,end)
    support = loader.module('trust_input_support', custody.root / 'scripts/mint_seed_support.py')
    installation = documents['canonical-seed-installation-inputs.json']
    selected = installation['artifacts']
    pins_path = work / 'prepared-cohort/src-stage0'
    pinned, pins_raw = records.regular(pins_path,end,maximum=records.PROOF_LIMIT)
    require(pinned['sha256'] == installation['stage0_sha256'], 'canonical installer selection changed prepared pins')
    prepared_pins = {}
    for line in pins_raw.decode('utf-8').splitlines():
        if not line or line.startswith('#'):
            continue
        key, separator, value = line.partition('=')
        require(separator and key not in prepared_pins, 'canonical prepared pins are malformed')
        prepared_pins[key] = value
    require(selected['source_commit'] == inputs['authenticated']['source']['source_commit']
            and selected['host'] == inputs['authenticated']['host'], 'canonical installer source/host identity differs')
    require(tuple(row['component'] for row in selected['artifacts']) == tuple(support.COMPONENTS),
            'canonical installer component domain differs')
    external_joins = []
    for role in ('genesis','ddc'):
        _, channel_raw = records.binding(Path(values[role + '_manifest']),end,maximum=records.PROOF_LIMIT)
        channel = tomllib.loads(channel_raw.decode('utf-8'))
        for name in ('rustc','cargo','rust-std'):
            item = channel['pkg'][name]['target'][inputs['authenticated']['host']]
            archive = Path(values[role + '_archives']) / item['xz_url'].rsplit('/',1)[1]
            external_joins.append(archives.external_payload(archive,Path(values[role + '_sysroot']),
                name,inputs['authenticated']['host'],end))
    installer_joins = []
    for row in selected['artifacts']:
        component = row['component']
        filename = f"{component}-{selected['source_version']}-trust-{selected['host']}.tar.xz"
        require(row['filename'] == filename and row['package_root'] == filename.removesuffix('.tar.xz'),
                'canonical archive identity changed')
        pin = 'dist/' + prepared_pins['compiler_date'] + '/' + filename
        require(prepared_pins.get(pin) == row['sha256'], 'canonical installer archive differs from original prepared pin')
        actual, _ = records.regular(work / 'artifacts' / filename,end)
        require(actual['sha256'] == row['sha256'] and actual['bytes'] == row['archive_bytes'], 'canonical archive pin changed')
        archives.archive_projection(work / 'artifacts' / filename,
                                    records.tree(work / 'unpack' / component,end),end)
        installer = work / 'unpack' / component / row['package_root'] / 'install.sh'
        observed, _ = records.regular(installer,end)
        require(observed['sha256'] == row['installer_sha256'] and observed['mode'] & 0o111,
                'actual original executed installer bytes/mode changed')
        installer_joins.append({'component':component,'archive_sha256':actual['sha256'],
                                'installer_sha256':observed['sha256']})
    # Every retained chunk must be in the closed live index's transitive closure.
    # Unknown files are not a place to hide more than the aggregate proof limit.
    referenced = {str(path) for path in map(Path,budget.files) if path.parent == store.root}
    retained = set()
    for path in store.root.iterdir():
        remaining(end)
        require(len(retained) < records.ENTRY_LIMIT, 'proof store entry bound exceeded')
        retained.add(str(path))
    require(retained == referenced, 'physical proof store has an orphan or missing canonical chunk')
    loader.recheck()
    custody.recheck_source()
    remaining(end)
    covered = ('recursive-committed-source-providers','orchestration-committed-source',
               'base-config-and-declared-config-closure','configured-native-tool-resolution-bytes',
               'complete-configured-llvm-tree','external-sysroot-and-original-archive-bytes',
               'supplier-original-private-copy-and-final-cache-physical-trees','equal-pre-ddc-private-input-universes',
               'registry-archive-to-extracted-source-for-committed-locks','canonical-archive-unpack-installer-bytes')
    return {'schema':'trust.original629-physical-input-coverage.v1','passed_declared_physical_joins':True,
            'complete_original_input_closure':False,'admitted_root_seed':False,
            'counts_as_trust_stage0_evidence':False,'current_toolchain_qualification':False,
            'covered':[{'family':name,'status':'PHYSICAL_DECLARED_SCOPE_CLOSED'} for name in covered],
            'refusals':[{'family':name,'status':status.value} for name,status in OPEN_FAMILIES],
            'registry':registry,'canonical_installers':installer_joins,'external_archive_payloads':external_joins,
            'unique_metadata_bytes':budget.total,'proof_limit':records.PROOF_LIMIT,
            'aggregate_limit':records.AGGREGATE_LIMIT,'original_deadline':end}
