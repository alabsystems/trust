#!/usr/bin/env python3
"""Inert native-component boundary controls; never execute or qualify an SDK."""
import copy
import base64
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import types
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'sdk_targo_component.py'
api = types.ModuleType('tested_native_targo_component')
api.__file__ = str(SCRIPT)
sys.modules[api.__name__] = api
exec(compile(SCRIPT.read_bytes(), str(SCRIPT), 'exec'), api.__dict__)


class NativeComponent(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()

    def tree(self):
        root = self.root / 'hierarchy/sdk'
        (root / 'bin').mkdir(parents=True)
        for name in ('targo', 'cargo', 'trustc', 'targo-trust'):
            (root / 'bin' / name).write_bytes(b'old pair' if name in api.ALIASES else name.encode())
            (root / 'bin' / name).chmod(0o755)
        (root / 'lib/private').mkdir(parents=True)
        (root / 'lib/private/abi').write_bytes(b'unchanged private hierarchy')
        (root / 'lib/lean-table').write_bytes(b'unchanged Lean table')
        (root / 'lib/source-link').symlink_to('../historical-rust-src')
        private = root.parent / 'rustc-private-sysroots/retained82'; private.mkdir(parents=True)
        (private / 'rustc_driver.rlib').write_bytes(b'unchanged sibling private ABI')
        return root

    def record(self):
        hashed = 'a' * 64
        files = {name: hashed for name in api.BASE_SOURCE_PATHS | api.PRODUCTION_PATHS | {api.TEST_PATH}}
        return {'schema': api.SCHEMA, 'status': 'prepared', 'name': 'targo', 'aliases': ['targo', 'cargo'],
                'retained_inputs_unchanged': True,
                'base': {'compiler_source': api.COMPILER_SOURCE, 'compiler_sha256': api.COMPILER_SHA256,
                         'host': api.HOST, 'mint_sha256': hashed, 'frontend_component_sha256': hashed,
                         'frontend_qualified_sha256': hashed, 'frontend_artifact_sha256': hashed,
                         'stage_binding_sha256': hashed, 'original_pair': dict.fromkeys(api.ALIASES, hashed),
                         'before_tools': {'targo': hashed, 'cargo': hashed, 'trustc': api.COMPILER_SHA256, 'targo-trust': hashed},
                         'stage_authority': {}, 'inventory': {}},
                'source': {'base': api.COMPILER_SOURCE, 'port_base': api.PORT_BASE, 'commit': 'b' * 40,
                           'tree': 'c' * 40, 'root': '/owned/source', 'files': files,
                           'production_delta': {name: files[name] for name in api.PRODUCTION_PATHS},
                           'test_delta': {api.TEST_PATH: hashed}, 'documentation_delta': {api.DOC_PATH: hashed},
                           'outside_delta_sha256': hashed, 'locks': dict.fromkeys(api.LOCKS, hashed),
                           'gitlinks': {}, 'relation': {}},
                'artifact': {'sha256': hashed, 'bytes': 3, 'mode': 0o755, 'system_libraries': ['/usr/lib/libSystem.B.dylib']},
                'build': {}, 'transport': {}}

    def test_aliases_compiler_and_source_allowlist_are_closed(self):
        record = self.record()
        api.record_shape(record)
        for edit in (
            lambda x: x.update(aliases=['targo', 'rustc']),
            lambda x: x['base'].update(compiler_sha256='b' * 64),
            lambda x: x['base']['original_pair'].update(cargo='b' * 64),
            lambda x: x['source']['production_delta'].update({'targo-trust/src/main.rs': 'a' * 64}),
            lambda x: x['source']['files'].update({'compiler/rustc_driver/src/lib.rs': 'a' * 64}),
            lambda x: x['source']['locks'].pop('Cargo.lock'),
        ):
            changed = copy.deepcopy(record)
            edit(changed)
            with self.assertRaises(api.Refusal):
                api.record_shape(changed)

    def test_source_protected_fold_excludes_only_declared_delta(self):
        root = self.root / 'source'; root.mkdir()
        env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
        env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull)
        def git(*args):
            return subprocess.check_output(['/usr/bin/git', '-C', str(root), *args], env=env).decode().strip()
        git('init', '-q')
        git('config', 'user.name', 'Inert fixture'); git('config', 'user.email', 'fixture@example.invalid')
        git('config', 'commit.gpgsign', 'false')
        path = root / next(iter(sorted(api.PRODUCTION_PATHS))); path.parent.mkdir(parents=True)
        path.write_text('before\n'); (root / 'Cargo.lock').write_text('locked\n')
        git('add', '.'); git('commit', '-qm', 'inert original')
        old = git('rev-parse', 'HEAD')
        path.write_text('allowed production delta\n'); git('add', '.'); git('commit', '-qm', 'inert allowed delta')
        changed = git('rev-parse', 'HEAD')
        self.assertEqual(api._protected_tree(root, old), api._protected_tree(root, changed))
        (root / 'Cargo.lock').write_text('foreign lock\n'); git('add', '.'); git('commit', '-qm', 'inert forbidden delta')
        self.assertNotEqual(api._protected_tree(root, old), api._protected_tree(root, git('rev-parse', 'HEAD')))

    def test_full_inventory_allows_pair_only_and_rejects_partial_or_private_drift(self):
        root = self.tree(); before = api.inventory(root)
        payload = b'new native pair'
        artifact = {'sha256': api.sha256(payload), 'bytes': len(payload), 'mode': 0o755}
        (root / 'bin/targo').write_bytes(payload)
        with self.assertRaises(api.Refusal):
            api.pair_inventory(before, api.inventory(root), artifact)
        (root / 'bin/cargo').write_bytes(payload)
        api.pair_inventory(before, api.inventory(root), artifact)
        for path in ('lib/private/abi', 'lib/lean-table', 'bin/targo-trust',
                     '../rustc-private-sysroots/retained82/rustc_driver.rlib'):
            original = (root / path).read_bytes(); (root / path).write_bytes(b'changed')
            with self.assertRaises(api.Refusal):
                api.pair_inventory(before, api.inventory(root), artifact)
            (root / path).write_bytes(original)
        link = root / 'lib/source-link'; link.unlink(); link.symlink_to('/foreign/source')
        with self.assertRaises(api.Refusal):
            api.pair_inventory(before, api.inventory(root), artifact)

    def test_typed_overlay_rejects_forgery_wrong_base_other_copy_and_mutation(self):
        root = self.tree()
        current = api.tool_map(root); old = dict(current, targo='a' * 64, cargo='a' * 64)
        overlay = api._ValidatedNativeTargoOverlay('a' * 64, 'a' * 64, current['targo'], 'b' * 64,
                    api.COMPILER_SOURCE, api.COMPILER_SHA256, 'c' * 64, 'd' * 64,
                    str(root), api.sha256(api.canonical(api.inventory(root))), api._SEAL)
        args = dict(mint='b' * 64, compiler_source=api.COMPILER_SOURCE, compiler_sha256=api.COMPILER_SHA256,
                    frontend_component='c' * 64, frontend_artifact='d' * 64)
        self.assertEqual(api.project_verified_tool_map(overlay, root, current, old, **args), old)
        with self.assertRaises(api.Refusal):
            api.project_verified_tool_map(dict(overlay.__dict__), root, current, old, **args)
        with self.assertRaises(api.Refusal):
            api.project_verified_tool_map(overlay, root, current, old, **dict(args, mint='e' * 64))
        other = self.root / 'other'; other.mkdir()
        with self.assertRaises(api.Refusal):
            api.project_verified_tool_map(overlay, other, current, old, **args)
        (root / 'lib/private/abi').write_bytes(b'mutated after inspection')
        with self.assertRaises(api.Refusal):
            api.project_verified_tool_map(overlay, root, current, old, **args)

    def test_fixed_refs_reject_abspath_traversal_symlink_and_duplicate_json(self):
        root = self.root / 'evidence'; root.mkdir()
        raw = b'actual raw bytes'; (root / 'build.stderr').write_bytes(raw)
        evidence = api.Evidence(root)
        self.assertEqual(evidence.read({'path': 'build.stderr', 'sha256': api.sha256(raw)}, 'build.stderr'), raw)
        for path in (str(root / 'build.stderr'), '../build.stderr', 'transport.stderr'):
            with self.assertRaises(api.Refusal):
                evidence.read({'path': path, 'sha256': api.sha256(raw)}, 'build.stderr')
        (root / 'transport.stderr').symlink_to(root / 'build.stderr')
        with self.assertRaises(api.Refusal):
            api.Evidence(root).read({'path': 'transport.stderr', 'sha256': api.sha256(raw)}, 'transport.stderr')
        with self.assertRaises(api.Refusal):
            api.parse(b'{"exit":0,"exit":0}')

    def test_actual_zero_refuses_bool_unknown_incomplete_and_signal(self):
        api.retirement({'completed': True, 'actual_exit': 0, 'owned_command_drained': True})
        for value in (False, True, None, -15, 1, 130):
            with self.assertRaises(api.Refusal):
                api.retirement({'completed': True, 'actual_exit': value, 'owned_command_drained': True})
        for field in ('completed', 'owned_command_drained'):
            with self.assertRaises(api.Refusal):
                api.retirement(dict(completed=True, actual_exit=0, owned_command_drained=True, **{}) | {field: False})

    def test_version_own_source_tuple_and_retained_release_are_separate(self):
        source = '123456789' + 'a' * 31
        env = dict(CFG_VER_HASH=source, CFG_COMMIT_HASH=source, CFG_SHORT_COMMIT_HASH=source[:9],
                   CFG_COMMIT_DATE='2026-11-08', CFG_RELEASE='1.101.0-dev', CFG_TRUST_VERSION='0.13.0')
        api.version_environment(env, source)
        raw = ('targo 1.101.0-dev\nrelease: 1.101.0-dev\ncommit-hash: ' + source
               + '\ntrust-repo-commit-hash: ' + source + '\ntrust: 0.13.0\n').encode()
        api._version(raw, source, 'targo', '1.101.0-dev', '0.13.0')
        for changed in (dict(env, CFG_SHORT_COMMIT_HASH=source[:7]), dict(env, CFG_VER_HASH=api.COMPILER_SOURCE),
                        dict(env, CFG_TRUST_VERSION=''), dict(env, RUSTC='/foreign/compiler')):
            with self.assertRaises(api.Refusal): api.version_environment(changed, source)
        with self.assertRaises(api.Refusal):
            api._version(raw, api.COMPILER_SOURCE, 'targo', '1.101.0-dev', '0.13.0')
        with self.assertRaises(api.Refusal):
            api._version(raw, source, 'targo', '1.100.0', '0.13.0')

    def test_native_image_rejects_foreign_cpu_library_rpath_and_bad_signature_bounds(self):
        def image(library='/usr/lib/libSystem.B.dylib', cpu=0x100000c, extra=b''):
            name = library.encode() + b'\0'; name += b'\0' * (-len(name) % 4)
            dylib = struct.pack('<6I', 0xc, 24 + len(name), 24, 0, 0, 0) + name
            commands = dylib + extra
            return struct.pack('<8I', 0xfeedfacf, cpu, 0, 2, 1 + bool(extra), len(commands), 0, 0) + commands
        self.assertEqual(api.native_image(image(), api.HOST), (['/usr/lib/libSystem.B.dylib'], False))
        for raw in (image(cpu=0x1000007), image(library='/opt/foreign/lib.dylib'),
                    image(extra=struct.pack('<2I', 0x8000001c, 8)),
                    image(extra=struct.pack('<4I', 0x1d, 16, 0xffffff, 4))):
            with self.assertRaises(api.Refusal): api.native_image(raw, api.HOST)

    def test_transport_raw_requires_same_real_pipe_compiler_and_typed_negative(self):
        subject = '/unqualified/sandbox'; identity = [1, 2, 1, 2]
        child = {'kind': 'native-run', 'observed_pipe': identity, 'available_before': 0, 'available_after': 0,
                 'compiler_exit': 0, 'compiler_stdout_hex': (subject + '\n').encode().hex(),
                 'compiler_stderr_hex': '', 'sysroot': subject, 'marker': 'native-targo-custody-positive-v1'}
        stream = lambda value: b'NATIVE_TARGO_CUSTODY ' + json.dumps(value).encode() + b'\n'
        context = {'selected_subject': subject}
        observed = api.transport_observation(2, [(0, stream(child), b'')], context, identity)
        self.assertEqual(observed['compiler_stdout_sha256'], api.sha256((subject + '\n').encode()))
        for changed in (dict(child, observed_pipe=[9, 9, 9, 9]), dict(child, available_after=1),
                        dict(child, compiler_exit=False), dict(child, sysroot='/foreign'),
                        dict(child, compiler_stdout_hex=b'/foreign\n'.hex())):
            with self.assertRaises(api.Refusal):
                api.transport_observation(2, [(0, stream(changed), b'')], context, identity)
        missing = dict(mode='missing', child_exit=75, reason='checked-import-unavailable', compiler_started=False, marker=False)
        malformed = dict(mode='malformed', child_exit=75, reason='checked-import-error', compiler_started=False, marker=False)
        api.transport_observation(3, [(75, stream(missing), b''), (75, stream(malformed), b'')], context)
        with self.assertRaises(api.Refusal):
            api.transport_observation(3, [(0, stream(missing), b''), (75, stream(malformed), b'')], context)
        with self.assertRaises(api.Refusal):
            api.transport_observation(3, [(75, stream(dict(missing, compiler_started=0)), b''),
                                           (75, stream(malformed), b'')], context)

    def test_full_transport_requires_closed_context_matching_raw_and_finite_observations(self):
        root = self.tree(); before = api.inventory(root); record = self.record()
        evidence = self.root / 'transport-evidence'; evidence.mkdir()
        def save(name, value, raw=False):
            value = value if raw else api._json_bytes(value)
            (evidence / name).write_bytes(value)
            return {'path': name, 'sha256': api.sha256(value)}
        record['base']['inventory'] = save('base-inventory.json', before)
        artifact = record['artifact']; stage = api.inventory_stage(before)
        after = copy.deepcopy(before)
        for row in after['entries']:
            if row['path'] in (stage + '/bin/targo', stage + '/bin/cargo'):
                row.update(mode=artifact['mode'], bytes=artifact['bytes'], sha256=artifact['sha256'])
        subject = '/prospective/' + stage
        test = [subject + '/bin/targo', '--unverified', 'test', '--config', 'build.test-jobs=1',
                '--manifest-path', '/owned/source/Cargo.toml',
                '--locked', '--offline', '-p', 'jobserver_utils', '--lib']
        run = [subject + '/bin/targo', '--unverified', 'run', '--locked', '--offline', '--manifest-path',
               '/owned/mini/Cargo.toml', '--bin', 'native-targo-custody-witness', '--']
        commands = [{'name': name, 'argv': [test + ['transport_witness_tests::' + name, '--', '--exact',
                                                    '--nocapture']]}
                    for name in api.CONTROLS[:2]]
        commands += [{'name': api.CONTROLS[2], 'argv': [run + ['positive', subject + '/bin/trustc']]},
                     {'name': api.CONTROLS[3], 'argv': [run + [mode, subject + '/bin/trustc']
                                                       for mode in ('missing', 'malformed')]}]
        context = {'schema': 'trust.native-targo-transport-context.v1', 'source_commit': record['source']['commit'],
                   'artifact_sha256': artifact['sha256'], 'compiler_sha256': api.COMPILER_SHA256,
                   'base_stage_binding_sha256': record['base']['stage_binding_sha256'], 'selected_subject': subject,
                   'aliases': {name: {'observed_path': subject + '/bin/' + name, 'sha256': artifact['sha256']}
                               for name in api.ALIASES},
                   'compiler': {'observed_path': subject + '/bin/trustc', 'source_commit': api.COMPILER_SOURCE,
                                'sha256': api.COMPILER_SHA256},
                   'frontend': {'observed_path': subject + '/bin/targo-trust',
                                'sha256': record['base']['frontend_artifact_sha256']},
                   'subject_inventory_sha256': api.sha256(api.canonical(after)),
                   'witness': {'project_root': '/owned/mini', 'source_sha256': api.TRANSPORT_SOURCE_SHA256,
                               'manifest_sha256': api.sha256(api.transport_manifest('/owned/source'))}, 'commands': commands}
        pipe = [1, 2, 1, 2]
        positive = dict(kind='native-run', observed_pipe=pipe, available_before=0, available_after=0,
                        compiler_exit=0, compiler_stdout_hex=(subject + '\n').encode().hex(),
                        compiler_stderr_hex='', sysroot=subject, marker='native-targo-custody-positive-v1')
        child = lambda x: b'NATIVE_TARGO_CUSTODY ' + api.canonical(x) + b'\n'
        out_frames, err_frames, controls = [], [], []
        for number, command in enumerate(commands):
            outputs = []
            for index, argv in enumerate(command['argv']):
                code = 75 if number == 3 else 0
                if number < 2:
                    out = ('test transport_witness_tests::' + api.CONTROLS[number]
                           + ' ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored; 20 filtered out\n').encode()
                elif number == 2:
                    out = child(positive)
                else:
                    mode = ('missing', 'malformed')[index]
                    out = child(dict(mode=mode, child_exit=75, reason='checked-import-' + ('unavailable' if index == 0 else 'error'),
                                     compiler_started=False, marker=False))
                outputs.append((code, out, b''))
                for target, raw in ((out_frames, out), (err_frames, b'')):
                    target.append(dict(name=command['name'], index=index, argv=argv, exit=code,
                                       raw_base64=base64.b64encode(raw).decode()))
            controls.append(dict(name=command['name'], exit=0, argv=command['argv'],
                                 observed=api.transport_observation(number, outputs, context, pipe if number == 2 else None)))
        refs = {'context': save('transport.context.json', context),
                'stdout': save('transport.stdout', b''.join(api.canonical(x) + b'\n' for x in out_frames), True),
                'stderr': save('transport.stderr', b''.join(api.canonical(x) + b'\n' for x in err_frames), True)}
        result = dict(schema='trust.native-targo-transport.v1', source_commit=record['source']['commit'],
                      artifact_sha256=artifact['sha256'], compiler_sha256=api.COMPILER_SHA256,
                      context_sha256=refs['context']['sha256'], stdout_sha256=refs['stdout']['sha256'],
                      stderr_sha256=refs['stderr']['sha256'], controls=controls, completed=True,
                      retirement=dict(completed=True, actual_exit=0, owned_command_drained=True))
        record['transport'] = dict(refs, result=save('transport.result.json', result), controls=list(api.CONTROLS))
        api._transport(record, api.Evidence(evidence))
        # Rebinding the context digest cannot turn a caller-supplied libtest
        # budget into the sole admitted route, even beside the new config.
        for change in ('manual-thread-arg', 'missing-owned-budget', 'different-owned-budget'):
            tainted = copy.deepcopy(context)
            argv = tainted['commands'][0]['argv'][0]
            if change == 'manual-thread-arg':
                argv.append('--test-threads=1')
            elif change == 'missing-owned-budget':
                index = argv.index('--config'); del argv[index:index + 2]
            else:
                argv[argv.index('build.test-jobs=1')] = 'build.test-jobs=2'
            record['transport']['context'] = save('transport.context.json', tainted)
            with self.subTest(change=change), self.assertRaisesRegex(api.Refusal, 'transport commands differ'):
                api._transport(record, api.Evidence(evidence))
        record['transport']['context'] = save('transport.context.json', context)
        changed = copy.deepcopy(result); changed['controls'][2]['observed'] = {}
        record['transport']['result'] = save('transport.result.json', changed)
        with self.assertRaises(api.Refusal): api._transport(record, api.Evidence(evidence))
        record['transport']['result'] = save('transport.result.json', result)
        altered = copy.deepcopy(context); altered['aliases']['cargo']['sha256'] = 'e' * 64
        record['transport']['context'] = save('transport.context.json', altered)
        with self.assertRaises(api.Refusal): api._transport(record, api.Evidence(evidence))


if __name__ == '__main__':
    unittest.main()
