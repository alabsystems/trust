#!/usr/bin/env python3
"""Inert source/artifact fixtures only; never qualify or execute an SDK tool."""
from pathlib import Path
import copy
import hashlib
import json
import os
import shutil
import struct
import subprocess
import tempfile
import types
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
tools = types.ModuleType('frontend_component_tested')
tools.__file__ = str(ROOT / 'sdk_frontend_component.py')
exec(compile(Path(tools.__file__).read_bytes(), tools.__file__, 'exec'), tools.__dict__)
reader = types.ModuleType('frontend_receipt_tested')
reader.__file__ = str(ROOT / 'lib/stage_receipt_provenance.py')
exec(compile(Path(reader.__file__).read_bytes(), reader.__file__, 'exec'), reader.__dict__)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class Component(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve(); self.source = self.root / 'source'; self.source.mkdir()
        self.git('init', '-q')
        (self.source / '.gitignore').write_text('build/\n')
        for path in tools.SHARED_SOURCE_PATHS:
            target = self.source / path; target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text('// inert shared source fixture\n')
        (self.source / 'docs').mkdir()
        (self.source / 'docs/DECISION_QUEUE.md').write_text('# inert decisions\n')
        identity = self.source / 'targo-trust/src/tool_identity.rs'
        identity.parent.mkdir(parents=True)
        identity.write_text('fn fixed_production() {}\n#[cfg(test)]\nmod tests {\n    // old private assertion\n}\n')
        (self.source / 'Cargo.lock').write_text('# inert root lock\n')
        self.changed = 'crates/trust-resource-controller/src/client.rs'
        (self.source / self.changed).parent.mkdir(parents=True, exist_ok=True)
        (self.source / self.changed).write_text('// inert baseline source\n')
        (self.source / 'crates/trust-resource-controller/Cargo.lock').write_text('# inert witness lock\n')
        for path in ('crates/trust-coordinator/src/coordinator.rs', 'targo-trust/src/pipeline/run.rs'):
            target = self.source / path; target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text('// inert original daemon-client binding\n')
        self.git('add', '.'); self.git('commit', '-qm', 'inert compiler source')
        self.base = self.git('rev-parse', 'HEAD')
        (self.source / self.changed).write_text('// PRIVATE_PRODUCER_SOURCE_NEVER_SHIP\n')
        (self.source / 'docs/DECISION_QUEUE.md').write_text('# inert decisions\nPRIVATE_DECISION_TEXT_NEVER_SHIP\n')
        self.git('add', '.'); self.git('commit', '-qm', 'inert repair source')
        self.repair = self.git('rev-parse', 'HEAD')
        self.stage = self.source / 'build/aarch64-apple-darwin/stage2'; (self.stage / 'bin').mkdir(parents=True)
        for name in ('targo-trust', 'targo', 'trustc', 'rustc', 'rustdoc', 'helper'):
            self.exe(self.stage / 'bin' / name, ('inert non-executed original ' + name).encode())
        relative = lambda name: 'build/aarch64-apple-darwin/stage2/bin/' + name
        row = lambda name: {'path': relative(name), 'sha256': sha((self.stage / 'bin' / name).read_bytes())}
        receipt = {'schema': 'trust.stage-tool-provenance.v2', 'status': 'internal-release-ready',
                   'tool_binding_status': 'ready', 'errors': [], 'path_scope': 'repository-root-relative',
                   'stage_root': 'build/aarch64-apple-darwin/stage2', 'host': 'aarch64-apple-darwin', 'trust_from_trust': True,
                   'bootstrap_lineage': {'schema': 'trust.bootstrap-lineage.v1', 'mode': 'seed',
                       'status': 'trust_from_trust', 'trust_from_trust': True, 'errors': [],
                       'validated_seed': {'materialization_status': 'fresh-from-validated-archives'}},
                   'tools': [dict(row(name), name=name, status='bound', producer_sha256=row(name)['sha256']) for name in ('targo', 'targo-trust')],
                   'compiler': {'path': relative('trustc'), 'compiler_sha256': row('trustc')['sha256'],
                       'source_commit': self.base, 'compatibility_alias': relative('rustc'),
                       'compatibility_alias_sha256': row('rustc')['sha256']},
                   'rustdoc_alias': row('rustdoc'), 'proc_macro_helper': row('helper')}
        self.accepted = self.save('accepted.json', receipt)
        mint = self.stage.parent.parent / 'trust-seed-mint'
        mint.write_text('# inert unexecuted canonical-format fixture\n'
                        'schema=trust-seed-mint-v1\nsource_commit=' + self.base + '\n'
                        'host=aarch64-apple-darwin\nddc_verdict=identical\nself_host_proof=pass\n'
                        'stage2_tree_sha256_pinned_seed=' + '1' * 64 + '\n'
                        'stage2_tree_sha256_ddc_seed=' + '1' * 64 + '\n'
                        'compiler_file=' + row('targo-trust')['sha256'] + ' bin/targo-trust\n')
        self.mint = {'path': str(mint), 'sha256': sha(mint.read_bytes())}
        self.original_receipt = b'{"status":"rejected","scope":"inert original audit preserved"}\n'
        (self.stage / 'tool-provenance.json').write_bytes(self.original_receipt)
        self.compiler = self.root / 'build-compiler/bin/trustc'; self.exe(self.compiler, b'inert build compiler')
        self.artifact = self.root / 'payload/targo-trust'; self.exe(self.artifact, self.image())
        self.witness = self.root / 'witness'; self.exe(self.witness, b'inert separately built transport witness')
        self.compiler_record = {'path': str(self.compiler), 'sha256': sha(self.compiler.read_bytes()), 'source': self.base, 'sysroot': str(self.compiler.parent.parent)}
        source_files = {name: sha((self.source / name).read_bytes()) for name in self.git('diff', '--name-only', self.base, self.repair).splitlines()}
        self.built = {'source_commit': self.repair, 'environment': {'CFG_VER_HASH': self.repair, 'CFG_RELEASE': '1.101.0-dev', 'CFG_TRUST_ORACLE_HOST': '1', 'CFG_TRUST_ORACLE_COMPILER_HASH': self.base, 'CLEAN_OLEAN_REQUIRE_PINNED_LEAN': '1', 'ELAN_HOME': str(self.root / 'private-elan')}, 'version_phase': self.phase('frontend-version'), 'compiler': self.compiler_record, 'target': 'aarch64-apple-darwin',
                      'argv': [str(self.compiler.with_name('targo')), '--unverified', 'build', '--release', '--locked', '--offline', '--manifest-path', str(self.source / 'targo-trust/Cargo.toml'), '--features', ','.join(tools.FEATURES), '--bin', 'targo-trust'],
                      'lock_sha256': sha((self.source / 'Cargo.lock').read_bytes()),
                      'artifact_sha256': sha(self.artifact.read_bytes()), 'retained_inputs_unchanged': True,
                      'phases': [self.phase('frontend-build')]}
        target = self.root / 'candidate-target'; target.mkdir()
        original_generated = self.stage.parent / 'stage2-tools/out/pinned_toolchain_manifest.rs'
        candidate_generated = target / 'release/build/clean-olean/out/pinned_toolchain_manifest.rs'
        for path in (original_generated, candidate_generated):
            path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(b'INERT GENERATED OLEAN DATA, not compiler evidence\n')
        ref = lambda path: {'path': str(path), 'sha256': sha(path.read_bytes()), 'bytes': path.stat().st_size}
        self.built['target_directory'] = str(target)
        self.built['generated_inputs'] = {'clean_olean_manifest': {'original': ref(original_generated), 'candidate': ref(candidate_generated), 'original_mint_sha256': self.mint['sha256']}}
        self.built['compiler_version_phase'] = dict(self.phase('build-compiler-version'), argv=[str(self.compiler), '-vV'])
        self.built['compiler_version_phase']['stdout'] = self.raw('compiler-version.stdout', ('binary: trustc\ncommit-hash: ' + self.base + '\n').encode())
        self.built['retained_compiler_version_phase'] = dict(self.phase('retained-compiler-version'), argv=[str(self.stage / 'bin/trustc'), '-vV'])
        self.built['retained_compiler_version_phase']['stdout'] = self.raw('oracle-compiler-version.stdout', ('binary: trustc\ncommit-hash: ' + self.base + '\nrelease: 1.101.0-dev\n').encode())
        self.built['image_phase'] = dict(self.phase('artifact-code-signature'), argv=['/usr/bin/codesign', '--verify', '--strict', str(self.artifact)])
        self.built['version_phase']['stdout'] = self.raw('version.stdout', ('targo-trust 0.13.0\ntrust-repo-commit-hash: ' + self.repair + '\ntrust-oracle-compiler-commit-hash: ' + self.base + '\ntrust-oracle-compiler-release: 1.101.0-dev\n').encode())
        self.controls = {'source_commit': self.repair, 'source_tree': self.git('rev-parse', 'HEAD^{tree}'), 'source_relation': None, 'controls': sorted(tools.CONTROL_NAMES),
                         'witness': {'path': str(self.witness), 'sha256': sha(self.witness.read_bytes()),
                             'compiler': self.compiler_record, 'features': ['probe-scheduler'],
                             'source_files': source_files, 'target': 'aarch64-apple-darwin',
                             'argv': ['inert-targo', '--unverified', 'build', '--locked', '--offline'],
                             'lock_sha256': sha((self.source / 'crates/trust-resource-controller/Cargo.lock').read_bytes())},
                         'phases': [self.phase('probe-transport-controls')]}
        self.record = {'schema': tools.SCHEMA, 'status': 'prepared', 'name': 'targo-trust',
                       'base': {'compiler_source': self.base, 'host': 'aarch64-apple-darwin',
                           'compiler_sha256': row('trustc')['sha256'], 'original_stage': str(self.stage),
                           'original_mint': self.mint, 'accepted_stage_provenance': self.accepted,
                           'original_targo_trust_sha256': row('targo-trust')['sha256'],
                           'existing_tool_sha256': tools.tool_map(self.stage)},
                       'source': {'root': str(self.source), 'commit': self.repair, 'base': self.base,
                           'tree': self.git('rev-parse', 'HEAD^{tree}'), 'files': source_files},
                       'artifact': {'path': str(self.artifact), 'sha256': sha(self.artifact.read_bytes()),
                           'bytes': self.artifact.stat().st_size, 'system_libraries': ['/usr/lib/libSystem.B.dylib']},
                       'retained_inputs_unchanged': True}
        self.record['identity_qualification'] = self.make_identity_witness()
        self.materialize()

    @staticmethod
    def image(cpu=0x0100000c, library='/usr/lib/libSystem.B.dylib'):
        name = library.encode() + b'\0'
        length = (24 + len(name) + 7) // 8 * 8
        command = struct.pack('<6I', 0xc, length, 24, 0, 0, 0) + name
        command += b'\0' * (length - len(command))
        return struct.pack('<8I', 0xfeedfacf, cpu, 0, 2, 1, length, 0, 0) + command

    def git(self, *args):
        return subprocess.check_output(['git', '-c', 'core.hooksPath=/dev/null', '-c', 'user.name=Inert fixture', '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false', '-C', str(self.source), *args], text=True).strip()

    def exe(self, path, raw):
        path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(raw); path.chmod(0o755)

    def save(self, name, value):
        path = self.root / name; path.write_text(json.dumps(value, sort_keys=True) + '\n')
        return {'path': str(path), 'sha256': sha(path.read_bytes())}

    def raw(self, name, content):
        path = self.root / name; path.write_bytes(content)
        return {'path': str(path), 'sha256': sha(content)}

    def phase(self, name):
        return {'name': name, 'exit': 0, 'stdout': self.raw(name + '.stdout', b'inert fixture raw output'), 'stderr': self.raw(name + '.stderr', b'')}

    def make_identity_witness(self):
        root = self.root / 'identity-source'
        subprocess.run(['git', '-c', 'core.hooksPath=/dev/null', 'clone', '-q', '--no-hardlinks', str(self.source), str(root)], check=True)
        git = lambda *a: subprocess.check_output(['git', '-c', 'core.hooksPath=/dev/null', '-c', 'user.name=Inert fixture', '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false', '-C', str(root), *a])
        source = git('rev-parse', 'HEAD').decode().strip(); tree = git('rev-parse', 'HEAD^{tree}').decode().strip()
        harness = self.root / 'identity-harness'; self.exe(harness, b'inert identity witness image')
        context = {'schema': 'trust.frontend-identity-witness.v2',
                   'harness_source': {'root': str(root), 'commit': source, 'tree': tree,
                        'files': {name: sha((root / name).read_bytes()) for name in git('diff', '--name-only', self.base, source).decode().splitlines()}},
                   'subject': {'source_commit': self.repair, 'tree': self.record['source']['tree'],
                        'artifact': self.record['artifact']},
                   'compiler': self.compiler_record, 'environment': self.built['environment'],
                   'features': list(tools.FEATURES), 'target': self.built['target']}
        phases = []
        for name in ('oracle-binding-controls', 'frontend-owning-tippy', 'artifact-system-libraries', 'artifact-code-signature'):
            item = self.phase(name); item['phase'] = item.pop('name'); item['argv'] = ['inert-witness', name]
            phases.append(item)
        output = json.dumps({'reason': 'compiler-artifact', 'target': {'name': 'targo-trust'}, 'profile': {'test': True}, 'executable': str(harness)}) + '\n'
        output += '\n'.join((*tools.IDENTITY_CONTROLS, 'test result: ok. 5 passed; 0 failed'))
        phases[0]['stdout'] = self.raw('identity-controls.stdout', output.encode())
        result = {'exit': 0, 'context': self.save('identity-context.json', context), 'phases': phases,
                  'harness': {'path': str(harness), 'sha256': sha(harness.read_bytes()), 'bytes': harness.stat().st_size},
                  'subject_artifact': self.record['artifact'], 'source_unchanged': True, 'subject_unchanged': True,
                  'scope': 'Inert fixture metadata; no actual code was compiled or executed.'}
        review = {'schema': 'trust.identity-harness-source-review.v2', 'clear': True,
                  'all_source_lock_feature_inputs_and_gitlinks_identical': True,
                  'artifact_source': self.repair, 'artifact_sha256': sha(self.artifact.read_bytes()),
                  'harness_source': source, 'source_tree': tree,
                  'source_readset_sha256': sha(json.dumps(self.record['source']['files'], sort_keys=True, separators=(',', ':')).encode())}
        return {'result': self.save('identity-result.json', result), 'source_review': self.save('identity-review.json', review)}

    def materialize(self):
        self.built['context'] = self.save('build-context.json', {'source_commit': self.record['source']['commit'], 'source_tree': self.record['source']['tree'], 'files': self.record['source']['files'], 'environment': self.built['environment'], 'target': self.built['target'], 'features': list(tools.FEATURES), 'compiler': self.compiler_record, 'target_directory': self.built['target_directory']})
        self.record['build_receipt'] = self.save('build.json', self.built)
        self.record['transport_qualification'] = self.save('controls.json', self.controls)
        ref = self.save('component.json', self.record); self.path = Path(ref['path']); self.expected = ref['sha256']

    def validate(self):
        return tools.prepared(self.path, self.expected, self.source, self.stage, self.base)

    def destination(self, name='new-seal', *, hardlinks=False):
        dest = self.root / name
        shutil.copytree(self.stage, dest, copy_function=os.link if hardlinks else shutil.copy2)
        reader.copy_selected_receipt(self.stage, self.base, self.source, Path(self.accepted['path']), self.accepted['sha256'], dest)
        return dest

    def install(self, dest=None):
        dest = self.destination() if dest is None else dest
        tools.install(self.path, self.expected, self.source, self.stage, self.base, dest)
        return dest

    def doctor(self, dest, *, actual_exit=0, ready=True, trust_verify=True, json_transport=True, wrong_subject=False):
        subject = self.root / 'foreign' if wrong_subject else dest
        report = {'ready': ready, 'compiler': {'path': str(subject / 'bin/trustc'),
                    'linked_toolchain_path': str(subject / 'bin/trustc'), 'discovery_source': 'sibling_trustc',
                    'linked_toolchain_status': 'visible', 'trust_verify': trust_verify, 'json_transport': json_transport,
                    'daily_driver': {'ready': True, 'linked_targo_path': str(subject / 'bin/targo'), 'linked_targo_trust_path': str(subject / 'bin/targo-trust')}}}
        stdout = dest / tools.DETAILS / 'candidate.stdout'; stdout.write_text(json.dumps(report))
        stderr = dest / tools.DETAILS / 'candidate.stderr'; stderr.write_bytes(b'')
        context = dest / tools.DETAILS / 'candidate.context.json'
        context.write_text(json.dumps({'actual_exit': actual_exit, 'argv': [str(dest / 'bin/targo'), 'trust', 'doctor', '--format', 'json'], 'cargo_home': str(self.root / 'inert-private-home'), 'initially_empty': True, 'cache_preparation': 'inert fixture, no real invocation'}))
        return tools.qualify(dest, self.base, self.expected, actual_exit, stdout, stderr, context)

    def test_prepared_is_not_runtime_qualification_and_default_reader_refuses_new_bytes(self):
        self.validate(); dest = self.install()
        with self.assertRaises(FileNotFoundError): tools.installed_binding(dest, self.base, self.expected)
        with self.assertRaises(reader.StageReceiptError): reader.lines(dest, self.base)
        self.assertEqual((self.stage / 'tool-provenance.json').read_bytes(), self.original_receipt)

    def test_atomic_copy_retains_original_hardlink_and_other_tools_then_explicit_qualified_reader(self):
        original = tools.tool_map(self.stage); dest = self.destination(hardlinks=True)
        before_inode = (self.stage / 'bin/targo-trust').stat().st_ino
        self.install(dest); self.doctor(dest)
        self.assertEqual(tools.tool_map(self.stage), original)
        self.assertNotEqual((dest / 'bin/targo-trust').stat().st_ino, before_inode)
        self.assertEqual((dest / 'tool-provenance.json').read_bytes(), Path(self.accepted['path']).read_bytes())
        lines = reader.lines(dest, self.base, frontend_component_path=dest / tools.RECORD, frontend_component_sha256=self.expected)
        self.assertIn('stage_frontend_source=' + self.repair, lines)
        self.assertIn('stage_receipt_sha256=' + self.accepted['sha256'], lines)
        self.assertEqual(set(tools.tool_map(dest)), set(original))
        self.assertIn('stage_receipt_files_verified=5', lines)
        self.assertIn('stage_frontend_original_entry=attested-replaced-not-installed', lines)
        self.assertFalse((dest / tools.DETAILS / 'source').exists())
        self.assertFalse((dest / tools.DETAILS / 'original-targo-trust').exists())
        for item in (dest / tools.DETAILS).rglob('*'):
            if item.is_file():
                self.assertFalse(item.stat().st_mode & 0o111)
                self.assertNotIn(b'PRIVATE_PRODUCER_SOURCE_NEVER_SHIP', item.read_bytes())
                self.assertNotIn(b'PRIVATE_DECISION_TEXT_NEVER_SHIP', item.read_bytes())

    def test_wrong_source_compiler_target_artifact_and_witness_refuse(self):
        variants = [('base', 'compiler_source', '0' * 40), ('base', 'host', 'wrong-host'), ('artifact', 'sha256', '0' * 64), ('source', 'tree', '0' * 40)]
        for section, key, value in variants:
            with self.subTest(section=section, key=key):
                previous = self.record[section][key]; self.record[section][key] = value; self.materialize()
                with self.assertRaises((tools.Refusal, reader.StageReceiptError)): self.validate()
                self.record[section][key] = previous
        self.controls['witness']['source_files'] = {}; self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'readset'): self.validate()

    def test_unbound_or_noncanonical_build_metadata_refuses(self):
        for key, value in (('CFG_VER_HASH', 'unbound'), ('CFG_TRUST_ORACLE_HOST', '0'), ('CFG_TRUST_ORACLE_COMPILER_HASH', '0' * 40)):
            with self.subTest(key=key):
                previous = self.built['environment'][key]; self.built['environment'][key] = value; self.materialize()
                with self.assertRaisesRegex(tools.Refusal, r'identity.*(?:environment|configuration)'): self.validate()
                self.built['environment'][key] = previous
        self.built['version_phase']['stdout'] = self.raw('wrong-version.stdout', b'targo-trust 0.13.0\ntrust-repo-commit-hash: unbound\n')
        self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'unbound'): self.validate()

    def test_nonactual_build_exit_and_missing_controls_refuse(self):
        for value in (True, None, 1):
            with self.subTest(value=value):
                self.built['phases'][0]['exit'] = value; self.materialize()
                with self.assertRaisesRegex(tools.Refusal, 'phase'): self.validate()
        self.built['phases'][0]['exit'] = 0; self.controls['controls'].pop(); self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'controls'): self.validate()

    def test_mismatch_or_symlink_refuses_before_any_destination_mutation(self):
        for kind in ('mismatch', 'symlink', 'other-tool'):
            with self.subTest(kind=kind):
                dest = self.destination(kind)
                target = dest / 'bin' / ('trustc' if kind == 'other-tool' else 'targo-trust')
                if kind == 'symlink': target.unlink(); target.symlink_to(self.stage / 'bin/targo-trust')
                else: target.write_bytes(b'unqualified different bytes')
                before = {str(x.relative_to(dest)): x.read_bytes() for x in dest.rglob('*') if x.is_file()}
                with self.assertRaises((tools.Refusal, OSError)): self.install(dest)
                self.assertFalse((dest / tools.DETAILS).exists())
                self.assertEqual(before, {str(x.relative_to(dest)): x.read_bytes() for x in dest.rglob('*') if x.is_file()})

    def test_destination_overlap_refuses_and_original_is_unchanged(self):
        dest = self.stage / 'nested-copy'; dest.mkdir()
        before = tools.tool_map(self.stage)
        with self.assertRaisesRegex(tools.Refusal, 'overlaps'): self.install(dest)
        self.assertEqual(tools.tool_map(self.stage), before)
        self.assertEqual(list(dest.iterdir()), [])

    def test_doctor_false_nonbool_nonzero_or_foreign_never_qualifies(self):
        for i, changes in enumerate(({'ready': False}, {'ready': 1}, {'trust_verify': False}, {'json_transport': 1}, {'actual_exit': 1}, {'wrong_subject': True})):
            with self.subTest(changes=changes):
                dest = self.install(self.destination('refused-' + str(i)))
                with self.assertRaises(tools.Refusal): self.doctor(dest, **changes)
                self.assertFalse((dest / tools.QUALIFIED).exists())

    def test_tampered_other_tool_or_raw_doctor_refuses_after_qualification(self):
        dest = self.install(); self.doctor(dest); tools.installed_binding(dest, self.base, self.expected)
        (dest / 'bin/trustc').write_bytes(b'different compiler')
        with self.assertRaises(tools.Refusal): tools.installed_binding(dest, self.base, self.expected)
        (dest / 'bin/trustc').write_bytes((self.stage / 'bin/trustc').read_bytes())
        (dest / tools.DETAILS / 'doctor.stdout').write_bytes(b'{}')
        with self.assertRaisesRegex(tools.Refusal, 'raw hash'): tools.installed_binding(dest, self.base, self.expected)

    def test_native_pair_never_acquires_authority_from_old_frontend_doctor(self):
        dest = self.install(); self.doctor(dest)
        historical = tools.installed_binding(dest, self.base, self.expected)
        (dest / 'bin/cargo').write_bytes(b'inert new native pair')
        (dest / 'bin/targo').write_bytes(b'inert new native pair')
        with self.assertRaisesRegex(tools.Refusal, 'installed tools changed'):
            tools.installed_binding(dest, self.base, self.expected)
        with self.assertRaises((tools.Refusal, OSError)):
            tools.installed_binding_with_native_targo(dest, self.base, self.expected, '0' * 64)
        # Historical qualification was not rewritten or converted to a new whole-stage grade.
        value = json.loads((dest / tools.QUALIFIED).read_bytes())
        self.assertEqual(sha((dest / tools.QUALIFIED).read_bytes()), historical['qualification_sha256'])
        self.assertNotEqual(value['tool_sha256']['targo'], sha((dest / 'bin/targo').read_bytes()))

    def advance_frontend_after_witness(self, path, text, kind='test-only-and-documentation'):
        old = self.repair
        before = self.git('show', old + ':' + path).encode() + b'\n'
        target = self.source / path; target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text); self.git('add', path); self.git('commit', '-qm', 'inert later frontend source')
        self.repair = self.git('rev-parse', 'HEAD')
        self.record['source']['commit'] = self.repair
        self.record['source']['tree'] = self.git('rev-parse', 'HEAD^{tree}')
        changed = self.git('diff', '--name-only', self.base, self.repair).splitlines()
        self.record['source']['files'] = {name: sha((self.source / name).read_bytes()) for name in changed}
        self.built['source_commit'] = self.repair
        self.built['environment']['CFG_VER_HASH'] = self.repair
        self.built['version_phase']['stdout'] = self.raw('version.stdout', ('targo-trust 0.13.0\ntrust-repo-commit-hash: ' + self.repair + '\ntrust-oracle-compiler-commit-hash: ' + self.base + '\ntrust-oracle-compiler-release: 1.101.0-dev\n').encode())
        relation = {'schema': 'trust.sdk-frontend-source-relation.v1', 'witness_source': old,
                    'frontend_source': self.repair, 'base': self.base,
                    'shared_files': {name: sha((self.source / name).read_bytes()) for name in tools.SHARED_SOURCE_PATHS},
                    'changed_files': {path: {'before_sha256': sha(before), 'after_sha256': sha(target.read_bytes())}},
                    'reviewed_change_kind': kind, 'reviewer': 'inert fixture reviewer'}
        self.controls['source_relation'] = self.save('source-relation.json', relation)
        shutil.rmtree(self.root / 'identity-source')
        self.record['identity_qualification'] = self.make_identity_witness()
        self.materialize()

    def test_distinct_reviewed_witness_source_keeps_actual_identity_and_shared_bytes(self):
        original_witness = self.controls['source_commit']
        self.advance_frontend_after_witness('docs/DECISION_QUEUE.md', '# inert decisions\n\nTest-only source note.\n')
        self.assertNotEqual(original_witness, self.record['source']['commit'])
        self.validate(); dest = self.install(); self.doctor(dest)
        tools.installed_binding(dest, self.base, self.expected)
        copied = json.loads((dest / tools.DETAILS / 'transport.json').read_bytes())
        self.assertEqual(copied['source_commit'], original_witness)
        self.assertNotEqual(copied['witness']['sha256'], self.record['artifact']['sha256'])

    def test_review_cannot_license_changed_shared_production(self):
        self.advance_frontend_after_witness('crates/trust-resource-controller/src/client/sdk.rs', '// changed owning production\n')
        with self.assertRaisesRegex(tools.Refusal, 'owning production'):
            self.validate()

    def test_promoter_refuses_partial_duplicate_or_unused_frontend_selector_before_tools(self):
        script = ROOT / 'promote-toolchain.sh'
        for args in (
            ['--frontend-component', str(self.path)],
            ['--frontend-component', str(self.path), '--frontend-component', str(self.path)],
            ['--gate-only', '--frontend-component', str(self.path), '--frontend-component-sha256', self.expected],
        ):
            with self.subTest(args=args):
                result = subprocess.run(['/bin/bash', str(script), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                self.assertEqual(result.returncode, 3, result.stderr)
                self.assertIn(b'frontend', result.stderr)

    def test_actual_image_arch_library_and_exact_feature_recipe_refuse(self):
        for i, payload in enumerate((self.image(cpu=0x01000007), self.image(library='@rpath/foreign.dylib'))):
            with self.subTest(i=i):
                self.artifact.write_bytes(payload)
                self.record['artifact']['sha256'] = sha(payload); self.record['artifact']['bytes'] = len(payload)
                self.built['artifact_sha256'] = sha(payload)
                self.materialize()
                with self.assertRaisesRegex(tools.Refusal, 'architecture|non-system'): self.validate()
        self.artifact.write_bytes(self.image())
        self.record['artifact']['sha256'] = sha(self.artifact.read_bytes()); self.record['artifact']['bytes'] = self.artifact.stat().st_size
        self.built['artifact_sha256'] = self.record['artifact']['sha256']
        self.built['argv'][self.built['argv'].index('--features') + 1] = ','.join(tools.FEATURES[:-1])
        self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'five-feature'): self.validate()

    def test_generated_lean_drift_or_borrowed_output_cannot_be_prepared(self):
        row = self.built['generated_inputs']['clean_olean_manifest']
        path = Path(row['candidate']['path']); path.write_bytes(b'INERT EMPTY generated table\n')
        row['candidate'] = {'path': str(path), 'sha256': sha(path.read_bytes()), 'bytes': path.stat().st_size}
        self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'olean inputs differ'): self.validate()
        row['candidate'] = dict(row['original']); self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'producer root'): self.validate()

    def test_generated_reference_uses_accepted_producer_not_archive_or_caller_ancestor(self):
        self.validate()
        original = self.built['generated_inputs']['clean_olean_manifest']['original']
        foreign = self.stage.parent.parent / 'dist/pinned_toolchain_manifest.rs'
        foreign.parent.mkdir(); foreign.write_bytes(Path(original['path']).read_bytes())
        self.built['generated_inputs']['clean_olean_manifest']['original'] = {'path': str(foreign), 'sha256': sha(foreign.read_bytes()), 'bytes': foreign.stat().st_size}
        self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'producer root'): self.validate()
        self.built['generated_inputs']['clean_olean_manifest']['original'] = original
        mint = Path(self.mint['path']); mint.write_bytes(mint.read_bytes() + ('host=aarch64-apple-darwin\n').encode())
        self.mint['sha256'] = sha(mint.read_bytes())
        self.built['generated_inputs']['clean_olean_manifest']['original_mint_sha256'] = self.mint['sha256']
        self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'duplicated'): self.validate()

    def test_ambient_git_replacement_and_graft_cannot_change_claimed_objects(self):
        original = self.repair
        (self.source / self.changed).write_text('// replacement object must not become authority\n')
        self.git('add', self.changed); self.git('commit', '-qm', 'inert replacement object')
        forged = self.git('rev-parse', 'HEAD')
        self.git('checkout', '-q', '--detach', original)
        self.git('replace', original, forged)
        (self.source / '.git/info/grafts').write_text(original + '\n')
        fake_bin = self.root / 'ambient-bin'; fake_bin.mkdir()
        marker = self.root / 'ambient-git-ran'
        self.exe(fake_bin / 'git', ('#!/bin/sh\ntouch "' + str(marker) + '"\nexit 91\n').encode())
        with mock.patch.dict(os.environ, {'PATH': str(fake_bin), 'GIT_DIR': '/nonexistent/redirect', 'GIT_WORK_TREE': '/nonexistent/worktree', 'GIT_CONFIG_COUNT': '1', 'GIT_CONFIG_KEY_0': 'core.fsmonitor', 'GIT_CONFIG_VALUE_0': '/nonexistent/execute'}):
            self.validate()
        self.assertFalse(marker.exists())

    def test_v2_identity_witness_cannot_reuse_a_historical_subject(self):
        self.artifact.write_bytes(self.image() + b'\0corrected-generated-inputs')
        self.record['artifact']['sha256'] = sha(self.artifact.read_bytes())
        self.record['artifact']['bytes'] = self.artifact.stat().st_size
        self.built['artifact_sha256'] = self.record['artifact']['sha256']; self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'subject differs'): self.validate()

    def test_identity_control_incomplete_or_retargeted_source_cannot_be_prepared(self):
        ref = self.record['identity_qualification']['result']
        value = json.loads(Path(ref['path']).read_bytes()); value['exit'] = 101
        self.record['identity_qualification']['result'] = self.save('failed-identity.json', value); self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'finish successfully'): self.validate()

    def test_v2_retained_release_observation_is_exact_and_not_the_build_compiler(self):
        self.validate()
        original = copy.deepcopy(self.built['retained_compiler_version_phase'])
        for content in (
            b'binary: trustc\ncommit-hash: ' + self.base.encode() + b'\n',
            b'binary: rustc\ncommit-hash: ' + self.base.encode() + b'\nrelease: 1.101.0-dev\n',
            b'binary: trustc\nbinary: trustc\ncommit-hash: ' + self.base.encode() + b'\nrelease: 1.101.0-dev\n',
            b'binary: trustc\ncommit-hash: ' + b'f' * 40 + b'\nrelease: 1.101.0-dev\n',
            b'binary: trustc\ncommit-hash: ' + self.base.encode() + b'\nrelease: 0.13.0\n',
            b'binary: trustc\ncommit-hash: ' + self.base.encode() + b'\nrelease: 1.101.0-dev\nrelease: 1.101.0-dev\n',
        ):
            with self.subTest(content=content):
                self.built['retained_compiler_version_phase'] = copy.deepcopy(original)
                self.built['retained_compiler_version_phase']['stdout'] = self.raw('oracle-compiler-version.stdout', content)
                self.materialize()
                with self.assertRaises(tools.Refusal): self.validate()

    def test_retained_release_requires_the_exact_delimiter(self):
        raw = ('binary: trustc\ncommit-hash: ' + self.base + '\nrelease:X1.101.0-dev\n').encode()
        with self.assertRaises(tools.Refusal): tools.retained_compiler_identity(raw, self.base)

    def test_v2_scope_adds_only_explicit_reviewed_daemon_owner_paths(self):
        self.assertEqual(len(tools.SOURCE_PATHS), 15)
        self.advance_frontend_after_witness('crates/trust-coordinator/src/coordinator.rs', '// reviewed explicit expected-build companion\n', 'reviewed-compile-time-oracle-binding')
        self.validate(); dest = self.install(); self.doctor(dest)
        tools.installed_binding(dest, self.base, self.expected)

    def test_v2_does_not_automatically_accept_v1_or_incomplete_release_controls(self):
        self.record['schema'] = 'trust.sdk-frontend-component.v1'; self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'wrong prepared'): self.validate()
        self.record['schema'] = tools.SCHEMA
        value = json.loads(Path(self.record['identity_qualification']['result']['path']).read_bytes())
        output = value['phases'][0]['stdout']
        raw = Path(output['path']).read_bytes().replace(b'5 passed; 0 failed', b'3 passed; 0 failed')
        value['phases'][0]['stdout'] = self.raw('identity-controls.stdout', raw)
        self.record['identity_qualification']['result'] = self.save('identity-incomplete.json', value)
        self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'incomplete'): self.validate()

    def test_v2_frontend_release_and_copied_observation_cannot_diverge(self):
        current = self.built['version_phase']['stdout']
        content = Path(current['path']).read_bytes().replace(b'trust-oracle-compiler-release: 1.101.0-dev', b'trust-oracle-compiler-release: 0.13.0')
        self.built['version_phase']['stdout'] = self.raw('version.stdout', content)
        self.materialize()
        with self.assertRaisesRegex(tools.Refusal, 'oracle release'): self.validate()

    def test_duplicate_json_and_partial_or_foreign_reader_selector_refuse(self):
        self.path.write_text('{"schema":"x","schema":"y"}')
        with self.assertRaisesRegex(tools.Refusal, 'duplicate'): tools.document(self.path)
        self.materialize(); dest = self.install(); self.doctor(dest)
        for values in ({'frontend_component_sha256': self.expected}, {'frontend_component_path': self.path, 'frontend_component_sha256': self.expected}):
            with self.subTest(values=values):
                with self.assertRaises(reader.StageReceiptError): reader.lines(dest, self.base, **values)
        (dest / 'tool-provenance.json').unlink()
        self.assertEqual(reader.lines(dest, self.base), ['stage_receipt=absent'])
        with self.assertRaisesRegex(reader.StageReceiptError, 'original stage receipt'):
            reader.lines(dest, self.base, frontend_component_path=dest / tools.RECORD, frontend_component_sha256=self.expected)


if __name__ == '__main__': unittest.main()
