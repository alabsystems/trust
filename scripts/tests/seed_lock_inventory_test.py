"""Synthetic committed-source lock selection; no Cargo, compiler or release runs."""
import ast
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import tarfile
import tempfile
import time
import types
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]

class Loader:
    def __init__(self):
        self.modules = {}
    def module(self, name, path):
        path = Path(path)
        if path not in self.modules:
            module = types.ModuleType(name)
            module.__file__, module.__trust_source_loader__ = str(path), self
            self.modules[path] = module
            exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)
        return self.modules[path]

A = Loader().module('lock_inventory_subject', SCRIPTS / 'seed_input_archives.py')

class LockInventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.end = time.monotonic() + 20
        for name in ('run', 'Popen', 'check_output', 'check_call', 'call'):
            p = patch.object(subprocess, name, side_effect=AssertionError('external process forbidden'))
            p.start()
            self.addCleanup(p.stop)
        text = (SCRIPTS / 'recreate_bootstrap.py').read_text()
        graph = next(n for n in ast.parse(text).body if isinstance(n, ast.ClassDef)
                     and n.name == '_Stage0ManifestGraph')
        self.write('scripts/recreate_bootstrap.py', ast.get_source_segment(text, graph))
        for directory in ('', 'library', 'src/bootstrap'):
            self.write(str(Path(directory) / 'Cargo.toml'), '[workspace]\nmembers = []\n')
            self.write(str(Path(directory) / 'Cargo.lock'), 'version = 3\n')
        self.write('Cargo.lock', self.lock('real', 'a'))

    def write(self, name, text):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        return p

    def lock(self, name, digit):
        return ('version = 3\n[[package]]\nname = "' + name + '"\nversion = "1.0.0"\n'
                'source = "registry+https://github.com/rust-lang/crates.io-index"\n' +
                ('' if digit is None else 'checksum = "' + digit * 64 + '"\n'))

    def snapshot(self):
        rows = []
        for p in sorted(self.root.rglob('*')):
            if p.is_symlink():
                rows.append({'path':p.relative_to(self.root).as_posix(), 'kind':'symlink',
                             'mode':stat.S_IMODE(p.lstat().st_mode), 'target':os.readlink(p)})
            elif p.is_file():
                raw = p.read_bytes()
                rows.append({'path':p.relative_to(self.root).as_posix(), 'kind':'file',
                             'mode':stat.S_IMODE(p.stat().st_mode), 'bytes':len(raw),
                             'sha256':hashlib.sha256(raw).hexdigest()})
        return {'source':{'.':rows}, 'orchestration':{'.':rows}}

    def pins(self, rows=None):
        return A.lock_checksums({'source':self.root, 'orchestration':self.root},
                                rows or self.snapshot(), self.end)

    def test_committed_unreferenced_fixture_cannot_poison_production_lock(self):
        self.write('tests/fixture/Cargo.toml', '[workspace]\n')
        self.write('tests/fixture/Cargo.lock', self.lock('fixture', None))
        self.assertEqual(self.pins(), {'real-1.0.0':'a'*64})

    def test_selected_lock_missing_checksum_still_refuses(self):
        self.write('Cargo.lock', self.lock('real', None))
        with self.assertRaisesRegex(ValueError, 'no exact checksum'):
            self.pins()

    def test_selected_nonhex_checksum_still_refuses(self):
        self.write('Cargo.lock', self.lock('real', 'z'))
        with self.assertRaisesRegex(ValueError, 'no exact checksum'):
            self.pins()

    def test_inconclusive_selected_manifest_graph_refuses(self):
        self.write('library/Cargo.toml', 'not TOML')
        with self.assertRaisesRegex(RuntimeError, 'inconclusive'):
            self.pins()

    def test_selected_conflicting_checksums_still_refuse(self):
        self.write('library/Cargo.lock', self.lock('real', 'b'))
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            self.pins()

    def test_new_source_declared_workspace_is_required(self):
        self.write('src/bootstrap/src/core/metadata.rs', 'collect_metadata("new-tool/Cargo.toml");')
        self.write('new-tool/Cargo.toml', '[workspace]\nmembers = []\n')
        with self.assertRaisesRegex(RuntimeError, 'no committed lockfile'):
            self.pins()
        self.write('new-tool/Cargo.lock', self.lock('new-tool', 'b'))
        self.assertEqual(self.pins()['new-tool-1.0.0'], 'b'*64)

    def test_untracked_glob_member_is_not_a_source_authority(self):
        self.write('Cargo.toml', '[workspace]\nmembers = ["members/*"]\n')
        self.write('members/real/Cargo.toml', '[package]\nname="member"\nversion="1.0.0"\n')
        rows = self.snapshot()
        self.write('members/untracked/Cargo.toml', 'not TOML')
        self.write('members/untracked/Cargo.lock', self.lock('poison', None))
        self.assertEqual(self.pins(rows), {'real-1.0.0':'a'*64})
        view = A._CommittedSourceView(self.root, rows['source'], self.end)
        self.assertEqual(view.glob(self.root, 'members/*'), [self.root/'members/real'])

    def test_glob_star_does_not_cross_components(self):
        self.write('members/real/Cargo.toml', '[workspace]\n')
        self.write('members/nested/deep/Cargo.toml', '[workspace]\n')
        view = A._CommittedSourceView(self.root, self.snapshot()['source'], self.end)
        self.assertNotIn(self.root/'members/nested/deep', view.glob(self.root, 'members/*'))
        self.assertIn(self.root/'members/nested/deep', view.glob(self.root, 'members/**'))

    def test_changed_selected_manifest_cannot_choose_other_locks(self):
        rows = self.snapshot()
        self.write('Cargo.toml', '[workspace]\nmembers=["injected"]\n')
        with self.assertRaisesRegex(ValueError, 'changed during selection'):
            self.pins(rows)

    def test_original_endpoint_is_preserved(self):
        self.end = time.monotonic() - 1
        with self.assertRaisesRegex(ValueError, 'deadline'):
            self.pins()

    def test_committed_self_link_selects_actual_manifest(self):
        self.write('linked/Cargo.toml', '[workspace]\nmembers = []\n')
        self.write('linked/Cargo.lock', self.lock('linked', 'b'))
        (self.root/'first-party').mkdir()
        (self.root/'first-party/trust').symlink_to('..')
        self.write('src/bootstrap/src/core/metadata.rs',
                   'collect_metadata("first-party/trust/linked/Cargo.toml");')
        self.assertEqual(self.pins()['linked-1.0.0'], 'b'*64)
        rows = self.snapshot()
        (self.root/'first-party/trust').unlink()
        (self.root/'first-party/trust').symlink_to('../library')
        with self.assertRaisesRegex(ValueError, 'link changed'):
            self.pins(rows)

    def test_captured_alias_glob_matches_default_component_semantics(self):
        self.write('members/one/Cargo.toml', '[package]\nname="one"\nversion="1.0.0"\n')
        self.write('members/one/deep/Cargo.toml', '[package]\nname="deep"\nversion="1.0.0"\n')
        (self.root/'alias').symlink_to('members')
        view = A._CommittedSourceView(self.root, self.snapshot()['source'], self.end)
        expected = sorted(p.resolve() for p in self.root.glob('alias/*') if p.is_dir())
        self.assertEqual(view.glob(self.root, 'alias/*'), expected)
        self.assertNotIn(self.root/'members/one/deep', view.glob(self.root, 'alias/*'))
        self.assertIn(self.root/'members/one/deep', view.glob(self.root, 'alias/**'))

    def test_unbound_intermediate_directory_cannot_be_erased(self):
        view = A._CommittedSourceView(self.root, self.snapshot()['source'], self.end)
        with self.assertRaisesRegex(ValueError, 'unbound directory'):
            view.path(self.root/'unrecorded/../Cargo.toml')

    def test_link_resolution_honors_parent_after_bound_link(self):
        self.write('real/inner/keep', 'x')
        self.write('real/value', 'right')
        self.write('value', 'wrong')
        (self.root/'alias').symlink_to('real/inner')
        (self.root/'entry').symlink_to('alias/../value')
        view = A._CommittedSourceView(self.root, self.snapshot()['source'], self.end)
        self.assertEqual(view.path(self.root/'entry'), self.root/'real/value')

    def test_unrecorded_recipe_link_and_link_cycle_refuse(self):
        self.write('src/bootstrap/src/core/metadata.rs', 'collect_metadata("alias/Cargo.toml");')
        rows = self.snapshot()
        (self.root/'alias').symlink_to('library')
        with self.assertRaisesRegex(RuntimeError, 'absent from committed'):
            self.pins(rows)
        (self.root/'alias').unlink()
        (self.root/'alias').symlink_to('alias')
        with self.assertRaisesRegex(ValueError, 'link depth'):
            self.pins()

    def test_default_filesystem_and_captured_recipe_selection_agree(self):
        rows = self.snapshot()
        view = A._CommittedSourceView(self.root, rows['source'], self.end)
        ordinary = A.dependencies.stage0_bootstrap_manifest_roots(self.root)
        captured = A.dependencies.stage0_bootstrap_manifest_roots(self.root, source_view=view)
        self.assertEqual(ordinary, captured)
        left = A.dependencies._source_inputs(self.root, ordinary, {}, source_only=True)
        right = A.dependencies._source_inputs(self.root, captured, {}, source_only=True,
                                              source_view=view)
        self.assertEqual(left, right)

class RegistrySourcesTests(unittest.TestCase):
    def setUp(self):
        for name in ('run', 'Popen', 'check_output', 'check_call', 'call'):
            guarded = patch.object(subprocess, name, side_effect=AssertionError('external process forbidden'))
            guarded.start()
            self.addCleanup(guarded.stop)

    def write(self, path, data, mode=0o644):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        path.chmod(mode)

    def make_archive(self, path, members, mode='w:gz'):
        path.parent.mkdir(parents=True, exist_ok=True)
        with tarfile.open(path, mode) as archive:
            for name, data, permissions in members:
                info = tarfile.TarInfo(name)
                info.mode = permissions
                if data is None:
                    info.type = tarfile.DIRTYPE
                    archive.addfile(info)
                else:
                    info.size = len(data)
                    archive.addfile(info, io.BytesIO(data))
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def ordinary_registry(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        cargo = Path(temporary.name).resolve()/'cargo'
        source = cargo/'registry/src/provider/p-1.0.0'
        self.write(source/'lib.rs',b'original')
        self.write(source/'.cargo-ok',b'{"v":1}')
        sha = self.make_archive(cargo/'registry/cache/provider/p-1.0.0.crate',
            [('p-1.0.0',None,0o755),('p-1.0.0/lib.rs',b'original',0o644)],'w:gz')
        return cargo,source,sha

    def test_registry_ordinary_extraction_is_authenticated_without_cache_writes(self):
        cargo,source,sha = self.ordinary_registry()
        before = A.records.tree(cargo,time.monotonic()+10)
        result = A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)
        self.assertEqual(result['verified_packages'],1)
        self.assertFalse(result['complete_used_dependency_universe'])
        self.assertEqual(A.records.tree(cargo,time.monotonic()+10),before)
        self.assertFalse(os.path.lexists(source/'.cargo-checksum.json'))

    def test_registry_ordinary_extraction_requires_a_completion_marker(self):
        cargo,source,sha = self.ordinary_registry()
        (source/'.cargo-ok').unlink()
        with self.assertRaisesRegex(ValueError,'no supported extraction marker'):
            A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)

    def test_registry_ordinary_extraction_still_checks_every_payload(self):
        for change,reason in (('bytes','archive payload differs'),('missing','archive payload differs'),
                              ('mode','mode/literal link'),('extra','unbound extra'),
                              ('archive','archive differs'),('pin','archive differs')):
            with self.subTest(change=change):
                cargo,source,sha = self.ordinary_registry()
                if change == 'bytes':
                    self.write(source/'lib.rs',b'tampered')
                elif change == 'missing':
                    (source/'lib.rs').unlink()
                elif change == 'mode':
                    (source/'lib.rs').chmod(0o755)
                elif change == 'extra':
                    self.write(source/'extra.rs',b'unbound')
                elif change == 'archive':
                    (cargo/'registry/cache/provider/p-1.0.0.crate').write_bytes(b'changed archive')
                else:
                    sha = '0'*64
                with self.assertRaisesRegex(ValueError,reason):
                    A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)

    def test_registry_ordinary_extraction_preserves_literal_link_checks(self):
        cargo,source,_ = self.ordinary_registry()
        (source/'alias').symlink_to('lib.rs')
        archive = cargo/'registry/cache/provider/p-1.0.0.crate'
        with tarfile.open(archive,'w:gz') as bundle:
            top = tarfile.TarInfo('p-1.0.0')
            top.type,top.mode = tarfile.DIRTYPE,0o755
            bundle.addfile(top)
            member = tarfile.TarInfo('p-1.0.0/lib.rs')
            member.mode,member.size = 0o644,len(b'original')
            bundle.addfile(member,io.BytesIO(b'original'))
            link = tarfile.TarInfo('p-1.0.0/alias')
            link.type,link.linkname,link.mode = tarfile.SYMTYPE,'lib.rs',stat.S_IMODE((source/'alias').lstat().st_mode)
            bundle.addfile(link)
        sha = hashlib.sha256(archive.read_bytes()).hexdigest()
        self.assertEqual(A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)['verified_packages'],1)
        (source/'alias').unlink()
        (source/'alias').symlink_to('missing.rs')
        with self.assertRaisesRegex(ValueError,'mode/literal link'):
            A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)

    def test_registry_ordinary_marker_validity_and_deadline(self):
        for raw in (b'{"v":2}',b'{"v":true}',b'{"v":1,"extra":"source"}',b'{"v":1,"v":1}'):
            with self.subTest(raw=raw):
                cargo,source,sha = self.ordinary_registry()
                self.write(source/'.cargo-ok',raw)
                with self.assertRaises(ValueError):
                    A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)
        for kind in ('executable','symlink','dangling'):
            with self.subTest(kind=kind):
                cargo,source,sha = self.ordinary_registry()
                marker = source/'.cargo-ok'
                if kind == 'executable':
                    marker.chmod(0o755)
                else:
                    marker.unlink()
                    target = cargo/'marker-target'
                    if kind == 'symlink':
                        self.write(target,b'{"v":1}')
                    marker.symlink_to(target)
                reason = 'not a regular file' if kind != 'executable' else 'Cargo marker'
                with self.assertRaisesRegex(ValueError,reason):
                    A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)
        cargo,_,sha = self.ordinary_registry()
        with self.assertRaisesRegex(ValueError,'deadline expired'):
            A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()-1)

    def test_registry_present_checksum_cannot_fall_back_to_valid_cargo_marker(self):
        for kind in ('valid','package','files','duplicate','extra','executable','symlink','dangling'):
            with self.subTest(kind=kind):
                cargo,source,sha = self.ordinary_registry()
                checksum = {'package':sha,'files':{'lib.rs':hashlib.sha256(b'original').hexdigest()}}
                if kind == 'package':
                    checksum['package'] = '0'*64
                elif kind == 'files':
                    checksum['files'] = {}
                elif kind == 'extra':
                    checksum['extra'] = 'source'
                raw = json.dumps(checksum).encode()
                if kind == 'duplicate':
                    raw = b'{"package":"'+sha.encode()+b'","package":"'+sha.encode()+b'","files":{}}'
                marker = source/'.cargo-checksum.json'
                if kind in ('symlink','dangling'):
                    target = cargo/'checksum-target'
                    if kind == 'symlink':
                        self.write(target,raw)
                    marker.symlink_to(target)
                else:
                    self.write(marker,raw,0o755 if kind == 'executable' else 0o644)
                if kind == 'valid':
                    self.assertEqual(A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)['verified_packages'],1)
                else:
                    reasons = {'package':'pinned archive identity','files':'source checksums differ',
                               'duplicate':'duplicate proof JSON key','extra':'extra fields or executable',
                               'executable':'extra fields or executable','symlink':'not a regular file',
                               'dangling':'not a regular file'}
                    with self.assertRaisesRegex(ValueError,reasons[kind]):
                        A.registry_sources(cargo,{'p-1.0.0':sha},time.monotonic()+10)

if __name__ == '__main__':
    unittest.main()
