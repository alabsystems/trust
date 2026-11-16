#!/usr/bin/env python3
"""Archive/input custody controls; fixture bytes are data, never executed tools."""
from __future__ import annotations

import hashlib
import io
import json
import os
from pathlib import Path
import py_compile
import sys
import tarfile
import tempfile
import types
import unittest
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / 'seed_staircase.py'

def load(path, name):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)
    return module

staircase = load(SCRIPT, 'seed_archive_auth_subject')
HOST = 'aarch64-apple-darwin'

class SeedArchiveAuthentication(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='seed-archive-auth-test-')
        self.root = Path(self.scratch.name)
        self.repo = self.root / 'repo'
        (self.repo / 'src').mkdir(parents=True)
        self.payloads = self.root / 'payloads'
        self.payloads.mkdir()
        self.pin = self.repo / 'src/stage0'
        self.seed = self.root / 'seed'
        self.pins = {'compiler_date': '2026-10-28', 'compiler_version': 'fixture',
                     'compiler_git_commit_hash': 'a' * 40}
        self.rows = {
            'trustc': {'bin/trustc': (b'compiler-data', 0o755),
                       'lib/private.rmeta': (b'private-metadata-data', 0o644)},
            'trust-std': {'lib/std.rlib': (b'std-data', 0o644)},
            'targo': {'bin/targo': (b'targo-data', 0o755), 'bin/cargo': (b'cargo-data', 0o755)},
        }
        self.host_patch = mock.patch.object(staircase, 'host_triple', return_value=HOST)
        self.system_patch = mock.patch.object(staircase.platform, 'system', return_value='Darwin')
        self.host_patch.start()
        self.system_patch.start()
        self.addCleanup(self.host_patch.stop)
        self.addCleanup(self.system_patch.stop)
        self.addCleanup(self.scratch.cleanup)
        self.write_archives()

    def archive(self, component, rows=None, extra=None):
        name = f'{component}-fixture-{HOST}.tar.xz'
        path = self.payloads / name
        prefix = name[:-7] + '/component/'
        with tarfile.open(path, 'w:xz') as tar:
            for relative, (data, mode) in (rows or self.rows[component]).items():
                member = tarfile.TarInfo(prefix + relative)
                member.size, member.mode = len(data), mode
                tar.addfile(member, io.BytesIO(data))
            if extra is not None:
                tar.addfile(extra)
        self.pins['dist/2026-10-28/' + name] = hashlib.sha256(path.read_bytes()).hexdigest()
        return path

    def write_archives(self):
        for component in self.rows:
            self.archive(component)
        self.write_pins()

    def write_pins(self):
        self.pin.write_text(''.join(f'{key}={value}\n' for key, value in self.pins.items()))

    def construct(self):
        return staircase.seed_sysroot(self.payloads, self.pin, self.seed)

    def rewrite_receipt(self):
        path = self.seed / 'STAGE0-SEED.json'
        record = json.loads(path.read_text())
        record.update(sha256=staircase.sysroot_files(self.seed),
                      installed_content_sha256=staircase.seed_content_identity(self.seed))
        path.write_text(json.dumps(record))

    def refuses_recomputed_record(self):
        self.rewrite_receipt()
        with self.assertRaisesRegex(staircase.Refusal, 'pinned archive installation'):
            staircase.pinned_seed_record(self.seed, self.repo)

    def test_valid_constructor_output_and_source_identity(self):
        record = self.construct()
        self.assertEqual(staircase.pinned_seed_record(self.seed, self.repo), record)
        used = staircase.support_source_inputs()
        support = SCRIPT.parent / 'lib/seal_content_identity.py'
        self.assertEqual(used[str(support)], hashlib.sha256(support.read_bytes()).hexdigest())

    def test_forged_executable_recomputed_record_refuses_before_execution(self):
        self.construct()
        (self.seed / 'bin/targo').write_bytes(b'forged executable bytes')
        with mock.patch.object(staircase.subprocess, 'run', side_effect=AssertionError('must not execute')):
            self.refuses_recomputed_record()

    def test_private_library_mutation_recomputed_record_refuses(self):
        self.construct()
        (self.seed / 'lib/private.rmeta').write_bytes(b'forged private namespace')
        self.refuses_recomputed_record()

    def test_extra_root_seal_record_names_are_not_exempt(self):
        self.construct()
        for name in ('PROVENANCE', 'SEED-MINT', 'STAGE0-LINEAGE', 'PROVENANCE.build-status'):
            with self.subTest(name=name):
                path = self.seed / name
                path.write_text('unlisted installed input')
                self.refuses_recomputed_record()
                path.unlink()

    def test_extra_empty_directory_and_missing_file_refuse(self):
        self.construct()
        (self.seed / 'extra').mkdir()
        self.refuses_recomputed_record()
        (self.seed / 'extra').rmdir()
        (self.seed / 'lib/std.rlib').unlink()
        self.refuses_recomputed_record()

    def test_file_to_same_bytes_symlink_refuses(self):
        self.construct()
        target = self.root / 'outside-copy'
        target.write_bytes((self.seed / 'bin/targo').read_bytes())
        (self.seed / 'bin/targo').unlink()
        (self.seed / 'bin/targo').symlink_to(target)
        self.refuses_recomputed_record()

    def test_file_to_directory_refuses(self):
        self.construct()
        (self.seed / 'lib/std.rlib').unlink()
        (self.seed / 'lib/std.rlib').mkdir()
        self.refuses_recomputed_record()

    def test_executable_mode_mutation_refuses(self):
        self.construct()
        (self.seed / 'bin/targo').chmod(0o644)
        self.refuses_recomputed_record()

    def test_group_other_writable_file_mutation_refuses(self):
        self.construct()
        (self.seed / 'bin/targo').chmod(0o777)
        self.refuses_recomputed_record()

    def test_archive_fifo_refuses_without_blocking(self):
        path = self.payloads / f'trustc-fixture-{HOST}.tar.xz'
        path.unlink()
        os.mkfifo(path)
        with self.assertRaisesRegex(staircase.Refusal, 'not a regular file'):
            self.construct()

    def test_constructor_umask_does_not_invent_archive_directory_modes(self):
        previous = os.umask(0o077)
        try:
            record = self.construct()
        finally:
            os.umask(previous)
        self.assertEqual(staircase.pinned_seed_record(self.seed, self.repo), record)

    def test_current_archive_is_reauthenticated_on_every_call(self):
        self.construct()
        staircase.pinned_seed_record(self.seed, self.repo)
        path = self.payloads / f'targo-fixture-{HOST}.tar.xz'
        path.write_bytes(path.read_bytes() + b'corruption')
        with self.assertRaisesRegex(staircase.Refusal, 'src/stage0 pin'):
            staircase.pinned_seed_record(self.seed, self.repo)

    def test_existing_missing_pin_and_archive_change_diagnostics(self):
        key = 'dist/2026-10-28/' + f'trustc-fixture-{HOST}.tar.xz'
        saved = self.pins.pop(key)
        self.write_pins()
        with self.assertRaisesRegex(staircase.Refusal, 'pins no.*apple-darwin'):
            self.construct()
        self.pins[key] = saved
        self.write_pins()
        self.construct()
        path = self.payloads / f'targo-fixture-{HOST}.tar.xz'
        path.write_bytes(path.read_bytes() + b'changed archive')
        with self.assertRaisesRegex(staircase.Refusal, 'archive changed'):
            staircase.pinned_seed_record(self.seed, self.repo)

    def test_disagreeing_component_overlap_refuses(self):
        self.rows['targo']['bin/trustc'] = (b'different compiler', 0o755)
        self.write_archives()
        with self.assertRaisesRegex(staircase.Refusal, 'components disagree'):
            self.construct()
        self.assertFalse(self.seed.exists())

    def test_agreeing_component_overlap_preserves_last_file_mode(self):
        self.rows['targo']['bin/trustc'] = (b'compiler-data', 0o700)
        self.write_archives()
        self.construct()
        self.assertEqual((self.seed / 'bin/trustc').stat().st_mode & 0o777, 0o700)
        staircase.pinned_seed_record(self.seed, self.repo)

    def test_unsafe_archive_members_refuse(self):
        for kind, name in ((tarfile.SYMTYPE, 'link'), (tarfile.REGTYPE, '../escape'),
                           (tarfile.REGTYPE, '/absolute'), (tarfile.FIFOTYPE, 'pipe')):
            with self.subTest(kind=kind, name=name):
                extra = tarfile.TarInfo(f'targo-fixture-{HOST}/component/' + name
                                        if not name.startswith('/') else name)
                extra.type, extra.linkname = kind, 'bin/targo'
                self.archive('targo', extra=extra)
                self.write_pins()
                with self.assertRaises(staircase.Refusal):
                    self.construct()

    def test_capture_hashes_the_same_bytes_tar_parses_despite_path_aba(self):
        path = self.payloads / f'trustc-fixture-{HOST}.tar.xz'
        original = path.read_bytes()
        self.archive('trustc', {'bin/trustc': (b'wrong-compiler', 0o755)})
        replacement = path.read_bytes()
        path.write_bytes(original)
        self.pins['dist/2026-10-28/' + path.name] = hashlib.sha256(original).hexdigest()
        self.write_pins()
        real_open = tarfile.open
        seen = []
        def swapped_open(*args, **kwargs):
            # Deterministic A->B->A at the parser boundary. Snapshot-backed
            # parsing must ignore B; the former path parser consumed B.
            source = kwargs.get('fileobj')
            if not seen:
                path.write_bytes(replacement)
                seen.append(source is not None)
                opened = real_open(*args, **kwargs)
                old_close = opened.close
                def close():
                    try:
                        old_close()
                    finally:
                        path.write_bytes(original)
                opened.close = close
                return opened
            return real_open(*args, **kwargs)
        with mock.patch.object(staircase.tarfile, 'open', side_effect=swapped_open):
            self.construct()
        self.assertEqual((self.seed / 'bin/trustc').read_bytes(), b'compiler-data')
        self.assertEqual(seen, [True])


class SupportSourceCapture(unittest.TestCase):
    def test_unchecked_pyc_and_sys_modules_cannot_replace_captured_source(self):
        with tempfile.TemporaryDirectory() as temporary:
            # The capture records the resolved path the script runs from
            # (macOS's temporary directory is under the /var -> /private/var link).
            root = Path(temporary).resolve()
            (root / 'lib').mkdir()
            script = root / 'seed_staircase.py'
            script.write_bytes(SCRIPT.read_bytes())
            support = root / 'lib/example.py'
            support.write_text('VALUE = "stale"\n')
            py_compile.compile(str(support), invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH)
            support.write_text('VALUE = "actual"\n')
            subject = load(script, 'isolated_seed_capture')
            stale = types.ModuleType('trust_seed_example')
            stale.VALUE = 'sys.modules-forgery'
            with mock.patch.dict(sys.modules, {'trust_seed_example': stale}):
                module = subject.staircase_support('example')
            self.assertEqual(module.VALUE, 'actual')
            expected = hashlib.sha256(support.read_bytes()).hexdigest()
            self.assertEqual(subject.support_source_inputs(), {str(support): expected})
            support.write_text('VALUE = "later"\n')
            self.assertEqual(subject.staircase_support('example').VALUE, 'actual')
            self.assertEqual(subject.support_source_inputs(), {str(support): expected})

    def test_canonical_bound_source_loader_protocol_is_used(self):
        loader_path = SCRIPT.parent / 'seed_custody_source.py'
        owner = load(loader_path, 'archive_test_bound_source_loader')
        support = SCRIPT.parent / 'lib/seal_content_identity.py'
        expected = {str(support.relative_to(SCRIPT.parent.parent)):
                    hashlib.sha256(support.read_bytes()).hexdigest()}
        loader = owner.BoundSourceLoader(SCRIPT.parent.parent, expected)
        subject = load(SCRIPT, 'protocol_seed_capture')
        subject.__trust_source_loader__ = loader
        module = subject.staircase_support('seal_content_identity')
        self.assertIs(module.__trust_source_loader__, loader)
        self.assertEqual(subject.support_source_inputs(), {str(support): expected[next(iter(expected))]})
        loader.recheck()

    def test_bad_support_name_refuses(self):
        for name in ('../outside', '/absolute', 'x.py', ''):
            with self.subTest(name=name), self.assertRaises(staircase.Refusal):
                staircase.staircase_support(name)

if __name__ == '__main__':
    unittest.main()
