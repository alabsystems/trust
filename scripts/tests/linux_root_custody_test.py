#!/usr/bin/env python3
"""Adverse controls for the connected NON-ADMITTING custody stage.

Authored source only; not run as part of this proposal. These controls exercise
boundary behavior, not evidence that a native producer has ever completed.
"""
from __future__ import annotations

import hashlib
import io
import os
from pathlib import Path
import py_compile
import select
import socket
import subprocess
import threading
import tempfile
import tarfile
import time
import types
import unittest
import sys
from unittest import mock

HERE = Path(__file__).resolve().parents[1]


def raw_module(name, path):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)
    return module


source = raw_module('test_custody_source', HERE / 'seed_custody_source.py')
custody = raw_module('test_producer_custody', HERE / 'seed_producer_custody.py')
contract = raw_module('test_producer_contract', HERE / 'seed_producer_contract.py')
initialization = raw_module('test_nonadmitting_initialization', HERE / 'seed_root_initialization.py')


class AuthenticatedSourceTests(unittest.TestCase):
    def native_projection_child(self, root, *, hostile=None, selection=False):
        # Actual interpreter/FD/clock/source caller only. Pipes and regular
        # fixture descriptions here are DATA shapes, never a GNU loan, SDK,
        # source Manager, original producer, NoFork or NativeClosed authority.
        import fcntl
        loader = self.projection_loader()
        captured = {name: source.regular_bytes(HERE.parent / name) for name in loader.expected}
        destination = root / 'original'; destination.mkdir(mode=0o700)
        archive = root / 'fixture.tar.xz'
        self.projection_archive(archive, (('trustc/bin/trustc', b'compiler'),))
        regular = root / 'inert-record'; regular.write_bytes(b'inert descriptor fixture')
        packet = {'schema': 'trust-native-component-projection-v1',
            'source_root': str(HERE.parent), 'destination': str(destination),
            'top': 'fixture', 'commit': 'a' * 40, 'component': 'trustc',
            'sources': {name: {'hex': raw.hex(), 'sha256': hashlib.sha256(raw).hexdigest()}
                        for name, raw in captured.items()},
            'clock': 'darwin-mach-uptime-raw-v1',
            'end_ns': time.clock_gettime_ns(time.CLOCK_UPTIME_RAW) + 30_000_000_000}
        if selection:
            _, _, host, raw, _ = self.seed_selection_fixture()
            packet = {key: packet[key] for key in ('source_root', 'sources', 'clock', 'end_ns')}
            packet.update(schema='trust-native-seed-selection-v1', host=host,
                          pin={'hex': raw.hex(), 'sha256': hashlib.sha256(raw).hexdigest()})
        opened = []
        read, write = os.pipe(); opened.extend((read, write))
        mapping = []
        try:
            for target in range(3, 22):
                if target in (3, 4):
                    original = read if target == 3 else write
                else:
                    path = HERE.parent if target == 6 else destination if target in (10, 20) else (
                        root if target in (7, 14, 16, 18, 19) else archive if target == 13 else regular)
                    flags = os.O_RDWR if hostile == 'writable' and target == 13 else os.O_RDONLY
                    original = os.open(path, flags); opened.append(original)
                copy = fcntl.fcntl(original, fcntl.F_DUPFD_CLOEXEC, 64)
                opened.append(copy); mapping.append((copy, target))
            archive_fd = next(copy for copy, target in mapping if target == 13)
            os.lseek(archive_fd, 7, os.SEEK_SET)
            original_flags = fcntl.fcntl(archive_fd, fcntl.F_GETFL)
            if hostile == 'extra':
                packet['passed'] = True
            elif hostile == 'directory':
                other = root / 'other'; other.mkdir(mode=0o700)
                packet['source_root' if selection else 'destination'] = str(other)
            elif hostile == 'expired':
                packet['end_ns'] = time.clock_gettime_ns(time.CLOCK_UPTIME_RAW) - 1
            elif hostile == 'missing':
                packet['sources'].pop('src/bootstrap/stage0_identity.py')
            elif hostile == 'pin':
                packet['pin']['sha256'] = '0' * 64
            elif hostile == 'host':
                packet['host'] = None
            prefix = ('import os, json\n'
                'for original, target in ' + repr(mapping) + ': os.dup2(original, target)\n'
                'for original, target in ' + repr(mapping) + ': os.close(original)\n')
            suffix = ('\npacket = json.load(sys.stdin)\n'
                + ('count = _native_seed_selection(packet)\n' if selection
                   else 'count = _native_projection(packet)\n') +
                'import fcntl, json\n'
                'print(json.dumps({' + repr('plan' if selection else 'bytes') +
                ':count,"cursor":os.lseek(13,0,os.SEEK_CUR),'
                '"flags":fcntl.fcntl(13,fcntl.F_GETFL)}))\n')
            code = prefix + ('exec(compile(' + repr(captured['scripts/seed_custody_source.py'])
                + ', ' + repr(str(HERE / 'seed_custody_source.py')) + ', "exec"), globals())\n') + suffix
            result = subprocess.run([sys.executable, '-I', '-S', '-c', code],
                input=__import__('json').dumps(packet), text=True, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, pass_fds=[copy for copy, _ in mapping], timeout=30)
            self.assertEqual(os.lseek(archive_fd, 0, os.SEEK_CUR), 7)
            self.assertEqual(fcntl.fcntl(archive_fd, fcntl.F_GETFL), original_flags)
            return result, destination, original_flags
        finally:
            for descriptor in reversed(opened):
                os.close(descriptor)

    @unittest.skipUnless(sys.platform == 'darwin', 'the fixed native profile uses Darwin uptime')
    def test_fixed_interpreter_entry_uses_original_descriptions_source_and_clock(self):
        with tempfile.TemporaryDirectory() as directory:
            result, destination, flags = self.native_projection_child(Path(directory).resolve())
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(__import__('json').loads(result.stdout),
                             {'bytes': len(b'compiler'), 'cursor': 7, 'flags': flags})
            self.assertEqual((destination / 'bin/trustc').read_bytes(), b'compiler')

    @unittest.skipUnless(sys.platform == 'darwin', 'the fixed native profile uses Darwin uptime')
    def test_fixed_interpreter_entry_refuses_foreign_data_before_output(self):
        for hostile in ('extra', 'directory', 'expired', 'missing', 'writable'):
            with self.subTest(hostile=hostile), tempfile.TemporaryDirectory() as directory:
                result, destination, _ = self.native_projection_child(Path(directory).resolve(), hostile=hostile)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, '')
                self.assertEqual(list(destination.iterdir()), [])

    @unittest.skipUnless(sys.platform == 'darwin', 'the fixed native profile uses Darwin uptime')
    def test_fixed_seed_selection_entry_uses_captured_source_without_projecting_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            result, destination, flags = self.native_projection_child(
                Path(directory).resolve(), selection=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            data = __import__('json').loads(result.stdout)
            self.assertEqual(data['cursor'], 7)
            self.assertEqual(data['flags'], flags)
            self.assertEqual(len(data['plan']['archives']), 7)
            self.assertEqual(data['plan']['schema'], 'trust-native-seed-archive-plan-v1')
            self.assertEqual(list(destination.iterdir()), [])

    @unittest.skipUnless(sys.platform == 'darwin', 'the fixed native profile uses Darwin uptime')
    def test_fixed_seed_selection_entry_refuses_foreign_pin_code_root_host_and_end(self):
        for hostile in ('extra', 'directory', 'expired', 'missing', 'pin', 'host'):
            with self.subTest(hostile=hostile), tempfile.TemporaryDirectory() as directory:
                result, destination, _ = self.native_projection_child(
                    Path(directory).resolve(), hostile=hostile, selection=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, '')
                self.assertEqual(list(destination.iterdir()), [])

    def projection_loader(self):
        root = HERE.parent
        paths = ('scripts/seed_custody_source.py', 'scripts/mint_seed_support.py',
                 'src/bootstrap/stage0_identity.py')
        captured = {name: source.regular_bytes(root / name) for name in paths}
        return source.BoundSourceLoader(root,
            {name: hashlib.sha256(raw).hexdigest() for name, raw in captured.items()},
            captured_sources=captured)

    def seed_selection_fixture(self):
        loader = self.projection_loader()
        helper = loader.module('seed_selection_fixture', HERE / 'mint_seed_support.py')
        host = helper.detected_host()
        pin = {'compiler_git_commit_hash': 'a' * 40, 'compiler_date': '2026-11-07',
               'compiler_version': '0.13.0-trust', 'dist_server': 'file:///unused'}
        rows, _, _ = helper._IDENTITY_OWNER.component_archives(
            pin, pin['compiler_date'], pin['compiler_version'], host, '.tar.xz')
        for filename, _ in rows:
            pin['dist/2026-11-07/' + filename] = 'b' * 64
        raw = ''.join(key + '=' + value + '\n' for key, value in pin.items()).encode()
        return loader, helper, host, raw, rows

    def test_captured_seed_selection_uses_the_complete_bootstrap_plan_without_payload_io(self):
        loader, helper, host, raw, rows = self.seed_selection_fixture()
        with mock.patch('subprocess.run', side_effect=AssertionError('selection spawned a target')):
            plan = loader.select_seed_archives_from_capture(raw, host, deadline=time.monotonic() + 30)
        self.assertEqual(plan['schema'], 'trust-native-seed-archive-plan-v1')
        self.assertEqual(plan['host'], host)
        self.assertEqual(len(plan['archives']), 7)
        self.assertEqual([(row['path'].removeprefix('bootstrap/trust-stage0/dist/2026-11-07/'),
                           row['component']) for row in plan['archives']], rows)
        self.assertTrue(all(row['sha256'] == 'b' * 64 for row in plan['archives']))
        self.assertEqual(plan['extraction_stamp'],
                         helper.stage0_extraction_stamp(helper.parse_stage0_pin(raw)))
        self.assertEqual(plan['legacy_targo'], [])
        self.assertFalse(plan['legacy_tippy'])

    def test_captured_seed_selection_refuses_missing_checksum_duplicate_pin_and_foreign_host(self):
        loader, helper, host, raw, rows = self.seed_selection_fixture()
        missing = b'\n'.join(line for line in raw.splitlines()
                             if rows[-1][0].encode() not in line) + b'\n'
        for bad in (missing, raw + b'compiler_version=0.13.0-trust\n',
                    raw.replace(b'b' * 64, b'bad-checksum', 1), bytearray(raw)):
            with self.assertRaises((helper.WorkflowError, ValueError, RuntimeError)):
                loader.select_seed_archives_from_capture(bad, host, deadline=time.monotonic() + 30)
        with self.assertRaisesRegex(RuntimeError, 'not the native host'):
            loader.select_seed_archives_from_capture(raw, 'different-unknown-host',
                                                     deadline=time.monotonic() + 30)
        with self.assertRaisesRegex(ValueError, 'endpoint'):
            loader.select_seed_archives_from_capture(raw, host, deadline=time.monotonic() - 1)

    def test_captured_seed_pin_parser_is_the_ordinary_path_parser(self):
        loader, helper, host, raw, _ = self.seed_selection_fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); (root / 'src').mkdir()
            (root / 'src/stage0').write_bytes(raw)
            self.assertEqual(helper.read_stage0_pin(root), helper.parse_stage0_pin(raw))
        for bad in (raw + b'compiler_date=2026-11-07\n', raw.replace(b'compiler_date=', b'bad=')):
            with self.assertRaises(helper.WorkflowError):
                helper.parse_stage0_pin(bad)

    def projection_archive(self, path, entries, links=()):
        with tarfile.open(path, 'w:xz') as bundle:
            for name, raw in (('install.sh', b'#!/bin/sh\nexit 0\n'),
                              ('version', b'1.99.0 fixture\n'),
                              ('git-commit-hash', b'a' * 40 + b'\n'), *entries):
                member = tarfile.TarInfo('fixture/' + name)
                if raw is None:
                    member.type = tarfile.DIRTYPE; member.mode = 0o755
                    bundle.addfile(member)
                    continue
                member.mode = 0o755 if '/bin/' in name or name == 'install.sh' else 0o644
                member.size = len(raw); bundle.addfile(member, io.BytesIO(raw))
            for name, target, hard in links:
                member = tarfile.TarInfo('fixture/' + name)
                member.type = tarfile.LNKTYPE if hard else tarfile.SYMTYPE
                member.linkname = 'fixture/' + target if hard else target
                bundle.addfile(member)

    def test_captured_projection_composes_exact_components_without_an_installer(self):
        import fcntl
        loader = self.projection_loader()
        helper = loader.module('captured_projection', HERE / 'mint_seed_support.py')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); destination = root / 'original'
            destination.mkdir(mode=0o700)
            for component in ('trustc', 'targo'):
                archive = root / (component + '.tar.xz')
                self.projection_archive(archive, ((component + '/bin/' + component, component.encode()),),
                    ((component + '/bin/' + component + '-alias', component, False),
                     (component + '/bin/' + component + '-hard', component + '/bin/' + component, True)))
                with archive.open('rb') as original:
                    descriptor = original.fileno(); os.lseek(descriptor, 7, os.SEEK_SET)
                    flags = fcntl.fcntl(descriptor, fcntl.F_GETFL)
                    with mock.patch.object(helper.subprocess, 'run', side_effect=AssertionError('no child')), \
                            mock.patch.object(helper.subprocess, 'Popen', side_effect=AssertionError('no child')):
                        count = loader.project_for_preparation_fd(descriptor, destination,
                            'fixture', 'a' * 40, component, deadline=time.monotonic() + 30)
                    self.assertEqual(count, len(component))
                    self.assertEqual(os.lseek(descriptor, 0, os.SEEK_CUR), 7)
                    self.assertEqual(fcntl.fcntl(descriptor, fcntl.F_GETFL), flags)
                actual = destination / 'bin' / component
                self.assertEqual(actual.read_bytes(), component.encode())
                self.assertEqual((actual.parent / (component + '-alias')).read_bytes(), component.encode())
                self.assertEqual(actual.stat().st_ino, (actual.parent / (component + '-hard')).stat().st_ino)
            self.assertEqual(set(path.name for path in destination.iterdir()), {'bin'})
            loader.recheck()

    def test_canonical_installer_metadata_and_identical_shared_files_compose_without_overwrite(self):
        # rust-installer::Generator writes a manifest.in INSIDE every image.
        # It describes installation; it is not a file installed into the seed.
        loader = self.projection_loader()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); destination = root / 'original'
            destination.mkdir(mode=0o700); shared_stamp = None
            for component in ('trustc', 'targo'):
                archive = root / (component + '.tar.xz')
                self.projection_archive(archive, (
                    (component + '/manifest.in', ('file:bin/' + component + '\nfile:share/license\n').encode()),
                    (component + '/bin/' + component, component.encode()),
                    (component + '/share/license', b'exact same shared license bytes'),
                    (component + '/share/manifest.in', b'installed nested data'),
                ))
                with archive.open('rb') as original:
                    loader.project_for_preparation_fd(original.fileno(), destination,
                        'fixture', 'a' * 40, component, deadline=time.monotonic() + 30)
                shared = destination / 'share/license'
                info = shared.stat()
                stamp = (info.st_dev, info.st_ino, info.st_mode, info.st_size,
                         info.st_mtime_ns, info.st_ctime_ns)
                if shared_stamp is None:
                    shared_stamp = stamp
                self.assertEqual(stamp, shared_stamp)
            self.assertFalse((destination / 'manifest.in').exists())
            self.assertEqual((destination / 'share/manifest.in').read_bytes(), b'installed nested data')
            self.assertEqual((destination / 'bin/trustc').read_bytes(), b'trustc')
            self.assertEqual((destination / 'bin/targo').read_bytes(), b'targo')

    def test_projection_refuses_same_bytes_with_conflicting_existing_file_mode(self):
        loader = self.projection_loader()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); destination = root / 'original'
            destination.mkdir(mode=0o700)
            (destination / 'share').mkdir(mode=0o700)
            shared = destination / 'share/license'; shared.write_bytes(b'same bytes')
            shared.chmod(0o600); original = shared.stat()
            archive = root / 'fixture.tar.xz'
            self.projection_archive(archive, (('trustc/share/license', b'same bytes'),))
            with archive.open('rb') as opened, self.assertRaises(FileExistsError):
                loader.project_for_preparation_fd(opened.fileno(), destination,
                    'fixture', 'a' * 40, 'trustc', deadline=time.monotonic() + 30)
            self.assertEqual(shared.read_bytes(), b'same bytes')
            self.assertEqual(shared.stat().st_ino, original.st_ino)
            self.assertEqual(shared.stat().st_mode, original.st_mode)
            self.assertEqual(shared.stat().st_mtime_ns, original.st_mtime_ns)
            self.assertEqual(shared.stat().st_ctime_ns, original.st_ctime_ns)

    def test_private_creation_mask_does_not_change_fresh_canonical_projection_modes(self):
        loader = self.projection_loader()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); destination = root / 'original'
            destination.mkdir(mode=0o700)
            previous = os.umask(0o077)
            try:
                for component in ('trustc', 'targo'):
                    archive = root / (component + '.tar.xz')
                    self.projection_archive(archive, (
                        (component + '/manifest.in', ('file:bin/' + component + '\n').encode()),
                        (component + '/bin/' + component, component.encode()),
                        (component + '/share/license', b'identical shared installed bytes'),
                    ))
                    with archive.open('rb') as original:
                        loader.project_for_preparation_fd(original.fileno(), destination,
                            'fixture', 'a' * 40, component, deadline=time.monotonic() + 30)
                    self.assertEqual((destination / 'bin' / component).stat().st_mode & 0o777, 0o755)
                    self.assertEqual((destination / 'share/license').stat().st_mode & 0o777, 0o644)
            finally:
                os.umask(previous)

    def test_projection_refuses_a_prefix_decoy_before_populating_the_producer(self):
        loader = self.projection_loader()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); archive = root / 'decoy.tar.xz'
            destination = root / 'original'; destination.mkdir(mode=0o700)
            self.projection_archive(archive, (('trustc-preview/bin/trustc', b'decoy'),))
            with archive.open('rb') as original, self.assertRaisesRegex(RuntimeError, 'exact projected component'):
                loader.project_for_preparation_fd(original.fileno(), destination,
                    'fixture', 'a' * 40, 'trustc', deadline=time.monotonic() + 30)
            self.assertEqual(list(destination.iterdir()), [])

    def test_projection_preserves_existing_directory_modes_and_refuses_conflicting_components(self):
        loader = self.projection_loader()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); archive = root / 'fixture.tar.xz'
            destination = root / 'original'; destination.mkdir(mode=0o700)
            self.projection_archive(archive, (('trustc/lib', None), ('trustc/lib/first', b'first')))
            with archive.open('rb') as original:
                loader.project_for_preparation_fd(original.fileno(), destination,
                    'fixture', 'a' * 40, 'trustc', deadline=time.monotonic() + 30)
            self.assertEqual((destination / 'lib').stat().st_mode & 0o777, 0o755)
            self.projection_archive(archive, (('targo/lib', None), ('targo/lib/second', b'second')))
            with archive.open('rb') as original:
                loader.project_for_preparation_fd(original.fileno(), destination,
                    'fixture', 'a' * 40, 'targo', deadline=time.monotonic() + 30)
            (destination / 'lib').chmod(0o700)
            with archive.open('rb') as original, self.assertRaisesRegex(RuntimeError, 'directory permissions'):
                loader.project_for_preparation_fd(original.fileno(), destination,
                    'fixture', 'a' * 40, 'targo', deadline=time.monotonic() + 30)
            self.assertEqual((destination / 'lib').stat().st_mode & 0o777, 0o700)
            self.assertEqual((destination / 'lib/first').read_bytes(), b'first')
            self.assertEqual((destination / 'lib/second').read_bytes(), b'second')

    def test_projection_refuses_a_link_to_an_unprojected_component_before_writes(self):
        loader = self.projection_loader()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); archive = root / 'cross.tar.xz'
            destination = root / 'original'; destination.mkdir(mode=0o700)
            self.projection_archive(archive, (('trustc/bin/trustc', b'compiler'),
                                            ('other/bin/provider', b'provider')),
                (('trustc/bin/escape', '../../other/bin/provider', False),))
            with archive.open('rb') as original, self.assertRaisesRegex(RuntimeError, 'leaves its exact component'):
                loader.project_for_preparation_fd(original.fileno(), destination,
                    'fixture', 'a' * 40, 'trustc', deadline=time.monotonic() + 30)
            self.assertEqual(list(destination.iterdir()), [])

    def test_projection_neither_overwrites_nor_follows_existing_output_names(self):
        loader = self.projection_loader()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); archive = root / 'fixture.tar.xz'
            self.projection_archive(archive, (('trustc/bin/trustc', b'new'),))
            for alias in (False, True):
                destination = root / str(alias); destination.mkdir(mode=0o700)
                outside = root / ('outside-' + str(alias)); outside.mkdir(mode=0o700)
                if alias:
                    (destination / 'bin').symlink_to(outside, target_is_directory=True)
                else:
                    (destination / 'bin').mkdir(mode=0o700)
                    (destination / 'bin/trustc').write_bytes(b'old')
                    (destination / 'bin/trustc').chmod(0o755)
                with archive.open('rb') as original, self.assertRaises(OSError):
                    loader.project_for_preparation_fd(original.fileno(), destination,
                        'fixture', 'a' * 40, 'trustc', deadline=time.monotonic() + 30)
                self.assertEqual(list(outside.iterdir()), [])
                if not alias:
                    self.assertEqual((destination / 'bin/trustc').read_bytes(), b'old')

    def test_projection_keeps_partial_output_at_the_same_original_deadline(self):
        loader = self.projection_loader()
        helper = loader.module('deadline_projection', HERE / 'mint_seed_support.py')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); archive = root / 'fixture.tar.xz'
            destination = root / 'original'; destination.mkdir(mode=0o700)
            self.projection_archive(archive, (('trustc/bin/first', b'first'),
                                            ('trustc/bin/second', b'second')))
            end = time.monotonic() + 30; current = [end - 1]; write = os.write
            def expire_after_write(*args):
                result = write(*args); current[0] = end + 1
                return result
            with archive.open('rb') as original, \
                    mock.patch.object(helper.time, 'monotonic', side_effect=lambda: current[0]), \
                    mock.patch.object(helper.os, 'write', side_effect=expire_after_write), \
                    self.assertRaisesRegex((RuntimeError, ValueError), 'endpoint|deadline'):
                loader.project_for_preparation_fd(original.fileno(), destination,
                    'fixture', 'a' * 40, 'trustc', deadline=end)
            self.assertEqual((destination / 'bin/first').read_bytes(), b'first')
            self.assertFalse((destination / 'bin/second').exists())

    def test_projection_refuses_writable_archive_and_invalid_selector_without_output(self):
        loader = self.projection_loader()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); archive = root / 'fixture.tar.xz'
            destination = root / 'original'; destination.mkdir(mode=0o700)
            self.projection_archive(archive, (('trustc/bin/trustc', b'compiler'),))
            with archive.open('r+b') as original, self.assertRaisesRegex(RuntimeError, 'not readonly'):
                loader.project_for_preparation_fd(original.fileno(), destination,
                    'fixture', 'a' * 40, 'trustc', deadline=time.monotonic() + 30)
            with archive.open('rb') as original, self.assertRaisesRegex(ValueError, 'component path'):
                loader.project_for_preparation_fd(original.fileno(), destination,
                    'fixture', 'a' * 40, '../trustc', deadline=time.monotonic() + 30)
            self.assertEqual(list(destination.iterdir()), [])

    def test_observed_context_transition_preserves_standalone_inspection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            helper = root / 'helper.py'
            raw = (b'def read():\n    live = __trust_source_loader__.context\n'
                   b'    return live.auxiliary() if live is not None else "inspect"\n')
            helper.write_bytes(raw)
            loader = source.BoundSourceLoader(root, {'helper.py': hashlib.sha256(raw).hexdigest()})
            module = loader.module('context_fixture', helper)
            self.assertEqual(module.read(), 'inspect')
            loader.begin_observed_execution()
            with self.assertRaisesRegex(ValueError, 'not installed'):
                module.read()
            class Context:
                def auxiliary(self):
                    return 'observed'
            live = Context()
            loader.bind_observed_execution(live)
            self.assertIs(loader.context, live)
            self.assertEqual(module.read(), 'observed')
            for replacement in (None, Context()):
                with self.assertRaisesRegex(ValueError, 'replaced or cleared'):
                    loader.bind_observed_execution(replacement)
            with self.assertRaises(AttributeError):
                loader.context = None
            with self.assertRaises(ValueError):
                loader.begin_observed_execution()

    def test_observed_context_cannot_be_bound_without_pending_worker(self):
        with tempfile.TemporaryDirectory() as directory:
            loader = source.BoundSourceLoader(Path(directory).resolve(), {})
            with self.assertRaises(ValueError):
                loader.bind_observed_execution(object())
            loader.begin_observed_execution()
            pending = loader.context
            for replacement in (None, pending):
                with self.assertRaises(ValueError):
                    loader.bind_observed_execution(replacement)
                self.assertIs(loader.context, pending)
            live = object()
            loader.bind_observed_execution(live)
            self.assertIs(loader.context, live)
            with self.assertRaises(ValueError):
                loader.bind_observed_execution(object())

    def test_valid_timestamp_shadow_cannot_replace_bound_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path = root / 'helper.py'
            bad, good = b'VALUE = "bad"\n', b'VALUE = "new"\n'
            path.write_bytes(bad)
            saved = path.stat()
            py_compile.compile(str(path), doraise=True)
            path.write_bytes(good)
            os.utime(path, ns=(saved.st_atime_ns, saved.st_mtime_ns))
            loader = source.BoundSourceLoader(root, {'helper.py': hashlib.sha256(good).hexdigest()})
            self.assertEqual(loader.module('one', path).VALUE, 'new')

    def test_aliases_share_exact_type_token_and_registry(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path = root / 'helper.py'
            raw = b'class Capability: pass\nTOKEN = object()\nREGISTRY = {}\n'
            path.write_bytes(raw)
            loader = source.BoundSourceLoader(root, {'helper.py': hashlib.sha256(raw).hexdigest()})
            first = loader.module('first', path)
            second = loader.module('second', path)
            self.assertIs(first, second)
            self.assertIs(first.Capability, second.Capability)
            self.assertIs(first.TOKEN, second.TOKEN)
            self.assertIs(first.REGISTRY, second.REGISTRY)

    def test_changed_source_is_refused_even_when_alias_already_cached(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path = root / 'helper.py'
            raw = b'VALUE = 1\n'
            path.write_bytes(raw)
            loader = source.BoundSourceLoader(root, {'helper.py': hashlib.sha256(raw).hexdigest()})
            loader.module('first', path)
            path.write_bytes(b'VALUE = 2\n')
            with self.assertRaisesRegex(ValueError, 'manifest'):
                loader.module('second', path)

    def test_failed_execution_is_not_a_cached_capability_issuer(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path = root / 'helper.py'
            raw = b'raise ValueError("no issuer")\n'
            path.write_bytes(raw)
            loader = source.BoundSourceLoader(root, {'helper.py': hashlib.sha256(raw).hexdigest()})
            for name in ('first', 'second'):
                with self.assertRaisesRegex(ValueError, 'no issuer'):
                    loader.module(name, path)
            self.assertEqual(loader.modules, {})

    def test_captured_graph_executes_exact_bytes_and_preserves_alias_issuer(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); helper = root / 'helper.py'
            raw = b'class Capability: pass\nTOKEN = object()\nREGISTRY = {}\n'
            helper.write_bytes(raw)
            captured = {'helper.py': raw}
            loader = source.BoundSourceLoader(root, {'helper.py': hashlib.sha256(raw).hexdigest()},
                                               captured_sources=captured)
            captured['helper.py'] = b'raise AssertionError("caller mapping was retained")\n'
            first = loader.module('captured_first', helper)
            second = loader.module('captured_second', helper)
            self.assertIs(first, second)
            self.assertIs(first.Capability, second.Capability)
            self.assertIs(first.TOKEN, second.TOKEN)
            self.assertIs(first.REGISTRY, second.REGISTRY)
            loader.recheck()

    def test_captured_code_is_not_reselected_after_physical_source_bookend(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); helper = root / 'helper.py'
            raw = b'VALUE = "original"\n'; helper.write_bytes(raw)
            loader = source.BoundSourceLoader(root, {'helper.py': hashlib.sha256(raw).hexdigest()},
                                               captured_sources={'helper.py': raw})
            # Change the physical name AFTER its checked read. Execution must
            # still use the original captured code; the physical postcheck must
            # then refuse. This is no source-lock or atomic freeze assertion.
            original_compile = compile
            def compile_then_change(value, *args, **kwargs):
                self.assertEqual(value, raw)
                helper.write_bytes(b'VALUE = "changed"\n')
                return original_compile(value, *args, **kwargs)
            with mock.patch('builtins.compile', side_effect=compile_then_change):
                module = loader.module('captured_changed_after_read', helper)
            self.assertEqual(module.VALUE, 'original')
            with self.assertRaisesRegex(ValueError, 'executed source changed'):
                loader.recheck()

    def test_captured_graph_refuses_missing_extra_changed_and_mutable_code(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); raw = b'VALUE = 1\n'
            expected = {'helper.py': hashlib.sha256(raw).hexdigest()}
            for captured in ({}, {'other.py': raw}, {'helper.py': raw, 'other.py': raw},
                             {'helper.py': bytearray(raw)}, {'helper.py': b'VALUE = 2\n'}):
                with self.assertRaisesRegex(ValueError, 'captured source'):
                    source.BoundSourceLoader(root, expected, captured_sources=captured)

    def test_captured_graph_keeps_transitive_extra_source_closed(self):
        with tempfile.TemporaryDirectory() as directory, tempfile.TemporaryDirectory() as outside:
            root = Path(directory).resolve(); helper = root / 'helper.py'
            extra = Path(outside).resolve() / 'extra.py'; raw = b'VALUE = "extra"\n'
            extra.write_bytes(raw)
            main = ('other = __trust_source_loader__.module("captured_extra", '
                    '__import__("pathlib").Path(' + repr(str(extra)) + '))\nVALUE = other.VALUE\n').encode()
            helper.write_bytes(main)
            expected = {'helper.py': hashlib.sha256(main).hexdigest()}
            extras = {str(extra): hashlib.sha256(raw).hexdigest()}
            with self.assertRaisesRegex(ValueError, 'incomplete'):
                source.BoundSourceLoader(root, expected, extra_sources=extras,
                                        captured_sources={'helper.py': main})
            loader = source.BoundSourceLoader(root, expected, extra_sources=extras,
                captured_sources={'helper.py': main, str(extra): raw})
            self.assertEqual(loader.module('captured_transitive_main', helper).VALUE, 'extra')
            self.assertEqual(set(loader.executed), {'helper.py', str(extra)})
            extra.write_bytes(b'VALUE = "changed"\n')
            with self.assertRaisesRegex(ValueError, 'executed source changed'):
                loader.recheck()

    def test_captured_graph_limits_apply_before_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); raw = b'VALUE = 1\n'
            with mock.patch.object(source, 'MAX_CAPTURED_SOURCES', 1):
                with self.assertRaisesRegex(ValueError, 'exceeds its bound'):
                    source.BoundSourceLoader(root, {p: hashlib.sha256(raw).hexdigest()
                        for p in ('one.py', 'two.py')},
                        captured_sources={p: raw for p in ('one.py', 'two.py')})
            with mock.patch.object(source, 'MAX_CAPTURED_BYTES', len(raw) - 1):
                with self.assertRaisesRegex(ValueError, 'exceeds its bound'):
                    source.BoundSourceLoader(root, {'helper.py': hashlib.sha256(raw).hexdigest()},
                                            captured_sources={'helper.py': raw})

    def test_captured_canonical_extractor_uses_the_original_archive_description(self):
        # Actual maintained source/translation caller, still no native
        # admission, NoFork target, seed issuer or whole-route qualification.
        root = HERE.parent
        paths = ('scripts/seed_custody_source.py', 'scripts/mint_seed_support.py',
                 'src/bootstrap/stage0_identity.py')
        captured = {name: source.regular_bytes(root / name) for name in paths}
        loader = source.BoundSourceLoader(root,
            {name: hashlib.sha256(raw).hexdigest() for name, raw in captured.items()},
            captured_sources=captured)
        helper = loader.module('captured_canonical_extractor', root / paths[1])
        with tempfile.TemporaryDirectory() as directory:
            temporary = Path(directory).resolve(); archive = temporary / 'fixture.tar.xz'
            commit = 'a' * 40
            with tarfile.open(archive, 'w:xz') as bundle:
                for name, raw in (('install.sh', b'#!/bin/sh\nexit 0\n'),
                                  ('version', b'1.99.0 fixture\n'),
                                  ('git-commit-hash', (commit + '\n').encode())):
                    member = tarfile.TarInfo('fixture/' + name)
                    member.mode = 0o755 if name == 'install.sh' else 0o644
                    member.size = len(raw); bundle.addfile(member, io.BytesIO(raw))
            descriptor = os.open(archive, os.O_RDONLY)
            try:
                os.lseek(descriptor, 7, os.SEEK_SET)
                with mock.patch.object(helper.subprocess, 'run', side_effect=AssertionError('no child')), \
                        mock.patch.object(helper.subprocess, 'Popen', side_effect=AssertionError('no child')):
                    count = loader.extract_for_preparation_fd(descriptor, temporary / 'retained',
                        'fixture', commit, deadline=time.monotonic() + 30)
                self.assertGreater(count, 0)
                self.assertEqual((temporary / 'retained/fixture/git-commit-hash').read_text().strip(), commit)
                self.assertEqual(os.lseek(descriptor, 0, os.SEEK_CUR), 7)
                self.assertEqual(set(loader.executed), set(paths) - {'scripts/seed_custody_source.py'})
                loader.recheck()
            finally:
                os.close(descriptor)

    def test_preparation_extractor_refuses_missing_extra_or_uncaptured_graph_before_output(self):
        root = HERE.parent
        paths = ('scripts/seed_custody_source.py', 'scripts/mint_seed_support.py',
                 'src/bootstrap/stage0_identity.py')
        captured = {name: source.regular_bytes(root / name) for name in paths}
        expected = {name: hashlib.sha256(raw).hexdigest() for name, raw in captured.items()}
        profiles = [source.BoundSourceLoader(root, expected),
            source.BoundSourceLoader(root, {name: expected[name] for name in paths[1:]},
                captured_sources={name: captured[name] for name in paths[1:]}),
            source.BoundSourceLoader(root, expected | {'extra.py': hashlib.sha256(b'pass').hexdigest()},
                captured_sources=captured | {'extra.py': b'pass'})]
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / 'never-created'
            for loader in profiles:
                with self.assertRaisesRegex(ValueError, 'fixed captured extractor graph'):
                    loader.extract_for_preparation_fd(99999, destination, 'fixture', 'a' * 40,
                                                       deadline=time.monotonic() + 30)
                self.assertFalse(destination.exists())
                self.assertEqual(loader.executed, {})

    def test_preparation_extractor_never_renews_an_invalid_or_expired_original_end(self):
        root = HERE.parent
        paths = ('scripts/seed_custody_source.py', 'scripts/mint_seed_support.py',
                 'src/bootstrap/stage0_identity.py')
        captured = {name: source.regular_bytes(root / name) for name in paths}
        loader = source.BoundSourceLoader(root,
            {name: hashlib.sha256(raw).hexdigest() for name, raw in captured.items()},
            captured_sources=captured)
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / 'never-created'
            for deadline in (None, True, float('nan'), float('inf'), time.monotonic() - 1):
                with self.assertRaisesRegex(ValueError, 'endpoint'):
                    loader.extract_for_preparation_fd(99999, destination, 'fixture', 'a' * 40,
                                                       deadline=deadline)
                self.assertFalse(destination.exists())
                self.assertEqual(loader.executed, {})

    def test_preparation_extractor_postcheck_covers_loader_entry_and_retains_partial_output(self):
        paths = ('scripts/seed_custody_source.py', 'scripts/mint_seed_support.py',
                 'src/bootstrap/stage0_identity.py')
        captured = {name: source.regular_bytes(HERE.parent / name) for name in paths}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            for name, raw in captured.items():
                path = root / name; path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
            loader = source.BoundSourceLoader(root,
                {name: hashlib.sha256(raw).hexdigest() for name, raw in captured.items()},
                captured_sources=captured)
            helper = loader.module('postcheck_canonical_extractor', root / paths[1])
            archive = root / 'fixture.tar.xz'; commit = 'a' * 40
            with tarfile.open(archive, 'w:xz') as bundle:
                for name, raw in (('install.sh', b'#!/bin/sh\nexit 0\n'),
                                  ('version', b'1.99.0 fixture\n'),
                                  ('git-commit-hash', (commit + '\n').encode())):
                    member = tarfile.TarInfo('fixture/' + name); member.mode = 0o644
                    member.size = len(raw); bundle.addfile(member, io.BytesIO(raw))
            original = helper.extract_for_preparation_fd
            def extract_then_change(*args, **kwargs):
                count = original(*args, **kwargs)
                (root / paths[0]).write_bytes(b'# displaced loader code\n')
                return count
            descriptor = os.open(archive, os.O_RDONLY)
            try:
                with mock.patch.object(helper, 'extract_for_preparation_fd', extract_then_change), \
                        self.assertRaisesRegex(ValueError, 'original preparation source changed'):
                    loader.extract_for_preparation_fd(descriptor, root / 'retained',
                        'fixture', commit, deadline=time.monotonic() + 30)
                self.assertEqual((root / 'retained/fixture/git-commit-hash').read_text().strip(), commit)
                self.assertGreater(os.fstat(descriptor).st_size, 0)
            finally:
                os.close(descriptor)


class CapabilityTests(unittest.TestCase):
    def test_passed_receipt_and_duck_types_have_no_live_authority(self):
        class Fake:
            _issuer = object()
            _used = False
        for value in ({'passed': True, 'closed': True, 'admitted_root_seed': True}, Fake()):
            with self.assertRaisesRegex(ValueError, 'live closed-run'):
                custody.closed_capability(value)

    def test_exact_type_object_without_registry_entry_is_refused(self):
        forged = object.__new__(custody.ClosedProducerObservation)
        with self.assertRaisesRegex(ValueError, 'live closed-run'):
            custody.closed_capability(forged)

    def test_original_expired_budget_cannot_be_renewed(self):
        with self.assertRaisesRegex(ValueError, 'original producer deadline'):
            custody.remaining(time.monotonic() - 1)

    def test_legacy_file_only_admission_still_refuses(self):
        with self.assertRaisesRegex(ValueError, 'pending'):
            initialization.validate_completed_producer(Path('/no-authority'),
                'aarch64-unknown-linux-gnu', {'passed': True, 'admitted_root_seed': True})


class ActualArtifactTests(unittest.TestCase):
    def test_physical_tree_preserves_mode_bytes_and_literal_link(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            payload = root / 'compiler'
            payload.write_bytes(b'compiler-original')
            payload.chmod(0o755)
            (root / 'source-link').symlink_to('/unretained-source-root')
            before = custody.physical_tree(root, time.monotonic() + 5)
            self.assertEqual(before[0]['mode'], 0o755)
            self.assertEqual(before[1]['target'], '/unretained-source-root')
            payload.chmod(0o644)
            after = custody.physical_tree(root, time.monotonic() + 5)
            self.assertNotEqual(before, after)

    def test_physical_root_alias_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / 'actual').mkdir()
            (root / 'alias').symlink_to(root / 'actual', target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'canonical'):
                custody.physical_tree(root / 'alias', time.monotonic() + 5)

    def test_special_file_is_not_hashed_or_opened(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            os.mkfifo(root / 'fifo')
            with self.assertRaisesRegex(ValueError, 'special file'):
                custody.physical_tree(root, time.monotonic() + 5)


class ActualChildObservationTests(unittest.TestCase):
    def exercise(self, program, timeout=2):
        # A tiny Python fixture only; no compiler, build-slot, scope, lease or
        # producer resource admission is obtained by this unit control.
        class InertGraph:
            def command(self, phase, argv, cwd, env):
                pass
        left, right = socket.socketpair(socket.AF_UNIX, socket.SOCK_SEQPACKET)
        self.addCleanup(left.close)
        self.addCleanup(right.close)
        started = time.monotonic()
        end = started + 5
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        control = Path(temporary.name).resolve()
        root = HERE.parent
        hashes = {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in HERE.glob('seed_*.py')}
        loader = source.BoundSourceLoader(root, hashes)
        loader.begin_observed_execution()
        payload = {'token':'fixture', 'deadline':end, 'started':started,
                   'work_end':end-1, 'cleanup_end':end, 'root':str(root)}
        live = custody.WorkerContext(left, payload, InertGraph(), loader, control)
        loader.bind_observed_execution(live)
        events = loader.module('fixture_auxiliary_events', HERE / 'seed_observed_events.py')
        identity = custody.proc(os.getpid())
        observer = events.AuxiliaryObserver(worker_pid=os.getpid(), worker_start=identity['start'],
            cgroup=custody.group(os.getpid()), started=started, work_end=end-1,
            cleanup_end=end, spool_root=control/'auxiliary')
        values = []
        with tempfile.TemporaryFile() as output:
            def run():
                try:
                    values.append(live.command('external-bootstrap',
                        ['/usr/bin/python3','-I','-S','-B','-c',program],Path('/'),
                        {'PATH':'/usr/bin:/bin'},output,timeout))
                except BaseException as error:
                    values.append(error)
            thread = threading.Thread(target=run)
            thread.start()
            semantic = []
            while not values:
                self.assertLess(time.monotonic(), end)
                if not select.select([right], [], [], min(.05, end-time.monotonic()))[0]:
                    continue
                event = custody.receive(right,end)
                if event['kind'] == 'auxiliary-chunk':
                    observer.accept(event['chunk'])
                    custody.send(right, {'aux_ack':event['aux_sequence']}, end)
                    continue
                semantic.append(event)
                if event['kind'] == 'child-start':
                    actual = custody.proc(event['pid'])
                    self.assertEqual(actual['start'], event['start'])
                    self.assertEqual(actual['parent'], os.getpid())
                    observer.semantic_child(event['phase'],event['pid'],event['start'])
                else:
                    self.assertEqual(event['kind'], 'child-reaped')
                    self.assertFalse(Path('/proc',str(event['pid'])).exists())
                custody.send(right, {'ack':event['sequence']}, end)
            thread.join(timeout=4)
            self.assertFalse(thread.is_alive())
            children = list({id(c):c for c in [*live.observed.active.values(),
                                              *live.observed.quarantine.values()]}.values())
            for child in children:
                self.assertTrue(child.reaped)
                self.assertFalse(Path('/proc',str(child.child.pid)).exists())
                child.close_handles()
            if timeout == 2:
                self.assertEqual([r['kind'] for r in semantic], ['child-start','child-reaped'])
                observer.finish(live.observed.finish())
                self.assertEqual(observer.account.commands, 1)
            else:
                self.assertTrue(live.observed.poisoned)
            for child in observer.active.values():
                for name in ('pidfd','executable_fd','launcher_fd'):
                    if child.get(name) is not None:
                        os.close(child[name])
        return values

    def test_actual_short_child_is_observed_and_reaped(self):
        self.assertEqual(self.exercise('raise SystemExit(0)'),[0])

    def test_actual_failure_is_not_upgraded_to_zero(self):
        self.assertEqual(self.exercise('raise SystemExit(7)'),[7])

    def test_actual_timeout_kills_and_reaps_only_owned_child(self):
        values = self.exercise('import time; time.sleep(60)',timeout=.01)
        self.assertEqual(len(values),1)
        self.assertEqual(type(values[0]).__name__, 'CustodyFailure')
        self.assertIn('expired', str(values[0]))


class CommandGraphTests(unittest.TestCase):
    def make_graph(self):
        def xpy(source, config, build, host, verb, *paths):
            return ['/usr/bin/python3','-I','-S','-B',str(source/'x.py'),'--config',str(config),
                    verb,'--build-dir',str(build),'--build',host,'--host',host,'--target',host,
                    '--stage','2','--set','build.submodules=false','--set','rust.channel=trust',
                    '--set','rust.download-rustc=false','--set','llvm.download-ci-llvm=false','-j','1',*paths]
        return contract.CommandGraph(Path('/source'),Path('/source/build/run'),
            'aarch64-unknown-linux-gnu',time.monotonic()+5,xpy,Path('/orchestration'),('trustc',))

    def test_missing_and_reordered_actual_commands_refuse(self):
        graph = self.make_graph()
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            graph.finish()
        with self.assertRaisesRegex(ValueError, 'reordered'):
            graph.command('candidate-self-host',['/some/trustc'],Path('/source'),{})

    def test_changed_xpy_vector_refuses_before_any_launch(self):
        graph = self.make_graph()
        env = {'CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','TRUST_SEED_STAIRCASE':'1'}
        with self.assertRaisesRegex(ValueError, 'actual xpy'):
            graph.command('external-bootstrap',['/usr/bin/python3','--keep-stage','2'],Path('/source'),env)
        self.assertEqual(graph.commands, [])

    def test_three_role_owner_cannot_enter_v2_live_custody(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            src, cargo, orchestration = root/'source', root/'cache', root/'orchestration'
            for path in (src/'build',cargo,orchestration):
                path.mkdir(parents=True)
            with self.assertRaisesRegex(ValueError, 'all four original roles'):
                custody.OriginalLeaseCustody(source=src,cargo_home=cargo,work=src/'build/run',
                    started=time.monotonic()-1,deadline=time.monotonic()+300,
                    roles={name:(root/name,0) for name in ('host','cargo','target')},
                    source_hashes={},orchestration_root=orchestration)


if __name__ == '__main__':
    unittest.main()
