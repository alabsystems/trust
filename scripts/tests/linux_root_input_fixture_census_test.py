#!/usr/bin/env python3
"""Bounded fixture-census controls; authored UNRUN, no native/network commands."""
from __future__ import annotations
import importlib.util
import marshal
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent


def raw_module(name, path):
    with path.open('rb') as stream:
        source = stream.read(4 * 1024 * 1024 + 1)
    if len(source) > 4 * 1024 * 1024:
        raise ValueError('test subject exceeds source bound')
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    exec(compile(source,str(path),'exec',dont_inherit=True),value.__dict__)
    return value


FIXTURE = raw_module('bounded_fixture_census', HERE / 'linux_root_input_fixture.py')
EXPECTED = (
    'src/bootstrap/stage0_identity.py',
    'scripts/seed_input_closure.py', 'scripts/seed_input_records.py',
    'scripts/seed_input_committed.py', 'scripts/seed_input_archives.py',
    'scripts/bootstrap_dependency_closure.py',
    'scripts/initialize_linux_root_seed.py', 'scripts/mint_seed_support.py',
    'scripts/seed_host_ledger.py', 'scripts/seed_root_initialization.py',
    'scripts/lib/seed_linux.py',
)


class FixtureCensusTests(unittest.TestCase):
    def checkout(self):
        directory = tempfile.TemporaryDirectory(prefix='trust-fixture-census-test-')
        self.addCleanup(directory.cleanup)
        root = Path(directory.name).resolve()
        for relative in (*EXPECTED, 'scripts/seed_custody_source.py'):
            destination = root / relative
            destination.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(FIXTURE.HERE.parent / relative,destination)
        tests = root / 'scripts/tests'
        tests.mkdir()
        for name in ('linux_root_input_fixture.py','linux_root_input_closure_test.py'):
            shutil.copyfile(HERE / name, tests / name)
        return root

    def test_fixed_roster_never_discovers_checkout_builds_or_submodules(self):
        root = self.checkout()
        for relative in ('build/ignored.py','src/llvm-project/ignored.py','.git/ignored.py'):
            path = root / relative
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(b'raise AssertionError("unrelated source must not execute")\n')
        with mock.patch.object(FIXTURE,'HERE',root/'scripts'), mock.patch.object(Path,'rglob',side_effect=AssertionError('fixture must not discover the repository')):
            loader,closure,auth = FIXTURE.modules()
        self.assertEqual(FIXTURE.FIXTURE_HELPER_SOURCES,EXPECTED)
        self.assertEqual(set(loader.expected),set(EXPECTED))
        self.assertEqual(set(loader.executed),set(EXPECTED))
        self.assertEqual(len(loader.modules),11)
        self.assertIs(loader.module('fixture_stage0_identity_second_alias',root/'src/bootstrap/stage0_identity.py'),auth.support._IDENTITY_OWNER)
        self.assertIs(closure.records,closure.committed.records)
        self.assertIs(closure.records,closure.archives.records)

    def test_second_alias_retains_canonical_module_and_capability_identity(self):
        root = self.checkout()
        with mock.patch.object(FIXTURE,'HERE',root/'scripts'):
            loader,closure,auth = FIXTURE.modules()
        again = loader.module('fixture_support_second_alias',root/'scripts/mint_seed_support.py')
        self.assertIs(again,auth.support)
        self.assertEqual(len(loader.modules),11)
        self.assertEqual(set(loader.executed),set(EXPECTED))
        self.assertIs(loader.module('fixture_records_second_alias',root/'scripts/seed_input_records.py'),closure.records)

    def test_driver_ignores_valid_unchecked_hash_fixture_bytecode(self):
        root = self.checkout()
        path = root / 'scripts/tests/linux_root_input_fixture.py'
        source = path.read_bytes()
        bad = compile('raise RuntimeError("unchecked fixture pyc executed")\n',str(path),'exec')
        pyc = importlib.util.MAGIC_NUMBER + struct.pack('<I',1) + importlib.util.source_hash(source) + marshal.dumps(bad)
        cache = path.parent / '__pycache__'
        cache.mkdir()
        (cache / ('linux_root_input_fixture.' + sys.implementation.cache_tag + '.pyc')).write_bytes(pyc)
        driver = raw_module('bounded_fixture_driver',path.with_name('linux_root_input_closure_test.py'))
        self.assertEqual(set(driver.LOADER.expected),set(EXPECTED))
        self.assertEqual(set(driver.LOADER.executed),set(EXPECTED))
        self.assertEqual(driver.fixture.HERE,root/'scripts')


if __name__ == '__main__':
    unittest.main()
