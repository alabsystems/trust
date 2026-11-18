#!/usr/bin/env python3
"""Select real locked Source roots without acquiring unrelated recipe inputs."""
import json
import os
import runpy
import shutil
import tempfile
from pathlib import Path
import shlex
import subprocess
import sys
import time
import unittest
from unittest import mock

import daily_toolchain_stage_test as existing


class SelectedManifestPreparationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.source = self.root / 'source'
        self.work = self.root / 'work'
        self.source.mkdir()
        self.work.mkdir()
        self.trace = self.work / 'rust-driver-trace'
        repo = existing.SCRIPT.parents[1]
        self.closure = runpy.run_path(str(repo / 'scripts/bootstrap_dependency_closure.py'))
        self.recreator = runpy.run_path(str(repo / 'scripts/recreate_bootstrap.py'))
        for name in ('scripts/recreate_bootstrap.py', 'scripts/source_working_cache.py',
                     'scripts/seed_custody_source.py', 'scripts/bootstrap_dependency_closure.py',
                     'src/bootstrap/stage0_identity.py'):
            target = self.source / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(repo / name, target)
        for name in self.closure['_RECIPE_INPUTS']:
            path = self.source / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('')
        (self.source / self.closure['_RECIPE_INPUTS'][-1]).write_text(
            'fn ensure_default_verifier_tool_bins() { ToolBuild { path: "tool", } }\n'
            'fn ensure_user_facing_tools() { ToolBuild { path: "tool", } }\n')
        (self.source / 'src/bootstrap/src/core/build_steps/vendor.rs').write_text(
            "pub fn default_paths_to_vendor(builder: &Builder<'_>) -> Vec<(PathBuf, Vec<&'static str>)> {\n"
            'let paths: Vec<(&str, Vec<&staticstr>)> = vec![("dist-only/Cargo.toml", vec![]),];\n'
            'paths.into_iter().map(|(path, submodules)| (builder.src.join(path), submodules)).collect() }'.replace('&staticstr', "&'static str"))
        for name in (*self.closure['_BASE_MANIFESTS'], 'tool/Cargo.toml', 'dist-only/Cargo.toml'):
            path = self.source / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('[workspace]\nmembers = []\n')
            path.with_name('Cargo.lock').write_text('version = 4\n')

    def transport(self):
        return existing.DependencyFetchBoundaryTests.transport(self)

    def git(self, root, *args):
        return subprocess.check_output(['git', '-C', str(root), *args], text=True,
                                       stderr=subprocess.DEVNULL).strip()

    def commit_inputs(self, root=None):
        root = root or self.source
        subprocess.run(['git', 'init', '-q', '--template=', str(root)], check=True)
        self.git(root, 'config', 'user.name', 'Source fixture')
        self.git(root, 'config', 'user.email', 'source@example.invalid')
        self.git(root, 'add', 'Cargo.toml', 'Cargo.lock')
        self.git(root, 'commit', '-qm', 'locked Source fixture')

    def prepare_selected(self, manifests):
        self.commit_inputs()
        cache = self.work / 'cargo-home'
        cache.mkdir(exist_ok=True)
        return self.transport()['prepare_profile'](
            self.source, self.work, cache, self.closure, self.recreator,
            {'HOME': str(self.work), 'CARGO_HOME': str(cache)}, deadline=time.monotonic() + 900, manifest_paths=manifests)

    def test_actual_selection_ignores_unselected_broken_recipe_and_keeps_default(self):
        (self.source / 'tool/Cargo.toml').write_text('invalid manifest [')
        policy, document = self.prepare_selected(['Cargo.toml'])
        self.assertEqual(document['manifest_selection']['manifests'], ['Cargo.toml'])
        self.assertEqual(sorted(document['manifest_selection']['tracked_inputs']), ['Cargo.lock', 'Cargo.toml'])
        self.assertEqual(document['locks'], ['Cargo.lock'])
        self.assertEqual(document['acquisitions'], [])
        self.assertEqual(json.loads(policy.read_text()), document)
        with self.assertRaisesRegex(RuntimeError, 'inconclusive'):
            self.transport()['prepare_profile'](
                self.source, self.work, self.work / 'cargo-home', self.closure, self.recreator,
                {'HOME': str(self.work), 'CARGO_HOME': str(self.work / 'cargo-home')},
                deadline=time.monotonic() + 900)

    def locked_git_fixture(self):
        origin = self.root / 'probe=original'
        origin.mkdir()
        (origin / 'Cargo.toml').write_text('[package]\nname = "probe"\nversion = "0.1.0"\n')
        (origin / 'Cargo.lock').write_text('version = 4\n')
        self.commit_inputs(origin)
        oid = self.git(origin, 'rev-parse', 'HEAD')
        lock_source = 'git+https://github.com/Owner/probe#' + oid
        (self.source / 'Cargo.lock').write_text(
            'version = 4\n[[package]]\nname = "probe"\nversion = "0.1.0"\nsource = ' + json.dumps(lock_source) + '\n')
        self.commit_inputs()
        return origin, oid

    def test_owner_routed_checkout_can_finish_after_six_hundred_seconds(self):
        origin, oid = self.locked_git_fixture()
        api = self.transport()
        # The item's clock and its measure: a transfer that keeps moving at 64 B/s.
        now = [100.0]
        owner = {**self.recreator, '_dependency_clock': lambda: now[0],
                 '_dependency_measure': lambda paths: int(now[0] * 64)}
        cache = self.work / 'cargo-home'
        cache.mkdir()
        client = self.root / 'agh'
        client.write_text('#!/bin/sh\nexit 99\n')
        client.chmod(0o700)
        commands, scratches = [], []

        def transfer(argv, *, environment, timeout_seconds, credential_gh, progress=None):
            commands.append(argv)
            # No fixed child bound: the item runs while it moves, until the preparation's ceiling.
            self.assertIsNone(timeout_seconds)
            self.assertIsNone(credential_gh)
            destination = Path(argv[4])
            self.assertIsInstance(progress, owner['_SubmoduleProgress'])
            # The source and the scratch Agh writes it in first, in this acquisition's own folder.
            self.assertEqual(progress.paths, (destination, Path(environment['TMPDIR'])))
            self.assertEqual(Path(environment['TMPDIR']).parent, destination.parent.resolve())
            scratches.append(Path(environment['TMPDIR']))
            self.assertEqual(argv[5:], ['--ref', oid, '--into',
                                       'refs/agh/trust-daily-dependencies/' + oid, '--checkout-closure'])
            subprocess.run(['git', '-c', 'protocol.file.allow=always', '-C', str(destination), 'fetch',
                            '--quiet', '--no-tags', str(origin), f'{oid}:{argv[8]}'],
                           check=True, capture_output=True)
            progress.begin()
            for now[0] in (400.0, 840.0):  # 740 s in, past the former fixed 600 s
                progress.check(argv)
            return subprocess.CompletedProcess(argv, 0)

        owner['_run_submodule_update_process'] = transfer
        with mock.patch.dict(owner['_agh_source_fetch'].__globals__, {'which': lambda name: str(client)}):
            _, profile = api['prepare_profile'](
                self.source, self.work, cache, self.closure, owner, {'HOME': str(self.work), 'CARGO_HOME': str(cache)},
                deadline=1100, manifest_paths=['Cargo.toml'])
        self.assertEqual(len(commands), 1)
        self.assertEqual(len(scratches), 1)
        self.assertFalse(scratches[0].exists())
        self.assertEqual(now[0], 840.0)
        self.assertEqual(profile['deadline'], 1100)
        self.assertEqual([(row['method'], row['commit']) for row in profile['acquisitions']],
                         [('owner-routed-agh', oid)])

    def test_cli_binds_declared_checkout_cache_to_exact_locked_request(self):
        origin, oid = self.locked_git_fixture()
        helper = existing.SCRIPT.with_name('daily_dependency_git.py')
        shutil.copyfile(helper.with_name('bootstrap_dependency_closure.py'),
                        self.source / 'scripts/bootstrap_dependency_closure.py')
        cache = self.work / 'cargo-home'
        cache.mkdir()
        args_record = self.work / 'agh-args.json'
        client = self.work / 'agh'
        driver = self.work / 'agh-fixture.py'
        driver.write_text(
            'import json, subprocess, sys\n'
            'from pathlib import Path\n'
            'args = sys.argv\n'
            f'Path({str(args_record)!r}).write_text(json.dumps(args[1:]))\n'
            'subprocess.run(["/usr/bin/git", "-c", "protocol.file.allow=always", "-C", args[4],\n'
            '                "fetch", "--quiet", "--no-tags", args[11], args[6] + ":" + args[8]], check=True)\n')
        client.write_text('#!/bin/sh\nexec ' + shlex.join([sys.executable, '-B', str(driver)]) + ' "$@"\n')
        client.chmod(0o700)
        output = self.work / 'selected-profile.json'
        environment = {**os.environ, 'PATH': str(self.work) + os.pathsep + os.environ['PATH']}
        command = [sys.executable, '-B', str(helper), 'prepare-profile', '--source', str(self.source),
                   '--work', str(self.work), '--cargo-home', str(cache), '--manifest', 'Cargo.toml',
                   '--output', str(output), '--checkout-cache', f'https://github.com/Owner/probe#{oid}={origin}']
        result = subprocess.run(command, capture_output=True, text=True, env=environment)
        self.assertEqual(result.returncode, 0, result.stderr)
        recorded = json.loads(args_record.read_text())
        self.assertEqual(recorded[:3], ['repo', 'fetch', 'Owner/probe'])
        self.assertEqual(recorded[4:], ['--ref', oid, '--into', 'refs/agh/trust-daily-dependencies/' + oid,
                                       '--checkout-closure', '--checkout-cache', str(origin)])
        profile = json.loads(Path(json.loads(output.read_text())['policy']).read_text())
        self.assertEqual(len(profile['acquisitions']), 1)
        acquisition = profile['acquisitions'][0]
        self.assertEqual((acquisition['method'], acquisition['commit'], acquisition['checkout_cache']),
                         ('owner-routed-agh', oid, str(origin)))
        self.assertEqual(self.git(origin, 'rev-parse', 'HEAD'), oid)

    def test_cli_refuses_checkout_cache_outside_selected_source_graph(self):
        self.commit_inputs()
        helper = existing.SCRIPT.with_name('daily_dependency_git.py')
        shutil.copyfile(helper.with_name('bootstrap_dependency_closure.py'),
                        self.source / 'scripts/bootstrap_dependency_closure.py')
        cache = self.work / 'cargo-home'
        cache.mkdir()
        output = self.work / 'selected-profile.json'
        result = subprocess.run([
            sys.executable, '-B', str(helper), 'prepare-profile', '--source', str(self.source),
            '--work', str(self.work), '--cargo-home', str(cache), '--manifest', 'Cargo.toml',
            '--output', str(output), '--checkout-cache', f'https://github.com/Owner/probe#{"a" * 40}={self.source}',
        ], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('checkout caches do not match selected dependency sources', result.stderr)
        self.assertFalse(output.exists())

    def test_aliased_cargo_home_refuses_before_any_source_acquisition(self):
        self.locked_git_fixture()
        physical = self.work / 'build.noindex'
        (physical / 'bootstrap-cargo-home').mkdir(parents=True)
        alias = self.work / 'build'
        alias.symlink_to(physical, target_is_directory=True)
        cache = alias / 'bootstrap-cargo-home'
        fetch = mock.Mock(side_effect=AssertionError('Agh must not start with aliased cache custody'))
        owner = {**self.recreator, '_agh_source_fetch': fetch}

        with self.assertRaisesRegex(RuntimeError, 'symbolic or missing custody'):
            self.transport()['prepare_profile'](
                self.source, self.work, cache, self.closure, owner, {'HOME': str(self.work), 'CARGO_HOME': str(cache)},
                deadline=time.monotonic() + 900, manifest_paths=['Cargo.toml'])
        fetch.assert_not_called()
        self.assertFalse(list(self.work.glob('agh-git-*')))

    def test_independent_workspace_keeps_its_own_manifest_and_lock(self):
        source = self.root / 'independent'
        source.mkdir()
        (source / 'Cargo.toml').write_text('[workspace]\nmembers = []\n')
        (source / 'Cargo.lock').write_text('version = 4\n')
        self.commit_inputs(source)
        cache = self.work / 'cargo-home'
        cache.mkdir()
        helper = existing.SCRIPT.with_name('daily_dependency_git.py')
        orchestration = helper.resolve().parents[1]
        output = self.work / 'external-profile.json'
        result = subprocess.run([
            sys.executable, '-B', str(helper), 'prepare-profile', '--source', str(source),
            '--orchestration-source', str(orchestration), '--work', str(self.work),
            '--cargo-home', str(cache), '--manifest', 'Cargo.toml', '--output', str(output),
        ], check=True, capture_output=True, text=True)
        receipt = json.loads(result.stdout)
        self.assertEqual(receipt, json.loads(output.read_text()))
        self.assertEqual(receipt['source'], str(source))
        self.assertEqual(receipt['orchestration_source'], str(orchestration))
        policy = Path(receipt['policy'])
        profile = json.loads(policy.read_text())
        self.assertEqual(profile['locks'], ['Cargo.lock'])
        self.assertEqual(profile['manifest_selection']['repositories'], {'.': self.git(source, 'rev-parse', 'HEAD')})
        self.assertIn(str(orchestration / 'scripts/recreate_bootstrap.py'), profile['source_inputs_sha256'])
        self.assertIn(str(source / 'Cargo.lock'), profile['source_inputs_sha256'])
        callback = [sys.executable, '-B', str(helper), '--policy', str(policy), '--']
        subprocess.run([*callback, '--version'], check=True, capture_output=True)
        lock = source / 'Cargo.lock'
        lock.write_text(lock.read_text() + '# changed lock\n')
        refused = subprocess.run([*callback, 'gc', '--auto'], capture_output=True, text=True)
        self.assertEqual(refused.returncode, 2)
        self.assertIn('differs from its prepared policy', refused.stderr)

    def test_selection_refuses_escape_alias_duplicate_and_empty(self):
        self.commit_inputs()
        api = self.transport()
        (self.source / 'alias').symlink_to(self.source, target_is_directory=True)
        # Every local Git query runs under the preparation's ceiling, as inside prepare_profile.
        owner = {**self.recreator, '_dependency_deadline': time.monotonic() + 900}
        for names in ([], ['../Cargo.toml'], ['/Cargo.toml'], ['Cargo.toml', 'Cargo.toml'],
                      ['alias/Cargo.toml'], ['Cargo.lock'], ['.git/Cargo.toml']):
            with self.subTest(names=names), self.assertRaises(RuntimeError):
                api['selected_manifest_roots'](self.source, names, owner)
        self.assertEqual(api['selected_manifest_roots'](self.source, ['Cargo.toml'], owner),
                         [self.source / 'Cargo.toml'])

    def test_owner_lock_must_be_tracked_and_match_actual_source(self):
        self.commit_inputs()
        cache = self.work / 'cargo-home'
        cache.mkdir()
        api = self.transport()
        arguments = (self.source, self.work, cache, self.closure, self.recreator,
                     {'HOME': str(self.work), 'CARGO_HOME': str(cache)})
        lock = self.source / 'Cargo.lock'
        lock.write_text('version = 4\n# uncommitted resolver input\n')
        with self.assertRaisesRegex(RuntimeError, 'differs from its Source index'):
            api['prepare_profile'](*arguments, deadline=time.monotonic() + 900, manifest_paths=['Cargo.toml'])
        self.git(self.source, 'checkout', '--', 'Cargo.lock')
        self.git(self.source, 'rm', '--cached', 'Cargo.lock')
        with self.assertRaisesRegex(RuntimeError, 'tracked regular Source input'):
            api['prepare_profile'](*arguments, deadline=time.monotonic() + 900, manifest_paths=['Cargo.toml'])
        self.assertFalse(list(self.work.glob('agh-git-*')))

    def test_selected_component_uses_its_own_tracked_lock(self):
        self.commit_inputs()
        child = self.source / 'first-party/selected'
        child.mkdir(parents=True)
        (child / 'Cargo.toml').write_text('[workspace]\nmembers = []\n')
        (child / 'Cargo.lock').write_text('version = 4\n')
        self.commit_inputs(child)
        cache = self.work / 'cargo-home'
        cache.mkdir()
        arguments = (self.source, self.work, cache, self.closure, self.recreator,
                     {'HOME': str(self.work), 'CARGO_HOME': str(cache)})
        with self.assertRaisesRegex(RuntimeError, 'exact indexed Source gitlink'):
            self.transport()['prepare_profile'](*arguments, deadline=time.monotonic() + 900, manifest_paths=['first-party/selected/Cargo.toml'])
        (self.source / '.gitmodules').write_text(
            '[submodule "selected"]\npath=first-party/selected\nurl=https://github.com/Owner/selected.git\n')
        self.git(self.source, 'add', '.gitmodules')
        head = self.git(child, 'rev-parse', 'HEAD')
        self.git(self.source, 'update-index', '--add', '--cacheinfo', '160000', head, 'first-party/selected')
        self.git(self.source, 'commit', '-qm', 'pin the selected component Source')
        _, document = self.transport()['prepare_profile'](*arguments,
            deadline=time.monotonic() + 900, manifest_paths=['first-party/selected/Cargo.toml'])
        self.assertEqual(document['locks'], ['first-party/selected/Cargo.lock'])
        self.assertEqual(document['manifest_selection']['manifests'], ['first-party/selected/Cargo.toml'])

    def test_staged_outer_input_must_match_committed_source(self):
        self.commit_inputs()
        manifest = self.source / 'Cargo.toml'
        manifest.write_text(manifest.read_text() + '# staged alternate input\n')
        self.git(self.source, 'add', 'Cargo.toml')
        cache = self.work / 'cargo-home'
        cache.mkdir()
        with self.assertRaisesRegex(RuntimeError, 'committed Source HEAD'):
            self.transport()['prepare_profile'](
                self.source, self.work, cache, self.closure, self.recreator,
                {'HOME': str(self.work), 'CARGO_HOME': str(cache)}, deadline=time.monotonic() + 900, manifest_paths=['Cargo.toml'])

    def test_later_committed_input_cannot_replace_the_prepared_body(self):
        policy, _ = self.prepare_selected(['Cargo.toml'])
        manifest = self.source / 'Cargo.toml'
        manifest.write_text(manifest.read_text() + '# later committed input\n')
        self.git(self.source, 'add', 'Cargo.toml')
        self.git(self.source, 'commit', '-qm', 'later Source')
        with self.assertRaisesRegex(RuntimeError, 'differs from its prepared policy'):
            self.transport()['git_entry'](policy, ['gc', '--auto'])
        self.transport()['git_entry'](policy, ['--version'])

    def test_same_path_fifo_refuses_without_blocking(self):
        policy, _ = self.prepare_selected(['Cargo.toml'])
        manifest = self.source / 'Cargo.toml'
        manifest.unlink()
        os.mkfifo(manifest)
        result = subprocess.run([sys.executable, '-B', str(existing.SCRIPT.with_name('daily_dependency_git.py')),
                                 '--policy', str(policy), '--', 'gc', '--auto'],
                                capture_output=True, text=True, timeout=5)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('differs from its prepared policy', result.stderr)

    def test_cli_prepares_only_transport_and_records_one_selection(self):
        self.commit_inputs()
        repo = existing.SCRIPT.parents[1]
        (self.source / 'scripts/bootstrap_dependency_closure.py').write_bytes(
            (repo / 'scripts/bootstrap_dependency_closure.py').read_bytes())
        cache = self.work / 'cargo-home'
        cache.mkdir()
        output = self.work / 'selected-profile.json'
        argv = [sys.executable, '-B', str(repo / 'scripts/daily_dependency_git.py'),
                'prepare-profile', '--source', str(self.source), '--work', str(self.work),
                '--cargo-home', str(cache), '--manifest', 'Cargo.toml', '--output', str(output)]
        result = subprocess.run(argv, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        record = json.loads(output.read_text())
        self.assertEqual(record['manifest_selection']['manifests'], ['Cargo.toml'])
        policy = json.loads(Path(record['policy']).read_text())
        self.assertEqual(record['manifest_selection'], policy['manifest_selection'])
        self.assertFalse(self.trace.exists(), 'a Source-only profile must not run a Rust driver')
        retry = subprocess.run(argv, capture_output=True, text=True)
        self.assertNotEqual(retry.returncode, 0)
        self.assertIn('result already exists', retry.stderr)


if __name__ == '__main__':
    unittest.main()
