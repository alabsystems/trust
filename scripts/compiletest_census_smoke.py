#!/usr/bin/env python3
"""Focused real compiletest case/command census qualification; never runs test binaries."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import shutil
from pathlib import Path
import subprocess

from compiletest_census import read_census


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--compiletest', required=True, type=Path)
    p.add_argument('--rustc', required=True, type=Path)
    p.add_argument('--sysroot', required=True, type=Path)
    p.add_argument('--out', required=True, type=Path)
    p.add_argument('--incremental-only', action='store_true')
    a = p.parse_args()
    out = a.out.absolute()
    out.mkdir(exist_ok=False)
    repo = Path(__file__).resolve().parent.parent
    mode = 'incremental' if a.incremental_only else 'ui'
    fixtures = repo/'scripts/tests/fixtures/compiletest-census'/mode
    inputs = out/'inputs'
    suite = inputs/'tests'/mode
    shutil.copytree(fixtures, suite)
    (inputs/'src').symlink_to(repo/'src', target_is_directory=True)
    (inputs/'tests/auxiliary').symlink_to(repo/'tests/auxiliary', target_is_directory=True)
    build = out/'build'
    (build/mode).mkdir(parents=True)
    host = subprocess.check_output([str(a.rustc), '-vV'], text=True)
    triple = next(line.removeprefix('host: ') for line in host.splitlines() if line.startswith('host: '))
    cmd = [str(a.compiletest), '--rustc-path', str(a.rustc), '--compile-lib-path', str(a.sysroot/'lib'),
           '--run-lib-path', str(a.sysroot/'lib/rustlib'/triple/'lib'), '--sysroot-base', str(a.sysroot),
           '--src-root', str(inputs), '--src-test-suite-root', str(suite), '--build-root', str(build),
           '--build-test-suite-root', str(build/mode), '--stage', '1', '--stage-id', 'stage1-'+triple,
           '--mode', mode, '--suite', mode, '--python', '/usr/bin/python3', '--cc', 'cc', '--cxx', 'c++',
           '--cflags=', '--cxxflags=', '--llvm-components=', '--channel', 'nightly', '--nightly-branch', 'main',
           '--git-merge-commit-email', 'bors@rust-lang.org', '--minicore-path', str(repo/'tests/auxiliary/minicore.rs'),
           '--jobs', '2', '--host', triple, '--target', triple, '--trust-vanilla', '--force-rerun',
           '--trust-invocation-census', str(out/'census')]
    env = os.environ.copy()
    env['RUST_TEST_THREADS'] = '2'
    with (out/'harness.log').open('wb') as log:
        result = subprocess.run(cmd, cwd=repo, env=env, stdout=log, stderr=subprocess.STDOUT)
    binding = {'argv': cmd, 'exit': result.returncode, 'rustc_version': host,
               'compiletest_sha256': digest(a.compiletest), 'rustc_sha256': digest(a.rustc),
               'fixtures': {str(path.relative_to(repo)): digest(path) for path in sorted(fixtures.rglob('*')) if path.is_file()},
               'scope': 'complete '+mode+' fixture group only; normal compiler invocations; no test-program execution'}
    (out/'RUN.json').write_text(json.dumps(binding, indent=2)+'\n')
    assert result.returncode == 0, f'harness failed: {out}/harness.log'
    report = read_census(out/'census')
    (out/'REPORT.json').write_text(json.dumps(report, indent=2)+'\n')
    if a.incremental_only:
        assert len(report['planned']) == 1 and report['planned'][0]['revision'] is None
        assert report['planned'][0]['all_revisions'] == ['bpass1', 'bpass2']
        assert report['planned'][0]['terminal']['outcome'] == 'ok'
        commands = report['commands']
        assert len(commands) == 2 and all(c['terminal']['success'] for c in commands)
        assert {c['attempt']['case'] for c in commands} == {report['planned'][0]['case']}
        assert [c['attempt']['revision'] for c in commands] == ['bpass1', 'bpass2']
        parsed = [obs for c in commands for obs in c['observations'] if obs.get('status') == 'parsed']
        assert sum(o['kind'] == 'trust-body-census' and o['observation']['status'] == 'complete' for o in parsed) == 2
        assert sum(o['kind'] == 'trust-instance-census' and o['observation']['status'] == 'collector_observed' for o in parsed) == 2
        print('PASS: one aggregate incremental case binds both actual revisions and two HIR/mono observations')
        return
    assert len(report['planned']) == 4
    assert all(row['selected'] for row in report['planned'])
    assert sorted(row['terminal']['outcome'] for row in report['planned']) == ['ignored', 'ok', 'ok', 'ok']
    commands = report['commands']
    assert len(commands) == 5 and all(row['attempt']['kind'] == 'selected-rustc' for row in commands)
    assert sum(row['terminal']['success'] for row in commands) == 4
    assert all(row['spawn_pid_recorded'] for row in commands)
    assert len({row['attempt']['case'] for row in commands}) == 3
    parsed = [obs for cmdrow in commands for obs in cmdrow['observations'] if obs.get('status') == 'parsed']
    assert sum(row['kind'] == 'trust-body-census' and row['observation']['status'] == 'complete' for row in parsed) == 4
    assert sum(row['kind'] == 'trust-instance-census' and row['observation']['status'] == 'collector_observed' for row in parsed) == 4
    assert len(report['collection_exclusions']) == 1
    assert report['collection_exclusions'][0]['reason'] == 'compiletest-ignore-dir'
    assert any(body['producer'] is not None for cmdrow in commands for body in cmdrow['producer_body_join'].get('bodies', []))
    assert report['whole_corpus_complete'] is False
    # A filtered run must retain the original plan. It executes no test binary
    # and no rustc: only the deliberately ignored case is selected.
    filtered_cmd = list(cmd)
    filtered_cmd[filtered_cmd.index('--trust-invocation-census')+1] = str(out/'filtered-census')
    filtered_cmd.append('ignored.rs')
    with (out/'filtered.log').open('wb') as log:
        filtered = subprocess.run(filtered_cmd, cwd=repo, env=env, stdout=log, stderr=subprocess.STDOUT)
    assert filtered.returncode == 0
    filtered_report = read_census(out/'filtered-census')
    assert len(filtered_report['planned']) == 4
    assert sum(row['selected'] for row in filtered_report['planned']) == 1
    assert not filtered_report['commands']
    (out/'FILTERED-REPORT.json').write_text(json.dumps(filtered_report, indent=2)+'\n')
    before = digest(out/'filtered-census/events.jsonl')
    with (out/'create-only-refusal.log').open('wb') as log:
        repeated = subprocess.run(filtered_cmd, cwd=repo, env=env, stdout=log, stderr=subprocess.STDOUT)
    assert repeated.returncode != 0 and before == digest(out/'filtered-census/events.jsonl')
    (out/'CONTROLS.json').write_text(json.dumps({'filter_argv': filtered_cmd, 'filter_exit': filtered.returncode,
        'create_only_exit': repeated.returncode, 'existing_record_unchanged_sha256': before}, indent=2)+'\n')
    print('PASS: 4 planned cases, 5 actual compiler commands, 4 HIR and 4 mono observations; ignored/invalid preserved')


if __name__ == '__main__':
    main()
