#!/usr/bin/env python3
"""Regression for unsupported-loop SAT, not a source-refinement certificate.

Run with an explicit physical Trust compiler and a NEW external output directory.
The unchanged A12 frontier must still be refused, with its original obligations,
but must not report a counterexample over an ungrounded loop state. Independently
grounded negative controls and the supported-loop positive must retain their
outcomes. Raw streams, commands, extracts and input hashes are kept on failure.
This development probe does not seal the compiler's full dependency closure.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
HELD = 'generic solver counterexample withheld:'
CRASH = re.compile(r'internal compiler error|compiler unexpectedly panicked|thread .* panicked')
FAILED = re.compile(r'\[[^\]\n]+\] FAILED(?:[; (]|$)')
# The invariant and measure are the same supported family as A6. The final
# access is genuinely out of bounds, including for the empty input, and does
# not become correct merely because the invariant was established.
SUPPORTED_LOOP_FAILURE = '''pub fn supported_loop_failure(xs: &[u8]) -> u8 {
    let mut i = 0usize;
    while i < xs.len()
        invariant i <= xs.len()
        decreases xs.len() - i
    {
        i += 1;
    }
    xs[xs.len()]
}
'''


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def check_outcome(label, code, emitted, stderr):
    """A crash, timeout, generic refusal or missing verdict is never success."""
    errors = []
    if CRASH.search(stderr):
        errors.append('compiler crashed')
    if label == 'supported-loop':
        if code != 0 or not emitted or FAILED.search(stderr) or HELD in stderr:
            errors.append('supported loop must still compile without a held or failed row')
    elif code != 1 or emitted:
        errors.append('strict negative control must refuse with exit 1 and no artifact')
    elif label == 'unsupported-loop':
        if FAILED.search(stderr) or 'counterexample:' in stderr:
            errors.append('unsupported loop must not acquire a fabricated counterexample')
        if HELD not in stderr or 'UNKNOWN' not in stderr:
            errors.append('exact unresolved dependency reason must remain visible')
        if ('UserLoopContractUnsupported' not in stderr
                or 'lo <= hi && hi <= xs.len()' not in stderr
                or 'hi - lo' not in stderr):
            errors.append('original invariant and decreases gaps must remain present')
        if not re.search(r'Trust verification: [^\n]* out of 9 obligation\(s\)', stderr):
            errors.append('original nine-obligation inventory must not shrink or disappear')
    elif not FAILED.search(stderr):
        errors.append('grounded negative control must retain an actual FAILED verdict')
    if label == 'supported-loop-failure':
        if HELD in stderr or 'UserLoopContractUnsupported' in stderr:
            errors.append('modeled loop must not be mislabeled as an unsupported dependency')
        if not re.search(r'Trust verification: 4 proved, 1 failed, 0 unknown, 0 timed out, '
                         r'0 runtime-checked out of 5 obligation\(s\)', stderr):
            errors.append('supported invariant/measure and real bounds failure must all remain measured')
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trustc', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    compiler = args.trustc.resolve(strict=True)
    if compiler.name != 'trustc' or not compiler.is_file():
        parser.error('--trustc must explicitly name Trust; no stock fallback')
    output = args.out.absolute()
    if output.is_symlink() or output.exists():
        parser.error('--out must be new; existing outputs are never replaced')
    resolved_output = output.resolve()
    if resolved_output == ROOT or ROOT in resolved_output.parents:
        parser.error('--out must be outside the source checkout')
    if any(key.startswith('DYLD_') for key in os.environ):
        parser.error('remove ambient DYLD overrides before this identity probe')
    output.mkdir()
    supported_failure = output / 'supported_loop_failure.rs'
    with supported_failure.open('x') as stream:
        stream.write(SUPPORTED_LOOP_FAILURE)
    lane = ROOT / 'tests/two-language-battery/lane-a-rust'
    fixtures = [
        ('unsupported-loop', lane / 'a12_FRONTIER_multipath_loop.rs'),
        ('supported-loop', lane / 'a6_binary_search_loop.rs'),
        ('supported-loop-failure', supported_failure),
        ('grounded-contract-failure', lane / 'a3_NEG_false_ensures.rs'),
        ('grounded-overflow-failure', HERE / 'fixtures/dump_unsafe.rs'),
    ]
    # These are stage-local candidates, not an observation of loaded libraries.
    paths = [compiler, Path(__file__).resolve(), *(path for _, path in fixtures),
             *sorted((compiler.parent.parent / 'lib').glob('librustc_driver-*'))]

    def snapshot():
        return {'sha256': {str(path): digest(path) for path in paths if path.is_file()},
                'source_revision': subprocess.check_output(
                    ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()}

    before = snapshot()
    save(output / 'before.json', before)
    version_command = [str(compiler), '-vV']
    version = subprocess.run(version_command, capture_output=True, text=True, timeout=30)
    save(output / 'version.json', {'command': version_command, 'exit_code': version.returncode,
                                  'stdout': version.stdout, 'stderr': version.stderr})
    if version.returncode != 0 or 'commit-hash: ' not in version.stdout:
        raise RuntimeError('Trust compiler version probe failed')
    runs, errors = {}, []
    for label, fixture in fixtures:
        run_dir = output / label
        run_dir.mkdir()
        emitted = run_dir / 'output.rlib'
        extracts = run_dir / 'extracts'
        extracts.mkdir()
        command = [str(compiler), str(fixture), '--edition=2021', '--crate-type=lib',
                   '-Ztrust-verify=on', '-Coverflow-checks=on', '-Zthreads=1',
                   '-Ztrust-dump=mir:' + str(extracts), '-o', str(emitted)]
        started = time.monotonic()
        with (run_dir / 'stdout.txt').open('xb') as stdout, (run_dir / 'stderr.txt').open('xb') as stderr:
            try:
                process = subprocess.run(command, cwd=run_dir, stdout=stdout, stderr=stderr, timeout=180)
                code = process.returncode
            except subprocess.TimeoutExpired:
                code = None
        diagnostics = (run_dir / 'stderr.txt').read_text(errors='replace')
        problems = check_outcome(label, code, emitted.is_file(), diagnostics)
        row = {'command': command, 'exit_code': code, 'elapsed_seconds': time.monotonic() - started,
               'artifact_sha256': digest(emitted) if emitted.is_file() else None,
               'extracts': {path.name: digest(path) for path in sorted(extracts.glob('*.json'))},
               'errors': problems}
        if not row['extracts']:
            problems.append('actual current compiler extraction was not retained')
        errors.extend(label + ': ' + error for error in problems)
        runs[label] = row
        save(run_dir / 'result.json', row)
        print(label, 'exit=' + str(code), 'errors=' + str(len(problems)), flush=True)
    after = snapshot()
    save(output / 'after.json', after)
    if before != after:
        errors.append('probe input bytes or source revision changed')
    result = {'kind': 'loop-refutation-development-regression-not-refinement',
              'status': 'passed' if not errors else 'failed', 'runs': runs,
              'inputs_stable': before == after, 'errors': errors,
              'per_compile_loaded_driver_observed': False}
    save(output / 'result.json', result)
    print(json.dumps({'status': result['status'], 'output': str(output), 'errors': errors}, indent=2))
    return 0 if not errors else 1


if __name__ == '__main__':
    raise SystemExit(main())
