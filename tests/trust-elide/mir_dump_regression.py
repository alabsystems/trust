#!/usr/bin/env python3
"""Explicit TrustVerify boundary dumps, not a source-refinement certificate.

Requires an explicit Trust compiler and a new external output directory. Raw
compiler streams, exact commands, all MIR dumps and input hashes are retained.
This development probe does not seal a toolchain or attest a complete runtime.
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


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def overflow_asserts(text):
    return sum('assert(' in line and 'overflow' in line.lower()
               for line in text.splitlines())


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trustc', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    compiler = args.trustc.resolve(strict=True)
    if compiler.name != 'trustc':
        parser.error('--trustc must explicitly name Trust, with no stock fallback')
    output = args.out.absolute()
    if output.is_symlink() or output.exists():
        parser.error('--out must be new; existing outputs are never replaced')
    resolved_output = output.resolve()
    if resolved_output == ROOT or ROOT in resolved_output.parents:
        parser.error('--out must be outside the source checkout')
    if any(key.startswith('DYLD_') for key in os.environ):
        parser.error('remove ambient DYLD overrides before this identity probe')
    output.mkdir()
    fixtures = [HERE / 'fixtures/dump_widen.rs', HERE / 'fixtures/dump_unsafe.rs']
    # Full dynamic closure is a separate sealed-toolchain preflight. Preserve
    # the launcher, stage-local drivers and every source used by this probe.
    paths = [compiler, Path(__file__).resolve(), *fixtures,
             *sorted((compiler.parent.parent / 'lib').glob('librustc_driver-*'))]

    def snapshot():
        return {'sha256': {str(path): digest(path) for path in paths if path.is_file()},
                'source_revision': subprocess.check_output(
                    ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'source_status': subprocess.check_output(
                    ['git', 'status', '--porcelain=v1'], cwd=ROOT, text=True)}

    before = snapshot()
    save(output / 'before.json', before)
    errors, runs = [], {}
    version = subprocess.run([str(compiler), '-vV'], capture_output=True, text=True, timeout=30)
    save(output / 'version.json', {'command': [str(compiler), '-vV'],
                                 'exit_code': version.returncode,
                                 'stdout': version.stdout, 'stderr': version.stderr})
    if version.returncode != 0 or 'commit-hash: ' not in version.stdout:
        raise RuntimeError('Trust compiler version probe failed')
    for label, fixture, verify, selector in [
        ('verified-boundary', fixtures[0], True, 'successor & TrustVerify'),
        ('verification-off', fixtures[0], False, 'successor'),
        ('no-dump-request', fixtures[0], True, None),
        ('nonmatching-selector', fixtures[0], True, 'NoSuchTrustPassForThisControl'),
        ('unsafe-verification-off', fixtures[1], False, 'successor'),
        ('unsafe-refusal', fixtures[1], True, 'successor & TrustVerify'),
    ]:
        run_dir = output / label
        run_dir.mkdir()
        dumps = run_dir / 'dumps'
        dumps.mkdir()
        emitted = run_dir / 'output.mir'
        command = [str(compiler), str(fixture), '--crate-type=lib', '--edition=2024',
                   '--emit=mir', '-Coverflow-checks=on', '-Zthreads=1',
                   '-Ztrust-verify=' + ('on' if verify else 'off'),
                   '-Zdump-mir-dir=' + str(dumps), '-o', str(emitted)]
        if selector is not None:
            command.append('-Zdump-mir=' + selector)
        started = time.monotonic()
        with (run_dir / 'stdout.txt').open('xb') as stdout, (run_dir / 'stderr.txt').open('xb') as stderr:
            try:
                process = subprocess.run(command, cwd=run_dir, stdout=stdout,
                                         stderr=stderr, timeout=120)
                code = process.returncode
            except subprocess.TimeoutExpired:
                code = None
        names = sorted(path.name for path in dumps.glob('*.mir'))
        boundary = [name for name in names if '.TrustVerify.' in name]
        row = {'command': command, 'exit_code': code,
               'elapsed_seconds': time.monotonic() - started,
               'dumps': {name: digest(dumps / name) for name in names},
               'trust_verify_boundaries': boundary,
               'emitted_mir_sha256': digest(emitted) if emitted.is_file() else None}
        runs[label] = row
        if label == 'unsafe-refusal':
            diagnostics = (run_dir / 'stderr.txt').read_text()
            if (code != 1 or emitted.exists()
                    or not re.search(r'\[overflow:add\] FAILED(?:[; (])', diagnostics)
                    or 'dump_unsafe::successor' not in diagnostics
                    or 'verification' not in diagnostics
                    or re.search(r'internal compiler error|compiler unexpectedly panicked|thread .* panicked', diagnostics)):
                errors.append('unsafe fixture must be refused without emitted MIR')
            # An abort may prevent the after dump; never fabricate one or
            # require a successful transition for a failed compiler process.
        elif code != 0 or not emitted.is_file():
            errors.append(label + ': compile did not complete successfully')
        elif label == 'verified-boundary':
            pre = [name for name in boundary if name.endswith('.before.mir')]
            post = [name for name in boundary if name.endswith('.after.mir')]
            if names != boundary or len(boundary) != 2 or len(pre) != 1 or len(post) != 1:
                errors.append('expected exactly one TrustVerify before/after pair')
            else:
                left, right = (dumps / pre[0]).read_text(), (dumps / post[0]).read_text()
                if overflow_asserts(left) != 1 or overflow_asserts(right) != 0:
                    errors.append('TrustVerify pair does not expose the exact overflow-check rewrite')
                if 'AddWithOverflow' not in left or 'AddWithOverflow' not in right:
                    errors.append('arithmetic disappeared from the observed boundary')
        elif label in ('verification-off', 'unsafe-verification-off'):
            if boundary or overflow_asserts(emitted.read_text()) != 1:
                errors.append('disabled verifier must leave the check, without a fabricated pass dump')
        elif names:
            errors.append('MIR pass files appeared without a dump request')
        save(run_dir / 'result.json', row)
        print(label, 'exit=' + str(code), 'boundaries=' + str(len(boundary)), flush=True)
    baseline_mir = runs['no-dump-request']['emitted_mir_sha256']
    if baseline_mir is None or any(runs[label]['emitted_mir_sha256'] != baseline_mir
                                  for label in ('verified-boundary', 'nonmatching-selector')):
        errors.append('requesting diagnostic dumps changed the emitted MIR')
    after = snapshot()
    save(output / 'after.json', after)
    if before != after:
        errors.append('probe inputs changed during compilation')
    result = {'kind': 'mir-dump-development-regression-not-refinement',
              'runs': runs, 'inputs_stable': before == after, 'errors': errors,
              'status': 'passed' if not errors else 'failed'}
    save(output / 'result.json', result)
    print(json.dumps({'status': result['status'], 'errors': errors, 'output': str(output)}, indent=2))
    return 0 if not errors else 1


if __name__ == '__main__':
    raise SystemExit(main())
