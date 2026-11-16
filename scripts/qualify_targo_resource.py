#!/usr/bin/env python3
"""Observe a shipped Targo's admission protocol; never compile or grant resources."""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import signal
import stat
import sys
import tempfile
import types

SCHEMA = 'trust.shipped-targo-resource.v1'


def identity(path):
    path = path.resolve(strict=True)
    before = path.stat()
    if not stat.S_ISREG(before.st_mode):
        raise ValueError('cohort member is not a regular file: ' + str(path))
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    after = path.stat()
    key = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_mode)
    if key(before) != key(after):
        raise ValueError('cohort member changed while read: ' + str(path))
    return dict(path=str(path), sha256=h.hexdigest(), bytes=after.st_size,
                device=after.st_dev, inode=after.st_ino, mtime_ns=after.st_mtime_ns,
                ctime_ns=after.st_ctime_ns, mode=stat.S_IMODE(after.st_mode))


def cohort(root):
    paths = [root / 'bin' / name for name in ('targo', 'trustc', 'rustc')]
    for pattern in ('lib/librustc_driver-*', 'lib/rustlib/*/codegen-backends/*'):
        paths.extend(p for p in root.glob(pattern) if p.is_file())
    return {str(p.relative_to(root)): identity(p) for p in sorted(set(paths))}


def gate_owner():
    path = Path(__file__).resolve().with_name('build-slot')
    owner = types.ModuleType('shipped_targo_admission_owner')
    owner.__file__ = str(path)
    # Reuse the maintained exact decoder, bounded two-channel probe and sole
    # group cleanup/reap. Source bytes, rather than an ambient cached module.
    exec(compile(path.read_bytes(), str(path), 'exec'), owner.__dict__)
    return owner


def qualifier_identity():
    here = Path(__file__).resolve()
    return {str(path.relative_to(here.parents[1])): identity(path)
            for path in (here, here.with_name('build-slot'),
                         here.with_name('lib') / 'landing_targo.py')}


def qualify(root):
    record = dict(schema=SCHEMA, scope='read-only admission discovery; no compile, resource or SDK readiness authority',
                  sysroot=str(root), passed=False, observations=[])
    completed = False
    try:
        root = root.resolve(strict=True)
        record['sysroot'] = str(root)
        record['opening_cohort'] = cohort(root)
        record['opening_qualifier'] = qualifier_identity()
        owner = gate_owner()
        original_env, original_cwd = os.environ.copy(), Path.cwd()
        scratch_parent = Path(tempfile.gettempdir()) / '.ubd'
        scratch_parent.mkdir(mode=0o700, exist_ok=True)
        if scratch_parent.is_symlink() or not scratch_parent.is_dir():
            raise ValueError('scratch parent is not an ordinary directory')
        with tempfile.TemporaryDirectory(prefix='shipped-targo-resource-', dir=scratch_parent) as temporary:
            work = Path(temporary).resolve()
            for name in ('home', 'cargo', 'rustup', 'tmp', 'project/src'):
                (work / name).mkdir(parents=True, exist_ok=True)
            (work / 'project/Cargo.toml').write_text(
                '[package]\nname="shipped-resource-probe"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
            (work / 'project/src/lib.rs').write_text('// Capability discovery never compiles this file.\n')
            environment = dict(PATH=str(root / 'bin') + os.pathsep + '/usr/bin:/bin:/usr/sbin:/sbin',
                               HOME=str(work / 'home'), CARGO_HOME=str(work / 'cargo'),
                               TARGO_HOME=str(work / 'cargo'), RUSTUP_HOME=str(work / 'rustup'),
                               TMPDIR=str(work / 'tmp'), LC_ALL='C')
            record.update(environment=environment, cwd=str(work / 'project'),
                          manifest=(work / 'project/Cargo.toml').read_text())
            try:
                os.environ.clear()
                os.environ.update(environment)
                os.chdir(work / 'project')
                for verb in ('check', 'test'):
                    command = [str(root / 'bin/targo'), '--unverified', verb, '--locked', '--offline',
                               '--manifest-path', str(work / 'project/Cargo.toml')]
                    if verb == 'test':
                        command.append('--lib')
                    row = dict(command=command, argv=[command[0], '--resource-capabilities', '--', *command[1:]],
                               capture_complete=False,
                               capture_scope='completed probe raw streams; transport failures retain bounded original diagnostics in refusal')
                    record['observations'].append(row)
                    def observed(argv, code, stdout, stderr):
                        row.update(argv=argv, exit=code, capture_complete=True,
                                   stdout_base64=base64.b64encode(stdout).decode('ascii'),
                                   stderr_base64=base64.b64encode(stderr).decode('ascii'))
                    native = owner.worker_capability(command, observation=observed)
                    if not row['capture_complete']:
                        raise ValueError('selected profile has no complete capability observation')
                    row['supported_boundary'] = 'native-workers-v2' if native else 'fixed'
            finally:
                os.chdir(original_cwd)
                os.environ.clear()
                os.environ.update(original_env)
        completed = True
    except (OSError, ValueError, RuntimeError) as error:
        record['refusal'] = str(error)
    # A refusal is an observation too. Close both books without replacing its
    # original cause, and disclose unavailable closing observations explicitly.
    for name, reader in (('cohort', lambda: cohort(root)), ('qualifier', qualifier_identity)):
        try:
            record['closing_' + name] = reader()
        except (OSError, ValueError, RuntimeError) as error:
            record['closing_' + name + '_error'] = str(error)
    stable = all('opening_' + name in record
                 and record.get('closing_' + name) == record['opening_' + name]
                 for name in ('cohort', 'qualifier'))
    record['inputs_stable'] = stable
    if not stable:
        record.setdefault('refusal', 'shipped frontend/compiler cohort changed or qualifier source changed during discovery')
    record['passed'] = completed and stable
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sysroot', required=True, type=Path)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    if args.receipt is not None:
        if not args.receipt.is_absolute() or args.receipt.resolve().is_relative_to(args.sysroot.resolve()):
            parser.error('receipt must be absolute and outside the shipped SDK')
        if os.path.lexists(args.receipt):
            parser.error('receipt already exists; use a new epoch')
    def stop(signum, frame):
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, stop)
    result = qualify(args.sysroot)
    raw = json.dumps(result, sort_keys=True, separators=(',', ':')) + '\n'
    if args.receipt is not None:
        # A failed observation must remain a failure even if its receipt cannot
        # be persisted. Never overwrite an earlier epoch or the shipped SDK.
        with args.receipt.open('x') as stream:
            stream.write(raw)
    print('targo-resource-qualification=' + raw, end='', flush=True)
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
