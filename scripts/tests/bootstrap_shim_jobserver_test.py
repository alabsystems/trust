#!/usr/bin/env python3
"""Check actual bootstrap shim jobserver handoff on Unix without building anything.

Provide ordinary rustc/rustdoc shim artifacts, a Trust SDK and its host triple.
The SDK queries use the repository's explicit no-proof Cargo fixture context;
the controlled driver observes descriptors separately and makes no compile claim.
All logs are retained in a new --output directory. Use --require-fixed to fail on
any failed control; omit it to retain a RED baseline with the same oracle.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import time

METADATA = ('CARGO_MAKEFLAGS', 'MAKEFLAGS', 'MFLAGS')
SDK = None
HOST = None
DRIVER = None

def canonical_context():
    return dict(RUSTC_REAL=str(SDK / 'bin/trustc'), RUSTC_SNAPSHOT=str(SDK / 'bin/trustc'),
                RUSTC_LIBDIR=str(SDK / 'lib'), RUSTC_SNAPSHOT_LIBDIR=str(SDK / 'lib'),
                RUSTDOC_REAL=str(SDK / 'bin/trustdoc'), RUSTDOC_LIBDIR=str(SDK / 'lib'),
                RUSTC_SYSROOT=str(SDK), RUSTC_STAGE='1', CFG_COMPILER_BUILD_TRIPLE=HOST,
                RUSTC_LINK_STD_INTO_RUSTC_DRIVER='0', TRUST_BOOTSTRAP_SHIM_NO_VERIFY='1',
                TRUST_CARGO_TEST_SHIM_VERSION='3', TRUST_VANILLA_ANNOUNCED='1')

def identity(fd):
    try:
        item = os.fstat(fd)
        return {'open': True, 'device': item.st_dev, 'inode': item.st_ino,
                'kind': stat.S_IFMT(item.st_mode), 'flags': fcntl.fcntl(fd, fcntl.F_GETFD)}
    except OSError as error:
        return {'open': False, 'errno': error.errno}

def observer():
    """A controlled compiler stand-in, never a production compiler claim."""
    original = json.loads(os.environ['FD_CONTROL_INPUTS'])
    observed = {name: identity(fd) for name, fd in original['fds'].items()}
    census = {str(fd): value for fd in range(3, 256) if (value := identity(fd))['open']}
    flags = {name: os.environ[name] for name in METADATA if name in os.environ}
    selected = next((flags[key] for key in METADATA if key in flags), '')
    auth = re.search(r'(?:^|\s)--jobserver-auth=([^\s]+)', selected)
    if auth is None:
        auth = re.search(r'(?:^|\s)--jobserver-fds=([^\s]+)', selected)
    token = {'attempted': False}
    opened = []
    advertised = {}
    if auth:
        transport = auth.group(1)
        try:
            if transport.startswith('fifo:'):
                read = write = os.open(transport[5:], os.O_RDWR | os.O_NONBLOCK)
                opened.append(read)
            elif re.fullmatch(r'[0-9]+,[0-9]+', transport):
                read, write = map(int, transport.split(','))
            else:
                raise ValueError('not a numeric pair or named FIFO')
            advertised = {'read': {'fd': read, **identity(read)},
                          'write': {'fd': write, **identity(write)}}
            if all(advertised[key].get('kind') == stat.S_IFIFO for key in ('read', 'write')):
                token['attempted'] = True
                data = os.read(read, 1)
                token['read_hex'] = data.hex()
                token['written'] = os.write(write, data)
        except (OSError, ValueError) as error:
            token['error'] = type(error).__name__ + ': ' + str(error)
    for fd in opened:
        os.close(fd)
    print(json.dumps({'controlled_driver': True, 'argv': sys.argv[1:],
                      'original_fds': observed, 'metadata': flags,
                      'advertised': advertised, 'token': token,
                      'pre_observer_open_fds_3_through_255': census}, sort_keys=True))
    return 0

def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def file_identity(path):
    return {'path': str(path), 'physical_path': str(path.resolve(strict=True)),
            'bytes': path.stat().st_size, 'sha256': sha(path)}

def high_copy(fd, minimum):
    return fcntl.fcntl(fd, fcntl.F_DUPFD_CLOEXEC, minimum)

def pipe(minimum):
    first, second = os.pipe()
    try:
        read = high_copy(first, minimum)
        write = high_copy(second, minimum + 1)
    finally:
        os.close(first)
        os.close(second)
    os.set_blocking(read, False)
    return read, write

def run_one(out, label, executable, argv, transport, *, controlled, root, direct_control=False):
    destination = out / label
    destination.mkdir()
    owned = []
    pair = pipe(100)
    owned.extend(pair)
    other = pipe(120)
    owned.extend(other)
    fds = {'read': pair[0], 'write': pair[1], 'unrelated_read': other[0], 'unrelated_write': other[1]}
    passing = list(owned)
    token_read, token_write = pair
    flags = {'CARGO_MAKEFLAGS': f'-j --jobserver-fds={pair[0]},{pair[1]} --jobserver-auth={pair[0]},{pair[1]}'}
    valid = transport in ('cargo-pipe', 'legacy-pipe', 'make-pipe', 'mflags-pipe', 'fifo', 'cargo-valid-shadows-make')
    fifo = None
    if transport == 'legacy-pipe':
        flags = {'CARGO_MAKEFLAGS': f'-j --jobserver-fds={pair[0]},{pair[1]}'}
    elif transport == 'make-pipe':
        flags = {'MAKEFLAGS': f'-j --jobserver-auth={pair[0]},{pair[1]}'}
    elif transport == 'mflags-pipe':
        flags = {'MFLAGS': f'-j --jobserver-auth={pair[0]},{pair[1]}'}
    elif transport == 'cargo-valid-shadows-make':
        flags['MAKEFLAGS'] = '-j --jobserver-auth=9000,9001'
    elif transport == 'cargo-invalid-shadows-make':
        flags = {'CARGO_MAKEFLAGS': '-j --jobserver-auth=invalid',
                 'MAKEFLAGS': f'-j --jobserver-auth={pair[0]},{pair[1]}'}
    elif transport == 'absent':
        flags = {}
    elif transport == 'malformed':
        flags = {'CARGO_MAKEFLAGS': '-j --jobserver-auth=not-a-pair'}
    elif transport == 'closed':
        flags = {'CARGO_MAKEFLAGS': '-j --jobserver-auth=9000,9001'}
    elif transport == 'half-closed':
        flags = {'CARGO_MAKEFLAGS': f'-j --jobserver-auth={pair[0]},9001'}
    elif transport == 'regular-file':
        file = destination / 'nonpipe'
        file.write_text('only a private regular file\n')
        opened = os.open(file, os.O_RDWR)
        try:
            a, b = high_copy(opened, 140), high_copy(opened, 141)
        finally:
            os.close(opened)
        owned.extend((a, b))
        passing.extend((a, b))
        fds.update(nonpipe_read=a, nonpipe_write=b)
        flags = {'CARGO_MAKEFLAGS': f'-j --jobserver-auth={a},{b}'}
    elif transport == 'fifo':
        fifo = destination / 'owned-jobserver.fifo'
        os.mkfifo(fifo, 0o600)
        token_read = token_write = os.open(fifo, os.O_RDWR | os.O_NONBLOCK)
        owned.append(token_read)
        flags = {'CARGO_MAKEFLAGS': f'-j --jobserver-auth=fifo:{fifo}'}
    elif transport == 'missing-fifo':
        flags = {'CARGO_MAKEFLAGS': '-j --jobserver-auth=fifo:' + str(destination / 'absent.fifo')}
    env = {'PATH': '/usr/bin:/bin:/usr/sbin:/sbin', 'HOME': str(root / 'home'),
           'LANG': 'C.UTF-8', 'PYTHONDONTWRITEBYTECODE': '1', **flags}
    if not controlled and executable != SDK / 'bin/trustc':
        # Ordinary newly built shims have no sidecar. Select the exact same
        # explicit no-proof bootstrap context as the canonical fixture owner.
        env.update(canonical_context())
    if controlled:
        driver = DRIVER
        env.update(RUSTC_REAL=str(driver), RUSTC_SNAPSHOT=str(driver), RUSTDOC_REAL=str(driver),
                   RUSTC_LIBDIR=str(SDK / 'lib'), RUSTC_SNAPSHOT_LIBDIR=str(SDK / 'lib'),
                   RUSTDOC_LIBDIR=str(SDK / 'lib'), RUSTC_SYSROOT=str(SDK),
                   RUSTC_STAGE='1', CFG_COMPILER_BUILD_TRIPLE=HOST,
                   FD_CONTROL_OBSERVER='1', FD_CONTROL_INPUTS=json.dumps({'fds': fds}))
    original = {name: identity(fd) for name, fd in fds.items()}
    os.write(token_write, b'j')
    command = [str(executable), *argv]
    begin = time.monotonic()
    try:
        with (destination / 'stdout').open('xb') as stdout, (destination / 'stderr').open('xb') as stderr:
            process = subprocess.Popen(command, cwd=destination, env=env, stdin=subprocess.DEVNULL,
                                       stdout=stdout, stderr=stderr, pass_fds=passing, start_new_session=True)
            try:
                exit_code = process.wait(timeout=15)
            except BaseException as error:
                # The leader can finish while its compiler child keeps this
                # private session alive. Do not reap/poll before killing it.
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass  # The entire private group already finished.
                except BaseException as cleanup_error:
                    error.add_note(f'owned process-group cleanup failed: {cleanup_error!r}')
                try:
                    process.wait(timeout=5)
                except BaseException as cleanup_error:
                    error.add_note(f'owned child reap failed: {cleanup_error!r}')
                raise
        after = {name: identity(fd) for name, fd in fds.items()}
        remaining = os.read(token_read, 1)
        report = {'name': label, 'transport': transport, 'valid_transport': valid,
                  'controlled_driver': controlled, 'command': command, 'pid': process.pid,
                  'exit_code': exit_code, 'terminal_observed': process.returncode is not None,
                  'seconds': time.monotonic() - begin, 'first_child_pass_fds': passing,
                  'metadata_input': flags, 'parent_fds_before': original, 'parent_fds_after': after,
                  'parent_fds_unchanged': original == after, 'token_remains_hex': remaining.hex(),
                  'stdout': file_identity(destination / 'stdout'), 'stderr': file_identity(destination / 'stderr')}
        if controlled and exit_code == 0:
            observation = json.loads((destination / 'stdout').read_text())
            report['observation'] = observation
            actual = observation['advertised']
            # Darwin may give the read and write ends distinct inode values.
            # Each advertised endpoint must match its own retained parent end.
            expected_pipe = {'read': identity(token_read), 'write': identity(token_write)}
            identities_match = all(actual.get(key, {}).get('kind') == expected_pipe[key]['kind']
                and actual[key].get('device') == expected_pipe[key]['device']
                and actual[key].get('inode') == expected_pipe[key]['inode'] for key in ('read', 'write'))
            report['advertised_pipe_matches_parent'] = identities_match
            report['token_roundtrip'] = observation['token'].get('read_hex') == '6a' and observation['token'].get('written') == 1
            report['unrelated_and_nonpipe_absent'] = all(not value['open'] for name, value in observation['original_fds'].items()
                                                        if name.startswith(('unrelated_', 'nonpipe_')))
            report['invalid_metadata_unchanged'] = valid or observation['metadata'] == flags
            report['secondary_metadata_unchanged'] = all(observation['metadata'].get(name) == value
                for name, value in flags.items() if name != 'CARGO_MAKEFLAGS')
            census = set(observation['pre_observer_open_fds_3_through_255'])
            expected_fds = ({str(fd) for fd in passing} if direct_control else
                            {str(actual[key]['fd']) for key in ('read', 'write')}
                            if valid and transport != 'fifo' else set())
            report['inherited_fd_set_expected'] = census == expected_fds
            report['direct_control_sees_unrelated'] = all(
                value['open'] for name, value in observation['original_fds'].items()
                if name.startswith('unrelated_'))
            exclusion = (report['direct_control_sees_unrelated'] if direct_control else
                         report['unrelated_and_nonpipe_absent'])
            report['expected_handoff_passed'] = (exclusion and report['inherited_fd_set_expected']
                and report['invalid_metadata_unchanged'] and report['secondary_metadata_unchanged']
                and report['parent_fds_unchanged'] and remaining == b'j'
                and ((identities_match and report['token_roundtrip']) if valid else not report['token_roundtrip']))
        with (destination / 'result.json').open('x') as stream:
            json.dump(report, stream, indent=2)
            stream.write('\n')
        return report
    finally:
        for fd in owned:
            os.close(fd)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sdk', type=Path, required=True, help='Trust SDK containing bin/trustc and bin/trustdoc')
    parser.add_argument('--host', required=True, help='SDK host target triple')
    parser.add_argument('--rustc', type=Path, required=True)
    parser.add_argument('--rustdoc', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--require-fixed', action='store_true')
    args = parser.parse_args()
    def interrupted(signum, _frame):
        raise KeyboardInterrupt('signal ' + str(signum))
    for signum in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(signum, interrupted)
    global SDK, HOST, DRIVER
    SDK, HOST = args.sdk.resolve(strict=True), args.host
    args.rustc, args.rustdoc = args.rustc.resolve(strict=True), args.rustdoc.resolve(strict=True)
    out = args.output.absolute()
    root = out
    out.mkdir(mode=0o700)
    (out / 'home').mkdir()
    DRIVER = out / 'fd-observer.py'
    source = Path(__file__).resolve().read_text()
    # sh/python polyglot: a shebang cannot carry an interpreter path with spaces.
    DRIVER.write_text('#!/bin/sh\n""":"\nexec "' + sys.executable + '" "$0" "$@"\n":"""\n'
                      + source.split('\n', 1)[1])
    DRIVER.chmod(0o755)
    (out / 'canonical-context.json').write_text(json.dumps(canonical_context(), indent=2) + '\n')
    copies = out / 'controlled-shims-no-sidecar'
    copies.mkdir(mode=0o700)
    before = [file_identity(path) for path in [args.rustc, args.rustdoc, SDK / 'bin/trustc', SDK / 'bin/trustdoc', DRIVER, Path(__file__).resolve()]]
    for name, source in [('rustc', args.rustc), ('rustdoc', args.rustdoc)]:
        destination = copies / name
        shutil.copyfile(source, destination)
        destination.chmod(0o755)
        assert sha(source) == sha(destination)
    assert not (copies / '.trust-cargo-test-shim.json').exists()
    cases = ('cargo-pipe', 'legacy-pipe', 'make-pipe', 'mflags-pipe', 'absent', 'malformed',
             'closed', 'half-closed', 'regular-file', 'fifo', 'missing-fifo',
             'cargo-valid-shadows-make', 'cargo-invalid-shadows-make')
    rows = [run_one(out, 'direct-observer-nonvacuity', DRIVER, ['--print', 'cfg'],
                    'cargo-pipe', controlled=True, root=root, direct_control=True)]
    for path, executable, argv in [('rustc-normal', copies/'rustc', ['--print', 'cfg']),
                                   ('rustc-version', copies/'rustc', ['-vV']),
                                   ('rustdoc-normal', copies/'rustdoc', ['--print', 'cfg'])]:
        for case in cases:
            rows.append(run_one(out, path + '-' + case, executable, argv, case, controlled=True, root=root))
    for path, executable, args_text in [('rustc-normal', copies/'rustc', '--print\ncfg\n'),
                                       ('rustc-version', copies/'rustc', '-vV\n'),
                                       ('rustdoc-normal', copies/'rustdoc', '--print\ncfg\n')]:
        argfile = out / (path + '.args')
        argfile.write_text(args_text)
        rows.append(run_one(out, path + '-argfile-cargo-pipe', executable, ['@' + str(argfile)],
                            'cargo-pipe', controlled=True, root=root))
    # Canonical source binaries and their actual sidecar remain untouched here.
    for name, executable in [('direct-sdk', SDK/'bin/trustc'), ('actual-shim', args.rustc)]:
        for case in ['cargo-pipe', 'absent', 'malformed', 'closed', 'regular-file', 'fifo']:
            rows.append(run_one(out, name + '-' + case, executable, ['--print', 'cfg'],
                                case, controlled=False, root=root))
    after = [file_identity(Path(row['path'])) for row in before]
    failures = [row['name'] for row in rows if row['controlled_driver'] and not row.get('expected_handoff_passed')]
    queries = [row for row in rows if not row['controlled_driver']]
    direct = {row['transport']: row for row in queries if row['name'].startswith('direct-sdk-')}
    actual = {row['transport']: row for row in queries if row['name'].startswith('actual-shim-')}
    query_checks = []
    for case in direct:
        d, a = direct[case], actual[case]
        same_stdout = d['stdout']['sha256'] == a['stdout']['sha256']
        stderr_expected = (d['stderr']['bytes'] == a['stderr']['bytes'] == 0 if case in ('cargo-pipe', 'absent', 'fifo')
                           else d['stderr']['bytes'] > 0 and a['stderr']['bytes'] > 0)
        passed = d['exit_code'] == a['exit_code'] == 0 and same_stdout and stderr_expected
        query_checks.append({'transport': case, 'both_exit0': d['exit_code'] == a['exit_code'] == 0,
                             'stdout_exact': same_stdout, 'unfiltered_stderr_behavior_expected': stderr_expected,
                             'passed': passed})
        if not passed:
            failures.append('actual-query-' + case)
    result = {'status': 'FIXED_HANDOFF_PASS' if not failures and before == after else 'OBSERVED_HANDOFF_RED',
              'identity_before': before, 'identity_after': after, 'inputs_unchanged': before == after,
              'rows': rows, 'controlled_failures': failures, 'row_count': len(rows),
              'real_compiler_query_checks': query_checks,
              'no_builds_or_gate_claim': True,
              'boundary': 'Owned fresh transports and tiny compiler queries only; controlled driver copies test actual FD custody separately from canonical fixture context; every stdout/stderr retained unfiltered.'}
    with (out / 'result.json').open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'status': result['status'], 'rows': len(rows), 'controlled_failures': failures,
                      'inputs_unchanged': before == after}, indent=2))
    return 1 if before != after or (args.require_fixed and failures) else 0

if __name__ == '__main__':
    raise SystemExit(observer() if os.environ.get('FD_CONTROL_OBSERVER') == '1' else main())
