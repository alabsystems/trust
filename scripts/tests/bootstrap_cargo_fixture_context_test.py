#!/usr/bin/env python3
"""Exercise dedicated Cargo-test shim announcement custody at real child boundaries.

Use freshly built bootstrap shims and a Trust SDK. Compiler cases really compile;
observer cases only inspect the final child environment and make no proof claim.
Every process identity and typed terminal result precedes its drain assertion.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import time


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def cleanup_owned_child(child, row, persist):
    """Retain the exact child's terminal result even if group cleanup races."""
    errors = []
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except BaseException as error:
        errors.append('own group cleanup: ' + repr(error))
    try:
        code = child.wait(timeout=5)
        row.update(exit_code=code, direct_child_reaped=True)
    except BaseException as error:
        # Do not manufacture an exit or discard a previously recorded one.
        errors.append('own child reap: ' + repr(error))
    if errors:
        row['cleanup_errors'] = errors
    persist(row)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sdk', type=Path, required=True)
    parser.add_argument('--rustc', type=Path, required=True)
    parser.add_argument('--rustdoc', type=Path, required=True)
    parser.add_argument('--host', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.absolute()
    out.mkdir(mode=0o700)
    sdk = args.sdk.resolve(strict=True)
    shims = {name: getattr(args, name).resolve(strict=True) for name in ('rustc', 'rustdoc')}
    inputs = {str(path): sha(path) for path in [*shims.values(), sdk/'bin/trustc', sdk/'bin/trustdoc']}
    base = dict(PATH='/usr/bin:/bin:/usr/sbin:/sbin', HOME=str(out), LANG='C', LC_ALL='C')
    context = dict(RUSTC_REAL=str(sdk/'bin/trustc'), RUSTC_SNAPSHOT=str(sdk/'bin/trustc'),
                   RUSTC_LIBDIR=str(sdk/'lib'), RUSTC_SNAPSHOT_LIBDIR=str(sdk/'lib'),
                   RUSTDOC_REAL=str(sdk/'bin/trustdoc'), RUSTDOC_LIBDIR=str(sdk/'lib'),
                   RUSTC_SYSROOT=str(sdk), RUSTC_STAGE='1', CFG_COMPILER_BUILD_TRIPLE=args.host,
                   RUSTC_LINK_STD_INTO_RUSTC_DRIVER='0', TRUST_BOOTSTRAP_SHIM_NO_VERIFY='1',
                   TRUST_CARGO_TEST_SHIM_VERSION='3', TRUST_VANILLA_ANNOUNCED='1')
    observer = out/'observe.py'
    observer.write_text('#!'+sys.executable+'\nimport json,os,sys\nprint(json.dumps({"argv":sys.argv[1:],"announced":os.environ.get("TRUST_VANILLA_ANNOUNCED"),"authored":os.environ.get("TRUST_FIXTURE_AUTHORED")}))\n')
    observer.chmod(0o700)
    observer_stage = out/'stage1'
    observer_stage.mkdir(mode=0o700)
    for name in ('trustc', 'trustdoc'):
        shutil.copy2(observer, observer_stage/name)
    results = []

    def record(path, value):
        temporary = path.with_suffix(path.suffix+'.tmp')
        with temporary.open('w') as stream:
            json.dump(value, stream, indent=2)
            stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
        temporary.replace(path)

    def run(directory, name, argv, environment):
        row = dict(name=name, argv=list(map(str, argv)))
        with (directory/(name+'.stdout')).open('xb') as stdout, (directory/(name+'.stderr')).open('xb') as stderr:
            child = subprocess.Popen(row['argv'], cwd=directory, env=environment,
                                     stdout=stdout, stderr=stderr, start_new_session=True)
            row['pid'] = child.pid
            record(directory/(name+'.started.json'), row)
            try:
                code = child.wait(timeout=30)
            except BaseException:
                row['interrupted'] = True
                cleanup_owned_child(child, row, lambda value: record(directory/(name+'.terminal.json'), value))
                raise
            row.update(exit_code=code, direct_child_reaped=True)
            record(directory/(name+'.terminal.json'), row)
            try:
                os.killpg(child.pid, 0)
            except ProcessLookupError:
                row['own_process_group_absent'] = True
            else:
                row['drain_refused'] = True
                record(directory/(name+'.drain-refusal.json'), row)
                cleanup_owned_child(child, row, lambda value: record(directory/(name+'.cleanup.json'), value))
                raise AssertionError('child process group remained: '+name)
        row.update(stdout_sha256=sha(directory/(name+'.stdout')), stderr_sha256=sha(directory/(name+'.stderr')))
        record(directory/(name+'.result.json'), row)
        return code, (directory/(name+'.stdout')).read_text(), (directory/(name+'.stderr')).read_text()

    cases = ['ordinary-unannounced', 'ordinary-announced', 'fixture-announced',
             'fixture-authored-controls', 'missing-announcement', 'false-announcement',
             'old-schema', 'unknown-authority', 'rustc-observer', 'rustdoc-observer',
             'verified-rustc-observer', 'verified-rustdoc-observer']
    for case in cases:
        directory = out/case
        directory.mkdir(mode=0o700)
        for name, source in shims.items():
            shutil.copy2(source, directory/name)
        selected = dict(base)
        configuration = dict(context)
        real = 'observer' not in case
        dedicated = not case.startswith('ordinary-')
        source = directory/'fixture.rs'
        source.write_text('pub fn answer() -> u32 { 42 }\n')
        if not dedicated:
            selected.update(context)
            selected.pop('TRUST_VANILLA_ANNOUNCED')
            if case == 'ordinary-announced':
                selected['TRUST_VANILLA_ANNOUNCED'] = '1'
        if case == 'fixture-authored-controls':
            selected.update(RUSTC_STAGE='authored-stage', RUSTC_REAL='authored-not-a-driver',
                            TRUST_BOOTSTRAP_SHIM_NO_VERIFY='0', TRUST_FIXTURE_AUTHORED='authored-value',
                            TRUST_VANILLA_ANNOUNCED='0')
            source.write_text('fn main() { println!("{}|{}|{}", env!("RUSTC_STAGE"), env!("TRUST_BOOTSTRAP_SHIM_NO_VERIFY"), env!("TRUST_FIXTURE_AUTHORED")); }\n')
        if case == 'missing-announcement':
            configuration.pop('TRUST_VANILLA_ANNOUNCED')
            selected['TRUST_VANILLA_ANNOUNCED'] = '1'
        if case == 'false-announcement':
            configuration['TRUST_VANILLA_ANNOUNCED'] = '0'
        if case == 'old-schema':
            configuration['TRUST_CARGO_TEST_SHIM_VERSION'] = '2'
        if case == 'unknown-authority':
            configuration['TRUST_OTHER_POLICY'] = '1'
        if not real:
            configuration.update(RUSTC_REAL=str(observer_stage/'trustc'), RUSTC_SNAPSHOT=str(observer_stage/'trustc'), RUSTDOC_REAL=str(observer_stage/'trustdoc'))
            selected.update(TRUST_FIXTURE_AUTHORED='authored-value', TRUST_VANILLA_ANNOUNCED='authored-not-authority')
            if case.startswith('verified-'):
                selected['TRUST_TARGO_FRONTEND'] = '1'
        if dedicated:
            (directory/'.trust-cargo-test-shim.json').write_text(json.dumps(configuration)+'\n')
        kind = 'rustdoc' if 'rustdoc' in case else 'rustc'
        argv = [directory/kind, '--crate-name', 'fixture', str(source), '--out-dir', str(directory)]
        if case != 'fixture-authored-controls':
            argv += ['--crate-type', 'lib']
        code, stdout, stderr = run(directory, 'shim', argv, selected)
        if case in ('missing-announcement', 'false-announcement', 'old-schema', 'unknown-authority'):
            passed = code != 0 and 'Cargo-test shim config' in stderr
        elif not real:
            observed = json.loads(stdout)
            expected = None if case.startswith('verified-') else '1'
            passed = code == 0 and observed['announced'] == expected and observed['authored'] == 'authored-value'
        else:
            announced = 'compiled WITHOUT Trust verification' not in stderr
            passed = code == 0 and announced == (case != 'ordinary-unannounced')
            if case == 'fixture-authored-controls' and passed:
                status, output, error = run(directory, 'compiled-program', [directory/'fixture'], base)
                passed = status == 0 and output == 'authored-stage|0|authored-value\n' and error == ''
        results.append(dict(name=case, passed=passed, exit_code=code, real_compiler=real))
    unchanged = inputs == {name: sha(Path(name)) for name in inputs}
    record(out/'result.json', dict(cases=results, inputs=inputs, inputs_unchanged=unchanged,
                                   passed=sum(row['passed'] for row in results), total=len(results),
                                   ordinary_no_proof_only=True))
    assert unchanged and all(row['passed'] for row in results), results
    print(f'{len(results)} Cargo fixture custody controls passed')


if __name__ == '__main__':
    main()
