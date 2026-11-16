#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Andrew Yates
"""Capture native Targo transport in an unqualified, exact SDK sandbox.

The caller owns real b121 -> serial-executor custody through this process and
its waits. This harness neither makes scheduler pipes nor mints resource rights.
No command is dispatched on import. It never installs a component or writes Ready.
"""
from __future__ import annotations

import argparse
import base64
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import types

VALIDATOR_SHA256 = '23957eb0eae05d2ba3c4e7183ab4cb6c3f7f27c3139ca0eb5a1e20b828c82038'

class InterruptedCustody(RuntimeError):
    def __init__(self, code):
        self.code = code
        super().__init__('interrupted/signalled witness; caller must retain unresolved custody')


def require_normal_retirement(code, pending):
    if pending or not 0 <= code < 128:
        raise InterruptedCustody(128 + pending[0] if pending else (128 - code if code < 0 else code))


def owner():
    path = Path(__file__).resolve().with_name('sdk_targo_component.py')
    import hashlib
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != VALIDATOR_SHA256:
        raise ValueError('native validator source changed')
    module = types.ModuleType('native_targo_witness_validation')
    module.__file__ = str(path)
    sys.modules[module.__name__] = module
    exec(compile(raw, str(path), 'exec'), module.__dict__)
    return module


def inherited_pipe(api):
    flags = os.environ.get('CARGO_MAKEFLAGS', '')
    pairs = re.findall(r'(?:^|\s)--jobserver-(?:auth|fds)=([0-9]+),([0-9]+)(?=\s|$)', flags)
    # configure_pipe publishes auth and legacy fds aliases for the SAME owner.
    api.require(bool(pairs) and len(set(pairs)) == 1, 'one consistent real inherited pipe advertisement required')
    descriptors = tuple(map(int, pairs[0]))
    api.require(descriptors[0] != descriptors[1], 'scheduler descriptor roles alias')
    result = []
    for fd in descriptors:
        value = os.fstat(fd)
        api.require(stat.S_ISFIFO(value.st_mode), 'scheduler descriptor is not a live pipe')
        result.extend((value.st_dev, value.st_ino))
    return descriptors, result


def observe_child(api, command, env, descriptors, *, cwd=None):
    """Forward cooperatively to this exact owned group and wait; never KILL an owner."""
    pending = []
    child = None
    def forward(number, _frame):
        pending.append(number)
        if child is not None:
            try:
                os.killpg(child.pid, number)
            except ProcessLookupError:
                pass
    previous = {number: signal.signal(number, forward) for number in (signal.SIGINT, signal.SIGTERM)}
    try:
        child = subprocess.Popen(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 pass_fds=descriptors, start_new_session=True, cwd=cwd)
        for number in pending:
            try:
                os.killpg(child.pid, number)
            except ProcessLookupError:
                pass
        stdout, stderr = child.communicate()
        return child.returncode, stdout, stderr, pending
    except BaseException as error:
        if child is None:
            raise
        # An unexpected post-spawn failure is also unknown ownership. Cooperate
        # with the exact owned group and wait; do not turn it into ordinary exit1.
        try:
            os.killpg(child.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            child.communicate()
        except BaseException:
            child.wait()
        raise InterruptedCustody(128 + signal.SIGTERM) from error
    finally:
        # A Python failure after spawn must still wait for the actual command.
        # A signalled result never produces a completed transport record.
        if child is not None and child.poll() is None:
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            child.wait()
        for number, handler in previous.items():
            signal.signal(number, handler)


def transport_commands(api, subject, source, project):
    """Plan the exact owning/witness routes without dispatching a command."""
    full_cases = ['transport_witness_tests::' + name for name in api.CONTROLS[:2]]
    test = [str(subject / 'bin/targo'), '--unverified', 'test', '--config', 'build.test-jobs=1', '--manifest-path',
            str(source / 'Cargo.toml'), '--locked', '--offline', '-p', 'jobserver_utils', '--lib']
    commands = [{'name': name, 'argv': [test + [case, '--', '--exact', '--nocapture']]}
                for name, case in zip(api.CONTROLS, full_cases)]
    invoke = [str(subject / 'bin/targo'), '--unverified', 'run', '--locked', '--offline',
              '--manifest-path', str(project / 'Cargo.toml'), '--bin', 'native-targo-custody-witness', '--']
    commands += [{'name': api.CONTROLS[2], 'argv': [invoke + ['positive', str(subject / 'bin/trustc')]]},
                 {'name': api.CONTROLS[3], 'argv': [invoke + [mode, str(subject / 'bin/trustc')]
                                                  for mode in ('missing', 'malformed')]}]
    return commands


def run(args):
    api = owner()
    source = api.physical_directory(args.source)
    subject = api.physical_directory(args.subject)
    project = api.physical_directory(args.project)
    target = api.physical_directory(args.target)
    evidence = api.physical_directory(args.evidence)
    base = api.document(args.record, args.sha256)[0]
    api.record_shape(base)
    api.require(base['source']['root'] == str(source), 'witness source differs')
    api.require(api._git(source, 'rev-parse', 'HEAD').decode().strip() == base['source']['commit']
                and api._git(source, 'rev-parse', 'HEAD^{tree}').decode().strip() == base['source']['tree']
                and not api._git(source, 'status', '--porcelain=v1').strip(), 'witness source not committed clean')
    for path, hashed in base['source']['files'].items():
        api.require(api.sha256(api._git_file(source, base['source']['commit'], path)) == hashed,
                    'witness selected source changed')
    selected = base['artifact']
    api.require(all(api.sha256(api.regular(subject / 'bin' / name, api.MAX_BINARY)) == selected['sha256']
                    for name in api.ALIASES), 'prospective pair differs')
    api._base_files(base, subject)
    before = api.inventory(subject)
    original = api.document(args.base_inventory, base['base']['inventory']['sha256'])[0]
    api.pair_inventory(original, before, selected)
    api.require(not any(os.path.lexists(subject / name) for name in (api.RECORD, api.DETAILS, api.QUALIFIED)),
                'transport sandbox must remain explicitly unqualified')
    fixture = Path(__file__).resolve().parent / 'tests/fixtures/native_targo_custody.rs'
    source_raw = api.regular(fixture)
    api.require(api.sha256(source_raw) == api.TRANSPORT_SOURCE_SHA256
                and api.regular(project / 'src/main.rs') == source_raw
                and api.regular(project / 'Cargo.toml') == api.transport_manifest(source), 'mini source/manifest changed')
    api.regular(project / 'Cargo.lock')  # canonical input preparation must already have resolved it
    descriptors, identity = inherited_pipe(api)
    env = {key: value for key, value in os.environ.items()
           if key not in ('RUSTC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'RUSTFLAGS',
                          'CARGO_BUILD_RUSTC', 'CARGO_ENCODED_RUSTFLAGS', 'CARGO_BUILD_TARGET')}
    env.update(PATH=str(subject / 'bin') + os.pathsep + env.get('PATH', ''),
               TRUST_STAGE2_BIN=str(subject / 'bin'), CARGO_TARGET_DIR=str(target), CARGO_BUILD_JOBS='1')
    commands = transport_commands(api, subject, source, project)
    context = {'schema': 'trust.native-targo-transport-context.v1',
               'source_commit': base['source']['commit'], 'artifact_sha256': selected['sha256'],
               'compiler_sha256': base['base']['compiler_sha256'],
               'base_stage_binding_sha256': base['base']['stage_binding_sha256'],
               'selected_subject': str(subject),
               'aliases': {name: {'observed_path': str(subject / 'bin' / name), 'sha256': selected['sha256']}
                           for name in api.ALIASES},
               'compiler': {'observed_path': str(subject / 'bin/trustc'), 'source_commit': api.COMPILER_SOURCE,
                            'sha256': api.COMPILER_SHA256},
               'frontend': {'observed_path': str(subject / 'bin/targo-trust'),
                            'sha256': base['base']['frontend_artifact_sha256']},
               'subject_inventory_sha256': api.sha256(api.canonical(before)),
               'witness': {'project_root': str(project), 'source_sha256': api.sha256(source_raw),
                           'manifest_sha256': api.sha256(api.transport_manifest(source))},
               'commands': commands}
    context_raw = api._json_bytes(context)
    api._atomic(evidence / 'transport.context.json', context_raw)
    rows = []
    # Preserve actual raw output/status BEFORE interpreting a failed case. These
    # exclusive files also prevent a failed prospective namespace being retried in place.
    with (evidence / 'transport.stdout').open('xb') as stdout, (evidence / 'transport.stderr').open('xb') as stderr:
        for number, item in enumerate(commands):
            outputs = []
            for index, command in enumerate(item['argv']):
                code, out, err, pending = observe_child(api, command, env, descriptors)
                for stream, raw in ((stdout, out), (stderr, err)):
                    frame = {'name': item['name'], 'index': index, 'argv': command, 'exit': code,
                             'raw_base64': base64.b64encode(raw).decode('ascii')}
                    stream.write(api.canonical(frame) + b'\n'); stream.flush(); os.fsync(stream.fileno())
                if pending or not 0 <= code < 128:
                    api._atomic(evidence / 'transport.incomplete.json', api._json_bytes({
                        'completed': False, 'actual_child_exit': code, 'signals': pending,
                        'owned_command_drained': False, 'source_commit': base['source']['commit'],
                        'context_sha256': api.sha256(context_raw)}))
                    require_normal_retirement(code, pending)
                outputs.append((code, out, err))
            observed = api.transport_observation(number, outputs, context, identity if number == 2 else None)
            rows.append({'name': item['name'], 'exit': 0, 'argv': item['argv'], 'observed': observed})
    api.require(api.inventory(subject) == before and inherited_pipe(api)[1] == identity,
                'sandbox or original scheduler changed')
    streams = [api.sha256(api.regular(evidence / ('transport.' + name))) for name in ('stdout', 'stderr')]
    result = {'schema': 'trust.native-targo-transport.v1', 'source_commit': base['source']['commit'],
              'artifact_sha256': selected['sha256'], 'compiler_sha256': api.COMPILER_SHA256,
              'context_sha256': api.sha256(context_raw), 'stdout_sha256': streams[0], 'stderr_sha256': streams[1],
              'controls': rows, 'completed': True,
              'retirement': {'completed': True, 'actual_exit': 0, 'owned_command_drained': True}}
    api._atomic(evidence / 'transport.result.json', api._json_bytes(result))
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', type=Path, required=True)
    p.add_argument('--subject', type=Path, required=True)
    p.add_argument('--project', type=Path, required=True)
    p.add_argument('--target', type=Path, required=True)
    p.add_argument('--record', type=Path, required=True)
    p.add_argument('--sha256', required=True)
    p.add_argument('--base-inventory', type=Path, required=True)
    p.add_argument('--evidence', type=Path, required=True)
    args = p.parse_args()
    try:
        print(json.dumps(run(args), sort_keys=True))
    except InterruptedCustody as error:
        print(str(error), file=sys.stderr)
        # Keep the canonical outer wait's unknown/signalled classification. The
        # outer owner must use its retained-custody/independent retirement ACK path.
        return error.code
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print('native transport witness incomplete: ' + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
