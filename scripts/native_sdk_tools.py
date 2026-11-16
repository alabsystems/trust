#!/usr/bin/env python3
"""Bind a separately qualified LLVM-native component into a new SDK seal.

The unchanged mint records the compiler build/origin. This record binds only
the additional native tools and is content of the derived immutable artifact.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess

SCHEMA = 'trust.native-sdk-tools.v1'
TOOLS = frozenset(('rust-lld', 'dsymutil'))
MAX_RECORD = 16 << 20
MAX_TOOL = 1 << 30


class Refusal(ValueError):
    pass


def require(value: bool, message: str) -> None:
    if not value:
        raise Refusal(message)


def identity(st: os.stat_result) -> tuple[int, ...]:
    return (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)


def read_regular(path: Path, maximum: int | None = None) -> bytes:
    require(path.is_absolute(), f'path is not absolute: {path}')
    fd = os.open(path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
    try:
        before = os.fstat(fd)
        require(stat.S_ISREG(before.st_mode), f'not a regular file: {path}')
        require(maximum is None or before.st_size <= maximum, f'file exceeds limit: {path}')
        chunks = []
        total = 0
        while data := os.read(fd, 1 << 20):
            chunks.append(data)
            total += len(data)
            require(maximum is None or total <= maximum, f'file grew past limit: {path}')
        require(identity(before) == identity(os.fstat(fd)), f'file changed during read: {path}')
        require(identity(before) == identity(path.lstat()), f'named file changed during read: {path}')
        return b''.join(chunks)
    finally:
        os.close(fd)


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON field: {key}')
        result[key] = value
    return result


def document(path: Path, expected: str | None = None):
    raw = read_regular(path, MAX_RECORD)
    if expected is not None:
        require(bool(re.fullmatch('[0-9a-f]{64}', expected)), 'expected SHA-256 must be exact lowercase hex')
        require(digest(raw) == expected, f'evidence digest differs: {path}')
    parsed = json.loads(raw, object_pairs_hook=unique)
    require(isinstance(parsed, dict), f'record is not an object: {path}')
    return parsed, raw


def evidence(reference):
    require(isinstance(reference, dict), 'evidence reference is not an object')
    return document(Path(reference['path']), reference['sha256'])


def validate(source_root: Path, stage: Path, commit: str, record_path: Path, expected: str, *,
             receipt_path: Path | None = None, receipt_sha256: str | None = None):
    record, raw = document(record_path, expected)
    require(record.get('schema') == SCHEMA, 'wrong native-tools schema')
    require(record.get('source') == commit and bool(re.fullmatch('[0-9a-f]{40}', commit)), 'component compiler source differs')
    llvm_tree = subprocess.check_output(
        ['git', '-c', 'core.hooksPath=/dev/null', '-C', str(source_root),
         'rev-parse', f'{commit}:src/llvm-project'], text=True).strip()
    require(record.get('llvm_tree') == llvm_tree, 'component LLVM source tree differs')
    selected = receipt_path is not None or receipt_sha256 is not None
    if selected:
        require(receipt_path is not None and receipt_sha256 is not None,
                'external stage provenance needs both receipt and sha256')
        # Execute the exact current engine reader source, never a cached pyc.
        # It binds the selected receipt to this ORIGINAL producer stage and
        # checks every recorded installed file, including native LLD.
        reader = Path(__file__).resolve().parent / 'lib/stage_receipt_provenance.py'
        namespace = {'__name__':'native_component_stage_reader', '__file__':str(reader)}
        exec(compile(reader.read_bytes(), str(reader), 'exec'), namespace)
        try:
            namespace['lines'](stage, commit, receipt_path=receipt_path,
                               receipt_sha256=receipt_sha256, source_root=source_root)
        except namespace['StageReceiptError'] as error:
            raise Refusal(f'external stage provenance refused: {error}') from error
    stage_record, stage_raw = document(receipt_path if selected else stage / 'tool-provenance.json',
                                       receipt_sha256 if selected else None)
    require(stage_record.get('status') == 'internal-release-ready', 'base stage is not internally ready')
    require(record.get('stage_provenance_sha256') == digest(stage_raw), 'component base-stage provenance differs')
    require(record.get('retained_inputs_unchanged') is True, 'component does not retain its original inputs')
    built, built_raw = evidence(record['built_receipt'])
    smoke, smoke_raw = evidence(record['native_smoke'])
    for what, value in [('build', built), ('native smoke', smoke)]:
        require(value.get('passed') is True, f'{what} did not pass')
        require(value.get('source') == commit and value.get('llvm_tree') == llvm_tree,
                f'{what} source identity differs')
        phases = value.get('phases')
        require(isinstance(phases, list) and phases, f'{what} has no actual phases')
        require(all(isinstance(p, dict) and type(p.get('exit')) is int and p['exit'] == 0 for p in phases),
                f'{what} contains a nonzero or non-actual phase')
    require(built.get('retained_inputs_unchanged') is True, 'build inputs changed')
    require(smoke.get('actual_native_resource_worker') is True, 'smoke did not use an actual native resource worker')
    files = record.get('files')
    require(isinstance(files, dict) and set(files) == TOOLS, 'component must contain exactly rust-lld and dsymutil')
    require(files == built.get('files'), 'qualified tool map differs from the actual build')
    require(smoke.get('tool_sha256') == {name: row['sha256'] for name, row in files.items()},
            'native smoke did not exercise these tool bytes')
    payload = {}
    for name in sorted(TOOLS):
        row = files[name]
        path = Path(row['path'])
        require(path.name == name, f'wrong native tool name: {path}')
        content = read_regular(path, MAX_TOOL)
        require(type(row.get('bytes')) is int and len(content) == row['bytes'], f'{name} size differs')
        require(digest(content) == row.get('sha256'), f'{name} digest differs')
        require(bool(path.stat().st_mode & 0o111), f'{name} is not executable')
        payload[name] = content
    return record, raw, built_raw, smoke_raw, payload


def install(source_root: Path, stage: Path, commit: str, record_path: Path, expected: str, destination: Path, *,
            receipt_path: Path | None = None, receipt_sha256: str | None = None):
    record, raw, built, smoke, payload = validate(source_root, stage, commit, record_path, expected,
                                                receipt_path=receipt_path, receipt_sha256=receipt_sha256)
    require(destination.is_dir() and not destination.is_symlink(), 'new seal is not a real directory')
    require((destination / 'bin').is_dir() and not (destination / 'bin').is_symlink(), 'new seal bin is not a real directory')
    retained = {}
    # Inspect BOTH destinations before installing either tool. A canonical
    # stage can already carry LLD while still needing dsymutil. Preserve that
    # exact qualified image, never overwrite or chmod an existing file.
    for name in sorted(TOOLS):
        target = destination / 'bin' / name
        if os.path.lexists(target):
            content = read_regular(target, MAX_TOOL)
            require(digest(content) == record['files'][name]['sha256'],
                    f'will not overwrite a mismatched existing native tool: {name}')
            require(os.access(target, os.X_OK), f'existing native tool is not executable: {name}')
            retained[name] = identity(target.lstat())
    require(not os.path.lexists(destination / 'NATIVE-TOOLS.json'), 'will not overwrite component provenance')
    details = destination / 'NATIVE-TOOLS.evidence'
    require(not os.path.lexists(details), 'will not overwrite component evidence')
    for name, original in retained.items():
        target = destination / 'bin' / name
        require(identity(target.lstat()) == original
                and digest(read_regular(target, MAX_TOOL)) == record['files'][name]['sha256'],
                f'existing native tool changed before install: {name}')
    details.mkdir()
    for name, content in payload.items():
        target = destination / 'bin' / name
        if name in retained:
            require(identity(target.lstat()) == retained[name]
                    and digest(read_regular(target, MAX_TOOL)) == record['files'][name]['sha256'],
                    f'existing native tool changed during install: {name}')
            continue
        with target.open('xb') as f:
            f.write(content)
        target.chmod(0o755)
        require(digest(read_regular(target)) == record['files'][name]['sha256'], f'copied {name} differs')
    for target, content in [(destination / 'NATIVE-TOOLS.json', raw),
                            (details / 'component-built.json', built), (details / 'native-smoke.json', smoke)]:
        with target.open('xb') as f:
            f.write(content)
        target.chmod(0o644)
    index = {'scope':'Supplementary component, not a claim that the original mint built these tools',
             'retained_existing_tools':sorted(retained),
             'installed_tools':sorted(TOOLS - retained.keys()),
             'record_sha256':digest(raw), 'evidence':{
                 'built_receipt':{'path':'component-built.json','sha256':digest(built)},
                 'native_smoke':{'path':'native-smoke.json','sha256':digest(smoke)}}}
    with (details / 'INDEX.json').open('x') as f:
        f.write(json.dumps(index, indent=2) + '\n')


def main(argv=None):
    class Once(argparse.Action):
        def __call__(self, parser, namespace, values, option_string=None):
            if getattr(namespace, self.dest) is not None:
                parser.error(f'duplicate {option_string}')
            setattr(namespace, self.dest, values)

    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('command', choices=('validate','install'))
    p.add_argument('--source-root', type=Path, required=True)
    p.add_argument('--stage', type=Path, required=True)
    p.add_argument('--commit', required=True)
    p.add_argument('--record', type=Path, required=True)
    p.add_argument('--sha256', required=True)
    p.add_argument('--destination', type=Path)
    p.add_argument('--stage-provenance-receipt', type=Path, action=Once)
    p.add_argument('--stage-provenance-sha256', action=Once)
    a = p.parse_args(argv)
    try:
        require(a.source_root.is_absolute() and a.stage.is_absolute(), 'source and stage must be absolute')
        if a.command == 'install':
            require(a.destination is not None and a.destination.is_absolute(), 'install needs an absolute destination')
            install(a.source_root, a.stage, a.commit, a.record, a.sha256, a.destination,
                    receipt_path=a.stage_provenance_receipt, receipt_sha256=a.stage_provenance_sha256)
        else:
            require(a.destination is None, 'validate does not install anything')
            validate(a.source_root, a.stage, a.commit, a.record, a.sha256,
                     receipt_path=a.stage_provenance_receipt, receipt_sha256=a.stage_provenance_sha256)
        print(json.dumps({'command':a.command,'source':a.commit,'native_tools':sorted(TOOLS),'passed':True}))
        return 0
    except (Refusal, OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as e:
        print(f'native SDK tools refused: {e}', file=__import__('sys').stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
