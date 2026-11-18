#!/usr/bin/env python3
"""Capture actual C frontend DATA; never a C semantics or admission certificate.

The complete AST and preprocessed TU are retained. No selected-name/body census
or successful C run establishes source/ARC/NoUB correspondence. A future Lean
checker must check the actual source/typed-TU relation and atomic semantics.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import shutil
import subprocess


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def capture(clean, out, clang):
    out.mkdir(parents=True, exist_ok=False)
    root = out / 'runtime'
    for part, name in [('src', 'clean_runtime.c'), ('include', 'clean_runtime.h')]:
        dest = root / part / name
        dest.parent.mkdir(parents=True)
        shutil.copyfile(clean / 'crates/clean-runtime' / part / name, dest)
    source = root / 'src/clean_runtime.c'
    base = [str(clang), '-std=c11']
    commands = []

    def run(name, args):
        command = base + args
        with (out / (name + '.out')).open('xb') as stdout, (out / (name + '.err')).open('xb') as stderr:
            result = subprocess.run(command, stdout=stdout, stderr=stderr, cwd=out)
        commands.append({'name': name, 'command': command, 'exit': result.returncode})
        (out / 'COMMANDS.json').write_text(json.dumps(commands, indent=2) + '\n')
        if result.returncode:
            raise RuntimeError(f'{name} refused: {result.returncode}; retained DATA at {out}')
        return out / (name + '.out')

    tool_before = digest(clang)
    producer_before = digest(Path(__file__))
    run('version', ['--version'])
    run('target', ['-dumpmachine'])
    run('resource-dir', ['-print-resource-dir'])
    dependency_file = run('dependencies', ['-M', '-MT', 'capture', str(source)])
    dep_text = dependency_file.read_text().replace('\\\n', '')
    if not dep_text.startswith('capture:'):
        raise RuntimeError('unexpected dependency transport')
    dependencies = sorted({Path(p).resolve(strict=True) for p in shlex.split(dep_text[len('capture:'):])})
    if source.resolve() not in dependencies or (root / 'include/clean_runtime.h').resolve() not in dependencies:
        raise RuntimeError('runtime source/header missing from actual dependency capture')
    before = {str(p): {'bytes': p.stat().st_size, 'sha256': digest(p)} for p in dependencies}
    retained = out / 'source-dependencies'
    retained.mkdir()
    for dependency in dependencies:
        raw = dependency.read_bytes()
        identity = hashlib.sha256(raw).hexdigest()
        if identity != before[str(dependency)]['sha256']:
            raise RuntimeError('dependency changed before retention')
        dest = retained / identity
        if dest.exists() and dest.read_bytes() != raw:
            raise RuntimeError('source dependency digest collision')
        dest.write_bytes(raw)
    (out / 'DEPENDENCIES_BEFORE.json').write_text(json.dumps(before, indent=2) + '\n')
    run('preprocessed', ['-E', '-dD', str(source)])
    run('typed-ast', ['-Xclang', '-ast-dump=json', '-fsyntax-only', str(source)])
    # This validates transport syntax only; it does not validate AST meaning.
    json.loads((out / 'typed-ast.out').read_bytes())
    after = {str(p): {'bytes': p.stat().st_size, 'sha256': digest(p)} for p in dependencies}
    (out / 'DEPENDENCIES_AFTER.json').write_text(json.dumps(after, indent=2) + '\n')
    result = {'dependencies_equal': before == after, 'tool_equal': tool_before == digest(clang),
              'producer_sha256': producer_before, 'producer_equal': producer_before == digest(Path(__file__)),
              'clang': str(clang), 'clang_sha256': tool_before,
              'source': digest(source), 'header': digest(root / 'include/clean_runtime.h'),
              'complete_preprocessed': digest(out / 'preprocessed.out'),
              'complete_ast': digest(out / 'typed-ast.out'),
              'scope': 'untrusted complete source/frontend DATA only; no semantic, ARC, atomic, ABI, NoUB, ownership, runtime, kernel or admission authority'}
    (out / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    if not result['dependencies_equal'] or not result['tool_equal'] or not result['producer_equal']:
        raise RuntimeError('C source/frontend inputs changed during capture')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--clean', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--clang', type=Path, default=Path('/usr/bin/clang'))
    args = parser.parse_args()
    print(json.dumps(capture(args.clean.resolve(strict=True), args.out.absolute(), args.clang.resolve(strict=True)), indent=2))
