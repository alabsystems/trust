#!/usr/bin/env python3
"""Finite observations of exact runtime C. Not a proof/ABI/NoUB certificate."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


def sha(path):
    return hashlib.file_digest(path.open('rb'), 'sha256').hexdigest()


def run(clean, out):
    out.mkdir(parents=True, exist_ok=False)
    fixture = Path(__file__).with_name('header_runtime_controls.c')
    cc = Path('/usr/bin/cc').resolve(strict=True)
    original = [clean / 'crates/clean-runtime/src/clean_runtime.c',
                clean / 'crates/clean-runtime/include/clean_runtime.h']
    def book():
        return {str(p): sha(p) for p in original + [fixture, cc, Path(__file__)]}
    before = book()
    (out / 'BEFORE.json').write_text(json.dumps(before, indent=2) + '\n')
    rows = []
    for name, expected in [('original', 0), ('changed-drop', 10), ('changed-increment', 20)]:
        dest = out / name
        dest.mkdir()
        shutil.copyfile(fixture, dest / fixture.name)
        for source in original:
            relative = source.relative_to(clean / 'crates/clean-runtime')
            target = dest / 'runtime' / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
        if name == 'changed-drop':
            p = dest / 'runtime/src/clean_runtime.c'
            data = p.read_text()
            needle = 'static inline bool clean_rc_drop(clean_obj* o) {\n    if (atomic_load_explicit(&o->header.ref_count, memory_order_relaxed) >= CLEAN_RC_STICKY_DROP)'
            assert data.count(needle) == 1
            p.write_text(data.replace(needle, needle.replace('>=', '>')))
        if name == 'changed-increment':
            p = dest / 'runtime/include/clean_runtime.h'
            data = p.read_text()
            needle = '#define CLEAN_RC_STICKY      0xF0000000u'
            assert data.count(needle) == 1
            p.write_text(data.replace(needle, '#define CLEAN_RC_STICKY      0xE0000000u'))
        command = [str(cc), '-std=c11', '-O0', '-Wall', '-Wextra', '-Werror',
                   str(dest / fixture.name), '-o', str(dest / 'controls')]
        with (dest / 'compile.log').open('xb') as log:
            compiled = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        observed = None
        if compiled.returncode == 0:
            with (dest / 'run.log').open('xb') as log:
                observed = subprocess.run([str(dest / 'controls')], stdout=log, stderr=subprocess.STDOUT).returncode
        rows.append({'name': name, 'command': command, 'compile_exit': compiled.returncode,
                     'observed_exit': observed, 'expected_exit': expected})
    after = book()
    (out / 'AFTER.json').write_text(json.dumps(after, indent=2) + '\n')
    good = before == after and all(r['compile_exit'] == 0 and r['observed_exit'] == r['expected_exit'] for r in rows)
    (out / 'RESULT.json').write_text(json.dumps({'rows': rows, 'books_equal': before == after,
        'expected_controls': {'header_updates': 27, 'two_owned_aliases': 5},
        'scope': 'finite actual C observations only; no C11/source/ARC/NoUB/ABI/ownership/kernel/runtime permission', 'ok': good}, indent=2) + '\n')
    return good


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--clean', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    raise SystemExit(not run(args.clean.resolve(strict=True), args.out.absolute()))
