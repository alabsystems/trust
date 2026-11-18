#!/usr/bin/env python3
"""Focused DATA-custody controls; no C typing or runtime verification claim."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main(capture, out):
    out.mkdir()
    producer = Path(__file__).with_name('generate_c11_declaration_advice.py')
    spec = importlib.util.spec_from_file_location('declaration_advice', producer)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    book = json.loads((capture / 'DEPENDENCIES_BEFORE.json').read_text())
    needed = [data['sha256'] for name, data in book.items() if
              name.endswith(('/_uint8_t.h', '/_uint16_t.h', '/_uint32_t.h', '/stdbool.h', '/stdatomic.h'))]
    paths = [capture / name for name in ['typed-ast.out', 'RESULT.json', 'DEPENDENCIES_BEFORE.json',
                                        'runtime/include/clean_runtime.h']]
    paths += [capture / 'source-dependencies' / name for name in needed]
    before = {str(path): sha(path) for path in paths}
    rows = []
    module.produce(capture, out / 'original')
    data = (out / 'original/C11ActualDeclarationData.lean').read_bytes()
    declarations = json.loads((out / 'original/DECLARATIONS.json').read_text())
    for name in ['bool', 'true', 'false']:
        assert sum(row['name'] == name for row in declarations) == 2
    for row in declarations:
        owner = out / 'original/owners' / row['owner_sha256']
        assert sha(owner) == row['owner_sha256']
        assert owner.read_bytes()[row['begin']:row['end']].decode('utf-8') == row['raw']
    rows.append({'case': 'actual_complete_spans_and_all_macro_alternatives', 'exit': 0})

    def fixture(name):
        destination = out / name
        for path in paths:
            relative = path.relative_to(capture)
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
        (destination / 'FIXTURE_SCOPE.json').write_text(json.dumps({
            'scope': 'owned deliberate untrusted producer-readset fixture; not a complete compiler capture/SDK',
            'files': [str(path.relative_to(capture)) for path in paths]}, indent=2))
        return destination

    poisoned = fixture('poisoned-type-advice-input')
    ast = json.loads((poisoned / 'typed-ast.out').read_text())
    changed = 0

    def poison(node):
        nonlocal changed
        if node.get('kind') == 'TypedefDecl' and node.get('name') in ['uint8_t', 'uint16_t', 'uint32_t']:
            node['type'] = {'qualType': 'float'}
            changed += 1
        for child in node.get('inner', []):
            poison(child)
    poison(ast)
    assert changed == 3
    (poisoned / 'typed-ast.out').write_text(json.dumps(ast))
    result = json.loads((poisoned / 'RESULT.json').read_text())
    result['complete_ast'] = sha(poisoned / 'typed-ast.out')
    (poisoned / 'RESULT.json').write_text(json.dumps(result))
    module.produce(poisoned, out / 'poisoned-type-advice-output')
    assert (out / 'poisoned-type-advice-output/C11ActualDeclarationData.lean').read_bytes() == data
    rows.append({'case': 'forged_clang_type_annotations_cannot_change_source_data', 'exit': 0})

    changed_source = fixture('changed-source-input')
    header = changed_source / 'runtime/include/clean_runtime.h'
    raw = header.read_bytes()
    assert raw.count(b'_Atomic uint32_t ref_count;') == 1
    header.write_bytes(raw.replace(b'_Atomic uint32_t ref_count;', b'        uint32_t ref_count;'))
    try:
        module.produce(changed_source, out / 'changed-source-output')
    except AssertionError:
        rows.append({'case': 'changed_actual_source_with_stale_capture_refused', 'exit': 0})
    else:
        raise AssertionError('changed source was accepted')

    after = {str(path): sha(path) for path in paths}
    assert after == before
    (out / 'RESULT.json').write_text(json.dumps({'rows': rows, 'exit': 0,
        'original_inputs_unchanged': True, 'producer_sha256': sha(producer),
        'test_sha256': sha(Path(__file__)), 'scope': 'untrusted DATA proposal/custody only'}, indent=2) + '\n')
    print(f'{len(rows)} controls PASS; original inputs unchanged')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    main(args.capture, args.out)
