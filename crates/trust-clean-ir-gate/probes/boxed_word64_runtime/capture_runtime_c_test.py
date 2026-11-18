#!/usr/bin/env python3
"""Actual frontend capture controls, not C semantic/proof tests."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import unittest

from capture_runtime_c import capture


class CaptureTests(unittest.TestCase):
    def source(self, case):
        root = ARTIFACTS / case / 'clean'
        for part, filename in [('src', 'clean_runtime.c'), ('include', 'clean_runtime.h')]:
            dest = root / 'crates/clean-runtime' / part / filename
            dest.parent.mkdir(parents=True)
            shutil.copyfile(CLEAN / 'crates/clean-runtime' / part / filename, dest)
        return root

    def test_complete_dependencies_are_retained(self):
        root = self.source('original')
        out = ARTIFACTS / 'original/capture'
        result = capture(root, out, CLANG)
        self.assertTrue(result['dependencies_equal'] and result['tool_equal'] and result['producer_equal'])
        rows = json.loads((out / 'DEPENDENCIES_BEFORE.json').read_text())
        self.assertGreater(len(rows), 2)
        for row in rows.values():
            raw = (out / 'source-dependencies' / row['sha256']).read_bytes()
            self.assertEqual(len(raw), row['bytes'])
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row['sha256'])
        self.assertEqual(json.loads((out / 'typed-ast.out').read_bytes())['kind'], 'TranslationUnitDecl')

    def test_source_fixed_guard_mutation_is_observed(self):
        root = self.source('changed-drop')
        source = root / 'crates/clean-runtime/src/clean_runtime.c'
        old = source.read_text()
        needle = 'static inline bool clean_rc_drop(clean_obj* o) {\n    if (atomic_load_explicit(&o->header.ref_count, memory_order_relaxed) >= CLEAN_RC_STICKY_DROP)'
        self.assertEqual(old.count(needle), 1)
        source.write_text(old.replace(needle, needle.replace('>= CLEAN_RC_STICKY_DROP)', '> CLEAN_RC_STICKY_DROP)')))
        out = ARTIFACTS / 'changed-drop/capture'
        result = capture(root, out, CLANG)
        original = hashlib.sha256((CLEAN / 'crates/clean-runtime/src/clean_runtime.c').read_bytes()).hexdigest()
        self.assertNotEqual(result['source'], original)
        ast = json.loads((out / 'typed-ast.out').read_bytes())
        functions = [n for n in ast['inner'] if n.get('kind') == 'FunctionDecl' and n.get('name') == 'clean_rc_drop']
        self.assertEqual(len(functions), 1)
        def opcodes(node):
            return [node.get('opcode')] + [op for child in node.get('inner', []) for op in opcodes(child)]
        self.assertIn('>', opcodes(functions[0]))
        self.assertNotIn('>=', opcodes(functions[0]))

    def test_malformed_source_refuses_and_retains_failure(self):
        root = self.source('malformed')
        source = root / 'crates/clean-runtime/src/clean_runtime.c'
        source.write_bytes(source.read_bytes() + b'\nint invalid( {\n')
        out = ARTIFACTS / 'malformed/capture'
        with self.assertRaisesRegex(RuntimeError, 'typed-ast refused'):
            capture(root, out, CLANG)
        self.assertFalse((out / 'RESULT.json').exists())
        self.assertNotEqual(json.loads((out / 'COMMANDS.json').read_text())[-1]['exit'], 0)
        self.assertTrue((out / 'typed-ast.err').read_bytes())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--clean', type=Path, required=True)
    parser.add_argument('--artifacts', type=Path, required=True)
    args = parser.parse_args()
    CLEAN = args.clean.resolve(strict=True)
    ARTIFACTS = args.artifacts.absolute()
    ARTIFACTS.mkdir(parents=True, exist_ok=False)
    CLANG = Path('/usr/bin/clang').resolve(strict=True)
    unittest.main(argv=['capture_runtime_c_test'], verbosity=2)
