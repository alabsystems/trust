#!/usr/bin/env python3
"""Custody controls for the untrusted inventory advice producer, not C semantics."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('inventory_advice', HERE / 'generate_c11_predefined_advice.py')
ADVICE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ADVICE)


class AdviceCustodyTests(unittest.TestCase):
    def test_every_record_and_opaque_tail_is_retained(self):
        source = '#define a unsupported + body\n#define f(x) x ## suffix\n'
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / 'out'
            ADVICE.generate(source, out)
            info = json.loads((out / 'INPUT.json').read_text())
            self.assertEqual(info['names'], ['a', 'f'])
            self.assertEqual(info['bytes'], len(source.encode()))
            self.assertEqual(info['sha256'], hashlib.sha256(source.encode()).hexdigest())
            data = (out / 'C11PredefinedData.lean').read_text()
            self.assertIn('unsupported + body', data)
            self.assertIn('(x) x ## suffix', data)

    def test_cli_does_not_normalize_unsupported_crlf(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'input'
            source.write_bytes(b'#define a 1\r\n')
            out = root / 'out'
            result = subprocess.run([sys.executable, str(HERE / 'generate_c11_predefined_advice.py'),
                                     '--input', str(source), '--out', str(out)],
                                    capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(out.exists())
            self.assertEqual(source.read_bytes(), b'#define a 1\r\n')

    def test_nul_is_not_dropped(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / 'out'
            with self.assertRaises(AssertionError):
                ADVICE.generate('#define a 1\x00\n', out)
            self.assertFalse(out.exists())

    def test_duplicate_or_reordered_names_refuse(self):
        for source in ['#define a 1\n#define a 2\n', '#define z 1\n#define a 2\n']:
            with self.subTest(source=source), tempfile.TemporaryDirectory() as directory:
                out = Path(directory) / 'out'
                with self.assertRaises(AssertionError):
                    ADVICE.generate(source, out)
                self.assertFalse(out.exists())


if __name__ == '__main__':
    unittest.main()
