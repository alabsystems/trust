#!/usr/bin/env python3
"""Controls for checked-in in-process ELF fixtures; no compiler needed."""
from pathlib import Path
import importlib.util
import hashlib
import struct
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests/fixtures/binary_decomp"
HELPER = FIXTURES / "regenerate_inprocess_elf.py"
spec = importlib.util.spec_from_file_location("inprocess_elf_fixture_generator", HELPER)
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)


class InProcessFixtureTests(unittest.TestCase):
    def data(self, case):
        return bytes.fromhex((FIXTURES / (case[0] + "-elf.hex")).read_text())

    def test_each_checked_in_object_has_exact_code_and_function_symbol(self):
        self.assertEqual(len(generator.CASES), 5)
        for case in generator.CASES:
            with self.subTest(case=case[0]):
                generator.validate(self.data(case), case)

    def test_wrong_machine_and_executable_type_are_rejected(self):
        for case in generator.CASES:
            for field, value in [(16, 2), (18, 0)]:
                with self.subTest(case=case[0], field=field):
                    data = bytearray(self.data(case))
                    struct.pack_into("<H", data, field, value)
                    with self.assertRaises(ValueError):
                        generator.validate(data, case)

    def test_changed_code_and_changed_symbol_are_rejected(self):
        for case in generator.CASES:
            with self.subTest(case=case[0]):
                raw = self.data(case)
                code = bytes.fromhex(case[4])
                self.assertEqual(raw.count(code), 1)
                data = bytearray(raw)
                data[raw.index(code)] ^= 1
                with self.assertRaises(ValueError):
                    generator.validate(data, case)
                symbol = case[3].encode() + b"\0"
                self.assertEqual(raw.count(symbol), 1)
                data = bytearray(raw)
                data[raw.index(symbol)] = ord("X")
                with self.assertRaises(ValueError):
                    generator.validate(data, case)

    def test_truncated_object_and_section_table_are_rejected(self):
        case = generator.CASES[0]
        raw = self.data(case)
        for data in [raw[:16], raw[:-1]]:
            with self.subTest(size=len(data)), self.assertRaises(ValueError):
                generator.validate(data, case)

    def test_missing_assembler_fails_without_modifying_fixtures(self):
        paths = sorted(FIXTURES.glob("*-inprocess-*-elf.hex"))
        before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        for mode in [[], ["--check"]]:
            with self.subTest(mode=mode):
                result = subprocess.run([sys.executable, "-B", str(HELPER), *mode,
                                         "--cc", "/nonexistent/inprocess-fixture-compiler"],
                                        capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("regeneration failed", result.stderr)
                self.assertEqual(before, {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})


if __name__ == "__main__":
    unittest.main()
