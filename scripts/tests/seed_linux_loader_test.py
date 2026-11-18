#!/usr/bin/env python3
"""Inert ELF inventory/loader grammar controls; no native tool or code execution."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import struct
import tempfile
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location(
    "seed_linux_loader_subject", Path(__file__).resolve().parents[1] / "lib/seed_linux.py")
assert SPEC and SPEC.loader
support = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(support)
HOST = "aarch64-unknown-linux-gnu"


class LoaderInventoryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.binary = Path(temporary.name) / "inert.so"

    def elf(self, entries=((0, 0),), *, dynamic=True, machine=183, interpreter=b"", strings=b""):
        ident = b"\x7fELF\x02\x01\x01" + bytes(9)
        count = 1 + int(dynamic) + bool(interpreter)
        head = struct.pack("<16sHHIQQQIHHHHHH", ident, 3, machine, 1, 0, 64, 0, 0,
                           64, 56, count, 0, 0, 0)
        body = b"".join(struct.pack("<qQ", *entry) for entry in entries) if dynamic else b""
        offset = 64 + 56 * count
        interpreter_offset = offset + len(body)
        size = interpreter_offset + len(interpreter) + len(strings)
        load = struct.pack("<IIQQQQQQ", 1, 6, 0, 0x400000, 0, size, size, 4096)
        phdr = struct.pack("<IIQQQQQQ", 2, 6, offset, 0x400000 + offset, 0,
                           len(body), len(body), 8)
        interp = struct.pack("<IIQQQQQQ", 3, 4, interpreter_offset, 0, 0,
                             len(interpreter), len(interpreter), 1) if interpreter else b""
        self.binary.write_bytes(head + load + (phdr if dynamic else b"") + interp + body + interpreter + strings)
        return self.binary

    def search_path(self, tag, name, *, offset=1):
        # Four dynamic entries directly precede the fixture's string table.
        string_address = 0x400000 + 64 + 2 * 56 + 4 * 16
        table = b"\0" + name
        return self.elf(((5, string_address), (10, len(table)), (tag, offset), (0, 0)), strings=table)

    def dependencies(self, table, *offsets):
        string_address = 0x400000 + 64 + 2 * 56 + (3 + len(offsets)) * 16
        entries = [(5, string_address), (10, len(table)), *((1, offset) for offset in offsets), (0, 0)]
        return self.elf(entries, strings=table)

    def mutate(self, offset, fmt, value):
        raw = bytearray(self.binary.read_bytes())
        struct.pack_into(fmt, raw, offset, value)
        self.binary.write_bytes(raw)

    def test_exact_single_static_marker_needs_independent_empty_inventory(self):
        binary = self.elf()
        needed = support.needed_entries(binary)
        self.assertEqual(needed, [])
        for output in ["statically linked", "statically linked\n", "\tstatically linked\n"]:
            self.assertEqual(support.loader_rows(output, binary, needed=needed), [])

    def test_missing_or_nonempty_inventory_cannot_admit_static_marker(self):
        for inventory in [None, [1], [0], (), {}]:
            with self.subTest(inventory=inventory):
                with self.assertRaisesRegex(support.Refusal, "empty DT_NEEDED"):
                    support.loader_rows("statically linked\n", self.binary, needed=inventory)

    def test_static_marker_cannot_mix_rows_blank_lines_duplicates_or_unknown_text(self):
        mapping = "/lib/libc.so.6 (0x123)\n"
        for output in ["\nstatically linked\n", "statically linked\n\n",
                       "statically linked\nstatically linked\n", mapping + "statically linked\n",
                       "statically linked\n" + mapping, "statically linked (unknown)\n",
                       "statically linked\r\n", "unknown\n"]:
            with self.subTest(output=output):
                with self.assertRaises(support.Refusal):
                    support.loader_rows(output, self.binary, needed=[])

    def test_existing_mapping_and_anonymous_initial_row_grammar_remains(self):
        output = "(0x123)\nlinux-vdso.so.1 (0x456)\nlibc.so.6 => /lib/libc.so.6 (0x789)\n"
        self.assertEqual(support.loader_rows(output, self.binary, needed=[1]),
                         [(self.binary.name, self.binary), ("libc.so.6", Path("/lib/libc.so.6"))])
        with self.assertRaises(support.Refusal):
            support.loader_rows("(0x123)\n(0x456)\n", self.binary, needed=[])

    def test_program_headers_distinguish_no_dynamic_table_from_zero_needed_table(self):
        self.assertEqual(support.needed_entries(self.elf(dynamic=False)), [])
        self.assertEqual(support.needed_entries(self.elf()), [])

    def test_needed_offsets_are_not_inferred_from_loader_or_readelf_text(self):
        binary = self.dependencies(b"\0librustc.so\0libc.so.6\0", 1, 13)
        with mock.patch.object(support, "command", side_effect=AssertionError("no metadata subprocess")):
            info = support.metadata(binary, HOST)
        self.assertTrue(info["dynamic"])
        self.assertIsNone(info["interpreter"])
        self.assertEqual(info["needed"], [1, 13])
        with self.assertRaisesRegex(support.Refusal, "empty DT_NEEDED"):
            support.loader_rows("statically linked\n", binary, needed=info["needed"])

    def test_dependency_paths_must_not_depend_on_the_current_directory(self):
        for name in (b"libc.so.6", b"lib$LIBRARY.so", b"/lib/libc.so.6", b"$ORIGIN/libx.so",
                     b"${ORIGIN}/$LIB/libx.so"):
            with self.subTest(name=name):
                self.assertEqual(support.metadata(self.dependencies(b"\0" + name + b"\0", 1), HOST)["needed"], [1])
        for name in (b"lib/libc.so.6", b"./libc.so.6", b"../libc.so.6", b"$LIB/libc.so.6",
                     b"$LIB", b"lib${LIB}.so", b"x$ORIGIN.so", b"$PLATFORM"):
            with self.subTest(name=name), self.assertRaisesRegex(support.Refusal, "cwd-dependent DT_NEEDED"):
                support.metadata(self.dependencies(b"\0" + name + b"\0", 1), HOST)

    def test_dependency_offsets_require_bounded_nonempty_names(self):
        cases = ((b"\0libc.so.6\0", 100, "outside"), (b"\0libc.so.6", 1, "unterminated"),
                 (b"\0libc.so.6\0", 0, "empty"))
        for table, offset, detail in cases:
            with self.subTest(offset=offset, detail=detail), self.assertRaisesRegex(support.Refusal, detail):
                support.metadata(self.dependencies(table, offset), HOST)
        with self.assertRaisesRegex(support.Refusal, "bounded dynamic string table"):
            support.metadata(self.elf(((1, 4), (0, 0))), HOST)

    def test_interpreter_comes_from_the_program_header_without_sections(self):
        interpreter = b"/lib/ld-linux-aarch64.so.1\0"
        binary = self.elf(interpreter=interpreter)
        with mock.patch.object(support, "command", side_effect=AssertionError("no metadata subprocess")):
            info = support.metadata(binary, HOST)
        self.assertEqual(info["interpreter"], interpreter[:-1].decode())
        self.assertTrue(info["dynamic"])
        self.elf(interpreter=interpreter[:-1])
        with self.assertRaisesRegex(support.Refusal, "terminated absolute path"):
            support.metadata(self.binary, HOST)
        self.elf(interpreter=interpreter)
        self.mutate(64 + 2 * 56 + 8, "<Q", 1 << 63)
        with self.assertRaisesRegex(support.Refusal, "out-of-bounds PT_INTERP"):
            support.metadata(self.binary, HOST)

    def test_dynamic_search_paths_are_checked_in_the_file_backed_string_table(self):
        for tag in (15, 29):
            support.metadata(self.search_path(tag, b"$ORIGIN/lib:/usr/lib\0"), HOST)
            for name in (b"relative\0", b"$ORIGIN/lib:\0", b"\0"):
                with self.subTest(tag=tag, name=name), self.assertRaisesRegex(support.Refusal, "cwd-dependent"):
                    support.metadata(self.search_path(tag, name), HOST)
            with self.assertRaisesRegex(support.Refusal, "outside the dynamic string table"):
                support.metadata(self.search_path(tag, b"/lib\0", offset=100), HOST)
            with self.assertRaisesRegex(support.Refusal, "unterminated ELF search path"):
                support.metadata(self.search_path(tag, b"/lib"), HOST)

    def test_dynamic_audit_tags_are_refused_from_program_bytes(self):
        for tag in (0x6ffffefb, 0x6ffffefc):
            with self.subTest(tag=tag), mock.patch.object(support, "command", side_effect=AssertionError("no loader")):
                with self.assertRaisesRegex(support.Refusal, "embedded ELF audit modules"):
                    support.metadata(self.elf(((tag, 1), (0, 0))), HOST)

    def test_dynamic_filters_are_refused_from_program_bytes(self):
        for tag in (0x7ffffffd, 0x7fffffff):
            with self.subTest(tag=tag), self.assertRaisesRegex(support.Refusal, "embedded ELF filters"):
                support.metadata(self.elf(((tag, 1), (0, 0))), HOST)

    def test_null_terminator_ends_the_loader_visible_dynamic_table(self):
        self.assertEqual(support.needed_entries(self.elf(((0, 0), (1, 7)))), [])

    def test_truncated_or_unsupported_headers_are_refused_before_tool_execution(self):
        for raw in [b"\x7fELF", self.elf().read_bytes()[:63]]:
            self.binary.write_bytes(raw)
            with mock.patch.object(support, "command", side_effect=AssertionError("no tool")):
                with self.assertRaises(support.Refusal):
                    support.metadata(self.binary, HOST)
        self.elf()
        self.mutate(5, "<B", 2)
        with self.assertRaises(support.Refusal):
            support.needed_entries(self.binary)

    def test_program_header_bounds_sizes_and_extended_counts_refuse(self):
        for offset, fmt, value in [(32, "<Q", 1 << 63), (54, "<H", 1), (56, "<H", 0xffff)]:
            self.elf()
            self.mutate(offset, fmt, value)
            with self.assertRaises(support.Refusal):
                support.needed_entries(self.binary)

    def test_dynamic_table_bounds_alignment_size_and_memory_extent_refuse(self):
        for offset, value in [(128, 1 << 63), (152, 15), (152, (1 << 20) + 16), (160, 1)]:
            self.elf()
            self.mutate(offset, "<Q", value)
            with self.assertRaises(support.Refusal):
                support.needed_entries(self.binary)

    def test_unterminated_table_cannot_be_reported_as_no_needed(self):
        self.elf(((5, 7),))
        with self.assertRaisesRegex(support.Refusal, "DT_NULL"):
            support.needed_entries(self.binary)

    def test_multiple_dynamic_segments_are_ambiguous_and_refused(self):
        raw = bytearray(self.elf().read_bytes()[:64])
        struct.pack_into("<H", raw, 56, 3)
        load = struct.pack("<IIQQQQQQ", 1, 6, 0, 0x400000, 0, 248, 248, 4096)
        dynamic = struct.pack("<IIQQQQQQ", 2, 6, 232, 0x400000 + 232, 0, 16, 16, 8)
        self.binary.write_bytes(raw + load + dynamic + dynamic + struct.pack("<qQ", 0, 0))
        with self.assertRaisesRegex(support.Refusal, "multiple PT_DYNAMIC"):
            support.needed_entries(self.binary)

    def test_dynamic_table_requires_its_unique_file_backed_virtual_mapping(self):
        # A different in-file p_offset cannot attest the bytes at p_vaddr.
        for offset, value in [(128, 160), (136, 0x800000), (96, 120)]:
            self.elf()
            self.mutate(offset, "<Q", value)
            with self.assertRaisesRegex(support.Refusal, "PT_LOAD mapping"):
                support.needed_entries(self.binary)
        # Two overlapping load mappings are ambiguous even if their bytes agree.
        raw = bytearray(self.elf().read_bytes()[:64])
        struct.pack_into("<H", raw, 56, 3)
        load = struct.pack("<IIQQQQQQ", 1, 6, 0, 0x400000, 0, 248, 248, 4096)
        dynamic = struct.pack("<IIQQQQQQ", 2, 6, 232, 0x400000 + 232, 0, 16, 16, 8)
        self.binary.write_bytes(raw + load + load + dynamic + struct.pack("<qQ", 0, 0))
        with self.assertRaisesRegex(support.Refusal, "unambiguous PT_LOAD"):
            support.needed_entries(self.binary)

    def test_foreign_platform_is_still_refused_before_metadata_tool_execution(self):
        self.elf(machine=62)
        with mock.patch.object(support, "command", side_effect=AssertionError("no tool")):
            with self.assertRaisesRegex(support.Refusal, "ELF platform differs"):
                support.metadata(self.binary, HOST)


if __name__ == "__main__":
    unittest.main()
