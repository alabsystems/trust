#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Archive and byte-comparison controls; fixtures are not compiler output."""

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "check_std_objects_identical.py"
SPEC = importlib.util.spec_from_file_location("std_objects", SCRIPT)
TOOL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOL)


def object_bytes(tag=0):
    # Minimal object-shaped DATA, never executed or credited as valid code.
    return struct.pack("<8I", 0xFEEDFACF, 0x0100000C, 0, 1, 0, 0, 0, 0) + bytes([tag]) * 16


def member(name, data, timestamp=0):
    fields = (name.encode().ljust(16), str(timestamp).encode().ljust(12), b"0     ",
              b"0     ", b"100644  ", str(len(data)).encode().ljust(10), b"`\n")
    header = b"".join(fields)
    assert len(header) == 60
    return header + data + (b"\n" if len(data) % 2 else b"")


def archive(objects=None, metadata=b"metadata", timestamp=0):
    if objects is None:
        objects = [("a.o", object_bytes()), ("b.o", object_bytes(1))]
    return b"!<arch>\n" + member("/", b"symbol index", timestamp) + member(
        "lib.rmeta/", metadata, timestamp) + b"".join(
        member(name + "/", data, timestamp) for name, data in objects)


class StdObjectsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="std-object-data-")
        self.addCleanup(self.temp.cleanup)
        self.left, self.right = [Path(self.temp.name) / name for name in ("without", "with")]
        for root in (self.left, self.right):
            root.mkdir()
            for crate in TOOL.CRATES:
                (root / f"lib{crate}-abc.rlib").write_bytes(archive())

    def compare(self):
        return TOOL.compare(self.left, self.right)

    def test_metadata_headers_and_symbol_indexes_may_differ_but_all_object_bytes_must_match(self):
        raw = archive(metadata=b"changed metadata", timestamp=37).replace(
            b"symbol index", b"other index!")
        (self.right / "libcore-abc.rlib").write_bytes(raw)
        report = self.compare()
        self.assertTrue(report["object_bytes_identical"])
        self.assertTrue(report["inputs_revalidated"])
        self.assertEqual([row["crate"] for row in report["crates"]], list(TOOL.CRATES))
        core = report["crates"][0]
        self.assertEqual(core["without_producer"]["object_count"], 2)
        self.assertEqual(core["with_producer"]["object_bytes"], 96)
        self.assertNotEqual(core["without_producer"]["archive_sha256"],
                            core["with_producer"]["archive_sha256"])
        self.assertEqual(core["without_producer"]["objects"], core["with_producer"]["objects"])

    def test_same_size_native_byte_change_is_reported(self):
        path = self.right / "liballoc-abc.rlib"
        path.write_bytes(archive(objects=[("a.o", object_bytes(2)), ("b.o", object_bytes(1))]))
        report = self.compare()
        self.assertFalse(report["object_bytes_identical"])
        self.assertEqual(report["crates"][1]["changed_objects"], ["a.o"])

    def test_missing_extra_and_renamed_objects_are_not_a_favorable_subset(self):
        for objects, missing, extra in [
            ([("a.o", object_bytes())], ["b.o"], []),
            ([("a.o", object_bytes()), ("b.o", object_bytes(1)), ("c.o", object_bytes())], [], ["c.o"]),
            ([("a.o", object_bytes()), ("renamed.o", object_bytes(1))], ["b.o"], ["renamed.o"]),
        ]:
            with self.subTest(objects=[name for name, _ in objects]):
                (self.right / "libstd-abc.rlib").write_bytes(archive(objects=objects))
                row = self.compare()["crates"][2]
                self.assertEqual(row["missing_objects"], missing)
                self.assertEqual(row["extra_objects"], extra)

    def test_duplicate_objects_refuse_even_when_their_bytes_are_equal(self):
        with self.assertRaisesRegex(ValueError, "duplicate archive member"):
            TOOL.archive_objects(archive(objects=[("a.o", object_bytes()), ("a.o", object_bytes())]))

    def test_gnu_and_bsd_extended_names_compare_the_same_named_payloads(self):
        name = "long_object_member_name.rcgu.o"
        gnu = (b"!<arch>\n" + member("//", name.encode() + b"/\n")
               + member("lib.rmeta/", b"gnu metadata") + member("/0", object_bytes()))
        # BSD includes padded filename bytes in the member payload and size.
        encoded = name.encode() + b"\0\0\0"
        bsd = (b"!<arch>\n" + member("lib.rmeta/", b"bsd metadata")
               + member(f"#1/{len(encoded)}", encoded + object_bytes()))
        self.assertEqual({n: bytes(b) for n, b in TOOL.archive_objects(gnu).items()},
                         {n: bytes(b) for n, b in TOOL.archive_objects(bsd).items()})
        for root, raw in ((self.left, gnu), (self.right, bsd)):
            for path in root.iterdir():
                path.write_bytes(raw)
        self.assertTrue(self.compare()["object_bytes_identical"])

    def test_thin_truncated_invalid_and_unknown_archive_inputs_refuse(self):
        good = archive()
        bad = [b"!<thin>\n", good[:19], good[:-1], good + b"garbage",
               b"!<arch>\n" + member("unknown/", b"data"),
               archive(objects=[]), archive(objects=[("a.o", b"BC\xc0\xde" + b"0" * 44)]),
               b"!<arch>\n" + member("/0", object_bytes()),
               b"!<arch>\n" + member("lib.rmeta/", b"x") + member("#1/99", b"too short")]
        malformed = bytearray(good)
        malformed[8 + 48:8 + 58] = b"-1        "
        bad.append(bytes(malformed))
        for raw in bad:
            with self.subTest(raw=raw[:80]), self.assertRaises(ValueError):
                TOOL.archive_objects(raw)

    def test_gnu_name_must_start_at_an_entry_boundary(self):
        raw = (b"!<arch>\n" + member("//", b"prefix_name.o/\n")
               + member("lib.rmeta/", b"data") + member("/7", object_bytes()))
        with self.assertRaisesRegex(ValueError, "entry boundary"):
            TOOL.archive_objects(raw)

    def test_missing_ambiguous_and_symlinked_crate_archives_refuse(self):
        path = self.right / "libcore-abc.rlib"
        original = path.read_bytes()
        path.unlink()
        with self.assertRaisesRegex(ValueError, "exactly one core"):
            self.compare()
        path.write_bytes(original)
        second = self.right / "libcore-def.rlib"
        second.write_bytes(original)
        with self.assertRaisesRegex(ValueError, "exactly one core"):
            self.compare()
        second.unlink()
        noncanonical = self.right / "libcore-not-a-crate-hash.rlib"
        noncanonical.write_bytes(original)
        with self.assertRaisesRegex(ValueError, "noncanonical core"):
            self.compare()
        noncanonical.unlink()
        path.unlink()
        path.symlink_to(self.left / "libcore-abc.rlib")
        with self.assertRaisesRegex(ValueError, "not a plain file"):
            self.compare()

    def test_shared_physical_archive_or_same_library_root_refuses(self):
        with self.assertRaisesRegex(ValueError, "distinct"):
            TOOL.compare(self.left, self.left)
        path = self.right / "libcore-abc.rlib"
        path.unlink()
        os.link(self.left / "libcore-abc.rlib", path)
        with self.assertRaisesRegex(ValueError, "six distinct physical files"):
            self.compare()

    def test_input_change_after_comparison_refuses(self):
        original = TOOL.capture
        calls = 0

        def capture(path):
            nonlocal calls
            calls += 1
            if calls == 7:
                changed = self.left / "libcore-abc.rlib"
                changed.write_bytes(archive(metadata=b"changed after capture"))
            return original(path)

        with patch.object(TOOL, "capture", capture), self.assertRaisesRegex(ValueError, "changed during"):
            self.compare()

    def test_cli_distinguishes_identical_different_and_refused_with_json(self):
        argv = ["--without-producer", str(self.left), "--with-producer", str(self.right)]
        for expected in (0, 1, 2):
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertEqual(TOOL.main(argv), expected)
            self.assertEqual(json.loads(output.getvalue())["status"],
                             ("identical", "different", "refused")[expected])
            if expected == 0:
                (self.right / "libcore-abc.rlib").write_bytes(
                    archive(objects=[("a.o", object_bytes(2))]))
            elif expected == 1:
                (self.right / "libcore-abc.rlib").write_bytes(b"!<thin>\n")


if __name__ == "__main__":
    unittest.main()
