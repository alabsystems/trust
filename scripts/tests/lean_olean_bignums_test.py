#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The .olean bignum walk on hand-built compacted regions (no Lean toolchain)."""

import contextlib
import importlib.util
import io
from pathlib import Path
import struct
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "lean_olean_bignums", Path(__file__).parents[1] / "lean_olean_bignums.py")
tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)


def pad8(raw):
    return raw + b"\0" * (-len(raw) % 8)


def header():
    return b"olean" + bytes([1]) + b"df668f00e6c0".ljust(42, b"\0") + struct.pack("<Q", 0x10000)


def obj(tag, cs_sz, other, body):
    return pad8(struct.pack("<iHBB", 0, cs_sz, other, tag) + body)


def ctor(fields):
    return obj(0, 8 + 8 * len(fields), len(fields), b"".join(struct.pack("<Q", f) for f in fields))


def string(text):
    raw = text.encode() + b"\0"
    body = struct.pack("<QQQ", len(raw), len(raw), len(text)) + raw
    return obj(tool.TAG_STRING, 1, 0, body)


def scalar_array(elem_size, payload):
    count = len(payload) // elem_size
    return obj(tool.TAG_SCALAR_ARRAY, 1, elem_size, struct.pack("<QQ", count, count) + payload)


def mpz(value, padding=b"\x8b\x23\x4d\x01\0\0\0"):
    sign = 1 if value < 0 else 0
    magnitude = abs(value)
    digits = []
    while magnitude:
        digits.append(magnitude & 0xFFFFFFFF)
        magnitude >>= 32
    body = (bytes([sign]) + padding + struct.pack("<QQ", len(digits), 0)
            + b"".join(struct.pack("<I", d) for d in digits))
    return obj(tool.TAG_MPZ, 32 + 4 * len(digits), 0, body)


def olean(*objects):
    return header() + struct.pack("<Q", 0) + b"".join(objects)


class BignumWalkTests(unittest.TestCase):
    def test_reports_each_bignum_with_its_offset_and_value(self):
        data = olean(ctor([1, 2]), string("TrustIr.Semantics.Cast"), mpz(2 ** 64),
                     scalar_array(1, b"\x01\x02\x03"), mpz(-(2 ** 127)))
        found = tool.bignums(data)
        self.assertEqual([value for _, value in found], [2 ** 64, -(2 ** 127)])
        first = found[0][0]
        self.assertEqual(data[first + 7], tool.TAG_MPZ)

    def test_a_region_without_a_bignum_reports_none(self):
        self.assertEqual(tool.bignums(olean(ctor([7]), string("x"), scalar_array(4, b"\0" * 8))), [])

    def test_two_builds_differing_only_in_padding_report_the_same_value(self):
        one = olean(ctor([1]), mpz(2 ** 64, b"\x8b\x23\x4d\x01\0\0\0"))
        two = olean(ctor([1]), mpz(2 ** 64, b"\x0b\xa4\x26\x01\0\0\0"))
        self.assertNotEqual(one, two)
        self.assertEqual(tool.bignums(one), tool.bignums(two))

    def test_refuses_what_it_cannot_walk(self):
        with self.assertRaises(tool.OleanWalkError):
            tool.bignums(b"not an olean at all, just some bytes padded out" + b"\0" * 32)
        with self.assertRaises(tool.OleanWalkError):
            tool.bignums(olean(ctor([1]), obj(254, 16, 0, b"\0" * 8)))  # an external object
        with self.assertRaises(tool.OleanWalkError):
            tool.bignums(olean(ctor([1]))[:-4])  # truncated
        overrun = olean(ctor([1]))
        overrun = overrun[:-16] + struct.pack("<iHBB", 0, 64, 1, 0) + overrun[-8:]
        with self.assertRaises(tool.OleanWalkError):
            tool.bignums(overrun)

    def test_cli_refuse_exit_codes(self):
        with tempfile.TemporaryDirectory() as scratch:
            clean = Path(scratch) / "Clean.olean"
            clean.write_bytes(olean(ctor([1])))
            held = Path(scratch) / "Held.olean"
            held.write_bytes(olean(mpz(2 ** 64)))
            broken = Path(scratch) / "Broken.olean"
            broken.write_bytes(b"garbage")
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                self.assertEqual(tool.main(["--refuse", str(clean)]), 0)
                self.assertEqual(tool.main([str(held)]), 0)
                self.assertEqual(tool.main(["--refuse", str(clean), str(held)]), 1)
                self.assertEqual(tool.main(["--refuse", str(broken)]), 2)
            self.assertIn("18446744073709551616", out.getvalue())
            self.assertIn("cannot audit", err.getvalue())


if __name__ == "__main__":
    unittest.main()
