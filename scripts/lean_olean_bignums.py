#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""List the bignums a Lean 4.8.0 .olean persists, which make it non-reproducible.

WHY. Lean 4.8.0's release toolchain is built without GMP (its `lean/config.h`
defines no `LEAN_USE_GMP`), so a natural number at or above 2^63 is a `LeanMPZ`
object holding Lean's own `mpz` class: `bool m_sign`, seven bytes of struct
padding, `size_t m_size`, `mpn_digit * m_digits`. The object compactor that
writes an .olean copies that struct with `memcpy`, padding included, and the
padding is whatever the heap held before the allocation. So a module whose
environment holds a bignum gets different .olean bytes on every build of the
same source. Measured 2026-10-13 on trust-ir 3d315a17: three fresh builds gave
three digests of `TrustIr/Semantics/Cast.olean`, differing in exactly those
bytes of its one MPZ object (2^64, the closed term the compiler folded
`u < 2 ^ 64` into); every module holding no bignum reproduced byte for byte.

This tool walks the compacted region object by object (the header, then each
object's own size: constructor objects carry it, arrays, scalar arrays and
strings carry their capacity) and reports every MPZ object with the value it
holds. A module of the bridge closure must report none: its bytes are vendored
by digest (`scripts/regen-trustir-oleans.sh`). An object the walk cannot size
is a refusal, never a skip.

Usage: lean_olean_bignums.py [--refuse] FILE.olean...
  prints `<file>\\t0x<offset>\\t<value>` per bignum; with --refuse, exits 1 when
  any file holds one and 2 when a file cannot be walked.
"""

import argparse
import struct
import sys

HEADER = b"olean"
# olean_header (Lean 4.8.0 src/runtime/object_ref.h's companion in
# src/library/module.cpp): marker[5], version u8, githash[42], base_addr u64.
BASE_ADDR_OFFSET = 48
DATA_OFFSET = 56

MAX_CTOR_TAG = 244
TAG_ARRAY = 246
TAG_SCALAR_ARRAY = 248
TAG_STRING = 249
TAG_MPZ = 250
TAG_THUNK = 251
TAG_REF = 253


class OleanWalkError(ValueError):
    """The compacted region has an object this walk cannot size."""


def _align8(n):
    return (n + 7) & ~7


def bignums(data):
    """Every MPZ object in `data` (an .olean's bytes): `(offset, value)` pairs.

    The region after the header is the root object's offset (one word) and
    then the objects back to back, each 8-aligned; the walk must end exactly at
    the end of the file.
    """
    if len(data) < DATA_OFFSET + 8 or data[:5] != HEADER:
        raise OleanWalkError("not a Lean .olean (no `olean` header)")
    if data[5] != 1:
        raise OleanWalkError(f"olean version {data[5]}, this walk reads version 1")
    found = []
    off = DATA_OFFSET + 8
    end = len(data)
    while off < end:
        if off + 8 > end:
            raise OleanWalkError(f"truncated object header at 0x{off:x}")
        rc, cs_sz, other, tag = struct.unpack_from("<iHBB", data, off)
        if rc != 0:
            raise OleanWalkError(f"object at 0x{off:x} has rc {rc}, not a compacted object")
        if tag <= MAX_CTOR_TAG or tag in (TAG_MPZ, TAG_THUNK, TAG_REF):
            size = cs_sz
            if size < 8:
                raise OleanWalkError(f"object at 0x{off:x} (tag {tag}) has size {size}")
        elif tag == TAG_ARRAY:
            _, capacity = struct.unpack_from("<QQ", data, off + 8)
            size = 24 + 8 * capacity
        elif tag == TAG_SCALAR_ARRAY:
            _, capacity = struct.unpack_from("<QQ", data, off + 8)
            size = 24 + other * capacity
        elif tag == TAG_STRING:
            _, capacity = struct.unpack_from("<QQ", data, off + 8)
            size = 32 + capacity
        else:
            raise OleanWalkError(f"object at 0x{off:x} has tag {tag}, which this walk cannot size")
        if tag == TAG_MPZ:
            found.append((off, _mpz_value(data, off, size)))
        off += _align8(size)
    if off != end:
        raise OleanWalkError(f"walk ended at 0x{off:x}, past the end 0x{end:x}")
    return found


def _mpz_value(data, off, size):
    """The value of the non-GMP `mpz` at `off`: sign byte, padding, digit count, digits."""
    sign = data[off + 8]
    (count,) = struct.unpack_from("<Q", data, off + 16)
    if sign not in (0, 1) or size != 32 + 4 * count:
        raise OleanWalkError(f"MPZ object at 0x{off:x} is not the non-GMP layout this walk reads")
    digits = struct.unpack_from(f"<{count}I", data, off + 32)
    value = sum(digit << (32 * i) for i, digit in enumerate(digits))
    return -value if sign else value


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--refuse", action="store_true",
                        help="exit 1 if any file holds a bignum (2 if one cannot be walked)")
    parser.add_argument("files", nargs="+")
    args = parser.parse_args(argv)
    held = False
    for path in args.files:
        try:
            with open(path, "rb") as handle:
                found = bignums(handle.read())
        except (OSError, OleanWalkError) as error:
            print(f"{path}: cannot audit: {error}", file=sys.stderr)
            return 2
        for off, value in found:
            held = True
            print(f"{path}\t0x{off:x}\t{value}")
    return 1 if (held and args.refuse) else 0


if __name__ == "__main__":
    sys.exit(main())
