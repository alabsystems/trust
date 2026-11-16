#!/usr/bin/env python3
"""Regenerate the in-process binary-decompile ELF object fixtures with clang.

Runtime tests read the checked-in, SHA256-pinned hex instead of finding a C
compiler. Regeneration is explicit; --check writes only in a temporary directory.
It validates ELF64/ET_REL, machine, exact .text and the function symbol before
comparing bytes. A different clang may lay out sections differently: DIFFERS is
not success and never updates the Rust pins.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import struct
import subprocess
import tempfile


# file stem, target, ELF machine, symbol, .text bytes, symbol offset
CASES = (
    ("x86_64-inprocess-return", "x86_64", 62, "trust_fixture_return", "90c3", 1),
    ("x86_64-inprocess-undecodable", "x86_64", 62, "trust_fixture_undecodable", "90c3ff", 1),
    ("x86_64-inprocess-unsupported", "x86_64", 62, "trust_fixture_unsupported", "90cc", 1),
    ("x86_64-inprocess-unresolved", "x86_64", 62, "trust_fixture_unresolved", "90ffe0", 1),
    ("aarch64-inprocess-exclusive", "aarch64", 183, "trust_fixture_aarch64_exclusive", "00fc5fc8c0035fd6", 0),
)


def assembly(case):
    _, arch, _, symbol, hex_text, offset = case
    # Encode the x86 bytes explicitly so neither assembler mnemonic aliases nor
    # instruction selection changes the intended negative-control sequence.
    if arch == "x86_64":
        prefix = "    .byte 0x90\n"
        body = "    .byte " + ", ".join(f"0x{x:02x}" for x in bytes.fromhex(hex_text)[offset:]) + "\n"
        kind = "@"
        header = ""
    else:
        prefix = ""
        body = "    ldaxr x0, [x0]\n    ret\n"
        kind = "%"
        header = "    .arch armv8-a\n"
    return (
        header + "    .text\n" + prefix + f"    .globl {symbol}\n"
        + f"    .type {symbol},{kind}function\n{symbol}:\n" + body
        + f"    .size {symbol}, .-{symbol}\n"
        + f'    .section .note.GNU-stack,"",{kind}progbits\n'
    )


def validate(data, case):
    """Check the generated object independently of clang's exit status."""
    _, _, machine, symbol, hex_text, offset = case
    if len(data) < 64 or data[:7] != b"\x7fELF\x02\x01\x01":
        raise ValueError("not a little-endian ELF64 object")
    header = struct.unpack_from("<HHIQQQIHHHHHH", data, 16)
    etype, actual_machine = header[:2]
    shoff, shentsize, shnum, shstrndx = header[5], header[10], header[11], header[12]
    if (etype, actual_machine, shentsize) != (1, machine, 64):
        raise ValueError("wrong ELF type, machine or section-header width")
    if not 0 < shstrndx < shnum or shoff + shnum * shentsize > len(data):
        raise ValueError("invalid section table")
    sections = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize) for i in range(shnum)]

    def contents(section):
        start, size = section[4:6]
        if start + size > len(data):
            raise ValueError("section outside object")
        return data[start:start + size]

    def string(table, start):
        if start >= len(table):
            raise ValueError("string outside table")
        end = table.find(b"\0", start)
        if end < 0:
            raise ValueError("unterminated string")
        return table[start:end].decode("ascii")

    names = contents(sections[shstrndx])
    text = [(i, s) for i, s in enumerate(sections) if string(names, s[0]) == ".text"]
    if len(text) != 1 or contents(text[0][1]) != bytes.fromhex(hex_text):
        raise ValueError(".text is not the intended instruction sequence")
    functions = []
    for section in sections:
        if section[1] != 2:  # SHT_SYMTAB
            continue
        if section[9] != 24 or section[5] % 24 or section[6] >= len(sections):
            raise ValueError("invalid symbol table")
        symbols = contents(section)
        strings = contents(sections[section[6]])
        for i in range(0, len(symbols), 24):
            name, info, _, index, value, size = struct.unpack_from("<IBBHQQ", symbols, i)
            if info & 15 == 2:  # STT_FUNC
                functions.append((string(strings, name), info >> 4, index, value, size))
    if functions != [(symbol, 1, text[0][0], offset, len(bytes.fromhex(hex_text)) - offset)]:
        raise ValueError(f"unexpected function symbols: {functions}")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--cc", default="clang", help="one compiler executable, not shell text")
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parent
    generated = []
    try:
        with tempfile.TemporaryDirectory(prefix="binary-decomp-inprocess-") as scratch:
            for case in CASES:
                stem, arch = case[:2]
                asm = Path(scratch) / (stem + ".s")
                obj = Path(scratch) / (stem + ".o")
                asm.write_text(assembly(case))
                subprocess.run([args.cc, f"--target={arch}-unknown-linux-gnu", "-c", "-x", "assembler",
                                str(asm), "-o", str(obj)], check=True, timeout=30)
                data = obj.read_bytes()
                validate(data, case)
                encoded = "\n".join(data[i:i + 32].hex() for i in range(0, len(data), 32)) + "\n"
                generated.append((root / (stem + "-elf.hex"), encoded, hashlib.sha256(data).hexdigest()))
        # Validate all five before any write, so a failed assembler never leaves
        # only part of the fixture set regenerated.
        differs = False
        for path, encoded, digest in generated:
            if args.check:
                same = path.is_file() and bytes.fromhex(path.read_text()) == bytes.fromhex(encoded)
                differs |= not same
                print(f"{'reproduced' if same else 'DIFFERS'} {path.name} sha256={digest}")
            else:
                path.write_text(encoded)
                print(f"generated {path.name} sha256={digest}; re-pin the Rust consumer deliberately")
        return int(differs)
    except (OSError, ValueError, struct.error, subprocess.SubprocessError) as error:
        parser.exit(2, f"in-process fixture regeneration failed: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
