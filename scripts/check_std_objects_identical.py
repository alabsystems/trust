#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Compare every core/alloc/std rlib object in two completed sysroot lib dirs.

Usage: check_std_objects_identical.py --without-producer LIB --with-producer LIB

This compares captured bytes; it does not establish either build's flags, source,
compiler identity, object validity, or formal correctness. Bind those separately
to the two builds. No build, archive extraction, or compiler command is executed.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys

CRATES = ("core", "alloc", "std")
MAX_ARCHIVE = 1024 * 1024 * 1024
SYMBOL_TABLES = {"/", "/SYM64/", "__.SYMDEF", "__.SYMDEF SORTED",
                 "__.SYMDEF_64", "__.SYMDEF_64 SORTED"}
SCOPE = ("Exact complete core/alloc/std object-member byte comparison DATA. "
         "No build provenance, source-to-machine, proof, SDK, or release claim.")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def archive_objects(raw):
    """Read regular BSD/GNU ar, refusing thin, unknown, or ambiguous members."""
    require(raw[:8] == b"!<arch>\n", "expected a regular ar archive (thin archives refused)")
    position, names, objects, long_names = 8, set(), {}, None
    metadata = 0
    while position < len(raw):
        require(len(raw) - position >= 60, "truncated archive member header")
        header = raw[position:position + 60]
        require(header[58:] == b"`\n", "invalid archive member header")
        size_text = header[48:58].strip()
        require(size_text.isdigit(), "invalid archive member length")
        size = int(size_text)
        position += 60
        require(size <= len(raw) - position, "truncated archive member payload")
        payload = memoryview(raw)[position:position + size]
        position += size
        if size % 2:
            require(position < len(raw) and raw[position:position + 1] == b"\n",
                    "missing archive alignment byte")
            position += 1
        try:
            name = header[:16].rstrip(b" ").decode("ascii")
        except UnicodeError as error:
            raise ValueError("non-ASCII archive member header name") from error
        if name == "//":
            require(long_names is None, "duplicate GNU long-name table")
            long_names = bytes(payload)
            continue
        if name.startswith("#1/"):
            length = name[3:]
            require(length.isdigit() and 0 < int(length) <= len(payload),
                    "invalid BSD extended member name")
            length = int(length)
            encoded = bytes(payload[:length]).rstrip(b"\0")
            payload = payload[length:]
            try:
                name = encoded.decode("ascii")
            except UnicodeError as error:
                raise ValueError("non-ASCII BSD member name") from error
        elif name.startswith("/") and name[1:].isdigit():
            offset = int(name[1:])
            require(long_names is not None and offset < len(long_names),
                    "missing or invalid GNU long-name reference")
            require(offset == 0 or long_names[offset - 1:offset] == b"\n",
                    "GNU name reference is not at an entry boundary")
            end = long_names.find(b"/\n", offset)
            require(end >= 0, "unterminated GNU long name")
            try:
                name = long_names[offset:end].decode("ascii")
            except UnicodeError as error:
                raise ValueError("non-ASCII GNU member name") from error
        elif name not in SYMBOL_TABLES:
            name = name.removesuffix("/")
        require(name and name.isprintable(), "empty or nonprintable member name")
        require(name not in names, f"duplicate archive member: {name}")
        names.add(name)
        if name in SYMBOL_TABLES:
            continue
        require("/" not in name and "\\" not in name and name not in (".", ".."),
                f"noncanonical archive member: {name}")
        if name == "lib.rmeta":
            metadata += 1
        elif name.endswith((".o", ".obj")):
            # A bitcode-only LTO member is not evidence about native object bytes.
            magic = bytes(payload[:4])
            native = (magic in (b"\x7fELF", b"\xfe\xed\xfa\xce", b"\xce\xfa\xed\xfe",
                                b"\xfe\xed\xfa\xcf", b"\xcf\xfa\xed\xfe")
                      or bytes(payload[:2]) in (b"\x64\x86", b"\x64\xaa", b"\x4c\x01"))
            require(len(payload) >= 20 and native,
                    f"unsupported non-native object member: {name}")
            objects[name] = payload
        else:
            raise ValueError(f"unsupported archive member: {name}")
    require(metadata == 1, "rlib must contain exactly one lib.rmeta member")
    require(objects, "rlib has no native object members")
    return objects


def stamp(info):
    return (info.st_dev, info.st_ino, info.st_mode, info.st_size,
            info.st_mtime_ns, info.st_ctime_ns)


def capture(path):
    """Read one plain file and bind both the path and the actual open FD."""
    path_before = os.stat(path, follow_symlinks=False)
    require(stat.S_ISREG(path_before.st_mode), f"archive path is not a plain file: {path}")
    with os.fdopen(os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)), "rb") as stream:
        before = os.fstat(stream.fileno())
        require(stamp(before) == stamp(path_before), f"archive path changed before reading: {path}")
        require(stat.S_ISREG(before.st_mode) and 0 < before.st_size <= MAX_ARCHIVE,
                f"not a supported regular archive: {path}")
        raw = stream.read(MAX_ARCHIVE + 1)
        require(len(raw) == before.st_size and stamp(before) == stamp(os.fstat(stream.fileno())),
                f"archive changed while reading: {path}")
    require(stamp(before) == stamp(os.stat(path, follow_symlinks=False)),
            f"archive path changed while reading: {path}")
    return raw, stamp(before)


def selected(root):
    require(root.is_dir(), f"not a library directory: {root}")
    result = {}
    entries = list(root.iterdir())
    for crate in CRATES:
        pattern = re.compile(r"lib" + crate + r"(?:-[0-9a-f]+)?\.rlib\Z")
        matches = [entry for entry in entries if entry.name == f"lib{crate}.rlib"
                   or (entry.name.startswith(f"lib{crate}-") and entry.name.endswith(".rlib"))]
        require(all(pattern.fullmatch(entry.name) for entry in matches),
                f"noncanonical {crate} rlib filename in {root}")
        require(len(matches) == 1, f"expected exactly one {crate} rlib in {root}")
        result[crate] = matches[0]
    return result


def compare(without_producer, with_producer):
    roots = [Path(without_producer).resolve(strict=True), Path(with_producer).resolve(strict=True)]
    require(roots[0] != roots[1], "the two library directories must be distinct")
    selections = [selected(root) for root in roots]
    captured = []
    for selection in selections:
        side = {}
        for crate, path in selection.items():
            raw, identity = capture(path)
            side[crate] = {"path": str(path), "identity": identity,
                           "raw": raw, "objects": archive_objects(raw)}
        captured.append(side)
    identities = [row[crate]["identity"][:2] for row in captured for crate in CRATES]
    require(len(set(identities)) == 6, "selected archives must be six distinct physical files")
    rows = []
    for crate in CRATES:
        before, after = [side[crate] for side in captured]
        a, b = before["objects"], after["objects"]
        rows.append({
            "crate": crate,
            "without_producer": inventory(before), "with_producer": inventory(after),
            "missing_objects": sorted(a.keys() - b.keys()),
            "extra_objects": sorted(b.keys() - a.keys()),
            "changed_objects": sorted(name for name in a.keys() & b.keys() if a[name] != b[name]),
        })
    # Revalidate actual input bytes as well as inode/stamps after all comparisons.
    for root, selection, side in zip(roots, selections, captured):
        require(selected(root) == selection, f"selected crate population changed: {root}")
        for row in side.values():
            raw, identity = capture(row["path"])
            require(identity == row["identity"] and raw == row["raw"],
                    f"archive changed during comparison: {row['path']}")
    equal = all(not row[key] for row in rows
                for key in ("missing_objects", "extra_objects", "changed_objects"))
    return {"schema": "trust.std-object-comparison.v1", "status": "identical" if equal else "different",
            "object_bytes_identical": equal, "inputs_revalidated": True,
            "scope": SCOPE, "crates": rows}


def inventory(row):
    return {"path": row["path"], "archive_bytes": len(row["raw"]),
            "archive_sha256": digest(row["raw"]),
            "object_count": len(row["objects"]),
            "object_bytes": sum(len(data) for data in row["objects"].values()),
            "objects": [{"name": name, "bytes": len(data), "sha256": digest(data)}
                        for name, data in sorted(row["objects"].items())]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--without-producer", required=True, type=Path, metavar="LIB")
    parser.add_argument("--with-producer", required=True, type=Path, metavar="LIB")
    args = parser.parse_args(argv)
    try:
        report = compare(args.without_producer, args.with_producer)
        code = 0 if report["object_bytes_identical"] else 1
    except (OSError, ValueError) as error:
        report = {"schema": "trust.std-object-comparison.v1", "status": "refused",
                  "scope": SCOPE, "error": str(error)}
        code = 2
    json.dump(report, sys.stdout, sort_keys=True, indent=2)
    print()
    return code


if __name__ == "__main__":
    raise SystemExit(main())
