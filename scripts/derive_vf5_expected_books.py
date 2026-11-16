#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Derive untrusted VF5 comparison books from independent Lean byte output.

Usage: derive_vf5_expected_books.py ORIGINAL_STDOUT SOURCE_BOOK NEW_DIRECTORY

The input must be the original official-Lean export, produced independently of
the Rust measurement. This script does not authenticate that producer, prove
source provenance, run a kernel, admit a reference, or activate a pin. Join the
original execution/custody evidence separately. It never reads a Rust report.
"""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

MARKER = b"VF5_INDEPENDENT_REPAIRED_WORLD_BYTES="
CODEC = "clean_auto::bridge::ay_contract::serialize_term/bincode2-standard"
TYPE_TARGETS = ("RowProved", "row_of", "checkBlob", "rowShape",
                "vc_sound_F1", "compose_F1", "rootsSafe_of")
VALUE_TARGETS = ("functionIdsUnique", "checkModuleC", "rowShape", "RowProved", "ValidBlob")
OLD_WORLD = "24861300fea40294bb485bb630eb216756dc558d"
MAX_INPUT_BYTES = 1024 * 1024 * 1024
MAX_TERM_BYTES = 64 * 1024 * 1024


def strict_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def read_json(raw):
    def reject_constant(value):
        raise ValueError(f"non-JSON numeric constant: {value}")
    return json.loads(raw, object_pairs_hook=strict_object, parse_constant=reject_constant)


def exact_fields(value, fields, label):
    if not isinstance(value, dict) or set(value) != set(fields):
        raise ValueError(f"wrong {label} fields")


def name(leaf):
    return {"Str": [{"Str": ["Anon", "VF5"]}, leaf]}


def canonical_bytes(row, field):
    values = row[field]
    if not isinstance(values, list) or not 0 < len(values) <= MAX_TERM_BYTES:
        raise ValueError("missing, empty or oversized canonical bytes")
    if any(type(value) is not int or not 0 <= value <= 255 for value in values):
        raise ValueError("canonical bytes must be literal u8 integers")
    return bytes(values)


def derive(stdout, source_raw):
    """Pure derivation: compare metadata, hash literal bytes, grant no authority."""
    lines = [line[len(MARKER):] for line in stdout.splitlines() if line.startswith(MARKER)]
    if len(lines) != 1:
        raise ValueError("require exactly one original independent Lean byte export")
    exported, source = read_json(lines[0]), read_json(source_raw)
    exact_fields(source, ("clean_revision", "lean_world", "source_files"), "Source book")
    revision = source["clean_revision"]
    if not isinstance(revision, str) or not re.fullmatch("[0-9a-f]{40}", revision):
        raise ValueError("Source book requires an exact Clean commit")
    if revision == OLD_WORLD:
        raise ValueError("old248 is not a repaired-world export")
    sources = source["source_files"]
    if not isinstance(sources, dict) or len(sources) != 51:
        raise ValueError("require a 51-member Source book; check provenance separately")
    for path, digest in sources.items():
        if (not path or PurePosixPath(path).is_absolute() or "\\" in path
                or any(part in ("", ".", "..") for part in path.split("/"))
                or not isinstance(digest, str) or not re.fullmatch("[0-9a-f]{64}", digest)):
            raise ValueError("malformed Source path/hash")
    exact_fields(exported, ("kind", "projection_scope", "clean_revision", "lean_world",
                          "target_type_codec", "production_admission", "producer_control_families",
                          "definition_values", "target_types"), "independent export")
    if exported["kind"] != "vf5-independent-repaired-world-bytes-v1":
        raise ValueError("wrong independent producer kind")
    if exported["production_admission"] is not False:
        raise ValueError("an independent byte producer cannot grant authority")
    if (exported["clean_revision"] != revision or exported["lean_world"] != source["lean_world"]
            or source["lean_world"] != "v4.30.0-rc2"):
        raise ValueError("Source/package-world identity mismatch")
    if exported["target_type_codec"] != CODEC:
        raise ValueError("wrong bounded term codec")
    types, values = [], []
    for key, targets, field, output in (
            ("target_types", TYPE_TARGETS, "canonical_type_bytes", types),
            ("definition_values", VALUE_TARGETS, "canonical_value_bytes", values)):
        rows = exported[key]
        if (not isinstance(rows, list) or len(rows) != len(targets)
                or any(not isinstance(row, dict) for row in rows)
                or [row.get("name") for row in rows] != [name(target) for target in targets]):
            raise ValueError(f"changed {key} denominator/order/names")
        for row in rows:
            fields = ("name", "level_params", field, "observed_nodes")
            if key == "definition_values":
                fields += ("constant_kind",)
            exact_fields(row, fields, key + " row")
            if row["level_params"] != []:
                raise ValueError("unexpected target universe parameters")
            if type(row["observed_nodes"]) is not int or row["observed_nodes"] <= 0:
                raise ValueError("invalid producer node count")
            if key == "definition_values" and row["constant_kind"] != "defnInfo":
                raise ValueError("repaired value subject is not a definition")
            data = canonical_bytes(row, field)
            stem = field.removesuffix("_bytes")
            output.append({"name": row["name"], "level_params": [],
                           stem + "_byte_len": len(data),
                           stem + "_sha256": list(hashlib.sha256(data).digest())})
    return {
        "ORIGINAL-REPAIRED-LEAN-BYTES.json": exported,
        "INDEPENDENT-TARGET-TYPES.json": types,
        "INDEPENDENT-DEFINITION-VALUES.json": {"codec": CODEC, "definition_values": values},
        "DERIVATION.json": {
            "kind": "independent-vf5-comparison-DATA-only", "clean_revision": revision,
            "lean_world": source["lean_world"], "original_stdout_sha256": hashlib.sha256(stdout).hexdigest(),
            "source_book_sha256": hashlib.sha256(source_raw).hexdigest(),
            "target_count": len(types), "definition_count": len(values),
            "production_admission": False, "pin_update": False,
            "qualification": "NOT ESTABLISHED: join original Lean execution, Source/provider custody and separate EMPTY-start Rust replay",
        },
    }


def read_bounded(path, limit=MAX_INPUT_BYTES):
    with path.open("rb") as stream:
        raw = stream.read(limit + 1)
    if len(raw) > limit:
        raise ValueError(f"input exceeds {limit} bytes: {path}")
    return raw


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("original_stdout", type=Path)
    parser.add_argument("source_book", type=Path)
    parser.add_argument("new_directory", type=Path)
    args = parser.parse_args(argv)
    try:
        stdout, source = read_bounded(args.original_stdout), read_bounded(args.source_book)
        books = derive(stdout, source)
        # Complete validation precedes any output. Never replace earlier evidence.
        args.new_directory.mkdir(mode=0o700)
        for filename, data in books.items():
            with (args.new_directory / filename).open("x") as output:
                output.write(json.dumps(data, indent=2, sort_keys=True) + "\n")
        for filename, raw in (("ORIGINAL.stdout", stdout), ("SOURCE-BOOK.json", source)):
            with (args.new_directory / filename).open("xb") as output:
                output.write(raw)
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(f"independent VF5 book derivation refused: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
