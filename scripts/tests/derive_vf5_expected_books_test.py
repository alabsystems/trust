#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Focused contracts for independent comparison DATA, not kernel proofs."""

import contextlib
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "derive_vf5_expected_books.py"
if not SCRIPT.exists():
    SCRIPT = ROOT / "scripts/derive_vf5_expected_books.py"
if not SCRIPT.exists():
    SCRIPT = Path(__file__).with_name("derive_vf5_expected_books.py")
SPEC = importlib.util.spec_from_file_location("derive_vf5_expected_books", SCRIPT)
TOOL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOL)


def encoded(value):
    return json.dumps(value, separators=(",", ":")).encode()


def fixture():
    # Deliberately untrusted protocol DATA. No artifact, Lean execution or
    # Source provenance is established by these parser/derivation controls.
    source = {"clean_revision": "b" * 40, "lean_world": "v4.30.0-rc2",
              "source_files": {f"fixture/{i}.lean": "0" * 64 for i in range(51)}}
    def row(target, field):
        return {"name": TOOL.name(target), "level_params": [], field: [2, 0], "observed_nodes": 2}
    exported = {
        "kind": "vf5-independent-repaired-world-bytes-v1", "projection_scope": "test DATA",
        "clean_revision": source["clean_revision"], "lean_world": source["lean_world"],
        "target_type_codec": TOOL.CODEC, "production_admission": False,
        "producer_control_families": ["test DATA"],
        "target_types": [row(target, "canonical_type_bytes") for target in TOOL.TYPE_TARGETS],
        "definition_values": [dict(row(target, "canonical_value_bytes"), constant_kind="defnInfo")
                              for target in TOOL.VALUE_TARGETS],
    }
    return exported, source


def derive(exported, source):
    return TOOL.derive(TOOL.MARKER + encoded(exported) + b"\n", encoded(source))


class IndependentBooksTests(unittest.TestCase):
    def test_books_match_the_minimal_type_and_definition_reader_schemas(self):
        exported, source = fixture()
        books = derive(exported, source)
        types = books["INDEPENDENT-TARGET-TYPES.json"]
        values = books["INDEPENDENT-DEFINITION-VALUES.json"]
        self.assertEqual(len(types), 7)
        self.assertEqual(set(types[0]), {"name", "level_params", "canonical_type_byte_len", "canonical_type_sha256"})
        self.assertEqual(set(values), {"codec", "definition_values"})
        self.assertEqual(values["codec"], TOOL.CODEC)
        self.assertEqual(len(values["definition_values"]), 5)
        self.assertEqual(set(values["definition_values"][0]),
                         {"name", "level_params", "canonical_value_byte_len", "canonical_value_sha256"})
        self.assertEqual(values["definition_values"][0]["canonical_value_sha256"],
                         list(hashlib.sha256(b"\x02\x00").digest()))
        self.assertIs(books["DERIVATION.json"]["production_admission"], False)

    def test_same_types_with_different_definition_bodies_produce_different_value_books(self):
        exported, source = fixture()
        before = derive(exported, source)
        exported["definition_values"][1]["canonical_value_bytes"] = [2, 1]
        after = derive(exported, source)
        self.assertEqual(before["INDEPENDENT-TARGET-TYPES.json"], after["INDEPENDENT-TARGET-TYPES.json"])
        self.assertNotEqual(before["INDEPENDENT-DEFINITION-VALUES.json"], after["INDEPENDENT-DEFINITION-VALUES.json"])

    def test_refuses_missing_ambiguous_duplicate_key_and_measured_report_inputs(self):
        exported, source = fixture()
        line = TOOL.MARKER + encoded(exported)
        for stdout in (b"{}", line + b"\n" + line,
                       line.replace(b'"production_admission":false',
                                    b'"production_admission":false,"production_admission":true'),
                       b'{"kind":"vf5-definition-values-measurement-v1"}'):
            with self.subTest(stdout=stdout[:60]), self.assertRaises(ValueError):
                TOOL.derive(stdout, encoded(source))

    def test_refuses_changed_source_world_codec_and_authority_claims(self):
        exported, source = fixture()
        for key, value in (("clean_revision", "c" * 40), ("lean_world", "v4.8.0"),
                           ("target_type_codec", "another codec"), ("production_admission", 0),
                           ("production_admission", True)):
            changed = copy.deepcopy(exported); changed[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                derive(changed, source)
        source["clean_revision"] = exported["clean_revision"] = TOOL.OLD_WORLD
        with self.assertRaisesRegex(ValueError, "old248"):
            derive(exported, source)

    def test_refuses_missing_duplicate_reordered_or_renamed_target_rows(self):
        exported, source = fixture()
        for key in ("target_types", "definition_values"):
            variants = []
            rows = copy.deepcopy(exported[key]); rows.pop(); variants.append(rows)
            rows = copy.deepcopy(exported[key]); rows[1] = rows[0]; variants.append(rows)
            rows = copy.deepcopy(exported[key]); rows[0], rows[1] = rows[1], rows[0]; variants.append(rows)
            rows = copy.deepcopy(exported[key]); rows[0]["name"] = TOOL.name("other"); variants.append(rows)
            for rows in variants:
                changed = copy.deepcopy(exported); changed[key] = rows
                with self.subTest(key=key), self.assertRaises(ValueError):
                    derive(changed, source)

    def test_refuses_nonbytes_universes_wrong_kind_and_unsupported_row_fields(self):
        exported, source = fixture()
        for field, value in (("canonical_value_bytes", []), ("canonical_value_bytes", [True]),
                             ("canonical_value_bytes", [256]), ("canonical_value_bytes", [-1]),
                             ("canonical_value_bytes", [2.0]), ("constant_kind", "thmInfo"),
                             ("level_params", ["u"]), ("observed_nodes", True), ("extra", 1)):
            changed = copy.deepcopy(exported); changed["definition_values"][0][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                derive(changed, source)

    def test_source_book_population_hashes_and_world_domains_are_checked(self):
        exported, source = fixture()
        for mutation in (lambda s: s["source_files"].pop("fixture/0.lean"),
                         lambda s: s["source_files"].update({"fixture/0.lean": "bad"}),
                         lambda s: s["source_files"].update({"../escape": s["source_files"].pop("fixture/0.lean")}),
                         lambda s: s.update({"lean_world": "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"})):
            changed = copy.deepcopy(source); mutation(changed)
            with self.assertRaises(ValueError):
                derive(exported, changed)

    def test_cli_preserves_originals_and_never_overwrites_existing_evidence(self):
        exported, source = fixture()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); stdout = b"oracle log\n" + TOOL.MARKER + encoded(exported) + b"\n"
            (root / "stdout").write_bytes(stdout); (root / "source").write_bytes(encoded(source))
            argv = [str(root / "stdout"), str(root / "source"), str(root / "new")]
            self.assertEqual(TOOL.main(argv), 0)
            self.assertEqual((root / "new/ORIGINAL.stdout").read_bytes(), stdout)
            self.assertEqual((root / "new/SOURCE-BOOK.json").read_bytes(), encoded(source))
            before = {path.name: path.read_bytes() for path in (root / "new").iterdir()}
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(TOOL.main(argv), 2)
            self.assertEqual(before, {path.name: path.read_bytes() for path in (root / "new").iterdir()})
            (root / "stdout").write_bytes(b"not an export")
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(TOOL.main(argv[:-1] + [str(root / "invalid")]), 2)
            self.assertFalse((root / "invalid").exists())


if __name__ == "__main__":
    unittest.main()
