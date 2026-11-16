#!/usr/bin/env python3
"""The Python stage-receipt reader gives the verdicts its Rust twin is held to.

crates/trust-stage-receipt is the Rust twin of scripts/lib/stage_receipt_provenance.py
and must make the same decisions on the same receipts. The crate's tests hold it to two
fixture sets committed under crates/trust-stage-receipt/tests/data:

  * reference.json.gz, the 204 filesystem cases recorded from this reader's tests
    (PROVENANCE.md beside it): the lines of each accepted case, and that each refused
    case is refused (its prose is observational there, and here);
  * fixed-point-cases.json, receipts whose seed capture selected a host record
    (docs/PLAN.md PKG-S6) and receipts that bind native stage tools (rust-lld and its
    stated in-tree LLVM), each with its exact lines (the receipt's own digest apart)
    or its exact refusal (the stage directory's path apart).

It also holds the Python reader to the two JSON bounds the crate's json.rs applies (1000
nested containers, 4300-digit integers) whatever the interpreter allows, on a receipt the
crate's src/tests.rs builds the same way.

This module runs the Python reader on the same inputs and holds it to the same verdicts,
so a change to either reader that the other does not make turns one of the two suites
red. It runs no Rust and builds nothing: a verdict here is the Python reader's, and the
crate's own tests (`targo --unverified test --locked` in that crate) are the Rust
reader's. The parity is the conjunction of the two runs.

Run: python3 -B scripts/tests/stage_receipt_reader_parity_test.py

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import copy
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

REPO = Path(__file__).resolve().parents[2]
READER = REPO / "scripts/lib/stage_receipt_provenance.py"
DATA = REPO / "crates/trust-stage-receipt/tests/data"
# The sha256 of reference.json.gz's JSON, which the crate's src/tests.rs pins too.
REFERENCE_SHA256 = "f563c189186c6b9ef0a16bf473e8caec61b774be9ad10d05eeeea68a83a39cfd"
FIXED_POINT_SCHEMA = "trust.stage-receipt.fixed-point-cases.v1"
RECEIPT_DIGEST = "<receipt>"
TOOLCHAIN = "<toolchain>"
# The fixture's population, which the crate's src/tests/fixed_point.rs holds too.
ACCEPTED_CASES = 13
REFUSED_CASES = 85


def load_reader():
    spec = importlib.util.spec_from_file_location("stage_receipt_provenance_parity", READER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


reader = load_reader()


def reference() -> dict:
    raw = gzip.decompress((DATA / "reference.json.gz").read_bytes())
    if hashlib.sha256(raw).hexdigest() != REFERENCE_SHA256:
        raise AssertionError("reference.json.gz is not the archive the crate's tests pin")
    return json.loads(raw)


def write_files(root: Path, files: dict) -> None:
    """Each stage-relative name of `files` under `root`, holding the bytes its hex gives."""
    for name, hexed in files.items():
        parts = name.split("/")
        if name.startswith("/") or any(part in ("", ".", "..") for part in parts):
            raise AssertionError(f"a fixture file escapes its stage: {name!r}")
        path = root.joinpath(*parts)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(bytes.fromhex(hexed))


def make_links(root: Path, links: dict) -> None:
    """Each stage-relative name of `links` under `root`, a symbolic link whose text is the
    name of a file in the same directory, which need not exist."""
    for name, target in links.items():
        parts = name.split("/")
        if name.startswith("/") or any(part in ("", ".", "..") for part in parts):
            raise AssertionError(f"a fixture link escapes its stage: {name!r}")
        if target in ("", ".", "..") or "/" in target:
            raise AssertionError(f"a fixture link leaves its directory: {name!r} -> {target!r}")
        path = root.joinpath(*parts)
        path.parent.mkdir(parents=True, exist_ok=True)
        os.symlink(target, path)


def materialize(root: Path, case: dict, receipt: bytes | None = None) -> None:
    """The stage of a reference case under `root`, with `receipt` as its receipt when given."""
    write_files(root, case["files"])
    path = root / reader.RECEIPT_NAME
    kind = "file" if receipt is not None else case["receipt_kind"]
    if kind == "file":
        path.write_bytes(receipt if receipt is not None else bytes.fromhex(case["raw_hex"]))
    elif kind == "directory":
        path.mkdir()
    elif kind == "link":
        os.symlink("unowned-receipt", path)
    elif kind != "absent":
        raise AssertionError(f"unsupported reference fixture kind {kind!r}")


def edited(receipt: dict, edits: list, paths: dict) -> dict:
    """`receipt` after `edits`, each of which sets or deletes one key of an existing table."""
    receipt = copy.deepcopy(receipt)
    for edit in edits:
        if set(edit) == {"set", "to"}:
            verb = "set"
        elif set(edit) == {"delete"}:
            verb = "delete"
        else:
            raise AssertionError(f"an edit is neither a set nor a delete: {edit!r}")
        path = edit[verb]
        if path and path[0].startswith("@"):
            path = paths[path[0][1:]] + path[1:]
        *parents, key = path
        table = receipt
        for part in parents:
            table = table[part]
        if not isinstance(table, dict):
            raise AssertionError(f"an edit's parent is not a table: {path!r}")
        if verb == "set":
            table[key] = copy.deepcopy(edit["to"])
        elif key in table:
            del table[key]
        else:
            raise AssertionError(f"an edit deletes a key that is not there: {path!r}")
    return receipt


class ReferenceVerdictTests(unittest.TestCase):
    def test_every_recorded_reference_verdict_is_still_this_readers(self):
        cases = reference()["file_cases"]
        self.assertEqual(len(cases), 204)
        accepted = refused = 0
        for index, case in enumerate(cases):
            with self.subTest(case=index), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                materialize(root, case)
                with mock.patch.object(reader, "MAX_RECEIPT_BYTES", case["max_bytes"]):
                    if case.get("lines") is not None:
                        self.assertEqual(reader.lines(root, case["commit"]), case["lines"])
                        accepted += 1
                    else:
                        with self.assertRaises(reader.StageReceiptError):
                            reader.lines(root, case["commit"])
                        refused += 1
        # The population the crate's test holds (more than 30 accepted, 80 refused).
        self.assertGreater(accepted, 30)
        self.assertGreater(refused, 80)


class FixedPointVerdictTests(unittest.TestCase):
    def test_every_fixed_point_case_gets_its_recorded_verdict(self):
        fixture = json.loads((DATA / "fixed-point-cases.json").read_text(encoding="utf-8"))
        self.assertEqual(fixture["schema"], FIXED_POINT_SCHEMA)
        base_case = reference()["file_cases"][fixture["reference_case"]]
        self.assertEqual(base_case["commit"], fixture["commit"])
        base = json.loads(bytes.fromhex(base_case["raw_hex"]))
        starts = {"base": base, "fixed-point": edited(base, fixture["fixed_point"], fixture["paths"]),
                  "native-lld": edited(base, fixture["native_lld"], fixture["paths"])}
        labels = [case["label"] for case in fixture["cases"]]
        self.assertEqual(len(labels), len(set(labels)), "a label names one case")
        accepted = refused = 0
        for case in fixture["cases"]:
            with self.subTest(case["label"]), tempfile.TemporaryDirectory() as directory:
                self.assertEqual(len({"lines", "refusal"} & set(case)), 1)
                receipt = edited(starts[case["from"]], case["edits"], fixture["paths"])
                raw = (json.dumps(receipt, indent=2, sort_keys=True) + "\n").encode("utf-8")
                root = Path(directory)
                materialize(root, base_case, raw)
                # A case's own stage files, beside the reference case's.
                files = case.get("files", {})
                self.assertIsInstance(files, dict)
                self.assertNotIn(reader.RECEIPT_NAME, files)
                write_files(root, files)
                # Its own symbolic links, each named in its own directory.
                links = case.get("links", {})
                self.assertIsInstance(links, dict)
                self.assertNotIn(reader.RECEIPT_NAME, links)
                make_links(root, links)
                if "lines" in case:
                    digest = hashlib.sha256(raw).hexdigest()
                    self.assertEqual(sum(RECEIPT_DIGEST in line for line in case["lines"]), 1)
                    self.assertEqual(reader.lines(root, fixture["commit"]),
                                     [line.replace(RECEIPT_DIGEST, digest) for line in case["lines"]])
                    accepted += 1
                else:
                    with self.assertRaises(reader.StageReceiptError) as refusal:
                        reader.lines(root, fixture["commit"])
                    self.assertEqual(str(refusal.exception), case["refusal"].replace(TOOLCHAIN, str(root)))
                    refused += 1
        # Both grades and both kinds of verdict are present: an emptied fixture is no parity.
        self.assertGreaterEqual(accepted, ACCEPTED_CASES)
        self.assertGreaterEqual(refused, REFUSED_CASES)
        statuses = {line for case in fixture["cases"] for line in case.get("lines", ())
                    if line.startswith("stage_receipt_status=")}
        self.assertEqual(statuses, {f"stage_receipt_status={status}" for status in reader.ACCEPTED_STATUSES})

    def test_an_edit_changes_what_the_reader_is_given(self):
        # The instrument: the starting receipt the cases build on is the reference
        # case's own, and an edit reaches the bytes the reader reads.
        fixture = json.loads((DATA / "fixed-point-cases.json").read_text(encoding="utf-8"))
        base = json.loads(bytes.fromhex(reference()["file_cases"][fixture["reference_case"]]["raw_hex"]))
        self.assertEqual(edited(base, [], fixture["paths"]), base)
        changed = edited(base, [{"set": ["@seed", "materialization_status"], "to": "x"}], fixture["paths"])
        self.assertEqual(changed["bootstrap_lineage"]["validated_seed"]["materialization_status"], "x")
        self.assertNotEqual(base["bootstrap_lineage"]["validated_seed"]["materialization_status"], "x")
        with self.assertRaises(AssertionError):
            edited(base, [{"delete": ["no-such-key"]}], fixture["paths"])
        # An integer step reaches a row of a list: the native-lld start's rust-lld row.
        native = edited(base, fixture["native_lld"], fixture["paths"])
        self.assertNotIn("native_stage_tools", base)
        self.assertEqual(native["native_stage_tools"][0]["status"], "bound")
        changed = edited(native, [{"set": ["@lld", "status"], "to": "x"}], fixture["paths"])
        self.assertEqual(changed["native_stage_tools"][0]["status"], "x")


def nested_receipt(depth: int) -> tuple[bytes, int]:
    """Reference file case 0's receipt with one more key, holding `depth` lists one inside
    the next, and the byte of its 1000th list. The crate's src/tests.rs builds the same."""
    raw = bytes.fromhex(reference()["file_cases"][0]["raw_hex"]).rstrip()
    if not raw.endswith(b"}"):
        raise AssertionError("the reference receipt is not one JSON object")
    prefix = raw[:-1] + b', "nested": '
    return prefix + b"[" * depth + b"]" * depth + b"}\n", len(prefix) + 999


class JsonBoundTests(unittest.TestCase):
    """Both readers refuse a receipt nested past 1000 containers or holding an integer
    of more than 4300 digits, whatever Python runs and however it is set."""

    def test_the_bounds_are_the_rust_readers(self):
        source = (REPO / "crates/trust-stage-receipt/src/json.rs").read_text(encoding="utf-8")
        self.assertEqual((reader.MAX_JSON_NESTING, reader.MAX_JSON_INTEGER_DIGITS), (1000, 4300))
        self.assertIn(f"const MAX_NESTING: usize = {reader.MAX_JSON_NESTING};", source)
        self.assertIn(f"const MAX_INTEGER_DIGITS: usize = {reader.MAX_JSON_INTEGER_DIGITS};", source)

    def test_a_receipt_nested_past_the_bound_is_refused_where_the_rust_reader_refuses_it(self):
        case = reference()["file_cases"][0]
        # 999 lists inside the receipt's own object are 1000 containers: read as before.
        raw, _ = nested_receipt(999)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            materialize(root, case, raw)
            lines = reader.lines(root, case["commit"])
        self.assertIn(f"stage_receipt_sha256={hashlib.sha256(raw).hexdigest()}", lines)
        self.assertIn("stage_receipt_files_verified=19", lines)
        # One more is refused at its byte, in the Rust reader's words, although this
        # interpreter's json module decodes it.
        raw, byte = nested_receipt(1000)
        self.assertEqual(raw[byte:byte + 1], b"[")
        self.assertIsInstance(json.loads(raw), dict)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            materialize(root, case, raw)
            with self.assertRaises(reader.StageReceiptError) as refusal:
                reader.lines(root, case["commit"])
        self.assertEqual(str(refusal.exception),
                         f"it is not JSON: JSON nesting exceeds 1000 containers at byte {byte}")

    def test_an_integer_past_the_bound_is_refused_whatever_the_interpreter_allows(self):
        case = reference()["file_cases"][0]
        prefix = bytes.fromhex(case["raw_hex"]).rstrip()[:-1] + b', "integer": -'
        default = sys.get_int_max_str_digits()
        # PYTHONINTMAXSTRDIGITS=0 would lift the interpreter's own bound like this.
        sys.set_int_max_str_digits(0)
        try:
            for digits, refused in [(4300, False), (4301, True)]:
                raw = prefix + b"9" * digits + b"}\n"
                with self.subTest(digits=digits), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    materialize(root, case, raw)
                    if not refused:
                        self.assertIn("stage_receipt_files_verified=19", reader.lines(root, case["commit"]))
                        continue
                    with self.assertRaises(reader.StageReceiptError) as refusal:
                        reader.lines(root, case["commit"])
                    self.assertEqual(str(refusal.exception),
                                     "it is not JSON: decimal integer exceeds the original 4300-digit limit")
        finally:
            sys.set_int_max_str_digits(default)

    def test_brackets_in_strings_and_after_escapes_are_not_containers(self):
        for raw, error in [
            (b"[" * 1000 + b"]" * 1000, None),
            (b"[" * 1001 + b"]" * 1001, "JSON nesting exceeds 1000 containers at byte 1000"),
            (b'{"[\\"[": ' + b"[" * 999 + b"]" * 999 + b"}", None),
            # An escaped backslash ends its escape: the quote after it closes the string.
            (b'{"\\\\": ' + b"[" * 1000 + b"]" * 1000 + b"}", "JSON nesting exceeds 1000 containers at byte 1006"),
            (b'["[[[[", "{{{{"]', None),
        ]:
            with self.subTest(raw[:12]):
                self.assertEqual(reader._nesting_error(raw), error)


if __name__ == "__main__":
    unittest.main()
