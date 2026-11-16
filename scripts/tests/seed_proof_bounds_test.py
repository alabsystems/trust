#!/usr/bin/env python3
"""Bound proof capture before parsing; these controls never launch a process."""

from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import dual_host_seed_ledger_test as fixture
from scripts import mint_seed_support as support
from scripts import seed_host_ledger as ledger


class ShortCapture:
    def __init__(self, handle, calls):
        self.handle, self.calls = handle, calls

    def __enter__(self):
        self.handle.__enter__()
        return self

    def __exit__(self, *args):
        return self.handle.__exit__(*args)

    def fileno(self):
        return self.handle.fileno()

    def read(self, limit):
        self.calls.append(limit)
        return self.handle.read(limit)[:-1]


class SeedProofBoundsTests(unittest.TestCase):
    def setUp(self):
        self.process_guard = mock.patch("subprocess.Popen", side_effect=AssertionError("no process may execute"))
        self.process_guard.start()
        self.addCleanup(self.process_guard.stop)

    def test_exact_bound_captures_identical_native_and_foreign_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "proof"
            payload = b"x" * ledger.MAX_PROOF_BYTES
            path.write_bytes(payload)
            self.assertEqual(ledger.read_proof_file(path), payload)
            self.assertEqual(ledger.read_proof(root, "proof"), payload)

    def test_zero_and_oversized_files_refuse_before_open(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "proof"
            for size in (0, ledger.MAX_PROOF_BYTES + 1):
                path.write_bytes(b"x" * size)
                for reader in (lambda: ledger.read_proof_file(path), lambda: ledger.read_proof(root, "proof")):
                    with self.subTest(size=size, reader=reader), mock.patch.object(os, "open") as opened:
                        with self.assertRaisesRegex(ValueError, "bounded input size"):
                            reader()
                        opened.assert_not_called()

    def test_final_symlink_and_directory_refuse_before_open(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            target = root / "target"
            target.write_bytes(b"proof")
            alias = root / "alias"
            alias.symlink_to(target)
            for path in (root, alias):
                with self.subTest(path=path), mock.patch.object(os, "open") as opened:
                    with self.assertRaisesRegex(ValueError, "regular file"):
                        ledger.read_proof_file(path)
                    opened.assert_not_called()

    def test_foreign_parent_alias_remains_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            target = root / "target"
            target.mkdir()
            (target / "proof").write_bytes(b"proof")
            (root / "alias").symlink_to(target, target_is_directory=True)
            with mock.patch.object(os, "open") as opened:
                with self.assertRaisesRegex(ValueError, "symlink"):
                    ledger.read_proof(root, "alias/proof")
                opened.assert_not_called()

    def test_short_native_and_foreign_reads_refuse_exact_length_mismatch(self):
        original = os.fdopen
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "proof"
            path.write_bytes(b"unchanged regular proof")
            for reader in (lambda: ledger.read_proof_file(path), lambda: ledger.read_proof(root, "proof")):
                calls = []
                def shortened(fd, mode):
                    return ShortCapture(original(fd, mode), calls)
                with self.subTest(reader=reader), mock.patch.object(os, "fdopen", side_effect=shortened):
                    with self.assertRaisesRegex(ValueError, "capture length differs"):
                        reader()
                self.assertEqual(calls, [ledger.MAX_PROOF_BYTES + 1])

    def test_metadata_change_during_capture_refuses_even_at_same_length(self):
        original = os.fstat
        calls = []
        def changed(fd):
            fields = original(fd)
            calls.append(fd)
            if len(calls) == 1:
                return fields
            return SimpleNamespace(**{name: getattr(fields, name) + (1 if name == "st_ctime_ns" else 0)
                                      for name in ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")})
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "proof"
            path.write_bytes(b"proof")
            with mock.patch.object(os, "fstat", side_effect=changed):
                with self.assertRaisesRegex(ValueError, "changed during capture"):
                    ledger.read_proof_file(path)

    def native_refusal(self, kind, short):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pins, _ = fixture.fixture(root)
            (root / "src-stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n" + fixture.stage0_text(pins))
            (root / "src/stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n")
            receipt, surface = fixture.proof_bytes(fixture.LINUX)
            paths = {"receipt": root / "native-receipt", "surface": root / "native-surface"}
            payloads = {"receipt": receipt, "surface": surface}
            if not short:
                payloads[kind] += b" " * (ledger.MAX_PROOF_BYTES + 1 - len(payloads[kind]))
            for name, path in paths.items():
                path.write_bytes(payloads[name])
            target_inode = paths[kind].stat().st_ino
            original_fdopen, original_read = os.fdopen, Path.read_bytes
            original_receipt_parse, original_json_parse = support.parse_receipt, json.loads
            calls = []
            def fdopen(fd, mode):
                handle = original_fdopen(fd, mode)
                return ShortCapture(handle, calls) if short and os.fstat(fd).st_ino == target_inode else handle
            def read_bytes(path):
                if path in paths.values():
                    raise AssertionError("native proof must not use unbounded Path.read_bytes")
                return original_read(path)
            with mock.patch.object(support, "repository_state", return_value={"commit": fixture.COMMIT, "commit_date": fixture.DATE}), \
                 mock.patch.object(support, "read_stage0_pin", return_value={"compiler_git_commit_hash": "b" * 40, "compiler_date": "2026-07-13"}), \
                 mock.patch.object(support, "check_repin_date"), \
                 mock.patch.object(support, "create_repin_commit") as commit, \
                 mock.patch.object(support, "parse_receipt", wraps=original_receipt_parse) as receipt_parse, \
                 mock.patch.object(json, "loads", wraps=original_json_parse) as surface_parse, \
                 mock.patch.object(os, "fdopen", side_effect=fdopen), \
                 mock.patch.object(Path, "read_bytes", read_bytes):
                with self.assertRaisesRegex(support.WorkflowError, "capture length differs" if short else "bounded input size"):
                    support.repin(root, root, fixture.COMMIT, fixture.LINUX, "seed/inert",
                                  "Inert <inert@example.invalid>", paths["receipt"], paths["surface"], root)
                commit.assert_not_called()
                self.assertEqual(receipt_parse.call_count, 0 if kind == "receipt" else 1)
                surface_parse.assert_not_called()
            self.assertEqual(calls, [ledger.MAX_PROOF_BYTES + 1] if short else [])

    def test_native_oversized_receipt_and_surface_refuse_before_their_parsers(self):
        for kind in ("receipt", "surface"):
            with self.subTest(kind=kind):
                self.native_refusal(kind, short=False)

    def test_native_short_receipt_and_surface_refuse_before_their_parsers(self):
        for kind in ("receipt", "surface"):
            with self.subTest(kind=kind):
                self.native_refusal(kind, short=True)


if __name__ == "__main__":
    unittest.main()
