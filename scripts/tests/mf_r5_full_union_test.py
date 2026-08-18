#!/usr/bin/env python3
"""Focused fail-closed controls for ``scripts/mf_r5_full_union.py``.

Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import mf_r5_full_union as gate  # noqa: E402


def body(
    verdict: str,
    *,
    markers_exact: bool = False,
    markers_detail: str = "",
    def_index: int = 1,
    def_path: str = "probe::f",
) -> dict:
    return {
        "def_index": def_index,
        "kind": "fn",
        "def_path": def_path,
        "differentials": {
            "derived_mir": {
                "verdict": verdict,
                "markers_exact": markers_exact,
                "markers_detail": markers_detail,
            }
        },
    }


class SixCaseClassifier(unittest.TestCase):
    def test_all_review_cases_are_distinct(self):
        fixtures = [
            (body("unsupported"), "unsupported"),
            (body("mismatch"), "other_non_agreed"),
            (
                body(
                    "agreed",
                    markers_exact=True,
                    markers_detail="13 marker line(s) identical",
                ),
                "agreed_exact",
            ),
            (
                body(
                    "agreed",
                    markers_detail=(
                        "markers differ: line 0: built `mk b0.0:live s0:u32` "
                        "vs derived `<end>`"
                    ),
                ),
                "marker_free_refusal",
            ),
            (
                body(
                    "agreed",
                    markers_detail=(
                        "markers differ: line 1: built `mk b0.1:dead s0:u32` "
                        "vs derived `mk b0.2:dead s0:u32`"
                    ),
                ),
                "admitted_wrong",
            ),
            (
                body(
                    "agreed",
                    markers_detail=(
                        "marker channel(built): storage marker in unwalked block 8 "
                        "(cleanup/dead code)"
                    ),
                ),
                "marker_channel_other",
            ),
        ]
        self.assertEqual(
            [gate.classify_body(fixture) for fixture, _expected in fixtures],
            [expected for _fixture, expected in fixtures],
        )

    def test_refusal_requires_line_zero_and_derived_end(self):
        wrong_short = body(
            "agreed",
            markers_detail=(
                "markers differ: line 2: built `mk b0.2:dead s0:u32` vs derived `<end>`"
            ),
        )
        surplus = body(
            "agreed",
            markers_detail=(
                "markers differ: line 0: built `<end>` vs derived `mk b0.0:live s0:u32`"
            ),
        )
        self.assertEqual(gate.classify_body(wrong_short), "admitted_wrong")
        self.assertEqual(gate.classify_body(surplus), "admitted_wrong")

    def test_refusal_requires_a_canonical_built_marker(self):
        for detail in (
            "markers differ: line 0: built `junk` vs derived `<end>`",
            "markers differ: line 0: built `<end>` vs derived `<end>`",
            "markers differ: line 0: built `mk junk` vs derived `<end>`",
        ):
            with self.subTest(detail=detail):
                self.assertEqual(
                    gate.classify_body(body("agreed", markers_detail=detail)),
                    "admitted_wrong",
                )

    def test_unknown_or_inconsistent_schema_refuses(self):
        invalid = [
            body("future-verdict"),
            body("agreed"),
            body("agreed", markers_exact=True, markers_detail=""),
            body("agreed", markers_detail="future marker diagnostic"),
            body("unsupported", markers_detail="markers differ: x"),
            body("mismatch", markers_exact=True, markers_detail="0 marker line(s) identical"),
        ]
        for fixture in invalid:
            with self.subTest(fixture=fixture), self.assertRaises(gate.GateError):
                gate.classify_body(fixture)


class CoverageSchema(unittest.TestCase):
    def test_v2_projection_binds_full_row_identity_and_bucket(self):
        document = {
            "schema": gate.COVERAGE_SCHEMA,
            "totals": {"bodies": 1},
            "bodies": [
                body(
                    "agreed",
                    markers_exact=True,
                    markers_detail="2 marker line(s) identical",
                    def_index=17,
                    def_path="probe::exact",
                )
            ],
        }
        rows, counts = gate.validate_and_project(document, "probe.rs")
        self.assertEqual(rows, [("probe.rs", 17, "fn", "probe::exact", "agreed_exact")])
        self.assertEqual(counts, {"agreed_exact": 1})

    def test_unknown_schema_and_total_mismatch_refuse(self):
        for document in (
            {"schema": "v3", "totals": {"bodies": 0}, "bodies": []},
            {"schema": gate.COVERAGE_SCHEMA, "totals": {"bodies": 2}, "bodies": []},
        ):
            with self.subTest(document=document), self.assertRaises(gate.GateError):
                gate.validate_and_project(document, "probe.rs")

    def test_duplicate_json_key_refuses(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "coverage.json"
            path.write_text('{"schema":"a","schema":"b"}\n', encoding="utf-8")
            with self.assertRaisesRegex(gate.GateError, "repeats key"):
                gate.load_json_strict(path)


class FlipLog(unittest.TestCase):
    def test_empty_log_is_not_an_expected_corpus_measurement(self):
        count = gate.flip_event_count(b"")
        self.assertEqual(count, 0)
        probe = "crates/trust-thir-lower/probes/mb_adversarial.rs"
        with self.assertRaisesRegex(gate.GateError, "flip-event count drifted"):
            gate.require_flip_count(probe, 0, count)

    def test_unique_codegen_and_ctfe_events_are_counted(self):
        digest_a = "a" * 64
        digest_b = "b" * 64
        log = (
            "INFO trust-ir-flip: compiled from trust-ir, did=DefId(1), "
            f"asserts=0, lineage=sha256:{digest_a}, flipped_so_far=1\n"
            "INFO trust-ir-flip: CTFE compiled from trust-ir, did=DefId(2), "
            f"asserts=1, lineage=sha256:{digest_b}, flipped_so_far=2\n"
        ).encode()
        self.assertEqual(gate.flip_event_count(log), 2)

    def test_exact_measured_count_passes(self):
        probe = "crates/trust-thir-lower/probes/mb_adversarial.rs"
        self.assertEqual(gate.require_flip_count(probe, 0, 16), 16)

    def test_malformed_near_match_refuses(self):
        with self.assertRaisesRegex(gate.GateError, "malformed trust-ir flip event"):
            gate.flip_event_count(
                b"INFO trust-ir-flip: compiled from trust-ir, did=x, lineage=sha256:bad\n"
            )


class OptimizationParity(unittest.TestCase):
    ROW = ("probe.rs", 1, "fn", "probe::f", "agreed_exact")

    def test_exact_tuple_parity_passes(self):
        gate.require_opt_parity({0: [self.ROW], 3: [self.ROW]})

    def test_bucket_or_identity_movement_refuses(self):
        moved = ("probe.rs", 1, "fn", "probe::f", "marker_free_refusal")
        with self.assertRaisesRegex(gate.GateError, "parity failed"):
            gate.require_opt_parity({0: [self.ROW], 3: [moved]})

    def test_missing_optimization_refuses(self):
        with self.assertRaisesRegex(gate.GateError, "exactly O0/O3"):
            gate.require_opt_parity({0: [self.ROW]})

    def test_review_ratchet_aggregates_only_the_two_other_cases(self):
        self.assertEqual(
            gate.review_ratchet(gate.EXPECTED_BUCKET_COUNTS), gate.EXPECTED_REVIEW_RATCHET
        )

    def test_equal_cross_opt_mutation_still_fails_the_baseline_ratchet(self):
        mutated = {0: [self.ROW], 3: [self.ROW]}
        gate.require_opt_parity(mutated)
        with self.assertRaisesRegex(gate.GateError, "row-tuple digest drifted"):
            gate.require_row_tuple_ratchet(mutated)


class AtomicReceipt(unittest.TestCase):
    def test_both_run_destinations_must_be_absent(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            output = root / "output"
            receipt = root / "receipt.json"
            gate.require_fresh_destinations(output, receipt)
            output.mkdir()
            with self.assertRaisesRegex(gate.GateError, "output destination already exists"):
                gate.require_fresh_destinations(output, receipt)
            output.rmdir()
            receipt.write_bytes(b"prior receipt\n")
            with self.assertRaisesRegex(gate.GateError, "receipt destination already exists"):
                gate.require_fresh_destinations(output, receipt)

    def test_atomic_new_file_and_digest_contract(self):
        payload = {"schema": gate.SCHEMA, "status": "passed"}
        digest = gate.receipt_digest(payload)
        payload["receipt_sha256"] = digest
        encoded = gate.canonical_json(payload)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "nested" / "receipt.json"
            gate.atomic_write_new(path, encoded)
            self.assertEqual(path.read_bytes(), encoded)
            self.assertEqual(path.stat().st_mode & 0o222, 0)
            self.assertEqual(gate.receipt_digest(json.loads(path.read_text())), digest)
            self.assertEqual(list(path.parent.glob(".*.tmp")), [])

    def test_preexisting_file_is_never_replaced(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "receipt.json"
            path.write_bytes(b"prior evidence\n")
            with self.assertRaisesRegex(gate.GateError, "already exists"):
                gate.atomic_write_new(path, b"new evidence\n")
            self.assertEqual(path.read_bytes(), b"prior evidence\n")

    @unittest.skipUnless(hasattr(os, "symlink"), "symlink refusal")
    def test_dangling_symlink_counts_as_preexisting(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "receipt.json"
            path.symlink_to("missing-target")
            with self.assertRaisesRegex(gate.GateError, "already exists"):
                gate.atomic_write_new(path, b"evidence\n")
            self.assertTrue(path.is_symlink())


class RetainedEvidence(unittest.TestCase):
    def test_tree_is_sealed_and_inventoried_read_only(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "evidence"
            nested = output / "run"
            nested.mkdir(parents=True)
            artifact = nested / "artifact.json"
            artifact.write_bytes(b'{"status":"passed"}\n')
            gate.seal_evidence_tree(output)
            try:
                inventory = gate.retained_tree_inventory(output)
                self.assertEqual(output.stat().st_mode & 0o222, 0)
                self.assertEqual(nested.stat().st_mode & 0o222, 0)
                self.assertEqual(artifact.stat().st_mode & 0o222, 0)
                self.assertTrue(any(row.get("sha256") for row in inventory))
            finally:
                output.chmod(0o755)
                nested.chmod(0o755)

    @unittest.skipUnless(hasattr(os, "symlink"), "evidence symlink refusal")
    def test_tree_with_a_symlink_refuses_sealing(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "evidence"
            output.mkdir()
            (output / "link").symlink_to("missing")
            with self.assertRaisesRegex(gate.GateError, "link or special entry"):
                gate.seal_evidence_tree(output)


class ToolSelection(unittest.TestCase):
    @unittest.skipUnless(hasattr(os, "symlink"), "host alias deduplication")
    def test_default_stage1_deduplicates_host_alias(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            canonical = root / "build" / "test-host" / "stage1" / "bin" / "trustc"
            canonical.parent.mkdir(parents=True)
            canonical.write_bytes(b"compiler")
            canonical.chmod(0o755)
            (root / "build" / "host").symlink_to(root / "build" / "test-host")
            self.assertEqual(gate.select_trustc(root, None), canonical.resolve())


class AuthorityEnvironment(unittest.TestCase):
    def test_default_process_environment_drops_hostile_git_and_loader_state(self):
        hostile = {
            "GIT_DIR": "/hostile/git-dir",
            "GIT_INDEX_FILE": "/hostile/index",
            "DYLD_LIBRARY_PATH": "/hostile/dylibs",
            "LD_LIBRARY_PATH": "/hostile/libs",
        }
        with mock.patch.dict(os.environ, hostile, clear=False):
            result = gate.run_capture(("/usr/bin/env",), cwd=Path("/"))
        self.assertEqual(result.returncode, 0)
        rendered = result.stdout.decode("utf-8")
        for name, value in hostile.items():
            self.assertNotIn(f"{name}={value}", rendered)
        self.assertIn("GIT_CONFIG_GLOBAL=/dev/null", rendered)
        self.assertIn("GIT_CONFIG_NOSYSTEM=1", rendered)


class Stage1Inventory(unittest.TestCase):
    def fixture(self, root: Path) -> tuple[Path, Path]:
        stage1 = root / "build" / "host" / "stage1"
        trustc = stage1 / "bin" / "trustc"
        driver = stage1 / "lib" / "librustc_driver-abcd.so"
        trustc.parent.mkdir(parents=True)
        driver.parent.mkdir(parents=True)
        trustc.write_bytes(b"launcher\0librustc_driver-abcd.so\0")
        trustc.chmod(0o755)
        driver.write_bytes(b"driver-v1")
        return trustc, driver

    def test_complete_inventory_binds_driver_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            trustc, driver = self.fixture(root)
            before = gate.stage1_inventory(root, trustc)
            self.assertEqual(before["driver_path"], str(driver.relative_to(root)))
            driver.write_bytes(b"driver-v2")
            after = gate.stage1_inventory(root, trustc)
            self.assertNotEqual(before["inventory_sha256"], after["inventory_sha256"])

    def test_missing_or_extra_driver_refuses(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            trustc, driver = self.fixture(root)
            driver.unlink()
            with self.assertRaisesRegex(gate.GateError, "exactly the rustc_driver"):
                gate.stage1_inventory(root, trustc)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            trustc, _driver = self.fixture(root)
            (trustc.parent.parent / "lib" / "librustc_driver-ffff.so").write_bytes(b"stale")
            with self.assertRaisesRegex(gate.GateError, "exactly the rustc_driver"):
                gate.stage1_inventory(root, trustc)

    @unittest.skipUnless(hasattr(os, "symlink"), "symlink escape refusal")
    def test_stage1_symlink_escape_refuses(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = base / "root"
            root.mkdir()
            trustc, _driver = self.fixture(root)
            outside = base / "outside"
            outside.write_bytes(b"not repository evidence")
            (trustc.parent.parent / "escape").symlink_to(outside)
            with self.assertRaisesRegex(gate.GateError, "resolve inside the repository"):
                gate.stage1_inventory(root, trustc)


class ReviewedCorpusRatchet(unittest.TestCase):
    """`corpus_inventory` had no test at all, which is why it asserted a false number.

    It pinned 27 probes, ended in a literal `!= 27`, and compared its pin table
    for set EQUALITY against a directory that had grown to 45 — so wiring it into
    any runner would have produced a red on a correct tree. These are the three
    behaviours that decide whether the ratchet is worth having.
    """

    REAL_ROOT = Path(__file__).resolve().parents[2]

    def test_reviewed_union_ratchets_clean_on_the_real_tree(self):
        # The whole point: on a correct tree this must PASS, not raise. It is the
        # check that a directory-equality contract got wrong.
        inventory = gate.corpus_inventory(self.REAL_ROOT)
        self.assertEqual(len(inventory), len(gate.EXPECTED_CORPUS_SHA256))
        self.assertEqual(
            sorted(row["path"] for row in inventory),
            sorted(gate.EXPECTED_CORPUS_SHA256),
        )

    def test_probes_outside_the_reviewed_union_are_reported_not_asserted(self):
        # An unrelated wave's probe must be VISIBLE and must not be fatal.
        unpinned = gate.unpinned_probes(self.REAL_ROOT)
        self.assertNotIn(
            set(unpinned) & set(gate.EXPECTED_CORPUS_SHA256),
            [set(gate.EXPECTED_CORPUS_SHA256)],
        )
        for path in unpinned:
            self.assertNotIn(path, gate.EXPECTED_CORPUS_SHA256)

    def test_a_pinned_probe_that_stops_being_tracked_refuses(self):
        missing = sorted(gate.EXPECTED_CORPUS_SHA256)[0]
        tracked = [p for p in sorted(gate.EXPECTED_CORPUS_SHA256) if p != missing]
        with mock.patch.object(gate, "git", return_value="\n".join(tracked)):
            with self.assertRaisesRegex(gate.GateError, "lost tracked files"):
                gate.corpus_inventory(self.REAL_ROOT)

    def test_a_pinned_probe_whose_bytes_move_refuses(self):
        victim = sorted(gate.EXPECTED_CORPUS_SHA256)[0]
        drifted = dict(gate.EXPECTED_CORPUS_SHA256)
        drifted[victim] = "0" * 64
        with mock.patch.object(gate, "EXPECTED_CORPUS_SHA256", drifted):
            with self.assertRaisesRegex(gate.GateError, "bytes drifted"):
                gate.corpus_inventory(self.REAL_ROOT)

    def test_the_size_check_is_stated_against_the_pin_table_not_a_literal(self):
        # A literal restates the constant beside it and drifts on re-pin. Removing
        # one entry must move the refusal too, which a hard-coded 27 would not do.
        trimmed = dict(gate.EXPECTED_CORPUS_SHA256)
        trimmed.pop(sorted(trimmed)[0])
        with mock.patch.object(gate, "EXPECTED_CORPUS_SHA256", trimmed):
            inventory = gate.corpus_inventory(self.REAL_ROOT)
        self.assertEqual(len(inventory), len(trimmed))


if __name__ == "__main__":
    unittest.main()
