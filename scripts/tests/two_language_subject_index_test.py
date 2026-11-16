#!/usr/bin/env python3
"""Controls for scripts/two_language_subject_index.py, the G3 subject-index producer.

The round trip feeds the producer the G3 checker's own fixture inputs, lets the
checker judge what it wrote, and requires the measurable joins to pass while
every authority conjunct keeps its standing refusal.  Mutations of the produced
join must be refused by the checker; malformed inputs must be refused by the
producer; every printed-path pairing must be disclosed; output is deterministic.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

TESTS = Path(__file__).resolve().parent
ROOT = TESTS.parents[1]
PRODUCER = ROOT / "scripts/two_language_subject_index.py"
sys.path.insert(0, str(TESTS))

from completion_gates_g3_test import REV, RUN, GateRoot  # noqa: E402
from trust_ir_producer_census_test import census_v2, mutate_census  # noqa: E402
from trust_ir_producer_scorecard_completion_test import compiler_census  # noqa: E402

OUT = "produced"
# The G3 fixture's admitted Rust file is `fn f() {}\n`; its fixture compile
# names that file `/fixture/src/lib.rs`.
ADMITTED_RUST_SHA = hashlib.sha256(b"fn f() {}\n").hexdigest()
ROOT_INPUT = "/fixture/src/lib.rs"


def load_producer():
    spec = importlib.util.spec_from_file_location("two_language_subject_index_under_test", PRODUCER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


PRODUCER_MODULE = load_producer()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class Fixture:
    """The G3 checker's fixture, with the producer's outputs swapped in."""

    def __init__(self) -> None:
        self.g = GateRoot()

    def close(self) -> None:
        self.g.close()

    def produce(self, out: str = OUT, *extra: str) -> tuple[int, str, str]:
        process = subprocess.run(
            [sys.executable, "-B", str(PRODUCER), "--root", str(self.g.root),
             "--corpus-manifest", "corpus.json",
             "--rust-scorecard", self.g.refs["rust_scorecard"]["path"],
             "--lean-body-census", self.g.refs["lean_body_census"]["path"],
             "--acceptance-run-id", RUN, "--source-revision", REV, "--out-dir", out, *extra],
            capture_output=True, text=True, timeout=120, check=False)
        return process.returncode, process.stdout, process.stderr

    def read(self, name: str, out: str = OUT) -> dict:
        return json.loads((self.g.root / out / name).read_text())

    def adopt(self, out: str = OUT) -> None:
        """Bind the produced subject index, join and module as the checker's inputs."""
        subject = self.g.root / out / "subject-index.json"
        self.g.subject = json.loads(subject.read_text())
        self.g.write("subject.json", subject.read_bytes())
        join = self.g.root / out / "body-join.json"
        self.g.docs["body_join"] = json.loads(join.read_text())
        self.g.refs["body_join"] = {"path": f"{out}/body-join.json", "sha256": digest(join.read_bytes())}
        [module] = self.g.subject["programs"][0]["modules"]
        self.g.module_ref = module["artifact"]

    def check(self) -> tuple[dict[str, bool], str]:
        rc, verdict, stderr = self.g.run()
        assert rc == 1 and not verdict["passed"], stderr
        return {row["id"]: row["passed"] for row in verdict["checks"]}, stderr

    def set_rust_census(self, census_raw: str, printed: str, exit_code: object = 0) -> None:
        """Give the Rust fixture file a retained control census whose one body
        is `printed`, from a control compile that exited `exit_code`."""
        corpus = self.g.docs["rust_scorecard"]["corpora"]["full"]
        corpus["body_census"]["bodies"][0]["def"] = printed
        corpus["files"][0]["bodies"][0]["def"] = printed
        corpus["files"][0]["measurement"] = {"control": {
            "input": "/fixture/src/lib.rs", "exit_code": exit_code, "census_raw": census_raw}}
        self.g.artifact("rust_scorecard", self.g.docs["rust_scorecard"])


def v1_census(printed_stem: str = "crate::f") -> str:
    """A v1 control census whose body is `crate[1a2b]::f` (crate-disambiguated)."""
    raw = compiler_census("/fixture/src/lib.rs", [{"def": printed_stem, "kind": "named"}], "1" * 64, False)
    v2 = census_v2(raw)
    records = [json.loads(line) for line in v2.splitlines()]
    for record in records:
        record["schema"] = "trust.rust.hir-body-census.v1"
    for body in records[1]["bodies"]:
        for key in ("crate_name", "def_path_no_crate", "source"):
            body.pop(key)
    lines = [json.dumps(record) + "\n" for record in records]
    records[2]["snapshot_sha256"] = digest(lines[1].encode())
    lines[2] = json.dumps(records[2]) + "\n"
    return "".join(lines)


def v2_census(owning: str = ROOT_INPUT, owning_sha: str = ADMITTED_RUST_SHA,
              root_sha: str = ADMITTED_RUST_SHA) -> str:
    """A v2 control census of the admitted root input (digest `root_sha`) whose
    one body `crate[1a2b]::f` is owned by `owning` with digest `owning_sha`.
    A non-root owner is added to the compile's own loaded-source lists."""
    raw = census_v2(compiler_census(ROOT_INPUT, [{"def": "crate::f", "kind": "named"}], root_sha, False),
                    source={"file": owning, "sha256": owning_sha, "lo": [1, 0], "hi": [1, 9]})
    if owning == ROOT_INPUT:
        return raw

    def add_source(records):
        for record in (records[1], records[2]):
            record["sources"] = sorted(record["sources"] + [{"file": owning, "sha256": owning_sha}],
                                       key=lambda row: row["file"])
    return mutate_census(raw, add_source)


def with_disambiguator(raw: str, old: str, new: str) -> str:
    """The same census as another compiler would print it: only the crate
    disambiguator differs (the 4b2c observation)."""
    records = [json.loads(line) for line in raw.splitlines()]
    for body in records[1]["bodies"]:
        body["def"] = body["def"].replace(f"[{old}]", f"[{new}]")
    lines = [json.dumps(record) + "\n" for record in records]
    records[2]["snapshot_sha256"] = digest(lines[1].encode())
    lines[2] = json.dumps(records[2]) + "\n"
    return "".join(lines)


class SubjectIndexProducerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.f = Fixture()

    def tearDown(self) -> None:
        self.f.close()

    def produce_ok(self, out: str = OUT) -> dict:
        rc, stdout, stderr = self.f.produce(out)
        self.assertIn(rc, (0, 3), stderr)
        return self.f.read("pairing-report.json", out)

    def assert_standing_refusals_only(self, checks: dict[str, bool], stderr: str) -> None:
        """The joins passed: only the checker's authority refusals remain."""
        self.assertTrue(checks["admitted_file_manifest_exact"], stderr)
        for check in ("reachable_body_census_exact", "no_denominator_exclusions",
                      "subject_index_roots_match", "all_joined_modules_valid",
                      "rust_zero_producer_residue", "lean_zero_producer_residue"):
            self.assertFalse(checks[check], check)
        # Each authority refusal is reached only AFTER joined()/subject() pass.
        self.assertIn("reachable_body_census_exact: subject function/body digests are authored labels", stderr)
        self.assertIn("no_denominator_exclusions: mixed admitted sources", stderr)
        self.assertIn("subject_index_roots_match: only admitted_files, reachable_bodies, and modules", stderr)
        for join_failure in ("bijection", "wrong-module", "root differs", "partition", "subject index"):
            self.assertNotIn(join_failure, stderr)

    # -- round trip ----------------------------------------------------------

    def test_round_trip_through_the_checker(self) -> None:
        report = self.produce_ok()
        self.assertEqual(report["bodies"], 2)
        self.f.adopt()
        self.assert_standing_refusals_only(*self.f.check())

    def test_hand_authored_fixture_and_produced_index_reach_the_same_verdicts(self) -> None:
        # Control: the checker's hand-built subject index gives the same pattern.
        hand = self.f.check()[0]
        self.produce_ok()
        self.f.adopt()
        self.assertEqual(self.f.check()[0], hand)

    # -- checker refusals of mutated producer output -------------------------

    def mutate_join(self, change) -> tuple[dict[str, bool], str]:
        self.produce_ok()
        self.f.adopt()
        join = copy.deepcopy(self.f.g.docs["body_join"])
        change(join["rows"])
        self.f.g.artifact("body_join", join)
        return self.f.check()

    def test_duplicate_body_is_refused(self) -> None:
        checks, stderr = self.mutate_join(lambda rows: rows.append(copy.deepcopy(rows[0])))
        self.assertFalse(checks["no_denominator_exclusions"])
        self.assertIn("unknown/duplicate/wrong-module body", stderr)

    def test_dropped_body_is_refused(self) -> None:
        checks, stderr = self.mutate_join(lambda rows: rows.pop())
        self.assertFalse(checks["reachable_body_census_exact"])
        self.assertIn("not an exact duplicate-free bijection", stderr)
        self.assertNotIn("reachable_body_census_exact: subject function/body digests", stderr)

    def test_wrong_module_is_refused(self) -> None:
        def change(rows):
            rows[0]["module_id"] = "program.other"
        checks, stderr = self.mutate_join(change)
        self.assertFalse(checks["subject_index_roots_match"])
        self.assertIn("unknown/duplicate/wrong-module body", stderr)

    def test_produced_root_is_recomputed_not_trusted(self) -> None:
        self.produce_ok()
        self.f.adopt()
        self.f.g.subject["programs"][0]["bodies"][0]["function_identity_sha256"] = "3" * 64
        self.f.g.write("subject.json", self.f.g.subject)
        checks, stderr = self.f.check()
        self.assertFalse(checks["admitted_file_manifest_exact"])
        self.assertIn("reachable_bodies root differs from recomputed rows", stderr)

    # -- producer input refusals -----------------------------------------------

    def assert_producer_refuses(self, needle: str) -> None:
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 2, stderr)
        self.assertIn(needle, stderr)
        self.assertFalse((self.f.g.root / OUT).exists())

    def test_duplicate_rust_census_body_refused_by_producer(self) -> None:
        corpus = self.f.g.docs["rust_scorecard"]["corpora"]["full"]
        corpus["body_census"]["bodies"].append(copy.deepcopy(corpus["body_census"]["bodies"][0]))
        self.f.g.artifact("rust_scorecard", self.f.g.docs["rust_scorecard"])
        self.assert_producer_refuses("duplicate Rust body census row")

    def test_duplicate_lean_census_declaration_refused_by_producer(self) -> None:
        census = self.f.g.docs["lean_body_census"]
        census["declarations"].append(copy.deepcopy(census["declarations"][0]))
        self.f.g.artifact("lean_body_census", census)
        self.assert_producer_refuses("duplicate Lean body census declaration")

    def test_two_bodies_with_one_identity_refused_by_producer(self) -> None:
        # Two printed defs that differ ONLY by crate disambiguator strip to one
        # printed path in one file: one identity, never two silently merged rows.
        corpus = self.f.g.docs["rust_scorecard"]["corpora"]["full"]
        corpus["body_census"]["bodies"] = [
            {"file": "inputs/r.rs", "def": "crate[1a2b]::f", "kind": "named"},
            {"file": "inputs/r.rs", "def": "crate[9f9f]::f", "kind": "named"}]
        self.f.g.artifact("rust_scorecard", self.f.g.docs["rust_scorecard"])
        self.assert_producer_refuses("two bodies share one identity")

    def test_existing_output_is_never_overwritten(self) -> None:
        self.produce_ok()
        before = (self.f.g.root / OUT / "subject-index.json").read_bytes()
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 2, stderr)
        self.assertIn("--out-dir already exists", stderr)
        self.assertEqual((self.f.g.root / OUT / "subject-index.json").read_bytes(), before)

    def test_safe_program_ids_stay_in_the_output_directory(self) -> None:
        for number, program_id in enumerate(("program", "Clean_85-prod", "0")):
            with self.subTest(program_id=program_id):
                out = f"safe-{number}"
                rc, _, stderr = self.f.produce(out, "--program-id", program_id)
                self.assertEqual(rc, 3, stderr)  # Fixture lacks a measured Rust census.
                paths = {str(path.relative_to(self.f.g.root / out))
                         for path in (self.f.g.root / out).rglob("*") if path.is_file()}
                self.assertEqual(paths, {"subject-index.json", "body-join.json", "pairing-report.json",
                                         f"modules/{program_id}.unretained-module.json"})
                module = self.f.read(f"modules/{program_id}.unretained-module.json", out)
                self.assertEqual(module["program_id"], program_id)
                self.assertEqual(module["trust_ir"], "unretained")
                report = self.f.read("pairing-report.json", out)
                self.assertTrue(report["authority"].startswith("none:"))
                self.assertEqual(report["unmeasured"]["body_digest_sentinels"],
                                 {field: PRODUCER_MODULE.sentinel(field)
                                  for field in PRODUCER_MODULE.BODY_DIGESTS})

    def test_unsafe_program_ids_refuse_before_any_output_write(self) -> None:
        before = {str(path.relative_to(self.f.g.root)): path.read_bytes() if path.is_file() else None
                  for path in self.f.g.root.rglob("*")}
        for program_id in ("", ".", "..", "../../../escape", "a/b", "a\\b", "/absolute",
                           "C:\\absolute", "a.b", "-program", " program", "program\n", "é"):
            with self.subTest(program_id=program_id):
                rc, stdout, stderr = self.f.produce(OUT, f"--program-id={program_id}")
                self.assertEqual(rc, 2, stderr)
                self.assertEqual(stdout, "")
                self.assertIn("--program-id must be one ASCII filename component", stderr)
                self.assertFalse((self.f.g.root / OUT).exists())
                after = {str(path.relative_to(self.f.g.root)): path.read_bytes() if path.is_file() else None
                         for path in self.f.g.root.rglob("*")}
                self.assertEqual(after, before)

    # -- pairing disclosure --------------------------------------------------

    def test_printed_path_pairing_is_disclosed_per_row(self) -> None:
        report = self.produce_ok()
        self.assertEqual(report["paired_by"], {"stable-identity": 0, "stable-identity-from-failed-compile": 0,
                                               "kernel-identity": 0, "kernel-identity-from-failed-compile": 0,
                                               "printed-path": 2})
        for row in report["rows"]:
            self.assertEqual(row["paired_by"], "printed-path")
            self.assertTrue(row["reason"])
            self.assertEqual(row["process_status"], "unmeasured")
            self.assertTrue(row["body_id"].startswith(f"{row['language']}/printed-path/"))
        self.assertEqual(report["reconciliation_error_counts"], {"rust.compiler-census-absent": 1})

    def test_v1_census_pairs_by_printed_path_with_its_reason(self) -> None:
        self.f.set_rust_census(v1_census(), "crate[1a2b]::f")
        report = self.produce_ok()
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual(rust["paired_by"], "printed-path")
        self.assertIn("hir-body-census.v1: no crate-independent identity", rust["reason"])
        self.assertEqual(rust["identity"]["printed_path"], "crate::f")
        self.assertEqual(report["reconciliation_error_counts"], {})

    def test_v2_census_pairs_by_stable_identity(self) -> None:
        self.f.set_rust_census(v2_census(), "crate[1a2b]::f")
        report = self.produce_ok()
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual(rust["paired_by"], "stable-identity", rust)
        self.assertIsNone(rust["reason"])
        self.assertEqual(rust["process_status"], "success")
        self.assertEqual(rust["owning_source_checks"], {"census_sources": "match", "admitted_root_input": "match"})
        self.assertEqual(rust["identity"], {"language": "rust", "basis": "stable-identity", "crate_name": "crate",
                                            "def_path_no_crate": "::f", "owning_source_sha256": ADMITTED_RUST_SHA})
        self.assertEqual(report["reconciliation_error_counts"], {})
        # And the checker still accepts the joins built on it.
        self.f.adopt()
        self.assert_standing_refusals_only(*self.f.check())

    def test_v2_owning_digest_absent_from_the_compiles_own_sources_is_demoted(self) -> None:
        # The row claims a digest for its owning file that the same compile's
        # loaded-source footer does not list: never stable-identity.
        raw = census_v2(compiler_census(ROOT_INPUT, [{"def": "crate::f", "kind": "named"}],
                                        ADMITTED_RUST_SHA, False),
                        source={"file": ROOT_INPUT, "sha256": "2" * 64, "lo": [1, 0], "hi": [1, 9]})
        self.f.set_rust_census(raw, "crate[1a2b]::f")
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 3, stderr)
        report = self.f.read("pairing-report.json")
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual(rust["paired_by"], "printed-path")
        self.assertIn("not the digest this compile lists", rust["reason"])
        self.assertEqual(report["reconciliation_errors"], {
            "rust.owning-source-not-in-census-sources": ["inputs/r.rs crate[1a2b]::f"]})

    def test_v2_root_input_owner_must_carry_the_admitted_digest(self) -> None:
        # The compile is self-consistent (row and footer agree) but it compiled
        # bytes other than the admitted file's: never stable-identity.
        self.f.set_rust_census(v2_census(owning_sha="1" * 64, root_sha="1" * 64), "crate[1a2b]::f")
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 3, stderr)
        report = self.f.read("pairing-report.json")
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual(rust["paired_by"], "printed-path")
        self.assertIn("root-input digest is not the admitted file's", rust["reason"])
        self.assertEqual(report["reconciliation_errors"], {
            "rust.compile-root-input-differs-from-admitted": ["inputs/r.rs crate[1a2b]::f"]})

    def test_v2_non_root_owner_of_a_compile_that_built_other_root_bytes_is_demoted(self) -> None:
        # The body is owned by a module file the compile lists consistently,
        # but the compile's own root input is not the admitted bytes.
        self.f.set_rust_census(v2_census(owning="/fixture/src/m.rs", owning_sha="4" * 64, root_sha="1" * 64),
                               "crate[1a2b]::f")
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 3, stderr)
        report = self.f.read("pairing-report.json")
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual(rust["paired_by"], "printed-path")
        self.assertEqual(rust["owning_source_checks"], {"census_sources": "match", "admitted_root_input": "mismatch"})
        self.assertEqual(report["reconciliation_errors"], {
            "rust.compile-root-input-differs-from-admitted": ["inputs/r.rs crate[1a2b]::f"]})

    def test_v2_non_root_owner_is_checked_against_census_sources_and_the_root_input(self) -> None:
        # Control twin: the same module-file owner, from a compile whose root
        # input IS the admitted bytes, is stable-identity.
        self.f.set_rust_census(v2_census(owning="/fixture/src/m.rs", owning_sha="4" * 64), "crate[1a2b]::f")
        report = self.produce_ok()
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual(rust["paired_by"], "stable-identity", rust)
        self.assertEqual(rust["owning_source_checks"], {"census_sources": "match", "admitted_root_input": "match"})
        self.assertEqual(report["reconciliation_error_counts"], {})

    def failed_compile_census(self) -> str:
        # A tracked (include_str!) input makes the scorecard's census status
        # `input_closure_incomplete`, which REPLACES `compiler_failed`.
        return mutate_census(v2_census(), lambda records: records[2]["other_inputs"]["tracked_files"].append(
            "/fixture/x.txt"))

    def test_rust_rows_from_a_failed_control_compile_are_never_stable_identity(self) -> None:
        self.f.set_rust_census(self.failed_compile_census(), "crate[1a2b]::f", exit_code=1)
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 3, stderr)
        report = self.f.read("pairing-report.json")
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual((rust["paired_by"], rust["process_status"]),
                         ("stable-identity-from-failed-compile", "failed"))
        self.assertEqual(rust["reason"], "control compile process is failed")
        self.assertEqual(report["by_language"]["rust"]["stable-identity"], 0)
        self.assertEqual(report["by_language"]["rust"]["stable-identity-from-failed-compile"], 1)
        self.assertEqual(report["reconciliation_errors"], {
            "rust.compiler-census-compile-failed": ["inputs/r.rs: exit 1"]})

    def test_rust_rows_from_a_successful_compile_with_tracked_inputs_stay_stable_identity(self) -> None:
        # Negative twin: the SAME census at exit 0.
        self.f.set_rust_census(self.failed_compile_census(), "crate[1a2b]::f", exit_code=0)
        report = self.produce_ok()
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual((rust["paired_by"], rust["process_status"]), ("stable-identity", "success"))
        self.assertEqual(report["reconciliation_error_counts"], {})

    def test_rust_rows_from_a_compile_with_no_exit_status_are_printed_path(self) -> None:
        self.f.set_rust_census(self.failed_compile_census(), "crate[1a2b]::f", exit_code=None)
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 3, stderr)
        report = self.f.read("pairing-report.json")
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual((rust["paired_by"], rust["process_status"]), ("printed-path", "unmeasured"))
        self.assertEqual(rust["reason"], "control compile exit status is unmeasured")
        self.assertEqual(report["reconciliation_errors"], {
            "rust.compiler-census-exit-unmeasured": ["inputs/r.rs: exit None"]})

    def test_v2_row_with_unmeasured_source_falls_back_and_says_so(self) -> None:
        empty = {"file": None, "sha256": None, "lo": None, "hi": None}
        self.f.set_rust_census(census_v2(compiler_census(
            ROOT_INPUT, [{"def": "crate::f", "kind": "named"}], ADMITTED_RUST_SHA, False), source=empty),
            "crate[1a2b]::f")
        [rust] = [row for row in self.produce_ok()["rows"] if row["language"] == "rust"]
        self.assertEqual(rust["paired_by"], "printed-path")
        self.assertIn("owning source as unmeasured", rust["reason"])

    def test_census_row_missing_for_a_listed_body_is_a_reconciliation_error(self) -> None:
        self.f.set_rust_census(v1_census("crate::g"), "crate[1a2b]::f")
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 3, stderr)
        report = self.f.read("pairing-report.json")
        self.assertEqual(report["reconciliation_error_counts"], {
            "rust.body-census-row-without-compiler-row": 1, "rust.compiler-census-row-unlisted": 1})

    def test_census_rows_of_a_file_with_no_listed_body_are_still_reconciled(self) -> None:
        # Negative twin of the zero-body file: its census names a body the
        # body census omits, which is an omission, never a measured zero.
        self.f.set_rust_census(v1_census(), "crate[1a2b]::f")
        corpus = self.f.g.docs["rust_scorecard"]["corpora"]["full"]
        corpus["body_census"]["bodies"] = []
        self.f.g.artifact("rust_scorecard", self.f.g.docs["rust_scorecard"])
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 3, stderr)
        self.assertEqual(self.f.read("pairing-report.json")["reconciliation_errors"],
                         {"rust.compiler-census-row-unlisted": ["inputs/r.rs crate[1a2b]::f"]})

    # A REAL compiler transcript: `trustc 1.99.0-dev (321aaeda7 2026-09-17)
    # -Ztrust-lean-census` of tests/ui/trust/clean_origin_wrapping_binop.rs (a
    # run-pass test: the compile exited 0), whose kernel roster registers wsum,
    # wdec and bsum.  Its one machine path, the capture checkout, is rewritten
    # to the placeholder `/<repo>/` (the parser requires an absolute label) and
    # the record chain re-hashed over the rewritten bytes; nothing else moved.
    ISLAND = ROOT / "scripts/tests/fixtures/lean-island-census/clean_origin_wrapping_binop.321aaeda7.jsonl"
    # SHA-256 of tests/ui/trust/clean_origin_wrapping_binop.rs as captured
    # (equal to the transcript's own source-map checksum for its root input,
    # and to that file's bytes in the capture tree).
    ISLAND_SOURCE_SHA = "112299236c5733d0cdff9d46d05c3f20e2bacbfd9ad1c55d2122b185de9e05be"

    def admit_lean_sha(self, sha: str) -> None:
        corpus = self.f.g.corpus
        corpus["lean"]["entries"][0]["source"]["sha256"] = sha
        self.f.g.write("corpus.json", corpus)

    def lean_with_island(self, names: list[str], exit_code: str = "0", island: bytes | None = None,
                         proof_only: tuple[str, ...] = (), admitted_sha: str | None = None) -> tuple[int, dict]:
        self.admit_lean_sha(self.ISLAND_SOURCE_SHA if admitted_sha is None else admitted_sha)
        census = self.f.g.docs["lean_body_census"]
        census["declarations"] = [{"file": "inputs/l.lean", "name": name, "kind": "computational"}
                                  for name in names] + [
            {"file": "inputs/l.lean", "name": name, "kind": "proof-only"} for name in proof_only]
        self.f.g.artifact("lean_body_census", census)
        self.f.g.write("evidence/island.jsonl", self.ISLAND.read_bytes() if island is None else island)
        rc, _, stderr = self.f.produce(OUT, "--lean-island-census",
                                       f"inputs/l.lean=evidence/island.jsonl:{exit_code}")
        self.assertIn(rc, (0, 3), stderr)
        return rc, self.f.read("pairing-report.json")

    def test_committed_island_fixture_carries_no_machine_path(self) -> None:
        # scripts/tests/fixtures is outside fast.fixture-span-paths' roots, so
        # this is where its unwaivable rule A is applied to this capture.
        spec = importlib.util.spec_from_file_location(
            "check_fixture_span_paths_for_subject_index", ROOT / "scripts/check_fixture_span_paths.py")
        assert spec is not None and spec.loader is not None
        guard = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(guard)
        text = self.ISLAND.read_text(encoding="utf-8")
        leaks = [what for pattern, what in guard.LEAK_PATTERNS if pattern.search(text)]
        self.assertEqual(leaks, [])

    def test_lean_bodies_pair_by_kernel_identity_from_a_real_island_census(self) -> None:
        rc, report = self.lean_with_island(["bsum", "wdec", "wsum"])
        lean = {row["source_body"]: row for row in report["rows"] if row["language"] == "lean"}
        self.assertEqual({name: row["paired_by"] for name, row in lean.items()},
                         {"bsum": "kernel-identity", "wdec": "kernel-identity", "wsum": "kernel-identity"})
        self.assertEqual(lean["bsum"]["identity"]["kernel_payload_sha256"],
                         "9317b5a852db04e13adb857693ed8532a0bf54fa29998e8192c5c48c985fe738")
        self.assertEqual({row["process_status"] for row in lean.values()}, {"success"})
        self.assertEqual({json.dumps(row["owning_source_checks"]) for row in lean.values()},
                         {json.dumps({"island_input_source": "match"})})
        self.assertEqual(report["reconciliation_error_counts"], {"rust.compiler-census-absent": 1})

    def test_the_island_footer_digest_is_the_captured_source(self) -> None:
        footer = json.loads(self.ISLAND.read_bytes().splitlines()[-1])
        self.assertEqual([source["source_map_checksum_sha256"] for source in footer["loaded_sources"]],
                         [self.ISLAND_SOURCE_SHA])

    def test_kernel_rows_of_an_island_compiled_from_other_bytes_are_never_kernel_identity(self) -> None:
        # Negative twin: the SAME transcript against an admitted Lean file whose
        # digest is not the one the compile lists for its own root input.
        rc, report = self.lean_with_island(["bsum", "wdec", "wsum"], admitted_sha=digest(b"def f := 1\n"))
        self.assertEqual(rc, 3)
        lean = [row for row in report["rows"] if row["language"] == "lean"]
        self.assertEqual({row["paired_by"] for row in lean}, {"printed-path"})
        self.assertEqual({row["reason"] for row in lean},
                         {"the island compile's root-input checksum is not the admitted file's"})
        self.assertEqual({json.dumps(row["owning_source_checks"]) for row in lean},
                         {json.dumps({"island_input_source": "mismatch"})})
        self.assertEqual(report["reconciliation_errors"], {
            "lean.island-input-differs-from-admitted": [
                "inputs/l.lean: /<repo>/tests/ui/trust/clean_origin_wrapping_binop.rs"],
            "rust.compiler-census-absent": ["inputs/r.rs"]})

    def test_kernel_rows_from_a_failed_compile_are_never_kernel_identity(self) -> None:
        # Negative twin: the SAME transcript, reported with a non-zero exit.
        rc, report = self.lean_with_island(["bsum", "wdec", "wsum"], exit_code="1")
        self.assertEqual(rc, 3)
        lean = [row for row in report["rows"] if row["language"] == "lean"]
        self.assertEqual({row["paired_by"] for row in lean}, {"kernel-identity-from-failed-compile"})
        self.assertEqual({row["process_status"] for row in lean}, {"failed"})
        self.assertTrue(all("process is failed" in row["reason"] for row in lean))
        self.assertEqual(report["by_language"]["lean"]["kernel-identity"], 0)
        self.assertEqual(report["by_language"]["lean"]["kernel-identity-from-failed-compile"], 3)
        self.assertEqual(report["reconciliation_errors"]["lean.island-census-compile-failed"],
                         ["inputs/l.lean: exit 1"])

    def test_island_census_without_an_exit_status_is_refused(self) -> None:
        self.f.g.write("evidence/island.jsonl", self.ISLAND.read_bytes())
        for spec in ("inputs/l.lean=evidence/island.jsonl", "inputs/l.lean=evidence/island.jsonl:",
                     "inputs/l.lean=evidence/island.jsonl:ok"):
            rc, _, stderr = self.f.produce(OUT, "--lean-island-census", spec)
            self.assertEqual(rc, 2, spec)
            self.assertIn("FILE=CENSUS:EXIT", stderr)
            self.assertFalse((self.f.g.root / OUT).exists())

    def test_proof_only_declarations_are_not_indexed(self) -> None:
        # `bsum` is listed proof-only: it is neither a body nor unlisted.
        rc, report = self.lean_with_island(["wdec", "wsum"], proof_only=("bsum",))
        lean = {row["source_body"] for row in report["rows"] if row["language"] == "lean"}
        self.assertEqual(lean, {"wdec", "wsum"})
        self.assertEqual(report["reconciliation_error_counts"], {"rust.compiler-census-absent": 1})

    def test_unusable_island_census_is_a_reconciliation_error(self) -> None:
        # The real transcript without its completion footer.
        truncated = b"".join(self.ISLAND.read_bytes().splitlines(keepends=True)[:-1])
        rc, report = self.lean_with_island(["wsum"], island=truncated)
        self.assertEqual(rc, 3)
        [row] = [row for row in report["rows"] if row["language"] == "lean"]
        self.assertEqual((row["paired_by"], row["reason"]),
                         ("printed-path", "no usable Lean island census supplied for this file"))
        self.assertEqual(report["reconciliation_errors"], {
            "lean.island-census-unusable": ["inputs/l.lean: incomplete"],
            "rust.compiler-census-absent": ["inputs/r.rs"]})

    def test_lean_census_and_kernel_roster_disagreements_are_reconciliation_errors(self) -> None:
        # Negative twin: one roster computational body is unlisted, and one
        # listed name has no roster row (so it falls back to printed-path).
        rc, report = self.lean_with_island(["wsum", "notInRoster"])
        self.assertEqual(rc, 3)
        lean = {row["source_body"]: row["paired_by"] for row in report["rows"] if row["language"] == "lean"}
        self.assertEqual(lean, {"wsum": "kernel-identity", "notInRoster": "printed-path"})
        self.assertEqual(report["reconciliation_errors"], {
            "lean.census-declaration-without-kernel-row": ["inputs/l.lean notInRoster"],
            "lean.kernel-computational-unlisted": ["inputs/l.lean bsum", "inputs/l.lean wdec"],
            "rust.compiler-census-absent": ["inputs/r.rs"]})

    def test_island_census_for_an_unadmitted_file_is_refused(self) -> None:
        self.f.g.write("evidence/island.jsonl", self.ISLAND.read_bytes())
        rc, _, stderr = self.f.produce(OUT, "--lean-island-census", "inputs/r.rs=evidence/island.jsonl:0")
        self.assertEqual(rc, 2, stderr)
        self.assertIn("unadmitted Lean file", stderr)

    def test_admitted_file_the_scorecard_never_measured_is_a_reconciliation_error(self) -> None:
        corpus = self.f.g.corpus
        corpus["rust"]["entries"].append({
            "id": "r2", "kind": "program", "admitted": True, "expected_outcome": "ok",
            "source": {"path": "inputs/r2.rs", "sha256": "5" * 64}})
        self.f.g.write("corpus.json", corpus)
        rc, _, stderr = self.f.produce()
        self.assertEqual(rc, 3, stderr)
        report = self.f.read("pairing-report.json")
        self.assertEqual(report["reconciliation_errors"], {
            "admission.admitted-file-unmeasured": ["rust r2 inputs/r2.rs"],
            "rust.compiler-census-absent": ["inputs/r.rs"]})

    # -- identity across compilers -----------------------------------------------

    def identity_for(self, census_raw: str, printed: str, out: str) -> str:
        self.f.set_rust_census(census_raw, printed)
        report = self.produce_ok(out)
        [rust] = [row for row in report["rows"] if row["language"] == "rust"]
        self.assertEqual(rust["paired_by"], "stable-identity", rust)
        return rust["body_id"]

    def test_stable_identity_survives_a_crate_disambiguator_change(self) -> None:
        v2 = v2_census()
        first = self.identity_for(v2, "crate[1a2b]::f", "a")
        second = self.identity_for(with_disambiguator(v2, "1a2b", "9f9f"), "crate[9f9f]::f", "b")
        self.assertEqual(first, second)

    def test_stable_identity_is_bound_to_the_owning_source_content(self) -> None:
        # Negative twin: same crate-free path, different (census-listed)
        # owning source bytes.
        first = self.identity_for(v2_census(owning="/fixture/src/m.rs", owning_sha="4" * 64),
                                  "crate[1a2b]::f", "a")
        second = self.identity_for(v2_census(owning="/fixture/src/m.rs", owning_sha="6" * 64),
                                   "crate[1a2b]::f", "b")
        self.assertNotEqual(first, second)

    # -- determinism ---------------------------------------------------------------

    def test_output_is_deterministic_and_input_order_free(self) -> None:
        self.produce_ok()
        first = {path.relative_to(self.f.g.root / OUT): path.read_bytes()
                 for path in sorted((self.f.g.root / OUT).rglob("*.json"))}
        shutil.rmtree(self.f.g.root / OUT)
        census = self.f.g.docs["lean_body_census"]
        census["declarations"].append({"file": "inputs/l.lean", "name": "A.g", "kind": "computational"})
        self.f.g.artifact("lean_body_census", census)
        self.produce_ok()
        grown = {path.relative_to(self.f.g.root / OUT): path.read_bytes()
                 for path in sorted((self.f.g.root / OUT).rglob("*.json"))}
        shutil.rmtree(self.f.g.root / OUT)
        census["declarations"].reverse()
        self.f.g.artifact("lean_body_census", census)
        self.produce_ok()
        reordered = {path.relative_to(self.f.g.root / OUT): path.read_bytes()
                     for path in sorted((self.f.g.root / OUT).rglob("*.json"))}
        self.assertNotEqual(first, grown)
        # Only the input's own hash (in the report's input list) may change.
        grown_report = json.loads(grown.pop(Path("pairing-report.json")))
        reordered_report = json.loads(reordered.pop(Path("pairing-report.json")))
        self.assertEqual(grown, reordered)
        for report in (grown_report, reordered_report):
            report.pop("inputs")
        self.assertEqual(grown_report, reordered_report)

    def test_unmeasured_fields_are_sentinels_listed_in_the_report(self) -> None:
        report = self.produce_ok()
        subject = self.f.read("subject-index.json")
        sentinels = report["unmeasured"]["body_digest_sentinels"]
        for body in subject["programs"][0]["bodies"]:
            for field, value in sentinels.items():
                self.assertEqual(body[field], value)
                self.assertEqual(value, PRODUCER_MODULE.sentinel(field))
        for name, value in report["unmeasured"]["root_sentinels"].items():
            self.assertEqual(subject["roots"][name], value)
        self.assertEqual(len(report["unmeasured"]["root_sentinels"]), 8)


if __name__ == "__main__":
    unittest.main()
