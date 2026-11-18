"""Regression controls for the compiler-report certification scoreboard."""

from contextlib import redirect_stderr, redirect_stdout
from copy import deepcopy
import hashlib
import io
import json
from pathlib import Path
from subprocess import CompletedProcess
import tempfile
import unittest
from unittest.mock import patch

from scripts import trust_certified_scoreboard as scoreboard


ROOT = Path(__file__).resolve().parents[2]
LEGACY_FLOOR = ROOT / "tests/self-proof/certified-scoreboard.baseline"
CAPTURE = ROOT / "crates/trust-types/tests/fixtures/obligation-key-divergence/mir-lane-rows.jsonl"
NEGATIVE = ROOT / "tests/ui/trust/e9_requires_hypothesis_swapped_negative.stderr"
CRATE = "aterm_bidi"
SESSION = "fixture-run"


def captured_certified_row():
    original = CAPTURE.read_bytes()
    for line in original.decode().splitlines():
        function = json.loads(line.removeprefix("TRUST_JSON:"))
        for row in function["results"]:
            if row.get("proof_evidence", {}).get("strength", {}).get("assurance") == "Certified":
                return row
    raise AssertionError("original compiler capture lacks its expected Certified row")


def complete_records(crate=CRATE, session=SESSION, row=None):
    fn = crate + "::f"
    rows = [captured_certified_row() if row is None else row]
    counts = dict(proved=int(rows[0]["outcome"] == "proved"),
                  failed=int(rows[0]["outcome"] == "failed"), unknown=0, timed_out=0,
                  runtime_checked=0, skipped=0)
    summary_counts = {"total_" + name: value for name, value in counts.items()}
    records = [
        dict(type="function_result", function=fn, total=1,
             stable_ids=["a" * 16], results=rows, **counts),
        dict(type="coverage_summary", eligible=1, processed=1, function_identities={
            "schema": "trustc.coverage-function-identities.v1",
            "eligible_functions": [fn], "processed_functions": [fn],
        }, memory={"schema": "trust-memory-summary/v1", "counters": {}}),
        dict(type="crate_summary", functions_analyzed=1,
             functions_verified=counts["proved"], total_obligations=1, **summary_counts),
    ]
    return [dict(record, crate_name=crate, verification_session=session) for record in records]


def compile_result(records, code=0, stdout="", diagnostic=""):
    wire = "".join("TRUST_JSON:" + json.dumps(record) + "\n" for record in records)
    return CompletedProcess(["trustc"], code, stdout, diagnostic + wire)


class ReportTests(unittest.TestCase):
    def test_replayed_exact_negative_is_unmeasured(self):
        original = NEGATIVE.read_bytes()
        self.assertEqual(hashlib.sha256(original).hexdigest(),
                         "48765da38e3c5054323e6970ae8143b6c2bcd2f7fe74dd063e835a90803e66cd")
        result = CompletedProcess(["trustc"], 1, "", original.decode())
        with self.assertRaisesRegex(scoreboard.ScoreboardError, "compiler exited 1"):
            scoreboard.measure_report(result, CRATE, SESSION)

    def test_real_retained_proof_row_projects_into_structured_report_only(self):
        self.assertEqual(hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
                         "761aab9d9ced1f4d828856c51aa9533d2642803e1213a693d20d14df70876812")
        report = scoreboard.measure_report(compile_result(complete_records()), CRATE, SESSION)
        self.assertEqual(report["counts"]["kernel_certified"], 1)
        self.assertEqual(report["counts"]["obligations"], 1)
        self.assertEqual(report["rows"][0]["stable_id"], "a" * 16)
        self.assertEqual(report["rows"][0]["reported_assurance"], "CleanCertified")
        board = scoreboard.make_board({"aterm-bidi": report})
        self.assertEqual(board["evidence_scope"], "compiler-report-only")

    def test_nested_and_prose_certification_do_not_count(self):
        row = captured_certified_row()
        row["proof_evidence"].pop("strength")
        records = complete_records(row=row)
        marker = "note: of which 500 kernel-certified by the clean CIC kernel\n"
        report = scoreboard.measure_report(compile_result(records, diagnostic=marker), CRATE, SESSION)
        self.assertEqual(report["counts"]["proved"], 1)
        self.assertEqual(report["counts"]["kernel_certified"], 0)
        records = complete_records()
        records[0]["modeled_facts"] = ["fixture premise"]
        report = scoreboard.measure_report(compile_result(records), CRATE, SESSION)
        self.assertEqual(report["counts"]["kernel_certified"], 0)

        records = complete_records()
        records[0]["results"][0]["grade"] = {"premises": ["executor_protocol"]}
        report = scoreboard.measure_report(compile_result(records), CRATE, SESSION)
        self.assertEqual(report["counts"]["kernel_certified"], 0)
        records = complete_records()
        records[0]["results"][0]["proof_evidence"]["strength"]["assurance"] = {
            "BoundedSound": {"depth": 8},
        }
        report = scoreboard.measure_report(compile_result(records), CRATE, SESSION)
        self.assertEqual(report["counts"]["kernel_certified"], 0)

    def test_only_literal_smt_backed_assurance_counts_as_smt_backed(self):
        for assurance, expected in (("SmtBacked", 1), ("Sound", 0)):
            with self.subTest(assurance=assurance):
                records = complete_records()
                records[0]["results"][0]["proof_evidence"]["strength"]["assurance"] = assurance
                report = scoreboard.measure_report(compile_result(records), CRATE, SESSION)
                self.assertEqual(report["counts"]["smt_backed"], expected)
                self.assertEqual(report["counts"]["kernel_certified"], 0)

    def test_negative_or_incomplete_wire_refuses_even_with_favorable_rows(self):
        records = complete_records()
        other = complete_records(session="another-run")
        bad_total = deepcopy(records)
        bad_total[-1]["total_obligations"] += 1
        missing_id = deepcopy(records)
        missing_id[0].pop("stable_ids")
        withheld = deepcopy(records)
        withheld[0]["transport_budget"] = {}
        duplicated = deepcopy(records)
        duplicated[0]["results"] *= 2
        duplicated[0]["stable_ids"] *= 2
        duplicated[0].update(total=2, proved=2)
        duplicated[2].update(total_obligations=2, total_proved=2)
        wrong_status = deepcopy(records)
        wrong_status[0]["results"][0]["proof_evidence"]["status"] = "unknown"
        for result, detail in (
            (compile_result(records, 75), "compiler exited 75"),
            (compile_result(records[:-1]), "coverage_summary and crate_summary"),
            (compile_result(other), "crate/session"),
            (compile_result(bad_total), "crate summary disagrees"),
            (compile_result(missing_id), "obligation IDs"),
            (compile_result(duplicated), "obligation IDs"),
            (compile_result(withheld), "transport withheld"),
            (compile_result(wrong_status), "without matching proved outcomes"),
        ):
            with self.subTest(detail=detail), self.assertRaisesRegex(scoreboard.ScoreboardError, detail):
                scoreboard.measure_report(result, CRATE, SESSION)


class CommandTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.floor = self.root / "floor.json"
        self.command = ["--aterm", str(self.root), "--trustc", "/test-only/trustc"]
        for name in scoreboard.DEFAULT_CRATES:
            source = self.root / "crates" / name / "src/lib.rs"
            source.parent.mkdir(parents=True)
            source.write_text("pub fn f() {}\n", encoding="utf-8")

    def invoke(self, *args):
        stdout, stderr = io.StringIO(), io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            status = scoreboard.main([*self.command, *args])
        return status, stdout.getvalue(), stderr.getvalue()

    @staticmethod
    def fake_compiler(command, **_):
        return CommandTests.compiler_with_row(command)

    @staticmethod
    def compiler_with_row(command, row=None):
        crate = command[command.index("--crate-name") + 1]
        [session] = [word.split("=", 1)[1] for word in command
                     if word.startswith("-Ztrust-verify-session=")]
        assert "-Ztrust-verify-output=json" in command
        assert "--crate-type=lib" in command
        return compile_result(complete_records(crate, session, row))

    def test_positive_floor_and_real_regression_from_complete_peer_reports(self):
        with patch.object(scoreboard.subprocess, "run", side_effect=self.fake_compiler) as run:
            status, stdout, stderr = self.invoke("--out", str(self.floor))
            self.assertEqual(status, 0, stderr)
            self.assertEqual(run.call_count, len(scoreboard.DEFAULT_CRATES))
            board = json.loads(stdout)
            self.assertEqual(set(board["per_crate"]), set(scoreboard.DEFAULT_CRATES))
            self.assertEqual(board["totals"]["kernel_certified"], len(scoreboard.DEFAULT_CRATES))
            self.assertEqual(self.invoke("--baseline", str(self.floor))[0], 0)

        row = captured_certified_row()
        row.pop("proof_evidence")
        with patch.object(scoreboard.subprocess, "run",
                          side_effect=lambda cmd, **_: self.compiler_with_row(cmd, row)):
            status, _, stderr = self.invoke("--baseline", str(self.floor))
        self.assertEqual(status, 1, stderr)
        self.assertIn("REGRESSION: reported count 0", stderr)

    def test_missing_or_invalid_floors_refuse_before_compilation(self):
        self.assertEqual(hashlib.sha256(LEGACY_FLOOR.read_bytes()).hexdigest(),
                         "85f7949d3f8c69bb25c3e2a9961aaf616bb439624e72c9fec9c99142cc82ab3e")
        with patch.object(scoreboard, "run_crate") as run:
            for floor in (self.floor, LEGACY_FLOOR):
                status, stdout, stderr = self.invoke("--baseline", str(floor))
                self.assertEqual((status, stdout), (2, ""), stderr)
                self.assertIn("baseline", stderr)
            self.floor.write_text('{"schema":null,"schema":null}', encoding="utf-8")
            self.assertIn("duplicate baseline field", self.invoke("--baseline", str(self.floor))[2])
            run.assert_not_called()

    def test_incomplete_inputs_cannot_publish_or_overwrite_a_floor(self):
        with patch.object(scoreboard.subprocess, "run", side_effect=self.fake_compiler):
            self.assertEqual(self.invoke("--out", str(self.floor))[0], 0)
        original = self.floor.read_bytes()
        with patch.object(scoreboard, "run_crate") as run:
            status, _, stderr = self.invoke("--baseline", str(self.floor), "--out", str(self.floor))
            self.assertEqual(status, 2, stderr)
            self.assertEqual(self.floor.read_bytes(), original)
            (self.root / "crates/aterm-bidi/src/lib.rs").unlink()
            status, stdout, stderr = self.invoke("--baseline", str(self.floor))
            self.assertEqual((status, stdout), (2, ""), stderr)
            self.assertIn("missing aterm leaf sources", stderr)
            run.assert_not_called()

    def test_structured_floor_recomputes_all_counts_from_unique_rows(self):
        with patch.object(scoreboard.subprocess, "run", side_effect=self.fake_compiler):
            self.assertEqual(self.invoke("--out", str(self.floor))[0], 0)
        original = json.loads(self.floor.read_bytes())
        with patch.object(scoreboard, "run_crate") as run:
            contradictory = deepcopy(original)
            contradictory["totals"]["kernel_certified"] = 309
            self.floor.write_text(json.dumps(contradictory), encoding="utf-8")
            self.assertIn("counts do not match", self.invoke("--baseline", str(self.floor))[2])
            repeated = deepcopy(original)
            repeated["per_crate"]["aterm-bidi"]["rows"] *= 2
            self.floor.write_text(json.dumps(repeated), encoding="utf-8")
            self.assertIn("duplicate obligation identity", self.invoke("--baseline", str(self.floor))[2])
            run.assert_not_called()

    def test_partial_compile_does_not_publish_earlier_crates(self):
        def incomplete(cmd, **kwargs):
            if "aterm_bidi" in cmd:
                return self.fake_compiler(cmd, **kwargs)
            return compile_result([], diagnostic="note: of which 500 kernel-certified\n")

        with patch.object(scoreboard.subprocess, "run", side_effect=incomplete) as run:
            status, stdout, stderr = self.invoke("--out", str(self.floor))
            self.assertEqual((status, stdout), (2, ""), stderr)
            self.assertIn("aterm_bits: invalid verification wire", stderr)
            self.assertEqual(run.call_count, 2)
        self.assertFalse(self.floor.exists())


if __name__ == "__main__":
    unittest.main()
