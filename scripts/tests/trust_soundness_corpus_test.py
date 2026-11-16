#!/usr/bin/env python3
"""Soundness-corpus reader controls. No compiler, provider or proof is created.

The small fixture projects actual closed ec8 observations. Tests rekey its
function names to the runner's fixed `sbc` test namespace, mutate wire DATA and
exercise classification only; none is native/compiler/proof qualification.
"""
import copy
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "trust-soundness-corpus.py"
spec = importlib.util.spec_from_file_location("tested_soundness_corpus", SCRIPT)
corpus = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = corpus
exec(compile(SCRIPT.read_bytes(), str(SCRIPT), "exec"), corpus.__dict__)
FIXTURE = Path(__file__).with_name("fixtures") / "trust_soundness_corpus_native_rows.json"


def framed(value):
    return "TRUST_JSON:" + json.dumps(value) + "\n"


class TrustcRows(unittest.TestCase):
    def setUp(self):
        self.observed = json.loads(FIXTURE.read_text())["functions"]
        self.frames = copy.deepcopy(self.observed)
        for frame in self.frames:
            frame["function"] = "sbc::" + frame["function"].split("::")[-1]
        self.entry = {
            "id": "reader-only-control", "lang": "rust", "source": "not-executed.rs",
            "_dir": FIXTURE.parent,
            "reproducer": {"function": "direct_counted", "obligation": {
                "kind": "assert", "message": "panic freedom"}},
            "twin": {"function": "reified_counted", "obligation": {
                "kind": "divzero", "message": "division by zero"}},
        }

    def verdict(self, text, side="reproducer", rc=1, entry=None):
        functions, problems = corpus.decode_trustc_rows(text)
        return corpus.trustc_level_verdict(
            entry or self.entry, side, rc, functions, "error: unrelated callee root refused\n",
            problems,
        )

    def original_text(self):
        return "".join(map(framed, self.frames))

    def proved_entry(self):
        # The observed division theorem is real, but this only tests whether
        # the reader retains an emitted claim. It declares no false program.
        entry = copy.deepcopy(self.entry)
        entry["reproducer"] = copy.deepcopy(entry["twin"])
        return entry

    def test_actual_distinct_function_frames_and_other_record_types_remain_readable(self):
        text = "ordinary diagnostics\n" + self.original_text()
        text += framed({"type": "crate_summary", "total": 4})
        functions, problems = corpus.decode_trustc_rows(text)
        self.assertEqual(problems, [])
        self.assertEqual(len(functions), 3)
        self.assertEqual(functions["sbc::direct_counted"], self.frames[1]["results"])
        self.assertEqual(self.verdict(text)[0], corpus.REFUSED)
        self.assertEqual(self.verdict(text, "twin")[0], corpus.PROVED)

    def test_stdout_stderr_boundary_does_not_join_two_complete_json_records(self):
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            corpus, "run", return_value=(1, framed(self.frames[0]).rstrip("\n"),
                                         framed(self.frames[1])),
        ) as child:
            result = corpus.trustc_rows(
                self.entry, "not-executed", [], "0", Path(directory), "not-executed.rs",
            )
        child.assert_called_once()
        self.assertEqual(result[3], [])
        self.assertEqual(set(result[1]), {"sbc::reified_counted", "sbc::direct_counted"})

    def test_unreadable_record_after_an_unproved_row_is_error_not_refusal(self):
        text = self.original_text() + 'TRUST_JSON:{"type":"function_result",\n'
        for rc in (0, 1):
            with self.subTest(rc=rc):
                verdict = self.verdict(text, rc=rc)
                self.assertEqual(verdict[0], corpus.ERROR)
                self.assertIn("unreadable TRUST_JSON", verdict[1])
                self.assertEqual(corpus.classify(
                    self.entry, "trustc-default", "reproducer", verdict,
                ), "ERROR")

    def test_duplicate_envelopes_cannot_be_read_as_one_refusal_or_twin_proof(self):
        text = self.original_text() + framed(self.frames[1])
        self.assertIn("duplicate function", ";".join(corpus.decode_trustc_rows(text)[1]))
        self.assertEqual(self.verdict(text)[0], corpus.ERROR)
        self.assertEqual(self.verdict(text, "twin")[0], corpus.ERROR)

    def test_duplicate_json_keys_are_not_silently_overwritten(self):
        malformed = ('TRUST_JSON:{"type":"function_result", "function":"sbc::f", '
                     '"results":[], "results":[]}\n')
        self.assertEqual(self.verdict(self.original_text() + malformed)[0], corpus.ERROR)
        self.assertIn("duplicate JSON key", ";".join(corpus.decode_trustc_rows(malformed)[1]))

    def test_missing_arrays_and_nonobject_records_are_error(self):
        for value in (None, [], 17, {}, {"type": 1},
                      {"type": "function_result", "function": "sbc::f"},
                      {"type": "function_result", "function": "", "results": []},
                      {"type": "function_result", "function": "sbc::f", "results": None}):
            with self.subTest(value=value):
                self.assertEqual(self.verdict(self.original_text() + framed(value))[0], corpus.ERROR)

    def test_malformed_rows_cannot_leave_an_unproved_prefix_as_a_refusal(self):
        for row in (None, [], {}, {"kind": "assert"},
                    {"kind": "assert", "outcome": None},
                    {"kind": "assert", "outcome": "unknown", "location": []}):
            bad = {"type": "function_result", "function": "sbc::other", "results": [row]}
            with self.subTest(row=row):
                self.assertEqual(self.verdict(self.original_text() + framed(bad))[0], corpus.ERROR)

    def test_inconsistent_declared_totals_are_error(self):
        for total in (True, "1", -1, 0, 2):
            bad = copy.deepcopy(self.frames[0])
            bad["function"] = "sbc::other"
            bad["total"] = total
            with self.subTest(total=total):
                self.assertEqual(self.verdict(self.original_text() + framed(bad))[0], corpus.ERROR)

    def test_all_nine_current_wire_outcomes_remain_readable(self):
        # Outcome::as_str, not the broader saved-report alias parser.
        outcomes = ("proved", "failed", "unknown", "timeout", "runtime_checked",
                    "skipped", "unsupported", "canceled", "rejected")
        for outcome in outcomes:
            frame = {"type": "function_result", "function": "sbc::wire_syntax", "results": [
                {"kind": "assert", "outcome": outcome},
            ]}
            with self.subTest(outcome=outcome):
                functions, problems = corpus.decode_trustc_rows(framed(frame))
                self.assertEqual(problems, [])
                self.assertEqual(functions["sbc::wire_syntax"][0]["outcome"], outcome)

    def test_unknown_or_noncanonical_outcomes_cannot_be_classified_as_refusal(self):
        for outcome in ("gibberish", "almost_proved", "PROVED", "timed_out", "cancelled",
                        "refuted", "proven"):
            bad = {"type": "function_result", "function": "sbc::other", "results": [
                {"kind": "assert", "outcome": outcome},
            ]}
            with self.subTest(outcome=outcome):
                text = self.original_text() + framed(bad)
                self.assertEqual(self.verdict(text)[0], corpus.ERROR)
                self.assertEqual(self.verdict(text, "twin")[0], corpus.ERROR)
                self.assertEqual(self.verdict(text, entry=self.proved_entry())[0], corpus.PROVED)

    def test_nonfinite_json_constants_refuse_at_any_depth_without_erasing_prior_claims(self):
        for constant in ("NaN", "Infinity", "-Infinity"):
            bad = ('TRUST_JSON:{"type":"function_result","function":"sbc::other",'
                   '"results":[{"kind":"assert","outcome":"unknown",'
                   '"nested":{"nonfinite":' + constant + '}}]}\n')
            with self.subTest(constant=constant):
                text = self.original_text() + bad
                self.assertEqual(self.verdict(text)[0], corpus.ERROR)
                self.assertEqual(self.verdict(text, "twin")[0], corpus.ERROR)
                self.assertEqual(self.verdict(text, entry=self.proved_entry())[0], corpus.PROVED)

    def test_overflowing_float_does_not_silently_become_infinity(self):
        for number in ("1e309", "-1e309"):
            bad = ('TRUST_JSON:{"type":"crate_summary","value":' + number + '}\n')
            with self.subTest(number=number):
                self.assertEqual(self.verdict(self.original_text() + bad)[0], corpus.ERROR)
        finite = framed({"type": "crate_summary", "value": 1.25e100})
        self.assertEqual(self.verdict(self.original_text() + finite)[0], corpus.REFUSED)

    def test_existing_minimal_selftest_records_do_not_need_optional_count_fields(self):
        minimal = {"type": "function_result", "function": self.frames[1]["function"],
                   "results": self.frames[1]["results"]}
        self.assertEqual(self.verdict(framed(minimal))[0], corpus.REFUSED)

    def test_observed_reproducer_proof_survives_bad_output_and_later_crash(self):
        text = self.original_text() + "TRUST_JSON:{truncated\n"
        for rc in (1, 101, -11, None):
            with self.subTest(rc=rc):
                verdict = self.verdict(text, rc=rc, entry=self.proved_entry())
                self.assertEqual(verdict[0], corpus.PROVED)
                self.assertEqual(corpus.classify(
                    self.entry, "trustc-default", "reproducer", verdict,
                ), "FALSE-PROVED")
                self.assertEqual(self.verdict(text, "twin", rc=rc)[0], corpus.ERROR)

    def test_whole_crate_refusal_does_not_hide_an_anchored_proved_claim(self):
        self.assertEqual(self.verdict(
            self.original_text(), entry=self.proved_entry(), rc=1,
        )[0], corpus.PROVED)

    def test_real_missing_reified_call_carrier_is_anchor_error_not_division_proof(self):
        entry = copy.deepcopy(self.entry)
        entry["reproducer"]["function"] = "reified_counted"
        verdict = self.verdict(self.original_text(), entry=entry)
        self.assertEqual(verdict[0], corpus.ERROR)
        self.assertIn("anchor-miss", verdict[1])

    def test_bad_output_does_not_retire_a_known_open_marker(self):
        entry = copy.deepcopy(self.entry)
        entry["known_open"] = {"trustc-default": "reader-only marker"}
        verdict = self.verdict(self.original_text() + "TRUST_JSON:{\n", entry=entry)
        self.assertEqual(corpus.classify(
            entry, "trustc-default", "reproducer", verdict,
        ), "ERROR(known-open)")

    def test_assumption_mode_keeps_observed_reproducer_claim_but_not_twin_proof(self):
        entry = copy.deepcopy(self.entry)
        for side in corpus.SIDES:
            entry[side] = {"function": "assumed", "mode": "assumption-kept"}
        text = framed({"type": "function_result", "function": "sbc::assumed", "results": [
            {"kind": "assumption:assumed-total", "outcome": "skipped"},
        ]}) + "TRUST_JSON:{\n"
        self.assertEqual(self.verdict(text, entry=entry)[0], corpus.PROVED)
        self.assertEqual(self.verdict(text, "twin", entry=entry)[0], corpus.ERROR)

    def test_explicit_build_acceptance_still_judges_process_status(self):
        entry = copy.deepcopy(self.entry)
        entry["reproducer"]["mode"] = "build-accepted"
        for rc, status in ((0, corpus.PROVED), (1, corpus.REFUSED), (101, corpus.ERROR)):
            with self.subTest(rc=rc):
                self.assertEqual(self.verdict("TRUST_JSON:{\n", rc=rc, entry=entry)[0], status)


class SelectorOwnership(unittest.TestCase):
    module = "scripts.tests.trust_soundness_corpus_test"
    paths = (
        "scripts/trust-soundness-corpus.py",
        "scripts/tests/trust_soundness_corpus_test.py",
        "scripts/tests/fixtures/trust_soundness_corpus_native_rows.json",
        "tests/trust-soundness-corpus/README.md",
    )
    neighbours = (
        "scripts/trust-soundness-corpus-extra.py",
        "scripts/tests/fixtures/trust_soundness_corpus_native_rows_extra.json",
        "tests/trust-soundness-corpus/README-extra.md",
    )

    def setUp(self):
        scripts = Path(__file__).resolve().parents[1]
        paths = mock.patch.object(sys, "path", [str(scripts / "lib"), str(scripts),
                                                str(scripts.parent), *sys.path])
        paths.start()
        self.addCleanup(paths.stop)
        import land_development
        import land_gate
        import land_select
        from scripts.tests import land_gate_test
        self.development = land_development
        self.gate = land_gate
        self.selection = land_select
        self.fixtures = land_gate_test
        temporary = tempfile.TemporaryDirectory(prefix="soundness-corpus-owner-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.files = {
            "Cargo.toml": '[workspace]\nmembers=["crates/fixture"]\ndefault-members=["crates/fixture"]\n',
            "crates/fixture/Cargo.toml": '[package]\nname="fixture"\nversion="0.1.0"\n',
            "crates/fixture/src/lib.rs": "// selector input only; never compiled\n",
        }
        self.files.update({path: "# selector input only\n" for path in (*self.paths, *self.neighbours)})
        self.base = self.fixtures.make_repo(self.root, self.files, {})

    def changed(self, paths):
        for path, content in self.files.items():
            (self.root / path).write_text(content + ("# changed\n" if path in paths else ""))
        self.fixtures.git_in(self.root, "add", "-A")
        self.fixtures.git_in(self.root, "commit", "-qm", "source owner control", "--allow-empty")
        graph = self.selection.build_manifest_graph(
            self.selection.TreeIndex.load(str(self.root), "HEAD"),
        )
        actual = self.selection.changed_paths(str(self.root), self.base, graph.index.rev)
        self.assertEqual(set(actual), set(paths))
        return graph, self.selection.select(graph, self.base, actual)

    def test_each_exact_reader_input_selects_the_fresh_control_module(self):
        for paths in [(path,) for path in self.paths] + [self.paths]:
            with self.subTest(paths=paths):
                graph, selected = self.changed(paths)
                self.assertEqual(self.selection.validation_test_modules(paths), [self.module])
                scoped = self.development.scope(graph, selected)
                self.assertFalse(scoped.errors)
                self.assertEqual(scoped.tests, [self.module])
                self.assertTrue(self.development.has_declared_source_ownership(graph.index, paths))
                leg, = self.gate.development_legs(graph, selected, [], 1)
                self.assertEqual(leg.id, "development-validation-tests")
                self.assertEqual(leg.command, [sys.executable, "scripts/land_gate.py",
                                               "validation-tests", self.module])
                self.assertTrue(leg.force_run)
                self.assertFalse(leg.cache_members)

    def test_full_script_diagnostics_stay_global_and_exact_readme_has_a_validation_owner(self):
        graph, _ = self.changed(self.paths)
        for path in self.paths:
            with self.subTest(path=path):
                with mock.patch.dict(self.selection.VALIDATION_TEST_SUBJECTS, clear=True):
                    ordinary = self.selection.classify(graph, path)
                self.assertEqual(self.selection.classify(graph, path), ordinary)
                if path == "tests/trust-soundness-corpus/README.md":
                    self.assertNotIn(path, self.selection.VALIDATION_TEST_SUBJECTS)
                    self.assertEqual(self.selection.VALIDATION_PROGRAM_TESTS[path], (self.module,))
                    self.assertEqual(ordinary[0], "validation")
                    without_readme = dict(self.selection.VALIDATION_PROGRAM_TESTS)
                    del without_readme[path]
                    with mock.patch.dict(self.selection.VALIDATION_PROGRAM_TESTS,
                                         without_readme, clear=True):
                        self.assertEqual(self.selection.classify(graph, path)[0], "unmapped")
                else:
                    self.assertEqual(self.selection.VALIDATION_TEST_SUBJECTS[path], (self.module,))
                    self.assertNotIn(path, self.selection.VALIDATION_PROGRAM_TESTS)
                    self.assertEqual(ordinary[0], "everything")
                    self.assertTrue(self.selection.select(graph, self.base, [path]).everything)

    def test_neighbouring_scripts_and_data_remain_unowned_alone_and_in_union(self):
        for neighbour in self.neighbours:
            for paths in ((neighbour,), (*self.paths, neighbour)):
                with self.subTest(paths=paths):
                    graph, selected = self.changed(paths)
                    self.assertNotIn(neighbour, self.development.PROGRAM_TESTS)
                    self.assertNotIn(neighbour, self.selection.VALIDATION_PROGRAM_TESTS)
                    self.assertNotIn(neighbour, self.selection.VALIDATION_TEST_SUBJECTS)
                    self.assertFalse(self.development.may_have_scope(paths))
                    self.assertFalse(self.development.has_declared_source_ownership(graph.index, paths))
                    self.assertTrue(self.development.scope(graph, selected).errors)
                    with self.assertRaisesRegex(RuntimeError, "development scope refused"):
                        self.gate.development_legs(graph, selected, [], 1)


class TrustVcDriverRows(unittest.TestCase):
    """The real VC reader consumes fake wire DATA; no driver/compiler runs."""

    def setUp(self):
        self.entry = next(copy.deepcopy(entry) for entry in corpus.load_entries()
                          if entry["lang"] == "trust-vc")
        self.bad = self.entry["reproducer"]["function"]
        self.good = self.entry["twin"]["function"]

    @staticmethod
    def row(function, verdict, detail=""):
        return f"TRUST_VC_DRIVER_RESULT\t{function}\t{verdict}\t{detail}\n"

    @staticmethod
    def summary(counts="2\t1\t1\t0\t0\t0"):
        return "TRUST_VC_DRIVER_SUMMARY\t" + counts + "\n"

    def ordinary_rows(self):
        return self.row(self.bad, "Refuted") + self.row(self.good, "Verified")

    def verdicts(self, text, rc=1):
        with mock.patch.object(corpus, "is_executable", return_value=True):
            driver = corpus.TrustVcMir("/fake/not-executed/trust-vc-driver", None)
        with tempfile.TemporaryDirectory(prefix="vc-driver-wire-rows-") as directory, \
                mock.patch.object(corpus, "run", return_value=(rc, text, "")) as child:
            result = {side: driver.verdict(self.entry, side, Path(directory))
                      for side in corpus.SIDES}
        child.assert_called_once()  # Both targets use the same actual record set.
        return result

    def test_complete_current_six_outcome_wire_contract_remains_readable(self):
        text = self.ordinary_rows()
        for verdict in ("Unknown", "Error", "UnsupportedType", "UnsupportedContract"):
            text += self.row("other::" + verdict, verdict, "detail\u2028still one LF record")
        got = self.verdicts(text + self.summary("6\t1\t1\t1\t1\t2"))
        self.assertEqual(got["reproducer"][0], corpus.REFUSED)
        self.assertEqual(got["twin"][0], corpus.PROVED)

    def test_unique_qualified_function_names_remain_readable(self):
        text = self.row("sbc::" + self.bad, "Refuted")
        text += self.row("sbc::" + self.good, "Verified")
        got = self.verdicts(text + self.summary())
        self.assertEqual(got["reproducer"][0], corpus.REFUSED)
        self.assertEqual(got["twin"][0], corpus.PROVED)

    def test_contradictory_driver_output_cannot_make_the_strict_report_green(self):
        driver = "/fake/not-executed/trust-vc-driver"
        text = self.ordinary_rows() + self.summary("2\t0\t2\t0\t0\t0")

        def run(argv, **_kwargs):
            return (1, text, "") if argv[0] == driver else (0, "fake metadata DATA\n", "")

        with tempfile.TemporaryDirectory(prefix="vc-driver-strict-report-") as directory:
            root = Path(directory)
            work = root / "work"
            work.mkdir()
            output = root / "report.json"
            args = SimpleNamespace(filter=None, verifiers="trust-vc-mir", no_witness=True,
                                   strict=True, json=str(output), keep_work=False, jobs=1,
                                   timeout=None)
            with mock.patch.object(corpus, "load_entries", return_value=[self.entry]), \
                    mock.patch.object(corpus, "resolve_trustc", return_value=(None, "fixture metadata only")), \
                    mock.patch.object(corpus, "is_executable", return_value=True), \
                    mock.patch.object(corpus, "run", side_effect=run), \
                    mock.patch.dict(corpus.os.environ, {"TRUST_VC_MIR_DRIVER": driver}), \
                    mock.patch.object(corpus.tempfile, "mkdtemp", return_value=str(work)), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                rc = corpus.corpus_run(args)
            report = json.loads(output.read_text())
        self.assertEqual(rc, 1)
        cells = report["results"][0]["verifiers"]["trust-vc-mir"]
        self.assertEqual({side: cells[side]["class"] for side in corpus.SIDES},
                         {side: "ERROR" for side in corpus.SIDES})

    def test_summary_requires_every_exact_per_verdict_counter(self):
        for counts in ("2\t0\t2\t0\t0\t0", "2", "02\t1\t1\t0\t0\t0",
                       "2\t1\t1\t0\t0\t0\textra", "2\t1\t1\t0\t0\t" + "9" * 5000):
            with self.subTest(counts=counts[:60]):
                got = self.verdicts(self.ordinary_rows() + self.summary(counts))
                self.assertEqual(got["reproducer"][0], corpus.ERROR)
                self.assertEqual(got["twin"][0], corpus.ERROR)

    def test_unknown_wire_outcome_cannot_become_a_refusal(self):
        for verdict in ("Verfied", "verified", "", "FutureOutcome"):
            with self.subTest(verdict=verdict):
                text = self.row(self.bad, verdict) + self.row(self.good, "Verified")
                got = self.verdicts(text + self.summary())
                self.assertEqual(got["reproducer"][0], corpus.ERROR)
                self.assertEqual(got["twin"][0], corpus.ERROR)

    def test_duplicate_records_never_erase_an_observed_reproducer_proof(self):
        text = self.row(self.bad, "Verified") + self.ordinary_rows()
        got = self.verdicts(text + self.summary())
        self.assertEqual(got["reproducer"][0], corpus.PROVED)
        self.assertEqual(corpus.classify(self.entry, "trust-vc-mir", "reproducer",
                                       got["reproducer"]), "FALSE-PROVED")
        self.assertEqual(got["twin"][0], corpus.ERROR)

    def test_incomplete_output_keeps_observed_false_proofs_but_no_twin_credit(self):
        rows = self.row(self.bad, "Verified") + self.row(self.good, "Verified")
        for suffix in ("", self.summary("2\t1\t1\t0\t0\t0"),
                       self.summary("2\t2\t0\t0\t0\t0") * 2):
            with self.subTest(suffix=suffix):
                got = self.verdicts(rows + suffix)
                self.assertEqual(got["reproducer"][0], corpus.PROVED)
                self.assertEqual(got["twin"][0], corpus.ERROR)

    def test_a_summary_before_records_is_not_a_trailing_completion_record(self):
        got = self.verdicts(self.summary() + self.ordinary_rows())
        self.assertEqual(got["reproducer"][0], corpus.ERROR)
        self.assertEqual(got["twin"][0], corpus.ERROR)

    def test_ambiguous_unqualified_names_cannot_select_an_unrelated_function(self):
        text = self.row("left::" + self.bad, "Refuted")
        text += self.row("right::" + self.bad, "Verified") + self.row(self.good, "Verified")
        got = self.verdicts(text + self.summary("3\t2\t1\t0\t0\t0"))
        self.assertEqual(got["reproducer"][0], corpus.ERROR)

    def test_malformed_rows_cannot_license_a_twin_proof(self):
        for extra in ("TRUST_VC_DRIVER_RESULT\tmissing-verdict\n",
                      "TRUST_VC_DRIVER_RESULT\t\tRefuted\t\n",
                      self.row("other", "Refuted").rstrip("\n") + "\textra\n"):
            with self.subTest(extra=extra):
                got = self.verdicts(self.ordinary_rows() + extra + self.summary())
                self.assertEqual(got["reproducer"][0], corpus.ERROR)
                self.assertEqual(got["twin"][0], corpus.ERROR)

    def test_crashed_twin_has_no_proof_credit_but_a_reproducer_claim_stands(self):
        rows = self.row(self.bad, "Verified") + self.row(self.good, "Verified")
        got = self.verdicts(rows + self.summary("2\t2\t0\t0\t0\t0"), rc=2)
        self.assertEqual(got["reproducer"][0], corpus.PROVED)
        self.assertEqual(got["twin"][0], corpus.ERROR)

    def test_completion_status_must_match_the_observed_result_population(self):
        for verdict, counts, rc in (
                ("Refuted", "2\t1\t1\t0\t0\t0", 0),
                ("Unknown", "2\t1\t0\t1\t0\t0", 0),
                ("Error", "2\t1\t0\t0\t1\t0", 0),
                ("Verified", "2\t2\t0\t0\t0\t0", 1),
                ("UnsupportedType", "2\t1\t0\t0\t0\t1", 1),
                ("UnsupportedContract", "2\t1\t0\t0\t0\t1", 1)):
            with self.subTest(verdict=verdict, rc=rc):
                text = self.row(self.bad, verdict) + self.row(self.good, "Verified")
                got = self.verdicts(text + self.summary(counts), rc=rc)
                self.assertEqual(got["reproducer"][0],
                                 corpus.PROVED if verdict == "Verified" else corpus.ERROR)
                self.assertEqual(got["twin"][0], corpus.ERROR)

    def test_verified_and_unsupported_only_populations_keep_normal_exit_zero(self):
        for verdict, counts in (("Verified", "2\t2\t0\t0\t0\t0"),
                                ("UnsupportedType", "2\t1\t0\t0\t0\t1"),
                                ("UnsupportedContract", "2\t1\t0\t0\t0\t1")):
            with self.subTest(verdict=verdict):
                text = self.row(self.bad, verdict) + self.row(self.good, "Verified")
                got = self.verdicts(text + self.summary(counts), rc=0)
                self.assertEqual(got["reproducer"][0],
                                 corpus.PROVED if verdict == "Verified" else corpus.REFUSED)
                self.assertEqual(got["twin"][0], corpus.PROVED)


class StrictKnownProofs(unittest.TestCase):
    """Fake verdict DATA exercises the real report/exit path; no verifier runs."""

    def run_report(self, *, strict=True, fixed=False, include_passing=False):
        entries = [copy.deepcopy(entry) for entry in corpus.load_entries()
                   if entry["lang"] == "rust"
                   and corpus.expectation(entry, "trustc-default", "reproducer") != corpus.NA
                   and corpus.expectation(entry, "trustc-default", "twin") == "proved"]
        selected = entries[:2] if include_passing else entries[:1]
        self.assertEqual(len(selected), 2 if include_passing else 1)
        bad_id = selected[0]["id"]
        for entry in selected:
            entry["known_open"] = {}
        selected[0]["known_open"]["trustc-default"] = "synthetic regression marker; no proof credit"

        def verdicts(entry, *_args):
            reproduced = corpus.REFUSED if fixed or entry["id"] != bad_id else corpus.PROVED
            return {"reproducer": (reproduced, "fake verifier DATA"),
                    "twin": (corpus.PROVED, "fake verifier DATA")}

        with tempfile.TemporaryDirectory(prefix="strict-known-proof-") as directory:
            root = Path(directory)
            work = root / "work"
            work.mkdir()
            output = root / "report.json"
            args = SimpleNamespace(filter=None, verifiers="trustc-default", no_witness=True,
                                   strict=strict, json=str(output), keep_work=False,
                                   jobs=1, timeout=None)
            with mock.patch.object(corpus, "load_entries", return_value=selected), \
                    mock.patch.object(corpus, "resolve_trustc", return_value=("/fake/not-executed/trustc", None)), \
                    mock.patch.object(corpus, "run", return_value=(0, "fake metadata DATA\n", "")), \
                    mock.patch.object(corpus, "run_trustc_lane", side_effect=verdicts) as lane, \
                    mock.patch.object(corpus.tempfile, "mkdtemp", return_value=str(work)), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                rc = corpus.corpus_run(args)
            self.assertEqual(lane.call_count, len(selected))
            report = json.loads(output.read_text())
        return rc, report, bad_id

    def test_strict_rejects_a_known_false_proof_without_changing_its_marker(self):
        rc, report, bad_id = self.run_report()
        cell = report["results"][0]["verifiers"]["trustc-default"]["reproducer"]
        self.assertEqual(cell["class"], "KNOWN-FALSE-PROVED")
        self.assertEqual(cell["verdict"], corpus.PROVED)
        self.assertEqual(rc, 1)
        self.assertIn([bad_id, "trustc-default", "reproducer", "KNOWN-FALSE-PROVED"],
                      report["strict_failures"])

    def test_report_only_keeps_the_false_proof_and_reports_its_strict_failure(self):
        rc, report, bad_id = self.run_report(strict=False)
        self.assertEqual(rc, 0)
        self.assertEqual(report["results"][0]["verifiers"]["trustc-default"]["reproducer"]["class"],
                         "KNOWN-FALSE-PROVED")
        self.assertIn([bad_id, "trustc-default", "reproducer", "KNOWN-FALSE-PROVED"],
                      report["strict_failures"])

    def test_a_passing_case_cannot_hide_a_known_false_proof(self):
        rc, report, bad_id = self.run_report(include_passing=True)
        ordinary = next(row for row in report["results"] if row["id"] != bad_id)
        self.assertEqual(ordinary["verifiers"]["trustc-default"]["reproducer"]["class"], "ok")
        self.assertEqual(rc, 1)
        self.assertEqual(report["strict_failures"],
                         [[bad_id, "trustc-default", "reproducer", "KNOWN-FALSE-PROVED"]])

    def test_fixed_known_entry_still_requires_retiring_the_marker(self):
        rc, report, bad_id = self.run_report(fixed=True)
        self.assertEqual(rc, 1)
        self.assertIn([bad_id, "trustc-default", "reproducer", "XFIXED"], report["strict_failures"])


if __name__ == "__main__":
    unittest.main()
