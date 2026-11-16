#!/usr/bin/env python3
"""Wire accounting and fake-tool battery controls; these execute no Rust compiler."""

from copy import deepcopy
import importlib.util
from itertools import permutations
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / "scripts/lib/trust_program_wire.py"
spec = importlib.util.spec_from_file_location("trust_program_wire", HELPER)
wire = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wire)


def rows(outcome="proved", *, session="test-session", extra=False):
    results = [] if outcome is None else [{"kind": "postcondition", "outcome": outcome}]
    fn = {"type": "function_result", "crate_name": "main", "verification_session": session,
          "function": "main::main", "results": results, "proved": int(outcome == "proved"),
          "failed": int(outcome == "failed"), "unknown": int(outcome in wire.UNKNOWN_OUTCOMES),
          "timed_out": int(outcome == "timeout"), "skipped": int(outcome == "skipped"),
          "runtime_checked": int(outcome == "runtime_checked"), "total": len(results)}
    functions = [fn]
    if extra:
        second = deepcopy(fn)
        second["function"] = "main::m::generated"
        functions.append(second)
    names = sorted(x["function"] for x in functions)
    coverage = {"type": "coverage_summary", "crate_name": "main", "verification_session": session,
                "eligible": len(names), "processed": len(names), "function_identities": {
                    "schema": wire.IDENTITIES, "eligible_functions": names,
                    "processed_functions": names.copy()},
                "memory": {"schema": wire.MEMORY, "counters": {}}}
    summary = {"type": "crate_summary", "crate_name": "main", "verification_session": session,
               "functions_analyzed": len(names),
               "functions_verified": len(names) if outcome == "proved" else 0}
    for field in ("proved", "failed", "unknown", "timed_out", "skipped", "runtime_checked"):
        summary["total_" + field] = sum(x[field] for x in functions)
    summary["total_obligations"] = sum(x["total"] for x in functions)
    return functions + [coverage, summary]


def encode(messages):
    return "\n".join(wire.PREFIX + json.dumps(x) for x in messages) + "\n"


def inspect(messages, stdout=""):
    return wire.inspect_wire(encode(messages), stdout, crate_name="main", session="test-session",
                             required_functions=["main::main"])


class WireTests(unittest.TestCase):
    def test_valid_complete_population_retains_extra_bodies(self):
        report = inspect(rows(extra=True))
        self.assertEqual(report["functions"], ["main::m::generated", "main::main"])
        self.assertEqual(report["counts"]["proved"], 2)
        self.assertTrue(wire.acceptable(report))

    def test_present_body_with_no_obligations_earns_no_proof_count(self):
        report = inspect(rows(None))
        self.assertEqual(sum(report["counts"].values()), 0)
        self.assertEqual(report["functions"], ["main::main"])
        self.assertFalse(wire.acceptable(report))

    def test_empty_malformed_and_wrong_shape_wire_refuse(self):
        for raw in ("", "diagnostic only", "TRUST_JSON:{", "TRUST_JSON:[]", "TRUST_JSON:null",
                    'TRUST_JSON:"text"', 'TRUST_JSON:{"type":"x","type":"x"}',
                    'TRUST_JSON:{"x":NaN}', 'TRUST_JSON:{"type":[]}',
                    'TRUST_JSON:{"type":{}}', "prefix TRUST_JSON:{}"):
            with self.subTest(raw=raw), self.assertRaises(wire.WireError):
                wire.inspect_wire(raw, "", crate_name="main", session="test-session",
                                  required_functions=["main::main"])

    def test_each_missing_or_duplicate_transport_row_refuses(self):
        original = rows()
        for i in range(len(original)):
            for changed in (original[:i] + original[i+1:], original + [original[i]]):
                with self.subTest(index=i, count=len(changed)), self.assertRaises(wire.WireError):
                    inspect(changed)

    def test_only_function_rows_then_coverage_then_summary_are_accepted(self):
        accepted = rejected = 0
        for changed in permutations(rows(extra=True)):
            types = [row["type"] for row in changed]
            with self.subTest(types=types):
                if types == ["function_result", "function_result", "coverage_summary", "crate_summary"]:
                    self.assertTrue(wire.acceptable(inspect(changed)))
                    accepted += 1
                else:
                    with self.assertRaises(wire.WireError):
                        inspect(changed)
                    rejected += 1
        self.assertEqual((accepted, rejected), (2, 22))

    def test_expected_main_is_required_not_any_nonempty_body(self):
        changed = rows()
        changed[0]["function"] = "main::unrelated"
        changed[1]["function_identities"]["eligible_functions"] = ["main::unrelated"]
        changed[1]["function_identities"]["processed_functions"] = ["main::unrelated"]
        with self.assertRaises(wire.WireError):
            inspect(changed)

    def test_coverage_identity_mismatch_duplicate_and_unsorted_refuse(self):
        for names in (["main::other"], ["main::main", "main::main"],
                      ["main::main", "main::m::generated"], []):
            changed = rows()
            changed[1]["function_identities"]["processed_functions"] = names
            changed[1]["processed"] = len(names)
            with self.subTest(names=names), self.assertRaises(wire.WireError):
                inspect(changed)

    def test_coverage_without_a_current_memory_summary_refuses(self):
        # T3 L4 C09w: the memory summary is required, at its one schema.
        for memory in (None, {"counters": {}},
                       {"schema": "trust-memory-summary/v0", "counters": {}},
                       {"schema": wire.MEMORY}):
            changed = rows()
            if memory is None:
                del changed[1]["memory"]
            else:
                changed[1]["memory"] = memory
            with self.subTest(memory=memory), self.assertRaises(wire.WireError):
                inspect(changed)

    def test_missing_or_extra_function_cannot_hide_behind_counts(self):
        changed = rows(extra=True)
        changed[0]["function"] = "main::other"
        with self.assertRaises(wire.WireError):
            inspect(changed)

    def test_consistently_empty_inventory_is_not_fixture_coverage(self):
        changed = rows(None)[1:]
        changed[0].update(eligible=0, processed=0)
        changed[0]["function_identities"].update(eligible_functions=[], processed_functions=[])
        changed[1]["functions_analyzed"] = 0
        with self.assertRaises(wire.WireError):
            inspect(changed)

    def test_all_reported_counts_are_reconciled(self):
        original = rows("timeout")
        for index, row in enumerate(original):
            for field, value in row.items():
                if type(value) is not int:
                    continue
                for wrong in (value + 1, True, -1, "0", None):
                    changed = deepcopy(original)
                    changed[index][field] = wrong
                    with self.subTest(index=index, field=field, wrong=wrong), self.assertRaises(wire.WireError):
                        inspect(changed)

    def test_malformed_results_refuse(self):
        for results in ({}, None, [None], [{"outcome": "proved"}],
                        [{"outcome": "proved", "kind": ""}],
                        [{"outcome": "refuted", "kind": "postcondition"}]):
            changed = rows()
            changed[0]["results"] = results
            with self.subTest(results=results), self.assertRaises(wire.WireError):
                inspect(changed)

    def test_all_nonproved_outcomes_prevent_clean_acceptance(self):
        for outcome in wire.OUTCOMES[1:]:
            report = inspect(rows(outcome, extra=True))
            self.assertFalse(wire.acceptable(report), outcome)
            self.assertEqual(len(report["nonclean"]), 2)

    def test_only_existing_unknown_print_gap_allowance_is_permitted(self):
        for outcome in ("failed", "unknown", "timeout", "skipped", "runtime_checked"):
            changed = rows(extra=True)
            changed[1] = rows(outcome)[0]
            changed[1]["function"] = "main::m::generated"
            changed[1]["results"][0]["kind"] = "native-verification-gap"
            changed[-1]["functions_verified"] = 1
            for field in ("proved", "failed", "unknown", "timed_out", "skipped", "runtime_checked"):
                changed[-1]["total_" + field] = sum(row[field] for row in changed[:2])
            report = inspect(changed)
            self.assertEqual(wire.acceptable(report, "native-verification-gap"), outcome == "unknown")
        self.assertFalse(wire.acceptable(inspect(rows("unknown")), "native-verification-gap"))

    def test_crate_session_and_channel_binding(self):
        for index in range(3):
            for field, wrong in (("crate_name", "foreign"), ("verification_session", "stale")):
                changed = rows()
                changed[index][field] = wrong
                with self.subTest(index=index, field=field), self.assertRaises(wire.WireError):
                    inspect(changed)
        with self.assertRaises(wire.WireError):
            inspect(rows(), stdout=encode(rows()))

    def test_nonclean_extra_body_is_retained(self):
        changed = rows(extra=True)
        changed[1]["results"][0]["outcome"] = "unknown"
        changed[1].update(proved=0, unknown=1)
        changed[-1].update(total_proved=1, total_unknown=1, functions_verified=1)
        report = inspect(changed)
        self.assertFalse(wire.acceptable(report))
        self.assertEqual(report["nonclean"][0]["function"], "main::m::generated")

    def test_cli_distinguishes_invalid_from_reported_nonclean(self):
        with tempfile.TemporaryDirectory() as tmp:
            err, out = Path(tmp)/"stderr", Path(tmp)/"stdout"
            out.write_text("")
            for raw, expected in (("", 2), (encode(rows("unknown")), 1), (encode(rows(None)), 1),
                                  (encode(rows()), 0)):
                err.write_text(raw)
                run = subprocess.run([sys.executable, "-B", str(HELPER), "--stderr", str(err),
                                      "--stdout", str(out), "--crate-name", "main", "--session", "test-session",
                                      "--require-function", "main::main"], capture_output=True, text=True)
                self.assertEqual(run.returncode, expected, run.stderr)


class BatteryMockTests(unittest.TestCase):
    def run_battery(self, mode, fixture="r08_clean_origin_call_verify_on"):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root/"tests").mkdir()
            shutil.copy2(ROOT/"tests/e2e_two_language_programs.sh", root/"tests")
            shutil.copytree(ROOT/"tests/two-language-programs"/fixture,
                            root/"tests/two-language-programs"/fixture)
            (root/"scripts/lib").mkdir(parents=True)
            shutil.copy2(HELPER, root/"scripts/lib")
            # The battery ends by checking the executed rows against the fixture
            # directories ($TRUST_ROOT/scripts/check_two_language_program_inventory.py);
            # without it every run here exits 1 AFTER its graded rows passed.
            shutil.copy2(ROOT/"scripts/check_two_language_program_inventory.py", root/"scripts")
            (root/"tests/two-language-programs").mkdir(exist_ok=True)
            shutil.copy2(ROOT/"tests/two-language-programs/wire_grade.py",
                         root/"tests/two-language-programs/wire_grade.py")
            bindir = root/"bin"
            bindir.mkdir()
            (bindir/"targo").write_text("#!/bin/sh\necho 'targo mock for oracle tests only'\n")
            payload = rows(None if mode == "zero-obligations" else "proved")
            (root/"payload.json").write_text(json.dumps(payload))
            mock = '''#!PYTHON
import json, os, pathlib, sys
args = sys.argv[1:]
if '--version' in args or '-Vv' in args:
    print('trustc mock for oracle tests only'); sys.exit(0)
out = pathlib.Path(args[args.index('-o') + 1])
out.write_text('#!/bin/sh\\ncat expected.txt\\nprintf ran > ' + os.environ['MOCK_RAN'] + '\\n')
out.chmod(0o755)
if '-Ztrust-verify-output=json' not in args:
    sys.exit(0)
mode = os.environ['MOCK_MODE']
if mode == 'empty': sys.exit(0)
if mode == 'malformed': print('TRUST_JSON:{', file=sys.stderr); sys.exit(0)
if mode == 'wrong-shape': print('TRUST_JSON:[]', file=sys.stderr); sys.exit(0)
if mode == 'reader-crash': print('TRUST_JSON:null', file=sys.stderr); sys.exit(0)
payload = json.loads(pathlib.Path(os.environ['MOCK_PAYLOAD']).read_text())
if mode == 'post-terminal-function': payload = payload[1:] + payload[:1]
session = next((x.split('=', 1)[1] for x in args if x.startswith('-Ztrust-verify-session=')), '')
for row in payload:
    row['verification_session'] = session
    if mode == 'missing-main':
        if row['type'] == 'function_result': row['function'] = 'main::unrelated'
        if row['type'] == 'coverage_summary':
            row['function_identities']['eligible_functions'] = ['main::unrelated']
            row['function_identities']['processed_functions'] = ['main::unrelated']
    if mode in ('print-gap', 'timed-out-print-gap', 'classed-print-gap', 'unclassed-print-gap',
                'failed-print-gap', 'requires-assumption'):
        kind = ('assumption:requires' if mode == 'requires-assumption' else
                'native-verification-gap' if mode in ('print-gap', 'timed-out-print-gap') else 'assert')
        outcome = {'print-gap': 'unknown', 'timed-out-print-gap': 'timeout',
                   'classed-print-gap': 'runtime_checked', 'unclassed-print-gap': 'runtime_checked',
                   'failed-print-gap': 'failed', 'requires-assumption': 'skipped'}[mode]
        is_unknown = outcome in ('unknown', 'timeout', 'skipped')
        if row['type'] == 'function_result':
            gap = {'kind': kind, 'outcome': outcome}
            if mode in ('classed-print-gap', 'failed-print-gap'): gap['gap_class'] = 'std-print-dispatch'
            row['results'].append(gap)
            row.update(unknown=int(is_unknown), total=2, timed_out=int(outcome == 'timeout'),
                       skipped=int(outcome == 'skipped'), runtime_checked=int(outcome == 'runtime_checked'),
                       failed=int(outcome == 'failed'))
        if row['type'] == 'crate_summary':
            row.update(total_unknown=int(is_unknown), total_obligations=2, functions_verified=0,
                       total_timed_out=int(outcome == 'timeout'), total_skipped=int(outcome == 'skipped'),
                       total_runtime_checked=int(outcome == 'runtime_checked'), total_failed=int(outcome == 'failed'))
    print('TRUST_JSON:' + json.dumps(row), file=sys.stderr)
sys.exit(7 if mode == 'valid-wire-compiler-fails' else 0)
'''.replace("PYTHON", sys.executable, 1)
            (bindir/"trustc").write_text(mock)
            for tool in bindir.iterdir():
                tool.chmod(0o755)
            ran = root/"ran"
            env = dict(os.environ, TRUSTC=str(bindir/"trustc"), TARGO=str(bindir/"targo"),
                       MOCK_MODE=mode, MOCK_PAYLOAD=str(root/"payload.json"), MOCK_RAN=str(ran))
            run = subprocess.run(["/bin/bash", str(root/"tests/e2e_two_language_programs.sh"),
                                  "--only", fixture], env=env, capture_output=True, text=True)
            return run, ran.exists()

    def test_valid_wire_runs_fixture(self):
        run, ran = self.run_battery("valid")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertTrue(ran)
        self.assertIn("wire: 1 fns, 1 proved", run.stdout)

    def test_zero_obligation_inventory_does_not_verify_a_program(self):
        run, ran = self.run_battery("zero-obligations")
        self.assertNotEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertFalse(ran)
        self.assertIn("vacuous: nothing proved", run.stdout)

    def test_invalid_wire_does_not_run_fixture(self):
        for mode in ("empty", "malformed", "wrong-shape", "reader-crash", "missing-main",
                     "post-terminal-function"):
            with self.subTest(mode=mode):
                run, ran = self.run_battery(mode)
                self.assertNotEqual(run.returncode, 0, run.stdout + run.stderr)
                self.assertFalse(ran)

    def test_valid_wire_cannot_hide_nonzero_compiler_exit(self):
        run, ran = self.run_battery("valid-wire-compiler-fails")
        self.assertNotEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertFalse(ran)

    def test_r09_keeps_current_tolerances_after_accounting_validation(self):
        for mode in ("print-gap", "classed-print-gap", "requires-assumption"):
            with self.subTest(mode=mode):
                run, ran = self.run_battery(mode, "r09_println_verify_on")
                self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
                self.assertTrue(ran)
                self.assertIn("| clean=yes", run.stdout)
        for mode in ("timed-out-print-gap", "unclassed-print-gap", "failed-print-gap",
                     "valid-wire-compiler-fails", "missing-main", "post-terminal-function",
                     "zero-obligations"):
            with self.subTest(mode=mode):
                run, ran = self.run_battery(mode, "r09_println_verify_on")
                self.assertNotEqual(run.returncode, 0, run.stdout + run.stderr)
                self.assertFalse(ran)

    def test_verification_off_lane_does_not_require_wire(self):
        run, ran = self.run_battery("empty", "r01_rust_calls_clean_select")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertTrue(ran)
        self.assertNotIn("wire:", run.stdout)


if __name__ == "__main__":
    unittest.main()
