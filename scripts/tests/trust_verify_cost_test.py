"""Cost measurements cannot get credit from absent work or a failed child."""

import copy
import contextlib
from decimal import Decimal, localcontext
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

from scripts import trust_verify_cost as cost


def records():
    rows = []
    sources = cost.function_source_hashes()
    for name in cost.FUNCTIONS:
        rows.append({
            "type": "function_result", "function": name, "crate_name": cost.CRATE,
            "verification_session": "", "proved": 1, "failed": 0, "unknown": 0,
            "timed_out": 0, "skipped": 0, "runtime_checked": 0, "total": 1,
            "cached": 0, "runtime_checks": {"overflow_checks": True, "ub_checks": False},
            "source_sha256": sources[name], "stable_ids": ["0123456789abcdef"],
            "results": [{"kind": "arithmetic_overflow_add", "outcome": "proved"}],
        })
    rows.append({
        "type": "coverage_summary", "crate_name": cost.CRATE, "verification_session": "",
        "eligible": cost.COUNT, "processed": cost.COUNT,
        "function_identities": {"schema": "trustc.coverage-function-identities.v1",
            "eligible_functions": list(cost.FUNCTIONS), "processed_functions": list(cost.FUNCTIONS)},
        "memory": {"schema": "trust-memory-summary/v1", "counters": {}},
    })
    rows.append({
        "type": "crate_summary", "crate_name": cost.CRATE, "verification_session": "",
        "functions_analyzed": cost.COUNT, "functions_verified": cost.COUNT,
        "total_proved": cost.COUNT, "total_failed": 0, "total_unknown": 0,
        "total_timed_out": 0, "total_skipped": 0, "total_runtime_checked": 0,
        "total_obligations": cost.COUNT,
    })
    return rows


def wire(rows):
    return "".join(cost.PREFIX + json.dumps(row) + "\n" for row in rows)


class CostPopulationTests(unittest.TestCase):
    def test_body_digest_and_local_ids_are_bound_to_the_fixed_item_and_exact_owner(self):
        original = records()
        self.assertEqual(original[0]["source_sha256"],
                         "6690238b74d53b26b32fa39857d5376c3dad77c39cfb1800c40d6185cbcbb7a9")
        report = cost.judge_wire(wire(original), "")
        self.assertEqual(report["obligation_keys"][0], cost.FUNCTIONS[0] + "#0123456789abcdef")
        for digest in ("b" * 64, original[1]["source_sha256"]):
            changed = copy.deepcopy(original)
            changed[0]["source_sha256"] = digest
            with self.assertRaisesRegex(cost.CostError, "body source identity differs"):
                cost.judge_wire(wire(changed), "")
        for identity in ("another_crate::foreign#0123456789abcdef", "0123456789abcde",
                         "0123456789abcdeF", "0123456789abcdef0"):
            changed = copy.deepcopy(original)
            changed[0]["stable_ids"] = [identity]
            with self.assertRaisesRegex(cost.CostError, "obligation identities"):
                cost.judge_wire(wire(changed), "")
        duplicate = copy.deepcopy(original)
        duplicate[0]["results"].append({"kind": "hardened_panic_boundary", "outcome": "proved"})
        duplicate[0].update(total=2, proved=2, stable_ids=["0123456789abcdef"] * 2)
        duplicate[-1].update(total_proved=501, total_obligations=501)
        with self.assertRaisesRegex(cost.CostError, "obligation identities"):
            cost.judge_wire(wire(duplicate), "")

    def test_complete_accounting_cannot_hide_one_empty_or_different_obligation(self):
        original = records()
        self.assertEqual(len(cost.judge_wire(wire(original), "")["functions"]), 500)
        empty = copy.deepcopy(original)
        empty[0].update(results=[], proved=0, total=0, stable_ids=[])
        empty[-1].update(functions_verified=499, total_proved=499, total_obligations=499)
        with self.assertRaisesRegex(cost.CostError, "real addition-overflow"):
            cost.judge_wire(wire(empty), "")
        changed = copy.deepcopy(original)
        changed[0]["results"][0]["kind"] = "irrelevant-tautology"
        with self.assertRaisesRegex(cost.CostError, "real addition-overflow"):
            cost.judge_wire(wire(changed), "")

    def test_accounting_consistent_partial_population_cannot_shrink_the_workload(self):
        partial = records()[1:]
        partial[-2].update(eligible=499, processed=499)
        partial[-2]["function_identities"].update(
            eligible_functions=list(cost.FUNCTIONS[1:]), processed_functions=list(cost.FUNCTIONS[1:]))
        partial[-1].update(functions_analyzed=499, functions_verified=499,
                           total_proved=499, total_obligations=499)
        with self.assertRaises(cost.CostError):
            cost.judge_wire(wire(partial), "")

    def test_disabled_cached_or_premise_bearing_work_is_not_a_fresh_cost_pass(self):
        for field, value in (("cached", 1), ("cached", False),
                             ("runtime_checks", {"overflow_checks": False}),
                             ("modeled_facts", ["argument-premise: assumed"]),
                             ("modeled_facts", {}), ("transport_budget", {"withheld": 1}),
                             ("source_sha256", None), ("stable_ids", [])):
            with self.subTest(field=field, value=value):
                rows = records()
                rows[0][field] = value
                with self.assertRaises(cost.CostError):
                    cost.judge_wire(wire(rows), "")

    def test_nonpassing_outcomes_do_not_get_credit_despite_consistent_summary(self):
        for outcome, aggregate in (("failed", "failed"), ("unknown", "unknown"),
                                   ("runtime_checked", "runtime_checked")):
            with self.subTest(outcome=outcome):
                rows = records()
                rows[0]["results"][0]["outcome"] = outcome
                rows[0].update(proved=0, **{aggregate: 1})
                rows[-1].update(functions_verified=499, total_proved=499,
                                **{"total_" + aggregate: 1})
                with self.assertRaises(cost.CostError):
                    cost.judge_wire(wire(rows), "")

    def test_nonfinite_or_overdeep_transport_refuses_before_accounting(self):
        original = wire(records())
        for extra in ('"extra":1e999,', '"extra":NaN,',
                      '"extra":' + '[' * 130 + '0' + ']' * 130 + ','):
            with self.subTest(extra=extra[:30]):
                malformed = original.replace('{"type":', '{' + extra + '"type":', 1)
                with self.assertRaises(cost.CostError):
                    cost.judge_wire(malformed, "")


class NativeResourceTests(unittest.TestCase):
    def test_just_above_five_cannot_round_into_a_pass_under_ambient_decimal_precision(self):
        text = "real 5.0000000000000000000000000001\n 399999999 maximum resident set size\n"
        with localcontext() as ambient:
            ambient.prec = 1
            measured = cost.native_time(text, "Darwin")
            self.assertGreater(Decimal(measured["wall_upper_bound_seconds"]), Decimal("5"))
            ordinary = cost.native_time("real 5.00\n 399999999 maximum resident set size\n", "Darwin")
            self.assertEqual(ordinary["wall_upper_bound_seconds"], "5.01")

    def test_existing_evidence_directory_is_never_overwritten_on_refusal(self):
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary) / "evidence"
            destination.mkdir()
            original = b'{"immutable":"prior failed result"}\n'
            (destination / "RESULT.json").write_bytes(original)
            with mock.patch.dict(os.environ, {}, clear=True), contextlib.redirect_stdout(io.StringIO()):
                code = cost.main(["--trustc", sys.executable, "--out-dir", str(destination)])
            self.assertEqual(code, 2)
            self.assertEqual((destination / "RESULT.json").read_bytes(), original)
            self.assertEqual(sorted(path.name for path in destination.iterdir()), ["RESULT.json"])

    def test_rss_units_and_conservative_decimal_wall_boundary(self):
        darwin = "real 4.99\nuser 1.00\nsys 0.01\n 399999999  maximum resident set size\n"
        measured = cost.native_time(darwin, "Darwin")
        self.assertEqual(measured["wall_upper_bound_seconds"], "5.00")
        self.assertEqual(measured["peak_rss_bytes"], 399999999)
        linux = cost.LINUX_TIME + " 4.99 390625\n"
        self.assertEqual(cost.native_time(linux, "Linux")["peak_rss_bytes"], 400000000)
        self.assertEqual(cost.native_time(darwin.replace("4.99", "5.00"), "Darwin")
                         ["wall_upper_bound_seconds"], "5.01")
        for bad in ("", darwin + darwin, darwin.replace("4.99", "NaN"),
                    darwin.replace("399999999", "0"), darwin + "real NaN\n",
                    darwin + "oops maximum resident set size\n"):
            with self.subTest(bad=bad[:40]):
                with self.assertRaises(cost.CostError):
                    cost.native_time(bad, "Darwin")
        with self.assertRaises(cost.CostError):
            cost.native_time(linux + cost.LINUX_TIME + " malformed\n", "Linux")

    def test_real_failed_process_keeps_raw_evidence_and_cannot_use_favorable_rows(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            fixture = root / "fixture.txt"
            text = wire(records())
            fixture.write_text(text)
            observed = root / "observed"
            observed.mkdir()
            command = [sys.executable, "-c",
                "from pathlib import Path; import sys; "
                "sys.stderr.buffer.write(Path(sys.argv[1]).read_bytes()); sys.exit(101)", str(fixture)]
            run = cost.run_recorded(command, observed, dict(os.environ), ())
            self.assertEqual(run["exit_code"], 101)
            self.assertEqual((observed / "stderr.raw").read_text(), text)
            self.assertEqual((observed / "stdout.raw").read_bytes(), b"")
            with self.assertRaisesRegex(cost.CostError, "exited 101"):
                cost.judge_run(run["exit_code"], text, "", "Darwin")


if __name__ == "__main__":
    unittest.main()
