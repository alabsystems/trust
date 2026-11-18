#!/usr/bin/env python3
"""Inject process failures into the maintained battery's actual Bash lanes.

No compiler, solver, submodule build or network is used. These tests qualify
harness accounting, never compiler proof or runtime acceptance.
"""

import json
import os
from pathlib import Path
import subprocess
import sys
import shlex
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
HARNESS = ROOT / "tests/e2e_two_language_programs.sh"
LIB_DIAG = "error: Trust strict verification failed for `lib::double`: 1 obligation(s) were not fully verified\n"
BIN_DIAG = "error: Trust strict verification failed for `main::main`: 1 obligation(s) were not fully verified\n"


# A `#!{sys.executable}` shebang cannot carry an interpreter path with spaces (atpkg's python
# lives under `Application Support/`): exec splits it and the fake never runs. This sh/python
# polyglot execs the interpreter quoted and keeps argv[0] as the fake's own path.
PYTHON_SHEBANG = f'#!/bin/sh\n""":"\nexec "{sys.executable}" "$0" "$@"\n":"""\n'


def wire(function="lib::double", kind="postcondition", outcome="failed", summary=True):
    rows = [{"type": "function_result", "function": function,
             "results": [{"obligation_id": "vc:fixture:" + kind,
                          "kind": kind, "outcome": outcome}]}]
    if summary:
        rows.append({"type": "crate_summary", "functions_analyzed": 1,
                     "functions_verified": int(outcome == "proved"),
                     "total_proved": int(outcome == "proved"),
                     "total_failed": int(outcome == "failed"),
                     "total_unknown": int(outcome == "unknown"),
                     "total_timed_out": 0, "total_skipped": 0,
                     "total_runtime_checked": 0, "total_obligations": 1})
    return "".join("TRUST_JSON:" + json.dumps(row) + "\n" for row in rows)


def outcome(text, status=1):
    return {"text": text, "status": status}


class BatteryRefusals(unittest.TestCase):
    def run_lane(self, args, plain, json_run=None, lone=None):
        harness = HARNESS.read_text()
        scrub = harness[harness.index("scrub() {"):harness.index("# ---- the frontier:")]
        lanes = harness[harness.index("known_red_reason() {"):harness.index('IR_JUDGE=')]
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            executable = temp / "fake-tool"
            executable.write_text(PYTHON_SHEBANG + '''
import json, os, sys
from pathlib import Path
scenario = json.loads(Path(os.environ["BATTERY_SCENARIO"]).read_text())
key = "plain"
if "-Ztrust-verify-output=json" in sys.argv:
    key = "wire"
elif sys.argv[1:] == ["trust", "check", "B.lean"]:
    key = "lone"
result = scenario[key]
sys.stderr.write(result["text"])
sys.exit(result["status"])
''')
            executable.chmod(0o755)
            # macOS holds the FIRST exec of a newly written executable while it is
            # assessed: 6-10 s measured on a loaded host (d9cbc6f930, targo-trust's fake
            # trustd; ff0a855ac0 pays the same for a fake targo). Pay it here, untimed,
            # so the 15 s budget below times the lane rather than the assessment. The
            # scenario-less run exits non-zero before reading anything; only the exec counts.
            subprocess.run([str(executable)], env={"PATH": os.environ.get("PATH", "")},
                           capture_output=True, check=False, timeout=300)
            scenario = temp / "scenario.json"
            scenario.write_text(json.dumps({"plain": plain,
                                            "wire": json_run or plain,
                                            "lone": lone or plain}))
            program = '''set -uo pipefail
TRUST_ROOT=$1
SCRATCH=$2
TRUSTC=$3
TARGO=$3
shift 3
ROWS_DIR="$TRUST_ROOT/tests/two-language-programs"
WIRE_GRADER="$ROWS_DIR/wire_grade.py"
WIRE_READER="$TRUST_ROOT/scripts/lib/trust_program_wire.py"
KNOWN_RED=""
ONLY=""
LANE=""
''' + scrub + lanes + '''
"$@"
[ "$PASSES" = 1 ] && [ "$FAILS" = 0 ] && [ "$REDS" = 0 ] && [ "$UNEXPECTED" = 0 ]
'''
            env = dict(os.environ, BATTERY_SCENARIO=str(scenario))
            return subprocess.run(["bash", "-c", program, "refusal-regression",
                                   str(ROOT), str(temp), str(executable), *args],
                                  text=True, capture_output=True, env=env, timeout=15)

    def assert_verdict(self, result, passes):
        self.assertEqual(result.returncode == 0, passes, result.stdout + result.stderr)
        self.assertIn("PASS" if passes else "FAIL", result.stdout)

    def lib(self, plain=None, json_run=None, expect="refused"):
        args = ["row_trustc_lib", "r07_rust_contract_refuted_strict", expect]
        if expect == "refused":
            args.append("lib::double=postcondition")
        return self.run_lane(args, plain or outcome(LIB_DIAG),
                             json_run or outcome(LIB_DIAG + wire()))

    def test_false_contract_requires_its_failed_wire_row(self):
        self.assert_verdict(self.lib(), True)
        for text in [LIB_DIAG, LIB_DIAG + wire(function="lib::other"),
                     LIB_DIAG + wire(kind="precondition"),
                     LIB_DIAG + wire(outcome="unknown"),
                     LIB_DIAG + wire(summary=False),
                     (LIB_DIAG + wire()).replace('"total_failed": 1', '"total_failed": 0')]:
            with self.subTest(text=text):
                self.assert_verdict(self.lib(json_run=outcome(text)), False)

    def test_false_contract_rejects_unrelated_errors_and_abnormal_exit(self):
        for text, status in [("error: expected expression\n", 1),
                             ("error: cannot load shared library\n", 127),
                             (LIB_DIAG, 101), (LIB_DIAG, 137),
                             (LIB_DIAG + "thread 'rustc' panicked at fixture.rs:1\n", 1),
                             (LIB_DIAG + "error: internal compiler error\n", 1)]:
            with self.subTest(status=status, text=text):
                self.assert_verdict(self.lib(plain=outcome(text, status)), False)

    def test_false_contract_rejects_wire_crash_and_success_exit(self):
        for text, status in [(LIB_DIAG + wire(), 0), (LIB_DIAG + wire(), 101),
                             (LIB_DIAG + wire() + "thread 'rustc' panicked at fixture.rs:1\n", 1)]:
            with self.subTest(status=status, text=text):
                self.assert_verdict(self.lib(json_run=outcome(text, status)), False)

    def test_library_positive_still_requires_success_and_clean_wire(self):
        self.assert_verdict(self.lib(plain=outcome("", 0),
                                      json_run=outcome(wire(outcome="proved"), 0), expect="ok"), True)
        self.assert_verdict(self.lib(plain=outcome("", 0),
                                      json_run=outcome(wire(outcome="proved"), 101), expect="ok"), False)

    def test_bin_negative_requires_normal_exit_and_complete_wire(self):
        args = ["row_trustc_refused", "r27_println_verify_on_violated_requires",
                "Trust strict verification failed for `main::main`", "main::main=precondition"]
        good = BIN_DIAG + wire(function="main::main", kind="precondition")
        self.assert_verdict(self.run_lane(args, outcome(good)), True)
        for text, status in [(good, 101), (good, 137),
                             (good + "error: internal compiler error\n", 1),
                             (BIN_DIAG + wire(function="main::main", kind="precondition", summary=False), 1)]:
            with self.subTest(status=status, text=text):
                self.assert_verdict(self.run_lane(args, outcome(text, status)), False)

    def test_lean_negative_requires_named_goal_rejection(self):
        args = ["row_lean", "r05_lean_standalone_rejected", "Bad.lean", "REJECTED", "unsolved goals"]
        good = "error: Bad.lean: unsolved goals\nREJECTED Bad.lean\n"
        self.assert_verdict(self.run_lane(args, outcome(good)), True)
        for text, status in [(good, 101), (good + "thread 'main' panicked at test.rs:1\n", 1),
                             ("error: dependency missing\nREJECTED Bad.lean\n", 1)]:
            with self.subTest(status=status, text=text):
                self.assert_verdict(self.run_lane(args, outcome(text, status)), False)

    def test_citation_audit_refusal_names_the_citation_and_function(self):
        args = ["row_trustc_audit_refused", "r43_alab_a3d_decide_link_false_constant",
                "lib::octree_depth_fits", "depth_fits_is_span_fits"]
        good = ("error: citation `depth_fits_is_span_fits` failed the strict Clean "
                "statement/certification audit: strict certification audit failed: "
                "[TermRejected { error: TypeMismatch }]\n"
                "error: Trust strict verification failed for `lib::octree_depth_fits`\n")
        self.assert_verdict(self.run_lane(args, outcome(good)), True)
        # cb1/B2 (2026-09-28): a refuted POSTCONDITION goal leads the error.
        post = good.replace(
            "statement/certification audit: ",
            "statement/certification audit against this postcondition with `result` bound "
            "to the imported definition of `octree_depth_fits`: ")
        self.assert_verdict(self.run_lane(args, outcome(post)), True)
        for text, status in [(good, 0), (good, 101), (good, 127), (good, 137),
                             (post.replace("definition of `octree_depth_fits`",
                                           "definition of `other_fn`"), 1),
                             (post.replace(" against this postcondition", " against this goal"), 1),
                             (good.replace("depth_fits_is_span_fits", "other_citation"), 1),
                             (good.replace("lib::octree_depth_fits", "lib::other"), 1),
                             (good.replace("TypeMismatch", "UnknownIdentifier"), 1),
                             ("error: expected expression\n", 1),
                             (good + "error: internal compiler error\n", 1),
                             (good + "thread 'rustc' panicked at fixture.rs:1\n", 1)]:
            with self.subTest(status=status, text=text):
                self.assert_verdict(self.run_lane(args, outcome(text, status)), False)

    def test_maintained_negative_registrations_have_named_expectations(self):
        for line in HARNESS.read_text().splitlines():
            if not line.startswith("row_"):
                continue
            args = shlex.split(line, comments=True)
            with self.subTest(row=args):
                if args[0] == "row_trustc_lib" and args[2] == "refused":
                    self.assertEqual(len(args), 4)
                    self.assertIn("=", args[3])
                if args[0] == "row_lean" and args[3] == "REJECTED":
                    self.assertEqual(len(args), 5)
                    self.assertTrue(args[4])
                if args[0] == "row_trustc_audit_refused":
                    self.assertEqual(len(args), 4)
                    self.assertTrue(args[2] and args[3])

    def test_false_span_requires_its_arithmetic_rejection(self):
        args = ["row_lean", "r44_alab_a3d_decide_link_false_span", "FalseSpan.lean",
                "REJECTED", "Tactic failed: decide: comparison is false"]
        good = ("error: FalseSpan.lean:41:1: error: `span_fwd` did not elaborate: "
                "Tactic failed: decide: comparison is false\nREJECTED FalseSpan.lean\n")
        self.assert_verdict(self.run_lane(args, outcome(good)), True)
        for text, status in [(good, 101), (good.replace("comparison is false", "unknown tactic"), 1),
                             (good + "error: internal compiler error\n", 1),
                             (good.replace("REJECTED FalseSpan.lean", "REJECTED Bad.lean"), 1)]:
            with self.subTest(status=status, text=text):
                self.assert_verdict(self.run_lane(args, outcome(text, status)), False)

    def test_multi_file_lone_rejection_requires_the_missing_citation(self):
        args = ["row_lean_multi", "r17_lean_multi_file_citation", "PROVED", "A.lean", "B.lean"]
        joint = outcome("PROVED A.lean\nPROVED B.lean\n", 0)
        good = "error: B.lean: Unknown identifier: base\nREJECTED B.lean\n"
        self.assert_verdict(self.run_lane(args, joint, lone=outcome(good)), True)
        for text, status in [(good, 101), (good, 127),
                             (good + "thread 'main' panicked at test.rs:1\n", 1),
                             ("error: missing library\n", 1),
                             ("error: B.lean: Unknown identifier: unrelated\nREJECTED B.lean\n", 1),
                             ("error: B.lean: Unknown identifier: base_other\nREJECTED B.lean\n", 1),
                             ("error: Unknown identifier: base\nREJECTED A.lean\n", 1)]:
            with self.subTest(status=status, text=text):
                self.assert_verdict(self.run_lane(args, joint, lone=outcome(text, status)), False)

    def test_targo_false_twin_rejects_crash_after_expected_diagnostic(self):
        args = ["row_targo_file", "r30_targo_trust_check_lean_false_twin", "refused"]
        good = ("error: clause was not discharged by definitional equality\n"
                "[PROVED] honest (clean-kernel-citation)\nGate: FAIL\n")
        self.assert_verdict(self.run_lane(args, outcome(good)), True)
        for text, status in [(good, 101), (good + "thread 'main' panicked at test.rs:1\n", 1)]:
            with self.subTest(status=status, text=text):
                self.assert_verdict(self.run_lane(args, outcome(text, status)), False)


if __name__ == "__main__":
    unittest.main()
