#!/usr/bin/env python3
"""Offline self-test for scripts/trust_f1_ladder.py.

The ladder is a MEASUREMENT instrument: it needs a trustc that carries the
builtin trust-cg backend. What this pins needs none: the judging logic, driven
through a FAKE trustc (a Python script) that

  * answers `-vV`;
  * "compiles" an rlib by writing a file whose content is the value the rung
    will print, chosen from the rung's name and whether trust-cg was selected;
  * refuses, with an F1-style refusal census or with a session fatal, a rung
    whose name says so;
  * "links" the driver by writing an executable that prints that value.

Cases: a rung that agrees is OK; a rung whose trust-cg build prints something
else is MISMATCH and fails the run; a refused rung is REFUSED, its census
classes are tallied, and the run still exits 0; an unclassified fatal is kept
under its error line; a rung LLVM cannot build is ORACLE and fails the run;
`--mode default` runs the strict column and the verified LLVM column and
passes neither a verify-off flag; `--mode fixture-checked` keeps overflow
checks on; `--consumer lir` selects that consumer on every trust-cg build, is
recorded, and reaches no LLVM build;
`--expect` pins the OK count in both directions; a trustc
without the backend is refused before measuring; an empty corpus is a usage
error, not a green zero.

Run directly (`python3 -B scripts/tests/trust_f1_ladder_test.py`) or through
`scripts/check_script_tests.sh`.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "trust_f1_ladder.py"
_spec = importlib.util.spec_from_file_location("trust_f1_ladder", SCRIPT)
ladder = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(ladder)

FAKE_TRUSTC = r'''#!/usr/bin/env python3
import os, sys
argv = sys.argv[1:]
with open(os.environ["FAKE_TRUSTC_LOG"], "a") as log:
    log.write(" ".join(argv) + "\n")
if argv == ["-vV"]:
    print("rustc 9.9.9-fake (trustc fake)")
    sys.exit(0)
cg = "-Zcodegen-backend=trust-cg" in argv
if "--print=supported-crate-types" in argv:
    if os.environ.get("FAKE_TRUSTC_NO_BACKEND"):
        sys.stderr.write("error: failed to find a codegen-backends folder\n")
        sys.exit(1)
    print("rlib")
    sys.exit(0)
if "-o" in argv:  # driver link
    rlib = [a for a in argv if a.startswith("rung=")][0][len("rung="):]
    value = open(rlib).read()
    if "-Zprint-mono-items=yes" in argv and "driverblank" not in rlib:
        if "driverregen" in rlib:
            print("MONO_ITEM fn rung::rung @@ fake[Internal]")
        else:
            print("MONO_ITEM fn main @@ fake[External]")
    exe = argv[argv.index("-o") + 1]
    with open(exe, "w") as f:
        f.write("#!/bin/sh\n%secho %s-$1\n" % ("sleep 30\n" if "slow" in rlib else "", value))
    os.chmod(exe, 0o755)
    sys.exit(0)
src = argv[0]
name = os.path.basename(src)
out = argv[argv.index("--out-dir") + 1]
if "oraclefail" in name:
    sys.stderr.write("error: llvm cannot build this\n")
    sys.exit(1)
if cg and "refuse" in name:
    sys.stderr.write("error: trust-cg F1 refused 3 of 4 reachable function(s)\n"
                     "     2 ( 66.7%) [upstream-body] bodies from another crate\n"
                     "     1 ( 33.3%) [unfaithful-panic] reaches an Assert\n")
    sys.exit(1)
if cg and "fatal" in name:
    sys.stderr.write("error: codegen backend trust-cg cannot emit crate type bin\n")
    sys.exit(1)
if cg and os.path.basename(os.path.dirname(src)) == "lean":
    if "missing" not in name:
        counts = (int("mirread" in name), int("inventoryread" in name), int("recorderread" in name))
        sys.stderr.write("`clean_origin_mir` reached: codegen %d, inventory %d, recorder %d (plan step 3)\n" % counts)
value = "wrong" if (cg and "wrong" in name) else "right"
if cg and "unknown" in name and "-Ztrust-cg-output-gate=allow-unknown" not in argv:
    sys.stderr.write("error: strict gate\n     1 (100.0%) [f1-output-gate] Unknown\n")
    sys.exit(1)
with open(os.path.join(out, "librung.rlib"), "w") as f:
    f.write(value)
'''


class LadderTest(unittest.TestCase):
    @unittest.skipUnless(os.name == "posix", "process-group ownership is Unix-only")
    def test_run_retires_descendants_on_timeout_and_normal_exit(self) -> None:
        import fcntl

        program = self.tmp / "descendant.py"
        program.write_text('''
import fcntl, subprocess, sys, time
from pathlib import Path
mode, lock, ready, stop = sys.argv[1:]
lock, ready, stop = map(Path, (lock, ready, stop))
if mode == "child":
    with lock.open("a") as held:
        fcntl.flock(held, fcntl.LOCK_EX)
        ready.write_text("locked")
        deadline = time.monotonic() + 15
        while not stop.exists() and time.monotonic() < deadline:
            time.sleep(.02)
else:
    subprocess.Popen([sys.executable, __file__, "child", str(lock), str(ready), str(stop)],
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    deadline = time.monotonic() + 5
    while not ready.exists():
        if time.monotonic() > deadline:
            raise RuntimeError("descendant never acquired its lock")
        time.sleep(.02)
    print("captured stdout", flush=True)
    print("captured stderr", file=sys.stderr, flush=True)
    if mode == "timeout":
        time.sleep(60)
''')
        for mode in ("timeout", "exit"):
            with self.subTest(mode=mode):
                lock = self.tmp / (mode + ".lock")
                ready = self.tmp / (mode + ".ready")
                stop = self.tmp / (mode + ".stop")

                def released() -> bool:
                    with lock.open("a") as held:
                        try:
                            fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        except BlockingIOError:
                            return False
                        return True

                try:
                    rc, stdout, stderr = ladder.run(
                        [sys.executable, str(program), mode, str(lock), str(ready), str(stop)],
                        2 if mode == "timeout" else 5,
                    )
                    self.assertTrue(ready.exists(), "the actual descendant must have run")
                    self.assertEqual(rc, None if mode == "timeout" else 0)
                    self.assertEqual(stdout, "" if mode == "timeout" else "captured stdout\n")
                    self.assertIn("captured stderr", stderr)
                    deadline = time.monotonic() + 1
                    while not released() and time.monotonic() < deadline:
                        time.sleep(.02)
                    self.assertTrue(released(), "run returned with its descendant still alive")
                finally:
                    # Release this fixture even against the broken runner. No
                    # numeric PID is signalled, and the fixture is self-bounded.
                    stop.write_text("stop")
                    deadline = time.monotonic() + 2
                    while not released() and time.monotonic() < deadline:
                        time.sleep(.02)
                    self.assertTrue(released(), "fixture descendant did not finish")

    @unittest.skipUnless(os.name == "posix", "descriptor transport is Unix-only")
    def test_run_preserves_original_scheduler_and_closes_unadvertised_fds(self) -> None:
        read, write = os.pipe()
        unrelated_read, unrelated_write = os.pipe()
        try:
            env = {"CARGO_MAKEFLAGS": f"-j --jobserver-auth={read},{write}"}
            probe = r"""
import os, stat, sys
r, w, unrelated = map(int, sys.argv[1:])
a, b = os.fstat(r), os.fstat(w)
assert stat.S_ISFIFO(a.st_mode) and stat.S_ISFIFO(b.st_mode)
try: os.fstat(unrelated)
except OSError: pass
else: raise AssertionError("unadvertised descriptor leaked")
print(a.st_dev, a.st_ino, b.st_dev, b.st_ino)
"""
            with patch.dict(os.environ, env, clear=True):
                rc, stdout, stderr = ladder.run(
                    [sys.executable, "-c", probe, str(read), str(write), str(unrelated_read)], 10
                )
            self.assertEqual(rc, 0, stderr)
            original_read, original_write = os.fstat(read), os.fstat(write)
            self.assertEqual(
                stdout.strip(),
                f"{original_read.st_dev} {original_read.st_ino} {original_write.st_dev} {original_write.st_ino}",
            )
        finally:
            for fd in (read, write, unrelated_read, unrelated_write):
                os.close(fd)

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.trustc = self.tmp / "trustc"
        self.trustc.write_text(FAKE_TRUSTC)
        self.trustc.chmod(0o755)
        self.log = self.tmp / "argv.log"
        os.environ["FAKE_TRUSTC_LOG"] = str(self.log)
        self.corpus = self.tmp / "corpus"
        (self.corpus / "programs").mkdir(parents=True)
        (self.corpus / "micro").mkdir()
        (self.corpus / "lean").mkdir()
        (self.corpus / "lean" / "l0_good.rs").write_text("// fake\n")
        (self.corpus / "driver.rs").write_text("fn main() {}\n")

    def tearDown(self) -> None:
        os.environ.pop("FAKE_TRUSTC_LOG", None)
        self._tmp.cleanup()

    def rung(self, set_name: str, name: str) -> None:
        (self.corpus / set_name / f"{name}.rs").write_text("// fake\n")

    def go(self, *extra: str) -> tuple[int, str, str, dict]:
        out = self.tmp / "out"
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            rc = ladder.main(["--trustc", str(self.trustc), "--out-dir", str(out), "--corpus", str(self.corpus), *extra])
        results = json.loads((out / "results.json").read_text()) if (out / "results.json").exists() else {}
        return rc, stdout.getvalue(), stderr.getvalue(), results

    def test_ok_refused_and_gate_columns(self) -> None:
        self.rung("programs", "p1_good")
        self.rung("programs", "p2_refuse")
        self.rung("programs", "p3_unknown")
        self.rung("micro", "m1_fatal")
        rc, stdout, _, results = self.go("--mode", "fixture")
        self.assertEqual(rc, 0, "refusals are a measurement, not a failure")
        strict = results["summary"]["f1-strict"]
        relaxed = results["summary"]["f1-allow-unknown"]
        self.assertEqual(strict["sets"]["programs"], {"total": 3, "OK": 1, "REFUSED": 2})
        self.assertEqual(relaxed["sets"]["programs"], {"total": 3, "OK": 2, "REFUSED": 1})
        self.assertEqual(strict["refusal_classes"]["[upstream-body]"], 2)
        self.assertEqual(strict["refusal_classes"]["[unfaithful-panic]"], 1)
        self.assertEqual(strict["refusal_classes"]["[f1-output-gate]"], 1)
        fatal = [k for k in strict["refusal_classes"] if k.startswith("(unclassified)")]
        self.assertEqual(len(fatal), 1, "a session fatal outside the census is kept, not dropped")
        self.assertIn("cannot emit crate type bin", fatal[0])
        self.assertEqual(
            ladder.refusal_classes("error: verification incomplete for `a::b`: 2 obligation(s)\n"),
            ladder.refusal_classes("error: verification incomplete for `c::d`: 14 obligation(s)\n"),
            "an unclassified refusal is keyed by message shape, not by function name or count",
        )
        self.assertIn("f1-strict programs: 1/3 OK", stdout)
        self.assertIn("rustc 9.9.9-fake", stdout)

    def test_mismatch_fails_the_run(self) -> None:
        self.rung("programs", "p1_good")
        self.rung("programs", "p2_wrong")
        self.rung("micro", "m1_good")
        rc, _, stderr, results = self.go("--mode", "fixture")
        self.assertEqual(rc, 1)
        self.assertIn("p2_wrong f1-strict: MISMATCH", stderr)
        row = [r for r in results["results"] if r["rung"] == "p2_wrong"][0]
        self.assertEqual(row["lanes"]["f1-strict"]["diff"]["0"], [[0, "right-0"], [0, "wrong-0"]])

    def test_oracle_failure_judges_no_lane_and_fails(self) -> None:
        self.rung("programs", "p1_oraclefail")
        self.rung("micro", "m1_good")
        rc, _, stderr, results = self.go("--mode", "fixture")
        self.assertEqual(rc, 1)
        self.assertIn("ORACLE", stderr)
        self.assertEqual(results["summary"]["f1-strict"]["sets"]["programs"], {"total": 1, "ORACLE": 1})

    def test_an_oracle_that_cannot_finish_an_input_judges_nothing(self) -> None:
        self.rung("programs", "p1_slow")
        self.rung("micro", "m1_good")
        real_run = ladder.run
        ladder.run = lambda cmd, timeout: real_run(cmd, 0.5 if timeout == 20 else timeout)
        try:
            rc, _, stderr, results = self.go("--mode", "fixture")
        finally:
            ladder.run = real_run
        self.assertEqual(rc, 1, "a timeout compared with a timeout must not read as OK")
        self.assertIn("RUN-TIMEOUT", stderr)
        self.assertEqual(results["summary"]["f1-strict"]["sets"]["programs"], {"total": 1, "ORACLE": 1})

    def test_default_mode_is_verification_on_and_strict_only(self) -> None:
        self.rung("programs", "p1_good")
        self.rung("micro", "m1_good")
        rc, _, _, results = self.go()
        self.assertEqual(rc, 0)
        self.assertEqual(list(results["summary"]), ["f1-strict", "llvm-verified"])
        argv = self.log.read_text()
        subject_lines = [line for line in argv.splitlines() if "--out-dir" in line]
        self.assertTrue(subject_lines)
        for line in subject_lines:
            self.assertIn("-Coverflow-checks=on", line)
            self.assertNotIn("allow-unknown", line)
            if "-Zcodegen-backend=trust-cg" in line:
                self.assertNotIn("-Ztrust-verify=off", line, "default mode must leave verification on for the subject")
        llvm_lines = [line for line in subject_lines if "-Zcodegen-backend=trust-cg" not in line]
        self.assertTrue(any("-Ztrust-verify=off" in line for line in llvm_lines), "the oracle is output-only and never verified")
        self.assertTrue(any("-Ztrust-verify=off" not in line for line in llvm_lines), "llvm-verified is a default LLVM build")
        self.assertTrue(any("-Ztrust-cg-f1-backend=compiler" in line for line in subject_lines), "the R-5 consumer is the subject")

    def test_consumer_option_selects_the_backend_consumer_and_is_recorded(self) -> None:
        self.rung("programs", "p1_good")
        self.rung("micro", "m1_good")
        rc, stdout, _, results = self.go("--mode", "fixture", "--consumer", "lir")
        self.assertEqual(rc, 0)
        self.assertEqual(results["consumer"], "lir")
        self.assertIn("consumer: lir", stdout)
        cg_lines = [line for line in self.log.read_text().splitlines() if "-Zcodegen-backend=trust-cg" in line and "--out-dir" in line]
        self.assertTrue(cg_lines)
        for line in cg_lines:
            self.assertIn("-Ztrust-cg-f1-backend=lir", line)
            self.assertNotIn("-Ztrust-cg-f1-backend=compiler", line)
        self.log.write_text("")
        rc, stdout, _, results = self.go()
        self.assertEqual(results["consumer"], "compiler")
        for line in self.log.read_text().splitlines():
            self.assertNotIn("-Ztrust-cg-f1-backend=lir", line)
            if "-Zcodegen-backend=trust-cg" not in line:
                self.assertNotIn("-Ztrust-cg-f1-backend", line, "an LLVM build takes no consumer flag")

    def test_fixture_checked_keeps_overflow_checks(self) -> None:
        self.rung("programs", "p1_good")
        self.rung("micro", "m1_good")
        rc, _, _, results = self.go("--mode", "fixture-checked")
        self.assertEqual(rc, 0)
        self.assertEqual(list(results["summary"]), ["f1-strict", "f1-allow-unknown"])
        for line in [line for line in self.log.read_text().splitlines() if "--out-dir" in line]:
            self.assertIn("-Coverflow-checks=on", line)
            self.assertIn("-Ztrust-verify=off", line)

    def test_expect_pins_the_count_both_ways(self) -> None:
        self.rung("programs", "p1_good")
        self.rung("programs", "p2_refuse")
        self.rung("micro", "m1_good")
        self.assertEqual(self.go("--mode", "fixture", "--expect", "f1-strict=3")[0], 0)
        rc, _, stderr, _ = self.go("--mode", "fixture", "--expect", "f1-strict=4")
        self.assertEqual(rc, 1)
        self.assertIn("f1-strict: 3 OK, expected 4", stderr)
        self.assertEqual(self.go("--mode", "fixture", "--expect", "f1-strict=1")[0], 1, "an unrecorded improvement also fails the pin")
        self.assertEqual(self.go("--expect", "f1-allow-unknown=1")[0], 2, "a lane the mode does not run is a usage error")
        self.assertEqual(self.go("--mode", "fixture", "--expect", "programs:f1-strict=1", "--expect", "micro:f1-strict=1")[0], 0)
        rc, _, stderr, _ = self.go("--mode", "fixture", "--expect", "programs:f1-strict=2")
        self.assertEqual(rc, 1)
        self.assertIn("programs:f1-strict: 1 OK, expected 2", stderr)
        self.assertEqual(self.go("--mode", "fixture", "--set", "micro", "--expect", "programs:f1-strict=1")[0], 2, "a set that is not run cannot be pinned")

    def test_missing_backend_is_not_a_green_all_refused_run(self) -> None:
        self.rung("programs", "p1_good")
        self.rung("micro", "m1_good")
        os.environ["FAKE_TRUSTC_NO_BACKEND"] = "1"
        try:
            rc, _, stderr, results = self.go("--mode", "fixture")
        finally:
            del os.environ["FAKE_TRUSTC_NO_BACKEND"]
        self.assertEqual(rc, 2)
        self.assertIn("cannot load the trust-cg backend", stderr)
        self.assertEqual(results, {}, "nothing is measured")

    def test_lean_requires_direct_path_evidence(self) -> None:
        self.rung("lean", "l1_missing")
        self.rung("lean", "l2_mirread")
        self.rung("lean", "l3_driverregen")
        self.rung("lean", "l4_driverblank")
        self.rung("lean", "l5_inventoryread")
        self.rung("lean", "l6_recorderread")
        rc, _, stderr, results = self.go("--set", "lean")
        self.assertEqual(rc, 1)
        self.assertIn("PATH", stderr)
        self.assertEqual(results["summary"]["f1-strict"]["sets"]["lean"],
                         {"total": 7, "OK": 1, "PATH": 6})
        self.assertEqual(results["summary"]["llvm-verified"]["sets"]["lean"],
                         {"total": 7, "OK": 7})

    def test_empty_corpus_is_a_usage_error(self) -> None:
        self.rung("programs", "p1_good")
        rc, _, stderr, _ = self.go("--mode", "fixture")
        self.assertEqual(rc, 2)
        self.assertIn("no rungs", stderr)


if __name__ == "__main__":
    unittest.main()
