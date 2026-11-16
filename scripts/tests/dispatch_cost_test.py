"""scripts/dispatch_cost.py: the statistics, the refusals and the probe's
command line, with no GPU and no build."""
from __future__ import annotations

import contextlib
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts import dispatch_cost as dc  # noqa: E402

HEADER = "device Test GPU\nunified 1\nqos user-interactive\nwarm 7\n"


def samples(series, calls):
    """A sample per call: visible one below it, and a GPU time that varies."""
    return "".join(f"S {series} {call} {call - 1} {call // 7}\n" for call in calls)


def lines(series, triples):
    return "".join(f"S {series} {call} {visible} {gpu}\n" for call, visible, gpu in triples)


def run(text, *flags):
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder) / "samples.txt"
        path.write_bytes(text if isinstance(text, bytes) else text.encode("utf-8"))
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = dc.main(["--samples", str(path), *flags])
    return status, out.getvalue(), err.getvalue()


class Percentile(unittest.TestCase):
    def test_nearest_rank(self):
        ordered = list(range(1, 1001))
        self.assertEqual(dc.percentile(ordered, 0.5), 500)
        self.assertEqual(dc.percentile(ordered, 0.999), 999)
        self.assertEqual(dc.percentile(ordered, 1.0), 1000)
        self.assertEqual(dc.percentile(ordered, 0.0001), 1)

    def test_a_fractional_rank_rounds_up(self):
        # Rank 2.5 is the third sample; rounding half to even gives the second.
        self.assertEqual(dc.median([1, 2, 3, 4, 5]), 3)
        # Rank 1598.4 is sample 1599; rounding gives 1598.
        self.assertEqual(dc.percentile(list(range(1, 1601)), 0.999), 1599)
        # Rank 999.999 is sample 1000; truncating gives 999.
        self.assertEqual(dc.percentile(list(range(1, 1002)), 0.999), 1000)
        self.assertEqual(dc.percentile(list(range(1, 12)), 0.1), 2)

    def test_the_tail_is_a_sample_not_an_interpolation(self):
        ordered = [10] * 1998 + [70, 9000]
        self.assertEqual(dc.percentile(ordered, 0.999), 10)
        # 1998 of these 2000 samples are at or below 70: that is 99.9% of them.
        self.assertEqual(dc.percentile([10] * 1997 + [70, 80, 9000], 0.999), 70)
        self.assertEqual(dc.percentile([10] * 997 + [70, 80, 9000], 0.999), 80)

    def test_median_of_an_even_count_is_the_lower_middle(self):
        self.assertEqual(dc.median([1, 2, 3, 4]), 2)
        self.assertEqual(dc.median([7]), 7)

    def test_refuses_no_samples_and_bad_fractions(self):
        with self.assertRaises(ValueError):
            dc.percentile([], 0.5)
        for fraction in (0.0, -0.1, 1.5):
            with self.assertRaises(ValueError):
                dc.percentile([1], fraction)


class Parse(unittest.TestCase):
    def test_reads_header_and_series_in_order(self):
        header, series = dc.parse(HEADER + "S hot 9 8 1\nS idle10 30 20 2\nS hot 11 11 0\n")
        self.assertEqual(header, {"device": "Test GPU", "unified": "1",
                                  "qos": "user-interactive", "warm": "7"})
        self.assertEqual(series, {"hot": [(9, 8, 1), (11, 11, 0)], "idle10": [(30, 20, 2)]})

    def test_refuses_what_the_probe_does_not_print(self):
        for bad in ("S hot 9 8\n", "S hot 9 8 x\n", "S hot 8 9 1\n", "S hot -1 -2 1\n",
                    "S hot 9 8 -1\n", "S hot 1_0 9 1\n", "S hot +9 8 1\n", "S hot 09 8 1\n",
                    "S hot 9 8 ²\n", "S hot ٩ 8 1\n", "S hot 9  8 1\n",
                    "note hello\n", "device Again\n"):
            with self.subTest(bad=bad), self.assertRaises(dc.Malformed):
                dc.parse(HEADER + bad)

    def test_refuses_a_series_the_probe_does_not_print(self):
        for name in ("cold", "idle", "idlex", "hot2", "spin", "spin-1", "sleep5", "idle01",
                     "idle²", "idle٣"):
            with self.subTest(name=name), self.assertRaises(dc.Malformed):
                dc.parse(HEADER + f"S {name} 9 8 1\n")

    def test_refuses_a_missing_header_field(self):
        with self.assertRaises(dc.Malformed) as caught:
            dc.parse("device Test GPU\nunified 1\nS hot 9 8 1\n")
        self.assertIn("qos, warm", str(caught.exception))

    def test_refuses_header_values_the_probe_does_not_print(self):
        for old, new in (("unified 1", "unified yes"), ("unified 1", "unified 2"),
                         ("warm 7", "warm many"), ("warm 7", "warm ²"),
                         ("qos user-interactive", "qos background")):
            with self.subTest(new=new), self.assertRaises(dc.Malformed):
                dc.parse(HEADER.replace(old, new) + "S hot 9 8 1\n")
        dc.parse(HEADER.replace("qos user-interactive", "qos default") + "S hot 9 8 1\n")


class Summarize(unittest.TestCase):
    def text(self, hot=None, extra=""):
        hot = list(range(100, 100 + 2000)) if hot is None else hot
        return HEADER + samples("hot", hot) + extra

    def test_the_row(self):
        summary = dc.summarize(*dc.parse(self.text(
            extra=samples("idle100", [5000, 7000, 6000]) + samples("idle1", [1000, 1100])
            + samples("spin100", [1200]))))
        self.assertEqual(summary["samples"], 2000)
        self.assertEqual(summary["warm_up"], 7)
        self.assertEqual(summary["round_trip_ns"],
                         {"median": 1099, "p99_9": 2097, "max": 2099, "min": 100})
        self.assertEqual(summary["visible_median_ns"], 1098)
        # The GPU column is call // 7 over calls 100..2099: ranks 200, 1000, 1800.
        self.assertEqual(summary["gpu_ns"], {"p10": 299 // 7, "median": 157, "p90": 1899 // 7})
        self.assertEqual(summary["wake_up"], [
            {"thread": "sleep", "idle_ms": 1, "samples": 2, "median_ns": 1000, "max_ns": 1100,
             "penalty_ns": -99},
            {"thread": "sleep", "idle_ms": 100, "samples": 3, "median_ns": 6000, "max_ns": 7000,
             "penalty_ns": 4901},
            {"thread": "spin", "idle_ms": 100, "samples": 1, "median_ns": 1200, "max_ns": 1200,
             "penalty_ns": 101},
        ])

    def test_sample_order_does_not_change_the_row(self):
        forward = dc.summarize(*dc.parse(self.text()))
        backward = dc.summarize(*dc.parse(self.text(hot=list(range(2099, 99, -1)))))
        self.assertEqual(forward, backward)

    def test_too_few_samples_for_the_tail_is_refused(self):
        with self.assertRaises(dc.Refused) as caught:
            dc.summarize(*dc.parse(self.text(hot=[5] * 999)))
        self.assertIn("999", str(caught.exception))
        dc.summarize(*dc.parse(self.text(hot=[5] * 1000)))

    def test_no_hot_series_is_refused(self):
        with self.assertRaises(dc.Refused):
            dc.summarize(*dc.parse(HEADER + samples("idle1", [5] * 2000)))

    def test_a_device_without_unified_memory_is_refused(self):
        text = self.text().replace("unified 1", "unified 0")
        with self.assertRaises(dc.Refused) as caught:
            dc.summarize(*dc.parse(text))
        self.assertIn("unified memory", str(caught.exception))


class Render(unittest.TestCase):
    def test_durations(self):
        self.assertEqual(dc.duration(999), "999 ns")
        self.assertEqual(dc.duration(103_333), "103.3 us")
        self.assertEqual(dc.duration(1_900_000), "1.90 ms")
        self.assertEqual(dc.duration(2_500_000_000), "2.50 s")
        self.assertEqual(dc.duration(-99), "-99 ns")

    def test_each_figure_is_printed_under_its_own_label(self):
        # Every figure differs from every other, so a statistic printed under
        # the wrong label fails. 1000 hot samples: the median is rank 500, the
        # 99.9th percentile rank 999.
        hot = ([(101_000 + 100 * i, 90_000 + 100 * i, 2_000 + i) for i in range(998)]
               + [(899_000, 600_000, 9_000), (950_000, 700_000, 9_500)])
        status, out, err = run(HEADER + lines("hot", hot)
                               + lines("idle100", [(500_000, 1, 1), (600_000, 1, 1), (720_000, 1, 1)])
                               + lines("spin100", [(210_000, 1, 1)]))
        self.assertEqual((status, err), (0, ""))
        self.assertEqual(out.splitlines(), [
            "dispatch-cost: Test GPU, Metal, unified memory",
            "  1000 back-to-back dispatches of an empty kernel after 7 warm-up, "
            "thread QoS user-interactive",
            "  round trip          median 150.9 us   99.9th 899.0 us   max 950.0 us   min 101.0 us",
            "  result visible      median 139.9 us",
            "  on the GPU          10th 2.1 us   median 2.5 us   90th 2.9 us   "
            "(moves with the GPU's power state)",
            "  wake-up penalty: first dispatch after an idle gap, median over the "
            "back-to-back median",
            "    sleep   100 ms   +449.1 us   (median 600.0 us, max 720.0 us, n=3)",
            "    spin    100 ms   +59.1 us   (median 210.0 us, max 210.0 us, n=1)",
        ])

    def test_no_idle_series_says_the_penalty_was_not_measured(self):
        status, out, _ = run(HEADER + samples("hot", [5] * 1000))
        self.assertEqual(status, 0)
        self.assertIn("wake-up penalty: not measured (no sample follows an idle gap)", out)

    def test_a_negative_penalty_is_printed_as_negative(self):
        status, out, _ = run(HEADER + samples("hot", [5000] * 1000) + samples("idle1", [4000]))
        self.assertEqual(status, 0)
        self.assertIn("sleep     1 ms   -1.0 us", out)

    def test_json_carries_the_same_numbers(self):
        status, out, _ = run(HEADER + samples("hot", range(100, 2100)), "--json")
        self.assertEqual(status, 0)
        row = json.loads(out)
        self.assertEqual(row["round_trip_ns"]["p99_9"], 2097)
        self.assertEqual(row["gpu_ns"]["median"], 157)
        self.assertEqual(row["host"], {})
        self.assertIs(row["unified_memory"], True)


class Main(unittest.TestCase):
    def test_exit_statuses(self):
        self.assertEqual(run(HEADER + samples("hot", [5] * 10))[0], 2)
        self.assertEqual(run(HEADER + "garbage\n")[0], 1)
        self.assertEqual(
            run(HEADER.replace("unified 1", "unified yes") + samples("hot", [5] * 1000))[0], 1)
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = dc.main(["--samples", "/nonexistent/dispatch-cost-samples"])
        self.assertEqual(status, 2)
        self.assertIn("no row", err.getvalue())

    def test_samples_that_are_not_text_fail_without_a_traceback(self):
        status, out, err = run(b"\xff\xfe\x00garbage")
        self.assertEqual((status, out), (1, ""))
        self.assertIn("dispatch-cost: failed:", err)
        self.assertIn("not UTF-8", err)

    def test_a_refusal_prints_no_row(self):
        status, out, err = run(HEADER + samples("hot", [5] * 10))
        self.assertEqual((status, out), (2, ""))
        self.assertIn("99.9th percentile needs at least 1000", err)

    def test_arguments_are_checked(self):
        never = AssertionError("an argument check let the probe run")
        with mock.patch.object(dc, "run_probe", side_effect=never), \
                mock.patch.object(dc, "read_host", side_effect=never):
            for flags in (["--hot", "-1"], ["--hot", "4294967296"], ["--warm", "x"],
                          ["--idle-ms", "1,x"], ["--idle-ms", "5,5"], ["--idle-ms", "-3"],
                          ["--idle-ms", "3600001"], ["--idle-reps", "many"]):
                with self.subTest(flags=flags):
                    with self.assertRaises(SystemExit) as caught, \
                            contextlib.redirect_stderr(io.StringIO()):
                        dc.main(flags)
                    self.assertEqual(caught.exception.code, 2)

    def test_the_probe_is_refused_off_apple_silicon(self):
        plan = dc.argparse.Namespace(warm=1, hot=1, idle_ms=[], idle_reps=0, no_spin=False)
        with mock.patch.object(dc.sys, "platform", "linux"), \
                mock.patch.object(dc.platform, "machine", lambda: "x86_64"), \
                mock.patch.object(dc.subprocess, "run", side_effect=AssertionError("ran")), \
                self.assertRaises(dc.Refused) as caught:
            dc.run_probe("targo-that-is-never-run", plan)
        self.assertIn("linux x86_64", str(caught.exception))


class Probe(unittest.TestCase):
    """main() down to the commands it hands targo, on any host."""

    GOOD = HEADER + samples("hot", range(100, 1100))

    def drive(self, flags, results, environ=None, lock=None):
        """Runs main(flags) with targo replaced by `results` (one per call: a
        CompletedProcess, or an exception to raise)."""
        calls = []
        pending = list(results)

        def fake(command, **kwargs):
            calls.append((list(command), kwargs))
            result = pending.pop(0)
            if isinstance(result, BaseException):
                raise result
            return result

        out, err = io.StringIO(), io.StringIO()
        with contextlib.ExitStack() as stack:
            folder = stack.enter_context(tempfile.TemporaryDirectory())
            stack.enter_context(mock.patch.object(dc.sys, "platform", "darwin"))
            stack.enter_context(mock.patch.object(dc.platform, "machine", lambda: "arm64"))
            stack.enter_context(mock.patch.object(
                dc, "read_host", lambda: {"model": "TestMac1,1", "load": "1.0"}))
            stack.enter_context(mock.patch.object(dc, "read_load", lambda: "2.0"))
            stack.enter_context(mock.patch.object(dc.tempfile, "gettempdir", lambda: lock or folder))
            stack.enter_context(mock.patch.dict(dc.os.environ, environ or {}, clear=True))
            stack.enter_context(mock.patch.object(dc.subprocess, "run", fake))
            stack.enter_context(contextlib.redirect_stdout(out))
            stack.enter_context(contextlib.redirect_stderr(err))
            status = dc.main(flags)
        return status, out.getvalue(), err.getvalue(), calls

    @staticmethod
    def done(code=0, stdout="", stderr=""):
        return subprocess.CompletedProcess([], code, stdout, stderr)

    def test_the_build_then_the_measurement(self):
        status, out, err, calls = self.drive(
            ["--targo", "/x/targo", "--warm", "3", "--hot", "1000", "--idle-ms", "1,20",
             "--idle-reps", "4", "--json"],
            [self.done(), self.done(stdout=self.GOOD)])
        self.assertEqual((status, err), (0, ""))

        def targo(verb):
            return ["/x/targo", "--unverified", verb, "--release", "--locked", "--quiet",
                    "--manifest-path", str(dc.MANIFEST)]

        self.assertEqual([command for command, _ in calls], [
            targo("build"),
            targo("run") + ["--", "--warm", "3", "--hot", "1000", "--idle-ms", "1,20",
                            "--idle-reps", "4", "--spin", "1"],
        ])
        for _, kwargs in calls:
            self.assertEqual(Path(kwargs["cwd"]), dc.ROOT)
            self.assertEqual(kwargs["env"]["CARGO_TARGET_DIR"],
                             os.path.realpath(dc.ROOT / "crates" / "target"))
        self.assertEqual(json.loads(out)["host"], {"model": "TestMac1,1", "load": "1.0 -> 2.0"})

    def test_no_spin_and_a_target_the_caller_named(self):
        for name in dc.TARGET_DIR_VARIABLES:
            with self.subTest(name=name):
                status, _, _, calls = self.drive(["--no-spin", "--hot", "1000"],
                                                 [self.done(), self.done(stdout=self.GOOD)],
                                                 environ={name: "/elsewhere"})
                self.assertEqual(status, 0)
                self.assertEqual(calls[1][0][-2:], ["--spin", "0"])
                self.assertEqual(calls[1][0][0], "targo")
                env = calls[1][1]["env"]
                self.assertEqual(env[name], "/elsewhere")
                self.assertEqual("CARGO_TARGET_DIR" in env, name == "CARGO_TARGET_DIR")

    def test_every_flag_the_driver_passes_is_one_the_probe_takes(self):
        source = (dc.MANIFEST.parent / "src" / "main.rs").read_text(encoding="utf-8")
        taken = set(re.findall(r'^\s*"(--[a-z-]+)" => ', source, re.MULTILINE))
        plan = dc.argparse.Namespace(warm=1, hot=2, idle_ms=[3], idle_reps=4, no_spin=False)
        passed = set(dc.probe_arguments(plan)[0::2])
        self.assertEqual(passed, {"--warm", "--hot", "--idle-ms", "--idle-reps", "--spin"})
        self.assertEqual(passed - taken, set())
        self.assertTrue((dc.MANIFEST.parent / "Cargo.lock").is_file())
        self.assertIn('name = "dispatch-cost-probe"', dc.MANIFEST.read_text(encoding="utf-8"))

    def test_a_failed_build_is_not_a_measurement(self):
        status, out, err, calls = self.drive(["--hot", "1000"],
                                             [self.done(101, stderr="error: no\n")])
        self.assertEqual((status, out, len(calls)), (1, "", 1))
        self.assertIn("`targo build` of the probe exited 101", err)
        self.assertIn("error: no", err)

    def test_a_failing_probe_prints_no_row(self):
        status, out, err, _ = self.drive(
            ["--hot", "1000"],
            [self.done(), self.done(1, stdout=self.GOOD, stderr="dispatch-cost probe: no device\n")])
        self.assertEqual((status, out), (1, ""))
        self.assertIn("`targo run` of the probe exited 1", err)
        self.assertIn("no device", err)

    def test_arguments_the_probe_refuses_are_a_refusal(self):
        status, out, err, _ = self.drive(["--hot", "1000"],
                                         [self.done(), self.done(2, stderr="usage: probe\n")])
        self.assertEqual((status, out), (2, ""))
        self.assertIn("does not take these arguments", err)

    def test_targo_does_not_start(self):
        status, out, err, _ = self.drive(["--hot", "1000"], [FileNotFoundError("no targo")])
        self.assertEqual((status, out), (2, ""))
        self.assertIn("did not start", err)

    def test_too_few_hot_samples_is_refused_before_anything_runs(self):
        status, out, err, calls = self.drive(["--hot", "999"], [])
        self.assertEqual((status, out, calls), (2, "", []))
        self.assertIn("999 back-to-back samples", err)

    def test_a_relative_targo_is_the_callers(self):
        status, _, _, calls = self.drive(["--targo", "./bin/targo", "--hot", "1000"],
                                         [self.done(), self.done(stdout=self.GOOD)])
        self.assertEqual(status, 0)
        self.assertEqual(calls[0][0][0], os.path.abspath("./bin/targo"))

    def test_keep_samples(self):
        with tempfile.TemporaryDirectory() as folder:
            kept = Path(folder) / "kept.txt"
            status, out, _, _ = self.drive(["--hot", "1000", "--keep-samples", str(kept)],
                                           [self.done(), self.done(stdout=self.GOOD)])
            self.assertEqual(status, 0)
            self.assertIn("round trip", out)
            self.assertEqual(kept.read_text(encoding="utf-8"), self.GOOD)
            # A place that cannot be written is refused before the probe runs.
            status, out, err, calls = self.drive(
                ["--hot", "1000", "--keep-samples", str(Path(folder) / "missing" / "kept.txt")], [])
            self.assertEqual((status, out, calls), (2, "", []))
            self.assertIn("cannot be written", err)
            status, _, _, calls = self.drive(["--hot", "1000", "--keep-samples", folder], [])
            self.assertEqual((status, calls), (2, []))

    def test_a_write_that_fails_after_the_run_keeps_the_row(self):
        with tempfile.TemporaryDirectory() as folder, \
                mock.patch.object(dc.Path, "write_text", side_effect=OSError("disk full")):
            status, out, err, _ = self.drive(
                ["--hot", "1000", "--keep-samples", str(Path(folder) / "kept.txt")],
                [self.done(), self.done(stdout=self.GOOD)])
        self.assertEqual(status, 1)
        self.assertIn("round trip", out)
        self.assertIn("the samples were not kept", err)
        self.assertIn("disk full", err)

    def test_a_second_run_on_the_machine_is_refused(self):
        with tempfile.TemporaryDirectory() as folder:
            with open(Path(folder) / "trust-dispatch-cost.lock", "a") as held:
                dc.fcntl.flock(held, dc.fcntl.LOCK_EX | dc.fcntl.LOCK_NB)
                status, out, err, calls = self.drive(["--hot", "1000"], [], lock=folder)
            self.assertEqual((status, out, calls), (2, "", []))
            self.assertIn("another dispatch-cost is running", err)
            status, _, _, _ = self.drive(["--hot", "1000"],
                                         [self.done(), self.done(stdout=self.GOOD)], lock=folder)
            self.assertEqual(status, 0)


if __name__ == "__main__":
    unittest.main()
