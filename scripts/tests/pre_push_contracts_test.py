"""Run the real shell contracts that read the landing hook.

These tests build isolated Git fixtures, not the compiler. A shell exit code
alone is insufficient: every contract must execute checks and reach its own
terminal success line. The landing validation runner executes this module
uncached, just like the other declared validator tests.
"""
from __future__ import annotations

import contextlib
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

REPO = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(REPO), str(REPO / "scripts/lib")]
from scripts.lib import landing_targo

CONTRACTS = {
    "pre_push_fast_pool_test.sh": "pre-push fast-pool tests: all passed",
    "pre_push_overlap_scoped_test.sh": "pre-push overlap tests: all passed",
    "pre_push_stale_destination_test.sh": "pre-push stale-destination tests: all passed",
    "pre_push_quarantine_test.sh": "pre-push quarantine tests: all passed",
    "pre_push_inherited_red_test.sh": "pre-push inherited-red tests: all passed",
    "pre_push_shadow_test.sh": None,  # includes its actual passed/failed counts
    "ssh_keepalive_test.sh": "ssh keepalive tests: all passed",
}
TIMEOUT_SECONDS = 600


def judge_output(name, code, output):
    if code != 0:
        raise ValueError(f"{name}: shell contract exited {code}")
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    checks = len(re.findall(r"^  ok   \S.*$", output, re.M))
    if not checks:
        raise ValueError(f"{name}: no shell checks executed")
    if re.search(r"^\s*(?:SKIP(?:PED)?\b|FAIL\b)", output, re.M):
        raise ValueError(f"{name}: skipped or failed shell checks are not coverage")
    if name == "pre_push_shadow_test.sh":
        summaries = re.findall(r"^pre_push_shadow_test: (\d+) passed, (\d+) failed$", output, re.M)
        if summaries != [(str(checks), "0")] or lines[-1] != f"pre_push_shadow_test: {checks} passed, 0 failed":
            raise ValueError(f"{name}: incomplete or inconsistent terminal counts")
    else:
        expected = CONTRACTS[name]
        if lines[-1] != expected or lines.count(expected) != 1:
            raise ValueError(f"{name}: missing unique terminal success")
    return checks


@contextlib.contextmanager
def deadline(seconds, timed_out):
    if not hasattr(signal, "setitimer") or seconds <= 0:
        raise RuntimeError("shell contract requires a positive POSIX deadline")
    if signal.getitimer(signal.ITIMER_REAL) != (0.0, 0.0):
        raise RuntimeError("another interval timer already owns this process")
    def expired(signum, frame):
        timed_out[0] = True
        # Use the owned-process signal protocol, which defers interruption
        # while final group identity is being released.
        os.kill(os.getpid(), signal.SIGTERM)
    prior = signal.signal(signal.SIGALRM, expired)
    try:
        signal.setitimer(signal.ITIMER_REAL, seconds)
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, prior)


def run_contract(name, root=REPO, seconds=TIMEOUT_SECONDS):
    if name not in CONTRACTS:
        raise ValueError(f"undeclared shell contract: {name}")
    script = Path(root) / "scripts/tests" / name
    env = landing_targo.hook_environment(os.environ)
    # Fixtures own their Git state and cannot inherit the push being judged.
    for key in list(env):
        if key.startswith("TRUST_LAND_") or key in {
            "TRUST_PUSHED_REFS", "TRUST_PUSH_REMOTE", "GIT_DIR", "GIT_WORK_TREE",
            "GIT_INDEX_FILE", "GIT_COMMON_DIR", "GIT_OBJECT_DIRECTORY",
            "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_PREFIX", "GIT_SHALLOW_FILE",
        }:
            del env[key]
    output = []
    timed_out = [False]
    try:
        with landing_targo.owned_process(["bash", str(script)], cwd=root, env=env,
                                         stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, text=True, errors="replace") as child:
            with deadline(seconds, timed_out):
                for line in child.stdout:
                    output.append(line)
                    print(line, end="", flush=True)
                code = child.wait()
    except KeyboardInterrupt:
        if timed_out[0]:
            raise TimeoutError(f"shell contract exceeded {seconds:g}s") from None
        raise
    return judge_output(name, code, "".join(output))


class RunnerControls(unittest.TestCase):
    def test_zero_partial_skipped_failed_and_duplicate_verdicts_refuse(self):
        name = "pre_push_fast_pool_test.sh"
        final = CONTRACTS[name]
        for code, output in (
            (0, ""), (0, final + "\n"), (0, "  ok   one\n"),
            (0, "  ok   one\nSKIPPED: unavailable\n" + final + "\n"),
            (0, "  ok   one\n  FAIL two\n" + final + "\n"),
            (1, "  ok   one\n" + final + "\n"),
            (0, "  ok   one\n" + final + "\n" + final + "\n"),
        ):
            with self.subTest(code=code, output=output):
                with self.assertRaises(ValueError):
                    judge_output(name, code, output)
        self.assertEqual(judge_output(name, 0, "  ok   one\n" + final + "\n"), 1)

    def test_shadow_summary_counts_actual_checks(self):
        self.assertEqual(judge_output("pre_push_shadow_test.sh", 0,
                         "  ok   one\npre_push_shadow_test: 1 passed, 0 failed\n"), 1)
        for summary in ("0 passed, 0 failed", "2 passed, 0 failed", "1 passed, 1 failed"):
            with self.assertRaises(ValueError):
                judge_output("pre_push_shadow_test.sh", 0,
                             f"  ok   one\npre_push_shadow_test: {summary}\n")

    def test_deadline_stops_an_owned_descendant(self):
        with tempfile.TemporaryDirectory(prefix="shell-contract-timeout.") as tmp:
            root = Path(tmp)
            scripts = root / "scripts/tests"
            scripts.mkdir(parents=True)
            pidfile = root / "pid"
            (scripts / "pre_push_fast_pool_test.sh").write_text(
                'sleep 30 &\nprintf "%s\\n" "$!" > pid\nwait\n')
            with mock.patch.object(landing_targo, "STOP_GRACE_S", .05):
                with self.assertRaises(TimeoutError):
                    run_contract("pre_push_fast_pool_test.sh", root=root, seconds=.1)
            pid = int(pidfile.read_text())
            state = subprocess.run(["ps", "-p", str(pid), "-o", "stat="],
                                   capture_output=True, text=True).stdout.strip()
            self.assertTrue(not state or state.startswith("Z"), state)

    def test_alarm_during_reaping_never_signals_a_released_group_id(self):
        raw_reaped = [False]
        post_reap_signals = []
        timed_out = [False]
        signal_group = landing_targo.signal_owned_group

        def guarded_signal(pid, sig):
            if raw_reaped[0]:
                post_reap_signals.append((pid, sig))
                return  # never actually address an already-released PID
            signal_group(pid, sig)

        with mock.patch.object(landing_targo, "STOP_GRACE_S", .01), \
                mock.patch.object(landing_targo, "signal_owned_group", side_effect=guarded_signal):
            with self.assertRaises(KeyboardInterrupt):
                with landing_targo.owned_process([sys.executable, "-c", "pass"],
                                                 stdout=subprocess.PIPE, text=True) as child:
                    real_wait = child.process.wait

                    def pause_after_wait():
                        code = real_wait()
                        if not raw_reaped[0]:
                            raw_reaped[0] = True
                            signal.setitimer(signal.ITIMER_REAL, .001)
                            time.sleep(.05)
                        return code

                    child.process.wait = pause_after_wait
                    with deadline(2, timed_out):
                        child.communicate()
        self.assertTrue(raw_reaped[0])
        self.assertTrue(timed_out[0])
        self.assertTrue(child.reaped)
        self.assertEqual(post_reap_signals, [])


class HookShellContracts(unittest.TestCase):
    def test_fast_pool(self):
        run_contract("pre_push_fast_pool_test.sh")

    def test_overlap(self):
        run_contract("pre_push_overlap_scoped_test.sh")

    def test_stale_destination(self):
        run_contract("pre_push_stale_destination_test.sh")

    def test_quarantine(self):
        run_contract("pre_push_quarantine_test.sh")

    def test_inherited_red(self):
        run_contract("pre_push_inherited_red_test.sh")

    def test_shadow(self):
        run_contract("pre_push_shadow_test.sh")

    def test_ssh_keepalive(self):
        run_contract("ssh_keepalive_test.sh")

if __name__ == "__main__":
    unittest.main()
