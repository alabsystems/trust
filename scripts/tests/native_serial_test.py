"""Fixture-only lifecycle/descriptor tests; no managed package admission."""

from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lib"))
import native_serial


@unittest.skipUnless(os.name == "posix", "maintained native owner is POSIX")
class SerialLifecycleTests(unittest.TestCase):
    def test_group_quit_is_translated_to_term_and_waits_for_actual_retirement(self):
        with tempfile.TemporaryDirectory(prefix="serial group ü ") as tmp:
            root = Path(tmp)
            owner = root / "owner.py"
            owner.write_text(
                "import json,os,pathlib,signal,sys,time\n"
                "root=pathlib.Path(sys.argv[1])\n"
                "def stop(*_):\n"
                " (root/'term').write_text('TERM')\n"
                " while not (root/'release').exists(): time.sleep(.01)\n"
                " (root/'retired').write_text('retired')\n"
                " raise SystemExit(0)\n"
                "signal.signal(signal.SIGTERM,stop)\n"
                "signal.signal(signal.SIGQUIT,lambda *_:(root/'quit').write_text('QUIT'))\n"
                "(root/'ready').write_text(json.dumps([os.getpid(),os.getppid(),os.getpgrp(),os.getsid(0)]))\n"
                "while True: time.sleep(.01)\n"
            )
            supervisor = root / "supervisor.py"
            supervisor.write_text(
                "import os,pathlib,sys\n"
                f"sys.path.insert(0,{str(Path(native_serial.__file__).parent)!r})\n"
                "import native_serial\n"
                "try:\n"
                " native_serial.run_custodied_command([sys.executable,sys.argv[1],sys.argv[2]],env=dict(os.environ))\n"
                "except KeyboardInterrupt:\n"
                " pathlib.Path(sys.argv[2],'cancelled').write_text('cancelled')\n"
                " raise SystemExit(130)\n"
            )
            # The disposable supervisor owns its own group; no lab/agent group
            # is signalled. The fake owner supplies no managed authority.
            with subprocess.Popen(
                [
                    sys.executable,
                    "-I",
                    "-S",
                    "-B",
                    str(supervisor),
                    str(owner),
                    str(root),
                ],
                start_new_session=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            ) as process:

                def await_file(name):
                    deadline = time.monotonic() + 30
                    while not (root / name).exists() and process.poll() is None:
                        if time.monotonic() >= deadline:
                            self.fail(f"fixture did not reach {name}")
                        time.sleep(0.01)
                    self.assertTrue((root / name).exists(), name)

                pid = None
                try:
                    await_file("ready")
                    pid, ppid, group, session = json.loads((root / "ready").read_text())
                    self.assertEqual(ppid, process.pid)
                    self.assertEqual((group, session), (pid, pid))
                    self.assertNotEqual(group, process.pid)
                    os.killpg(process.pid, signal.SIGQUIT)
                    await_file("term")
                    self.assertIsNone(process.poll())
                    self.assertFalse((root / "quit").exists())
                    self.assertFalse((root / "retired").exists())
                finally:
                    (root / "release").write_text("release")
                    if process.poll() is None and not (root / "term").exists():
                        process.terminate()
                    elif pid is not None and not (root / "term").exists():
                        # Even an assertion/regression which killed the fake
                        # supervisor cannot leave our known fixture orphaned.
                        try:
                            os.kill(pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                    output, errors = process.communicate(timeout=30)
                self.assertEqual(process.returncode, 130, output + errors)
                self.assertEqual((root / "retired").read_text(), "retired")
                self.assertEqual((root / "cancelled").read_text(), "cancelled")

    def test_original_numeric_descriptions_and_environment_remain_transparent(self):
        # These are data-only fixture descriptors, not forged scheduler/SDK
        # capabilities. Actual native importer admission is a separate gate.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            program = root / "observed.py"
            program.write_text(
                "import json,os,sys\n"
                "fds=[int(x) for x in sys.argv[1:]]\n"
                "print(json.dumps([os.getppid(),[os.fstat(fd).st_ino for fd in fds],"
                "{k:os.environ[k] for k in ('SDKROOT','CARGO_MAKEFLAGS','MAKEFLAGS','MFLAGS',"
                "'CARGO_JOBSERVER_HANDOFF','ATERM_SDK_LEASE_V3')}]))\n"
            )
            read, write = os.pipe()
            try:
                with (root / "sdk-data").open("w+b") as sdk:
                    flags = f"--jobserver-auth={read},{write} -j"
                    selected = {
                        "SDKROOT": "/fixture sdk ü",
                        "CARGO_MAKEFLAGS": flags,
                        "MAKEFLAGS": flags,
                        "MFLAGS": flags,
                        "CARGO_JOBSERVER_HANDOFF": "fixture-text-uninterpreted",
                        "ATERM_SDK_LEASE_V3": str(sdk.fileno()),
                    }
                    result = native_serial.run_custodied_command(
                        [
                            sys.executable,
                            "-I",
                            "-S",
                            "-B",
                            str(program),
                            str(read),
                            str(write),
                            str(sdk.fileno()),
                        ],
                        env=dict(os.environ, **selected),
                        timeout=30,
                    )
                    self.assertEqual(result.returncode, 0, result.stderr)
                    observed = json.loads(result.stdout)
                    self.assertEqual(
                        observed,
                        [
                            os.getpid(),
                            [os.fstat(fd).st_ino for fd in (read, write, sdk.fileno())],
                            selected,
                        ],
                    )
            finally:
                os.close(read)
                os.close(write)

    def test_term_oserror_preserves_original_failure_and_wait_without_add_note(self):
        # An exception with no add_note models the supported Python3.9 floor.
        class Failure(Exception):
            def __getattribute__(self, name):
                if name == "add_note":
                    raise AssertionError("Python3.9 has no exception notes")
                return super().__getattribute__(name)

        original = Failure("original communicate failure")
        child = mock.Mock()
        child.communicate.side_effect = [original, ("", "")]
        child.terminate.side_effect = PermissionError("TERM unavailable fixture")
        diagnostic = io.StringIO()
        with mock.patch.object(
            native_serial.subprocess, "Popen", return_value=child
        ), contextlib.redirect_stderr(diagnostic):
            with self.assertRaises(Failure) as raised:
                native_serial.run_custodied_command(["fixture"], env={})
        self.assertIs(raised.exception, original)
        self.assertEqual(child.communicate.call_count, 2)
        child.wait.assert_called_once_with()
        self.assertIn("TERM unavailable; retaining custody", diagnostic.getvalue())

    def test_broken_diagnostic_cannot_replace_original_term_failure(self):
        original = RuntimeError("original fixture communicate failure")
        child = mock.Mock()
        child.communicate.side_effect = [original, ("", "")]
        child.terminate.side_effect = PermissionError("TERM unavailable fixture")
        broken = mock.Mock()
        broken.write.side_effect = OSError("diagnostic stream closed")
        with mock.patch.object(
            native_serial.subprocess, "Popen", return_value=child
        ), mock.patch.object(native_serial.sys, "stderr", broken):
            with self.assertRaises(RuntimeError) as raised:
                native_serial.run_custodied_command(["fixture"], env={})
        self.assertIs(raised.exception, original)
        self.assertEqual(child.communicate.call_count, 2)
        child.wait.assert_called_once_with()

    def test_blocked_quit_refuses_before_launch_without_changing_mask(self):
        previous = signal.pthread_sigmask(signal.SIG_BLOCK, (signal.SIGQUIT,))
        try:
            blocked = signal.pthread_sigmask(signal.SIG_BLOCK, ())
            with mock.patch.object(native_serial.subprocess, "Popen") as launch:
                with self.assertRaisesRegex(RuntimeError, "blocked cancellation"):
                    native_serial.run_custodied_command(["unlaunched"], env={})
                launch.assert_not_called()
            self.assertEqual(signal.pthread_sigmask(signal.SIG_BLOCK, ()), blocked)
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous)


if __name__ == "__main__":
    unittest.main()
