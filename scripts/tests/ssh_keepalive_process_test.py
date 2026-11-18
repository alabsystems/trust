#!/usr/bin/env python3
"""Real local process controls for the ssh -G capture; never runs ssh/network."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

PARSER = argparse.ArgumentParser()
PARSER.add_argument("--helper-dir", type=Path, default=Path(__file__).resolve().parents[1] / "hooks")
OPTIONS, TEST_ARGS = PARSER.parse_known_args()


# A `#!{sys.executable}` shebang cannot carry an interpreter path with spaces (atpkg's python
# lives under `Application Support/`): exec splits it and the fake never runs. This sh/python
# polyglot execs the interpreter quoted and keeps argv[0] as the fake's own path.
PYTHON_SHEBANG = f'#!/bin/sh\n""":"\nexec "{sys.executable}" "$0" "$@"\n":"""\n'


class ProbeProcesses(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="ssh-probe-process-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.identity = self.root / "owned.json"
        self.wrapper = self.root / "wrapper"
        # The identity is published by rename, so the test, which signals the
        # wrapper once the file exists, never reads it half written (under load
        # a cancellation landed between create and write: JSONDecodeError).
        self.wrapper.write_text(PYTHON_SHEBANG + '''import json,os,sys,time
from pathlib import Path
mode=os.environ['PROBE_CASE']
if mode == 'positive':
 print('serveraliveinterval 30');sys.exit(0)
if mode == 'oversize':
 sys.stdout.write('x'*(1024*1024+1));sys.exit(0)
if mode == 'direct':
 time.sleep(45);sys.exit(0)
child=os.fork()
if child == 0:
 if mode == 'closed-stdout': os.close(1)
 time.sleep(45);os._exit(0)
identity=Path(os.environ['PROBE_IDENTITY']);staged=identity.with_name(identity.name+'.partial')
staged.write_text(json.dumps(dict(leader=os.getpid(),child=child,group=os.getpgrp())));os.replace(staged,identity)
if mode == 'closed-stdout':
 print('serveraliveinterval 30',flush=True);os._exit(0)
if mode == 'leader-exit': os._exit(0)
os.waitpid(child,0)
''')
        self.wrapper.chmod(0o700)
        self.env = os.environ.copy()
        self.env.update(HOME=str(self.root), GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_NOSYSTEM="1",
                        GIT_SSH=str(self.wrapper), PROBE_IDENTITY=str(self.identity))
        for name in ("GIT_SSH_COMMAND", "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE"):
            self.env.pop(name, None)

    def run_probe(self, mode, cancel=None):
        self.env["PROBE_CASE"] = mode
        self.identity.unlink(missing_ok=True)
        if cancel:
            argv = ["perl", str(OPTIONS.helper_dir / "_ssh_probe.pl"), "--", str(self.wrapper), "-G", "git@github.invalid"]
        else:
            argv = ["bash", "-c", '. "$1"; trust_ssh_keepalive git@github.invalid:owner/repo.git',
                    "probe-test", str(OPTIONS.helper_dir / "_ssh_keepalive.sh")]
        started = time.monotonic()
        child = subprocess.Popen(argv, env=self.env, cwd=self.root, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, start_new_session=True)
        timed_out = False
        try:
            if cancel:
                until = time.monotonic() + 5
                while not self.identity.exists() and child.poll() is None and time.monotonic() < until:
                    time.sleep(0.01)
                self.assertTrue(self.identity.exists(), "wrapper must really start before cancellation")
                child.send_signal(cancel)
            try:
                out, err = child.communicate(timeout=14 if not cancel else 4)
            except subprocess.TimeoutExpired:
                timed_out = True
                # Only this test's session. The old alarm-only implementation's
                # descendants share it; the new probe owns its separate group.
                os.killpg(child.pid, signal.SIGTERM)
                out, err = child.communicate(timeout=3)
        finally:
            # Observe production closure BEFORE this test's emergency cleanup;
            # otherwise cleanup itself could make a leaking implementation pass.
            group_absent = True
            identity = None
            if self.identity.exists():
                identity = json.loads(self.identity.read_text())
                until = time.monotonic() + 1
                group_absent = False
                while time.monotonic() < until:
                    try:
                        os.killpg(identity["group"], 0)
                    except ProcessLookupError:
                        group_absent = True
                        break
                    time.sleep(0.01)
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                child.communicate(timeout=3)
            if identity is not None and not group_absent:
                # Never signal a recorded PGID after its leader may be reaped.
                # A broken implementation stays RED; its cooperative fixture
                # child exits naturally after45s, bounded by this final wait.
                until = started + 47
                while time.monotonic() < until:
                    try:
                        os.killpg(identity["group"], 0)
                    except ProcessLookupError:
                        break
                    time.sleep(0.01)
        elapsed = time.monotonic() - started
        print(json.dumps(dict(mode=mode, exit=child.returncode, outer_timeout=timed_out,
                              seconds=elapsed, group_absent=group_absent)), flush=True)
        self.assertFalse(timed_out, "capture must finish before the outer safety timeout")
        self.assertTrue(group_absent, "the probe must close its owned wrapper group")
        return child.returncode, out, err

    def test_positive(self):
        code, out, _ = self.run_probe("positive")
        self.assertEqual(code, 0)
        self.assertIn(b"on 30 (GIT_SSH)", out)

    def test_direct_hang(self):
        code, out, _ = self.run_probe("direct")
        self.assertEqual(code, 2)
        self.assertIn(b"unknown", out)

    def test_stdout_holding_descendant(self):
        code, out, _ = self.run_probe("descendant")
        self.assertEqual(code, 2)
        self.assertIn(b"unknown", out)

    def test_exited_leader_stdout_holding_descendant(self):
        code, out, _ = self.run_probe("leader-exit")
        self.assertEqual(code, 2)
        self.assertIn(b"unknown", out)

    def test_cancellation_closes_descendants(self):
        for sig in (signal.SIGHUP, signal.SIGINT, signal.SIGQUIT, signal.SIGTERM):
            with self.subTest(signal=sig):
                code, _, _ = self.run_probe("descendant", cancel=sig)
                self.assertEqual(code, 128 + sig)

    def test_success_closes_quiet_descendants(self):
        code, out, _ = self.run_probe("closed-stdout")
        self.assertEqual(code, 0)
        self.assertIn(b"on 30 (GIT_SSH)", out)

    def test_output_bound(self):
        code, out, _ = self.run_probe("oversize")
        self.assertEqual(code, 2)
        self.assertIn(b"unknown", out)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], *TEST_ARGS])
