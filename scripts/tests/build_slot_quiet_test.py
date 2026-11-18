#!/usr/bin/env python3
"""Bounded real-process admission controls; no shared host locks or heavy work."""
import fcntl
import importlib.machinery
import importlib.util
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from urllib.parse import quote
from unittest import mock
from build_slot_test import isolate_resource_environment, launcher_directories


GATE = Path(__file__).resolve().parents[1] / "build-slot"

# Probe injection lives only in this test process launcher, never in the gate's
# CLI/environment. Real flock, subprocess, signals and monotonic deadlines run.
LAUNCHER = r'''
import importlib.machinery, importlib.util, json, pathlib, sys, time
loader = importlib.machinery.SourceFileLoader("gate", sys.argv[1])
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
# Keep imported adoption records private to this fixture, like its slot files.
gate.ADOPTION_DIR = str(pathlib.Path(sys.argv[2]).parent / "adopted")
gate.cpu_capacity_directory = lambda: str(pathlib.Path(sys.argv[2]).parent / "cpu-capacity")
state = pathlib.Path(sys.argv[2])
def read(key):
    return json.loads(state.read_text())[key]
gate.MEASURED_NCPU = read("cpus")
gate.NCPU = gate.MEASURED_NCPU or 4
gate.available_gib = lambda: read("memory")
gate.load1 = lambda: read("load")
gate.build_processes = lambda: read("builds")
gate.ledger_discovery = lambda env: None  # never the operator's real aterm ledger
gate.QUIET_SECONDS = 0.12
sleep = time.sleep
gate.time.sleep = lambda seconds: sleep(min(seconds, 0.02))
try:
    sys.exit(gate.main(sys.argv[3:]))
except gate.AdmissionTimeout:
    print("admission wait timed out; no command was started", file=sys.stderr)
    sys.exit(2)
'''

# The legacy protocol intentionally has no admission.lock: take any single
# slot-N, then hold it for the child lifetime. New exclusivity must see this.
LEGACY = r'''
import fcntl, os, pathlib, sys, time
pool, count, started = sys.argv[1:]
while True:
    for i in range(int(count)):
        fd = os.open(os.path.join(pool, "slot-" + str(i)), os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            pathlib.Path(started).write_text(str(i))
            while True: time.sleep(1)
        except BlockingIOError:
            os.close(fd)
    time.sleep(0.02)
'''

CHILD = r'''
import json, os, pathlib, signal, sys, time
if len(sys.argv) > 2:
    def delayed_exit(sig, frame):
        pathlib.Path(sys.argv[1] + ".term").touch()
        time.sleep(0.2)
        sys.exit(128 + sig)
    signal.signal(signal.SIGTERM, delayed_exit)
pathlib.Path(sys.argv[1]).write_text(json.dumps({k: os.environ.get(k) for k in ("BUILD_SLOT_HELD", "CARGO_BUILD_JOBS")}))
if len(sys.argv) > 2:
    while True: time.sleep(1)
'''

RESOURCE_RUNNER = r'''
import json, os, pathlib, sys
from urllib.parse import quote
args = sys.argv[1:]
trace = pathlib.Path(os.environ['RESOURCE_TEST_TRACE'])
if args == ['ctl', '@self', 'resources', 'capabilities']:
    trace.with_suffix('.probe').write_text(json.dumps(args))
    if os.environ.get('RESOURCE_TEST_MODE') == 'legacy':
        print('ERR unknown verb resources');sys.exit(1)
    print('OK resources capabilities version=1 runner=' + quote(os.environ['RESOURCE_TEST_RUNNER'], safe='') + ' ai=codex')
    sys.exit(0)
if args[:1] != ['resource-run']:
    trace.with_suffix('.unexpected').touch();sys.exit(79)
trace.write_text(json.dumps({'pid': os.getpid(), 'argv': args}))
if os.environ.get('RESOURCE_TEST_MODE') == 'refuse':sys.exit(73)
command = args[args.index('--') + 1:]
os.execv(command[0], command)
'''

RESOURCE_CHILD = r'''
import pathlib, signal, sys, time
marker = pathlib.Path(sys.argv[1])
release = marker.with_suffix('.release')
def stopped(sig, frame):
    marker.with_suffix('.signal').write_text(str(sig))
    while not release.exists(): time.sleep(0.01)
    sys.exit(128 + sig)
for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
    signal.signal(sig, stopped)
marker.touch()
while True: time.sleep(1)
'''

LEASE_CHILD = r'''
import json, os, pathlib, sys, time
root = pathlib.Path(sys.argv[1])
(root / "job.json").write_text(json.dumps({"pid": os.getpid(), "ppid": os.getppid()}))
while not (root / "release").exists(): time.sleep(0.01)
(root / "finished").touch()
'''


class BuildSlotTest(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        self.tmp = tempfile.TemporaryDirectory(prefix="build-slot-test.")
        self.root = Path(self.tmp.name)
        self.pool = self.root / "locks"
        launcher_directories(self.pool)
        self.state = self.root / "host.json"
        self.host()
        self.env = dict(os.environ, BUILD_SLOT_DIR=str(self.pool), BUILD_SLOTS="3",
                        BUILD_SLOT_HELD="0", BUILD_SLOT_MEM_GB="8")
        # Admission controls must never contact the operator's real aterm.
        for key in list(self.env):
            if key.startswith("ATERM_") or key == "BUILD_SLOT_ATERM_CLI":
                self.env.pop(key)
        self.env.pop("CARGO_BUILD_JOBS", None)
        # These controls use a private simulated CPU pool, not the enclosing
        # build's budget provenance. Keep production cap enforcement unchanged.
        self.env.pop("TARGO_PLANNED_JOBS", None)
        self.env.pop("TARGO_CALLER_JOBS", None)
        self.processes = []
        self.logs = []

    def tearDown(self):
        # Only these owned processes, each with one bounded wait after TERM.
        for proc in self.processes:
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait(timeout=3)
        for log in self.logs:
            log.close()
        self.tmp.cleanup()

    def host(self, memory=100, load=0, builds=None, cpus=32):
        pending = self.state.with_suffix(".next")
        pending.write_text(json.dumps({"memory": memory, "load": load, "builds": [] if builds is None else builds, "cpus": cpus}))
        pending.replace(self.state)

    def spawn(self, cmd, env=None):
        log = (self.root / f"process-{len(self.processes)}.log").open("w+")
        proc = subprocess.Popen(cmd, cwd=self.root, env=env or self.env, stdout=log, stderr=log)
        self.processes.append(proc)
        self.logs.append(log)
        return proc

    def gate(self, name, *options, hold=False, env=None, worktree=False):
        marker = self.root / name
        cmd = [sys.executable, "-c", LAUNCHER, str(GATE), str(self.state),
               *([] if worktree else ["--no-worktree-lock"]), *options,
               "--", sys.executable, "-c", CHILD, str(marker)]
        if hold:
            cmd.append("hold")
        return self.spawn(cmd, env), marker

    def until(self, predicate, timeout=3):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if predicate():
                return
            time.sleep(0.01)
        self.fail("bounded condition timed out: " + "\n".join(self.output(p) for p in self.processes))

    def output(self, proc):
        log = self.logs[self.processes.index(proc)]
        log.flush()
        return Path(log.name).read_text()

    def held(self, slot):
        fd = os.open(self.pool / f"slot-{slot}", os.O_RDWR | os.O_CREAT, 0o644)
        try:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return False
            except BlockingIOError:
                return True
        finally:
            os.close(fd)

    def admission_held(self):
        fd = os.open(self.pool / "admission.lock", os.O_RDWR | os.O_CREAT, 0o644)
        try:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return False
            except BlockingIOError:
                return True
        finally:
            os.close(fd)

    def lease_survives_wrapper_loss(self, *, worktree=False, exclusive=False, resource=False):
        if worktree:
            subprocess.run(["git", "init", "-q", str(self.root)], check=True, capture_output=True)
        env = self.resource_environment() if resource else self.env
        options = ([] if worktree else ["--no-worktree-lock"])
        if exclusive:
            options += ["--exclusive", "--wait-timeout", "5"]
        proc = self.spawn([sys.executable, "-B", "-c", LAUNCHER, str(GATE), str(self.state),
                           *options, "--", sys.executable, "-B", "-c", LEASE_CHILD,
                           str(self.root)], env)
        child = None
        child_start = None

        def identity(pid):
            result = subprocess.run(["ps", "-p", str(pid), "-o", "lstart="],
                                    capture_output=True, text=True)
            return result.stdout.strip() if result.returncode == 0 else None

        def locked(path):
            fd = os.open(path, os.O_RDWR)
            try:
                try:
                    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    return False
                except BlockingIOError:
                    return True
            finally:
                os.close(fd)

        try:
            self.until(lambda: (self.root / "job.json").exists(), timeout=8)
            observed = json.loads((self.root / "job.json").read_text())
            child = observed["pid"]
            child_start = identity(child)
            self.assertIsNotNone(child_start)
            self.assertEqual(observed["ppid"], proc.pid)
            locks = sorted(self.pool.glob("slot-*"))
            if worktree:
                locks.append(self.root / ".git/build-slot.lock")
            if exclusive:
                locks.append(self.pool / "admission.lock")
                self.assertEqual(len(locks), 6)
            self.assertTrue(locks)
            self.assertTrue(all(locked(path) for path in locks))
            proc.kill()
            self.assertEqual(proc.wait(timeout=3), -signal.SIGKILL)
            self.assertEqual(identity(child), child_start)
            self.assertTrue(all(locked(path) for path in locks),
                            "live admitted command lost its reservation after wrapper death")
            if resource:
                self.assertEqual(json.loads(self.resource_trace.read_text())["pid"], child)
            (self.root / "release").touch()
            self.until(lambda: (self.root / "finished").exists())
            self.until(lambda: identity(child) is None)
            self.assertFalse(any(locked(path) for path in locks))
        finally:
            (self.root / "release").touch()
            if child is not None and child_start and identity(child) == child_start:
                self.until(lambda: identity(child) is None)

    def test_worktree_reservation_survives_wrapper_death(self):
        self.lease_survives_wrapper_loss(worktree=True)

    def test_exclusive_reservation_survives_wrapper_death(self):
        self.lease_survives_wrapper_loss(exclusive=True)

    def test_resource_exec_retains_reservation_after_wrapper_death(self):
        self.lease_survives_wrapper_loss(resource=True)

    def resource_environment(self, mode="supported"):
        tools = self.root / "tool bin"
        tools.mkdir()
        runner = tools / "aterm"
        body = tools / "aterm.py"
        body.write_text(RESOURCE_RUNNER)
        # The selected Trust Python can live below Application Support. A
        # shebang splits that path; a quoted exec preserves the real interpreter.
        runner.write_text("#!/bin/sh\nexec " + shlex.quote(sys.executable)
                          + " -I -B " + shlex.quote(str(body)) + ' "$@"\n')
        runner.chmod(0o755)
        self.resource_trace = self.root / "resource-trace.json"
        return dict(self.env, PATH=str(tools) + os.pathsep + self.env.get("PATH", ""),
                    ATERM_CHILD="1", ATERM_SESSION_ID="stale-inherited-session",
                    RESOURCE_TEST_RUNNER=str(runner),
                    RESOURCE_TEST_TRACE=str(self.resource_trace), RESOURCE_TEST_MODE=mode)

    def test_admitted_job_uses_authenticated_resource_runner_and_preserves_budget(self):
        # Test preservation of an explicit caller budget. An uncapped job is
        # allowed to borrow all three free slots on this 32-CPU fixture.
        env = dict(self.resource_environment(), CARGO_BUILD_JOBS="10")
        proc, marker = self.gate("owned-resource", env=env)
        self.assertEqual(proc.wait(timeout=10), 0, self.output(proc))
        self.assertEqual(json.loads(marker.read_text()),
                         {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "10"})
        invocation = json.loads(self.resource_trace.read_text())["argv"]
        self.assertEqual(invocation[:3], ["resource-run", "--session", "@self"])
        self.assertNotIn("stale-inherited-session", invocation)
        self.assertEqual(invocation[invocation.index("--") + 1:],
                         [sys.executable, "-c", CHILD, str(marker)])
        label = invocation[invocation.index("--job") + 1]
        self.assertNotIn(CHILD, label)
        self.assertIn(Path(sys.executable).name, label)

    def test_admitted_job_discovers_explicit_client_outside_compiler_path(self):
        env = self.resource_environment()
        env.update(PATH="", BUILD_SLOT_ATERM_CLI=str(self.root / "tool bin/aterm"))
        proc, marker = self.gate("explicit-resource", env=env)
        self.assertEqual(proc.wait(timeout=10), 0, self.output(proc))
        self.assertTrue(marker.exists())
        invocation = json.loads(self.resource_trace.read_text())["argv"]
        self.assertEqual(invocation[:3], ["resource-run", "--session", "@self"])
        self.assertEqual(invocation[invocation.index("--") + 1:],
                         [sys.executable, "-c", CHILD, str(marker)])

    def test_legacy_aterm_is_explicitly_unreported_and_never_runs_unknown_verb(self):
        proc, marker = self.gate("legacy-resource", env=self.resource_environment("legacy"))
        self.assertEqual(proc.wait(timeout=10), 0, self.output(proc))
        self.assertTrue(marker.exists())
        self.assertFalse(self.resource_trace.exists())
        self.assertFalse(self.resource_trace.with_suffix(".unexpected").exists())
        self.assertIn("resource attribution unavailable", self.output(proc))

    def test_refused_resource_runner_never_starts_or_retries_command(self):
        proc, marker = self.gate("refused-resource", env=self.resource_environment("refuse"))
        self.assertEqual(proc.wait(timeout=10), 73, self.output(proc))
        self.assertTrue(self.resource_trace.exists())
        self.assertFalse(marker.exists())

    def test_resource_command_signals_retain_slot_until_child_exits(self):
        env = self.resource_environment()
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            with self.subTest(signal=sig):
                marker = self.root / f"resource-signal-{sig}"
                proc = self.spawn([sys.executable, "-c", LAUNCHER, str(GATE), str(self.state),
                                   "--no-worktree-lock", "--", sys.executable, "-c",
                                   RESOURCE_CHILD, str(marker)], env)
                try:
                    self.until(marker.exists)
                    proc.send_signal(sig)
                    self.until(marker.with_suffix(".signal").exists)
                    self.assertEqual(marker.with_suffix(".signal").read_text(), str(int(sig)))
                    self.assertIsNone(proc.poll())
                    self.assertTrue(self.held(0), "retain admission through delayed signal handling")
                finally:
                    marker.with_suffix(".release").touch()
                self.assertEqual(proc.wait(timeout=3), 128 + sig, self.output(proc))
                self.assertFalse(any(self.held(i) for i in range(3)))

    def test_exclusive_drains_legacy_and_excludes_legacy_and_new_jobs(self):
        legacy_marker = self.root / "legacy-start"
        legacy = self.spawn([sys.executable, "-c", LEGACY, str(self.pool), "3", str(legacy_marker)])
        self.until(legacy_marker.exists)
        exclusive, marker = self.gate("exclusive", "--exclusive", "--wait-timeout", "3", hold=True)
        self.until(lambda: "draining legacy" in self.output(exclusive))
        self.assertFalse(marker.exists())
        legacy.terminate()
        legacy.wait(timeout=3)
        self.until(marker.exists)
        self.assertTrue(all(self.held(i) for i in range(3)))
        old_marker = self.root / "old-waiter"
        old = self.spawn([sys.executable, "-c", LEGACY, str(self.pool), "3", str(old_marker)])
        new, new_marker = self.gate("new-waiter")
        self.until(lambda: "exclusive reservation owns admission" in self.output(new))
        time.sleep(0.08)
        self.assertFalse(old_marker.exists())
        self.assertFalse(new_marker.exists())
        exclusive.terminate()
        self.until(lambda: marker.with_suffix(".term").exists())
        self.assertTrue(all(self.held(i) for i in range(3)), "retain reservation while child handles TERM")
        self.assertEqual(exclusive.wait(timeout=3), 143)
        self.until(old_marker.exists)
        self.until(new_marker.exists)
        self.assertEqual(new.wait(timeout=3), 0)
        old.terminate()
        old.wait(timeout=3)
        self.assertFalse(any(self.held(i) for i in range(3)))

    def test_historic_larger_pool_is_reserved(self):
        fd = os.open(self.pool / "slot-7", os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            proc, marker = self.gate("historic", "--exclusive", "--wait-timeout", "3", hold=True)
            self.until(lambda: "draining legacy" in self.output(proc))
            self.assertFalse(marker.exists())
        finally:
            os.close(fd)
        self.until(marker.exists)
        self.assertTrue(self.held(7))

    def test_second_exclusive_times_out_without_launching_or_releasing_first(self):
        first, marker = self.gate("first-exclusive", "--exclusive", hold=True)
        self.until(marker.exists)
        second, second_marker = self.gate("second-exclusive", "--exclusive", "--wait-timeout", "0.3")
        self.until(lambda: "exclusive reservation owns admission" in self.output(second))
        self.assertEqual(second.wait(timeout=3), 2)
        self.assertFalse(second_marker.exists())
        self.assertTrue(all(self.held(i) for i in range(3)))
        first.terminate()
        self.assertEqual(first.wait(timeout=3), 143)
        self.assertFalse(any(self.held(i) for i in range(3)))

    def test_cancel_during_drain_releases_partial_and_admission_locks(self):
        fd = os.open(self.pool / "slot-1", os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            proc, marker = self.gate("cancel", "--exclusive")
            self.until(lambda: "draining legacy" in self.output(proc))
            self.assertFalse(self.held(0), "partial slot leases are released while draining")
            self.assertTrue(self.admission_held(), "retain exclusive admission authority while draining")
            proc.terminate()
            self.assertEqual(proc.wait(timeout=3), -signal.SIGTERM)
            self.assertFalse(marker.exists())
            self.assertFalse(self.held(0))
            self.assertFalse(self.admission_held(), "cancellation releases exclusive admission authority")
            normal, started = self.gate("after-cancel")
            self.until(started.exists)
            self.assertEqual(normal.wait(timeout=3), 0)
        finally:
            os.close(fd)

    def test_unknown_and_busy_host_never_launch_then_ready_launches(self):
        for i, host in enumerate((
                {"memory": None}, {"memory": 7.9}, {"load": -1}, {"load": 11.21},
                {"load": float("nan")}, {"builds": [[999, "rustc"]]}, {"memory": float("nan")})):
            with self.subTest(host=host):
                self.host(**host)
                proc, marker = self.gate(f"host-{i}", "--exclusive", "--wait-timeout", "3")
                self.until(lambda: "waiting:" in self.output(proc))
                time.sleep(0.15)
                self.assertFalse(marker.exists())
                self.host(load=11.2, memory=8)
                self.until(marker.exists)
                self.assertEqual(proc.wait(timeout=3), 0)
                self.assertIn("quiet for", self.output(proc))

    def test_unmeasurable_process_scan_times_out_without_launch(self):
        self.state.write_text('{"memory":100,"load":0,"builds":null,"cpus":32}')
        proc, marker = self.gate("unknown-builds", "--exclusive", "--wait-timeout", "0.3")
        self.assertEqual(proc.wait(timeout=3), 2)
        self.assertFalse(marker.exists())
        self.assertIn("timed out", self.output(proc))
        self.assertFalse(any(self.held(i) for i in range(3)))

    def test_busy_sample_resets_quiet_interval(self):
        proc, marker = self.gate("reset", "--exclusive", "--wait-timeout", "3")
        self.until(lambda: "waiting for host readiness" in self.output(proc))
        time.sleep(0.05)
        self.host(load=100)
        self.until(lambda: "load1 100" in self.output(proc))
        self.host()
        time.sleep(0.08)
        self.assertFalse(marker.exists())
        self.until(marker.exists)
        self.assertEqual(proc.wait(timeout=3), 0)

    def test_timeout_and_cancel_while_host_busy_release_every_slot(self):
        self.host(load=100)
        for cancel in (False, True):
            with self.subTest(cancel=cancel):
                proc, marker = self.gate(f"busy-{cancel}", "--exclusive", "--wait-timeout", "0.3")
                self.until(lambda: "load1 100" in self.output(proc))
                self.assertTrue(all(self.held(i) for i in range(3)))
                if cancel:
                    proc.terminate()
                self.assertEqual(proc.wait(timeout=3), -signal.SIGTERM if cancel else 2)
                self.assertFalse(marker.exists())
                self.assertFalse(any(self.held(i) for i in range(3)))

    def test_default_memory_wait_and_per_worktree_serialization_remain(self):
        subprocess.run(["git", "init", "--quiet", str(self.root)], check=True, capture_output=True)
        self.host(memory=1)
        first, marker = self.gate("worktree-first", hold=True, worktree=True)
        self.until(lambda: "GiB needed" in self.output(first))
        self.assertFalse(marker.exists())
        self.host()
        self.until(marker.exists)
        second, second_marker = self.gate("worktree-second", worktree=True)
        self.until(lambda: "another build-slot job runs in this worktree" in self.output(second))
        self.assertFalse(second_marker.exists())
        first.terminate()
        self.assertEqual(first.wait(timeout=3), 143)
        self.until(second_marker.exists)
        self.assertEqual(second.wait(timeout=3), 0)

    def test_waiting_ordinary_does_not_block_exclusive_reservation(self):
        self.host(memory=1)
        ordinary, ordinary_marker = self.gate("memory-waiter")
        self.until(lambda: "GiB needed" in self.output(ordinary))
        exclusive, marker = self.gate("reservation", "--exclusive", "--wait-timeout", "0.3")
        self.until(lambda: "GiB" in self.output(exclusive))
        self.assertFalse(marker.exists())
        self.assertFalse(ordinary_marker.exists())
        self.assertEqual({p.name for p in self.pool.iterdir()}, {"admission"})
        self.assertFalse(any(self.held(i) for i in range(5)),
                         "publishing a memory waiter must acquire no CPU slot")
        ticket, = (self.pool / "admission").glob("wait-*")
        self.assertEqual(json.loads(ticket.read_text())["pid"], ordinary.pid)
        self.assertEqual(exclusive.wait(timeout=3), 2)
        ordinary.terminate()
        self.assertEqual(ordinary.wait(timeout=3), -signal.SIGTERM)
        self.host()
        healthy, healthy_marker = self.gate("healthy-reservation", "--exclusive", "--wait-timeout", "3")
        self.until(lambda: "reserved 5 slots exclusively" in self.output(healthy))
        self.until(healthy_marker.exists)
        self.assertEqual(healthy.wait(timeout=3), 0)

    def test_actual_cli_times_out_before_launch_with_unmodified_probes(self):
        marker = self.root / "real-cli"
        proc = self.spawn([sys.executable, str(GATE), "--exclusive", "--no-worktree-lock",
                           "--wait-timeout", "0.15", "--", sys.executable, "-c", CHILD, str(marker)])
        self.assertEqual(proc.wait(timeout=15), 2)
        self.assertFalse(marker.exists())
        self.assertIn("admission wait timed out", self.output(proc))
        self.assertFalse(any(self.held(i) for i in range(3)))

    def test_default_keeps_parallel_slots_cpu_share_and_unknown_memory_policy(self):
        self.host(memory=None, load=100, builds=[[999, "trustc"]])
        for raw, jobs in ((None, "10"), ("100", "10"), ("2", "2")):
            env = dict(self.env)
            if raw is not None:
                env["CARGO_BUILD_JOBS"] = raw
            proc, marker = self.gate(f"ordinary-{raw}", hold=True, env=env)
            self.until(marker.exists)
            self.assertEqual(json.loads(marker.read_text()), {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": jobs})
        self.assertTrue(all(self.held(i) for i in range(3)))
        fourth, marker = self.gate("fourth")
        self.until(lambda: "waiting for one of 3 slots" in self.output(fourth))
        self.assertFalse(marker.exists())
        self.processes[0].terminate()
        self.assertEqual(self.processes[0].wait(timeout=3), 143)
        self.until(marker.exists)
        self.assertEqual(fourth.wait(timeout=3), 0)

    def test_nested_default_executes_but_exclusive_and_bad_requests_refuse(self):
        for exclusive in (False, True):
            env = dict(self.env, BUILD_SLOT_HELD="1")
            env.pop("CARGO_BUILD_JOBS", None)
            options = ("--exclusive",) if exclusive else ()
            proc, marker = self.gate(f"nested-{exclusive}", *options, env=env)
            self.assertEqual(proc.wait(timeout=3), 2 if exclusive else 0)
            self.assertEqual(marker.exists(), not exclusive)
        for i, options in enumerate((("--exclusive", "--wait-timeout", "nan"),
                                     ("--exclusive", "--wait-timeout", "0"), ("--exclusive", "--wait-timeout"),
                                     ("--exclusive", "--mem-gb", "nan"))):
            proc, marker = self.gate(f"bad-{i}", *options)
            self.assertEqual(proc.wait(timeout=3), 2)
            self.assertFalse(marker.exists())
        self.assertFalse(list(self.pool.iterdir()), "refuse before any admission")

    def test_process_probe_exact_names_and_fail_closed_errors(self):
        loader = importlib.machinery.SourceFileLoader("slot_probe", str(GATE))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        gate = importlib.util.module_from_spec(spec)
        loader.exec_module(gate)
        self.assertEqual((gate.QUIET_LOAD_FRACTION, gate.QUIET_SECONDS), (0.35, 10))
        out = "1 S /bin/python\n2 S /opt/trust/bin/trustc\n3 Z rustc\n4 T cargo\n5 S rustc-wrapper\n"
        with mock.patch.object(gate.subprocess, "run", return_value=mock.Mock(stdout=out)):
            self.assertEqual(gate.build_processes(), [(2, "/opt/trust/bin/trustc"), (4, "cargo")])
        for out in ("", "malformed\n"):
            with mock.patch.object(gate.subprocess, "run", return_value=mock.Mock(stdout=out)):
                self.assertIsNone(gate.build_processes())
        with mock.patch.object(gate.subprocess, "run", side_effect=subprocess.TimeoutExpired("ps", 10)):
            self.assertIsNone(gate.build_processes())

    def test_unknown_cpu_refuses_exclusive_but_default_retains_fallback(self):
        for cpus in (None, 0, -1):
            with self.subTest(cpus=cpus):
                self.host(cpus=cpus, load=0.5, memory=16)
                proc, marker = self.gate(f"cpu-{cpus}", "--exclusive", "--wait-timeout", "1")
                self.assertEqual(proc.wait(timeout=3), 2)
                self.assertFalse(marker.exists())
                self.assertIn("measured positive CPU count", self.output(proc))
                self.assertFalse(list(self.pool.iterdir()), "refuse before any lease")
        self.host(cpus=None, load=0.5, memory=16)
        proc, marker = self.gate("cpu-default")
        self.assertEqual(proc.wait(timeout=3), 0)
        self.assertEqual(json.loads(marker.read_text())["CARGO_BUILD_JOBS"], "1")

    def test_deadline_crossing_between_wait_samples_is_a_timeout(self):
        loader = importlib.machinery.SourceFileLoader("slot_deadline", str(GATE))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        gate = importlib.util.module_from_spec(spec)
        loader.exec_module(gate)
        opened = set()
        real_open = os.open
        real_close = os.close
        def track_open(*args, **kwargs):
            fd = real_open(*args, **kwargs)
            opened.add(fd)
            return fd
        def track_close(fd):
            opened.discard(fd)
            real_close(fd)
        try:
            with mock.patch.dict(os.environ, self.env), mock.patch.object(gate, "DIR", str(self.pool)),                     mock.patch.object(gate, "ADOPTION_DIR", str(self.root / "adopted")), \
                    mock.patch.object(gate, "available_gib", return_value=16), \
                    mock.patch.object(gate, "load1", return_value=100), \
                    mock.patch.object(gate, "build_processes", return_value=[]), \
                    mock.patch.object(gate, "ledger_discovery", return_value=None), \
                    mock.patch.object(gate.os, "open", side_effect=track_open), \
                    mock.patch.object(gate.os, "close", side_effect=track_close), \
                    mock.patch.object(gate.time, "monotonic", side_effect=[0, .1, .2, .3, .999999, 1.000001]), \
                    mock.patch.object(gate.subprocess, "Popen") as child:
                with self.assertRaises(gate.AdmissionTimeout):
                    gate.main(["--exclusive", "--wait-timeout", "1", "--no-worktree-lock", "--", "never-start"])
                child.assert_not_called()
        finally:
            for fd in opened:
                os.close(fd)
        self.assertFalse(any(self.held(i) for i in range(3)))


class ResourceCommandTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="resource-command.")
        self.addCleanup(temporary.cleanup)
        self.runner = Path(temporary.name) / "aterm runner"
        self.runner.touch()
        self.runner.chmod(0o755)
        loader = importlib.machinery.SourceFileLoader("resource_gate", str(GATE))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        self.gate = importlib.util.module_from_spec(spec)
        loader.exec_module(self.gate)
        self.command = ["native-compiler", "--argument=must-not-be-in-job-label"]
        self.env = {"ATERM_CHILD": "1", "PATH": "/tool/bin"}

    def capability(self, text, returncode=0):
        return subprocess.CompletedProcess([], returncode, stdout=text, stderr="")

    def test_no_aterm_context_performs_no_probe(self):
        with mock.patch.object(self.gate.subprocess, "run") as run:
            self.assertEqual(self.gate.resource_command(self.command, {}), self.command)
        run.assert_not_called()

    def test_explicit_discovery_cli_does_not_need_the_compiler_path(self):
        env = dict(self.env, BUILD_SLOT_ATERM_CLI=str(self.runner))
        record = "OK resources version=1 runner=" + quote(str(self.runner), safe="")
        with mock.patch.object(self.gate.shutil, "which", return_value=None) as which, \
                mock.patch.object(self.gate.subprocess, "run", return_value=self.capability(record)) as run:
            result = self.gate.resource_command(self.command, env)
        which.assert_not_called()
        self.assertEqual(run.call_args.args[0],
                         [str(self.runner), "ctl", "@self", "resources", "capabilities"])
        self.assertEqual(result[result.index("--") + 1:], self.command)

    def test_invalid_explicit_discovery_cli_never_falls_back_to_path(self):
        for cli in ("relative/aterm", str(self.runner.parent), str(self.runner.parent / "missing")):
            with self.subTest(cli=cli), \
                    mock.patch.object(self.gate.shutil, "which", return_value=str(self.runner)) as which, \
                    mock.patch.object(self.gate.subprocess, "run") as run:
                result = self.gate.resource_command(self.command, dict(self.env, BUILD_SLOT_ATERM_CLI=cli))
            self.assertEqual(result, self.command)
            which.assert_not_called()
            run.assert_not_called()

    def test_malformed_or_unsupported_capabilities_never_launch_a_runner(self):
        path = quote(str(self.runner), safe="")
        records = ["", "OK version=1", "OK resources version=2 runner=" + path,
                   "OK resources version=1 version=1 runner=" + path,
                   "OK resources version=1 available=0 runner=" + path,
                   "OK resources version=1 available=unknown runner=" + path,
                   "OK resources capabilities capabilities version=1 runner=" + path,
                   "OK resources version=1 runner=relative",
                   "OK resources version=1 runner=%GG",
                   "OK resources version=1 runner=%00",
                   "OK resources version=1 runner=" + quote(str(self.runner.parent / "missing"), safe="")]
        for record in records:
            with self.subTest(record=record), \
                    mock.patch.object(self.gate.shutil, "which", return_value="/cli/aterm"), \
                    mock.patch.object(self.gate.subprocess, "run", return_value=self.capability(record)):
                self.assertEqual(self.gate.resource_command(self.command, self.env), self.command)

    def test_control_errors_are_unreported_without_an_unknown_command_probe(self):
        for error in (subprocess.TimeoutExpired("ctl", 5), OSError("control unavailable"),
                      UnicodeDecodeError("utf8", b"\xff", 0, 1, "invalid response")):
            with self.subTest(error=type(error).__name__), \
                    mock.patch.object(self.gate.shutil, "which", return_value="/cli/aterm"), \
                    mock.patch.object(self.gate.subprocess, "run", side_effect=error) as run:
                self.assertEqual(self.gate.resource_command(self.command, self.env), self.command)
            self.assertEqual(run.call_args.args[0],
                             ["/cli/aterm", "ctl", "@self", "resources", "capabilities"])

    def test_reported_runner_and_host_ai_default_preserve_original_arguments(self):
        record = "OK resources version=1 runner=" + quote(str(self.runner), safe="") + " ai=claude"
        for env in (self.env, {"ATERM_PARENT_SESSION_ID": "s-parent", "PATH": "/tool/bin"}):
            with self.subTest(context=env), \
                    mock.patch.object(self.gate.shutil, "which", return_value="/older/client/aterm"), \
                    mock.patch.object(self.gate.subprocess, "run", return_value=self.capability(record)):
                result = self.gate.resource_command(self.command, env)
            self.assertEqual(result[:4], [str(self.runner), "resource-run", "--session", "@self"])
            self.assertNotIn("--ai", result, "authenticated target derives the AI default")
            self.assertEqual(result[result.index("--") + 1:], self.command)
            self.assertNotIn(self.command[1], result[result.index("--job") + 1])

    def test_valid_native_path_names_fit_the_host_job_label_contract(self):
        record = "OK resources version=1 runner=" + quote(str(self.runner), safe="")
        cases = [("a" * 255, "compiler"), ("λ" * 120, "compiler"),
                 ("work\n\x1bdir", "compiler\tname"), ("bytes-\udcff", "compiler"),
                 (" " * 240 + "x", "compiler"), ("a" * 199, "🦀" * 40)]
        for directory, executable in cases:
            command = ["/bin/" + executable, "", "--argument=kept-exactly"]
            with self.subTest(directory=repr(directory), executable=executable), \
                    mock.patch.object(self.gate.os, "getcwd", return_value="/tmp/" + directory), \
                    mock.patch.object(self.gate.shutil, "which", return_value="/cli/aterm"), \
                    mock.patch.object(self.gate.subprocess, "run", return_value=self.capability(record)):
                result = self.gate.resource_command(command, self.env)
            label = result[result.index("--job") + 1]
            self.assertTrue(label.strip(), "the host refuses an empty job label")
            self.assertLessEqual(len(label.encode("utf-8")), 200, "the host's byte limit")
            self.assertFalse(any(ord(c) < 32 or 0x7f <= ord(c) <= 0x9f for c in label),
                             "the host refuses control characters")
            self.assertEqual(result[result.index("--") + 1:], command)


if __name__ == "__main__":
    unittest.main()
