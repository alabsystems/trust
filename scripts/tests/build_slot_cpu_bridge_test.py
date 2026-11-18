#!/usr/bin/env python3
"""Private native/fixed reservation fixtures; never touch the host CPU pool."""
import fcntl
from contextlib import ExitStack
import importlib.machinery
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import subprocess
import unittest
from unittest import mock

from build_slot_test import (WRAPPER, write_python_program, isolate_resource_environment,
                             launcher_directories)

SCRIPT = Path(__file__).resolve().parents[1] / "build-slot"


class CpuBridgeTests(unittest.TestCase):
    def setUp(self):
        isolate_resource_environment(self)
        self.tmp = tempfile.TemporaryDirectory(prefix="cpu-bridge-")
        self.root = Path(self.tmp.name)
        loader = importlib.machinery.SourceFileLoader("cpu_bridge_gate", str(SCRIPT))
        spec = importlib.util.spec_from_loader(loader.name, loader)
        self.gate = importlib.util.module_from_spec(spec)
        loader.exec_module(self.gate)
        self.native = self.root / "native"
        self.external = self.root / "external"
        self.external.mkdir(mode=0o700)
        self.fds = []
        self.gate.cpu_capacity_directory = lambda: str(self.native)

    def tearDown(self):
        for fd in self.fds:
            os.close(fd)
        self.tmp.cleanup()

    def held(self, path, row):
        fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
        os.write(fd, json.dumps(row).encode())
        fcntl.flock(fd, fcntl.LOCK_EX)
        self.fds.append(fd)
        return fd

    def pool(self, cpus=4):
        self.native.mkdir(mode=0o700)
        rows = [f"trust-build-cpu-v1 slots={cpus}"]
        for i in range(cpus):
            path = self.native / f"slot-{i:08x}"
            path.touch(mode=0o600)
            stat = path.stat()
            rows.append(f"slot={i} dev={stat.st_dev} ino={stat.st_ino}")
        (self.native / "pool").write_text("\n".join(rows) + "\n")
        (self.native / "pool").chmod(0o600)

    def record(self, mode="fixed-v1", budget=2, lease="1" * 32):
        return dict(cpu_mode=mode, cpu_budget=budget, lease_id=lease, pool_slots=4)

    def automatic(self, waiter, maximum=4):
        return waiter.attempt(
            lambda pending: self.gate.try_command_claim(
                waiter.required["worktree"], 4, False, 1, maximum, pending),
            128, borrow=True)

    def release_claim(self, claim):
        for _, fd in claim:
            os.close(fd)

    def test_optional_borrowing_leaves_minimum_real_leases_for_live_peers(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        for peers in (0, 1, 3):
            with self.subTest(peers=peers), ExitStack() as stack:
                head = stack.enter_context(self.gate.AdmissionWaiter("head", slots=4))
                self.assertIsNone(head.attempt(lambda: None, 128))
                queued = []
                for index in range(peers):
                    peer = stack.enter_context(self.gate.AdmissionWaiter(str(index), slots=4))
                    self.assertIsNone(peer.attempt(lambda: None, 128))
                    queued.append(peer)
                claim = self.automatic(head)
                self.assertEqual(len(claim) - 1, 4 - peers)
                try:
                    for peer in queued:
                        other = peer.attempt(
                            lambda: self.gate.try_command_claim(None, 4, False, 1), 128)
                        self.assertIsNotNone(other, "pending minimum must have a real free slot")
                        self.release_claim(other)
                finally:
                    self.release_claim(claim)

    def test_pending_reservation_uses_free_slots_not_nominal_pool_width(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        busy = self.held(self.external / "slot-0", {})
        with self.gate.AdmissionWaiter("head", slots=4) as head, \
             self.gate.AdmissionWaiter("weighted peer", slots=4, needed=2) as peer:
            self.assertIsNone(head.attempt(lambda: None, 128))
            self.assertIsNone(peer.attempt(lambda: None, 128))
            claim = self.automatic(head)
            self.assertEqual(len(claim) - 1, 1)
            try:
                other = peer.attempt(
                    lambda: self.gate.try_command_claim(None, 4, False, 2), 128)
                self.assertIsNotNone(other)
                self.release_claim(other)
            finally:
                self.release_claim(claim)

    def test_optional_borrowing_preserves_slots_in_a_peers_smaller_pool(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        with self.gate.AdmissionWaiter("head", slots=4) as head, \
             self.gate.AdmissionWaiter("smaller pool peer", slots=2) as peer:
            self.assertIsNone(head.attempt(lambda: None, 128))
            self.assertIsNone(peer.attempt(lambda: None, 128))
            claim = self.automatic(head)
            try:
                self.assertEqual(len(claim) - 1, 3)
                other = peer.attempt(
                    lambda: self.gate.try_command_claim(None, 2, False, 1), 128)
                self.assertIsNotNone(other, "a free slot outside the peer's pool cannot back its minimum")
                self.release_claim(other)
            finally:
                self.release_claim(claim)

    def test_optional_borrow_failure_closes_own_and_peer_probe_descriptions(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        with self.gate.AdmissionWaiter("head", slots=4) as head, \
             self.gate.AdmissionWaiter("smaller pool peer", slots=2) as peer:
            self.assertIsNone(head.attempt(lambda: None, 128))
            self.assertIsNone(peer.attempt(lambda: None, 128))
            original = self.gate.try_shared_slots
            def interrupted(slots, needed, *args, **kwargs):
                if needed == 0:
                    raise OSError("injected optional acquisition failure")
                return original(slots, needed, *args, **kwargs)
            with mock.patch.object(self.gate, "try_shared_slots", side_effect=interrupted):
                with self.assertRaisesRegex(OSError, "injected optional acquisition failure"):
                    self.automatic(head)
            for index in range(4):
                fd = self.gate.try_lease(str(self.external / f"slot-{index}"))
                self.assertIsNotNone(fd, "failed borrowing retained a minimum/probe lock")
                os.close(fd)
            fd = self.gate.try_lease(str(self.external / "admission.lock"))
            self.assertIsNotNone(fd, "failed borrowing retained admission")
            os.close(fd)

    def test_ineligible_dead_and_same_worktree_peers_do_not_strand_borrowing(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        worktree = str(self.root / "worktree.lock")
        for kind in ("memory", "dead", "same-worktree", "busy-worktree"):
            with self.subTest(kind=kind), ExitStack() as stack:
                own_worktree = worktree if kind == "same-worktree" else None
                head = stack.enter_context(self.gate.AdmissionWaiter("head", slots=4, worktree=own_worktree))
                self.assertIsNone(head.attempt(lambda: None, 128))
                peer = stack.enter_context(self.gate.AdmissionWaiter(
                    "peer", slots=4, memory=256 if kind == "memory" else 0,
                    worktree=worktree if "worktree" in kind else None))
                self.assertIsNone(peer.attempt(lambda: None, 128))
                if kind == "dead":
                    os.close(peer.fd)
                    peer.fd = None  # leave the stale ticket; the real lock proves death
                elif kind == "busy-worktree":
                    held = self.gate.try_lease(worktree)
                    stack.callback(os.close, held)
                claim = self.automatic(head)
                self.assertEqual(len(claim) - (2 if own_worktree else 1), 4)
                self.release_claim(claim)

    def test_unreadable_live_peer_prevents_optional_borrowing(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        with self.gate.AdmissionWaiter("head", slots=4) as head, \
             self.gate.AdmissionWaiter("unreadable", slots=4) as peer:
            self.assertIsNone(head.attempt(lambda: None, 128))
            self.assertIsNone(peer.attempt(lambda: None, 128))
            os.ftruncate(peer.fd, 0)
            claim = self.automatic(head)
            self.assertEqual(len(claim) - 1, 1)
            self.release_claim(claim)

    def test_nonparallel_successors_do_not_strand_optional_capacity(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        for kind in ("full-width", "exclusive", "native"):
            with self.subTest(kind=kind), ExitStack() as stack:
                head = stack.enter_context(self.gate.AdmissionWaiter("head", slots=4))
                self.assertIsNone(head.attempt(lambda: None, 128))
                if kind == "native":
                    peer = stack.enter_context(self.gate.NativeEpochWaiter(
                        str(self.external), 4, "native", 0))
                    self.assertIsNone(peer.attempt(128))
                else:
                    peer = stack.enter_context(self.gate.AdmissionWaiter(
                        kind, slots=4, needed=4 if kind == "full-width" else 1,
                        exclusive=kind == "exclusive"))
                    self.assertIsNone(peer.attempt(lambda: None, 128))
                claim = self.automatic(head)
                self.assertEqual(len(claim) - 1, 4)
                self.release_claim(claim)

    def test_fixed_budget_waits_for_native_workers_and_ignores_stale_records(self):
        self.pool()
        stale = self.external / "slot-9"
        stale.write_text("broken stale metadata")
        stale.chmod(0o644)  # the launcher's own slot-file mode, whatever this runner's umask
        self.held(self.external / "slot-0", self.record())
        native = [self.held(self.native / f"slot-{i:08x}", {}) for i in range(3)]
        self.assertFalse(self.gate.native_cpu_room(str(self.external), 4, 4))
        fcntl.flock(native[-1], fcntl.LOCK_UN)
        self.assertTrue(self.gate.native_cpu_room(str(self.external), 4, 4))

    def test_new_records_deduplicate_and_cooperative_roots_reserve_no_fixed_width(self):
        self.held(self.external / "slot-0", self.record())
        self.held(self.external / "slot-1", self.record())
        self.held(self.external / "slot-2", self.record("workers-v1", 1, "2" * 32))
        self.assertEqual(self.gate.fixed_cpu_reservations(str(self.external), 4, 4), 2)
        self.held(self.external / "slot-3", {"pid": 44, "cmd": "legacy", "cwd": "/fixture", "started": 0})
        self.assertEqual(self.gate.fixed_cpu_reservations(str(self.external), 4, 4), 3)

    def test_exclusive_fence_reserves_the_host_before_individual_slots_drain(self):
        self.held(self.external / "admission.lock", {})
        self.assertEqual(self.gate.fixed_cpu_reservations(str(self.external), 4, 4), 4)

    def test_unknown_or_conflicting_held_records_refuse(self):
        for row in ({}, self.record("unknown"), self.record(budget=True), self.record(mode=None)):
            path = self.external / "slot-0"
            fd = self.held(path, row)
            with self.assertRaises(self.gate.CpuBridgeUnavailable):
                self.gate.fixed_cpu_reservations(str(self.external), 4, 4)
            fcntl.flock(fd, fcntl.LOCK_UN)
            path.unlink()
        self.held(self.external / "slot-0", self.record())
        self.held(self.external / "slot-1", self.record(budget=3))
        with self.assertRaises(self.gate.CpuBridgeUnavailable):
            self.gate.fixed_cpu_reservations(str(self.external), 4, 4)

    def test_replaced_native_slot_is_not_new_capacity(self):
        self.pool()
        path = self.native / "slot-00000000"
        path.rename(self.native / "old-slot")
        path.touch(mode=0o600)
        with self.assertRaises(self.gate.CpuBridgeUnavailable):
            self.gate.native_cpu_room(str(self.external), 4, 4)

    def test_capability_probe_follows_selected_shim_without_parsing_it(self):
        path = self.root / "targo"
        path.write_text('#!/bin/sh\nprintf \'%s\\n\' \'{"version":3,"cpu_workers":true,"supports_invocation":true}\'\n')
        path.chmod(0o700)
        self.assertTrue(self.gate.worker_capability([str(path), "--unverified", "build"]))
        path.write_text('#!/bin/sh\nprintf \'%s\\n\' \'{"version":1,"cpu_workers":1}\'\n')
        with self.assertRaises(self.gate.CpuBridgeUnavailable):
            self.gate.worker_capability([str(path), "--unverified", "build"])
        self.assertFalse(self.gate.worker_capability([sys.executable]))
        nested = "[" * 2000 + "]" * 2000
        write_python_program(path, f"print({nested!r})\n")
        with self.assertRaises(self.gate.CpuBridgeUnavailable):
            self.gate.worker_capability([str(path), "--unverified", "build"])

    def test_old_driver_only_capability_does_not_authorize_any_native_command(self):
        program = self.root / "targo"
        for version in (1, 2):
            value = ({"version": 1, "cpu_workers": True,
                      "supported_commands": ["build", "check"], "supported_lanes": ["unverified"]}
                     if version == 1 else {"version": 2, "cpu_workers": True,
                                           "supports_invocation": True})
            write_python_program(program, f'print({json.dumps(value)!r})\n')
            program.chmod(0o700)
            for command in ("build", "check", "test"):
                with self.assertRaises(self.gate.CpuBridgeUnavailable):
                    self.gate.worker_capability([str(program), "--unverified", command, "--lib"])

    def test_capability_timeout_kills_and_reaps_only_its_probe(self):
        path = self.root / "targo"
        marker = self.root / "pid"
        path.write_text(f'#!/bin/sh\nprintf "%s" "$$" > "{marker}"\nexec /bin/sleep 30\n')
        path.chmod(0o700)
        start = time.monotonic()
        with self.assertRaisesRegex(self.gate.CpuBridgeUnavailable, "timed out"):
            self.gate.worker_capability([str(path), "--unverified", "build"])
        self.assertLess(time.monotonic() - start, 4)
        with self.assertRaises(ProcessLookupError):
            os.kill(int(marker.read_text()), 0)

    def test_failed_discovery_cannot_claim_or_launch_fixed_work(self):
        program = self.root / "targo"
        launched = self.root / "command-launched"
        failures = [
            ("pass\n", "failed"),
            ("import sys\nsys.stderr.write('original diagnostic')\nsys.exit(7)\n", "status 7"),
            ("print('not json')\n", "failed"),
            ("print('x' * 8193)\n", "stdout bound"),
            ("import sys\nsys.stderr.write('x' * 8193)\n", "stderr bound"),
            ('print(\'{"version":3,"cpu_workers":false,"supports_invocation":true}\')\n', "invalid"),
            ('print(\'{"version":3,"cpu_workers":true,"supports_invocation":true,"supports_invocation":false}\')\n', "duplicate"),
            ('print(\'{"version":3,"cpu_workers":true,"supports_invocation":true,"runtime_refusal":"native refusal retained"}\')\n', "native refusal retained"),
        ]
        for source, reason in failures:
            with self.subTest(reason=reason, source=source):
                write_python_program(program,
                    "import pathlib, sys\n"
                    "if '--resource-capabilities' not in sys.argv:\n"
                    f" pathlib.Path({str(launched)!r}).touch()\n"
                    "else:\n" + "".join(" " + line + "\n" for line in source.splitlines()))
                with mock.patch.dict(os.environ, {"BUILD_SLOT_DIR": str(self.external)}, clear=True), \
                     mock.patch.object(self.gate, "MEASURED_NCPU", 4), \
                     mock.patch.object(self.gate, "worktree_lock_path", return_value=None), \
                     mock.patch.object(self.gate, "try_command_claim", side_effect=AssertionError("claimed")), \
                     mock.patch.object(self.gate, "AdmissionWaiter", side_effect=AssertionError("queued")):
                    with self.assertRaisesRegex(self.gate.CpuBridgeUnavailable, reason) as failure:
                        self.gate.main(["--", str(program), "--unverified", "build"])
                if "original diagnostic" in source:
                    self.assertIn("original diagnostic", str(failure.exception))
                if "not json" in source:
                    self.assertIn("not json", str(failure.exception))
                self.assertLess(len(str(failure.exception)), 9000)
                self.assertFalse(launched.exists())
                self.assertEqual(list(self.external.iterdir()), [])

    def test_explicit_unsupported_capability_remains_distinct_from_missing_program(self):
        program = self.root / "targo"
        for cpu, invocation in [(False, False), (True, False)]:
            write_python_program(program,
                f'print({json.dumps(dict(version=3, cpu_workers=cpu, supports_invocation=invocation))!r})\n')
            self.assertFalse(self.gate.worker_capability([str(program), "--unverified", "build"]))
        program.unlink()
        with self.assertRaisesRegex(self.gate.CpuBridgeUnavailable, "unavailable"):
            self.gate.worker_capability([str(program), "--unverified", "build"])

    def test_capability_descendant_pipe_cannot_outlive_the_original_deadline(self):
        program = self.root / "targo"
        descendant = self.root / "descendant"
        write_python_program(program,
            "import os, pathlib, signal, time\n"
            "if os.fork() == 0:\n"
            " signal.alarm(5)\n"
            f" pathlib.Path({str(descendant)!r}).write_text(str(os.getpid()))\n"
            " time.sleep(30)\n"
            " os._exit(0)\n"
            "print('{\"version\":3,\"cpu_workers\":true,\"supports_invocation\":true}', flush=True)\n")
        unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])
        try:
            start = time.monotonic()
            with self.assertRaisesRegex(self.gate.CpuBridgeUnavailable, "timed out"):
                self.gate.worker_capability([str(program), "--unverified", "build"])
            self.assertLess(time.monotonic() - start, 4)
            self.assertIsNone(unrelated.poll(), "only the probe's owned group may be stopped")
            # The descendant is no longer runnable. On Darwin an orphaned
            # zombie can remain visible briefly until launchd reaps it.
            state = subprocess.run(["ps", "-o", "stat=", "-p", descendant.read_text()],
                                   capture_output=True, text=True, timeout=1)
            self.assertFalse(state.stdout.strip() and not state.stdout.strip().startswith("Z"),
                             state.stdout)
        finally:
            unrelated.kill()
            unrelated.wait()

    def test_explicit_unsupported_worker_cohort_refuses_before_claim_or_launch(self):
        with mock.patch.dict(os.environ, {"BUILD_SLOT_DIR": str(self.external)}, clear=True), \
             mock.patch.object(self.gate, "worker_capability", return_value=False), \
             mock.patch.object(self.gate, "available_gib", return_value=128), \
             mock.patch.object(self.gate, "worktree_lock_path", return_value=None), \
             mock.patch.object(self.gate, "try_command_claim", side_effect=AssertionError("claimed")), \
             mock.patch.object(self.gate.subprocess, "Popen", side_effect=AssertionError("launched")):
            for command in ("build", "check", "test", "run", "doc"):
                with self.subTest(command=command):
                    self.assertEqual(self.gate.main([
                        "--", "targo", "--resource-worker-v2", "--unverified", command
                    ]), 2)
        self.assertEqual(list(self.external.iterdir()), [])

    def test_main_publishes_modes_and_preserves_explicit_caps(self):
        cases = [(True, [], 28, {}), (False, [], 28, {}),
                 (True, ["--cpus", "14"], 14, {}),
                 (True, [], 28, {"CARGO_BUILD_JOBS": "28", "TARGO_PLANNED_JOBS": "28"}),
                 (True, [], 7, {"CARGO_BUILD_JOBS": "7", "TARGO_PLANNED_JOBS": "7"}),
                 (True, [], 3, {"CARGO_BUILD_JOBS": "3"}),
                 (True, [], 3, {"CARGO_BUILD_JOBS": "28", "TARGO_PLANNED_JOBS": "28", "TARGO_CALLER_JOBS": "3"})]
        for serial, (cooperative, extra, expected, incoming) in enumerate(cases):
            with self.subTest(cooperative=cooperative, extra=extra):
                directory = self.root / f"run-{serial}"
                # A namespace an older launcher made under umask 022 stays admitted.
                launcher_directories(directory)
                captured = {}
                # main() observes the original child's exit without reaping it
                # before forwarding stops and wait() reaps. Fake pid 42 is no
                # child of this process, so the real observer fails closed with
                # ECHILD by design; record the observation and its order.
                order = []
                # main() owns every descriptor it transfers to the child and
                # closes each once after the child's exit (fdb293a14d,
                # ADMISSION-RECOVERY-1). Record closes, and where launch fell
                # among them, instead of closing them again here: a second
                # close could hit a reused descriptor number.
                closed = []
                real_close = os.close
                def record_close(fd):
                    real_close(fd)
                    closed.append(fd)
                class Child:
                    pid = 42
                    def __init__(self, cmd, **kwargs):
                        captured.update(kwargs)
                        captured["command"] = cmd
                        captured["closes_before_launch"] = len(closed)
                    def wait(self):
                        order.append(("wait",))
                        return 0
                observe = mock.Mock(side_effect=lambda pid: order.append(("observe", pid)))
                self.gate.NCPU = self.gate.MEASURED_NCPU = 28
                self.gate.ADOPTION_DIR = str(self.root / "adopted")
                with mock.patch.dict(os.environ, {"BUILD_SLOT_DIR": str(directory), **incoming}, clear=True), \
                     mock.patch.object(self.gate, "worker_capability", return_value=cooperative), \
                     mock.patch.object(self.gate, "available_gib", return_value=128), \
                     mock.patch.object(self.gate, "worktree_lock_path", return_value=None), \
                     mock.patch.object(self.gate.subprocess, "Popen", Child), \
                     mock.patch.object(self.gate, "original_child_exit_observer",
                                       return_value=observe) as exit_observer, \
                     mock.patch.object(self.gate.signal, "signal"):
                    try:
                        with mock.patch.object(self.gate.os, "close", side_effect=record_close):
                            self.assertEqual(self.gate.main([*extra, "--", "targo", "--unverified", "build"]), 0)
                        after_launch = closed[captured["closes_before_launch"]:]
                        self.assertTrue(captured["pass_fds"])
                        self.assertEqual(sorted(after_launch), sorted(captured["pass_fds"]),
                                         "each transferred descriptor is closed once, after the child")
                        exit_observer.assert_called_once_with()
                        observe.assert_called_once_with(42)
                        self.assertEqual(order, [("observe", 42), ("wait",)])
                        env = captured["env"]
                        mode = "workers-v1" if cooperative else "fixed-v1"
                        self.assertEqual(env["CARGO_BUILD_JOBS"], str(expected))
                        self.assertEqual(env["TARGO_PLANNED_JOBS"], str(expected))
                        if "TARGO_CALLER_JOBS" in incoming:
                            self.assertEqual(env["TARGO_CALLER_JOBS"], incoming["TARGO_CALLER_JOBS"])
                        self.assertEqual(env["BUILD_SLOT_CPU_MODE"], mode)
                        resource_dir = directory / "runtime-v2" if cooperative else directory
                        rows = [json.loads(p.read_text()) for p in resource_dir.glob("slot-*")]
                        self.assertEqual(len(rows), 2 if extra else (1 if cooperative else 4))
                        self.assertTrue(all(r["cpu_mode"] == mode for r in rows))
                        self.assertEqual(len({r["lease_id"] for r in rows}), 1)
                        if cooperative:
                            self.assertEqual(env["BUILD_SLOT_CPU_PROTOCOL"], "2")
                            self.assertEqual(captured["command"][1], "--resource-worker-v2")
                            self.assertEqual(len(env["BUILD_SLOT_FENCE_FDS"].split(",")), 5)
                            self.assertEqual(env["BUILD_SLOT_DIR"], os.path.realpath(directory))
                            self.assertEqual(env["BUILD_SLOT_V2_DIR"], os.path.realpath(directory / "runtime-v2"))
                            self.assertEqual(env["BUILD_SLOT_POOL_SLOTS"], "4")
                    finally:
                        # Only on a failure path: release what main did not close.
                        launched = captured.get("closes_before_launch")
                        released = closed[launched:] if launched is not None else []
                        for fd in captured.get("pass_fds", []):
                            if fd not in released:
                                real_close(fd)

    def test_nested_native_requires_capability_and_installs_one_mandatory_flag(self):
        program = self.root / "targo"
        program.write_text('#!/bin/sh\nprintf \'%s\\n\' \'{"version":3,"cpu_workers":true,"supports_invocation":true}\'\n')
        program.chmod(0o700)
        class Executed(Exception): pass
        for command in ("build", "check"):
            for flagged in (False, True):
                args = [str(program), *(["--resource-worker-v2"] if flagged else []),
                        "--unverified", command, "-p", "crate with spaces"]
                environment = {"BUILD_SLOT_HELD": "1", "BUILD_SLOT_CPU_PROTOCOL": "2",
                               "CARGO_BUILD_JOBS": "7", "TARGO_PLANNED_JOBS": "7",
                               "TARGO_CALLER_JOBS": "3"}
                with self.subTest(command=command, flagged=flagged), \
                     mock.patch.dict(os.environ, environment, clear=True), \
                     mock.patch.object(self.gate.os, "execvp", side_effect=Executed) as execute:
                    with self.assertRaises(Executed):
                        self.gate.main(["--", *args])
                    self.assertEqual(execute.call_args.args,
                                     (str(program), [str(program), "--resource-worker-v2",
                                                     "--unverified", command, "-p", "crate with spaces"]))
                    self.assertEqual(os.environ["TARGO_CALLER_JOBS"], "3")
                    self.assertEqual(os.environ["CARGO_BUILD_JOBS"], "7")
                    self.assertEqual(os.environ["TARGO_PLANNED_JOBS"], "7")

    def test_nested_native_refuses_unknown_or_exclusive_before_launch(self):
        environment = {"BUILD_SLOT_HELD": "1", "BUILD_SLOT_CPU_PROTOCOL": "2",
                       "BUILD_SLOT_EXCLUSIVE": "1"}
        cases = [["--", "python", "sweep.py"],
                 ["--", "targo", "--unverified", "doc"],
                 ["--", "targo", "trust", "build"],
                 ["--", "targo", "--resource-worker-v2", "--resource-worker-v2", "--unverified", "build"],
                 ["--exclusive", "--", "targo", "--unverified", "build"]]
        with mock.patch.dict(os.environ, environment, clear=True), \
             mock.patch.object(self.gate.os, "execvp", side_effect=AssertionError("launched")), \
             mock.patch.object(self.gate.subprocess, "Popen", side_effect=AssertionError("probed unsupported command")):
            for args in cases:
                with self.subTest(args=args):
                    # Targo's own parser judges a `targo` invocation (7c40278d3b), so
                    # these reach its query, and with no selected Targo here they are
                    # refused by CpuBridgeUnavailable, which the entry exits 2 for.
                    try:
                        status = self.gate.main(args)
                    except self.gate.CpuBridgeUnavailable:
                        status = 2
                    self.assertEqual(status, 2)
        # Even the right command shape must prove actual capability.
        with mock.patch.dict(os.environ, environment, clear=True), \
             mock.patch.object(self.gate, "worker_capability", return_value=False), \
             mock.patch.object(self.gate.os, "execvp", side_effect=AssertionError("launched")):
            self.assertEqual(self.gate.main(["--", "targo", "--unverified", "build"]), 2)

    def test_nested_native_explicit_cpu_shrink_preserves_stricter_caller_cap(self):
        class Executed(Exception): pass
        environment = {"BUILD_SLOT_HELD": "1", "BUILD_SLOT_CPU_PROTOCOL": "2",
                       "CARGO_BUILD_JOBS": "7", "TARGO_PLANNED_JOBS": "7",
                       "TARGO_CALLER_JOBS": "2"}
        with mock.patch.dict(os.environ, environment, clear=True), \
             mock.patch.object(self.gate, "worker_capability", return_value=True), \
             mock.patch.object(self.gate.os, "execvp", side_effect=Executed):
            with self.assertRaises(Executed):
                self.gate.main(["--cpus", "3", "--", "targo", "--unverified", "build"])
            self.assertEqual(os.environ["CARGO_BUILD_JOBS"], "3")
            self.assertEqual(os.environ["TARGO_PLANNED_JOBS"], "3")
            self.assertEqual(os.environ["TARGO_CALLER_JOBS"], "2")

    def test_legacy_fence_waits_for_old_holders_and_allows_native_peers(self):
        self.gate.NCPU = self.gate.MEASURED_NCPU = 28
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        old = self.held(self.external / "slot-0", {})
        self.assertIsNone(self.gate.try_legacy_fence(str(self.external), 4))
        fcntl.flock(old, fcntl.LOCK_UN)
        first = self.gate.try_legacy_fence(str(self.external), 4)
        second = self.gate.try_legacy_fence(str(self.external), 4)
        self.assertIsNotNone(first)
        self.assertIsNotNone(second)
        self.assertIsNone(self.gate.try_lease(str(self.external / "slot-0")))
        for fd in first: os.close(fd)
        self.assertIsNone(self.gate.try_lease(str(self.external / "slot-0")))
        for fd in second: os.close(fd)
        available = self.gate.try_lease(str(self.external / "slot-0"))
        self.assertIsNotNone(available)
        os.close(available)

    def test_child_inheritance_retains_legacy_fence_after_supervisor_closes(self):
        self.gate.NCPU = self.gate.MEASURED_NCPU = 28
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        fence = self.gate.try_legacy_fence(str(self.external), 4)
        child = subprocess.Popen([sys.executable, "-c", "import sys; sys.stdin.buffer.read()"],
                                 stdin=subprocess.PIPE, pass_fds=fence)
        try:
            for fd in fence: os.close(fd)
            self.assertIsNone(self.gate.try_lease(str(self.external / "slot-0")))
            child.stdin.close()
            child.wait(timeout=5)
            available = self.gate.try_lease(str(self.external / "slot-0"))
            self.assertIsNotNone(available)
            os.close(available)
        finally:
            if child.poll() is None: child.kill()
            child.wait()

    def test_registered_legacy_waiter_stops_new_native_epoch_joins(self):
        self.gate.NCPU = self.gate.MEASURED_NCPU = 28
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        self.gate.DIR = str(self.external)
        with self.gate.AdmissionWaiter("legacy", slots=4) as waiter:
            self.assertIsNone(waiter.attempt(lambda: None, 128))
            self.assertIsNone(self.gate.try_legacy_fence(str(self.external), 4))
        fence = self.gate.try_legacy_fence(str(self.external), 4)
        self.assertIsNotNone(fence)
        for fd in fence: os.close(fd)

    def test_native_epoch_queues_before_new_fixed_requests_and_drains_holder(self):
        self.gate.DIR = str(self.external)
        self.gate.NCPU = self.gate.MEASURED_NCPU = 12
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        # A real child retains the old fixed slot. The second slot stays free,
        # so a newer fixed request would otherwise overtake the native root.
        old = self.held(self.external / "slot-0", {})
        child = subprocess.Popen([sys.executable, "-c", "import sys; sys.stdin.buffer.read()"],
                                 stdin=subprocess.PIPE, pass_fds=[old])
        self.fds.remove(old)
        os.close(old)
        try:
            with self.gate.NativeEpochWaiter(str(self.external), 2, "native", 4) as native, \
                 self.gate.AdmissionWaiter("new fixed", slots=2) as fixed:
                self.assertIsNone(native.attempt(128))
                # Its real exclusive admission lease is visible while draining.
                self.assertIsNotNone(native.barrier)
                record = json.loads((self.external / "admission.lock").read_text())
                self.assertEqual(record["pid"], os.getpid())
                self.assertIs(record["native_epoch_transition"], True)
                self.assertIsNone(self.gate.try_lease(str(self.external / "admission.lock")))
                with self.assertRaises(BlockingIOError):
                    fixed.attempt(lambda: self.gate.try_command_claim(None, 2, False, 1), 128)
                child.stdin.close()
                child.wait(timeout=5)
                fence = native.attempt(128)
                self.assertEqual(len(fence), 3)
                try:
                    self.assertIsNone(self.gate.try_lease(str(self.external / "slot-0")))
                    with self.assertRaises(BlockingIOError):
                        fixed.attempt(lambda: self.gate.try_command_claim(None, 2, False, 1), 128)
                finally:
                    for fd in fence: os.close(fd)
                claim = fixed.attempt(lambda: self.gate.try_command_claim(None, 2, False, 1), 128)
                self.assertTrue(claim)
                for _, fd in claim: os.close(fd)
            self.assertEqual(list((self.external / "admission").glob("wait-*")), [])
        finally:
            if child.stdin and not child.stdin.closed: child.stdin.close()
            if child.poll() is None: child.kill()
            child.wait()

    def test_native_epoch_preserves_older_eligible_fixed_priority(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        with self.gate.AdmissionWaiter("old fixed", slots=2) as old, \
             self.gate.NativeEpochWaiter(str(self.external), 2, "native", 4) as native, \
             self.gate.AdmissionWaiter("new fixed", slots=2) as newer:
            self.assertIsNone(old.attempt(lambda: None, 128))
            self.assertIsNone(native.attempt(128))
            self.assertIsNone(native.barrier)
            self.assertTrue(Path(native.waiter.path).exists())
            self.assertIsNone(newer.attempt(lambda: self.gate.try_command_claim(None, 2, False, 1), 128))
            claim = old.attempt(lambda: self.gate.try_command_claim(None, 2, False, 1), 128)
            self.assertTrue(claim)
            # Release only admission: the old fixed child retains its slot.
            os.close(claim[0][1])
            self.assertIsNone(native.attempt(128))
            self.assertIsNotNone(native.barrier)
            for _, fd in claim[1:]: os.close(fd)
            fence = native.attempt(128)
            self.assertIsNotNone(fence)
            for fd in fence: os.close(fd)

    def test_native_epoch_low_memory_and_cancel_release_all_claims(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        old = self.held(self.external / "slot-0", {})
        with self.gate.NativeEpochWaiter(str(self.external), 2, "native", 4) as native:
            self.assertIsNone(native.attempt(3))
            self.assertIsNone(native.waiter.fd)
            self.assertIsNone(native.barrier)
            self.assertIsNone(native.attempt(128))
            self.assertIsNotNone(native.barrier)
            self.assertIsNone(native.attempt(3))
            self.assertIsNone(native.barrier)
            admission = self.gate.try_lease(str(self.external / "admission.lock"))
            self.assertIsNotNone(admission, "memory-ineligible transition kept its drain barrier")
            os.close(admission)
            fixed = self.gate.try_command_claim(None, 2, False, 1)
            self.assertIsNotNone(fixed, "eligible fixed work could not use a genuinely free slot")
            for _, fd in fixed:
                os.close(fd)
            self.assertIsNone(native.attempt(128))
            self.assertIsNotNone(native.barrier, "recovered transition did not rejoin admission")
        admission = self.gate.try_lease(str(self.external / "admission.lock"))
        self.assertIsNotNone(admission)
        os.close(admission)
        self.assertEqual(list((self.external / "admission").glob("wait-*")), [])
        fcntl.flock(old, fcntl.LOCK_UN)
        fence = self.gate.try_legacy_fence(str(self.external), 2)
        self.assertIsNotNone(fence)
        for fd in fence: os.close(fd)

    def test_native_epoch_busy_worktree_bypasses_then_recovers_fifo_and_transfers_lease(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        worktree = str(self.root / "worktree.lock")
        busy = self.held(worktree, {})
        with self.gate.NativeEpochWaiter(str(self.external), 2, "native", 4, worktree) as native, \
             self.gate.AdmissionWaiter("new fixed", slots=2) as newer:
            self.assertIsNone(native.attempt(128))
            self.assertIsNone(native.barrier)
            self.assertIsNone(native.worktree_fd)
            self.assertIsNotNone(native.waiter.fd)
            # Busy native worktree leaves ordinary fixed admission available.
            claim = newer.attempt(lambda: self.gate.try_command_claim(None, 2, False, 1), 128)
            self.assertTrue(claim)
            for _, fd in claim: os.close(fd)
            # A subsequent fixed request registers while the native is busy.
            self.assertIsNone(newer.attempt(lambda: None, 128))
            fcntl.flock(busy, fcntl.LOCK_UN)
            # The native is now eligible; its older ticket must regain priority
            # even when this younger fixed caller retries first.
            self.assertIsNone(newer.attempt(lambda: self.gate.try_command_claim(None, 2, False, 1), 128))
            fence = native.attempt(128)
            self.assertIsNotNone(fence)
            lease = native.take_worktree()
            self.assertIsNotNone(lease)
            self.assertIsNone(self.gate.try_lease(worktree))
        # Context closes no transferred descriptor; native heavy claim reuses it.
        self.assertIsNone(self.gate.try_lease(worktree))
        os.close(lease)
        for fd in fence: os.close(fd)
        available = self.gate.try_lease(worktree)
        self.assertIsNotNone(available)
        os.close(available)

    def test_native_epoch_conversion_loss_releases_slots_and_requeues(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        old = self.held(self.external / "slot-0", {})
        worktree = str(self.root / "worktree.lock")
        with self.gate.NativeEpochWaiter(str(self.external), 2, "native", 4, worktree) as native:
            self.assertIsNone(native.attempt(128))
            barrier = native.barrier
            fcntl.flock(old, fcntl.LOCK_UN)
            real_flock = fcntl.flock
            def lose_conversion(fd, operation):
                if fd == barrier and operation == fcntl.LOCK_SH | fcntl.LOCK_NB:
                    # Model kernels that release EX before a failed SH acquire.
                    real_flock(fd, fcntl.LOCK_UN)
                    raise BlockingIOError()
                return real_flock(fd, operation)
            with mock.patch.object(self.gate.fcntl, "flock", side_effect=lose_conversion):
                self.assertIsNone(native.attempt(128))
            self.assertIsNone(native.barrier)
            self.assertIsNone(native.worktree_fd)
            claim = self.gate.try_command_claim(worktree, 2, True, 1)
            for _, fd in claim: os.close(fd)
            fence = native.attempt(128)
            self.assertIsNotNone(fence)
            lease = native.take_worktree()
            os.close(lease)
            for fd in fence: os.close(fd)

    def test_production_main_native_transition_cannot_be_overtaken(self):
        # Only host observations/account-home are deterministic. The production
        # main, capability probe, canonical queue, flock and child lifetimes run.
        shim = self.root / "targo"
        write_python_program(shim,
                        "import json,sys\nfrom pathlib import Path\n" +
                        "if '--resource-capabilities' in sys.argv:\n" +
                        " print(json.dumps(dict(version=3,cpu_workers=True,supports_invocation=True)))\n" +
                        "else:\n Path(sys.argv[-1]).touch(); sys.stdin.buffer.read(1)\n")
        shim.chmod(0o700)
        self.assertTrue(self.gate.worker_capability([str(shim), "--unverified", "build", "marker"]))
        environment = {key: value for key, value in os.environ.items()
                       if not key.startswith(("BUILD_SLOT", "BUILD_SLOTS", "FIXTURE_", "ATERM_"))
                       and key not in ("CARGO_BUILD_JOBS", "TARGO_PLANNED_JOBS", "TARGO_CALLER_JOBS")}
        environment.update(BUILD_SLOT_DIR=str(self.external), FIXTURE_USER_HOME=str(self.root),
                           FIXTURE_CPU_COUNT="12")
        wrapper = [sys.executable, "-I", "-B", "-c", WRAPPER, str(SCRIPT),
                   "--slots", "2", "--cpus", "1", "--mem-gb", "4", "--"]
        old = self.held(self.external / "slot-0", {})
        holder = subprocess.Popen([sys.executable, "-c", "import sys; sys.stdin.buffer.read()"],
                                  stdin=subprocess.PIPE, pass_fds=[old])
        self.fds.remove(old)
        os.close(old)
        processes = [holder]
        native_marker, fixed_marker = self.root / "native-start", self.root / "fixed-start"
        def spawn(command):
            process = subprocess.Popen([*wrapper, *command], env=environment, cwd=self.root,
                                       stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            processes.append(process)
            return process
        def until(predicate, timeout=6):
            deadline = time.monotonic() + timeout
            while time.monotonic() < deadline:
                if predicate(): return True
                time.sleep(0.01)
            return False
        native = spawn([str(shim), "--unverified", "build", str(native_marker)])
        try:
            # EX admission must be reserved while old slot0 is still held.
            def reserved():
                fd = os.open(self.external / "admission.lock", os.O_RDWR | os.O_CREAT, 0o600)
                try:
                    try: fcntl.flock(fd, fcntl.LOCK_SH | fcntl.LOCK_NB)
                    except BlockingIOError: return True
                    return False
                finally: os.close(fd)
            self.assertTrue(until(reserved), "native wait remained invisible before the canonical FIFO")
            self.assertFalse(native_marker.exists(), "native ran alongside an old fixed holder")
            fixed = spawn([sys.executable, "-c", "from pathlib import Path; import sys; Path(sys.argv[1]).touch(); sys.stdin.buffer.read(1)", str(fixed_marker)])
            self.assertFalse(until(fixed_marker.exists, 0.2), "new fixed work overtook the waiting native epoch")
            holder.stdin.close()
            holder.wait(timeout=5)
            self.assertTrue(until(native_marker.exists), "native did not enter after the old holder drained")
            self.assertFalse(fixed_marker.exists())
            native.stdin.close()
            self.assertEqual(native.wait(timeout=5), 0)
            self.assertTrue(until(fixed_marker.exists), "fixed work did not resume after all native fences closed")
            fixed.stdin.close()
            self.assertEqual(fixed.wait(timeout=5), 0)
        finally:
            for process in reversed(processes):
                if process.stdin and not process.stdin.closed: process.stdin.close()
                if process.poll() is None: process.terminate()
                process.wait(timeout=5)
                if process.stderr:
                    diagnostic = process.stderr.read().decode()
                    if process.returncode not in (0, -15):
                        print("fixture gate diagnostic:", process.returncode, diagnostic)
                for stream in (process.stdout, process.stderr):
                    if stream: stream.close()

    def test_queued_native_peers_share_epoch_after_old_holder_drains(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        old = self.held(self.external / "slot-0", {})
        fences = []
        try:
            with self.gate.NativeEpochWaiter(str(self.external), 2, "first", 4) as first, \
                 self.gate.NativeEpochWaiter(str(self.external), 2, "second", 4) as second:
                self.assertIsNone(first.attempt(128))
                self.assertIsNone(second.attempt(128))
                self.assertIsNotNone(second.waiter.fd)
                fcntl.flock(old, fcntl.LOCK_UN)
                fences.append(first.attempt(128))
                self.assertIsNotNone(fences[0])
                joined = second.attempt(128)
                self.assertIsNotNone(joined, "queued native peer serialized behind a compatible epoch")
                fences.append(joined)
                for fd in fences.pop(0): os.close(fd)
                self.assertIsNone(self.gate.try_lease(str(self.external / "slot-0")))
        finally:
            for fence in fences:
                for fd in fence: os.close(fd)
        fixed = self.gate.try_command_claim(None, 2, False, 1)
        for _, fd in fixed: os.close(fd)

    def test_queued_native_join_never_bypasses_older_fixed_epoch_drain(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        active = self.gate.try_legacy_fence(str(self.external), 2)
        try:
            with self.gate.AdmissionWaiter("older fixed", slots=2) as fixed, \
                 self.gate.NativeEpochWaiter(str(self.external), 2, "native", 4) as native:
                self.assertIsNone(fixed.attempt(lambda: None, 128))
                # Slot availability alone must not make an older fixed request
                # invisible while the very SH epoch we would extend blocks it.
                self.assertIsNone(native.attempt(128))
                self.assertIsNone(native.barrier)
                for fd in active: os.close(fd)
                active = []
                claim = fixed.attempt(lambda: self.gate.try_command_claim(None, 2, False, 1), 128)
                self.assertTrue(claim)
                # Production fixed main releases admission before its child,
                # retaining only the legacy slot claim during execution.
                self.assertEqual(Path(claim[0][0]).name, "admission.lock")
                os.close(claim.pop(0)[1])
                try:
                    self.assertIsNone(native.attempt(128))
                    self.assertIsNotNone(native.barrier)
                finally:
                    for _, fd in claim: os.close(fd)
                fence = native.attempt(128)
                self.assertIsNotNone(fence)
                for fd in fence: os.close(fd)
        finally:
            for fd in active: os.close(fd)

    def test_queued_native_join_bypasses_only_memory_or_worktree_ineligibility(self):
        self.gate.DIR = str(self.external)
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        worktree = str(self.root / "worktree.lock")
        busy = self.held(worktree, {})
        for requirements in ({"memory": 999}, {"worktree": worktree}):
            with self.subTest(requirements=requirements):
                active = self.gate.try_legacy_fence(str(self.external), 2)
                try:
                    with self.gate.AdmissionWaiter("ineligible fixed", slots=2, **requirements) as fixed, \
                         self.gate.NativeEpochWaiter(str(self.external), 2, "native", 4) as native:
                        self.assertIsNone(fixed.attempt(lambda: None, 128))
                        fence = native.attempt(128)
                        self.assertIsNotNone(fence)
                        for fd in fence: os.close(fd)
                finally:
                    for fd in active: os.close(fd)
        fcntl.flock(busy, fcntl.LOCK_UN)

    def test_stale_generated_marker_cannot_erase_a_later_user_cap(self):
        self.assertEqual(self.gate.job_provenance({"CARGO_BUILD_JOBS": "2", "TARGO_PLANNED_JOBS": "7", "TARGO_CALLER_JOBS": "12"}), (False, 2))
        with self.assertRaises(ValueError):
            self.gate.job_provenance({"TARGO_CALLER_JOBS": "0"})

    def test_native_operation_eligibility_uses_exact_invocation_query(self):
        program = self.root / "targo"
        capture = self.root / "query.json"
        for args, supported in [
            (["--unverified", "test", "--lib", "-p", "crate with spaces"], True),
            (["--config", "build.build-dir='cache with spaces'", "--unverified", "check", "--all-targets"], True),
            (["--unverified", "--config", "net.offline=true", "build"], True),
            (["--unverified", "test", "--lib", "--", "--skip", "--resource-worker-v2"], True),
            (["trust", "build"], False),
            (["--version"], False),
            (["--unverified", "alias"], False),
            (["--unverified", "test"], False),
            (["--unverified", "test", "--doc"], False),
        ]:
            write_python_program(program, 'import json, pathlib, sys\n'
                               f'pathlib.Path({str(capture)!r}).write_text(json.dumps(sys.argv[1:]))\n'
                               f'print(json.dumps({{"version": 3, "cpu_workers": True, "supports_invocation": {supported!r}}}))\n')
            program.chmod(0o700)
            self.assertEqual(self.gate.worker_capability([str(program), *args]), supported)
            self.assertEqual(json.loads(capture.read_text()), ["--resource-capabilities", "--", *args])
        # Old version-one build/check advertisements grant no test capability.
        for value in [
            {"version": 1, "cpu_workers": True, "supported_commands": ["build", "check"], "supported_lanes": ["unverified"]},
            {"version": 3, "cpu_workers": True, "supports_invocation": 1},
            {"version": 3, "cpu_workers": 1, "supports_invocation": True},
            {"version": 3, "cpu_workers": True, "supports_invocation": True, "unknown": True},
            {"version": 2, "cpu_workers": True, "supports_invocation": True},
        ]:
            write_python_program(program, f'print({json.dumps(value)!r})\n')
            with self.assertRaises(self.gate.CpuBridgeUnavailable):
                self.gate.worker_capability([str(program), "--unverified", "test", "--lib"])

    def test_native_shim_front_queries_and_launches_the_same_selected_invocation(self):
        front = [str(self.root / "atpkg"), "__build_admit", "--shim", "targo", "-",
                 str(self.root / "selected SDK" / "bin" / "targo")]
        answer = json.dumps(dict(version=3, cpu_workers=True, supports_invocation=True)).encode()
        for verb in ("build", "check", "test"):
            args = ["--unverified", verb, "--locked", "--lib", "-p", "crate with spaces"]
            for flagged in (False, True):
                command = [*front, *(["--resource-worker-v2"] if flagged else []), *args]
                with self.subTest(verb=verb, flagged=flagged), \
                     mock.patch.object(self.gate.shutil, "which", return_value=front[0]), \
                     mock.patch.object(self.gate, "bounded_native_query", return_value=(0, answer, b"")) as query:
                    self.assertTrue(self.gate.worker_capability(command))
                    query.assert_called_once_with(
                        [*front, "--resource-capabilities", "--", *args], observation=None)
                    self.assertEqual(self.gate.worker_command(command),
                                     [*front, "--resource-worker-v2", *args])
        # An actual unsupported response cannot conceal this front as fixed work.
        for cpu, invocation in ((False, False), (True, False)):
            answer = json.dumps(dict(version=3, cpu_workers=cpu, supports_invocation=invocation)).encode()
            with mock.patch.object(self.gate.shutil, "which", return_value=front[0]), \
                 mock.patch.object(self.gate, "bounded_native_query", return_value=(0, answer, b"")):
                with self.assertRaisesRegex(self.gate.CpuBridgeUnavailable, "does not support"):
                    self.gate.worker_capability([*front, "--unverified", "test", "--lib"])

    def test_malformed_native_shim_fronts_refuse_before_any_query_or_fixed_launch(self):
        program, sdk = str(self.root / "atpkg"), str(self.root / "sdk" / "targo")
        lead = [program, "__build_admit", "--shim", "targo", "-"]
        malformed = [
            [program, "__build_admit"],
            [program, "--private-state-root", *lead[1:], sdk, "--unverified", "test"],
            [program, "__build_admit", "--shim", "targo-tippy", "-", sdk, "--unverified", "test"],
            [program, "__build_admit", "--shim", "targo", "config", sdk, "--unverified", "test"],
            [program, "__build_admit", "--shim", "targo", "env", sdk, "--unverified", "test"],
            [*lead, "relative/targo", "--unverified", "test"],
            [*lead, str(self.root / "sdk" / "other"), "--unverified", "test"],
        ]
        with mock.patch.object(self.gate.subprocess, "Popen", side_effect=AssertionError("unexpected child")):
            for command in malformed:
                with self.subTest(command=command):
                    with self.assertRaises(self.gate.CpuBridgeUnavailable):
                        self.gate.worker_capability(command)
                    for options in ([], ["--exclusive"]):
                        with self.assertRaises(self.gate.CpuBridgeUnavailable):
                            self.gate.main([*options, "--", *command])
        self.assertIsNone(self.gate.worker_command(["env", *lead, sdk, "--unverified", "test"]))
        # An ordinary command's data is not the hidden verb's dispatch position.
        self.assertIsNone(self.gate.worker_command(
            [program, "run", "other-tool", "--", "__build_admit", "--unverified", "test"]))

    def test_native_shim_front_child_retains_original_epoch_after_gate_sigkill(self):
        front, program = self.root / "atpkg", self.root / "targo"
        marker, capture = self.root / "front-worker", self.root / "front-query"
        write_python_program(front, '''import os, sys
if sys.argv[1:5] != ["__build_admit", "--shim", "targo", "-"]:
    raise SystemExit(91)
os.execv(sys.argv[5], sys.argv[5:])
''')
        write_python_program(program, f'''import json, os, pathlib, sys
if sys.argv[1:3] == ["--resource-capabilities", "--"]:
    pathlib.Path({str(capture)!r}).write_text(json.dumps(sys.argv[1:]))
    print('{{"version":3,"cpu_workers":true,"supports_invocation":true}}')
    raise SystemExit(0)
if sys.argv[1] != "--resource-worker-v2": raise SystemExit(92)
fds = [int(value) for value in os.environ["BUILD_SLOT_FENCE_FDS"].split(",")]
for fd in fds: os.fstat(fd)
pathlib.Path({str(marker)!r}).write_text(json.dumps(dict(
    protocol=os.environ["BUILD_SLOT_CPU_PROTOCOL"], jobs=os.environ["CARGO_BUILD_JOBS"],
    fences=len(fds), args=sys.argv[1:])))
sys.stdin.buffer.read(1)
''')
        args = ["--config", "net.offline=true", "--unverified", "test", "--lib",
                "-p", "ordinary-consumer", "--", "--skip", "--resource-worker-v2"]
        env = {key: value for key, value in os.environ.items()
               if not key.startswith(("BUILD_SLOT", "BUILD_SLOTS", "ATERM_", "TARGO_"))
               and key != "CARGO_BUILD_JOBS"}
        env.update(BUILD_SLOT_DIR=str(self.external), FIXTURE_USER_HOME=str(self.root / "home"))
        child = subprocess.Popen([sys.executable, "-I", "-B", "-c", WRAPPER, str(SCRIPT),
            "--cpus", "1", "--", str(front), "__build_admit", "--shim", "targo", "-",
            str(program), *args], env=env, cwd=self.root, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            end = time.monotonic() + 5
            while not marker.exists():
                self.assertLess(time.monotonic(), end, "private native front did not start")
                time.sleep(.01)
            self.assertEqual(json.loads(capture.read_text()), ["--resource-capabilities", "--", *args])
            actual = json.loads(marker.read_text())
            self.assertEqual((actual["protocol"], actual["jobs"]), ("2", "1"))
            self.assertGreater(actual["fences"], 0)
            self.assertEqual(actual["args"], ["--resource-worker-v2", *args])
            child.kill()
            child.wait(timeout=5)
            self.assertIsNone(self.gate.try_lease(str(self.external / "slot-0")))
            child.stdin.close()
            end = time.monotonic() + 5
            while True:
                released = self.gate.try_lease(str(self.external / "slot-0"))
                if released is not None:
                    os.close(released)
                    break
                self.assertLess(time.monotonic(), end, "native front lost or retained its epoch incorrectly")
                time.sleep(.01)
        finally:
            if child.stdin and not child.stdin.closed: child.stdin.close()
            if child.poll() is None: child.kill()
            child.wait()
            for stream in (child.stdout, child.stderr):
                if stream: stream.close()

    def test_native_roots_coexist_while_legacy_exclusive_protocol_waits(self):
        program = self.root / "targo"
        write_python_program(program, '''import json, pathlib, sys
if sys.argv[1:3] == ["--resource-capabilities", "--"]:
    print('{"version":3,"cpu_workers":true,"supports_invocation":true}')
    raise SystemExit(0)
if sys.argv[1] != "--resource-worker-v2":
    raise SystemExit(7)
pathlib.Path(sys.argv[-1]).touch()
sys.stdin.buffer.read(1)
''')
        program.chmod(0o700)
        env = {key: value for key, value in os.environ.items()
               if not key.startswith(("BUILD_SLOT", "BUILD_SLOTS", "ATERM_", "TARGO_"))
               and key != "CARGO_BUILD_JOBS"}
        env.update(BUILD_SLOT_DIR=str(self.external), FIXTURE_USER_HOME=str(self.root / "home"))
        children = []
        def started(marker):
            end = time.monotonic() + 5
            while not marker.exists():
                self.assertLess(time.monotonic(), end, "private fixture did not start")
                time.sleep(.01)
        try:
            for index in range(2):
                marker = self.root / f"native-{index}"
                child = subprocess.Popen([sys.executable, "-I", "-c", WRAPPER, str(SCRIPT),
                    "--", str(program), "--unverified", "build", str(marker)], env=env, cwd=self.root,
                    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                children.append(child)
                started(marker)
            legacy_marker = self.root / "legacy"
            legacy = subprocess.Popen([sys.executable, "-c", '''import fcntl, pathlib, sys, time
f=open(sys.argv[1], "r+")
while True:
    try: fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB); break
    except BlockingIOError: time.sleep(.01)
pathlib.Path(sys.argv[-1]).touch()
sys.stdin.buffer.read(1)
''', str(self.external / "slot-0"), str(legacy_marker)], stdin=subprocess.PIPE)
            children.append(legacy)
            self.assertFalse(legacy_marker.exists())
            children[0].communicate(b"x", timeout=5)
            self.assertFalse(legacy_marker.exists())
            children[1].communicate(b"x", timeout=5)
            started(legacy_marker)
            legacy.communicate(b"x", timeout=5)
        finally:
            for child in children:
                if child.poll() is None: child.kill()
                child.wait()
                for stream in (child.stdin, child.stdout, child.stderr):
                    if stream and not stream.closed: stream.close()

    def test_native_child_keeps_legacy_fence_after_gate_sigkill(self):
        program, marker = self.root / "targo", self.root / "native-pid"
        write_python_program(program, '''import os, pathlib, sys
if sys.argv[1:3] == ["--resource-capabilities", "--"]:
    print('{"version":3,"cpu_workers":true,"supports_invocation":true}')
    raise SystemExit(0)
if sys.argv[1] != "--resource-worker-v2": raise SystemExit(7)
pathlib.Path(sys.argv[-1]).write_text(str(os.getpid()))
sys.stdin.buffer.read(1)
''')
        program.chmod(0o700)
        env = {key: value for key, value in os.environ.items()
               if not key.startswith(("BUILD_SLOT", "BUILD_SLOTS", "ATERM_", "TARGO_"))
               and key != "CARGO_BUILD_JOBS"}
        env.update(BUILD_SLOT_DIR=str(self.external), FIXTURE_USER_HOME=str(self.root / "home"))
        self.gate.ADOPTION_DIR = str(self.root / "adopted")
        gate = subprocess.Popen([sys.executable, "-I", "-c", WRAPPER, str(SCRIPT), "--",
            str(program), "--unverified", "build", str(marker)], env=env, cwd=self.root, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            end = time.monotonic() + 5
            while not marker.exists():
                self.assertLess(time.monotonic(), end, "native fixture did not start")
                time.sleep(.01)
            gate.kill()
            gate.wait(timeout=5)
            self.assertIsNone(self.gate.try_lease(str(self.external / "slot-0")))
            gate.stdin.close()  # the already-running native child sees EOF
            while True:
                released = self.gate.try_lease(str(self.external / "slot-0"))
                if released is not None:
                    os.close(released)
                    break
                self.assertLess(time.monotonic(), end, "native child did not release fence")
                time.sleep(.01)
        finally:
            if gate.poll() is None: gate.kill()
            gate.wait()
            for stream in (gate.stdin, gate.stdout, gate.stderr):
                if stream and not stream.closed: stream.close()


if __name__ == "__main__":
    unittest.main()
