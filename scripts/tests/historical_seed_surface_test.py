#!/usr/bin/env python3
"""Inert native CLI/socket controls, with no compiler or RootSeed credit."""

from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest
import subprocess
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts import seed_historical_surface as historical
from scripts import seed_root_initialization as initialization
from scripts import mint_seed_support as support

HOST = "aarch64-unknown-linux-gnu"


# A `#!{sys.executable}` shebang cannot carry an interpreter path with spaces (atpkg's python
# lives under `Application Support/`): exec splits it and the fake never runs. This sh/python
# polyglot execs the interpreter quoted and keeps argv[0] as the fake's own path.
PYTHON_SHEBANG = f'#!/bin/sh\n""":"\nexec "{sys.executable}" "$0" "$@"\n":"""\n'


class HistoricalSurfaceControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.env = {"PATH": "/usr/bin:/bin", "LC_ALL": "C"}
        for relative in initialization.FULL_TOOLS:
            self.executable(relative, "print('inert historical tool fixture')\n")
        self.executable("bin/trustc", "import sys\n"
            + "if '--print' in sys.argv: print(" + repr(str(self.root)) + ")\n"
            + "else: print(" + repr("rustc 1.99.0-dev (trustc)\nbinary: trustc\ncommit-hash: " + historical.SOURCE
                                     + "\nhost: " + HOST + "\nrelease: 1.99.0-dev") + ")\n")
        self.copy_alias("trustc", "rustc")
        self.executable("bin/targo", "print(" + repr("targo 1.99.0-dev\nhost: " + HOST) + ")\n")
        self.copy_alias("targo", "cargo")
        self.copy_alias("trustdoc", "rustdoc")
        self.status = {"version": "trustd.status.v1", "budget_bytes": 1024, "reserved_bytes": 0,
                       "free_bytes": 1024, "queue_depth": 0, "granted_total": 0, "released_total": 0,
                       "started_at": 1, "active": []}
        self.daemon()

    def executable(self, relative, code):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(PYTHON_SHEBANG + code)
        path.chmod(0o755)
        return path

    def copy_alias(self, name, alias):
        (self.root / "bin" / alias).write_bytes((self.root / "bin" / name).read_bytes())
        (self.root / "bin" / alias).chmod(0o755)

    def daemon(self, *, ping="PONG", status=None):
        return self.executable("bin/trustd", "import socket,sys,json,os\n"
            + "p=sys.argv[sys.argv.index('--socket')+1]\n"
            + "s=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM);s.bind(p);s.listen(2)\n"
            + "while True:\n"
            + " c,_=s.accept()\n"
            + " with c,c.makefile('rb') as stream:\n"
            + "  for line in stream:\n"
            + "   reply=" + repr(ping) + " if line==b'PING\\n' else " + repr(json.dumps(self.status if status is None else status)) + "\n"
            + "   c.sendall((reply+'\\n').encode())\n")

    def test_actual_original_identity_never_qualifies_current_native_pairing(self):
        result = historical.candidate(self.root, HOST, "1.99.0", self.env, time.monotonic() + 5)
        self.assertEqual(result["source_commit"], historical.SOURCE)
        self.assertEqual(result["contract"], initialization.HISTORICAL_CONTRACT)
        self.assertFalse(result["supports_modern_native_lane"])
        self.assertFalse(result["current_toolchain_qualification"])
        self.assertGreater(result["frontend"]["pid"], 1)
        with self.assertRaises(support.WorkflowError):
            support.native_seed_tool_pair(result["compiler"]["stdout"], result["frontend"]["stdout"], "1.99.0", HOST)

    def test_different_source_or_host_never_selects_historical_contract(self):
        for host, version in (("x86_64-unknown-linux-gnu", "1.99.0"), (HOST, "0.10.0")):
            with self.subTest(host=host, version=version), self.assertRaises(ValueError):
                historical.candidate(self.root, host, version, self.env, time.monotonic() + 5)

    def test_stock_frontend_and_mixed_identity_epoch_refuse(self):
        for text in ("cargo 1.99.0\nhost: " + HOST,
                     "targo 1.99.0\nhost: " + HOST + "\ntrust-repo-commit-hash: " + historical.SOURCE):
            self.executable("bin/targo", "print(" + repr(text) + ")\n")
            self.copy_alias("targo", "cargo")
            with self.subTest(output=text), self.assertRaises(ValueError):
                historical.candidate(self.root, HOST, "1.99.0", self.env, time.monotonic() + 5)

    def test_genuine_development_line_cannot_substitute_for_original_source(self):
        path = self.root / "bin/trustc"
        path.write_text(path.read_text().replace(historical.SOURCE, "6986546eaafc7620e49331269685dbd1b2900ba3"))
        self.copy_alias("trustc", "rustc")
        with self.assertRaisesRegex(ValueError, "actual original native compiler"):
            historical.candidate(self.root, HOST, "1.99.0", self.env, time.monotonic() + 5)

    def test_actual_private_ping_status_reaps_only_its_own_child(self):
        result = historical.daemon(self.root / "bin/trustd", self.env, time.monotonic() + 5)
        self.assertEqual(result["observations"]["status"], self.status)
        self.assertFalse(Path(result["argv"][-1]).exists())
        self.assertFalse(Path("/proc/" + str(result["observations"]["pid"])).exists())
        self.assertTrue(result["owned_child_reaped"])
        self.assertEqual(result["current_identity_protocol"], "unsupported")

    def test_bad_ping_and_malformed_status_fail_closed(self):
        for ping, status in (("wrong", None), ("PONG", {"version": "trustd.status.v1"})):
            self.daemon(ping=ping, status=status)
            with self.subTest(ping=ping, status=status), self.assertRaises(ValueError):
                historical.daemon(self.root / "bin/trustd", self.env, time.monotonic() + 5)

    def test_status_counter_domain_and_semantics_are_closed(self):
        for key, value in (("budget_bytes", 0), ("free_bytes", 1023), ("reserved_bytes", 1),
                           ("queue_depth", True), ("granted_total", 1), ("started_at", 2**64),
                           ("active", [{"pid": os.getpid()}]), ("unexpected", 1)):
            changed = {**self.status, key: value}
            with self.subTest(key=key), self.assertRaises(ValueError):
                historical.validate_status(changed)
        with self.assertRaisesRegex(ValueError, "duplicate"):
            json.loads('{"version":"a","version":"b"}', object_pairs_hook=historical.json_object)

    def test_expired_original_deadline_never_starts_a_probe(self):
        marker = self.root / "never-started"
        path = self.executable("bin/never-start", "open(" + repr(str(marker)) + ",'w').write('started')\n")
        with self.assertRaisesRegex(ValueError, "deadline expired"):
            historical.probe(path, ["-vV"], self.env, time.monotonic() - 1)
        self.assertFalse(marker.exists())

    def test_actual_timed_out_probe_reaps_its_owned_child(self):
        marker = self.root / "timed-child.pid"
        # The deadline outlasts the child's start on a loaded host, so the child has written
        # its pid before the probe times out; it then sleeps far past the deadline.
        path = self.executable("bin/timed", "import os,time\nopen(" + repr(str(marker)) + ",'w').write(str(os.getpid()))\ntime.sleep(60)\n")
        with self.assertRaises(subprocess.TimeoutExpired):
            historical.probe(path, [], self.env, time.monotonic() + 3)
        # Reaped, not merely killed: signal 0 still reaches a zombie, on Linux and on macOS.
        with self.assertRaises(ProcessLookupError):
            os.kill(int(marker.read_text()), 0)

    def test_candidate_symlink_is_refused_before_execution(self):
        (self.root / "bin/targo").unlink()
        (self.root / "bin/targo").symlink_to("cargo")
        with self.assertRaisesRegex(ValueError, "contained regular executable"):
            historical.candidate(self.root, HOST, "1.99.0", self.env, time.monotonic() + 5)

    def test_daemon_that_never_binds_is_retired_after_original_deadline(self):
        marker = self.root / "no-socket.pid"
        path = self.executable("bin/trustd", "import os,time\nopen(" + repr(str(marker)) + ",'w').write(str(os.getpid()))\ntime.sleep(5)\n")
        with self.assertRaisesRegex(ValueError, "deadline expired"):
            historical.daemon(path, self.env, time.monotonic() + .2)
        self.assertFalse(Path("/proc/" + marker.read_text()).exists())

    def test_kernel_peer_pid_must_match_the_actual_spawned_daemon(self):
        original = historical.socket.socket
        class OtherPeer:
            def __init__(self, *args):
                self.stream = original(*args)
            def __enter__(self):
                return self
            def __exit__(self, *args):
                self.stream.close()
            def __getattr__(self, key):
                return getattr(self.stream, key)
            def getsockopt(self, *args):
                return historical.struct.pack("3i", os.getpid(), os.geteuid(), os.getegid())
        with mock.patch.object(historical.socket, "socket", OtherPeer), self.assertRaisesRegex(ValueError, "peer is not the owned process"):
            historical.daemon(self.root / "bin/trustd", self.env, time.monotonic() + 5)

    def test_full18_historical_inventory_is_not_the_current_full18_contract(self):
        result = historical.native_tools(self.root, initialization.FULL_TOOLS, HOST, "1.99.0", self.env,
                                         time.monotonic() + 10)
        self.assertEqual(set(result["tools"]), set(initialization.FULL_TOOLS))
        self.assertFalse(result["current_toolchain_qualification"])
        self.assertFalse(result["supports_modern_native_lane"])
        self.assertEqual(result["probes"]["libexec/trust-analyzer-proc-macro-srv"]["scope"],
                         "shape-only; original stdio protocol has no info CLI")

    def test_missing_tool_or_changed_alias_is_not_a_historical_exception(self):
        (self.root / "bin/trustd").unlink()
        with self.assertRaisesRegex(ValueError, "missing a regular executable"):
            historical.native_tools(self.root, initialization.FULL_TOOLS, HOST, "1.99.0", self.env,
                                     time.monotonic() + 10)
        self.copy_alias("trustc", "cargo")
        with self.assertRaisesRegex(ValueError, "aliases differ"):
            historical.candidate(self.root, HOST, "1.99.0", self.env, time.monotonic() + 5)

    def test_actual_installed_minimal_surface_records_historical_scope(self):
        result = historical.installed_seed(self.root, HOST, "1.99.0", self.env, time.monotonic() + 5, support)
        self.assertFalse(result["current_toolchain_qualification"])
        self.assertEqual(result["bootstrap_contract"], historical.CONTRACT)
        self.assertEqual(len(result["entrypoint_sha256"]), 6)
        initialization.require(bool(result["tree"]["sha256"]), "missing actual tree")


if __name__ == "__main__":
    unittest.main()
