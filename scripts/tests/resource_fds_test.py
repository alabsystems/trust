#!/usr/bin/env python3
"""Fixed/GNU descriptor transport regressions; native GNU mode retains its owner.

Pure OS parser fixtures below grant no SDK/CPU/GNU authority. --native adds
actual same-pipe forwarding through the existing maintained Rust importer.
"""
from __future__ import annotations

import array
import fcntl
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import termios
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts/lib"))
import landing_targo as transport
import native_serial

NATIVE = "--native" in sys.argv
if NATIVE:
    sys.argv.remove("--native")

SINGLE = ("ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1", "TRUST_CPU_IMPLICIT_FD")
SETS = ("ATERM_WORKLOAD_CPU_FDS_V1", "BUILD_SLOT_FENCE_FDS")
GNU = ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS")


class EffectiveAdvertisementTests(unittest.TestCase):
    def setUp(self):
        self.read, self.write = os.pipe()
        self.addCleanup(os.close, self.read)
        self.addCleanup(os.close, self.write)
        self.live = f"{self.read},{self.write}"
        self.closed = os.dup(self.read)
        os.close(self.closed)
        self.obsolete = f"{self.closed},{self.closed}"

    def test_last_auth_and_legacy_fallback_ignore_closed_obsolete_descriptors(self):
        cases = [
            f"--jobserver-auth={self.obsolete} --jobserver-auth={self.live}",
            f"--jobserver-fds={self.obsolete} --jobserver-fds={self.live}",
            f"--jobserver-auth={self.live} --jobserver-fds={self.obsolete}",
        ]
        for name in GNU:
            for flags in cases:
                with self.subTest(name=name, flags=flags):
                    self.assertEqual(transport.resource_fds({name: flags}), (self.read, self.write))

    def test_first_present_variable_masks_every_lower_priority_variable(self):
        for first, lower in [("CARGO_MAKEFLAGS", "MAKEFLAGS"), ("CARGO_MAKEFLAGS", "MFLAGS"), ("MAKEFLAGS", "MFLAGS")]:
            self.assertEqual(transport.resource_fds({
                first: f"--jobserver-auth={self.live}", lower: f"--jobserver-auth={self.obsolete}",
            }), (self.read, self.write))
            for value in ["", "-j4"]:
                self.assertEqual(transport.resource_fds({
                    first: value, lower: f"--jobserver-auth={self.obsolete}",
                }), ())

    def test_live_obsolete_descriptors_are_not_forwarded(self):
        old_read, old_write = os.pipe()
        try:
            flags = f"--jobserver-auth={old_read},{old_write} --jobserver-auth={self.live}"
            self.assertEqual(transport.resource_fds({"CARGO_MAKEFLAGS": flags}),
                             (self.read, self.write))
        finally:
            os.close(old_read)
            os.close(old_write)

    def test_non_numeric_style_and_disabled_auth_never_revive_legacy_pipe(self):
        for value in ["fifo:/not-opened", "-1,-1", f"-1,{self.write}"]:
            flags = f"--jobserver-auth={self.live} --jobserver-auth={value} --jobserver-fds={self.obsolete}"
            env = {"CARGO_MAKEFLAGS": flags, "CARGO_JOBSERVER_HANDOFF": "opaque-native-owner-data"}
            before = dict(env)
            with mock.patch.object(transport.os, "fstat", side_effect=AssertionError("obsolete pipe consulted")):
                self.assertEqual(transport.resource_fds(env), ())
            self.assertEqual(env, before)

    def test_native_option_substring_space_and_numeric_spelling(self):
        # Rust find_jobserver_auth uses rsplit_once(marker) and split(' '),
        # not shell tokenization, general whitespace or an option boundary.
        self.assertEqual(transport.resource_fds({
            "CARGO_MAKEFLAGS": f"prefix--jobserver-auth=+0{self.read},+0{self.write} -j",
        }), (self.read, self.write))
        zeroes = "0" * 5000
        self.assertEqual(transport.resource_fds({
            "CARGO_MAKEFLAGS": f"--jobserver-auth=+{zeroes}{self.read},+{zeroes}{self.write}",
        }), (self.read, self.write))
        with self.assertRaises(RuntimeError):
            transport.resource_fds({"CARGO_MAKEFLAGS": f"--jobserver-auth={self.live}\t-j"})

    def test_malformed_or_closed_effective_advertisement_refuses_before_launch(self):
        values = ["", "fifo:", "not-a-pair", "3,", "3,4,5", self.obsolete, "2147483648,3", "-2147483649,3"]
        for value in values:
            env = {"CARGO_MAKEFLAGS": f"--jobserver-auth={self.live} --jobserver-auth={value}"}
            with self.subTest(value=value), mock.patch.object(native_serial.subprocess, "Popen") as launch:
                with self.assertRaises(RuntimeError):
                    native_serial.run_custodied_command(["/unreachable"], env=env)
                launch.assert_not_called()

    def test_non_utf8_selected_flags_refuse(self):
        with self.assertRaises(RuntimeError):
            transport.resource_fds({"CARGO_MAKEFLAGS": f"\udcff --jobserver-auth={self.live}"})

    def test_non_gnu_field_rules_and_native_range_refusal_are_preserved(self):
        # These pipes are parser/liveness DATA only, never native authorities.
        for name in SINGLE:
            self.assertEqual(transport.resource_fds({name: str(self.read)}), (self.read,))
        for name in SETS:
            self.assertEqual(transport.resource_fds({name: self.live}), (self.read, self.write))
        for name in (*SINGLE, *SETS):
            for value in ["", "0", "2", "-1", "01", "9999999999"]:
                with self.subTest(name=name, value=value), self.assertRaises(RuntimeError):
                    transport.resource_fds({name: value})
        for name in SETS:
            with self.assertRaises(RuntimeError):
                transport.resource_fds({name: f"{self.read},{self.read}"})


class FixedAdvertisementTests(unittest.TestCase):
    """OS transport data only; the native importer still authenticates custody."""

    def setUp(self):
        self.read, self.write = os.pipe()
        self.addCleanup(os.close, self.read)
        self.addCleanup(os.close, self.write)

    def test_original_fixed_pipe_reaches_the_custodied_child(self):
        env = {"TRUST_FIXED_ADMISSION_FD_V1": str(self.read)}
        original = dict(env)
        os.write(self.write, b"original fixed transport")
        result = native_serial.run_custodied_command(
            [sys.executable, "-I", "-B", "-c",
             "import json,os; fd=int(os.environ['TRUST_FIXED_ADMISSION_FD_V1']); "
             "s=os.fstat(fd); print(json.dumps({'identity':[s.st_dev,s.st_ino,s.st_mode,s.st_rdev],"
             "'payload':os.read(fd,64).decode()}))"],
            env=env, timeout=15)
        self.assertEqual(result.returncode, 0, result.stderr)
        observed = json.loads(result.stdout)
        self.assertEqual(observed["identity"], identity(self.read))
        self.assertEqual(observed["payload"], "original fixed transport")
        self.assertEqual(env, original)

    def test_malformed_or_closed_fixed_descriptor_refuses_before_launch(self):
        closed = os.dup(self.read)
        os.close(closed)
        for value in ("", "0", "2", "-1", "01", "+3", "3,4", "9999999999",
                      str(closed), "requires-live-ancestor-v2"):
            env = {"TRUST_FIXED_ADMISSION_FD_V1": value}
            with self.subTest(value=value), mock.patch.object(native_serial.subprocess, "Popen") as launch:
                with self.assertRaises(RuntimeError):
                    native_serial.run_custodied_command(["/unreachable"], env=env)
                launch.assert_not_called()

    def test_ancestor_locator_stays_opaque_and_never_becomes_a_descriptor(self):
        for courier in ("opaque-native-owner-data", "{not JSON}", " "):
            env = {"TRUST_FIXED_ADMISSION_FD_V1": "requires-live-ancestor-v1",
                   "TRUST_FIXED_CLAIM_HANDOFF_V1": courier}
            original = dict(env)
            with self.subTest(courier=courier), mock.patch.object(
                    transport.os, "fstat", side_effect=AssertionError("opaque locator parsed as FD")):
                self.assertEqual(transport.resource_fds(env), ())
            self.assertEqual(env, original)

    def test_ancestor_marker_without_its_original_locator_refuses_before_launch(self):
        for extra in ({}, {"TRUST_FIXED_CLAIM_HANDOFF_V1": ""}):
            env = {"TRUST_FIXED_ADMISSION_FD_V1": "requires-live-ancestor-v1", **extra}
            with self.subTest(extra=extra), mock.patch.object(native_serial.subprocess, "Popen") as launch:
                with self.assertRaises(RuntimeError):
                    native_serial.run_custodied_command(["/unreachable"], env=env)
                launch.assert_not_called()

    def test_fixed_descriptor_joins_existing_transports_without_duplicates(self):
        env = {"TRUST_FIXED_ADMISSION_FD_V1": str(self.read),
               "ATERM_SDK_LEASE_V3": str(self.read),
               "CARGO_MAKEFLAGS": f"--jobserver-auth={self.read},{self.write}",
               "MAKEFLAGS": "--jobserver-auth=closed,obsolete"}
        self.assertEqual(transport.resource_fds(env), (self.read, self.write))


def identity(fd):
    info = os.fstat(fd)
    return [info.st_dev, info.st_ino, info.st_mode, info.st_rdev]


@unittest.skipUnless(NATIVE, "requires --native under maintained GNU owner")
class ActualInheritedGnuTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = next((key for key in GNU if key in os.environ), None)
        if name is None:
            raise RuntimeError("native controls require actual retained GNU transport")
        flags = os.environ[name]
        value = flags.rsplit("--jobserver-auth=", 1)[1].split(" ", 1)[0]
        cls.read, cls.write = map(int, value.split(","))
        cls.expected = [identity(cls.read), identity(cls.write)]
        cls.executor = native_serial.managed_serial_executor(dict(os.environ))
        cls.temp = tempfile.TemporaryDirectory(prefix="trust-effective-gnu-native-")
        cls.probe = Path(cls.temp.name) / "probe.py"
        cls.probe.write_text(r"""import array,fcntl,json,os,termios
value=os.environ["CARGO_MAKEFLAGS"].rsplit("--jobserver-auth=",1)[1].split(" ",1)[0]
r,w=map(int,value.split(","))
def identity(fd):
 s=os.fstat(fd);return [s.st_dev,s.st_ino,s.st_mode,s.st_rdev]
observed=[identity(r),identity(w)]
assert observed==json.loads(os.environ["TEST_ORIGINAL_GNU_IDENTITIES"]),observed
count=array.array("i",[0]);fcntl.ioctl(r,termios.FIONREAD,count,True)
print(json.dumps({"same_original_pipe":True,"identities":observed,"available_bytes_observed_no_consumption":count[0]}))
""")
        print("ACTUAL_GNU_OWNER=" + json.dumps({"executor": str(cls.executor), "identities": cls.expected}), flush=True)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def run_flags(self, flags, **lower):
        env = dict(os.environ)
        env.update(lower)
        env["CARGO_MAKEFLAGS"] = flags
        env["TEST_ORIGINAL_GNU_IDENTITIES"] = json.dumps(self.expected)
        # No helper-created pipe, token or context clearing. The existing Rust
        # serial owner imports the effective genuine pipe and keeps its wait.
        inherited = transport.resource_fds(env)
        self.assertIn(self.read, inherited)
        self.assertIn(self.write, inherited)
        result = native_serial.run_custodied_command(
            [str(self.executor), "--", sys.executable, "-B", str(self.probe)],
            env=env, cwd=self.temp.name, timeout=15)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(json.loads(result.stdout)["same_original_pipe"])
        print("NATIVE_CHILD_TRANSPORT=" + result.stdout.strip(), flush=True)

    def closed(self):
        fd = os.dup(self.read)
        os.close(fd)
        return f"{fd},{fd}"

    def test_last_genuine_auth_after_obsolete_closed_auth(self):
        self.run_flags(f"--jobserver-auth={self.closed()} --jobserver-auth={self.read},{self.write}")

    def test_auth_wins_over_later_obsolete_legacy_fds(self):
        self.run_flags(f"--jobserver-auth={self.read},{self.write} --jobserver-fds={self.closed()}")

    def test_first_variable_ignores_obsolete_lower_priority_advertisements(self):
        self.run_flags(f"--jobserver-auth={self.read},{self.write}",
                       MAKEFLAGS=f"--jobserver-auth={self.closed()}",
                       MFLAGS=f"--jobserver-auth={self.closed()}")

    def test_last_legacy_fallback_is_the_genuine_pipe(self):
        self.run_flags(f"--jobserver-fds={self.closed()} --jobserver-fds={self.read},{self.write}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
