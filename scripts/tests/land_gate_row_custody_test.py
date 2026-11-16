#!/usr/bin/env python3
"""Actual row transport controls; no compiler, proof, or resource grant."""
from pathlib import Path
import json
import os
import shlex
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import land_gate


class RowCustodyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if os.environ.get("BUILD_SLOT_HELD") != "1":
            raise AssertionError("controls require actual outer admission")
        cls.qualified_executor = (os.environ.get("TRUST_SERIAL_COMMAND_TEST_BIN")
                                  or str(land_gate.managed_serial_executor(dict(os.environ))))
        cls.executor_before = (str(Path(cls.qualified_executor).resolve(strict=True)),
                               land_gate.sha256_file(Path(cls.qualified_executor)))

    @classmethod
    def tearDownClass(cls):
        after = (str(Path(cls.qualified_executor).resolve(strict=True)),
                 land_gate.sha256_file(Path(cls.qualified_executor)))
        if after != cls.executor_before:
            raise AssertionError("selected native transport image moved during controls")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.env = dict(os.environ)
        for name in ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", "CARGO_JOBSERVER_HANDOFF",
                     "ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_CPU_FDS_V1",
                     "ATERM_WORKLOAD_HOST_STORE_FD_V1", "TRUST_CPU_IMPLICIT_FD",
                     "BUILD_SLOT_FENCE_FDS", "TRUST_LAND_SERIAL_COMMAND"):
            self.env.pop(name, None)
        self.executor = self.qualified_executor
        self.assertEqual(self.env.get("BUILD_SLOT_HELD"), "1", "controls require actual outer admission")

    def run_row(self, command, env=None, kind="fast.transport"):
        log = self.root / "row.log"
        if kind == "verify.executes":
            # A synthetic script at the canonical role path exercises transport
            # only. The separate actual-source pulse runs the real verifier row.
            script = self.root / "scripts/check_verifier_executes.sh"
            script.parent.mkdir(exist_ok=True)
            script.write_text("#!/bin/bash\n" + command + "\n")
            command = "bash scripts/check_verifier_executes.sh"
        row = land_gate.PushRow(kind, "true", command)
        result = land_gate._run_row(row, self.root, env or self.env, log, False)
        return result, log.read_bytes()

    def python(self, source):
        return shlex.join([sys.executable, "-c", source])

    def test_original_advertised_descriptions_survive_and_unrelated_one_does_not(self):
        descriptors = []
        for number in range(6):
            stream = (self.root / str(number)).open("w+b")
            self.addCleanup(stream.close)
            descriptors.append(stream.fileno())
        a, b, c, d, e, unrelated = descriptors
        os.set_inheritable(unrelated, True)
        expected = {fd: [os.fstat(fd).st_dev, os.fstat(fd).st_ino] for fd in descriptors}
        env = dict(self.env, ATERM_SDK_LEASE_V3=str(a),
                   ATERM_WORKLOAD_CPU_FDS_V1=f"{b},{c}",
                   ATERM_WORKLOAD_HOST_STORE_FD_V1=str(d), BUILD_SLOT_FENCE_FDS=str(e))
        code = "import json,os\nout={}\nfor fd in " + repr(descriptors) + ":\n try:\n  s=os.fstat(fd);out[fd]=[s.st_dev,s.st_ino]\n except OSError:out[fd]=None\nprint(json.dumps(out))"
        result, output = self.run_row(self.python(code), env)
        self.assertEqual(result, 0, output)
        observed = json.loads(output)
        for fd in descriptors[:-1]:
            self.assertEqual(observed[str(fd)], expected[fd])
        self.assertNotEqual(observed[str(unrelated)], expected[unrelated])

    def test_exact_inherited_gnu_pair_reaches_native_owner_without_new_credits(self):
        read, write = os.pipe()
        self.addCleanup(os.close, read)
        self.addCleanup(os.close, write)
        expected = [[os.fstat(fd).st_dev, os.fstat(fd).st_ino] for fd in (read, write)]
        code = "import json,os,re,select; p=re.search(r'--jobserver-auth=(\\d+),(\\d+)',os.environ['CARGO_MAKEFLAGS']); assert p; f=list(map(int,p.groups())); assert not select.select([f[0]],[],[],0)[0]; print(json.dumps([[os.fstat(n).st_dev,os.fstat(n).st_ino] for n in f]))"
        env = dict(self.env, CARGO_MAKEFLAGS=f"-j --jobserver-auth={read},{write}")
        result, output = self.run_row(self.python(code), env, "verify.executes")
        self.assertEqual(result, 0, output)
        self.assertEqual(json.loads(output), expected)

    def test_native_owner_supplies_real_zero_extra_transport_when_absent(self):
        code = "import os,re,select,stat; p=re.search(r'--jobserver-auth=(\\d+),(\\d+)',os.environ['CARGO_MAKEFLAGS']); assert p; r,w=map(int,p.groups()); assert stat.S_ISFIFO(os.fstat(r).st_mode) and stat.S_ISFIFO(os.fstat(w).st_mode); assert not select.select([r],[],[],0)[0]; print('actual-empty-transport')"
        result, output = self.run_row(self.python(code), kind="verify.executes")
        self.assertEqual((result, output), (0, b"actual-empty-transport\n"))

    def test_caller_wrapper_overrides_never_run_verifier_row(self):
        marker = self.root / "ran"
        alias = self.root / "alias"
        alias.symlink_to(self.executor)
        noop = self.root / "noop"
        noop.write_text("#!/bin/sh\nexit 0\n")
        noop.chmod(0o700)
        forged = self.root / "forged"
        forged.write_text("#!/bin/sh\necho 'VERIFIER-EXECUTES: GREEN'\nexit 0\n")
        forged.chmod(0o700)
        for selected in ("", str(alias), str(noop), str(forged), self.executor):
            env = dict(self.env, TRUST_LAND_SERIAL_COMMAND=selected)
            with self.assertRaises(RuntimeError):
                self.run_row(shlex.join(["touch", str(marker)]), env, "verify.executes")
            self.assertFalse(marker.exists())

    def test_fake_atpkg_script_is_rejected_before_it_can_print_package_claims(self):
        marker = self.root / "fake-atpkg-ran"
        fake = self.root / "atpkg"
        fake.write_text("#!/bin/sh\ntouch " + shlex.quote(str(marker)) + "\necho '{}'\n")
        fake.chmod(0o700)
        with self.assertRaises(RuntimeError):
            land_gate.managed_serial_executor(dict(self.env, PATH=str(self.root)))
        self.assertFalse(marker.exists())

    def test_unmanaged_wrong_source_wrong_image_and_nonmatch_package_refuse(self):
        actual_run = subprocess.run
        for mutation in ("unmanaged", "source", "image", "verify", "root", "schema"):
            def query(argv, **kwargs):
                result = actual_run(argv, **kwargs)
                if argv[1:3] == ["which", "--json"]:
                    value = json.loads(result.stdout)
                    if mutation == "unmanaged": value["managed"] = False
                    if mutation == "source": value["provenance"]["index_source"] = "other/source"
                    if mutation == "image": value["executable"] = "/bin/true"
                    if mutation == "schema": value["schema"] = True
                    return subprocess.CompletedProcess(argv, 0, json.dumps(value), "")
                if argv[1] == mutation:
                    return subprocess.CompletedProcess(argv, 0, "unattestable\n", "")
                if mutation == "root" and argv[1] == "tree-root":
                    return subprocess.CompletedProcess(argv, 0, "0" * 64 + "\n", "")
                return result
            with self.subTest(mutation=mutation), patch.object(land_gate.subprocess, "run", side_effect=query):
                with self.assertRaises(RuntimeError):
                    land_gate.managed_serial_executor(self.env)

    def test_malformed_closed_and_duplicate_locators_never_run(self):
        marker = self.root / "ran"
        for fields in ({"ATERM_SDK_LEASE_V3": "invalid"},
                       {"ATERM_SDK_LEASE_V3": "999999"},
                       {"ATERM_WORKLOAD_CPU_FDS_V1": "3,3"},
                       {"BUILD_SLOT_FENCE_FDS": ""},
                       {"TRUST_CPU_IMPLICIT_FD": "02"}):
            with self.subTest(fields=fields), self.assertRaises(RuntimeError):
                self.run_row(shlex.join(["touch", str(marker)]), dict(self.env, **fields))
            self.assertFalse(marker.exists())

    def test_malformed_effective_gnu_pair_refuses_before_launch(self):
        # 57b30f5979 ("Forward only the effective inherited GNU transport" in
        # docs/DECISION_QUEUE.md) rejects a malformed effective numeric
        # advertisement before child launch; this control predates it and
        # expected the native owner's exit 75 after launch. Named FIFO and
        # native handoff advertisements still go to the native importer.
        marker = self.root / "ran"
        env = dict(self.env, CARGO_MAKEFLAGS="-j --jobserver-auth=not-a-pair")
        with self.assertRaisesRegex(RuntimeError, "malformed CARGO_MAKEFLAGS jobserver descriptor pair"):
            self.run_row(shlex.join(["touch", str(marker)]), env, "verify.executes")
        self.assertFalse(marker.exists())

    def test_serial_owner_preserves_raw_bytes_and_nonzero_status(self):
        result, output = self.run_row("printf 'a\\r\\nb\\rc\\n'; exit 23", kind="verify.executes")
        self.assertEqual((result, output), (23, b"a\r\nb\rc\n"))

    def test_shell_startup_cannot_skip_the_actual_row(self):
        marker = self.root / "startup-ran"
        startup = self.root / "startup"
        startup.write_text("touch " + shlex.quote(str(marker)) + "; echo forged; exit 0\n")
        result, output = self.run_row("printf actual; exit 23", dict(self.env, BASH_ENV=str(startup)))
        self.assertEqual((result, output), (23, b"actual"))
        self.assertFalse(marker.exists())

    def test_path_bash_shadow_cannot_replace_the_authored_verifier_script(self):
        marker = self.root / "fakebash-ran"
        fake = self.root / "bash"
        fake.write_text("#!/bin/sh\ntouch " + shlex.quote(str(marker))
                        + "\necho 'VERIFIER-EXECUTES: GREEN'\nexit 0\n")
        fake.chmod(0o700)
        env = dict(self.env, PATH=str(self.root) + ":" + self.env["PATH"])
        result, output = self.run_row("printf actual; exit 23", env, "verify.executes")
        self.assertEqual((result, output), (23, b"actual"))
        self.assertFalse(marker.exists())

    def test_changed_authored_verifier_command_is_refused(self):
        with self.assertRaises(RuntimeError):
            land_gate._run_row(land_gate.PushRow("verify.executes", "true", "echo forged"),
                               self.root, self.env, self.root / "row.log", False)

    def test_unadmitted_caller_is_refused_before_launch_not_graded_by_the_owner(self):
        # The real owner refuses an unadmitted caller with 75, and a row's 75
        # grades FAIL: `land_gate.py run` outside build-slot ended RED on
        # verify.executes. The caller's admission decides before the launch.
        marker = self.root / "ran"
        for held in (None, "0"):
            env = {k: v for k, v in self.env.items() if k != "BUILD_SLOT_HELD"}
            if held is not None:
                env["BUILD_SLOT_HELD"] = held
            with self.subTest(held=held):
                with self.assertRaisesRegex(RuntimeError, "row custody: verify.executes borrows a build-slot admission"):
                    self.run_row(shlex.join(["touch", str(marker)]), env, "verify.executes")
                self.assertFalse(marker.exists())
                refused = subprocess.run([self.executor, "--", "/usr/bin/touch", str(marker)], env=env,
                                         stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=60)
                self.assertEqual(refused.returncode, 75, refused.stderr)
                self.assertIn("already-admitted caller", refused.stderr)
                self.assertFalse(marker.exists())

    def test_package_queries_preserve_only_the_advertised_original_descriptor(self):
        with (self.root / "lease").open("w+b") as lease, (self.root / "other").open("w+b") as other:
            fd = lease.fileno()
            before = os.fstat(fd)
            observed = []
            actual_run = subprocess.run
            def query(argv, **kwargs):
                self.assertEqual(kwargs.get("pass_fds"), (fd,))
                self.assertNotIn(other.fileno(), kwargs["pass_fds"])
                self.assertEqual((os.fstat(fd).st_dev, os.fstat(fd).st_ino),
                                 (before.st_dev, before.st_ino))
                observed.append(argv)
                return actual_run(argv, **kwargs)
            with patch.object(land_gate.subprocess, "run", side_effect=query):
                selected = land_gate.managed_serial_executor(dict(self.env, ATERM_SDK_LEASE_V3=str(fd)))
            self.assertEqual(str(selected), self.executor)
            self.assertEqual(len(observed), 4)

    def test_original_path_and_relative_compiler_selection_are_bound_before_utilities(self):
        tool = self.root / "trustc"
        tool.write_text("#!/bin/sh\nexit 99\n")
        tool.chmod(0o700)
        for fields in ({"TRUSTC": "trustc", "PATH": str(self.root) + ":" + self.env["PATH"]},
                       {"TRUSTC": "./trustc"},
                       {"TRUSTC": str(tool)}):
            with self.subTest(fields=fields):
                result, output = self.run_row("printf '%s' \"$TRUSTC\"; exit 23",
                                              dict(self.env, **fields), "verify.executes")
                self.assertEqual((result, output), (23, str(tool).encode()))


if __name__ == "__main__":
    unittest.main()
