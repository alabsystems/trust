#!/usr/bin/env python3
"""Oracle and orchestration controls; these do not qualify real native tools."""
import copy
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


SPEC = importlib.util.spec_from_file_location("native_admission_runner", Path(__file__).with_name("run.py"))
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)
CANONICAL = b'{"fixture":"canonical report"}\n'
DAEMON_HASH = "9" * 64
COMMIT = "a" * 40
HOST = "aarch64-apple-darwin"


def report(run_digest="0" * 64):
    units = []
    for index, (kind, function) in enumerate((("lib", "value"), ("bin", "main")), 1):
        target = {
            "package_id": "path+file:///fixture#native-admission-fixture@0.1.0",
            "package_name": "native-admission-fixture", "target_name": "same_name",
            "target_kinds": [kind], "compile_mode": "check", "proof_unit_mode": "check",
            "proof_unit_role": "primary", "compile_target": HOST, "compile_kind": "host",
            "unit_identity_sha256": str(index) * 64, "semantics_sha256": str(index + 2) * 64,
            "proof_unit_index": index, "compile_target_spec_sha256": None,
        }
        binding = {
            "run_digest": run_digest, "unit_digest": target["unit_identity_sha256"],
            "semantics_digest": target["semantics_sha256"], "role": "primary", "target": HOST,
        }
        body = {"function": f"same_name::{function}", "body_digest": str(index + 4) * 64}
        work_digest = str(index + 6) * 64
        grant = {
            "bytes": 1024, "token": index,
            "work": {**{key: binding[key] for key in ("run_digest", "unit_digest", "semantics_digest")},
                     "work_digest": work_digest, "attempt": 1},
            "authority": {"daemon": {"executable_sha256": DAEMON_HASH, "commit": COMMIT}},
        }
        census = {
            "complete": True, "problems": [], "package_name": "native-admission-fixture",
            "crate_name": "same_name", "binding": binding, "bodies": [body], "auxiliary_bodies": [],
            "attempts": [{"body": body.copy(), "terminal": True, "work_digest": work_digest,
                          "attempt": 1, "outcome": {"state": "admitted", "receipt": {"grant": grant}}}],
        }
        units.append({"cargo_target": target, "census": census})
    return {
        "proof_report_hash": "sha256:" + hashlib.sha256(CANONICAL).hexdigest(),
        "availability": "complete", "problems": [], "units": units,
        "expected_units": copy.deepcopy([unit["cargo_target"] for unit in units]),
    }


def validate(value):
    return RUNNER.validate_report(value, CANONICAL, DAEMON_HASH, COMMIT, HOST)


class ReportOracleTests(unittest.TestCase):
    def test_complete_fixture_and_fresh_runs(self):
        RUNNER.validate_runs([validate(report()), validate(report("f" * 64))])

    def test_required_population_and_terminal_controls(self):
        for mutation in ("empty", "missing-bin", "wrong-kind", "missing-body", "wrong-body",
                         "empty-attempts", "unclosed", "extra-attempt", "wrong-expected",
                         "duplicate-unit", "incomplete", "wrong-hash", "wrong-package"):
            with self.subTest(mutation=mutation):
                value = report()
                unit = value["units"][1]
                if mutation == "empty":
                    value["units"] = value["expected_units"] = []
                elif mutation == "missing-bin":
                    value["units"].pop()
                elif mutation == "wrong-kind":
                    unit["cargo_target"]["target_kinds"] = ["lib"]
                    value["expected_units"][1] = copy.deepcopy(unit["cargo_target"])
                elif mutation == "missing-body":
                    # Both compiler inventories can omit the same real source body.
                    unit["census"]["bodies"] = unit["census"]["attempts"] = []
                elif mutation == "wrong-body":
                    unit["census"]["bodies"][0]["function"] = "same_name::wrong"
                elif mutation == "empty-attempts":
                    unit["census"]["attempts"] = []
                elif mutation == "unclosed":
                    unit["census"]["attempts"][0]["terminal"] = False
                elif mutation == "extra-attempt":
                    extra = copy.deepcopy(unit["census"]["attempts"][0])
                    extra["body"]["function"] = "same_name::undeclared"
                    unit["census"]["attempts"].append(extra)
                elif mutation == "wrong-expected":
                    value["expected_units"].pop()
                elif mutation == "duplicate-unit":
                    unit["cargo_target"]["unit_identity_sha256"] = "1" * 64
                    value["expected_units"][1] = copy.deepcopy(unit["cargo_target"])
                elif mutation == "incomplete":
                    value["availability"] = "incomplete"
                elif mutation == "wrong-hash":
                    value["proof_report_hash"] = "sha256:" + "0" * 64
                elif mutation == "wrong-package":
                    unit["cargo_target"]["package_name"] = "another-package"
                    value["expected_units"][1] = copy.deepcopy(unit["cargo_target"])
                with self.assertRaises(AssertionError):
                    validate(value)

    def test_binding_and_receipt_controls(self):
        for section, fields in (
            ("binding", ("unit_digest", "semantics_digest", "role", "target")),
            ("work", ("run_digest", "unit_digest", "semantics_digest", "work_digest", "attempt")),
            ("daemon", ("executable_sha256", "commit")),
        ):
            for field in fields:
                with self.subTest(section=section, field=field):
                    value = report()
                    census = value["units"][0]["census"]
                    grant = census["attempts"][0]["outcome"]["receipt"]["grant"]
                    target = {"binding": census["binding"], "work": grant["work"],
                              "daemon": grant["authority"]["daemon"]}[section]
                    target[field] = 2 if field == "attempt" else "bad"
                    with self.assertRaises(AssertionError):
                        validate(value)

    def test_positive_receipt_and_one_run_are_required(self):
        value = report()
        for unit in value["units"]:
            unit["census"]["attempts"][0]["outcome"] = {"state": "cache_reuse"}
        with self.assertRaises(AssertionError):
            validate(value)
        value = report()
        census = value["units"][1]["census"]
        census["binding"]["run_digest"] = "e" * 64
        census["attempts"][0]["outcome"]["receipt"]["grant"]["work"]["run_digest"] = "e" * 64
        with self.assertRaises(AssertionError):
            validate(value)

    def test_freshness_and_per_unit_identity_controls(self):
        first = validate(report())
        with self.assertRaises(AssertionError):
            RUNNER.validate_runs([first, first])
        second = report("f" * 64)
        for index, unit in enumerate(second["units"]):
            digest = str(4 - index) * 64
            unit["cargo_target"]["semantics_sha256"] = digest
            second["expected_units"][index]["semantics_sha256"] = digest
            unit["census"]["binding"]["semantics_digest"] = digest
            unit["census"]["attempts"][0]["outcome"]["receipt"]["grant"]["work"]["semantics_digest"] = digest
        with self.assertRaises(AssertionError):
            RUNNER.validate_runs([first, validate(second)])

    def test_fresh_invocation_unit_digests_may_change_with_exact_joins_intact(self):
        second = report("f" * 64)
        for index, unit in enumerate(second["units"]):
            digest = str(index + 7) * 64
            unit["cargo_target"]["unit_identity_sha256"] = digest
            unit["cargo_target"]["proof_unit_index"] += 10
            second["expected_units"][index] = copy.deepcopy(unit["cargo_target"])
            unit["census"]["binding"]["unit_digest"] = digest
            unit["census"]["attempts"][0]["outcome"]["receipt"]["grant"]["work"]["unit_digest"] = digest
        RUNNER.validate_runs([validate(report()), validate(second)])

    def test_optimized_interpreters_still_reject_empty_reports(self):
        value = report()
        value["units"] = value["expected_units"] = []
        program = (
            "import importlib.util,json,sys; "
            "s=importlib.util.spec_from_file_location('runner',sys.argv[1]); "
            "m=importlib.util.module_from_spec(s); s.loader.exec_module(m); "
            f"m.validate_report(json.loads(sys.argv[2]),{CANONICAL!r},{DAEMON_HASH!r},{COMMIT!r},{HOST!r})"
        )
        for option in ("-O", "-OO"):
            with self.subTest(option=option):
                child = subprocess.run([sys.executable, option, "-c", program,
                                        str(Path(__file__).with_name("run.py")), json.dumps(value)],
                                       text=True, capture_output=True, timeout=10)
                self.assertNotEqual(child.returncode, 0)
                self.assertIn("expected exactly the fixture lib and bin", child.stderr)


POLICY = """raise RuntimeError('policy source must never execute')
BUILD_AUTHORITY_ENV_NAMES = {'CC', 'GIT_DIR', 'PYTHONPATH', 'LD_PRELOAD'}
BUILD_AUTHORITY_ENV_PREFIXES = ('GIT_CONFIG_', 'SDK_')
"""


class EnvironmentTests(unittest.TestCase):
    def test_source_policy_is_read_as_data_and_applied_to_the_whole_environment(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            (root / "scripts/recreate_bootstrap.py").write_text(POLICY)
            poisoned = dict(CC="other-cc", GIT_DIR="other-repo", PYTHONPATH="other-code",
                            LD_PRELOAD="other-library", GIT_CONFIG_COUNT="1", SDK_TEST="other-sdk",
                            CARGO_TARGET_DIR="other-target", RUSTFLAGS="other-flags",
                            TRUST_TEST="other-policy", TRUSTD_TEST="other-daemon",
                            PATH="/tools", ATERM_SESSION_ID="retained", BUILD_SLOT_HELD="1")
            with mock.patch.dict(os.environ, poisoned, clear=True):
                self.assertEqual(RUNNER.qualification_environment(root, True),
                                 dict(PATH="/tools", ATERM_SESSION_ID="retained", BUILD_SLOT_HELD="1"))

    def test_local_mode_keeps_its_existing_policy_without_reading_the_driver(self):
        with mock.patch.dict(os.environ, dict(CC="kept", GIT_DIR="kept", RUSTFLAGS="removed",
                                             CARGO_TARGET_DIR="removed"), clear=True):
            self.assertEqual(RUNNER.qualification_environment(Path("/missing-source"), False),
                             dict(CC="kept", GIT_DIR="kept"))

    def test_missing_duplicate_and_nonliteral_policy_refuse(self):
        for policy in ("", POLICY + "BUILD_AUTHORITY_ENV_NAMES = {'OTHER'}\n",
                       POLICY.replace("{'CC', 'GIT_DIR', 'PYTHONPATH', 'LD_PRELOAD'}", "['CC']"),
                       POLICY.replace("('GIT_CONFIG_', 'SDK_')", "'GIT_CONFIG_'"),
                       POLICY.replace("('GIT_CONFIG_', 'SDK_')", "('',)"),
                       POLICY.replace("('GIT_CONFIG_', 'SDK_')", "tuple(['GIT_CONFIG_'])")):
            with self.subTest(policy=policy), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "scripts").mkdir()
                (root / "scripts/recreate_bootstrap.py").write_text(policy)
                with self.assertRaises((AssertionError, ValueError)):
                    RUNNER.qualification_environment(root, True)


class StageProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        (self.root / "scripts").mkdir()
        (self.root / "scripts/recreate_bootstrap.py").write_text(POLICY)
        self.bindir = self.root / "build" / HOST / "stage2/bin"
        self.make_tools(self.bindir)
        self.events = []
        self.environments = []
        self.provenance_count = self.native_count = 0
        self.fail_provenance = None

    def make_tools(self, bindir):
        bindir.mkdir(parents=True)
        for name in ("trustc", "targo", "targo-trust", "trustd"):
            (bindir / name).write_text("inert fixture " + name)

    def fake_run(self, argv, cwd, env):
        self.environments.append(dict(env))
        stdout = ""
        if argv[:2] == ["git", "rev-parse"]:
            self.events.append("source-head")
            stdout = COMMIT + "\n"
        elif argv[:2] == ["git", "status"]:
            self.events.append("source-clean")
        elif argv[0] == str(self.bindir / "trustc"):
            self.events.append("compiler")
            stdout = f"commit-hash: {COMMIT}\nhost: {HOST}\n"
        elif "--verify-stage-provenance" in argv:
            self.provenance_count += 1
            self.events.append(f"provenance-{self.provenance_count}")
            self.assertEqual(argv, [sys.executable, str(self.root / "scripts/recreate_bootstrap.py"),
                                   "--verify-stage-provenance", "--require-immutable-lineage",
                                   "--stage", "2", "--host", HOST])
            self.assertEqual(cwd, self.root)
            if self.fail_provenance == self.provenance_count:
                raise AssertionError("fixture stage provenance refused")
        elif argv[1:] == ["--unverified", "--version"]:
            self.events.append("discriminator")
        else:
            self.assertEqual(argv[:4], [str(self.bindir / "targo"), "trust", "check", "--report-dir"])
            self.native_count += 1
            self.events.append(f"native-{self.native_count}")
            destination = Path(argv[4])
            destination.mkdir()
            value = report("0" * 64 if self.native_count == 1 else "f" * 64)
            for unit in value["units"]:
                unit["census"]["attempts"][0]["outcome"]["receipt"]["grant"]["authority"]["daemon"][
                    "executable_sha256"] = RUNNER.digest_file(self.bindir / "trustd")
            (destination / "compiler-admission.json").write_text(json.dumps(value))
            (destination / "report.json").write_bytes(CANONICAL)
        return subprocess.CompletedProcess(argv, 0, stdout, "")

    def invoke(self, verify=True):
        argv = ["--bin", str(self.bindir)]
        if verify:
            argv.append("--verify-stage-provenance")
        output = io.StringIO()
        self.output = output
        with mock.patch.object(RUNNER, "__file__", str(self.root / "tests/native-admission-census/run.py")), \
             mock.patch.object(RUNNER, "run", side_effect=self.fake_run), \
             mock.patch.dict(os.environ, dict(CC="removed", GIT_DIR="removed", GIT_CONFIG_COUNT="1",
                                             SDK_TEST="removed", ATERM_SESSION_ID="retained"), clear=True), \
             mock.patch("sys.stdout", output):
            RUNNER.main(argv)
        return output.getvalue()

    def test_before_native_postchecks_after_and_success_use_one_clean_environment(self):
        self.assertIn("native admission:", self.invoke())
        self.assertEqual(self.events, ["source-head", "source-clean", "compiler", "provenance-1",
                                      "discriminator", "native-1", "native-2", "source-head",
                                      "source-clean", "provenance-2"])
        expected = dict(PATH=str(self.bindir) + os.pathsep, ATERM_SESSION_ID="retained")
        self.assertTrue(self.environments)
        self.assertTrue(all(env == expected for env in self.environments))

    def test_either_provenance_failure_refuses_success(self):
        for phase in (1, 2):
            with self.subTest(phase=phase):
                self.events.clear()
                self.native_count = self.provenance_count = 0
                self.fail_provenance = phase
                with self.assertRaisesRegex(AssertionError, "stage provenance refused"):
                    self.invoke()
                self.assertNotIn("native admission:", self.output.getvalue())
                self.assertEqual(self.native_count, 0 if phase == 1 else 2)

    def test_unrelated_bin_refuses_before_provenance_or_native_work(self):
        self.bindir = self.root / "unrelated/bin"
        self.make_tools(self.bindir)
        with self.assertRaisesRegex(AssertionError, "canonical Stage2 bin"):
            self.invoke()
        self.assertEqual(self.native_count, 0)
        self.assertEqual(self.provenance_count, 0)
        self.assertNotIn("native admission:", self.output.getvalue())

    def test_build_host_symlink_resolves_to_the_same_canonical_bin(self):
        host = self.root / "build" / HOST
        target = self.root / "host-output"
        host.rename(target)
        host.symlink_to(target, target_is_directory=True)
        self.bindir = (host / "stage2/bin").resolve()
        self.assertIn("native admission:", self.invoke())
        self.assertEqual(self.provenance_count, 2)

    def test_local_mode_still_accepts_an_explicit_unrelated_bin(self):
        self.bindir = self.root / "local/bin"
        self.make_tools(self.bindir)
        self.assertIn("native admission:", self.invoke(verify=False))
        self.assertEqual(self.provenance_count, 0)
        self.assertEqual(self.native_count, 2)
        self.assertTrue(all(env["CC"] == "removed" for env in self.environments))


if __name__ == "__main__":
    unittest.main()
