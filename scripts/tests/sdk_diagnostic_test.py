#!/usr/bin/env python3
"""Noncompiling owner/CLI controls. Fake SDK gates grant no real SDK grade."""
import contextlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


daily = load("diagnostic_daily_fixture", ROOT / "scripts/daily_toolchain_stage.py")
diag = load("sdk_diagnostic_fixture", ROOT / "scripts/sdk_diagnostic.py")


def executable(path, source):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)
    path.chmod(0o755)


class DiagnosticTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="sdk-diagnostic-fixture-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.work = self.root / "project"
        self.work.mkdir()
        self.cargo = self.root / "cargo"
        self.cargo.mkdir()
        self.sdk = self.root / "store/trust/2.noindex"
        self.marker = self.root / "command-marker"
        self.pub = self.root / "publication"
        executable(self.pub / "bin/pub", """import os, signal
def terminate_process_group(child):
    try: os.killpg(child.pid, signal.SIGTERM)
    except ProcessLookupError: pass
    try: child.wait(timeout=2)
    except Exception:
        try: os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError: pass
        child.wait(timeout=2)
""")
        self.bindir = self.root / "host-bin"
        self.serial = self.bindir / "trust-serial-command"
        executable(self.serial, "#!/bin/sh\nexit 0\n")
        executable(self.bindir / "rustup", """#!/bin/sh
if [ "$1 $2" = 'toolchain link' ]; then
    mkdir -p "$RUSTUP_HOME/toolchains"
    ln -s "$4" "$RUSTUP_HOME/toolchains/$3"
    exit 0
fi
if [ "$1" = run ]; then shift 2; tool=$1; shift; exec "$RUSTUP_HOME/toolchains/trust/bin/$tool" "$@"; fi
exit 2
""")
        self.make_sdk()
        self.env = {"HOME": str(self.root), "PATH": f"{self.bindir}:/usr/bin:/bin:/usr/sbin:/sbin",
                    "CARGO_HOME": str(self.cargo), "SDK_TEST_MARKER": str(self.marker),
                    "TRUST_TOOLCHAIN_PYTHON3": sys.executable}
        self.git("init", "-q")
        (self.work / "Cargo.toml").write_text('[package]\nname="fixture"\nversion="0.0.0"\n')
        self.git("add", ".")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture")
        self.counter = 0
        self.gate_failure = None
        self.gate_change = None

    def git(self, *args):
        return subprocess.check_output(["git", "-c", "core.hooksPath=/dev/null", "-C", str(self.work), *args],
                                       stderr=subprocess.STDOUT)

    def make_sdk(self):
        targo = """#!/bin/sh
sdk=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
if [ "$1" = --resource-capabilities ]; then printf '%s\n' '{"version":3,"cpu_workers":false,"supports_invocation":false}'; exit 0; fi
if [ "$1 $2" = '--unverified --version' ] || [ "$1" = --version ]; then echo 'targo 1.0 (targo fixture)'; exit 0; fi
if [ "$1 $2" = 'trust doctor' ]; then
  compiler="$sdk/bin/trustc"
  [ -z "${SDK_TEST_FOREIGN_DOCTOR-}" ] || compiler=/foreign/trustc
  frontend="$sdk/bin/targo"
  [ -z "${SDK_TEST_FOREIGN_FRONTEND-}" ] || frontend=/foreign/targo
  printf '{"ready":true,"compiler":{"trust_verify":true,"json_transport":true,"path":"%s","linked_toolchain_path":"%s","discovery_source":"sibling_trustc","linked_toolchain_status":"visible","daily_driver":{"ready":true,"linked_targo_path":"%s","linked_targo_trust_path":"%s/bin/targo-trust"}}}\n' "$compiler" "$compiler" "$frontend" "$sdk"
  exit 0
fi
printf '%s\n' "$0" "$*" "$RUSTUP_HOME" "$CARGO_TARGET_DIR" "$TARGO" > "$SDK_TEST_MARKER"
[ -z "${SDK_TEST_MUTATE_SOURCE-}" ] || printf changed >> "$SDK_TEST_MUTATE_SOURCE"
[ -z "${SDK_TEST_MUTATE_SDK-}" ] || printf changed >> "$sdk/lib/librustc_driver-fixture.dylib"
[ -z "${SDK_TEST_SLEEP-}" ] || sleep "$SDK_TEST_SLEEP"
exit "${SDK_TEST_EXIT:-0}"
"""
        executable(self.sdk / "bin/targo", targo)
        shutil.copy2(self.sdk / "bin/targo", self.sdk / "bin/cargo")
        compiler = """#!/bin/sh
if [ "$1 $2" = '--print sysroot' ]; then CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd; exit 0; fi
echo 'rustc 1.0 (trustc fixture)'
"""
        executable(self.sdk / "bin/trustc", compiler)
        shutil.copy2(self.sdk / "bin/trustc", self.sdk / "bin/rustc")
        banners = {"ay": "ay fixture", "ty": "ty fixture", "clean": "clean fixture",
                   "targo-trust": "targo-trust fixture", "trustd": "trustd fixture",
                   "trustdoc": "rustc 1.0 (trustdoc fixture)", "trustfmt": "trustfmt fixture",
                   "targo-fmt": "trustfmt fixture", "tippy": "tippy fixture", "targo-tippy": "tippy fixture",
                   "tippy-driver": "tippy fixture", "trust-analyzer": "trust-analyzer fixture"}
        for name, banner in banners.items():
            executable(self.sdk / "bin" / name, "#!/bin/sh\nprintf '%s\\n' '" + banner + "'\n")
        shutil.copy2(self.sdk / "bin/trustdoc", self.sdk / "bin/rustdoc")
        executable(self.sdk / "libexec/trust-analyzer-proc-macro-srv", "fixture shape only\n")
        (self.sdk / "lib").mkdir()
        (self.sdk / "lib/librustc_driver-fixture.dylib").write_bytes(b"nonexecuted fixture cohort DATA")

    def new_request(self):
        self.counter += 1
        state = self.root / f"diagnostic-{self.counter}"
        state.mkdir(mode=0o700)
        return {"schema": diag.SCHEMA, "scope": diag.SCOPE, "sdk": str(self.sdk),
                "repo": str(self.work), "state": str(state), "source": str(ROOT),
                "publication": str(self.pub), "serial": str(self.serial),
                "cargo_home": str(self.cargo), "timeout": 10,
                "command": ["targo", "--unverified", "check", "--locked", "--offline"]}

    def fixture_gates(self, call, sdk, source, host, python, promotion):
        # Only the first real surface gate runs fake executables. These two
        # stand-ins exercise orchestration without compiling fake Rust or
        # claiming actual libraries/native tool-start qualification.
        for name in ("fixture-library-contract", "fixture-tool-start"):
            if self.gate_change:
                self.gate_change(sdk)
            if name == self.gate_failure:
                raise ValueError(name + " refused")

    def fixture_owned_argv(self, slot, python, driver, cleanup, result, timeout, argv, admission):
        self.assertEqual(admission, ["--cpus", "6", "--mem-gb", "34"])
        # Fixture executables only: reuse the real original-exit/cleanup owner,
        # never make a real resource or SDK claim from these test processes.
        return [str(python), "-I", "-S", "-B", str(driver), "_owned-command", str(cleanup),
                str(result), str(timeout or 0), "--", *argv]

    def run_fixture(self, request=None, **environment):
        request = request or self.new_request()
        api = {**daily.__dict__, "full_sdk_gates": self.fixture_gates,
               "owned_step_argv": self.fixture_owned_argv}
        with mock.patch.dict(os.environ, {**self.env, **environment}, clear=True):
            code = diag.Diagnostic(api, request).run()
        value = json.loads((Path(request["state"]) / "worker-result.json").read_text())
        return code, value, request

    def test_positive_exact_frontend_private_environment_and_no_grade(self):
        original = os.environ.copy()
        code, value, request = self.run_fixture()
        self.assertEqual(code, 0, value.get("refusal"))
        self.assertEqual(os.environ, original)
        self.assertTrue(value["passed"])
        self.assertFalse(value["sdk_ready"] or value["consumer_ready"] or value["publication_ready"])
        self.assertEqual(value["command_result"]["command"][1:], request["command"][1:])
        lines = self.marker.read_text().splitlines()
        state = Path(request["state"])
        self.assertEqual(lines[0], str(state / "sdk/bin/targo"))
        self.assertEqual(lines[2:], [str(state / "rustup"), str(state / "target"), str(state / "sdk/bin/targo")])
        self.assertFalse((self.root / ".rustup/toolchains/trust").exists())

    def test_bad_alias_actual_complete_surface_refuses_before_copy_or_command(self):
        (self.sdk / "bin/cargo").write_text("#!/bin/sh\necho cargo fixture\n")
        code, value, request = self.run_fixture()
        self.assertEqual(code, 1)
        self.assertFalse(value["command_started"] or self.marker.exists())
        self.assertFalse((Path(request["state"]) / "sdk").exists())
        actual = Path(value["steps"][0]["log"]).read_text()
        self.assertIn("targo and cargo are not byte-identical same-surface artifacts", actual)
        self.assertNotIn("cannot be canonicalized", actual)

    def test_partial_sdk_refuses_before_command(self):
        (self.sdk / "bin/clean").unlink()
        code, value, _ = self.run_fixture()
        self.assertEqual(code, 1)
        self.assertFalse(value["command_started"] or self.marker.exists())

    def test_first_real_surface_binds_python_before_copy_even_when_path_python_refuses(self):
        executable(self.bindir / "python3", "#!/bin/sh\nexit 99\n")
        (self.sdk / "bin/cargo").write_text("#!/bin/sh\necho cargo fixture\n")
        code, value, request = self.run_fixture()
        self.assertEqual(code, 1)
        self.assertFalse(value["command_started"] or self.marker.exists())
        self.assertFalse((Path(request["state"]) / "sdk").exists())
        actual = Path(value["steps"][0]["log"]).read_text()
        self.assertIn("targo and cargo are not byte-identical same-surface artifacts", actual)
        self.assertNotIn("cannot be canonicalized", actual)

    def test_each_original_later_gate_failure_prevents_command(self):
        for failure in ("fixture-library-contract", "fixture-tool-start"):
            with self.subTest(failure=failure):
                self.gate_failure = failure
                code, value, _ = self.run_fixture()
                self.assertEqual(code, 1)
                self.assertIn(failure, value["refusal"])
                self.assertFalse(value["command_started"] or self.marker.exists())

    def test_changed_sdk_after_successful_fixture_gate_refuses(self):
        self.gate_change = lambda sdk: (sdk / "lib/librustc_driver-fixture.dylib").write_bytes(b"changed")
        code, value, _ = self.run_fixture()
        self.assertEqual(code, 1)
        self.assertFalse(value["command_started"] or self.marker.exists())

    def test_foreign_doctor_compiler_refuses(self):
        code, value, _ = self.run_fixture(SDK_TEST_FOREIGN_DOCTOR="1")
        self.assertEqual(code, 1)
        self.assertIn("different compiler", value["refusal"])
        self.assertFalse(value["command_started"] or self.marker.exists())

    def test_foreign_doctor_frontend_refuses(self):
        code, value, _ = self.run_fixture(SDK_TEST_FOREIGN_FRONTEND="1")
        self.assertEqual(code, 1)
        self.assertFalse(value["command_started"] or self.marker.exists())

    def test_project_parent_home_and_cli_movers_refuse_before_any_gate(self):
        for label, path, command in (
            ("project", self.work / ".cargo/config.toml", None),
            ("parent", self.root / ".cargo/config.toml", None),
            ("home", self.cargo / "config.toml", None),
            ("cli", None, ['--config', 'build.rustc="/foreign/trustc"']),
        ):
            with self.subTest(label=label):
                request = self.new_request()
                if path:
                    path.parent.mkdir(exist_ok=True)
                    path.write_text('[build]\nrustc="/foreign/trustc"\n')
                if command:
                    request["command"] += command
                code, value, _ = self.run_fixture(request)
                self.assertEqual(code, 1)
                self.assertFalse(value["steps"] or self.marker.exists())
                if path:
                    path.unlink()

    def test_env_mover_and_inherited_epoch_refuse(self):
        for environment in ({"RUSTC": "/foreign/trustc"}, {"CARGO_BUILD_TARGET": "foreign"},
                            {"CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS": "--sysroot=/foreign"},
                            {"BUILD_SLOT_HELD": "1"},
                            {"BUILD_SLOT_CPU_PROTOCOL": "2"}):
            with self.subTest(environment=environment):
                code, value, _ = self.run_fixture(**environment)
                self.assertEqual(code, 1)
                self.assertFalse(value["steps"] or self.marker.exists())

    def test_config_environment_cannot_replace_private_selection(self):
        for setting in ('env.PATH="/foreign"', 'env.TARGO="/foreign/targo"',
                        'target.aarch64-apple-darwin.runner="/foreign/runner"',
                        'build.rustflags=["--sysroot=/foreign"]', 'include="foreign.toml"'):
            with self.subTest(setting=setting):
                request = self.new_request()
                request["command"] += ["--config", setting]
                code, value, _ = self.run_fixture(request)
                self.assertEqual(code, 1)
                self.assertFalse(value["steps"] or self.marker.exists())

    def test_lane_foreign_entry_target_directory_and_worker_refuse(self):
        for command in (["targo", "check", "--locked", "--offline"],
                        ["/foreign/targo", "--unverified", "check", "--locked", "--offline"],
                        ["targo", "trust", "check", "--unverified", "--locked", "--offline"],
                        ["targo", "--unverified", "check", "--target", "native", "--locked", "--offline"],
                        ["targo", "--unverified", "check", "-qC/foreign", "--locked", "--offline"],
                        ["targo", "--unverified", "test", "--", "--locked", "--offline"],
                        ["targo", "--unverified", "test", "--locked", "--", "--offline"],
                        ["targo", "--unverified", "check", "--resource-worker-v2", "--locked", "--offline"]):
            with self.subTest(command=command):
                request = self.new_request()
                request["command"] = command
                code, value, _ = self.run_fixture(request)
                self.assertEqual(code, 1)
                self.assertFalse(value["command_started"] or self.marker.exists())

    def test_actual_nonzero_retained_without_promoting_result(self):
        code, value, _ = self.run_fixture(SDK_TEST_EXIT="7")
        self.assertEqual(code, 1)
        self.assertEqual(value["command_result"]["owned_result"]["exit_code"], 7)
        self.assertFalse(value["passed"])

    def test_original_admission_refusal_reports_attempt_without_claiming_child_start(self):
        request = self.new_request()
        def refusing_slot(slot, python, driver, cleanup, result, timeout, argv, admission):
            self.assertEqual(admission, ["--cpus", "6", "--mem-gb", "34"])
            # Exercise the original gate's actual invalid-admission refusal.
            # The negative does not ask a real worker for a reduced profile.
            return daily.owned_step_argv(slot, python, driver, cleanup, result, timeout,
                                         argv, ["--cpus", "0", "--mem-gb", "34"])
        api = {**daily.__dict__, "full_sdk_gates": self.fixture_gates, "owned_step_argv": refusing_slot}
        with mock.patch.dict(os.environ, self.env, clear=True):
            code = diag.Diagnostic(api, request).run()
        value = json.loads((Path(request["state"]) / "worker-result.json").read_text())
        self.assertEqual(code, 1)
        self.assertTrue(value["command_attempted"])
        self.assertIsNone(value["command_started"])
        self.assertNotIn("owned_result", value["command_result"])
        self.assertFalse(self.marker.exists() or value["passed"])

    def test_actual_timeout_retains_child_and_original_cleanup_result(self):
        request = self.new_request()
        request["timeout"] = 1
        code, value, _ = self.run_fixture(request, SDK_TEST_SLEEP="20")
        self.assertEqual(code, 1)
        self.assertTrue(value["command_result"]["owned_result"]["timed_out"])
        self.assertIsInstance(value["command_result"]["owned_result"]["exit_code"], int)
        detail, actual = value["command_result"]["owned_result"], value["command_result"]
        self.assertEqual(actual["exit_code"], detail["exit_code"])
        self.assertEqual(actual["timed_out"], detail["timed_out"])
        self.assertEqual(actual["interrupted"], detail["interrupted"])
        self.assertEqual(actual["wrapper_exit_code"], 124)
        self.assertIn(f'actual owned child exited {detail["exit_code"]}', value["refusal"])

    def test_source_change_after_actual_exit_zero_withholds_stability(self):
        code, value, _ = self.run_fixture(SDK_TEST_MUTATE_SOURCE=str(self.work / "Cargo.toml"))
        self.assertEqual(code, 1)
        self.assertEqual(value["command_result"]["owned_result"]["exit_code"], 0)
        self.assertTrue(value["command_started"])
        self.assertFalse(value["passed"])

    def test_sdk_change_after_actual_exit_zero_withholds_stability(self):
        code, value, _ = self.run_fixture(SDK_TEST_MUTATE_SDK="1")
        self.assertEqual(code, 1)
        self.assertEqual(value["command_result"]["owned_result"]["exit_code"], 0)
        self.assertTrue(value["command_started"])
        self.assertFalse(value["passed"])

    def test_unmanaged_directory_is_not_a_successful_native_lease(self):
        current = self.sdk.parent / "1.noindex"
        current.mkdir()
        record = {"package": "trust", "store_root": str(current)}
        diag.managed_sdk(self.sdk, record)
        foreign = self.root / "unmanaged"
        foreign.mkdir()
        with self.assertRaisesRegex(ValueError, "unmanaged lease"):
            diag.managed_sdk(foreign, record)

    def test_build_identity_matches_the_native_positive_u64_domain(self):
        current = self.sdk.parent / "1.noindex"
        current.mkdir()
        record = {"package": "trust", "store_root": str(current)}
        for name in ("0", "00", "02.noindex", str(1 << 64), str(1 << 64) + ".noindex"):
            path = self.sdk.parent / name
            path.mkdir()
            with self.subTest(name=name), self.assertRaises(ValueError):
                diag.managed_sdk(path, record)
        last = self.sdk.parent / str((1 << 64) - 1)
        last.mkdir()
        # Domain admission is lifetime selection, not signed installation.
        diag.managed_sdk(last, record)

    def test_public_cli_refused_or_noop_lease_never_runs_command(self):
        executable(self.bindir / "aterm", "#!/bin/sh\nexit 0\n")
        current = self.sdk.parent / "1.noindex"
        current.mkdir()
        serial_root = self.root / "store/trust-resource-controller/1.noindex"
        serial = serial_root / "bin/trust-serial-command"
        executable(serial, "#!/bin/sh\nexit 0\n")
        records = {"targo": {"package": "trust", "store_root": str(current)},
                   "trust-serial-command": {"physical_executable": str(serial), "store_root": str(serial_root)}}
        for refused in (False, True):
            with self.subTest(refused=refused):
                state = self.root / ("lease-refused" if refused else "lease-noop")
                argv = ["--sdk", str(self.sdk), "--repo", str(self.work), "--state-root", str(state),
                        "--publication-repo", str(self.pub), "--cargo-home", str(self.cargo), "--timeout", "30",
                        "--", "targo", "--unverified", "check", "--locked", "--offline"]

                def lease(command, cwd, env, log, **kwargs):
                    self.assertEqual(command[:3], [str(self.bindir / "aterm"), "pkg", "lease"])
                    self.assertEqual(command[3], str(self.sdk))
                    log.write_text("fixture native lease refused/no-op; no SDK standing\n")
                    if refused:
                        raise daily.CommandFailed("fixture lease refusal", 75)
                    return ""

                api = {**daily.__dict__, "command": lease}
                with mock.patch.dict(os.environ, self.env, clear=True), mock.patch.object(
                        diag, "native_record", side_effect=lambda _aterm, tool: records[tool]):
                    code = diag.main(argv, api)
                value = json.loads((state / "result.json").read_text())
                self.assertEqual(code, 1)
                self.assertFalse(value["passed"] or value["command_started"] or self.marker.exists())
                self.assertIsNone(value["command_started"])
                self.assertEqual(value["native_lease_exit"], 75 if refused else 0)

    def test_public_parent_interrupt_retains_after_start_child_or_reports_unknown(self):
        executable(self.bindir / "aterm", "#!/bin/sh\nexit 0\n")
        current = self.sdk.parent / "1.noindex"
        current.mkdir()
        serial_root = self.root / "store/trust-resource-controller/1.noindex"
        serial = serial_root / "bin/trust-serial-command"
        executable(serial, "#!/bin/sh\nexit 0\n")
        records = {"targo": {"package": "trust", "store_root": str(current)},
                   "trust-serial-command": {"physical_executable": str(serial), "store_root": str(serial_root)}}
        for terminal in (True, False):
            with self.subTest(terminal=terminal):
                state = self.root / ("interrupt-terminal" if terminal else "interrupt-unknown")
                argv = ["--sdk", str(self.sdk), "--repo", str(self.work), "--state-root", str(state),
                        "--publication-repo", str(self.pub), "--cargo-home", str(self.cargo), "--timeout", "30",
                        "--", "targo", "--unverified", "check", "--locked", "--offline"]
                detail = {"exit_code": -15, "timed_out": False, "interrupted": True}

                def lease(*args, **kwargs):
                    request = json.loads((state / "request.json").read_text())
                    if terminal:
                        child = {"schema": diag.SCHEMA, "scope": diag.SCOPE, "request": request,
                                 "passed": True, "command_started": True, "command_attempted": True,
                                 "command_result": {"owned_result": detail},
                                 "sdk_ready": False, "consumer_ready": False, "publication_ready": False,
                                 "native_lease_exit": 0}
                        (state / "worker-result.json").write_text(json.dumps(child))
                    error = InterruptedError("fixture parent interrupted after worker launch")
                    error.child_exit_code = 143
                    raise error

                with mock.patch.dict(os.environ, self.env, clear=True), mock.patch.object(
                        diag, "native_record", side_effect=lambda _aterm, tool: records[tool]):
                    code = diag.main(argv, {**daily.__dict__, "command": lease})
                value = json.loads((state / "result.json").read_text())
                self.assertEqual(code, 130)
                self.assertFalse(value["passed"])
                self.assertTrue(value["interrupted"])
                self.assertEqual(value["native_lease_exit"], 143)
                self.assertEqual(value["command_started"], True if terminal else None)
                if terminal:
                    self.assertEqual(value["command_result"]["owned_result"], detail)
                else:
                    self.assertIn("worker_collection_refusal", value)

    def test_original_full_sdk_gate_order_and_selected_python_are_preserved(self):
        calls = []
        daily.full_sdk_gates(lambda *args, **kwargs: calls.append((args, kwargs)), self.sdk,
                             ROOT, "aarch64-apple-darwin", Path("/selected/python"), {"selection": "exact"})
        self.assertEqual([args[0] for args, _ in calls],
                         ["toolchain-output-contract", "sysroot-library-contract", "staged-ui-and-tool-start"])
        self.assertEqual(calls[1][0][1][:4], ["/selected/python", "-I", "-S", "-B"])
        self.assertEqual(calls[2][1], {"heavy": True, "env": {"selection": "exact"}})

    def test_source_reader_uses_original_fixed_git_and_closed_environment(self):
        marker = self.root / "foreign-git-marker"
        executable(self.bindir / "git", '#!/bin/sh\nprintf wrong > "' + str(marker) + '"\nexit 1\n')
        with mock.patch.dict(os.environ, {**self.env, "GIT_DIR": "/foreign", "GIT_CONFIG_COUNT": "1",
                                         "GIT_CONFIG_KEY_0": "core.fsmonitor", "GIT_CONFIG_VALUE_0": "/foreign"}, clear=True):
            reader = diag.GitReader(ROOT)
            actual = reader.read(self.work, "rev-parse", "--show-toplevel").decode().strip()
        self.assertEqual(Path(actual), self.work)
        self.assertFalse(marker.exists())
        self.assertNotIn("GIT_DIR", reader.environment)
        self.assertNotIn("GIT_CONFIG_COUNT", reader.environment)

    def test_sparse_source_book_preserves_absence_without_expanding_index(self):
        for name in ("selected/current", "omitted/unmaterialized"):
            path = self.work / name
            path.parent.mkdir()
            path.write_text(name)
        self.git("add", ".")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "sparse")
        missing = self.git("rev-parse", "HEAD:omitted/unmaterialized").decode().strip()
        self.git("sparse-checkout", "init", "--cone", "--sparse-index")
        self.git("sparse-checkout", "set", "selected")
        index = (self.work / ".git/index").read_bytes()
        (self.work / ".git/objects" / missing[:2] / missing[2:]).unlink()
        output = self.root / "sparse-source.jsonl"
        book = diag.worktree_book(daily.__dict__, self.work, output, diag.GitReader(ROOT))
        rows = {item["path"]: item for item in map(json.loads, output.read_text().splitlines())}
        self.assertEqual(book["entries"], 3)
        self.assertEqual(rows["omitted/unmaterialized"]["kind"], "absent")
        self.assertEqual(rows["selected/current"]["kind"], "file")
        self.assertEqual(index, (self.work / ".git/index").read_bytes())

    def test_shared_environment_is_literal_original_consumer_mapping(self):
        base = {"HOME": "/owned", "other": "unchanged"}
        actual = daily.consumer_environment(base, Path("/sdk"), Path("/private/rustup"), Path("/private/target"), "/usr/bin")
        self.assertEqual(actual, {**base, "RUSTUP_HOME": "/private/rustup", "CARGO_TARGET_DIR": "/private/target",
                                 "TARGO": "/sdk/bin/targo", "PATH": "/private/rustup/bin:/sdk/bin:/usr/bin"})
        self.assertEqual(base, {"HOME": "/owned", "other": "unchanged"})


if __name__ == "__main__":
    unittest.main()
