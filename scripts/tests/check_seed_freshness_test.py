#!/usr/bin/env python3
"""Focused regressions for the executable stage0 identity probe."""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import tempfile
import signal
import unittest
from pathlib import Path
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "check_seed_freshness.py"
SPEC = importlib.util.spec_from_file_location("check_seed_freshness", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
freshness = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = freshness
SPEC.loader.exec_module(freshness)
seed_compiler_identity = sys.modules["seed_compiler_identity"]


class SeedFixtureCase(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        bridge = Path(scratch.name) / "bridge"
        bridge.write_text("#!/bin/sh\nshift\nexec \"$@\"\n")
        bridge.chmod(0o700)
        # Unit fixtures preserve actual argv but confer no native admission.
        self.enterContext(mock.patch.object(freshness.native_serial,
                          "managed_serial_executor", return_value=bridge))
        # These executable fixtures isolate banner/argv/custody behavior. The
        # separate identity tests use real pinned tar members and no auth mock.
        self.enterContext(mock.patch.object(
            freshness, "authenticate_compiler",
            side_effect=lambda _root, binary, _stage0, **_kw:
                seed_compiler_identity.compiler_snapshot(binary),
        ))


@unittest.skipUnless(os.name == "posix", "executable seed fixture requires POSIX")
class MaterializedStage0IdentityTests(SeedFixtureCase):
    def test_identity_mismatch_never_emits_identity_match_note(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = root / "build/test-host/stage0/bin/rustc"
            binary.parent.mkdir(parents=True)
            binary.write_text(
                """#!/usr/bin/env python3
import pathlib
import sys

if "-vV" in sys.argv:
    print("rustc 1.99.0-trust")
    print("commit-hash: 2222222222222222222222222222222222222222")
    print("commit-date: 2026-07-13")
    print("release: 1.99.0-trust")
else:
    output = pathlib.Path(sys.argv[sys.argv.index("-o") + 1])
    output.write_bytes(b"rmeta")
""",
                encoding="utf-8",
            )
            binary.chmod(0o755)
            stage0 = {
                "compiler_git_commit_hash": "1" * 40,
                "compiler_date": "2026-07-13",
                "compiler_version": "1.99.0-trust",
            }

            (binary.parent.parent / ".rustc-stamp").write_text(freshness.stage0_extraction_stamp(stage0), encoding="utf-8")
            with mock.patch.object(freshness, "ROOT", root):
                errors, notes = freshness.probe_materialized_stage0(stage0)

            self.assertTrue(any("commit-hash" in error for error in errors))
            self.assertFalse(any("identity matches the pin" in note for note in notes))

    def test_a_seed_on_the_trust_version_line_is_checked_against_its_trust_line(self) -> None:
        # A re-pin minted after the version split names its archives on Trust's
        # line (0.10.0-trust) while `release:` stays on Rust's (1.99.0-dev).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = root / "build" / "test-host" / "stage0" / "bin" / "rustc"
            binary.parent.mkdir(parents=True)
            binary.write_text(
                FAKE_SEED.replace(
                    'print("release: 1.99.0-trust")',
                    'print("release: 1.99.0-dev")\n    print("trust: {trust}")',
                ).format(commit=PIN, trust="0.10.0+g1111111"),
                encoding="utf-8",
            )
            binary.chmod(0o755)
            stage0 = {
                "compiler_git_commit_hash": PIN,
                "compiler_date": "2026-09-29",
                "compiler_version": "0.10.0-trust",
            }
            (binary.parent.parent / ".rustc-stamp").write_text(freshness.stage0_extraction_stamp(stage0), encoding="utf-8")
            with mock.patch.object(freshness, "ROOT", root):
                errors, _notes = freshness.probe_materialized_stage0(stage0)
            # commit-date in the fixture is 2026-07-13, so only that differs.
            self.assertTrue(any("commit-date" in error for error in errors), errors)
            self.assertFalse(any("major.minor" in error for error in errors), errors)
            stage0["compiler_version"] = "0.11.0-trust"
            (binary.parent.parent / ".rustc-stamp").write_text(freshness.stage0_extraction_stamp(stage0), encoding="utf-8")
            with mock.patch.object(freshness, "ROOT", root):
                errors, _notes = freshness.probe_materialized_stage0(stage0)
            self.assertTrue(any("trust '0.10.0+g1111111'" in error for error in errors), errors)

    def test_extraction_of_an_older_pin_is_a_note_not_a_failure(self) -> None:
        # The day a re-pin lands, every checkout still holds the previous pin's
        # extraction. Bootstrap re-extracts it (its stamp binds the compiler/archive identity),
        # so it is not the seed of the next build and must not turn the gate red.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = write_seed(root / "build" / "test-host" / "stage0" / "bin" / "rustc", OTHER)
            stage0 = {
                "compiler_git_commit_hash": PIN,
                "compiler_date": "2026-09-30",
                "compiler_version": "1.99.0-trust",
            }
            (binary.parent.parent / ".rustc-stamp").write_text("2026-07-13", encoding="utf-8")
            with mock.patch.object(freshness, "ROOT", root):
                errors, notes = freshness.probe_materialized_stage0(stage0)
            self.assertEqual(errors, [])
            self.assertTrue(any("re-extracts the pinned seed" in note for note in notes))

    def test_same_day_older_pin_identity_is_stale_even_when_its_date_matches(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = write_seed(root / "build/test-host/stage0/bin/rustc", OTHER)
            previous = {
                "compiler_git_commit_hash": OTHER, "compiler_date": "2026-07-13",
                "compiler_version": "1.99.0-trust",
            }
            (binary.parent.parent / ".rustc-stamp").write_text(freshness.stage0_extraction_stamp(previous))
            current = {**previous, "compiler_git_commit_hash": PIN}
            with mock.patch.object(freshness, "ROOT", root), \
                    mock.patch.object(freshness, "probe_seed_binary", side_effect=AssertionError("stale seed probed")):
                errors, notes = freshness.probe_materialized_stage0(current)
            self.assertEqual(errors, [])
            self.assertTrue(any("re-extracts the pinned seed" in note for note in notes))


PIN = "1" * 40
OTHER = "2" * 40
FAKE_SEED = """#!/usr/bin/env python3
import os
import pathlib
import sys

if "-vV" in sys.argv:
    print("rustc 1.99.0-trust")
    print("commit-hash: {commit}")
    print("commit-date: 2026-07-13")
    print("release: 1.99.0-trust")
    raise SystemExit(0)
# The stage0 contract: bootstrap hands a snapshot `--cfg bootstrap` and the
# off-switch through TRUST_NO_VERIFY=1, never a verifier flag on argv.
if os.environ.get("TRUST_NO_VERIFY") != "1" or any(a.startswith("-Z") for a in sys.argv):
    print("error: unknown unstable option", file=sys.stderr)
    raise SystemExit(1)
pathlib.Path(sys.argv[sys.argv.index("-o") + 1]).write_bytes(b"rmeta")
"""


def write_seed(path: Path, commit: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(FAKE_SEED.format(commit=commit), encoding="utf-8")
    path.chmod(0o755)
    return path


def fixture_tree(root: Path) -> None:
    """A minimal tree the whole gate runs against, pinned at PIN."""
    (root / "scripts").mkdir(parents=True)
    (root / "scripts" / "check_seed_freshness.py").write_bytes(SCRIPT.read_bytes())
    (root / "scripts/lib").mkdir()
    for name in ("native_serial.py", "landing_targo.py", "seed_compiler_identity.py"):
        (root / "scripts/lib" / name).write_bytes((SCRIPT.parent / "lib" / name).read_bytes())
    # The gate reads a config through the pack cut's reader.
    (root / "scripts" / "mint_seed_support.py").write_bytes(
        (SCRIPT.parent / "mint_seed_support.py").read_bytes()
    )
    (root / "src").mkdir()
    (root / "src/bootstrap").mkdir()
    (root / "src/bootstrap/stage0_identity.py").write_bytes(
        (SCRIPT.parent.parent / "src/bootstrap/stage0_identity.py").read_bytes()
    )
    (root / "src" / "rust-compat-version").write_text("1.99.0\n", encoding="utf-8")
    manifest = "a" * 64
    (root / "src" / "stage0").write_text(
        "\n".join(
            [
                f"compiler_channel_manifest_hash={manifest}",
                f"compiler_git_commit_hash={PIN}",
                "compiler_date=2026-07-13",
                "compiler_version=1.99.0-trust",
                f"rustfmt_channel_manifest_hash={manifest}",
                f"rustfmt_git_commit_hash={PIN}",
                "rustfmt_date=2026-07-13",
                "rustfmt_version=1.99.0-trust",
                "",
            ]
        ),
        encoding="utf-8",
    )


def run_gate(root: Path, *args: str) -> "subprocess.CompletedProcess[str]":
    env = {k: v for k, v in os.environ.items() if k != "RUST_BOOTSTRAP_CONFIG"}
    return subprocess.run(
        [sys.executable, str(root / "scripts" / "check_seed_freshness.py"), *args],
        capture_output=True,
        text=True,
        cwd=root,
        env=env,
        pass_fds=freshness.landing_targo.resource_fds(env),
        timeout=120,
    )


@unittest.skipUnless(os.name == "posix", "executable seed fixture requires POSIX")
class ConfiguredSeedTests(SeedFixtureCase):
    """TRUST-19 / D12: a configured [build] rustc or cargo IS a seed, and is refused."""

    def test_configured_seed_that_is_not_the_pin_fails_the_gate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture_tree(root)
            seed = write_seed(root / "store" / "7" / "bin" / "trustc", OTHER)
            (root / "bootstrap.toml").write_text(
                f'[build]\nrustc = "{seed}"\n', encoding="utf-8"
            )
            result = run_gate(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("FAIL: configured seed", result.stdout)
            self.assertIn(str(seed), result.stdout)

    def test_configured_seed_fails_even_when_it_reports_the_pin(self) -> None:
        # D12: the committed pin is the only seed. An identity line is a claim;
        # the pin is checksum-bound archives, so a matching -vV earns nothing.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture_tree(root)
            seed = write_seed(root / "store" / "7" / "bin" / "trustc", PIN)
            (root / "bootstrap.toml").write_text(
                f'[build]\nrustc = "{seed}"\n', encoding="utf-8"
            )
            result = run_gate(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("overrides the src/stage0 pin", result.stdout)
            self.assertNotIn("identity matches the pin", result.stdout)

    def test_a_configured_cargo_alone_is_a_seed_override(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture_tree(root)
            (root / "bootstrap.toml").write_text(
                'build.cargo = "/opt/elsewhere/bin/cargo"\n', encoding="utf-8"
            )
            result = run_gate(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("[build] cargo", result.stdout)

    def test_an_include_or_a_profile_cannot_carry_a_seed_past_the_gate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture_tree(root)
            (root / "seed.toml").write_text('[build]\nrustc = "/pkg/store/trust/9192/bin/trustc"\n')
            (root / "bootstrap.toml").write_text('include = ["seed.toml"]\n', encoding="utf-8")
            result = run_gate(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("[build] rustc = '/pkg/store/trust/9192/bin/trustc'", result.stdout)
            defaults = root / "src" / "bootstrap" / "defaults"
            defaults.mkdir(parents=True)
            (defaults / "bootstrap.dist.toml").write_text('[build]\ncargo = "/elsewhere/cargo"\n')
            (root / "bootstrap.toml").write_text('profile = "dist"\n', encoding="utf-8")
            result = run_gate(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("[build] cargo = '/elsewhere/cargo'", result.stdout)

    def test_an_override_on_a_good_pin_is_named_a_local_override_not_a_stale_seed(self) -> None:
        # The committed pin passes; only this checkout's bootstrap.toml is red.
        # Still a refusal (D12), but the verdict names the local fix.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture_tree(root)
            (root / "bootstrap.toml").write_text(
                '[build]\nrustc = "/opt/elsewhere/bin/rustc"\n', encoding="utf-8"
            )
            result = run_gate(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("configures its own seed", result.stdout)
            self.assertIn("authenticated_fetch", result.stdout)
            self.assertNotIn("re-seed before this change lands", result.stdout)

    def test_a_stale_pin_under_an_override_is_still_a_re_seed(self) -> None:
        # Control: a red committed seed keeps the re-seed verdict, override or not.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture_tree(root)
            (root / "src" / "rust-compat-version").write_text("1.98.0\n", encoding="utf-8")
            (root / "bootstrap.toml").write_text(
                '[build]\nrustc = "/opt/elsewhere/bin/rustc"\n', encoding="utf-8"
            )
            result = run_gate(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("is NEWER than source", result.stdout)
            self.assertIn("re-seed before this change lands", result.stdout)
            self.assertNotIn("configures its own seed", result.stdout)

    def test_unfetched_payloads_on_a_good_pin_say_fetch_not_re_seed(self) -> None:
        # --require-payloads with nothing materialized: a local red, named so.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture_tree(root)
            result = run_gate(root, "--require-payloads")
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("FAIL: --require-payloads", result.stdout)
            self.assertIn("has not materialized the pinned seed's payloads", result.stdout)
            self.assertNotIn("re-seed before this change lands", result.stdout)

    def test_config_without_seed_selectors_is_the_pinned_download(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture_tree(root)
            (root / "bootstrap.toml").write_text(
                '[build]\nrustfmt = "/opt/fmt/bin/trustfmt"\n', encoding="utf-8"
            )
            result = run_gate(root)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("sets no [build] rustc or cargo", result.stdout)

    def test_no_config_is_the_pinned_download(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture_tree(root)
            result = run_gate(root)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("no bootstrap config", result.stdout)

    def test_materialized_probe_uses_bootstraps_snapshot_transport(self) -> None:
        # The fake seed refuses any -Z flag on argv and requires
        # TRUST_NO_VERIFY=1, exactly as bootstrap drives a snapshot.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = write_seed(root / "build" / "test-host" / "stage0" / "bin" / "rustc", PIN)
            (binary.parent.parent / ".rustc-stamp").write_text("2026-07-13", encoding="utf-8")
            stage0 = {
                "compiler_git_commit_hash": PIN,
                "compiler_date": "2026-07-13",
                "compiler_version": "1.99.0-trust",
            }
            (binary.parent.parent / ".rustc-stamp").write_text(freshness.stage0_extraction_stamp(stage0), encoding="utf-8")
            with mock.patch.object(freshness, "ROOT", root):
                errors, notes = freshness.probe_materialized_stage0(stage0)
            self.assertEqual(errors, [])
            self.assertTrue(any("identity matches the pin" in note for note in notes))


class SeedCustodyTests(SeedFixtureCase):
    def test_windows_materialized_compiler_is_unavailable_without_execution(self):
        stage0 = {"compiler_git_commit_hash": PIN, "compiler_date": "2026-07-13",
                  "compiler_version": "1.99.0-trust"}
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            binary = root / "build/test-host/stage0/bin/rustc"
            binary.parent.mkdir(parents=True)
            binary.write_text("not an executable")
            stamp = binary.parent.parent / ".rustc-stamp"
            stamp.write_text(freshness.stage0_extraction_stamp(stage0))
            with mock.patch.object(freshness, "ROOT", root), \
                    mock.patch.object(freshness.sys, "platform", "win32"), \
                    mock.patch.object(freshness, "probe_seed_binary", side_effect=AssertionError("executed")), \
                    mock.patch.object(freshness.os, "execv", side_effect=AssertionError("gate")):
                errors, _ = freshness.probe_materialized_stage0(stage0)
                self.assertEqual(len(errors), 1)
                self.assertIsInstance(errors[0], freshness.ProbeUnavailable)
                binary.unlink()
                errors, notes = freshness.probe_materialized_stage0(stage0)
                self.assertEqual(errors, [])
                self.assertTrue(notes)

    def test_original_descriptor_and_exact_contract_argv_reach_compiler(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = write_seed(root / "rustc", PIN)
            ledger = root / "argv"
            source = binary.read_text().replace(
                'if "-vV" in sys.argv:',
                'import json\n'
                'with open(os.environ["PROBE_LEDGER"], "a") as log:\n'
                '    log.write(json.dumps([sys.argv[1:], os.fstat(int(os.environ["TRUST_CPU_IMPLICIT_FD"])).st_ino]) + "\\n")\n'
                'if "-vV" in sys.argv:')
            binary.write_text(source)
            # A transparent test-only stand-in isolates argv/FD forwarding. It
            # supplies no admission; the real pinned seed is checked separately.
            bridge = root / "bridge"
            bridge.write_text("#!/bin/sh\nshift\nexec \"$@\"\n")
            bridge.chmod(0o700)
            with (root / "lease").open("w+b") as lease:
                env = dict(os.environ, PROBE_LEDGER=str(ledger),
                           TRUST_CPU_IMPLICIT_FD=str(lease.fileno()))
                with mock.patch.dict(os.environ, env, clear=True), mock.patch.object(
                        freshness.native_serial, "managed_serial_executor", return_value=bridge):
                    errors, notes = freshness.probe_seed_binary(binary, "fixture", {
                        "compiler_git_commit_hash": PIN, "compiler_date": "2026-07-13",
                        "compiler_version": "1.99.0-trust"})
                self.assertEqual(errors, [])
                import json
                records = [json.loads(line) for line in ledger.read_text().splitlines()]
                self.assertEqual(records[0][0], ["-vV"])
                self.assertEqual(records[1][0][:7],
                                 ["--edition", "2021", "--crate-type", "lib", "--emit=metadata", "--cfg", "bootstrap"])
                self.assertEqual([record[1] for record in records], [os.fstat(lease.fileno()).st_ino] * 2)
                self.assertTrue(notes)

    def test_inherited_blocked_cancellation_refuses_before_launch_without_unblocking(self):
        previous = signal.pthread_sigmask(signal.SIG_BLOCK, (signal.SIGTERM,))
        try:
            blocked = signal.pthread_sigmask(signal.SIG_BLOCK, ())
            with mock.patch.object(freshness.subprocess, "Popen") as launch:
                with self.assertRaises(RuntimeError):
                    freshness.run_seed_command(["unlaunched"], env=dict(os.environ), timeout=120)
                launch.assert_not_called()
            self.assertEqual(signal.pthread_sigmask(signal.SIG_BLOCK, ()), blocked)
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous)

    def test_timeout_and_cancellation_wait_for_owned_term_cleanup(self):
        import time
        real_monotonic = time.monotonic
        for reason in ("timeout", "launch-cancel", "communicate-cancel", "complete-cancel", "result-cancel", "term-error"):
            with self.subTest(reason=reason), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                marker, ready = root / "reaped", root / "ready"
                program = root / "owner.py"
                program.write_text("import signal,time,pathlib,sys\n"
                                   "def stop(*_):\n"
                                   " pathlib.Path(sys.argv[1]).write_text('cleaned')\n"
                                   " raise SystemExit(0)\n"
                                   "signal.signal(signal.SIGTERM,stop)\n"
                                   "pathlib.Path(sys.argv[2]).write_text('ready')\n"
                                   "while True: time.sleep(.01)\n")
                actual_popen = subprocess.Popen
                clock = [0.0]
                def ready_owner(*args, **kwargs):
                    process = actual_popen(*args, **kwargs)
                    try:
                        deadline = real_monotonic() + 60
                        while not ready.exists() and process.poll() is None and real_monotonic() < deadline:
                            time.sleep(.01)
                        if not ready.exists() or ready.read_text() != "ready":
                            raise AssertionError("owned fixture did not install its TERM handler")
                    except BaseException:
                        process.terminate()
                        process.communicate()
                        raise
                    communicate = process.communicate
                    if reason == "term-error":
                        terminate = process.terminate
                        def failed_term():
                            terminate()
                            raise PermissionError("injected signal error after real delivery")
                        process.terminate = failed_term
                    first = True
                    def observe(*args, **kwargs):
                        nonlocal first
                        if first and kwargs.get("timeout") is not None:
                            first = False
                            if reason in ("complete-cancel", "result-cancel"):
                                process.terminate()
                                result = communicate()
                                if reason == "complete-cancel":
                                    os.kill(os.getpid(), signal.SIGTERM)
                                return result
                            if reason in ("timeout", "term-error"):
                                clock[0] = 121.0
                            else:
                                os.kill(os.getpid(), signal.SIGTERM)
                            raise subprocess.TimeoutExpired(process.args, kwargs["timeout"])
                        # A second cancellation during cleanup must only record;
                        # it cannot bypass the real owner communicate/reap.
                        os.kill(os.getpid(), signal.SIGTERM)
                        return communicate(*args, **kwargs)
                    process.communicate = observe
                    if reason == "launch-cancel":
                        os.kill(os.getpid(), signal.SIGTERM)
                    return process
                completed = subprocess.CompletedProcess
                def result_record(*args, **kwargs):
                    if reason == "result-cancel":
                        os.kill(os.getpid(), signal.SIGTERM)
                    return completed(*args, **kwargs)
                expected = subprocess.TimeoutExpired if reason in ("timeout", "term-error") else KeyboardInterrupt
                with mock.patch.object(freshness.subprocess, "CompletedProcess", side_effect=result_record), \
                        mock.patch.object(freshness.subprocess, "Popen", side_effect=ready_owner), \
                        mock.patch.object(freshness.native_serial.time, "monotonic", side_effect=lambda: clock[0]), \
                        self.assertRaises(expected):
                    freshness.run_seed_command([sys.executable, str(program), str(marker), str(ready)],
                                               env=dict(os.environ), timeout=120)
                self.assertEqual(marker.read_text(), "cleaned")

    def test_standalone_materialized_cli_routes_through_normal_gate_without_grant(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = write_seed(root / "build/host/stage0/bin/rustc", PIN)
            stage0 = {"compiler_git_commit_hash": PIN, "compiler_date": "2026-07-13",
                      "compiler_version": "1.99.0-trust"}
            (binary.parent.parent / ".rustc-stamp").write_text(freshness.stage0_extraction_stamp(stage0))
            environment = dict(os.environ)
            environment.pop("BUILD_SLOT_HELD", None)
            class Reentered(Exception):
                pass
            with mock.patch.dict(os.environ, environment, clear=True), \
                    mock.patch.object(freshness, "ROOT", root), \
                    mock.patch.object(freshness, "__name__", "__main__"), \
                    mock.patch.object(sys, "argv", [str(SCRIPT), "--require-payloads"]), \
                    mock.patch.object(freshness.os, "execv", side_effect=Reentered) as execute:
                with self.assertRaises(Reentered):
                    freshness.probe_materialized_stage0(stage0)
                execute.assert_called_once_with(str(root / "scripts/build-slot"),
                    [str(root / "scripts/build-slot"), "--", sys.executable,
                     str(SCRIPT), "--require-payloads"])
                self.assertNotIn("BUILD_SLOT_HELD", os.environ)

    def test_unavailable_is_two_but_known_seed_and_payload_failures_remain_one(self):
        import contextlib
        import io
        stage0 = {"compiler_version": "1.99.0-trust", "compiler_date": "2026-07-13",
                  "compiler_git_commit_hash": PIN}
        for known, payload, expected in ((False, False, 2), (True, False, 1), (False, True, 1)):
            errors = [freshness.ProbeUnavailable("resource unavailable")]
            if known:
                errors.append("commit-hash mismatch")
            with self.subTest(known=known, payload=payload), contextlib.ExitStack() as stack:
                stack.enter_context(mock.patch.dict(os.environ, BUILD_SLOT_HELD="1"))
                stack.enter_context(mock.patch.object(sys, "argv", [str(SCRIPT), "--require-payloads"]))
                stack.enter_context(mock.patch.object(freshness, "read_source_version", return_value=(1, 99)))
                stack.enter_context(mock.patch.object(freshness, "read_stage0", return_value=stage0))
                stack.enter_context(mock.patch.object(freshness, "validate_stage0_metadata", return_value=[]))
                stack.enter_context(mock.patch.object(freshness, "probe_materialized_stage0", return_value=(errors, [])))
                stack.enter_context(mock.patch.object(freshness, "probe_configured_seed", return_value=([], [])))
                stack.enter_context(mock.patch.object(freshness, "validate_materialized_payloads",
                                                     return_value=["missing payload"] if payload else []))
                stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
                self.assertEqual(freshness.main(), expected)

    def test_known_identity_failure_stops_before_later_unavailability(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = write_seed(Path(tmp) / "rustc", OTHER)
            with mock.patch.object(freshness.native_serial, "managed_serial_executor",
                                   side_effect=RuntimeError("admission unavailable")) as owner:
                errors, _ = freshness.probe_seed_binary(binary, "fixture", {
                    "compiler_git_commit_hash": PIN, "compiler_date": "2026-07-13",
                    "compiler_version": "1.99.0-trust"})
            self.assertTrue(any(not isinstance(error, freshness.ProbeUnavailable) for error in errors))
            self.assertFalse(any(isinstance(error, freshness.ProbeUnavailable) for error in errors))
            owner.assert_not_called()


if __name__ == "__main__":
    unittest.main()
