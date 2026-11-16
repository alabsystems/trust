#!/usr/bin/env python3
"""Producer custody controls with inert subprocesses; no native build credit."""

from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_os.execv(_floor_path, [_floor_path, "-I", "-S", "-B", _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]])
    _floor_sys.exit("linux_root_producer_test.py requires Python 3.11+ (tomllib); none found on PATH")

import fcntl
import ast
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tarfile
import time
import tomllib
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts import produce_linux_root_seed as producer


class ProducerControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def runner(self):
        args = mock.Mock(source_root=self.root)
        owner = {"host": "aarch64-unknown-linux-gnu", "deadline_monotonic": time.monotonic() + 30}
        with mock.patch.object(producer.auth, "git", return_value="1"):
            return producer.Producer(args, self.root, owner)

    def test_finite_systemd_caps_and_malformed_values(self):
        for raw, seconds in (("6h", 21600), ("1h 30min", 5400), ("30s", 30), ("500ms", .5), ("2us", .000002)):
            with self.subTest(raw=raw):
                self.assertEqual(producer.duration_seconds(raw), seconds)
        for raw in ("infinity", "max", "NaN", "-1s", "0s", "1e20s", "1hgarbage", "1h  2s", "1h\n2s"):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                producer.duration_seconds(raw)

    def test_expired_or_extended_original_owner_refused_before_native_work(self):
        base = {"schema": "trust.linux-root-producer-owner.v2", "host": "aarch64-unknown-linux-gnu"}
        for started, deadline in ((1, 2), (time.monotonic(), time.monotonic() + 90000),
                                  (float("nan"), float("inf")), (time.monotonic() + 20, time.monotonic() + 40)):
            with self.subTest(started=started), self.assertRaises(ValueError):
                producer.owner_binding({**base, "started_monotonic": started, "deadline_monotonic": deadline}, base["host"])

    def test_final_capture_cannot_pass_after_original_deadline(self):
        runner = self.runner()
        original = runner.owner["deadline_monotonic"]
        with mock.patch.object(producer, "owner_binding", return_value=runner.owner):
            self.assertLess(runner.completion_time(), original)
            runner.owner["deadline_monotonic"] = time.monotonic() - 1
            with self.assertRaisesRegex(ValueError, "deadline exhausted"):
                runner.completion_time()
        runner.owner["deadline_monotonic"] = original
        with mock.patch.object(runner, "remaining", return_value=1), \
                mock.patch.object(producer.time, "monotonic", return_value=original):
            with self.assertRaisesRegex(ValueError, "deadline exhausted during final capture"):
                runner.completion_time()

    def test_actual_nonisolated_entrypoint_refuses_before_authenticating_owner(self):
        arguments = []
        for name in ("source-root", "std-source-archive", "config", "cargo-home", "work-dir", "owner",
                     "genesis-manifest", "genesis-archives", "genesis-sysroot", "ddc-manifest", "ddc-archives", "ddc-sysroot",
                     "legacy-receipt", "legacy-archives", "legacy-manifest"):
            arguments.extend(["--" + name, str(self.root)])
        result = subprocess.run([sys.executable, "-B", str(ROOT / "scripts/produce_linux_root_seed.py"), *arguments],
                                capture_output=True, text=True, timeout=10, check=False)
        self.assertEqual(result.returncode, 1)
        self.assertIn("Python -I -S -B isolation", result.stderr)
        self.assertEqual(list(self.root.iterdir()), [])

    def test_floor_selection_keeps_native_driver_isolation_and_arguments(self):
        class Reexecuted(Exception):
            pass
        for relative in ("scripts/produce_linux_root_seed.py", "scripts/initialize_linux_root_seed.py",
                         "scripts/tests/linux_root_producer_test.py"):
            path = ROOT / relative
            tree = ast.parse(path.read_text())
            floor_index = next(i for i, node in enumerate(tree.body) if isinstance(node, ast.If))
            prefix = ast.Module(body=tree.body[:floor_index + 1], type_ignores=[])
            with self.subTest(script=relative), mock.patch.object(sys, "version_info", (3, 9)), \
                    mock.patch.object(sys, "argv", [str(path), "--inert-argument"]), \
                    mock.patch.object(producer.shutil, "which", return_value="/inert/python3.12"), \
                    mock.patch.object(producer.os, "execv", side_effect=Reexecuted) as reexec:
                with self.assertRaises(Reexecuted):
                    exec(compile(prefix, str(path), "exec"), {"__name__": "__main__", "__file__": str(path)})
                reexec.assert_called_once_with("/inert/python3.12", ["/inert/python3.12", "-I", "-S", "-B",
                                                                     str(path), "--inert-argument"])

    def test_actual_inert_unpack_retains_exact_projection_and_rejects_changed_payload(self):
        stage2 = self.root / "stage2"
        for relative in ("bin/inert-tool", "lib/inert-library", "share/unpackaged-metadata"):
            path = stage2 / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"inert fixture, never executed")
        (stage2 / "bin/internal-link").symlink_to("../lib/inert-library")
        manifest = producer.support.stage2_manifest(stage2)
        archive = self.root / "native-fixture.tar.xz"
        with tarfile.open(archive, "w:xz") as bundle:
            for name in ("bin", "lib"):
                bundle.add(stage2 / name, arcname=name)
        installed = self.root / "installed"
        installed.mkdir()
        runner = self.runner()
        (self.root / "safe-bin").mkdir()
        (self.root / "safe-bin/xz").symlink_to("/usr/bin/xz")
        with mock.patch.object(runner, "remaining", return_value=10):
            runner.run("native-unpack", ["/usr/bin/tar", "--extract", "--xz", "--no-same-owner", "--same-permissions",
                                        "--file", str(archive), "--directory", str(installed)])
        actual = producer.recheck_native_installation(manifest, installed)
        self.assertFalse(any(row["path"].startswith("share/") for row in actual["records"]))
        self.assertEqual((installed / "bin/internal-link").readlink().as_posix(), "../lib/inert-library")
        (installed / "bin/inert-tool").write_bytes(b"changed extracted payload")
        with self.assertRaisesRegex(ValueError, "differs from its authenticated payload tree"):
            producer.recheck_native_installation(manifest, installed)
        self.assertFalse((self.root / "CANDIDATE.json").exists())

    def test_actual_gnu_tar_omits_only_retained_source_snapshots(self):
        stage2 = self.root / "stage2"
        for relative in ("bin/inert-tool", "lib/runtime-library"):
            path = stage2 / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"inert; never executed")
        for prefix in producer.initialization.SOURCE_SNAPSHOTS:
            directory = stage2 / prefix
            directory.mkdir(parents=True)
            (directory / "rust").symlink_to(self.root, target_is_directory=True)
        manifest = producer.support.stage2_manifest(stage2)
        _, omitted = producer.initialization.native_projection(manifest, self.root)
        self.assertEqual(len(omitted), 4)
        runner = self.runner()
        (self.root / "safe-bin").mkdir()
        (self.root / "safe-bin/xz").symlink_to("/usr/bin/xz")
        archive = self.root / "native.tar.xz"
        installed = self.root / "installed"
        installed.mkdir()
        with mock.patch.object(runner, "remaining", return_value=10):
            runner.run("native-pack", ["/usr/bin/tar", "--create", "--xz", "--file", str(archive),
                        *("--exclude=" + p for p in producer.initialization.SOURCE_SNAPSHOTS),
                        "--directory", str(stage2), "bin", "lib"])
            runner.run("native-unpack", ["/usr/bin/tar", "--extract", "--xz", "--file", str(archive),
                                         "--directory", str(installed)])
        actual = producer.recheck_native_installation(manifest, installed)
        self.assertFalse(any(row["path"].startswith(producer.initialization.SOURCE_SNAPSHOTS) for row in actual["records"]))
        self.assertEqual((installed / "lib/runtime-library").read_bytes(), b"inert; never executed")

    def test_installer_inputs_are_selected_from_actual_prepared_pins(self):
        host, commit, version = "aarch64-unknown-linux-gnu", "6" * 40, "1.99.0"
        prepared = self.root / "prepared"
        dist = prepared / "bootstrap/trust-stage0/dist/2026-07-13"
        dist.mkdir(parents=True)
        pins = ["compiler_git_commit_hash=" + commit, "compiler_version=" + version + "-trust", "compiler_date=2026-07-13"]
        for component in producer.support.COMPONENTS:
            top = f"{component}-{version}-trust-{host}"
            archive = dist / (top + ".tar.xz")
            with tarfile.open(archive, "w:xz") as bundle:
                for name, body in (("install.sh", b"#!/bin/sh\nexit 125\n"), ("version", version.encode()),
                                   ("git-commit-hash", commit.encode()), (component + "/inert", b"prepared fixture only")):
                    row = tarfile.TarInfo(top + "/" + name)
                    row.mode, row.size = 0o755 if name == "install.sh" else 0o644, len(body)
                    bundle.addfile(row, io.BytesIO(body))
            pins.append("dist/2026-07-13/" + archive.name + "=" + hashlib.sha256(archive.read_bytes()).hexdigest())
        (prepared / "src-stage0").write_text("\n".join(pins) + "\n")
        positive = self.root / "positive"
        positive.mkdir()
        artifacts = producer.prepared_artifacts(prepared, positive, version, host, commit)
        self.assertEqual(len(artifacts["artifacts"]), 5)
        self.assertTrue(all(row["installer_sha256"] == hashlib.sha256(b"#!/bin/sh\nexit 125\n").hexdigest()
                            for row in artifacts["artifacts"]))
        # A checksum of a different raw dist cannot authorize this selected input.
        (prepared / "src-stage0").write_text("\n".join([*pins[:-1], pins[-1].split("=")[0] + "=" + "f" * 64]) + "\n")
        negative = self.root / "negative"
        negative.mkdir()
        with self.assertRaisesRegex(ValueError, "differs from its canonical pin"):
            producer.prepared_artifacts(prepared, negative, version, host, commit)
        self.assertFalse((negative / "canonical-seed-installation-inputs.json").exists())

    def test_four_inert_leases_cannot_substitute_for_global_lease(self):
        files, rows = [], []
        for name in ("host", "target", "cargo", "source"):
            fd = os.open(self.root / name, os.O_RDWR | os.O_CREAT | os.O_EXCL, 0o600)
            self.addCleanup(os.close, fd)
            files.append(fd)
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            info = os.fstat(fd)
            rows.append({"path": str(self.root / name), "fd": fd, "device": info.st_dev, "inode": info.st_ino, "role": name})
        owner = {"lease_owner_pid": os.getpid(), "lease_owner_start_ticks": producer.linux.stat_identity(os.getpid())[1],
                 "leases": rows}
        with self.assertRaisesRegex(ValueError, "machine-wide"):
            producer.held_leases(owner)
        rows[0]["inode"] += 1
        with self.assertRaisesRegex(ValueError, "original held regular"):
            producer.held_leases(owner)

    def test_no_inherited_build_overrides(self):
        with mock.patch.dict(os.environ, {"RUSTFLAGS": "injected", "CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER": "injected",
                                          "LD_PRELOAD": "injected", "CC": "injected", "PYTHONPATH": "injected"}):
            runner = self.runner()
        self.assertFalse(set(runner.env) & {"RUSTFLAGS", "CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER", "LD_PRELOAD", "CC", "PYTHONPATH"})
        self.assertEqual(runner.env["CARGO_BUILD_JOBS"], "1")
        self.assertEqual(runner.env["CARGO_NET_OFFLINE"], "true")
        self.assertEqual(runner.env["TRUST_SEED_STAIRCASE"], "1")

    def test_same_driver_and_path_with_explicit_external_only_compiler(self):
        base = self.root / "base.toml"
        base.write_text('profile = "compiler"\n')
        for role, compiler in (("self-host", "/candidate/bin/trustc"), ("ddc", "/external/bin/rustc")):
            config = self.root / (role + ".toml")
            producer.phase_config(base, config, Path(compiler), Path("/candidate/bin/cargo"), Path("/role/bin/trustdoc"))
            document = tomllib.loads(config.read_text())
            self.assertEqual(document["build"]["cargo"], "/candidate/bin/cargo")
            self.assertEqual(document["build"]["rustc"], compiler)
            self.assertFalse(document["rust"]["download-rustc"])
            argv = producer.xpy(self.root, config, self.root / "same-comparison", "aarch64-unknown-linux-gnu", "build", "compiler/rustc", "library/std")
            self.assertEqual(argv[argv.index("--build-dir") + 1], str(self.root / "same-comparison"))
            self.assertEqual(argv[-2:], ["compiler/rustc", "library/std"])

    def test_candidate_requests_the_authenticated_trustfmt_source_path(self):
        for path in ("src/tools/targo", "src/tools/trustdoc", "src/tools/trustfmt"):
            target = self.root / path / "Cargo.toml"
            target.parent.mkdir(parents=True)
            target.write_text("# inert producer-path fixture\n")
        self.assertEqual(producer.external_candidate_tools(self.root),
                         ("src/tools/targo", "src/tools/trustdoc", "src/tools/trustfmt"))
        (self.root / "src/tools/trustfmt/Cargo.toml").unlink()
        with self.assertRaisesRegex(ValueError, "lacks a native candidate tool producer"):
            producer.external_candidate_tools(self.root)

    def test_actual_private_dependency_source_tamper_refused(self):
        runner = self.runner()
        dependency = self.root / "cargo-home/registry/src/inert/source.rs"
        dependency.parent.mkdir(parents=True)
        dependency.write_text("inert fixture only")
        runner.bind_cache_sources("before")
        dependency.write_text("changed")
        with self.assertRaisesRegex(ValueError, "dependency source changed"):
            runner.bind_cache_sources("after")

    def test_real_same_path_staging_restores_self_host_and_retains_ddc(self):
        comparison = self.root / "comparison-build"
        comparison.mkdir()
        (comparison / "inert-compiler").write_bytes(b"self-host fixture")
        external_llvm = self.root / "external-llvm"
        external_llvm.mkdir()
        (external_llvm / "inert-library").write_bytes(b"common LLVM fixture")
        producer.stage_comparison(self.root)
        self.assertFalse(comparison.exists())
        comparison.mkdir()
        (comparison / "inert-compiler").write_bytes(b"ddc fixture")
        producer.restore_comparison(self.root)
        self.assertEqual((comparison / "inert-compiler").read_bytes(), b"self-host fixture")
        self.assertEqual((self.root / "comparison-ddc/inert-compiler").read_bytes(), b"ddc fixture")
        self.assertEqual((external_llvm / "inert-library").read_bytes(), b"common LLVM fixture")
        producer.stage_comparison(self.root)
        comparison.mkdir()
        (comparison / "inert-compiler").write_bytes(b"archive rebuild fixture")
        producer.restore_comparison(self.root, "comparison-archive-rebuild")
        self.assertEqual((comparison / "inert-compiler").read_bytes(), b"self-host fixture")
        self.assertEqual((self.root / "comparison-archive-rebuild/inert-compiler").read_bytes(), b"archive rebuild fixture")
        self.assertEqual((self.root / "comparison-ddc/inert-compiler").read_bytes(), b"ddc fixture")

    def test_staging_refuses_preexisting_or_symlink_output_without_mutation(self):
        comparison, retained = self.root / "comparison-build", self.root / "comparison-self-host"
        comparison.mkdir()
        (comparison / "inert-compiler").write_bytes(b"self-host fixture")
        retained.mkdir()
        with self.assertRaises(ValueError):
            producer.stage_comparison(self.root)
        retained.rmdir()
        retained.symlink_to(comparison, target_is_directory=True)
        with self.assertRaises(ValueError):
            producer.stage_comparison(self.root)
        self.assertEqual((comparison / "inert-compiler").read_bytes(), b"self-host fixture")

    def test_inert_success_and_real_failure_record_actual_commands_and_status(self):
        runner = self.runner()
        with mock.patch.object(producer, "owner_binding", return_value=runner.owner), mock.patch.object(runner, "remaining", return_value=10):
            runner.run("candidate-targo", [sys.executable, "-I", "-S", "-c", "print('inert subprocess control')"])
            with self.assertRaisesRegex(ValueError, "failed with status 7"):
                runner.run("external-bootstrap", [sys.executable, "-I", "-S", "-c", "raise SystemExit(7)"])
        events = [json.loads((self.root / f"phase-{i:02d}.json").read_text()) for i in (1, 2)]
        self.assertEqual([event["returncode"] for event in events], [0, 7])
        self.assertTrue(all(event["deadline_monotonic"] == runner.owner["deadline_monotonic"] for event in events))
        self.assertFalse((self.root / "CANDIDATE.json").exists())

    def test_actual_inert_timeout_has_no_success_status_or_fresh_budget(self):
        runner = self.runner()
        with mock.patch.object(runner, "remaining", return_value=.02), self.assertRaises(subprocess.TimeoutExpired):
            runner.run("external-bootstrap", [sys.executable, "-I", "-S", "-c", "import time; time.sleep(1)"])
        event = json.loads((self.root / "phase-01.json").read_text())
        self.assertNotIn("returncode", event)
        self.assertEqual(event["deadline_monotonic"], runner.owner["deadline_monotonic"])

    def test_rejected_existing_work_is_never_written(self):
        arguments = ["--" + name for name in ()]
        for name in ("source-root", "std-source-archive", "config", "cargo-home", "work-dir", "owner",
                     "genesis-manifest", "genesis-archives", "genesis-sysroot", "ddc-manifest", "ddc-archives", "ddc-sysroot",
                     "legacy-receipt", "legacy-archives", "legacy-manifest"):
            arguments.extend(["--" + name, str(self.root)])
        with mock.patch.object(producer.support, "native_host", return_value="aarch64-unknown-linux-gnu"), \
                mock.patch.object(producer.sys, "flags", mock.Mock(isolated=1, no_site=1, dont_write_bytecode=1)), \
                mock.patch.object(producer.auth.ledger, "read_proof_file", return_value=b"{}"), \
                mock.patch.object(producer, "owner_binding", return_value={"host": "aarch64-unknown-linux-gnu",
                                                                          "cargo_home": str(self.root), "work_dir": str(self.root)}):
            self.assertEqual(producer.main(arguments), 1)
        self.assertEqual(list(self.root.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
