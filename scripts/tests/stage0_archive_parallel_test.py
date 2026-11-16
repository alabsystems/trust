#!/usr/bin/env python3
"""Small real archive controls; no compiler, public dist or large benchmark."""
from __future__ import annotations

import copy
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tarfile
import tempfile
import threading
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("parallel_stage0_prepare", ROOT / "src/tools/trust-stage0-dist/prepare.py")
prepare = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = prepare
SPEC.loader.exec_module(prepare)
HOSTS = ("aarch64-apple-darwin", "x86_64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class Archives(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.inputs = self.root / "inputs"
        self.inputs.mkdir()

    def fixture(self, count=4, *, conflicting_alias=False, formats=("xz",)):
        manifest = {"date": "2026-11-07", "pkg": {p: {"version": "0.13.0-trust"} for p in prepare.REQUIRED_MANIFEST_PACKAGES}}
        targets = manifest["pkg"]["targo"]["target"] = {}
        for index, host in enumerate(HOSTS[:count]):
            target = targets[host] = {"available": True}
            for fmt in formats:
                name = f"targo-0.13.0-trust-{host}.tar.{fmt}"
                prefix = prepare.tarball_prefix(name)
                path = self.inputs / name
                with tarfile.open(path, "w:" + fmt) as archive:
                    for leaf in ("targo", "cargo"):
                        data = (f"archive-{index}\n".encode() * 1024)
                        if conflicting_alias and index == 0 and leaf == "cargo":
                            data = b"conflicting inherited executable"
                        member = tarfile.TarInfo(prefix + "/targo/bin/" + leaf)
                        member.size = len(data)
                        member.mode = 0o755
                        archive.addfile(member, io.BytesIO(data))
                url, key = ("xz_url", "xz_hash") if fmt == "xz" else ("url", "hash")
                target.update({url: "https://fixture.invalid/" + name, key: digest(path)})
        return manifest

    def rewrite(self, manifest, output, jobs=1, archive_format="xz"):
        output.mkdir(exist_ok=True)
        prepare.rewrite_manifest(manifest, input_dist=self.inputs, output_date_dir=output,
                                 date="2026-11-07", dist_server="file://fixture", source_channel="trust",
                                 owned_channel="trust", archive_format=archive_format, jobs=jobs)

    def test_real_xz_and_gzip_parity_and_two_worker_bound(self):
        with mock.patch("time.time", return_value=1234567890):
            original = self.fixture(formats=("xz", "gz"))
            serial, parallel = copy.deepcopy(original), copy.deepcopy(original)
            self.rewrite(serial, self.root / "serial", archive_format="both")
            real = prepare.repack_owned_tarball
            lock = threading.Lock()
            barrier = threading.Barrier(2)
            active = peak = started = 0

            def observed(*args, **kwargs):
                nonlocal active, peak, started
                with lock:
                    active += 1
                    started += 1
                    current = started
                    peak = max(peak, active)
                try:
                    if current <= 2:
                        barrier.wait(timeout=5)
                    return real(*args, **kwargs)
                finally:
                    with lock:
                        active -= 1

            with mock.patch.object(prepare, "repack_owned_tarball", side_effect=observed):
                self.rewrite(parallel, self.root / "parallel", jobs=2, archive_format="both")
        self.assertEqual(peak, 2)
        self.assertEqual(started, 8)
        self.assertEqual(serial, parallel)
        for left in (self.root / "serial").iterdir():
            right = self.root / "parallel" / left.name
            self.assertEqual(left.read_bytes(), right.read_bytes())
            with tarfile.open(right) as archive:
                self.assertEqual(len(archive.getnames()), 2)
                self.assertTrue(all(m.isfile() and m.mode == 0o755 for m in archive.getmembers()))

    def test_identical_destination_references_keep_serial_behavior(self):
        manifest = self.fixture(count=1)
        targets = manifest["pkg"]["targo"]["target"]
        targets[HOSTS[1]] = copy.deepcopy(targets[HOSTS[0]])
        with mock.patch.object(prepare, "ThreadPoolExecutor", side_effect=AssertionError("Aliased outputs ran concurrently")):
            self.rewrite(manifest, self.root / "serial-alias", jobs=4)
        self.assertEqual(len(list((self.root / "serial-alias").iterdir())), 1)
        self.assertEqual(targets[HOSTS[0]], targets[HOSTS[1]])

    def test_shared_target_object_keeps_serial_behavior(self):
        manifest = self.fixture(count=1)
        targets = manifest["pkg"]["targo"]["target"]
        targets[HOSTS[1]] = targets[HOSTS[0]]
        with mock.patch.object(prepare, "ThreadPoolExecutor", side_effect=AssertionError("Shared dict raced")):
            self.rewrite(manifest, self.root / "shared-target", jobs=4)

    def test_conflicting_physical_destinations_refuse_before_workers(self):
        for kind in ("symlink", "hardlink"):
            with self.subTest(kind=kind):
                manifest = self.fixture(count=2)
                output = self.root / kind
                output.mkdir()
                names = [Path(row["xz_url"]).name for row in manifest["pkg"]["targo"]["target"].values()]
                if kind == "symlink":
                    (output / names[0]).symlink_to(output / names[1])
                else:
                    (output / names[0]).write_bytes(b"existing output")
                    os.link(output / names[0], output / names[1])
                sources = {p: digest(p) for p in self.inputs.iterdir()}
                with mock.patch.object(prepare, "ThreadPoolExecutor", side_effect=AssertionError("Conflicting workers started")):
                    with self.assertRaisesRegex(ValueError, "conflicting archive producers"):
                        self.rewrite(manifest, output, jobs=2)
                if kind == "symlink":
                    self.assertFalse((output / names[1]).exists())
                else:
                    self.assertEqual((output / names[0]).read_bytes(), b"existing output")
                self.assertEqual(sources, {p: digest(p) for p in self.inputs.iterdir()})

    def test_source_alias_refuses_without_truncating_input(self):
        manifest = self.fixture(count=1)
        sources = {p: digest(p) for p in self.inputs.iterdir()}
        with self.assertRaisesRegex(ValueError, "aliases its source"):
            self.rewrite(manifest, self.inputs, jobs=2)
        self.assertEqual(sources, {p: digest(p) for p in self.inputs.iterdir()})

    def test_destination_aliasing_another_selected_input_refuses_before_writers(self):
        for jobs in (1, 2):
            with self.subTest(jobs=jobs):
                manifest = self.fixture(count=2)
                output = self.root / f"cross-input-{jobs}"
                output.mkdir()
                names = [Path(row["xz_url"]).name for row in manifest["pkg"]["targo"]["target"].values()]
                os.link(self.inputs / names[1], output / names[0])
                sources = {p: digest(p) for p in self.inputs.iterdir()}
                with mock.patch.object(prepare, "repack_owned_tarball", side_effect=AssertionError("Input alias reached a writer")):
                    with self.assertRaisesRegex(ValueError, "aliases a selected input"):
                        self.rewrite(manifest, output, jobs=jobs)
                self.assertEqual(sources, {p: digest(p) for p in self.inputs.iterdir()})
                self.assertEqual(list(output.iterdir()), [output / names[0]])
                self.assertEqual(digest(output / names[0]), sources[self.inputs / names[1]])

    def test_checksum_refusal_precedes_workers(self):
        manifest = self.fixture(count=2)
        manifest["pkg"]["targo"]["target"][HOSTS[0]]["xz_hash"] = "0" * 64
        with mock.patch.object(prepare, "ThreadPoolExecutor", side_effect=AssertionError("Unchecked workers started")):
            with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                self.rewrite(manifest, self.root / "bad-checksum", jobs=2)
        self.assertEqual(list((self.root / "bad-checksum").iterdir()), [])

    def test_worker_retains_conflicting_member_refusal(self):
        manifest = self.fixture(count=2, conflicting_alias=True)
        sources = {p: digest(p) for p in self.inputs.iterdir()}
        with self.assertRaisesRegex(ValueError, "conflicting archive members"):
            self.rewrite(manifest, self.root / "worker-refusal", jobs=2)
        self.assertEqual(sources, {p: digest(p) for p in self.inputs.iterdir()})

    def test_jobs_default_and_invalid_counts(self):
        self.assertEqual(prepare.parse_args([]).jobs, 1)
        self.assertEqual(prepare.parse_args(["--jobs", "2"]).jobs, 2)
        for value in ("0", "-1", "not-an-integer"):
            with self.subTest(value=value), mock.patch("sys.stderr", io.StringIO()), self.assertRaises(SystemExit):
                prepare.parse_args(["--jobs", value])
        for value in (0, -1, True):
            with self.assertRaisesRegex(ValueError, "positive integer"):
                self.rewrite(self.fixture(count=1), self.root / "bad-jobs", jobs=value)

    def test_actual_mint_prepare_command_carries_admitted_jobs(self):
        text = (ROOT / "scripts/mint_and_prove_seed.sh").read_text()
        command = 'run_clean "$SAFE_BIN" repin \\\n' + text.split('run_clean "$SAFE_BIN" repin \\\n', 1)[1].split('REPIN_LINE=', 1)[0]
        for jobs in ([], ["--jobs", "2"]):
            prefix = (f"PYTHON_BIN={shlex.quote(sys.executable)}\nROOT='/source with spaces'\n"
                      "SAFE_BIN=/safe\nDIST=/dist\nCOMMIT=fixture\nCOMMIT_DATE=2026-11-07\n"
                      "PIN_DIST_SERVER=file://fixture\nPREPARED='/prepared with spaces'\n"
                      "BUILD_JOB_ARGS=(" + " ".join(map(shlex.quote, jobs)) + ")\n"
                      "run_clean() { shift 2; \"$PYTHON_BIN\" -I -B -c "
                      "'import json,sys;print(json.dumps(sys.argv[1:]))' \"$@\"; }\n")
            result = subprocess.run(["/bin/bash", "-eu", "-c", prefix + command], capture_output=True, text=True, check=True)
            argv = json.loads(result.stdout)
            self.assertEqual(argv[1], "-I")
            parsed = prepare.parse_args(argv[3:])
            self.assertEqual(parsed.jobs, 2 if jobs else 1)
            self.assertEqual(argv.count("--jobs"), bool(jobs))


if __name__ == "__main__":
    unittest.main()
