#!/usr/bin/env python3
"""Exercise orchestration with real temporary Git histories and fake pipeline owners."""
import importlib.util
import hashlib
import json
import shlex
import os
from pathlib import Path
import plistlib
import runpy
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import types
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "daily_toolchain_stage.py"
SPEC = importlib.util.spec_from_file_location("daily_toolchain_stage", SCRIPT)
stage = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(stage)
LIBRARY_SCRIPT = SCRIPT.with_name("verify_sysroot_libraries.py")
LIBRARY_SPEC = importlib.util.spec_from_file_location("verify_sysroot_libraries", LIBRARY_SCRIPT)
libraries = importlib.util.module_from_spec(LIBRARY_SPEC)
LIBRARY_SPEC.loader.exec_module(libraries)
HOST = "aarch64-apple-darwin"
OUTCOME_OWNER = SCRIPT.parents[1] / "scripts/tests/fixtures/publication_daily_consumer_outcomes.py"


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True,
                                   stderr=subprocess.DEVNULL).strip()


def executable(path, text="#!/bin/sh\nexit 0\n"):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    path.chmod(0o755)


def toolchain(path):
    executable(path / "bin/trustc")
    executable(path / "bin/targo")
    (path / "lib").mkdir()
    (path / "lib/libstd.rlib").write_bytes(b"std")


class SysrootLibrarySurfaceTests(unittest.TestCase):
    # Independent contract expectation from library/sysroot and std's closure;
    # removing a production requirement must not remove its test fixture too.
    REQUIRED = ("core", "alloc", "std", "compiler_builtins", "test", "proc_macro", "trust_bignum")

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.host = self.complete(HOST)

    def complete(self, target):
        lib = self.root / "lib/rustlib" / target / "lib"
        lib.mkdir(parents=True)
        for crate in self.REQUIRED:
            (lib / f"lib{crate}-fixture.rlib").write_bytes(b"structural fixture; not Rust metadata")
        return lib

    def check(self, *targets):
        return libraries.inspect(self.root, targets or (HOST,))

    def test_complete_host_and_discovered_cross_target(self):
        self.complete("x86_64-apple-darwin")
        result = self.check()
        self.assertEqual(result["errors"], [])
        self.assertEqual(set(result["targets"]), {HOST, "x86_64-apple-darwin"})
        self.assertTrue(all(t["full_library_required"] for t in result["targets"].values()))
        self.assertFalse(result["semantic_qualification"])

    def test_every_required_rlib_is_required_on_each_full_target(self):
        cross = self.complete("x86_64-apple-darwin")
        for lib in (self.host, cross):
            for crate in self.REQUIRED:
                with self.subTest(target=lib.parent.name, crate=crate):
                    path = lib / f"lib{crate}-fixture.rlib"
                    path.unlink()
                    self.assertTrue(any(f"missing {crate} rlib" in e
                                        for e in self.check(HOST, "x86_64-apple-darwin")["errors"]))
                    path.write_bytes(b"structural fixture; not Rust metadata")

    def test_metadata_and_empty_files_do_not_supply_a_required_rlib(self):
        path = self.host / "libproc_macro-fixture.rlib"
        path.unlink()
        (self.host / "libproc_macro-fixture.rmeta").write_bytes(b"metadata fixture")
        self.assertIn(f"{HOST}: missing proc_macro rlib", self.check()["errors"])
        path.touch()
        self.assertIn(f"{HOST}: invalid public library {path.name}", self.check()["errors"])

    def test_public_cohorts_are_checked_for_rlib_and_metadata(self):
        for crate in ("libc", "hashbrown", "std"):
            for suffix in ("rlib", "rmeta"):
                with self.subTest(crate=crate, suffix=suffix):
                    first = self.host / f"lib{crate}-fixture.rlib"
                    existed = first.exists()
                    if not existed:
                        first.write_bytes(b"standard-library dependency")
                    other = self.host / f"lib{crate}-compiler-helper.{suffix}"
                    other.write_bytes(b"different dependency cohort")
                    self.assertTrue(any(f"multiple public {crate} artifact cohorts" in e
                                        for e in self.check()["errors"]))
                    other.unlink()
                    if not existed:
                        first.unlink()
        for crate in ("std", "libc", "hashbrown"):
            for suffix in ("rlib", "rmeta"):
                for name in (f"lib{crate}.{suffix}", f"lib{crate}-.{suffix}",
                             f"lib{crate}-other\ncohort.{suffix}"):
                    with self.subTest(filename=name):
                        path = self.host / name
                        path.write_bytes(b"renamed public metadata candidate")
                        self.assertTrue(any("invalid public library filename" in e
                                            for e in self.check()["errors"]))
                        path.unlink()

    def test_same_cohort_metadata_and_private_helper_versions_are_accepted(self):
        (self.host / "libstd-fixture.rmeta").write_bytes(b"same artifact identity")
        (self.host / "liblibc-stdlib.rlib").write_bytes(b"public std dependency")
        private = self.host / "rustc-dependencies"
        private.mkdir()
        for identity in ("compiler-one", "compiler-two"):
            (private / f"liblibc-{identity}.rlib").write_bytes(b"private compiler helper")
        (self.host / "libstd_detect-unrelated.rlib").write_bytes(b"different crate family")
        self.assertEqual(self.check()["errors"], [])

    def test_required_artifacts_and_public_directories_must_be_real(self):
        path = self.host / "libcore-fixture.rlib"
        path.unlink()
        target = self.root / "elsewhere.rlib"
        target.write_bytes(b"outside library")
        path.symlink_to(target)
        self.assertIn(f"{HOST}: invalid public library {path.name}", self.check()["errors"])
        path.unlink()
        path.mkdir()
        self.assertIn(f"{HOST}: invalid public library {path.name}", self.check()["errors"])
        path.rmdir()
        moved = self.root / "moved"
        self.host.rename(moved)
        self.host.symlink_to(moved, target_is_directory=True)
        self.assertIn(f"{HOST}: missing or aliased public library directory", self.check()["errors"])

    def test_core_only_installed_target_is_not_misreported_as_a_full_std_target(self):
        lib = self.root / "lib/rustlib/thumbv7em-none-eabi/lib"
        lib.mkdir(parents=True)
        for helper_only in (False, True):
            with self.subTest(helper_only=helper_only):
                if helper_only:
                    (lib / "libcompiler_builtins-one.rlib").write_bytes(b"helper without core")
                self.assertIn("thumbv7em-none-eabi: missing core rlib", self.check()["errors"])
        (lib / "libcore-one.rlib").write_bytes(b"core-only fixture")
        result = self.check()
        self.assertEqual(result["errors"], [])
        self.assertFalse(result["targets"]["thumbv7em-none-eabi"]["full_library_required"])
        self.assertIn("thumbv7em-none-eabi: missing std rlib",
                      self.check(HOST, "thumbv7em-none-eabi")["errors"])

    def test_missing_declared_target_and_metadata_only_std_target_refuse(self):
        result = self.check(HOST, "x86_64-apple-darwin")
        self.assertIn("x86_64-apple-darwin: missing or aliased public library directory", result["errors"])
        lib = self.root / "lib/rustlib/x86_64-apple-darwin/lib"
        lib.mkdir(parents=True)
        for name in ("libstd-one.rmeta", "libstd.rmeta", "libstd-.rmeta", "libstd-other\ncohort.rmeta"):
            with self.subTest(filename=name):
                path = lib / name
                path.write_bytes(b"metadata alone")
                self.assertIn("x86_64-apple-darwin: missing std rlib", self.check()["errors"])
                path.unlink()

    def test_real_cli_reports_the_original_five_defect_shape(self):
        cross = self.complete("x86_64-apple-darwin")
        for crate in ("libc", "hashbrown"):
            for identity in ("stdlib", "compiler"):
                (self.host / f"lib{crate}-{identity}.rmeta").write_bytes(b"different cohort")
        for crate in ("test", "proc_macro", "trust_bignum"):
            (cross / f"lib{crate}-fixture.rlib").unlink()
        proc = subprocess.run([sys.executable, "-I", "-S", "-B", str(LIBRARY_SCRIPT),
                               "--sysroot", str(self.root), "--target", HOST],
                              capture_output=True, text=True)
        self.assertEqual(proc.returncode, 1, proc.stderr)
        report = json.loads(proc.stdout)
        self.assertEqual(len(report["errors"]), 5, report)
        self.assertFalse(report["semantic_qualification"])


class Owners:
    """Injection stays in tests; the CLI has no success/skip/stub override."""
    def __init__(self):
        self.calls = []
        self.fail = None
        self.timeouts = {}
        self.consumer_exits = {}
        self.interrupt = None
        self.consumer_hook = None
        self.consumer_outputs = {}

    def __call__(self, argv, cwd, env, log, timeout=None, *, cleanup_owner=None, cancel_event=None):
        if Path(argv[0]).name == "git":
            return stage.command(argv, cwd, env, log, cleanup_owner=cleanup_owner, cancel_event=cancel_event)
        if cancel_event is not None and cancel_event.is_set():
            raise InterruptedError("fixture cancelled")
        name = log.stem.split("-", 1)[1]
        self.calls.append((name, argv, dict(env)))
        self.timeouts[name] = int(argv[argv.index("_owned-command") + 3]) if "_owned-command" in argv else timeout
        log.write_text(json.dumps({"argv": argv, "cwd": str(cwd)}) + "\n")
        if name.endswith("-consumer-check") and self.consumer_hook:
            self.consumer_hook(name)
        if self.fail == name:
            raise stage.Refused(f"fake {name} failure; see {log}")
        if self.interrupt == name:
            raise InterruptedError("fixture interruption")
        if name.endswith("-consumer-check") and self.consumer_exits.get(name):
            log.write_text(log.read_text() + "same known-red baseline; no new failures\n")
            raise stage.CommandFailed("fake consumer command failed", self.consumer_exits[name])
        output = ""
        if name == "mint-version":
            output = "0.10.0"
        elif name == "clean-lean-inputs":
            home = Path(argv[argv.index("--elan-home") + 1])
            output = json.dumps({"schema": "trust.mint-clean-lean-inputs.v1",
                                 "library_path": str(home / "toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean"),
                                 "fingerprint": "fixture-source-bound-input"})
            if "--output" in argv:
                with Path(argv[argv.index("--output") + 1]).open("x") as receipt:
                    receipt.write(output + "\n")
                output = ""
        elif name == "native-host":
            output = HOST
        elif name == "pinned-bootstrap-config":
            (cwd / "bootstrap.toml").write_text("[build]\n")
        elif name == "pinned-bootstrap":
            toolchain(cwd / "build" / HOST / "stage2")
        elif name == "locked-dependency-prewarm":
            index = argv.index("_prewarm-dependencies")
            work, receipt = Path(argv[index + 2]), Path(argv[index + 4])
            seed = work / "seed"
            if not seed.exists():
                toolchain(seed)
            cache = work / "mint-inputs/fixture/cargo-home"
            cache.mkdir(parents=True, exist_ok=True)
            if not (work / "initial-cache.json").exists():
                stage.atomic_json(work / "initial-cache.json", {"source": "fixture"})
            stage.atomic_json(receipt, {"schema": "trust.bootstrap-offline-dependency-closure.v1",
                "config_policy": {"path": str(Path(argv[index + 6]) / "bin/pub-relock"),
                                  "sha256": stage.file_hash(Path(argv[index + 6]) / "bin/pub-relock")},
                "source_inputs_sha256": {str(cwd / "README"): stage.file_hash(cwd / "README")},
                "cargo_home": str(cache),
                "handoff_offline_replay": {"schema": "trust.bootstrap-offline-dependency-closure.v1",
                    "source_inputs_sha256": {str(cwd / "README"): stage.file_hash(cwd / "README")},
                    "completed_fetches": [{"manifest": "Cargo.toml", "offline": True}]},
                "completed_fetches": [{"manifest": "Cargo.toml", "offline": False},
                                      {"manifest": "Cargo.toml", "offline": True}],
                "cache_trees": {"registry/index": None, "registry/cache": None, "git/db": None}})
        elif name == "sanctioned-mint-and-double-compile":
            commit = git(cwd, "rev-parse", "HEAD")
            mint = cwd / f"build/pack-mint-0.10.0-{HOST}-{commit[:12]}"
            toolchain(mint / HOST / "stage2")
            dist = mint / "repin/bootstrap/trust-stage0/dist/2026-10-19"
            dist.mkdir(parents=True)
            (dist / "trustc.tar.xz").write_bytes(b"archive")
            branch = f"seed/repin-{commit[:12]}"
            git(cwd, "update-ref", f"refs/heads/{branch}", commit)
            (mint / "trust-seed-mint").write_text(
                f"source_commit={commit}\nhost={HOST}\nddc_verdict=identical\n"
                f"self_host_proof=pass\nrepin_commit={commit}\nrepin_branch={branch}\n"
                "ddc_seed_relation=same-lineage\nlineage_disjoint_anchor=none\n")
        elif name == "seal-without-admission":
            commit = git(cwd, "rev-parse", "HEAD")
            root = Path(env["TRUST_TOOLCHAIN_HOME"])
            root.mkdir(parents=True, exist_ok=True)
            shutil.copytree(Path(argv[-1]), root / f"trust-{commit[:8]}", symlinks=True)
            private = root / "rustc-private-sysroots"
            private.mkdir(exist_ok=True)
            (private / commit).write_bytes(b"private sysroot")
        elif name == "trust-wp-drivers":
            for name in stage.WP_BINS:
                executable(Path(env["CARGO_TARGET_DIR"]) / "release" / name)
        elif name.startswith("unsigned-"):
            output_dir = Path(argv[argv.index("--out") + 1])
            # atpkg-publish's plain pack appends the program; pack-bundle
            # writes its archive and manifest directly into the supplied out.
            if "pack" in argv:
                output_dir /= argv[argv.index("pack") + 1]
            output_dir.mkdir(parents=True)
            (output_dir / "pkg-fixture.toml").write_text("schema = 1\n")
            (output_dir / "fixture.tar.zst").write_bytes(b"package")
        elif name.endswith("-committed-policy"):
            return stage.command(argv, cwd, env, log, cleanup_owner=cleanup_owner, cancel_event=cancel_event)
        elif name.endswith("-scratch-trust-link"):
            link = Path(env["RUSTUP_HOME"]) / "toolchains/trust"
            link.parent.mkdir(parents=True, exist_ok=True)
            if not link.exists():
                link.symlink_to(argv[-1])
        elif name.endswith("-candidate-sysroot"):
            output = str((Path(env["RUSTUP_HOME"]) / "toolchains/trust").resolve())
        elif name.endswith("-genuine-targo"):
            output = "targo 0.10.0 fixture"
        elif name.endswith("-consumer-check"):
            output = self.consumer_outputs.get(
                name, "Gate: PASS [strict lane, exit 0] (1 proved, 0 failed, 1 total)")
        elif name.endswith("-cross-oracle-install"):
            oracle = argv[argv.index("install") + 1]
            root = Path(env["RUSTUP_HOME"]) / "toolchains" / oracle
            if not root.exists():
                toolchain(root)
        elif name.endswith("-cross-oracle-sysroot"):
            output = str(Path(env["RUSTUP_HOME"]) / "toolchains" / argv[argv.index("run") + 1])
        log.write_text(log.read_text() + output + "\n")
        if "_owned-command" in argv:
            result_file = Path(argv[argv.index("_owned-command") + 2])
            stage.atomic_json(result_file, {"exit_code": 0, "timed_out": False, "interrupted": False})
        return log.read_text()


class TrainOwners(Owners):
    """The train's owners: a real re-pin commit, and real pushes to the fixture's remote."""
    def __init__(self):
        super().__init__()
        self.push_exits = []

    def __call__(self, argv, cwd, env, log, timeout=None, *, cleanup_owner=None, cancel_event=None):
        result = super().__call__(argv, cwd, env, log, timeout, cleanup_owner=cleanup_owner, cancel_event=cancel_event)
        if Path(argv[0]).name == "git":
            return result
        name = log.stem.split("-", 1)[1]
        if name == "sanctioned-mint-and-double-compile":
            # The mint's re-pin: a child of the cut commit on seed/repin-<C>.
            commit = git(cwd, "rev-parse", "HEAD")
            repin = git(cwd, "-c", "user.name=mint", "-c", "user.email=mint@example.invalid",
                        "commit-tree", f"{commit}^{{tree}}", "-p", commit, "-m", "re-pin")
            git(cwd, "update-ref", f"refs/heads/seed/repin-{commit[:12]}", repin)
            receipt = cwd / f"build/pack-mint-0.10.0-{HOST}-{commit[:12]}/trust-seed-mint"
            receipt.write_text(receipt.read_text().replace(f"repin_commit={commit}", f"repin_commit={repin}"))
        elif name == "seed-archives-and-repin-branch":
            branch = "seed/repin-" + git(cwd, "rev-parse", "HEAD")[:12]
            git(cwd, "push", "-q", "origin", f"refs/heads/{branch}:refs/heads/{branch}")
        elif "-push-" in name:
            # scripts/prewarm_push.sh: merge main into the branch, then push it to main through the hook.
            git(cwd, "fetch", "-q", "origin", "refs/heads/main:refs/remotes/origin/main")
            git(cwd, "merge", "-q", "--no-edit", "refs/remotes/origin/main")
            code = self.push_exits.pop(0) if self.push_exits else 0
            if code:
                stage.atomic_json(Path(argv[argv.index("_owned-command") + 2]),
                                  {"exit_code": code, "timed_out": False, "interrupted": False})
            else:
                git(cwd, "push", "-q", "origin", "HEAD:refs/heads/main")
        elif name == "signed-pack-stage-upload":
            source = argv[argv.index("--trust-repo") + 1]
            commit = Path(argv[argv.index("--seal") + 1]).name.removeprefix("stage-trust-")
            build = git(source, "rev-list", "--count", commit)
            git(source, "push", "-q", "origin", f"{commit}:refs/tags/atpkg-trust-{build}")
        return result


class FakeGitHub:
    """What the train asks GitHub, answered by Git in the fixture's bare remote."""
    slug = "fixture/trust"

    def __init__(self, remote):
        self.remote = remote
        self.deleted = []

    def can_push(self):
        return True

    def main(self):
        return git(self.remote, "rev-parse", "refs/heads/main")

    def builds(self):
        return sorted(int(match[1]) for tag in git(self.remote, "tag", "-l").split()
                      if (match := stage.BUILD_TAG.fullmatch(tag)))

    def ahead(self, base):
        if subprocess.run(["git", "-C", str(self.remote), "merge-base", "--is-ancestor", base, "refs/heads/main"],
                          capture_output=True).returncode:
            return None
        return int(git(self.remote, "rev-list", "--count", f"{base}..refs/heads/main"))

    def delete_branch(self, branch, commit):
        if git(self.remote, "for-each-ref", "--format=%(objectname)", f"refs/heads/{branch}") != commit:
            raise stage.Refused("the branch moved or is gone")
        git(self.remote, "update-ref", "-d", f"refs/heads/{branch}")
        self.deleted.append(branch)


class JsonArtifactTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="daily-json-artifact-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.receipt = self.root / "receipt.json"

    def test_snapshot_keeps_existing_fingerprint_and_utf8_object_semantics(self):
        value = {"library_path": "/selected/lean", "unicode": "\u03bb"}
        self.receipt.write_text(json.dumps(value, ensure_ascii=False) + "\n", encoding="utf-8")
        self.receipt.chmod(0o640)
        parsed, identity = stage.read_json_artifact(self.receipt)
        self.assertEqual(parsed, value)
        self.assertEqual(identity, stage.fingerprint(self.receipt))
        for payload in (b"[]", b"{", b'{"library_path": "\xff"}', '{}'.encode('utf-16')):
            with self.subTest(payload=payload):
                self.receipt.write_bytes(payload)
                with self.assertRaises((stage.Refused, ValueError)):
                    stage.read_json_artifact(self.receipt)

    def test_snapshot_refuses_links_nonregular_and_oversize_inputs(self):
        self.receipt.write_text("{}")
        symlink = self.root / "symlink"
        symlink.symlink_to(self.receipt)
        directory = self.root / "directory"
        directory.mkdir()
        fifo = self.root / "fifo"
        os.mkfifo(fifo)
        oversize = self.root / "oversize"
        with oversize.open("wb") as stream:
            stream.truncate(8 * 1024 * 1024 + 1)
        for path in (self.root / "missing", symlink, directory, fifo, oversize):
            with self.subTest(path=path.name):
                with self.assertRaises(stage.Refused):
                    stage.read_json_artifact(path)

    def test_growth_during_snapshot_read_stays_bounded_and_refuses(self):
        self.receipt.write_text("{}")
        original = os.fdopen
        limits = []

        class GrowingReader:
            def __init__(reader, descriptor, mode):
                reader.stream = original(descriptor, mode)

            def __enter__(reader):
                return reader

            def __exit__(reader, *args):
                return reader.stream.__exit__(*args)

            def fileno(reader):
                return reader.stream.fileno()

            def read(reader, limit):
                limits.append(limit)
                with self.receipt.open("ab") as changed:
                    changed.write(b" " * (8 * 1024 * 1024))
                return reader.stream.read(limit)

        with mock.patch.object(stage.os, "fdopen", side_effect=GrowingReader):
            with self.assertRaisesRegex(stage.Refused, "changed while reading"):
                stage.read_json_artifact(self.receipt)
        self.assertEqual(limits, [8 * 1024 * 1024 + 1])

    def test_replacement_while_opening_refuses_original_descriptor_bytes(self):
        self.receipt.write_text('{"library_path": "/original"}')
        original = os.open

        def replaced_open(path, flags):
            descriptor = original(path, flags)
            replacement = self.root / "replacement"
            replacement.write_text('{"library_path": "/replacement"}')
            replacement.replace(self.receipt)
            return descriptor

        with mock.patch.object(stage.os, "open", side_effect=replaced_open):
            with self.assertRaisesRegex(stage.Refused, "changed while reading"):
                stage.read_json_artifact(self.receipt)


class ConsumerOutcomeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="daily-consumer-outcome-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.owner = self.root / "bin/pub"
        self.owner.parent.mkdir()
        self.owner.write_text(OUTCOME_OWNER.read_text() +
                              "\ndef terminate_process_group(process): pass\n")
        self.policy = {"reader_sha256": stage.file_hash(self.owner), "lane": "advisory"}
        self.log = self.root / "complete.log"
        self.step = {"log": str(self.log), "argv": ["/bin/sh", "-c", "fixture"],
                     "cwd": str(self.root), "status": "passed", "exit_code": 0}

    @staticmethod
    def banner(status="PASS", lane="advisory", code=0, counts="1 proved, 0 failed, 1 total"):
        return f"Gate: {status} [{lane} lane, exit {code}] ({counts})\n"

    def capture(self, output):
        self.log.write_bytes(json.dumps({"argv": self.step["argv"], "cwd": self.step["cwd"]}).encode()
                             + b"\n" + output.encode())
        self.step["log_identity"] = stage.fingerprint(self.log)

    def outcome(self):
        return stage.consumer_outcome(self.root, self.policy, self.step)

    def test_fifteen_actual_masked_shell_outcomes_use_publication_semantics(self):
        good = self.banner()
        nv = self.banner("COULD-NOT-RUN", code=3, counts="0 proved, 0 failed, 1 unknown, 1 total")
        cases = [
            ("pass", good, 0, True),
            ("conditional", self.banner("CONDITIONAL-PASS", counts="0 proved, 0 failed, 1 runtime-checked, 1 total"), 0, True),
            ("advisory-no-verdict", nv, 3, True),
            ("strict-no-verdict", self.banner("COULD-NOT-RUN", "strict", 3), 3, False),
            ("refuted-no-verdict", self.banner("COULD-NOT-RUN", code=3, counts="0 proved, 1 failed, 1 total"), 3, False),
            ("fail", self.banner("FAIL", code=3, counts="0 proved, 1 failed, 1 total"), 3, False),
            ("wrong-no-verdict-exit", self.banner("COULD-NOT-RUN", code=1), 3, False),
            ("unknown-status", self.banner("FUTURE-STATUS"), 3, False),
            ("stopped", nv + "targo trust: COULD NOT RUN: compiler did not finish\n", 3, False),
            ("ansi-stopped", nv + "\x1b[31mtargo trust: COULD NOT RUN: stopped\x1b[0m\n", 3, False),
            ("signal-death", nv + "process didn't exit successfully: `trustc test.rs` (signal: 9, SIGKILL)\n", 3, False),
            ("missing-census", "compiler exited without a report\n", 3, False),
            ("unaccounted", self.banner(counts="1 total"), 3, False),
            ("earlier-refutation", self.banner("FAIL", code=1, counts="0 proved, 1 failed, 1 total") + good, 3, False),
            ("multiple-successes", good + self.banner("CONDITIONAL-PASS"), 0, True),
        ]
        for name, output, code, accepted in cases:
            with self.subTest(name=name):
                inner = "printf '%s' " + shlex.quote(output) + f"; exit {code}"
                shell = "( /bin/sh -c " + shlex.quote(inner) + " || [ $? -eq 3 ] ) && /usr/bin/true"
                self.step["argv"] = ["/bin/sh", "-c", shell]
                stage.command(self.step["argv"], self.root, dict(os.environ), self.log, timeout=10)
                self.step["log_identity"] = stage.fingerprint(self.log)
                result = self.outcome()
                self.assertEqual(result["accepted"], accepted)
                self.assertEqual(result["log_sha256"], stage.file_hash(self.log))
                self.assertEqual(result["output_sha256"], hashlib.sha256(output.encode()).hexdigest())
                self.assertEqual(result["signal_death_count"], int(name == "signal-death"))

    def test_death_count_matches_owner_once_per_line_and_excludes_argv_header(self):
        death = "process didn't exit successfully: `trustc test.rs` (signal: 9)"
        self.step["argv"] = ["echo", death]
        self.capture(self.banner())
        self.assertEqual(self.outcome()["signal_death_count"], 0)
        self.capture(self.banner() + death + " " + death + "\n" + death + "\n")
        self.assertEqual(self.outcome()["signal_death_count"], 2)

    def test_zero_proved_unknown_and_empty_gate_are_not_new_refusals(self):
        for counts in ("0 proved, 0 failed, 1 unknown, 1 total", "0 proved, 0 failed, 0 total"):
            with self.subTest(counts=counts):
                self.capture(self.banner(counts=counts))
                self.assertTrue(self.outcome()["accepted"])

    def test_shell_nonzero_is_never_excused_by_a_passing_census(self):
        self.capture(self.banner())
        self.step["exit_code"] = 3
        with self.assertRaisesRegex(stage.Refused, "shell exit zero"):
            self.outcome()

    def test_shell_zero_requires_an_integer_exit_status(self):
        self.capture(self.banner())
        self.assertTrue(self.outcome()["accepted"])
        for value in (False, 0.0, None, "0", True, -9):
            with self.subTest(value=repr(value)):
                self.step["exit_code"] = value
                with self.assertRaisesRegex(stage.Refused, "shell exit zero"):
                    self.outcome()

    def test_output_missing_changed_truncated_or_linked_never_accepts(self):
        for change in ("missing", "changed", "truncated", "linked", "identity-absent"):
            with self.subTest(change=change):
                self.capture(self.banner())
                if change == "missing":
                    self.log.unlink()
                elif change == "changed":
                    self.log.write_text(self.log.read_text().replace("1 proved", "2 proved"))
                elif change == "truncated":
                    self.log.write_bytes(self.log.read_bytes()[:-1])
                elif change == "linked":
                    saved = self.root / "saved.log"
                    self.log.rename(saved)
                    self.log.symlink_to(saved)
                else:
                    self.step.pop("log_identity")
                with self.assertRaises(stage.Refused):
                    self.outcome()
                if self.log.is_symlink():
                    self.log.unlink()

    def test_unreadable_output_never_accepts(self):
        self.capture(self.banner())
        with mock.patch.object(Path, "read_bytes", side_effect=PermissionError("unreadable output")):
            with self.assertRaises(PermissionError):
                self.outcome()

    def test_command_header_is_required_even_when_log_hash_is_rebound(self):
        self.capture(self.banner())
        self.log.write_text('{"argv": []}\n' + self.banner())
        self.step["log_identity"] = stage.fingerprint(self.log)
        with self.assertRaisesRegex(stage.Refused, "exact command header"):
            self.outcome()

    def test_owner_identity_change_and_missing_api_never_accept(self):
        self.capture(self.banner())
        self.owner.write_text(self.owner.read_text() + "\n# new owner\n")
        with self.assertRaisesRegex(stage.Refused, "owner changed"):
            self.outcome()
        self.owner.write_text("def terminate_process_group(process): pass\n")
        self.policy["reader_sha256"] = stage.file_hash(self.owner)
        with self.assertRaisesRegex(stage.Refused, "outcome API"):
            self.outcome()

    def test_output_or_owner_mutation_during_validation_never_accepts(self):
        for changed in ("output", "owner"):
            with self.subTest(changed=changed):
                self.capture(self.banner())
                api = dict(stage.cleanup_api(self.root))
                original = api["parse_gate_census"]
                def mutate(text):
                    path = self.log if changed == "output" else self.owner
                    path.write_text(path.read_text() + "\n# changed during read\n")
                    return original(text)
                api["parse_gate_census"] = mutate
                with mock.patch.object(stage, "cleanup_api", return_value=api):
                    with self.assertRaisesRegex(stage.Refused, "changed during outcome"):
                        self.outcome()


class PrewarmBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="daily-fetch-boundary-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.source, self.work = self.root / "source", self.root / "work"
        self.work.mkdir()
        self.seed = self.work / "seed"
        toolchain(self.seed)
        self.trace = self.root / "fetch.jsonl"
        self.driver = self.seed / "bin/targo"
        executable(self.driver, "#!/bin/sh\n" + "'''exec' " + shlex.quote(sys.executable) + ' "$0" "$@" # ' + "'''\n" +
            "import json, os, pathlib, sys\n" +
            "if sys.argv[1:] == ['--unverified','--version']: print('targo fixture'); sys.exit(0)\n" +
            "if sys.argv[1:] == ['-Z','unstable-options','config','get','http.proxy','--format','json']: print(json.dumps({'http':{'proxy':os.environ['CARGO_HTTP_PROXY']}})); sys.exit(0)\n" +
            "if sys.argv[1:] == ['-Z','unstable-options','config','get','build.target-dir','--format','json']: print(json.dumps({'build':{'target-dir':os.environ['CARGO_TARGET_DIR']}})); sys.exit(0)\n" +
            "assert sys.argv[1:3] == ['fetch','--locked']\n" +
            "home=pathlib.Path(os.environ['CARGO_HOME']); archive=home/'registry/cache/archive'; extracted=home/'registry/src/extracted'\n" +
            "if '--offline' not in sys.argv:\n" +
            "    archive.parent.mkdir(parents=True,exist_ok=True); archive.write_text('locked')\n" +
            "    extracted.parent.mkdir(parents=True,exist_ok=True); extracted.write_text('locked')\n" +
            "else: assert archive.is_file() or extracted.is_file(), 'no archive; extracted source cannot mask the handoff'\n" +
            f"with open({str(self.trace)!r}, 'a') as f: f.write(json.dumps({{'argv':sys.argv,'env':dict(os.environ)}})+'\\n')\n")
        repo = SCRIPT.parents[1]
        self.closure = stage.runpy.run_path(str(repo / "scripts/bootstrap_dependency_closure.py"))
        graph_owner = self.source / "scripts/recreate_bootstrap.py"
        graph_owner.parent.mkdir(parents=True)
        shutil.copy2(repo / "scripts/recreate_bootstrap.py", graph_owner)
        identity_owner = self.source / "src/bootstrap/stage0_identity.py"
        identity_owner.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(repo / "src/bootstrap/stage0_identity.py", identity_owner)
        for relative in self.closure["_RECIPE_INPUTS"]:
            path = self.source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("")
        (self.source / self.closure["_RECIPE_INPUTS"][-1]).write_text(
            'fn ensure_default_verifier_tool_bins() { ToolBuild { path: "tool", } }\n'
            'fn ensure_user_facing_tools() { ToolBuild { path: "tool", } }\n')
        (self.source / "src/bootstrap/src/core/build_steps/vendor.rs").write_text(
            "pub fn default_paths_to_vendor(builder: &Builder<'_>) -> Vec<(PathBuf, Vec<&'static str>)> {\n"
            "let paths: Vec<(&str, Vec<&'static str>)> = vec![(\"dist-only/Cargo.toml\", vec![]),];\n"
            "paths.into_iter().map(|(path, submodules)| (builder.src.join(path), submodules)).collect() }")
        for relative in (*self.closure["_BASE_MANIFESTS"], "tool/Cargo.toml", "dist-only/Cargo.toml"):
            path = self.source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("[workspace]\nmembers = []\n")
            path.with_name("Cargo.lock").write_text("version = 4\n")
        self.pin = {"compiler_git_commit_hash": "a" * 40, "compiler_date": "2026-10-19"}
        self.compiler = {"commit": "a" * 40, "date": "2026-10-19", "host": HOST, "lineage": "trust"}
        self.staircase = {"read_stage0_pins": lambda _p: self.pin, "host_triple": lambda: HOST,
                          "pinned_seed_record": lambda *_a: {"pin": "exact-archive-fixture"},
                          "support_source_inputs": lambda: {},
                          "native_kind": lambda _p: "macho"}
        self.mint = {"foreign_load_commands": lambda *_a: {"checked": True},
                     "compiler_identity": lambda *_a: self.compiler,
                     "CARGO_HOME_INPUT_TREES": ("registry/index", "registry/cache", "git/db"),
                     "cargo_home_inputs": self.cache_input}
        self.recreator = stage.runpy.run_path(str(repo / "scripts/recreate_bootstrap.py"))
        self.recreator["_submodule_auth_config"] = lambda _p: self.fail("legacy gh selection is outside dependency acquisition")
        shutil.copy2(repo / "scripts/daily_dependency_git.py", self.source / "scripts/daily_dependency_git.py")
        shutil.copy2(repo / "scripts/daily_registry_proxy.py", self.source / "scripts/daily_registry_proxy.py")
        for name in ("scripts/seed_custody_source.py", "scripts/lib/seed_linux.py", "scripts/lib/seal_content_identity.py"):
            target = self.source / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(repo / name, target)
        for name in ("seed_staircase.py", "bootstrap_dependency_closure.py", "mint_seed_support.py"):
            path = self.source / "scripts" / name
            if not path.exists():
                path.write_text("# Explicit mocked owner fixture; no native/compiler claim.\n")
        self.recreator["_reject_local_git_execution_authority"] = lambda _p: None
        policy_source = PUBLICATION_OWNER / "bin/pub-relock"
        if not policy_source.is_file():
            self.skipTest("real fetch boundary requires publication's config policy reader")
        self.policy_engine = self.root / "policy"
        policy_file = self.policy_engine / "bin/pub-relock"
        policy_file.parent.mkdir(parents=True)
        shutil.copy2(policy_source, policy_file)
        policy = stage.runpy.run_path(str(policy_source))
        real_loader = stage.bound_dependency_owner
        def load(owner, path, name):
            fixtures = {"seed_staircase.py": self.staircase, "mint_seed_support.py": self.mint,
                        "bootstrap_dependency_closure.py": self.closure,
                        "pub-relock": policy, "recreate_bootstrap.py": self.recreator}
            if path.name in fixtures:
                return fixtures[path.name], stage.file_hash(path)
            return real_loader(owner, path, name)
        self.loader = mock.patch.object(stage, "bound_dependency_owner", side_effect=load)
        self.loader.start()
        self.addCleanup(self.loader.stop)

    def cache_input(self, source, destination):
        destination.mkdir()
        if source is not None:
            for relative in self.mint["CARGO_HOME_INPUT_TREES"]:
                if getattr(self, "omit_handoff_archive", False) and relative == "registry/cache":
                    continue
                if (source / relative).exists():
                    (destination / relative).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copytree(source / relative, destination / relative)
            self.assertFalse((destination / "registry/src").exists())
        return {"source": "explicit fixture"}

    def prepare(self):
        receipt = self.work / "receipt.json"
        stage.prewarm_dependencies(self.source, self.work, HOST, receipt, [], None, self.policy_engine)
        return stage.read_json(receipt)

    def test_actual_owner_fetch_uses_pinned_driver_private_cache_and_closed_environment(self):
        config = self.source / ".cargo/config.toml"
        config.parent.mkdir()
        config.write_text('[build]\ntarget-dir = "/unowned-target"\n'
                          '[target.aarch64-apple-darwin]\nrustflags = ["-Zcodegen-backend=untrusted"]\n'
                          '[host]\nrustflags = ["-Zcodegen-backend=untrusted-host"]\n'
                          '[unstable]\nhost-config = true\n')
        with mock.patch.dict(os.environ, {"CARGO_HOME": "/ambient", "RUSTC_WRAPPER": "/ambient-wrapper",
                "GIT_CONFIG_COUNT": "9", "GITHUB_TOKEN": "secret-fixture", "HTTPS_PROXY": "http://ambient"}):
            report = self.prepare()
        calls = [json.loads(line) for line in self.trace.read_text().splitlines()]
        self.assertEqual(len(calls), 15)
        self.assertEqual(report["driver_sha256"], stage.file_hash(self.driver))
        for call in calls:
            self.assertEqual(call["argv"][0], str(self.driver))
            environment = call["env"]
            self.assertIn(environment["CARGO_HOME"], {str(self.work / "cargo-home"), report["cargo_home"]})
            self.assertEqual(environment["RUSTC"], str(self.seed / "bin/trustc"))
            self.assertEqual(environment["HOME"], str(self.work / "home"))
            self.assertTrue(environment["PATH"].startswith(str(self.work / "git-bin")))
            for key in ("RUSTC_WRAPPER", "GIT_CONFIG_COUNT", "GITHUB_TOKEN", "HTTPS_PROXY"):
                if key == "RUSTC_WRAPPER":
                    self.assertEqual(environment[key], "")
                elif key == "HTTPS_PROXY":
                    self.assertEqual(environment[key], report["registry_transport"]["proxy_url"])
                    self.assertNotEqual(environment[key], "http://ambient")
                    self.assertEqual(environment["CARGO_HTTP_PROXY"], environment[key])
                    self.assertEqual(environment["NO_PROXY"], "")
                    self.assertEqual(environment["no_proxy"], "")
                else:
                    self.assertNotIn(key, environment)
            for key in ("RUSTC_WORKSPACE_WRAPPER", "CARGO_ENCODED_RUSTFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS"):
                self.assertEqual(environment[key], "")
            self.assertEqual(environment["CARGO_UNSTABLE_HOST_CONFIG"], "false")
            self.assertEqual(environment["CARGO_TARGET_DIR"], str(self.work / "unused-target"))
            self.assertEqual(environment["CARGO_BUILD_TARGET_DIR"], environment["CARGO_TARGET_DIR"])
        self.assertEqual([row["offline"] for row in report["completed_fetches"]], [False]*5+[True]*5)
        self.assertEqual([row["offline"] for row in report["handoff_offline_replay"]["completed_fetches"]], [True]*5)

    def test_extracted_sources_cannot_mask_a_missing_safe_handoff_archive(self):
        self.omit_handoff_archive = True
        with self.assertRaisesRegex(RuntimeError, "extracted source cannot mask"):
            self.prepare()
        self.assertFalse((self.work / "receipt.json").exists())
        self.assertTrue((self.work / "cargo-home/registry/src/extracted").exists())
        failures = list(self.work.glob("agh-git-*/registry-http-failure.json"))
        self.assertEqual(len(failures), 1)
        failed = json.loads(failures[0].read_text())
        self.assertEqual(failed["status"], "FAILED_OR_INCOMPLETE")
        self.assertTrue(failed["workers_settled"])
        self.assertEqual(failed["events"], [])

    def test_wrong_pinned_compiler_or_nongenuine_driver_refuses_before_fetch(self):
        self.compiler["commit"] = "b" * 40
        with self.assertRaisesRegex(stage.Refused, "seed identity refused"):
            self.prepare()
        self.assertFalse(self.trace.exists())
        self.compiler["commit"] = "a" * 40
        executable(self.driver, "#!/bin/sh\necho cargo fixture\n")
        with self.assertRaisesRegex(stage.Refused, "not genuine Targo"):
            self.prepare()
        self.assertFalse(self.trace.exists())

    def test_cargo_execution_config_refuses(self):
        config = self.source / ".cargo/config.toml"
        config.parent.mkdir()
        config.write_text('[env]\nRUSTC_WRAPPER = "ambient"\n')
        with self.assertRaisesRegex(stage.Refused, "Cargo config.*authority"):
            self.prepare()
        self.assertFalse(self.trace.exists())
        config.unlink()
        config.write_text('include = "unbound-config.toml"\n')
        with self.assertRaisesRegex(stage.Refused, "Cargo config.*authority"):
            self.prepare()
        self.assertFalse(self.trace.exists())

    def test_real_publication_policy_refuses_unbound_sources_and_lock_redirection_before_fetch(self):
        config = self.source / ".cargo/config.toml"
        config.parent.mkdir()
        outside = self.root / "outside-vendor"
        outside.mkdir()
        examples = [f'[source.crates-io]\nreplace-with = "outside"\n[source.outside]\ndirectory = "{outside}"\n',
                    '[patch.crates-io]\nexample = { path = "../../outside-package" }\n',
                    'paths = ["../../outside-package"]\n',
                    '[resolver]\nlockfile-path = "../../outside.lock"\n']
        for text in examples:
            with self.subTest(config=text.splitlines()[0]):
                config.write_text(text)
                with self.assertRaisesRegex(stage.Refused, "Cargo config.*authority"):
                    self.prepare()
                self.assertFalse(self.trace.exists())
        config.unlink()
        git_config = self.work / "cargo-home/git/db/fixture/config"
        git_config.parent.mkdir(parents=True)
        git_config.write_text('[core]\nbare = true\nsshCommand = evil\n')
        with self.assertRaisesRegex(stage.Refused, "Git config.*unsupported authority"):
            self.prepare()
        self.assertFalse(self.trace.exists())
        git_config.write_text('[core]\nbare = true\n')
        alternates = git_config.parent / "objects/info/alternates"
        alternates.parent.mkdir(parents=True)
        alternates.write_text("/unbound/object-store\n")
        with self.assertRaisesRegex(stage.Refused, "external or replacement custody"):
            self.prepare()
        self.assertFalse(self.trace.exists())

    def test_symlinked_or_non_directory_cargo_home_refuses_before_fetch(self):
        cache = self.work / "cargo-home"
        outside = self.root / "outside"
        outside.mkdir()
        cache.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(stage.Refused, "owned non-symlink director"):
            self.prepare()
        self.assertFalse(self.trace.exists())
        cache.unlink()
        cache.write_text("file")
        with self.assertRaisesRegex(stage.Refused, "owned non-symlink director"):
            self.prepare()
        self.assertFalse(self.trace.exists())


class DependencyLocalGitBudgetTests(unittest.TestCase):
    def transport(self):
        path = SCRIPT.with_name("daily_dependency_git.py")
        api = {"__file__": str(path), "__name__": "dependency_local_git_budget_tests"}
        exec(compile(path.read_bytes(), str(path), "exec"), api)
        return api

    def test_local_acquisition_uses_finite_source_ceiling(self):
        api = self.transport()
        calls = []
        fetch = ["-c", "protocol.file.allow=always", "-c", "fetch.fsckObjects=true", "-C",
                 "/owned/stage", "fetch", "--no-tags", "/owned/cache",
                 "+" + "a" * 40 + ":refs/agh/trust-daily-dependencies/" + "a" * 40]
        owner = {"_dependency_deadline": 1000,
                 "_provenance_git_environment": lambda: {},
                 "_controlled_git_command": lambda args: ["fixed-git", *args],
                 "_run_submodule_update_process": lambda *args, **kwargs:
                     calls.append((args, kwargs)) or subprocess.CompletedProcess(args, 0)}
        with mock.patch.dict(api, {"time": types.SimpleNamespace(monotonic=lambda: 100)}):
            api["local_git"](owner, fetch, bounded=True, acquisition=True)
            self.assertEqual(calls[-1][1]["timeout_seconds"], 600)
            api["local_git"](owner, ["gc", "--auto"], bounded=True)
            self.assertEqual(calls[-1][1]["timeout_seconds"], 120)
            owner["_dependency_deadline"] = 145
            api["local_git"](owner, fetch, bounded=True, acquisition=True)
            self.assertEqual(calls[-1][1]["timeout_seconds"], 45)
            owner["_dependency_deadline"] = 100
            count = len(calls)
            with self.assertRaisesRegex(RuntimeError, "deadline exhausted"):
                api["local_git"](owner, fetch, bounded=True, acquisition=True)
            self.assertEqual(len(calls), count)

    def test_acquisition_requires_owned_process_tree(self):
        api = self.transport()
        with self.assertRaisesRegex(RuntimeError, "process-tree custody"):
            api["local_git"]({}, ["fetch"], acquisition=True)
        for args in (["gc", "--auto"], ["fetch"], ["fetch", "--upload-pack=foreign"]):
            with self.subTest(args=args), self.assertRaisesRegex(RuntimeError, "fixed local source fetch"):
                api["local_git"]({}, args, bounded=True, acquisition=True)

    def test_local_acquisition_keeps_original_cleanup_and_exit_refusal(self):
        api = self.transport()
        fetch = ["-c", "protocol.file.allow=always", "--git-dir", "/owned/cache", "fetch",
                 "--no-tags", "--force", "--update-head-ok", "--recurse-submodules=no", "/owned/stage",
                 "+" + "a" * 40 + ":refs/commit/" + "a" * 40]
        owner = {"_dependency_deadline": time.monotonic() + 900,
                 "_provenance_git_environment": lambda: {},
                 "_controlled_git_command": lambda args: ["fixed-git", *args],
                 "_run_submodule_update_process": mock.Mock(side_effect=subprocess.TimeoutExpired("fixed-git", 600))}
        with self.assertRaises(subprocess.TimeoutExpired):
            api["local_git"](owner, fetch, bounded=True, acquisition=True)
        owner["_run_submodule_update_process"] = mock.Mock(return_value=subprocess.CompletedProcess([], 2))
        with self.assertRaisesRegex(RuntimeError, "did not complete"):
            api["local_git"](owner, fetch, bounded=True, acquisition=True)



class DependencyFetchBoundaryTests(unittest.TestCase):
    setUp = PrewarmBoundaryTests.setUp
    cache_input = PrewarmBoundaryTests.cache_input
    prepare = PrewarmBoundaryTests.prepare

    def transport(self):
        path = SCRIPT.with_name("daily_dependency_git.py")
        api = {"__file__": str(path), "__name__": "daily_dependency_transport_tests"}
        exec(compile(path.read_bytes(), str(path), "exec"), api)
        return api

    def repository(self, name, manifest=None, extra=None):
        root = self.root / ("git-" + name)
        root.mkdir()
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        git(root, "config", "user.name", "fixture")
        git(root, "config", "user.email", "fixture@example.invalid")
        git(root, "config", "core.hooksPath", os.devnull)
        (root / "Cargo.toml").write_text(manifest or f'[package]\nname="{name}"\nversion="0.1.0"\nedition="2021"\n')
        (root / "src").mkdir()
        (root / "src/lib.rs").write_text("")
        for rel, content in (extra or {}).items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        git(root, "add", ".")
        git(root, "commit", "-qm", "fixture")
        return root, git(root, "rev-parse", "HEAD")

    def profile(self, sources):
        api = self.transport()
        cache = self.work / "cargo-home"
        cache.mkdir(exist_ok=True)
        owner = dict(self.recreator)
        calls = []
        self.acquisition_calls = calls
        def acquire(url, stage, oid, ref, **kwargs):
            calls.append((url, oid))
            self.acquisition_store = stage.parent
            origin = sources[(url, oid)]
            subprocess.run(["git", "-c", "protocol.file.allow=always", "-C", str(stage),
                            "fetch", "--no-tags", str(origin), "+" + oid + ":" + ref],
                           check=True, capture_output=True)
            return {"program": {"fixture": "local only"}, "repository": url,
                    "source": oid, "private_ref": ref, "commit": oid}
        owner["_agh_source_fetch"] = acquire
        policy, document = api["prepare_profile"](self.source, self.work, cache,
                            self.closure, owner, {"HOME": str(self.work), "CARGO_HOME": str(cache)})
        return api, policy, document, calls

    def declare(self, url, oid, **extra):
        selector = next((key for key in ("branch", "tag") if key in extra), "rev")
        value = extra.get(selector, oid)
        text = '[package]\nname="profile-root"\nversion="0.1.0"\n[dependencies]\nprobe={git=' + json.dumps(url)
        text += ', ' + selector + '=' + json.dumps(value) + '}\n'
        path = self.source / "Cargo.toml"
        path.write_text(path.read_text() + text)
        source = "git+" + url + "?" + selector + "=" + value + "#" + oid
        (self.source / "Cargo.lock").write_text('version=4\n[[package]]\nname="probe"\nversion="0.1.0"\nsource=' + json.dumps(source) + '\n')

    def test_short_lock_and_nondefault_registry_refuse_before_acquisition(self):
        lock = self.source / "Cargo.lock"
        for value in ('git+https://github.com/Owner/probe#abcdef0', 'registry+https://github.com/Owner/index'):
            lock.write_text('version=4\n[[package]]\nname="probe"\nversion="0.1.0"\nsource=' + json.dumps(value) + '\n')
            with self.subTest(value=value), self.assertRaises(RuntimeError):
                self.profile({})
            self.assertFalse((self.work / "agh-git").exists())


    def test_transitive_exact_git_and_relative_gitlink_are_inspected(self):
        child, child_oid = self.repository("child")
        other, other_oid = self.repository("other")
        manifest = '[package]\nname="probe"\nversion="0.1.0"\n[dependencies]\nother={git="https://github.com/Owner/other",rev="' + other_oid + '"}\n'
        origin, _ = self.repository("probe", manifest)
        (origin / ".gitmodules").write_text('[submodule "nested"]\npath=nested\nurl=../child.git\n')
        git(origin, "add", ".gitmodules")
        git(origin, "update-index", "--add", "--cacheinfo", "160000", child_oid, "nested")
        git(origin, "commit", "-qm", "gitlink")
        oid = git(origin, "rev-parse", "HEAD")
        self.declare("https://github.com/Owner/probe", oid)
        lock = self.source / "Cargo.lock"
        lock.write_text(lock.read_text() + '\n[[package]]\nname="other"\nversion="0.1.0"\nsource="git+https://github.com/Owner/other?rev=' + other_oid + '#' + other_oid + '"\n')
        sources = {("https://github.com/Owner/" + name + ".git", value): path for name, value, path in
                   (("probe", oid, origin), ("child", child_oid, child), ("other", other_oid, other))}
        _, _, document, calls = self.profile(sources)
        self.assertEqual(set(calls), set(sources))
        self.assertEqual(len(document["stages"]), 3)



    def test_non_rust_gitlink_source_needs_no_fabricated_cargo_package(self):
        child, child_oid = self.repository("child")
        (child / "Cargo.toml").unlink()
        git(child, "add", "-u")
        git(child, "commit", "-qm", "non-Rust submodule")
        child_oid = git(child, "rev-parse", "HEAD")
        origin, _ = self.repository("probe", extra={".gitmodules": '[submodule "nested"]\npath=nested\nurl=../child.git\n'})
        git(origin, "update-index", "--add", "--cacheinfo", "160000", child_oid, "nested")
        git(origin, "commit", "-qm", "gitlink")
        oid = git(origin, "rev-parse", "HEAD")
        self.declare("https://github.com/Owner/probe", oid)
        _, _, document, calls = self.profile({("https://github.com/Owner/probe.git", oid): origin,
                                             ("https://github.com/Owner/child.git", child_oid): child})
        self.assertEqual(len(calls), 2)
        row = next(row for row in document["acquisitions"] if row["commit"] == child_oid)
        self.assertTrue(any(row["parent_oid"] == oid and row["oid"] == child_oid and row["active"] for row in document["gitlinks"]))

    def test_exact_owned_cache_content_avoids_agh_without_guessing_a_cargo_identifier(self):
        origin, oid = self.repository("probe")
        self.declare("https://github.com/Owner/probe", oid)
        cache = self.work / "cargo-home"
        db = cache / "git/db/owned-support-store-is-not-a-cargo-url-hash"
        db.parent.mkdir(parents=True)
        subprocess.run(["git", "init", "--bare", "-q", str(db)], check=True)
        subprocess.run(["git", "-c", "protocol.file.allow=always", "--git-dir", str(db),
                        "fetch", "--no-tags", str(origin), "+" + oid + ":refs/commit/" + oid],
                       check=True, capture_output=True)
        _, _, document, calls = self.profile({})
        self.assertEqual(calls, [])
        self.assertEqual(document["acquisitions"][0]["method"], "exact-owned-cargo-cache")
        self.assertEqual(document["acquisitions"][0]["cache_db"], str(db))
        stage = Path(document["stages"]["https://github.com/Owner/probe.git#" + oid]["path"])
        self.assertFalse((stage / ".git/objects/info/alternates").exists())
        self.assertEqual(git(stage, "rev-parse", document["acquisitions"][0]["private_ref"]), oid)

    def test_same_url_commits_share_owned_store_and_preserve_both_exact_refs(self):
        origin, first = self.repository("probe")
        (origin / "src/lib.rs").write_text("// another exact commit\n")
        git(origin, "add", ".")
        git(origin, "commit", "-qm", "second")
        second = git(origin, "rev-parse", "HEAD")
        self.declare("https://github.com/Owner/probe", second)
        (self.source / "Cargo.lock").write_text('version=4\n[[package]]\nname="probe"\nversion="0.1.0"\n'
            'source="git+https://github.com/Owner/probe#' + first + '"\n'
            '\n[[package]]\nname="probe"\nversion="0.1.0"\nsource="git+https://github.com/Owner/probe#' + second + '"\n')
        _, _, document, calls = self.profile({("https://github.com/Owner/probe.git", first): origin,
                                             ("https://github.com/Owner/probe.git", second): origin})
        stages = list(document["stages"].values())
        self.assertEqual(len(stages), 2)
        self.assertEqual(stages[0]["path"], stages[1]["path"])
        for stage in stages:
            self.assertEqual(git(Path(stage["path"]), "rev-parse", stage["ref"]), stage["oid"])

    def test_bare_cache_config_and_object_redirects_refuse_before_any_agh(self):
        origin, oid = self.repository("probe")
        self.declare("https://github.com/Owner/probe", oid)
        db = self.work / "cargo-home/git/db/actual-physical-db"
        db.parent.mkdir(parents=True)
        subprocess.run(["git", "init", "--bare", "-q", str(db)], check=True)
        config = db / "config"
        original = config.read_bytes()
        for extra in (b'\n[include]\npath=/unowned-config\n', b'\n[core]\nhooksPath=/unowned-hooks\n'):
            config.write_bytes(original + extra)
            with self.subTest(extra=extra), self.assertRaisesRegex(RuntimeError, "unsupported authority"):
                self.profile({})
            self.assertEqual(self.acquisition_calls, [])
        config.write_bytes(original)
        (db / "objects/info/alternates").write_text(str(origin / ".git/objects") + "\n")
        with self.assertRaisesRegex(RuntimeError, "custody"):
            self.profile({})
        self.assertEqual(self.acquisition_calls, [])

    def test_missing_owner_lock_refuses_before_any_acquisition(self):
        (self.source / "Cargo.lock").unlink()
        with self.assertRaisesRegex(RuntimeError, "no committed lockfile"):
            self.profile({})

    def test_locked_mutable_selector_is_native_data_not_a_second_resolution(self):
        origin, oid = self.repository("probe", extra={"unrelated/Cargo.toml": "not valid TOML at all"})
        self.declare("https://github.com/Owner/probe", oid, branch="main")
        _, _, document, calls = self.profile({("https://github.com/Owner/probe.git", oid): origin})
        self.assertEqual(calls, [("https://github.com/Owner/probe.git", oid)])
        self.assertEqual(document["roots"][0]["owner_lock"], "Cargo.lock")
        self.assertEqual(document["roots"][0]["oid"], oid)

    def test_inactive_gitlink_retained_without_acquisition(self):
        child, child_oid = self.repository("child")
        origin, _ = self.repository("probe", extra={".gitmodules": '[submodule "nested"]\npath=nested\nurl=../child.git\nupdate=none\n'})
        git(origin, "update-index", "--add", "--cacheinfo", "160000", child_oid, "nested")
        git(origin, "commit", "-qm", "inactive gitlink")
        oid = git(origin, "rev-parse", "HEAD")
        self.declare("https://github.com/Owner/probe", oid)
        _, _, document, calls = self.profile({("https://github.com/Owner/probe.git", oid): origin})
        self.assertEqual(calls, [("https://github.com/Owner/probe.git", oid)])
        self.assertEqual(len(document["gitlinks"]), 1)
        self.assertFalse(document["gitlinks"][0]["active"])
        self.assertEqual(document["gitlinks"][0]["oid"], child_oid)

    def test_http_routing_configuration_refuses_before_driver_fetch(self):
        config = self.source / ".cargo/config.toml"
        config.parent.mkdir()
        for text in ('[http]\nproxy="http://unowned"\n', '[http]\nno-proxy="*"\n', '[http]\nssl-verify=false\n'):
            config.write_text(text)
            with self.subTest(text=text), self.assertRaisesRegex(stage.Refused, "HTTP routing/TLS authority"):
                self.prepare()
            self.assertFalse(self.trace.exists())

    def test_cli_rejects_nonliteral_options_and_refspecs(self):
        api = self.transport()
        oid = "a" * 40
        good = ["fetch", "--no-tags", "--force", "--update-head-ok", "--recurse-submodules=no",
                "https://github.com/Owner/probe", "+" + oid + ":refs/commit/" + oid]
        self.assertEqual(api["parse_fetch"](good)[1], oid)
        for argv in (["-c", "core.sshCommand=evil", *good], [*good[:-1], "+refs/heads/*:refs/remotes/origin/*"],
                     [*good[:-1], "+" + oid + ":refs/heads/main"],
                     [*good[:1], "--tags", *good[2:]], [*good, "--upload-pack=evil"]):
            with self.subTest(argv=argv), self.assertRaises(RuntimeError):
                api["parse_fetch"](argv)

    def test_local_adapter_preserves_actual_cargo_db_ref_and_fetch_head(self):
        origin, oid = self.repository("probe")
        self.declare("https://github.com/Owner/probe", oid)
        api, policy, document, _ = self.profile({("https://github.com/Owner/probe.git", oid): origin})
        db = self.work / "cargo-home/git/db/arbitrary-cargo-selected-identifier"
        db.parent.mkdir(parents=True)
        subprocess.run(["git", "init", "--bare", "-q", str(db)], check=True)
        argv = ["fetch", "--no-tags", "--quiet", "--force", "--update-head-ok", "--recurse-submodules=no",
                "https://github.com/Owner/probe", "+" + oid + ":refs/commit/" + oid]
        old = Path.cwd()
        try:
            os.chdir(db)
            with mock.patch.dict(os.environ, {"GIT_DIR": str(db)}, clear=True):
                api["git_entry"](policy, argv)
                self.assertEqual(git(db, "rev-parse", "refs/commit/" + oid), oid)
                self.assertTrue((db / "FETCH_HEAD").read_text().startswith(oid + "\t"))
                with mock.patch.dict(os.environ, {"GIT_DIR": str(origin)}), self.assertRaises(RuntimeError):
                    api["git_entry"](policy, argv)
                (db / "objects/info/alternates").write_text(str(origin / ".git/objects") + "\n")
                with self.assertRaisesRegex(RuntimeError, "custody"):
                    api["git_entry"](policy, argv)
        finally:
            os.chdir(old)


class DependencySourceOwnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="dependency-source-owner-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.path = self.root / "owner.py"
        self.marker = self.root / "marker"
        path = SCRIPT.with_name("daily_dependency_git.py")
        self.api = {"__file__": str(path), "__name__": "dependency_source_owner_tests"}
        exec(compile(path.read_bytes(), str(path), "exec"), self.api)
        self.good = f"from pathlib import Path\nPath({str(self.marker)!r}).write_text('A')\n".encode()
        self.bad = self.good.replace(b"'A'", b"'B'")
        self.expected = hashlib.sha256(self.good).hexdigest()

    def test_aba_executes_exactly_the_buffer_whose_digest_is_recorded(self):
        import builtins
        self.path.write_bytes(self.good)
        original_read = Path.read_bytes
        captured, seen = [], []
        def read(path):
            raw = original_read(path)
            if path == self.path and not seen:
                seen.append(True)
                self.path.write_bytes(self.bad)
            return raw
        def compile_buffer(raw, filename, mode):
            captured.append(raw)
            self.path.write_bytes(self.good)
            return builtins.compile(raw, filename, mode)
        with mock.patch.object(Path, "read_bytes", read), mock.patch.dict(self.api, {"compile": compile_buffer}):
            _owner, actual = self.api["source_owner"](self.path, "captured_aba_owner", self.expected)
        self.assertEqual(actual, self.expected)
        self.assertEqual(captured, [self.good])
        self.assertEqual(self.marker.read_text(), "A")
        self.assertEqual(self.path.read_bytes(), self.good)

    def test_expected_mismatch_refuses_before_source_execution(self):
        self.path.write_bytes(self.bad)
        with self.assertRaisesRegex(RuntimeError, "captured identity"):
            self.api["source_owner"](self.path, "wrong_source_owner", self.expected)
        self.assertFalse(self.marker.exists())

    def test_timestamp_valid_bytecode_is_never_the_loaded_owner(self):
        import py_compile
        self.path.write_bytes(self.bad)
        old = self.path.stat()
        cached = Path(py_compile.compile(str(self.path), doraise=True))
        cached_hash = hashlib.sha256(cached.read_bytes()).hexdigest()
        self.path.write_bytes(self.good)
        os.utime(self.path, ns=(old.st_atime_ns, old.st_mtime_ns))
        _owner, actual = self.api["source_owner"](self.path, "source_without_cached_owner", self.expected)
        self.assertEqual(actual, self.expected)
        self.assertEqual(self.marker.read_text(), "A")
        self.assertEqual(hashlib.sha256(cached.read_bytes()).hexdigest(), cached_hash)

    def test_changed_source_cannot_return_a_successful_owner(self):
        raw = f"from pathlib import Path\nPath({str(self.path)!r}).write_text('changed')\n".encode()
        self.path.write_bytes(raw)
        with self.assertRaisesRegex(RuntimeError, "changed while loading"):
            self.api["source_owner"](self.path, "changed_source_owner")

    def test_actual_recreator_and_mint_share_the_source_bound_identity_module(self):
        import py_compile
        import types
        source = SCRIPT.parents[1]
        names = ("scripts/recreate_bootstrap.py", "scripts/mint_seed_support.py",
                 "scripts/seed_custody_source.py", "src/bootstrap/stage0_identity.py")
        for name in names:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source / name, target)
        identity = self.root / names[-1]
        good = identity.read_bytes()
        bad = b"raise RuntimeError('unchecked identity bytecode executed')\n"
        bad += b"#" * (len(good) - len(bad))
        identity.write_bytes(bad)
        old = identity.stat()
        cached = Path(py_compile.compile(str(identity), doraise=True))
        cache_hash = hashlib.sha256(cached.read_bytes()).hexdigest()
        identity.write_bytes(good)
        os.utime(identity, ns=(old.st_atime_ns, old.st_mtime_ns))
        owner, _digest = self.api["source_owner"](self.root / names[2], "actual_dependency_source_loader")
        expected = {name: hashlib.sha256((self.root / name).read_bytes()).hexdigest() for name in names}
        loader = owner["BoundSourceLoader"](self.root, expected)
        with mock.patch.dict(sys.modules, {"trust_stage0_identity": types.ModuleType("untrusted_cached_identity")}):
            recreator = loader.module("actual_dependency_recreator", self.root / names[0])
            mint = loader.module("actual_dependency_mint", self.root / names[1])
            self.assertIs(recreator._IDENTITY_OWNER, mint._IDENTITY_OWNER)
            self.assertEqual(recreator._IDENTITY_SOURCE_SHA256, expected[names[-1]])
            self.assertEqual(mint._IDENTITY_OWNER.__source_sha256__, expected[names[-1]])
            self.assertIsNone(loader.context)
            loader.recheck()
        self.assertEqual(hashlib.sha256(cached.read_bytes()).hexdigest(), cache_hash)


class RegistryHttpBoundaryTests(unittest.TestCase):
    def api(self):
        path = SCRIPT.with_name("daily_registry_proxy.py")
        api = {"__file__": str(path), "__name__": "registry_policy_control"}
        exec(compile(path.read_bytes(), str(path), "exec"), api)
        return api

    def request(self, gate, first_line):
        import socket
        client = socket.socket()
        client.settimeout(3)
        client.connect(gate.server.server_address)
        client.sendall(first_line + b"\r\nHost: ignored\r\n\r\n")
        reply = client.recv(4096)
        client.close()
        return reply

    def test_only_exact_registry_tls_connects_are_admitted_before_any_dns(self):
        api = self.api()
        with mock.patch.object(api["socket"], "getaddrinfo") as outbound:
            with api["RegistryHttpGate"](time.monotonic() + 5) as gate:
                for line in (b"CONNECT api.github.com:443 HTTP/1.1", b"CONNECT github.com:443 HTTP/1.1",
                             b"CONNECT index.crates.io:80 HTTP/1.1", b"GET http://index.crates.io/config.json HTTP/1.1",
                             b"CONNECT user@index.crates.io:443 HTTP/1.1", b"CONNECT index.crates.io.evil:443 HTTP/1.1",
                             b"CONNECT static.crates.io:444 HTTP/1.1"):
                    with self.subTest(line=line):
                        self.assertIn(b"403", self.request(gate, line))
            outbound.assert_not_called()
            self.assertEqual(len(gate.events), 7)
            self.assertTrue(all(not event["accepted"] for event in gate.events))

    def test_opaque_tunnel_preserves_full_binary_tail_and_half_close(self):
        import socket
        api = self.api()
        left, right = socket.socketpair()
        payload = bytes(range(256)) * 600
        def echo():
            try:
                while True:
                    data = right.recv(4096)
                    if not data:
                        right.shutdown(socket.SHUT_WR)
                        break
                    right.sendall(data)
            finally:
                right.close()
        thread = threading.Thread(target=echo)
        thread.start()
        try:
            def connected(gate, host):
                self.assertEqual(host, "index.crates.io")
                self.assertTrue(gate._register(left))
                return left
            with mock.patch.object(api["RegistryHttpGate"], "_connect_upstream", autospec=True,
                                   side_effect=connected) as outbound:
                with api["RegistryHttpGate"](time.monotonic() + 10) as gate:
                    client = socket.socket()
                    client.settimeout(5)
                    client.connect(gate.server.server_address)
                    client.sendall(b"CONNECT index.crates.io:443 HTTP/1.1\r\n\r\n")
                    header = bytearray()
                    while not header.endswith(b"\r\n\r\n"):
                        header.extend(client.recv(1))
                    self.assertIn(b"200", header)
                    client.sendall(payload)
                    client.shutdown(socket.SHUT_WR)
                    received = bytearray()
                    while True:
                        data = client.recv(8192)
                        if not data:
                            break
                        received.extend(data)
                    client.close()
                    self.assertEqual(received, payload)
                outbound.assert_called_once()
                self.assertEqual(outbound.call_args.args[1], "index.crates.io")
                self.assertEqual(gate.events, [{"target": "index.crates.io:443", "accepted": True}])
        finally:
            left.close()
            right.close()
            thread.join(5)
            self.assertFalse(thread.is_alive())

    def test_offline_policy_and_proxy_environment_cannot_inherit_bypass(self):
        api = self.api()
        with mock.patch.object(api["socket"], "getaddrinfo") as outbound:
            with api["RegistryHttpGate"](time.monotonic() + 5, offline=True) as gate:
                env = gate.environment({"NO_PROXY": "*", "no_proxy": "github.com", "CARGO_HTTP_PROXY": "", "HTTPS_PROXY": "http://other"})
                self.assertEqual(env["CARGO_HTTP_PROXY"], gate.url)
                for name in ("HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "http_proxy", "https_proxy", "all_proxy"):
                    self.assertEqual(env[name], gate.url)
                self.assertEqual(env["NO_PROXY"], "")
                self.assertEqual(env["no_proxy"], "")
                self.assertEqual(env["CARGO_HTTP_SSL_VERIFY"], "true")
                self.assertIn(b"403", self.request(gate, b"CONNECT index.crates.io:443 HTTP/1.1"))
            outbound.assert_not_called()

    def test_event_budget_fails_closed_instead_of_dropping_complete_population(self):
        api = self.api()
        api["RegistryHttpGate"]._event.__globals__["MAX_EVENTS"] = 2
        with mock.patch.object(api["socket"], "getaddrinfo") as outbound:
            with self.assertRaisesRegex(RuntimeError, "event population"):
                with api["RegistryHttpGate"](time.monotonic() + 5) as gate:
                    for _ in range(3):
                        self.assertIn(b"403", self.request(gate, b"CONNECT api.github.com:443 HTTP/1.1"))
            outbound.assert_not_called()
            self.assertEqual(len(gate.events), 2)

    def test_listener_start_failure_closes_bound_socket(self):
        api = self.api()
        gate = api["RegistryHttpGate"](time.monotonic() + 5)
        with mock.patch.object(gate.thread, "start", side_effect=RuntimeError("cannot start listener")):
            with self.assertRaisesRegex(RuntimeError, "cannot start listener"):
                gate.__enter__()
        self.assertEqual(gate.server.fileno(), -1)
        self.assertFalse(gate.thread.is_alive())
        self.assertTrue(gate.closed.is_set())

    def test_worker_start_failure_returns_capacity_and_never_joins_unstarted_thread(self):
        api = self.api()
        for failure in ("constructor", "start"):
            with self.subTest(failure=failure):
                gate = api["RegistryHttpGate"](time.monotonic() + 5)
                with self.assertRaisesRegex(RuntimeError, "worker could not start"):
                    with gate:
                        target = api["threading"] if failure == "constructor" else api["threading"].Thread
                        attribute = "Thread" if failure == "constructor" else "start"
                        with mock.patch.object(target, attribute, side_effect=RuntimeError("thread unavailable")):
                            self.assertIn(b"503", self.request(gate, b"CONNECT index.crates.io:443 HTTP/1.1"))
                        self.assertEqual(gate.workers, set())
                        available = 0
                        while gate.capacity.acquire(blocking=False):
                            available += 1
                        for _ in range(available):
                            gate.capacity.release()
                        self.assertEqual(available, api["MAX_CONNECTIONS"])
                self.assertFalse(gate.thread.is_alive())
                self.assertEqual(gate.server.fileno(), -1)

    def test_delayed_dns_cannot_create_a_socket_after_shutdown(self):
        import socket
        api = self.api()
        gate = api["RegistryHttpGate"](time.monotonic() + 5)
        entered = threading.Event()
        def resolve(*args, **kwargs):
            entered.set()
            self.assertTrue(gate.closed.wait(3))
            return [(socket.AF_INET, socket.SOCK_STREAM, 6, "", ("127.0.0.1", 443))]
        gate.__enter__()
        client = socket.socket()
        try:
            with mock.patch.object(api["socket"], "getaddrinfo", side_effect=resolve):
                client.connect(gate.server.server_address)
                client.sendall(b"CONNECT index.crates.io:443 HTTP/1.1\r\n\r\n")
                self.assertTrue(entered.wait(3))
                with mock.patch.object(api["socket"], "socket", wraps=socket.socket) as outbound:
                    gate.__exit__(None, None, None)
                    outbound.assert_not_called()
            self.assertFalse(gate.thread.is_alive())
            self.assertEqual(gate.workers, set())
            self.assertTrue(all(not event["accepted"] for event in gate.events))
        finally:
            client.close()
            if gate.thread.is_alive():
                gate.__exit__(None, None, None)

    def test_dns_returning_after_deadline_cannot_begin_connect(self):
        import socket
        api = self.api()
        gate = api["RegistryHttpGate"](time.monotonic() + 5)
        entered, release = threading.Event(), threading.Event()
        def resolve(*args, **kwargs):
            entered.set()
            self.assertTrue(release.wait(3))
            return [(socket.AF_INET, socket.SOCK_STREAM, 6, "", ("127.0.0.1", 443))]
        with gate, mock.patch.object(api["socket"], "getaddrinfo", side_effect=resolve):
            client = socket.socket()
            client.settimeout(3)
            try:
                client.connect(gate.server.server_address)
                client.sendall(b"CONNECT index.crates.io:443 HTTP/1.1\r\n\r\n")
                self.assertTrue(entered.wait(3))
                with mock.patch.object(api["socket"], "socket", wraps=socket.socket) as outbound:
                    gate.deadline = time.monotonic() - 1
                    release.set()
                    self.assertIn(b"403", client.recv(4096))
                    outbound.assert_not_called()
            finally:
                release.set()
                client.close()
        self.assertFalse(gate.thread.is_alive())
        self.assertEqual(gate.workers, set())
        self.assertEqual(gate.events, [{"target": "index.crates.io:443", "accepted": False}])


class DailyStagingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="daily-stage-test-")
        self.root = Path(self.temp.name).resolve()
        self.repo = self.make_repository("trust")
        self.aterm = self.make_repository("aterm")
        self.publication = self.make_publication()
        self.state = self.root / "state"
        self.cargo_home = self.root / "cargo-inputs"
        self.cargo_home.mkdir()
        self.elan_home = self.root / "default-elan-home"
        self.elan_home.mkdir()
        # Inert stand-in: the runner selects and hashes it; no fixture owner runs it.
        self.serial = self.root / "serial/trust-serial-command"
        executable(self.serial)
        self.owners = Owners()

    def tearDown(self):
        self.temp.cleanup()

    def make_repository(self, name):
        repo = self.root / name
        repo.mkdir()
        subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True)
        git(repo, "config", "user.email", "fixture@example.invalid")
        git(repo, "config", "user.name", "fixture")
        git(repo, "config", "core.hooksPath", "/dev/null")
        git(repo, "config", "commit.gpgsign", "false")
        (repo / ".gitignore").write_text("/bootstrap.toml\n/build/\n")
        (repo / "README").write_text(name)
        executable(repo / "scripts/build-slot")
        (repo / "scripts/recreate_bootstrap.py").write_text(
            'BUILD_AUTHORITY_ENV_NAMES = {"CARGO_HOME", "RUSTUP_HOME", "CPATH", "LIBRARY_PATH", "SDKROOT"}\n'
            'BUILD_AUTHORITY_ENV_PREFIXES = ("CARGO_", "RUST", "TRUST_")\n')
        git(repo, "add", ".")
        git(repo, "commit", "-qm", "initial")
        remote = self.root / (name + ".git")
        subprocess.run(["git", "clone", "-q", "--bare", str(repo), str(remote)], check=True)
        git(repo, "remote", "add", "origin", str(remote))
        return repo

    def arguments(self, *extra):
        lean = [] if "--elan-home" in extra or os.environ.get("ELAN_HOME") else ["--elan-home", str(self.elan_home)]
        serial = [] if "--serial-command" in extra or "--serial-command-from-path" in extra else ["--serial-command", str(self.serial)]
        extra = tuple(word for word in extra if word != "--serial-command-from-path")
        return stage.parser().parse_args(["run", "--repo", str(self.repo), "--state-root", str(self.state),
                                         "--host", HOST, "--cargo-home", str(self.cargo_home), "--consumer-jobs", "1",
                                         *lean, *serial, *extra])

    def train_arguments(self, *extra):
        lean = [] if "--elan-home" in extra or os.environ.get("ELAN_HOME") else ["--elan-home", str(self.elan_home)]
        serial = [] if "--serial-command" in extra else ["--serial-command", str(self.serial)]
        return stage.parser().parse_args([
            "train", "--repo", str(self.repo), "--state-root", str(self.state), "--host", HOST,
            "--cargo-home", str(self.cargo_home), "--consumer-jobs", "1", "--aterm-repo", str(self.aterm),
            "--publication-repo", str(self.publication), "--github-repo", "fixture/trust", *lean, *serial, *extra])

    def make_publication(self):
        publication = self.make_repository("publication")
        engine = publication / "bin/pub"
        engine.parent.mkdir()
        engine.write_text('''import hashlib, re, shlex
def load_config(directory):
    text = (directory / "config.sh").read_text()
    match = re.fullmatch(r'CHECK_CMD_DEFAULT="([^"]*)"\\n', text)
    if not match:
        raise ValueError("unsupported committed policy fixture")
    command = match[1]
    if "--standalone" in command:
        raise ValueError("non-proof command")
    return {"check": command, "check_lane": "strict", "check_timeout": 60, "check_baseline": None}
def check_command_toolchain(command):
    return "trust" if "rustup run trust targo" in command else None
def check_command_steps(command):
    return [shlex.split(part) for part in command.split("&&")]
def stock_rust_step(words):
    if words[:2] == ["rustup", "run"] and len(words) > 3 and words[3] == "cargo":
        return ("cargo", words[2], tuple([words[words.index("--target") + 1]]))
    return None
def gate_wall_clock_bound(command, committed, source):
    return {"seconds": committed, "committed": committed, "source": "committed"}
def terminate_process_group(process, drain=None):
    process.terminate()
    process.wait(timeout=5)
    return None, None
''')
        engine.write_text(engine.read_text() + "\n" + OUTCOME_OWNER.read_text())
        (publication / "bin/pub-relock").write_text("def config_refusals(label, doc): return []\n")
        git(publication, "add", "bin/pub", "bin/pub-relock")
        git(publication, "commit", "-qm", "policy reader")
        git(publication, "push", "origin", "main")
        return publication

    def consumer_arguments(self):
        repositories = {"aterm": self.aterm}
        repositories.update({name: self.make_repository(name) for name in ("ay", "ty", "clean")})
        argv = ["--publication-repo", str(self.publication)]
        for name, repo in repositories.items():
            policy = repo / "publish/config.sh"
            policy.parent.mkdir()
            policy.write_text('CHECK_CMD_DEFAULT="rustup run trust targo trust check --locked && printf fixture"\n')
            git(repo, "add", "publish/config.sh")
            git(repo, "commit", "-qm", "committed check")
            git(repo, "push", "origin", "main")
            argv += ["--consumer", f"{name}={repo}"]
        return argv, repositories

    def run_pipeline(self, *extra):
        runner = stage.Runner(self.arguments(*extra), self.owners)
        result = runner.run()
        return result, runner.record

    def names(self):
        return [name for name, _, _ in self.owners.calls]

    def test_oversized_dirty_status_cannot_be_mistaken_for_clean_source(self):
        runner = stage.Runner(self.arguments())
        runner.invocation = self.state / "runs/query-boundary"
        runner.invocation.mkdir(parents=True)
        runner.record = {"steps": []}
        fake_bin = self.root / "fake-bin"
        payload = "import sys; sys.stdout.write((' M ' + 'x'*100 + '\\n')*12000)"
        executable(fake_bin / "git", f"#!/bin/sh\nexec {shlex.quote(sys.executable)} -I -S -c {shlex.quote(payload)}\n")
        runner.env["PATH"] = f"{fake_bin}:/usr/bin:/bin"
        # Managed queries ignore a caller's PATH Git. Explicitly inject the
        # oversized fixture child at the existing executor seam instead, while
        # retaining the real production bounded-query transport and refusal.
        runner.clean(self.repo)
        def oversized_query(argv, cwd, env, log, **kwargs):
            self.assertNotEqual(argv[0], str(fake_bin / "git"))
            return stage.command([str(fake_bin / "git")], cwd, env, log, **kwargs)
        runner.execute = oversized_query
        with self.assertRaisesRegex(stage.Refused, "Git query output exceeds"):
            runner.clean(self.repo)
        self.assertGreater(Path(runner.last_step()["log"]).stat().st_size, stage.MAX_QUERY_BYTES)

    def test_real_large_clean_receipt_survives_bounded_query_transport(self):
        helper = self.repo / "scripts/mint_seed_support.py"
        helper.write_text('''import argparse, json
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument("command")
p.add_argument("--root")
p.add_argument("--elan-home")
p.add_argument("--output")
args = p.parse_args()
value = {"schema": "trust.mint-clean-lean-inputs.v1",
         "library_path": str(Path(args.elan_home) / "toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean"),
         "fingerprint": "fixture-source-bound-input",
         "installed_files": [{"path": f"lib/lean/Lean/Module{n}.olean", "sha256": "a"*64}
                             for n in range(14446)]}
text = json.dumps(value) + "\\n"
if args.output:
    with Path(args.output).open("x") as stream:
        stream.write(text)
else:
    print(text, end="")
''')
        git(self.repo, "add", "scripts/mint_seed_support.py")
        git(self.repo, "commit", "-qm", "large selector receipt fixture")
        git(self.repo, "push", "origin", "main")

        def execute(argv, cwd, env, log, timeout=None, **kwargs):
            if "clean-lean-inputs" in argv:
                return stage.command(argv, cwd, env, log, timeout, **kwargs)
            return self.owners(argv, cwd, env, log, timeout, **kwargs)

        runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), execute)
        self.assertEqual(runner.run(), 0, runner.record.get("error"))
        lean = runner.record["clean_lean_inputs"]
        self.assertEqual(len(lean["installed_files"]), 14446)
        call = next(row for row in runner.record["steps"] if row["name"] == "clean-lean-inputs")
        receipt = Path(call["argv"][call["argv"].index("--output") + 1])
        self.assertEqual(receipt.parent, runner.invocation)
        self.assertGreater(receipt.stat().st_size, stage.MAX_QUERY_BYTES)
        self.assertLess(Path(call["log"]).stat().st_size, stage.MAX_QUERY_BYTES)
        self.assertEqual(json.loads(receipt.read_text()), lean)
        self.assertEqual(runner.record["artifacts"][str(receipt)], stage.fingerprint(receipt))

    def test_unusable_clean_receipt_refuses_before_mint(self):
        valid = self.root / "outside-clean-input.json"
        valid.write_text('{"library_path": "/outside"}\n')
        for kind in ("missing", "symlink", "directory", "truncated"):
            with self.subTest(kind=kind):
                self.state = self.root / ("state-clean-receipt-" + kind)
                self.owners.calls.clear()

                def execute(argv, cwd, env, log, timeout=None, **kwargs):
                    if "clean-lean-inputs" not in argv:
                        return self.owners(argv, cwd, env, log, timeout, **kwargs)
                    receipt = Path(argv[argv.index("--output") + 1])
                    if kind == "symlink":
                        receipt.symlink_to(valid)
                    elif kind == "directory":
                        receipt.mkdir()
                    elif kind == "truncated":
                        receipt.write_text('{"library_path":')
                    log.write_text(json.dumps({"argv": argv, "cwd": str(cwd)}) + "\n")
                    return log.read_text()

                runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), execute)
                self.assertEqual(runner.run(), 1)
                self.assertEqual(runner.record["status"], "failed")
                self.assertFalse(runner.record["deployment_ready"])
                self.assertNotIn("mint-preflight", self.names())
                self.assertNotIn("sanctioned-mint-and-double-compile", self.names())

    def test_fresh_stage_creates_build_root_before_real_mint_output_guard(self):
        checks = []

        def execute(argv, cwd, env, log, timeout=None, **kwargs):
            if log.stem.endswith("-mint-preflight"):
                guard = subprocess.run(
                    [sys.executable, "-I", "-S", str(SCRIPT.parent / "mint_seed_support.py"),
                     "check-output", str(cwd), str(cwd / "build/probe-new-output"), "fixture output"],
                    capture_output=True, text=True,
                )
                self.assertEqual(guard.returncode, 0, guard.stderr)
                self.assertTrue((cwd / "build").is_dir())
                self.assertFalse((cwd / "build").is_symlink())
                checks.append(guard.returncode)
            return self.owners(argv, cwd, env, log, timeout, **kwargs)

        runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), execute)
        self.assertEqual(runner.run(), 0, runner.record.get("error"))
        self.assertEqual(checks, [0])

    def test_unsafe_managed_build_root_refuses_before_mint(self):
        outside = self.root / "outside-build"
        outside.mkdir()
        for kind in ("directory-link", "dangling-link", "file"):
            with self.subTest(kind=kind):
                self.state = self.root / ("state-build-" + kind)
                self.owners.calls.clear()

                def execute(argv, cwd, env, log, timeout=None, **kwargs):
                    result = self.owners(argv, cwd, env, log, timeout, **kwargs)
                    if log.stem.endswith("-pinned-bootstrap-config"):
                        build = cwd / "build"
                        if kind == "file":
                            build.write_text("preserve existing file")
                        else:
                            build.symlink_to(outside if kind == "directory-link" else outside / "absent")
                    return result

                runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), execute)
                self.assertEqual(runner.run(), 1)
                self.assertEqual(runner.record["status"], "failed")
                self.assertFalse(runner.record["deployment_ready"])
                self.assertNotIn("mint-preflight", self.names())
                self.assertNotIn("sanctioned-mint-and-double-compile", self.names())
                self.assertEqual(list(outside.iterdir()), [])
                build = self.state / "source/build"
                if kind == "file":
                    self.assertEqual(build.read_text(), "preserve existing file")
                else:
                    self.assertTrue(build.is_symlink())


    def test_clean_receipt_replacement_after_parse_refuses_before_mint(self):
        for reuse in (False, True):
            with self.subTest(reuse=reuse):
                self.state = self.root / ("receipt-race-cached" if reuse else "receipt-race-cold")
                if reuse:
                    cached = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), self.owners)
                    self.assertEqual(cached.run(), 0, cached.record.get("error"))
                self.owners.calls.clear()
                runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), self.owners)
                original = json.loads
                replaced = []

                def replace_after_parse(text, *args, **kwargs):
                    value = original(text, *args, **kwargs)
                    if (not replaced and isinstance(value, dict)
                            and value.get("schema") == "trust.mint-clean-lean-inputs.v1"):
                        receipt = runner.invocation / "clean-lean-inputs.json"
                        replacement = receipt.with_suffix(".replacement")
                        replacement.write_text(json.dumps({**value, "library_path": "/changed/after/parse"}))
                        replacement.replace(receipt)
                        replaced.append(receipt)
                    return value

                with mock.patch.object(stage.json, "loads", side_effect=replace_after_parse):
                    self.assertEqual(runner.run(), 1)
                self.assertEqual(len(replaced), 1)
                self.assertEqual(runner.record["status"], "failed")
                self.assertFalse(runner.record["consumer_ready"])
                self.assertFalse(runner.record["deployment_ready"])
                self.assertNotIn("mint-preflight", self.names())
                self.assertNotIn("sanctioned-mint-and-double-compile", self.names())
                self.assertNotIn("mint", runner.record["reused"])

    def test_complete_local_stage_uses_owners_and_cannot_admit_or_upload(self):
        original = git(self.repo, "rev-parse", "HEAD")
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        self.assertEqual(record["status"], "local_staged")
        self.assertFalse(record["deployment_ready"])
        self.assertTrue(record["deployment_requirements"])
        self.assertEqual(record["source_commit"], original)
        self.assertEqual(git(self.repo, "symbolic-ref", "HEAD"), "refs/heads/main")
        self.assertEqual(git(self.repo, "status", "--porcelain"), "")
        self.assertEqual(git(self.aterm, "status", "--porcelain"), "")
        self.assertFalse((self.state / "rustup/toolchains/trust").exists())
        self.assertIn("sanctioned-mint-and-double-compile", self.names())
        for name, argv, env in self.owners.calls:
            self.assertNotIn("--upload", argv)
            self.assertNotIn("--publish", argv)
            self.assertNotIn("cargo", argv)
            if "recreate_bootstrap.py" in " ".join(argv):
                self.assertNotIn("RUSTUP_HOME", env)
                self.assertNotIn("CARGO_HOME", env)
            elif name != "locked-dependency-prewarm":
                self.assertEqual(env["RUSTUP_HOME"], str(self.state / "rustup"))
            if name in {"sanctioned-mint-and-double-compile", "seal-without-admission", "trust-wp-drivers"} or name.startswith("unsigned-"):
                self.assertEqual(argv[1], "--")  # build-slot admission
            if name.startswith("unsigned-"):
                self.assertIn("--unsigned", argv)
                if "pack" in argv:
                    self.assertEqual(Path(argv[argv.index("--out") + 1]), Path(record["packages"]))
            if name == "seal-without-admission":
                self.assertIn("--no-flip", argv)
                self.assertIn("--require-llvm-identity", argv)
        self.assertEqual(json.loads((self.state / "latest.json").read_text())["status"], "local_staged")
        for name in ("trust", "trust-ir", "trust-cg", "trust-vc"):
            directory = Path(record["packages"]) / name
            self.assertTrue(list(directory.glob("pkg-*.toml")), name)
            self.assertTrue(list(directory.glob("*.tar.zst")), name)
            self.assertFalse((directory / name).exists(), name)

    def test_promotion_alone_gets_the_selected_serial_command(self):
        # promote-toolchain.sh refuses before any gate without the variable, and
        # the runner removes every ambient TRUST_* setting: until 2026-11-14 the
        # seal step could only refuse, after the whole mint.
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        promotion = {"seal-without-admission", "staged-ui-and-tool-start"}
        seen = set()
        for name, _argv, env in self.owners.calls:
            if name in promotion:
                seen.add(name)
                self.assertEqual(env.get("TRUST_TOOLCHAIN_SERIAL_COMMAND"), str(self.serial), name)
            else:
                self.assertNotIn("TRUST_TOOLCHAIN_SERIAL_COMMAND", env, name)
        self.assertEqual(seen, promotion)
        self.assertEqual(record["settings"]["serial_command"],
                         {"path": str(self.serial), "sha256": stage.file_hash(self.serial)})

    def test_a_serial_command_promotion_would_refuse_stops_before_any_build(self):
        link = self.root / "serial/link"
        link.symlink_to(self.serial)
        plain = self.root / "serial/not-executable"
        plain.write_text("#!/bin/sh\nexit 0\n")
        plain.chmod(0o644)
        for index, bad in enumerate(("serial/trust-serial-command", str(link), str(plain),
                                     str(self.root / "serial/absent"), str(self.root / "serial"))):
            with self.subTest(bad=bad):
                self.state = self.root / f"state-refused-{index}"
                self.owners = Owners()
                result, record = self.run_pipeline("--serial-command", bad)
                self.assertEqual(result, 1)
                self.assertIn("serial command must be the absolute path of a regular executable file, not a link",
                              record["error"])
                self.assertEqual([name for name in self.names() if name != "fetch-main"], [])

    def test_the_default_serial_command_is_the_one_on_path_with_a_link_followed(self):
        bin_directory = self.root / "path-bin"
        bin_directory.mkdir()
        (bin_directory / "trust-serial-command").symlink_to(self.serial)
        runner = stage.Runner(self.arguments("--serial-command-from-path", "--aterm-repo", str(self.aterm)), self.owners)
        runner.env["PATH"] = f"{bin_directory}:/usr/bin:/bin"
        self.assertEqual(runner.run(), 0, runner.record.get("error"))
        self.assertEqual(runner.record["settings"]["serial_command"]["path"], str(self.serial))
        self.state = self.root / "state-no-serial"
        self.owners = Owners()
        runner = stage.Runner(self.arguments("--serial-command-from-path"), self.owners)
        runner.env["PATH"] = "/usr/bin:/bin"
        self.assertEqual(runner.run(), 1)
        self.assertIn("none is on PATH; pass --serial-command", runner.record["error"])
        self.assertNotIn("sanctioned-mint-and-double-compile", self.names())

    def test_a_serial_command_replaced_during_staging_refuses_the_result(self):
        def replace_after_packages(argv, cwd, env, log, timeout=None, **kwargs):
            result = Owners.__call__(self.owners, argv, cwd, env, log, timeout, **kwargs)
            if log.stem.split("-", 1)[1] == "unsigned-trust-vc-package":
                self.serial.write_text("#!/bin/sh\nexit 1\n")
            return result
        runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), replace_after_packages)
        self.assertEqual(runner.run(), 1)
        self.assertEqual(runner.record["error"], "promotion's serial command changed during staging")

    def test_unsigned_package_family_uses_optimized_selected_producer(self):
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        staged = Path(record["staged_toolchain"])
        source = self.state / "source"
        producer = self.state / "aterm-source"
        packages = Path(record["packages"])
        target = self.state / "targets" / record["package_producer"]["commit"] / "atpkg-publish.noindex"
        calls = [row for row in self.owners.calls if row[0].startswith("unsigned-")]
        self.assertEqual([row[0] for row in calls], [
            "unsigned-trust-package", "unsigned-trust-ir-package",
            "unsigned-trust-cg-package", "unsigned-trust-vc-package",
        ])
        for name, argv, env in calls:
            with self.subTest(package=name):
                self.assertEqual(argv[1], "--")  # The entire producer stays admitted.
                owner = argv.index("_owned-command")
                self.assertEqual(Path(argv[owner + 1]), self.state / "publication-source")
                self.assertEqual(argv[owner + 4], "--")
                command = argv[owner + 5:]
                self.assertEqual(command[:3], [str(staged / "bin/targo"), "--unverified", "run"])
                boundary = command.index("--")
                self.assertEqual(command[3:boundary], [
                    "--release", "--locked", "-q", "--manifest-path",
                    str(producer / "crates/atpkg-publish/Cargo.toml"),
                ])
                self.assertEqual(Path(env["RUSTC"]), staged / "bin/trustc")
                self.assertEqual(Path(env["CARGO_TARGET_DIR"]), target)
                if name == "unsigned-trust-package":
                    expected = ["pack-bundle", "trust", "--sysroot", str(staged),
                                "--src-repo", str(source), "--trust-repo", str(source),
                                "--out", str(packages / "trust"), "--unsigned"]
                else:
                    package = name.removeprefix("unsigned-").removesuffix("-package")
                    expected = ["pack", package, "--checkout", str(source / "first-party" / package),
                                "--toolchain", str(staged / "bin"), "--trust-repo", str(source),
                                "--out", str(packages), "--unsigned"]
                # Exact owner arguments preserve all default compression and gate settings.
                self.assertEqual(command[boundary + 1:], expected)
        self.assertEqual(record["status"], "local_staged")
        self.assertFalse(record["deployment_ready"])

    def test_prewarm_precedes_mint_preflight_and_hands_only_private_cache_to_mint(self):
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        names = self.names()
        self.assertLess(names.index("locked-dependency-prewarm"), names.index("mint-preflight"))
        call = next(row for row in self.owners.calls if row[0] == "locked-dependency-prewarm")
        self.assertIn("_owned-command", call[1])
        self.assertNotIn("CARGO_HOME", call[2])
        self.assertNotIn("RUSTUP_HOME", call[2])
        self.assertEqual(self.owners.timeouts[call[0]], stage.DEPENDENCY_PREWARM_SECONDS)
        report = stage.read_json(Path(record["dependency_preparation"]["report"]))
        self.assertTrue(report["completed_fetches"][-1]["offline"])
        expected = record["dependency_preparation"]["cargo_home"]
        self.assertTrue(Path(expected).is_relative_to(self.state / "dependencies" / record["source_commit"] / "mint-inputs"))
        for name, argv, _env in self.owners.calls:
            if name in {"mint-preflight", "sanctioned-mint-and-double-compile"}:
                self.assertEqual(argv[argv.index("--cargo-home") + 1], expected)
                self.assertEqual(argv[argv.index("--clean-lean-lib") + 1], record["clean_lean_inputs"]["library_path"])

    def test_failed_fetch_retains_evidence_and_does_not_start_mint(self):
        self.owners.fail = "locked-dependency-prewarm"
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 1)
        self.assertFalse(record["deployment_ready"])
        self.assertNotIn("mint-preflight", self.names())
        self.assertTrue(Path(record["steps"][-1]["log"]).exists())
        self.owners.fail = None
        self.assertEqual(self.run_pipeline("--aterm-repo", str(self.aterm))[0], 0)

    def test_modified_seed_or_fetch_receipt_refuses_completed_mint_reuse(self):
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        receipt = Path(record["dependency_preparation"]["report"])
        receipt.write_text("{}")
        self.owners.calls.clear()
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 1)
        self.assertIn("dependency preparation input changed", record["error"])
        self.assertNotIn("sanctioned-mint-and-double-compile", self.names())

    def test_successful_reuse_rehashes_and_runs_gates_again(self):
        self.assertEqual(self.run_pipeline("--aterm-repo", str(self.aterm))[0], 0)
        self.owners.calls.clear()
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        self.assertIn("mint", record["reused"])
        self.assertIn("staged-toolchain", record["reused"])
        self.assertNotIn("sanctioned-mint-and-double-compile", self.names())
        self.assertNotIn("seal-without-admission", self.names())
        self.assertNotIn("trust-wp-drivers", self.names())
        self.assertIn("staged-ui-and-tool-start", self.names())
        self.assertIn("llvm-and-build-provenance", self.names())

    def test_changed_artifact_refuses_reuse_and_preserves_it(self):
        _, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        staged = Path(record["staged_toolchain"])
        (staged / "bin/trustc").write_text("changed")
        self.owners.calls.clear()
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 1)
        self.assertIn("staged-toolchain artifacts changed", record["error"])
        self.assertFalse(record["deployment_ready"])
        self.assertEqual((staged / "bin/trustc").read_text(), "changed")
        self.assertNotIn("trust-wp-drivers", self.names())

    def test_llvm_owner_refusal_is_failure_and_mint_checkpoint_survives(self):
        self.owners.fail = "llvm-and-build-provenance"
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 1)
        self.assertEqual(record["status"], "failed")
        self.assertNotIn("seal-without-admission", self.names())
        self.assertIn("fake llvm-and-build-provenance failure", record["error"])
        self.assertTrue(list((self.state / "source/build").glob("pack-mint-*")))
        self.owners.fail = None
        self.owners.calls.clear()
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        self.assertIn("mint", record["reused"])
        self.assertNotIn("sanctioned-mint-and-double-compile", self.names())

    def test_missing_package_producer_retains_stage_and_reports_missing_gate(self):
        result, record = self.run_pipeline()
        self.assertEqual(result, 1)
        self.assertTrue(Path(record["staged_toolchain"]).is_dir())
        self.assertIn("--aterm-repo", record["error"])
        self.assertFalse(record["deployment_ready"])
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        self.assertIn("staged-toolchain", record["reused"])

    def test_failed_gate_never_reports_local_stage(self):
        self.owners.fail = "staged-ui-and-tool-start"
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 1)
        self.assertEqual(record["status"], "failed")
        self.assertFalse(record["deployment_ready"])
        self.assertFalse(any(name.startswith("unsigned-") for name in self.names()))
        self.assertTrue(Path(record["steps"][-1]["log"]).exists())

    def test_library_surface_failure_cannot_report_a_staged_toolchain(self):
        self.owners.fail = "sysroot-library-contract"
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 1)
        self.assertEqual(record["status"], "failed")
        self.assertFalse(record["deployment_ready"])
        self.assertFalse(any(name.startswith("unsigned-") for name in self.names()))

    def test_full_stage_checks_host_libraries_before_semantic_gates(self):
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        names = self.names()
        self.assertLess(names.index("toolchain-output-contract"), names.index("sysroot-library-contract"))
        self.assertLess(names.index("sysroot-library-contract"), names.index("staged-ui-and-tool-start"))
        argv = next(argv for name, argv, _ in self.owners.calls if name == "sysroot-library-contract")
        self.assertIn("verify_sysroot_libraries.py", " ".join(argv))
        self.assertEqual(argv[argv.index("--target") + 1], HOST)

    def test_prepare_has_pinned_llvm_build_but_no_mint_or_package(self):
        result, record = self.run_pipeline("--mode", "prepare")
        self.assertEqual(result, 0, record.get("error"))
        self.assertEqual(record["status"], "prepared")
        self.assertFalse(record["deployment_ready"])
        self.assertNotIn("sanctioned-mint-and-double-compile", self.names())
        build = next(argv for name, argv, _ in self.owners.calls if name == "pinned-bootstrap")
        for option in ("--require-seed", "--fresh-seed", "--no-atpkg", "--no-register", "--require-llvm-identity"):
            self.assertIn(option, build)

    def test_latest_remote_main_is_selected_without_moving_callers_branch(self):
        self.assertEqual(self.run_pipeline("--aterm-repo", str(self.aterm))[0], 0)
        (self.repo / "README").write_text("new source")
        git(self.repo, "add", "README")
        git(self.repo, "commit", "-qm", "latest")
        latest = git(self.repo, "rev-parse", "HEAD")
        git(self.repo, "push", "origin", "main")
        # The controller need not have main checked out.
        git(self.repo, "checkout", "--detach", "HEAD~1")
        controller = git(self.repo, "rev-parse", "HEAD")
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        self.assertEqual(record["source_commit"], latest)
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), controller)

    def test_private_fetch_preserves_remote_tracking_refs_head_and_fetch_head(self):
        # A normal remote fetch map must be present: without --refmap= Git
        # opportunistically updates origin/main even with an explicit destination.
        self.assertEqual(git(self.repo, "config", "remote.origin.fetch"),
                         "+refs/heads/*:refs/remotes/origin/*")
        git(self.repo, "fetch", "origin")
        original = git(self.repo, "rev-parse", "HEAD")
        branch = git(self.repo, "symbolic-ref", "HEAD")
        fetch_head = self.repo / ".git/FETCH_HEAD"
        fetch_head_bytes = fetch_head.read_bytes()
        runner = stage.Runner(self.arguments())
        runner.invocation = self.state / "runs/snapshot"
        runner.invocation.mkdir(parents=True)
        runner.record = {"steps": []}
        self.assertEqual(runner.snapshot(self.repo, runner.source, "trust"), original)
        caller_refs = git(self.repo, "for-each-ref", "--format=%(refname) %(objectname)")
        fetch = next(step for step in runner.record["steps"]
                     if step["name"] == "fetch-main" and step["cwd"] == str(runner.source))
        private_ref = fetch["argv"][-1].split(":", 1)[1]
        self.assertTrue(private_ref.startswith("refs/agh/trust-daily-staging/"))
        self.assertEqual(git(runner.source, "rev-parse", private_ref), original)

        # Only a separate writer advances the remote; the controller stays put.
        writer = self.root / "writer"
        remote = self.root / "trust.git"
        subprocess.run(["git", "clone", "-q", str(remote), str(writer)], check=True)
        for key, value in (("user.name", "fixture"), ("user.email", "fixture@example.invalid"),
                           ("core.hooksPath", "/dev/null"), ("commit.gpgsign", "false")):
            git(writer, "config", key, value)
        (writer / "README").write_text("new remote source")
        git(writer, "add", "README")
        git(writer, "commit", "-qm", "advance remote main")
        latest = git(writer, "rev-parse", "HEAD")
        git(writer, "push", "origin", "main")
        self.assertNotEqual(latest, original)

        self.assertEqual(runner.snapshot(self.repo, runner.source, "trust"), latest)
        self.assertEqual(git(runner.source, "rev-parse", private_ref), latest)
        self.assertEqual(git(self.repo, "for-each-ref", "--format=%(refname) %(objectname)"), caller_refs)
        self.assertEqual(git(self.repo, "rev-parse", "refs/remotes/origin/main"), original)
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), original)
        self.assertEqual(git(self.repo, "symbolic-ref", "HEAD"), branch)
        self.assertEqual(fetch_head.read_bytes(), fetch_head_bytes)

        # A real failed fetch cannot become a cached success or move any refs.
        remote.rename(self.root / "unavailable-remote.git")
        with self.assertRaises(stage.CommandFailed):
            runner.snapshot(self.repo, runner.source, "trust")
        failure = [step for step in runner.record["steps"] if step["name"] == "fetch-main"][-1]
        self.assertEqual(failure["status"], "failed")
        self.assertNotEqual(failure["exit_code"], 0)
        self.assertEqual(git(runner.source, "rev-parse", private_ref), latest)
        self.assertEqual(git(self.state / "source", "rev-parse", "HEAD"), latest)
        self.assertEqual(git(self.repo, "rev-parse", "refs/remotes/origin/main"), original)
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), original)
        self.assertEqual(git(self.repo, "symbolic-ref", "HEAD"), branch)
        self.assertEqual(fetch_head.read_bytes(), fetch_head_bytes)

    def snapshot_runner(self):
        runner = stage.Runner(self.arguments())
        runner.invocation = self.state / "runs/snapshot"
        runner.invocation.mkdir(parents=True)
        runner.record = {"steps": []}
        return runner

    def test_named_source_commit_is_held_while_main_moves_and_must_be_on_main(self):
        start = git(self.repo, "rev-parse", "HEAD")
        def snapshot(*extra):
            runner = stage.Runner(self.arguments(*extra))
            runner.invocation = self.state / "runs/snapshot"
            runner.invocation.mkdir(parents=True, exist_ok=True)
            runner.record = {"steps": []}
            return runner, runner.snapshot(self.repo, runner.source, "trust")
        runner, commit = snapshot("--source-commit", start)
        self.assertEqual((commit, runner.record["source_main"]), (start, start))

        writer = self.root / "writer"
        subprocess.run(["git", "clone", "-q", str(self.root / "trust.git"), str(writer)], check=True)
        for key, value in (("user.name", "fixture"), ("user.email", "fixture@example.invalid"),
                           ("core.hooksPath", "/dev/null"), ("commit.gpgsign", "false")):
            git(writer, "config", key, value)
        (writer / "README").write_text("main moved under the cut")
        git(writer, "commit", "-qam", "advance remote main")
        moved = git(writer, "rev-parse", "HEAD")
        git(writer, "push", "origin", "main")
        # A commit that origin has, but that is not on its main, is not selectable.
        git(writer, "checkout", "-qb", "side", start)
        (writer / "README").write_text("a side branch")
        git(writer, "commit", "-qam", "not on main")
        side = git(writer, "rev-parse", "HEAD")
        git(writer, "push", "origin", "side")

        # The restarted cut stays on the commit it started on; main's new tip is recorded, not built.
        runner, commit = snapshot("--source-commit", start)
        self.assertEqual((commit, runner.record["source_main"]), (start, moved))
        self.assertEqual(git(runner.source, "rev-parse", "HEAD"), start)
        self.assertEqual((runner.source / "README").read_text(), "trust")

        for refused, reason in ((side, "is not on origin/main"), ("0" * len(start), "is not on origin/main"),
                                (start[:12], "full lowercase commit id"), (start.upper(), "full lowercase commit id")):
            with self.assertRaisesRegex(stage.Refused, reason):
                snapshot("--source-commit", refused)
            self.assertEqual(git(runner.source, "rev-parse", "HEAD"), start)

        # Without the option the same state root follows main, and it never goes back.
        self.assertEqual(snapshot()[1], moved)
        with self.assertRaises(stage.CommandFailed):
            snapshot("--source-commit", start)
        self.assertEqual(git(runner.source, "rev-parse", "HEAD"), moved)

        # A train reads main itself.
        with mock.patch("sys.stderr") as stderr, self.assertRaises(SystemExit) as refused:
            stage.main(["train", "--source-commit", start])
        self.assertEqual(refused.exception.code, 2)
        self.assertIn("--source-commit belongs to run", "".join(call.args[0] for call in stderr.write.call_args_list))

    def test_developer_execution_config_stays_with_caller_and_real_recreator_audit_passes(self):
        git(self.repo, "config", "core.hooksPath", "scripts/hooks")
        git(self.repo, "config", "core.sshCommand", "/usr/bin/false")
        recreator = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")), run_name="fixture_git_authority")
        with self.assertRaisesRegex(RuntimeError, "local:core.hookspath.*local:core.sshcommand"):
            recreator["_run_git_read"](self.repo, ["ls-files", "--stage", "--", ".gitmodules"])
        paths = [self.repo / ".git/config", self.repo / ".git/index", self.repo / ".git/HEAD"]
        before = [path.read_bytes() for path in paths]
        refs = git(self.repo, "for-each-ref", "--format=%(refname) %(objectname)")
        runner = self.snapshot_runner()
        commit = runner.snapshot(self.repo, runner.source, "trust")
        self.assertEqual(recreator["_run_git_read"](runner.source, ["ls-files", "--stage", "--", ".gitmodules"]).returncode, 0)
        self.assertEqual([path.read_bytes() for path in paths], before)
        self.assertEqual(git(self.repo, "for-each-ref", "--format=%(refname) %(objectname)"), refs)
        self.assertTrue((runner.source / ".git").is_dir())
        self.assertEqual(git(runner.source, "rev-parse", "--absolute-git-dir"), str(runner.source / ".git"))
        self.assertFalse((runner.source / ".git/objects/info/alternates").exists())
        # Neither the caller nor the remote must remain live to supply objects.
        self.repo.rename(self.root / "caller-retained")
        (self.root / "trust.git").rename(self.root / "remote-retained")
        self.assertEqual(git(runner.source, "rev-parse", "HEAD"), commit)
        self.assertEqual(git(runner.source, "cat-file", "-t", commit), "commit")

    def test_legacy_shared_snapshot_requires_fresh_state_and_preserves_evidence(self):
        runner = self.snapshot_runner()
        git(self.repo, "worktree", "add", "--detach", str(runner.source), "HEAD")
        marker = runner.source.with_name("source.owner.json")
        marker.write_text(json.dumps({"schema": stage.SCHEMA, "git_common_dir": str(self.repo / ".git"), "path": str(runner.source)}))
        checkpoint = self.state / "checkpoints/prior.json"
        checkpoint.parent.mkdir();checkpoint.write_text('{"prior":"keep"}\n')
        before = stage.fingerprint(runner.source), marker.read_bytes(), checkpoint.read_bytes()
        with self.assertRaisesRegex(stage.Refused, "fresh --state-root"):
            runner.snapshot(self.repo, runner.source, "trust")
        self.assertEqual((stage.fingerprint(runner.source), marker.read_bytes(), checkpoint.read_bytes()), before)

    def test_resumed_snapshot_rejects_execution_config_and_shared_object_custody(self):
        runner = self.snapshot_runner()
        runner.snapshot(self.repo, runner.source, "trust")
        git_dir = runner.source / ".git"
        git(runner.source, "config", "core.sshCommand", "/usr/bin/false")
        with self.assertRaisesRegex(stage.Refused, "unowned authority"):
            runner.snapshot(self.repo, runner.source, "trust")
        git(runner.source, "config", "--unset", "core.sshCommand")
        git(runner.source, "config", "--add", "remote.origin.url", str(self.root / "unowned"))
        with self.assertRaisesRegex(stage.Refused, "duplicate authority"):
            runner.snapshot(self.repo, runner.source, "trust")
        git(runner.source, "config", "--unset-all", "remote.origin.url")
        git(runner.source, "config", "remote.origin.url", str(self.root / "trust.git"))
        executable(git_dir / "hooks/post-checkout", "#!/bin/sh\nexit 7\n")
        with self.assertRaisesRegex(stage.Refused, "unowned Git hooks"):
            runner.snapshot(self.repo, runner.source, "trust")
        (git_dir / "hooks/post-checkout").unlink()
        alternate = git_dir / "objects/info/alternates"
        alternate.write_text(str(self.repo / ".git/objects") + "\n")
        with self.assertRaisesRegex(stage.Refused, "alternates"):
            runner.snapshot(self.repo, runner.source, "trust")
        alternate.unlink()
        http_alternate = git_dir / "objects/info/http-alternates"
        http_alternate.write_text("https://unowned.example/objects\n")
        with self.assertRaisesRegex(stage.Refused, "alternates"):
            runner.snapshot(self.repo, runner.source, "trust")
        http_alternate.unlink()
        config = git_dir / "config"; original_config = config.read_bytes();config.unlink();os.mkfifo(config)
        try:
            def no_git_query(*_args):
                self.fail("nonregular Git config must refuse before any query can block")
            with self.assertRaisesRegex(stage.Refused, "nonregular"):
                runner.snapshot_custody(runner.source, str(self.root / "trust.git"), no_git_query)
        finally:
            config.unlink();config.write_bytes(original_config)
        outside = self.root / "shared-git-file";outside.write_text("unowned")
        os.link(outside, git_dir / "shared-file")
        with self.assertRaisesRegex(stage.Refused, "shared file"):
            runner.snapshot(self.repo, runner.source, "trust")

    def test_snapshot_ignores_ambient_global_execution_config_and_rejects_remote_helpers(self):
        hostile = self.root / "global-config"
        sentinel = self.root / "must-not-execute"
        hostile.write_text('[core]\nsshCommand = touch ' + str(sentinel) + '\nhooksPath = /unowned\n')
        with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": str(hostile)}):
            runner = self.snapshot_runner()
            runner.snapshot(self.repo, runner.source, "trust")
        self.assertFalse(sentinel.exists())

        git(self.repo, "config", "remote.origin.url", "ext::touch " + str(sentinel))
        with self.assertRaisesRegex(stage.Refused, "remote helper"):
            runner.snapshot(self.repo, runner.source, "trust")
        self.assertFalse(sentinel.exists())

    def test_https_snapshot_uses_owner_routed_agh_without_a_credential_helper(self):
        api = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")), run_name="fixture_https_authority")
        client = self.root / "fixture-agh"
        executable(client)
        selected = dict(api)
        real_fetch = api["_agh_source_fetch"]
        def acquire(*args, **kwargs):
            with mock.patch.dict(real_fetch.__globals__, {"which": lambda name: str(client) if name == "agh" else None}):
                return real_fetch(*args, **kwargs)
        selected["_agh_source_fetch"] = acquire
        selected["_submodule_auth_config"] = mock.Mock(side_effect=AssertionError("legacy credentials must not be selected"))
        git(self.repo, "config", "remote.origin.url", "git@github.com:fixture/snapshot.git")
        runner = self.snapshot_runner()
        observed = []
        def execute(argv, cwd, env, log, **kwargs):
            actual = list(argv)
            if argv[0] == str(client):
                observed.append((list(argv), dict(env)))
                self.assertEqual(argv[1:4], ["repo", "fetch", "fixture/snapshot"])
                self.assertEqual(argv[5:8], ["--ref", "refs/heads/main", "--into"])
                self.assertTrue(argv[8].startswith("refs/agh/"))
                # Only this test executor substitutes its local Git server.
                # No private-network authentication claim is made here.
                actual = ["git", "-c", "protocol.file.allow=always", "-C", argv[4],
                          "fetch", "--no-tags", str(self.root / "trust.git"),
                          "refs/heads/main:" + argv[8]]
            elif "fetch" in argv and any("github.com" in arg for arg in argv):
                self.fail("raw GitHub Git fallback must not run")
            return stage.command(actual, cwd, env, log, **kwargs)
        runner.execute = execute
        with mock.patch.object(stage.runpy, "run_path", return_value=selected):
            commit = runner.snapshot(self.repo, runner.source, "trust")
        self.assertEqual(git(runner.source, "rev-parse", "HEAD"), commit)
        self.assertEqual(git(runner.source, "remote", "get-url", "origin"), "https://github.com/fixture/snapshot.git")
        self.assertEqual(len(observed), 1)
        selected["_submodule_auth_config"].assert_not_called()
        _, env = observed[0]
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(env["GIT_TERMINAL_PROMPT"], "0")
        self.assertNotIn("GH_TOKEN", env)
        self.assertNotIn("GITHUB_TOKEN", env)
        receipts = list(runner.invocation.glob("*-trust-source-acquisition.json"))
        self.assertEqual(len(receipts), 1)
        self.assertEqual(json.loads(receipts[0].read_text())["commit"], commit)
        self.assertFalse(list(runner.invocation.glob("snapshot-credential-*")))

    def test_snapshot_refuses_query_and_fragment_before_logging_or_origin_creation(self):
        runner = self.snapshot_runner()
        for suffix in ("?access_token=FIXTURE_NONSECRET_QUERY", "#FIXTURE_NONSECRET_FRAGMENT"):
            with self.subTest(suffix=suffix):
                origin = "https://github.com/fixture/snapshot.git" + suffix
                git(self.repo, "config", "remote.origin.url", origin)
                with self.assertRaisesRegex(stage.Refused, "query or fragment"):
                    runner.snapshot(self.repo, runner.source, "trust")
                self.assertFalse(runner.source.exists())
                self.assertFalse(any(step["name"] == "source-origin" for step in runner.record["steps"]))
                for log in runner.invocation.glob("*.log"):
                    self.assertNotIn("FIXTURE_NONSECRET", log.read_text())
                self.assertEqual(git(self.repo, "config", "remote.origin.url"), origin)

    def global_fsmonitor(self):
        sentinel = self.root / "GLOBAL_FS_MONITOR_MUST_NOT_RUN"
        helper = self.root / "fixture-fsmonitor"
        executable(helper, "#!/bin/sh\nprintf called > " + shlex.quote(str(sentinel)) + "\nexit 0\n")
        config = self.root / "fixture-global-git-config"
        config.write_text("[core]\nfsmonitor = " + str(helper) + "\n")
        return config, sentinel

    def test_managed_clean_and_policy_queries_ignore_ambient_global_git_execution(self):
        config, sentinel = self.global_fsmonitor()
        with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": str(config)}):
            runner = self.snapshot_runner()
            runner.clean(self.repo)
            self.assertEqual(runner.git("fixture-policy", self.repo, "rev-parse", "HEAD"), git(self.repo, "rev-parse", "HEAD"))
        self.assertFalse(sentinel.exists())
        self.assertIn("fsmonitor", config.read_text())

    def test_synchronizer_shell_git_uses_closed_owner_shim_and_preserves_caller_settings(self):
        # Actual production synchronize() executes a fixture synchronizer whose
        # bare Git invocation exposes the shell boundary without network access.
        (self.repo / ".gitmodules").write_text("")
        executable(self.repo / "scripts/submodule_sync.sh", "#!/bin/sh\nset -eu\ngit -C \"$2\" status --porcelain\n")
        git(self.repo, "add", ".gitmodules", "scripts/submodule_sync.sh")
        git(self.repo, "commit", "-qm", "fixture synchronizer")
        git(self.repo, "push", "origin", "main")
        config, sentinel = self.global_fsmonitor()
        api = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")), run_name="fixture_sync_git_authority")
        selected = dict(api)
        selected["_submodule_auth_config"] = mock.Mock(side_effect=AssertionError("legacy credentials must not be selected"))
        with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": str(config)}):
            runner = self.snapshot_runner()
            with mock.patch.object(stage.runpy, "run_path", return_value=selected):
                runner.snapshot(self.repo, runner.source, "trust")
            self.assertEqual(runner.synchronize(runner.source, "fixture"), "")
        self.assertFalse(sentinel.exists())
        selected["_submodule_auth_config"].assert_not_called()
        shims = list(runner.invocation.glob("managed-git-*/bin/git"))
        self.assertEqual(len(shims), 1)
        self.assertIn("exec /usr/bin/env -i", shims[0].read_text())
        self.assertIn("protocol.https.allow=never", shims[0].read_text())
        self.assertIn("GIT_NO_LAZY_FETCH=1", shims[0].read_text())
        refused = subprocess.run([str(shims[0]), "ls-remote", str(self.root / "trust.git")],
                                 capture_output=True, text=True, timeout=30)
        self.assertNotEqual(refused.returncode, 0)
        self.assertIn("transport 'file' not allowed", refused.stderr)
        self.assertTrue(any("--offline" in step["argv"] for step in runner.record["steps"]
                            if step["name"] == "submodule-sync"))
        self.assertIn("fsmonitor", config.read_text())

    def test_missing_pin_is_acquired_without_moving_existing_child_before_offline_restore(self):
        server = self.root / "pin-server"
        server.mkdir()
        git(server, "init", "--quiet", "--template=", "--initial-branch=main")
        git(server, "config", "user.name", "fixture")
        git(server, "config", "user.email", "fixture@example.invalid")
        (server / "value").write_text("old")
        git(server, "add", "value")
        git(server, "commit", "-qm", "old")
        old = git(server, "rev-parse", "HEAD")
        previous = self.root / "old-pin-source"
        subprocess.run(["git", "clone", "--quiet", "--no-hardlinks", str(server), str(previous)], check=True)
        (server / "value").write_text("new")
        git(server, "commit", "-qam", "new")
        target = git(server, "rev-parse", "HEAD")
        url = "https://github.com/fixture/pin.git"
        (self.repo / ".gitmodules").write_text(
            '[submodule "fixture"]\n\tpath = first-party/fixture\n\turl = ' + url + '\n')
        shutil.copy2(SCRIPT.with_name("submodule_sync.sh"), self.repo / "scripts/submodule_sync.sh")
        git(self.repo, "add", ".gitmodules", "scripts/submodule_sync.sh")
        git(self.repo, "update-index", "--add", "--cacheinfo", "160000", target, "first-party/fixture")
        git(self.repo, "commit", "-qm", "select new child pin")
        git(self.repo, "push", "origin", "main")
        runner = self.snapshot_runner()
        runner.snapshot(self.repo, runner.source, "trust")
        child = runner.source / "first-party/fixture"
        subprocess.run(["git", "clone", "--quiet", "--no-hardlinks", str(previous), str(child)], check=True)
        git(child, "config", "remote.origin.url", url)
        original_index = git(runner.source, "write-tree")
        owner = runner.git_owner()
        real_fetch = owner["_agh_source_fetch"]
        client = self.root / "fixture-pin-agh"
        executable(client)
        acquired = []
        def execute(argv, cwd, env, log, **kwargs):
            if argv[0] == str(client):
                acquired.append(list(argv))
                self.assertEqual(argv[1:7], ["repo", "fetch", "fixture/pin", str(child), "--ref", target])
                self.assertEqual(git(child, "rev-parse", "HEAD"), old)
                argv = [*owner["_controlled_git_command"]([]), "-c", "protocol.file.allow=always",
                        "-C", str(child), "fetch", "--quiet", "--no-tags", "--recurse-submodules=no",
                        str(server), target + ":" + argv[8]]
            elif "fetch" in argv and any("github.com" in arg for arg in argv):
                self.fail("direct GitHub transport must not run")
            return stage.command(argv, cwd, env, log, **kwargs)
        runner.execute = execute
        with mock.patch.dict(real_fetch.__globals__, {"which": lambda name: str(client) if name == "agh" else None}):
            runner.acquire_submodule_pins(runner.source, "fixture", 0)
            self.assertEqual(git(child, "rev-parse", "HEAD"), old)
            self.assertEqual(git(runner.source, "write-tree"), original_index)
            self.assertEqual(len(acquired), 1)
            runner.synchronize(runner.source, "fixture")
        self.assertEqual(git(child, "rev-parse", "HEAD"), target)
        self.assertEqual(git(previous, "rev-parse", "HEAD"), old)
        self.assertEqual(len(acquired), 1)
        self.assertEqual(git(runner.source, "write-tree"), original_index)

    def test_a_declared_source_object_cache_reaches_only_the_trust_source(self):
        url = "https://github.com/fixture/pin.git"
        (self.repo / ".gitmodules").write_text(
            '[submodule "fixture"]\n\tpath = first-party/fixture\n\turl = ' + url + '\n')
        git(self.repo, "add", ".gitmodules")
        git(self.repo, "update-index", "--add", "--cacheinfo", "160000", "1" * 40, "first-party/fixture")
        git(self.repo, "commit", "-qm", "index a first-party child")
        git(self.repo, "push", "origin", "main")
        cache = self.root / "fixture-cache"
        cache.mkdir()
        declaration = f"first-party/fixture={cache}"
        runner = stage.Runner(self.arguments("--source-object-cache", declaration))
        runner.invocation = self.state / "runs/cache"
        runner.invocation.mkdir(parents=True)
        runner.record = {"steps": []}
        runner.snapshot(self.repo, runner.source, "trust")
        owner = runner.git_owner()
        seen = []
        owner["ensure_submodules"] = lambda path, **options: seen.append((path, options))
        owner["_inspect_submodule_tree"] = lambda path: []
        runner.acquire_submodule_pins(runner.source, "source", 0)
        # The publication and package-producer snapshots have no first-party gitlinks.
        runner.acquire_submodule_pins(runner.source, "publication", 1)
        self.assertEqual(seen, [(runner.source, {"checkout_caches": {"first-party/fixture": cache}}),
                                (runner.source, {})])
        # A declaration the source's index does not name refuses before any acquisition.
        runner.args.source_object_cache = [f"first-party/absent={cache}"]
        with self.assertRaisesRegex(RuntimeError, "source object cache must name one indexed first-party path"):
            runner.acquire_submodule_pins(runner.source, "source", 2)
        self.assertEqual(len(seen), 2)
        # The train's agent carries the declaration to each tick.
        words = stage.train_plist(self.train_arguments("--source-object-cache", declaration))["ProgramArguments"]
        self.assertEqual(words[words.index("--source-object-cache") + 1], declaration)

    def test_dirty_managed_worktree_is_never_overwritten(self):
        self.run_pipeline("--mode", "prepare")
        work = self.state / "source/README"
        work.write_text("uncommitted work")
        result, record = self.run_pipeline("--mode", "prepare")
        self.assertEqual(result, 1)
        self.assertIn("dirty managed worktree", record["error"])
        self.assertEqual(work.read_text(), "uncommitted work")

    def test_rewritten_remote_history_is_refused_without_moving_managed_source(self):
        (self.repo / "README").write_text("second commit")
        git(self.repo, "add", "README")
        git(self.repo, "commit", "-qm", "second")
        git(self.repo, "push", "origin", "main")
        self.assertEqual(self.run_pipeline("--mode", "prepare")[0], 0)
        current = git(self.state / "source", "rev-parse", "HEAD")
        previous = git(self.repo, "rev-parse", "HEAD~1")
        git(self.root / "trust.git", "update-ref", "refs/heads/main", previous)
        result, record = self.run_pipeline("--mode", "prepare")
        self.assertEqual(result, 1)
        self.assertEqual(record["status"], "failed")
        self.assertEqual(git(self.state / "source", "rev-parse", "HEAD"), current)

    def test_existing_unowned_worktree_is_refused(self):
        (self.state / "source").mkdir(parents=True)
        (self.state / "source/evidence").write_text("keep")
        result, record = self.run_pipeline()
        self.assertEqual(result, 1)
        self.assertIn("not owned", record["error"])
        self.assertEqual((self.state / "source/evidence").read_text(), "keep")

    def test_lock_rejects_second_runner_without_replacing_status(self):
        with stage.single_run(self.state):
            sentinel = {"active": "keep"}
            stage.atomic_json(self.state / "latest.json", sentinel)
            runner = stage.Runner(self.arguments(), self.owners)
            with self.assertRaisesRegex(stage.Refused, "another daily staging run"):
                runner.run()
            self.assertEqual(json.loads((self.state / "latest.json").read_text()), sentinel)

    def test_train_agent_uses_absolute_python_and_paths_and_ticks_every_hour(self):
        data = stage.train_plist(self.train_arguments())
        argv = data["ProgramArguments"]
        self.assertEqual(argv[:4], [str(Path(sys.executable).resolve()), str(SCRIPT), "train", "run"])
        self.assertTrue(Path(argv[0]).is_absolute())
        self.assertEqual((data["Label"], data["StartInterval"], data["RunAtLoad"]),
                         ("systems.alab.trust-train", 3600, True))
        self.assertEqual(data["WorkingDirectory"], str(self.repo))
        self.assertEqual(argv[argv.index("--state-root") + 1], str(self.state))
        self.assertEqual(argv[argv.index("--publisher-host") + 1], "agh-staging")
        self.assertEqual(argv[argv.index("--serial-command") + 1], str(self.serial))
        self.assertFalse(self.state.exists())
        self.assertNotIn("KeepAlive", data)
        self.assertNotIn("StartCalendarInterval", data)
        for interval in ("299", "86401"):
            with self.assertRaisesRegex(stage.Refused, "--interval"):
                stage.train_plist(self.train_arguments("--interval", interval))
        without_publisher = self.train_arguments()
        without_publisher.aterm_repo = None
        with self.assertRaisesRegex(stage.Refused, "--aterm-repo"):
            stage.train_plist(without_publisher)

    def test_private_python_alias_keeps_schedule_owner_commands_on_controller_python(self):
        legacy = self.root / "legacy-bin"
        executable(legacy / "python3", "#!/bin/sh\nprintf '3.9 stale python\\n'\nexit 1\n")
        inherited = str(legacy) + os.pathsep + os.environ["PATH"]
        args = self.arguments("--mode", "prepare")
        with mock.patch.dict(os.environ, {"PATH": inherited}):
            agent_path = stage.train_plist(self.train_arguments())["EnvironmentVariables"]["PATH"]
            runner = stage.Runner(args, self.owners)
            self.assertEqual(runner.run(), 0, runner.record.get("error"))
        # The agent carries the caller's PATH; each tick's runner puts its own python-bin first.
        self.assertEqual(agent_path, runner.env["PATH"].split(os.pathsep, 1)[1])
        self.assertEqual(agent_path.split(os.pathsep)[0], str(legacy))
        selected = shutil.which("python3", path=runner.env["PATH"])
        self.assertEqual(Path(selected).resolve(), Path(sys.executable).resolve())
        subprocess.run([selected, "-I", "-S", "-c", "import sys, tomllib; assert sys.version_info >= (3,11)"],
                       env={**os.environ, "PATH": runner.env["PATH"]}, check=True, capture_output=True)
        self.assertEqual(runner.record["settings"]["python"]["sha256"], stage.file_hash(Path(sys.executable).resolve()))
        self.assertIn("3.9 stale python", (legacy / "python3").read_text())

    def test_ambient_lean_home_is_promoted_to_an_explicit_schedule_input(self):
        elan_home = self.root / "elan-home"
        elan_home.mkdir()
        args = self.train_arguments()
        # This control exercises ambient selection, without the ordinary
        # fixture's explicit default installed home.
        args.elan_home = None
        with mock.patch.dict(os.environ, {"ELAN_HOME": str(elan_home),
                                          "GH_TOKEN": "fixture-secret-not-a-schedule-input"}):
            data = stage.train_plist(args)
            runner = stage.Runner(args, self.owners)
        self.assertEqual(data["EnvironmentVariables"]["ELAN_HOME"], runner.env["ELAN_HOME"])
        argv = data["ProgramArguments"]
        self.assertEqual(argv[argv.index("--elan-home") + 1], str(elan_home))
        self.assertEqual(set(data["EnvironmentVariables"]), {"PATH", "ELAN_HOME"})
        self.assertNotIn(b"fixture-secret", plistlib.dumps(data))

    def test_explicit_lean_home_reaches_every_consumer_and_the_generated_schedule(self):
        elan_home = self.root / "owned elan-home"
        elan_home.mkdir()
        alias = self.root / "elan-alias"
        alias.symlink_to(elan_home, target_is_directory=True)
        arguments, _ = self.consumer_arguments()
        args = self.arguments(*arguments, "--elan-home", str(alias))
        with mock.patch.dict(os.environ, {"ELAN_HOME": str(self.root / "wrong-ambient-home")}):
            runner = stage.Runner(args, self.owners)
            self.assertEqual(runner.run(), 0, runner.record.get("error"))
            data = stage.train_plist(self.train_arguments(*arguments, "--elan-home", str(alias)))
        self.assertEqual(runner.record["settings"]["elan_home"], str(elan_home))
        lean_identity = stage.elan_home_identity(elan_home)
        self.assertEqual(runner.record["settings"]["elan_home_identity"], lean_identity)
        argv = data["ProgramArguments"]
        self.assertEqual(argv[argv.index("--elan-home") + 1], str(elan_home))
        self.assertEqual(data["EnvironmentVariables"]["ELAN_HOME"], str(elan_home))
        for name in stage.CONSUMERS:
            self.assertEqual(runner.record["consumers"][name]["identity"]["elan_home_identity"], lean_identity)
            _, _, environment = next(call for call in self.owners.calls if call[0] == f"{name}-consumer-check")
            self.assertEqual(environment["ELAN_HOME"], str(elan_home))
            # A real child sees the same selected home after owner-policy
            # neutralization, not just the in-memory namespace or plist.
            result = subprocess.run([sys.executable, "-I", "-S", "-c",
                                     "import os; print(os.environ['ELAN_HOME'])"],
                                    env=environment, text=True, capture_output=True, check=True)
            self.assertEqual(result.stdout.strip(), str(elan_home))
        with mock.patch.dict(os.environ, data["EnvironmentVariables"], clear=True):
            scheduled = stage.Runner(stage.parser().parse_args(argv[2:]), self.owners)
        self.assertEqual(scheduled.env["ELAN_HOME"], runner.env["ELAN_HOME"])

    def test_invalid_lean_home_refuses_before_creating_schedule_or_run_state(self):
        regular = self.root / "not-a-directory"
        regular.write_text("not an elan home")
        agents = self.root / "LaunchAgents"
        for path in (regular, self.root / "absent-elan-home"):
            with self.subTest(path=path):
                args = self.arguments("--elan-home", str(path))
                with self.assertRaisesRegex(stage.Refused, "ELAN_HOME"):
                    stage.Runner(args, self.owners)
                with self.assertRaisesRegex(stage.Refused, "ELAN_HOME"):
                    stage.train_install(self.train_arguments("--elan-home", str(path), "--launch-agents", str(agents)),
                                        lambda *_args, **_kwargs: self.fail("launchctl ran"))
                self.assertFalse(agents.exists())
                self.assertFalse(self.state.exists())

    def test_changing_selected_lean_home_invalidates_a_checkpoint(self):
        homes = [self.root / "elan-one", self.root / "elan-two"]
        for home in homes:
            home.mkdir()
        result, first = self.run_pipeline("--mode", "prepare", "--elan-home", str(homes[0]))
        self.assertEqual(result, 0, first.get("error"))
        result, second = self.run_pipeline("--mode", "prepare", "--elan-home", str(homes[1]))
        self.assertEqual(result, 1)
        self.assertIn("checkpoint settings differ", second["error"])
        self.assertEqual(second["status"], "failed")

    def test_replacing_lean_bytes_at_the_same_home_invalidates_a_checkpoint(self):
        home = self.root / "elan-home"
        executable(home / "bin/lean", "#!/bin/sh\necho original\n")
        result, first = self.run_pipeline("--mode", "prepare", "--elan-home", str(home))
        self.assertEqual(result, 0, first.get("error"))
        executable(home / "bin/lean", "#!/bin/sh\necho changed\n")
        result, second = self.run_pipeline("--mode", "prepare", "--elan-home", str(home))
        self.assertEqual(result, 1)
        self.assertIn("checkpoint settings differ", second["error"])

    def test_linked_lean_toolchains_bind_resolved_bytes_without_allowing_nested_escape(self):
        home = self.root / "elan-home"
        installed = self.root / "installed-lean"
        executable(installed / "bin/lean", "#!/bin/sh\necho original\n")
        toolchains = home / "toolchains"
        toolchains.mkdir(parents=True)
        (toolchains / "leanprover--lean4---v4.8.0").symlink_to(installed, target_is_directory=True)
        first = stage.elan_home_identity(home)
        executable(installed / "bin/lean", "#!/bin/sh\necho changed\n")
        self.assertNotEqual(stage.elan_home_identity(home), first)
        outside = self.root / "outside"
        outside.write_text("not in the installed toolchain")
        (installed / "escaped").symlink_to(outside)
        with self.assertRaisesRegex(stage.Refused, "link escapes"):
            stage.elan_home_identity(home)

    def test_lean_mutation_during_consumer_checks_refuses_acceptance(self):
        home = self.root / "elan-home"
        executable(home / "bin/lean", "#!/bin/sh\necho original\n")
        arguments, _ = self.consumer_arguments()
        def mutate(name):
            executable(home / "bin/lean", "#!/bin/sh\necho changed\n")
        self.owners.consumer_hook = mutate
        result, record = self.run_pipeline(*arguments, "--elan-home", str(home))
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertTrue(any("Lean installation changed" in error for error in record["consumer_failures"]))
        self.assertFalse(any((self.state / "consumer-results").glob("*/*.json")))

    def test_hash_covers_modes_names_bytes_and_internal_links_but_refuses_escapes(self):
        tree = self.root / "artifact"
        tree.mkdir()
        executable(tree / "tool", "payload")
        (tree / "alias").symlink_to("tool")
        before = stage.fingerprint(tree)
        (tree / "tool").chmod(0o700)
        self.assertNotEqual(stage.fingerprint(tree), before)
        (tree / "alias").unlink()
        (tree / "alias").symlink_to(self.repo / "README")
        with self.assertRaisesRegex(stage.Refused, "escapes"):
            stage.fingerprint(tree)

    def test_owner_environment_policy_is_used_without_importing_owner(self):
        owner = self.repo / "scripts/recreate_bootstrap.py"
        owner.write_text(owner.read_text() + '\nraise RuntimeError("must not import")\n')
        environment = {"CPATH": "ambient", "LIBRARY_PATH": "ambient", "SDKROOT": "ambient",
                       "CARGO_BUILD_JOBS": "6", "RUSTUP_HOME": "ambient", "TRUST_WAIVER": "ambient",
                       "HOME": str(self.root), "PATH": "/usr/bin:/bin"}
        self.assertEqual(stage.bootstrap_environment(environment, owner),
                         {"HOME": str(self.root), "PATH": "/usr/bin:/bin"})

    def test_current_repository_owner_policy_can_be_read_without_execution(self):
        environment = {"CPATH": "ambient", "LIBRARY_PATH": "ambient", "SDKROOT": "ambient",
                       "CARGO_BUILD_JOBS": "20", "CARGO_HOME": "ambient", "RUSTUP_HOME": "ambient",
                       "HOME": str(self.root), "PATH": "/usr/bin:/bin", "ELAN_HOME": "/owned/elan"}
        owner = SCRIPT.parent / "recreate_bootstrap.py"
        self.assertEqual(stage.bootstrap_environment(environment, owner),
                         {"HOME": str(self.root), "PATH": "/usr/bin:/bin", "ELAN_HOME": "/owned/elan"})

    def test_admitted_wrapper_converts_cpu_share_to_option_and_clears_authority(self):
        owner = self.root / "recreate_bootstrap.py"
        owner.write_text((self.repo / "scripts/recreate_bootstrap.py").read_text() +
                         '\nimport json, os, sys\nprint(json.dumps({"args": sys.argv[1:], "env": dict(os.environ)}))\n')
        environment = {**os.environ, "BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "3",
                       "CPATH": "ambient", "LIBRARY_PATH": "ambient", "SDKROOT": "ambient"}
        result = subprocess.run([sys.executable, str(SCRIPT), "_admitted-bootstrap", sys.executable,
                                 str(owner), "--no-register"], env=environment, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        output = json.loads(result.stdout)
        self.assertEqual(output["args"], ["--no-register", "--jobs", "3"])
        for key in ("CARGO_BUILD_JOBS", "CPATH", "LIBRARY_PATH", "SDKROOT", "RUSTUP_HOME"):
            self.assertNotIn(key, output["env"])
        environment.pop("BUILD_SLOT_HELD")
        result = subprocess.run([sys.executable, str(SCRIPT), "_admitted-bootstrap", sys.executable,
                                 str(owner)], env=environment, text=True, capture_output=True)
        self.assertEqual(result.returncode, 2)

    def test_all_consumers_run_their_committed_commands_in_isolated_homes(self):
        arguments, repositories = self.consumer_arguments()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        self.assertEqual(record["status"], "consumer_ready")
        self.assertTrue(record["consumer_ready"])
        self.assertFalse(record["deployment_ready"])
        homes, targets = set(), set()
        for name in stage.CONSUMERS:
            accepted = record["consumers"][name]
            self.assertEqual(accepted["status"], "passed")
            self.assertEqual(accepted["source_commit"], git(repositories[name], "rev-parse", "HEAD"))
            _, argv, env = next(call for call in self.owners.calls if call[0] == f"{name}-consumer-check")
            self.assertEqual(argv[1], "--")
            self.assertEqual(argv[-1], accepted["identity"]["policy"]["command"])
            self.assertEqual(self.owners.timeouts[f"{name}-consumer-check"], 60)
            home = Path(env["RUSTUP_HOME"])
            self.assertTrue(home.is_relative_to(self.state / "consumer-rustup"))
            self.assertEqual((home / "toolchains/trust").resolve(), Path(record["staged_toolchain"]))
            homes.add(home)
            targets.add(env["CARGO_TARGET_DIR"])
            receipt = stage.read_json(Path(accepted["receipt"]))
            self.assertEqual(receipt["exit_code"], 0)
            self.assertEqual(receipt["step"]["name"], f"{name}-consumer-check")
            self.assertEqual(receipt["step"]["exit_code"], 0)
        self.assertEqual(len(homes), 4)
        self.assertEqual(len(targets), 4)
        self.assertFalse((self.state / "rustup/toolchains/trust").exists())

    def test_consumer_red_is_not_excused_by_baseline_text_and_other_checks_finish(self):
        arguments, _ = self.consumer_arguments()
        self.owners.consumer_exits["ay-consumer-check"] = 1
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertEqual(record["consumers"]["ay"]["exit_code"], 1)
        self.assertEqual(record["consumers"]["clean"]["status"], "passed")
        self.assertTrue(Path(record["packages"]).exists())
        self.assertIn("consumer acceptance incomplete", record["error"])
        self.owners.consumer_exits.clear()
        self.owners.calls.clear()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        self.assertTrue(record["consumer_ready"])
        self.assertEqual([n for n in self.names() if n.endswith("-consumer-check")], ["ay-consumer-check"])
        self.assertTrue(record["consumers"]["aterm"]["reused"])

    def test_consumer_source_advance_invalidates_only_that_acceptance(self):
        arguments, repositories = self.consumer_arguments()
        self.assertEqual(self.run_pipeline(*arguments)[0], 0)
        ay = repositories["ay"]
        (ay / "README").write_text("new consumer source")
        git(ay, "add", "README")
        git(ay, "commit", "-qm", "new source")
        git(ay, "push", "origin", "main")
        self.owners.calls.clear()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        self.assertEqual([n for n in self.names() if n.endswith("-consumer-check")], ["ay-consumer-check"])

    def test_consumer_reuse_recomputes_bound_outcomes_from_all_full_logs(self):
        arguments, _ = self.consumer_arguments()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        for consumer in record["consumers"].values():
            receipt = stage.read_json(Path(consumer["receipt"]))
            self.assertEqual(receipt["schema"], stage.CONSUMER_RECEIPT_SCHEMA)
            self.assertTrue(receipt["outcome"]["accepted"])
            self.assertEqual(receipt["outcome"]["reader_sha256"], consumer["identity"]["policy"]["reader_sha256"])
            self.assertEqual(receipt["outcome"]["log_sha256"], stage.file_hash(Path(consumer["log"])))
        self.owners.calls.clear()
        with mock.patch.object(stage, "consumer_outcome", wraps=stage.consumer_outcome) as validate:
            result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        self.assertEqual(validate.call_count, 4)
        self.assertTrue(all(row["reused"] for row in record["consumers"].values()))
        self.assertFalse(any(name.endswith("-consumer-check") for name in self.names()))

    def test_cached_outcome_tampering_is_refused_without_rerunning_the_command(self):
        arguments, _ = self.consumer_arguments()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        path = Path(record["consumers"]["ty"]["receipt"])
        receipt = stage.read_json(path)
        receipt["outcome"]["census"]["counts"]["proved"] = 99
        stage.atomic_json(path, receipt)
        self.owners.calls.clear()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertIn("cached outcome is refused or changed", record["consumers"]["ty"]["error"])
        self.assertNotIn("ty-consumer-check", self.names())
        self.assertTrue(record["consumers"]["aterm"]["reused"])

    def test_consumer_cache_requires_integer_exit_statuses_without_rerunning(self):
        arguments, _ = self.consumer_arguments()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        path = Path(record["consumers"]["ty"]["receipt"])
        original = stage.read_json(path)
        for location in ("receipt", "step"):
            for value in (False, 0.0):
                with self.subTest(location=location, value=repr(value)):
                    receipt = json.loads(json.dumps(original))
                    target = receipt if location == "receipt" else receipt["step"]
                    target["exit_code"] = value
                    stage.atomic_json(path, receipt)
                    self.owners.calls.clear()
                    result, record = self.run_pipeline(*arguments)
                    self.assertEqual(result, 1)
                    self.assertFalse(record["consumer_ready"])
                    self.assertRegex(record["consumers"]["ty"]["error"],
                                     "acceptance cache|shell exit zero")
                    self.assertNotIn("ty-consumer-check", self.names())
                    self.assertTrue(record["consumers"]["aterm"]["reused"])
        stage.atomic_json(path, original)
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        self.assertTrue(all(row["reused"] for row in record["consumers"].values()))

    def test_legacy_exit_only_receipt_and_truncated_output_cannot_be_reused(self):
        arguments, _ = self.consumer_arguments()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        path = Path(record["consumers"]["ty"]["receipt"])
        original = stage.read_json(path)
        legacy = dict(original)
        legacy["schema"] = stage.SCHEMA
        legacy.pop("outcome")
        stage.atomic_json(path, legacy)
        self.assertEqual(self.run_pipeline(*arguments)[0], 1)
        stage.atomic_json(path, original)
        log = Path(original["log"])
        log.write_bytes(log.read_bytes()[:-1])
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertIn("retained log changed", record["consumers"]["ty"]["error"])
        self.assertFalse(record["consumer_ready"])

    def test_publication_owner_advance_invalidates_acceptance_and_records_new_hash(self):
        arguments, _ = self.consumer_arguments()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        previous = record["consumers"]["aterm"]["outcome"]["reader_sha256"]
        owner = self.publication / "bin/pub"
        owner.write_text(owner.read_text() + "\n# new committed outcome owner\n")
        git(self.publication, "add", "bin/pub")
        git(self.publication, "commit", "-qm", "outcome owner advance")
        git(self.publication, "push", "origin", "main")
        self.owners.calls.clear()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        self.assertEqual(sum(name.endswith("-consumer-check") for name in self.names()), 4)
        for consumer in record["consumers"].values():
            self.assertNotEqual(consumer["outcome"]["reader_sha256"], previous)
            self.assertEqual(consumer["outcome"]["reader_sha256"], stage.file_hash(owner))

    def test_exit_zero_without_census_fails_but_other_consumers_complete(self):
        arguments, _ = self.consumer_arguments()
        self.owners.consumer_outputs["ty-consumer-check"] = "build stopped before its report"
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertFalse(record["deployment_ready"])
        self.assertFalse(record["consumers"]["ty"]["outcome"]["accepted"])
        self.assertEqual(record["consumers"]["clean"]["status"], "passed")
        self.assertTrue(Path(record["consumers"]["ty"]["log"]).is_file())
        self.assertFalse((self.state / "consumer-results/ty").exists())
        self.assertEqual(sum(name.endswith("-consumer-check") for name in self.names()), 4)

    def test_missing_consumer_mapping_runs_supplied_checks_but_is_not_ready(self):
        arguments, _ = self.consumer_arguments()
        del arguments[-2:]  # clean mapping
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertEqual(record["consumers"]["ay"]["status"], "passed")
        self.assertEqual(record["consumers"]["clean"]["status"], "not-configured")

    def test_unsupported_consumer_policy_refuses_without_trimming_command(self):
        arguments, repositories = self.consumer_arguments()
        ay = repositories["ay"]
        policy = ay / "publish/config.sh"
        policy.write_text('CHECK_CMD_DEFAULT="rustup run trust targo trust check --locked && git push origin main"\n')
        git(ay, "add", "publish/config.sh")
        git(ay, "commit", "-qm", "unsafe check fixture")
        git(ay, "push", "origin", "main")
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertEqual(record["consumers"]["ay"]["status"], "failed")
        self.assertEqual(record["consumers"]["ay"]["source_commit"], git(ay, "rev-parse", "HEAD"))
        self.assertTrue(Path(record["consumers"]["ay"]["log"]).is_file())
        self.assertNotIn("ay-consumer-check", self.names())
        self.assertIn("clean-consumer-check", self.names())

    def test_consumer_cache_requires_its_full_retained_log(self):
        arguments, _ = self.consumer_arguments()
        _, record = self.run_pipeline(*arguments)
        Path(record["consumers"]["ty"]["log"]).write_text("replacement log")
        self.owners.calls.clear()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertIn("retained log changed", record["consumers"]["ty"]["error"])
        self.assertNotIn("ty-consumer-check", self.names())

    def test_consumer_interruption_stops_new_work_and_retains_completed_receipts(self):
        arguments, _ = self.consumer_arguments()
        self.owners.interrupt = "ay-consumer-check"
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertEqual(record["consumers"]["aterm"]["status"], "passed")
        self.assertNotIn("ty-consumer-check", self.names())
        self.assertTrue(record["steps"][-1]["interrupted"])
        self.owners.interrupt = None
        self.owners.calls.clear()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        self.assertTrue(record["consumers"]["aterm"]["reused"])

    def test_schedule_retains_absolute_consumer_and_policy_reader_mappings(self):
        arguments, repositories = self.consumer_arguments()
        argv = stage.train_plist(self.train_arguments(*arguments))["ProgramArguments"]
        for name, repository in repositories.items():
            self.assertIn(f"{name}={repository}", argv)
        self.assertIn(str(self.root / "publication"), argv)

    def test_command_records_real_nonzero_and_timeout_failures(self):
        with self.assertRaises(stage.CommandFailed) as failure:
            stage.command([sys.executable, "-c", "raise SystemExit(17)"], self.root,
                          dict(os.environ), self.root / "exit.log")
        self.assertEqual(failure.exception.exit_code, 17)
        with self.assertRaises(stage.CommandFailed) as failure:
            stage.command([sys.executable, "-c", "import time; time.sleep(30)"], self.root,
                          dict(os.environ), self.root / "timeout.log", timeout=0.02)
        self.assertTrue(failure.exception.timed_out)

    def test_labelled_stock_cross_target_inputs_stay_inside_scratch_home(self):
        arguments, repositories = self.consumer_arguments()
        aterm = repositories["aterm"]
        policy = aterm / "publish/config.sh"
        policy.write_text('CHECK_CMD_DEFAULT="rustup run trust targo trust check --locked && rustup run 1.97.1 cargo check --target wasm32-unknown-unknown"\n')
        git(aterm, "add", "publish/config.sh")
        git(aterm, "commit", "-qm", "labelled cross-target oracle")
        git(aterm, "push", "origin", "main")
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        oracle = record["consumers"]["aterm"]["identity"]["cross_target_oracles"]["1.97.1"]
        self.assertTrue(Path(oracle["path"]).is_relative_to(self.state / "consumer-rustup"))
        self.assertFalse(Path(oracle["path"]).is_symlink())
        install = next(argv for name, argv, _ in self.owners.calls if name == "aterm-cross-oracle-install")
        self.assertIn("--no-self-update", install)
        self.assertEqual(install[-2:], ["--target", "wasm32-unknown-unknown"])
        self.assertIn("identity", oracle)

    def test_declared_stock_target_add_binds_an_opaque_cross_target_command(self):
        arguments, repositories = self.consumer_arguments()
        aterm = repositories["aterm"]
        policy = aterm / "publish/config.sh"
        policy.write_text('CHECK_CMD_DEFAULT="rustup run trust targo trust check --locked && '
                          'rustup target add --toolchain 1.97.1 wasm32-unknown-unknown && '
                          "sh -c 'RUSTFLAGS=-Ctarget-feature=+simd128 "
                          'RUSTC=$(rustup which --toolchain 1.97.1 rustc) '
                          "rustup run 1.97.1 cargo check --locked --target wasm32-unknown-unknown -p aterm-wasm'\"\n")
        git(aterm, "add", "publish/config.sh")
        git(aterm, "commit", "-qm", "explicit stock target declaration before opaque check")
        git(aterm, "push", "origin", "main")
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        consumer = record["consumers"]["aterm"]
        oracle = consumer["identity"]["cross_target_oracles"]["1.97.1"]
        self.assertEqual(oracle["targets"], ["wasm32-unknown-unknown"])
        self.assertTrue(Path(oracle["path"]).is_relative_to(self.state / "consumer-rustup"))
        self.assertIn("identity", oracle)
        names = self.names()
        self.assertLess(names.index("aterm-cross-oracle-install"), names.index("aterm-consumer-check"))
        self.assertIn("RUSTC=$(rustup which --toolchain 1.97.1 rustc)",
                      consumer["identity"]["policy"]["command"])

    def test_declared_stock_target_add_requires_one_explicit_bounded_selection(self):
        root = self.root / "declared-policy"
        (root / "publish").mkdir(parents=True)
        policy = root / "publish/config.sh"
        for declaration in (
                "rustup target add wasm32-unknown-unknown",
                "rustup target add --toolchain trust wasm32-unknown-unknown",
                "rustup target add --toolchain 1.97.1",
                "rustup target add wasm32-unknown-unknown --toolchain",
                "rustup target add --toolchain 1.97.1 --toolchain 1.97.1 wasm32-unknown-unknown",
                "rustup target add --toolchain=1.97.1 --toolchain=1.98.0 wasm32-unknown-unknown",
                "rustup target add --toolchain 1.97.1 --unknown wasm32-unknown-unknown",
                "rustup target add --toolchain=../escape wasm32-unknown-unknown",
                "rustup target add --toolchain 1.97.1 ../escape"):
            with self.subTest(declaration=declaration):
                policy.write_text('CHECK_CMD_DEFAULT="rustup run trust targo trust check --locked && '
                                  + declaration + '"\n')
                with self.assertRaises(stage.Refused):
                    stage.consumer_policy(self.publication, root)
        policy.write_text('CHECK_CMD_DEFAULT="rustup run trust targo trust check --locked && '
                          'rustup target add wasm32-unknown-unknown --toolchain=1.97.1 '
                          'wasm32-wasip1 && rustup run 1.97.1 cargo check --target wasm32-unknown-unknown"\n')
        parsed = stage.consumer_policy(self.publication, root)
        self.assertEqual(parsed["cross_target_oracles"],
                         {"1.97.1": ["wasm32-unknown-unknown", "wasm32-wasip1"]})

    def test_declared_stock_target_add_refuses_oracle_mutation_during_check(self):
        arguments, repositories = self.consumer_arguments()
        aterm = repositories["aterm"]
        policy = aterm / "publish/config.sh"
        policy.write_text('CHECK_CMD_DEFAULT="rustup run trust targo trust check --locked && '
                          'rustup target add --toolchain 1.97.1 wasm32-unknown-unknown"\n')
        git(aterm, "add", "publish/config.sh")
        git(aterm, "commit", "-qm", "explicit stock target declaration mutation control")
        git(aterm, "push", "origin", "main")

        def replace_oracle(name):
            if name == "aterm-consumer-check":
                paths = list((self.state / "consumer-rustup/aterm").glob("*/toolchains/1.97.1/lib/libstd.rlib"))
                self.assertEqual(len(paths), 1)
                paths[0].write_bytes(b"changed stock cross-target oracle")

        self.owners.consumer_hook = replace_oracle
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertIn("changed its stock cross-target oracle inputs", record["consumers"]["aterm"]["error"])
        self.assertNotIn("receipt", record["consumers"]["aterm"])

    def test_cargo_configuration_changes_invalidate_consumer_acceptance(self):
        arguments, _ = self.consumer_arguments()
        self.assertEqual(self.run_pipeline(*arguments)[0], 0)
        (self.cargo_home / "config.toml").write_text("[net]\nretry = 2\n")
        self.owners.calls.clear()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        self.assertEqual(len([name for name in self.names() if name.endswith("-consumer-check")]), 4)

    def test_parallel_consumers_are_bounded_and_status_and_receipts_stay_consistent(self):
        arguments, _ = self.consumer_arguments()
        arguments += ["--consumer-jobs", "2"]
        active = 0
        peak = 0
        lock = threading.Lock()
        both = threading.Event()
        release = threading.Event()

        def hook(_name):
            nonlocal active, peak
            with lock:
                active += 1
                peak = max(peak, active)
                if active == 2:
                    both.set()
            if not release.wait(timeout=10):
                raise AssertionError("parallel fixture was not released")
            with lock:
                active -= 1

        self.owners.consumer_hook = hook
        runner = stage.Runner(self.arguments(*arguments), self.owners)
        outcomes = []
        thread = threading.Thread(target=lambda: outcomes.append(runner.run()))
        thread.start()
        try:
            self.assertTrue(both.wait(timeout=15), "two consumers never ran together")
            for _ in range(30):
                record = stage.read_json(self.state / "latest.json")
                logs = [step["log"] for step in record["steps"]]
                self.assertEqual(len(logs), len(set(logs)))
                self.assertGreaterEqual(len([step for step in record["steps"]
                                             if step["name"].endswith("-consumer-check") and step["status"] == "running"]), 2)
                self.assertEqual(record["consumer_jobs"], 2)
                self.assertTrue(all(step.get("exit_code") == 0 for step in record["steps"] if step["status"] == "passed"))
        finally:
            release.set()
            thread.join(timeout=20)
        self.assertFalse(thread.is_alive())
        self.assertEqual(outcomes, [0], runner.record.get("error"))
        self.assertEqual(peak, 2)
        for name, consumer in runner.record["consumers"].items():
            receipt = stage.read_json(Path(consumer["receipt"]))
            self.assertEqual(receipt["step"]["name"], f"{name}-consumer-check")

    def test_parallel_consumer_failure_does_not_cancel_other_consumers(self):
        arguments, _ = self.consumer_arguments()
        self.owners.consumer_exits["ay-consumer-check"] = 1
        self.owners.consumer_hook = lambda _name: time.sleep(0.03)
        runner = stage.Runner(self.arguments(*arguments, "--consumer-jobs", "2"), self.owners)
        self.assertEqual(runner.run(), 1)
        self.assertFalse(runner.cancelled.is_set())
        self.assertEqual(runner.record["consumers"]["ay"]["status"], "failed")
        for name in ("aterm", "ty", "clean"):
            self.assertEqual(runner.record["consumers"][name]["status"], "passed")
        self.assertEqual(len([name for name in self.names() if name.endswith("-consumer-check")]), 4)

    # The fleet train.

    def gated_trust(self):
        """The fixture's Trust checkout as a Mac sets it up: pushes run scripts/hooks/pre-push."""
        self.hook_ran = self.root / "hook-ran"
        executable(self.repo / "scripts/hooks/pre-push", f"#!/bin/sh\ncat >/dev/null\necho ran >> '{self.hook_ran}'\n")
        executable(self.repo / "scripts/prewarm_push.sh")
        (self.repo / "docs").mkdir()
        (self.repo / "docs/OPEN_ISSUES.md").write_text(
            "# Open issues\n\n## Toolchain, bootstrap and release\n\n### OTHER-1 — another item\nIts text.\n\n## Later\n\nMore.\n")
        git(self.repo, "config", "core.hooksPath", "scripts/hooks")
        git(self.repo, "add", ".")
        git(self.repo, "commit", "-qm", "the push gate and the open issues")
        git(self.repo, "push", "-q", "origin", "main")
        self.hook_ran.unlink()
        self.owners = TrainOwners()
        self.github = FakeGitHub(self.root / "trust.git")

    def train(self, *extra):
        tools = {name: f"/fixture/bin/{name}" for name in ("aterm", "agh", "targo")}
        return stage.Train(self.train_arguments(*extra), self.owners, self.github, tools)

    def tick(self, *extra):
        with mock.patch("builtins.print"):
            return self.train(*extra).tick()

    def train_state(self):
        return json.loads((self.state / "train.json").read_text())

    def remote_file(self, name):
        return git(self.root / "trust.git", "show", f"refs/heads/main:{name}")

    def foreign_commit(self, text):
        git(self.repo, "pull", "-q", "--ff-only", "origin", "main")
        (self.repo / "README").write_text(text)
        git(self.repo, "commit", "-qam", text)
        git(self.repo, "push", "-q", "origin", "main")
        return git(self.repo, "rev-parse", "HEAD")

    def test_train_cuts_when_main_moved_publishes_without_the_index_and_then_waits(self):
        self.gated_trust()
        arguments, _ = self.consumer_arguments()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        self.assertEqual(self.tick(*arguments), 0, self.train_state())
        state = self.train_state()
        self.assertEqual((state["last"]["status"], state["last"]["build"], state["good"]["commit"]), ("published", build, cut))
        self.assertEqual(state["last"]["report"], "nothing found; docs/OPEN_ISSUES.md holds no FLEET-BUILD-REPORT-1")
        self.assertEqual(self.github.builds(), [build])
        # The re-pin reached main by a push that ran the hook; its branch is gone from origin.
        repin = self.github.main()
        self.assertEqual(git(self.root / "trust.git", "rev-parse", f"{repin}^"), cut)
        self.assertEqual(self.hook_ran.read_text(), "ran\n")
        self.assertEqual(self.github.deleted, [f"seed/repin-{cut[:12]}"])
        self.assertEqual(state["settled"], repin)
        names = self.names()
        order = ["release-signing-ready", "publisher-hosts-check", "trust-repo-admitted", "sanctioned-mint-and-double-compile",
                 "signed-pack-dry-run", "seed-cut-dry-run", "seed-archives-and-repin-branch", "re-pin-push-1",
                 "signed-pack-stage-upload"]
        self.assertEqual([name for name in names if name in order], order)
        self.assertFalse([name for name in names if name.startswith("unsigned-")])
        # Never the index, the public owner, a canary or a withdrawal.
        for name, argv, _env in self.owners.calls:
            self.assertFalse(stage.PUBLISHER_REFUSED.intersection(argv), (name, argv))
            self.assertNotIn("alabsystems", " ".join(argv))
            self.assertEqual("--publish" in argv, name == "seed-archives-and-repin-branch", name)
            if "atpkg-publish" in argv and name != "publisher-hosts-check":
                self.assertEqual(argv[argv.index("atpkg-publish") + 1:][:5],
                                 ["--", "--host", "agh-staging", "publish-group", "rustc"])
                self.assertEqual(len({"--dry-run", "--stage-upload"}.intersection(argv)), 1)
        self.assertEqual(json.loads((Path(state["good"]["build_dir"]) / "latest.json").read_text())["published"]["index"], "unchanged")
        # The landing worktree is left detached and clean, with no branch of the train's.
        landing = self.state / "landing.noindex"
        self.assertEqual(git(landing, "status", "--porcelain"), "")
        self.assertEqual(git(self.repo, "branch", "--list", "trust-train/*"), "")

        # Main holds nothing but the train's own re-pin: the next tick starts nothing.
        calls = len(self.owners.calls)
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train(*arguments).tick(), 0)
        self.assertIn(f"main has not moved since build {build} was published", printed.call_args.args[0])
        self.assertEqual(len(self.owners.calls), calls)
        self.assertEqual(len(list((self.state / "builds").iterdir())), 1)
        status = stage.train_status(self.state, self.train(*arguments).read_main)
        self.assertRegex(status, rf"^train: last published build {build}, 1 commits behind main \({repin[:12]}, build {build + 1}, ")
        self.assertIn(f"the last train published build {build} ({cut[:12]})", status)

        # Someone lands a commit: the next tick cuts it, and the last good build stays, trimmed.
        first = Path(state["good"]["build_dir"])
        self.assertTrue((first / "source/build").is_dir())
        moved = self.foreign_commit("moved")
        self.assertEqual(self.tick(*arguments), 0, self.train_state())
        state = self.train_state()
        self.assertEqual((state["good"]["commit"], state["good"]["build"]), (moved, build + 2))
        self.assertEqual(self.github.builds(), [build, build + 2])
        self.assertEqual({path.name for path in (self.state / "builds").iterdir()},
                         {first.name, Path(state["good"]["build_dir"]).name})
        self.assertFalse((first / "source/build").exists())
        self.assertTrue((first / f"toolchains/stage-trust-{cut}/bin/trustc").is_file())

    def test_train_exits_zero_while_another_train_holds_the_lock(self):
        self.gated_trust()
        with stage.train_lock(self.state) as owned:
            self.assertTrue(owned)
            with mock.patch("builtins.print") as printed:
                self.assertEqual(self.train().tick(), 0)
            self.assertIn("nothing started", printed.call_args.args[0])
            self.assertIn("a train is starting", stage.train_status(self.state))
        self.assertEqual(self.owners.calls, [])
        self.assertFalse((self.state / "builds").exists())
        self.assertIn("no train has run here", stage.train_status(self.state))

    def test_failed_cut_is_not_repeated_until_main_moves(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        self.owners.fail = "sanctioned-mint-and-double-compile"
        self.assertEqual(self.tick(), 1)
        state = self.train_state()
        self.assertEqual((state["last"]["status"], state["settled"]), ("failed", cut))
        self.assertIn("fake sanctioned-mint-and-double-compile failure", state["last"]["error"])
        self.assertEqual(self.github.builds(), [])
        self.assertEqual(self.github.main(), cut)
        calls = len(self.owners.calls)
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train().tick(), 0)
        self.assertIn("main has not moved since the last train ended", printed.call_args.args[0])
        self.assertEqual(len(self.owners.calls), calls)
        # Main moves: the failed build directory goes, its record stays, and the tip is cut.
        self.owners.fail = None
        failed = Path(state["last"]["build_dir"])
        moved = self.foreign_commit("moved")
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual(self.train_state()["good"]["commit"], moved)
        self.assertFalse(failed.exists())
        self.assertEqual(json.loads((self.state / "history" / failed.name / "latest.json").read_text())["status"], "failed")

    def test_refused_publisher_preflight_publishes_nothing(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        self.owners.fail = "signed-pack-dry-run"
        self.assertEqual(self.tick(), 1)
        self.assertNotIn("seed-archives-and-repin-branch", self.names())
        self.assertEqual((self.github.main(), self.github.builds()), (cut, []))
        self.assertFalse(self.hook_ran.exists())

    def test_red_push_gate_stops_the_train_before_the_upload(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        self.owners.push_exits = [5]
        self.assertEqual(self.tick(), 1)
        self.assertNotIn("signed-pack-stage-upload", self.names())
        self.assertNotIn("re-pin-push-2", self.names())
        self.assertEqual((self.github.main(), self.github.builds()), (cut, []))
        # The minted re-pin stays on origin until a re-pin lands; the next train's supersedes it.
        self.assertEqual(self.github.deleted, [])
        self.assertEqual(git(self.root / "trust.git", "branch", "--list", "seed/repin-*").strip(), f"seed/repin-{cut[:12]}")
        moved = self.foreign_commit("moved")
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual(self.github.deleted, [f"seed/repin-{cut[:12]}", f"seed/repin-{moved[:12]}"])
        self.assertNotIn("branches", self.train_state())
        self.assertEqual(git(self.repo, "branch", "--list", "trust-train/*"), "")

    def test_landing_runs_the_push_helper_again_when_main_moved_under_it(self):
        self.gated_trust()
        self.owners.push_exits = [4, 6]
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual([name for name in self.names() if name.startswith("re-pin-push-")],
                         ["re-pin-push-1", "re-pin-push-2", "re-pin-push-3"])
        # The helper's lease is taken with the Targo of the build just cut, not the Mac's installed one.
        for name, _argv, env in self.owners.calls:
            if name.startswith("re-pin-push-"):
                self.assertRegex(env["TARGO"], r"/toolchains/stage-trust-[0-9a-f]{40}/bin/targo$")
        self.owners.push_exits = [6, 4, 6, 4]
        self.foreign_commit("moved")
        self.assertEqual(self.tick(), 1)
        self.assertIn("main moved under 4 runs", self.train_state()["last"]["error"])
        # That landing's branch and merge are still in the train's worktree; the next landing clears them.
        self.assertRegex(git(self.repo, "branch", "--list", "trust-train/*"), r"trust-train/repin-")
        self.foreign_commit("moved again")
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual(git(self.repo, "branch", "--list", "trust-train/*"), "")
        self.assertEqual(git(self.state / "landing.noindex", "status", "--porcelain"), "")

    def test_consumer_red_is_reported_after_the_upload_and_never_refuses_it(self):
        self.gated_trust()
        arguments, repositories = self.consumer_arguments()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        self.owners.consumer_exits["aterm-consumer-check"] = 1
        self.assertEqual(self.tick(*arguments), 0, self.train_state())
        state = self.train_state()
        self.assertEqual((state["last"]["status"], state["last"]["build"]), ("published", build))
        names = self.names()
        self.assertLess(names.index("signed-pack-stage-upload"), names.index("aterm-consumer-check"))
        issues = self.remote_file("docs/OPEN_ISSUES.md")
        aterm = git(repositories["aterm"], "rev-parse", "HEAD")
        self.assertIn(f"### FLEET-BUILD-REPORT-1 — fleet build {build}:", issues)
        self.assertIn(f"- aterm at `{aterm[:12]}`: the committed check is red (exit 1).", issues)
        self.assertNotIn(str(self.root), issues)
        self.assertLess(issues.index("### OTHER-1"), issues.index("### FLEET-BUILD-REPORT-1"))
        self.assertLess(issues.index("### FLEET-BUILD-REPORT-1"), issues.index("## Later"))
        self.assertEqual(state["last"]["report"], "1 finding(s) in docs/OPEN_ISSUES.md FLEET-BUILD-REPORT-1")
        # The report is the train's own commit: main has not moved.
        self.assertEqual(state["settled"], self.github.main())
        self.assertEqual(self.hook_ran.read_text(), "ran\nran\n")
        calls = len(self.owners.calls)
        self.assertEqual(self.tick(*arguments), 0)
        self.assertEqual(len(self.owners.calls), calls)
        # The next build's checks pass: its train removes the item.
        self.owners.consumer_exits.clear()
        self.foreign_commit("moved")
        self.assertEqual(self.tick(*arguments), 0, self.train_state())
        self.assertNotIn("FLEET-BUILD-REPORT-1", self.remote_file("docs/OPEN_ISSUES.md"))
        self.assertIn("### OTHER-1 — another item\nIts text.\n\n## Later", self.remote_file("docs/OPEN_ISSUES.md"))
        self.assertEqual(self.train_state()["last"]["report"], "nothing found; docs/OPEN_ISSUES.md holds no FLEET-BUILD-REPORT-1")

    def test_train_that_died_is_recorded_and_its_commit_is_cut_again(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        self.state.mkdir()
        stage.atomic_json(self.state / "train.json", {"schema": stage.TRAIN_SCHEMA, "last": {
            "status": "running", "phase": "cutting", "main": cut, "commit": cut, "build": None,
            "build_dir": str(self.state / "builds/gone"), "started_at": stage.now()}})
        self.assertIn("ended without a result", stage.train_status(self.state))
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train("--dry-run").tick(), 0)
        self.assertIn(f"train: would cut {cut[:12]}", printed.call_args.args[0])
        self.assertEqual(self.train_state()["last"]["status"], "interrupted")
        self.assertEqual(self.owners.calls, [])
        self.assertFalse((self.state / "builds").exists())

    def test_train_decision_cuts_only_a_main_that_moved(self):
        tip, other = "a" * 40, "b" * 40
        published = {"settled": tip, "last": {"status": "published", "build": 7}}
        self.assertEqual(stage.train_decision(published, tip, 7, 9), (False, "main has not moved since build 7 was published"))
        self.assertTrue(stage.train_decision(published, other, 7, 9)[0])
        self.assertTrue(stage.train_decision(published, other, 7, None)[0])
        self.assertTrue(stage.train_decision({}, tip, None, None)[0])
        # A fresh state root on a main the newest build already counts.
        self.assertEqual(stage.train_decision({}, tip, 9, 9), (False, "main has not moved since build 9 was published"))
        failed = {"settled": tip, "last": {"status": "failed", "error": "the mint refused"}}
        cut, reason = stage.train_decision(failed, tip, 7, 9)
        self.assertFalse(cut)
        self.assertIn("failed: the mint refused", reason)
        # An interrupted train settles nothing, so its commit is cut again.
        self.assertTrue(stage.train_decision({"settled": other, "last": {"status": "interrupted"}}, tip, 7, 9)[0])

    def test_fleet_publisher_builds_only_a_dry_run_or_a_stage_upload(self):
        group = ["publish-group", "rustc", "--seal", "/seal", "--trust-repo", "/trust", "--out", "/out"]
        prefix = ["/bin/targo", "--unverified", "run", "-q", "--locked", "-p", "atpkg-publish", "--"]
        self.assertEqual(stage.fleet_publisher("/bin/targo", "agh-staging", ["hosts", "check"]),
                         [*prefix, "hosts", "check", "--host", "agh-staging"])
        for mode in ("--dry-run", "--stage-upload"):
            self.assertEqual(stage.fleet_publisher("/bin/targo", "agh-staging", [*group, mode]),
                             [*prefix, "--host", "agh-staging", *group, mode])
        for words in ([*group, "--publish-staged"], [*group], [*group, "--dry-run", "--stage-upload"],
                      [*group, "--stage-upload", "--publish-staged"], [*group, "--stage-upload", "--upload"],
                      [*group, "--stage-upload", "--force-same-build"], [*group, "--stage-upload", "--allow-build-tree-seal"],
                      ["canary", "--stage-upload"], ["index", "publish", "--dry-run"], ["lane", "withdraw", "--dry-run"],
                      ["adopt", "trust=1", "--dry-run"], ["publish-group", "aterm", "--stage-upload"], ["hosts", "check", "x"]):
            with self.subTest(words=words), self.assertRaisesRegex(stage.Refused, "never publishes the index"):
                stage.fleet_publisher("/bin/targo", "agh-staging", words)

    def test_github_reads_refs_and_has_no_write_but_one_branch_delete(self):
        calls = []

        def run(argv, **_kwargs):
            calls.append(argv)
            if argv[1:3] == ["repo", "refs"]:
                rows = [{"oid": "a" * 40, "ref": "refs/heads/main"}, {"oid": "b" * 40, "ref": "refs/tags/atpkg-trust-12"},
                        {"oid": "c" * 40, "ref": "refs/tags/atpkg-trust-resource-controller-99"},
                        {"oid": "d" * 40, "ref": "refs/heads/atpkg-trust-50"}, {"oid": "e" * 40, "ref": "refs/tags/atpkg-trust-7"}]
                rows = [row for row in rows if "--ref" not in argv or row["ref"] == argv[-1]]
                return types.SimpleNamespace(returncode=0, stdout=json.dumps(rows), stderr="")
            code = 11 if argv[1] in ("can", "compare") else 5
            return types.SimpleNamespace(returncode=code, stdout="", stderr="agh: refused\nmore")
        github = stage.GitHub("fixture/trust", "/fixture/agh", self.root / "github.log", run)
        self.assertEqual((github.main(), github.builds()), ("a" * 40, [7, 12]))
        self.assertIsNone(github.can_push())
        self.assertIsNone(github.ahead("f" * 40))
        with self.assertRaisesRegex(stage.Refused, "agh ref delete exited 5: agh: refused"):
            github.delete_branch("seed/repin-0123", "f" * 40)
        self.assertEqual(calls[-1], ["/fixture/agh", "ref", "delete", "fixture/trust", "refs/heads/seed/repin-0123",
                                     "--expect", "f" * 40, "--confirm", "refs/heads/seed/repin-0123"])
        self.assertEqual({call[1] for call in calls}, {"repo", "can", "compare", "ref"})
        self.assertEqual(len((self.root / "github.log").read_text().splitlines()), len(calls))
        self.assertEqual({name for name in vars(stage.GitHub) if not name.startswith("_")},
                         {"can_push", "refs", "main", "builds", "ahead", "delete_branch"})
        for slug in ("alabsystems/trust", "AlabSystems/trust", "trust", "a/b/c"):
            with self.subTest(slug=slug), self.assertRaises(stage.Refused):
                stage.GitHub(slug, "/fixture/agh")
        self.assertEqual(stage.github_slug("https://github.com/fixture/trust.git"), "fixture/trust")
        self.assertEqual(stage.github_slug("git@github.com:fixture/trust"), "fixture/trust")
        with self.assertRaisesRegex(stage.Refused, "--github-repo"):
            stage.github_slug(str(self.root / "trust.git"))

    def test_report_item_is_inserted_replaced_and_removed_in_place(self):
        text = "# Open\n\n## Toolchain, bootstrap and release\n\n### A-1 — a\nText.\n\n## Later\n\n### B-1 — b\nText.\n"
        first = stage.issue_block(7, "c" * 40, "2026-11-14", ["one."], None)
        inserted = stage.replace_issue(text, first)
        self.assertEqual(inserted, text.replace("## Later", first + "\n## Later"))
        self.assertIn("No earlier train build's row counts exist to compare with", first)
        second = stage.issue_block(9, "d" * 40, "2026-11-15", ["two.", "three."], {"build": 7})
        replaced = stage.replace_issue(inserted, second)
        self.assertEqual(replaced, text.replace("## Later", second + "\n## Later"))
        self.assertIn("- two.\n- three.\n", replaced)
        self.assertEqual(stage.replace_issue(replaced, None), text)
        self.assertEqual(stage.replace_issue(text, None), text)
        last = "# Open\n\n## Toolchain, bootstrap and release\n\n### A-1 — a\nText.\n"
        self.assertEqual(stage.replace_issue(last, first), last + "\n" + first)
        with self.assertRaisesRegex(stage.Refused, "has no section"):
            stage.replace_issue("# Open\n", first)

    def test_report_finds_red_checks_missing_consumers_and_lost_rows(self):
        passed = {"status": "passed", "commit": "a" * 40, "proved": 10, "failed": 1}
        rows = {name: dict(passed) for name in stage.CONSUMERS}
        self.assertEqual(stage.report_findings(rows, None), [])
        self.assertEqual(stage.report_findings(rows, {"build": 7, "consumers": rows}), [])
        now = {**rows, "ay": {**passed, "proved": 8, "failed": 3}, "ty": {"status": "failed", "commit": "b" * 40, "timed_out": True},
               "clean": {"status": "not-configured"}}
        before = {"build": 7, "consumers": {**rows, "ay": {**passed, "commit": "c" * 40}}}
        self.assertEqual(stage.report_findings(now, before), [
            "ay at `aaaaaaaaaaaa`: 8 rows proved, 10 on build 7 (ay then at `cccccccccccc`): 2 fewer.",
            "ay at `aaaaaaaaaaaa`: 3 rows failed, 1 on build 7 (ay then at `cccccccccccc`): 2 more.",
            "ty at `bbbbbbbbbbbb`: the committed check is red (it ran past its time bound).",
            "clean: not run (the train was given no `--consumer clean=REPO`)."])

    def test_retired_builds_keep_their_records_and_only_train_directories_go(self):
        builds = self.state / "builds"
        for name in ("a", "b", "c"):
            (builds / name / "source/build").mkdir(parents=True)
            (builds / name / "toolchains/sealed").mkdir(parents=True)
            (builds / name / "toolchains/sealed").chmod(0o555)
            (builds / name / "runs").mkdir()
            (builds / name / "latest.json").write_text(json.dumps({"name": name}))
            (builds / name / "train-build.json").write_text("{}")
        (builds / "c/train-build.json").unlink()
        outside = self.root / "outside"
        outside.mkdir()
        (builds / "a/link").symlink_to(outside, target_is_directory=True)
        problems = stage.retire_builds(self.state, builds / "b")
        self.assertEqual(problems, [f"{builds / 'c'} is not a train build directory; left in place"])
        self.assertEqual({path.name for path in builds.iterdir()}, {"b", "c"})
        self.assertFalse((builds / "b/source/build").exists())
        self.assertTrue((builds / "b/toolchains/sealed").is_dir())
        self.assertTrue((builds / "b/latest.json").is_file())
        self.assertEqual(json.loads((self.state / "history/a/latest.json").read_text()), {"name": "a"})
        self.assertTrue(outside.is_dir())
        for index in range(stage.TRAIN_HISTORY + 2):
            (self.state / "history" / f"old-{index:02d}").mkdir()
        stage.retire_builds(self.state, builds / "b")
        self.assertEqual(len(list((self.state / "history").iterdir())), stage.TRAIN_HISTORY)

    def test_train_install_writes_and_starts_the_agent_and_remove_stops_it(self):
        agents = self.root / "LaunchAgents"
        args = self.train_arguments("--launch-agents", str(agents), "--interval", "1800")
        calls = []

        def launchctl(argv, **_kwargs):
            calls.append(argv)
            return types.SimpleNamespace(returncode=0, stdout="", stderr="")
        agent = stage.train_install(args, launchctl)
        domain = f"gui/{os.getuid()}"
        self.assertEqual(agent, agents / "systems.alab.trust-train.plist")
        self.assertEqual(plistlib.loads(agent.read_bytes()), stage.train_plist(args))
        self.assertEqual(plistlib.loads(agent.read_bytes())["StartInterval"], 1800)
        self.assertEqual(calls, [["launchctl", "bootstrap", domain, str(agent)]])
        # Installed again, the running agent is stopped and replaced.
        stage.train_install(args, launchctl)
        self.assertEqual(calls[1:], [["launchctl", "bootout", f"{domain}/systems.alab.trust-train"],
                                     ["launchctl", "bootstrap", domain, str(agent)]])
        self.assertEqual([path.name for path in agents.iterdir()], [agent.name])
        self.assertEqual(stage.train_remove(args, launchctl), agent)
        self.assertEqual(calls[-1], ["launchctl", "bootout", f"{domain}/systems.alab.trust-train"])
        self.assertFalse(agent.exists())
        self.assertTrue(self.state.is_dir())
        with self.assertRaisesRegex(stage.Refused, "launchctl bootstrap exited 5: Bootstrap failed.*not loaded"):
            stage.train_install(args, lambda argv, **_kwargs: types.SimpleNamespace(
                returncode=5, stdout="", stderr="Bootstrap failed\n"))

    def test_run_and_status_keep_their_state_root_and_take_no_train_word(self):
        for argv in (["run"], ["status"], ["run", "install", "--state-root", str(self.state)],
                     ["launchd-plist", "--state-root", str(self.state)]):
            with self.subTest(argv=argv), mock.patch("sys.stderr"), self.assertRaises(SystemExit) as refused:
                stage.main(argv)
            self.assertEqual(refused.exception.code, 2)
        self.assertEqual(stage.parser().parse_args(["train"]).verb, None)

    def test_default_parallelism_is_one_consumer_per_six_cpus_up_to_four(self):
        args = stage.parser().parse_args(["run", "--state-root", str(self.state)])
        self.assertEqual(args.consumer_jobs, min(4, max(1, (os.cpu_count() or 1) // 6)))


PUBLICATION_OWNER = SCRIPT.parents[2] / "publication"


class CleanupApiTests(unittest.TestCase):
    def test_nested_signal_during_latch_retains_the_actual_gate_receipt(self):
        with tempfile.TemporaryDirectory(prefix="daily-nested-signal-") as temporary:
            root = Path(temporary)
            engine = root / "publication"
            (engine / "bin").mkdir(parents=True)
            (engine / "bin/pub").write_text(
                "def terminate_process_group(process):\n"
                "    process.terminate()\n"
                "    process.wait(timeout=2)\n")
            result = root / "result.json"
            # Deliver a second TERM while the old Event.set holds its condition
            # lock. The child exits on its own even if the old helper deadlocks.
            probe = r'''
import importlib.util, os, signal, sys, threading
spec = importlib.util.spec_from_file_location("daily_signal_probe", sys.argv[1])
stage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(stage)
class NestedSignalEvent(threading.Event):
    def set(self):
        with self._cond:
            os.kill(os.getpid(), signal.SIGTERM)
            self._flag = True
            self._cond.notify_all()
stage.threading.Event = NestedSignalEvent
gate = "import os,signal,time; os.kill(os.getppid(),signal.SIGTERM); time.sleep(0.5)"
raise SystemExit(stage.main(["_owned-command", sys.argv[2], sys.argv[3], "0", "--",
                            sys.executable, "-c", gate]))
'''
            outcome = subprocess.run([sys.executable, "-I", "-S", "-c", probe,
                                      str(SCRIPT), str(engine), str(result)],
                                     capture_output=True, text=True, timeout=5)
            self.assertEqual(outcome.returncode, 130, outcome.stderr)
            receipt = stage.read_json(result)
            self.assertTrue(receipt["interrupted"], receipt)
            self.assertEqual(receipt["exit_code"], -signal.SIGTERM)
            self.assertEqual(receipt["signal"], signal.SIGTERM)

    def test_signal_during_wait_exit_observation_preserves_the_actual_gate_status(self):
        with tempfile.TemporaryDirectory() as temporary:
            receipt = Path(temporary) / "result.json"
            handlers = {}
            child = mock.Mock(returncode=None)

            def observe(**_kwargs):
                # The signal arrives after kernel reaping, before Popen stores
                # returncode. A throwing handler loses this status boundary.
                handlers[signal.SIGTERM](signal.SIGTERM, None)
                child.returncode = -signal.SIGTERM
                return child.returncode

            child.wait.side_effect = observe
            with mock.patch.object(stage.signal, "signal", side_effect=lambda key, value: handlers.update({key: value})), \
                    mock.patch.object(stage, "cleanup_api", return_value={"terminate_process_group": mock.Mock()}), \
                    mock.patch.object(stage.subprocess, "Popen", return_value=child):
                code = stage.main(["_owned-command", temporary, str(receipt), "0", "--", "/fixture-gate"])
            self.assertEqual(code, 130)
            result = stage.read_json(receipt)
            self.assertTrue(result["interrupted"])
            self.assertEqual(result["exit_code"], -signal.SIGTERM)
            self.assertEqual(result["signal"], signal.SIGTERM)
            child.wait.assert_called_once_with(timeout=0.2)

    def test_concurrent_cleanup_loads_once_per_owner_identity(self):
        with tempfile.TemporaryDirectory(prefix="daily-cleanup-api-") as temporary:
            engine = Path(temporary)
            owner = engine / "bin/pub"
            owner.parent.mkdir()
            counter = engine / "loads"
            owner.write_text(f'''import pathlib, time
counter = pathlib.Path({str(counter)!r})
time.sleep(0.02)
counter.write_text(str(int(counter.read_text()) + 1) if counter.exists() else "1")
def terminate_process_group(process, drain=None): pass
''')
            with stage.concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
                apis = list(pool.map(lambda _: stage.cleanup_api(engine), range(8)))
            self.assertEqual(counter.read_text(), "1")
            self.assertTrue(all(api is apis[0] for api in apis))
            owner.write_text(owner.read_text() + "\n# changed owner identity\n")
            self.assertIsNot(stage.cleanup_api(engine), apis[0])
            self.assertEqual(counter.read_text(), "2")


@unittest.skipUnless((PUBLICATION_OWNER / "bin/pub").is_file() and shutil.which("cc"),
                     "live cleanup fixture needs the publication owner and a C compiler")
class PublicationCleanupTests(unittest.TestCase):
    """Real owner cleanup, with our own old-style shared-group daemon stand-in."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="daily-cleanup-test-")
        self.root = Path(self.temp.name).resolve()
        source = self.root / "daemon.c"
        source.write_text(r'''#include <stdio.h>
#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>
int main(int argc, char **argv) {
    if (argc != 3) return 2;
    int solver = fork();
    if (solver == 0) { execl("/bin/sleep", "sleep", "30", (char*)0); return 3; }
    FILE *out = fopen(argv[2], "w");
    fprintf(out, "%d %d\n", getpid(), solver); fclose(out);
    while (access(argv[1], F_OK) != 0) usleep(10000);
    kill(solver, SIGTERM); waitpid(solver, 0, 0); return 0;
}
''')
        self.daemon = self.root / "trustd"
        subprocess.run([shutil.which("cc"), str(source), "-o", str(self.daemon)],
                       check=True, capture_output=True)
        self.stop = self.root / "stop"
        self.pids = self.root / "daemon-pids"
        self.ready = self.root / "ready.json"
        self.result = self.root / "result.json"
        launcher = self.root / "launcher.py"
        launcher.write_text('''import json, os, pathlib, subprocess, sys, time
subprocess.Popen(sys.argv[1:4], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
pids = pathlib.Path(sys.argv[3])
deadline = time.monotonic() + 5
while not pids.exists() or len(pids.read_text().split()) != 2:
    if time.monotonic() >= deadline: raise RuntimeError("daemon did not start")
    time.sleep(0.01)
daemon, solver = map(int, pids.read_text().split())
compiler = subprocess.Popen(["/bin/sleep", "30"], start_new_session=True)
pathlib.Path(sys.argv[4]).write_text(json.dumps({"daemon": daemon, "solver": solver, "compiler": compiler.pid}))
time.sleep(30)
''')
        forwarder = self.root / "build-slot.py"
        forwarder.write_text('''import os, signal, subprocess, sys
assert sys.argv[1] == "--"
child = subprocess.Popen(sys.argv[2:], start_new_session=True)
def forward(sig, frame):
    try: os.killpg(child.pid, sig)
    except ProcessLookupError: pass
signal.signal(signal.SIGTERM, forward)
sys.exit(child.wait())
''')
        self.argv = [sys.executable, str(forwarder), "--", sys.executable, str(SCRIPT),
                     "_owned-command", str(PUBLICATION_OWNER), str(self.result), "1", "--",
                     sys.executable, str(launcher), str(self.daemon), str(self.stop), str(self.pids), str(self.ready)]

    def tearDown(self):
        # The stand-in follows its own normal exit protocol; nobody signals trustd.
        self.stop.touch()
        if self.pids.exists():
            daemon, solver = map(int, self.pids.read_text().split())
            self.until(lambda: not self.alive(daemon), timeout=5)
            if self.alive(solver):
                os.kill(solver, signal.SIGTERM)
        if self.ready.exists():
            compiler = stage.read_json(self.ready)["compiler"]
            if self.alive(compiler):
                os.kill(compiler, signal.SIGTERM)
        self.temp.cleanup()

    @staticmethod
    def alive(pid):
        status = subprocess.run(["ps", "-p", str(pid), "-o", "stat="], capture_output=True,
                                text=True, timeout=5).stdout.strip()
        return bool(status) and not status.startswith("Z")

    @staticmethod
    def until(predicate, timeout):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if predicate():
                return True
            time.sleep(0.02)
        return predicate()

    def assert_spared(self):
        self.assertTrue(self.ready.exists())
        pids = stage.read_json(self.ready)
        self.assertTrue(self.alive(pids["daemon"]), "cleanup signalled the shared-group trustd stand-in")
        self.assertTrue(self.alive(pids["solver"]), "cleanup descended into the daemon's solver subtree")
        self.assertTrue(self.until(lambda: not self.alive(pids["compiler"]), timeout=3),
                        "owned compiler escaped cleanup in its separate process group")

    def test_timeout_uses_publication_cleanup_and_spares_daemon_and_solver(self):
        with self.assertRaises(stage.CommandFailed):
            stage.command(self.argv, self.root, dict(os.environ), self.root / "timeout.log",
                          timeout=10, cleanup_owner=PUBLICATION_OWNER)
        self.assertTrue(stage.read_json(self.result)["timed_out"])
        self.assert_spared()

    def test_interrupt_through_slot_forwarder_spares_daemon_and_solver(self):
        self.argv[self.argv.index("_owned-command") + 3] = "0"
        cancelled = threading.Event()
        failures = []

        def run():
            try:
                stage.command(self.argv, self.root, dict(os.environ), self.root / "interrupt.log",
                              cleanup_owner=PUBLICATION_OWNER, cancel_event=cancelled)
            except BaseException as error:
                failures.append(error)

        thread = threading.Thread(target=run)
        thread.start()
        try:
            self.assertTrue(self.until(self.ready.exists, timeout=5))
        finally:
            cancelled.set()
            thread.join(timeout=20)
        self.assertFalse(thread.is_alive())
        self.assertTrue(failures and isinstance(failures[0], InterruptedError), failures)
        result = stage.read_json(self.result)
        # The gate can reap before its supervisor receives the forwarded signal.
        # Caller interruption and the gate's actual signal are separate evidence.
        self.assertEqual(result["signal"], signal.SIGTERM)
        self.assertEqual(result["exit_code"], -signal.SIGTERM)
        self.assert_spared()


if __name__ == "__main__":
    unittest.main()
