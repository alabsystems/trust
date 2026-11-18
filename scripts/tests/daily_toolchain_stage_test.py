#!/usr/bin/env python3
"""Exercise orchestration with real temporary Git histories and fake pipeline owners."""
import ast
import contextlib
import copy
import importlib.util
from contextlib import nullcontext
import hashlib
import io
import json
import shlex
import os
from pathlib import Path
import plistlib
import re
import runpy
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
import types
import unittest
import zlib
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
# The publisher's program name, spelled here and not read from the runner under test.
CONTROLLER = "trust-resource-controller"
OUTCOME_OWNER = SCRIPT.parents[1] / "scripts/tests/fixtures/publication_daily_consumer_outcomes.py"


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True,
                                   stderr=subprocess.DEVNULL).strip()


def executable(path, text="#!/bin/sh\nexit 0\n"):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    path.chmod(0o755)


def stand_in_agh(version, answer="echo 'agh @VERSION@'; exit 0"):
    """An Agh that answers `version` and nothing else: no test's command reaches a real one."""
    return ("#!/bin/sh\nif [ \"$1\" = version ]; then " + answer.replace("@VERSION@", version) + "; fi\n"
            "echo 'fixture agh: only version is answered' >&2\nexit 97\n")


def toolchain(path):
    executable(path / "bin/trustc")
    executable(path / "bin/targo")
    (path / "lib").mkdir()
    (path / "lib/libstd.rlib").write_bytes(b"std")


def bootstrap_sysroot(path, source):
    """A stage sysroot as x.py leaves it: its two source entries link to the building checkout."""
    toolchain(path)
    for entry in ("src", "rustc-src"):
        (path / "lib/rustlib" / entry).mkdir(parents=True)
        (path / "lib/rustlib" / entry / "rust").symlink_to(source)


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
        self.progress = {}  # step name -> the progress bound the runner gave it
        self.fail = None
        self.timeouts = {}
        self.consumer_exits = {}
        self.interrupt = None
        self.consumer_hook = None
        self.consumer_outputs = {}
        self.consumer_terminal_results = {}
        # What the manager scripts/build-tree-manager.sh builds answers to `--protocol`.
        self.manager_answer = "trust-build-tree-manager-v2"

    def __call__(self, argv, cwd, env, log, timeout=None, *, cleanup_owner=None, cancel_event=None, progress=None):
        if progress is not None:
            self.progress[log.stem.split("-", 1)[1]] = progress
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
        elif name == "build-tree-manager":
            executable(cwd / "build-tree-manager.noindex/debug/bootstrap", f"#!/bin/sh\necho {self.manager_answer}\n")
        elif name == "pinned-bootstrap-config":
            (cwd / "bootstrap.toml").write_text("[build]\n")
        elif name == "pinned-bootstrap":
            bootstrap_sysroot(cwd / "build" / HOST / "stage2", cwd)
        elif name == "locked-dependency-ceiling":
            index = argv.index("_prewarm-dependencies")
            self.assertion_ceiling = ["--ceiling-only" in argv, "--ceiling-seconds" in argv]
            stage.atomic_json(Path(argv[index + 4]), {"seconds": 4321, "items": 1})
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
            bootstrap_sysroot(mint / HOST / "stage2", cwd)
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
            seal = root / f"trust-{commit[:8]}"
            shutil.copytree(Path(argv[-1]), seal, symlinks=True)
            # Promotion freezes the live source entries inside the seal.
            (seal / "lib/rustlib/src/rust").unlink()
            (seal / "lib/rustlib/src/rust").mkdir()
            (seal / "lib/rustlib/rustc-src/rust").unlink()
            (seal / "lib/rustlib/rustc-src/rust").symlink_to("../src/rust")
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
            terminal = self.consumer_terminal_results.get(
                name, {"exit_code": 0, "signal": None, "timed_out": False, "interrupted": False})
            if isinstance(terminal, str):
                result_file.write_text(terminal)
            else:
                stage.atomic_json(result_file, terminal)
        return log.read_text()


class TrainOwners(Owners):
    """The train's owners: a real re-pin commit, real pushes to the fixture's remote, and a fake channel head.

    `head` is the signed index aterm's publisher reads and writes. `races` makes the next
    runs of an index-publishing step lose the next index number to another publisher;
    `refusals` makes every run of a step refuse with that text; `after[step]` runs once,
    right after that step's command. With `real_submodules`, a submodule pin's acquisition
    (the Agh on PATH) and scripts/submodule_sync.sh run for real.
    """
    def __init__(self):
        super().__init__()
        self.real_submodules = False
        self.push_exits = []
        self.head = {"index": 40, "pins": {"trust": 1, CONTROLLER: 1}}
        self.races = {}
        self.refusals = {}
        self.after = {}

    def __call__(self, argv, cwd, env, log, timeout=None, *, cleanup_owner=None, cancel_event=None, progress=None):
        if progress is not None:
            self.progress[log.stem.split("-", 1)[1]] = progress
        result = self.step(argv, cwd, env, log, timeout, cleanup_owner=cleanup_owner, cancel_event=cancel_event)
        if Path(argv[0]).name != "git" and (hook := self.after.pop(log.stem.split("-", 1)[1], None)):
            hook()
        return result

    def refuse(self, argv, log, text):
        log.write_text(log.read_text() + f"atpkg-publish: {text}\n")
        stage.atomic_json(Path(argv[argv.index("_owned-command") + 2]),
                          {"exit_code": 1, "timed_out": False, "interrupted": False})

    def status(self):
        lines = [f"atpkg-index-{self.head['index']} — signed by machine fixture under roster_seq 1",
                 "channel alab (channel_build 1): min_build 1"]
        lines += [f"  pin {program} = {build}" + (" [rustc]" if program == "trust" else "")
                  for program, build in sorted(self.head["pins"].items())]
        return "".join(f"atpkg-publish status: {line}\n" for line in lines)

    def publisher(self, argv, log, name):
        """aterm's publisher, as far as the train's index steps read and write the channel head."""
        words = argv[argv.index("atpkg-publish") + 2:]
        words = words[2:] if words[:1] == ["--host"] else words
        step = name.rstrip("0123456789").rstrip("-")
        if step in self.refusals:
            if words[:1] == ["canary"]:
                # A refused canary has made its output directory and signed nothing.
                Path(words[words.index("--out") + 1]).mkdir(exist_ok=True)
            return self.refuse(argv, log, self.refusals[step])
        if self.races.get(step):
            self.races[step] -= 1
            self.head["index"] += 1
            return self.refuse(argv, log, f"atpkg-index-{self.head['index']} already exists on fixture/atpkg-index with "
                               f"DIFFERENT bytes (index.toml) — another publisher took index {self.head['index']}; "
                               "never clobbered. Re-baseline on it: publish again, and the new publish baselines on the channel head")
        if words == ["status"]:
            log.write_text(log.read_text() + self.status())
        elif words[:1] == ["canary"]:
            out = Path(words[words.index("--out") + 1])
            if out.exists():
                return self.refuse(argv, log, "create fresh canary output: File exists")
            out.mkdir()
            (out / "train-receipt.toml").write_text(words[1].replace("trust=", "build = ") + "\n")
            (out / "train-receipt.toml.sig").write_bytes(b"signature")
        elif words[:3] == ["publish-group", "rustc", "--publish-staged"]:
            out = Path(words[words.index("--out") + 1])
            if not (out / "canary/train-receipt.toml.sig").is_file():
                return self.refuse(argv, log, "no signed canary receipt")
            staged = dict(line.split(" = ") for line in (out / "staged-builds.toml").read_text().splitlines())
            self.head["index"] += 1
            self.head["pins"].update({program: int(build) for program, build in staged.items()})
        elif words[:1] == ["pack"]:
            package = Path(words[words.index("--out") + 1]) / words[1]
            package.mkdir(parents=True, exist_ok=True)
            (package / f"pkg-{words[1]}-{words[words.index('--build') + 1]}.toml").write_text("schema = 1\n")
        elif words[:1] == ["index"]:
            program, build = words[words.index("--pin") + 1].split("=")
            self.head["index"] += 1
            self.head["pins"][program] = int(build)

    def step(self, argv, cwd, env, log, timeout=None, *, cleanup_owner=None, cancel_event=None):
        if self.real_submodules and log.stem.split("-", 1)[1] in ("acquire-submodule-pin", "submodule-sync"):
            if log.stem.split("-", 1)[1] == "submodule-sync":
                # The fixture's Trust source has no copy of the script; run this checkout's.
                argv = [argv[0], str(SCRIPT.with_name("submodule_sync.sh")), *argv[2:]]
            return stage.command(argv, cwd, env, log, cleanup_owner=cleanup_owner, cancel_event=cancel_event)
        result = super().__call__(argv, cwd, env, log, timeout, cleanup_owner=cleanup_owner, cancel_event=cancel_event)
        if Path(argv[0]).name == "git":
            return result
        name = log.stem.split("-", 1)[1]
        if "atpkg-publish" in argv and name not in ("signed-pack-dry-run", "signed-pack-stage-upload") \
                and not name.endswith("hosts-check"):
            self.publisher(argv, log, name)
            return log.read_text()
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
            before_merge = git(cwd, "rev-parse", "HEAD")
            git(cwd, "merge", "-q", "--no-edit", "refs/remotes/origin/main")
            code = self.push_exits.pop(0) if self.push_exits else 0
            # A merge that moved a first-party gitlink is kept, and the helper asks for a build (exit 4).
            if not code and git(cwd, "diff", "--name-only", before_merge, "HEAD", "--", "first-party", ".gitmodules"):
                code = 4
            # Its restore runs without `--fetch`: a child not at the merged pin stops it (exit 7).
            if not code and any(line[:1] in "+-U" for line in subprocess.check_output(
                    ["git", "-C", str(cwd), "submodule", "status", "--recursive"], text=True).splitlines()):
                code = 7
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
            # The publisher's record of the staged group, which --publish-staged reads.
            group = Path(argv[argv.index("--out") + 1])
            group.mkdir(parents=True, exist_ok=True)
            (group / "staged-builds.toml").write_text(f"trust = {build}\ntrust-cg = 3\ntrust-ir = 2\ntrust-vc = 4\n")
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
            "import time\n" +
            f"if pathlib.Path({str(self.root / 'slow-fetch')!r}).exists(): time.sleep(0.25)\n" +
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
        shutil.copy2(repo / "scripts/source_working_cache.py", graph_owner.with_name("source_working_cache.py"))
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

    def cache_input(self, source, destination, *, trees=None, run=None):
        """mint_seed_support.cargo_home_inputs's contract: the selected trees, each copy one item."""
        destination.mkdir()
        if source is not None:
            for relative in trees or self.mint["CARGO_HOME_INPUT_TREES"]:
                if getattr(self, "omit_handoff_archive", False) and relative == "registry/cache":
                    continue
                if (source / relative).exists():
                    (destination / relative).parent.mkdir(parents=True, exist_ok=True)
                    def copy(relative=relative):
                        blocked = getattr(self, "blocked_copy", None)
                        if blocked and blocked[0] == relative and blocked[1].wait(5):
                            return  # released by the test after its preparation ended
                        shutil.copytree(source / relative, destination / relative)
                    label = f"the copy of cargo home input {relative} into {destination}"
                    run(label, copy, destination / relative) if run else copy()
            self.assertFalse((destination / "registry/src").exists())
        return {"source": "explicit fixture", "trees": list(trees or self.mint["CARGO_HOME_INPUT_TREES"])}

    def registry_input(self):
        """An input Cargo home with registry trees and no Git databases."""
        given = self.root / "registry-input"
        for relative in ("registry/index/fixture/.cache/pr/ob/probe", "registry/cache/fixture/probe-0.1.0.crate"):
            (given / relative).parent.mkdir(parents=True, exist_ok=True)
            (given / relative).write_text("fixture")
        return given

    def cargo_like_git(self, packages):
        """Make the stand-in driver take Git dependencies as Cargo does: an exact depth-one fetch
        into its own database through the `git` on its PATH (the preparation's local-only shim),
        and a checkout whose objects are hard links to the database's, as Cargo's local clone
        makes them. Offline, a commit its database lacks fails. ``packages``: (url, oid, db name)."""
        real_git = shutil.which("git")
        fetch = self.driver.with_name("targo-fetch")
        self.driver.rename(fetch)
        executable(self.driver, "#!/bin/sh\n" + "'''exec' " + shlex.quote(sys.executable) + ' "$0" "$@" # ' + "'''\n" +
            "import os, pathlib, subprocess, sys\n" +
            f"git = {real_git!r}\npackages = {packages!r}\n" +
            "home = pathlib.Path(os.environ.get('CARGO_HOME', '/nonexistent'))\n" +
            "if sys.argv[1:3] == ['fetch', '--locked']:\n" +
            "    offline = '--offline' in sys.argv\n" +
            "    for url, oid, name in packages:\n" +
            "        db = home / 'git/db' / name\n" +
            "        held = db.is_dir() and subprocess.run([git, '--git-dir', str(db), 'cat-file', '-e', oid + '^{commit}'],\n" +
            "                                              capture_output=True).returncode == 0\n" +
            "        if not held:\n" +
            "            if offline:\n" +
            "                sys.exit(f'fixture cargo: {oid} is not in {db} and the fetch is offline')\n" +
            "            db.mkdir(parents=True, exist_ok=True)\n" +
            "            subprocess.run([git, 'init', '--bare', '-q', str(db)], check=True)\n" +
            "            subprocess.run(['git', 'fetch', '--no-tags', '--force', '--update-head-ok', '--recurse-submodules=no',\n" +
            "                            '--depth=1', url, '+' + oid + ':refs/commit/' + oid], cwd=db,\n" +
            "                           env={**os.environ, 'GIT_DIR': str(db)}, check=True)\n" +
            "        checkout = home / 'git/checkouts' / name / oid[:7]\n" +
            "        if not offline and not checkout.exists():\n" +
            "            subprocess.run([git, 'init', '-q', str(checkout)], check=True)\n" +
            "            for body in sorted((db / 'objects').rglob('*')):\n" +
            "                target = checkout / '.git/objects' / body.relative_to(db / 'objects')\n" +
            "                if body.is_file() and not target.exists():\n" +
            "                    target.parent.mkdir(parents=True, exist_ok=True)\n" +
            "                    os.link(body, target)\n" +
            "            if (db / 'shallow').exists():\n" +
            "                (checkout / '.git/shallow').write_bytes((db / 'shallow').read_bytes())\n" +
            "            subprocess.run([git, '-C', str(checkout), 'checkout', '-q', '--detach', oid], check=True)\n" +
            f"os.execv({str(fetch)!r}, [{str(fetch)!r}, *sys.argv[1:]])\n")

    def prepare(self, cargo_input=None, **options):
        receipt = self.work / "receipt.json"
        # The fake driver tests cache handoff and environment closure. Darwin
        # uses the explicit diagnostic test executor, as in the closure suite;
        # production _fetch still refuses without a resident custodian.
        executor = (
            mock.patch.dict(self.closure["dependency_closure"].__globals__,
                            {"_fetch": self.closure["_fetch_darwin"]})
            if sys.platform == "darwin" else nullcontext()
        )
        with executor:
            stage.prewarm_dependencies(self.source, self.work, HOST, receipt, [], cargo_input, self.policy_engine,
                                       **options)
        return stage.read_json(receipt)

    def test_prewarm_enforces_checkout_cache_selection_before_fetch(self):
        donor = self.root / "checkout cache"
        donor.mkdir()
        declaration = f"https://github.com/fixture/unselected#{'1' * 40}={donor}"
        with self.assertRaisesRegex(RuntimeError, "checkout caches do not match selected dependency sources"):
            self.prepare(checkout_cache_specs=[declaration])
        self.assertFalse(self.trace.exists())
        self.assertFalse((self.work / "receipt.json").exists())

    def locked_git_dependency(self):
        """A locked Git dependency whose commit a filled Cargo input home's git/db holds, and a
        stand-in driver that takes it as Cargo does (cargo_like_git). Returns the input home."""
        real_git = shutil.which("git")
        origin = self.root / "git-probe"
        subprocess.run([real_git, "init", "-q", str(origin)], check=True)
        for key, value in (("user.name", "fixture"), ("user.email", "fixture@example.invalid"),
                           ("core.hooksPath", os.devnull)):
            git(origin, "config", key, value)
        (origin / "Cargo.toml").write_text('[package]\nname="probe"\nversion="0.1.0"\nedition="2021"\n')
        (origin / "src").mkdir()
        (origin / "src/lib.rs").write_text("")
        git(origin, "add", ".")
        git(origin, "commit", "-qm", "fixture")
        oid = git(origin, "rev-parse", "HEAD")
        url = "https://github.com/Owner/probe"
        manifest = self.source / "Cargo.toml"
        manifest.write_text(manifest.read_text() + '[package]\nname="profile-root"\nversion="0.1.0"\n'
                            '[dependencies]\nprobe={git=' + json.dumps(url) + ', rev=' + json.dumps(oid) + '}\n')
        (self.source / "Cargo.lock").write_text('version=4\n[[package]]\nname="probe"\nversion="0.1.0"\nsource='
                                               + json.dumps(f"git+{url}?rev={oid}#{oid}") + '\n')
        given = self.root / "cargo-inputs"
        db = given / "git/db/probe-fixture"
        db.parent.mkdir(parents=True)
        subprocess.run([real_git, "init", "--bare", "-q", str(db)], check=True)
        subprocess.run([real_git, "-c", "protocol.file.allow=always", "-c", "maintenance.auto=false", "--git-dir",
                        str(db), "fetch", "--no-tags", str(origin), f"+{oid}:refs/commit/{oid}"],
                       check=True, capture_output=True)
        # The input home holds the commit, so no run asks Agh for it.
        self.recreator["_agh_source_fetch"] = lambda *_a, **_k: self.fail("the input home's database holds the commit")
        self.cargo_like_git([(url, oid, "probe-fixture")])
        return given

    def linked_db_objects(self):
        objects = self.work / "cargo-home/git/db/probe-fixture/objects"
        return [path for path in sorted(objects.rglob("*")) if path.is_file() and path.stat().st_nlink != 1]

    def test_a_prewarm_run_twice_on_one_commit_revalidates_its_reused_cache(self):
        # The 5062 relaunch (2026-11-15) stopped at its prewarm: "dependency Cargo bare DB contains
        # aliased/special or excessive files", the links being Cargo's own checkout of that database.
        given = self.locked_git_dependency()
        first = self.prepare(given)
        cache = self.work / "cargo-home"
        self.assertTrue((cache / "git/checkouts/probe-fixture").is_dir())
        self.assertTrue(self.linked_db_objects(), "the stand-in fetch hardlinks the database, as Cargo does")
        initial = stage.fingerprint(self.work / "initial-cache.json")
        second = self.prepare(given)
        # The first run lends the input home's database; the second finds the commit in the
        # database Cargo made in its own home on the first.
        self.assertEqual([row["method"] for row in first["transport"]["acquisitions"]], ["exact-local-object-cache"])
        self.assertEqual([(row["method"], row["cache_db"]) for row in second["transport"]["acquisitions"]],
                         [("exact-owned-cargo-cache", str(cache / "git/db/probe-fixture"))])
        # The same cache, reused: not filled again from the input home.
        self.assertEqual(stage.fingerprint(self.work / "initial-cache.json"), initial)
        self.assertNotEqual(first["cargo_home"], second["cargo_home"])
        self.assertTrue((cache / "git/checkouts/probe-fixture").is_dir())

    def test_a_db_object_linked_from_outside_the_cargo_home_still_refuses_on_reuse(self):
        given = self.locked_git_dependency()
        self.prepare(given)
        loose = next(path for path in self.linked_db_objects() if len(path.parent.name) == 2)
        outside = self.root / "outside-link"
        os.link(loose, outside)
        with self.assertRaisesRegex(RuntimeError, "aliased/special or excessive files"):
            self.prepare(given)
        # Cargo's checkouts went first; the database still carries the link from outside.
        self.assertFalse((self.work / "cargo-home/git/checkouts").exists())
        self.assertEqual(loose.stat().st_nlink, 2)
        self.assertEqual(outside.read_bytes(), loose.read_bytes())

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
        self.assertEqual(len(calls), 10)
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
        self.assertEqual([row["offline"] for row in report["input_acquisition"]["completed_fetches"]], [False]*5)
        self.assertEqual([row["offline"] for row in report["completed_fetches"]], [True]*5)
        self.assertEqual([row["offline"] for row in report["handoff_offline_replay"]["completed_fetches"]], [True]*5)
        stage.validate_dependency_preparation({"report": str(self.work / "receipt.json"),
                                               "cargo_home": report["cargo_home"]})

    def test_older_source_helper_and_its_resumed_receipt_keep_the_three_actual_passes(self):
        self.closure.pop("acquire_dependency_inputs")
        report = self.prepare()
        self.assertNotIn("input_acquisition", report)
        self.assertEqual(len(self.trace.read_text().splitlines()), 15)
        self.assertEqual(report["ceiling"]["fetch_passes"], 3)
        self.assertEqual([row["offline"] for row in report["completed_fetches"]], [False]*5+[True]*5)
        stage.validate_dependency_preparation({"report": str(self.work / "receipt.json"),
                                               "cargo_home": report["cargo_home"]})

    def assert_handoff_change_refused(self, change):
        original = self.cache_input
        def altered(source, destination, **options):
            result = original(source, destination, **options)
            if source == self.work / "cargo-home":
                if change == "roots":
                    recipe = self.source / self.closure["_RECIPE_INPUTS"][-1]
                    recipe.write_text(recipe.read_text().replace('path: "tool"', 'path: "new-tool"'))
                    (self.source / "new-tool").mkdir()
                    (self.source / "new-tool/Cargo.toml").write_text("[workspace]\nmembers=[]\n")
                    (self.source / "new-tool/Cargo.lock").write_text("version=4\n")
                elif change == "config":
                    (destination / "config.toml").write_text("[net]\nretry=1\n")
                else:
                    self.driver.write_text(self.driver.read_text() + "\n# changed after acquisition\n")
            return result
        self.mint["cargo_home_inputs"] = altered
        with self.assertRaisesRegex(RuntimeError, "changed during handoff|same ordered manifest/policy"):
            self.prepare()
        self.assertFalse((self.work / "receipt.json").exists())

    def test_changed_roots_between_acquisition_and_replay_never_ready(self):
        self.assert_handoff_change_refused("roots")

    def test_changed_config_between_acquisition_and_replay_never_ready(self):
        self.assert_handoff_change_refused("config")

    def test_changed_driver_between_acquisition_and_replay_never_ready(self):
        self.assert_handoff_change_refused("driver")

    def test_different_resolver_environment_in_the_replay_never_ready(self):
        original = self.closure["dependency_closure"]
        def changed(root, driver, env, **options):
            return original(root, driver, {**env, "CARGO_HTTP_TIMEOUT": "123"}, **options)
        self.closure["dependency_closure"] = changed
        with self.assertRaisesRegex(stage.Refused, "same ordered manifest/policy"):
            self.prepare()
        self.assertFalse((self.work / "receipt.json").exists())

    def test_acquisition_or_incomplete_replay_cannot_authorize_a_preparation(self):
        report = self.prepare()
        with self.assertRaisesRegex(stage.Refused, "offline fetch readiness"):
            stage.validate_preparation_fetches(report["input_acquisition"])
        for selected in ("completed_fetches", "manifests", "manifest_policy_sha256"):
            changed = copy.deepcopy(report)
            replay = changed["handoff_offline_replay"]
            replay[selected] = replay[selected][:-1]
            with self.subTest(selected=selected), self.assertRaises(stage.Refused):
                stage.validate_preparation_fetches(changed)
        changed = copy.deepcopy(report)
        changed["input_acquisition"]["manifests"].reverse()
        with self.assertRaisesRegex(stage.Refused, "same ordered manifest/policy"):
            stage.validate_preparation_fetches(changed)

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

    def test_cargo_env_is_judged_by_name_by_the_shared_policy(self):
        # Trust's own .cargo/config.toml (72166f7901) sets [env] RUST_MIN_STACK; the train's
        # fetch-only lane refused every [env] wholesale and stopped every tick at this step
        # (2026-11-17T22:12Z, cut cd8e74698194). Publication's policy judges [env] by name:
        # a loader, Git, proxy or compiler name refuses before any fetch or Cargo home, beside
        # main's own entry, and main's table prepares with its hash in the receipt.
        config = self.source / ".cargo/config.toml"
        config.parent.mkdir()
        for name in ("GIT_SSH_COMMAND", "DYLD_INSERT_LIBRARIES", "CARGO_HTTP_PROXY", "RUSTFLAGS"):
            with self.subTest(name=name):
                config.write_text(f'[env]\nRUST_MIN_STACK = "16777216"\n{name} = "x"\n')
                with self.assertRaisesRegex(stage.Refused,
                        f"Cargo config contains unsupported execution/source/lock authority: .*\\[env\\] {name}"):
                    self.prepare()
                self.assertFalse(self.trace.exists())
                self.assertFalse((self.work / "cargo-home").exists())
        config.write_text('[net]\ngit-fetch-with-cli = true\n\n'
                          "[env]\n"
                          "# The native_wp_body target imports trust-wp's bounded recursive controls.\n"
                          "# Match that workspace's debug-test stack default; nested Cargo configuration\n"
                          "# is not inherited here. Preserve an explicit caller's runtime stack setting.\n"
                          'RUST_MIN_STACK = { value = "16777216", force = false }\n')
        report = self.prepare()
        self.assertEqual(len(self.trace.read_text().splitlines()), 10)
        self.assertEqual(len(report["handoff_offline_replay"]["completed_fetches"]), 5)
        self.assertEqual(report["source_inputs_sha256"][str(config)], stage.file_hash(config))

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

    def fake_time(self, step, *, input_bytes, moving, still=None):
        """A clock that advances ``step`` seconds at each reading, from the real monotonic now,
        and a measure of what an item's watched paths hold: ``input_bytes`` for the input home's
        trees, nothing new under ``still``, and ``moving`` more bytes at each other reading."""
        state = {"start": time.monotonic(), "moved": 0}
        state["now"] = state["start"]
        given = self.root / "registry-input"

        def clock():
            state["now"] += step
            return state["now"]

        def measure(paths):
            if paths and all(given in Path(path).parents for path in paths):
                return input_bytes
            if paths == (still,):
                return 0
            state["moved"] += moving
            return state["moved"]
        return state, clock, measure

    def expected_ceiling(self, items, input_bytes):
        floor = stage.PREWARM_FLOOR_BYTES_PER_SECOND
        return stage.PREWARM_ITEM_SECONDS * items + -(-2 * input_bytes // floor)

    def test_prewarm_that_keeps_moving_outlives_the_former_total(self):
        # RL-55. One total bounded the whole preparation (900 s, then 3600 s); m86's ended at
        # offline fetch 32 of 55 on 2026-11-14 while every fetch was still moving. Each item is
        # now bounded by its progress, and the whole by a ceiling computed from its inputs.
        self.assertFalse(hasattr(stage, "DEPENDENCY_PREWARM_SECONDS"))
        given = self.registry_input()
        state, clock, measure = self.fake_time(120, input_bytes=256 << 30, moving=1 << 20)
        (self.root / "slow-fetch").write_text("")
        with mock.patch.dict(self.closure, {"PROGRESS_POLL_SECONDS": 0.02}):
            report = self.prepare(given, clock=clock, measure=measure, poll=0.01)
        # 2 input copies, no locked Git commit, 2 fetches of 5 manifests, 3 handoff copies.
        self.assertEqual((report["ceiling"]["items"], report["ceiling"]["input_bytes"]), (15, 256 << 30))
        self.assertEqual(report["ceiling"]["seconds"], self.expected_ceiling(15, 256 << 30))
        elapsed = state["now"] - state["start"]
        self.assertGreater(elapsed, 3600, "the preparation ran past the former total")
        self.assertLess(elapsed, report["ceiling"]["seconds"])
        self.assertEqual(len(report["input_acquisition"]["completed_fetches"]) + len(report["completed_fetches"]), 10)

    def test_prewarm_that_stalls_ends_naming_the_item(self):
        # RL-55. An item that stops moving is ended after the recreator's stall window, long
        # before the ceiling, and the refusal names it; nothing after it runs.
        given = self.registry_input()
        release = threading.Event()
        self.addCleanup(release.set)
        self.blocked_copy = ("registry/cache", release)
        target = self.work / "cargo-home/registry/cache"
        _state, clock, measure = self.fake_time(300, input_bytes=256 << 30, moving=1 << 20, still=target)
        with self.assertRaisesRegex(stage.Refused,
                f"dependency preparation ended the copy of cargo home input registry/cache into "
                f"{re.escape(str(self.work / 'cargo-home'))}: the copy of cargo home input registry/cache .* "
                "showed too little progress: 0 bytes observed"):
            self.prepare(given, clock=clock, measure=measure, poll=0.01)
        release.set()
        self.assertFalse(self.trace.exists())
        self.assertFalse((self.work / "receipt.json").exists())

    def test_prewarm_below_its_floor_rate_ends_at_its_computed_ceiling(self):
        # RL-55. An item that keeps moving above the stall floor, but whose preparation moves
        # slower than the ceiling's floor rate, is ended at the ceiling the preparation printed
        # at its start; a supervisor given another number refuses before anything runs.
        given = self.registry_input()
        input_bytes = 4 << 20
        state, clock, measure = self.fake_time(60, input_bytes=input_bytes, moving=64 << 10)
        planned = self.prepare(given, ceiling_only=True, clock=clock, measure=measure)
        seconds = self.expected_ceiling(15, input_bytes)
        self.assertEqual((planned["seconds"], planned["items"]), (seconds, 15))
        (self.work / "receipt.json").unlink()
        self.assertFalse((self.work / "cargo-home").exists())
        with self.assertRaisesRegex(stage.Refused, f"ceiling is {seconds} s, not the {seconds + 1} s"):
            self.prepare(given, ceiling_seconds=seconds + 1, clock=clock, measure=measure)
        self.assertFalse((self.work / "cargo-home").exists())
        (self.root / "slow-fetch").write_text("")
        begun = state["now"]
        printed = io.StringIO()
        with mock.patch.dict(self.closure, {"PROGRESS_POLL_SECONDS": 0.02}), \
                contextlib.redirect_stderr(printed), \
                self.assertRaisesRegex(RuntimeError, f"ceiling of {seconds} s, printed at its start") as ended:
            self.prepare(given, ceiling_seconds=seconds, clock=clock, measure=measure, poll=0.01)
        self.assertIn(f"dependency preparation ceiling: {seconds} s for 15 items", printed.getvalue())
        self.assertNotIn("too little progress", str(ended.exception))
        self.assertGreaterEqual(state["now"] - begun, seconds)
        self.assertFalse((self.work / "receipt.json").exists())


class DependencyLocalGitBudgetTests(unittest.TestCase):
    def transport(self):
        path = SCRIPT.with_name("daily_dependency_git.py")
        api = {"__file__": str(path), "__name__": "dependency_local_git_budget_tests"}
        exec(compile(path.read_bytes(), str(path), "exec"), api)
        return api

    def owner(self, **extra):
        recreator = stage.runpy.run_path(str(SCRIPT.parents[1] / "scripts/recreate_bootstrap.py"))
        names = ("_SubmoduleProgress", "_SubmoduleStalled", "_submodule_progress_bytes", "SUBMODULE_STALL_WINDOW_SECONDS")
        return {**{name: recreator[name] for name in names},
                "_provenance_git_environment": lambda: {},
                "_controlled_git_command": lambda args: ["fixed-git", *args], **extra}

    def test_local_acquisition_uses_finite_source_ceiling(self):
        # RL-55: a local transfer or gc is one item, bounded by its progress, not by a constant
        # (600 s and 120 s until 2026-11-17); the preparation's ceiling, printed at its start,
        # ends a running item and refuses the next before it starts, naming both.
        api = self.transport()
        calls, now = [], [100.0]
        fetch = ["-c", "protocol.file.allow=always", "-c", "fetch.fsckObjects=true", "-C",
                 "/owned/stage", "fetch", "--no-tags", "--depth=1", "/owned/cache",
                 "+" + "a" * 40 + ":refs/agh/trust-daily-dependencies/" + "a" * 40]
        owner = self.owner(_dependency_deadline=1000.0, _dependency_clock=lambda: now[0], _dependency_ceiling=900,
                           _run_submodule_update_process=lambda *args, **kwargs:
                               calls.append((args, kwargs)) or subprocess.CompletedProcess(args, 0))
        label = "the local transfer of probe"
        api["local_git"](owner, fetch, bounded=True, acquisition=True, label=label, paths=(Path("/owned/stage"),))
        self.assertIsNone(calls[-1][1]["timeout_seconds"])
        progress = calls[-1][1]["progress"]
        self.assertEqual((progress.label, progress.paths), (label, (Path("/owned/stage"),)))
        api["local_git"](owner, ["gc", "--auto"], bounded=True)
        self.assertIsNone(calls[-1][1]["timeout_seconds"])
        self.assertIsNotNone(calls[-1][1]["progress"])
        progress.begin()
        now[0] = 1000.0
        with self.assertRaisesRegex(owner["_SubmoduleStalled"],
                                    f"{label} was still running 900 s after it started when the preparation "
                                    "reached its ceiling of 900 s, printed at its start"):
            progress.check(["fixed-git"])
        count = len(calls)
        with self.assertRaisesRegex(RuntimeError, "deadline exhausted: it reached its ceiling of 900 s, "
                                    f"printed at its start, before {label}"):
            api["local_git"](owner, fetch, bounded=True, acquisition=True, label=label)
        self.assertEqual(len(calls), count)

    def test_fetch_item_never_walks_what_cargo_has_finished(self):
        # Each `targo fetch` item watched its whole Cargo home and walked all of it at its start
        # and at each sample, ty's checkout included (475,787 entries, 11.5 s on m86 at load 40):
        # the proof's offline fetches took 12.9 s each, 27009's 2.4 s (review, 2026-11-17). A
        # checkout or unpacked crate holding the .cargo-ok Cargo writes last is never walked;
        # growth anywhere else in the home still counts.
        temp = tempfile.TemporaryDirectory(prefix="dependency-fetch-measure-")
        self.addCleanup(temp.cleanup)
        home = Path(temp.name).resolve() / "cargo-home"
        finished = home / "git/checkouts/probe-0123456789abcdef/abcdef0"
        unpacked = home / "registry/src/index.crates.io-1949cf8c6b5b557f/probe-0.1.0"
        running = home / "git/checkouts/other-0123456789abcdef/1234567"
        for directory, done in ((finished, ".cargo-ok"), (unpacked, '{"v":1}'), (running, None)):
            (directory / "src").mkdir(parents=True)
            (directory / "src/lib.rs").write_text("// checked out\n")
            if done is not None:
                (directory / ".cargo-ok").write_text("" if done == ".cargo-ok" else done)
        for relative in ("registry/cache/index.crates.io-1949cf8c6b5b557f/probe-0.1.0.crate",
                         "registry/index/index.crates.io-1949cf8c6b5b557f/.cache/pr/ob/probe",
                         "git/db/probe-0123456789abcdef/objects/pack/pack-0.pack"):
            (home / relative).parent.mkdir(parents=True)
            (home / relative).write_bytes(b"\0" * 64)
        recreator = stage.runpy.run_path(str(SCRIPT.parents[1] / "scripts/recreate_bootstrap.py"))
        now = [0.0]
        bound = stage.PrewarmBound(recreator, self.transport(), {"seconds": 5000}, clock=lambda: now[0])
        watch = bound.item("locked fetch 1/1 Cargo.toml", (home,))
        scanned, scandir = [], os.scandir

        def spy(path):
            scanned.append(Path(path))
            return scandir(path)
        with mock.patch.object(stage.os, "scandir", side_effect=spy):
            watch.begin()
            self.assertEqual(stage.cargo_home_progress_bytes((home,)), 3 * 64 + len("// checked out\n"))
            (running / "src/grown.rs").write_bytes(b"\1" * 4096)
            (finished / "src/never-counted.rs").write_bytes(b"\1" * 8192)
            now[0] = 30.0
            watch.check(["targo", "fetch", "--locked", "--offline"])
        self.assertEqual(watch.received, 4096)
        for done in (finished, unpacked):
            self.assertFalse([path for path in scanned if path == done or done in path.parents], done)
        for walked in (running / "src", home / "registry/cache", home / "registry/index", home / "git/db"):
            self.assertIn(walked, scanned)

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
                 "--no-tags", "--depth=1", "--force", "--update-head-ok", "--recurse-submodules=no", "/owned/stage",
                 "+" + "a" * 40 + ":refs/commit/" + "a" * 40]
        owner = self.owner(_dependency_deadline=time.monotonic() + 900,
                           _run_submodule_update_process=mock.Mock(side_effect=subprocess.TimeoutExpired("fixed-git", 600)))
        with self.assertRaises(subprocess.TimeoutExpired):
            api["local_git"](owner, fetch, bounded=True, acquisition=True)
        owner["_run_submodule_update_process"] = mock.Mock(return_value=subprocess.CompletedProcess([], 2))
        with self.assertRaisesRegex(RuntimeError, "did not complete"):
            api["local_git"](owner, fetch, bounded=True, acquisition=True)



class DependencyFetchBoundaryTests(unittest.TestCase):
    setUp = PrewarmBoundaryTests.setUp
    cache_input = PrewarmBoundaryTests.cache_input
    prepare = PrewarmBoundaryTests.prepare
    registry_input = PrewarmBoundaryTests.registry_input
    cargo_like_git = PrewarmBoundaryTests.cargo_like_git

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

    def profile(self, sources, *, dropped=(), **options):
        """prepare_profile with a stand-in Agh that fetches from ``sources`` and then loses
        the objects named in ``dropped``; it records what each request asked of Agh."""
        api = self.transport()
        cache = self.work / "cargo-home"
        cache.mkdir(exist_ok=True)
        owner = dict(self.recreator)
        calls = []
        self.acquisition_calls = calls
        self.acquisition_options = []
        def acquire(url, stage, oid, ref, **kwargs):
            calls.append((url, oid))
            self.acquisition_options.append({key: value for key, value in kwargs.items() if key != "execute"})
            self.acquisition_store = stage.parent
            origin = sources[(url, oid)]
            # No detached auto-maintenance: it rewrites the stage's .git while the
            # recreator's custody walk reads it ("staged child Git custody contains
            # aliases/special files"), which failed these tests at random under load.
            subprocess.run(["git", "-c", "protocol.file.allow=always", "-c", "fetch.unpackLimit=1000000",
                            "-c", "maintenance.auto=false", "-C", str(stage),
                            "fetch", "--no-tags", str(origin), "+" + oid + ":" + ref],
                           check=True, capture_output=True)
            for name in dropped:
                (stage / ".git/objects" / name[:2] / name[2:]).unlink()
            return {"program": {"fixture": "local only"}, "repository": url,
                    "source": oid, "private_ref": ref, "commit": oid}
        owner["_agh_source_fetch"] = acquire
        policy, document = api["prepare_profile"](self.source, self.work, cache,
                            self.closure, owner, {"HOME": str(self.work), "CARGO_HOME": str(cache)},
                            deadline=time.monotonic() + 900, **options)
        return api, policy, document, calls

    def history(self, name):
        """A repository whose locked (current) commit no longer has bodies its ancestor had.
        Returns it, the current commit and every object only its ancestor reaches."""
        origin, _first = self.repository(name, extra={"src/old.rs": "// a body only the ancestor has\n"})
        (origin / "src/old.rs").unlink()
        (origin / "src/lib.rs").write_text("// the body the locked commit has\n")
        git(origin, "add", "-A")
        git(origin, "commit", "-qm", "current")
        current = git(origin, "rev-parse", "HEAD")
        every = {line.split()[0] for line in git(origin, "rev-list", "--objects", current).splitlines()}
        closure = {line.split()[0] for line in git(origin, "rev-list", "--objects", "--no-walk", current).splitlines()}
        return origin, current, every - closure

    def bare_copy(self, origin, store, *refs):
        """A bare repository at ``store`` holding ``refs`` of ``origin`` as loose objects."""
        store.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "init", "--bare", "-q", str(store)], check=True)
        subprocess.run(["git", "-c", "protocol.file.allow=always", "-c", "fetch.unpackLimit=1000000",
                        "-c", "maintenance.auto=false", "--git-dir", str(store), "fetch", "--no-tags",
                        str(origin), *refs], check=True, capture_output=True)
        return store

    def agh_profile(self, sources, **options):
        """prepare_profile with the recreator's own _agh_source_fetch, which builds the Agh
        command and binds a stand-in `agh` on PATH by identity. ``acquire``, prepare_profile's
        executor hook, receives each command it built, keeps it, and fetches the requested
        commit from ``sources`` in Agh's place. Returns the policy document and the commands."""
        api = self.transport()
        cache = self.work / "cargo-home"
        cache.mkdir(exist_ok=True)
        agh = self.root / "agh-bin/agh"
        executable(agh, "#!/bin/sh\necho 'the stand-in agh is never run' >&2\nexit 97\n")
        commands = []

        def acquire(command, _environment):
            commands.append(list(command))
            repository, destination = command[3], Path(command[4])
            oid, ref = command[command.index("--ref") + 1], command[command.index("--into") + 1]
            origin = sources[("https://github.com/" + repository + ".git", oid)]
            subprocess.run(["git", "-c", "protocol.file.allow=always", "-c", "fetch.unpackLimit=1000000",
                            "-c", "maintenance.auto=false", "-C", str(destination),
                            "fetch", "--no-tags", str(origin), "+" + oid + ":" + ref],
                           check=True, capture_output=True)
        with mock.patch.dict(os.environ, {"PATH": f"{agh.parent}{os.pathsep}{os.environ['PATH']}"}):
            _policy, document = api["prepare_profile"](
                self.source, self.work, cache, self.closure, dict(self.recreator),
                {"HOME": str(self.work), "CARGO_HOME": str(cache)}, deadline=time.monotonic() + 900,
                acquire=acquire, **options)
        return document, agh, commands

    def test_lock_commit_is_acquired_as_its_checkout_closure(self):
        # RL-54. A tick took a locked commit as the whole history before it (Agh, or a copy of
        # filled Cargo databases): 18-22 GB of trust-ir for one commit on m86, 2026-11-14.
        # A declared repository that holds the commit lends exactly its checkout closure, by a
        # depth-one local transfer through a relay; Agh is not asked.
        origin, current, ancestor_only = self.history("probe")
        url = "https://github.com/Owner/probe.git"
        lock = self.source / "Cargo.lock"
        self.declare("https://github.com/Owner/probe", current)
        # A second URL whose declared repository is stale (it lacks the locked commit), as the
        # train's clean cache lacked 7722f8495bc4: that commit goes to Agh's checkout closure,
        # with the declared repository as its checkout cache.
        other, older = self.repository("other")
        stale = self.bare_copy(other, self.root / "stale-other", f"+{older}:refs/heads/main")
        (other / "src/lib.rs").write_text("// newer than the stale cache\n")
        git(other, "commit", "-qam", "newer")
        newer = git(other, "rev-parse", "HEAD")
        other_url = "https://github.com/Owner/other.git"
        # A third URL with no declared repository: Agh's checkout closure, with no cache. Its
        # unfiltered whole-history fetch (native_exact) is what the closure replaces.
        third, pinned = self.repository("third")
        third_url = "https://github.com/Owner/third.git"
        for name, oid in (("other", newer), ("third", pinned)):
            lock.write_text(lock.read_text() + f'\n[[package]]\nname="{name}"\nversion="0.1.0"\n'
                            f'source="git+https://github.com/Owner/{name}#{oid}"\n')
        document, agh, commands = self.agh_profile({(other_url, newer): other, (third_url, pinned): third},
                                                   object_caches={url: origin, other_url: stale})
        stages = {key.split("#")[0]: Path(row["path"]) for key, row in document["stages"].items()}
        self.assertEqual(sorted(commands), [
            [str(agh), "repo", "fetch", "Owner/other", str(stages[other_url]), "--ref", newer,
             "--into", "refs/agh/trust-daily-dependencies/" + newer, "--checkout-closure", "--checkout-cache", str(stale)],
            [str(agh), "repo", "fetch", "Owner/third", str(stages[third_url]), "--ref", pinned,
             "--into", "refs/agh/trust-daily-dependencies/" + pinned, "--checkout-closure"]])
        rows = {row["commit"]: row for row in document["acquisitions"]}
        self.assertEqual(rows[current]["method"], "exact-local-object-cache")
        self.assertEqual(rows[current]["object_stores"], [str(origin / ".git/objects")])
        self.assertEqual((rows[newer]["method"], rows[newer]["checkout_cache"]), ("owner-routed-agh", str(stale)))
        self.assertEqual(rows[pinned]["method"], "owner-routed-agh")
        self.assertNotIn("checkout_cache", rows[pinned])
        self.assertEqual(rows[pinned]["program"]["resolved"], str(agh.resolve()))
        stage = Path(document["stages"][url + "#" + current]["path"])
        self.assertEqual((stage / ".git/shallow").read_text().split(), [current])
        held = set(git(stage, "cat-file", "--batch-all-objects", "--batch-check=%(objectname)").split())
        closure = {line.split()[0] for line in git(origin, "rev-list", "--objects", "--no-walk", current).splitlines()}
        self.assertEqual(held, closure)
        self.assertTrue(ancestor_only)
        self.assertFalse(held & ancestor_only)
        # The declared repository was read, never configured into the stage.
        self.assertFalse((stage / ".git/objects/info/alternates").exists())

    def test_prewarm_holds_no_ancestor_only_blob(self):
        # RL-54. The input Cargo home's databases held every ancestor's bodies (28 GB on m86,
        # 2026-11-14), and the preparation copied them into its home and from there into the
        # handoff. They are now object sources: only the locked commit's checkout closure enters.
        origin, current, ancestor_only = self.history("probe")
        url = "https://github.com/Owner/probe"
        self.declare(url, current)
        # A second crate of the same locked commit, as a workspace's crates are locked.
        lock = self.source / "Cargo.lock"
        lock.write_text(lock.read_text() + '\n[[package]]\nname="probe-macros"\nversion="0.1.0"\nsource='
                        + json.dumps(f"git+{url}?rev={current}#{current}") + '\n')
        given = self.registry_input()
        name = "probe-0123456789abcdef"
        db = self.bare_copy(origin, given / "git/db" / name, "+refs/heads/*:refs/heads/*")
        blobs = {oid for oid in ancestor_only if git(db, "cat-file", "-t", oid) == "blob"}
        self.assertTrue(blobs, "the input home holds an ancestor-only body")
        self.recreator["_agh_source_fetch"] = lambda *_a, **_k: self.fail("the input home's database holds the commit")
        self.cargo_like_git([(url, current, name)])
        report = self.prepare(given)
        handoff = Path(report["cargo_home"])
        stores = [path.parent for home in (self.work / "cargo-home", handoff)
                  for path in home.rglob("objects") if path.is_dir()]
        stores += [path / ".git" for path in self.work.glob("agh-git-*/source-*")]
        self.assertGreaterEqual(len(stores), 4)  # each home's database and checkout, and the stage
        for store in stores:
            self.assertFalse((store / "objects/info/alternates").exists(), store)
            for blob in blobs:
                found = subprocess.run(["git", "--git-dir", str(store), "cat-file", "-e", blob], capture_output=True)
                self.assertNotEqual(found.returncode, 0, f"{store} holds ancestor-only body {blob}")
        self.assertEqual([row["method"] for row in report["transport"]["acquisitions"]], ["exact-local-object-cache"])
        # The ceiling counts the commit's one acquisition, not its two locked rows.
        self.assertEqual(report["ceiling"]["git_commits"], 1)
        self.assertEqual(git(handoff / "git/db" / name, "show", current + ":src/lib.rs"),
                         "// the body the locked commit has")

    def test_closure_missing_a_checkout_blob_refuses(self):
        # RL-54. Nothing stands behind a checkout closure (no ancestry to fall back on), so each
        # is checked whole: a store that lacks a body the locked tree reaches is not lent, and
        # an acquisition that lacks one refuses, naming the body and its path.
        origin, oid = self.repository("probe", extra={"src/body.rs": "// a body the locked tree reaches\n"})
        url = "https://github.com/Owner/probe.git"
        self.declare("https://github.com/Owner/probe", oid)
        body = git(origin, "rev-parse", oid + ":src/body.rs")
        partial = self.bare_copy(origin, self.root / "partial", f"+{oid}:refs/heads/main")
        (partial / "objects" / body[:2] / body[2:]).unlink()
        with self.assertRaisesRegex(RuntimeError, f"checkout closure of {url} {oid[:12]} lacks 1 object\\(s\\) "
                                    f"its tree reaches: {body} \\(src/body.rs\\)"):
            self.profile({(url, oid): origin}, dropped=(body,), object_caches={url: partial})
        # The incomplete declared store was not lent; Agh was asked, with it as the cache.
        self.assertEqual(self.acquisition_calls, [(url, oid)])
        self.assertEqual(self.acquisition_options, [{"checkout_cache": partial}])

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
        subprocess.run(["git", "-c", "protocol.file.allow=always", "-c", "maintenance.auto=false", "--git-dir", str(db),
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
        # The preparation's ceiling reads the owner locks first, before its home exists.
        with self.assertRaisesRegex(RuntimeError, "dependency owner lock is missing: no committed lockfile "
                                    + re.escape(str(self.source / "Cargo.lock"))):
            self.prepare()
        self.assertFalse(self.trace.exists())
        self.assertFalse((self.work / "cargo-home").exists())
        with self.assertRaisesRegex(RuntimeError, "no committed lockfile"):
            self.profile({})

    def test_declared_cache_without_its_own_object_store_refuses_before_any_agh(self):
        # A declared cache lends its object directory and nothing else of it, so one that routes
        # its objects elsewhere, or shares another repository's store (a linked worktree's Git
        # directory, which names it in `commondir`), refuses before any acquisition.
        origin, oid = self.repository("probe")
        url = "https://github.com/Owner/probe.git"
        self.declare("https://github.com/Owner/probe", oid)
        routed = self.bare_copy(origin, self.root / "routed", f"+{oid}:refs/heads/main")
        (routed / "objects/info/alternates").write_text(str(origin / ".git/objects") + "\n")
        with self.assertRaisesRegex(RuntimeError, "declared dependency object cache routes its objects elsewhere: "
                                    + re.escape(str(routed / "objects/info/alternates"))):
            self.profile({(url, oid): origin}, object_caches={url: routed})
        self.assertEqual(self.acquisition_calls, [])
        worktree = self.root / "linked-worktree"
        git(origin, "worktree", "add", "--quiet", "--detach", str(worktree), oid)
        linked = origin / ".git/worktrees" / worktree.name
        self.assertTrue((linked / "commondir").is_file())
        for declared in (linked, worktree):  # its Git directory, and the checkout whose .git is a file
            with self.subTest(declared=declared), self.assertRaisesRegex(
                    RuntimeError, "must be a repository with its own object store: " + re.escape(str(declared))):
                self.profile({(url, oid): origin}, object_caches={url: declared})
            self.assertEqual(self.acquisition_calls, [])

    def test_corrupt_body_in_a_declared_cache_refuses_and_is_never_held(self):
        # The census that admits a declared cache asks only whether each object is present. A
        # body stored under its true name with other content is caught by the depth-one transfer
        # (fetch.fsckObjects, and the object it then lacks), which refuses: the tick stops rather
        # than take it, and no stage holds the true name.
        origin, oid = self.repository("probe", extra={"src/body.rs": "// the true body\n"})
        url = "https://github.com/Owner/probe.git"
        self.declare("https://github.com/Owner/probe", oid)
        body = git(origin, "rev-parse", oid + ":src/body.rs")
        corrupt = self.bare_copy(origin, self.root / "corrupt", f"+{oid}:refs/heads/main")
        loose = corrupt / "objects" / body[:2] / body[2:]
        content = b"// another body under the true name\n"
        loose.chmod(0o644)
        loose.write_bytes(zlib.compress(b"blob %d\0" % len(content) + content))
        with self.assertRaisesRegex(RuntimeError, "fixed local dependency Git process did not complete successfully: "
                                    f"the local transfer of {re.escape(url)} {oid[:12]} from its declared object caches"):
            self.profile({(url, oid): origin}, object_caches={url: corrupt})
        self.assertEqual(self.acquisition_calls, [])
        stages = list(self.work.glob("agh-git-*/source-*"))
        self.assertEqual(len(stages), 1)
        held = subprocess.run(["git", "-C", str(stages[0]), "cat-file", "-e", body], capture_output=True)
        self.assertNotEqual(held.returncode, 0, "the stage holds the corrupt body's true name")

    def test_closure_check_refuses_a_body_that_does_not_hash_to_its_name(self):
        # Git's --verify-objects reports a body whose content does not hash to its name on stderr
        # and still exits zero (Git 2.54 and 2.56, measured 2026-11-17): verify_checkout_closure
        # refuses on any diagnostic, and this is the case that rule exists for.
        api = self.transport()
        origin, oid = self.repository("probe", extra={"src/body.rs": "// the true body\n"})
        body = git(origin, "rev-parse", oid + ":src/body.rs")
        loose = origin / ".git/objects" / body[:2] / body[2:]
        content = b"// another body under the true name\n"
        loose.chmod(0o644)
        loose.write_bytes(zlib.compress(b"blob %d\0" % len(content) + content))
        scratch = self.root / "closure-scratch"
        scratch.mkdir()
        owner = {**self.recreator, "_dependency_deadline": time.monotonic() + 900}
        with self.assertRaisesRegex(RuntimeError, "checkout closure of the probe does not verify "
                                    f"\\(exit 0\\): .*hash mismatch {body}"):
            api["verify_checkout_closure"](owner, origin, oid, "the probe", scratch)

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
        self.assertEqual(api["parse_fetch"]([*good[:2], "--depth=1", *good[2:]])[1], oid)
        for argv in (["-c", "core.sshCommand=evil", *good], [*good[:-1], "+refs/heads/*:refs/remotes/origin/*"],
                     [*good[:-1], "+" + oid + ":refs/heads/main"],
                     [*good[:1], "--depth=2", *good[1:]], [*good[:1], "--deepen=1", *good[1:]],
                     [*good[:1], "--unshallow", *good[1:]],
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

    def test_selected_checkout_transfers_without_obsolete_history_bodies(self):
        origin, first = self.repository("probe")
        (origin / "src/lib.rs").write_text("// obsolete, unselected body\n")
        git(origin, "add", ".")
        git(origin, "commit", "-qm", "obsolete middle")
        obsolete = git(origin, "rev-parse", "HEAD:src/lib.rs")
        (origin / "src/lib.rs").write_text("// selected current body\n")
        git(origin, "add", ".")
        git(origin, "commit", "-qm", "current")
        current = git(origin, "rev-parse", "HEAD")
        self.declare("https://github.com/Owner/probe", current)
        (self.source / "Cargo.lock").write_text('version=4\n' + "".join(
            '[[package]]\nname="probe"\nversion="0.1.0"\n'
            'source="git+https://github.com/Owner/probe#' + oid + '"\n'
            for oid in (first, current)))
        sources = {("https://github.com/Owner/probe.git", oid): origin for oid in (first, current)}
        other, other_oid = self.repository("unrelated")
        lock = self.source / "Cargo.lock"
        lock.write_text(lock.read_text() + '\n[[package]]\nname="unrelated"\nversion="0.1.0"\n'
            'source="git+https://github.com/Owner/unrelated#' + other_oid + '"\n')
        sources[("https://github.com/Owner/unrelated.git", other_oid)] = other
        api, policy, document, _ = self.profile(sources)
        provider = Path(document["stages"]["https://github.com/Owner/probe.git#" + current]["path"])
        # Model Agh's complete selected checkouts and retained ancestry metadata,
        # with an obsolete historical body intentionally outside that closure.
        body = provider / ".git/objects" / obsolete[:2] / obsolete[2:]
        self.assertTrue(body.is_file())
        body.unlink()
        self.assertFalse((provider / ".git/shallow").exists())
        db = self.work / "cargo-home/git/db/native-selected-checkouts"
        db.parent.mkdir(parents=True)
        subprocess.run(["git", "init", "--bare", "-q", str(db)], check=True)
        old = Path.cwd()
        try:
            os.chdir(db)
            with mock.patch.dict(os.environ, {"GIT_DIR": str(db)}, clear=True):
                for oid in (current, first, current):
                    # Native Cargo reinitializes a shallow DB before another
                    # request. Each callback must preserve the whole approved
                    # pin set needed by the later offline handoff.
                    for path in db.iterdir():
                        if path.is_dir():
                            shutil.rmtree(path)
                        else:
                            path.unlink()
                    subprocess.run(["git", "init", "--bare", "-q", str(db)], check=True)
                    api["git_entry"](policy, ["fetch", "--no-tags", "--force", "--update-head-ok",
                        "--recurse-submodules=no", "https://github.com/Owner/probe",
                        "+" + oid + ":refs/commit/" + oid])
                    for pin in (first, current):
                        self.assertEqual(git(db, "rev-parse", "refs/commit/" + pin), pin)
                        for path in ("Cargo.toml", "src/lib.rs"):
                            self.assertEqual(git(db, "show", pin + ":" + path), git(origin, "show", pin + ":" + path))
                    self.assertNotEqual(subprocess.run(["git", "-C", str(db), "cat-file", "-e", other_oid],
                        capture_output=True).returncode, 0)
                    self.assertTrue((db / "FETCH_HEAD").read_text().startswith(oid + "\t"))
        finally:
            os.chdir(old)
        self.assertFalse((provider / ".git/shallow").exists())
        git(db, "fsck", "--full")
        # Both same-URL pins survive the next preparation without acquisition
        # or a guessed Cargo URL-hash directory; the unrelated URL still needs
        # its own owner acquisition rather than leaking into this DB.
        _, _, imported, calls = self.profile({("https://github.com/Owner/unrelated.git", other_oid): other})
        self.assertEqual(calls, [("https://github.com/Owner/unrelated.git", other_oid)])
        for oid in (first, current):
            row = imported["stages"]["https://github.com/Owner/probe.git#" + oid]
            target = Path(row["path"])
            self.assertEqual(git(target, "rev-parse", row["ref"]), oid)
            for path in ("Cargo.toml", "src/lib.rs"):
                self.assertEqual(git(target, "show", oid + ":" + path), git(origin, "show", oid + ":" + path))

    def test_selected_checkout_missing_current_body_still_refuses(self):
        origin, oid = self.repository("probe")
        self.declare("https://github.com/Owner/probe", oid)
        api, policy, document, _ = self.profile({("https://github.com/Owner/probe.git", oid): origin})
        provider = Path(document["stages"]["https://github.com/Owner/probe.git#" + oid]["path"])
        current = git(provider, "rev-parse", oid + ":src/lib.rs")
        body = provider / ".git/objects" / current[:2] / current[2:]
        self.assertTrue(body.is_file())
        body.unlink()
        db = self.work / "cargo-home/git/db/missing-selected-body"
        db.parent.mkdir(parents=True)
        subprocess.run(["git", "init", "--bare", "-q", str(db)], check=True)
        old = Path.cwd()
        try:
            os.chdir(db)
            with mock.patch.dict(os.environ, {"GIT_DIR": str(db)}, clear=True), \
                    self.assertRaisesRegex(RuntimeError, "did not complete"):
                api["git_entry"](policy, ["fetch", "--no-tags", "--force", "--update-head-ok",
                    "--recurse-submodules=no", "https://github.com/Owner/probe",
                    "+" + oid + ":refs/commit/" + oid])
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
        for name in (*names, "scripts/source_working_cache.py"):
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


class BuildTreeManagerSourceTests(unittest.TestCase):
    def test_the_runner_asks_the_managers_x_py_asks_and_the_one_the_script_builds(self):
        # The runner's probe copies x.py's in-tree lease frontends and the path
        # scripts/build-tree-manager.sh builds. Were either to move without it, the runner
        # would report a manager the mint's x.py never asks, and the mint would refuse its
        # lease after the prewarm, the failure the build-tree-manager step removed.
        root = SCRIPT.parents[1]
        frontend = next(node for node in ast.walk(ast.parse((root / "x.py").read_text(encoding="utf-8")))
                        if isinstance(node, ast.FunctionDef) and node.name == "_trust_build_lock_frontend")
        in_tree = tuple("/".join(argument.value for argument in call.args[1:])
                        for loop in ast.walk(frontend) if isinstance(loop, ast.For) and isinstance(loop.iter, ast.Tuple)
                        for call in loop.iter.elts
                        if isinstance(call, ast.Call) and ast.unparse(call.func) == "os.path.join"
                        and ast.unparse(call.args[0]) == "rust_dir")
        self.assertEqual(in_tree, stage.TREE_MANAGERS)
        constants = {node.value for node in ast.walk(frontend) if isinstance(node, ast.Constant)}
        self.assertEqual({value for value in constants if isinstance(value, bytes)}, {stage.MANAGER_PROTOCOL})
        self.assertLessEqual({"--trust-build-tree-lock", "--protocol"}, constants)
        script = (root / "scripts/build-tree-manager.sh").read_text(encoding="utf-8")
        settings = dict(re.findall(r'^(PROTOCOL|target|binary)="([^"]*)"$', script, re.MULTILINE))
        self.assertEqual(settings["PROTOCOL"].encode() + b"\n", stage.MANAGER_PROTOCOL)
        built = settings["binary"].replace("$target", settings["target"])
        self.assertEqual(built, "$root/" + stage.TREE_MANAGERS[-1])


class KeptAghTests(unittest.TestCase):
    """keep_agh: a run's own copy of the Agh on PATH, which an update of the installed one cannot reach."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.state = self.root / "state"
        self.state.mkdir()
        self.app = self.root / "Applications/Fixture.app"
        self.link = self.root / "local-bin/agh"
        self.link.parent.mkdir()
        # As ~/.local/bin/agh is: a link to the bundle's own link, which names the program.
        self.link.symlink_to(self.app / "Contents/MacOS/agh")
        self.path = f"{self.link.parent}{os.pathsep}/usr/bin{os.pathsep}/bin"
        identity = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")),
                                  run_name="fixture_kept_agh")["_agh_source_identity"]
        # The identity each acquisition records for its Agh before it starts and compares at its end.
        self.identity = lambda agh: identity(Path(agh))

    def install(self, version, answer="echo 'agh @VERSION@'; exit 0"):
        """Install an aterm as its updater does: a whole new bundle in the old one's place."""
        staged = self.root / f"staged-{version}/Fixture.app"
        executable(staged / "Contents/MacOS/aterm", stand_in_agh(version, answer))
        (staged / "Contents/MacOS/agh").symlink_to("aterm")
        (staged / "Contents/Info.plist").write_text(f"<plist>{version}</plist>\n")
        (staged / "Contents/MacOS/aterm").chmod(0o555)
        if self.app.exists():
            os.replace(self.app, self.root / f"replaced-by-{version}.app")
        self.app.parent.mkdir(exist_ok=True)
        os.replace(staged, self.app)

    def answer(self, agh):
        return subprocess.run([str(agh), "version"], capture_output=True, text=True, timeout=30).stdout

    def slot(self, origin=None):
        """The directory keep_agh keeps a copy of `origin` (the installed bundle) in."""
        return self.state / "kept-agh/program" / stage.fingerprint(origin or self.app)["sha256"]

    def test_reused_hash_slot_must_not_be_a_symlink(self):
        self.install("1.0")
        stage.keep_agh(self.state, self.path)
        slot = self.slot()
        outside = self.root / "outside-state-slot"
        slot.rename(outside)
        (outside / "bin/agh").unlink()
        (outside / "bin").rmdir()
        slot.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(stage.Refused, "slot"):
            stage.keep_agh(self.state, self.path)
        self.assertFalse((outside / "bin").exists())
        self.assertTrue(slot.is_symlink())

    def test_reused_alias_parent_must_not_be_a_symlink(self):
        self.install("1.0")
        stage.keep_agh(self.state, self.path)
        parent = self.slot() / "bin"
        outside = self.root / "outside-state-alias"
        parent.rename(outside)
        parent.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(stage.Refused, "link directory"):
            stage.keep_agh(self.state, self.path)
        self.assertTrue(parent.is_symlink())
        self.assertTrue((outside / "agh").is_symlink())

    def protect(self, *protected):
        """macOS's App Management: a copied bundle one of whose programs has run can no longer be
        changed or removed by a process outside its signer (EPERM, measured 2026-11-17 on m86)."""
        real = stage.remove_tree

        def remove_tree(path):
            if any(Path(path) == item or Path(path).is_relative_to(item) for item in protected):
                raise PermissionError(1, "Operation not permitted", str(path))
            real(path)
        return mock.patch.object(stage, "remove_tree", remove_tree)

    def test_a_bundled_agh_is_kept_with_its_bundle_and_an_update_cannot_change_it(self):
        self.install("1.0")
        kept = stage.keep_agh(self.state, self.path)
        slot = self.slot()
        self.assertEqual(kept, {
            "selected": str(self.link), "program": str(self.app / "Contents/MacOS/aterm"),
            "kept": str(slot / "bin/agh"), "directory": str(slot / "bin"),
            "executable": str(slot / "Fixture.app/Contents/MacOS/aterm"),
            "sha256": hashlib.sha256(stand_in_agh("1.0").encode()).hexdigest(), "version": "agh 1.0",
            "reused": False, "left": []})
        # The directory a run puts on its PATH holds the one name; the bundle is whole beside it.
        self.assertEqual(os.listdir(slot / "bin"), ["agh"])
        self.assertEqual(Path(kept["kept"]).resolve(), Path(kept["executable"]))
        self.assertEqual((slot / "Fixture.app/Contents/Info.plist").read_text(), "<plist>1.0</plist>\n")
        self.assertEqual(os.readlink(slot / "Fixture.app/Contents/MacOS/agh"), "aterm")
        installed, copy = self.identity(str(self.link)), self.identity(kept["kept"])
        self.assertEqual(installed["sha256"], copy["sha256"])

        self.install("2.0")
        # What ended the 18:26Z tick on 2026-11-16: the identity an acquisition compares at
        # its end is another program's. The run's copy is the file it was.
        self.assertNotEqual(self.identity(str(self.link)), installed)
        self.assertEqual(self.identity(kept["kept"]), copy)
        self.assertEqual((self.answer(self.link), self.answer(kept["kept"])), ("agh 2.0\n", "agh 1.0\n"))

        # The next run keeps the Agh then installed in a copy of its own, and removes the
        # earlier copy, read-only files and all, when macOS lets it.
        again = stage.keep_agh(self.state, self.path)
        self.assertEqual((again["kept"], again["version"], again["reused"], again["left"]),
                         (str(self.slot() / "bin/agh"), "agh 2.0", False, []))
        self.assertNotEqual(again["kept"], kept["kept"])
        self.assertEqual(self.identity(again["kept"])["sha256"], self.identity(str(self.link))["sha256"])
        self.assertEqual(os.listdir(self.state / "kept-agh/program"), [self.slot().name])
        self.assertEqual(os.listdir(self.state / "kept-agh"), ["program"])

    def test_an_agh_outside_a_bundle_is_kept_as_one_file(self):
        program = self.root / "tools/agh-0.3"
        executable(program, stand_in_agh("0.3"))
        self.link.unlink()
        self.link.symlink_to(program)
        kept = stage.keep_agh(self.state, self.path)
        home, slot = self.state / "kept-agh", self.slot(program)
        self.assertEqual((kept["program"], kept["executable"], kept["version"]),
                         (str(program), str(slot / "agh-0.3"), "agh 0.3"))
        name = slot.name
        self.assertEqual(sorted(str(path.relative_to(home)) for path in home.rglob("*")),
                         ["program", f"program/{name}", f"program/{name}/agh-0.3",
                          f"program/{name}/bin", f"program/{name}/bin/agh"])
        self.assertEqual((slot / "agh-0.3").stat().st_mode & 0o777, 0o755)

    def test_a_path_without_agh_keeps_nothing(self):
        self.assertIsNone(stage.keep_agh(self.state, "/usr/bin" + os.pathsep + "/bin"))
        self.assertFalse((self.state / "kept-agh").exists())
        before = os.environ.get("PATH")
        with mock.patch.dict(os.environ, {"PATH": "/usr/bin" + os.pathsep + "/bin"}):
            with stage.agh_kept_in(self.state) as kept:
                self.assertIsNone(kept)
                self.assertEqual(os.environ["PATH"], "/usr/bin" + os.pathsep + "/bin")
        self.assertEqual(os.environ.get("PATH"), before)

    def test_the_kept_agh_is_first_on_the_process_path_only_inside_its_block(self):
        self.install("1.0")
        with mock.patch.dict(os.environ, {"PATH": self.path}):
            with self.assertRaisesRegex(RuntimeError, "the block's own error"):
                with stage.agh_kept_in(self.state) as kept:
                    self.assertEqual(os.environ["PATH"], kept["directory"] + os.pathsep + self.path)
                    self.assertEqual(shutil.which("agh"), kept["kept"])
                    raise RuntimeError("the block's own error")
            self.assertEqual(os.environ["PATH"], self.path)
            self.assertEqual(shutil.which("agh"), str(self.link))

    def test_a_copy_that_is_not_the_selected_agh_or_does_not_run_refuses(self):
        # macOS ends an application's executable that starts outside its bundle; the stand-in
        # ends itself the same way.
        self.install("1.0", answer="kill -9 $$")
        with self.assertRaisesRegex(stage.Refused, r"does not run from .*/kept-agh/program/[0-9a-f]{64}/bin/agh: `agh version` exited -9"):
            stage.keep_agh(self.state, self.path)
        self.install("1.1", answer="echo 'no such verb' >&2; exit 2")
        with self.assertRaisesRegex(stage.Refused, r"`agh version` exited 2: no such verb"):
            stage.keep_agh(self.state, self.path)

        self.install("2.0")
        real, nested = shutil.copytree, []

        def updated_while_copied(source, destination, *arguments, **options):
            # shutil copies each directory through this same name; the update lands once,
            # after the whole bundle.
            nested.append(source)
            try:
                real(source, destination, *arguments, **options)
            finally:
                nested.pop()
            if not nested:
                (Path(destination) / "Contents/Info.plist").write_text("<plist>2.1</plist>\n")
        with mock.patch.object(stage.shutil, "copytree", updated_while_copied), \
                self.assertRaisesRegex(stage.Refused, "Agh changed while this run copied it"):
            stage.keep_agh(self.state, self.path)

    def test_an_unchanged_agh_is_reused_and_its_copy_is_never_written_again(self):
        self.install("1.0")
        first = stage.keep_agh(self.state, self.path)
        # The copy has run (`agh version`), so macOS now refuses this process any change to it.
        with self.protect(self.slot()), \
                mock.patch.object(stage.shutil, "copytree", side_effect=AssertionError("copied again")):
            again = stage.keep_agh(self.state, self.path)
        self.assertEqual({**again, "reused": False}, first)
        self.assertTrue(again["reused"])
        self.assertEqual(self.answer(again["kept"]), "agh 1.0\n")

    def test_an_earlier_copy_macos_protects_is_left_named_and_the_run_goes_on(self):
        # m86, 2026-11-17T17:14Z: the tick after the first ended at its start with
        # "[Errno 1] Operation not permitted: .../kept-agh/program/aterm.app".
        self.install("1.0")
        first = stage.keep_agh(self.state, self.path)
        earlier = Path(first["directory"]).parent
        self.install("2.0")
        with self.protect(earlier), mock.patch("sys.stderr", new_callable=io.StringIO) as said:
            kept = stage.keep_agh(self.state, self.path)
        self.assertEqual((kept["version"], kept["reused"], kept["left"]), ("agh 2.0", False, [str(earlier)]))
        self.assertIn(f"remove from a session in aterm: {earlier}", said.getvalue())
        self.assertEqual(self.answer(first["kept"]), "agh 1.0\n")
        # Once something allowed removes it, the next run names nothing.
        self.assertEqual(stage.keep_agh(self.state, self.path)["left"], [])
        self.assertFalse(earlier.exists())

    def test_the_single_copy_layout_of_an_earlier_runner_does_not_stop_the_run(self):
        # trust d0b7f21a61 kept one copy at kept-agh/program/NAME.app with its link in kept-agh/bin.
        self.install("1.0")
        legacy = self.state / "kept-agh/program/Fixture.app"
        shutil.copytree(self.app, legacy, symlinks=True)
        (self.state / "kept-agh/bin").mkdir()
        (self.state / "kept-agh/bin/agh").symlink_to(legacy / "Contents/MacOS/aterm")
        self.install("2.0")
        with self.protect(legacy):
            kept = stage.keep_agh(self.state, self.path)
        self.assertEqual((kept["version"], kept["left"]), ("agh 2.0", [str(legacy)]))
        self.assertFalse((self.state / "kept-agh/bin").exists())
        kept = stage.keep_agh(self.state, self.path)
        self.assertEqual((kept["reused"], kept["left"]), (True, []))
        self.assertEqual(os.listdir(self.state / "kept-agh/program"), [self.slot().name])

    def test_an_unfinished_copy_is_made_again_and_one_that_cannot_go_refuses(self):
        self.install("1.0")
        slot = self.slot()
        (slot / "Fixture.app/Contents").mkdir(parents=True)  # a run that ended while copying
        kept = stage.keep_agh(self.state, self.path)
        self.assertEqual((kept["version"], kept["reused"]), ("agh 1.0", False))
        (slot / "Fixture.app/Contents/Info.plist").write_text("<plist>edited</plist>\n")
        with self.protect(slot), self.assertRaisesRegex(stage.Refused, "neither whole nor removable"):
            stage.keep_agh(self.state, self.path)

    def test_a_kept_directory_that_is_not_the_runs_own_refuses(self):
        self.install("1.0")
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir()
        (self.state / "kept-agh").symlink_to(elsewhere)
        with self.assertRaisesRegex(stage.Refused, "must be this state root's own directory"):
            stage.keep_agh(self.state, self.path)
        self.assertEqual(os.listdir(elsewhere), [])
        (self.state / "kept-agh").unlink()
        # A PATH that already selects this root's copy: replacing it would delete its own source.
        kept = stage.keep_agh(self.state, self.path)
        with self.assertRaisesRegex(stage.Refused, "PATH already selects the Agh a run kept"):
            stage.keep_agh(self.state, kept["directory"] + os.pathsep + self.path)
        self.assertEqual(self.answer(kept["kept"]), "agh 1.0\n")


class DailyCliTests(unittest.TestCase):
    def test_dry_run_refuses_other_actions_before_dispatch(self):
        unsupported = (["run"], ["status"], ["train", "status"],
                       ["train", "install"], ["train", "remove"])
        with tempfile.TemporaryDirectory(prefix="daily-cli-dry-run-") as temporary:
            state = Path(temporary) / "uncreated-state"
            with mock.patch.object(stage, "Runner", side_effect=AssertionError("runner dispatched")) as runner, \
                    mock.patch.object(stage, "train_main", side_effect=AssertionError("train dispatched")) as train, \
                    mock.patch.object(stage, "read_json", side_effect=AssertionError("status dispatched")) as status:
                for words in unsupported:
                    with self.subTest(words=words), contextlib.redirect_stderr(io.StringIO()) as diagnostic:
                        with self.assertRaises(SystemExit) as refused:
                            stage.main([*words, "--dry-run", "--state-root", str(state)])
                        self.assertEqual(refused.exception.code, 2)
                        self.assertIn("--dry-run belongs to train run", diagnostic.getvalue())
                runner.assert_not_called()
                train.assert_not_called()
                status.assert_not_called()
            self.assertFalse(state.exists())

    def test_dry_run_keeps_explicit_and_default_train_run_dispatch(self):
        for words in (["train"], ["train", "run"]):
            with self.subTest(words=words), mock.patch.object(stage, "train_main", return_value=0) as train:
                self.assertEqual(stage.main([*words, "--dry-run"]), 0)
                train.assert_called_once()
                args = train.call_args.args[0]
                self.assertTrue(args.dry_run)
                self.assertEqual(args.action, "train")
                self.assertEqual(args.verb, words[1] if len(words) == 2 else None)


class TrainSourceObjectTests(unittest.TestCase):
    PATH = "first-party/fixture"
    URL = "https://github.com/fixture/child.git"

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="train-source-objects-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.state = self.root / "train"
        self.state.mkdir()
        self.owner = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")), run_name="source_object_fixture")
        self.external = self.root / "external"
        self.repository(self.external, "external")
        self.caches = {self.PATH: self.external}
        self.manager = stage.TrainSourceObjects(self.state, self.owner, [f"{self.PATH}={self.external}"])

    def repository(self, path, content):
        path.mkdir(parents=True)
        subprocess.run(["git", "init", "-q", "-b", "main", "--template=", str(path)], check=True)
        (path / "README").write_text(content)
        git(path, "add", "README")
        self.commit(path, "fixture")
        git(path, "remote", "add", "origin", self.URL)
        return git(path, "rev-parse", "HEAD")

    def commit(self, path, message):
        git(path, "-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid",
            "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", "commit", "-qm", message)

    def build(self, name, content="selected", *, child_from=None):
        build = self.state / "builds" / name
        source, child = build / "source", build / "source" / self.PATH
        self.repository(source, "controller")
        if child_from is None:
            pin = self.repository(child, content)
        else:
            child.parent.mkdir(parents=True)
            subprocess.run(["git", "clone", "--quiet", "--no-hardlinks", "--template=",
                            str(child_from), str(child)], check=True)
            git(child, "remote", "set-url", "origin", self.URL)
            pin = git(child, "rev-parse", "HEAD")
        (source / ".gitmodules").write_text(
            f'[submodule "fixture"]\n\tpath = {self.PATH}\n\turl = {self.URL}\n')
        git(source, "add", ".gitmodules")
        git(source, "update-index", "--add", "--cacheinfo", "160000", pin, self.PATH)
        self.commit(source, "selected child")
        stage.atomic_json(build / "train-build.json", {"schema": stage.TRAIN_SCHEMA,
                                                       "main": git(source, "rev-parse", "HEAD")})
        self.manager.capture(source, build, self.caches)
        return build, source, child, pin

    def select(self, source, caches, good):
        return self.manager.select(self.owner["_indexed_submodules"](source), caches, good)

    def next_source(self, source, name):
        destination = self.root / name
        subprocess.run(["git", "clone", "--quiet", "--no-hardlinks", "--template=",
                        str(source), str(destination)], check=True)
        return destination

    def files(self, root):
        return {str(path.relative_to(root)): (path.read_bytes(), stat.S_IMODE(path.stat().st_mode),
                                             path.stat().st_ino, path.stat().st_nlink)
                for path in root.rglob("*") if path.is_file()}

    def failed(self, build):
        return {"status": "failed", "build_dir": str(build)}

    def test_failed_late_cut_reuses_exact_pin_after_real_retirement_without_copying(self):
        build, source, child, pin = self.build("failed")
        next_source = self.next_source(source, "next")
        original = (child / ".git").stat()
        external = self.files(self.external)
        with stage.train_lock(self.state) as owned:
            self.assertTrue(owned)
            self.manager.retain_failed(self.failed(build), None)
            self.assertFalse((child / ".git").exists())
            self.assertEqual(stage.retire_builds(self.state, None), [])
            self.assertFalse(build.exists())
            donor = self.select(next_source, self.caches, None)[self.PATH]
            retained = (donor / ".git").stat()
            self.assertEqual((retained.st_dev, retained.st_ino), (original.st_dev, original.st_ino))
            self.assertFalse((donor / "README").exists())
            self.assertEqual(git(donor, "show", pin + ":README"), "selected")
            self.assertEqual(self.files(self.external), external)
            self.assertEqual({path.name for path in donor.parent.iterdir()}, {"current.json", donor.name})

    def test_exact_last_good_is_preferred_and_does_not_make_another_donor(self):
        good_build, good_source, good_child, _pin = self.build("good")
        failed, source, child, _pin = self.build("failed", child_from=good_child)
        next_source = self.next_source(source, "next")
        good = {"build_dir": str(good_build)}
        # Previously retained independent snapshots need no new receipt or write.
        (good_build / "source-object-pins.json").unlink()
        stage.atomic_json(good_build / "source.owner.json", {
            "schema": stage.SCHEMA, "snapshot_kind": "independent-git-v1", "path": str(good_source)})
        original_good = self.files(good_build)
        with stage.train_lock(self.state):
            self.manager.retain_failed(self.failed(failed), good)
            self.assertTrue((child / ".git").is_dir())
            self.assertFalse((self.state / "source-objects-v1").exists())
            self.assertEqual(stage.retire_builds(self.state, good_build), [])
            self.assertEqual(self.select(next_source, self.caches, good)[self.PATH], good_child)
            self.assertTrue((good_source / ".git").is_dir())
            self.assertEqual(self.files(good_build), original_good)

    def test_interrupted_transfer_keeps_working_donor_then_retries_and_bounds_replacement(self):
        old, source_a, _child_a, _pin_a = self.build("old", "A")
        source_a = self.next_source(source_a, "source-a")
        with stage.train_lock(self.state):
            self.manager.retain_failed(self.failed(old), None)
            stage.retire_builds(self.state, None)
            old_donor = self.select(source_a, self.caches, None)[self.PATH]
            build, source_b, child, pin_b = self.build("new", "B")
            source_b = self.next_source(source_b, "source-b")
            actual_move = self.owner["_source_object_exclusive_move"]
            def interrupted(parent, container):
                move, close = actual_move(parent, container)
                def move_then_interrupt(source, destination):
                    move(source, destination)
                    raise InterruptedError("after the physical object transfer")
                return move_then_interrupt, close
            with mock.patch.dict(self.owner, {"_source_object_exclusive_move": interrupted}):
                with self.assertRaisesRegex(InterruptedError, "physical object transfer"):
                    self.manager.retain_failed(self.failed(build), None)
            self.assertFalse((child / ".git").exists())
            self.assertEqual(self.select(source_a, self.caches, None)[self.PATH], old_donor)
            self.assertTrue(old_donor.exists())
            self.manager.retain_failed(self.failed(build), None)
            self.assertEqual(stage.retire_builds(self.state, None), [])
            donor = self.select(source_b, self.caches, None)[self.PATH]
            self.assertEqual(git(donor, "show", pin_b + ":README"), "B")
            self.assertFalse(old_donor.exists())
            self.assertEqual(self.select(source_a, self.caches, None), self.caches)
            self.assertEqual({path.name for path in donor.parent.iterdir()}, {"current.json", donor.name})

    def test_changed_repository_or_pin_never_reuses_the_retained_donor(self):
        build, source, _child, _pin = self.build("failed")
        next_source = self.next_source(source, "next")
        with stage.train_lock(self.state):
            self.manager.retain_failed(self.failed(build), None)
            stage.retire_builds(self.state, None)
            modules = next_source / ".gitmodules"
            modules.write_text(modules.read_text().replace(self.URL, "https://github.com/fixture/other.git"))
            git(next_source, "add", ".gitmodules")
            self.assertEqual(self.select(next_source, self.caches, None), self.caches)
            modules.write_text(modules.read_text().replace("https://github.com/fixture/other.git", self.URL))
            git(next_source, "add", ".gitmodules")
            git(next_source, "update-index", "--cacheinfo", "160000", "1" * 40, self.PATH)
            self.assertEqual(self.select(next_source, self.caches, None), self.caches)

    def test_unknown_capture_and_bad_child_custody_do_not_replace_working_donor(self):
        old, source, _child, _pin = self.build("old", "A")
        next_source = self.next_source(source, "next")
        with stage.train_lock(self.state):
            self.manager.retain_failed(self.failed(old), None)
            stage.retire_builds(self.state, None)
            donor = self.select(next_source, self.caches, None)[self.PATH]
            original = self.files(donor)
            external = self.files(self.external)
            for name in ("alternates", "hooks", "symlink", "capture"):
                with self.subTest(name=name):
                    build, _source, child, _pin = self.build(name, name)
                    if name == "alternates":
                        (child / ".git/objects/info/alternates").write_text(str(self.external / ".git/objects") + "\n")
                    elif name == "hooks":
                        git(child, "config", "core.hooksPath", str(self.external))
                    elif name == "symlink":
                        child.rename(child.with_name("original"))
                        child.symlink_to(self.external, target_is_directory=True)
                    else:
                        stage.atomic_json(build / "source-object-pins.json", {"schema": "unknown"})
                    self.manager.retain_failed(self.failed(build), None)
                    self.assertEqual(self.files(donor), original)
                    self.assertEqual(self.files(self.external), external)

    def test_creation_interrupted_after_mkdir_reuses_empty_slot_without_deleting_files(self):
        build, source, _child, _pin = self.build("failed")
        next_source = self.next_source(source, "next")
        slot = self.manager.slot(self.PATH)
        mkdir = Path.mkdir
        def interrupted(path, *args, **kwargs):
            result = mkdir(path, *args, **kwargs)
            if path == slot / "donor-0":
                raise InterruptedError("after mkdir before binding the empty slot")
            return result
        with stage.train_lock(self.state):
            with mock.patch.object(Path, "mkdir", interrupted):
                with self.assertRaisesRegex(InterruptedError, "after mkdir"):
                    self.manager.retain_failed(self.failed(build), None)
            original_inode = (slot / "donor-0").stat().st_ino
            self.assertEqual(list((slot / "donor-0").iterdir()), [])
            self.manager.retain_failed(self.failed(build), None)
            stage.retire_builds(self.state, None)
            donor = self.select(next_source, self.caches, None)[self.PATH]
            self.assertEqual(donor.stat().st_ino, original_inode)
            self.assertEqual({item.name for item in slot.iterdir()}, {"current.json", "donor-0"})

    def test_unknown_creation_files_and_unusable_current_never_veto_retirement(self):
        old, source, _child, _pin = self.build("old", "A")
        next_source = self.next_source(source, "next")
        with stage.train_lock(self.state):
            self.manager.retain_failed(self.failed(old), None)
            stage.retire_builds(self.state, None)
            donor = self.select(next_source, self.caches, None)[self.PATH]
            slot = donor.parent
            build, _source, _child, _pin = self.build("new", "B")
            mkdir = Path.mkdir
            def interrupted(path, *args, **kwargs):
                result = mkdir(path, *args, **kwargs)
                if path == slot / "donor-1":
                    (path / "unknown").write_text("must survive")
                    raise InterruptedError("after unknown directory appeared")
                return result
            with mock.patch.object(Path, "mkdir", interrupted):
                with self.assertRaises(InterruptedError):
                    self.manager.retain_failed(self.failed(build), None)
            self.manager.retain_failed(self.failed(build), None)
            self.assertEqual(stage.retire_builds(self.state, None), [])
            self.assertEqual((slot / "donor-1/unknown").read_text(), "must survive")
            self.assertEqual(self.select(next_source, self.caches, None)[self.PATH], donor)
            # Optional malformed donor DATA cannot block the next otherwise valid cut.
            git(donor, "config", "core.hooksPath", str(self.external))
            preserved = self.files(donor)
            self.assertEqual(self.select(next_source, self.caches, None), self.caches)
            failed, _source, _child, _pin = self.build("later", "C")
            self.manager.retain_failed(self.failed(failed), None)
            self.assertEqual(stage.retire_builds(self.state, None), [])
            self.assertEqual(self.files(donor), preserved)

    def test_interrupted_old_cleanup_recovers_without_deleted_git_metadata(self):
        old, source, _child, _pin = self.build("old", "A")
        with stage.train_lock(self.state):
            self.manager.retain_failed(self.failed(old), None)
            donor = self.select(source, self.caches, None)[self.PATH]
            stage.retire_builds(self.state, None)
            failed, source, _child, pin = self.build("new", "B")
            next_source = self.next_source(source, "next")
            remove = stage.remove_tree
            def interrupted(path):
                if path == donor:
                    (path / ".git/config").unlink()
                    raise InterruptedError("after deleting previous Git metadata")
                remove(path)
            with mock.patch.object(stage, "remove_tree", interrupted):
                with self.assertRaisesRegex(InterruptedError, "previous Git metadata"):
                    self.manager.retain_failed(self.failed(failed), None)
            self.assertTrue((donor.parent / "retiring.json").is_file())
            self.manager.retain_failed(self.failed(failed), None)
            self.assertEqual(stage.retire_builds(self.state, None), [])
            current = self.select(next_source, self.caches, None)[self.PATH]
            self.assertEqual(git(current, "show", pin + ":README"), "B")
            self.assertFalse(donor.exists())
            self.assertEqual({item.name for item in current.parent.iterdir()}, {"current.json", current.name})

    def test_runner_captures_after_offline_restoration_and_landing_never_overwrites_it(self):
        build, source, child, pin = self.build("source")
        capture = build / "source-object-pins.json"
        capture.unlink()
        (child / "README").write_text("admissible later child")
        git(child, "add", "README")
        self.commit(child, "later child")
        runner = object.__new__(stage.Runner)
        runner.source, runner.state = source, build
        runner.invocation = build / "runs/fixture"
        runner.invocation.mkdir(parents=True)
        runner.record_lock = threading.RLock()
        runner.args = types.SimpleNamespace(source_object_cache=[f"{self.PATH}={self.external}"],
                                            owned_object_cache=[])
        runner.train = types.SimpleNamespace(source_objects=lambda: self.manager, state={})
        runner.git_owner = lambda: self.owner
        runner.git = lambda _name, path, *args: self.manager.git(path, *args)
        runner.synchronization_git_environment = lambda: nullcontext({})
        def synchronize(_name, _argv, **_kwargs):
            if not capture.exists():
                self.assertNotEqual(git(child, "rev-parse", "HEAD"), pin)
                git(child, "checkout", "--quiet", "--detach", pin)
            return ""
        runner.call = synchronize
        with stage.train_lock(self.state):
            runner.synchronize(source, "source")
            self.assertEqual(git(child, "rev-parse", "HEAD"), pin)
            original = capture.read_bytes()
            landing = self.next_source(source, "landing")
            landing_child = landing / self.PATH
            subprocess.run(["git", "clone", "--quiet", "--no-hardlinks", "--template=",
                            str(child), str(landing_child)], check=True)
            git(landing_child, "remote", "set-url", "origin", self.URL)
            runner.synchronize(landing, "landing-trust")
            self.assertEqual(capture.read_bytes(), original)

    def test_installer_confinement_and_independent_transfer_retarget_refusal(self):
        parent, destination = self.root / "from", self.root / "to"
        parent.mkdir()
        destination.mkdir()
        (parent / "object-data").mkdir()
        with self.assertRaisesRegex(RuntimeError, "inside its destination parent"):
            self.owner["_submodule_exclusive_move"](parent, destination)
        move, close = self.owner["_source_object_exclusive_move"](parent, destination)
        try:
            destination.rename(self.root / "held-original")
            destination.mkdir()
            with self.assertRaisesRegex(RuntimeError, "directory changed"):
                move(parent / "object-data", destination / "objects")
            self.assertTrue((parent / "object-data").is_dir())
            self.assertEqual(list(destination.iterdir()), [])
        finally:
            close()


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
        # Owners simulates toolchain commands. Discovery must use fixture data
        # too, rather than depending on whether the host installs rustup.
        self.rustup = self.root / "consumer-tools/rustup"
        executable(self.rustup, "#!/bin/sh\necho 'fixture rustup must use Owners' >&2\nexit 97\n")
        # A run keeps the Agh first on its PATH (keep_agh): the fixture's, not this Mac's.
        self.agh = self.rustup.with_name("agh")
        executable(self.agh, stand_in_agh("0.0.0-fixture"))
        environment = mock.patch.dict(os.environ, {
            "PATH": str(self.rustup.parent) + os.pathsep + os.environ.get("PATH", ""),
        })
        environment.start()
        self.addCleanup(environment.stop)

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
        (repo / ".gitignore").write_text("/bootstrap.toml\n/build/\n/build-tree-manager.noindex/\n")
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
            elif name == "build-tree-manager":
                # Built with the prepared seed's Targo and a copy of the prepared handoff, in the
                # recreator's environment: no rustup selection and not the run's --cargo-home.
                self.assertNotIn("RUSTUP_HOME", env)
                self.assertTrue(Path(env["CARGO_HOME"]).is_relative_to(
                    self.state / "dependencies" / original / "manager-inputs"), env["CARGO_HOME"])
            elif name not in {"locked-dependency-ceiling", "locked-dependency-prewarm"}:
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
        # The supervisor's bound is the ceiling the preparation's owners computed before it
        # started, and the preparation is handed the same number to check: no constant total.
        self.assertEqual(self.owners.assertion_ceiling, [True, False])
        self.assertEqual(self.owners.timeouts[call[0]], 4321)
        self.assertEqual(call[1][call[1].index("--ceiling-seconds") + 1], "4321")
        self.assertLess(names.index("locked-dependency-ceiling"), names.index("locked-dependency-prewarm"))
        report = stage.read_json(Path(record["dependency_preparation"]["report"]))
        self.assertTrue(report["completed_fetches"][-1]["offline"])
        expected = record["dependency_preparation"]["cargo_home"]
        self.assertTrue(Path(expected).is_relative_to(self.state / "dependencies" / record["source_commit"] / "mint-inputs"))
        for name, argv, _env in self.owners.calls:
            if name in {"mint-preflight", "sanctioned-mint-and-double-compile"}:
                self.assertEqual(argv[argv.index("--cargo-home") + 1], expected)
                self.assertEqual(argv[argv.index("--clean-lean-lib") + 1], record["clean_lean_inputs"]["library_path"])

    def test_selected_older_helper_reply_reaches_mint_and_resumes_without_refetch(self):
        # Owners returns the selected older helper's three-pass wire. The actual
        # older-helper dispatch is separately exercised by PrewarmBoundaryTests.
        result, first = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, first.get("error"))
        receipt = Path(first["dependency_preparation"]["report"])
        original = receipt.read_bytes()
        report = stage.read_json(receipt)
        self.assertNotIn("input_acquisition", report)
        self.assertEqual(report["completed_fetches"], [
            {"manifest": "Cargo.toml", "offline": False},
            {"manifest": "Cargo.toml", "offline": True}])
        self.assertIn("sanctioned-mint-and-double-compile", self.names())
        self.owners.calls.clear()
        result, resumed = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, resumed.get("error"))
        self.assertIn("mint", resumed["reused"])
        self.assertNotIn("locked-dependency-prewarm", self.names())
        self.assertNotIn("sanctioned-mint-and-double-compile", self.names())
        self.assertEqual(receipt.read_bytes(), original)

    def claiming_build_slot(self):
        """The snapshot's build-slot takes --rank and --claim-key, and says so when asked."""
        executable(self.repo / "scripts/build-slot",
                   "#!/bin/sh\nif [ \"$1\" = --capabilities ]; then echo build-slot-claim-v1; fi\nexit 0\n")
        git(self.repo, "add", "scripts/build-slot")
        git(self.repo, "commit", "-qm", "a build-slot that takes claim words")
        git(self.repo, "push", "origin", "main")

    @staticmethod
    def admission_words(argv):
        """What a build-slot step asks of its gate: the words before its first `--`."""
        return argv[1:argv.index("--")]

    def test_heavy_step_claims_release_rank(self):
        # LS-104: the train admitted only through the slot pool, invisible to aterm's
        # capacity ledger, whose watch yields to Release claims. Each build-slot step now
        # claims at Release rank under one stable key per step. An unsized ledger claim
        # asks for one pool share, so each compiling step asks for the host (--wide), the
        # width the slot pool's uncapped borrowing gives it; the sized prewarm does not.
        self.claiming_build_slot()
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        heavy = [(name, argv) for name, argv, _ in self.owners.calls if "_owned-command" in argv]
        self.assertIn("sanctioned-mint-and-double-compile", [name for name, _ in heavy])
        for name, argv in heavy:
            with self.subTest(step=name):
                words = self.admission_words(argv)
                claim = ["--rank", "release", "--claim-key", f"trust-train:{name}"]
                if name == "locked-dependency-prewarm":
                    self.assertEqual(words, ["--cpus", "1", "--mem-gb", "0", *claim])
                else:
                    self.assertEqual(words, [*claim, "--wide"])
        self.assertEqual(stage.train_claim_key("index-publish-3"), "trust-train:index-publish")

    def test_fetch_prewarm_claims_one_core_and_no_memory(self):
        # The fetch-only prewarm waited 37.6 minutes for a slot on 2026-11-17, and in
        # the ledger an ALONE claim stops every memory claim. It compiles nothing.
        for claims in (False, True):
            with self.subTest(claims=claims):
                if claims:
                    self.owners.calls.clear()
                    self.claiming_build_slot()
                    self.state = self.root / "state-with-claims"
                result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
                self.assertEqual(result, 0, record.get("error"))
                (argv,) = [argv for name, argv, _ in self.owners.calls if name == "locked-dependency-prewarm"]
                words = self.admission_words(argv)
                self.assertEqual(words[:4], ["--cpus", "1", "--mem-gb", "0"])
                # An older build-slot (a resumed cut's own) gets no words it would refuse.
                self.assertEqual(words[4:], ["--rank", "release", "--claim-key",
                                             "trust-train:locked-dependency-prewarm"] if claims else [])

    def test_train_and_runner_forward_exact_dependency_checkout_caches(self):
        cache = self.root / "source object cache"
        cache.mkdir()
        provider = self.root / "seed libraries"
        provider.mkdir()
        declarations = [f"https://github.com/fixture/{name}#{oid * 40}={cache}"
                        for name, oid in (("second", "2"), ("first", "1"))]
        options = ["--dependency-checkout-cache", declarations[0],
                   "--dependency-checkout-cache", declarations[1]]
        words = stage.train_plist(self.train_arguments(*options))["ProgramArguments"]
        self.assertEqual([words[i + 1] for i, word in enumerate(words) if word == options[0]], declarations)

        result, record = self.run_pipeline("--aterm-repo", str(self.aterm), "--seed-dylib-path", str(provider),
                                           *options)
        self.assertEqual(result, 0, record.get("error"))
        self.assertEqual(record["settings"]["dependency_checkout_cache"], sorted(declarations))
        command = next(argv for name, argv, _env in self.owners.calls if name == "locked-dependency-prewarm")
        worker = command[command.index("_prewarm-dependencies"):]
        with mock.patch.object(stage, "prewarm_dependencies") as prewarm:
            self.assertEqual(stage.main(worker), 0)
        # The worker also carries the ceiling its supervisor was given (RL-55) and the
        # host's per-URL object caches, none here.
        prewarm.assert_called_once_with(Path(worker[1]), Path(worker[2]), worker[3], Path(worker[4]), [provider],
                                        self.cargo_home, Path(worker[6]), object_caches={},
                                        checkout_cache_specs=declarations,
                                        ceiling_seconds=int(worker[worker.index("--ceiling-seconds") + 1]))

    def test_the_runner_builds_its_snapshot_manager_from_the_prepared_dependencies(self):
        # 2026-11-15, in two state roots: the mint's first x.py refused its lease ("native
        # build-tree manager v2 is unavailable"). A Targo on PATH that answers v2 does not
        # count: the mint's x.py never sees it. 2026-11-16: built before the preparation with
        # --cargo-home as its Cargo home, the offline build ended six ticks of the train on
        # "no matching package named `chrono` found". So the manager is built after the
        # preparation and before the mint's preflight, from the prepared handoff and seed.
        path_bin = self.root / "path-bin"
        executable(path_bin / "targo", "#!/bin/sh\necho trust-build-tree-manager-v2\n")
        runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), self.owners)
        runner.env["PATH"] = f"{path_bin}:{runner.env['PATH']}"
        self.assertEqual(runner.run(), 0, runner.record.get("error"))
        names = self.names()
        self.assertEqual(names.count("build-tree-manager"), 1)
        order = [names.index(name) for name in ("locked-dependency-prewarm", "build-tree-manager-inputs",
                                                "build-tree-manager", "mint-preflight")]
        self.assertEqual(order, sorted(order), names)
        work = self.state / "dependencies" / runner.record["source_commit"]
        prepared = runner.record["dependency_preparation"]["cargo_home"]
        _name, copy, _env = next(row for row in self.owners.calls if row[0] == "build-tree-manager-inputs")
        self.assertEqual(copy[1:5], ["-I", "-S", str(self.state / "source/scripts/mint_seed_support.py"),
                                     "cargo-home-inputs"])
        self.assertEqual(copy[copy.index("--source") + 1], prepared)
        home = Path(copy[copy.index("--destination") + 1])
        self.assertTrue(home.is_relative_to(work / "manager-inputs"), home)
        self.assertNotEqual(home, Path(prepared))  # the handoff itself stays the mint's unwritten input
        _name, argv, env = next(row for row in self.owners.calls if row[0] == "build-tree-manager")
        self.assertEqual(argv[1], "--")  # its own build-slot admission
        self.assertEqual(argv[-4:], ["bash", str(self.state / "source/scripts/build-tree-manager.sh"),
                                     "--targo", str(work / "seed/bin/targo")])
        # The offline build reads the prepared copy, never the optional --cargo-home.
        self.assertEqual(env["CARGO_HOME"], str(home))
        self.assertNotEqual(Path(env["CARGO_HOME"]), self.cargo_home)
        self.assertNotIn("RUSTUP_HOME", env)
        step = next(row for row in runner.record["steps"] if row["name"] == "build-tree-manager")
        self.assertEqual(step["status"], "passed")
        self.assertTrue(Path(step["log"]).is_file())
        manager = self.state / "source/build-tree-manager.noindex/debug/bootstrap"
        self.assertEqual(runner.record["build_tree_manager"],
                         {"path": str(manager), "sha256": stage.file_hash(manager), "built": True,
                          "targo": str(work / "seed/bin/targo"), "cargo_home": str(home),
                          "cargo_home_inputs": str(home.with_name("cargo-home-inputs.json"))})
        # A snapshot whose own manager answers v2 is given nothing more.
        self.owners.calls.clear()
        result, record = self.run_pipeline("--aterm-repo", str(self.aterm))
        self.assertEqual(result, 0, record.get("error"))
        self.assertNotIn("build-tree-manager", self.names())
        self.assertNotIn("build-tree-manager-inputs", self.names())
        self.assertEqual(record["build_tree_manager"],
                         {"path": str(manager), "sha256": stage.file_hash(manager), "built": False})

    def offline_manager_owners(self):
        """Owners whose manager build is Cargo's offline resolution: it knows a locked crate only
        by the registry index entry in its own Cargo home, and the preparation's handoff holds it."""
        entry = "registry/index/fixture-index/.cache/ch/ro/chrono"

        def execute(argv, cwd, env, log, timeout=None, **kwargs):
            name = log.stem.split("-", 1)[1] if Path(argv[0]).name != "git" else None
            if name == "build-tree-manager" and not (Path(env.get("CARGO_HOME", "/nonexistent")) / entry).is_file():
                self.owners.calls.append((name, argv, dict(env)))
                log.write_text(json.dumps({"argv": argv, "cwd": str(cwd)}) + "\n"
                               "error: no matching package named `chrono` found\nlocation searched: crates.io index\n"
                               "required by package `bootstrap v0.0.0`\n"
                               "As a reminder, you're using offline mode (via `--frozen`)\n")
                stage.atomic_json(Path(argv[argv.index("_owned-command") + 2]),
                                  {"exit_code": 101, "timed_out": False, "interrupted": False})
                return log.read_text()
            result = self.owners(argv, cwd, env, log, timeout, **kwargs)
            if name == "locked-dependency-prewarm":
                # The handoff the offline replay resolved holds the entry, and its receipt binds it.
                receipt = Path(argv[argv.index("_prewarm-dependencies") + 4])
                report = stage.read_json(receipt)
                handoff = Path(report["cargo_home"])
                (handoff / entry).parent.mkdir(parents=True, exist_ok=True)
                (handoff / entry).write_bytes(b"chrono index entry")
                report["cache_trees"]["registry/index"] = stage.fingerprint(handoff / "registry/index")
                stage.atomic_json(receipt, report)
            elif name == "build-tree-manager-inputs":
                # mint_seed_support.py cargo-home-inputs: a private copy of the input trees.
                source, destination = (Path(argv[argv.index(flag) + 1]) for flag in ("--source", "--destination"))
                self.assertFalse(destination.exists())
                destination.mkdir(mode=0o700)
                for tree in ("registry/index", "registry/cache", "git/db"):
                    if (source / tree).is_dir():
                        shutil.copytree(source / tree, destination / tree)
                stage.atomic_json(Path(argv[argv.index("--output") + 1]), {"schema": "trust-cargo-home-inputs-v1"})
            return result
        return execute

    def test_a_cargo_home_that_lacks_a_locked_index_entry_still_gets_its_manager(self):
        # The class of 2026-11-16: --cargo-home held Bootstrap's archives and too few index
        # entries. This run's --cargo-home holds no entry at all; the manager's own home is the
        # prepared handoff's copy, so the offline build resolves.
        self.assertEqual(list(self.cargo_home.iterdir()), [])
        runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), self.offline_manager_owners())
        self.assertEqual(runner.run(), 0, runner.record.get("error"))
        _name, _argv, env = next(row for row in self.owners.calls if row[0] == "build-tree-manager")
        home = Path(env["CARGO_HOME"])
        self.assertTrue((home / "registry/index/fixture-index/.cache/ch/ro/chrono").is_file())
        self.assertEqual(runner.record["build_tree_manager"]["cargo_home"], str(home))
        self.assertTrue(runner.record["build_tree_manager"]["built"])
        self.assertIn("mint-preflight", self.names())
        # The stand-in does fail as Cargo does when the step is handed --cargo-home instead.
        self.state, self.owners = self.root / "state-ambient-home", Owners()
        ambient = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), self.offline_manager_owners())
        original = ambient.build_tree_manager
        ambient.build_tree_manager = lambda work=None, prepared=None: original()
        self.assertEqual(ambient.run(), 1)
        self.assertIn("the build-tree-manager step built no manager", ambient.record["error"])
        _name, _argv, env = next(row for row in self.owners.calls if row[0] == "build-tree-manager")
        self.assertEqual(Path(env["CARGO_HOME"]), self.cargo_home)
        self.assertIn("no matching package named `chrono`", Path(ambient.record["steps"][-1]["log"]).read_text())

    def test_a_prepare_run_builds_its_manager_before_its_compiler_build(self):
        result, record = self.run_pipeline("--mode", "prepare")
        self.assertEqual(result, 0, record.get("error"))
        names = self.names()
        self.assertLess(names.index("build-tree-manager"), names.index("pinned-bootstrap"))
        self.assertNotIn("build-tree-manager-inputs", names)
        _name, argv, env = next(row for row in self.owners.calls if row[0] == "build-tree-manager")
        # No preparation exists in this mode: the run's own environment and --cargo-home.
        self.assertEqual(argv[-2:], ["bash", str(self.state / "source/scripts/build-tree-manager.sh")])
        self.assertEqual(Path(env["CARGO_HOME"]), self.cargo_home)
        self.assertEqual(set(record["build_tree_manager"]), {"path", "sha256", "built"})

    def test_a_snapshot_manager_that_does_not_answer_v2_refuses_before_the_mint_preflight(self):
        for outcome in ("answers v1", "script refuses"):
            with self.subTest(outcome=outcome):
                self.state = self.root / ("state-manager-" + outcome.replace(" ", "-"))
                self.owners = Owners()
                self.owners.manager_answer = "trust-build-tree-manager-v1"

                def execute(argv, cwd, env, log, timeout=None, **kwargs):
                    result = self.owners(argv, cwd, env, log, timeout, **kwargs)
                    if outcome == "script refuses" and log.stem.endswith("-build-tree-manager"):
                        # scripts/build-tree-manager.sh exits 1 when its binary does not answer v2.
                        stage.atomic_json(Path(argv[argv.index("_owned-command") + 2]),
                                          {"exit_code": 1, "timed_out": False, "interrupted": False})
                    return result

                runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), execute)
                self.assertEqual(runner.run(), 1)
                record = runner.record
                self.assertEqual(record["status"], "failed")
                self.assertIn("the build-tree-manager step", record["error"])
                self.assertIn("trust-build-tree-manager-v2", record["error"])
                self.assertEqual(record["steps"][-1]["name"], "build-tree-manager")
                self.assertNotIn("build_tree_manager", record)
                for later in ("mint-preflight", "sanctioned-mint-and-double-compile"):
                    self.assertNotIn(later, self.names())

    def test_a_manager_build_that_changes_the_pinned_seed_refuses_before_the_mint_preflight(self):
        def execute(argv, cwd, env, log, timeout=None, **kwargs):
            result = self.owners(argv, cwd, env, log, timeout, **kwargs)
            if log.stem.endswith("-build-tree-manager"):
                Path(argv[argv.index("--targo") + 1]).with_name("left-by-the-build").write_text("x")
            return result

        runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), execute)
        self.assertEqual(runner.run(), 1)
        self.assertIn("changed the pinned seed it built with", runner.record["error"])
        self.assertNotIn("build_tree_manager", runner.record)
        self.assertNotIn("mint-preflight", self.names())

    def failed_mint_fixture(self):
        """A seed pin the mint reads, and a stand-in mint that writes its stage receipt, DDC
        manifests, WORK and dist and then fails; `shape` says how far it got and how it ended."""
        spec = importlib.util.spec_from_file_location("daily_mint_recovery", SCRIPT.with_name("mint_seed_recovery.py"))
        recovery = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(recovery)
        support = recovery.load_support()
        # What the mint reads beside its build: the version and the src/stage0 pin of its seed.
        pins = ["compiler_git_commit_hash=" + "b" * 40, "compiler_date=2026-10-01",
                "compiler_version=0.1.0-trust", "dist_server=file://{trust-root}/bootstrap/trust-stage0",
                "artifacts_server=file://{trust-root}/bootstrap/trust-stage0/artifacts",
                "artifacts_with_llvm_assertions_server=file://{trust-root}/bootstrap/trust-stage0/artifacts-with-llvm-assertions",
                "compiler_channel_manifest_hash=" + "d" * 64, "compiler_dist_channel=trust",
                "git_merge_commit_email=trust@fixture.invalid", "min_stage0_rustc_version=1.100.0",
                "nightly_branch=main", "rustfmt_channel_manifest_hash=" + "d" * 64,
                "rustfmt_date=2026-10-01", "rustfmt_dist_channel=trust",
                "rustfmt_git_commit_hash=" + "b" * 40, "rustfmt_version=0.1.0-trust"]
        payloads = []
        for component in support.SEED_COMPONENTS:
            relative = f"bootstrap/trust-stage0/dist/2026-10-01/{component}.tar.xz"
            archive = self.repo / relative
            archive.parent.mkdir(parents=True, exist_ok=True)
            archive.write_text("pinned " + component)
            digest = stage.file_hash(archive)
            pins.append(f"dist/2026-10-01/{component}.tar.xz={digest}")
            payloads.append({"path": relative, "actual_sha256": digest, "pinned_sha256": digest, "matches_pin": True})
        (self.repo / "src").mkdir()
        (self.repo / "src/version").write_text("0.10.0\n")
        (self.repo / "src/stage0").write_text("\n".join(pins) + "\n")
        (self.repo / "bootstrap/trust-stage0/channel.toml").write_text("pinned channel")
        git(self.repo, "add", ".")
        git(self.repo, "commit", "-qm", "seed pin")
        git(self.repo, "push", "-q", "origin", "main")
        oracle_root = self.root / "oracle"
        executable(oracle_root / "bin/rustc", "#!/bin/sh\nexit 1\n")
        executable(oracle_root / "lib/driver", "#!/bin/sh\nexit 1\n")
        helper = self.root / "native/helper"
        executable(helper, "#!/bin/sh\nexit 1\n")
        configuration = {"fingerprint": "fixture-config-closure", "files": ["bootstrap.toml"]}
        lineage = {"status": "immutable_release", "errors": [], "closure_sha256": "e" * 64,
                   "repositories": [{"path": ".", "working_tree_snapshot_sha256": "e" * 64}]}
        kept = {}
        # By default: an accepted receipt (status None: none written), build-slot's 36 jobs, a
        # default DDC seed recorded in ddc-seed.json, and a terminal exit 1.
        shape = {"status": "internal-release-ready", "jobs": 36, "sysroot": True, "exit_code": 1, "timed_out": False}

        def failed_mint(argv, cwd, env, log, timeout=None, **kwargs):
            """A mint that reached its stage receipt and then failed, keeping its WORK."""
            if not log.stem.endswith("-sanctioned-mint-and-double-compile"):
                return self.owners(argv, cwd, env, log, timeout, **kwargs)
            owned = argv.index("_owned-command")
            command = kept["argv"] = argv[owned + 5:]
            source = support.repository_state(cwd)
            commit, host = source["commit"], command[command.index("--host") + 1]
            library = command[command.index("--clean-lean-lib") + 1]
            lean = kept["lean"] = {"library_path": library, "fingerprint": "fixture-lean",
                                   "physical_installation": str(Path(library).parents[1]),
                                   "environment": {"CLEAN_OLEAN_PINNED_LEAN_LIB": library,
                                                   "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"}}
            build = cwd / f"build/pack-mint-0.10.0-{host}-{commit[:12]}"
            stage2, work = build / host / "stage2", cwd / "build/.mint-and-prove.fixture"
            producer = build / host / "stage3-tools-bin" / host / "targo"
            for path in (stage2 / "bin/trustc", stage2 / "bin/targo", producer):
                executable(path, "#!/bin/sh\nexit 0\n")
            compared = support.stage2_manifest(stage2)
            oracle = {"commit": "c" * 40, "host": host, "relation": "lineage-disjoint", "sysroot": str(oracle_root),
                      "compiler": "bin/rustc", "compiler_sha256": stage.file_hash(oracle_root / "bin/rustc"),
                      "driver": "lib/driver", "driver_sha256": stage.file_hash(oracle_root / "lib/driver")}
            if not shape["sysroot"]:
                del oracle["sysroot"]
            for name, value in (("stage2-pinned-seed.json", compared), ("stage2-ddc-seed.json", compared),
                                ("ddc-seed.json", oracle), ("ddc-seed-post-build.json", oracle),
                                ("safe-path.json", {"schema": "trust-sanitized-path-v2", "profile": support.SANITIZED_PATH_PROFILE,
                                                    "host": host, "python": str(helper), "admitted": {
                                                        name: support.sanitized_tool_identity(helper)
                                                        for name in support.build_helper_names(host)}})):
                stage.atomic_json(work / name, value)
            (work / "cargo-home").mkdir()
            declared = {"CARGO_HOME": str(work / "cargo-home"), "CARGO_NET_OFFLINE": "true", "GIT_CONFIG_NOSYSTEM": "1",
                        "GIT_CONFIG_GLOBAL": os.devnull, "RUSTUP_HOME": str(work / "environment-mint/rustup-home"),
                        "SOURCE_DATE_EPOCH": str(source["source_date_epoch"]), **lean["environment"]}
            accepted = shape["status"] == "internal-release-ready"
            stage.atomic_json(stage2 / "tool-provenance.json", {
                "schema": "trust.stage-tool-provenance.v2", "status": shape["status"],
                "errors": [] if accepted else ["unmapped public stage tool rust-lld"],
                "writer": "scripts/mint_and_prove_seed.sh", "stage": 2, "host": host, "compiler": {"source_commit": commit},
                "source_lineage": {**lineage, "pre_build_closure_sha256": lineage["closure_sha256"],
                                   "post_build_closure_sha256": lineage["closure_sha256"], "stable_across_build": True},
                "tools": [{"name": "targo", "path": str((stage2 / "bin/targo").relative_to(cwd)),
                           "sha256": stage.file_hash(stage2 / "bin/targo"),
                           "producer_path": str(producer.relative_to(cwd)), "producer_sha256": stage.file_hash(producer)}],
                # build-slot's share, as the mint's --jobs to every x.py; the runner named none.
                "bootstrap_lineage": {"config_path": "bootstrap.toml", "mint_configuration": {
                    "host": host, "xpy_config_overrides": {} if shape["jobs"] is None else {"build.jobs": shape["jobs"]},
                    "configuration_closure": configuration, "clean_lean_inputs": lean},
                    "validated_seed": {"authority": {
                        "pins": {key: value for key, value in support.read_stage0_pin(cwd).items() if not key.startswith("dist/")},
                        "payloads": payloads,
                        "src_stage0": {"path": "src/stage0", "sha256": stage.file_hash(cwd / "src/stage0")},
                        "channel_manifest": {"path": "bootstrap/trust-stage0/channel.toml",
                                             "sha256": stage.file_hash(cwd / "bootstrap/trust-stage0/channel.toml")}}}},
                "build_authority": {"cargo_environment": {"cargo_home": str(work / "cargo-home")},
                    "declared_rustup_home": {"selected_local_path": declared["RUSTUP_HOME"], "entries": [], "errors": []},
                    "clean_lean_inputs": lean,
                    "declared_environment_sha256": {key: hashlib.sha256(value.encode()).hexdigest()
                                                    for key, value in declared.items()}}})
            if shape["status"] is None:
                (stage2 / "tool-provenance.json").unlink()
            channel = []
            for index, component in enumerate(support.SEED_COMPONENTS):
                prefix = f"{component}-0.10.0-trust{'' if component == 'trust-src' else '-' + host}.tar."
                gz, xz = build / "dist" / (prefix + "gz"), build / "dist" / (prefix + "xz")
                gz.parent.mkdir(parents=True, exist_ok=True)
                gz.write_text("gz " + component)
                xz.write_text("xz " + component)
                channel.append(f'[pkg.p{index}.target."{host}"]\nurl="https://trust.invalid/{gz.name}"\n'
                               f'hash="{stage.file_hash(gz)}"\nxz_url="https://trust.invalid/{xz.name}"\n'
                               f'xz_hash="{stage.file_hash(xz)}"\n')
            (build / "dist/channel-rust-trust.toml").write_text("\n".join(channel))
            (build / "dist/channel-rust-trust-date.txt").write_text(source["commit_date"])
            (build / "dist/channel-rust-trust-git-commit-hash.txt").write_text(commit)
            log.write_text(json.dumps({"argv": argv, "cwd": str(cwd)}) + "\n"
                           "error: seed targo reports duplicate identity field freshness\n")
            stage.atomic_json(Path(argv[owned + 2]), {"exit_code": shape["exit_code"], "timed_out": shape["timed_out"],
                                                      "interrupted": False})
            return log.read_text()

        return types.SimpleNamespace(execute=failed_mint, kept=kept, shape=shape, recovery=recovery, support=support,
                                     oracle_root=oracle_root, configuration=configuration, lineage=lineage)

    def run_failed_mint(self, mint, label):
        """One runner run, in its own state root, over the stand-in mint as `mint.shape` says."""
        self.state, self.owners = self.root / f"state-{label}", Owners()
        runner = stage.Runner(self.arguments("--aterm-repo", str(self.aterm)), mint.execute)
        with contextlib.redirect_stderr(io.StringIO()) as printed:
            self.assertEqual(runner.run(), 1)
        self.assertEqual(runner.record["status"], "failed")
        self.assertEqual(runner.record["error"], "owned command did not complete successfully")
        return runner, printed.getvalue()

    def assert_nothing_kept(self, runner):
        """The mint's WORK where it left it, and no continuation evidence, whole or partial."""
        work = self.state / "source/build/.mint-and-prove.fixture"
        self.assertTrue((work / "cargo-home").is_dir())
        self.assertFalse(work.with_name("retained" + work.name).exists())
        self.assertEqual(sorted(path.name for path in runner.invocation.iterdir() if "continuation" in path.name), [])
        self.assertNotIn("evidence", runner.record.get("mint_continuation", {}))

    def test_the_mint_continuation_keeps_the_train_claim(self):
        # The printed continuation is run in place of the mint step, so it claims as that step did.
        self.claiming_build_slot()
        mint = self.failed_mint_fixture()
        runner, _printed = self.run_failed_mint(mint, "claiming")
        command = runner.record["mint_continuation"]["command"]
        self.assertEqual(command[1:command.index("--")],
                         ["--rank", "release", "--claim-key", "trust-train:sanctioned-mint-and-double-compile",
                          "--wide"])

    def test_a_runner_mint_that_fails_after_provenance_is_inspected_from_what_the_runner_kept(self):
        # The da63c88b7b cut stopped after 5h58m with an identical DDC and an accepted stage
        # receipt, and was built again: the continuation read --jobs and --ddc-seed from an argv
        # the runner never gave them, and nothing wrote the evidence it reads.
        mint = self.failed_mint_fixture()
        runner, printed = self.run_failed_mint(mint, "continuable")
        record, kept = runner.record, mint.kept
        self.assertNotIn("--jobs", kept["argv"])
        self.assertNotIn("--ddc-seed", kept["argv"])
        source = self.state / "source"
        build = source / f"build/pack-mint-0.10.0-{HOST}-{record['source_commit'][:12]}"
        continuation = record["mint_continuation"]
        evidence = Path(continuation["evidence"])
        self.assertEqual(evidence.parent, runner.invocation)
        # The continuation makes WORK afresh, so the mint's WORK leaves that name, and stays in
        # the snapshot's build beside it.
        retained = source / "build/retained.mint-and-prove.fixture"
        self.assertFalse((source / "build/.mint-and-prove.fixture").exists())
        self.assertEqual(continuation["retained_work"], str(retained))
        self.assertTrue((retained / "cargo-home").is_dir())
        attributes = dict(vars(mint.support))
        attributes.update(configuration_closure=lambda *_a: mint.configuration, clean_lean_inputs=lambda *_a: kept["lean"])
        inspected = mint.recovery.validate(source, build, evidence, support=types.SimpleNamespace(**attributes),
                                           owner=types.SimpleNamespace(capture_source_lineage=lambda *_a: mint.lineage),
                                           engine={"commit": "f" * 40})
        self.assertEqual(inspected["state"], "inspected")
        self.assertEqual((inspected["original_jobs"], inspected["ddc_seed"]), (36, str(mint.oracle_root)))
        # The printed continuation passes on what the argv did not name, and keeps all it did.
        command = continuation["command"]
        self.assertIn(shlex.join(command), printed)
        self.assertEqual(command, [str(source / "scripts/build-slot"), "--", *kept["argv"][:2],
                                   "--resume-after-provenance", str(evidence), "--source-root", str(source),
                                   "--jobs", "36", *kept["argv"][2:], "--ddc-seed", str(mint.oracle_root)])
        # In a train this state root is a build directory. Retiring it carries its runs/ into
        # history/, which keeps eight; the WORK, a full Cargo home on a real cut, goes with the
        # snapshot instead.
        train = self.root / "train"
        (train / "builds").mkdir(parents=True)
        cut = self.state.rename(train / "builds/cut")
        (cut / "train-build.json").write_text("{}\n")
        self.assertEqual(stage.retire_builds(train, None), [])
        self.assertFalse(cut.exists())
        history = train / "history/cut"
        self.assertTrue((history / "runs" / runner.invocation.name / "mint-continuation/mint-result.json").is_file())
        self.assertEqual([path for path in history.rglob("*") if "mint-and-prove" in path.name or path.name == "cargo-home"], [])

    def test_a_failed_mint_with_no_continuation_value_keeps_nothing_and_leaves_its_work(self):
        # Every value is read and checked before anything is written or moved.
        mint = self.failed_mint_fixture()
        for label, change, missing in (("no-jobs", {"jobs": None}, "build.jobs"),
                                       ("no-seed", {"sysroot": False}, "sysroot")):
            with self.subTest(label=label):
                mint.shape.update(change)
                runner, _printed = self.run_failed_mint(mint, label)
                self.assert_nothing_kept(runner)
                self.assertIn(missing, runner.record["mint_continuation"]["error"])
                mint.shape.update(jobs=36, sysroot=True)

    def test_only_a_terminal_exit_1_after_an_accepted_receipt_keeps_continuation_evidence(self):
        mint = self.failed_mint_fixture()
        for label, change in (("signal", {"exit_code": 143}), ("timeout", {"timed_out": True}),
                              ("rejected", {"status": "rejected"}), ("no-receipt", {"status": None})):
            with self.subTest(label=label):
                mint.shape.update(change)
                runner, _printed = self.run_failed_mint(mint, label)
                self.assert_nothing_kept(runner)
                if "status" in change:
                    # Failed before its stage provenance: the cut is built again, with nothing to say.
                    self.assertNotIn("mint_continuation", runner.record)
                else:
                    self.assertIn("only a terminal exit 1 is continued", runner.record["mint_continuation"]["error"])
                mint.shape.update(status="internal-release-ready", exit_code=1, timed_out=False)

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

    def test_snapshot_is_gits_checkout_and_reads_no_controller_working_file(self):
        # The snapshot is Git's checkout of the acquired objects, as in build 27009's cut:
        # no working file of the controller (or a consumer checkout) is a DATA donor.
        runner = self.snapshot_runner()
        owner = dict(runner.git_owner())
        def donor(*_args):
            self.fail("a snapshot must not read its controller's working files")
        owner["_prepare_source_working_cache"] = donor
        runner._managed_git_owner = owner
        controller = git(self.repo, "rev-parse", "HEAD")
        config = (self.repo / ".git/config").read_bytes()
        head = runner.snapshot(self.repo, runner.source, "trust")
        self.assertEqual(head, controller)
        self.assertEqual(list(runner.invocation.glob("*-working-data.json")), [])
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), controller)
        self.assertEqual((self.repo / ".git/config").read_bytes(), config)
        self.assertEqual(git(runner.source, "status", "--porcelain"), "")
        self.assertEqual(git(runner.source, "ls-files", "--stage"), git(self.repo, "ls-files", "--stage"))
        self.assertFalse(os.path.lexists(runner.source / ".git/trust-source-working-cache.json"))
        select = [step for step in runner.record["steps"] if step["name"] == "select-main"]
        self.assertEqual([step["status"] for step in select], ["passed"])
        self.assertEqual(select[0]["argv"][-3:], ["checkout", "--detach", controller])
        self.assertNotIn(b"hooksPath", (runner.source / ".git/config").read_bytes())
        complete = [step for step in runner.record["steps"] if step["name"] == "snapshot-complete"]
        self.assertEqual([step["status"] for step in complete], ["passed"])
        self.assertIn("--ignored", complete[0]["argv"])

    def test_fresh_snapshot_refuses_an_ignored_file_left_after_checkout(self):
        # Git's checkout leaves a fresh tree with nothing untracked or ignored; a file that
        # appears beside it (here one the repository's own exclude hides) is refused before
        # the snapshot is owned, as the per-file route's final audit refused it.
        runner = self.snapshot_runner()
        call = runner.call
        def plant(name, argv, *args, **kwargs):
            result = call(name, argv, *args, **kwargs)
            if name == "select-main":
                (runner.source / ".git/info").mkdir(exist_ok=True)
                with (runner.source / ".git/info/exclude").open("a") as exclude:
                    exclude.write("planted.log\n")
                (runner.source / "planted.log").write_text("not Git's\n")
            return result
        runner.call = plant
        with self.assertRaisesRegex(stage.Refused, "fresh snapshot holds untracked or ignored files"):
            runner.snapshot(self.repo, runner.source, "trust")
        self.assertFalse(os.path.lexists(runner.source.with_name(runner.source.name + ".owner.json")))
        self.assertEqual(git(runner.source, "status", "--porcelain"), "")
        self.assertIn("planted.log", git(runner.source, "status", "--porcelain", "--ignored"))

    def test_reused_snapshot_keeps_its_ignored_build_outputs(self):
        # Only a fresh tree must be exactly Git's checkout: an owned snapshot that a build
        # has used holds ignored outputs, and moving it forward must not refuse them.
        runner = self.snapshot_runner()
        head = runner.snapshot(self.repo, runner.source, "trust")
        (runner.source / ".git/info").mkdir(exist_ok=True)
        (runner.source / ".git/info/exclude").write_text("build/\n")
        (runner.source / "build").mkdir()
        (runner.source / "build/output.o").write_text("an ignored build output\n")
        self.assertEqual(runner.snapshot(self.repo, runner.source, "trust"), head)
        self.assertTrue((runner.source / "build/output.o").is_file())
        complete = [step for step in runner.record["steps"] if step["name"] == "snapshot-complete"]
        self.assertEqual(len(complete), 1)

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
                private = Path(env["TMPDIR"]).resolve()
                self.assertEqual(kwargs["progress"].paths, (Path(argv[4]), private))
                self.assertTrue(private.is_dir())
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
        # The fetch of main has no total: it ends only for lack of progress in the snapshot or its log.
        fetch = next(step for step in runner.record["steps"] if step["name"] == "fetch-main")
        self.assertNotIn("timeout_seconds", fetch)
        self.assertEqual(fetch["progress_bound"], {"stall_window_seconds": api["SUBMODULE_STALL_WINDOW_SECONDS"],
                                                   "floor_bytes_per_second": api["SUBMODULE_FLOOR_BYTES_PER_SECOND"]})
        self.assertNotIn("SUBMODULE_UPDATE_TIMEOUT_SECONDS", api)
        selected["_submodule_auth_config"].assert_not_called()
        _, env = observed[0]
        self.assertFalse(Path(env["TMPDIR"]).exists())
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(env["GIT_TERMINAL_PROMPT"], "0")
        self.assertNotIn("GH_TOKEN", env)
        self.assertNotIn("GITHUB_TOKEN", env)
        # Agh's transfer directory was made in this run's folder, which the train retires.
        self.assertEqual(Path(env["TMPDIR"]).parent, runner.invocation.resolve())
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
        acquired, scratches = [], []
        def execute(argv, cwd, env, log, **kwargs):
            if argv[0] == str(client):
                acquired.append(list(argv))
                self.assertEqual(argv[1:7], ["repo", "fetch", "fixture/pin", str(child), "--ref", target])
                self.assertEqual(kwargs["progress"].paths[:2], (child, Path(env["TMPDIR"])))
                self.assertEqual(Path(env["TMPDIR"]).parent, runner.invocation.resolve())
                scratches.append(Path(env["TMPDIR"]))
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
            self.assertFalse(scratches[0].exists())
            # Bounded by the bytes arriving in the child and Agh's scratch, with no total.
            pin = next(step for step in runner.record["steps"] if step["name"] == "acquire-submodule-pin")
            self.assertNotIn("timeout_seconds", pin)
            self.assertEqual(pin["progress_bound"], {"stall_window_seconds": owner["SUBMODULE_STALL_WINDOW_SECONDS"],
                                                     "floor_bytes_per_second": owner["SUBMODULE_FLOOR_BYTES_PER_SECOND"]})
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

    def owned_cache_fixture(self):
        """The source indexes first-party/fixture at a commit an owned bare cache does not hold yet.

        The cache holds the server's history to the commit before, on its main and on the ref an
        earlier refresh left. Returns the server, the cache, that earlier commit and the pin.
        """
        server = self.root / "cache-server"
        server.mkdir()
        git(server, "init", "--quiet", "--template=", "--initial-branch=main")
        git(server, "config", "user.name", "fixture")
        git(server, "config", "user.email", "fixture@example.invalid")
        (server / "value").write_text("earlier")
        git(server, "add", "value")
        git(server, "commit", "-qm", "earlier")
        earlier = git(server, "rev-parse", "HEAD")
        cache = self.root / "owned-cache.git"
        subprocess.run(["git", "clone", "--quiet", "--bare", "--no-hardlinks", str(server), str(cache)], check=True)
        git(cache, "update-ref", "refs/agh/owned-object-cache/" + earlier, earlier)
        (server / "value").write_text("pinned")
        git(server, "commit", "-qam", "pinned")
        pin = git(server, "rev-parse", "HEAD")
        (self.repo / ".gitmodules").write_text(
            '[submodule "fixture"]\n\tpath = first-party/fixture\n\turl = https://github.com/fixture/pin.git\n')
        git(self.repo, "add", ".gitmodules")
        git(self.repo, "update-index", "--add", "--cacheinfo", "160000", pin, "first-party/fixture")
        git(self.repo, "commit", "-qm", "index a first-party child")
        git(self.repo, "push", "origin", "main")
        return server, cache, earlier, pin

    def owned_cache_runner(self, cache, transfer):
        """A runner whose Agh `transfer`s (argv, env, progress) and whose acquisitions are recorded."""
        runner = stage.Runner(self.arguments("--owned-object-cache", f"first-party/fixture={cache}"))
        runner.invocation = self.state / "runs/owned-cache"
        runner.invocation.mkdir(parents=True)
        runner.record = {"steps": []}
        runner.snapshot(self.repo, runner.source, "trust")
        owner = runner.git_owner()
        client = self.root / "fixture-cache-agh"
        executable(client)
        order = []

        def execute(argv, cwd, env, log, **kwargs):
            if argv[0] == str(client):
                order.append(("agh", list(argv), Path(env["TMPDIR"])))
                self.assertEqual(kwargs["progress"].paths[:2], (Path(argv[4]), Path(env["TMPDIR"])))
                self.assertEqual(Path(env["TMPDIR"]).parent, runner.invocation.resolve())
                argv = transfer(argv, owner)
            return stage.command(argv, cwd, env, log, **kwargs)
        runner.execute = execute
        owner["ensure_submodules"] = lambda path, **options: order.append(("acquire", path, options))
        owner["_inspect_submodule_tree"] = lambda path: []
        fetch = owner["_agh_source_fetch"]
        return runner, order, mock.patch.dict(fetch.__globals__, {"which": lambda name: str(client) if name == "agh" else None})

    def test_an_owned_object_cache_is_brought_to_the_pin_before_the_snapshot_acquires_from_it(self):
        # On 2026-11-17 the train's hand-made cache of clean was three days behind its pin: each cut
        # copied its 1.94 GB start and fetched 2.6 GB again. A cache the train owns follows the pins.
        server, cache, earlier, pin = self.owned_cache_fixture()

        def transfer(argv, owner):
            # Only the transfer is substituted, by local Git from the fixture's server.
            return [*owner["_controlled_git_command"]([]), "-c", "protocol.file.allow=always", "-C", argv[4],
                    "fetch", "--quiet", "--no-tags", str(server), argv[6] + ":" + argv[8]]
        runner, order, agh = self.owned_cache_runner(cache, transfer)
        with agh:
            runner.acquire_submodule_pins(runner.source, "source", 0)
            # The landing worktree at the same pin reads the cache as the snapshot left it.
            runner.acquire_submodule_pins(runner.source, "landing-fixture", 0)
        [refresh] = [entry for entry in order if entry[0] == "agh"]
        # Agh's unfiltered fetch negotiated against the cache, into a private ref: no closure.
        self.assertEqual(refresh[1][1:], ["repo", "fetch", "fixture/pin", str(cache), "--ref", pin,
                                          "--into", "refs/agh/owned-object-cache/" + pin])
        self.assertFalse(refresh[2].exists())
        self.assertEqual([entry[0] for entry in order], ["agh", "acquire", "acquire"])
        for _, path, options in order[1:]:
            self.assertEqual((path, options), (runner.source, {"checkout_caches": {"first-party/fixture": cache}}))
        # HEAD names the pin, so Agh starts the next closure there; the earlier refresh's ref is gone
        # and nothing else of the cache moved.
        self.assertEqual(git(cache, "rev-parse", "HEAD"), pin)
        self.assertNotEqual(subprocess.run(["git", "-C", str(cache), "symbolic-ref", "-q", "HEAD"]).returncode, 0)
        self.assertEqual(git(cache, "for-each-ref", "--format=%(refname)", "refs/agh/"),
                         "refs/agh/owned-object-cache/" + pin)
        self.assertEqual(git(cache, "rev-parse", "refs/heads/main"), earlier)
        self.assertFalse((cache / "objects/info/alternates").exists())
        record = runner.record["owned_object_caches"]["first-party/fixture"]
        self.assertEqual({key: record[key] for key in ("repository", "pin", "status", "head")},
                         {"repository": str(cache), "pin": pin, "status": "refreshed", "head": pin})
        self.assertIsInstance(record["pack_kib"], int)
        refreshes = [step for step in runner.record["steps"] if step["name"] == "refresh-object-cache"]
        self.assertEqual(len(refreshes), 1)
        self.assertNotIn("timeout_seconds", refreshes[0])
        self.assertIn("progress_bound", refreshes[0])

    def test_an_owned_object_cache_that_is_not_refreshed_is_read_as_it_is(self):
        server, cache, earlier, pin = self.owned_cache_fixture()
        runner, order, agh = self.owned_cache_runner(
            cache, lambda argv, owner: [sys.executable, "-I", "-c", "raise SystemExit(7)"])
        with agh, mock.patch("sys.stdout", new_callable=io.StringIO) as said, \
                mock.patch("sys.stderr", new_callable=io.StringIO) as diagnostics:
            runner.acquire_submodule_pins(runner.source, "source", 0)
            # Nor is it tried again for the landing worktree at the same pin.
            runner.acquire_submodule_pins(runner.source, "landing-fixture", 0)
        self.assertIn("the owned object cache of first-party/fixture was not refreshed, and is read as it is",
                      said.getvalue())
        self.assertEqual([entry[0] for entry in order], ["agh", "acquire", "acquire"])
        self.assertEqual(order[1][2], {"checkout_caches": {"first-party/fixture": cache}})
        # The failed transfer's directory is kept and named, in this run's folder, which the
        # train retires with its build.
        self.assertTrue(order[0][2].is_dir())
        self.assertEqual(order[0][2].parent, runner.invocation.resolve())
        self.assertIn(str(order[0][2]), diagnostics.getvalue())
        record = runner.record["owned_object_caches"]["first-party/fixture"]
        self.assertEqual(record["status"], "failed")
        self.assertIn("command exited 7", record["error"])
        self.assertNotIn("head", record)
        self.assertEqual(git(cache, "rev-parse", "HEAD"), earlier)
        self.assertEqual(git(cache, "for-each-ref", "--format=%(refname)", "refs/agh/"),
                         "refs/agh/owned-object-cache/" + earlier)

    def test_an_owned_object_cache_is_a_bare_repository_and_one_gitlinks_only_cache(self):
        server, cache, earlier, pin = self.owned_cache_fixture()
        worktree = self.root / "worktree-cache"
        subprocess.run(["git", "clone", "--quiet", "--no-hardlinks", str(server), str(worktree)], check=True)
        runner, order, agh = self.owned_cache_runner(worktree, lambda argv, owner: self.fail("Agh must not run"))
        with agh, mock.patch("sys.stdout", new_callable=io.StringIO):
            runner.acquire_submodule_pins(runner.source, "source", 0)
        record = runner.record["owned_object_caches"]["first-party/fixture"]
        self.assertEqual(record["status"], "failed")
        self.assertIn("is not one", record["error"])
        self.assertEqual([entry[0] for entry in order], ["acquire"])
        self.assertEqual(git(worktree, "symbolic-ref", "HEAD"), "refs/heads/main")
        # A gitlink takes one cache: declared or owned, never both.
        runner.args.source_object_cache = [f"first-party/fixture={cache}"]
        with self.assertRaisesRegex(stage.Refused, "a gitlink takes one object cache, a declared or an owned one: "
                                                   "first-party/fixture"):
            runner.acquire_submodule_pins(runner.source, "source", 1)
        self.assertEqual(len(order), 1)
        # The train's agent carries the declaration to each tick.
        declaration = f"first-party/fixture={cache}"
        words = stage.train_plist(self.train_arguments("--owned-object-cache", declaration))["ProgramArguments"]
        self.assertEqual(words[words.index("--owned-object-cache") + 1], declaration)

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
        self.assertEqual(argv[argv.index("--index-host") + 1], "agh")
        self.assertEqual(stage.train_plist(self.train_arguments("--index-host", "none"))["ProgramArguments"][
            argv.index("--index-host") + 1], "none")
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
        # The agent carries the caller's PATH; each run puts its own python-bin first, then the
        # one name of the Agh it keeps.
        self.assertEqual(runner.env["PATH"].split(os.pathsep, 2),
                         [str(self.state / "python-bin"), runner.record["agh"]["directory"], agent_path])
        self.assertEqual(Path(runner.record["agh"]["directory"]).parent.parent, self.state / "kept-agh/program")
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

    def test_stage_tree_binds_only_its_bootstrap_source_links_to_the_run_snapshot(self):
        tree = self.root / "stage2"
        bootstrap_sysroot(tree, self.repo)
        with self.assertRaisesRegex(stage.Refused, "escapes"):
            stage.fingerprint(tree)
        bound = stage.fingerprint(tree, self.repo)
        self.assertEqual(stage.fingerprint(tree, self.repo), bound)
        # The links are bound by their text: another checkout is another identity or a refusal.
        with self.assertRaisesRegex(stage.Refused, "escapes"):
            stage.fingerprint(tree, self.root)
        (tree / "lib/rustlib/src/rust").unlink()
        (tree / "lib/rustlib/src/rust").symlink_to(self.repo / "README")
        with self.assertRaisesRegex(stage.Refused, "escapes"):
            stage.fingerprint(tree, self.repo)
        (tree / "lib/rustlib/src/rust").unlink()
        (tree / "lib/rustlib/src/rust").symlink_to(self.repo)
        self.assertEqual(stage.fingerprint(tree, self.repo), bound)
        # Only the two named entries: the same target anywhere else still escapes.
        (tree / "lib/source").symlink_to(self.repo)
        with self.assertRaisesRegex(stage.Refused, "escapes"):
            stage.fingerprint(tree, self.repo)

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
            self.assertEqual(accepted["identity"]["rustup"]["path"], str(self.rustup.resolve()))
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

    def test_missing_consumer_rustup_refuses_before_running_checks(self):
        arguments, _ = self.consumer_arguments()
        discover = shutil.which

        def without_rustup(name, *args, **kwargs):
            return None if name == "rustup" else discover(name, *args, **kwargs)

        with mock.patch.object(stage.shutil, "which", side_effect=without_rustup):
            result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertIn("consumer acceptance requires rustup", record["error"])
        self.assertFalse(any(name.endswith("-consumer-check") for name in self.names()))

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

    def test_consumer_proof_banner_cannot_override_invalid_owner_receipts(self):
        arguments, _ = self.consumer_arguments()
        self.owners.consumer_terminal_results["ty-consumer-check"] = {
            "exit_code": 0, "signal": 9, "timed_out": False, "interrupted": False,
        }
        self.owners.consumer_terminal_results["ay-consumer-check"] = (
            '{"exit_code":7,"exit_code":0,"signal":null,"timed_out":false,"interrupted":false}\n')
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 1)
        self.assertFalse(record["consumer_ready"])
        self.assertIn("successful owned shell exit", record["consumers"]["ty"]["error"])
        self.assertIn("duplicate JSON artifact field", record["consumers"]["ay"]["error"])
        ay_step = next(step for step in record["steps"] if step["name"] == "ay-consumer-check")
        self.assertEqual(ay_step["status"], "failed")
        self.assertTrue(record["consumers"]["aterm"]["receipt"])

    def test_cached_consumer_requires_the_unchanged_owned_terminal_receipt(self):
        arguments, _ = self.consumer_arguments()
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        receipt_path = Path(record["consumers"]["ty"]["receipt"])
        accepted = stage.read_json(receipt_path)
        other = stage.read_json(Path(record["consumers"]["aterm"]["receipt"]))
        terminal_path = Path(accepted["step"]["result_file"])
        original = terminal_path.read_bytes()

        for replacement in (None, original + b"\n", original.replace(b'"exit_code": 0', b'"exit_code": 0.0')):
            with self.subTest(replacement=replacement):
                if replacement is None:
                    terminal_path.unlink()
                else:
                    terminal_path.write_bytes(replacement)
                self.owners.calls.clear()
                result, record = self.run_pipeline(*arguments)
                self.assertEqual(result, 1)
                self.assertFalse(record["consumer_ready"])
                self.assertRegex(record["consumers"]["ty"]["error"], "terminal receipt|regular JSON artifact")
                self.assertNotIn("ty-consumer-check", self.names())
                self.assertTrue(record["consumers"]["aterm"]["reused"])
                terminal_path.write_bytes(original)

        unbound = {**accepted, "step": dict(accepted["step"])}
        unbound["step"].pop("owned_result_identity", None)
        transplanted = {**accepted, **{key: other[key] for key in ("log", "log_identity", "step", "outcome")}}
        for wrong, reason in [(unbound, "lacks its completion identity"),
                              (transplanted, "does not belong to its owned command")]:
            stage.atomic_json(receipt_path, wrong)
            result, record = self.run_pipeline(*arguments)
            self.assertEqual(result, 1)
            self.assertIn(reason, record["consumers"]["ty"]["error"])

        stage.atomic_json(receipt_path, accepted)
        result, record = self.run_pipeline(*arguments)
        self.assertEqual(result, 0, record.get("error"))
        self.assertTrue(all(row["reused"] for row in record["consumers"].values()))

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

    def progress_step(self, script, window=1.0):
        """Run a Python child as a step under a progress bound of `window` seconds on its own directory."""
        owner = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")), run_name="fixture_progress_bound")
        destination = self.root / "progress-destination"
        if destination.exists():
            shutil.rmtree(destination)
        destination.mkdir()
        log = self.root / "progress-step.log"
        bound = owner["_SubmoduleProgress"]("Agh's fetch of fixture main", (destination,), window=window)
        started = time.monotonic()
        try:
            stage.command([sys.executable, "-I", "-c", script, str(destination)], self.root, dict(os.environ), log,
                          progress=bound)
            return None, time.monotonic() - started, bound, log
        except stage.CommandFailed as error:
            return error, time.monotonic() - started, bound, log

    def test_a_step_under_a_progress_bound_outlives_its_window_while_bytes_arrive_and_ends_when_they_stop(self):
        writes = ("import sys, time\nfor number in range(16):\n"
                  "    open(sys.argv[1] + f'/pack-{number}', 'wb').write(b'x' * 4096)\n    time.sleep(0.2)\n")
        error, elapsed, bound, _log = self.progress_step(writes)
        # Three windows long, and never under the floor.
        self.assertIsNone(error)
        self.assertGreater(elapsed, 3 * bound.window)
        self.assertGreaterEqual(bound.received, 12 * 4096)

        # What the child prints is in the step's log, and counts as the recreator's relayed output does.
        prints = "import time\nfor number in range(16):\n    print('x' * 200, flush=True)\n    time.sleep(0.2)\n"
        error, elapsed, bound, log = self.progress_step(prints)
        self.assertIsNone(error)
        self.assertGreater(elapsed, 3 * bound.window)
        self.assertIn(log, bound.paths)

        stalls = ("import sys, time\nopen(sys.argv[1] + '/pack-0', 'wb').write(b'x' * 4096)\n"
                  "print('waiting', flush=True)\ntime.sleep(600)\n")
        error, elapsed, bound, log = self.progress_step(stalls)
        self.assertIsNotNone(error)
        self.assertTrue(error.timed_out)
        self.assertRegex(str(error), r"^Agh's fetch of fixture main showed too little progress: \d+ bytes observed "
                                     r"under its watched paths and on its output, "
                                     r"0\.0 bytes/s over its last 1 s against a floor of 16 bytes/s, and none observed "
                                     r"for the last 1 s; bytes it holds elsewhere are not seen"
                                     rf"; see {re.escape(str(log))}$")
        self.assertNotRegex(str(error).partition("; see ")[0], r"received|stood still")
        # One window after its last byte, not the ten minutes it would have slept.
        self.assertLess(elapsed, 30)

    def test_a_progress_bound_is_refused_for_a_build_slot_step(self):
        runner = stage.Runner(self.arguments("--mode", "prepare"), self.owners)
        with self.assertRaisesRegex(stage.Refused, "a build-slot step is bounded by its own owner"):
            runner.call("build", ["true"], heavy=True, progress=object())

    def test_a_run_keeps_the_agh_it_started_with_for_every_selection(self):
        inherited, selected = os.environ["PATH"], []

        def execute(*args, **kwargs):
            # What an acquisition in this process would select now (the recreator's which).
            selected.append(shutil.which("agh"))
            if len(selected) == 1:
                # The Mac's updater replaces the installed Agh while the run is under way.
                replaced = self.agh.with_name("agh-next")
                executable(replaced, stand_in_agh("9.9.9-updated"))
                os.replace(replaced, self.agh)
            return self.owners(*args, **kwargs)
        runner = stage.Runner(self.arguments("--mode", "prepare"), execute)
        self.assertEqual(runner.run(), 0, runner.record.get("error"))
        slot = self.state / "kept-agh/program" / runner.record["agh"]["kept"].split("/")[-3]
        kept = slot / "bin/agh"
        self.assertEqual(runner.record["agh"], {
            "selected": str(self.agh), "program": str(self.agh), "kept": str(kept), "directory": str(kept.parent),
            "executable": str(slot / "agh"),
            "sha256": hashlib.sha256(stand_in_agh("0.0.0-fixture").encode()).hexdigest(),
            "version": "agh 0.0.0-fixture", "reused": False, "left": []})
        self.assertEqual(json.loads((self.state / "latest.json").read_text())["agh"], runner.record["agh"])
        self.assertEqual(os.listdir(kept.parent), ["agh"])
        self.assertEqual(kept.resolve().read_text(), stand_in_agh("0.0.0-fixture"))
        self.assertIn("9.9.9-updated", self.agh.read_text())
        # In this process and in every step's environment, before and after the update.
        self.assertGreater(len(selected), 3)
        self.assertEqual(set(selected), {str(kept)})
        for name, _argv, environment in self.owners.calls:
            self.assertEqual(shutil.which("agh", path=environment["PATH"]), str(kept), name)
        # The run's selection ends with the run.
        self.assertEqual(os.environ["PATH"], inherited)
        self.assertEqual(shutil.which("agh"), str(self.agh))

    def test_a_run_whose_kept_agh_does_not_run_refuses_before_its_snapshot(self):
        executable(self.agh, stand_in_agh("0", answer="kill -9 $$"))
        runner = stage.Runner(self.arguments("--mode", "prepare"), self.owners)
        with self.assertRaisesRegex(stage.Refused, r"the Agh this run kept does not run from "
                                                   r".*kept-agh/program/[0-9a-f]{64}/bin/agh: `agh version` exited -9"):
            runner.run()
        self.assertEqual(self.owners.calls, [])
        self.assertFalse((self.state / "source").exists())

    def test_a_tick_keeps_one_agh_for_its_reader_and_its_cut(self):
        self.gated_trust()
        arguments, _ = self.consumer_arguments()
        tools = {name: f"/fixture/bin/{name}" for name in ("aterm", "targo")}
        train = stage.Train(self.train_arguments(*arguments), self.owners, self.github, tools)
        inherited = os.environ["PATH"]
        with mock.patch("builtins.print"):
            self.assertEqual(train.tick(), 0, self.train_state())
        kept = self.state / "kept-agh/program" / stage.fingerprint(self.agh)["sha256"] / "bin/agh"
        # The train's own Agh call, and the cut's record and steps: one copy, under the train's
        # root and not once more under the build's.
        admitted = [argv for name, argv, _env in self.owners.calls if name == "trust-repo-admitted"]
        self.assertEqual([argv[0] for argv in admitted], [str(kept)])
        self.assertEqual(train.tool("agh"), str(self.agh))
        build = Path(self.train_state()["good"]["build_dir"])
        self.assertEqual(json.loads((build / "latest.json").read_text())["agh"]["kept"], str(kept))
        self.assertFalse((build / "kept-agh").exists())
        for name, _argv, environment in self.owners.calls:
            self.assertEqual(shutil.which("agh", path=environment["PATH"]), str(kept), name)
        self.assertEqual(os.environ["PATH"], inherited)

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
        # Not `-a`: --repo's own worktree leaves a first-party child uninitialized.
        git(self.repo, "add", "README")
        git(self.repo, "commit", "-qm", text)
        git(self.repo, "push", "-q", "origin", "main")
        return git(self.repo, "rev-parse", "HEAD")

    def test_train_cuts_the_observed_commit_when_main_advances_before_snapshot(self):
        self.gated_trust()
        selected = self.github.main()
        build = int(git(self.repo, "rev-list", "--count", selected))
        train = self.train()
        read_main = train.read_main
        later = []

        def read_then_advance(state=None):
            reading = read_main(state)
            if not later:
                later.append(self.foreign_commit("main advanced before the snapshot"))
            return reading

        with mock.patch.object(train, "read_main", side_effect=read_then_advance):
            with mock.patch("builtins.print"):
                self.assertEqual(train.tick(), 0, self.train_state())

        state = self.train_state()
        record = json.loads((Path(state["good"]["build_dir"]) / "latest.json").read_text())
        self.assertNotEqual(selected, later[0])
        self.assertEqual(record["source_commit"], selected)
        self.assertEqual(record["source_main"], later[0])
        self.assertEqual(state["last"]["main"], selected)
        self.assertEqual((state["good"]["commit"], state["good"]["build"]), (selected, build))
        self.assertEqual(git(self.github.remote, "merge-base", later[0], self.github.main()), later[0])

    def test_train_cuts_when_main_moved_publishes_to_the_index_and_then_waits(self):
        self.gated_trust()
        arguments, _ = self.consumer_arguments()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        self.assertEqual(self.tick(*arguments), 0, self.train_state())
        state = self.train_state()
        self.assertEqual((state["last"]["status"], state["last"]["build"], state["good"]["commit"]), ("published", build, cut))
        self.assertEqual(state["published"], {"build": build, "commit": cut, "index": 41, "at": state["good"]["served_at"],
                                              "found_served": False})
        self.assertEqual((state["good"]["index"], state["good"]["controller_index"]), (41, 42))
        self.assertEqual(self.owners.head["pins"]["trust"], build)
        self.assertEqual(self.github.builds(), [build])
        # The re-pin reached main by a push that ran the hook; its branch is gone from origin.
        repin = self.github.main()
        self.assertEqual(git(self.root / "trust.git", "rev-parse", f"{repin}^"), cut)
        self.assertEqual(self.hook_ran.read_text(), "ran\n")
        self.assertEqual(self.github.deleted, [f"seed/repin-{cut[:12]}"])
        self.assertEqual(state["settled"], repin)
        names = self.names()
        order = ["release-signing-ready", "publisher-hosts-check", "index-hosts-check", "trust-repo-admitted",
                 "sanctioned-mint-and-double-compile", "signed-pack-dry-run", "seed-cut-dry-run",
                 "seed-archives-and-repin-branch", "re-pin-push-1", "signed-pack-stage-upload", "index-status", "canary",
                 "publish-staged-1", "publish-staged-served", "controller-pack", "controller-index-1",
                 "controller-index-served"]
        self.assertEqual([name for name in names if name in order], order)
        self.assertFalse([name for name in names if name.startswith("unsigned-")])
        # Never the publisher's overrides, a mirror, a lane, a withdrawal or the public release owner of Trust.
        for name, argv, _env in self.owners.calls:
            self.assertFalse(stage.PUBLISHER_NEVER.intersection(argv), (name, argv))
            self.assertNotIn("alabsystems", " ".join(argv))
            self.assertEqual("--publish" in argv, name == "seed-archives-and-repin-branch", name)
            if name in ("signed-pack-dry-run", "signed-pack-stage-upload"):
                self.assertEqual(argv[argv.index("atpkg-publish") + 1:][:5],
                                 ["--", "--host", "agh-staging", "publish-group", "rustc"])
            elif "atpkg-publish" in argv and not name.endswith("hosts-check"):
                self.assertEqual(argv[argv.index("atpkg-publish") + 1:][:3], ["--", "--host", "agh"], name)
        # Each preflight asks about the host its own steps write through: the stage-upload's, then the index's.
        hosts = {name: argv[argv.index("atpkg-publish") + 2:] for name, argv, _env in self.owners.calls
                 if name.endswith("hosts-check")}
        self.assertEqual(hosts, {"publisher-hosts-check": ["hosts", "check", "--host", "agh-staging"],
                                 "index-hosts-check": ["hosts", "check", "--host", "agh"]})
        record = json.loads((Path(state["good"]["build_dir"]) / "latest.json").read_text())
        self.assertEqual((record["status"], record["published"]["index"], record["published"][CONTROLLER],
                          record["staged"]["tag"]), ("published", "atpkg-index-41", "atpkg-index-42", f"atpkg-trust-{build}"))
        self.assertEqual((record["settings"]["publisher_host"], record["settings"]["index_host"]), ("agh-staging", "agh"))
        # The run's end checks ran after the stage-upload and before anything reached the index.
        steps = [step["name"] for step in record["steps"]]
        upload = steps.index("signed-pack-stage-upload")
        self.assertEqual(steps[upload + 1:steps.index("index-status")], ["source-clean", "final-source"])
        # The landing worktree is left detached and clean, with no branch of the train's.
        landing = self.state / "landing.noindex"
        self.assertEqual(git(landing, "status", "--porcelain"), "")
        self.assertEqual(git(self.repo, "branch", "--list", "trust-train/*"), "")
        self.assertEqual(state["last"]["report"], "nothing found; docs/OPEN_ISSUES.md holds no FLEET-BUILD-REPORT-1")

        # Main holds nothing but the train's own re-pin: the next tick starts nothing.
        calls = len(self.owners.calls)
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train(*arguments).tick(), 0)
        self.assertIn(f"main has not moved since build {build} was published", printed.call_args.args[0])
        self.assertEqual(len(self.owners.calls), calls)
        self.assertEqual(len(list((self.state / "builds").iterdir())), 1)
        status = stage.train_status(self.state, self.train(*arguments).read_main)
        self.assertRegex(status, rf"^train: last published build {build} \(atpkg-index-41\), 1 commits behind main "
                                 rf"\({repin[:12]}, build {build + 1}, read [^)]*\); the last train published build {build} ")

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

    def submodule_trust(self, refuse_landing=False, local_registration=False, hooks_path=None):
        """gated_trust with one first-party submodule whose pin a stand-in Agh on PATH serves.

        --repo registers the submodule by its indexed URL, or with `local_registration` by a local
        path, as a clone made from local stores does (m9, 2026-11-14). With `refuse_landing`, Agh
        refuses every fetch into the landing worktree; `hooks_path` is --repo's core.hooksPath.
        Returns the pin, the indexed URL, the local path and Agh's log of destinations.
        """
        self.gated_trust()
        if hooks_path is not None:
            git(self.repo, "config", "core.hooksPath", hooks_path)
        server = self.root / "pin-server"
        server.mkdir()
        git(server, "init", "--quiet", "--template=", "--initial-branch=main")
        git(server, "config", "user.name", "fixture")
        git(server, "config", "user.email", "fixture@example.invalid")
        (server / "value").write_text("pinned")
        git(server, "add", "value")
        git(server, "commit", "-qm", "pinned")
        pin = git(server, "rev-parse", "HEAD")
        url = "https://github.com/fixture/pin.git"
        (self.repo / ".gitmodules").write_text('[submodule "fixture"]\n\tpath = first-party/fixture\n\turl = ' + url + '\n')
        git(self.repo, "add", ".gitmodules")
        git(self.repo, "update-index", "--add", "--cacheinfo", "160000", pin, "first-party/fixture")
        git(self.repo, "commit", "-qm", "a first-party child")
        git(self.repo, "push", "-q", "origin", "main")
        self.hook_ran.unlink()
        git(self.repo, "config", "submodule.fixture.url", str(server) if local_registration else url)
        owner = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")), run_name="fixture_landing_agh")
        fetch = shlex.join([*owner["_controlled_git_command"]([]), "-c", "protocol.file.allow=always"])
        log = self.root / "agh-destinations"
        refusal = '*landing.noindex*) exit 1 ;;\n' if refuse_landing else ''
        # agh repo fetch OWNER/NAME DESTINATION --ref PIN --into PRIVATE-REF ...
        executable(self.root / "agh-bin/agh",
                   f"#!/bin/sh\necho \"$4\" >> {shlex.quote(str(log))}\ncase \"$4\" in\n{refusal}esac\n"
                   f"exec {fetch} -C \"$4\" fetch --quiet --no-tags --recurse-submodules=no "
                   f"{shlex.quote(str(server))} \"$6:$8\"\n")
        path = mock.patch.dict(os.environ, {"PATH": f"{self.root / 'agh-bin'}{os.pathsep}{os.environ['PATH']}"})
        path.start()
        self.addCleanup(path.stop)
        self.owners.real_submodules = True
        return pin, url, server, log

    def test_landing_worktree_submodules_are_at_their_pins_before_the_push(self):
        pin, url, server, log = self.submodule_trust()
        self.assertEqual(self.tick(), 0, self.train_state())
        landing = self.state / "landing.noindex"
        # A fresh linked worktree had none; the push ran from one with its child at the pin.
        self.assertEqual(git(landing / "first-party/fixture", "rev-parse", "HEAD"), pin)
        status = subprocess.check_output(["git", "-C", str(landing), "submodule", "status", "--recursive"], text=True)
        self.assertRegex(status, rf"^ {pin} first-party/fixture\b")
        self.assertEqual(git(landing, "status", "--porcelain"), "")
        # Two pushes ran the hook: the re-pin, then the report (no consumer is configured).
        self.assertEqual(self.hook_ran.read_text(), "ran\nran\n")
        # Acquired once for the landing, at the cut, before the mint; the landing found it there.
        destinations = log.read_text().splitlines()
        self.assertEqual(len([line for line in destinations if "landing.noindex" in line]), 1)
        record = json.loads((Path(self.train_state()["good"]["build_dir"]) / "latest.json").read_text())
        self.assertEqual(set(record["landing_submodules"]), {"cut", "re-pin", "report"})
        names = [step["name"] for step in record["steps"]]
        self.assertLess(names.index("landing-cut-pins"), names.index("sanctioned-mint-and-double-compile"))
        self.assertLess(names.index("re-pin-commit") if "re-pin-commit" in names else names.index("re-pin-branch"),
                        names.index("landing-re-pin-pins"))
        self.assertLess(names.index("landing-re-pin-pins"), names.index("re-pin-push-1"))

    def test_registrations_off_the_index_are_read_and_never_rewritten(self):
        children = {}
        for name in ("a", "b", "c", "d"):
            child = self.make_repository(f"child-{name}")
            children[name] = (child, git(child, "rev-parse", "HEAD"))
        (self.repo / ".gitmodules").write_text("".join(
            f'[submodule "{name}"]\n\tpath = first-party/{name}\n\turl = https://github.com/fixture/{name}.git\n'
            for name in children))
        git(self.repo, "add", ".gitmodules")
        for name, (_child, pin) in children.items():
            git(self.repo, "update-index", "--add", "--cacheinfo", "160000", pin, f"first-party/{name}")
        git(self.repo, "commit", "-qm", "four first-party children")
        # a by a local path, b by another remote, c by its indexed URL; d is not registered.
        git(self.repo, "config", "submodule.a.url", str(children["a"][0]))
        git(self.repo, "config", "submodule.b.url", "https://github.com/other/b.git")
        git(self.repo, "config", "submodule.c.url", "https://github.com/fixture/c.git")
        config = (self.repo / ".git/config").read_bytes()
        owner = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")), run_name="fixture_off_index")
        self.assertEqual(sorted(owner["submodule_registrations_off_index"](self.repo)), [
            ("a", [str(children["a"][0])], "https://github.com/fixture/a.git"),
            ("b", ["https://github.com/other/b.git"], "https://github.com/fixture/b.git")])
        self.assertEqual((self.repo / ".git/config").read_bytes(), config)

    def test_a_local_path_registration_refuses_the_tick_before_the_mint_and_is_left_as_it_was(self):
        pin, url, server, _log = self.submodule_trust(local_registration=True)
        cut = git(self.repo, "rev-parse", "HEAD")
        config = (self.repo / ".git/config").read_bytes()
        self.assertEqual(self.tick(), 1)
        error = self.train_state()["last"]["error"]
        self.assertIn("registers fixture by another URL than the indexed .gitmodules one", error)
        self.assertEqual((self.repo / ".git/config").read_bytes(), config)
        names = self.names()
        self.assertNotIn("sanctioned-mint-and-double-compile", names)
        self.assertNotIn("seed-archives-and-repin-branch", names)
        self.assertEqual((self.github.main(), self.github.builds()), (cut, []))
        # The refusal names the command that registers the indexed URL; after it, the train lands.
        remedy = error.split("to register the indexed URLs: ", 1)[1]
        self.assertEqual(shlex.split(remedy),
                         ["git", "-C", str(self.repo.resolve()), "config", "--replace-all", "submodule.fixture.url", url])
        subprocess.run(shlex.split(remedy), check=True)
        self.foreign_commit("moved")
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual(git(self.state / "landing.noindex/first-party/fixture", "rev-parse", "HEAD"), pin)

    def test_a_repo_with_the_hook_installers_ssh_keepalive_lands(self):
        # A train's --repo pushes through the hook, so scripts/install-git-hooks.sh has run in
        # it, and that also writes core.sshCommand. The landing worktree shares that config:
        # the first tick to reach it would have ended at its first read, before the mint.
        pin, _url, server, _log = self.submodule_trust()
        owner = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")), run_name="fixture_keepalive")
        git(self.repo, "config", "core.sshCommand", owner["INSTALLED_SSH_KEEPALIVE_COMMAND"])
        # Exercise the same declared donor and separately loaded retention owner as the fleet.
        original = (self.repo / ".git/config").read_bytes()
        self.assertEqual(self.tick("--source-object-cache", f"first-party/fixture={server}"), 0, self.train_state())
        self.assertEqual((self.repo / ".git/config").read_bytes(), original)
        self.assertEqual(self.hook_ran.read_text(), "ran\nran\n")
        landing = self.state / "landing.noindex"
        self.assertEqual(git(landing / "first-party/fixture", "rev-parse", "HEAD"), pin)
        self.assertEqual(self.hook_ran.read_text(), "ran\nran\n")
        self.assertEqual(git(self.repo, "config", "core.sshCommand"), owner["INSTALLED_SSH_KEEPALIVE_COMMAND"])
        # Any other ssh command in --repo still refuses the landing worktree.
        git(self.repo, "config", "core.sshCommand", "/usr/bin/false")
        with owner["admitted_trust_checkout"](landing), self.assertRaisesRegex(RuntimeError, "local:core.sshcommand"):
            owner["submodule_registrations_off_index"](landing)

    def test_a_landing_worktree_under_the_main_worktrees_absolute_hooks_path_lands(self):
        # scripts/install-git-hooks.sh writes the main worktree's absolute scripts/hooks, which
        # scripts/prewarm_push.sh's hooks_verdict accepts for a linked worktree (main-of-linked).
        pin, _url, _server, _log = self.submodule_trust(hooks_path=str(self.repo / "scripts/hooks"))
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual(git(self.state / "landing.noindex/first-party/fixture", "rev-parse", "HEAD"), pin)
        self.assertEqual(self.hook_ran.read_text(), "ran\nran\n")
        # Another repository's hooks are not the maintained path.
        owner = runpy.run_path(str(SCRIPT.with_name("recreate_bootstrap.py")), run_name="fixture_hooks_path")
        other = self.make_repository("other-hooks")
        executable(other / "scripts/hooks/pre-push")
        landing = self.state / "landing.noindex"
        for hooks, admitted in ((self.repo / "scripts/hooks", True), (landing / "scripts/hooks", True),
                                (other / "scripts/hooks", False), (self.root / "nowhere", False)):
            git(self.repo, "config", "core.hooksPath", str(hooks))
            with self.subTest(hooks=str(hooks)), owner["admitted_trust_checkout"](landing):
                if admitted:
                    owner["_reject_local_git_execution_authority"](landing)
                else:
                    with self.assertRaisesRegex(RuntimeError, "local:core.hookspath"):
                        owner["_reject_local_git_execution_authority"](landing)
        # Outside the block the landing worktree is any other repository.
        git(self.repo, "config", "core.hooksPath", str(self.repo / "scripts/hooks"))
        with self.assertRaisesRegex(RuntimeError, "local:core.hookspath"):
            owner["_reject_local_git_execution_authority"](landing)

    def test_landing_acquires_the_pins_main_moved_to_before_the_helper_runs_again(self):
        pin, _url, server, _log = self.submodule_trust()
        (server / "value").write_text("moved")
        git(server, "commit", "-qam", "moved")
        moved = git(server, "rev-parse", "HEAD")

        def move_main_gitlink():
            # Main's first-party gitlink moves while the mint runs.
            git(self.repo, "pull", "-q", "--ff-only", "origin", "main")
            git(self.repo, "update-index", "--cacheinfo", "160000", moved, "first-party/fixture")
            git(self.repo, "commit", "-qm", "a first-party pin moved")
            git(self.repo, "push", "-q", "origin", "main")
        self.owners.after["sanctioned-mint-and-double-compile"] = move_main_gitlink
        # The helper merges that main, keeps the merge and asks for a build (exit 4); then runs again.
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertNotIn("not landed", self.train_state()["last"]["report"])
        landing = self.state / "landing.noindex"
        self.assertEqual(git(landing / "first-party/fixture", "rev-parse", "HEAD"), moved)
        self.assertEqual(git(self.root / "trust.git", "rev-parse", "refs/heads/main:first-party/fixture"), moved)
        record = json.loads((Path(self.train_state()["good"]["build_dir"]) / "latest.json").read_text())
        names = [step["name"] for step in record["steps"]]
        self.assertLess(names.index("re-pin-push-1"), names.index("landing-re-pin-merged-1-pins"))
        self.assertLess(names.index("landing-re-pin-merged-1-pins"), names.index("re-pin-push-2"))
        self.assertRegex(record["landing_submodules"]["re-pin-merged-1"], rf"^{moved} first-party/fixture\b")
        # The report's branch starts at the re-pin, behind main's pin; its merge moves it again.
        self.assertRegex(record["landing_submodules"]["report"], rf"^{pin} first-party/fixture\b")
        self.assertRegex(record["landing_submodules"]["report-merged-1"], rf"^{moved} first-party/fixture\b")
        self.assertNotEqual(pin, moved)

    def test_a_landing_child_left_dirty_names_the_train_owned_worktree_and_its_remedy(self):
        pin, _url, _server, _log = self.submodule_trust()
        self.assertEqual(self.tick(), 0, self.train_state())
        landing = self.state / "landing.noindex"
        # reset --hard does not reach a child: one left dirty stays in the train's tree.
        (landing / "first-party/fixture/value").write_text("left behind")
        self.foreign_commit("moved")
        before = len(self.owners.calls)
        self.assertEqual(self.tick(), 1)
        error = self.train_state()["last"]["error"]
        self.assertIn("is the train's own landing worktree and holds no one else's work", error)
        self.assertNotIn("sanctioned-mint-and-double-compile", self.names()[before:])
        remedy = error.rsplit("once it is gone: ", 1)[1]
        self.assertEqual(remedy, f"rm -rf {shlex.quote(str(landing))} && git -C {shlex.quote(str(self.repo.resolve()))} worktree prune")
        subprocess.run(["/bin/sh", "-c", remedy], check=True)
        self.foreign_commit("moved again")
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual(git(landing / "first-party/fixture", "rev-parse", "HEAD"), pin)
        # A child past its pin with a commit no ref holds: scripts/submodule_sync.sh will not restore it.
        child = landing / "first-party/fixture"
        (child / "value").write_text("a local commit")
        git(child, "-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qam", "local")
        self.foreign_commit("moved a third time")
        self.assertEqual(self.tick(), 1)
        self.assertTrue(self.train_state()["last"]["error"].endswith(f"once it is gone: {remedy}"),
                        self.train_state()["last"]["error"])

    def test_landing_materialization_names_its_phase_before_checkout_and_pin_work(self):
        self.gated_trust()
        observed = []
        checkout = stage.Train.landing_checkout
        submodules = stage.Train.landing_submodules

        def checkout_with_phase(train, runner):
            if not observed:
                observed.append(("checkout", self.train_state()["last"]["phase"]))
            return checkout(train, runner)

        def submodules_with_phase(train, runner, landing, name):
            if name == "cut":
                observed.append(("pins", self.train_state()["last"]["phase"]))
            return submodules(train, runner, landing, name)

        with mock.patch.object(stage.Train, "landing_checkout", checkout_with_phase), \
             mock.patch.object(stage.Train, "landing_submodules", submodules_with_phase):
            self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual(observed, [("checkout", "materializing landing source"),
                                    ("pins", "materializing landing source")])
        self.assertIn("sanctioned-mint-and-double-compile", self.names())
        self.assertEqual(self.names().count("release-signing-ready"), 1)

    def test_landing_submodules_that_cannot_be_materialized_end_the_tick_before_any_push(self):
        pin, _url, _server, log = self.submodule_trust(refuse_landing=True)
        cut = git(self.repo, "rev-parse", "HEAD")
        self.assertEqual(self.tick(), 1)
        state = self.train_state()
        self.assertEqual(state["last"]["status"], "failed")
        self.assertEqual(state["last"]["phase"], "materializing landing source")
        self.assertIn("Agh source fetch failed", state["last"]["error"])
        # Nothing was left in the train's worktree, so its removal is not offered as the remedy.
        self.assertNotIn("is the train's own landing worktree", state["last"]["error"])
        # The source snapshot got its child; the landing's was refused, before the mint and step 4.
        self.assertTrue(any("landing.noindex" not in line for line in log.read_text().splitlines()))
        names = self.names()
        self.assertNotIn("sanctioned-mint-and-double-compile", names)
        self.assertNotIn("seed-archives-and-repin-branch", names)
        self.assertFalse([name for name in names if "-push-" in name])
        self.assertEqual((self.github.main(), self.github.builds()), (cut, []))
        self.assertEqual(git(self.root / "trust.git", "branch", "--list", "seed/repin-*"), "")
        self.assertFalse(self.hook_ran.exists())
        self.assertFalse((self.state / "landing.noindex/first-party/fixture/.git").exists())

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

    def publication_steps(self, names):
        return [name for name in names if name.startswith(("index-status", "canary", "publish-staged", "controller-"))]

    def test_lost_index_races_are_published_again_on_the_new_head(self):
        self.gated_trust()
        build = int(git(self.repo, "rev-list", "--count", "HEAD"))
        self.owners.races = {"publish-staged": 2, "controller-index": 1}
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual(self.publication_steps(self.names()), [
            "index-status", "canary", "publish-staged-1", "publish-staged-head-1", "publish-staged-2",
            "publish-staged-head-2", "publish-staged-3", "publish-staged-served", "controller-pack",
            "controller-index-1", "controller-index-head-1", "controller-index-2", "controller-index-served"])
        state = self.train_state()
        # Index 40, then 41 and 42 to the other publisher, 43 for this build; 44 to the other, 45 for the controller.
        self.assertEqual((state["last"]["status"], state["good"]["index"], state["good"]["controller_index"]),
                         ("published", 43, 45))
        self.assertEqual(self.owners.head["pins"], {"trust": build, CONTROLLER: build,
                                                    "trust-ir": 2, "trust-cg": 3, "trust-vc": 4})
        # Every run publishes the same staged group, and the controller under the cut's build number.
        runs = [argv for name, argv, _env in self.owners.calls if name.removeprefix("publish-staged-").isdigit()]
        self.assertEqual(len(runs), 3)
        self.assertEqual(len({tuple(argv[argv.index("atpkg-publish"):]) for argv in runs}), 1)
        pack = next(argv for name, argv, _env in self.owners.calls if name == "controller-pack")
        self.assertEqual(pack[pack.index("--build") + 1], str(build))
        self.assertEqual(pack[pack.index("--checkout") + 1], str(Path(state["good"]["build_dir"]) / "source/crates" / CONTROLLER))

    def test_index_publish_stops_after_three_lost_races_and_retries_no_other_refusal(self):
        self.gated_trust()
        build = int(git(self.repo, "rev-list", "--count", "HEAD"))
        self.owners.races = {"publish-staged": 3}
        self.assertEqual(self.tick(), 1)
        state = self.train_state()
        self.assertEqual(self.publication_steps(self.names()), [
            "index-status", "canary", "publish-staged-1", "publish-staged-head-1", "publish-staged-2",
            "publish-staged-head-2", "publish-staged-3", "publish-staged-head-3"])
        self.assertEqual((state["last"]["status"], state["good"]["build"]), ("staged", build))
        self.assertIn("another publisher took the next index number under each of 3 runs of publish-staged", state["last"]["error"])
        self.assertNotIn("published", state)
        # The consumer report still ran and landed.
        self.assertIn("finding(s) in docs/OPEN_ISSUES.md", state["last"]["report"])
        # An orphaned draft is no race: the next tick runs the publish once, reusing the signed canary receipt.
        self.owners.refusals = {"publish-staged": "atpkg-index-44 exists on fixture/atpkg-index as an orphaned DRAFT "
                                                  "with DIFFERENT bytes (index.toml) — never clobbered or published"}
        calls = len(self.owners.calls)
        self.assertEqual(self.tick(), 1)
        later = self.names()[calls:]
        self.assertEqual(self.publication_steps(later), ["index-status", "publish-staged-1"])
        self.assertNotIn("release-signing-ready", later)
        self.assertIn("orphaned DRAFT", self.train_state()["last"]["error"])
        self.assertEqual(self.train_state()["good"]["publish_ticks"], 2)

    def test_staged_build_is_published_by_the_next_tick_before_another_cut(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        self.owners.refusals = {"publish-staged": "could not reach fixture/atpkg-index (agh exited 7)"}
        self.assertEqual(self.tick(), 1)
        state = self.train_state()
        first = Path(state["good"]["build_dir"])
        self.assertEqual((state["last"]["status"], state["good"]["publish_ticks"]), ("staged", 1))
        self.assertNotIn("index", state["good"])
        self.assertEqual(json.loads((first / "latest.json").read_text())["status"], "staged")
        # Neither the status line nor the cut decision counts a build that is only staged.
        status = stage.train_status(self.state, self.train().read_main)
        self.assertRegex(status, rf"^train: no published build is known \([0-9a-f]{{12}}, build [0-9]+, read [^)]*\); "
                                 rf"newest staged build {build}; build {build} is staged and not yet published "
                                 rf"\(.*could not reach fixture/atpkg-index")
        self.assertIn(f"the last train staged build {build} ({cut[:12]}) at ", status)
        # Main moves. The next tick publishes the staged build first, in its own build directory, then cuts main.
        self.owners.refusals = {}
        moved = self.foreign_commit("moved")
        calls = len(self.owners.calls)
        self.assertEqual(self.tick(), 0, self.train_state())
        later = self.owners.calls[calls:]
        names = [name for name, _argv, _env in later]
        self.assertLess(names.index("controller-index-served"), names.index("release-signing-ready"))
        resumed = next(argv for name, argv, _env in later if name == "publish-staged-1")
        self.assertEqual(resumed[resumed.index("--out") + 1], str(first / "group"))
        # The first build's signed canary receipt is reused; the new build gets its own canary.
        self.assertEqual(names.count("canary"), 1)
        self.assertLess(names.index("release-signing-ready"), names.index("canary"))
        record = json.loads((first / "latest.json").read_text())
        self.assertEqual((record["status"], record["published"]["index"], record["published"][CONTROLLER]),
                         ("published", "atpkg-index-41", "atpkg-index-42"))
        state = self.train_state()
        moved_build = int(git(self.repo, "rev-list", "--count", moved))
        self.assertEqual((state["published"]["build"], state["published"]["index"], state["last"]["status"]),
                         (moved_build, 43, "published"))

    def test_publication_refused_for_three_ticks_is_given_up_and_the_train_cuts_again(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        self.owners.refusals = {"canary": "canary client install refused: digest mismatch"}
        self.assertEqual(self.tick(), 1)
        calls = len(self.owners.calls)
        self.assertEqual(self.tick(), 1)
        self.assertNotIn("release-signing-ready", self.names()[calls:])
        # A canary that ended early is moved aside; the publisher signs only into a fresh directory.
        group = Path(self.train_state()["good"]["build_dir"]) / "group"
        self.assertEqual(len(list(group.glob("canary.*"))), 1)
        # The tick that gives the build up has failed, though it has nothing to cut.
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train().tick(), 1)
        self.assertIn("nothing to cut", printed.call_args.args[0])
        state = self.train_state()
        self.assertEqual((state["good"]["publish_ticks"], self.names().count("canary")), (3, 3))
        self.assertIn("given_up", state["good"])
        self.assertIn("given up after 3 ticks", state["last"]["error"])
        self.assertIn(f"staged build {build} was not published, given up after 3 ticks (", stage.train_status(self.state))
        # No fourth try: main moves, and the next tick cuts it and publishes the new build.
        self.owners.refusals = {}
        moved = self.foreign_commit("moved")
        calls = len(self.owners.calls)
        self.assertEqual(self.tick(), 0, self.train_state())
        later = self.names()[calls:]
        self.assertLess(later.index("release-signing-ready"), later.index("index-status"))
        self.assertEqual(self.train_state()["published"]["build"], int(git(self.repo, "rev-list", "--count", moved)))

    def test_index_host_none_stops_each_build_at_the_stage_upload(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        self.assertEqual(self.tick("--index-host", "none"), 0, self.train_state())
        state = self.train_state()
        self.assertEqual(state["last"]["status"], "staged")
        self.assertEqual(self.publication_steps(self.names()), [])
        self.assertNotIn("index-hosts-check", self.names())
        self.assertNotIn("published", state)
        record = json.loads((Path(state["good"]["build_dir"]) / "latest.json").read_text())
        self.assertEqual((record["status"], record["settings"]["index_host"], "published" in record), ("staged", "none", False))
        status = stage.train_status(self.state, self.train("--index-host", "none").read_main)
        self.assertRegex(status, rf"^train: no published build is known \(.*\); newest staged build {build}; "
                                 rf"build {build} is staged and not yet published; the last train staged build {build} ")
        # Given the index host again, the next tick publishes that build; main has not moved, so nothing is cut.
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train().tick(), 0)
        self.assertIn("nothing to cut", printed.call_args.args[0])
        state = self.train_state()
        self.assertEqual((state["last"]["status"], state["published"]["build"]), ("published", build))
        self.assertIn(f"train: last published build {build} (atpkg-index-41)", stage.train_status(self.state))

    def test_staged_build_an_index_already_passed_is_not_published(self):
        self.gated_trust()
        build = int(git(self.repo, "rev-list", "--count", "HEAD"))
        self.owners.head["pins"]["trust"] = build + 100
        self.assertEqual(self.tick(), 0, self.train_state())
        state = self.train_state()
        self.assertEqual((state["last"]["status"], state["good"]["superseded_by"]), ("staged", build + 100))
        self.assertEqual(self.publication_steps(self.names()), ["index-status"])
        self.assertIn(f"staged build {build} was not published: the index already pins trust {build + 100}",
                      stage.train_status(self.state))

    def test_publication_interrupted_or_killed_is_finished_by_the_next_tick(self):
        self.gated_trust()
        build = int(git(self.repo, "rev-list", "--count", "HEAD"))
        self.owners.interrupt = "publish-staged-1"
        self.assertEqual(self.tick(), 1)
        state = self.train_state()
        self.assertEqual(state["last"]["status"], "staged")
        self.assertIn("after the upload: fixture interruption", state["last"]["error"])
        # A publishing tick killed outright leaves its record running; the next tick reads the head and finishes.
        self.owners.interrupt = None
        state["last"].update(status="running", kind="publish")
        stage.atomic_json(self.state / "train.json", state)
        self.assertIn("ended without a result; the next tick publishes again", stage.train_status(self.state))
        calls = len(self.owners.calls)
        self.assertEqual(self.tick(), 0, self.train_state())
        self.assertEqual(self.publication_steps(self.names()[calls:]), [
            "index-status", "publish-staged-1", "publish-staged-served", "controller-pack", "controller-index-1",
            "controller-index-served"])
        state = self.train_state()
        self.assertEqual((state["last"]["status"], state["last"]["kind"], state["published"]["build"]),
                         ("published", "publish", build))

    def test_dry_run_says_it_would_publish_a_staged_build_first_and_does_nothing(self):
        self.gated_trust()
        build = int(git(self.repo, "rev-list", "--count", "HEAD"))
        self.owners.refusals = {"publish-staged": "refused for the fixture"}
        self.assertEqual(self.tick(), 1)
        moved = self.foreign_commit("moved")
        calls = len(self.owners.calls)
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train("--dry-run").tick(), 0)
        self.assertEqual(len(self.owners.calls), calls)
        first, plan = (call.args[0] for call in printed.call_args_list)
        self.assertTrue(first.startswith(f"train: would first publish staged build {build} ("), first)
        self.assertIn("tick 2 of 3", first)
        self.assertIn(f"`canary trust={build} --out <its build>/group/canary`", first)
        self.assertIn("7. its custody: the source snapshot clean at the cut commit and each artifact the train keeps", first)
        self.assertIn(f"train: would cut {moved[:12]}", plan)
        self.assertIn("7. the run's end checks: the source snapshot clean at the cut commit; every artifact, the Lean", plan)
        self.assertLess(plan.index("never published"), plan.index("--publish-staged"))
        self.assertIn("`atpkg-publish hosts check --host agh-staging` and `hosts check --host agh`", plan)
        self.assertIn("`publish-group rustc --publish-staged --out <build>/group`", plan)
        self.assertIn(f"`index --pin {CONTROLLER}=", plan)
        self.assertEqual(self.train_state()["good"]["publish_ticks"], 1)
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train("--dry-run", "--index-host", "none").tick(), 0)
        self.assertEqual(len(printed.call_args_list), 1)
        self.assertIn("never published);\n     the index is not changed (--index-host none)", printed.call_args.args[0])
        self.assertNotIn("canary", printed.call_args.args[0])
        self.assertEqual(len(self.owners.calls), calls)

    def build_dir(self):
        """The build directory of the train that is running or ran last."""
        return Path(self.train_state()["last"]["build_dir"])

    def test_a_build_whose_custody_breaks_after_its_upload_is_never_published(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        self.owners.after["signed-pack-stage-upload"] = lambda: (
            self.build_dir() / f"toolchains/stage-trust-{cut}/bin/trustc").write_text("#!/bin/sh\necho changed\n")
        self.assertEqual(self.tick(), 1)
        state = self.train_state()
        # Staged, and nothing went to the index: no status read, no canary, no publish.
        self.assertEqual(self.github.builds(), [build])
        self.assertEqual(self.publication_steps(self.names()), [])
        self.assertEqual(self.owners.head, {"index": 40, "pins": {"trust": 1, CONTROLLER: 1}})
        self.assertNotIn("published", state)
        self.assertEqual(state["last"]["status"], "staged")
        self.assertIn("its custody check failed: artifact changed during staging", state["good"]["custody_error"])
        self.assertIn(f"build {build} is never published: its custody check failed", state["last"]["error"])
        # The run's own end checks found it again; its record says what the build is, as train.json does.
        record = json.loads((self.build_dir() / "latest.json").read_text())
        self.assertEqual(record["status"], "staged")
        self.assertIn("artifact changed during staging", record["error"])
        self.assertIn(f"; staged build {build} is never published: its custody check failed", stage.train_status(self.state))
        # No later tick publishes it: main has not moved, so nothing runs at all.
        calls = len(self.owners.calls)
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train().tick(), 0)
        self.assertIn("nothing to cut", printed.call_args.args[0])
        self.assertEqual(len(self.owners.calls), calls)

    def test_a_resumed_publication_first_checks_the_source_it_reads(self):
        self.gated_trust()
        build = int(git(self.repo, "rev-list", "--count", "HEAD"))
        self.owners.refusals = {"publish-staged": "could not reach fixture/atpkg-index (agh exited 7)"}
        self.assertEqual(self.tick(), 1)
        self.owners.refusals = {}
        # Between ticks, a file appears in the build's source snapshot, which the controller pack reads.
        (self.build_dir() / "source/crates").mkdir(exist_ok=True)
        (self.build_dir() / "source/crates/stray.rs").write_text("fn main() {}\n")
        calls = len(self.owners.calls)
        self.assertEqual(self.tick(), 1)
        self.assertEqual(self.publication_steps(self.names()[calls:]), [])
        state = self.train_state()
        self.assertIn("its custody check failed: refusing to move or build a dirty managed worktree",
                      state["good"]["custody_error"])
        self.assertEqual((state["good"]["publish_ticks"], state["last"]["status"]), (2, "staged"))
        self.assertIn(f"build {build} is never published", state["last"]["error"])
        # Never tried again.
        calls = len(self.owners.calls)
        self.assertEqual(self.tick(), 0)
        self.assertEqual(len(self.owners.calls), calls)

    def test_a_source_changed_during_publication_stops_the_controller_pack(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        self.owners.after["canary"] = lambda: (self.build_dir() / "source/stray.rs").write_text("fn main() {}\n")
        self.assertEqual(self.tick(), 1)
        state = self.train_state()
        self.assertEqual(self.publication_steps(self.names()), ["index-status", "canary", "publish-staged-1",
                                                                 "publish-staged-served"])
        self.assertEqual(self.owners.head["pins"], {"trust": build, CONTROLLER: 1, "trust-ir": 2, "trust-cg": 3, "trust-vc": 4})
        self.assertEqual((state["last"]["status"], state["published"]["build"], state["good"]["index"]), ("published", build, 41))
        self.assertIn(f"{CONTROLLER} {build} is never published: its custody check failed: refusing to move or build "
                      "a dirty managed worktree", state["last"]["error"])
        # The run's end checks failed after the index served the build: the tick fails, and the
        # record keeps the build published with that error, as train.json does.
        self.assertIn("after the upload: refusing to move or build a dirty managed worktree", state["last"]["error"])
        record = json.loads((self.build_dir() / "latest.json").read_text())
        self.assertEqual((record["status"], record["published"]["index"]), ("published", "atpkg-index-41"))
        self.assertIn("dirty managed worktree", record["error"])
        self.assertIn(f"; {CONTROLLER} {build} is never published: its custody check failed", stage.train_status(self.state))
        calls = len(self.owners.calls)
        self.assertEqual(self.tick(), 0)
        self.assertEqual(len(self.owners.calls), calls)

    def test_an_artifact_changed_after_publication_fails_the_tick_and_stays_recorded(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        # The build and its controller are served; then the staged tree changes, before the run's end checks.
        self.owners.after["controller-index-1"] = lambda: (
            self.build_dir() / f"toolchains/stage-trust-{cut}/bin/trustc").write_text("#!/bin/sh\necho changed\n")
        self.assertEqual(self.tick(), 1)
        state = self.train_state()
        self.assertEqual((self.owners.head["pins"]["trust"], self.owners.head["pins"][CONTROLLER]), (build, build))
        self.assertEqual((state["last"]["status"], state["good"]["index"], state["good"]["controller_index"]),
                         ("published", 41, 42))
        self.assertIn("after the upload: artifact changed during staging", state["last"]["error"])
        record = json.loads((self.build_dir() / "latest.json").read_text())
        self.assertEqual((record["status"], record["published"][CONTROLLER]), ("published", "atpkg-index-42"))
        self.assertIn("artifact changed during staging", record["error"])

    def test_a_v1_trains_state_is_migrated_and_its_staged_build_published(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        self.assertEqual(self.tick("--index-host", "none"), 0, self.train_state())
        # What a v1 train left: its stage-upload recorded as `published`, with the index unchanged.
        state = self.train_state()
        state["schema"] = "trust.toolchain-train.v1"
        state["good"]["published_at"] = state["good"].pop("staged_at")
        state["last"].update(status="published", published_at=state["last"].pop("staged_at"))
        state["main"]["published"] = state["main"].pop("staged")
        stage.atomic_json(self.state / "train.json", state)
        build_dir = Path(state["good"]["build_dir"])
        record = json.loads((build_dir / "latest.json").read_text())
        record.update(status="published", published={**record.pop("staged"), "index": "unchanged"})
        for key in ("publisher_host", "index_host"):
            del record["settings"][key]
        stage.atomic_json(build_dir / "latest.json", record)
        # A later cut trimmed the kept build to what it keeps of one.
        for relative in stage.TRAIN_INTERMEDIATES:
            if (build_dir / relative).is_dir():
                stage.remove_tree(build_dir / relative)
        self.assertRegex(stage.train_status(self.state), rf"^train: no published build is known .*; build {build} is staged "
                                                         rf"and not yet published; the last train staged build {build} ")
        calls = len(self.owners.calls)
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train().tick(), 0, self.train_state())
        self.assertIn("nothing to cut", printed.call_args.args[0])
        self.assertEqual(self.publication_steps(self.names()[calls:]), [
            "index-status", "canary", "publish-staged-1", "publish-staged-served", "controller-pack",
            "controller-index-1", "controller-index-served"])
        state = self.train_state()
        self.assertEqual((state["schema"], state["migrated"]["from"]), (stage.TRAIN_SCHEMA, "trust.toolchain-train.v1"))
        self.assertEqual((state["last"]["status"], state["published"]["build"], state["good"]["controller_index"]),
                         ("published", build, 42))
        record = json.loads((build_dir / "latest.json").read_text())
        self.assertEqual((record["status"], record["staged"]["tag"], record["published"]["index"]),
                         ("published", f"atpkg-trust-{build}", "atpkg-index-41"))
        self.assertIn("a v1 train's record", record["migrated"])

    def test_a_staging_tag_that_counts_main_is_no_reason_not_to_cut(self):
        self.gated_trust()
        tip = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", tip))
        # Another publisher stage-uploaded main's tip; no index serves it; this state root is new.
        git(self.repo, "push", "-q", "origin", f"{tip}:refs/tags/atpkg-trust-{build}")
        with mock.patch("builtins.print") as printed:
            self.assertEqual(self.train("--dry-run").tick(), 0)
        self.assertTrue(printed.call_args.args[0].startswith(
            f"train: would cut {tip[:12]} (build {build}): main is at {tip[:12]}, past every published build\n"),
            printed.call_args.args[0])
        self.assertEqual(self.owners.calls, [])
        self.assertEqual(self.train_state()["main"]["staged"], build)
        self.assertRegex(stage.train_status(self.state),
                         rf"^train: no published build is known \(.*\); newest staged build {build}; no train has run here$")

    def test_an_index_found_serving_the_build_is_recorded_as_found_and_kept(self):
        self.gated_trust()
        cut = git(self.repo, "rev-parse", "HEAD")
        build = int(git(self.repo, "rev-list", "--count", cut))
        # The tick ends after its index publish, before it read the head back.
        self.owners.interrupt = "publish-staged-served"
        self.assertEqual(self.tick(), 1)
        self.owners.interrupt = None
        self.assertEqual((self.owners.head["index"], self.owners.head["pins"]["trust"]), (41, build))
        # Another publisher writes the next index; this train's controller pack is refused once.
        self.owners.head["index"] += 1
        self.owners.head["pins"]["trust-ir"] = 9
        self.owners.refusals = {"controller-pack": "refused for the fixture"}
        self.assertEqual(self.tick(), 1)
        state = self.train_state()
        # Which index first served it is not known: the head the train read is recorded, as found.
        self.assertEqual((state["good"]["index"], state["good"]["found_served"], state["published"]["found_served"]),
                         (42, ["trust"], True))
        status = stage.train_status(self.state)
        self.assertIn(f"train: last published build {build} (found served by atpkg-index-42), ", status)
        self.assertIn(f"; {CONTROLLER} {build} is not yet published (controller-pack: refused for the fixture); "
                      f"the last train found build {build} ({cut[:12]}) served by atpkg-index-42 at ", status)
        # Another index again. The next tick publishes the controller and keeps the index it recorded.
        self.owners.refusals = {}
        self.owners.head["index"] += 1
        self.assertEqual(self.tick(), 0, self.train_state())
        state = self.train_state()
        self.assertEqual((state["good"]["index"], state["published"]["index"], state["good"]["controller_index"]),
                         (42, 42, 44))
        record = json.loads((self.build_dir() / "latest.json").read_text())
        self.assertEqual((record["published"]["index"], record["published"]["found_served"], record["published"][CONTROLLER]),
                         ("atpkg-index-42", ["trust"], "atpkg-index-44"))

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
        # A build that is only staged counts for nothing: no index serves build 9.
        staged = {"settled": other, "last": {"status": "staged", "build": 9}, "good": {"build": 9}}
        self.assertEqual(stage.train_decision(staged, tip, None, 9), (True, f"main is at {tip[:12]}, past every published build"))
        self.assertTrue(stage.train_decision(staged, tip, 7, 9)[0])

    def test_fleet_publisher_builds_exactly_the_trains_commands(self):
        group = ["publish-group", "rustc", "--seal", "/seal", "--trust-repo", "/trust", "--checkout", "trust-ir=/ir",
                 "--checkout", "trust-cg=/cg", "--checkout", "trust-vc=/vc", "--out", "/out"]
        prefix = ["/bin/targo", "--unverified", "run", "-q", "--locked", "-p", "atpkg-publish", "--"]
        canary = ["canary", "trust=12", "--out", "/out/canary", "--consumer", "aterm=/a", "--consumer", "ay=/b",
                  "--consumer", "ty=/c", "--consumer", "clean=/d"]
        controller = [CONTROLLER, "--checkout", "/trust/crates/c", "--toolchain", "/seal/bin", "--trust-repo", "/trust",
                      "--build", "12", "--out", "/build/controller", "--upload"]
        index = ["index", "--pin", f"{CONTROLLER}=12", "--out", "/build/controller-index", "--upload"]
        for host in ("agh-staging", "agh"):
            self.assertEqual(stage.fleet_publisher("/bin/targo", host, ["hosts", "check"]),
                             [*prefix, "hosts", "check", "--host", host])
        for host in ("agh-staging", "agh", "gh"):
            for mode in ("--dry-run", "--stage-upload"):
                self.assertEqual(stage.fleet_publisher("/bin/targo", host, [*group, mode]),
                                 [*prefix, "--host", host, *group, mode])
        for words in (canary, ["publish-group", "rustc", "--publish-staged", "--out", "/out"], ["status"],
                      ["pack", *controller], index):
            self.assertEqual(stage.fleet_publisher("/bin/targo", "agh", words), [*prefix, "--host", "agh", *words])
            # Writing the index, its evidence or the controller goes only through agh.
            for host in ("agh-staging", "gh"):
                with self.subTest(host=host, words=words), self.assertRaisesRegex(stage.Refused, "not a fleet train's"):
                    stage.fleet_publisher("/bin/targo", host, words)
        refused = [
            [*group], [*group, "--dry-run", "--stage-upload"], [*group, "--publish-staged"], [*group, "--stage-upload", "--upload"],
            [*group, "--stage-upload", "--force-same-build"], [*group[:-2], "--force-same-build", "/out", "--stage-upload"],
            [*group, "--stage-upload", "--allow-build-tree-seal"], [*group[:-1], "out", "--stage-upload"],
            ["publish-group", "rustc", "--publish-staged", "--out", "/out", "--force-same-build"],
            ["publish-group", "rustc", "--publish-staged", "--seal", "/seal", "--out", "/out"],
            [*canary, "--stage-receipt"], canary[:-2], ["canary", "trust=0", *canary[2:]], ["canary", "trust=x", *canary[2:]],
            ["pack", "trust", *controller[1:]], ["pack-bundle", *controller], ["pack", *controller[:-1]],
            ["pack", *controller, "--unsigned"], ["pack", *controller[:-5], "--merge-from", "/m", *controller[-5:]],
            ["index", "--pin", "trust=12", "--out", "/o", "--upload"], [*index, "--yank", "trust@11"],
            ["index", "--target-pin", f"aarch64-apple-darwin:{CONTROLLER}=12", "--out", "/o", "--upload"],
            ["index", "--pin", f"{CONTROLLER}=12", "--upload"], ["mirror", "--upload"], ["status", "--releases"],
            ["lane", "withdraw", "alab"], ["lane", "run", "alab"], ["adopt", "trust=12"], ["withdraw"],
            ["publish-group", "aterm", "--stage-upload"], ["hosts", "check", "x"]]
        for words in refused:
            for host in ("agh-staging", "agh"):
                with self.subTest(host=host, words=words), self.assertRaisesRegex(stage.Refused, "not a fleet train's"):
                    stage.fleet_publisher("/bin/targo", host, words)
        with self.assertRaisesRegex(stage.Refused, "not a fleet train's"):
            stage.fleet_publisher("/bin/targo", "gh", ["hosts", "check"])

    def test_index_pins_read_the_channel_head_a_client_on_the_host_installs(self):
        prefix = "atpkg-publish status: "
        text = "".join(prefix + line + "\n" for line in (
            "atpkg-index-57 — signed by machine m86 under roster_seq 4", "producer: something",
            "channel alab (channel_build 57): min_build 1", "  min_build trust: 3", "  pin trust = 16387 [rustc]",
            f"  pin {CONTROLLER} = 16300", "  pin trust = 16400 on aarch64-apple-darwin",
            "  pin trust = 9 on x86_64-unknown-linux-gnu", "  pin ty = 5 on riscv-unknown (not a target this client knows)"))
        noise = "   Compiling atpkg-publish\natpkg-publish canary: pin trust = 1\n"
        self.assertEqual(stage.index_pins(noise + text, "aarch64-apple-darwin"),
                         (57, {"trust": 16400, CONTROLLER: 16300}))
        self.assertEqual(stage.index_pins(text, "x86_64-apple-darwin"), (57, {"trust": 16387, CONTROLLER: 16300}))
        with self.assertRaisesRegex(stage.Refused, "no signed index"):
            stage.index_pins(noise, "aarch64-apple-darwin")
        with self.assertRaisesRegex(stage.Refused, "two channel heads"):
            stage.index_pins(text + text, "aarch64-apple-darwin")

    def test_lost_index_race_is_read_from_the_publishers_refusal(self):
        log = self.root / "publish.log"
        for text, race in (("…DIFFERENT bytes (index.toml) — another publisher took index 58; never clobbered.", True),
                           ("creating atpkg-index-58 on o/atpkg-index failed — if it exists now (a racing publisher), re-run", True),
                           ("atpkg-index-58 exists on o/atpkg-index as an orphaned DRAFT with DIFFERENT bytes (index.toml)", False),
                           ("the packs atpkg-index-58 pins are not all public", False)):
            log.write_text('{"argv": []}\n' + text + "\n")
            self.assertEqual(stage.lost_index_race(log), race, text)
        self.assertFalse(stage.lost_index_race(self.root / "absent.log"))
        # A refusal names the publisher's own last error line, not a progress line of a verb.
        log.write_text('{"argv": []}\natpkg-publish status: atpkg-index-57 — signed\natpkg-publish: REFUSED — first\n'
                       "  - a problem\natpkg-publish: could not run — agh exited 7\n")
        self.assertEqual(stage.publisher_refusal(log), "could not run — agh exited 7")
        log.write_text('{"argv": []}\natpkg-publish canary: Trust 12: installed\n')
        self.assertIsNone(stage.publisher_refusal(log))

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
            # `print` of a job launchd no longer runs exits 113.
            return types.SimpleNamespace(returncode=113 if argv[1] == "print" else 0, stdout="", stderr="")
        agent = stage.train_install(args, launchctl)
        domain = f"gui/{os.getuid()}"
        self.assertEqual(agent, agents / "systems.alab.trust-train.plist")
        self.assertEqual(plistlib.loads(agent.read_bytes()), stage.train_plist(args))
        self.assertEqual(plistlib.loads(agent.read_bytes())["StartInterval"], 1800)
        self.assertEqual(calls, [["launchctl", "bootstrap", domain, str(agent)]])
        # Installed again, the running agent is stopped and replaced once launchd no longer runs it.
        stage.train_install(args, launchctl)
        self.assertEqual(calls[1:], [["launchctl", "bootout", f"{domain}/systems.alab.trust-train"],
                                     ["launchctl", "print", f"{domain}/systems.alab.trust-train"],
                                     ["launchctl", "bootstrap", domain, str(agent)]])
        self.assertEqual([path.name for path in agents.iterdir()], [agent.name])
        self.assertEqual(stage.train_remove(args, launchctl), agent)
        self.assertEqual(calls[-1], ["launchctl", "bootout", f"{domain}/systems.alab.trust-train"])
        self.assertFalse(agent.exists())
        self.assertTrue(self.state.is_dir())
        with self.assertRaisesRegex(stage.Refused, "launchctl bootstrap exited 5: Bootstrap failed.*not loaded"):
            stage.train_install(args, lambda argv, **_kwargs: types.SimpleNamespace(
                returncode=5, stdout="", stderr="Bootstrap failed\n"))

    def test_train_install_waits_for_a_stopping_tick_before_it_starts_the_new_agent(self):
        agents = self.root / "LaunchAgents"
        args = self.train_arguments("--launch-agents", str(agents))
        agents.mkdir()
        (agents / "systems.alab.trust-train.plist").write_bytes(b"old agent")
        calls, stopping = [], [2]  # launchd still runs the SIGTERMed tick for two more prints

        def launchctl(argv, **_kwargs):
            calls.append(argv[1])
            if argv[1] == "print":
                stopping[0] -= 1
                return types.SimpleNamespace(returncode=0 if stopping[0] >= 0 else 113, stdout="", stderr="")
            if argv[1] == "bootstrap" and stopping[0] >= 0:
                return types.SimpleNamespace(returncode=5, stdout="", stderr="Bootstrap failed: 5")
            return types.SimpleNamespace(returncode=0, stdout="", stderr="")
        with mock.patch.object(stage.time, "sleep") as slept:
            stage.train_install(args, launchctl)
        self.assertEqual(calls, ["bootout", "print", "print", "print", "bootstrap"])
        self.assertEqual(slept.call_count, 2)
        self.assertEqual(plistlib.loads((agents / "systems.alab.trust-train.plist").read_bytes()), stage.train_plist(args))
        # A job launchd never stops refuses the install and leaves the old agent's file.
        (agents / "systems.alab.trust-train.plist").write_bytes(b"old agent")
        with mock.patch.object(stage, "TRAIN_BOOTOUT_WAIT", 0), \
                self.assertRaisesRegex(stage.Refused, "still runs systems.alab.trust-train"):
            stage.train_install(args, lambda argv, **_kwargs: types.SimpleNamespace(returncode=0, stdout="", stderr=""))
        self.assertEqual((agents / "systems.alab.trust-train.plist").read_bytes(), b"old agent")

    def test_a_tick_fast_forwards_its_own_clean_checkout_on_main_and_nothing_else(self):
        self.gated_trust()
        before = git(self.repo, "rev-parse", "HEAD")
        original_blob = git(self.repo, "rev-parse", "HEAD:README")
        writer = self.root / "writer"
        subprocess.run(["git", "clone", "-q", str(self.root / "trust.git"), str(writer)], check=True)
        git(writer, "config", "user.email", "fixture@example.invalid")
        git(writer, "config", "user.name", "fixture")
        (writer / "README").write_text("historical file content")
        git(writer, "commit", "-qam", "intermediate controller source")
        historical = git(writer, "rev-parse", "HEAD:README")
        (writer / "README").write_text("moved on main")
        git(writer, "commit", "-qam", "main moved")
        git(writer, "push", "-q", "origin", "main")
        moved = git(writer, "rev-parse", "HEAD")
        # The controller has a GitHub origin with no usable raw Git transport.
        # Agh supplies the exact objects from the fixture's local bare source.
        git(self.repo, "remote", "set-url", "origin", "git@github.com:fixture/trust.git")
        git(self.repo, "config", "core.sshCommand", "/usr/bin/false")
        agh_bin = self.root / "source-bin"
        log = self.root / "source-transport-arguments"
        wrong = self.root / "wrong-source"
        rejected = self.root / "reject-fetch"
        scratch_log = self.root / "source-transport-scratch"
        executable(agh_bin / "agh", f"""#!/bin/sh
printf '%s\\n' "$@" >> {shlex.quote(str(log))}
printf '%s\\n' "$TMPDIR" >> {shlex.quote(str(scratch_log))}
[ "$1" = repo ] && [ "$2" = fetch ] && [ "$3" = fixture/trust ] &&
    [ "$5" = --ref ] && [ "$7" = --into ] && [ "$#" -eq 8 ] || exit 2
for guarded in core.hooksPath core.sshCommand; do
    /usr/bin/git -C "$4" config --local --get "$guarded" >/dev/null && exit 8
done
[ "$(/usr/bin/git -C "$4" config --local --get remote.origin.url)" = https://github.com/fixture/trust.git ] || exit 8
[ ! -e {shlex.quote(str(rejected))} ] || exit 9
if [ -e {shlex.quote(str(wrong))} ]; then
    exec /usr/bin/git -C "$4" update-ref "$8" {before}
fi
# Like NativeExact, supply old history even when the destination had its commit
# but lacked the blob before the fetch.
/usr/bin/git -C {shlex.quote(str(self.root / 'trust.git'))} cat-file blob {original_blob} |
    /usr/bin/git -C "$4" hash-object -w --stdin >/dev/null || exit 3
exec /usr/bin/git -C "$4" fetch --quiet --no-write-fetch-head --refmap= --no-tags \
    {shlex.quote(str(self.root / 'trust.git'))} "$6:$8"
""")
        selected_path = str(agh_bin) + os.pathsep + os.environ["PATH"]
        train = self.train()
        # tick() calls advance() holding the train's lock, which made its state root.
        train.root.mkdir(parents=True, exist_ok=True)
        # A killed advance left its intake and Agh's scratch behind; the lock says nothing
        # uses them.
        left = train.root / "controller-intake-killed.noindex"
        (left / "agh-1.noindex/.ubd/agh-git-1_0.noindex").mkdir(parents=True)
        (left / "agh-1.noindex/.ubd/agh-git-1_0.noindex/pack").write_bytes(b"partial")
        (left / "source").mkdir()
        (train.root / "controller-intake-link.noindex").symlink_to(self.repo)
        with mock.patch.dict(os.environ, {"PATH": selected_path}), mock.patch("builtins.print") as said:
            # This runner's bytes did not change, so the tick goes on in this process.
            self.assertFalse(train.advance())
        self.assertFalse(left.exists())
        self.assertTrue((train.root / "controller-intake-link.noindex").is_symlink())
        self.assertTrue((self.repo / "README").exists())
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), moved)
        self.assertEqual(git(self.repo, "rev-parse", "refs/remotes/origin/main"), moved)
        self.assertNotEqual(moved, before)
        arguments = log.read_text().splitlines()
        intake = Path(arguments[3])
        self.assertEqual(intake.parent.parent, self.state)
        self.assertFalse(intake.parent.exists())
        self.assertEqual(arguments, ["repo", "fetch", "fixture/trust", str(intake),
            "--ref", moved, "--into", "refs/agh/trust-train/advance"])
        # Agh's scratch was the train's own, inside the intake's directory, and is gone.
        [scratch] = map(Path, scratch_log.read_text().splitlines())
        self.assertEqual(scratch.parent, intake.parent.resolve())
        self.assertFalse(scratch.exists())
        self.assertEqual(git(self.repo, "cat-file", "-p", historical), "historical file content")
        self.assertEqual(git(self.repo, "config", "--get", "core.hooksPath"), "scripts/hooks")
        self.assertEqual(git(self.repo, "config", "--get", "core.sshCommand"), "/usr/bin/false")
        said.assert_not_called()
        # On a tracking-only update the local tip already matches. Its missing
        # older README must still make it all the way back from the private intake.
        (self.repo / ".git/objects" / original_blob[:2] / original_blob[2:]).unlink()
        git(self.repo, "update-ref", "refs/remotes/origin/main", before, moved)
        with mock.patch.dict(os.environ, {"PATH": selected_path}), mock.patch("builtins.print") as said:
            self.assertFalse(train.advance())
        said.assert_not_called()
        self.assertEqual(git(self.repo, "rev-parse", "refs/remotes/origin/main"), moved)
        self.assertEqual(git(self.repo, "cat-file", "-p", original_blob), "trust")
        # A checkout with uncommitted changes, or on another branch, is left as it is.
        (writer / "README").write_text("moved again")
        git(writer, "commit", "-qam", "main moved again")
        git(writer, "push", "-q", "origin", "main")
        requested = git(writer, "rev-parse", "HEAD")
        # A failed fetch must not use the previous private ref, and a successful
        # fetch reporting the wrong commit must not select its checkout.
        for marker, message in [(rejected, "source fetch failed (exit 9)"),
                                (wrong, "source ref differs from the requested immutable commit")]:
            marker.touch()
            with mock.patch.dict(os.environ, {"PATH": selected_path}), mock.patch("builtins.print") as said:
                self.assertFalse(train.advance())
            self.assertIn(message, "\n".join(str(call.args[0]) for call in said.call_args_list))
            self.assertEqual(git(self.repo, "rev-parse", "HEAD"), moved)
            self.assertEqual(git(self.repo, "rev-parse", "refs/remotes/origin/main"), moved)
            marker.unlink()
        self.assertIn(requested, log.read_text().splitlines())
        mismatched = self.train("--github-repo", "elsewhere/trust")
        mismatched.github = None
        with mock.patch("builtins.print") as said:
            self.assertFalse(mismatched.advance())
        self.assertIn("differs from the checkout's origin", said.call_args[0][0])
        with mock.patch.object(stage.runpy, "run_path", side_effect=OSError("source helper unavailable")), \
                mock.patch("builtins.print") as said:
            self.assertFalse(train.advance())
        self.assertIn("source helper unavailable", said.call_args[0][0])
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), moved)
        (self.repo / "README").write_text("an edit of the checkout's own")
        with mock.patch("builtins.print") as said:
            self.assertFalse(train.advance())
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), moved)
        self.assertIn("uncommitted changes", said.call_args[0][0])
        git(self.repo, "checkout", "-q", "--", "README")
        git(self.repo, "checkout", "-q", "-b", "elsewhere")
        with mock.patch("builtins.print") as said:
            self.assertFalse(train.advance())
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), moved)
        self.assertIn("on elsewhere, not main", said.call_args[0][0])
        git(self.repo, "checkout", "-q", "main")
        # A local commit main does not contain is never overwritten.
        (self.repo / "README").write_text("a local commit")
        git(self.repo, "commit", "-qam", "local")
        local = git(self.repo, "rev-parse", "HEAD")
        with mock.patch.dict(os.environ, {"PATH": selected_path}), mock.patch("builtins.print") as said:
            self.assertFalse(train.advance())
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), local)
        self.assertEqual(git(self.repo, "rev-parse", "refs/remotes/origin/main"), moved)
        self.assertIn("does not fast-forward", "\n".join(str(call.args[0]) for call in said.call_args_list))

    def test_a_tick_whose_runner_changed_on_main_runs_the_new_runner_once(self):
        self.gated_trust()
        argv = ["/agent/runner.py", "train", "run", "--state-root", str(self.state)]
        train = self.train()
        train.tools.pop("agh")
        original = os.environ["PATH"]
        kept = {"directory": "/fixture/kept-agh/bin"}

        def advance():
            self.assertEqual(os.environ["PATH"], kept["directory"] + os.pathsep + original)
            return True

        def replaced(*_args):
            self.assertEqual(os.environ["PATH"], original)
            raise SystemExit("exec")

        with mock.patch.object(stage.Train, "advance", side_effect=advance) as advanced, \
                mock.patch.object(stage, "keep_agh", return_value=kept), \
                mock.patch.object(stage.os, "execv", side_effect=replaced) as execv, \
                mock.patch.object(stage.sys, "argv", argv), mock.patch.dict(os.environ, clear=False), \
                mock.patch("builtins.print"):
            os.environ.pop(stage.TRAIN_ADVANCED, None)
            with self.assertRaisesRegex(SystemExit, "exec"):
                train.tick()
            execv.assert_called_once_with(sys.executable, [sys.executable, *argv])
            self.assertEqual(os.environ[stage.TRAIN_ADVANCED], "1")
            # The new process does not advance again, and a dry run never advances.
            advanced.reset_mock()
            with mock.patch.object(stage.Train, "locked", return_value=0):
                self.assertEqual(train.tick(), 0)
            self.train("--dry-run").tick()
            os.environ.pop(stage.TRAIN_ADVANCED)
            self.train("--dry-run").tick()
            advanced.assert_not_called()

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
