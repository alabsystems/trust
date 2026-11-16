#!/usr/bin/env python3
"""Regressions for scripts/fixed_point_linux_seed.py: the build half of a first Linux seed.

The script sequences commands that have their own tests (seed_staircase.py,
mint_seed_support.py, linux_refresh_toolchain.py). What is its own, and what these
fixtures hold it to:

* `plan` prints every command of setup, the builds and dist in order and touches
  nothing; `status` reads files and touches nothing;
* `setup` binds every non-Rust input by digest, writes nothing outside the root, and
  each of its parts is done once: a second run repeats nothing, an interrupted one
  goes on, an argument a part refused is corrected under the same root, and one a
  done part used cannot be changed;
* the roles differ only in their stage0 and their label: one rung config, one build
  line, one environment, and a tool directory, cargo home, Lean copy, host C
  toolchain, fact store setting or trap-writing script that changed since an earlier
  role is a refusal before x.py starts;
* a label is used once: an interrupted build is followed by the next label from an
  empty build directory, one that ended not clean only with `--again`, and one that
  ended while the driver was away is judged from the record it left;
* where the evidence names the invoking account is recorded without spelling it;
* every expected failure is a refusal in words (the cause, the file or command, what
  was kept, what to run next) and never a traceback.

No compiler, no x.py and no network: `seed_staircase.py` and the checkout's own
scripts are small stand-ins, `mint_seed_support.py` is the real one over tiny trees.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: direct test execution needs the same tomllib floor as its driver.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_os.execv(_floor_path, [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]])
    _floor_sys.exit("fixed_point_linux_seed_test.py requires Python 3.11+ (tomllib); none found on PATH")

import argparse
import contextlib
import fcntl
import hashlib
import importlib.util
import io
import json
import os
import platform
import re
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import tomllib
import types
import unittest
from pathlib import Path
from unittest import mock

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts" / "fixed_point_linux_seed.py"
SPEC = importlib.util.spec_from_file_location("fixed_point_linux_seed", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
driver = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = driver
SPEC.loader.exec_module(driver)

GIT_ENV = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
           "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
           "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid"}
HOST = "aarch64-unknown-linux-gnu"
LEAN_PIN = "leanprover/lean4:v9.9.9"
LEAN_DIRECTORY = "leanprover--lean4---v9.9.9"
# An account no fixture path names, and a driver directory outside it.
NOBODY = ("/nonexistent/home-of-nobody", "nobody-at-all")
NEUTRAL_DRIVER = Path("/opt/trust-driver/scripts")
STAGE2 = {"bin/trustc": "trustc of the commit", "bin/targo-trust": "targo-trust", "bin/ty": "ty",
          "lib/libstd.so": "std"}
NATIVE = {"llvm/bin/llc": "\x7fELF llc", "llvm/lib/libLLVM.a": "!<arch>\nmember", "llvm/CMakeCache.txt": "text",
          "lld/bin/lld": "\x7fELF lld"}
ARCHIVES = {f"trustc-0.1.0-trust-{HOST}.tar.xz": 40, f"trustc-0.1.0-trust-{HOST}.tar.gz": 90,
            "trust-src-0.1.0-trust.tar.xz": 10}
TOOL = '#!/bin/sh\nprintf \'date %s server %s channel %s\\n\' "$3" "$4" "$5" > "$1/channel-rust-trust.toml"\n'
# What 82bb867edd's scripts/bootstrap_dependency_closure.py prints when `check` refuses
# (measured: its reason, then a `prepare` command for a person, which fetches).
CLOSURE_HINT = ("Prepare the SAME source and Cargo home separately, then retry:\n"
                "  env -u CARGO_BUILD_WARNINGS -u TARGO_BUILD_WARNINGS CARGO_HOME=/r/ledger/cargo-home "
                "/usr/bin/python3 -I -S -B /r/src/scripts/bootstrap_dependency_closure.py prepare --repo-root /r/src "
                "--targo /r/stage0/bin/cargo\n")
CLOSURE_MISSING = ("bootstrap dependency closure REFUSED: required bootstrap authority is missing: "
                   "src/bootstrap/src/core/metadata.rs\n" + CLOSURE_HINT)
CLOSURE_OUT_OF_TIME = (
    "bootstrap dependency fetch 1/54 offline src/bootstrap/Cargo.toml: command exited zero; inputs unchanged (8.1s)\n"
    "bootstrap dependency fetch 2/54 offline Cargo.toml: started\n"
    "bootstrap dependency fetch 2/54 offline Cargo.toml: refused after 891.9s\n"
    "bootstrap dependency closure REFUSED: dependency closure was not established for 2/54 offline Cargo.toml: "
    "the total budget expired while this fetch was still running; dependency child closure not established; no "
    "numeric PID/PGID signal is authorized; retain owner custody for enclosing-scope retirement\n"
    "    Unpacking serde v1.0.219\n" + CLOSURE_HINT)

# The base config seed-config writes, in the live root's shape: the target's C and C++
# compilers and linker by the names gcc and g++, which the roles cc and c++ resolve to.
BASE_CONFIG = ('profile = "compiler"\n\n[build]\npython = "/usr/bin/python3"\n\n'
               f'[target.{HOST}]\ncc = "/usr/bin/gcc"\ncxx = "/usr/bin/g++"\nlinker = "/usr/bin/gcc"\n')
# The host's tools by role, and the tools that config names by path: the same files.
ROLE_TOOLS = {"cc": {"path": "/usr/bin/cc", "real": "/usr/bin/gcc-13", "sha256": "c" * 64, "version": "cc 1"},
              "c++": {"path": "/usr/bin/c++", "real": "/usr/bin/g++-13", "sha256": "d" * 64, "version": "c++ 1"},
              "ld": {"path": "/usr/bin/ld", "real": "/usr/bin/ld.bfd", "sha256": "e" * 64, "version": "ld 1"},
              "make": {"path": "/usr/bin/make", "real": "/usr/bin/make", "sha256": "9" * 64, "version": "GNU Make 4.3"},
              "python": {"path": "/usr/bin/python3", "real": "/usr/bin/python3.12", "sha256": "b" * 64,
                         "version": "3.12.3"}}
# The python `seed_staircase.py run` starts x.py and the make adapter with, as the fake
# run records it, and the adapter it writes for the make ROLE_TOOLS binds.
RUN_PYTHON = "/usr/bin/python3.12"


def make_adapter(ledger: Path, make: dict = ROLE_TOOLS["make"]) -> dict:
    text = driver.staircase().make_adapter_text(RUN_PYTHON, make["path"])
    return {"path": str(ledger / "pathbin" / "make"), "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "make": make["path"], "make_sha256": make["sha256"]}


CONFIG_TOOLS = {"/usr/bin/gcc": {"path": "/usr/bin/gcc", "real": "/usr/bin/gcc-13", "sha256": "c" * 64,
                                 "version": "gcc 1"},
                "/usr/bin/g++": {"path": "/usr/bin/g++", "real": "/usr/bin/g++-13", "sha256": "d" * 64,
                                 "version": "g++ 1"},
                "/usr/bin/python3": {"path": "/usr/bin/python3", "real": "/usr/bin/python3.12", "sha256": "b" * 64,
                                     "version": "Python 3.12.3"}}

PRELUDE = ("import hashlib, json, os, pathlib, sys\n"
           "with open(os.environ['FAKE_CALLS'], 'a') as log:\n    log.write(sys.argv[1] + '\\n')\n"
           "sha = lambda path: hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()\n")

# `seed_staircase.py run`, as far as the driver can tell: it is given the real
# command line, does what x.py would leave behind, and prints the record.
FAKE_RUN = r'''
import hashlib, json, os, pathlib, sys
behaviour, argv = json.loads(sys.argv[1]), sys.argv[2:]
assert argv[0] == "run", argv
option = lambda name: argv[argv.index(name) + 1]
label, ledger, worktree = option("--label"), pathlib.Path(option("--ledger")), pathlib.Path(option("--worktree"))
xpy = argv[argv.index("--") + 1:]
with open(behaviour["calls"], "a") as log:
    log.write("run " + label + " " + " ".join(xpy[2:]) + "\n")
sha = lambda path: hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
fifo = ledger / "tmp" / "jobserver.fifo"
if "--fifo-jobserver" in argv[:argv.index("--")] and (fifo.exists() or fifo.is_symlink()):
    # As the real preflight: a FIFO a killed run left is never removed here.
    behaviour["refused"] = f"--fifo-jobserver: {fifo} is already there. Nothing was started"
if behaviour.get("refused"):
    print(json.dumps({"schema": "trust-seed-staircase-v1", "refused": behaviour["refused"]}))
    sys.exit(1)
host = worktree / "build" / behaviour["host"]
def put(path, data, mode=0o644):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data.encode("latin-1"))
    path.chmod(mode)
(ledger / "logs").mkdir(exist_ok=True)
(ledger / "logs" / (label + ".log")).write_text("fake x.py\n")
words = xpy[2:]
if words[0] == "dist":
    for name, size in behaviour["archives"].items():
        if isinstance(size, str):       # a real archive to ship, by path
            (worktree / "build" / "dist").mkdir(parents=True, exist_ok=True)
            (worktree / "build" / "dist" / name).write_bytes(pathlib.Path(size).read_bytes())
        else:
            put(worktree / "build" / "dist" / name, "x" * size)
elif "src/tools/build-manifest" in words:
    put(host / "stage3-tools-bin" / behaviour["host"] / "build-manifest", behaviour["tool"], 0o755)
else:
    for name, data in behaviour["native"].items():
        if not (host / name).exists():
            put(host / name, data)
    for name, data in behaviour["stage2"].items():
        put(host / "stage2" / name, data, 0o755)
for name, data in behaviour.get("also", {}).items():
    put(worktree / name, data)
for line in behaviour.get("trap", []):
    with open(ledger / "trap.log", "a") as log:
        log.write(line + "\n")
environment = {"HOME": os.environ["HOME"], "USER": os.environ["USER"], "LOGNAME": os.environ["LOGNAME"],
               "CARGO_HOME": str(ledger / "cargo-home"), "TMPDIR": str(ledger / "tmp"),
               "PATH": ":".join([str(ledger / "trap"), "/usr/bin", "/bin", option("--tool-dir")]),
               "TRUST_STAIRCASE_RUNG": label}
if "SSH_AUTH_SOCK" in os.environ:
    environment["SSH_AUTH_SOCK"] = os.environ["SSH_AUTH_SOCK"]
if "--offline" in argv[:argv.index("--")]:
    environment["CARGO_NET_OFFLINE"] = "true"
library = option("--clean-lean-lib")
environment.update({"CLEAN_OLEAN_PINNED_LEAN_LIB": library, "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"})
jobserver = None
if "--fifo-jobserver" in argv[:argv.index("--")]:
    # What run --fifo-jobserver hands x.py and records: the rung config's job count,
    # the FIFO at the ledger's one path, and every token back at the end.
    import re
    jobs = int(re.search(r"(?m)^jobs = ([0-9]+)$", pathlib.Path(xpy[1]).read_text()).group(1))
    path = behaviour["jobserver_path"]
    environment["MAKEFLAGS"] = f"-j{jobs} --jobserver-auth=fifo:{path}"
    jobserver = {"kind": "fifo", "path": path, "jobs": jobs, "jobs_from": "[build] jobs of " + xpy[1],
                 "tokens": jobs - 1, "tokens_at_end": jobs - 1, "path_unchanged": True,
                 "make_adapter": {**behaviour["make_adapter"], **behaviour.get("make_adapter_change", {})},
                 **behaviour.get("jobserver", {})}
    for key in behaviour.get("jobserver_drop", []):
        jobserver.pop(key)
digest = {"manifest_sha256": sha(behaviour["lean_manifest"])}
record = {"schema": "trust-seed-staircase-v1", "kind": "rung", "label": label, "worktree": str(worktree),
          "commit": behaviour["commit"], "argv": ["x.py", *xpy], "rc": 0, "no_stock_evidence": True,
          "elapsed_s": 1, "python": behaviour["python"], "environment": environment,
          "clean_lean": {"library": library, "before": digest, "after": digest, "unchanged": True},
          "config_tools": {"config_sha256": sha(xpy[1])}, "stage0_admission": option("--stage0-admission"),
          "tool": {"path": behaviour["tool_path"]}, "start": "2026-11-12T10:00:00+0000",
          "end": "2026-11-12T10:00:01+0000"}
if jobserver is not None:
    record["jobserver"] = jobserver
if behaviour.get("complete"):
    # What seed_staircase.py run records besides, as `record`'s validator reads it.
    admitted = json.loads(pathlib.Path(option("--stage0-admission")).read_text())
    def identity(top):
        found = {rel: sha(top / rel) for rel in ("bin/trustc", "bin/cargo", "bin/targo", "bin/trustdoc",
                                                 "bin/trustfmt") if (top / rel).is_file()}
        for pattern in ("lib/librustc_driver-*", "lib/libstd-*"):
            found.update({str(path.relative_to(top)): sha(path) for path in sorted(top.glob(pattern)) if path.is_file()})
        return found
    record.update({"trap_hits": [], "stage0_commit": admitted.get("commit"), "stage0_sha256": admitted.get("sha256"),
                   "process_census": {"kind": "process-census", "flagged": [], "ended": "watched-exited",
                                      "max_gap_s": 1.0, "abandoned_children": 0},
                   "build_census": {"kind": "build-census", "clean": True, "rustc_info_files": 3},
                   "stage0_matches_admission": True, "stage0_runtime_unchanged": True, "tool_dirs_unchanged": True,
                   "tool": {"path": behaviour["tool_path"], "sha256": "7" * 64, "checkout_head": "7" * 40,
                            "modified_in_checkout": False}})
    record["config_tools"]["matches_admission"] = True
    stage0 = pathlib.Path(admitted["stage0"])
    record["config_tools"]["tools"] = {
        key: {"kind": "elf", "named": str(stage0 / "bin" / name), "real": str(stage0 / "bin" / name),
              "sha256": sha(stage0 / "bin" / name)}
        for key, name in (("rustc", "trustc"), ("cargo", "cargo"), ("rustdoc", "trustdoc"), ("rustfmt", "trustfmt"))}
    record["stage0_observed"] = {"root": str(stage0), "sha256": identity(stage0)}
    tool_dir = pathlib.Path(option("--tool-dir"))
    record["tool_dirs"] = [{"dir": str(tool_dir), "entries": [
        {"name": entry.name, "path": str(entry), "real": str(entry), "sha256": sha(entry)}
        for entry in sorted(tool_dir.iterdir())]}]
    if (host / "stage2").is_dir():
        record["produced"] = {"stage2": str(host / "stage2"), "sha256": identity(host / "stage2")}
record.update(behaviour.get("record", {}))
record["environment"].update(behaviour.get("environment", {}))
if behaviour.get("exit"):
    record["rc"] = behaviour["exit"]
print(json.dumps(record))
sys.exit(1 if behaviour.get("exit") else 0)
'''


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), "-c", "protocol.file.allow=always", *args],
                          check=True, capture_output=True, text=True, env=GIT_ENV).stdout.strip()


def put(path: Path, text: str, mode: int = 0o644) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    path.chmod(mode)
    return path


def compiler(top: Path, name: str, *, lld: bool = False) -> Path:
    """A stand-in stage0: a `bin/trustc` whose bytes are its name."""
    put(top / "bin" / "trustc", f"trustc built at {name}\n", 0o755)
    put(top / "bin" / "cargo", "cargo\n", 0o755)
    put(top / "commit", f"{name * 40}"[:40] + "\n")
    if lld:
        put(top / "lib" / "rustlib" / HOST / "bin" / "rust-lld", "lld\n", 0o755)
        put(top / "lib" / "rustlib" / HOST / "bin" / "gcc-ld" / "ld.lld", "ld\n", 0o755)
    return top


class Source:
    """What setup copies from: a checkout with a submodule, a cargo home, a ninja
    behind a link, an installed Lean toolchain, and three compilers."""

    def __init__(self, base: Path):
        self.base = base
        donor = base / "donor"
        donor.mkdir(parents=True)
        git(donor, "init", "-q", "-b", "main")
        put(donor / "f.txt", "one\n")
        git(donor, "add", "-A")
        git(donor, "commit", "-qm", "one")
        upstream = base / "upstream"
        upstream.mkdir()
        git(upstream, "init", "-q", "-b", "main")
        put(upstream / ".gitignore", "bootstrap.toml\nbuild/\n__pycache__/\n.trust-build-lock*\nstray.txt\n")
        put(upstream / "x.py", "print('x.py of the commit')\n")
        put(upstream / "first-party" / "clean" / "lean-toolchain", LEAN_PIN + "\n")
        git(upstream, "add", "-A")
        git(upstream, "commit", "-qm", "tree")
        git(upstream, "submodule", "-q", "add", str(donor), "first-party/a")
        git(upstream, "commit", "-qm", "add a")
        self.repo = base / "source"
        git(base, "clone", "-q", "--recurse-submodules", str(upstream), str(self.repo))
        self.commit = git(self.repo, "rev-parse", "HEAD")
        self.cargo_home = base / "cargo-home"
        put(self.cargo_home / "registry" / "index" / "i" / "config.json", "{}\n")
        put(self.cargo_home / "registry" / "cache" / "i" / "a-1.0.0.crate", "crate\n")
        put(self.cargo_home / "git" / "db" / "r" / "HEAD", "ref: refs/heads/main\n")
        put(self.cargo_home / "bin" / "cargo", "a rustup proxy\n", 0o755)
        put(self.cargo_home / "config.toml", "[build]\nrustc = 'stock'\n")
        real = put(base / "bin" / "ninja", "#!/bin/sh\necho ninja\n", 0o755)
        self.ninja = base / "links" / "ninja"
        self.ninja.parent.mkdir()
        self.ninja.symlink_to(real)
        self.elan = base / "elan"
        put(self.elan / "toolchains" / LEAN_DIRECTORY / "lib" / "lean" / "Init" / "Prelude.olean", "olean\n")
        self.six = compiler(base / "compilers" / "six", "6")
        self.nine = compiler(base / "compilers" / "nine", "9")
        self.pinned = compiler(base / "compilers" / "pinned", "8")
        self.with_lld = compiler(base / "compilers" / "with-lld", "7", lld=True)


SOURCE: Source
_TMP: tempfile.TemporaryDirectory


def setUpModule() -> None:
    global SOURCE, _TMP
    _TMP = tempfile.TemporaryDirectory()
    SOURCE = Source(Path(_TMP.name).resolve())


def tearDownModule() -> None:
    _TMP.cleanup()


def snapshot(top: Path) -> dict[str, str]:
    """Every file under `top` with its bytes' digest (or its link target)."""
    found = {}
    for directory, _, filenames in os.walk(top):
        for name in filenames:
            path = Path(directory) / name
            found[str(path.relative_to(top))] = (os.readlink(path) if path.is_symlink()
                                                 else hashlib.sha256(path.read_bytes()).hexdigest())
    return found


def arguments(root: Path, **changes) -> argparse.Namespace:
    base = dict(command="setup", root=root, commit=SOURCE.commit, host=HOST, repo=SOURCE.repo,
                cargo_home=SOURCE.cargo_home, ninja=SOURCE.ninja, lean_toolchain=None, elan_home=SOURCE.elan,
                jobs=3, lld=False, role=None, stage0=None, again=False,
                asset_limit_bytes=driver.ASSET_LIMIT_BYTES, producer_stage0=SOURCE.six,
                cross_check_stage0=SOURCE.nine, parent="HEAD", cohort=Path("/nonexistent/cohort"), archive_jobs=2)
    base.update(changes)
    return argparse.Namespace(**base)


class FakePlan(driver.Plan):
    """A plan whose staircase and checkout commands are small scripts, so the
    control flow, the copies, the measurements and mint_seed_support.py run for real."""

    def __init__(self, args, host=HOST, commit=None, account=None, driver_dir=None):
        super().__init__(args, host, commit or args.commit, NOBODY if account is None else account,
                         NEUTRAL_DRIVER if driver_dir is None else driver_dir)
        self.calls = self.root.parent / (self.root.name + ".calls")
        self.behaviour: dict[str, dict] = {}        # per label: what the fake x.py does differently
        self.stage2_for: dict[str, dict] = {}       # per label: another stage2
        self.archives = dict(ARCHIVES)
        self.components = "trustc trust-src"
        self.alive: list[str] = []
        # prepare: the parent's src/stage0 and channel manifest, by path (PrepareTests).
        self.parent_files: dict[str, bytes] = {}
        self.fail: set[str] = set()                 # commands that exit 1 with a reason
        self.validate_seed_then = ""                # code the validate-seed stand-in runs last
        # The checkout's closure check: sys.argv[2] is the checkout, sys.argv[3] the trap log.
        self.closure_body = "print('the closure is ready, offline')\n"
        # The host's tools by role, and what measuring a path the base config names gives.
        self.host_tools_now = {name: dict(row) for name, row in ROLE_TOOLS.items()}
        self.tool_rows = {path: dict(row) for path, row in CONFIG_TOOLS.items()}

    def env(self):
        return {**super().env(), "FAKE_CALLS": str(self.calls)}

    def log(self) -> list[str]:
        return self.calls.read_text().splitlines() if self.calls.is_file() else []

    def script(self, name: str, body: str, *args: str) -> list[str]:
        if name in self.fail:
            body = "print('error: the stand-in was told to fail', file=sys.stderr); sys.exit(1)"
        return [sys.executable, "-c", PRELUDE + body, name, *args]

    def seed_config(self):
        return self.script("seed-config", (
            "config = pathlib.Path(sys.argv[2]) / 'bootstrap.toml'\n"
            f"config.write_text({BASE_CONFIG!r})\n"
            "print(json.dumps({'kind': 'seed-config', 'config': str(config), 'sha256': sha(config)}))\n"),
            str(self.src))

    def lean_inputs(self, out):
        return self.script("clean-lean-inputs", (
            "out, library = pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[3])\n"
            "assert not out.exists(), out\n"
            "out.write_text(json.dumps({'fingerprint': 'f' * 64, 'prelude': sha(library / 'Init/Prelude.olean'),\n"
            "    'installation_entries': [{'path': 'lib/lean/Init/Prelude.olean', 'kind': 'file'}],\n"
            "    'environment': {'CLEAN_OLEAN_PINNED_LEAN_LIB': str(library),\n"
            "                    'CLEAN_OLEAN_REQUIRE_PINNED_LEAN': '1'}}))\n"),
            str(out), str(self.lean_library))

    def lean_verify(self, manifest, digest):
        return self.script("verify-clean-lean-inputs", (
            "manifest, library = pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[4])\n"
            "if sha(manifest) != sys.argv[3]:\n"
            "    print('error: Clean Lean input manifest bytes changed', file=sys.stderr); sys.exit(1)\n"
            "if json.loads(manifest.read_text())['prelude'] != sha(library / 'Init/Prelude.olean'):\n"
            "    print('error: Clean Lean installation or source Oracle changed during the workflow',\n"
            "          file=sys.stderr)\n"
            "    sys.exit(1)\n"), str(manifest), digest, str(self.lean_library))

    def cargo_home_inputs(self, source, destination, out):
        if "cargo-home-inputs" in self.fail:
            return self.script("cargo-home-inputs", "")
        return super().cargo_home_inputs(source, destination, out)

    def admit(self):
        return self.script("admit", (
            "stage0 = pathlib.Path(sys.argv[2])\n"
            "if (stage0 / 'refuse').exists():\n"
            "    print(json.dumps({'kind': 'stage0-admission',\n"
            "                      'refusals': [(stage0 / 'refuse').read_text().strip()]}))\n"
            "    sys.exit(1)\n"
            "print(json.dumps({'kind': 'stage0-admission', 'stage0': str(stage0),\n"
            "                  'commit': (stage0 / 'commit').read_text().strip(),\n"
            "                  'sha256': {'bin/trustc': sha(stage0 / 'bin/trustc')}}))\n"), str(self.stage0))

    def config(self, out):
        return self.script("config", (
            "pathlib.Path(sys.argv[2]).write_text('include = [\"' + sys.argv[3] + '\"]\\n\\n[build]\\n'\n"
            "    'rustc = \"' + sys.argv[4] + '/bin/trustc\"\\n')\nprint('{}')\n"),
            str(out), str(self.src / "bootstrap.toml"), str(self.stage0))

    def closure(self):
        return self.script("closure", self.closure_body, str(self.src), str(self.ledger / "trap.log"))

    def run(self, label, words, admission):
        real = super().run(label, words, admission)
        behaviour = {"calls": str(self.calls), "host": self.host, "commit": self.commit, "native": NATIVE,
                     "stage2": self.stage2_for.get(label, STAGE2), "archives": self.archives, "tool": TOOL,
                     "lean_manifest": str(self.inputs / "clean-lean-inputs.json"),
                     "tool_path": str(self.driver / "seed_staircase.py"),
                     "jobserver_path": str(self.ledger / "tmp" / "jobserver.fifo"), "python": RUN_PYTHON,
                     "make_adapter": make_adapter(self.ledger), **self.behaviour.get(label, {})}
        return [sys.executable, "-c", FAKE_RUN, json.dumps(behaviour), *real[3:]]

    def dist_components(self):
        return self.script("dist-components", f"print({self.components!r})\n")

    def commit_date(self):
        return "2026-11-07"

    def role_tools(self):
        return self.host_tools_now

    def host_tool(self, path):
        # The base config's tools are found by the real walk (Plan.config_tools); only
        # measuring one is replaced.
        return self.tool_rows.get(path)

    def live(self):
        return self.alive

    # prepare: the real helpers, each first named in the calls log; validate-seed, which
    # runs the seed's own tools, and the version reader are stand-ins.
    def logged(self, name: str, command: list[str]) -> list[str]:
        if name in self.fail:
            return self.script(name, "")
        return [sys.executable, "-c", PRELUDE + "os.execv(sys.argv[2], sys.argv[2:])\n", name, *command]

    def version(self):
        return self.script("version", "print('0.13.0')\n")

    def stage_artifacts(self, dist, work, version):
        return self.logged("stage-artifacts", super().stage_artifacts(dist, work, version))

    def install(self, installer):
        return self.logged("install", super().install(installer))

    def validate_seed(self, version, out):
        # The tree it saw, as the real one writes it (mint_seed_support.validate_seed's "tree").
        return self.script("validate-seed", (
            "import importlib.util\n"
            "sys.dont_write_bytecode = True  # nothing written beside the checkout's scripts\n"
            "spec = importlib.util.spec_from_file_location('mint_seed_support_stand_in', sys.argv[5])\n"
            "mint = importlib.util.module_from_spec(spec)\n"
            "sys.modules[spec.name] = mint\n"
            "spec.loader.exec_module(mint)\n"
            "pathlib.Path(sys.argv[2]).write_text(json.dumps({'schema': 'trust-self-host-seed-surface-v1',\n"
            "    'version': sys.argv[3], 'seed': sys.argv[4],\n"
            "    'tree': mint.seed_tree_fingerprint(pathlib.Path(sys.argv[4]))}))\n") + self.validate_seed_then,
            str(out), version, str(self.seed), str(driver.MINT_SUPPORT))

    def carried(self):
        return self.logged("verify-archives-carry-compared", super().carried())

    def handoff(self, admitted, work, output_root):
        return self.logged("rustc-dev-handoff", super().handoff(admitted, work, output_root))

    def prepare_py(self, input_dist, output_root, stage0_output, date, server):
        return self.logged("prepare.py", super().prepare_py(input_dist, output_root, stage0_output, date, server))

    def parent_commit(self):
        return PARENT_COMMIT

    def parent_file(self, commit, path):
        if path not in self.parent_files:
            raise driver.Refusal(f"{path} cannot be read at the parent {commit[:10]}: no such file (fixture)")
        return self.parent_files[path]


class RootCase(unittest.TestCase):
    """A fresh root beside the module's sources, and the steps as the driver runs them."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve() / "root"
        patcher = mock.patch.dict(os.environ, GIT_ENV)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.plan = FakePlan(arguments(self.root))
        self.said: list[str] = []

    def quiet(self, call, *args):
        """Run a step, keeping what it printed."""
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            try:
                return call(*args)
            finally:
                self.said += out.getvalue().splitlines()

    def setup_root(self) -> int:
        self.root.mkdir(parents=True, exist_ok=True)
        return self.quiet(driver.setup, self.plan)

    def build(self, role: str, stage0: Path | None = None, again: bool = False) -> int:
        self.plan.args.role, self.plan.args.again = role, again
        self.plan.args.stage0 = stage0 if stage0 is not None else {
            "producer": SOURCE.six, "cross-check": SOURCE.nine}.get(role)
        return self.quiet(driver.build, self.plan, role)

    def dist(self, again: bool = False) -> int:
        self.plan.args.again = again
        return self.quiet(driver.dist, self.plan)

    def install_seed(self, source: Path | None = None) -> None:
        """What `prepare` leaves for the roles that build from the seed: the pinned
        archives as installed, and its record of that tree (PrepareTests run the
        real step)."""
        if self.plan.seed.exists():
            shutil.rmtree(self.plan.seed)
        shutil.copytree(source or SOURCE.pinned, self.plan.seed)
        driver.write_json(self.plan.prepare_record(), {
            "schema": driver.PREPARE_SCHEMA, "commit": self.plan.commit, "host": self.plan.host,
            "root": str(self.plan.root), "seed": {"tree": driver.tree_identity(self.plan.seed, "the seed")},
            "prepared": {"rows": {"kept": 9, "added": ["eight rows"] * 8}}, "members": {"counts": {"same": 0}}})

    def through_dist(self) -> None:
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer"), 0)
        self.assertEqual(self.dist(), 0)

    def kept(self, name: str) -> dict:
        return json.loads((self.plan.kept / name).read_text())

    def refused(self, pattern: str, call, *args, **kwargs) -> str:
        # (?s): a refusal quotes the command that failed, and a stand-in's text has line breaks.
        with self.assertRaisesRegex(driver.Refusal, "(?s)" + pattern) as caught:
            call(*args, **kwargs)
        return str(caught.exception)

    def runs(self) -> list[str]:
        return [line for line in self.plan.log() if line.startswith("run ")]


class HelperTests(unittest.TestCase):
    def test_a_path_that_names_the_account_is_found_by_home_or_by_login(self):
        account = ("/home/somebody", "somebody")
        self.assertEqual(driver.names_account("scripts", account), "/home/somebody")
        self.assertEqual(driver.names_account("/tmp/x-1000/-home-somebody-trust/root", account), "somebody")
        self.assertIsNone(driver.names_account("/var/tmp/trust-seed/82bb867edd", account))
        self.assertIsNone(driver.names_account("/var/tmp/somebodyelse/root", account))
        self.assertIsNone(driver.names_account("/var/tmp/x", ("/", "")))

    def test_the_native_table_holds_elf_and_ar_files_only_and_one_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            host = Path(tmp)
            for name, data in NATIVE.items():
                target = host / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data.encode("latin-1"))
            (host / "stage2").mkdir()
            (host / "stage2" / "trustc").write_bytes(b"\x7fELF not a native output")
            table = driver.native_table(host)
            self.assertEqual([(row["path"], row["kind"]) for row in table["rows"]],
                             [("llvm/bin/llc", "elf"), ("llvm/lib/libLLVM.a", "ar"), ("lld/bin/lld", "elf")])
            self.assertEqual(table["files"], 3)
            again = driver.native_table(host)
            self.assertEqual(again["sha256"], table["sha256"])
            (host / "llvm/bin/llc").write_bytes(b"\x7fELF rebuilt")
            after = driver.native_table(host)
            self.assertNotEqual(after["sha256"], table["sha256"])
            self.assertEqual(driver.native_changes(table, after),
                             {"changed": ["llvm/bin/llc"], "removed": [], "added": []})
            self.assertEqual(driver.native_table(host / "absent"),
                             {"schema": driver.NATIVE_SCHEMA, "files": 0, "sha256": driver.rows_sha256([]), "rows": []})

    def test_a_file_that_is_missing_or_not_json_is_a_refusal_in_words(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(driver.Refusal, "the setup record cannot be read: .*absent.json: No such file"):
                driver.read_json(Path(tmp) / "absent.json", "the setup record")
            (Path(tmp) / "bad.json").write_text("{")
            with self.assertRaisesRegex(driver.Refusal, "is not JSON: .*bad.json"):
                driver.read_json(Path(tmp) / "bad.json", "the setup record")

    def test_a_command_that_fails_is_quoted_by_its_own_reason(self):
        env = dict(os.environ)
        with self.assertRaisesRegex(driver.Refusal, r"doing a thing: `.*` exited 1, and its reason is: no such stage0"):
            driver.captured([sys.executable, "-c", "import json, sys; print(json.dumps({'refused': 'no such stage0'}));"
                             " sys.exit(1)"], "doing a thing", env=env)
        with self.assertRaisesRegex(driver.Refusal, r"exited 3, and the last line it printed on stderr is: error: why"):
            driver.captured([sys.executable, "-c", "import sys; print('error: why', file=sys.stderr); sys.exit(3)"],
                            "doing a thing", env=env)
        with self.assertRaisesRegex(driver.Refusal, "could not be started: No such file or directory"):
            driver.captured(["/nonexistent/program"], "doing a thing", env=env)

    def test_where_the_account_is_named_is_listed_without_spelling_it(self):
        account = ("/home/somebody", "somebody")
        record = {"tool": {"path": "scripts/seed_staircase.py"}, "rc": 0,
                  "environment": {"HOME": "/var/tmp/trust-seed/x/home", "USER": "trust-seed"},
                  "build_census": {"unremapped_std_roots": {"bootstrap/debug/rustc": {
                      "/home/somebody/linux-selfhost-20261106/h-6dad0d786f": 220}}},
                  "process_census": {"executables": [{"exe": "/var/tmp/x"}, {"exe": "/tmp/-home-somebody-x/ninja"}]}}
        found = driver.account_mentions(record, account)
        self.assertEqual(found, ["build_census.unremapped_std_roots.bootstrap/debug/rustc.<key>",
                                 "process_census.executables[].exe", "tool.path"])
        self.assertNotIn("somebody", json.dumps(found))
        self.assertEqual(driver.account_mentions(record, NOBODY), [])
        with tempfile.TemporaryDirectory() as tmp:
            top = Path(tmp)
            (top / "lib" / "rustlib" / "src").mkdir(parents=True)
            (top / "lib" / "rustlib" / "src" / "rust").symlink_to("/home/somebody/h-6dad0d786f")
            (top / "lib" / "here").symlink_to("rustlib")
            self.assertEqual(driver.account_links(top, account), ["lib/rustlib/src/rust"])

    def test_the_closure_checkers_own_reason_is_quoted_and_not_its_prepare_command(self):
        self.assertEqual(driver.closure_reason(CLOSURE_MISSING),
                         ("bootstrap dependency closure REFUSED: required bootstrap authority is missing: "
                          "src/bootstrap/src/core/metadata.rs", False))
        reason, out_of_time = driver.closure_reason(CLOSURE_OUT_OF_TIME)
        self.assertTrue(out_of_time)
        self.assertRegex(reason, r"\Abootstrap dependency closure REFUSED: .*the total budget expired")
        # Without the checker's own line, the last thing it printed.
        self.assertEqual(driver.closure_reason("error: targo could not be started\n"),
                         ("error: targo could not be started", False))

    def test_the_fact_store_is_judged_by_the_compilers_own_rule(self):
        with tempfile.TemporaryDirectory() as tmp:
            top = Path(tmp).resolve() / "root"
            (top / "cargo-home").mkdir(parents=True, mode=0o755)
            top.chmod(0o755)
            real_stat = os.stat

            def private_above(path, *args, **kwargs):
                # Every ancestor above the fixture is this user's and private, whatever the host's /tmp is.
                found = real_stat(path, *args, **kwargs)
                if Path(path) in top.parents:
                    return os.stat_result((0o40755, *tuple(found)[1:4], os.geteuid(), *tuple(found)[5:]))
                return found

            with mock.patch.object(driver.os, "stat", private_above):
                self.assertEqual(driver.fact_store_state(top / "cargo-home"), {"kept": True, "because": None})
                top.chmod(0o775)
                self.assertEqual(driver.fact_store_state(top / "cargo-home"),
                                 {"kept": False, "because": f"{top} is group- or world-writable, or another user's"})
            top.chmod(0o755)
            home = top / "cargo-home"
            home.chmod(0o775)
            self.assertEqual(driver.fact_store_state(home)["because"],
                             f"{home} is group- or world-writable, or another user's")
            # What an earlier step left under trust/ is set aside before every build, so it is not what
            # the compiler sees when the next one starts, and does not move the setting.
            home.chmod(0o755)
            before = driver.fact_store_state(home)
            store = home / "trust" / "results"
            store.mkdir(parents=True)
            store.chmod(0o777)
            self.assertEqual(driver.fact_store_state(home), before)
            # Before setup made the cargo home, the deepest ancestor that exists is judged, through a link.
            (top / "link").symlink_to(home)
            self.assertEqual(driver.fact_store_state(top / "link" / "not-yet"), before)
            self.assertIn("keeps no Clean kernel facts", driver.fact_store_words(
                {"kept": False, "because": f"{home} is group- or world-writable, or another user's"}, home))

    def test_a_helper_that_cannot_start_or_read_refuses_in_words(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            with self.assertRaisesRegex(driver.Refusal, "`/nonexistent/program` could not be started: No such file"):
                driver.run_recorded(["/nonexistent/program"], base / "o.json", base / "o.stderr",
                                    env=dict(os.environ), cwd=base)
            secret = base / "tree" / "d" / "secret"
            secret.parent.mkdir(parents=True)
            secret.write_text("x")
            secret.chmod(0)
            try:
                if os.access(secret, os.R_OK):
                    self.skipTest("this account reads a file of mode 000")
                with self.assertRaisesRegex(driver.Refusal, "a tree could not be measured: .*tree"):
                    driver.tree_identity(base / "tree", "a tree")
            finally:
                secret.chmod(0o644)

    def test_a_stop_request_is_passed_to_the_recorder_and_waited_out(self):
        # The child is seed_staircase.py's shape: on TERM it finishes its record and exits.
        child = ("import signal, sys, time\n"
                 "def stop(*_):\n    print('{\"rc\": -15, \"kind\": \"rung\"}'); sys.stdout.flush(); sys.exit(1)\n"
                 "signal.signal(signal.SIGTERM, stop)\nprint('started', file=sys.stderr); sys.stderr.flush()\n"
                 "time.sleep(30)\n")
        with tempfile.TemporaryDirectory() as tmp:
            out, errors = Path(tmp) / "run.json", Path(tmp) / "run.stderr"

            def ask():
                while not (errors.is_file() and errors.read_text()):
                    time.sleep(0.01)
                os.kill(os.getpid(), signal.SIGTERM)

            before = signal.getsignal(signal.SIGTERM)
            threading.Thread(target=ask, daemon=True).start()
            code, asked = driver.run_recorded([sys.executable, "-c", child], out, errors,
                                              env=dict(os.environ), cwd=Path(tmp))
            self.assertEqual((code, asked), (1, ["SIGTERM"]))
            self.assertIs(signal.getsignal(signal.SIGTERM), before)
            # The record of a run that did not exit 0 is beside the finished name, never under it.
            self.assertFalse(out.exists())
            self.assertEqual(json.loads((Path(tmp) / "run.json.partial").read_text())["rc"], -15)


class CommandLineTests(RootCase):
    def main(self, *argv: str, plan=FakePlan, umask: int | None = None,
             environment: dict[str, str] | None = None) -> tuple[int, str, str]:
        """driver.main as a person starts it: under their umask (or `umask`) and
        environment (plus `environment`); both are given back afterwards."""
        out, err = io.StringIO(), io.StringIO()
        invoker = os.umask(0o022 if umask is None else umask)
        if umask is None:
            os.umask(invoker)
        try:
            with mock.patch.object(driver, "Plan", plan), mock.patch.dict(os.environ, environment or {}), \
                    contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                code = driver.main(list(argv))
        finally:
            os.umask(invoker)
        return code, out.getvalue(), err.getvalue()

    def sources(self) -> list[str]:
        return ["--root", str(self.root), "--commit", SOURCE.commit, "--host", HOST, "--repo", str(SOURCE.repo),
                "--cargo-home", str(SOURCE.cargo_home), "--ninja", str(SOURCE.ninja),
                "--lean-toolchain", str(SOURCE.elan / "toolchains" / LEAN_DIRECTORY), "--jobs", "3"]

    def test_the_half_that_is_not_built_is_absent_from_the_parser(self):
        for argv, said in ((["scout"], "invalid choice"),
                           # commit names its parent, branch, identity and the Darwin pack state (T12), always.
                           (["commit", "--parent", "HEAD", "--branch", "b", "--identity", "A <a@b.c>"],
                            "the following arguments are required: --darwin-pack-state"),
                           (["commit", "--parent", "HEAD", "--branch", "b", "--identity", "A <a@b.c>",
                             "--darwin-pack-state", "unknown"], "invalid choice: 'unknown'"),
                           (["publish", "--clobber"], "unrecognized arguments: --clobber")):
            with self.subTest(argv), contextlib.redirect_stderr(io.StringIO()) as err:
                with self.assertRaises(SystemExit) as caught:
                    driver.parser().parse_args(argv)
                self.assertEqual(caught.exception.code, 2)
                self.assertIn(said, err.getvalue())
        verified = driver.parser().parse_args(["verify"])
        self.assertEqual((verified.rev, verified.rebuild, verified.produced, verified.jobs), ("HEAD", False, None, 20))
        self.assertEqual(driver.parser().parse_args(["publish"]).agh, None)
        self.assertEqual(driver.parser().parse_args(["build", "--role", "control"]).role, "control")
        prepared = driver.parser().parse_args(["prepare"])
        self.assertEqual((prepared.parent, prepared.cohort, prepared.archive_jobs), ("HEAD", driver.COHORT_DIR, 6))
        recorded = driver.parser().parse_args(["record"])
        self.assertEqual((recorded.chain, recorded.origin_provenance, recorded.origin_config),
                         (Path(driver.CHAIN_RECORD), None, Path(driver.ORIGIN_CONFIG)))

    def test_plan_prints_every_step_in_order_and_touches_nothing(self):
        before = snapshot(Path(self.tmp.name))
        code, out, err = self.main("plan", *self.sources(), "--producer-stage0", str(SOURCE.six),
                                   "--cross-check-stage0", str(SOURCE.nine), plan=driver.Plan)
        self.assertEqual((code, err), (0, ""))
        self.assertEqual(snapshot(Path(self.tmp.name)), before)
        self.assertFalse(self.root.exists())
        heads = [line.split("==")[1].strip() for line in out.splitlines() if line.startswith("# == ")]
        self.assertEqual(heads, ["setup", "producer", "dist", "prepare", "fixed-point", "cross-check", "control"])
        lines = out.splitlines()
        labels = [line.split("--label ")[1].split()[0] for line in lines if " run --worktree " in line]
        self.assertEqual(labels, ["p-build", "p-dist", "p-full", "p-manifest-tool", "f-build", "s-build"])
        # Every driver command it prints is one the parser takes.
        for line in lines:
            if line.startswith("# == ") and "fixed_point_linux_seed.py" in line:
                words = line.split("fixed_point_linux_seed.py", 1)[1].split("   ")[0].split()
                self.assertIn(driver.parser().parse_args(words).command, ("setup", "build", "dist", "prepare"))
        self.assertIn("umask 022", lines)
        self.assertIn(f"E='env -i HOME={self.root}/home USER=trust-seed LOGNAME=trust-seed", out)
        self.assertIn("jobs = 3; written once", out)
        self.assertIn(f"the FIFO jobserver every run is given (MAKEFLAGS='-j3 --jobserver-auth=fifo:{self.root}/ledger/"
                      f"tmp/jobserver.fifo', and make through {self.root}/ledger/pathbin/make)", out)
        self.assertIn("record cc, c++, ld, cmake, make, python, the host tools", out)
        self.assertEqual(len([line for line in lines if " run --worktree " in line and "--fifo-jobserver --" in line]),
                         6)
        self.assertIn("the system linker for every role", out)
        self.assertIn(f"producer stage0 {SOURCE.six}: ships no rust-lld", out)
        self.assertIn(f"fixed-point stage0 {self.root}/seed: not there yet", out)

    def test_the_script_started_by_its_path_writes_nothing_beside_itself(self):
        # As the task's own command starts it: `python3 scripts/fixed_point_linux_seed.py plan`, with no -B.
        # A copy, so that what the start leaves beside the script is this start's and nothing else's.
        copy = Path(self.tmp.name).resolve() / "driver" / "scripts"
        copy.mkdir(parents=True)
        for name in driver.DRIVER_SCRIPTS:
            shutil.copy2(driver.HERE / name, copy / name)
        before = snapshot(Path(self.tmp.name))
        environment = {name: value for name, value in os.environ.items()
                       if name not in ("PYTHONDONTWRITEBYTECODE", "PYTHONPYCACHEPREFIX")}
        for words in (["plan", *self.sources(), "--producer-stage0", str(SOURCE.six),
                       "--cross-check-stage0", str(SOURCE.nine)],
                      ["status", "--root", str(self.root), "--commit", SOURCE.commit, "--host", HOST]):
            with self.subTest(words[0]):
                done = subprocess.run([sys.executable, str(copy / "fixed_point_linux_seed.py"), *words],
                                      capture_output=True, text=True, env=environment, timeout=120)
                self.assertEqual((done.returncode, done.stderr), (0, ""), done.stdout)
                self.assertEqual(snapshot(Path(self.tmp.name)), before)
        self.assertIn(f"# == setup ==   python3 {copy}/fixed_point_linux_seed.py setup --root {self.root} "
                      f"--commit {SOURCE.commit}", subprocess.run(
                          [sys.executable, str(copy / "fixed_point_linux_seed.py"), "plan", *self.sources()],
                          capture_output=True, text=True, env=environment, timeout=120).stdout)
        self.assertEqual(snapshot(Path(self.tmp.name)), before)

    def test_the_compared_builds_of_a_plan_differ_only_in_label_and_stage0_source(self):
        plan = FakePlan(arguments(self.root, command="plan"))
        plan.lean_library = plan.inputs / "lean" / LEAN_DIRECTORY / "lib" / "lean"
        first = driver.Plan.run(plan, "p-build", driver.BUILD_LINE, plan.file("p-build", "admission.json"))
        second = driver.Plan.run(plan, "s-build", driver.BUILD_LINE, plan.file("s-build", "admission.json"))
        self.assertEqual([word.replace("s-build", "p-build") for word in second], first)
        self.assertEqual(first[first.index("--") + 1:],
                         ["--config", str(self.root / "ledger" / "rung.bootstrap.toml"),
                          "build", "--stage", "2", "compiler/rustc", "library/std"])
        for option in ("--offline", "--clean-lean-lib", "--tool-dir", "--stage0-admission", "--fifo-jobserver"):
            self.assertIn(option, first[:first.index("--")])
        # Leg 1 of verify --rebuild is given the FIFO jobserver too.
        leg = driver.Plan.run_seed_mode(plan, self.root / "w", self.root / "w" / "ledger", self.root / "a.json",
                                        self.root / "lean", self.root / "tools", 20)
        self.assertIn("--fifo-jobserver", leg[:leg.index("--")])
        self.assertEqual(leg[leg.index("--") + 1:], ["build", "--stage", "2", "-j", "20", "compiler/rustc",
                                                    "library/std"])
        # Every x.py invocation of dist names its stage: a bare `x.py build` is stage 1 here.
        for words in driver.dist_words(["trustc"]).values():
            self.assertEqual(words[1:3], ["--stage", "2"])

    def test_a_refusal_is_one_line_of_words_with_exit_2_and_never_a_traceback(self):
        base = Path(self.tmp.name).resolve()
        (base / "real").mkdir()
        (base / "link").symlink_to("real")
        locked = base / "locked"
        locked.mkdir(mode=0o555)
        locked.chmod(0o555)
        self.addCleanup(locked.chmod, 0o755)
        for argv, pattern in (
                (["status", "--commit", "82bb867edd", "--host", HOST], "not a commit id of 40 hexadecimal digits"),
                (["setup", "--root", str(driver.HERE.parent / "x"), "--host", HOST], "is inside the checkout"),
                (["setup", "--root", str(base / "link" / "root"), "--host", HOST],
                 rf"--root {base}/link/root is reached through a symbolic link: it is {base}/real/root\. .*Nothing "
                 rf"was written\. Give --root {base}/real/root"),
                (["setup", "--root", str(self.root), "--host", HOST, "--jobs", "0"],
                 r"--jobs is 0, and every build needs at least 1\. Nothing was set up\. Give the job count"),
                (["setup", "--root", str(locked / "root"), "--host", HOST, "--repo", str(SOURCE.repo)],
                 rf"the operating system refused a step: Permission denied: {locked}/root\. What was already "
                 "written is kept"),
                (["build", "--role", "producer", "--root", str(self.root), "--host", HOST],
                 r"setup of .* is not done \(.*inputs.json is not there\)\. Nothing was started\. Run: python3 "),
                (["dist", "--root", str(self.root), "--host", HOST], "setup of .* is not done"),
                (["prepare", "--root", str(self.root), "--host", HOST], "setup of .* is not done"),
                (["prepare", "--root", str(self.root), "--host", HOST, "--archive-jobs", "0"],
                 r"--archive-jobs is 0, and prepare.py repacks at least one archive at a time\. Nothing was started")):
            with self.subTest(argv[:3]):
                if "locked" in argv[2] and os.access(locked, os.W_OK):
                    continue        # an account that writes a directory of mode 555
                code, out, err = self.main(*argv)
                self.assertEqual((code, out), (2, ""))
                self.assertRegex(err, r"\Afixed-point-linux-seed: refused: .*" + pattern)
                self.assertNotIn("Traceback", err)
                self.assertEqual(len(err.splitlines()), 1)
        self.assertFalse(self.root.exists())
        self.assertEqual(os.listdir(base / "real"), [])

    def test_the_root_and_every_file_of_a_step_are_not_group_writable_under_the_invokers_umask(self):
        # The account's login shells here start with umask 002.
        code, out, err = self.main("setup", *self.sources(), umask=0o002)
        self.assertEqual((code, err), (0, ""), out)
        for path in (self.root, self.root / "inputs", self.root / "inputs" / "inputs.json",
                     self.root / "inputs" / "sources.json", self.root / "tools" / "ninja"):
            with self.subTest(path.name):
                self.assertEqual(path.stat().st_mode & 0o022, 0, oct(path.stat().st_mode))

    def test_the_invokers_environment_reaches_nothing_the_driver_starts(self):
        self.assertEqual(self.main("setup", *self.sources())[0], 0)
        (self.root / "src" / "untracked.txt").write_text("x")
        # In the invoker's environment git would not list the file; the step environment has no such setting.
        code, out, err = self.main("build", "--role", "producer", "--stage0", str(SOURCE.six), "--root",
                                   str(self.root), "--commit", SOURCE.commit, "--host", HOST,
                                   environment={"GIT_CONFIG_PARAMETERS": "'status.showuntrackedfiles'='no'"})
        self.assertEqual(code, 2, out)
        self.assertRegex(err, r"refused: .*/src is not a clean checkout of [0-9a-f]{10}: .*untracked")
        self.assertFalse((self.root / "kept" / "p-build.attempt.json").exists())

    def test_setup_and_a_build_through_the_command_line_use_only_the_step_environment(self):
        code, out, err = self.main("setup", *self.sources())
        self.assertEqual((code, err), (0, ""))
        self.assertIn("setup: done", out)
        code, out, err = self.main("build", "--role", "producer", "--stage0", str(SOURCE.six),
                                   "--root", str(self.root), "--commit", SOURCE.commit, "--host", HOST)
        self.assertEqual((code, err), (0, ""), out)
        record = json.loads((self.root / "kept" / "p.build.json").read_text())
        self.assertEqual(record["run_environment"]["HOME"], str(self.root / "home"))
        self.assertEqual(record["run_environment"]["USER"], "trust-seed")
        self.assertNotIn("SSH_AUTH_SOCK", record["run_environment"])
        code, out, err = self.main("status", "--root", str(self.root), "--commit", SOURCE.commit, "--host", HOST)
        self.assertEqual(code, 0)
        self.assertIn("producer     clean as p-build", out)
        self.assertRegex(out, r"next: python3 .*fixed_point_linux_seed.py dist --root ")

    def test_a_second_step_under_one_root_is_refused_while_the_first_holds_the_lock(self):
        self.root.mkdir(parents=True)
        with driver.locked(self.plan):
            text = self.refused("another step of this script is running under .*driver.lock: pid ",
                                lambda: driver.locked(self.plan).__enter__())
        self.assertIn("Nothing was started or changed", text)
        with driver.locked(self.plan):
            self.assertRegex((self.root / "driver.lock").read_text(), r"\Apid \d+, started ")
        self.assertEqual((self.root / "driver.lock").read_text(), "")


class SetupTests(RootCase):
    def test_setup_makes_the_root_binds_every_input_and_writes_nowhere_else(self):
        before = snapshot(SOURCE.base)
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(snapshot(SOURCE.base), before)
        self.assertEqual(sorted(path.name for path in Path(self.tmp.name).iterdir()), ["root", "root.calls"])
        inputs = json.loads(self.plan.inputs_file().read_text())
        self.assertEqual((inputs["schema"], inputs["commit"], inputs["host"], inputs["root"]),
                         (driver.INPUTS_SCHEMA, SOURCE.commit, HOST, str(self.root)))
        self.assertEqual((inputs["jobs"], inputs["linker"], inputs["build_line"]),
                         (3, "system", ["build", "--stage", "2", "compiler/rustc", "library/std"]))
        # The checkout: the commit, its submodule at its pin, clean, and its own base config.
        self.assertEqual(driver.refresh.worktree_problems(self.plan.src, SOURCE.commit), [])
        self.assertTrue((self.plan.src / "first-party" / "a" / "f.txt").is_file())
        config = self.plan.src / "bootstrap.toml"
        self.assertEqual(inputs["base_config"], {"path": str(config),
                                                 "sha256": hashlib.sha256(config.read_bytes()).hexdigest()})
        # ninja: the file behind the link, by bytes.
        ninja = self.plan.tools / "ninja"
        self.assertFalse(ninja.is_symlink())
        self.assertEqual(inputs["ninja"]["sha256"], hashlib.sha256(SOURCE.ninja.read_bytes()).hexdigest())
        self.assertEqual(os.listdir(self.plan.tools), ["ninja"])
        # Lean: the copy, bound by the manifest's digest.
        self.assertEqual(inputs["lean"]["library"],
                         str(self.root / "inputs" / "lean" / LEAN_DIRECTORY / "lib" / "lean"))
        manifest = self.root / "inputs" / "clean-lean-inputs.json"
        self.assertEqual(inputs["lean"]["manifest_sha256"], hashlib.sha256(manifest.read_bytes()).hexdigest())
        self.assertEqual((inputs["lean"]["toolchain"], inputs["lean"]["entries"]), (LEAN_PIN, 1))
        bound_lean = json.loads(manifest.read_text())
        self.assertEqual(inputs["lean"]["fingerprint"], bound_lean["fingerprint"])
        self.assertEqual(inputs["lean"]["entries_sha256"], driver.rows_sha256(bound_lean["installation_entries"]))
        self.assertEqual(inputs["ninja"]["bytes"], SOURCE.ninja.stat().st_size)
        # The cargo home: the three trees and nothing else of the source.
        home = self.plan.ledger / "cargo-home"
        self.assertEqual(sorted(str(path.relative_to(home)) for path in home.rglob("*") if path.is_file()),
                         ["git/db/r/HEAD", "registry/cache/i/a-1.0.0.crate", "registry/index/i/config.json"])
        bound = json.loads((self.root / "inputs" / "cargo-home-inputs.json").read_text())
        self.assertEqual(inputs["cargo_home"]["trees"], bound["trees"])
        self.assertEqual(inputs["cargo_home"]["trees"], driver.cargo_home_trees(self.plan))
        self.assertEqual(inputs["cargo_home"]["fingerprint"], bound["fingerprint"])
        self.assertEqual(inputs["environment"], self.plan.env())
        # The roles' tools, and every host tool the base config names by its path.
        self.assertEqual(inputs["host_tools"], {**ROLE_TOOLS, **CONFIG_TOOLS})
        self.assertTrue((self.plan.ledger / "trap" / "rustc").is_file())
        self.assertEqual(driver.entries_of(self.plan.home), [])
        # inputs.json names no source path; sources.json is where those are.
        self.assertNotIn(str(SOURCE.base), self.plan.inputs_file().read_text())
        self.assertEqual(json.loads((self.root / "inputs" / "sources.json").read_text()),
                         driver.setup_sources(self.plan))
        self.assertEqual(inputs["account_named_in"], {})
        self.assertEqual(inputs["clean_fact_store"], driver.fact_store_state(self.plan.ledger / "cargo-home"))
        # The jobserver every x.py run of the root is given, for the job count setup bound.
        fifo = self.plan.ledger / "tmp" / "jobserver.fifo"
        self.assertEqual(inputs["jobserver"], {"kind": "fifo", "path": str(fifo), "jobs": 3, "tokens": 2,
                                               "makeflags": f"-j3 --jobserver-auth=fifo:{fifo}",
                                               "make_adapter": str(self.plan.ledger / "pathbin" / "make")})
        self.assertFalse(fifo.exists())
        # ... and the make its adapter runs, bound with the C toolchain.
        self.assertEqual(inputs["host_tools"]["make"], ROLE_TOOLS["make"])
        self.assertTrue(any(line.startswith("fixed-point-linux-seed: clean fact store: ") for line in self.said))
        self.assertTrue(any("setup: done" in line and "build --role producer" in line for line in self.said))

    def test_where_a_setup_input_names_the_account_is_recorded_without_spelling_it(self):
        # An account whose login is the name of the directory every source is under.
        self.plan = FakePlan(arguments(self.root), account=("/nonexistent/home", SOURCE.base.name))
        self.assertEqual(self.setup_root(), 0)
        inputs = json.loads(self.plan.inputs_file().read_text())
        self.assertEqual(inputs["account_named_in"], {"cargo-home-inputs.json": ["source"],
                                                      "sources.json": ["cargo_home", "elan_home", "ninja", "repo"]})
        self.assertNotIn(SOURCE.base.name, self.plan.inputs_file().read_text())

    @unittest.skipUnless(shutil.which("cc", path="/usr/bin:/bin"), "no cc in /usr/bin:/bin")
    def test_the_host_c_toolchain_is_recorded_by_the_bytes_its_names_resolve_to(self):
        # The real measurement (not FakePlan's), of the roles and of the tools a base config names.
        plan = driver.Plan(arguments(self.root), HOST, SOURCE.commit, NOBODY, NEUTRAL_DRIVER)
        keys = {key: path for key, path in (("python", "/usr/bin/python3"), ("cc", "/usr/bin/gcc"),
                                            ("cxx", "/usr/bin/g++")) if os.path.isfile(path)}
        named = list(keys.values())
        put(plan.src / "bootstrap.toml", 'profile = "compiler"\n\n[target.x]\n'
            + "".join(f'{key} = "{path}"\n' for key, path in keys.items()))
        rows = plan.host_tools()
        self.assertEqual(sorted(rows), sorted(["c++", "cc", "cmake", "ld", "make", "python", *named]))
        # The make setup binds is the make the jobserver's adapter runs (seed_staircase.real_make).
        self.assertEqual((rows["make"] or {}).get("path"), driver.staircase().real_make([]))
        for name, row in rows.items():
            if row is not None:
                with self.subTest(name):
                    self.assertEqual(row["real"], os.path.realpath(row["path"]))
                    self.assertEqual(row["sha256"], hashlib.sha256(Path(row["real"]).read_bytes()).hexdigest())
        for path in named:
            self.assertEqual(rows[path]["path"], path)
        # A path that is no executable file measures as nothing (setup refuses it).
        self.assertIsNone(plan.host_tool(str(self.root / "no-such-tool")))

    def test_a_host_tool_is_an_executable_file_or_nothing(self):
        # The real measurement (not FakePlan's): a file that is there and is not
        # executable, or a directory, measures as nothing, so setup refuses it.
        plan = driver.Plan(arguments(self.root), HOST, SOURCE.commit, NOBODY, NEUTRAL_DRIVER)
        tool = put(self.root / "bin" / "tool", "#!/bin/sh\necho 'tool 1.0'\n", 0o644)
        self.assertIsNone(plan.host_tool(str(tool)))
        self.assertIsNone(plan.host_tool(str(tool.parent)))
        os.chmod(tool, 0o755)
        self.assertEqual(plan.host_tool(str(tool)), {"path": str(tool), "real": str(tool), "sha256": sha(tool),
                                                     "version": "tool 1.0"})

    def test_setup_binds_every_host_tool_the_base_config_names(self):
        self.assertEqual(self.setup_root(), 0)
        tools = json.loads(self.plan.inputs_file().read_text())["host_tools"]
        self.assertEqual(sorted(key for key in tools if key.startswith("/")),
                         ["/usr/bin/g++", "/usr/bin/gcc", "/usr/bin/python3"])
        self.assertEqual({path: tools[path] for path in CONFIG_TOOLS}, CONFIG_TOOLS)
        # A tool the base config names that is not there: nothing is recorded.
        self.plan.inputs_file().unlink()
        del self.plan.tool_rows["/usr/bin/g++"]
        self.refused(r"the base config names /usr/bin/g\+\+, and that is not an executable file here: every host "
                     "tool the base config names is a declared input, bound by its bytes. Nothing was recorded",
                     self.setup_root)
        self.assertFalse(self.plan.inputs_file().exists())

    def test_a_base_config_that_is_not_the_one_seed_config_wrote_is_refused(self):
        self.assertEqual(self.setup_root(), 0)
        self.plan.inputs_file().unlink()
        (self.plan.src / "bootstrap.toml").write_text('profile = "other"\n\n[build]\n')
        self.refused(r"bootstrap.toml is not the file .*seed-config.json records \(sha256 [0-9a-f]{64}\)\. Nothing "
                     "was changed", self.setup_root)
        self.assertFalse(self.plan.inputs_file().exists())

    def test_a_tool_directory_that_holds_more_than_ninja_or_a_checkout_with_no_clean_pin_is_refused(self):
        put(self.root / "tools" / "cmake", "#!/bin/sh\n", 0o755)
        self.refused(r"tools holds more than ninja \(cmake\); it is put on the build's PATH whole\. Nothing was "
                     "changed", self.setup_root)
        self.assertFalse(self.plan.inputs_file().exists())
        (self.plan.src / "first-party" / "clean" / "lean-toolchain").unlink()
        self.refused(r"the Clean pin cannot be read: .*lean-toolchain: No such file", driver.step_lean, self.plan)

    def test_a_second_setup_says_so_and_repeats_nothing(self):
        self.assertEqual(self.setup_root(), 0)
        calls, files = self.plan.log(), snapshot(self.root)
        self.said.clear()
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual((self.plan.log(), snapshot(self.root)), (calls, files))
        self.assertEqual(len(self.said), 1)
        self.assertRegex(self.said[0], "setup: already done .*; not repeated")

    def test_other_arguments_for_a_root_that_is_set_up_are_refused_by_name(self):
        self.assertEqual(self.setup_root(), 0)
        files = snapshot(self.root)
        self.plan.args.jobs = 9
        text = self.refused(r"was started with jobs = 3 \(.*sources.json\), and this command names 9\. That part of "
                            r"setup \(the setup record\) is done with it", self.setup_root)
        self.assertIn("nothing was changed", text)
        self.assertEqual(snapshot(self.root), files)

    def test_an_interrupted_setup_goes_on_where_it_stopped(self):
        self.plan.fail = {"clean-lean-inputs"}
        text = self.refused("the Lean copy .* could not be bound to the Clean pin: .* exited 1, and the last line "
                            "it printed on stderr is: error: the stand-in was told to fail", self.setup_root)
        self.assertNotIn("Traceback", text)
        self.assertFalse(self.plan.inputs_file().exists())
        self.assertEqual(driver.status_lines(self.plan)[1],
                         "  setup        unfinished (there: checkout, base config, ninja)")
        ninja = (self.plan.tools / "ninja").stat().st_ino
        self.plan.fail = set()
        self.assertEqual(self.setup_root(), 0)
        # The parts that were done were not done again.
        self.assertEqual(self.plan.log().count("seed-config"), 1)
        self.assertEqual((self.plan.tools / "ninja").stat().st_ino, ninja)
        self.assertTrue(any("checkout: " in line and "is there and clean" in line for line in self.said))

    def test_an_unfinished_clone_or_cargo_home_copy_is_removed_and_made_anew(self):
        self.root.mkdir(parents=True)
        (self.root / "src.partial" / "half").mkdir(parents=True)
        self.plan.fail = {"cargo-home-inputs"}
        text = self.refused("the cargo home could not be filled from .*The unfinished copy is .*cargo-home.partial; "
                            "the same command line removes it and copies again", self.setup_root)
        self.assertIn("error: the stand-in was told to fail", text)
        self.assertFalse((self.root / "src.partial").exists())
        (self.plan.ledger / "cargo-home.partial" / "junk").mkdir(parents=True)
        self.plan.fail = set()
        self.assertEqual(self.setup_root(), 0)
        self.assertFalse((self.plan.ledger / "cargo-home.partial").exists())
        self.assertFalse((self.plan.ledger / "cargo-home" / "junk").exists())

    def test_a_checkout_that_is_not_clean_is_refused(self):
        self.assertEqual(self.setup_root(), 0)
        self.plan.inputs_file().unlink()
        (self.plan.src / "x.py").write_text("edited\n")
        text = self.refused("is not a clean checkout of .*1 path.s. differ from HEAD", self.setup_root)
        self.assertIn("Nothing was changed", text)

    def test_an_argument_a_part_of_setup_refused_is_corrected_under_the_same_root(self):
        # The refusal names the argument; giving it right then finishes setup in that root, and
        # what was done before the refusal (the clone above all) is not done again.
        plain = Path(self.tmp.name).resolve() / "plain"
        git(Path(self.tmp.name), "clone", "-q", str(SOURCE.repo), str(plain))     # no module store
        for wrong, right, pattern in (
                ({"ninja": SOURCE.base / "no-ninja"}, {}, r"--ninja .*no-ninja is not an executable file .*Nothing "
                                                          "was copied. Name the ninja"),
                ({"elan_home": SOURCE.base / "no-elan"},
                 {"elan_home": SOURCE.base / "no-elan", "lean_toolchain": SOURCE.elan / "toolchains" / LEAN_DIRECTORY},
                 rf"the Lean toolchain {LEAN_PIN}, which .*lean-toolchain names, is not installed at .*no-elan.*"
                 "Name an installed copy with --lean-toolchain"),
                ({"cargo_home": SOURCE.base / "no-cargo-home"}, {}, "the cargo home could not be filled from"),
                ({"jobs": 0}, {}, r"--jobs is 0, and every build needs at least 1\. Nothing was set up\. Give the job "
                                  r"count every role builds with, for example --jobs \d+"),
                ({"repo": plain}, {}, r"the checkout could not be made from .*plain: .*is not a module store: .*Nothing "
                                      r"else was changed, and the unfinished clone .*src.partial is removed by the next "
                                      r"run\. Name with --repo a checkout that holds [0-9a-f]{10} and whose own \.git "
                                      "has a module store for every submodule")):
            with self.subTest(wrong=sorted(wrong)), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp).resolve() / "root"
                plan = FakePlan(arguments(root, **wrong))
                root.mkdir()
                with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(driver.Refusal, f"(?s){pattern}"):
                    driver.setup(plan)
                self.assertFalse(plan.inputs_file().exists())
                cloned = (root / "src" / ".git").exists() and (root / "src" / ".git").stat().st_ino
                plan = FakePlan(arguments(root, **right))
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(driver.setup(plan), 0)
                self.assertEqual(json.loads((root / "inputs" / "sources.json").read_text()), driver.setup_sources(plan))
                if cloned:
                    self.assertEqual((root / "src" / ".git").stat().st_ino, cloned)
        # An argument a done part used is still not changed under it.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve() / "root"
            plan = FakePlan(arguments(root, ninja=SOURCE.base / "no-ninja"))
            root.mkdir()
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaises(driver.Refusal):
                driver.setup(plan)
            plan = FakePlan(arguments(root, repo=plain))
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(
                    driver.Refusal, r"was started with repo = .*source.* \(.*sources.json\), and this command names "
                                    r".*plain.*\. That part of setup \(the checkout\) is done with it"):
                driver.setup(plan)

    def test_a_base_config_the_checkout_refuses_is_quoted(self):
        self.root.mkdir(parents=True)
        with mock.patch.object(FakePlan, "seed_config", lambda plan: [
                sys.executable, "-c", "import json, sys; print(json.dumps({'refused': 'seed-mode config sets "
                "[build] rustc'})); sys.exit(1)"]):
            text = self.refused("the checkout's base config could not be written: .* refused: seed-mode config sets "
                                r"\[build\] rustc", self.setup_root)
        self.assertIn("the same command line runs this step again", text)
        self.assertFalse((self.root / "inputs" / "seed-config.json").exists())


class ProducerTests(RootCase):
    def test_a_clean_producer_build_leaves_what_a_validator_needs_and_is_not_repeated(self):
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer"), 0)
        record = self.kept("p.build.json")
        self.assertEqual((record["role"], record["stem"], record["label"], record["problems"]),
                         ("producer", "p", "p-build", []))
        # The stage0: a copy at the one path, entry for entry.
        self.assertEqual(snapshot(self.plan.stage0), snapshot(SOURCE.six))
        self.assertEqual(record["stage0"]["path"], str(self.root / "stage0"))
        self.assertEqual(record["stage0"]["trustc_sha256"],
                         hashlib.sha256((SOURCE.six / "bin/trustc").read_bytes()).hexdigest())
        self.assertEqual(record["linker"], {"setting": "system", "stage0_ships_self_contained_lld": False})
        # The config: the recreator's, the stage0 keys, the job count, and no linker key.
        config = (self.plan.ledger / "rung.bootstrap.toml").read_text()
        self.assertIn(f'rustc = "{self.root}/stage0/bin/trustc"', config)
        self.assertTrue(config.endswith("jobs = 3\n"))
        self.assertNotIn("lld", config)
        self.assertEqual(record["config"]["sha256"], hashlib.sha256(config.encode()).hexdigest())
        self.assertEqual(record["config"]["base_sha256"], record["shared"]["base_config_sha256"])
        # The run record, the admission and the manifest, each by digest.
        for key, path in (("run", self.plan.ledger / "p-build.run.json"),
                          ("admission", self.plan.ledger / "p-build.admission.json"),
                          ("stage2_manifest", self.plan.kept / "p.stage2.json")):
            self.assertEqual(record[key]["path"], str(path))
            self.assertEqual(record[key]["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        manifest = self.kept("p.stage2.json")
        self.assertEqual(manifest["schema"], "trust-stage2-tree-v1")
        self.assertEqual(record["stage2_manifest"]["tree_sha256"], manifest["sha256"])
        # Native outputs before (none) and after (the producer's LLVM and lld), trap lines, the checkout.
        self.assertEqual((record["native_before"]["files"], record["native_after"]["files"]), (0, 3))
        self.assertEqual(self.kept("p-build.native-after.json")["sha256"], record["native_after"]["sha256"])
        self.assertEqual(record["native_after"]["against_before"]["added"], 3)
        self.assertEqual((record["trap_log_lines_before"], record["trap_log_lines_after"]), (0, 0))
        self.assertEqual(record["worktree"], {"ignored_before": ["bootstrap.toml"],
                                              "ignored_after": ["bootstrap.toml", "build/"], "problems_after": []})
        self.assertEqual(record["cargo_home_after"]["unchanged"], True)
        self.assertEqual(sorted(record["driver"]), sorted(driver.DRIVER_SCRIPTS))
        self.assertEqual(self.kept("current-tree.json"),
                         {"label": "p-build", "stem": "p", "role": "producer", "clean": True})
        self.assertNotIn("comparison", record)
        # x.py was given the compared build line once, and a second command starts nothing.
        self.assertEqual(self.runs(), ["run p-build build --stage 2 compiler/rustc library/std"])
        calls, files = self.plan.log(), snapshot(self.plan.kept)
        self.said.clear()
        self.assertEqual(self.build("producer"), 0)
        self.assertEqual((self.plan.log(), snapshot(self.plan.kept)), (calls, files))
        self.assertRegex(self.said[0], r"producer: already built clean as p-build \(.*p.build.json\); not repeated")

    def test_nothing_starts_from_a_root_that_names_the_account_a_trap_log_or_a_live_build(self):
        self.assertEqual(self.setup_root(), 0)
        cases = []
        login = FakePlan(arguments(self.root), account=("/elsewhere", self.root.name))
        cases.append((login, r"the root, .*, names the invoking account \(root\)\. Every record names the root many "
                             "times .*Nothing was started. Use a root whose path does not name the account, such as "
                             "the default " + re.escape(str(driver.ROOT_PARENT)) + "/"))
        alive = FakePlan(arguments(self.root))
        alive.alive = ["pid 7: python3 seed_staircase.py run"]
        cases.append((alive, "an earlier build under .* is still running .pid 7: .*Nothing was started"))
        for plan, pattern in cases:
            with self.subTest(pattern[:30]):
                plan.args.role, plan.args.stage0 = "producer", SOURCE.six
                with self.assertRaisesRegex(driver.Refusal, pattern):
                    driver.build(plan, "producer")
        (self.plan.ledger / "trap.log").write_text("2026-11-12T10:00:00\t9\trustc\t-vV\tsh\n")
        text = self.refused(r"trap.log has 1 line\(s\): a stock Rust tool name was reached", self.build, "producer")
        self.assertIn("Nothing was started and nothing was removed", text)
        self.assertEqual(self.runs(), [])
        self.assertFalse(self.plan.stage0.exists())
        self.assertFalse(self.plan.build_dir().exists())

    def test_a_driver_that_names_the_account_is_said_and_where_the_evidence_names_it_is_recorded(self):
        # The chain compilers on this host name the account whatever the driver does: their std carries
        # the path they were built in (the census records it) and their rust-src link points into the home.
        account = ("/home/somebody", "somebody")
        self.plan = FakePlan(arguments(self.root), account=account, driver_dir=Path("scripts"))
        self.assertEqual(self.setup_root(), 0)
        chain = compiler(Path(self.tmp.name) / "chain", "6")
        (chain / "lib" / "rustlib" / "src").mkdir(parents=True)
        (chain / "lib" / "rustlib" / "src" / "rust").symlink_to("/home/somebody/linux-selfhost/h-6dad0d786f")
        self.plan.behaviour["p-build"] = {"record": {"build_census": {"unremapped_std_roots": {
            "bootstrap/debug/rustc": {"/home/somebody/linux-selfhost/h-6dad0d786f": 220}}}}}
        self.assertEqual(self.build("producer", chain), 0)
        self.assertTrue(any("note: this script's directory, scripts, names the invoking account "
                            "(/home/somebody): the run records name it (`tool.path`)" in line for line in self.said))
        record = self.kept("p.build.json")
        self.assertEqual(record["account_named_in"], {
            "run_record": ["build_census.unremapped_std_roots.bootstrap/debug/rustc.<key>", "tool.path"],
            "admission": [], "stage0_links": ["lib/rustlib/src/rust"], "stage0_source": False,
            "driver_directory": True})
        self.assertNotIn("somebody", json.dumps(record["account_named_in"]))
        # A driver and a stage0 that name no account: nothing is listed.
        with tempfile.TemporaryDirectory() as tmp:
            self.root = Path(tmp).resolve() / "root"
            self.plan = FakePlan(arguments(self.root))
            self.assertEqual(self.setup_root(), 0)
            self.assertEqual(self.build("producer"), 0)
            self.assertEqual(self.kept("p.build.json")["account_named_in"], {
                "run_record": [], "admission": [], "stage0_links": [], "stage0_source": False,
                "driver_directory": False})

    @unittest.skipUnless(platform.system() == "Linux", "reads /proc")
    def test_a_process_that_carries_a_rungs_environment_is_found_alive(self):
        plan = driver.Plan(arguments(self.root), HOST, SOURCE.commit, NOBODY, NEUTRAL_DRIVER)
        self.assertEqual(plan.live(), [])
        child = subprocess.Popen(["sleep", "30"], env={"CARGO_HOME": str(plan.ledger / "cargo-home"),
                                                       "TRUST_STAIRCASE_RUNG": "p-build", "PATH": "/usr/bin:/bin"})
        try:
            found = plan.live()
            self.assertEqual(len(found), 1)
            self.assertRegex(found[0], rf"pid {child.pid}: sleep 30")
        finally:
            child.kill()
            child.wait()

    def test_a_build_that_did_not_exit_zero_is_kept_said_and_started_again_only_when_asked(self):
        self.assertEqual(self.setup_root(), 0)
        self.plan.behaviour["p-build"] = {"exit": 101, "record": {"no_stock_evidence": True}}
        text = self.refused(r"p-build is not a clean build: seed_staircase.py run exited 1; x.py exited 101\. Kept: "
                            r"its record .*p-build.not-clean.json, the run record .*p-build.run.json .`.partial` "
                            r"when x.py did not exit 0., x.py's output .*logs/p-build.log, the messages "
                            r".*p-build.run.stderr, and the build tree\. To build the producer role again under "
                            "the label p-build-2, give the same command line with --again", self.build, "producer")
        self.assertNotIn("Traceback", text)
        self.assertFalse((self.plan.kept / "p.build.json").exists())
        self.assertFalse((self.plan.ledger / "p-build.run.json").exists())
        self.assertEqual(self.kept("p-build.not-clean.json")["problems"],
                         ["seed_staircase.py run exited 1", "x.py exited 101"])
        self.assertEqual(driver.role_status(self.plan, "p")[0], "not-clean")
        # The same command line is refused and starts nothing.
        text = self.refused(r"p-build ended and was not clean: .*x.py exited 101\. Its record is .*Nothing was "
                            "started. To build the producer role again as p-build-2, give the same command line "
                            "with --again", self.build, "producer")
        self.assertEqual(len(self.runs()), 1)
        # --again: the next label, from an empty build directory; the failed tree is kept.
        self.assertEqual(self.build("producer", again=True), 0)
        self.assertEqual(self.kept("p.build.json")["label"], "p-build-2")
        self.assertTrue((self.plan.kept / "p-build-unfinished" / HOST / "stage2" / "bin" / "trustc").is_file())
        self.assertEqual(self.kept("p.build.json")["native_before"]["files"], 0)
        self.assertEqual([line.split()[1] for line in self.runs()], ["p-build", "p-build-2"])
        self.assertEqual(self.kept("current-tree.json")["label"], "p-build-2")

    def test_a_run_that_starts_no_build_quotes_the_recorders_reason(self):
        self.assertEqual(self.setup_root(), 0)
        self.plan.behaviour["p-build"] = {"refused": "memory gate: 3 GiB available after 60 min (< 24)"}
        self.refused(r"p-build is not a clean build: seed_staircase.py run exited 1; it started no build: memory "
                     r"gate: 3 GiB available after 60 min", self.build, "producer")

    def test_an_interrupted_build_is_followed_by_the_next_label_without_being_asked(self):
        self.assertEqual(self.setup_root(), 0)
        # As if the driver was killed while x.py ran: the build was given its label and left no record.
        with mock.patch.object(driver, "run_label", side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.build("producer")
        self.assertTrue((self.plan.kept / "p-build.attempt.json").is_file())
        self.assertEqual(driver.role_status(self.plan, "p"),
                         ("unfinished", "p-build was started and has left no record yet (running, or interrupted)"))
        (self.plan.build_dir() / HOST / "half-built").write_text("x")
        self.assertEqual(self.build("producer"), 0)
        self.assertEqual(self.kept("p.build.json")["label"], "p-build-2")
        self.assertTrue((self.plan.kept / "p-build-unfinished" / HOST / "half-built").is_file())
        self.assertFalse((self.plan.build_dir() / HOST / "half-built").exists())
        self.assertTrue(any("p-build was started and left no record" in line for line in self.said))

    def test_a_run_that_left_its_record_is_judged_and_not_run_again(self):
        self.assertEqual(self.setup_root(), 0)
        # The driver stops after x.py ended and before its own record: the manifest step fails once.
        with mock.patch.object(FakePlan, "manifest", lambda plan, tree, out: plan.script("manifest", "sys.exit(1)")):
            self.plan.fail = {"manifest"}
            text = self.refused("p-build: no manifest of its stage2 could be written. The build is kept and is not "
                                "built again: the same command line resumes here", self.build, "producer")
        self.assertIn("error: the stand-in was told to fail", text)
        self.plan.fail = set()
        self.assertEqual(driver.role_status(self.plan, "p")[0], "unfinished")
        self.assertEqual(self.build("producer"), 0)
        self.assertEqual(len(self.runs()), 1)
        self.assertEqual(self.kept("p.build.json")["label"], "p-build")
        self.assertTrue(any("resuming at the measurements" in line for line in self.said))

    def test_a_record_that_is_not_the_clean_record_of_this_build_is_named(self):
        cases = (
            ({"record": {"no_stock_evidence": False, "trap_hits": ["x"]}}, "the no-stock evidence is not clean"),
            ({"environment": {"USER": "somebody"}}, "the build's USER was 'somebody', not 'trust-seed'"),
            ({"environment": {"SSH_AUTH_SOCK": "/tmp/agent"}}, "the build was handed an SSH_AUTH_SOCK"),
            ({"environment": {"CARGO_NET_OFFLINE": "false"}}, "the build's CARGO_NET_OFFLINE was 'false'"),
            ({"record": {"clean_lean": {"unchanged": False}}}, "the Lean library changed under the build"),
            ({"record": {"config_tools": {"config_sha256": "0" * 64}}}, "the config x.py read is not "),
            ({"record": {"worktree": "/elsewhere"}}, "the record's worktree is \"/elsewhere\""),
            ({"record": {"argv": ["x.py", "build"]}}, r"the record's argv is \[\"x.py\", \"build\"\], not "),
            ({"record": {"commit": "0" * 40}}, f"the record's commit is \"{'0' * 40}\", not "),
            ({"environment": {"HOME": "/home/somebody"}}, "the build's HOME was '/home/somebody', not '.*/home'"),
            ({"record": {"clean_lean": {"before": {"manifest_sha256": "0" * 64},
                                        "after": {"manifest_sha256": "0" * 64}, "unchanged": True}}},
             "the Lean library the build was given is not the one setup bound"),
            ({"trap": ["a stock rustc was reached"]}, r"the trap log grew by 1 line\(s\)"),
            ({"also": {"stray.txt": "x"}}, "the build left ignored files that are not its own: stray.txt"),
            ({"also": {"x.py": "edited"}}, "the checkout is not clean after the build: 1 path"),
            # The FIFO jobserver (BOOTSTRAP-JOBSERVER-PROBE-1): handed over, and every token back.
            ({"environment": {"MAKEFLAGS": "-j3 --jobserver-auth=3,4"}},
             r"the build's MAKEFLAGS was '-j3 --jobserver-auth=3,4', not '-j3 --jobserver-auth=fifo:.*/ledger/tmp/"
             r"jobserver.fifo'"),
            ({"record": {"jobserver": None}}, "the run record shows no jobserver: x.py was not given the FIFO "
                                              "jobserver every run of this root is given"),
            ({"jobserver": {"kind": "pipe"}}, "its jobserver's kind was 'pipe', not 'fifo'"),
            ({"jobserver": {"jobs": 4}}, "its jobserver's jobs was 4, not 3"),
            ({"jobserver": {"tokens": 1}}, "its jobserver's tokens was 1, not 2"),
            ({"jobserver": {"path": "/tmp/jobserver.fifo"}}, "its jobserver's path was '/tmp/jobserver.fifo', not "),
            ({"jobserver": {"tokens_at_end": 1}}, r"its jobserver held 1 token\(s\) when x.py had exited, not the 2 it "
                                                  "was given: a process ended holding a token, or outlived x.py"),
            ({"jobserver": {"tokens_at_end": 3}}, r"held 3 token\(s\) .*: something wrote a token it never took"),
            ({"jobserver": {"tokens_at_end": None}}, r"held None token\(s\) .*: no count was taken"),
            ({"jobserver": {"tokens_at_end": 2.0}}, r"held 2.0 token\(s\) .*: no count was taken"),
            ({"jobserver": {"path_unchanged": False}}, "its jobserver's path .* did not name the FIFO when x.py had "
                                                       "exited"),
            ({"jobserver": {"path_unchanged": None}}, "its jobserver's path .* did not name the FIFO when x.py had "
                                                      "exited"),
            ({"jobserver_drop": ["path_unchanged"]}, "its jobserver's path .* did not name the FIFO when x.py had "
                                                     "exited"),
            # The make adapter: GNU make before 4.4 reaches the FIFO only through it.
            ({"jobserver_drop": ["make_adapter"]}, r"its jobserver record names no make adapter \(null\): GNU make "
                                                   "before 4.4, which a build step runs, stops on the FIFO's fifo: "
                                                   "spelling unless the adapter hands it over"),
            ({"make_adapter_change": {"path": "/elsewhere/pathbin/make"}},
             r"its make adapter was '/elsewhere/pathbin/make', not '.*/root/ledger/pathbin/make'"),
            ({"make_adapter_change": {"sha256": "0" * 64}},
             r"its make adapter \(sha256 0000000000000000\) is not the one seed_staircase.py writes for "
             r"/usr/bin/python3.12 and /usr/bin/make"),
            ({"make_adapter_change": {"make": "make"}},
             r"its make adapter names the make 'make' and the record the python '/usr/bin/python3.12', not two "
             "absolute paths"),
            ({"record": {"python": None}},
             r"its make adapter names the make '/usr/bin/make' and the record the python None, not two absolute paths"),
            ({"make_adapter_change": {key: value for key, value in make_adapter(
                Path("/x"), {"path": "/usr/local/bin/make", "sha256": "8" * 64}).items() if key != "path"}},
             r"its make adapter ran '/usr/local/bin/make' \(sha256 8888888888888888\), not the make setup bound, "
             r"'/usr/bin/make' \(sha256 9999999999999999\)"),
        )
        for behaviour, pattern in cases:
            with self.subTest(pattern), tempfile.TemporaryDirectory() as tmp:
                self.root = Path(tmp).resolve() / "root"
                self.plan = FakePlan(arguments(self.root))
                self.assertEqual(self.setup_root(), 0)
                self.plan.behaviour["p-build"] = behaviour
                self.refused("p-build is not a clean build: .*" + pattern, self.build, "producer")
                self.assertFalse((self.plan.kept / "p.build.json").exists())
                self.assertFalse((self.plan.kept / "p.stage2.json").exists())
                self.assertTrue((self.plan.kept / "p-build.not-clean.json").is_file())
                self.assertEqual(self.kept("current-tree.json")["clean"], False)

    def test_what_a_step_left_in_home_is_set_aside_so_x_py_starts_with_none(self):
        self.assertEqual(self.setup_root(), 0)
        (self.plan.home / ".cache").mkdir()
        (self.plan.ledger / "tmp" / "left").write_text("x")
        # The compiler's Clean fact store, where the root allows one: no role imports an earlier one's facts.
        put(self.plan.ledger / "cargo-home" / "trust" / "results" / "v1" / "clean-kernel-facts-v1" / "index" / "ab"
            / "key", "fact\n")
        self.plan.behaviour["p-build"] = {"also": {"../home/.written-by-the-build": "x",
                                                   "../ledger/cargo-home/trust/results/v1/new": "fact"}}
        self.assertEqual(self.build("producer"), 0)
        record = self.kept("p.build.json")
        self.assertEqual(record["set_aside_before"]["home"]["entries"], [".cache"])
        self.assertTrue((self.plan.kept / "p-build.home-before" / ".cache").is_dir())
        self.assertTrue((self.plan.kept / "p-build.tmp-before" / "left").is_file())
        self.assertEqual(record["set_aside_before"]["cargo-trust"],
                         {"entries": ["results"], "kept": str(self.plan.kept / "p-build.cargo-trust-before")})
        self.assertTrue((self.plan.kept / "p-build.cargo-trust-before" / "results" / "v1" / "clean-kernel-facts-v1"
                         / "index" / "ab" / "key").is_file())
        self.assertEqual(record["left_after"], {"home": [".written-by-the-build"], "tmp": [], "cargo-trust": ["results"]})
        self.assertEqual(record["shared"]["clean_fact_store"], driver.fact_store_state(self.plan.ledger / "cargo-home"))
        # What this build left is set aside before the next one, and the cargo home's input trees are untouched.
        self.assertEqual(record["cargo_home_after"]["unchanged"], True)

    def test_a_fact_store_setting_that_changed_since_setup_starts_nothing(self):
        # Whether the compiler may keep Clean kernel facts follows the modes of the cargo home and its
        # ancestors; a build must be given the setting setup recorded.
        self.assertEqual(self.setup_root(), 0)
        home = self.plan.ledger / "cargo-home"
        mode = home.stat().st_mode & 0o7777
        home.chmod(0o770)
        try:
            self.assertEqual(driver.fact_store_state(home)["because"],
                             f"{home} is group- or world-writable, or another user's")
            # (The values are quoted shortened, so the pattern does not depend on how long the paths are.)
            text = self.refused(r"p-build would not be given what setup recorded: clean_fact_store is .* now and was "
                                r".* at setup \(.*inputs.json\)\. Nothing was started and nothing was changed",
                                self.build, "producer")
        finally:
            home.chmod(mode)
        self.assertNotIn("Traceback", text)
        self.assertEqual(self.runs(), [])
        self.assertEqual(self.build("producer"), 0)

    def test_a_stage0_that_is_refused_or_missing_starts_nothing(self):
        self.assertEqual(self.setup_root(), 0)
        text = self.refused(r"--stage0 .*absent has no bin/trustc\. Nothing was started", self.build, "producer",
                            SOURCE.base / "absent")
        self.assertFalse(self.plan.stage0.exists())
        refused = compiler(Path(self.tmp.name) / "stock", "5")
        (refused / "refuse").write_text("trustc -vV says `binary: rustc`, not trustc: not a Trust compiler\n")
        text = self.refused(r"seed_staircase.py admit refused the stage0 of p-build \(.*stage0, a copy of .*stock\): "
                            r"trustc -vV says `binary: rustc`, not trustc.*Nothing was built; the copy is kept",
                            self.build, "producer", refused)
        self.assertNotIn("Traceback", text)
        self.assertEqual(self.runs(), [])
        self.assertFalse((self.plan.kept / "p-build.attempt.json").exists())
        # The label was not used: the same role then builds as p-build, from another compiler.
        self.assertEqual(self.build("producer"), 0)
        self.assertEqual(self.kept("p.build.json")["label"], "p-build")
        self.assertEqual(snapshot(self.root / "stage0.p-build"), snapshot(refused))

    def test_a_closure_check_that_refuses_is_quoted_by_its_own_reason_and_starts_nothing(self):
        self.assertEqual(self.setup_root(), 0)
        for printed, pattern, after in (
                (CLOSURE_MISSING, r"the cargo home does not hold this commit's dependency closure for the stage0 of "
                                  r"p-build: `.*` refused: bootstrap dependency closure REFUSED: required bootstrap "
                                  r"authority is missing: src/bootstrap/src/core/metadata.rs \(all it printed: "
                                  r".*p-build.closure.log.partial\)\. Nothing was built and the cargo home is kept\.",
                 "it belongs in a new --root after it is filled"),
                (CLOSURE_OUT_OF_TIME, r"the offline dependency check for the stage0 of p-build did not finish in its "
                                      r"900 s budget: bootstrap dependency closure REFUSED: .*the total budget expired "
                                      r".*Nothing was built, and the cargo home is kept as the check left it",
                 "The same command line runs the check again")):
            with self.subTest(after):
                self.plan.closure_body = (f"sys.stderr.write({printed!r}); sys.exit(1)\n")
                text = self.refused(pattern, self.build, "producer")
                self.assertTrue(text.endswith(after), text)
                # (The stand-in's own command line holds what it prints; the real checker's does not.)
                self.assertNotIn("env -u CARGO_BUILD_WARNINGS", text.rsplit("`", 1)[-1])
                self.assertNotIn("Traceback", text)
                self.assertEqual(self.runs(), [])
                self.assertFalse((self.plan.kept / "p-build.attempt.json").exists())
        # The step is run again under the same label once the check passes.
        self.plan.closure_body = "print('the closure is ready, offline')\n"
        self.assertEqual(self.build("producer"), 0)
        self.assertEqual(self.kept("p.build.json")["label"], "p-build")

    def test_a_closure_check_that_changes_the_checkout_or_reaches_a_stock_name_starts_nothing(self):
        self.assertEqual(self.setup_root(), 0)
        for body, pattern in (
                ("pathlib.Path(sys.argv[2], 'x.py').write_text('edited')\n",
                 r"the dependency check left .*src other than a clean checkout: 1 path.s. differ from HEAD.*Nothing "
                 "was built"),
                ("open(sys.argv[3], 'a').write('rustc -vV\\n')\n",
                 r"a step before x.py reached a stock Rust tool name: .*trap.log has 1 line\(s\), the first 'rustc "
                 r"-vV'\. Nothing was built")):
            with self.subTest(pattern[:30]):
                self.plan.closure_body = body
                self.refused(pattern, self.build, "producer")
                self.assertEqual(self.runs(), [])
                self.assertFalse((self.plan.kept / "p-build.attempt.json").exists())
                git(self.plan.src, "checkout", "--", "x.py")

    def test_a_run_that_ended_while_the_driver_was_away_is_judged_and_not_run_again(self):
        # The driver is killed without passing the stop on (SIGKILL, the out-of-memory killer) while
        # seed_staircase.py run goes on: the run finishes and its record stays under `.partial`.
        real = driver.run_recorded

        def driver_killed(command, out, stderr, **options):
            real(command, out, stderr, **options)
            if out.is_file():
                out.replace(out.with_name(out.name + ".partial"))
            raise KeyboardInterrupt

        for behaviour, outcome in (({}, "clean"), ({"exit": 101}, "not clean")):
            with self.subTest(outcome), tempfile.TemporaryDirectory() as tmp:
                self.root = Path(tmp).resolve() / "root"
                self.plan = FakePlan(arguments(self.root))
                self.assertEqual(self.setup_root(), 0)
                self.plan.behaviour["p-build"] = behaviour
                with mock.patch.object(driver, "run_recorded", driver_killed), self.assertRaises(KeyboardInterrupt):
                    self.build("producer")
                self.assertTrue((self.plan.ledger / "p-build.run.json.partial").is_file())
                if outcome == "clean":
                    self.assertEqual(self.build("producer"), 0)
                    self.assertEqual(self.kept("p.build.json")["label"], "p-build")
                    self.assertTrue(any("p-build: its run ended while this script was not there to read it" in line
                                        for line in self.said))
                else:
                    self.refused(r"p-build ended and was not clean: its run ended while this script was not there "
                                 r"to judge it; x.py exited 101\. .*Nothing was started\. To build the producer role "
                                 "again as p-build-2, give the same command line with --again", self.build, "producer")
                    self.assertFalse((self.plan.kept / "p.build.json").exists())
                self.assertEqual(self.runs(), ["run p-build build --stage 2 compiler/rustc library/std"])
        # A record that is not whole is a run that was interrupted: the next label follows it.
        with tempfile.TemporaryDirectory() as tmp:
            self.root = Path(tmp).resolve() / "root"
            self.plan = FakePlan(arguments(self.root))
            self.assertEqual(self.setup_root(), 0)
            with mock.patch.object(driver, "run_recorded", driver_killed), self.assertRaises(KeyboardInterrupt):
                self.build("producer")
            partial = self.plan.ledger / "p-build.run.json.partial"
            partial.write_text(partial.read_text()[:40])
            self.assertEqual(self.build("producer"), 0)
            self.assertEqual(self.kept("p.build.json")["label"], "p-build-2")

    def test_a_stop_after_the_stage0_copy_is_in_place_is_resumed_by_the_same_command(self):
        self.assertEqual(self.setup_root(), 0)
        real = driver.tree_identity

        def stopped(top, what):
            if what == "the installed stage0":
                raise KeyboardInterrupt
            return real(top, what)

        with mock.patch.object(driver, "tree_identity", stopped), self.assertRaises(KeyboardInterrupt):
            self.build("producer")
        self.assertTrue(self.plan.stage0.is_dir())
        self.assertFalse((self.root / "stage0.json").exists())
        inode = self.plan.stage0.stat().st_ino
        self.assertEqual(self.build("producer"), 0)
        self.assertEqual(self.plan.stage0.stat().st_ino, inode)       # measured again, not copied again
        self.assertEqual(json.loads((self.root / "stage0.json").read_text())["source"], str(SOURCE.six))
        # A tree there that is not a copy of the compiler named is not taken for one.
        with tempfile.TemporaryDirectory() as tmp:
            self.root = Path(tmp).resolve() / "root"
            self.plan = FakePlan(arguments(self.root))
            self.assertEqual(self.setup_root(), 0)
            shutil.copytree(SOURCE.nine, self.plan.stage0, symlinks=True)
            self.refused(r"stage0 exists, .*stage0.json does not say what it is a copy of, and it is not a copy of "
                         r".*six entry for entry\. Nothing was changed", self.build, "producer")
            self.assertEqual(snapshot(self.plan.stage0), snapshot(SOURCE.nine))

    def test_a_stage0_copy_or_build_that_does_not_keep_the_stage0_whole_is_not_used(self):
        self.assertEqual(self.setup_root(), 0)
        real = driver.refresh.copy_tree

        def lossy(source, target):
            real(source, target)
            if target.name == "stage0":
                (target / "commit").unlink()

        with mock.patch.object(driver.refresh, "copy_tree", lossy):
            self.refused(r"the copy of .*six is not that tree entry for entry .*set aside as .*stage0.partial and the "
                         "next run copies again", self.build, "producer")
        self.assertEqual(self.runs(), [])
        self.plan.behaviour["p-build"] = {"also": {"../stage0/bin/trustc": "changed by the build"}}
        self.refused(r"p-build is not a clean build: .*stage0 is not the tree the build was started from",
                     self.build, "producer")
        self.plan.behaviour["p-build"] = {}
        self.plan.stage2_for["p-build-2"] = {}
        text = self.refused(r"p-build-2 is not a clean build: x.py exited 0 and left no .*/stage2\.", self.build,
                            "producer", None, True)
        self.assertNotIn("Traceback", text)
        self.assertFalse((self.plan.kept / "p.build.json").exists())

    def test_the_self_contained_linker_is_for_every_role_or_for_none(self):
        self.plan = FakePlan(arguments(self.root, lld=True))
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(json.loads(self.plan.inputs_file().read_text())["linker"], "self-contained")
        text = self.refused(r"setup chose the self-contained linker \(--lld\) for every role, and the stage0 of "
                            r"p-build ships none: no .*rust-lld, .*gcc-ld/ld.lld\. The roles cannot differ in their "
                            "linker, so nothing was started", self.build, "producer")
        self.assertIn("Set up a new --root without --lld", text)
        self.assertEqual(self.runs(), [])
        self.assertEqual(self.build("producer", SOURCE.with_lld), 0)
        record = self.kept("p.build.json")
        self.assertEqual(record["linker"], {"setting": "self-contained", "stage0_ships_self_contained_lld": True})
        self.assertIn('bootstrap-override-lld = "self-contained"',
                      (self.plan.ledger / "rung.bootstrap.toml").read_text())


class DistTests(RootCase):
    def test_dist_runs_in_the_producers_tree_in_the_mints_order_and_is_not_repeated(self):
        self.assertEqual(self.setup_root(), 0)
        self.refused(r"dist packages the producer's build, and there is no clean one yet .*Run: python3 .* build "
                     "--role producer", self.dist)
        self.assertEqual(self.build("producer"), 0)
        self.assertEqual(self.dist(), 0)
        self.assertEqual(self.runs()[1:], ["run p-dist dist --stage 2 trustc trust-src", "run p-full build --stage 2",
                                           "run p-manifest-tool build --stage 2 src/tools/build-manifest"])
        calls = self.plan.log()
        self.assertLess(calls.index("dist-components"), calls.index("run p-dist dist --stage 2 trustc trust-src"))
        record = self.kept("dist.json")
        self.assertEqual((record["components"], record["problems"]), (["trustc", "trust-src"], []))
        self.assertEqual([run["label"] for run in record["runs"]], list(driver.DIST_LABELS))
        packaged = self.plan.build_dir() / "dist"
        # The channel manifest was written by the tree's own tool, with the commit's date.
        self.assertEqual((packaged / "channel-rust-trust.toml").read_text(),
                         "date 2026-11-07 server https://trust.invalid channel trust\n")
        self.assertEqual(record["channel_manifest_command"][1:], [str(packaged), str(packaged), "2026-11-07",
                                                                 "https://trust.invalid", "trust"])
        self.assertEqual([row["name"] for row in record["archives"]],
                         sorted([*ARCHIVES, "channel-rust-trust.toml"]))
        self.assertEqual(record["archive_bytes_total"], sum(ARCHIVES.values()) + 59)
        self.assertEqual(snapshot(self.plan.dist), snapshot(packaged))
        self.assertEqual(record["native_outputs"]["before"], record["native_outputs"]["after"])
        # Every dist run used the producer's admission and the one config.
        for label in driver.DIST_LABELS:
            run = json.loads((self.plan.ledger / f"{label}.run.json").read_text())
            self.assertEqual(run["stage0_admission"], str(self.plan.ledger / "p-build.admission.json"))
            self.assertEqual(run["argv"][:3], ["x.py", "--config", str(self.plan.ledger / "rung.bootstrap.toml")])
        self.assertTrue(any(line.startswith("fixed-point-linux-seed: next: python3 ") and " prepare " in line
                            for line in self.said), self.said)
        calls = self.plan.log()
        self.said.clear()
        self.assertEqual(self.dist(), 0)
        self.assertEqual(self.plan.log(), calls)
        self.assertRegex(self.said[0], "dist: already done .*4 files, 199 bytes.*; not repeated")

    def test_an_archive_over_the_limit_stops_here_and_a_rerun_repeats_no_x_py_run(self):
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer"), 0)
        self.plan.args.asset_limit_bytes = 39
        text = self.refused(rf"dist ran and is not usable: trustc-0.1.0-trust-{HOST}.tar.xz is 40 bytes, over the "
                            r"asset limit of 39\. This is the stop before the hours of the other builds\. Kept: "
                            "every archive in .*build/dist, the record .*dist.not-clean.json and the producer's "
                            "tree", self.dist)
        self.assertNotIn(".tar.gz", text)       # only what is published is held to the limit
        self.assertFalse(self.plan.dist.exists())
        self.assertFalse((self.plan.kept / "dist.json").exists())
        self.assertIn("ran and is NOT usable", "\n".join(driver.status_lines(self.plan)))
        self.refused("moves that tree out of .*dist is not done", self.build, "cross-check")
        runs = self.runs()
        self.plan.args.asset_limit_bytes = 40
        self.assertEqual(self.dist(), 0)
        self.assertEqual(self.runs(), runs)
        self.assertFalse((self.plan.kept / "dist.not-clean.json").exists())
        self.assertEqual(sum("already run clean; not repeated" in line for line in self.said), 3)

    def test_a_stage2_that_dist_changed_and_a_component_with_no_archive_are_refused(self):
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer"), 0)
        # The full build after dist rebuilds the compiler and both files a pinned-seed build may not
        # reproduce; the helper names the first path it meets and stops.
        self.plan.stage2_for["p-full"] = {**STAGE2, "bin/trustc": "rebuilt by dist", "bin/ty": "relinked",
                                          "bin/targo-trust": "relinked"}
        text = self.refused(r"the producer's stage2 is not what .*kept/p.stage2.json recorded before dist: 3 of its "
                            r"\d+ entries differ in .*kept/p-after-dist.stage2.json, 1 of them outside bin/targo-trust "
                            r"and bin/ty \(the first: bin/targo-trust, bin/trustc, bin/ty\)\. verify-stage2-unchanged: "
                            r"`.*` exited 1, and the last line it printed on stderr is: error: stage2 changed after the "
                            r"DDC compared it: bin/targo-trust\. .*whether the archives in .* are of that tree is not "
                            r"established either way\. Kept: both manifests, .*nothing was copied out\. Every run of "
                            r"dist in this root reaches this check again", self.dist)
        self.assertNotIn("so the archives are not of the compared tree", text)
        self.assertFalse(self.plan.dist.exists())
        self.assertFalse((self.plan.kept / "dist.json").exists())
        kept = self.kept("dist.not-clean.json")
        self.assertEqual({key: kept["stage2_after_dist"][key] for key in ("differing", "outside_allowed", "first")},
                         {"differing": 3, "outside_allowed": 1, "first": ["bin/targo-trust", "bin/trustc", "bin/ty"]})
        self.assertEqual(kept["stage2_after_dist"]["manifest"], str(self.plan.kept / "p-after-dist.stage2.json"))
        self.assertEqual(self.kept("p-after-dist.stage2.json")["schema"], "trust-stage2-tree-v1")
        self.assertIn("ran and is NOT usable (the producer's stage2 is not what",
                      "\n".join(driver.status_lines(self.plan)))
        # A rerun repeats no x.py run and says the same.
        runs = self.runs()
        self.refused("3 of its .* entries differ", self.dist)
        self.assertEqual(self.runs(), runs)

        with tempfile.TemporaryDirectory() as tmp:
            self.root = Path(tmp).resolve() / "root"
            self.plan = FakePlan(arguments(self.root))
            self.plan.components = "trustc trust-src tippy"
            self.assertEqual(self.setup_root(), 0)
            self.assertEqual(self.build("producer"), 0)
            self.refused("dist ran and is not usable: no .tar.xz archive of tippy", self.dist)

    def test_a_channel_manifest_tool_that_fails_is_quoted_and_records_no_dist(self):
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer"), 0)
        self.plan.behaviour["p-manifest-tool"] = {"tool": "#!/bin/sh\necho 'error: no such component' >&2\nexit 3\n"}
        text = self.refused(r"the channel manifest could not be written: `.*build-manifest .*` failed, and its last "
                            r"line is: error: no such component \(all of it: .*p-channel-manifest.log.partial\)\. The "
                            "archives in .* are kept; the same command line runs this step again and no x.py run is "
                            "repeated", self.dist)
        self.assertNotIn("Traceback", text)
        self.assertFalse((self.plan.kept / "dist.json").exists())
        self.assertFalse(self.plan.dist.exists())

    def test_dist_starts_only_in_the_producers_clean_tree_by_its_stage0_and_its_llvm(self):
        def fresh() -> None:
            self.root = Path(self.tmp.name).resolve() / f"root{len(list(Path(self.tmp.name).iterdir()))}"
            self.plan = FakePlan(arguments(self.root))
            self.assertEqual(self.setup_root(), 0)
            self.assertEqual(self.build("producer"), 0)

        def other_stage0() -> None:
            (self.plan.stage0 / "bin" / "trustc").write_text("another compiler\n")

        def other_tree() -> None:
            self.plan.current_tree().write_text(json.dumps({"label": "s-build", "clean": True}))

        def dirty() -> None:
            (self.plan.src / "x.py").write_text("edited\n")

        def llvm() -> None:
            (self.plan.build_dir() / HOST / "llvm" / "bin" / "llc").write_bytes(b"\x7fELF changed after the build")

        for change, pattern in (
                (other_stage0, r"stage0 is not the producer's stage0 any more\. dist is built by the compiler that "
                               r"built the tree\. Nothing was started"),
                (other_tree, r"build is not the producer's tree \(.*current-tree.json names 's-build', the producer is "
                             r"p-build\)\. dist runs in that tree and nowhere else\. Nothing was started"),
                (dirty, r"src is not a clean checkout of [0-9a-f]{10}: 1 path.s. differ from HEAD.*Nothing was started"),
                (llvm, r"the LLVM and lld in .* are not what the producer's build left .*Something changed the "
                       r"producer's tree after its build\. Nothing was started")):
            with self.subTest(change.__name__):
                fresh()
                change()
                self.refused(pattern, self.dist)
                self.assertEqual(len(self.runs()), 1)
                self.assertFalse((self.plan.kept / "p-dist.attempt.json").exists())

    def test_a_dist_that_dirties_the_checkout_reaches_a_stock_name_or_rebuilds_llvm_is_not_usable(self):
        for behaviour, pattern in (
                ({"p-dist": {"also": {"x.py": "edited"}}}, r"the checkout is not clean after dist: 1 path"),
                ({"p-dist": {"trap": ["rustc -vV"]}}, r"the trap log has 1 line\(s\)"),
                ({"p-full": {"also": {f"build/{HOST}/llvm/bin/llc": "\x7fELF rebuilt"}}},
                 r"dist changed 1 and removed 0 of the LLVM and lld files the producer's build linked \(the first: "
                 r"llvm/bin/llc\)")):
            with self.subTest(pattern[:24]), tempfile.TemporaryDirectory() as tmp:
                self.root = Path(tmp).resolve() / "root"
                self.plan = FakePlan(arguments(self.root))
                self.assertEqual(self.setup_root(), 0)
                self.assertEqual(self.build("producer"), 0)
                self.plan.behaviour.update(behaviour)
                self.refused("dist ran and is not usable: .*" + pattern, self.dist)
                self.assertFalse((self.plan.kept / "dist.json").exists())
                self.assertFalse(self.plan.dist.exists())

    def test_a_dist_copy_that_is_not_the_packaged_tree_is_not_recorded(self):
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer"), 0)
        put(self.plan.dist / "stray", "x")
        self.refused(r"dist is not the copy of .*build/dist file for file\. Nothing was recorded\. Move it aside",
                     self.dist)
        self.assertFalse((self.plan.kept / "dist.json").exists())

    def test_a_dist_run_that_fails_is_run_again_under_its_next_label_only_when_asked(self):
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer"), 0)
        self.plan.behaviour["p-full"] = {"exit": 1}
        self.refused(r"p-full is not a clean build: .*x.py exited 1\..*To run this part of dist again under the "
                     "label p-full-2, give the same command line with --again", self.dist)
        self.refused("p-full ended and was not clean", self.dist)
        self.assertEqual(self.dist(again=True), 0)
        self.assertEqual([run["label"] for run in self.kept("dist.json")["runs"]],
                         ["p-dist", "p-full-2", "p-manifest-tool"])
        self.assertEqual([line.split()[1] for line in self.runs()],
                         ["p-build", "p-dist", "p-full", "p-full-2", "p-manifest-tool"])


    def test_a_dist_run_without_the_fifo_jobserver_or_whose_tokens_did_not_balance_is_not_clean(self):
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer"), 0)
        self.plan.behaviour["p-full"] = {"record": {"jobserver": None}}
        self.refused(r"p-full is not a clean build: the run record shows no jobserver", self.dist)
        self.assertFalse(self.plan.dist_record().exists())
        self.assertTrue(self.plan.not_clean("p-full").is_file())
        self.plan.behaviour["p-full-2"] = {"jobserver": {"tokens_at_end": 0}}
        self.refused(r"p-full-2 is not a clean build: its jobserver held 0 token\(s\) when x.py had exited, not the 2",
                     self.dist, True)
        self.assertEqual(self.dist(True), 0)
        self.assertEqual([run["label"] for run in self.kept("dist.json")["runs"]], ["p-dist", "p-full-3",
                                                                                   "p-manifest-tool"])

    def test_a_dist_run_starts_with_an_empty_tmp_so_a_fifo_a_killed_run_left_is_kept_aside(self):
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer"), 0)
        # A dist run killed before it could remove its FIFO jobserver left it, and a file.
        tmp = self.plan.ledger / "tmp"
        os.mkfifo(tmp / "jobserver.fifo", 0o600)
        (tmp / "left").write_text("x")
        self.assertEqual(self.dist(), 0)
        aside = self.plan.kept / "p-dist.tmp-before"
        self.assertTrue(stat.S_ISFIFO((aside / "jobserver.fifo").lstat().st_mode))
        self.assertEqual(self.kept("p-dist.attempt.json")["set_aside_before"],
                         {"tmp": {"entries": ["jobserver.fifo", "left"], "kept": str(aside)}})
        # A run that found tmp empty sets nothing aside.
        self.assertEqual(self.kept("p-full.attempt.json")["set_aside_before"], {})
        self.assertEqual([line.split()[1] for line in self.runs()], ["p-build", "p-dist", "p-full", "p-manifest-tool"])

    def test_a_build_whose_setup_bound_no_make_is_not_clean(self):
        self.plan.host_tools_now["make"] = None
        self.assertEqual(self.setup_root(), 0)
        self.refused(r"p-build is not a clean build: .*setup bound no make \(inputs.json's host_tools has no make "
                     r"row\), and a build step runs make through the jobserver's adapter", self.build, "producer")


class RoleTests(RootCase):
    def test_the_other_roles_wait_for_the_producer_for_dist_and_for_the_seed(self):
        self.assertEqual(self.setup_root(), 0)
        self.refused(r"the cross-check build is compared with the producer's and links its LLVM, and there is no "
                     r"clean producer build yet .*Run: python3 .* build --role producer", self.build, "cross-check")
        self.refused("there is no clean producer build yet", self.build, "control")
        self.assertEqual(self.build("producer"), 0)
        self.refused(r"dist is not done \(.*dist.json is not there\)\. Nothing was started\. Run: python3 .* dist",
                     self.build, "fixed-point")
        self.assertEqual(self.dist(), 0)
        tree = snapshot(self.plan.build_dir())
        text = self.refused(r"seed is not prepared \(.*kept/prepare.json is not there\): the fixed-point build's "
                            r"stage0 is the pinned archives as installed, and the `prepare` step admits and installs "
                            r"them\. Nothing was started and everything built so far is kept\. Run: python3 .* "
                            r"prepare .*; the cross-check needs no seed: python3 .* build --role cross-check",
                            self.build, "fixed-point")
        # A seed someone put there is not a prepared one.
        shutil.copytree(SOURCE.pinned, self.plan.seed)
        self.refused(r"seed is not prepared", self.build, "fixed-point")
        shutil.rmtree(self.plan.seed)
        # The producer's tree was not moved for a build that could not start.
        self.assertEqual(snapshot(self.plan.build_dir()), tree)
        self.assertFalse((self.plan.kept / "p-build-tree").exists())
        self.install_seed()
        self.refused(r"--stage0 is for the producer and the cross-check", self.build, "fixed-point", SOURCE.nine)
        self.refused(r"a control repeats the fixed-point build, and there is no clean one yet", self.build, "control")

    def test_three_roles_share_everything_but_their_stage0_and_label(self):
        self.through_dist()
        self.install_seed()
        self.assertEqual(self.build("fixed-point"), 0)
        self.assertEqual(self.build("cross-check"), 0)
        p, f, s = (self.kept(f"{stem}.build.json") for stem in "pfs")
        self.assertEqual([record["label"] for record in (p, f, s)], ["p-build", "f-build", "s-build"])
        # One config file, one build line, one environment but for the label.
        self.assertEqual(p["shared"], f["shared"])
        self.assertEqual(p["shared"], s["shared"])
        self.assertEqual({record["config"]["sha256"] for record in (p, f, s)}, {p["config"]["sha256"]})
        runs = [json.loads((self.plan.ledger / f"{label}.run.json").read_text())
                for label in ("p-build", "f-build", "s-build")]
        self.assertEqual({tuple(run["argv"]) for run in runs},
                         {("x.py", "--config", str(self.plan.ledger / "rung.bootstrap.toml"),
                           "build", "--stage", "2", "compiler/rustc", "library/std")})
        environments = [{key: value for key, value in run["environment"].items() if key != "TRUST_STAIRCASE_RUNG"}
                        for run in runs]
        self.assertEqual(environments[0], environments[1])
        self.assertEqual(environments[0], environments[2])
        # One FIFO jobserver, setup's, for every role and every dist run.
        jobserver = json.loads(self.plan.inputs_file().read_text())["jobserver"]
        self.assertEqual(p["shared"]["jobserver"], jobserver)
        dist_runs = [json.loads((self.plan.ledger / f"{label}.run.json").read_text()) for label in driver.DIST_LABELS]
        self.assertEqual({run["environment"]["MAKEFLAGS"] for run in runs + dist_runs}, {jobserver["makeflags"]})
        self.assertEqual({(run["jobserver"]["path"], run["jobserver"]["tokens"]) for run in runs + dist_runs},
                         {(jobserver["path"], 2)})
        # Three different compilers, each copied to the one path; the earlier copies are kept.
        self.assertEqual(len({record["stage0"]["trustc_sha256"] for record in (p, f, s)}), 3)
        self.assertEqual({record["stage0"]["path"] for record in (p, f, s)}, {str(self.root / "stage0")})
        self.assertEqual(snapshot(self.root / "stage0.p-build"), snapshot(SOURCE.six))
        self.assertEqual(snapshot(self.root / "stage0.f-build"), snapshot(SOURCE.pinned))
        self.assertEqual(snapshot(self.plan.stage0), snapshot(SOURCE.nine))
        # Each earlier tree whole, and the producer's LLVM and lld under every later build, unchanged.
        self.assertTrue((self.plan.kept / "p-build-tree" / "dist").is_dir())
        self.assertTrue((self.plan.kept / "f-build-tree" / HOST / "stage2" / "bin" / "trustc").is_file())
        self.assertEqual(self.kept("current-tree.json")["label"], "s-build")
        for record in (f, s):
            self.assertEqual(record["native_before"]["sha256"], p["native_after"]["sha256"])
            self.assertEqual(record["native_after"]["sha256"], p["native_after"]["sha256"])
            self.assertEqual(record["comparison"], {"with": "p", "identical": True, "differing": [],
                                                    "outside_allowed": []})
        self.assertFalse((self.plan.build_dir() / "dist").exists())
        self.assertTrue(any("f-build: its stage2 is the producer's, entry for entry" in line for line in self.said))
        status = driver.status_lines(self.plan)
        self.assertIn("  control      none needed: the fixed-point tree is the producer's", status)
        self.assertIn("  record       not written", status)
        self.assertEqual(status[-1], "next: " + shlex.join(driver.command_line(self.plan, "record")))
        self.refused("the fixed-point build's tree is the producer's, entry for entry: there is nothing for a "
                     "control to decide", self.build, "control")

    def test_an_input_that_changed_since_an_earlier_role_is_refused_before_x_py_starts(self):
        self.through_dist()
        runs = self.runs()

        def changed(what: str, change, restore, pattern: str) -> None:
            with self.subTest(what):
                change()
                try:
                    text = self.refused(pattern, self.build, "cross-check")
                    self.assertRegex(text, "[Nn]othing was (started|built)")
                    self.assertEqual(self.runs(), runs)
                    self.assertFalse((self.plan.kept / "s-build.attempt.json").exists())
                finally:
                    restore()

        ninja = self.plan.tools / "ninja"
        original = ninja.read_bytes()
        changed("ninja", lambda: ninja.write_bytes(b"#!/bin/sh\necho other\n"), lambda: ninja.write_bytes(original),
                "tools is not what setup made, the one file ninja with sha256")
        extra = self.plan.tools / "cmake"
        changed("another tool", lambda: put(extra, "#!/bin/sh\n", 0o755), extra.unlink,
                "tools is not what setup made")
        crate = self.plan.ledger / "cargo-home" / "registry" / "cache" / "i" / "b-2.0.0.crate"
        changed("the cargo home", lambda: crate.write_text("fetched later\n"), crate.unlink,
                r"s-build would not be given what setup recorded: cargo_home is .* now and was .* at setup")
        prelude = self.plan.lean_library / "Init" / "Prelude.olean"
        changed("the Lean copy", lambda: prelude.write_text("other\n"), lambda: prelude.write_text("olean\n"),
                r"the Lean copy .* is no longer what setup bound .*; nothing was started: .*error: Clean Lean "
                "installation or source Oracle changed")
        tools = dict(self.plan.host_tools_now)

        def upgrade():
            self.plan.host_tools_now = {**tools, "cc": {**tools["cc"], "sha256": "0" * 64}}

        def downgrade():
            self.plan.host_tools_now = tools

        changed("the C compiler", upgrade, downgrade, "s-build would not be given what setup recorded: host_tools")
        gcc = dict(self.plan.tool_rows["/usr/bin/gcc"])
        changed("the gcc the base config names",
                lambda: self.plan.tool_rows.update({"/usr/bin/gcc": {**gcc, "real": "/opt/other/gcc"}}),
                lambda: self.plan.tool_rows.update({"/usr/bin/gcc": gcc}),
                r"s-build would not be given what setup recorded: host_tools is .* at setup \(.*inputs.json\)\. "
                r"Nothing was started .*\(the first entry of host_tools that differs: /usr/bin/gcc\)$")
        config = self.plan.ledger / "rung.bootstrap.toml"
        text = config.read_text()
        changed("the rung config", lambda: config.write_text(text + "# edited\n"), lambda: config.write_text(text),
                "the rung config s-build would be built with is not .*rung.bootstrap.toml, the one the earlier "
                "builds used, byte for byte")
        changed("the checkout", lambda: (self.plan.src / "x.py").write_text("edited\n"),
                lambda: git(self.plan.src, "checkout", "--", "x.py"), "is not a clean checkout of")
        stray = self.plan.src / "stray.txt"
        changed("an ignored file", lambda: stray.write_text("x"), stray.unlink,
                "holds ignored files a build does not leave: stray.txt")
        native = self.plan.build_dir() / HOST / "llvm" / "bin" / "llc"

        # After all of that the role still builds, and from the producer's LLVM.
        self.assertEqual(self.build("cross-check"), 0)
        self.assertEqual(self.kept("s.build.json")["label"], "s-build")
        self.assertEqual(native.read_bytes(), NATIVE["llvm/bin/llc"].encode("latin-1"))

    def test_a_root_set_up_before_the_config_tools_were_bound_builds_nothing_more(self):
        # Setup as it was: the roles' tools only, none of the base config's by path.
        with mock.patch.object(driver.Plan, "config_tools", lambda plan: {}):
            self.assertEqual(self.setup_root(), 0)
        self.assertFalse(any(key.startswith("/") for key in
                             json.loads(self.plan.inputs_file().read_text())["host_tools"]))
        text = self.refused(r"p-build would run /usr/bin/g\+\+, /usr/bin/gcc, /usr/bin/python3, which the base config "
                            r"names, and setup did not bind them: .*inputs.json has no row for them, so this root was "
                            "set up before setup measured the host tools the base config names. Nothing was started "
                            "and nothing was changed", self.build, "producer")
        self.assertIn("set up a new --root and build every role in it", text)
        self.assertEqual(self.runs(), [])
        self.assertFalse(self.plan.record("p").exists())

    def test_a_root_set_up_before_the_fifo_jobserver_builds_and_dists_nothing_more(self):
        # Setup as it was: no jobserver in inputs.json (BOOTSTRAP-JOBSERVER-PROBE-1).
        self.assertEqual(self.setup_root(), 0)
        recorded = self.plan.inputs_file().read_bytes()
        older = json.loads(recorded)
        older.pop("jobserver")
        older_bytes = json.dumps(older).encode()

        def refused_in_an_older_root(label, call, *args):
            self.plan.inputs_file().write_bytes(older_bytes)
            runs, kept = self.runs(), snapshot(self.plan.kept)
            try:
                text = self.refused(rf"{label} would be given a FIFO jobserver, as every x.py run is since "
                                    r"BOOTSTRAP-JOBSERVER-PROBE-1 \(seed_staircase.py run --fifo-jobserver\), and "
                                    r".*inputs.json records none, so this root was set up before every run was given "
                                    r"one: .*Nothing was started and nothing was changed. Set up a new --root and "
                                    "build every role in it", call, *args)
                # Refused before anything is measured, moved or written (dist would first write
                # the native outputs it starts with; a build, set the tree aside and copy its stage0).
                self.assertEqual(self.runs(), runs)
                self.assertEqual(snapshot(self.plan.kept), kept)
                self.assertIn("  jobserver    none recorded: this root was set up before every x.py run was given a "
                              "FIFO jobserver, and no build or dist starts in it; set up a new --root",
                              driver.status_lines(self.plan))
                return text
            finally:
                self.plan.inputs_file().write_bytes(recorded)

        refused_in_an_older_root("the producer build", self.build, "producer")
        self.assertFalse(self.plan.attempt("p-build").exists())
        # A jobserver of null is none either.
        older_bytes = json.dumps({**older, "jobserver": None}).encode()
        refused_in_an_older_root("the producer build", self.build, "producer")
        older_bytes = json.dumps(older).encode()
        self.assertEqual(self.build("producer"), 0)
        refused_in_an_older_root("dist", self.dist)
        self.assertFalse(self.plan.attempt("p-dist").exists())
        self.assertEqual(self.dist(), 0)
        refused_in_an_older_root("the cross-check build", self.build, "cross-check")
        self.assertFalse(self.plan.attempt("s-build").exists())
        self.assertFalse(any(line.startswith("  jobserver") for line in driver.status_lines(self.plan)))
        # require_shared holds it too, for a caller that did not ask first ...
        inputs = json.loads(recorded)
        inputs.pop("jobserver")
        self.refused(r"s-build would be given a FIFO jobserver", driver.require_shared, self.plan, inputs, {}, "s-build")
        # ... and a run is given only the arrangement setup recorded.
        shared = driver.shared_facts(self.plan, json.loads(recorded))
        inputs = json.loads(recorded)
        inputs["jobserver"] = {**inputs["jobserver"], "path": "/elsewhere/jobserver.fifo"}
        self.refused(r"s-build would not be given what setup recorded: jobserver is .* now and was .* at setup "
                     r"\(.*inputs.json\)\. Nothing was started .*\(the first entry of jobserver that differs: path\)$",
                     driver.require_shared, self.plan, inputs, shared, "s-build")

    def test_a_jobserver_seed_staircase_would_hand_out_otherwise_than_at_setup_starts_nothing(self):
        self.assertEqual(self.setup_root(), 0)
        # seed_staircase.py names the FIFO otherwise than when setup recorded it.
        with mock.patch.object(driver.staircase(), "FIFO_JOBSERVER_NAME", "other.fifo"):
            self.refused(r"p-build would not be given what setup recorded: jobserver is .* now and was .* at setup "
                         r".*Nothing was started .*\(the first entry of jobserver that differs: makeflags\)$",
                         self.build, "producer")
        self.assertEqual(self.runs(), [])
        self.assertFalse(self.plan.record("p").exists())
        with mock.patch.object(driver.staircase(), "make_adapter_path", lambda ledger: ledger / "bin" / "make"):
            self.refused(r"\(the first entry of jobserver that differs: make_adapter\)$", self.build, "producer")
        self.assertEqual(self.runs(), [])
        self.assertEqual(self.build("producer"), 0)

    def test_an_earlier_roles_record_is_what_a_later_one_is_held_to(self):
        self.through_dist()
        # What setup recorded is intact; only the producer's record says the job count was another.
        record = self.kept("p.build.json")
        original = (self.plan.kept / "p.build.json").read_text()
        record["shared"]["jobs"] = 20
        (self.plan.kept / "p.build.json").write_text(json.dumps(record))
        text = self.refused(r"s-build would not be given what p-build was given: jobs is 3 now and was 20 for that "
                            r"build \(.*p.build.json\)\. The roles differ only in their stage0",
                            self.build, "cross-check")
        self.assertEqual(len(self.runs()), 4)
        # So is the jobserver the producer was given.
        record = json.loads(original)
        record["shared"]["jobserver"]["path"] = "/elsewhere/jobserver.fifo"
        (self.plan.kept / "p.build.json").write_text(json.dumps(record))
        self.refused(r"s-build would not be given what p-build was given: jobserver is .* now and was .* for that "
                     r"build \(.*p.build.json\) \(the first entry of jobserver that differs: path\)\. The roles differ "
                     r"only in their stage0", self.build, "cross-check")
        self.assertEqual(len(self.runs()), 4)

    def test_a_later_role_run_by_other_scripts_or_given_another_environment_is_refused(self):
        self.through_dist()
        # The scripts that write the build's trap shims, environment and config tail are the producer's.
        record = self.kept("p.build.json")
        self.assertEqual(record["shared"]["scripts"], {name: hashlib.sha256((driver.HERE / name).read_bytes())
                                                       .hexdigest() for name in driver.GIVEN_BY})
        record["shared"]["scripts"]["seed_staircase.py"] = "0" * 64
        original = (self.plan.kept / "p.build.json").read_text()
        (self.plan.kept / "p.build.json").write_text(json.dumps(record))
        self.refused(r"s-build would not be given what p-build was given: scripts is .* now and was .* for that build "
                     r"\(.*p.build.json\) \(the first entry of scripts that differs: seed_staircase.py\)\. The roles "
                     r"differ only in their stage0, so nothing was started and nothing "
                     "was changed. seed_staircase.py and linux_refresh_toolchain.py write the build's trap shims, "
                     "environment and config tail and judge its run: run every role from one checkout of them at "
                     "one commit", self.build, "cross-check")
        (self.plan.kept / "p.build.json").write_text(original)
        self.assertEqual(len(self.runs()), 4)
        # x.py's environment, measured after the build, is the producer's in every key.
        self.plan.behaviour["s-build"] = {"environment": {"PATH": "/elsewhere:/usr/bin:/bin"}}
        self.refused(r"s-build is not a clean build: .*x.py's PATH was '/elsewhere:/usr/bin:/bin' and was '.*' for "
                     "p-build", self.build, "cross-check")
        self.assertFalse((self.plan.kept / "s.build.json").exists())

    def test_a_tool_directory_with_a_rust_tool_name_or_llvm_changed_after_dist_starts_nothing(self):
        self.through_dist()
        runs = self.runs()
        put(self.plan.tools / "cargo", "#!/bin/sh\n", 0o755)
        text = self.refused(r"the tool directory .*tools is not what setup made: --tool-dir .*tools carries a Rust tool "
                            r"name: cargo\. Nothing was started", self.build, "cross-check")
        self.assertNotIn("Traceback", text)
        (self.plan.tools / "cargo").unlink()
        (self.plan.build_dir() / HOST / "llvm" / "bin" / "llc").write_bytes(b"\x7fELF changed after dist")
        self.refused(r"the LLVM and lld copied for s-build are not the producer's .*after dist\)\. Nothing was started",
                     self.build, "cross-check")
        self.assertEqual(self.runs(), runs)
        self.assertFalse((self.plan.kept / "s-build.attempt.json").exists())

    def test_a_root_set_up_for_another_commit_is_not_built_in(self):
        self.through_dist()
        other = FakePlan(arguments(self.root, commit="1" * 40))
        other.args.role, other.args.stage0, other.args.again = "cross-check", SOURCE.nine, False
        with self.assertRaisesRegex(driver.Refusal, r"inputs.json is a setup with commit = '[0-9a-f]{40}', and this "
                                                    rf"command is for '{'1' * 40}'\. Nothing was started"):
            driver.build(other, "cross-check")

    def test_the_same_compiler_twice_is_not_a_second_role(self):
        self.through_dist()
        text = self.refused(r"the stage0 of s-build has the bin/trustc of p-build's \(sha256 [0-9a-f]{64}\)\. The "
                            "producer, the fixed point and the cross-check are three different compilers",
                            self.build, "cross-check", SOURCE.six)
        self.assertIn("Nothing was built", text)
        self.assertEqual(len(self.runs()), 4)

    def test_a_build_that_changes_the_producers_llvm_is_not_comparable(self):
        self.through_dist()
        self.plan.behaviour["s-build"] = {"also": {f"build/{HOST}/llvm/bin/llc": "\x7fELF rebuilt"}}
        self.refused(r"s-build is not a clean build: x.py did not leave the producer's LLVM and lld as they were "
                     r"\(1 changed, 0 removed, 0 added; the first: llvm/bin/llc\), so this build is not comparable",
                     self.build, "cross-check")
        self.assertFalse((self.plan.kept / "s.build.json").exists())
        # Built again, it starts from the producer's LLVM, not from the one that build left.
        self.plan.behaviour.clear()
        self.assertEqual(self.build("cross-check", again=True), 0)
        self.assertEqual(self.kept("s.build.json")["label"], "s-build-2")
        self.assertEqual((self.plan.build_dir() / HOST / "llvm/bin/llc").read_bytes(), b"\x7fELF llc")

    def test_a_tree_that_differs_outside_the_two_files_is_said_and_exits_1(self):
        self.through_dist()
        self.plan.stage2_for["s-build"] = {**STAGE2, "lib/libstd.so": "another std", "bin/ty": "another ty"}
        self.assertEqual(self.build("cross-check"), 1)
        found = self.kept("s.build.json")["comparison"]
        self.assertEqual((found["identical"], found["differing"], found["outside_allowed"]),
                         (False, ["bin/ty", "lib/libstd.so"], ["lib/libstd.so"]))
        self.assertTrue(any("s-build: its stage2 is NOT the producer's in 1 entry other than bin/targo-trust and "
                            "bin/ty (the first: lib/libstd.so" in line for line in self.said))
        self.assertEqual(self.build("cross-check"), 1)      # said again, built once
        self.assertEqual(len(self.runs()), 5)
        status = "\n".join(driver.status_lines(self.plan))
        self.assertIn("1 of them outside bin/targo-trust and bin/ty: STOP", status)


class ControlTests(RootCase):
    def fixed_point(self, **stage2) -> int:
        self.through_dist()
        self.install_seed()
        self.plan.stage2_for["f-build"] = {**STAGE2, **stage2}
        return self.build("fixed-point")

    def test_a_control_that_gives_the_producers_bytes_decides_the_file(self):
        self.assertEqual(self.fixed_point(**{"bin/ty": "ty, another link order"}), 0)
        self.assertTrue(any("f-build: its stage2 differs from the producer's only in bin/ty. Next: python3 "
                            in line and "build --role control" in line for line in self.said))
        self.assertIn("  control      0 of at most 3 built; bin/ty: undecided", driver.status_lines(self.plan))
        seed_copy = self.plan.stage0.stat().st_ino
        self.assertEqual(self.build("control"), 0)
        # The control is built from the copy of the seed the fixed point used: not copied again.
        self.assertEqual(self.plan.stage0.stat().st_ino, seed_copy)
        self.assertFalse((self.root / "stage0.f-build").exists())
        record = self.kept("c1.build.json")
        self.assertEqual((record["role"], record["label"], record["comparison"]["identical"]),
                         ("control", "c1-build", True))
        self.assertEqual(record["stage0"]["tree"], self.kept("f.build.json")["stage0"]["tree"])
        self.assertEqual(driver.control_state(self.plan),
                         {"controls": 1, "outside": [], "absent": [], "undecided": [], "decided": {
                             "bin/ty": "reproduced: a build by the pinned seed gave the producer's bytes"}})
        self.refused(r"every file the fixed-point build did not reproduce is already decided \(bin/ty: reproduced",
                     self.build, "control")
        self.assertNotIn("build --role control", "\n".join(driver.status_lines(self.plan)))

    def test_two_different_results_from_the_pinned_seed_decide_it_too(self):
        self.assertEqual(self.fixed_point(**{"bin/ty": "ty, order 2"}), 0)
        self.plan.stage2_for["c1-build"] = {**STAGE2, "bin/ty": "ty, order 3"}
        self.assertEqual(self.build("control"), 0)
        self.assertEqual(driver.control_state(self.plan)["decided"],
                         {"bin/ty": "nondeterministic: two builds by the pinned seed gave different bytes"})
        self.refused("already decided .bin/ty: nondeterministic", self.build, "control")

    def test_three_controls_that_agree_with_each_other_and_not_with_the_producer_are_the_stop(self):
        self.assertEqual(self.fixed_point(**{"bin/targo-trust": "from the seed"}), 0)
        for number in (1, 2, 3):
            self.plan.stage2_for[f"c{number}-build"] = {**STAGE2, "bin/targo-trust": "from the seed"}
            self.assertEqual(self.build("control"), 0)
            self.assertEqual(self.kept(f"c{number}.build.json")["label"], f"c{number}-build")
        self.refused(r"3 controls are built, and bin/targo-trust still has one digest in every build by the pinned "
                     r"seed and another in the producer's: the difference follows the stage0, and the rule is that "
                     "no record is written", self.build, "control")
        # Nothing more is asked of a control; the cross-check is still to build.
        self.assertEqual(driver.status_lines(self.plan)[-1], "next: " + shlex.join(
            driver.command_line(self.plan, "build", "--role", "cross-check")))
        self.assertEqual([line.split()[1] for line in self.runs() if line.split()[1].startswith("c")],
                         ["c1-build", "c2-build", "c3-build"])

    def test_a_control_cannot_decide_a_difference_outside_the_two_files(self):
        self.assertEqual(self.fixed_point(**{"bin/trustc": "another compiler"}), 1)
        text = self.refused(r"the builds by the pinned seed differ from the producer's tree in 1 entry other than "
                            r"bin/targo-trust and bin/ty \(the first: bin/trustc\)\. A control decides only those two "
                            "files", self.build, "control")
        self.assertIn("Nothing was started; every tree and manifest is kept", text)
        self.assertIn("  control      none can help: 1 entry differ outside the two allowed files",
                      driver.status_lines(self.plan))

    def test_a_control_is_built_from_the_seed_the_fixed_point_was(self):
        self.assertEqual(self.fixed_point(**{"bin/ty": "ty, order 2"}), 0)
        self.install_seed(SOURCE.with_lld)
        self.refused(r"c1-build repeats the fixed-point build, and its stage0 is not that build's \(.*seed changed "
                     r"since f-build\)\. Nothing was built", self.build, "control")


# ---------------------------------------------------------------------------
# prepare: a two-host pin in small. The parent pins nine archives of the commit for
# aarch64-apple-darwin (prepare.py's own repacks, beside the manifest naming them);
# this host's dist ships the nine for HOST, whose code is the producer's stage2 byte
# for byte. Real prepare.py, stage-artifacts, rustc-dev-handoff and
# verify-archives-carry-compared run over them; each archive's install.sh is a small
# rust-installer.

PREPARE_SPEC = importlib.util.spec_from_file_location("fixed_point_prepare_py", driver.PREPARE_PY)
assert PREPARE_SPEC is not None and PREPARE_SPEC.loader is not None
stage0_prepare = importlib.util.module_from_spec(PREPARE_SPEC)
sys.modules[PREPARE_SPEC.name] = stage0_prepare
PREPARE_SPEC.loader.exec_module(stage0_prepare)

DARWIN = "aarch64-apple-darwin"
SEED_DATE, SEED_VERSION = "2026-11-07", "0.13.0"
SEED_SERVER = "file://{trust-root}/bootstrap/trust-stage0"
PACKAGE_VERSION = "0.13.0-trust (fixture 2026-11-07)"
PARENT_COMMIT = "1234567890" * 4
INSTALLER = rb"""#!/bin/sh
# rust-installer's install.sh, reduced: each component's manifest.in, into --prefix.
set -eu
src_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
prefix=
for arg in "$@"; do case "$arg" in --prefix=*) prefix=${arg#--prefix=};; esac; done
mkdir -p "$prefix/lib/rustlib"
echo 3 > "$prefix/lib/rustlib/rust-installer-version"
for component in $(cat "$src_dir/components"); do
    while read -r line; do
        case "$line" in
            file:*)
                file=${line#file:}
                mkdir -p "$prefix/$(dirname "$file")"
                cp "$src_dir/$component/$file" "$prefix/$file"
                echo "file:$prefix/$file" >> "$prefix/lib/rustlib/manifest-$component";;
        esac
    done < "$src_dir/$component/manifest.in"
    echo "$component" >> "$prefix/lib/rustlib/components"
done
"""
# The shared source archive's install.sh, as rust-installer's generator writes it: prepare.py
# keeps the pinned trust-src only when its installer is install-template.sh with plain slot
# values. (trust-src is not one of the components prepare installs.)
SHARED_INSTALLER = (REPO / "src" / "tools" / "rust-installer" / "install-template.sh").read_bytes()
for _slot, _value in ((b"PRODUCT_NAME", b"'Trust'"), (b"REL_MANIFEST_DIR", b"rustlib"),
                      (b"SUCCESS_MESSAGE", b"'trust src installed.'"), (b"LEGACY_MANIFEST_DIRS", b"'rustlib,cargo'"),
                      (b"RUST_INSTALLER_VERSION", b"'3'")):
    SHARED_INSTALLER = SHARED_INSTALLER.replace(b"%%TEMPLATE_" + _slot + b"%%", _value)
# The producer's stage2, as the archives ship it.
STAGE2_SEED = {
    **STAGE2, "bin/trustc": "\x7fELF trustc", "bin/rustc": "\x7fELF trustc", "bin/trustdoc": "\x7fELF trustdoc",
    "bin/rustdoc": "\x7fELF trustdoc", "libexec/trust-analyzer-proc-macro-srv": "\x7fELF proc-macro-srv",
    "lib/librustc_driver-fixture.so": "\x7fELF driver", "lib/libstd-fixture.so": "\x7fELF std dylib",
    f"lib/rustlib/{HOST}/lib/libstd-fixture.rlib": "!<arch>\nstd",
    f"lib/rustlib/{HOST}/lib/librustc_middle-fixture.rlib": "!<arch>\nmiddle", "bin/targo": "\x7fELF targo",
    "bin/cargo": "\x7fELF targo", "bin/targo-trust": "\x7fELF targo-trust", "bin/trustfmt": "\x7fELF trustfmt",
    "bin/targo-fmt": "\x7fELF targo-fmt", "bin/tippy": "\x7fELF tippy", "bin/targo-tippy": "\x7fELF targo-tippy",
    "bin/tippy-driver": "\x7fELF tippy-driver", "bin/trust-analyzer": "\x7fELF trust-analyzer"}
# archive name stem -> (channel package, component directory, installed files); `{host}` is the triple.
SEED_ARCHIVES = {
    "trustc": ("trustc", "trustc", ("bin/trustc", "bin/rustc", "bin/trustdoc", "bin/rustdoc",
                                    "libexec/trust-analyzer-proc-macro-srv", "lib/librustc_driver-fixture.so",
                                    "lib/libstd-fixture.so")),
    "trust-std": ("trust-std", "trust-std-{host}", ("lib/rustlib/{host}/lib/libstd-fixture.rlib",)),
    "trustc-dev": ("trustc-dev", "trustc-dev", ("lib/rustlib/{host}/lib/librustc_middle-fixture.rlib",)),
    "targo": ("targo", "targo", ("bin/targo", "bin/cargo")),
    "trustfmt": ("trustfmt-preview", "trustfmt-preview", ("bin/trustfmt", "bin/targo-fmt")),
    "targo-trust": ("targo-trust", "targo-trust", ("bin/targo-trust",)),
    "tippy": ("tippy-preview", "tippy-preview", ("bin/tippy", "bin/targo-tippy", "bin/tippy-driver")),
    "trust-analyzer": ("trust-analyzer-preview", "trust-analyzer-preview", ("bin/trust-analyzer",)),
}
SOURCE_FILE = "lib/rustlib/src/rust/library/core/src/lib.rs"


def seed_archive(directory: Path, stem: str, host: str | None, files: dict[str, bytes],
                 builder_config: bytes | None = None) -> Path:
    """One dist archive: rust-installer's layout, `host` None for the shared source archive."""
    name = f"{stem}-{SEED_VERSION}-trust" + (f"-{host}" if host else "") + ".tar.xz"
    prefix, folder = name.removesuffix(".tar.xz"), (SEED_ARCHIVES.get(stem, (stem, stem))[1]).format(host=host)
    members = {"components": f"{folder}\n".encode(), "install.sh": INSTALLER if host else SHARED_INSTALLER,
               "version": f"{PACKAGE_VERSION}\n".encode(), "git-commit-hash": f"{SOURCE.commit}\n".encode(),
               f"{folder}/manifest.in": "".join(f"file:{path}\n" for path in sorted(files)).encode(),
               **{f"{folder}/{path}": data for path, data in files.items()}}
    if builder_config is not None:
        members["builder-config"] = builder_config
    with tarfile.open(directory / name, "w:xz") as archive:
        for member, data in members.items():
            info = tarfile.TarInfo(f"{prefix}/{member}")
            info.size, info.mode = len(data), 0o755 if member.startswith(("install.sh", f"{folder}/bin",
                                                                            f"{folder}/libexec")) else 0o644
            archive.addfile(info, io.BytesIO(data))
    return directory / name


def channel(built: dict[str, dict[str, tuple[str, str]]], unbuilt: tuple[str, ...]) -> dict:
    """A channel manifest: `built` package -> triple -> (url, sha256); every package
    is unbuilt for each of `unbuilt`, as build-manifest lists every triple."""
    pkg: dict = {"trust": {"version": PACKAGE_VERSION, "git_commit_hash": SOURCE.commit}}
    for package in stage0_prepare.SOURCE_STAGE0_COMPONENTS:
        targets: dict = {} if package == "trust-src" else {triple: {"available": False} for triple in unbuilt}
        for triple, (url, digest) in built.get(package, {}).items():
            targets[triple] = {"available": True, "xz_url": url, "xz_hash": digest}
        pkg[package] = {"version": PACKAGE_VERSION, "git_commit_hash": SOURCE.commit, "target": targets}
    return {"date": SEED_DATE, "pkg": pkg}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class SeedFixture:
    def __init__(self, base: Path):
        self.linux, self.cohort, raw = base / "linux-dist", base / "cohort", base / "darwin-raw"
        for directory in (self.linux, self.cohort, raw):
            directory.mkdir(parents=True)
        source = {SOURCE_FILE: b"pub fn core() {}\n"}
        built, pinned = {}, {}
        for stem, (package, _folder, paths) in SEED_ARCHIVES.items():
            files = {path.format(host=HOST): STAGE2_SEED[path.format(host=HOST)].encode("latin-1") for path in paths}
            archive = seed_archive(self.linux, stem, HOST, files)
            built[package] = {HOST: (f"https://trust.invalid/{SEED_DATE}/{archive.name}", sha(archive))}
            darwin = {path.format(host=DARWIN): f"darwin {STAGE2_SEED[path.format(host=HOST)]}".encode("latin-1")
                      for path in paths}
            raw_archive = seed_archive(raw, stem, DARWIN, darwin)
            stage0_prepare.repack_owned_tarball(raw_archive, self.cohort / raw_archive.name,
                                                old_filename=raw_archive.name, new_filename=raw_archive.name,
                                                source_channel="trust", owned_channel="trust")
            pinned[package] = {DARWIN: (f"{SEED_SERVER}/dist/{SEED_DATE}/{raw_archive.name}",
                                        sha(self.cohort / raw_archive.name))}
        archive = seed_archive(self.linux, "trust-src", None, source, b"build-dir = '/home/builder/build'\n")
        built["trust-src"] = {"*": (f"https://trust.invalid/{SEED_DATE}/{archive.name}", sha(archive))}
        raw_archive = seed_archive(raw, "trust-src", None, source, b"build-dir = '<home>/build'\n")
        stage0_prepare.repack_owned_tarball(raw_archive, self.cohort / raw_archive.name,
                                            old_filename=raw_archive.name, new_filename=raw_archive.name,
                                            source_channel="trust", owned_channel="trust")
        pinned["trust-src"] = {"*": (f"{SEED_SERVER}/dist/{SEED_DATE}/{raw_archive.name}",
                                     sha(self.cohort / raw_archive.name))}
        self.built = built
        self.toml = self.linux / "channel-rust-trust.toml"
        self.toml.write_text(stage0_prepare.dump_toml(channel(built, (DARWIN, HOST))))
        parent = channel(pinned, (DARWIN, HOST))
        self.manifest = stage0_prepare.dump_toml(parent).encode()
        checksums = stage0_prepare.checksum_entries(parent, dist_server=SEED_SERVER,
                                                    components=stage0_prepare.DEFAULT_STAGE0_COMPONENTS)
        self.rows = checksums
        # The parent's src/stage0: an editable head of its own, then prepare.py's section.
        self.stage0 = ("# The parent's editable head.\n" + stage0_prepare.stage0_content(
            manifest=parent, manifest_hash=hashlib.sha256(self.manifest).hexdigest(), git_commit_hash=SOURCE.commit,
            dist_server=SEED_SERVER, owned_channel="trust", compiler_version=f"{SEED_VERSION}-trust",
            rustfmt_version=f"{SEED_VERSION}-trust", checksums=checksums, metadata_only_checkout=False)).encode()
        self.archives = {path.name: str(path) for path in sorted(self.linux.glob("*.tar.xz"))}


_SEED: SeedFixture | None = None


def seed_fixture() -> SeedFixture:
    global _SEED
    if _SEED is None:
        _SEED = SeedFixture(SOURCE.base / "seed-fixture")
    return _SEED


class PrepareCase(RootCase):
    """A root through dist whose archives are SeedFixture's, and `prepare` over it."""

    def setUp(self):
        super().setUp()
        self.fixture = seed_fixture()
        self.configure(self.plan)

    def configure(self, plan) -> None:
        plan.archives = dict(self.fixture.archives)
        plan.components = " ".join(sorted({*SEED_ARCHIVES, "trust-src"}))
        plan.behaviour["p-manifest-tool"] = {"tool": f'#!/bin/sh\ncp {self.fixture.toml} "$1/channel-rust-trust.toml"\n'}
        plan.stage2_for.update({"p-build": STAGE2_SEED, "p-full": STAGE2_SEED})
        plan.args.cohort = self.fixture.cohort
        plan.parent_files = {"src/stage0": self.fixture.stage0,
                             driver.PARENT_MANIFEST.format(date=SEED_DATE): self.fixture.manifest}

    def prepare(self) -> int:
        return self.quiet(driver.prepare_seed, self.plan)

    def candidate(self) -> dict[str, str]:
        return driver.text_rows((self.plan.prepare_dir() / "stage0.candidate").read_text(), "candidate")


class PrepareTests(PrepareCase):
    def test_prepare_installs_the_pinned_archives_and_binds_every_input(self):
        self.through_dist()
        self.assertEqual(self.prepare(), 0, self.said)
        record = self.kept("prepare.json")
        # The candidate: the parent's nine rows (the shared trust-src among them) byte for
        # byte, this host's eight added, one new manifest hash.
        parent, candidate = driver.text_rows(self.fixture.stage0.decode(), "parent"), self.candidate()
        for key, value in parent.items():
            if key.endswith("_channel_manifest_hash"):
                self.assertNotEqual(candidate[key], value)
            else:
                self.assertEqual(candidate[key], value, key)
        added = sorted(set(candidate) - set(parent))
        self.assertEqual(added, sorted(f"dist/{SEED_DATE}/{stem}-{SEED_VERSION}-trust-{HOST}.tar.xz"
                                       for stem in SEED_ARCHIVES))
        self.assertEqual(record["prepared"]["rows"], {"kept": 9, "added": added})
        output = self.plan.output_root() / "dist" / SEED_DATE
        self.assertEqual(sha(output / f"trust-src-{SEED_VERSION}-trust.tar.xz"),
                         self.fixture.rows[f"dist/{SEED_DATE}/trust-src-{SEED_VERSION}-trust.tar.xz"])
        self.assertEqual(candidate["compiler_channel_manifest_hash"],
                         sha(self.plan.output_root() / "dist" / "channel-rust-trust.toml"))
        # The shared archive was kept with builder-config excluded, and the reason recorded.
        [kept] = record["prepared"]["shared_kept"]["kept"]
        self.assertEqual([row["path"] for row in kept["excluded"]], ["builder-config"])
        self.assertIn("install.sh installs only the component directories", kept["excluded"][0]["reason"])
        # The seed is the pinned archives as installed: the dist's trustc carries the stock name
        # bin/rustdoc, which the pin strips, so the seed has none.
        with tarfile.open(self.plan.dist / f"trustc-{SEED_VERSION}-trust-{HOST}.tar.xz") as archive:
            self.assertIn(f"trustc-{SEED_VERSION}-trust-{HOST}/trustc/bin/rustdoc", archive.getnames())
        self.assertFalse((self.plan.seed / "bin" / "rustdoc").exists())
        self.assertEqual((self.plan.seed / "bin" / "trustdoc").read_bytes(), b"\x7fELF trustdoc")
        self.assertEqual(record["seed"]["tree"], driver.tree_identity(self.plan.seed, "seed"))
        self.assertEqual(record["seed"]["installer_bookkeeping"],
                         ["lib/rustlib/components", "lib/rustlib/manifest-targo", "lib/rustlib/manifest-trust-std-"
                          f"{HOST}", "lib/rustlib/manifest-trustc", "lib/rustlib/manifest-trustc-dev",
                          "lib/rustlib/manifest-trustfmt", "lib/rustlib/rust-installer-version"])
        # Every input, by digest.
        self.assertEqual(record["parent"]["commit"], PARENT_COMMIT)
        self.assertEqual(record["parent"]["src_stage0_sha256"], hashlib.sha256(self.fixture.stage0).hexdigest())
        self.assertEqual(record["parent"]["manifest_sha256"], hashlib.sha256(self.fixture.manifest).hexdigest())
        self.assertEqual({row["name"]: row["sha256"] for row in record["cohort"]["archives"]},
                         {Path(key).name: value for key, value in self.fixture.rows.items()})
        self.assertEqual(record["dist"]["sha256"], sha(self.plan.dist_record()))
        self.assertEqual(record["producer"]["stage2_manifest"]["sha256"], sha(self.plan.manifest_path("p")))
        self.assertEqual(record["driver"]["prepare.py"], sha(driver.PREPARE_PY))
        # What made prepared/, as made-by.json says, and the tree validate-seed examined.
        self.assertEqual(record["prepared"]["made_by"], {
            "schema": "trust-fixed-point-linux-seed-prepared-maker-v1", "prepare.py": sha(driver.PREPARE_PY),
            "admitted_dist": sha(self.plan.prepare_dir() / "admit-dist" / "seed-inputs.json"),
            "dist_record": sha(self.plan.dist_record()), "parent_commit": PARENT_COMMIT})
        surface_tree = json.loads(Path(record["surface"]["path"]).read_text())["tree"]
        self.assertEqual({key: surface_tree[key] for key in ("entries", "sha256")}, record["seed"]["tree"])
        self.assertEqual(record["inputs_sha256"], sha(self.plan.inputs_file()))
        pins = driver.pinned_rows(candidate)
        self.assertEqual({row["filename"]: row["sha256"] for row in record["admitted_pinned"]["artifacts"]},
                         {Path(key).name: value for key, value in pins.items() if key.endswith(f"-{HOST}.tar.xz")
                          and Path(key).name.split(f"-{SEED_VERSION}-")[0] in driver.support().COMPONENTS})
        self.assertEqual({row["name"]: row["sha256"] for row in record["prepared"]["archives"]},
                         {Path(key).name: value for key, value in pins.items()})
        for part in ("surface", "members"):
            self.assertEqual(record[part]["sha256"], sha(Path(record[part]["path"])))
        self.assertEqual(record["members"]["counts"]["differs"], 0)
        self.assertEqual(record["members"]["counts"]["none_by_kind"], {"elf": 0, "ar": 0, "other": 0})
        self.assertGreater(record["carried_compared_files"], 0)
        table = json.loads((self.plan.prepare_dir() / "archive-members.json").read_text())
        self.assertEqual(len(table["archives"]), 9)
        self.assertEqual(sum(1 for row in table["archives"] if row.get("shared")), 1)
        # Done once: a second run repeats nothing; status says so; the fixed point builds from it.
        calls = self.plan.log()
        self.said.clear()
        self.assertEqual(self.prepare(), 0)
        self.assertEqual(self.plan.log(), calls)
        self.assertRegex(self.said[0], r"prepare: already done .*17 archives.*not repeated")
        status = driver.status_lines(self.plan)
        self.assertIn(f"  prepare      done: the parent's 9 rows kept, 8 added; "
                      f"{record['members']['counts']['same']} archive files are the producer's rows "
                      f"({self.plan.prepare_record()})", status)
        self.plan.args.stage0 = None
        self.assertEqual(driver.stage0_source(self.plan, "fixed-point"), self.plan.seed)
        self.assertEqual(driver.stage0_source(self.plan, "control"), self.plan.seed)


    def test_prepare_admits_only_a_dist_that_finished_clean(self):
        self.assertEqual(self.setup_root(), 0)
        self.refused(r"prepare admits the producer's dist, and there is no clean producer build .*Run: python3 .* "
                     "build --role producer", self.prepare)
        self.assertEqual(self.build("producer"), 0)
        self.refused(r"dist is not done \(.*kept/dist.json is not there\)\. Nothing was started\. Run: python3 .* dist",
                     self.prepare)
        self.assertEqual(self.dist(), 0)
        for name, pattern in (("dist.not-clean.json", r"dist ran and is not usable \(.*dist.not-clean.json\)"),
                              ("p-after-dist.stage2.json", r"the producer's stage2 moved during dist \(.*p-after-dist.stage2.json\)")):
            with self.subTest(name):
                (self.plan.kept / name).write_text("{}")
                self.refused(pattern + r": the archives are not known to be of the compared tree\. Nothing was "
                             "started", self.prepare)
                (self.plan.kept / name).unlink()
        put(self.plan.dist / "stray.tar.xz", "x")
        self.refused(r"dist is not the dist .*dist.json records, file for file\. Nothing was started", self.prepare)
        (self.plan.dist / "stray.tar.xz").unlink()
        # A dist record that is not a clean dist of this commit on this host.
        dist_json = self.plan.dist_record().read_bytes()
        for field, value in (("problems", ["one"]), ("host", "x86_64-unknown-linux-gnu"), ("commit", "f" * 40),
                             ("schema", "another-schema")):
            with self.subTest(field):
                self.plan.dist_record().write_text(json.dumps({**json.loads(dist_json), field: value}))
                try:
                    self.refused(rf"dist.json is not the record of a clean dist of {SOURCE.commit[:10]} on {HOST} .*"
                                 r"Nothing was started", self.prepare)
                finally:
                    self.plan.dist_record().write_bytes(dist_json)
        self.assertFalse(self.plan.prepare_dir().exists())
        self.assertIn("  prepare      not started", driver.status_lines(self.plan))
        self.assertEqual(driver.status_lines(self.plan)[-2], "next: " + shlex.join(
            driver.command_line(self.plan, "prepare")))

    def test_prepare_refuses_a_parent_or_cohort_it_cannot_bind(self):
        self.through_dist()
        stage0, manifest_path = self.fixture.stage0.decode(), driver.PARENT_MANIFEST.format(date=SEED_DATE)
        darwin = f"dist/{SEED_DATE}/trustc-{SEED_VERSION}-trust-{DARWIN}.tar.xz"
        cohort = Path(self.tmp.name) / "cohort"
        shutil.copytree(self.fixture.cohort, cohort)
        self.plan.args.cohort = cohort
        # A parent whose manifest (bound by the hash its src/stage0 pins) lists this host as built.
        listed = stage0_prepare.tomllib.loads(self.fixture.manifest.decode())
        listed["pkg"]["trustc"]["target"][HOST] = {
            "available": True, "xz_url": f"https://elsewhere.invalid/trustc-{SEED_VERSION}-trust-{HOST}.tar.xz",
            "xz_hash": "a" * 64}
        listed_manifest = stage0_prepare.dump_toml(listed).encode()
        listed_stage0 = stage0.replace(hashlib.sha256(self.fixture.manifest).hexdigest(),
                                       hashlib.sha256(listed_manifest).hexdigest()).encode()
        # The same, with this host built under another package than trustc.
        std_listed = stage0_prepare.tomllib.loads(self.fixture.manifest.decode())
        std_listed["pkg"]["trust-std"]["target"][HOST] = {
            "available": True, "xz_url": f"https://elsewhere.invalid/trust-std-{SEED_VERSION}-trust-{HOST}.tar.xz",
            "xz_hash": "a" * 64}
        std_manifest = stage0_prepare.dump_toml(std_listed).encode()
        std_stage0 = stage0.replace(hashlib.sha256(self.fixture.manifest).hexdigest(),
                                    hashlib.sha256(std_manifest).hexdigest()).encode()
        name = Path(darwin).name

        def parent_field(key: str, value: str | None) -> None:
            pattern = re.compile(rf"^{re.escape(key)}\s*=.*\n", re.M)
            self.assertEqual(len(pattern.findall(stage0)), 1, key)
            self.plan.parent_files["src/stage0"] = pattern.sub("" if value is None else f"{key} = {value}\n",
                                                               stage0).encode()

        def linked_cohort_archive() -> None:
            # The pinned bytes, behind a link: check_cohort reads only a regular file.
            (cohort / name).rename(cohort / "real")
            (cohort / name).symlink_to(cohort / "real")

        cases = (
            ("a parent whose rustfmt is another commit", lambda: parent_field("rustfmt_git_commit_hash", "f" * 40),
             rf"the parent 1234567890 pins rustfmt_git_commit_hash = '{'f' * 40}', and this root builds "),
            ("a parent whose compiler_version is not a -trust version",
             lambda: parent_field("compiler_version", SEED_VERSION),
             r"the parent 1234567890's src/stage0 declares no usable compiler_date, compiler_version or dist_server"),
            ("a parent whose compiler_date is not a date", lambda: parent_field("compiler_date", "2026-11"),
             r"the parent 1234567890's src/stage0 declares no usable compiler_date, compiler_version or dist_server"),
            ("a parent with no dist_server", lambda: parent_field("dist_server", None),
             r"the parent 1234567890's src/stage0 declares no usable compiler_date, compiler_version or dist_server"),
            ("a parent that pins a row outside its date",
             lambda: self.plan.parent_files.update({"src/stage0": (stage0 + f"dist/2026-11-08/trustc-{SEED_VERSION}-"
                                                                   f"trust-{DARWIN}.tar.xz={'0' * 64}\n").encode()}),
             rf"the parent 1234567890's src/stage0 pins no archive, or one outside dist/{SEED_DATE}/\. Nothing was "
             "started"),
            ("a parent of another version", lambda: setattr(
                self.plan, "version", lambda: self.plan.script("version", "print('0.14.0')\n")),
             rf"the parent pins compiler_version {SEED_VERSION}-trust, and the checkout is 0\.14\.0\. Nothing was "
             "started"),
            ("a cohort archive that is a link to the pinned bytes", linked_cohort_archive,
             rf"the pinned archive {name} is not a regular file in .*cohort\. Nothing was started"),
            ("a parent manifest that lists this host as built under trust-std",
             lambda: self.plan.parent_files.update({"src/stage0": std_stage0, manifest_path: std_manifest}),
             rf"already lists {HOST} as built \(pkg\.trust-std\.target\.{HOST} and 0 more\)"),
            ("a cohort archive with other bytes", lambda: (cohort / Path(darwin).name).write_bytes(b"other"),
             rf"cohort/{Path(darwin).name} has sha256 [0-9a-f]{{64}}, and the parent 1234567890 pins "
             rf"{self.fixture.rows[darwin]}\. Nothing was started; fetch the pinned archive again"),
            ("a cohort archive that is missing", lambda: (cohort / Path(darwin).name).unlink(),
             rf"the pinned archive {Path(darwin).name} is not a regular file in .*cohort\. Nothing was started"),
            ("a parent that pins this host",
             lambda: self.plan.parent_files.update({"src/stage0": (stage0 + f"dist/{SEED_DATE}/trustc-{SEED_VERSION}-"
                                                                   f"trust-{HOST}.tar.xz={'0' * 64}\n").encode()}),
             rf"the parent 1234567890 already pins {HOST} .*Nothing was started; a host is added to a pin once"),
            ("a parent of another commit",
             lambda: self.plan.parent_files.update({"src/stage0": stage0.replace(SOURCE.commit, "f" * 40).encode()}),
             rf"the parent 1234567890 pins compiler_git_commit_hash = '{'f' * 40}', and this root builds "),
            ("a manifest that is not the one the parent pins",
             lambda: self.plan.parent_files.update({manifest_path: self.fixture.manifest + b"\n"}),
             rf"{manifest_path} has sha256 [0-9a-f]{{64}}, and its src/stage0 pins compiler_channel_manifest_hash"),
            ("no manifest", lambda: self.plan.parent_files.pop(manifest_path),
             rf"{manifest_path} cannot be read at the parent 1234567890"),
            # Last: a case that is not refused leaves a record the cases after it would read.
            ("a parent manifest that lists this host as built",
             lambda: self.plan.parent_files.update({"src/stage0": listed_stage0, manifest_path: listed_manifest}),
             rf"the parent 1234567890's {manifest_path} already lists {HOST} as built \(pkg.trustc.target.{HOST} and "
             r"0 more\)\. Nothing was started; a host is added to a pin once"),
        )
        for what, change, pattern in cases:
            with self.subTest(what):
                change()
                try:
                    self.refused(pattern, self.prepare)
                    self.assertFalse((self.plan.prepare_dir() / "admit-dist").exists())
                    self.assertFalse(self.plan.prepared().exists())
                    self.assertFalse(self.plan.prepare_record().exists())
                finally:
                    shutil.rmtree(cohort)
                    shutil.copytree(self.fixture.cohort, cohort)
                    self.configure(self.plan)
                    self.plan.args.cohort = cohort
                    vars(self.plan).pop("version", None)
                    # A case that was not refused leaves no state the next case would read as its own.
                    for path in (self.plan.prepare_dir(), self.plan.prepared(), self.plan.root / "prepared.partial",
                                 self.plan.seed, self.plan.prepare_record()):
                        driver.remove_own(path)

    def test_prepare_resumes_where_it_stopped_and_redoes_only_an_unfinished_part(self):
        self.through_dist()
        self.plan.fail = {"validate-seed"}
        self.refused(r"validate-seed refused the installed seed .*seed: `.*` exited 1, and the last line it printed "
                     r"on stderr is: error: the stand-in was told to fail \(all of it: .*validate-seed.err", self.prepare)
        self.assertFalse(self.plan.prepare_record().exists())
        self.assertIn("  prepare      unfinished (there: admit-dist, prepared, admit-pinned, seed); the same command "
                      "resumes", driver.status_lines(self.plan))
        self.plan.args.stage0 = None
        self.refused(r"seed is not prepared", driver.stage0_source, self.plan, "fixed-point")
        # A seed this step did not start installing is not removed.
        (self.plan.prepare_dir() / "installed.json").unlink()
        put(self.plan.seed / "bin" / "left-over", "from the stopped install")
        self.refused(r"seed exists, and this step did not start installing it \(.*installing.json is not there\): "
                     r"prepare removes only an install of its own that stopped\. Nothing was changed", self.prepare)
        self.assertTrue((self.plan.seed / "bin" / "left-over").is_file())
        # An install of its own that stopped part way is removed and made again.
        driver.write_json(self.plan.prepare_dir() / "installing.json", {"admitted_sha256": "an earlier run"})
        # And a prepare.py run that stopped: its unfinished output root is removed by the next one.
        prepared = self.plan.prepared().rename(self.plan.root / "prepared.partial")
        put(prepared / "bootstrap" / "trust-stage0" / "half-written", "x")
        before = [line for line in self.plan.log() if line in ("stage-artifacts", "prepare.py", "install")]
        self.plan.fail = set()
        self.assertEqual(self.prepare(), 0, self.said)
        after = [line for line in self.plan.log() if line in ("stage-artifacts", "prepare.py", "install")]
        # admit-dist and admit-pinned were not admitted again; prepare.py ran again, and the five installs.
        self.assertEqual(after[len(before):], ["prepare.py"] + ["install"] * 5)
        self.assertEqual(before.count("stage-artifacts"), 2)
        self.assertFalse((self.plan.seed / "bin" / "left-over").exists())
        self.assertFalse((self.plan.prepare_dir() / "installing.json").exists())
        self.assertFalse((self.plan.root / "prepared.partial").exists())
        self.assertFalse((self.plan.output_root() / "half-written").exists())

    def test_prepare_refuses_a_candidate_that_is_not_the_parent_plus_this_host(self):
        self.through_dist()
        self.assertEqual(self.prepare(), 0, self.said)
        root = self.plan.output_root()
        output, generated = root / "dist" / SEED_DATE, self.plan.prepared() / "src-stage0"
        darwin = f"dist/{SEED_DATE}/trustc-{SEED_VERSION}-trust-{DARWIN}.tar.xz"
        linux = output / f"trustc-{SEED_VERSION}-trust-{HOST}.tar.xz"
        latest, dated = root / "dist" / "channel-rust-trust.toml", output / "channel-rust-trust.toml"
        admission, kept = root / "trust-stage0-admission.json", root / "trust-stage0-shared-kept.json"
        text, archive = generated.read_text(), linux.read_bytes()
        manifest = latest.read_text()
        new_hash, parent_hash = sha(latest), hashlib.sha256(self.fixture.manifest).hexdigest()
        handoff = root / "artifacts" / SOURCE.commit / f"trustc-dev-{SEED_VERSION}-trust-{HOST}.tar.xz"
        shared = f"trust-src-{SEED_VERSION}-trust.tar.xz"
        # Every file a case edits is put back after it (a case's own cleanup runs first).
        pinned_shared = output / shared
        saved = {path: path.read_bytes() for path in (generated, linux, latest, dated, admission, kept,
                                                    pinned_shared)}

        def edit_json(path: Path, change) -> None:
            value = json.loads(saved[path])
            change(value)
            path.write_text(json.dumps(value))

        def rebound(mutate):
            """The manifest edited, and every other place that names its digest (both
            manifests, the candidate's two hash rows, the admission) made to agree: only
            manifest_problems can see the edit."""
            def change() -> None:
                value = stage0_prepare.tomllib.loads(manifest)
                mutate(value)
                edited = stage0_prepare.dump_toml(value)
                digest = hashlib.sha256(edited.encode()).hexdigest()
                latest.write_text(edited)
                dated.write_text(edited)
                generated.write_text(text.replace(new_hash, digest))
                edit_json(admission, lambda record: record.update(manifest_hash=digest))
            return change

        def host_entry(value: dict) -> dict:
            return value["pkg"]["trustc"]["target"][HOST]

        def linked_archive() -> None:
            copy = Path(self.tmp.name) / linux.name
            copy.write_bytes(archive)
            linux.unlink()
            linux.symlink_to(copy)

        strays = (root / "stray-at-the-top.txt", handoff.with_name(handoff.name + ".orig"),
                  handoff.with_name("other.tar.xz"))
        cases = (
            ("a Darwin row moved", lambda: generated.write_text(text.replace(self.fixture.rows[darwin], "e" * 64)),
             None, rf"the parent's {darwin} = {self.fixture.rows[darwin]} is '{'e' * 64}' in the candidate"),
            ("an archive with other bytes", lambda: linux.write_bytes(archive + b"\0"), None,
             rf"{linux.name} has sha256 [0-9a-f]{{64}}, and the candidate pins"),
            ("a stray file", lambda: put(output / f"{shared}.this-run", "x"), (output / f"{shared}.this-run").unlink,
             r"the output root holds files prepare.py does not write: \['dist/2026-11-07/trust-src-0.13.0-trust"
             r".tar.xz.this-run'\]"),
            ("a Darwin manifest table moved", lambda: latest.write_text(manifest.replace(self.fixture.rows[darwin],
                                                                                         "e" * 64)),
             None, rf"pkg.trustc.target.{DARWIN} changed"),
            # The candidate's manifest hash rows and its added rows.
            ("the parent's manifest hash in the candidate", lambda: generated.write_text(text.replace(new_hash,
                                                                                                    parent_hash)),
             None, rf"compiler_channel_manifest_hash is '{parent_hash}': not the new manifest's sha256 {new_hash}"),
            ("the parent's manifest as the output's",
             lambda: (latest.write_bytes(self.fixture.manifest), dated.write_bytes(self.fixture.manifest),
                      generated.write_text(text.replace(new_hash, parent_hash)),
                      edit_json(admission, lambda record: record.update(manifest_hash=parent_hash))),
             None, rf"compiler_channel_manifest_hash is '{parent_hash}': not the new manifest's sha256 {parent_hash}"),
            ("a row that is not this host's", lambda: generated.write_text(text.rstrip("\n") + "\nextra_key=1\n"),
             None, r"the candidate adds \[[^]]*'extra_key'\], and this host adds exactly \["),
            # The dated manifest, the admission and the kept record, each bound to the candidate.
            ("a dated manifest that is not the latest", lambda: dated.write_bytes(saved[dated] + b"\n"), None,
             r"the dated channel manifest is not the latest one"),
            ("an admission payload with other bytes",
             lambda: edit_json(admission, lambda record: record["payloads"][0].update(sha256="0" * 64)), None,
             r"trust-stage0-admission.json does not admit exactly the candidate's archives and manifest"),
            ("an admission of another manifest",
             lambda: edit_json(admission, lambda record: record.update(manifest_hash="0" * 64)), None,
             r"trust-stage0-admission.json does not admit exactly the candidate's archives and manifest"),
            ("a kept record with another pinned digest",
             lambda: edit_json(kept, lambda record: record["kept"][0].update(pinned_sha256="0" * 64)), None,
             rf"trust-stage0-shared-kept.json does not say {shared} was kept with at most builder-config excluded"),
            ("a kept record that excluded more than builder-config",
             lambda: edit_json(kept, lambda record: record["kept"][0]["excluded"].append({"path": "trust-src/x"})),
             None, rf"trust-stage0-shared-kept.json does not say {shared} was kept with at most builder-config "
                   "excluded"),
            # The kept record is in prepared/, which made-by.json does not bind: its comparison is made
            # again from this host's dist and the pinned archive, field by field.
            ("a kept record rewritten to another comparison",
             lambda: edit_json(kept, lambda record: record["kept"][0].update(
                 excluded=[], this_run_sha256="0" * 64, members=1, pinned_member_table_sha256="0" * 64)), None,
             rf"trust-stage0-shared-kept.json records {re.escape(shared)} with another excluded, members, "
             r"pinned_member_table_sha256, this_run_sha256 than its comparison made again from .*dist and the "
             "pinned archive"),
            *((f"a kept record with another {key}",
               lambda key=key, value=value: edit_json(kept, lambda record: record["kept"][0].update({key: value})),
               None, rf"trust-stage0-shared-kept.json records {re.escape(shared)} with another {key} than its "
                     "comparison made again")
              for key, value in (("this_run_sha256", "0" * 64), ("members", 1),
                                 ("pinned_member_table_sha256", "0" * 64), ("excluded", []))),
            # Each binding of the shared row and of the archive listing, by its own words.
            # A pinned shared archive the comparison cannot read again is a refusal in words.
            *((f"a pinned shared archive that is {what}", lambda data=data: pinned_shared.write_bytes(data), None,
               rf"the comparison of {re.escape(shared)} with this host's dist could not be made again \(")
              for what, data in (("not an xz", b"not an archive"),
                                 ("cut short", saved[pinned_shared][:len(saved[pinned_shared]) // 2]))),
            ("the shared row moved in the candidate",
             lambda: generated.write_text(text.replace(self.fixture.rows[f"dist/{SEED_DATE}/{shared}"], "e" * 64)),
             None, rf"the shared {re.escape(shared)} is not the parent's pinned bytes in the candidate"),
            ("an archive the candidate pins that is not there", linux.unlink, None,
             rf"{re.escape(str(output))} holds 16 archives, and the candidate pins 17 \(other: "
             rf"\['{re.escape(linux.name)}'\]\)"),
            # A pinned archive that is a link is a refusal in words, not a KeyError.
            ("a pinned archive that is a link", linked_archive, linux.unlink,
             rf"{re.escape(str(linux))} is not a regular file \(prepare.py writes each pinned archive as one\)"),
            # Strays: anywhere in the output root, of any kind.
            *((f"a stray file at {path.relative_to(root)}", lambda path=path: put(path, "x"), path.unlink,
               rf"the output root holds files prepare.py does not write: \['{path.relative_to(root).as_posix()}'\]")
              for path in strays),
            ("a directory prepare.py does not make", lambda: (root / "dist" / "extra").mkdir(),
             (root / "dist" / "extra").rmdir,
             r"the output root holds directories prepare.py does not make: \['dist/extra'\]"),
            ("a link to a directory", lambda: (output / "elsewhere").symlink_to(Path(self.tmp.name)),
             (output / "elsewhere").unlink,
             r"the output root holds links, which prepare.py does not write: \['dist/2026-11-07/elsewhere'\]"),
            ("a link to a file", lambda: (root / "linked.json").symlink_to(admission), (root / "linked.json").unlink,
             r"the output root holds links, which prepare.py does not write: \['linked.json'\]"),
            # Each check of manifest_problems alone: the edited manifest is bound everywhere else.
            ("the manifest's date", rebound(lambda value: value.update(date="2026-11-08")), None,
             r"the manifest's date changed"),
            ("an extra package",
             rebound(lambda value: value["pkg"].update({"extra-tool": {"version": value["pkg"]["trustc"]["version"]}})),
             None, r"the manifest's packages changed: \['extra-tool'\]"),
            ("pkg.trustc's version", rebound(lambda value: value["pkg"]["trustc"].update(version="9.9.9")), None,
             r"pkg\.trustc changed outside its targets"),
            ("the shared '*' entry",
             rebound(lambda value: value["pkg"]["trust-src"]["target"]["*"].update(xz_hash="e" * 64)), None,
             r"pkg\.trust-src\.target\.\* changed"),
            ("this host's xz_hash", rebound(lambda value: host_entry(value).update(xz_hash="e" * 64)), None,
             rf"pkg\.trustc\.target\.{HOST} is not the archive the candidate pins"),
            ("this host's xz_url on another server",
             rebound(lambda value: host_entry(value).update(
                 xz_url="https://elsewhere.invalid/dist/" + host_entry(value)["xz_url"].split("/dist/", 1)[1])),
             None, rf"pkg\.trustc\.target\.{HOST} is not the archive the candidate pins"),
        )
        self.plan.prepare_record().unlink()
        for what, change, cleanup, pattern in cases:
            with self.subTest(what):
                try:
                    change()
                    text_ = self.refused(r"the prepared seed in .*prepared is not the parent's pin plus this host: .*"
                                         + pattern, self.prepare)
                    self.assertIn("Nothing was installed from it", text_)
                    self.assertFalse(self.plan.prepare_record().exists())
                finally:
                    if cleanup is not None:
                        cleanup()
                    for path, data in saved.items():
                        path.write_bytes(data)
                    # A missed refusal would leave a record that every later case would read as done.
                    self.plan.prepare_record().unlink(missing_ok=True)
        self.assertEqual(self.prepare(), 0)

    def test_prepare_refuses_archives_that_are_not_the_producers_compared_tree(self):
        for what, stage2, pattern in (
                ("no row for an elf file", {k: v for k, v in STAGE2_SEED.items() if k != "bin/trust-analyzer"},
                 rf"trust-analyzer-{SEED_VERSION}-trust-{HOST}.tar.xz ships the elf file bin/trust-analyzer, and the "
                 "producer's stage2 has no row at that path"),
                ("another tool's bytes", {**STAGE2_SEED, "bin/tippy": "\x7fELF tippy, rebuilt"},
                 rf"tippy-{SEED_VERSION}-trust-{HOST}.tar.xz ships bin/tippy with other bytes than the producer's "
                 "stage2 row at that path"),
                # An ar file is code too, and libexec/ is joined as bin/ and lib/ are.
                ("no row for an ar file",
                 {k: v for k, v in STAGE2_SEED.items() if k != f"lib/rustlib/{HOST}/lib/librustc_middle-fixture.rlib"},
                 rf"trustc-dev-{SEED_VERSION}-trust-{HOST}.tar.xz ships the ar file lib/rustlib/{HOST}/lib/"
                 "librustc_middle-fixture.rlib, and the producer's stage2 has no row at that path"),
                ("no row for a libexec file",
                 {k: v for k, v in STAGE2_SEED.items() if k != "libexec/trust-analyzer-proc-macro-srv"},
                 rf"trustc-{SEED_VERSION}-trust-{HOST}.tar.xz ships the elf file libexec/trust-analyzer-proc-macro-srv, "
                 "and the producer's stage2 has no row at that path")):
            with self.subTest(what), tempfile.TemporaryDirectory() as tmp:
                self.root = Path(tmp).resolve() / "root"
                self.plan = FakePlan(arguments(self.root))
                self.configure(self.plan)
                self.plan.stage2_for.update({"p-build": stage2, "p-full": stage2})
                self.through_dist()
                text = self.refused(r"the pinned archives or the seed installed from them are not the producer's "
                                    r"compared tree: .*" + pattern, self.prepare)
                self.assertIn("No prepare record was written, so no role builds from", text)
                self.assertFalse(self.plan.prepare_record().exists())
                self.assertTrue((self.plan.prepare_dir() / "archive-members.json").is_file())

    def test_a_new_install_is_validated_again(self):
        # validate-seed examined one install; the seed installed again must not inherit its surface.
        self.through_dist()
        self.plan.fail = {"verify-archives-carry-compared"}
        self.refused(r"do not carry the producer's compared bytes", self.prepare)
        surface = self.plan.prepare_dir() / "seed-surface.json"
        self.assertTrue(surface.is_file())
        self.assertEqual(self.plan.log().count("validate-seed"), 1)
        # The refusals' own way to redo the seed: it and its marker moved aside.
        self.plan.seed.rename(self.plan.root / "seed.aside")
        (self.plan.prepare_dir() / "installed.json").unlink()
        self.plan.fail = set()
        self.assertEqual(self.prepare(), 0, self.said)
        self.assertEqual(self.plan.log().count("install"), 10)
        self.assertEqual(self.plan.log().count("validate-seed"), 2)
        record = self.kept("prepare.json")
        tree = json.loads(surface.read_text())["tree"]
        self.assertEqual({key: tree[key] for key in ("entries", "sha256")}, record["seed"]["tree"])
        self.assertEqual(record["surface"]["sha256"], sha(surface))

    def test_a_surface_of_another_tree_is_not_adopted(self):
        self.through_dist()
        self.plan.fail = {"verify-archives-carry-compared"}
        self.refused(r"do not carry the producer's compared bytes", self.prepare)
        self.plan.fail = set()
        surface = self.plan.prepare_dir() / "seed-surface.json"
        was = json.loads(surface.read_text())
        for what, text in (("another digest", json.dumps({**was, "tree": {**was["tree"], "sha256": "0" * 64}})),
                           ("another entry count", json.dumps({**was, "tree": {**was["tree"], "entries": 1}})),
                           ("no tree", json.dumps({key: item for key, item in was.items() if key != "tree"})),
                           ("not JSON", "not json")):
            with self.subTest(what):
                surface.write_text(text)
                self.refused(r"seed-surface.json is validate-seed's surface of another tree .*validate-seed did not "
                             r"examine this seed\. No prepare record was written; the seed and .*prepared are kept\. "
                             r"Move .*seed-surface.json aside and run prepare again", self.prepare)
                self.assertFalse(self.plan.prepare_record().exists())
        surface.unlink()
        self.assertEqual(self.prepare(), 0, self.said)
        self.assertEqual(self.plan.log().count("validate-seed"), 2)

    def test_a_prepared_made_by_other_inputs_is_not_adopted(self):
        self.through_dist()
        self.assertEqual(self.prepare(), 0, self.said)
        self.plan.prepare_record().unlink()
        made_by = self.plan.prepared() / "made-by.json"
        was = made_by.read_bytes()
        cases = [(f"another {key}", lambda key=key: made_by.write_text(json.dumps({**json.loads(was), key: "0" * 64})),
                  rf"made-by.json differs in {re.escape(key)}\)")
                 for key in ("prepare.py", "admitted_dist", "dist_record", "parent_commit")]
        cases += [("a key it does not have", lambda: made_by.write_text(json.dumps({**json.loads(was), "extra": 1})),
                   r"made-by.json differs in extra\)"),
                  ("an unreadable record of its maker", lambda: made_by.write_text("not json"),
                   r"made-by.json is not a JSON object\)"),
                  ("no record of its maker", made_by.unlink, r"made-by.json is not there\)")]
        for what, change, pattern in cases:
            with self.subTest(what):
                change()
                try:
                    self.refused(r"prepared was not made by this run's prepare.py, admitted dist, dist record and "
                                 rf"parent \(.*{pattern}\. Nothing was changed or installed\. Move .*prepared aside and "
                                 r"run prepare again", self.prepare)
                    self.assertFalse(self.plan.prepare_record().exists())
                finally:
                    made_by.write_bytes(was)
        # The way out the refusal names: prepared/ moved aside is made again by prepare.py.
        before = self.plan.log().count("prepare.py")
        self.plan.prepared().rename(self.plan.root / "prepared.aside")
        self.assertEqual(self.prepare(), 0, self.said)
        self.assertEqual(self.plan.log().count("prepare.py"), before + 1)

    def test_prepare_refuses_an_admitted_record_that_is_not_this_dist(self):
        self.through_dist()
        self.plan.fail = {"validate-seed"}
        self.refused(r"validate-seed refused the installed seed", self.prepare)
        self.plan.fail = set()
        inputs = self.plan.prepare_dir() / "admit-dist" / "seed-inputs.json"
        was = inputs.read_bytes()
        admitted = json.loads(was)
        for what, value, pattern in (
                ("another host", {**admitted, "host": "x86_64-unknown-linux-gnu"},
                 rf"seed-inputs.json admits {SOURCE.commit} on x86_64-unknown-linux-gnu, not {SOURCE.commit} on "
                 rf"{HOST}\. Nothing was installed"),
                ("another commit", {**admitted, "source_commit": "f" * 40},
                 rf"seed-inputs.json admits {'f' * 40} on {HOST}, not {SOURCE.commit} on {HOST}\. Nothing was "
                 "installed"),
                ("an archive it did not admit",
                 {**admitted, "artifacts": [{**admitted["artifacts"][0], "sha256": "0" * 64},
                                            *admitted["artifacts"][1:]]},
                 r"is not the archive .*admit-dist/seed-inputs.json admitted \(sha256 0{64}\)\. Nothing was installed; "
                 r"move .*admit-dist aside and run prepare again")):
            with self.subTest(what):
                inputs.write_text(json.dumps(value))
                try:
                    self.refused(pattern, self.prepare)
                    self.assertFalse(self.plan.prepare_record().exists())
                finally:
                    inputs.write_bytes(was)
        self.assertEqual(self.prepare(), 0, self.said)

    def test_a_step_that_leaves_a_file_in_the_seed_is_refused(self):
        # validate-seed runs the seed's tools: one that writes into the seed after it was measured.
        self.plan.validate_seed_then = "(pathlib.Path(sys.argv[4]) / 'bin' / 'left-behind').write_bytes(b'x')\n"
        self.through_dist()
        text = self.refused(r"the pinned archives or the seed installed from them are not the producer's compared "
                            r"tree: ", self.prepare)
        self.assertIn("bin/left-behind is in the seed and no pinned archive installs it", text)
        self.assertIn("seed changed after it was installed (validate-seed runs its tools)", text)
        self.assertIn("No prepare record was written, so no role builds from", text)
        self.assertFalse(self.plan.prepare_record().exists())

    def test_a_step_that_reaches_a_stock_tool_name_is_refused(self):
        # What the trap shim writes when a prepare helper runs a stock tool name (appended here
        # directly, so no tool of this host runs).
        trap = self.plan.ledger / "trap.log"
        self.plan.validate_seed_then = f"open({str(trap)!r}, 'a').write('rustc -vV\\n')\n"
        self.through_dist()
        self.refused(r"a step of prepare reached a stock Rust tool name: .*trap.log grew by 1 line\(s\) \(the first "
                     r"new: 'rustc -vV'\)\. No prepare record was written", self.prepare)
        self.assertFalse(self.plan.prepare_record().exists())

    def test_a_seed_that_changed_after_prepare_is_no_stage0(self):
        self.through_dist()
        self.assertEqual(self.prepare(), 0, self.said)
        self.plan.args.stage0 = None
        (self.plan.seed / "bin" / "trustc").write_bytes(b"\x7fELF another compiler")
        self.refused(r"seed is not the tree .*prepare.json records as the pinned archives installed\. Nothing was "
                     "started", driver.stage0_source, self.plan, "fixed-point")
        self.refused(r"seed is not the seed .*prepare.json records\. Nothing was changed", self.prepare)
        record = self.kept("prepare.json")
        # A record of another schema, commit, host or root is no seed for this root's roles.
        for key, value in (("commit", "0" * 40), ("schema", "another-schema"), ("host", "x86_64-unknown-linux-gnu"),
                           ("root", "/elsewhere")):
            with self.subTest(key):
                driver.write_json(self.plan.prepare_record(), {**record, key: value})
                self.refused(rf"prepare.json has {key} = {re.escape(repr(value))}, not .*Nothing was started",
                             driver.stage0_source, self.plan, "control")

    def test_a_copy_of_a_pinned_archive_that_is_not_its_bytes_is_refused(self):
        self.through_dist()
        with mock.patch.object(driver.shutil, "copyfile", lambda source, target: Path(target).write_bytes(b"x")):
            self.refused(r"the copy .*prepared\.partial/.* is not the pinned archive \(sha256 [0-9a-f]{64}\)\. The "
                         r"unfinished .*prepared\.partial is removed by the next run", self.prepare)
        self.assertFalse(self.plan.prepared().exists())
        self.assertFalse(self.plan.prepare_record().exists())
        # The way on the refusal names: the next run removes the partial and copies again.
        self.assertEqual(self.prepare(), 0, self.said)

    def test_prepare_needs_the_producers_stage2_manifest(self):
        self.through_dist()
        self.plan.manifest_path("p").unlink()
        self.refused(r"the producer's stage2 manifest .* is not there\. Nothing was started", self.prepare)
        self.assertFalse(self.plan.prepare_dir().exists())

    def test_a_seed_that_is_not_the_tree_its_marker_records_is_not_installed_over(self):
        self.through_dist()
        self.plan.fail = {"validate-seed"}
        self.refused(r"validate-seed refused", self.prepare)
        self.plan.fail = set()
        (self.plan.seed / "bin" / "trustc").write_bytes(b"\x7fELF another compiler")
        self.refused(r"seed is not the tree .*installed\.json records \(or was installed from other admitted "
                     r"archives\)\. Nothing was changed\. Move the seed and the marker aside and run prepare again",
                     self.prepare)
        self.assertEqual((self.plan.seed / "bin" / "trustc").read_bytes(), b"\x7fELF another compiler")
        self.assertFalse(self.plan.prepare_record().exists())

    def test_two_pinned_archives_that_install_one_path_with_other_bytes_are_refused(self):
        # targo's table, as archive_members reads it, also installs bin/trustc with other bytes.
        self.through_dist()
        real = driver.archive_members

        def members(path: Path) -> dict:
            table = real(path)
            if path.name == f"targo-{SEED_VERSION}-trust-{HOST}.tar.xz":
                table["installed"] = [*table["installed"], {**table["installed"][0], "path": "bin/trustc",
                                                            "sha256": "0" * 64}]
            return table

        with mock.patch.object(driver, "archive_members", members):
            text = self.refused(r"the pinned archives or the seed installed from them are not the producer's "
                                r"compared tree: .*two pinned archives install bin/trustc with different bytes",
                                self.prepare)
        self.assertIn("No prepare record was written", text)
        self.assertFalse(self.plan.prepare_record().exists())


def tiny_archive(directory: Path, members: dict[str, object],
                 name: str = f"trustc-{SEED_VERSION}-trust-{HOST}.tar.xz") -> Path:
    """A .tar.xz whose package root is its name. A member is bytes, None for a
    directory, ("symlink", target) or ("hardlink", member name)."""
    prefix = name.removesuffix(".tar.xz")
    with tarfile.open(directory / name, "w:xz") as archive:
        info = tarfile.TarInfo(prefix)
        info.type, info.mode = tarfile.DIRTYPE, 0o755
        archive.addfile(info)
        for member, data in members.items():
            info = tarfile.TarInfo(f"{prefix}/{member}")
            if data is None:
                info.type, info.mode = tarfile.DIRTYPE, 0o755
                archive.addfile(info)
            elif isinstance(data, tuple):
                info.type = tarfile.SYMTYPE if data[0] == "symlink" else tarfile.LNKTYPE
                info.linkname = data[1]
                archive.addfile(info)
            else:
                info.size, info.mode = len(data), 0o755
                archive.addfile(info, io.BytesIO(data))
    return directory / name


class SeedTableTests(unittest.TestCase):
    """archive_members and seed_problems on small trees: what install.sh installs is read
    by install.sh's own rules, and every seed file is a pinned member."""

    BASE = {"components": b"trustc\n", "trustc/manifest.in": b"file:bin/trustc\n",
            "trustc/bin/trustc": b"\x7fELF trustc"}

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.top = Path(self.tmp.name)

    def members(self, changes: dict[str, object]) -> Path:
        directory = Path(tempfile.mkdtemp(dir=self.top))
        return tiny_archive(directory, {**self.BASE, **changes})

    def test_an_archive_installer_installs_only_what_it_reads_as_written(self):
        table = driver.archive_members(self.members({}))
        self.assertEqual([row["path"] for row in table["installed"]], ["bin/trustc"])
        prefix = f"trustc-{SEED_VERSION}-trust-{HOST}"
        for what, changes, pattern in (
                # `read` without -r turns '.\.' into '..': install.sh copies pkgdir from outside the component.
                ("a line `read` rewrites", {"trustc/manifest.in": b"file:bin/trustc\ndir:.\\./pkgdir\n",
                                            "pkgdir/marker": b"outside the component"},
                 r"has the line 'dir:\.\\\\\./pkgdir' in .*trustc/manifest\.in, which is not a file: or dir: path "
                 r"install\.sh reads as written \(a backslash"),
                ("trailing blanks `read` drops", {"trustc/manifest.in": b"file:bin/trustc \n",
                                                  "trustc/bin/trustc ": b"\x7fELF not what is installed"},
                 r"has the line 'file:bin/trustc ' .*\(leading or trailing whitespace"),
                ("a dir: line that selects nothing", {"trustc/manifest.in": b"file:bin/trustc\ndir:share/none\n"},
                 r"lists the directory share/none in .*trustc/manifest\.in, and no member is below"),
                ("a symlink member", {"trustc/bin/alias": ("symlink", "../../../builder-config"),
                                      "trustc/manifest.in": b"file:bin/trustc\nfile:bin/alias\n"},
                 rf"has the member '{prefix}/trustc/bin/alias', a symlink to '\.\./\.\./\.\./builder-config': every "
                 "member must be a regular file or a directory"),
                ("a hardlink member", {"trustc/bin/alias": ("hardlink", f"{prefix}/trustc/bin/trustc"),
                                       "trustc/manifest.in": b"file:bin/trustc\nfile:bin/alias\n"},
                 rf"has the member '{prefix}/trustc/bin/alias', a hardlink to "),
                ("a '.' in a member name", {"trustc/./bin/x": b"\x7fELF x",
                                            "trustc/manifest.in": b"file:bin/trustc\nfile:./bin/x\n"},
                 r"or a name with an empty, '\.' or '\.\.' component"),
                ("a '.' component in a line", {"trustc/manifest.in": b"file:bin/trustc\ndir:.\n"},
                 r"has the line 'dir:\.' .*\(an empty or absolute path, or an empty, '\.' or '\.\.' component"),
                ("an absolute line", {"trustc/manifest.in": b"file:/etc/passwd\n"},
                 r"has the line 'file:/etc/passwd' .*\(an empty or absolute path"),
                ("a component that is not one directory", {"components": b"trustc ..\n"},
                 r"names the component '\.\.' in .*components, which is not one directory"),
                ("a glob in components", {"components": b"trustc *\n"},
                 r"components with bytes other than letters, digits, .* \(b'\*'\): install.sh splits it on space"),
                # install.sh splits components on space, tab and newline only: it reads one component,
                # 'trustc\x1cfoo', and installs its bin/trustc, not the one a split on \x1c compares.
                ("components split on \\x1c", {"components": b"trustc\x1cfoo\n", "foo/manifest.in": b"file:share/foo\n",
                                               "foo/share/foo": b"foo\n",
                                               "trustc\x1cfoo/manifest.in": b"file:bin/trustc\n",
                                               "trustc\x1cfoo/bin/trustc": b"\x7fELF not the compared bytes"},
                 rf"has {prefix}/components with bytes other than letters, digits, '\.', '_', '-', space, tab and "
                 r"newline \(b'\\x1c'\): install.sh splits it on space, tab and newline only"),
                # `read` drops a NUL: 'file:.\0./marker' is 'file:../marker' to install.sh.
                ("a NUL `read` drops", {"trustc/manifest.in": b"file:bin/trustc\nfile:.\x00./marker\n",
                                        "marker": b"the package root"},
                 r"has the line 'file:\.\\x00\./marker' .*\(a control or line-separator character\)"),
                # bootstrap's stage0 unpack extracts every member under the component, listed or not.
                ("an unlisted file under bin/", {"trustc/bin/hidden": b"\x7fELF never compared"},
                 r"carries 1 file\(s\) under .*trustc/\(bin\|lib\|libexec\)/ that no manifest.in line installs "
                 r"\(\['.*trustc/bin/hidden'\]\)"),
                ("an unlisted file under lib/", {"trustc/lib/libhidden.so": b"\x7fELF never compared"},
                 r"carries 1 file\(s\) under .*that no manifest.in line installs \(\['.*trustc/lib/libhidden.so'\]\)"),
                ("an unlisted file under libexec/", {"trustc/libexec/hidden": b"\x7fELF never compared"},
                 r"carries 1 file\(s\) under .*that no manifest.in line installs \(\['.*trustc/libexec/hidden'\]\)")):
            with self.subTest(what):
                with self.assertRaisesRegex(driver.Refusal, pattern) as caught:
                    driver.archive_members(self.members(changes))
                self.assertIn("No prepare record was written, so no role builds from the seed; the archive is kept "
                              "where it is. Next:", str(caught.exception))

    def test_join_members_joins_bin_lib_and_libexec_by_bytes_and_links_by_target(self):
        def row(path: str, kind: str, digest: str) -> dict:
            return {"path": path, "type": "file", "kind": kind, "sha256": digest, "link": None}

        archive = {"installed": [
            row("bin/a", "elf", "1" * 64), row("lib/b", "ar", "2" * 64), row("libexec/c", "elf", "3" * 64),
            row("share/d", "other", "4" * 64),
            {"path": "bin/x", "type": "symlink", "kind": None, "sha256": None, "link": "a"},
            {"path": "bin/y", "type": "symlink", "kind": None, "sha256": None, "link": "a"}]}
        stage2 = {"bin/a": {"kind": "file", "sha256": "1" * 64}, "libexec/c": {"kind": "file", "sha256": "0" * 64},
                  "bin/x": {"kind": "symlink", "target": "b"}, "bin/y": {"kind": "symlink", "target": "a"}}
        self.assertEqual([(item["path"], item["stage2"]) for item in driver.join_members(archive, stage2)],
                         [("bin/a", "same"), ("lib/b", "none"), ("libexec/c", "differs"), ("bin/x", "differs"),
                          ("bin/y", "same")])

    def test_seed_problems_names_every_file_that_is_not_a_pinned_member(self):
        seed = self.top / "seed"
        for path, data in (("bin/trustc", b"other"), ("bin/stray", b"x"), ("bin/same", b"same"),
                           ("lib/rustlib/components", b"trustc\n"),
                           (f"lib/rustlib/{HOST}/lib/libextra.rlib", b"!<arch>\n")):
            (seed / path).parent.mkdir(parents=True, exist_ok=True)
            (seed / path).write_bytes(data)

        def row(data: bytes) -> dict:
            return {"type": "file", "sha256": hashlib.sha256(data).hexdigest(), "link": None}

        problems, bookkeeping = driver.seed_problems(
            seed, {"bin/trustc": row(b"pinned"), "bin/same": row(b"same"), "bin/missing": row(b"m")})
        self.assertEqual(bookkeeping, ["lib/rustlib/components"])
        self.assertEqual(problems, [
            "bin/stray is in the seed and no pinned archive installs it",
            "bin/trustc is not the pinned member's bytes",
            f"lib/rustlib/{HOST}/lib/libextra.rlib is in the seed and no pinned archive installs it",
            "bin/missing is installed by a pinned archive and is not in the seed"])


# ---------------------------------------------------------------------------
# record (design step 13): the real seed_host_ledger.py and seed_fixed_point.py judge
# what `record` writes from a root built by the stand-ins above, with a candidate door.

ROOT_COMMIT = "6986546eaafc7620e49331269685dbd1b2900ba3"
ANCESTOR = "ec2b5c59f7ae81dc57dac2a3346cb4c0ef9fad0d"
R1_COMMIT = "20565c3255adf151f9eb920e89cdf83c38f84abe"
# The chain's commits are the design's (seed_fixed_point.CHAIN_COMMITS): the
# producer's stage0 is 6dad0d786f's build and the cross-check's 29ebb403de's.
PRODUCER_COMMIT, CROSS_COMMIT = "6dad0d786fa63187a5e611b440953c94a04cbfca", "29ebb403de7a102850d6cb10a62d5cc3baf723ed"
STAGE0_NAMES = ("bin/trustc", "bin/cargo", "bin/targo", "bin/trustdoc", "bin/trustfmt")
SCRIPT_IDENTITY = (
    "found = {rel: sha(top / rel) for rel in " + repr(STAGE0_NAMES) + " if (top / rel).is_file()}\n"
    "for pattern in ('lib/librustc_driver-*', 'lib/libstd-*'):\n"
    "    found.update({str(path.relative_to(top)): sha(path) for path in sorted(top.glob(pattern))\n"
    "                  if path.is_file()})\n")


def chain_compiler(top: Path, name: str, commit: str) -> Path:
    """A chain compiler as an admission sees it: drivers, its librustc_driver and std."""
    for rel in (*STAGE0_NAMES, f"lib/librustc_driver-{name}.so", f"lib/libstd-{name}.so"):
        put(top / rel, f"{rel} of the chain compiler {name}\n", 0o755)
    put(top / "commit", commit + "\n")
    return top


class RecordPlan(FakePlan):
    """FakePlan whose stand-ins write what the validator reads: complete run records,
    admissions of every identity file, the rung config's four stage0 keys and a
    seed surface of the installed seed's entrypoints."""

    def admit(self):
        return self.script("admit", (
            "top, source = pathlib.Path(sys.argv[2]), sys.argv[3]\n" + SCRIPT_IDENTITY +
            "commit = (top / 'commit').read_text().strip() if (top / 'commit').is_file() else source\n"
            "print(json.dumps({'kind': 'stage0-admission', 'schema': 'trust-seed-staircase-v1', 'stage0': str(top),\n"
            "                  'commit': commit, 'sha256': found}))\n"), str(self.stage0), self.commit)

    def config(self, out):
        return self.script("config", (
            "keys = (('rustc', 'trustc'), ('cargo', 'cargo'), ('rustdoc', 'trustdoc'), ('rustfmt', 'trustfmt'))\n"
            "text = 'include = [\"' + sys.argv[3] + '\"]\\n\\n[build]\\n'\n"
            "text += ''.join(key + ' = \"' + sys.argv[4] + '/bin/' + name + '\"\\n' for key, name in keys)\n"
            "pathlib.Path(sys.argv[2]).write_text(text)\nprint('{}')\n"),
            str(out), str(self.src / "bootstrap.toml"), str(self.stage0))

    def validate_seed(self, version, out):
        # The tree it saw, as the real one writes it: prepare refuses a surface of another tree.
        return self.script("validate-seed", (
            "import importlib.util\n"
            "sys.dont_write_bytecode = True  # nothing written beside the checkout's scripts\n"
            "spec = importlib.util.spec_from_file_location('mint_seed_support_stand_in', sys.argv[6])\n"
            "mint = importlib.util.module_from_spec(spec)\n"
            "sys.modules[spec.name] = mint\n"
            "spec.loader.exec_module(mint)\n"
            "seed = pathlib.Path(sys.argv[4])\n"
            "names = ('trustc', 'rustc', 'trustdoc', 'targo', 'cargo', 'trustfmt')\n"
            "surface = {'schema': 'trust-self-host-seed-surface-v1', 'host': sys.argv[5], 'source_version': sys.argv[3],\n"
            "           'tool_versions': {name: name + ' ' + sys.argv[3] + ' (fixture)' for name in\n"
            "                             ('trustc', 'targo', 'trustfmt')},\n"
            "           'entrypoint_sha256': {name: sha(seed / 'bin' / name) for name in names},\n"
            "           'tree': mint.seed_tree_fingerprint(seed)}\n"
            "pathlib.Path(sys.argv[2]).write_text(json.dumps(surface, sort_keys=True))\n"),
            str(out), version, str(self.seed), self.host, str(driver.MINT_SUPPORT))

    def run(self, label, words, admission):
        self.behaviour[label] = {"complete": True, **self.behaviour.get(label, {})}
        return super().run(label, words, admission)


class RecordCase(PrepareCase):
    """A root at <tmp>/<commit, ten digits> (the build root the validator holds the
    record to), built through the cross-check by RecordPlan."""

    plan_class = None   # RecordPlan, or a subclass of it (CommitCase)

    def setUp(self):
        super().setUp()
        self.parent = Path(self.tmp.name).resolve()
        self.root = self.parent / SOURCE.commit[:10]
        self.plan = (self.plan_class or RecordPlan)(arguments(self.root))
        self.configure(self.plan)
        self.producer = chain_compiler(self.parent / "chain" / "producer", "p", PRODUCER_COMMIT)
        self.cross = chain_compiler(self.parent / "chain" / "cross", "s", CROSS_COMMIT)
        self.plan.args.chain, self.plan.args.origin_provenance, self.plan.args.origin_config = self.chain_files()
        patcher = mock.patch.object(driver.validator(), "BUILD_ROOT_PARENT", str(self.parent))
        patcher.start()
        self.addCleanup(patcher.stop)
        invoker = os.umask(0o022)
        self.addCleanup(os.umask, invoker)

    def configure(self, plan) -> None:
        super().configure(plan)
        plan.stage2_for.update({"f-build": STAGE2_SEED, "s-build": STAGE2_SEED})

    def chain_files(self, *, producer: str | None = None) -> tuple[Path, list[Path], Path]:
        """The host chain's CHAIN-UNPINNED-ROOT.json and the origin's build stamps and
        config, as this host keeps them: they name the invoking account's home."""
        home = self.plan.account[0]
        made = self.parent / "chain-records"
        made.mkdir(exist_ok=True)

        def invocation(label, commit, stage0, before, after):
            return {"label": label, "commit": commit, "stage0_commit": stage0, "rc": 0, "no_stock_evidence": True,
                    "stage0_sha256": {"bin/trustc": before}, "produced": {"sha256": {"bin/trustc": after}},
                    "worktree": f"{home}/linux-selfhost/{label}"}

        producer = producer or sha(self.producer / "bin" / "trustc")
        cross = sha(self.cross / "bin" / "trustc")
        chain = {"NOT_A_LINEAGE_RECORD": "root is not a src/stage0-pinned extraction", "kind": "unpinned-chain-check",
                 "chain": {"root": {"commit": ROOT_COMMIT, "admission": {"sha256": {"bin/trustc": "1" * 64}}},
                           "rungs": [{"label": "r1", "invocations": [
                               invocation("r1", R1_COMMIT, ROOT_COMMIT, "1" * 64, "2" * 64)]},
                               {"label": "r2", "invocations": [
                                   invocation("r2", CROSS_COMMIT, R1_COMMIT, "2" * 64, cross)]},
                               {"label": "r3", "invocations": [
                                   invocation("r3", PRODUCER_COMMIT, CROSS_COMMIT, cross, producer)]}]}}
        path = made / "CHAIN-UNPINNED-ROOT.json"
        path.write_text(json.dumps(chain))
        stamps = []
        for name, commit in (("root", ROOT_COMMIT), ("ancestor", ANCESTOR)):
            stamps.append(put(made / f"{name}.PROVENANCE",
                              f"provenance_class=BUILD-STAMPED-CLEAN\nreported_commit={commit}\n"
                              f"seal_name=trust-{commit[:8]}\nbuild_stamp:argv=--config {home}/x.toml build\n"))
        config = put(made / "root-build.toml",
                     f'[build]\nrustc = "{home}/toolchains/trust-{ANCESTOR[:8]}/bin/trustc"\n')
        return path, stamps, config

    def dist(self, again: bool = False) -> int:
        """x.py dist writes its --config file into every archive as builder-config, so
        this run's trust-src carries the rung config the producer built with (the
        validator holds the excluded member to it)."""
        config = self.plan.rung_config()
        if config.is_file():
            own = self.parent / "this-run-dist"
            own.mkdir(exist_ok=True)
            archive = seed_archive(own, "trust-src", None, {SOURCE_FILE: b"pub fn core() {}\n"}, config.read_bytes())
            built = {**self.fixture.built,
                     "trust-src": {"*": (f"https://trust.invalid/{SEED_DATE}/{archive.name}", sha(archive))}}
            toml = own / "channel-rust-trust.toml"
            toml.write_text(stage0_prepare.dump_toml(channel(built, (DARWIN, HOST))))
            self.plan.archives = {**self.plan.archives, archive.name: str(archive)}
            self.plan.behaviour["p-manifest-tool"] = {"tool": f'#!/bin/sh\ncp {toml} "$1/channel-rust-trust.toml"\n'}
        return super().dist(again)

    def through_cross_check(self) -> None:
        self.assertEqual(self.setup_root(), 0)
        self.assertEqual(self.build("producer", self.producer), 0, self.said)
        self.assertEqual(self.dist(), 0, self.said)
        self.assertEqual(self.prepare(), 0, self.said)
        self.assertEqual(self.build("fixed-point"), 0, self.said)
        self.assertEqual(self.build("cross-check", self.cross), 0, self.said)

    def record(self) -> int:
        return self.quiet(driver.record_step, self.plan)

    def proofs(self) -> Path:
        return self.plan.output_root() / "host-proofs" / HOST


class RecordTests(RecordCase):
    def test_record_writes_the_host_record_and_its_evidence_and_is_not_repeated(self):
        self.through_cross_check()
        self.assertEqual(self.record(), 0, self.said)
        module, hosts = driver.validator(), driver.ledger()
        proofs = self.proofs()
        self.assertEqual(sorted(path.name for path in proofs.iterdir()),
                         ["SEED-FIXED-POINT", "fixed-point", "host-record.json", "seed-surface.json"])
        self.assertEqual(sorted(path.name for path in (proofs / "fixed-point").iterdir()),
                         sorted(module.evidence_names(0)))
        receipt = (proofs / "SEED-FIXED-POINT").read_bytes()
        fields = module.parse_receipt(receipt).fields
        self.assertEqual((fields["fixed_point_verdict"], fields["cross_check_verdict"], fields["not_reproduced"],
                          fields["controls"], fields["config_departures"], fields["build_root"]),
                         ("identical", "identical", "none", "0", "build.jobs", str(self.root)))
        self.assertEqual(fields["shared_source_members_excluded"], "builder-config")
        self.assertEqual((fields["producer_stage0_commit"], fields["cross_check_stage0_commit"]),
                         (PRODUCER_COMMIT, CROSS_COMMIT))
        # The host tools the base config names: bound as setup measured them, and listed.
        self.assertEqual(fields["config_host_tools"], "/usr/bin/g++:setup,/usr/bin/gcc:setup,/usr/bin/python3:setup")
        tools = json.loads((proofs / "fixed-point" / "inputs.json").read_text())["host_tools"]
        self.assertEqual({path: tools[path] for path in CONFIG_TOOLS},
                         {path: {**row, "measured": "setup"} for path, row in CONFIG_TOOLS.items()})
        self.assertEqual({name: tools[name] for name in ROLE_TOOLS}, ROLE_TOOLS)
        # THE ACCOUNT: the chain names its home; the tracked copy does not, the raw one does,
        # and the receipt binds both and the count replaced.
        home = self.plan.account[0].encode()
        tracked, raw = (proofs / "fixed-point" / "chain.json").read_bytes(), \
            (self.root / "record" / "raw" / "chain.json").read_bytes()
        self.assertNotIn(home, tracked)
        self.assertIn(b"<home>/toolchains/trust-ec2b5c59/bin/trustc", tracked)
        self.assertIn(home, raw)
        self.assertEqual(fields["evidence_chain_raw_sha256"], sha(self.root / "record" / "raw" / "chain.json"))
        self.assertGreater(int(fields["evidence_chain_normalised_count"]), 0)
        self.assertEqual(fields["evidence_base_config_normalised_count"], "0")
        for path in (proofs / "fixed-point").iterdir():
            self.assertNotIn(home, path.read_bytes(), path.name)
        # Accepted with the candidate door; the shipped door is empty and refuses it.
        pins = driver.text_rows((self.plan.prepare_dir() / "stage0.candidate").read_text(), "candidate")
        record = json.loads((proofs / "host-record.json").read_text())
        kept = self.kept("record.json")
        self.assertEqual(kept["door"], {HOST: {"commit": SOURCE.commit,
                                               "receipt_sha256": sha(proofs / "SEED-FIXED-POINT")}})
        self.assertEqual(hosts.FIXED_POINT_FIRST_HOSTS, {})
        with self.assertRaisesRegex(ValueError, "fixed-point A1"):
            hosts.capture_host_record(self.plan.output_root(), pins, HOST, record)
        with mock.patch.dict(hosts.FIXED_POINT_FIRST_HOSTS, kept["door"]):
            actual, _ = hosts.capture_host_record(self.plan.output_root(), pins, HOST, record)
        self.assertEqual(actual, record)
        self.assertEqual(record["root_disclosure"]["producer_custody"], "recorded-not-authenticated")
        status = driver.status_lines(self.plan)
        self.assertTrue(any(line.startswith(f"  record       written: {proofs} (receipt sha256 ") for line in status))
        self.assertEqual(status[-1], f"next: python3 /opt/trust-driver/scripts/fixed_point_linux_seed.py commit "
                                     f"--root {self.root} --commit {SOURCE.commit} --parent <the parent, e.g. "
                                     f"origin/main> --branch seed/linux-first-{SOURCE.commit[:10]} --identity 'Name "
                                     "<email>' --darwin-pack-state published|not-published")
        # Done once: the second run validates again and writes nothing.
        before = snapshot(self.plan.output_root())
        self.said.clear()
        self.assertEqual(self.record(), 0)
        self.assertRegex(self.said[-1], r"record: already done .*archive members join and every rule holds again")
        self.assertEqual(snapshot(self.plan.output_root()), before)
        # Nothing outside the root: no tracked path of a checkout was written.
        self.assertFalse((REPO / "bootstrap" / "trust-stage0" / "host-proofs" / HOST).exists())

    def test_a_control_that_decided_a_file_is_recorded_with_its_evidence(self):
        self.plan.stage2_for["f-build"] = {**STAGE2_SEED, "bin/ty": "ty, another link order"}
        self.through_cross_check()
        self.refused(r"bin/ty is not decided yet \(a control build decides it\), so there is nothing to record yet\. "
                     r"Nothing was written.*Run: python3 .* build --role control", self.record)
        self.plan.stage2_for["c1-build"] = STAGE2_SEED
        self.assertEqual(self.build("control"), 0, self.said)
        self.assertEqual(self.record(), 0, self.said)
        fields = driver.validator().parse_receipt((self.proofs() / "SEED-FIXED-POINT").read_bytes()).fields
        self.assertEqual((fields["controls"], fields["not_reproduced"], fields["nondeterministic"],
                          fields["fixed_point_verdict"]), ("1", "none", "bin/ty", "compiler-and-std-identical"))
        self.assertTrue((self.proofs() / "fixed-point" / "run-control-1.json").is_file())

    def test_record_refuses_cleanly_when_an_earlier_role_is_missing(self):
        def nothing_written():
            self.assertFalse(self.proofs().exists())
            self.assertFalse((self.plan.kept / "record.json").exists())

        self.assertEqual(self.setup_root(), 0)
        steps = ((r"the producer is not built clean .*Run: python3 .* build --role producer",
                  lambda: self.build("producer", self.producer)),
                 (r"dist is not done clean .*Run: python3 .* dist", self.dist),
                 (r"prepare is not done .*Run: python3 .* prepare", self.prepare),
                 (r"the fixed point is not built clean .*Run: python3 .* build --role fixed-point",
                  lambda: self.build("fixed-point")),
                 (r"the cross-check is not built clean .*Run: python3 .* build --role cross-check",
                  lambda: self.build("cross-check", self.cross)))
        for pattern, step in steps:
            text = self.refused(pattern, self.record)
            self.assertIn("Nothing was written; every record, tree and manifest under", text)
            nothing_written()
            self.assertEqual(step(), 0, self.said)
        self.assertEqual(self.record(), 0, self.said)

    def test_a_producer_gate_stops_the_receipt_from_being_written(self):
        self.through_cross_check()

        def refused_and_nothing_written(pattern):
            self.refused(pattern, self.record)
            self.assertFalse(self.proofs().exists())
            self.assertFalse((self.plan.kept / "record.json").exists())

        os.umask(0o002)
        refused_and_nothing_written(r"the umask is 002, not 022")
        os.umask(0o022)
        trap = self.plan.ledger / "trap.log"
        trap.write_text("cargo build\n")
        # preflight's refusal, which record_step runs before anything it reads.
        refused_and_nothing_written(r"trap.log has 1 line\(s\): a stock Rust tool name was reached by an earlier step "
                                    r"under this root")
        trap.write_text("")
        rungs = self.plan.ledger / "rungs.jsonl"
        rungs.write_text(json.dumps({"label": "f-build"}) + "\n" + json.dumps({"label": "f-build"}) + "\n")
        refused_and_nothing_written(r"rungs.jsonl records the label f-build more than once")
        rungs.unlink()
        stray = put(self.plan.src / "stray.txt", "left by someone\n")
        refused_and_nothing_written(r"is not a clean checkout of .* now")
        stray.unlink()
        record = self.kept("f.build.json")
        driver.write_json(self.plan.record("f"), {**record, "native_after": {**record["native_after"],
                                                                            "sha256": "0" * 64}})
        refused_and_nothing_written(r"the fixed-point build \(f-build\) did not start and end with the LLVM and lld "
                                    r"dist left .*a native output changed between builds")
        driver.write_json(self.plan.record("f"), record)
        # Evidence that would name the invoking account after normalisation: an account
        # whose home JSON escapes (so a byte replacement misses it) and a chain naming it.
        self.plan.account = ("/nonexistent/hôme-of-nobody", "nobody-at-all")
        self.plan.args.chain, self.plan.args.origin_provenance, self.plan.args.origin_config = self.chain_files()
        refused_and_nothing_written(r"fixed-point/chain.json would name the invoking account after normalisation")
        self.plan.account = NOBODY
        self.plan.args.chain, self.plan.args.origin_provenance, self.plan.args.origin_config = self.chain_files()
        self.assertEqual(self.record(), 0, self.said)

    def test_a_record_its_validator_refuses_writes_nothing_under_prepared(self):
        self.through_cross_check()
        self.plan.args.chain, self.plan.args.origin_provenance, self.plan.args.origin_config = \
            self.chain_files(producer="0" * 64)
        text = self.refused(r"the record is refused by its validator: fixed-point C16: chain.json does not name the "
                            r"producer stage0", self.record)
        self.assertIn(f"Nothing was written under {self.plan.output_root()}", text)
        self.assertFalse(self.proofs().exists())
        self.assertFalse((self.plan.kept / "record.json").exists())
        self.assertTrue((self.root / "record" / "staging" / "host-proofs" / HOST / "SEED-FIXED-POINT").is_file())
        self.assertIn("  record       refused by its validator; what it proposed is kept in "
                      f"{self.root / 'record' / 'staging'}", driver.status_lines(self.plan))
        # Another chain record that is not a chain record at all.
        self.plan.args.chain.write_text("{}")
        self.refused(r"is not a staircase chain record .*Name the host's CHAIN-UNPINNED-ROOT.json with --chain",
                     self.record)
        # A build root other than the one the validator holds the record to.
        self.plan.args.chain, self.plan.args.origin_provenance, self.plan.args.origin_config = self.chain_files()
        with mock.patch.object(driver.validator(), "BUILD_ROOT_PARENT", "/var/tmp/trust-seed"):
            self.refused(r"fixed-point B2: build_root = .*every build of this commit ran at '/var/tmp/trust-seed/",
                         self.record)
        self.assertEqual(self.record(), 0, self.said)
        self.assertFalse((self.root / "record" / "staging" / "host-proofs" / HOST).exists())

    def refused_and_nothing_written(self, pattern: str) -> str:
        text = self.refused(pattern, self.record)
        self.assertFalse(self.proofs().exists())
        self.assertFalse((self.plan.kept / "record.json").exists())
        return text

    def through_cross_check_set_up_before_the_config_tools(self) -> None:
        """A root set up and built before setup measured the host tools the base
        config names (the live root's case): inputs.json has no row for them."""
        with mock.patch.object(driver.Plan, "config_tools", lambda plan: {}):
            self.through_cross_check()
        self.assertFalse(any(key.startswith("/") for key in
                             json.loads(self.plan.inputs_file().read_text())["host_tools"]))

    def test_record_measures_the_config_tools_setup_did_not_and_says_so(self):
        self.through_cross_check_set_up_before_the_config_tools()
        self.assertEqual(self.record(), 0, self.said)
        fields = driver.validator().parse_receipt((self.proofs() / "SEED-FIXED-POINT").read_bytes()).fields
        self.assertEqual(fields["config_host_tools"],
                         "/usr/bin/g++:record,/usr/bin/gcc:record,/usr/bin/python3:record")
        tools = json.loads((self.proofs() / "fixed-point" / "inputs.json").read_text())["host_tools"]
        self.assertEqual({path: tools[path] for path in CONFIG_TOOLS},
                         {path: {**row, "measured": "record"} for path, row in CONFIG_TOOLS.items()})
        self.assertTrue(any(line.startswith("fixed-point-linux-seed: record: /usr/bin/gcc, which the base config "
                                            f"names (target.{HOST}.cc, target.{HOST}.linker), was not measured at "
                                            "setup") for line in self.said), self.said)
        # setup's own record is not changed: the measurement is the tracked evidence's.
        self.assertFalse(any(key.startswith("/") for key in
                             json.loads(self.plan.inputs_file().read_text())["host_tools"]))

    def test_a_config_tool_that_is_not_its_roles_file_is_not_recorded(self):
        self.through_cross_check_set_up_before_the_config_tools()
        # The base config's gcc is another compiler than the cc setup bound.
        self.plan.tool_rows["/usr/bin/gcc"] = {**CONFIG_TOOLS["/usr/bin/gcc"], "real": "/usr/lib/ccache/gcc",
                                               "sha256": "9" * 64}
        self.refused_and_nothing_written(
            rf"the record is refused by its validator: fixed-point C15: base-config.toml names target\.{HOST}\.cc = "
            r"'/usr/bin/gcc', which is /usr/lib/ccache/gcc \(sha256 9{16}\), and the cc inputs.json binds is "
            r"/usr/bin/gcc-13 \(sha256 c{16}\)")
        # One that is not there at all: nothing to bind.
        del self.plan.tool_rows["/usr/bin/gcc"]
        self.refused_and_nothing_written(r"the base config names /usr/bin/gcc \(target\..*\.cc, target\..*\.linker\); "
                                         "setup did not bind it and it is not an executable file now")
        self.plan.tool_rows["/usr/bin/gcc"] = dict(CONFIG_TOOLS["/usr/bin/gcc"])
        self.assertEqual(self.record(), 0, self.said)

    def test_a_setup_record_edited_after_the_builds_is_not_setups(self):
        """The live root's case, hand-repaired: rows added to inputs.json after
        every build would be recorded as measured at setup. inputs.json is setup's
        record only while it is the bytes every build and prepare were held to."""
        self.through_cross_check_set_up_before_the_config_tools()
        path = self.plan.inputs_file()
        was = path.read_bytes()
        inputs = json.loads(was)
        inputs["host_tools"].update({tool: dict(row) for tool, row in CONFIG_TOOLS.items()})
        driver.write_json(path, inputs)
        for stem in ("p", "f", "s"):
            shared = self.kept(f"{stem}.build.json")["shared"]
            self.assertEqual(shared["inputs_sha256"], hashlib.sha256(was).hexdigest())
            self.assertFalse(any(key.startswith("/") for key in shared["host_tools"]))
        self.refused_and_nothing_written(
            rf"{re.escape(str(path))} is not the setup record the producer build \(p-build\) was held to: its sha256 "
            rf"is {driver.sha256_file(path)[:16]} now and was {hashlib.sha256(was).hexdigest()[:16]} then\. setup "
            "writes it once, so what it says now is not evidence of what the builds ran with. Nothing was written")
        path.write_bytes(was)
        # prepare's digest is held too.
        prepared = self.plan.prepare_record()
        record = prepared.read_bytes()
        driver.write_json(prepared, {**json.loads(record), "inputs_sha256": "0" * 64})
        self.refused_and_nothing_written(
            rf"{re.escape(str(path))} is not the setup record prepare \(.*\) was held to: its sha256 is "
            rf"{hashlib.sha256(was).hexdigest()[:16]} now and was 0{{16}}")
        prepared.write_bytes(record)
        self.assertEqual(self.record(), 0, self.said)
        fields = driver.validator().parse_receipt((self.proofs() / "SEED-FIXED-POINT").read_bytes()).fields
        self.assertEqual(fields["config_host_tools"], "/usr/bin/g++:record,/usr/bin/gcc:record,/usr/bin/python3:record")

    def test_a_config_tool_is_setups_only_when_every_build_was_held_to_it(self):
        """The label C15 cannot check: setup's row only when every build record holds
        that row, measured at record only when none holds one."""
        base, tools = BASE_CONFIG.encode(), {**ROLE_TOOLS, **CONFIG_TOOLS}

        def roles(*tables):
            return {f"role-{number}": {"label": f"r{number}-build", "shared": {"host_tools": table}}
                    for number, table in enumerate(tables)}

        rows = driver.evidence_host_tools(self.plan, tools, base, roles(tools, tools))
        self.assertEqual({tool: rows[tool] for tool in CONFIG_TOOLS},
                         {tool: {**row, "measured": "setup"} for tool, row in CONFIG_TOOLS.items()})
        rows = self.quiet(driver.evidence_host_tools, self.plan, dict(ROLE_TOOLS), base, roles(ROLE_TOOLS, ROLE_TOOLS))
        self.assertEqual({tool: rows[tool]["measured"] for tool in CONFIG_TOOLS}, dict.fromkeys(CONFIG_TOOLS, "record"))
        other_gcc = {**tools, "/usr/bin/gcc": {**CONFIG_TOOLS["/usr/bin/gcc"], "sha256": "9" * 64}}
        for what, setup_tools, held, pattern in (
                ("a setup row one build was not held to", tools, roles(tools, ROLE_TOOLS),
                 r"binds /usr/bin/g\+\+, which the base config names, as setup measured it, and the role-1 build "
                 r"\(r1-build\) was not held to that row: its record has null\. A row is setup's only when every build "
                 "was held to it"),
                ("a setup row a build was held to otherwise", tools, roles(other_gcc, tools),
                 r"binds /usr/bin/gcc, .* and the role-0 build \(r0-build\) was not held to that row"),
                ("no setup row, and a build held one", ROLE_TOOLS, roles(ROLE_TOOLS, tools),
                 r"has no row for /usr/bin/g\+\+, which the base config names, and the role-1 build \(r1-build\) was "
                 "held to one: setup's record and the builds' records disagree"),
                ("a setup row that is no measurement", {**tools, "/usr/bin/gcc": None},
                 roles({**tools, "/usr/bin/gcc": None}),
                 "records /usr/bin/gcc, which the base config names, as null, not a measurement. Nothing was written"),
                ("a build record without its host tools", tools, {"producer": {"label": "p-build", "shared": {}}},
                 r"the producer build record \(p-build\) has no host_tools table")):
            with self.subTest(what):
                self.refused(pattern, driver.evidence_host_tools, self.plan, dict(setup_tools), base, held)

    def test_every_kept_record_record_reads_is_checked(self):
        """T7: a record, table or file a step kept that changed after it, refuses."""
        self.through_cross_check()

        def rewrite_json(path: Path, change):
            before = path.read_bytes()
            value = json.loads(before)
            change(value)
            driver.write_json(path, value)
            return lambda: path.write_bytes(before)

        def append(path: Path, extra: bytes):
            before = path.read_bytes()
            path.write_bytes(before + extra)
            return lambda: path.write_bytes(before)

        def planted(path: Path):
            put(path, "x\n", 0o755)
            return path.unlink

        def made(path: Path):
            path.mkdir(parents=True)
            return path.rmdir

        shared_kept = self.plan.output_root() / "trust-stage0-shared-kept.json"
        cases = (
            ("the producer's native outputs", lambda: rewrite_json(self.plan.record("p"), lambda record: record[
                "native_after"].update(sha256="0" * 64)),
             r"the LLVM and lld dist started with are not what the producer's build left"),
            ("a build that left the checkout unclean", lambda: rewrite_json(self.plan.record("s"), lambda record:
                                                                            record.setdefault("worktree", {}).update(
                                                                                problems_after=["src/x.rs modified"])),
             r"the cross-check build \(s-build\) left the checkout unclean"),
            ("a build that left a stray ignored file", lambda: rewrite_json(self.plan.record("f"), lambda record:
                                                                            record.setdefault("worktree", {}).update(
                                                                                ignored_after=["stray.o"])),
             r"the fixed-point build \(f-build\) left the checkout unclean, stray ignored files"),
            ("the installed seed changed", lambda: planted(self.plan.seed / "bin" / "planted"),
             r"is no longer the pinned archives as installed"),
            ("a run record changed after its build", lambda: append(Path(self.kept("f.build.json")["run"]["path"]),
                                                                    b" "),
             r"the fixed-point run record .* is not the bytes its build recorded"),
            ("the native table dist recorded", lambda: rewrite_json(self.plan.native("p-dist", "after"),
                                                                    lambda table: table.update(sha256="0" * 64)),
             r"is not the table dist.json records"),
            ("prepare's record of the shared archive", lambda: rewrite_json(shared_kept, lambda kept: [
                row.update(pinned_member_table_sha256="0" * 64) for row in kept.get("kept") or []]),
             r"does not record the pinned .* with the member table it has"),
            ("the candidate src/stage0", lambda: append(self.plan.prepare_dir() / "stage0.candidate", b"# edited\n"),
             r"the candidate src/stage0 .* is not the bytes its build recorded"),
            ("this run's shared archive", lambda: append(self.plan.dist / f"trust-src-{SEED_VERSION}-trust.tar.xz",
                                                         b"\0"),
             r"this run's .*trust-src-.* is not the file dist.json records"),
        )
        for what, change, pattern in cases:
            with self.subTest(what):
                undo = change()
                try:
                    self.refused_and_nothing_written(pattern)
                finally:
                    undo()
        # An output directory this step did not finish.
        undo = made(self.proofs())
        self.refused(r"exists and .*record.json does not: it is not a record this step finished", self.record)
        self.assertFalse((self.plan.kept / "record.json").exists())
        undo()
        self.assertEqual(self.record(), 0, self.said)

    def test_record_reads_the_roles_it_records(self):
        self.through_cross_check()
        cases = (
            ("a tree outside the allowed files", lambda: driver.write_json(self.plan.record("f"), {
                **self.kept("f.build.json"), "comparison": {**(self.kept("f.build.json").get("comparison") or {}),
                                                            "outside_allowed": ["bin/trustc"]}}),
             self.plan.record("f"), r"the fixed-point tree differs from the producer's outside"),
            ("a build record with problems", lambda: driver.write_json(self.plan.record("s"), {
                **self.kept("s.build.json"), "problems": ["a problem"]}),
             self.plan.record("s"), r"the cross-check build record s-build lists problems"),
            ("controls out of order", lambda: driver.write_json(self.plan.record("c2"), self.kept("f.build.json")),
             self.plan.record("c2"), r"the controls are not c1, c2, \.\.\. in order"),
            ("a started control that is not clean", lambda: driver.write_json(self.plan.attempt("c1-build"),
                                                                              {"label": "c1-build"}),
             self.plan.attempt("c1-build"), r"the control c1 was started and is not built clean"),
            ("a dist that was not clean", lambda: driver.write_json(self.plan.kept / "dist.not-clean.json",
                                                                    {"why": "test"}),
             self.plan.kept / "dist.not-clean.json", r"dist is not done clean"),
        )
        for what, change, path, pattern in cases:
            with self.subTest(what):
                before = path.read_bytes() if path.is_file() else None
                change()
                try:
                    self.refused_and_nothing_written(pattern)
                finally:
                    if before is None:
                        path.unlink()
                    else:
                        path.write_bytes(before)
        self.assertEqual(self.record(), 0, self.said)

    def test_a_written_record_that_no_longer_validates_refuses_on_the_second_run(self):
        self.through_cross_check()
        self.assertEqual(self.record(), 0, self.said)
        chain = self.proofs() / "fixed-point" / "chain.json"
        before = snapshot(self.plan.output_root())
        chain.write_bytes(chain.read_bytes().replace(b'"r1"', b'"r0"', 1))
        self.refused(r"the record is refused by its validator: fixed-point C1: chain.json has sha256 .*no longer "
                     r"validates; nothing was changed", self.record)
        after = snapshot(self.plan.output_root())
        self.assertEqual({key for key in before if before[key] != after.get(key)},
                         {f"host-proofs/{HOST}/fixed-point/chain.json"})

    def test_controls_that_differ_outside_or_never_decide_refuse(self):
        # A control that differs from the producer outside the two files: the stop rule.
        self.plan.stage2_for["f-build"] = {**STAGE2_SEED, "bin/ty": "ty, another link order"}
        self.through_cross_check()
        self.plan.stage2_for["c1-build"] = {**STAGE2_SEED, "bin/ty": "ty, a third order",
                                            "bin/trustdoc": "\x7fELF trustdoc, another"}
        self.build("control")
        self.refused_and_nothing_written(r"the builds by the pinned seed differ from the producer's tree outside "
                                         r"bin/targo-trust and bin/ty \(the first: bin/trustdoc\): no record is "
                                         r"written")

    def test_three_controls_that_agree_against_the_producer_refuse(self):
        self.plan.stage2_for["f-build"] = {**STAGE2_SEED, "bin/ty": "ty, another link order"}
        self.through_cross_check()
        for number in range(1, driver.CONTROL_LIMIT + 1):
            self.plan.stage2_for[f"c{number}-build"] = {**STAGE2_SEED, "bin/ty": "ty, another link order"}
            self.assertEqual(self.build("control"), 0, self.said)
        self.refused_and_nothing_written(r"bin/ty has one digest in every build by the pinned seed and another in the "
                                         r"producer's after the last control: the difference follows the stage0")
        self.assertEqual(driver.status_lines(self.plan)[-1],
                         "next: nothing: the stop rule holds, and no record is written from these builds")

    def test_a_build_that_did_not_make_an_allowed_file_decides_nothing(self):
        self.plan.stage2_for["f-build"] = {key: value for key, value in STAGE2_SEED.items() if key != "bin/ty"}
        self.through_cross_check()
        self.assertEqual(driver.control_state(self.plan)["absent"], ["bin/ty"])
        self.refused(r"bin/ty is in some of the producer's and the pinned seed's trees and not in others: a build "
                     r"that did not make it gives no digest, so no control can decide it", self.build, "control")
        self.refused_and_nothing_written(r"bin/ty is in some of the producer's and the pinned seed's trees and not in "
                                         r"others, so it is neither reproduced nor nondeterministic")
        status = driver.status_lines(self.plan)
        self.assertIn("  control      none can help: bin/ty is missing from a build's tree", status)
        self.assertEqual(status[-1], "next: nothing: the stop rule holds, and no record is written from these builds")

    def test_the_surface_and_receipt_are_searched_for_the_account_too(self):
        self.through_cross_check()
        prepared = self.kept("prepare.json")
        surface = Path(prepared["surface"]["path"])
        before = surface.read_bytes(), self.plan.prepare_record().read_bytes()
        value = json.loads(before[0])
        value["tool_versions"]["targo"] = f"targo built by {self.plan.account[1]}_scratch"
        surface.write_text(json.dumps(value, sort_keys=True))
        driver.write_json(self.plan.prepare_record(), {**prepared, "surface": {**prepared["surface"],
                                                                               "sha256": sha(surface)}})
        self.refused_and_nothing_written(r"seed-surface.json would name the invoking account after normalisation")
        surface.write_bytes(before[0])
        self.plan.prepare_record().write_bytes(before[1])
        # A home that is not the invoker's, left in a tracked file: refused whatever the account.
        self.plan.args.chain, self.plan.args.origin_provenance, self.plan.args.origin_config = self.chain_files()
        chain = json.loads(self.plan.args.chain.read_text())
        chain["chain"]["rungs"][0]["invocations"][0]["label"] = "r1 of /home/someone-else"
        self.plan.args.chain.write_text(json.dumps(chain))
        self.refused_and_nothing_written(r"fixed-point/chain.json would name the invoking account after normalisation")

    def test_an_account_the_validator_cannot_search_for_refuses(self):
        self.through_cross_check()
        self.plan.account = ("/nonexistent/home", "nobody at all")
        text = self.refused_and_nothing_written(r"the invoking account cannot be recorded: the login is not 1 to 64 "
                                                r"of the characters .*Nothing was written\. Run record as an account "
                                                r"whose login and home the validator can search for")
        self.assertFalse((self.root / "record").exists(), text)

    def test_record_through_the_command_line_and_its_defaults(self):
        arguments_ = driver.parser().parse_args(["record", "--root", str(self.root), "--chain", "~/c.json"])
        driver.resolve(arguments_, HOST)
        self.assertEqual(arguments_.chain, Path(os.path.expanduser("~/c.json")))
        self.assertEqual(arguments_.origin_provenance, [Path(os.path.expanduser(path))
                                                        for path in driver.ORIGIN_PROVENANCE])
        self.assertEqual(arguments_.origin_config, Path(os.path.expanduser(driver.ORIGIN_CONFIG)))
        self.assertEqual(driver.UNREPRODUCED_ALLOWED, driver.ledger().FIXED_POINT_UNREPRODUCED_ALLOWED)


class TokenLeakTests(RecordCase):
    """SEED-TOKEN-LEAK-STAGE0-1 (docs/DECISION_QUEUE.md): a run whose FIFO jobserver came
    back short is accepted only when x.py exited 0, its census shows nothing outlived
    x.py, the FIFO's path was unchanged, the count is not below none and its stage0, as
    its admission records it, is a host chain commit that git says does not contain
    d57cafb60f7 (docs/OPEN_ISSUES.md RUSTC-FRONTEND-TOKEN-LEAK-1). The chain's commits are
    the real ones, judged by git in this checkout."""

    CENSUS = {"kind": "process-census", "flagged": [], "ended": "watched-exited", "max_gap_s": 1.0,
              "abandoned_children": 0}
    RULE = (r"SEED-TOKEN-LEAK-STAGE0-1 \(docs/OPEN_ISSUES.md RUSTC-FRONTEND-TOKEN-LEAK-1\) does not excuse its "
            r"jobserver's 1 of the 2 token\(s\) back: ")

    @staticmethod
    def short(*, jobserver: dict | None = None, **record) -> dict:
        """A fake run whose jobserver got 1 of its 2 tokens back; `record` changes its record."""
        return {"jobserver": {"tokens_at_end": 1, **(jobserver or {})}, "record": record}

    def test_a_token_kept_by_a_chain_stage0_without_the_fix_is_accepted_and_disclosed(self):
        self.plan.behaviour["s-build"] = self.short()
        self.through_cross_check()
        judged = self.kept("s.build.json")["jobserver_token_deficit"]
        self.assertEqual(judged, {"rule": "SEED-TOKEN-LEAK-STAGE0-1",
                                  "issue": "docs/OPEN_ISSUES.md RUSTC-FRONTEND-TOKEN-LEAK-1", "given": 2, "returned": 1,
                                  "stage0": f"its stage0 {CROSS_COMMIT[:10]} is a host chain commit that does not "
                                            f"contain d57cafb60f (git in {REPO})", "unmet": []})
        self.assertEqual([self.kept(f"{stem}.build.json")["jobserver_token_deficit"] for stem in "pf"], [None, None])
        accepted = [line for line in self.said if "s-build: its jobserver held" in line]
        self.assertEqual(len(accepted), 1, self.said)
        self.assertRegex(accepted[0], r"^fixed-point-linux-seed: s-build: its jobserver held 1 of the 2 token\(s\) when x.py had exited, and "
                                      r"SEED-TOKEN-LEAK-STAGE0-1 accepts it \(docs/OPEN_ISSUES.md "
                                      r"RUSTC-FRONTEND-TOKEN-LEAK-1: .*\): its stage0 29ebb403de is a host chain "
                                      r"commit that does not contain d57cafb60f .*the receipt names the run in "
                                      r"jobserver_token_deficits$")
        # Disclosed in the receipt, and the list is the one the tracked run records give.
        self.assertEqual(self.record(), 0, self.said)
        module = driver.validator()
        fields = module.parse_receipt((self.proofs() / "SEED-FIXED-POINT").read_bytes()).fields
        self.assertEqual(fields["jobserver_token_deficits"], "s-build:2->1")
        runs = [json.loads(path.read_text()) for path in sorted((self.proofs() / "fixed-point").glob("run-*.json"))]
        self.assertEqual(module.token_deficits(runs), ["s-build:2->1"])
        self.assertRegex(self.said[-1], r"jobserver token deficits s-build:2->1 \(SEED-TOKEN-LEAK-STAGE0-1\)")

    def test_a_short_jobserver_is_refused_unless_every_condition_holds(self):
        # Every attempt builds the stage2 its role's first attempt would.
        self.plan.stage2_for.update({label: STAGE2_SEED for label in (
            "p-build-2", "p-full-2", "f-build-2", *(f"s-build-{number}" for number in range(2, 16)))})
        self.assertEqual(self.setup_root(), 0)
        # The producer's stage0, 6dad0d786f, contains the fix: its build and its dist runs are refused.
        self.plan.behaviour["p-build"] = self.short()
        self.refused(r"p-build is not a clean build: its jobserver held 1 token\(s\) when x.py had exited, not the 2 it "
                     rf"was given: a process ended holding a token, or outlived x.py with one; {self.RULE}its stage0 "
                     rf"{PRODUCER_COMMIT[:10]} contains d57cafb60f \(git in ", self.build, "producer", self.producer)
        self.assertFalse((self.plan.kept / "p.build.json").exists())
        self.assertEqual(self.build("producer", self.producer, again=True), 0, self.said)
        self.plan.behaviour["p-full"] = self.short()
        self.refused(rf"p-full is not a clean build: .*{self.RULE}its stage0 {PRODUCER_COMMIT[:10]} contains d57cafb60f",
                     self.dist)
        self.assertEqual(self.dist(True), 0, self.said)
        self.assertEqual(self.prepare(), 0, self.said)
        # The fixed point's stage0 is the pinned seed, no chain compiler.
        self.plan.behaviour["f-build"] = self.short()
        self.refused(rf"f-build is not a clean build: .*{self.RULE}its stage0 commit .* is not one of the host chain's "
                     r"\(6986546eaa, 20565c3255, 29ebb403de, 6dad0d786f\)", self.build, "fixed-point")
        self.assertEqual(self.build("fixed-point", again=True), 0, self.said)
        # The cross-check, each condition broken alone.
        late = chain_compiler(self.parent / "chain" / "late", "l", PRODUCER_COMMIT)
        other = chain_compiler(self.parent / "chain" / "other", "o", "5" * 40)
        census = self.CENSUS
        cases = (
            ("x.py exited 1, not 0", self.short(rc=1), self.cross),
            (r"its process census ended 'cap' with abandoned_children 0, not watched-exited with 0, so a process may "
             r"have outlived x.py holding the token", self.short(process_census={**census, "ended": "cap"}), self.cross),
            (r"its process census ended 'watched-exited' with abandoned_children 1, not watched-exited with 0",
             self.short(process_census={**census, "abandoned_children": 1}), self.cross),
            (r"its process census ended 'watched-exited' with abandoned_children None, not watched-exited with 0",
             self.short(process_census={key: value for key, value in census.items() if key != "abandoned_children"}),
             self.cross),
            (r"its jobserver's path did not name the FIFO when x.py had exited",
             self.short(jobserver={"path_unchanged": False}), self.cross),
            (rf"its stage0 {PRODUCER_COMMIT[:10]} contains d57cafb60f \(git in ", self.short(), late),
            (r"its stage0 commit \"5{40}\" is not one of the host chain's", self.short(), other),
            (rf"the run record's stage0_commit \"{R1_COMMIT}\" is not its admission's \"{CROSS_COMMIT}\"",
             self.short(stage0_commit=R1_COMMIT), self.cross),
        )
        number = 0
        for pattern, behaviour, stage0 in cases:
            number += 1
            label = "s-build" if number == 1 else f"s-build-{number}"
            with self.subTest(label=label):
                self.plan.behaviour[label] = behaviour
                self.refused(rf"{label} is not a clean build: .*{self.RULE}{pattern}", self.build, "cross-check",
                             stage0, number > 1)
                self.assertFalse((self.plan.kept / "s.build.json").exists())
        # A count below none, and a surplus, are never excused.
        number += 1
        self.plan.behaviour[f"s-build-{number}"] = self.short(jobserver={"tokens_at_end": -1})
        self.refused(r"is not a clean build: .*SEED-TOKEN-LEAK-STAGE0-1 \(docs/OPEN_ISSUES.md "
                     r"RUSTC-FRONTEND-TOKEN-LEAK-1\) does not excuse its jobserver's -1 of the 2 token\(s\) back: it "
                     r"counted -1 token\(s\) at the end, not none or more", self.build, "cross-check", self.cross, True)
        number += 1
        self.plan.behaviour[f"s-build-{number}"] = self.short(jobserver={"tokens_at_end": 3})
        text = self.refused(r"its jobserver held 3 token\(s\) when x.py had exited, not the 2 it was given: something "
                            "wrote a token it never took", self.build, "cross-check", self.cross, True)
        self.assertNotIn("SEED-TOKEN-LEAK-STAGE0-1", text)
        # Every condition met: clean, and the record keeps what was decided.
        number += 1
        self.plan.behaviour[f"s-build-{number}"] = self.short()
        self.assertEqual(self.build("cross-check", self.cross, True), 0, self.said)
        record = self.kept("s.build.json")
        self.assertEqual((record["label"], record["jobserver_token_deficit"]["unmet"]), (f"s-build-{number}", []))


class TokenLeakStage0Tests(unittest.TestCase):
    """token_leak_stage0, SEED-TOKEN-LEAK-STAGE0-1's stage0 condition, says yes only on
    the admission the run was given and an honest answer from git that the validator's
    fixed set agrees with. Each repository here borrows this checkout's objects (read
    only) and is changed alone."""

    FIX = "d57cafb60f"

    def setUp(self):
        held = tempfile.TemporaryDirectory()
        self.addCleanup(held.cleanup)
        self.top = Path(held.name)

    def admission(self, commit: str) -> dict:
        path = self.top / "s-build.admission.json"
        path.write_text(json.dumps({"kind": "stage0-admission", "commit": commit}))
        return {"path": str(path), "sha256": sha(path)}

    @staticmethod
    def judged(repo: Path, commit: str, admission: dict) -> tuple[bool, str]:
        return driver.token_leak_stage0(types.SimpleNamespace(source_repo=lambda: repo), admission,
                                        {"stage0_commit": commit})

    def borrowing(self, name: str) -> Path:
        """A bare repository whose objects are this checkout's, through an alternate."""
        repo = self.top / name
        git(self.top, "init", "--quiet", "--bare", str(repo))
        common = git(REPO, "rev-parse", "--path-format=absolute", "--git-common-dir")
        (repo / "objects" / "info" / "alternates").write_text(f"{common}/objects\n")
        return repo

    def test_the_admission_must_be_the_file_the_run_was_given(self):
        given = self.admission(CROSS_COMMIT)
        self.assertEqual(self.judged(REPO, CROSS_COMMIT, given)[0], True)
        # The same commit, other bytes: not the admission whose sha256 the run's attempt recorded.
        Path(given["path"]).write_text(json.dumps({"kind": "stage0-admission", "commit": CROSS_COMMIT, "x": 1}))
        self.assertEqual(self.judged(REPO, CROSS_COMMIT, given),
                         (False, f"its admission {given['path']} is not the file the run was given"))
        Path(given["path"]).unlink()
        self.assertEqual(self.judged(REPO, CROSS_COMMIT, given),
                         (False, f"its admission {given['path']} cannot be read as the stage0 admission it was given"))

    def test_git_that_cannot_answer_is_a_no(self):
        given = self.admission(CROSS_COMMIT)
        # A checkout that holds neither the fix nor the stage0.
        empty = self.top / "empty"
        git(self.top, "init", "--quiet", str(empty))
        self.assertEqual(self.judged(empty, CROSS_COMMIT, given),
                         (False, f"git in {empty} does not hold {self.FIX}, so whether {CROSS_COMMIT[:10]} contains "
                                 f"{self.FIX} is not known"))
        # Git holds both, and its ancestry answer is neither yes nor no.
        real = driver.git_call

        def failing(repo, *args, **kwargs):
            if args[0] == "merge-base":
                return subprocess.CompletedProcess(["git", *args], 128, b"", b"fatal: a stand-in failure")
            return real(repo, *args, **kwargs)
        with mock.patch.object(driver, "git_call", failing):
            self.assertEqual(self.judged(REPO, CROSS_COMMIT, given),
                             (False, f"git in {REPO} could not say whether {CROSS_COMMIT[:10]} contains {self.FIX} "
                                     "(it exited 128)"))

    def test_replace_refs_grafts_and_a_shallow_history_do_not_hide_the_fix(self):
        given = self.admission(PRODUCER_COMMIT)
        identity = ("-c", "user.name=fixture", "-c", "user.email=fixture@invalid")
        for change in ("replace", "graft"):
            with self.subTest(change):
                repo = self.borrowing(change)
                if change == "replace":
                    git(repo, *identity, "replace", "--graft", PRODUCER_COMMIT, CROSS_COMMIT)
                else:
                    (repo / "info").mkdir(exist_ok=True)
                    (repo / "info" / "grafts").write_text(f"{PRODUCER_COMMIT} {CROSS_COMMIT}\n")
                # The lie is live: plain git now says the producer's stage0 does not contain the fix.
                plain = subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor",
                                        driver.validator().TOKEN_LEAK_FIX_COMMIT, PRODUCER_COMMIT],
                                       capture_output=True, env=GIT_ENV)
                self.assertEqual(plain.returncode, 1, plain.stderr)
                self.assertEqual(self.judged(repo, PRODUCER_COMMIT, given),
                                 (False, f"its stage0 {PRODUCER_COMMIT[:10]} contains {self.FIX} (git in {repo})"))
        repo = self.borrowing("shallow")
        (repo / "shallow").write_text(f"{PRODUCER_COMMIT}\n")
        self.assertEqual(self.judged(repo, PRODUCER_COMMIT, given),
                         (False, f"git in {repo} answers 'true' (exit 0) to rev-parse --is-shallow-repository, not "
                                 f"'false': a shallow history cannot show whether {PRODUCER_COMMIT[:10]} contains "
                                 f"{self.FIX}"))

    def test_no_stage0_the_validator_would_refuse_is_excused(self):
        given = self.admission(CROSS_COMMIT)
        module = driver.validator()
        fewer = tuple(commit for commit in module.TOKEN_LEAK_STAGE0_COMMITS if commit != CROSS_COMMIT)
        with mock.patch.object(module, "TOKEN_LEAK_STAGE0_COMMITS", fewer):
            self.assertEqual(self.judged(REPO, CROSS_COMMIT, given),
                             (False, f"git in {REPO} says {CROSS_COMMIT[:10]} does not contain {self.FIX}, but the "
                                     f"validator's TOKEN_LEAK_STAGE0_COMMITS ({', '.join(c[:10] for c in fewer)}) does "
                                     "not name it, and this script excuses no stage0 the validator would refuse"))
        self.assertEqual(self.judged(REPO, CROSS_COMMIT, given),
                         (True, f"its stage0 {CROSS_COMMIT[:10]} is a host chain commit that does not contain "
                                f"{self.FIX} (git in {REPO})"))


# ---------------------------------------------------------------------------
# commit, verify and publish (design steps 14-17): the real validator, door, ledger
# renderer and corpus checker over a parent repository built here, with real git.

CORPUS_SPEC = importlib.util.spec_from_file_location("fixed_point_corpus_membership",
                                                     REPO / "scripts" / "check_corpus_membership.py")
assert CORPUS_SPEC is not None and CORPUS_SPEC.loader is not None
corpus_membership = importlib.util.module_from_spec(CORPUS_SPEC)
sys.modules[CORPUS_SPEC.name] = corpus_membership
CORPUS_SPEC.loader.exec_module(corpus_membership)

# The scripts that judge a branch, copied into the parent (the real ones).
JUDGES = ("seed_host_ledger.py", "seed_fixed_point.py", "seed_root_initialization.py", "mint_seed_support.py",
          "recreate_bootstrap.py", "seed_staircase.py", "check_corpus_membership.py", "fixed_point_linux_seed.py",
          "linux_refresh_toolchain.py")
LEDGER_HEAD = ('# Trust stage0 seed (fixture ledger)\n\nscope = "internal"\npromotion_decision = "admit-internal"\n\n'
               'signatures = [\n  "placeholder:internal-admission-only:not-publicly-signed",\n]\n\n'
               '[release]\nrepo = "fixture/trust"\nvisibility = "private"\n')
# check_seed_freshness.py and check_ledger_pins.py read the whole tree (a native probe;
# the repository's gate ledgers): stand-ins whose exit code a file outside the repo sets.
CHECK_STAND_IN = ("import pathlib, sys\nmarker = pathlib.Path({marker!r})\n"
                  "code = int(marker.read_text()) if marker.is_file() else 0\n"
                  "if code:\n    print('FINDING: fixture {name} red')\n    print('FINDINGS: complete')\n"
                  "sys.exit(code)\n")
BRANCH = "seed/linux-first-fixture"
IDENTITY = "Seed Committer <seed@example.invalid>"


def darwin_proofs(pins: dict[str, str]) -> tuple[bytes, bytes]:
    """The cohort mint host's SEED-MINT and surface: a mint receipt of the commit and
    the entrypoints its archives (SeedFixture's Darwin ones) carry."""
    receipt = {
        "schema": "trust-seed-mint-v1", "source_commit": pins["compiler_git_commit_hash"],
        "source_commit_date": pins["compiler_date"], "source_version": SEED_VERSION, "host": DARWIN,
        "pinned_seed_commit": "b" * 40, "pinned_seed_date": "2026-11-01",
        "pinned_seed_compiler_sha256": "1" * 64, "pinned_seed_driver_sha256": "2" * 64,
        "ddc_seed_relation": "lineage-disjoint", "ddc_seed_commit": "c" * 40, "ddc_seed_date": "2026-10-30",
        "ddc_seed_lineage": "stock", "ddc_seed_compiler_sha256": "3" * 64, "ddc_seed_driver_sha256": "4" * 64,
        "ddc_build_driver": "the pinned seed's cargo, in both builds",
        "ddc_scope": "<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std",
        "stage2_tree_sha256_pinned_seed": "5" * 64, "stage2_tree_sha256_ddc_seed": "5" * 64,
        "ddc_verdict": "identical", "lineage_disjoint_anchor": pins["compiler_git_commit_hash"],
        "self_host_proof": "pass"}
    names = ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt")
    surface = {"schema": "trust-self-host-seed-surface-v1", "source_version": SEED_VERSION, "host": DARWIN,
               "tool_versions": {name: f"{name} {SEED_VERSION} (darwin fixture)" for name in ("trustc", "targo",
                                                                                            "trustfmt")},
               "entrypoint_sha256": {name: hashlib.sha256(f"darwin {STAGE2_SEED['bin/' + name]}".encode("latin-1"))
                                     .hexdigest() for name in names},
               "tree": {"sha256": "6" * 64}}
    text = "".join(f"{key}={value}\n" for key, value in receipt.items()) + f"compiler_file={'7' * 64} bin/trustc\n"
    return text.encode(), (json.dumps(surface, sort_keys=True) + "\n").encode()


def write_files(top: Path, files: dict[str, bytes]) -> None:
    for relative, payload in files.items():
        path = top / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)


class ParentRepo:
    """The checkout `commit` clones and --parent names: SeedFixture's pin (the cohort
    mint host's nine rows and its mint record), the scripts that judge a branch (the
    real ones, the validator's build-root parent moved to the test's), stand-ins for
    the two push rows that read the whole tree, and corpus manifests exact for this
    tree with the real headers (the TOML corpus needs more than 1000 documents)."""

    def __init__(self, base: Path, fixture: "SeedFixture", build_parent: Path):
        self.repo, self.checks = base / "trust", base / "checks"
        self.checks.mkdir(parents=True)
        self.repo.mkdir()
        git(self.repo, "init", "-q", "-b", "main")
        pins = driver.text_rows(fixture.stage0.decode(), "the parent's src/stage0")
        date, manifest_hash = pins["compiler_date"], hashlib.sha256(fixture.manifest).hexdigest()
        files = {f"scripts/{name}": (REPO / "scripts" / name).read_bytes() for name in JUDGES}
        # recreate_bootstrap.py loads its helpers from scripts/lib.
        files.update({f"scripts/lib/{path.name}": path.read_bytes()
                      for path in sorted((REPO / "scripts" / "lib").iterdir()) if path.is_file()})
        moved = files["scripts/seed_fixed_point.py"].replace(
            b'BUILD_ROOT_PARENT = "/var/tmp/trust-seed"', f'BUILD_ROOT_PARENT = "{build_parent}"'.encode())
        assert moved != files["scripts/seed_fixed_point.py"]
        files["scripts/seed_fixed_point.py"] = moved
        files["src/bootstrap/stage0_identity.py"] = (REPO / "src" / "bootstrap" / "stage0_identity.py").read_bytes()
        for name in ("check_seed_freshness", "check_ledger_pins"):
            files[f"scripts/{name}.py"] = CHECK_STAND_IN.format(marker=str(self.checks / name), name=name).encode()
        files["src/stage0"] = fixture.stage0
        for name in driver.MANIFEST_FILES:
            files[f"{driver.SEED_DIR}/{name.format(date=date)}"] = (
                fixture.manifest if name.endswith(".toml") else f"{manifest_hash}\n".encode())
        files[driver.ADMISSION_FILE] = (json.dumps({
            "admission": "internal", "date": date, "git_commit_hash": SOURCE.commit, "manifest_hash": manifest_hash,
            "payloads": [{"relative_path": key, "sha256": value}
                         for key, value in sorted(driver.pinned_rows(pins).items())]}, indent=2) + "\n").encode()
        hosts = driver.ledger()
        receipt, surface = darwin_proofs(pins)
        self.darwin_record = hosts.make_host_record(pins, DARWIN, receipt, surface)
        receipt_path, surface_path = hosts.proof_paths(DARWIN)
        files[f"{driver.SEED_DIR}/{receipt_path}"] = receipt
        files[f"{driver.SEED_DIR}/{surface_path}"] = surface
        files[f"{driver.SEED_DIR}/{hosts.record_path(DARWIN)}"] = hosts.record_bytes(self.darwin_record)
        ledger, self.tag = driver.support().render_seed_ledger(
            LEDGER_HEAD, pins, fixture.stage0.decode(), DARWIN,
            {name: value for name, value in json.loads(surface)["tool_versions"].items()},
            driver.support().parse_receipt(receipt.decode()), host_records={DARWIN: self.darwin_record})
        files[driver.LEDGER_FILE] = ledger.encode()
        ignore = (REPO / ".gitignore").read_text().split("# Trust stage0 local build caches")[1]
        files[".gitignore"] = ("# Trust stage0 local build caches" + ignore.split("## SOTA")[0]).encode()
        files["x.py"] = b"print('x.py of the fixture')\n"
        for number in range(1001):
            files[f"fixtures/corpus/document-{number:04}.toml"] = b"pinned = true\n"
        write_files(self.repo, files)
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-qm", "the parent's pin")
        self.repin("the corpus manifests")
        self.head = git(self.repo, "rev-parse", "HEAD")

    def repin(self, message: str) -> str:
        """Corpus manifests exact for the committed tree, with the real headers."""
        for suffix, manifest in driver.CORPUS_MANIFESTS.items():
            header, why = corpus_membership.split_header((REPO / manifest).read_text())
            assert header is not None, why
            listed = [path for path in git(self.repo, "ls-files", "--", f"*{suffix}").splitlines()
                      if not path.startswith(driver.CORPUS_EXCLUDED)
                      and (suffix != ".json" or (self.repo / path).stat().st_size < driver.CORPUS_JSON_CAP)]
            put(self.repo / manifest, header + "".join(f"{path}\n" for path in sorted(listed)))
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-qm", message)
        return git(self.repo, "rev-parse", "HEAD")

    def commit_on(self, base: str, files: dict[str, bytes], message: str) -> str:
        """A commit on `base` with `files` changed, made without moving any branch."""
        git(self.repo, "checkout", "-q", "--detach", base)
        write_files(self.repo, files)
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-qm", message)
        made = git(self.repo, "rev-parse", "HEAD")
        git(self.repo, "checkout", "-q", "main")
        return made

    def state(self) -> tuple[str, str, str, str]:
        """HEAD, every ref, the index and the working tree's status."""
        return (git(self.repo, "rev-parse", "HEAD"), git(self.repo, "for-each-ref"),
                hashlib.sha256((self.repo / ".git" / "index").read_bytes()).hexdigest(),
                git(self.repo, "status", "--porcelain", "--ignored"))


class CommitPlan(RecordPlan):
    """RecordPlan whose parent is a real repository (ParentRepo): --parent resolves
    there, prepare reads the pin from it, and every run names the seed_staircase.py
    of the commit it was run from."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.parent_repo: Path | None = None
        self.parent_overrides: dict[str, bytes] = {}    # path -> bytes the parent "has" (T4, T5 stand-ins)
        self.tool_sha256 = sha(REPO / "scripts" / "seed_staircase.py")
        self.tool_head: str | None = None

    def source_repo(self):
        return self.parent_repo

    def parent_commit(self):
        return driver.Plan.parent_commit(self)

    def parent_file(self, commit, path):
        if path in self.parent_overrides:
            return self.parent_overrides[path]
        return driver.Plan.parent_file(self, commit, path)

    def run(self, label, words, admission):
        self.behaviour.setdefault(label, {}).setdefault("record", {})["tool"] = {
            "path": str(self.driver / "seed_staircase.py"), "sha256": self.tool_sha256,
            "checkout_head": self.tool_head, "modified_in_checkout": False}
        return super().run(label, words, admission)


class CommitCase(RecordCase):
    plan_class = CommitPlan

    def setUp(self):
        super().setUp()
        self.trust = ParentRepo(self.parent / "parent-repository", self.fixture, self.parent)
        self.plan.parent_repo, self.plan.tool_head = self.trust.repo, self.trust.head
        self.plan.args.branch, self.plan.args.identity = BRANCH, IDENTITY
        self.plan.args.darwin_pack_state, self.plan.args.agh, self.plan.args.exit_test = "published", None, None

    def through_record(self) -> None:
        self.through_cross_check()
        self.assertEqual(self.record(), 0, self.said)

    def commit(self, **changes) -> int:
        for key, value in changes.items():
            setattr(self.plan.args, key, value)
        return self.quiet(driver.commit_step, self.plan)

    def branch_repo(self) -> Path:
        return self.plan.commit_dir() / "repo"

    def no_branch(self) -> None:
        self.assertFalse(self.plan.commit_dir().exists())
        self.assertFalse(driver.commit_record(self.plan).exists())

    def expected_paths(self) -> list[str]:
        proofs = f"{driver.SEED_DIR}/host-proofs/{HOST}"
        return sorted(["src/stage0", driver.LEDGER_FILE, driver.DOOR_FILE, driver.ADMISSION_FILE,
                       *(f"{driver.SEED_DIR}/{name.format(date=SEED_DATE)}" for name in driver.MANIFEST_FILES),
                       f"{proofs}/SEED-FIXED-POINT", f"{proofs}/seed-surface.json", f"{proofs}/host-record.json",
                       *(f"{proofs}/fixed-point/{name}" for name in driver.validator().evidence_names(0))])


class CommitTests(CommitCase):
    def test_commit_builds_the_add_host_branch_from_the_listed_paths_and_touches_no_checkout(self):
        self.through_record()
        before = self.trust.state()
        self.refused(r"T12: --darwin-pack-state is 'maybe'", self.commit, darwin_pack_state="maybe")
        self.refused(r"--identity 'nobody' is not 'Name <email>'", self.commit, darwin_pack_state="published",
                     identity="nobody")
        self.no_branch()
        self.assertEqual(self.commit(identity=IDENTITY), 0, self.said)
        made, repo = self.kept("commit.json"), self.branch_repo()
        first, second = made["commits"]
        self.assertEqual(git(repo, "rev-parse", f"refs/heads/{BRANCH}"), second)
        self.assertEqual(git(repo, "rev-list", "--parents", "-n", "1", second).split(), [second, first])
        self.assertEqual(git(repo, "rev-list", "--parents", "-n", "1", first).split(), [first, self.trust.head])
        # Commit 1 carries exactly the listed paths; commit 2 exactly the two corpus manifests; no archive.
        self.assertEqual(git(repo, "diff", "--name-only", self.trust.head, first).splitlines(), self.expected_paths())
        self.assertEqual(git(repo, "diff", "--name-only", first, second).splitlines(),
                         sorted(driver.CORPUS_MANIFESTS.values()))
        self.assertEqual(made["paths"], {"commit-1": self.expected_paths(),
                                         "commit-2": sorted(driver.CORPUS_MANIFESTS.values())})
        self.assertFalse([path for path in git(repo, "ls-tree", "-r", "--name-only", second).splitlines()
                          if path.endswith(".tar.xz") or ".this-run" in path])
        # The door: one line, naming the host, the commit and the receipt's sha256.
        receipt = self.proofs() / "SEED-FIXED-POINT"
        diff = git(repo, "diff", "-U0", self.trust.head, first, "--", driver.DOOR_FILE).splitlines()
        self.assertEqual([line for line in diff if line[:1] in "+-" and not line.startswith(("+++", "---"))],
                         [f"-{driver.EMPTY_DOOR_LINE}",
                          "+" + driver.DOOR_PREFIX + json.dumps({HOST: {"commit": SOURCE.commit,
                                                                        "receipt_sha256": sha(receipt)}})])
        # The ledger: both hosts in the title and tables, one [release.mint] line, no such table.
        ledger = git(repo, "show", f"{second}:{driver.LEDGER_FILE}")
        release = tomllib.loads(ledger)["release"]
        self.assertNotIn("mint", release)
        self.assertEqual(sum(line.startswith("[release.mint]") for line in ledger.splitlines()), 1)
        self.assertEqual(sorted(release["hosts"]), sorted([DARWIN, HOST]))
        self.assertEqual(release["hosts"][DARWIN], self.trust.darwin_record)
        self.assertIn(f"{DARWIN}, {HOST}", release["title"])
        self.assertEqual(driver.ledger().select_host_record(release, HOST)["schema"],
                         driver.ledger().FIXED_POINT_SCHEMA)
        # The cohort mint host's proofs keep their blob ids; the pin is the candidate.
        for path in git(repo, "ls-tree", "-r", "--name-only", self.trust.head, "--",
                        f"{driver.SEED_DIR}/host-proofs/{DARWIN}").splitlines():
            self.assertEqual(git(repo, "rev-parse", f"{self.trust.head}:{path}"), git(repo, "rev-parse", f"{second}:{path}"))
        self.assertEqual(blob(repo, second, "src/stage0"), (self.plan.prepare_dir() / "stage0.candidate").read_bytes())
        # The corpus re-pin adds exactly the new tracked .json and .toml, noted in each header,
        # and the branch tip is exact.
        for suffix, manifest in driver.CORPUS_MANIFESTS.items():
            old = driver.manifest_members(git(repo, "show", f"{self.trust.head}:{manifest}"))
            new = driver.manifest_members(git(repo, "show", f"{second}:{manifest}"))
            self.assertEqual(sorted(new - old), [path for path in self.expected_paths() if path.endswith(suffix)
                                                 and git_absent(repo, self.trust.head, path)])
            self.assertFalse(old - new)
            # The real headers carry older RE-PINNED notes: this commit adds exactly its own.
            notes = git(repo, "show", f"{self.trust.head}:{manifest}").count("# RE-PINNED ")
            after = git(repo, "show", f"{second}:{manifest}")
            self.assertEqual(after.count("# RE-PINNED "), notes + 1)
            self.assertIn(f"with the add-host commit of the first Linux seed ({first[:10]}): +", after)
        rejudged = subprocess.run([sys.executable, "-I", "-B", str(repo / driver.CORPUS_SCRIPT), "--rev", second],
                                  cwd=repo, capture_output=True, text=True)
        self.assertEqual(rejudged.returncode, 0, rejudged.stdout)
        # The message states what the record discloses and the Darwin pack state.
        message = git(repo, "log", "-1", "--format=%B", first)
        for words in ("root = unpinned-host-chain", "producer_custody = recorded-not-authenticated",
                      "double_compile_diverse = false", "stock_built_ancestor = inferred-no-receipt",
                      "unpinned-root-seed-ready", f"pack of {SOURCE.commit[:10]}: published"):
            self.assertIn(words, message)
        # --identity is the author and the committer of both commits, not the ambient git identity.
        for commit in (first, second):
            self.assertEqual(git(repo, "log", "-1", "--format=%an <%ae>|%cn <%ce>", commit), f"{IDENTITY}|{IDENTITY}")
        # Nothing was pushed or written in the checkout it was cloned from; the clone points nowhere.
        self.assertEqual(self.trust.state(), before)
        self.assertEqual(git(repo, "remote"), "")
        self.assertIn(f"  commit       made: {BRANCH} in {repo} at {second[:10]} (nothing pushed)",
                      driver.status_lines(self.plan))
        # Done once: the second run says so and changes nothing.
        snapshot_before = snapshot(self.plan.commit_dir())
        self.said.clear()
        self.assertEqual(self.commit(), 0)
        self.assertRegex(self.said[0], rf"commit: already done .*{BRANCH}.*not repeated")
        self.assertEqual(snapshot(self.plan.commit_dir()), snapshot_before)
        self.refused(r"commit is done with branch = .*Nothing was changed", self.commit, branch="another")
        # A done branch that moved since is not reported done.
        git(repo, "update-ref", f"refs/heads/{BRANCH}", first)
        self.refused(rf"commit is done .*and {BRANCH} in .* is not its tip {second[:10]} any more", self.commit,
                     branch=BRANCH)

    def test_a_reverted_add_host_commit_lands_again_with_the_identical_cohort_and_never_with_another(self):
        self.through_record()
        self.assertEqual(self.commit(), 0, self.said)
        made = self.kept("commit.json")
        # The revert of both commits: the parent's tree, so the generated src/stage0 section is the parent's.
        git(self.trust.repo, "fetch", "-q", str(self.branch_repo()), f"refs/heads/{BRANCH}:refs/landed/tip")
        tree = git(self.trust.repo, "rev-parse", f"{self.trust.head}^{{tree}}")
        reverted = git(self.trust.repo, "commit-tree", tree, "-p", made["commits"][1], "-m", "revert the add-host")
        self.assertEqual(git(self.trust.repo, "show", f"{reverted}:src/stage0"),
                         git(self.trust.repo, "show", f"{self.trust.head}:src/stage0"))
        self.plan.commit_dir().rename(self.root / "commit.first")
        driver.commit_record(self.plan).rename(self.plan.kept / "commit.first.json")
        # History pinned this host with these digests: re-landing them is allowed.
        self.assertEqual(self.commit(parent=reverted, branch=BRANCH + "-again"), 0, self.said)
        again = self.kept("commit.json")
        self.assertEqual(git(self.branch_repo(), "diff", "--name-only", reverted, again["commits"][0]).splitlines(),
                         self.expected_paths())
        # A history that pinned it with other digests is refused (T3).
        shutil.rmtree(self.plan.commit_dir())
        driver.commit_record(self.plan).unlink()
        stage0 = blob(self.trust.repo, self.trust.head, "src/stage0")
        row = f"dist/{SEED_DATE}/trustc-{SEED_VERSION}-trust-{HOST}.tar.xz"
        other = self.trust.commit_on(self.trust.head, {"src/stage0": stage0 + f"{row}={'0' * 64}\n".encode()},
                                     "pin the host with other bytes")
        back = self.trust.commit_on(other, {"src/stage0": stage0}, "and unpin it")
        self.refused(rf"T3: {other[:10]} in the parent's history pinned {re.escape(row)} = 0000000000000000\.\.\.",
                     self.commit, parent=back, branch=BRANCH + "-third")
        self.no_branch()
        # And on a side branch that pinned it, unpinned it and was merged: the merge is TREESAME to
        # its first parent, so git's default history simplification never reads that branch.
        side = self.trust.commit_on(self.trust.head, {"src/stage0": stage0 + f"{row}={'1' * 64}\n".encode()},
                                    "pin the host with other bytes on a side branch")
        unpinned = self.trust.commit_on(side, {"src/stage0": stage0}, "and unpin it there")
        moved = self.trust.commit_on(self.trust.head, {"README.main": b"main moved\n"}, "main moves")
        merge = git(self.trust.repo, "commit-tree", git(self.trust.repo, "rev-parse", f"{moved}^{{tree}}"), "-p", moved,
                    "-p", unpinned, "-m", "merge the side branch")
        self.assertNotIn(side, git(self.trust.repo, "rev-list", merge, "--", "src/stage0").split())
        self.refused(rf"T3: {side[:10]} in the parent's history pinned {re.escape(row)} = 1111111111111111\.\.\.",
                     self.commit, parent=merge, branch=BRANCH + "-fourth")
        self.no_branch()

    def test_each_transaction_rule_refuses_and_leaves_no_branch(self):
        self.refused(r"setup of .* is not done", self.commit)
        self.through_record()
        record = self.root / "kept" / "record.json"
        record.rename(record.with_name("record.aside"))
        self.refused(r"record is not done .*Nothing was written\. Run: python3 .* record", self.commit)
        record.with_name("record.aside").rename(record)
        before = self.trust.state()
        stage0 = blob(self.trust.repo, self.trust.head, "src/stage0").decode()
        door = (self.trust.repo / driver.DOOR_FILE).read_text()
        unrelated = git(self.trust.repo, "commit-tree", git(self.trust.repo, "rev-parse", "HEAD^{tree}"), "-m", "x")
        cases = (
            # --parent: the one prepare joined, or a descendant with the same pin and seed metadata.
            (r"prepare joined .*which is not an ancestor of it\. Nothing was written",
             {"parent": unrelated}),
            (r"src/stage0 moved there since .*the commit prepare joined",
             {"parent": self.trust.commit_on(self.trust.head, {"src/stage0": ("# a new head line\n" + stage0).encode()},
                                             "move the pin's head")}),
            # The door lands empty and gains its entry only here, by that one line.
            (r"does not hold the door as it lands",
             {"parent": self.trust.commit_on(self.trust.head, {driver.DOOR_FILE: door.replace(
                 driver.EMPTY_DOOR_LINE, driver.DOOR_PREFIX + '{"x86_64-unknown-linux-gnu": {}}').encode()},
                 "open the door elsewhere")}),
            # A parent whose corpus manifests are not exact would make the re-pin carry its changes.
            (r"corpus manifests are not exact .*Land the parent's re-pin on main first",
             {"parent": self.trust.commit_on(self.trust.head, {"docs/unpinned.json": b"{}\n"}, "an unpinned json")}),
        )
        for pattern, arguments_ in cases:
            with self.subTest(pattern):
                self.refused(pattern, self.commit, **arguments_)
                self.no_branch()
        self.plan.args.parent = "HEAD"
        git(self.trust.repo, "branch", BRANCH)
        self.refused(rf"T8: the branch {BRANCH} exists in .*Nothing was written", self.commit)
        git(self.trust.repo, "branch", "-D", BRANCH)
        ledger = blob(self.trust.repo, self.trust.head, driver.LEDGER_FILE).decode()
        darwin_table = f'[release.hosts."{DARWIN}"]'
        stand_ins = (
            # T4: one host table, a mint record of this commit.
            (driver.LEDGER_FILE, ledger.replace(f'schema = "{driver.ledger().SCHEMA}"',
                                                f'schema = "{driver.ledger().LEGACY_SCHEMA}"', 1),
             r"T4: the parent's host table is aarch64-apple-darwin's with schema 'trust-seed-legacy-host-record-v1'"),
            (driver.LEDGER_FILE, ledger + f'\n[release.hosts."x86_64-apple-darwin"]\nschema = "x"\n',
             r"T4: the parent's .*seed-ledger.toml has 2 host table\(s\)"),
            (driver.LEDGER_FILE, ledger.replace("[release.mint]", "[release.minted]"),
             r"T4: .*\[release.mint\] absent"),
            # T5: the candidate is the parent's head with prepare.py's section.
            ("src/stage0", "# another head\n" + stage0,
             r"T5: .*stage0.candidate is not the parent .*'s src/stage0 head with prepare.py's section"),
        )
        self.assertIn(darwin_table, ledger)
        for path, text, pattern in stand_ins:
            with self.subTest(pattern):
                self.plan.parent_overrides = {path: text.encode()}
                try:
                    self.refused(pattern, self.commit)
                finally:
                    self.plan.parent_overrides = {}
                self.no_branch()
        # T6: every pinned archive is in prepared/ with its pinned bytes.
        archive = self.plan.output_root() / "dist" / SEED_DATE / f"tippy-{SEED_VERSION}-trust-{HOST}.tar.xz"
        archive.rename(archive.with_name("aside"))
        self.refused(r"T5/T6: .*the pinned archive dist/.*/tippy-.* is not a regular file", self.commit)
        archive.with_name("aside").rename(archive)
        payload = archive.read_bytes()
        archive.write_bytes(payload + b"\0")
        self.refused(r"T5/T6: .*tippy-.* is not the bytes the candidate pins", self.commit)
        archive.write_bytes(payload)
        # T10: aterm's seed-pin switch needs the one [release.mint] line.
        render = driver.support().render_seed_ledger
        with mock.patch.object(driver.support(), "render_seed_ledger",
                               lambda *a, **k: render(*a, **{**k, "mint_switch_line": False})):
            self.refused(r"T10: the rendered ledger has 0 line\(s\) starting \[release.mint\]", self.commit)
        # T9: a commit that changes any other path is not made into a branch.
        listing = driver.changed_paths
        with mock.patch.object(driver, "changed_paths", lambda *a: sorted([*listing(*a), "README.md"])):
            self.refused(r"T9: commit 1 changes \['README.md'\] other than the listed paths\. No branch was made",
                         self.commit)
        self.assertFalse(self.plan.commit_dir().exists())
        self.assertFalse(driver.commit_record(self.plan).exists())
        # The re-pin adds exactly the new tracked .json and .toml: a --write that pins more is refused.
        corpus = self.plan.corpus

        def pins_more(repo, *words):
            if words != ("--write",):
                return corpus(repo, *words)
            return [sys.executable, "-c", "import pathlib, subprocess, sys\ndone = subprocess.run(sys.argv[1:-1])\n"
                    "path = pathlib.Path(sys.argv[-1])\npath.write_text(path.read_text() + 'a-not-this-commit.json\\n')\n"
                    "sys.exit(done.returncode)\n", *corpus(repo, *words), str(repo / driver.CORPUS_MANIFESTS[".json"])]
        with mock.patch.object(self.plan, "corpus", pins_more):
            self.refused(r"the re-pin of crates/trust-json/tests/corpus_manifest.txt adds \['a-not-this-commit.json', "
                         r".* and drops \[\]", self.commit)
        self.assertFalse(self.plan.commit_dir().exists())
        # A judge refusal: the branch's own door refuses a record it does not name.
        door = driver.door_text
        with mock.patch.object(driver, "door_text", lambda plan, parent, entry: door(
                plan, parent, {HOST: {**entry[HOST], "receipt_sha256": "0" * 64}})):
            self.refused(r"commit 1 is refused by the branch's own scripts/seed_host_ledger.py with its real door",
                         self.commit)
        self.assertFalse(driver.commit_record(self.plan).exists())
        # Every refusal left the checkout the branch is cloned from as it was, but for the fixture's own commits.
        self.assertEqual(self.trust.state()[0], before[0])
        self.assertEqual(self.commit(), 0, self.said)

    def test_an_orchestration_the_parent_does_not_hold_is_refused(self):
        self.plan.tool_sha256 = "7" * 64
        self.through_record()
        self.refused(r"T11: scripts/seed_staircase.py at .* is not the bytes the runs recorded", self.commit)
        self.no_branch()


def stage0_body_edit(text: str, edit) -> str:
    """src/stage0 with `edit` applied to its generated section only (the part splice replaces)."""
    marker = driver.support().STAGE0_GENERATED_MARKER
    head, body = text.split(marker)
    return head + marker + edit(body)


def stage0_set_row(text: str, key: str, value: str | None) -> str:
    """`key=value` in place of `key`'s row (None drops the row)."""
    lines = [line for line in text.split("\n") if not (line.startswith(key + "=") and value is None)]
    return "\n".join(f"{key}={value}" if line.startswith(key + "=") else line for line in lines)


class CommitRuleTests(CommitCase):
    """Each rule of `commit`, refused by its own words, on an input only it catches."""

    def stage0(self) -> str:
        return blob(self.trust.repo, self.trust.head, "src/stage0").decode()

    def overridden(self, path: str, payload, pattern: str) -> None:
        self.plan.parent_overrides = {path: payload.encode() if isinstance(payload, str) else payload}
        try:
            self.refused(pattern, self.commit)
        finally:
            self.plan.parent_overrides = {}
        self.no_branch()

    def changed(self, path: Path, payload: bytes, pattern: str) -> None:
        was = path.read_bytes()
        path.write_bytes(payload)
        try:
            self.refused(pattern, self.commit)
        finally:
            path.write_bytes(was)
        self.no_branch()

    def test_a_descendant_parent_whose_seed_directory_moved_is_refused(self):
        self.through_record()
        ledger = blob(self.trust.repo, self.trust.head, driver.LEDGER_FILE)
        moved = self.trust.commit_on(self.trust.head, {driver.LEDGER_FILE: ledger + b"# a later note\n"}, "ledger")
        self.refused(r"bootstrap/trust-stage0 moved there since .*prepare and record are made again", self.commit,
                     parent=moved)
        self.no_branch()

    def landed_again(self) -> None:
        """Set aside a branch `commit` made, so the next commit runs anew."""
        shutil.rmtree(self.plan.commit_dir())
        driver.commit_record(self.plan).unlink()

    def test_T3_skips_a_listed_commit_only_while_it_shows_what_excuses_it(self):
        self.through_record()
        stage0 = self.stage0()
        row = f"dist/{SEED_DATE}/trustc-{SEED_VERSION}-trust-{HOST}.tar.xz"
        repo = self.trust.repo

        def conflicted(ours: str, theirs: str) -> bytes:
            return (stage0 + f"<<<<<<< HEAD\n{ours}=======\n{theirs}>>>>>>> upstream\n").encode()

        def on_parent(commit: str) -> str:
            # A parent whose history holds `commit` and whose src/stage0 is the pin prepare joined.
            return self.trust.commit_on(commit, {"src/stage0": stage0.encode()}, "and unpin it")

        def merged_in(side: str) -> str:
            tree = git(repo, "rev-parse", f"{self.trust.head}^{{tree}}")
            return git(repo, "commit-tree", tree, "-p", self.trust.head, "-p", side, "-m", "merge it")

        # conflicted: every row of the host on the incoming side, and listed: not read, and disclosed.
        theirs = self.trust.commit_on(self.trust.head, {"src/stage0": conflicted("", f"{row}={'2' * 64}\n")},
                                      "a mid-merge stage0")
        with mock.patch.dict(driver.T3_NOT_A_PIN, {theirs: ("conflicted", "a fixture's mid-merge stage0")}):
            self.assertEqual(self.commit(parent=on_parent(theirs), branch=BRANCH + "-c"), 0, self.said)
        made = self.kept("commit.json")
        self.assertEqual(made["t3_skipped"], {theirs: f"1 row(s) of {HOST} not read: a fixture's mid-merge stage0"})
        message = git(self.branch_repo(), "log", "-1", "--format=%B", made["commits"][0])
        self.assertIn(f"* T3 did not read {theirs[:10]}'s src/stage0 (docs/DECISION_QUEUE.md SEED-T3-HISTORY-1): "
                      f"1 row(s) of {HOST} not read: a fixture's mid-merge stage0", message)
        self.landed_again()
        # The same commit, not listed: read.
        self.refused(rf"T3: {theirs[:10]} in the parent's history pinned {re.escape(row)} = 2222222222222222\.\.\.",
                     self.commit, parent=on_parent(theirs), branch=BRANCH + "-c2")
        self.no_branch()
        # Listed, but a row of the host on its own side, outside a conflict, or the markers out of order: read.
        for name, text in (("ours", conflicted(f"{row}={'3' * 64}\n", "")),
                           ("outside", (stage0 + f"{row}={'3' * 64}\n<<<<<<< HEAD\n=======\n>>>>>>> up\n").encode()),
                           ("unclosed", (stage0 + f"<<<<<<< HEAD\n=======\n{row}={'3' * 64}\n").encode()),
                           ("no markers", (stage0 + f"{row}={'3' * 64}\n").encode()),
                           # Read as stage0_payload_pins reads a line: trimmed, and split at \r too.
                           ("indented on its own side", conflicted(f"  {row}={'3' * 64}\n", "")),
                           ("after a carriage return", (stage0 + f"# x\r{row}={'3' * 64}\n<<<<<<< HEAD\n=======\n"
                                                        ">>>>>>> up\n").encode()),
                           ("in a diff3 base", (stage0 + f"<<<<<<< HEAD\n||||||| base\n{row}={'3' * 64}\n=======\n"
                                                ">>>>>>> up\n").encode()),
                           # An indented marker is no marker: the rows after it are read.
                           ("after an indented separator", conflicted("", "").replace(b"=======", b"  =======")
                            .replace(b">>>>>>> upstream\n", f"{row}={'3' * 64}\n>>>>>>> upstream\n".encode()))):
            with self.subTest(name):
                listed = self.trust.commit_on(self.trust.head, {"src/stage0": text}, f"a stage0, {name}")
                with mock.patch.dict(driver.T3_NOT_A_PIN, {listed: ("conflicted", "a fixture")}):
                    self.refused(rf"T3: {listed[:10]} in the parent's history pinned {re.escape(row)} = 3{{16}}\.\.\.",
                                 self.commit, parent=on_parent(listed), branch=BRANCH + "-" + name.replace(" ", "-"))
                self.no_branch()
        # before-admission: a root commit that pinned the host, an admission on it that pins no row of
        # the host, and the admission merged into the parent's history: not read.
        pinned = self.trust.commit_on(self.trust.head, {"src/stage0": (stage0 + f"{row}={'4' * 64}\n").encode()},
                                      "an imported stage0")
        root = git(repo, "commit-tree", git(repo, "rev-parse", f"{pinned}^{{tree}}"), "-m", "an initial import")
        admitted = git(repo, "commit-tree", git(repo, "rev-parse", f"{self.trust.head}^{{tree}}"), "-p", root,
                       "-m", "the Trust-native admission")
        listing = {root: ("before-admission", "a fixture's import")}
        with mock.patch.dict(driver.T3_NOT_A_PIN, listing), mock.patch.object(driver, "T3_ADMISSION_COMMIT", admitted):
            self.assertEqual(self.commit(parent=merged_in(admitted), branch=BRANCH + "-a"), 0, self.said)
        self.assertEqual(self.kept("commit.json")["t3_skipped"], {root: f"1 row(s) of {HOST} not read: a fixture's import"})
        self.landed_again()
        # ... read when the commit has a parent, when the admission pins a row of the host, when the
        # admission is not in the parent's history, or when the commit is not the admission's ancestor.
        not_root = git(repo, "commit-tree", git(repo, "rev-parse", f"{pinned}^{{tree}}"), "-p", self.trust.head,
                       "-m", "an import with a parent")
        on_not_root = git(repo, "commit-tree", git(repo, "rev-parse", f"{self.trust.head}^{{tree}}"), "-p", not_root,
                          "-m", "the admission")
        pinning = git(repo, "commit-tree", git(repo, "rev-parse", f"{pinned}^{{tree}}"), "-p", root,
                      "-m", "an admission that pins the host")
        unpinned = git(repo, "commit-tree", git(repo, "rev-parse", f"{self.trust.head}^{{tree}}"), "-p", pinning,
                       "-m", "and unpins it")
        elsewhere = git(repo, "commit-tree", git(repo, "rev-parse", f"{self.trust.head}^{{tree}}"),
                        "-m", "an admission that is not on root")
        for name, listed, admission, parent in (
                ("not a root", not_root, on_not_root, merged_in(on_not_root)),
                ("the admission pins the host", root, pinning, merged_in(unpinned)),
                ("the admission is not in the history", root, elsewhere, merged_in(admitted)),
                ("not the admission's ancestor", root, elsewhere, merged_in(git(
                    repo, "commit-tree", git(repo, "rev-parse", f"{self.trust.head}^{{tree}}"), "-p", admitted,
                    "-p", elsewhere, "-m", "both")))):
            with self.subTest(name):
                with mock.patch.dict(driver.T3_NOT_A_PIN, {listed: ("before-admission", "a fixture")}), \
                        mock.patch.object(driver, "T3_ADMISSION_COMMIT", admission):
                    self.refused(rf"T3: [0-9a-f]{{10}} in the parent's history pinned {re.escape(row)} = 4{{16}}\.\.\.",
                                 self.commit, parent=parent, branch=BRANCH + "-" + name.replace(" ", "-").replace("'", ""))
                self.no_branch()

    def test_T3_reads_history_as_it_is(self):
        self.through_record()
        stage0 = self.stage0()
        row = f"dist/{SEED_DATE}/trustc-{SEED_VERSION}-trust-{HOST}.tar.xz"
        repo = self.trust.repo
        other = self.trust.commit_on(self.trust.head, {"src/stage0": (stage0 + f"{row}={'5' * 64}\n").encode()},
                                     "pin the host with other bytes")
        back = self.trust.commit_on(other, {"src/stage0": stage0.encode()}, "and unpin it")
        # A replace ref that shows the pinning commit as one that pins nothing: T3 still reads it.
        plain = self.trust.commit_on(self.trust.head, {"README.plain": b"x\n"}, "pins nothing")
        git(repo, "-c", "user.name=fixture", "-c", "user.email=fixture@invalid", "replace", other, plain)
        try:
            self.assertNotIn(row, git(repo, "show", f"{other}:src/stage0"))
            self.refused(rf"T3: {other[:10]} in the parent's history pinned {re.escape(row)} = 5{{16}}\.\.\.",
                         self.commit, parent=back, branch=BRANCH + "-replaced")
        finally:
            git(repo, "replace", "-d", other)
        self.no_branch()
        # A graft that gives the parent's history another shape: T3 reads it as it is.
        grafts = repo / ".git" / "info" / "grafts"
        grafts.parent.mkdir(exist_ok=True)
        grafts.write_text(f"{back} {self.trust.head}\n")
        try:
            self.assertNotIn(other, subprocess.run(["git", "-C", str(repo), "rev-list", back], capture_output=True,
                                                   text=True, env=GIT_ENV).stdout.split())
            self.refused(rf"T3: {other[:10]} in the parent's history pinned {re.escape(row)} = 5{{16}}\.\.\.",
                         self.commit, parent=back, branch=BRANCH + "-grafted")
        finally:
            grafts.unlink()
        self.no_branch()
        # A src/stage0 the history names and this store cannot read (a partial clone whose
        # promisor is gone): refused, never skipped.
        named = git(repo, "rev-parse", f"{other}:src/stage0")
        loose = repo / ".git" / "objects" / named[:2] / named[2:]
        self.assertTrue(loose.is_file(), "the fixture's blob is a loose object")
        kept = loose.read_bytes()
        loose.unlink()
        try:
            self.refused(rf"T3: {other[:10]}'s src/stage0 \(blob {named[:10]}\) cannot be read in .*: a history T3 "
                         rf"cannot read can hide a commit that pinned {HOST}\. Nothing was written",
                         self.commit, parent=back, branch=BRANCH + "-unreadable")
        finally:
            loose.write_bytes(kept)
        self.no_branch()
        # A shallow history (cut at its root, so every other rule still sees the ancestry it needs):
        # refused before any row is read.
        shallow = repo / ".git" / "shallow"
        shallow.write_text(git(repo, "rev-list", "--max-parents=0", self.trust.head).split()[0] + "\n")
        try:
            self.refused(r"T3: git in .* answers 'true' \(exit 0\) to rev-parse --is-shallow-repository, not 'false': "
                         rf"a shallow history can hide a commit that pinned {HOST}\. Nothing was written",
                         self.commit, parent=back, branch=BRANCH + "-shallow")
        finally:
            shallow.unlink()
        self.no_branch()

    def test_the_two_listed_commits_show_what_excuses_them_in_this_repository(self):
        # Every T3_NOT_A_PIN entry is a commit of this repository's history, and still shows its
        # excuse, for the host the first Linux seed adds (skipped when the checkout is shallow).
        if git(REPO, "rev-parse", "--is-shallow-repository") != "false":
            self.skipTest("a shallow checkout cannot show the listed commits")
        plan = types.SimpleNamespace(host=HOST, source_repo=lambda: REPO)
        head = git(REPO, "rev-parse", "HEAD")
        self.assertEqual(set(driver.T3_NOT_A_PIN), {"06efaa37ef8a01b2cf11f39715a885a3e4f8c10c",
                                                    "60669f9fc265bc6a0c1de331dd0834f687fe7d03"})
        for commit, (kind, why) in driver.T3_NOT_A_PIN.items():
            with self.subTest(commit[:10]):
                text = blob(REPO, commit, "src/stage0").decode("utf-8", "replace")
                self.assertTrue(any(key.endswith(f"-{HOST}.tar.xz")
                                    for key in driver.support().stage0_payload_pins(text)))
                self.assertEqual(driver.t3_not_a_pin(plan, head, commit, text), why)

    def test_an_earlier_pin_of_another_host_with_other_digests_is_not_T3(self):
        self.through_record()
        stage0 = self.stage0()
        darwin_row = f"dist/{SEED_DATE}/trustc-{SEED_VERSION}-trust-{DARWIN}.tar.xz"
        older = self.trust.commit_on(self.trust.head, {"src/stage0": stage0_body_edit(
            stage0, lambda body: stage0_set_row(body, darwin_row, "0" * 64)).encode()}, "an earlier Darwin pin")
        back = self.trust.commit_on(older, {"src/stage0": stage0.encode()}, "the Darwin pin of this cohort")
        self.assertEqual(self.commit(parent=back), 0, self.said)

    def test_the_host_proofs_are_exactly_the_record(self):
        self.through_record()
        extra = put(self.proofs() / "notes.txt", "x\n")
        try:
            self.refused(r"is not the record `record` writes: other files \['notes.txt'\]", self.commit)
        finally:
            extra.unlink()
        self.no_branch()
        evidence = self.proofs() / "fixed-point" / "native-outputs.json"
        aside = self.proofs().parent / "native-outputs.aside"
        evidence.rename(aside)
        try:
            self.refused(r"is not the record `record` writes: missing \['fixed-point/native-outputs.json'\]",
                         self.commit)
        finally:
            aside.rename(evidence)
        self.no_branch()

    def test_a_parent_door_file_with_two_door_lines_or_none_is_refused(self):
        self.through_record()
        door = blob(self.trust.repo, self.trust.head, driver.DOOR_FILE).decode()
        self.overridden(driver.DOOR_FILE, door + "\n" + driver.EMPTY_DOOR_LINE + "\n",
                        r"does not hold the door as it lands, .*\(2 line\(s\) start")
        self.overridden(driver.DOOR_FILE, door.replace(driver.EMPTY_DOOR_LINE + "\n", ""),
                        r"does not hold the door as it lands, .*\(0 line\(s\) start")

    def test_root_files_changed_after_record_or_prepare_are_refused(self):
        self.through_record()
        receipt = self.proofs() / "SEED-FIXED-POINT"
        self.changed(receipt, receipt.read_bytes() + b"\n", r"the recorded receipt .* is not the bytes its build recorded")
        record = self.proofs() / "host-record.json"
        self.changed(record, record.read_bytes() + b" ", r"the recorded host record .* is not the bytes its build recorded")
        candidate = self.plan.prepare_dir() / "stage0.candidate"
        self.changed(candidate, candidate.read_bytes() + b"\n",
                     r"the candidate src/stage0 .* is not the bytes its build recorded")
        self.assertEqual(self.commit(), 0, self.said)

    def test_T2_a_parent_of_another_commit_or_already_pinning_the_host_is_refused(self):
        self.through_record()
        stage0 = self.stage0()
        self.overridden("src/stage0", stage0_body_edit(stage0, lambda body: stage0_set_row(
            body, "compiler_git_commit_hash", "f" * 40)), r"T2: the parent .* pins compiler_git_commit_hash = 'f{40}'")
        row = f"dist/{SEED_DATE}/trustc-{SEED_VERSION}-trust-{HOST}.tar.xz"
        self.overridden("src/stage0", stage0 + f"{row}={self.candidate()[row]}\n", rf"T2: the parent .* already pins {HOST}")

    def test_T5_a_parent_whose_darwin_rows_or_manifest_are_not_the_candidates_is_refused(self):
        self.through_record()
        stage0, candidate = self.stage0(), self.candidate()
        darwin_row = f"dist/{SEED_DATE}/trustc-{SEED_VERSION}-trust-{DARWIN}.tar.xz"
        # A Darwin row changes.
        self.overridden("src/stage0", stage0_body_edit(stage0, lambda body: stage0_set_row(body, darwin_row, "0" * 64)),
                        rf"the parent's {re.escape(darwin_row)} is '[0-9a-f]{{64}}' in the candidate")
        # The candidate adds a row that is not this host's.
        self.overridden("src/stage0", stage0_body_edit(stage0, lambda body: stage0_set_row(body, darwin_row, None)),
                        r"the candidate adds .*this host adds exactly its eight rows")
        # The parent already pins the new manifest's hash.
        new = candidate["compiler_channel_manifest_hash"]
        self.overridden("src/stage0", stage0_body_edit(stage0, lambda body: stage0_set_row(
            body, "compiler_channel_manifest_hash", new)), r"compiler_channel_manifest_hash is '[0-9a-f]{64}', not the "
                        "new manifest's sha256")
        # The parent's committed manifest is not the one its src/stage0 pins.
        path = driver.PARENT_MANIFEST.format(date=SEED_DATE)
        manifest = blob(self.trust.repo, self.trust.head, path)
        self.overridden(path, manifest + b"\n# another\n", r"the parent's channel manifest is not the one its src/stage0 pins")
        # A Darwin table of the manifest changes (the parent's pin names that manifest).
        parsed = tomllib.loads(manifest.decode())
        name = sorted(name for name, pkg in parsed["pkg"].items() if DARWIN in (pkg.get("target") or {}))[0]
        parsed["pkg"][name]["target"][DARWIN]["xz_hash"] = "0" * 64
        other = stage0_prepare.dump_toml(parsed).encode()
        digest = hashlib.sha256(other).hexdigest()
        self.plan.parent_overrides = {path: other, "src/stage0": stage0_body_edit(stage0, lambda body: stage0_set_row(
            stage0_set_row(body, "compiler_channel_manifest_hash", digest), "rustfmt_channel_manifest_hash",
            digest)).encode()}
        try:
            self.refused(rf"pkg\.{re.escape(name)}\.target\.{DARWIN} changed", self.commit)
        finally:
            self.plan.parent_overrides = {}
        self.no_branch()

    def test_T5_T6_the_prepared_manifest_files_and_admission_are_the_candidates(self):
        self.through_record()
        out = self.plan.output_root()
        dated = out / "dist" / SEED_DATE / "channel-rust-trust.toml"
        self.changed(dated, dated.read_bytes() + b"\n",
                     r"channel-rust-trust.toml is not the channel manifest the candidate pins")
        top_sha = out / "dist" / "channel-rust-trust.toml.sha256"
        self.changed(top_sha, ("0" * 64 + "\n").encode(),
                     r"channel-rust-trust.toml.sha256 does not name the manifest's sha256")
        dated_sha = out / "dist" / SEED_DATE / "channel-rust-trust.toml.sha256"
        dated_sha.rename(dated_sha.with_name("aside"))
        try:
            self.refused(r"channel-rust-trust.toml.sha256 is not a regular file", self.commit)
        finally:
            dated_sha.with_name("aside").rename(dated_sha)
        self.no_branch()
        # The admission is the bytes prepare recorded (E10: admission public, public_upload true) ...
        admission = out / "trust-stage0-admission.json"
        original = admission.read_bytes()
        value = json.loads(original)
        public = (json.dumps({**value, "admission": "public", "public_upload": True}, indent=2) + "\n").encode()
        self.changed(admission, public, r"prepare.py's admission .*trust-stage0-admission.json is not the bytes its "
                                        r"build recorded")
        # ... and admits exactly the candidate's archives, even under a record that names other bytes.
        dropped = (json.dumps({**value, "payloads": value["payloads"][1:]}, indent=2) + "\n").encode()
        prepared = self.plan.prepare_record()
        record = prepared.read_bytes()
        changed = json.loads(record)
        changed["prepared"]["admission"]["sha256"] = hashlib.sha256(dropped).hexdigest()
        prepared.write_text(json.dumps(changed))
        try:
            self.changed(admission, dropped, r"trust-stage0-admission.json does not admit exactly")
        finally:
            prepared.write_bytes(record)
        self.assertEqual(self.commit(), 0, self.said)

    def test_T4_the_parent_host_table_is_the_cohort_mint_host_of_this_commit(self):
        self.through_record()
        ledger = blob(self.trust.repo, self.trust.head, driver.LEDGER_FILE).decode()
        table = f'[release.hosts."{DARWIN}"]'
        self.overridden(driver.LEDGER_FILE, ledger.replace(f'[release.hosts."{DARWIN}"', '[release.hosts."x86_64-apple-darwin"'),
                        r"T4: the parent's host table is x86_64-apple-darwin's")
        before, after = ledger.split(table)
        self.assertIn(f'source_commit = "{SOURCE.commit}"', after)
        self.overridden(driver.LEDGER_FILE, before + table + after.replace(
            f'source_commit = "{SOURCE.commit}"', f'source_commit = "{"e" * 40}"', 1),
            r"T4: the parent's host table is .* at 'e{40}'")

    def test_T11_an_orchestration_beside_the_parent_is_refused(self):
        self.plan.tool_head = self.trust.commit_on(self.trust.head, {"README.side": b"side\n"}, "beside")
        self.through_record()
        self.refused(r"T11: orchestration_commit .* is not an ancestor of the parent", self.commit)
        self.no_branch()

    def test_T10_the_rendered_ledger_and_the_door_read_back(self):
        self.through_record()
        render = driver.support().render_seed_ledger
        with mock.patch.object(driver.support(), "render_seed_ledger", lambda *a, **k: (lambda text, tag: (
                text + "\n[release.mint]\nsource_commit = \"x\"\n", tag))(*render(*a, **{**k, "mint_switch_line": False}))):
            self.refused(r"T10: the rendered ledger has 1 line\(s\) starting \[release.mint\], and TOML finds release.mint",
                         self.commit)
        self.no_branch()
        linux = f'[release.hosts."{HOST}"]\n'
        with mock.patch.object(driver.support(), "render_seed_ledger", lambda *a, **k: (lambda text, tag: (
                text.replace(linux, linux + 'extra = "x"\n', 1), tag))(*render(*a, **k))):
            self.refused(r"the rendered ledger's host tables do not read back as the two records", self.commit)
        self.no_branch()
        # A door with an entry beyond this host's is refused by the judge of commit 1.
        door = driver.door_text
        with mock.patch.object(driver, "door_text", lambda plan, parent, entry: door(
                plan, parent, {**entry, "x86_64-unknown-linux-gnu": {"commit": "a" * 40, "receipt_sha256": "b" * 64}})):
            self.refused(r"its FIXED_POINT_FIRST_HOSTS is .*not the one entry", self.commit)
        self.no_branch()

    def test_the_branch_door_judges_each_host_table_selected_and_captured(self):
        self.through_record()
        # Evidence edited after record: the branch's own capture of this host's table refuses it.
        evidence = self.proofs() / "fixed-point" / "native-outputs.json"
        self.changed(evidence, evidence.read_bytes().replace(b'"files"', b'"files" ', 1),
                     r"commit 1 is refused by the branch's own scripts/seed_host_ledger.py with its real door")
        load = self.plan.repo_module

        def judge(change):
            def loaded(repo, name):
                module = load(repo, name)
                if name == "seed_host_ledger":
                    change(module)
                return module
            return loaded

        def refuse_selection(module):
            def select(release, host):
                raise ValueError(f"no record is selected for {host}")
            module.select_host_record = select

        def refuse_parent_pins(module):
            capture = module.capture_host_record

            def captured(seed_root, pins, name, table):
                if not any(key.endswith(f"-{HOST}.tar.xz") for key in pins):
                    raise ValueError(f"{name}'s table does not hold against the parent's pins")
                return capture(seed_root, pins, name, table)
            module.capture_host_record = captured
        for change, words in ((refuse_selection, "no record is selected for"),
                              (refuse_parent_pins, f"{DARWIN}'s table does not hold against the parent's pins")):
            with self.subTest(words), mock.patch.object(self.plan, "repo_module", judge(change)):
                self.refused(rf"commit 1 is refused by the branch's own .* with its real door: {re.escape(words)}",
                             self.commit)
            self.no_branch()

    def test_the_corpus_re_pin_is_held_to_exactly_the_new_documents(self):
        self.through_record()
        corpus, head = self.plan.corpus, self.trust.head

        def stand_in(script):
            def made(repo, *words):
                return [sys.executable, "-c", script, *corpus(repo, *words), "--",
                        str(repo / driver.CORPUS_MANIFESTS[".toml"]), head, *words]
            return made
        drops = ("import pathlib, subprocess, sys\nat = sys.argv.index('--')\ndone = subprocess.run(sys.argv[1:at])\n"
                 "path, words = pathlib.Path(sys.argv[at + 1]), sys.argv[at + 3:]\n"
                 "if words == ['--write']:\n"
                 "    lines = path.read_text().split('\\n')\n"
                 "    first = next(i for i, line in enumerate(lines) if line.startswith('fixtures/'))\n"
                 "    path.write_text('\\n'.join(lines[:first] + lines[first + 1:]))\n"
                 "sys.exit(done.returncode)\n")
        write_fails = ("import subprocess, sys\nat = sys.argv.index('--')\ndone = subprocess.run(sys.argv[1:at])\n"
                       "sys.exit(1 if sys.argv[at + 3:] == ['--write'] else done.returncode)\n")
        tip_red = ("import subprocess, sys\nat = sys.argv.index('--')\nwords = sys.argv[at + 3:]\n"
                   "if words[:1] == ['--rev'] and words[1] != sys.argv[at + 2]:\n"
                   "    print('FINDING: the tip is red'); sys.exit(1)\n"
                   "sys.exit(subprocess.run(sys.argv[1:at]).returncode)\n")
        for script, pattern in (
                (drops, r"the re-pin of crates/trust-toml/tests/corpus_manifest.txt adds .* and drops \['fixtures/"),
                (write_fails, r"check_corpus_membership.py --write refused in the clone"),
                (tip_red, r"check_corpus_membership.py --rev [0-9a-f]{10} is red on the branch tip")):
            with self.subTest(pattern), mock.patch.object(self.plan, "corpus", stand_in(script)):
                self.refused(pattern, self.commit)
            self.no_branch()

    def test_a_branch_name_and_a_commit_directory_this_step_did_not_finish(self):
        self.through_record()
        for name in ("-x", "a..b", "has space"):
            with self.subTest(name):
                self.refused(rf"--branch '{re.escape(name)}' is not a plain branch name", self.commit, branch=name)
        self.plan.args.branch = BRANCH
        self.plan.commit_dir().mkdir()
        self.refused(r"exists and .* does not: it is not a branch this step finished", self.commit)
        self.assertFalse(driver.commit_record(self.plan).exists())

    def test_the_rules_on_what_is_written_hold_whatever_produces_it(self):
        # Each of these cannot be reached from a root `record` wrote (the earlier rules exclude it);
        # each is shown here on an input made by a stand-in, so it stays a rule and not a comment.
        self.through_record()
        proofs = driver.proof_files
        with mock.patch.object(driver, "proof_files", lambda plan, controls: {**proofs(plan, controls),
                                                                               "fixed-point/x.tar.xz": b"x"}):
            self.refused(r"T9: the add-host commit would carry .*fixed-point/x.tar.xz, an archive", self.commit)
        self.no_branch()
        inputs = driver.commit_inputs
        darwin_proof = f"{driver.SEED_DIR}/host-proofs/{DARWIN}/SEED-MINT"

        def touching_darwin(plan, parent, prepared, recorded):
            made = inputs(plan, parent, prepared, recorded)
            made["writes"][darwin_proof] = made["writes"]["src/stage0"]
            return made
        with mock.patch.object(driver, "commit_inputs", touching_darwin):
            self.refused(rf"T4: {re.escape(darwin_proof)} is another blob in commit 1", self.commit)
        self.no_branch()
        repin = driver.corpus_repin

        def more(plan, repo, parent, first, writes):
            return {**repin(plan, repo, parent, first, writes), "README.extra": b"x\n"}

        def branch_appears(plan, repo, parent, first, writes):
            git(repo, "update-ref", f"refs/heads/{BRANCH}", parent)
            return repin(plan, repo, parent, first, writes)
        for stand_in, pattern in ((more, r"T9: the branch changes .* and commit 2 \['README.extra', "),
                                  (branch_appears, rf"the branch {BRANCH} could not be created \(it exists\)")):
            with self.subTest(pattern), mock.patch.object(driver, "corpus_repin", stand_in):
                self.refused(pattern, self.commit)
            self.assertFalse(self.plan.commit_dir().exists())
            self.assertFalse(driver.commit_record(self.plan).exists())
        self.assertEqual(self.commit(), 0, self.said)


def blob(repo: Path, rev: str, path: str) -> bytes:
    return subprocess.run(["git", "-C", str(repo), "cat-file", "blob", f"{rev}:{path}"], check=True,
                          capture_output=True).stdout


def git_absent(repo: Path, rev: str, path: str) -> bool:
    return subprocess.run(["git", "-C", str(repo), "cat-file", "-e", f"{rev}:{path}"],
                          capture_output=True).returncode != 0


class VerifyCase(CommitCase):
    """A committed branch, cloned as a person clones it, with the 17 archives placed."""

    def clone(self) -> Path:
        self.through_record()
        self.assertEqual(self.commit(), 0, self.said)
        clone = self.parent / "V"
        git(self.parent, "clone", "-q", str(self.branch_repo()), str(clone))
        git(clone, "checkout", "-q", BRANCH)
        dated = clone / driver.SEED_DIR / "dist" / SEED_DATE
        for archive in sorted((self.plan.output_root() / "dist" / SEED_DATE).glob("*.tar.xz")):
            shutil.copyfile(archive, dated / archive.name)
        self.plan.args.repo, self.plan.args.rev, self.plan.args.rebuild = clone, "HEAD", False
        return clone

    def verify(self) -> int:
        return self.quiet(driver.verify_step, self.plan)


class VerifyTests(VerifyCase):
    def test_verify_judges_the_branch_with_its_own_scripts_and_writes_nothing_there(self):
        clone = self.clone()
        before = snapshot(clone)
        self.assertEqual(self.verify(), 0, self.said)
        self.assertRegex(self.said[-1], rf"verify: .*the 17 pinned archives are in place and every file the judges "
                                        r"read is the commit's; the real door names this receipt alone; the admission "
                                        r"and the ledger's release name exactly the pin; the recreator captured "
                                        rf"{HOST} validated-payloads, {DARWIN} "
                                        r"validated-payloads; \d+ archive members joined; .* graded "
                                        "unpinned-root-seed-ready")
        self.assertEqual(snapshot(clone), before)
        # Through the command line too: verify needs no root and takes no lock there.
        code, _out, err = CommandLineTests.main(self, "verify", "--repo", str(clone), "--commit", SOURCE.commit,
                                                "--host", HOST, "--root", str(self.parent / "no-such-root"),
                                                plan=CommitPlan)
        self.assertEqual((code, err), (0, ""))
        self.assertFalse((self.parent / "no-such-root").exists())

    def test_verify_refuses_each_tampered_input(self):
        clone = self.clone()
        dated = clone / driver.SEED_DIR / "dist" / SEED_DATE
        archive = dated / f"trustc-{SEED_VERSION}-trust-{HOST}.tar.xz"
        darwin = dated / f"targo-{SEED_VERSION}-trust-{DARWIN}.tar.xz"
        proofs = clone / driver.SEED_DIR / "host-proofs" / HOST
        head = git(clone, "rev-parse", "HEAD")

        # The archives: each pinned one with its bytes, and no other.
        for pattern, change, undo in (
                (r"missing \['trustc-.*-unknown-linux-gnu.tar.xz'\]", lambda: archive.rename(dated / "aside"),
                 lambda: (dated / "aside").rename(archive)),
                (r"other bytes \['targo-.*-apple-darwin.tar.xz'\]", lambda: darwin.write_bytes(darwin.read_bytes() + b"x"),
                 lambda: darwin.write_bytes(darwin.read_bytes()[:-1])),
                (r"not pinned \['trustc-9.9.9-trust-x.tar.xz'\]", lambda: put(dated / "trustc-9.9.9-trust-x.tar.xz", "x"),
                 lambda: (dated / "trustc-9.9.9-trust-x.tar.xz").unlink()),
                (r"has changes to tracked files", lambda: put(clone / "x.py", "tampered\n"),
                 lambda: git(clone, "checkout", "-q", "--", "x.py"))):
            with self.subTest(pattern):
                change()
                try:
                    self.refused(pattern, self.verify)
                finally:
                    undo()
        self.plan.args.rev = "HEAD~1"
        self.refused(r"--rev HEAD~1 is .* and the clone's HEAD is .*must be one commit", self.verify)
        self.plan.args.rev = "HEAD"
        # Tracked bytes, committed so the tree is clean: each is refused by the branch's own judges.
        receipt = proofs / "SEED-FIXED-POINT"
        evidence = proofs / "fixed-point" / "native-outputs.json"
        ledger = clone / driver.LEDGER_FILE
        for pattern, path, change in (
                (r"the clone's real door .* is .* and this branch adds exactly", receipt,
                 lambda text: text.replace("producer_custody=recorded-not-authenticated",
                                           "producer_custody=recorded-not-authenticatedd")),
                (r"recreate_bootstrap's capture of the clone's seed for aarch64-unknown-linux-gnu refuses: .*"
                 r"fixed-point C1", evidence, lambda text: text.replace('"files"', '"files" ', 1)),
                (r"recreate_bootstrap's capture of the clone's seed for aarch64-unknown-linux-gnu refuses", ledger,
                 lambda text: text.replace('admission_kind = "fixed-point-unpinned-root"',
                                           'admission_kind = "mint"'))):
            with self.subTest(pattern):
                path.write_text(change(path.read_text()))
                git(clone, "commit", "-qam", "tamper")
                try:
                    self.refused(pattern, self.verify)
                finally:
                    git(clone, "reset", "-q", "--hard", head)
        # The push rows: any red refuses.
        for name, pattern in (("check_ledger_pins", r"check_ledger_pins.py --rev .* is red on the branch .*"
                                                    "FINDING: fixture check_ledger_pins red"),
                              # The capture runs it first (recreate_bootstrap); verify's own row is VerifyRuleTests'.
                              ("check_seed_freshness", r"canonical seed freshness")):
            with self.subTest(name):
                put(self.trust.checks / name, "1")
                try:
                    self.refused(pattern, self.verify)
                finally:
                    (self.trust.checks / name).unlink()
        put(clone / "docs" / "unpinned.json", "{}\n")
        git(clone, "add", "-A")
        git(clone, "commit", "-qm", "an unpinned json")
        self.refused(r"check_corpus_membership.py --rev .* is red on the branch .*trust-json NEW docs/unpinned.json",
                     self.verify)
        git(clone, "reset", "-q", "--hard", head)
        self.assertEqual(self.verify(), 0, self.said)


class VerifyRuleTests(VerifyCase):
    """Each rule of `verify`, refused by its own words, on an input only it catches."""

    def committed(self, clone: Path, path: Path, change) -> None:
        path.write_text(change(path.read_text()))
        git(clone, "commit", "-qam", "tamper")

    def test_the_judged_files_are_the_commits_whatever_git_status_says(self):
        clone = self.clone()
        head = git(clone, "rev-parse", "HEAD")
        receipt_path = f"{driver.SEED_DIR}/host-proofs/{HOST}/SEED-FIXED-POINT"
        receipt = clone / receipt_path
        good = receipt.read_bytes()
        view = r"the files verify judges in .* are not [0-9a-f]{10}'s: "
        # E1: the branch does not track the receipt; the file left untracked would stand in for it.
        git(clone, "rm", "-q", "--cached", receipt_path)
        git(clone, "commit", "-qm", "untrack the receipt")
        self.refused(view + rf"files [0-9a-f]{{10}} does not track \['{re.escape(receipt_path)}'\]", self.verify)
        git(clone, "reset", "-q", "--hard", head)
        # E2b, E2: the branch carries other bytes of the receipt, or of the judge itself, and the
        # working tree the good ones under skip-worktree: git status says nothing.
        for path, change in ((receipt_path, lambda text: text.replace(
                "producer_custody=recorded-not-authenticated", "producer_custody=recorded-not-authenticatedd")),
                             (driver.DOOR_FILE, lambda text: text + "\n# another judge\n")):
            with self.subTest(path):
                was = (clone / path).read_bytes()
                self.committed(clone, clone / path, change)
                git(clone, "update-index", "--skip-worktree", path)
                (clone / path).write_bytes(was)
                self.assertEqual(git(clone, "status", "--porcelain", "--untracked-files=no"), "")
                try:
                    self.refused(view + rf"files whose bytes are not [0-9a-f]{{10}}'s \['{re.escape(path)}'\]",
                                 self.verify)
                finally:
                    git(clone, "update-index", "--no-skip-worktree", path)
                    git(clone, "reset", "-q", "--hard", head)
        # An edit git's stat check does not see (the clone's own config; the same size and mtime, an
        # mtime older than the index, so the entry is not racily clean and is not hashed again).
        git(clone, "config", "core.checkStat", "minimal")
        git(clone, "config", "core.trustctime", "false")
        old = time.time() - 3600
        os.utime(receipt, (old, old))
        git(clone, "update-index", "--refresh")
        receipt.write_bytes(good.replace(b"producer_custody=", b"producer_Custody=", 1))
        os.utime(receipt, (old, old))
        try:
            self.assertEqual(git(clone, "status", "--porcelain", "--untracked-files=no"), "")
            self.refused(view + rf"files whose bytes are not [0-9a-f]{{10}}'s \['{re.escape(receipt_path)}'\]",
                         self.verify)
        finally:
            receipt.write_bytes(good)
            git(clone, "config", "--unset", "core.checkStat")
            git(clone, "config", "--unset", "core.trustctime")
        # A tracked file that is not there.
        missing =clone / driver.SEED_DIR / "dist" / "channel-rust-trust.toml.sha256"
        missing.unlink()
        self.refused(view + r"files [0-9a-f]{10} tracks that are not there "
                            r"\['bootstrap/trust-stage0/dist/channel-rust-trust.toml.sha256'\]", self.verify)
        git(clone, "checkout", "-q", "--", ".")
        # What else a person might copy from the producing root next to the archives.
        stray = put(clone / driver.SEED_DIR / "trust-stage0-shared-kept.json", "{}\n")
        self.refused(view + r"files [0-9a-f]{10} does not track \['bootstrap/trust-stage0/trust-stage0-shared-kept.json'\]",
                     self.verify)
        stray.unlink()
        # The index flags: a skip-worktree edit outside what the judges read (leg 1 builds it).
        for flag in ("--skip-worktree", "--assume-unchanged"):
            with self.subTest(flag):
                git(clone, "update-index", flag, "x.py")
                put(clone / "x.py", "tampered\n")
                try:
                    self.assertEqual(git(clone, "status", "--porcelain", "--untracked-files=no"), "")
                    self.refused(r"index entries git status does not compare .*x.py", self.verify)
                finally:
                    git(clone, "update-index", flag.replace("--", "--no-"), "x.py")
                    git(clone, "checkout", "-q", "--", "x.py")
        # A link the judges would follow.
        link = clone / "scripts" / "judge-link.py"
        link.symlink_to("seed_host_ledger.py")
        self.refused(view + r"links or special files \['scripts/judge-link.py'\]", self.verify)
        link.unlink()
        # Python's own byte code, which a run of the clone's scripts leaves, is not a file of the commit.
        put(clone / "scripts" / "__pycache__" / "not-a-module.cpython-0.pyc", "byte code\n")
        self.assertEqual(self.verify(), 0, self.said)

    def test_the_door_names_this_host_alone(self):
        clone = self.clone()
        door = clone / driver.DOOR_FILE
        entry = {HOST: {"commit": SOURCE.commit, "receipt_sha256": sha(clone / driver.SEED_DIR / "host-proofs" / HOST
                                                                       / "SEED-FIXED-POINT")}}
        self.committed(clone, door, lambda text: text.replace(driver.DOOR_PREFIX + json.dumps(entry), driver.DOOR_PREFIX + json.dumps(
            {**entry, "x86_64-unknown-linux-gnu": {"commit": SOURCE.commit, "receipt_sha256": "0" * 64}})))
        self.refused(r"the clone's real door .* is .*x86_64-unknown-linux-gnu.*, and this branch adds exactly", self.verify)

    def test_the_admission_and_the_ledger_release_name_exactly_the_pin(self):
        clone = self.clone()
        head = git(clone, "rev-parse", "HEAD")
        admission, ledger = clone / driver.ADMISSION_FILE, clone / driver.LEDGER_FILE

        def admitted(**changes):
            def change(text):
                value = json.loads(text)
                return json.dumps({**value, **{key: change(value) if callable(change) else change
                                               for key, change in changes.items()}}, indent=2) + "\n"
            return change
        tag = f"trust-stage0-{SEED_DATE}-{SOURCE.commit[:9]}"
        cases = (
            # E9: the last row dropped, another manifest, published.
            (admission, admitted(payloads=lambda value: value["payloads"][:-1]), r"its 16 payload rows are not the 17"),
            (admission, admitted(manifest_hash="0" * 64), r"manifest_hash is '0{64}', not"),
            (admission, admitted(public_upload=True), r"public_upload is True, not False"),
            (admission, admitted(admission="public"), r"admission is 'public', not 'internal'"),
            (admission, admitted(promotion_decision="hold-internal"), r"promotion_decision is 'hold-internal'"),
            (admission, admitted(schema="another"), r"schema is 'another'"),
            (admission, admitted(git_commit_hash="f" * 40), r"git_commit_hash is 'f{40}'"),
            (admission, admitted(payloads=lambda value: value["payloads"] + value["payloads"][:1]),
             r"its 18 payload rows are not the 17"),
            (admission, admitted(payloads=lambda value: value["payloads"] + ["not a row"]),
             r"its 18 payload rows are not the 17"),
            (admission, admitted(date="2026-01-01"), rf"date is '2026-01-01', not '{SEED_DATE}'"),
            # E4: the release clones fetch from, and what it checks.
            (ledger, lambda text: text.replace(f'tag = "{tag}"', f'tag = "trust-stage0-{SEED_DATE}-0000000000"'),
             rf"\[release\] tag is 'trust-stage0-{SEED_DATE}-0000000000', not '{tag}'"),
            (ledger, lambda text: text.replace("checksums = [\n", f'checksums = [\n  "sha256:{"0" * 64}", # extra\n'),
             r"checksums are not exactly the 17 pinned archives' sha256"),
            (ledger, lambda text: text.replace("--pattern '*.tar.xz'", "--pattern '*'"),
             r"\[release\] authenticated_fetch is"),
            (ledger, lambda text: text.replace("/releases/tag/", "/releases/tags/"), r"\[artifact_root\] path is"),
            (ledger, lambda text: text.replace('repo = "fixture/trust"', 'repo = ""', 1), r"\[release\] repo is ''"),
        )
        for path, change, pattern in cases:
            with self.subTest(pattern):
                self.committed(clone, path, change)
                try:
                    self.refused(pattern, self.verify)
                finally:
                    git(clone, "reset", "-q", "--hard", head)
        self.assertEqual(driver.ADMISSION_SCHEMA, stage0_prepare.STAGE0_ADMISSION_SCHEMA)
        self.assertEqual(self.verify(), 0, self.said)

    def test_not_a_clone_and_a_pin_of_another_commit(self):
        clone = self.clone()
        head = git(clone, "rev-parse", "HEAD")
        empty = self.parent / "not-a-clone"
        empty.mkdir()
        self.plan.args.repo = empty
        self.refused(r"is not a clone \(no .git\)", self.verify)
        self.plan.args.repo = clone
        self.committed(clone, clone / "src" / "stage0", lambda text: stage0_body_edit(
            text, lambda body: stage0_set_row(body, "compiler_git_commit_hash", "f" * 40)))
        self.refused(r"src/stage0 pins compiler_git_commit_hash = 'f{40}', not", self.verify)
        git(clone, "reset", "-q", "--hard", head)
        self.assertEqual(self.verify(), 0, self.said)

    def test_each_part_of_the_capture_the_join_and_verifys_own_freshness_row(self):
        self.clone()
        real = self.plan.seed_capture

        def altered(change):
            def capture(recreate, repo, host, build_root=None):
                lineage = json.loads(json.dumps(real(recreate, repo, host)))
                change(lineage, host)
                return lineage
            return capture

        def records(lineage):
            return lineage["authority"]["seed_ledger"]["host_records"]
        cases = (
            (lambda lineage, host: lineage.update(status="rejected"), r"its status is 'rejected'"),
            (lambda lineage, host: lineage.update(admission_status="public-admitted"),
             r"its admission is 'public-admitted', not internal-admitted"),
            (lambda lineage, host: records(lineage)["records"].pop(DARWIN), r"it captured the records of"),
            (lambda lineage, host: records(lineage).update(selected_host="x"), r"it captured the records of"),
            (lambda lineage, host: records(lineage).pop("fixed_point_validator_sha256", None) if host == HOST else None,
             r"its selected record is not the fixed-point kind"),
            (lambda lineage, host: lineage.update(errors=["the archive is not its pin"]) if host == DARWIN else None,
             r"the archive is not its pin"),
        )
        for change, pattern in cases:
            with self.subTest(pattern), mock.patch.object(self.plan, "seed_capture", altered(change)):
                self.refused(rf"recreate_bootstrap's capture of the clone's seed for .* refuses: .*{pattern}", self.verify)
        load = self.plan.repo_module

        def joins_refused(repo, name):
            module = load(repo, name)
            if name == "seed_host_ledger":
                def refuse(*args, **kwargs):
                    raise ValueError("a member is not its row")
                module.fixed_point_module = lambda: type("M", (), {"check_archive_joins": staticmethod(refuse)})
            return module
        with mock.patch.object(self.plan, "repo_module", joins_refused):
            self.refused(r"the full archive join refuses: a member is not its row", self.verify)
        with mock.patch.object(self.plan, "freshness", lambda repo: [
                sys.executable, "-c", "print('FINDING: verify own freshness red'); raise SystemExit(1)"]):
            self.refused(r"check_seed_freshness.py is red on the branch .*verify own freshness red", self.verify)
        self.assertEqual(self.verify(), 0, self.said)


class RebuildPlan(CommitPlan):
    """CommitPlan whose leg-1 commands are stand-ins: the seed-mode build of the
    clone's own source, its capture and its lineage. Leg 2 runs the stand-ins of
    the roles (the fake x.py, the real installer and stage2 manifest)."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.leg1: dict = {"pin_admission": True, "capture": "validated"}
        self.replay_setup = lambda replay: None     # what a test gives the replay's plan

    def seed_sysroot(self, payloads, stage0_file, out):
        return self.script("seed-sysroot", "pathlib.Path(sys.argv[2]).mkdir()\n"
                           "pathlib.Path(sys.argv[2], 'bin').mkdir()\nprint('{\"kind\": \"seed-sysroot\"}')\n",
                           str(out))

    def admit_for(self, stage0, repo, target):
        return self.script("admit-seed", "print(json.dumps({'kind': 'stage0-admission', 'pinned_seed': {}}))\n")

    def seed_config_for(self, worktree):
        return self.script("seed-config-clone", "print('{}')\n")

    def closure_for(self, worktree, stage0, verb):
        return self.script(f"closure-{verb}", "print('closure ready')\n")

    @staticmethod
    def seed_record(ledger, jobs, record: dict | None = None, **jobserver) -> dict:
        """Leg 1's run record as `run --fifo-jobserver` writes it, with `jobserver` changed
        and `record`'s keys added; its paths are under the ledger as that resolves it."""
        ledger = Path(os.path.realpath(ledger))
        path = str(ledger / "tmp" / "jobserver.fifo")
        return {"kind": "rung", "label": "verify-seed", "rc": 0, "no_stock_evidence": True, "python": RUN_PYTHON,
                "environment": {"MAKEFLAGS": f"-j{jobs} --jobserver-auth=fifo:{path}"},
                "jobserver": {"kind": "fifo", "path": path, "jobs": jobs, "tokens": jobs - 1,
                              "tokens_at_end": jobs - 1, "path_unchanged": True, "make_adapter": make_adapter(ledger),
                              **jobserver}, **(record or {})}

    def run_seed_mode(self, worktree, ledger, admission, lean, tools, jobs, *, record: dict | None = None,
                      **jobserver):
        # The real command line asks for the FIFO jobserver; its record shows it.
        assert "--fifo-jobserver" in super().run_seed_mode(worktree, ledger, admission, lean, tools, jobs)
        return self.script("run-seed-mode", "print(sys.argv[2])\n", json.dumps(self.seed_record(ledger, jobs, record,
                                                                                                 **jobserver)))

    def leg_env(self, work):
        return {**super().leg_env(work), "FAKE_CALLS": str(self.calls)}

    def seed_capture(self, recreate, repo, host, build_root=None):
        if build_root is None:
            return super().seed_capture(recreate, repo, host)
        return {"status": self.leg1["capture"], "errors": []}

    def lineage(self, admission, run, stage2, repo):
        module = self.repo_module(repo, "seed_host_ledger").fixed_point_module()
        fields = module.parse_receipt((repo / driver.SEED_DIR / "host-proofs" / HOST / "SEED-FIXED-POINT")
                                      .read_bytes()).fields
        pin = {"kind": module.KIND, "root_disclosure": module.root_disclosure(fields)} if self.leg1["pin_admission"] \
            else None
        return self.script("lineage", f"print(json.dumps({{'kind': 'lineage', 'root': {{'pin_admission': {pin!r}}}}}))\n")

    def replay_plan(self, root):
        replay = super().replay_plan(root)
        replay.behaviour = {key: dict(value) for key, value in self.behaviour.items()}
        replay.stage2_for = {**self.stage2_for, driver.REPLAY_LABEL: STAGE2_SEED}
        replay.archives, replay.components = dict(self.archives), self.components
        replay.parent_repo, replay.tool_head, replay.tool_sha256 = self.parent_repo, self.tool_head, self.tool_sha256
        self.replay_setup(replay)
        return replay

    def checkout_for(self, repo, commit, target):
        # The fixture's commit lives in SOURCE.repo, with its module store.
        return driver.refresh.clone_rung(SOURCE.repo, commit, target)


class RebuildTests(VerifyCase):
    plan_class = RebuildPlan

    def rebuild(self, work: str) -> int:
        self.plan.args.rebuild, self.plan.args.work = True, self.parent / work
        return self.verify()

    def test_verify_rebuild_runs_both_legs_and_says_not_comparable_for_other_native_outputs(self):
        clone = self.clone()
        produced = self.root.with_name(self.root.name + ".produced")
        self.plan.args.produced, self.plan.args.ninja = produced, SOURCE.ninja
        self.plan.args.lean_library, self.plan.args.jobs = self.plan.lean_library, 3
        # The recorded root is still there: the replay would build over it.
        self.refused(rf"the recorded root {self.root} is there, and this verify did not make it", self.rebuild, "w0")
        self.root.rename(produced)
        self.assertEqual(self.rebuild("w1"), 0, self.said)
        self.assertRegex("\n".join(self.said), r"(?s)leg 1 passed: .*leg 2 passed: the pinned archives rebuilt "
                                               rf"{SOURCE.commit[:10]} at {self.root} to the receipt's \d+ rows")
        self.assertIn("the exit test passed", self.said[-2])
        replay = json.loads((self.parent / "w1" / "replay-leg.json").read_text())
        self.assertEqual(replay["root"], str(self.root))
        # Done once: the same command repeats neither leg.
        self.said.clear()
        self.assertEqual(self.rebuild("w1"), 0)
        self.assertTrue(any("leg 1 already done" in line for line in self.said))
        self.assertTrue(any("leg 2 already done" in line for line in self.said))
        # What publish reads: the exit test of this head, its receipt, its pin and its 17 archives.
        head = git(clone, "rev-parse", "HEAD")
        passed = json.loads((self.parent / "w1" / "exit-test.json").read_text())
        receipt = clone / driver.SEED_DIR / "host-proofs" / HOST / "SEED-FIXED-POINT"
        self.assertEqual({key: passed[key] for key in ("schema", "commit", "host", "head", "receipt_sha256",
                                                       "stage0_sha256", "produced")},
                         {"schema": driver.EXIT_TEST_SCHEMA, "commit": SOURCE.commit, "host": HOST, "head": head,
                          "receipt_sha256": sha(receipt), "stage0_sha256": sha(clone / "src" / "stage0"),
                          "produced": str(produced)})
        self.assertEqual(len(passed["archives"]), 17)
        self.assertRegex(self.said[-1], rf"next \(design step 17\): .*mv {re.escape(str(produced))} "
                                        rf"{re.escape(str(self.root))}\), then .*publish --exit-test")
        # E11: --work is bound to what it was made for. Another head is not passed by the old legs ...
        put(clone / "compiler-change.txt", "a change after the exit test\n")
        git(clone, "add", "compiler-change.txt")
        git(clone, "commit", "-qm", "a change")
        self.refused(rf"holds leg 1 of {{\"head\": \"{head}\"}} .*Nothing was started.*Move .*w1 aside",
                     self.rebuild, "w1")
        git(clone, "reset", "-q", "--hard", head)
        # ... nor is another produced root by the old leg 2.
        moved = produced.with_name(produced.name + "-moved")
        produced.rename(moved)
        self.plan.args.produced = moved
        try:
            self.refused(r"holds leg 2 of \{.*\"produced\": .*Nothing was started", self.rebuild, "w1")
        finally:
            moved.rename(produced)
            self.plan.args.produced = produced
        # Files of a leg with nothing saying what they were made for are not reused.
        put(self.parent / "w4" / "seed.run.json", "{}\n")
        self.refused(r"w4 holds \['seed.run.json'\] of leg 1 and no seed-leg.binding.json", self.rebuild, "w4")
        # Native outputs that are not the record's: not comparable, exit 3, not a pass.
        shutil.rmtree(self.root)
        llc = produced / "kept" / "p-build-tree" / HOST / "llvm" / "bin" / "llc"
        original = llc.read_bytes()
        llc.write_bytes(original + b" rebuilt")
        with self.assertRaisesRegex(driver.NotComparable, r"not comparable: the LLVM and lld .* are not the record's "
                                                           r"native outputs .* This is not a pass"):
            self.rebuild("w2")
        llc.write_bytes(original)
        shutil.rmtree(self.root)
        self.plan.args.work = self.parent / "w3"
        llc.write_bytes(original + b" rebuilt")
        # Use the fixture's canonical root: macOS's /var alias must not mask the
        # native-output refusal. Nothing in this test may write beside a real seed.
        beside = sorted(driver.ROOT_PARENT.iterdir()) if driver.ROOT_PARENT.is_dir() else []
        code, _out, err = CommandLineTests.main(
            self, "verify", "--repo", str(clone), "--commit", SOURCE.commit, "--host", HOST, "--rebuild",
            "--root", str(self.root), "--produced", str(produced), "--work", str(self.parent / "w3"), "--lean-library",
            str(self.plan.lean_library), "--ninja", str(SOURCE.ninja), "--jobs", "3", plan=self.cli_plan())
        llc.write_bytes(original)
        self.assertEqual(code, 3, err)
        self.assertIn("not comparable", err)
        self.assertEqual(sorted(driver.ROOT_PARENT.iterdir()) if driver.ROOT_PARENT.is_dir() else [], beside,
                         f"the command-line case wrote beside the default root in {driver.ROOT_PARENT}")

    def cli_plan(self):
        case = self

        class Configured(RebuildPlan):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                case.configure(self)
                self.parent_repo, self.tool_head = case.trust.repo, case.trust.head
                # The stand-ins log their calls beside the plan's root, which for this plan is the
                # driver's default root: log them in the case's own temporary directory instead.
                self.calls = case.plan.calls
        return Configured

    def test_each_leg_refuses_what_it_cannot_hold_to_the_record(self):
        self.clone()
        produced = self.root.with_name(self.root.name + ".produced")
        self.root.rename(produced)
        self.plan.args.produced, self.plan.args.ninja = produced, SOURCE.ninja
        self.plan.args.lean_library, self.plan.args.jobs = self.plan.lean_library, 3
        self.plan.args.rebuild, self.plan.args.work = True, None
        self.refused(r"verify --rebuild needs --work", self.verify)
        # Leg 1: the lineage's root must carry the fixed-point admission; the capture must be validated.
        self.plan.leg1["pin_admission"] = False
        self.refused(r"the lineage's root does not carry the fixed-point admission", self.rebuild, "l1")
        self.plan.leg1.update(pin_admission=True, capture="validated-payloads")
        self.refused(r"after leg 1 the recreator's capture of the hydrated seed is 'validated-payloads', not "
                     "validated", self.rebuild, "l2")
        self.plan.leg1["capture"] = "validated"
        # Leg 2: the regenerated base config must be the recorded one.

        def other_config(replay):
            replay.seed_config = lambda: replay.script("seed-config", (
                "config = pathlib.Path(sys.argv[2]) / 'bootstrap.toml'\n"
                "config.write_text('profile = \"another\"\\n')\n"
                "print(json.dumps({'kind': 'seed-config', 'config': str(config), 'sha256': sha(config)}))\n"),
                str(replay.src))
        self.plan.replay_setup = other_config
        self.refused(r"the regenerated base config .* and the receipt's base_config_sha256 is", self.rebuild, "l3")
        shutil.rmtree(self.root)
        # Leg 2: the replay's stage2 must be the receipt's rows outside not_reproduced.

        def another_driver(replay):
            replay.stage2_for[driver.REPLAY_LABEL] = {**STAGE2_SEED, "lib/librustc_driver-fixture.so": "\x7fELF other"}
        self.plan.replay_setup = another_driver
        self.refused(r"the pinned archives did not rebuild their own source to the receipt's rows: 1 file\(s\) differ "
                     r"outside not_reproduced \(the first: lib/librustc_driver-fixture.so", self.rebuild, "l4")


class RebuildRuleTests(VerifyCase):
    """Each rule of `verify --rebuild`, refused by its own words; every case in a new --work."""
    plan_class = RebuildPlan

    def rebuild(self, work: str) -> int:
        self.plan.args.rebuild, self.plan.args.work = True, self.parent / work
        return self.verify()

    def ready(self) -> tuple[Path, Path]:
        clone = self.clone()
        produced = self.root.with_name(self.root.name + ".produced")
        self.root.rename(produced)
        self.plan.args.produced, self.plan.args.ninja = produced, SOURCE.ninja
        self.plan.args.lean_library, self.plan.args.jobs = self.plan.lean_library, 3
        return clone, produced

    def lineage_with(self, pin_of):
        plan = self.plan

        def lineage(admission, run, stage2, repo):
            module = plan.repo_module(repo, "seed_host_ledger").fixed_point_module()
            fields = module.parse_receipt((repo / driver.SEED_DIR / "host-proofs" / HOST / "SEED-FIXED-POINT")
                                          .read_bytes()).fields
            return plan.script("lineage", "print(json.dumps({'kind': 'lineage', 'root': {'pin_admission': "
                                          f"{pin_of(module, fields)!r}}}}}))\n")
        return lineage

    def test_leg_1_through_a_linked_work_holds_its_run_to_the_ledger_as_the_run_resolves_it(self):
        self.ready()
        (self.parent / "real-w").mkdir()
        (self.parent / "linked-w").symlink_to(self.parent / "real-w")
        # seed_staircase.py resolves --ledger: its record names real-w, which is the same ledger.
        self.assertEqual(self.rebuild("linked-w"), 0, self.said)
        self.assertTrue((self.parent / "real-w" / "seed-leg.json").is_file())

    def test_leg_1_refuses_what_it_cannot_hold_to_the_record(self):
        clone, _produced = self.ready()
        self.refused(r"--work .* is inside the clone", self.rebuild, str(clone / "w"))
        (self.parent / "held").mkdir()
        with open(self.parent / "held" / "verify.lock", "a+") as held:
            fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.refused(r"another verify --rebuild holds", self.rebuild, "held")
        plan = self.plan
        cases = (
            ("run_seed_mode", lambda *a: plan.script("run-seed-mode", "sys.exit(1)\n"),
             r"leg 1's seed-mode build of .* did not end clean"),
            ("run_seed_mode", lambda *a: plan.script("run-seed-mode", (
                "print(json.dumps({'kind': 'rung', 'label': 'verify-seed', 'rc': 0, 'no_stock_evidence': False}))\n")),
             r"leg 1's run record is not clean: the no-stock evidence is not clean"),
            # A run without the FIFO jobserver, or whose jobserver lost a token, is not leg 1's clean run.
            ("run_seed_mode", lambda *a: plan.script("run-seed-mode", (
                "print(json.dumps({'kind': 'rung', 'label': 'verify-seed', 'rc': 0, 'no_stock_evidence': True}))\n")),
             r"leg 1's run record is not clean: the build's MAKEFLAGS was None, not '-j3 --jobserver-auth=fifo:"
             r".*/ledger/tmp/jobserver.fifo'; the run record shows no jobserver"),
            ("run_seed_mode", lambda *a: RebuildPlan.run_seed_mode(plan, *a, tokens_at_end=1),
             r"leg 1's run record is not clean: its jobserver held 1 token\(s\) when x.py had exited, not the 2"),
            # A deficit that meets every other condition of SEED-TOKEN-LEAK-STAGE0-1 is still refused:
            # leg 1 judges no stage0 admission (it builds from the pinned seed, which contains the fix).
            ("run_seed_mode", lambda *a: RebuildPlan.run_seed_mode(plan, *a, tokens_at_end=1, record={
                "process_census": dict(TokenLeakTests.CENSUS)}),
             r"leg 1's run record is not clean: its jobserver held 1 token\(s\) when x.py had exited, not the 2 it was "
             rf"given: a process ended holding a token, or outlived x.py with one; {TokenLeakTests.RULE}"
             rf"{re.escape(driver.TOKEN_STAGE0_NOT_JUDGED)}\. The exit test is not passed$"),
            ("run_seed_mode", lambda worktree, ledger, *a: RebuildPlan.run_seed_mode(
                plan, worktree, ledger.with_name("elsewhere"), *a),
             r"leg 1's run record is not clean: the build's MAKEFLAGS was .*elsewhere/tmp/jobserver.fifo'"),
            ("lineage", self.lineage_with(lambda module, fields: {"kind": "mint",
                                                                  "root_disclosure": module.root_disclosure(fields)}),
             r"the lineage's root does not carry the fixed-point admission"),
            ("lineage", self.lineage_with(lambda module, fields: {"kind": module.KIND, "root_disclosure": {}}),
             r"the lineage's root does not carry the fixed-point admission"))
        for number, (name, stand_in, pattern) in enumerate(cases):
            with self.subTest(pattern), mock.patch.object(plan, name, stand_in):
                self.refused(pattern, self.rebuild, f"l{number}")
            self.assertFalse((self.parent / f"l{number}" / "seed-leg.json").exists())

    def test_leg_2_refuses_what_it_cannot_hold_to_the_record(self):
        _clone, produced = self.ready()
        plan, number = self.plan, iter(range(100))

        def again(pattern, prepare=None, undo=None):
            if prepare:
                prepare()
            try:
                self.refused(pattern, self.rebuild, f"m{next(number)}")
            finally:
                if undo:
                    undo()
                if self.root.exists():
                    shutil.rmtree(self.root)
        empty = self.parent / "empty"
        empty.mkdir()
        plan.args.produced = empty
        again(r"--produced .* is not the produced root")
        plan.args.produced = produced
        inputs_file = produced / "inputs" / "inputs.json"
        inputs_bytes = inputs_file.read_bytes()
        inputs = json.loads(inputs_bytes)

        def inputs_with(**changes):
            return lambda: inputs_file.write_text(json.dumps({**inputs, **changes}))

        def restore_inputs():
            inputs_file.write_bytes(inputs_bytes)
        # The produced root's setup record binds what the branch's receipt and evidence bind.
        for changes, words in (
                ({"cargo_home": {**inputs["cargo_home"], "manifest_sha256": "0" * 64}},
                 "the cargo-home input manifest sha256"),
                ({"cargo_home": {**inputs["cargo_home"], "trees": {"registry/index": "0" * 64}}}, "the cargo-home trees"),
                ({"lean": {**inputs["lean"], "manifest_sha256": "0" * 64}}, "the Lean input manifest sha256"),
                ({"lean": {**inputs["lean"], "library": "/nonexistent/lib"}}, "the Lean library"),
                ({"ninja": {**inputs["ninja"], "sha256": "0" * 64}}, "ninja's sha256")):
            again(rf"did not bind the inputs the branch's receipt and evidence bind: {re.escape(words)} is",
                  inputs_with(**changes), restore_inputs)
        with mock.patch.object(driver, "produced_problems", lambda *a: []):
            again(r"Lean library .* is not under", inputs_with(lean={**inputs["lean"], "library": "/nonexistent/lib"}),
                  restore_inputs)
        again(r"the regenerated rung config has sha256", inputs_with(jobs=inputs["jobs"] + 1), restore_inputs)

        def dirty(repo, commit, target):
            made = driver.refresh.clone_rung(SOURCE.repo, commit, target)
            (target / "untracked-by-a-test.rs").write_text("x\n")
            return made
        with mock.patch.object(plan, "checkout_for", dirty):
            again(r"is not a clean checkout of")

        def appended(path):
            was = path.read_bytes()
            return (lambda: path.write_bytes(was + b"\n")), (lambda: path.write_bytes(was))
        for path, pattern in ((produced / "tools" / "ninja", r"the copied ninja is not the one the produced root bound"),
                              (produced / "inputs" / "clean-lean-inputs.json",
                               r"Lean input manifest is not the one its setup bound")):
            change, undo = appended(path)
            again(pattern, change, undo)
        index = produced / "ledger" / "cargo-home" / "registry" / "index"
        existed = index.exists()
        again(r"the copied cargo home is not the one the produced root bound",
              lambda: (index.mkdir(parents=True, exist_ok=True), (index / "extra.txt").write_text("x")),
              lambda: shutil.rmtree(index) if not existed else (index / "extra.txt").unlink())
        for behaviour, pattern in (({"exit": 2}, r"leg 2's replay build did not end clean"),
                                   ({"record": {"no_stock_evidence": False}}, r"the replay's run record is not clean"),
                                   ({"record": {"jobserver": None}},
                                    r"the replay's run record is not clean: the run record shows no jobserver"),
                                   ({"jobserver": {"path_unchanged": False}},
                                    r"the replay's run record is not clean: its jobserver's path .*/ledger/tmp/"
                                    r"jobserver.fifo did not name the FIFO when x.py had exited"),
                                   # Every other condition of SEED-TOKEN-LEAK-STAGE0-1 met, and still refused:
                                   # leg 2 judges no stage0 admission (it builds from the pinned archives).
                                   ({"jobserver": {"tokens_at_end": 1}},
                                    r"the replay's run record is not clean: its jobserver held 1 token\(s\) when x.py "
                                    r"had exited, not the 2 it was given: a process ended holding a token, or outlived "
                                    rf"x.py with one; {TokenLeakTests.RULE}"
                                    rf"{re.escape(driver.TOKEN_STAGE0_NOT_JUDGED)}\. The exit test is not passed$"),
                                   ({"also": {f"build/{HOST}/llvm/bin/llc": "rebuilt"}},
                                    r"not comparable: the replay build changed the LLVM and lld")):
            def setup(replay, behaviour=behaviour):
                replay.behaviour[driver.REPLAY_LABEL] = {**replay.behaviour.get(driver.REPLAY_LABEL, {}), **behaviour}
            plan.replay_setup = setup
            again(pattern)
        plan.replay_setup = lambda replay: None
        self.assertEqual(self.rebuild("final"), 0, self.said)

    def test_publish_takes_the_exit_test_this_wrote_once_the_produced_root_is_back(self):
        _clone, produced = self.ready()
        self.assertEqual(self.rebuild("w"), 0, self.said)
        self.root.rename(self.root.with_name(self.root.name + ".replay"))
        produced.rename(self.root)
        agh_stand_in(self)
        self.plan.args.exit_test = self.parent / "w"
        self.assertEqual(self.quiet(driver.publish_step, self.plan), 0, self.said)
        published = self.kept("publish.json")
        self.assertEqual(published["exit_test"], {"path": str(self.parent / "w" / "exit-test.json"),
                                                  "sha256": sha(self.parent / "w" / "exit-test.json")})


AGH = r'''#!{python}
import hashlib, json, pathlib, shutil, sys
state, store, log = pathlib.Path({state!r}), pathlib.Path({store!r}), pathlib.Path({log!r})
argv = sys.argv[1:]
with open(log, "a") as handle:
    handle.write(json.dumps(argv) + "\n")
assets = json.loads(state.read_text()) if state.is_file() else {{}}
sha = lambda path: hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
behaviour = json.loads(pathlib.Path({behaviour!r}).read_text()) if pathlib.Path({behaviour!r}).is_file() else {{}}
if "--clobber" in argv:
    print("the stand-in never clobbers", file=sys.stderr); sys.exit(9)
verb = argv[:2]
if verb == ["release", "assets"]:
    assert argv[4:] == ["--format", "json"], argv
    rows = [{{"name": name, "digest": row["digest"], "state": behaviour.get("state", "uploaded")}}
            for name, row in sorted(assets.items())]
    print(json.dumps(rows + rows[:1] if behaviour.get("dupes") else rows))
    if behaviour.get("assets_rc"):
        sys.exit(1)
elif verb == ["release", "upload"]:
    if behaviour.get("upload_fails"):
        print("upload refused", file=sys.stderr); sys.exit(1)
    if behaviour.get("upload_noop"):
        sys.exit(0)
    for path in argv[4:]:
        name = pathlib.Path(path).name
        if name in assets and assets[name]["digest"] != "sha256:" + sha(path):
            print(f"{{name}} exists with other bytes", file=sys.stderr); sys.exit(1)
        store.mkdir(exist_ok=True)
        shutil.copyfile(path, store / name)
        assets[name] = {{"digest": "sha256:" + sha(path)}}
    state.write_text(json.dumps(assets))
elif verb == ["release", "download"]:
    names = [argv[i + 1] for i, word in enumerate(argv) if word == "--asset"]
    target = pathlib.Path(argv[argv.index("--dir") + 1])
    for name in names:
        data = (store / name).read_bytes()
        (target / name).write_bytes(data + (b"served otherwise" if behaviour.get("serve_other") else b""))
    if behaviour.get("download_extra"):
        (target / "extra.bin").write_bytes(b"x")
    if behaviour.get("download_rc"):
        sys.exit(1)
else:
    print("verb the stand-in does not know: " + " ".join(argv), file=sys.stderr); sys.exit(2)
'''


def agh_stand_in(case) -> tuple[Path, Path, Path]:
    """The stand-in agh, as `case`'s --agh: its release's assets in state.json, what it
    serves in store/, every call in log, and what a test makes it do in behaviour.json."""
    base = case.parent / "agh"
    base.mkdir()
    state, behaviour = base / "state.json", base / "behaviour.json"
    case.plan.args.agh = put(base / "agh", AGH.format(python=sys.executable, state=str(state), store=str(base / "store"),
                                                      log=str(base / "log"), behaviour=str(behaviour)), 0o755)
    return state, behaviour, base / "log"


class PublishCase(CommitCase):
    def stand_in(self) -> tuple[Path, Path, Path]:
        return agh_stand_in(self)

    def exit_test(self, **changes) -> Path:
        """What a passed `verify --rebuild` leaves in its --work for the branch tip commit
        recorded (RebuildRuleTests hand publish the real one)."""
        made = self.kept("commit.json")
        tip = made["commits"][-1]
        stage0 = blob(Path(made["repo"]), tip, "src/stage0")
        work = self.parent / "exit-test-work"
        work.mkdir(exist_ok=True)
        driver.write_json(work / "exit-test.json", {
            "schema": driver.EXIT_TEST_SCHEMA, "commit": SOURCE.commit, "host": HOST, "head": tip,
            "receipt_sha256": made["receipt_sha256"], "stage0_sha256": hashlib.sha256(stage0).hexdigest(),
            "archives": {Path(key).name: value for key, value in driver.pinned_rows(
                driver.text_rows(stage0.decode(), "pins")).items()}, **changes})
        self.plan.args.exit_test = work
        return work

    def calls(self) -> list[list[str]]:
        log = self.parent / "agh" / "log"
        return [json.loads(line) for line in log.read_text().splitlines()] if log.is_file() else []

    def pins(self) -> dict[str, str]:
        made = self.kept("commit.json")
        pins = driver.text_rows(git(Path(made["repo"]), "show", f"{made['commits'][1]}:src/stage0") + "\n", "pins")
        return {Path(key).name: value for key, value in driver.ledger().host_payloads(pins, HOST).items()
                if "/trust-src-" not in key}

    def publish(self) -> int:
        return self.quiet(driver.publish_step, self.plan)


class PublishTests(PublishCase):
    def test_publish_uploads_the_missing_archives_reads_them_back_and_never_clobbers(self):
        self.refused(r"setup of .* is not done", self.publish)
        self.through_record()
        state, behaviour, _log = self.stand_in()
        self.refused(r"commit is not done .*Nothing was uploaded", self.publish)
        self.assertEqual(self.commit(), 0, self.said)
        # Only archives an exit test passed with: none given, none there, or one of another tip.
        self.refused(r"publish needs the exit test \(design step 16\) passed on this branch: no --exit-test was "
                     r"given\. Nothing was uploaded", self.publish)
        self.plan.args.exit_test = self.parent / "no-such-work"
        self.refused(r"no-such-work/exit-test.json is not there\. Nothing was uploaded", self.publish)
        for changes, moved in (({"head": "f" * 40}, "head"), ({"receipt_sha256": "0" * 64}, "receipt_sha256"),
                               ({"stage0_sha256": "0" * 64}, "stage0_sha256"), ({"schema": "x"}, "schema"),
                               ({"archives": {}}, "archives"), ({"commit": "f" * 40}, "commit"),
                               ({"host": "x86_64-unknown-linux-gnu"}, "host")):
            with self.subTest(moved):
                self.exit_test(**changes)
                self.refused(rf"exit-test.json is an exit test of another {moved} than the branch tip .*Nothing was "
                             "uploaded", self.publish)
        self.assertEqual(self.calls(), [])
        self.exit_test()
        eight = self.pins()
        self.assertEqual(len(eight), 8)
        dated = self.plan.output_root() / "dist" / SEED_DATE
        # Three already there with their pinned bytes (an earlier run stopped): only five go up.
        first = sorted(eight)[:3]
        (self.parent / "agh" / "store").mkdir()
        for name in first:
            shutil.copyfile(dated / name, self.parent / "agh" / "store" / name)
        state.write_text(json.dumps({name: {"digest": "sha256:" + eight[name]} for name in first}))
        # The read-back serves other bytes: nothing is said to land.
        behaviour.write_text(json.dumps({"serve_other": True}))
        self.refused(r"the read-back in .*download is .* and \['.*'\] is not its pin: what the release serves is not "
                     "what the branch pins. Do not land", self.publish)
        self.assertFalse((self.plan.kept / "publish.json").exists())
        self.assertFalse(any("next (design step 18)" in line for line in self.said))
        uploads = [call for call in self.calls() if call[:2] == ["release", "upload"]]
        self.assertEqual(len(uploads), 1)
        self.assertEqual(sorted(Path(path).name for path in uploads[0][4:]), sorted(set(eight) - set(first)))
        self.assertEqual(uploads[0][2:4], ["fixture/trust", self.trust.tag])
        behaviour.unlink()
        self.said.clear()
        self.assertEqual(self.publish(), 0, self.said)
        record = self.kept("publish.json")
        self.assertEqual((record["repo"], record["tag"], record["assets"], record["uploaded"]),
                         ("fixture/trust", self.trust.tag, eight, []))
        download = Path(record["download"])
        self.assertEqual(download, self.root / "publish" / "download-2")
        self.assertEqual({path.name: sha(path) for path in download.iterdir()}, eight)
        self.assertTrue(self.said[-1].startswith("fixed-point-linux-seed: next (design step 18): in a main checkout, "
                                                 f"git fetch {self.branch_repo()} refs/heads/{BRANCH}"))
        # Never --clobber, never a delete; the verbs were list, upload, list, download only.
        calls = self.calls()
        self.assertFalse([call for call in calls if "--clobber" in call])
        self.assertEqual({tuple(call[:2]) for call in calls},
                         {("release", "assets"), ("release", "upload"), ("release", "download")})
        # Done once: the release is listed again, and nothing else is done.
        count = len(calls)
        self.said.clear()
        self.assertEqual(self.publish(), 0)
        self.assertRegex(self.said[0], r"publish: already done .*still reported with the pinned digests; not repeated")
        self.assertEqual(self.calls()[count:], [["release", "assets", "fixture/trust", self.trust.tag, "--format", "json"]])
        self.assertIn(f"  publish      done: {self.trust.tag}, read back", driver.status_lines(self.plan))
        # E6: an asset replaced since (another uploader's --clobber) is not reported done.
        name = sorted(eight)[0]
        state.write_text(json.dumps({**json.loads(state.read_text()), name: {"digest": "sha256:" + "1" * 64}}))
        self.said.clear()
        self.refused(rf"publish is done .*no longer reports \['{re.escape(name)}'\] with the pinned digests .*Do not "
                     r"land\. Nothing was uploaded or deleted", self.publish)
        self.assertFalse(any("next (design step 18)" in line for line in self.said))
        self.assertEqual([call[:2] for call in self.calls()[count + 1:]], [["release", "assets"]])

    def test_an_asset_of_the_same_name_with_other_bytes_is_refused_and_nothing_is_uploaded(self):
        self.through_record()
        state, behaviour, _log = self.stand_in()
        self.assertEqual(self.commit(), 0, self.said)
        self.exit_test()
        eight = self.pins()
        name = sorted(eight)[0]
        state.write_text(json.dumps({name: {"digest": "sha256:" + "0" * 64}}))
        self.refused(rf"T13: fixture/trust {self.trust.tag} already has {re.escape(name)} with digest 'sha256:0+' .*"
                     r"never replaced \(--clobber\) or deleted here\. Nothing was uploaded", self.publish)
        self.assertEqual([call[:2] for call in self.calls()], [["release", "assets"]])
        # A digest the release cannot say (null) is not the pinned bytes either.
        state.write_text(json.dumps({name: {"digest": None}}))
        self.refused(r"T13: .* with digest None", self.publish)
        # An upload that fails is a refusal; the next run uploads what is missing.
        state.write_text("{}")
        behaviour.write_text(json.dumps({"upload_fails": True}))
        self.refused(r"`.*agh release upload fixture/trust .*` exited 1\. Whatever reached the release", self.publish)
        behaviour.unlink()
        self.assertEqual(self.publish(), 0, self.said)
        self.assertFalse([call for call in self.calls() if "--clobber" in call])
        # The archives in prepared/ are held to the branch's pins before anything is listed.
        (self.plan.kept / "publish.json").unlink()
        archive = self.plan.output_root() / "dist" / SEED_DATE / name
        archive.write_bytes(archive.read_bytes() + b"\0")
        count = len(self.calls())
        self.refused(r"does not hold this host's eight archives with the branch's pins", self.publish)
        self.assertEqual(len(self.calls()), count)


class PublishRuleTests(PublishCase):
    """Each rule of `publish`, refused by its own words; nothing is recorded as published."""

    def test_the_branch_tip_the_tag_and_an_earlier_record(self):
        self.through_record()
        self.stand_in()
        self.assertEqual(self.commit(), 0, self.said)
        self.exit_test()
        made_path = driver.commit_record(self.plan)
        made = json.loads(made_path.read_text())
        repo, (first, second) = self.branch_repo(), made["commits"]
        git(repo, "update-ref", f"refs/heads/{BRANCH}", first)
        self.refused(r"is not the tip .* commit recorded\. Nothing was uploaded", self.publish)
        git(repo, "update-ref", f"refs/heads/{BRANCH}", second)
        done = self.plan.kept / "publish.json"
        done.write_text(json.dumps({"tag": "another", "assets": {}}))
        self.refused(r"records another release or other archives\. Nothing was uploaded", self.publish)
        done.unlink()
        # A tip whose ledger names another release: nothing goes to either.
        ledger = git(repo, "show", f"{second}:{driver.LEDGER_FILE}") + "\n"
        tag = tomllib.loads(ledger)["release"]["tag"]
        blob_id = subprocess.run(["git", "-C", str(repo), "hash-object", "-w", "--stdin"], input=ledger.replace(
            f'tag = "{tag}"', 'tag = "trust-stage0-another"').encode(), capture_output=True, check=True,
            env=GIT_ENV).stdout.decode().strip()
        index = {**GIT_ENV, "GIT_INDEX_FILE": str(self.parent / "other.index")}
        subprocess.run(["git", "-C", str(repo), "read-tree", second], env=index, check=True)
        subprocess.run(["git", "-C", str(repo), "update-index", "--cacheinfo", f"100644,{blob_id},{driver.LEDGER_FILE}"],
                       env=index, check=True)
        tree = subprocess.run(["git", "-C", str(repo), "write-tree"], env=index, capture_output=True,
                              check=True).stdout.decode().strip()
        other = git(repo, "commit-tree", tree, "-p", second, "-m", "another tag")
        git(repo, "update-ref", f"refs/heads/{BRANCH}", other)
        made_path.write_text(json.dumps({**made, "commits": [first, other]}))
        self.exit_test()
        self.refused(r"the branch's ledger names the release .*'trust-stage0-another', not this pin's", self.publish)
        self.assertEqual(self.calls(), [])

    def test_what_agh_reports_is_held_to_the_pins(self):
        self.through_record()
        state, behaviour, _log = self.stand_in()
        self.assertEqual(self.commit(), 0, self.said)
        self.exit_test()
        eight = self.pins()
        name = sorted(eight)[0]
        cases = (
            ({name: {"digest": "sha256:" + eight[name]}}, {"state": "starter"}, r"T13: .* already has .* \(state 'starter'\)"),
            ({}, {"upload_noop": True}, r"after the upload, .* does not report"),
            ({}, {"download_rc": True}, r"the read-back `agh release download .*` exited 1"),
            ({}, {"download_extra": True}, r"the read-back in .* is \[.*'extra.bin'.*\]\.\.\., and \[\] is not its pin"),
            ({name: {"digest": "sha256:" + eight[name]}}, {"dupes": True}, r"lists an asset name twice"),
            ({}, {"assets_rc": True}, r"`.*agh release assets .*` exited 1"),
        )
        store = self.parent / "agh" / "store"
        for assets, how, pattern in cases:
            with self.subTest(pattern):
                shutil.rmtree(store, ignore_errors=True)
                store.mkdir()
                state.write_text(json.dumps(assets))
                behaviour.write_text(json.dumps(how))
                self.refused(pattern, self.publish)
                self.assertFalse((self.plan.kept / "publish.json").exists())
        shutil.rmtree(store)
        store.mkdir()
        state.write_text("{}")
        behaviour.unlink()
        self.assertEqual(self.publish(), 0, self.said)


class StatusTests(RootCase):
    def test_status_reads_files_and_says_what_is_next_at_every_stage(self):
        def status() -> list[str]:
            before = snapshot(Path(self.tmp.name))
            lines = driver.status_lines(self.plan)
            self.assertEqual(snapshot(Path(self.tmp.name)), before)
            return lines

        me = "python3 /opt/trust-driver/scripts/fixed_point_linux_seed.py"
        where = f"--root {self.root} --commit {SOURCE.commit}"
        self.assertEqual(status(), [f"root {self.root}: {SOURCE.commit[:10]} on {HOST}",
                                    "  setup        not started (the root does not exist)",
                                    f"next: {me} setup {where}"])
        self.assertEqual(self.setup_root(), 0)
        lines = status()
        self.assertRegex(lines[1], r"  setup        done: jobs 3, system linker, base config [0-9a-f]{16}")
        self.assertEqual(lines[2:], ["  producer     not started", "  dist         not started",
                                     "  prepare      not started",
                                     f"  seed         absent ({self.root}/seed); made by `prepare`",
                                     "  fixed-point  not started", "  cross-check  not started",
                                     "  control      not known yet (it depends on the fixed-point build)",
                                     "  record       not written", "  commit       not made",
                                     "  publish      not done",
                                     f"next: {me} build --role producer {where}"])
        self.assertEqual(self.build("producer"), 0)
        lines = status()
        self.assertIn("  producer     clean as p-build, 1 s", lines)
        self.assertEqual(lines[-1], f"next: {me} dist {where}")
        self.assertEqual(self.dist(), 0)
        lines = status()
        self.assertIn("  dist         done: 4 files, 199 bytes", lines)
        self.assertEqual(lines[-2:], [f"next: {me} prepare {where}", f"next: {me} build --role cross-check {where}"])
        self.install_seed()
        lines = status()
        self.assertEqual(lines[-2], f"next: {me} build --role fixed-point {where}")
        self.assertIn(f"  prepare      done: the parent's 9 rows kept, 8 added; 0 archive files are the producer's "
                      f"rows ({self.root}/kept/prepare.json)", lines)
        self.assertRegex("\n".join(lines), rf"  seed         there \({self.root}/seed, \d+ entries, the pinned archives "
                                           r"as installed\)")
        # With the default commit and root, the command is the bare one.
        default = FakePlan(arguments(driver.ROOT_PARENT / driver.COMMIT[:10], commit=driver.COMMIT))
        self.assertEqual(driver.command_line(default, "dist"), ["python3", me.split()[1], "dist"])
        (self.plan.ledger / "trap.log").write_text("a line\n")
        self.assertIn("  trap log     1 line(s): no build starts and no record can be written from this root",
                      status())


if __name__ == "__main__":
    unittest.main()
