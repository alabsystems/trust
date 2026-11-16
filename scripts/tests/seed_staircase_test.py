#!/usr/bin/env python3
"""Regressions for scripts/seed_staircase.py: stage0 admission by content.

The shapes these fixtures reproduce were all measured on m2 on 2026-09-29:

* the pinned 2026-07-13 seed's bin/cargo carries a load command for Homebrew's
  /opt/homebrew/opt/libgit2/lib/libgit2.1.9.dylib, so the designed seed path
  died in x.py with a raw dyld abort (docs/SEED_STAIRCASE.md, rung R0-repro);
* the genesis adapter that seeded every local seal was a `#!` script that
  exec'd rustup's stock stable rustc (audit TB-1/TB-4);
* a renamed copy of stock rustc passes any NAME check; only its commit-hash
  (88d9e12ae, not a trust commit) and its missing Trust switch give it away.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import importlib.util
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts" / "seed_staircase.py"
SPEC = importlib.util.spec_from_file_location("seed_staircase", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
staircase = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = staircase
SPEC.loader.exec_module(staircase)

STOCK_COMMIT = "88d9e12ae178fab0fb5cc050a94da85685d449ea"  # stock rustc 1.98.0
HEAD = subprocess.run(["git", "-C", str(REPO), "rev-parse", "HEAD"],
                      capture_output=True, text=True, check=True).stdout.strip()
PARENT = subprocess.run(["git", "-C", str(REPO), "rev-parse", "HEAD~1"],
                        capture_output=True, text=True, check=False).stdout.strip()
CC = shutil.which("cc") or shutil.which("clang")

# A native executable whose behaviour is a shell script beside it (<argv0>.sh):
# admission must see a real Mach-O/ELF, while each fixture scripts its answers.
TRAMPOLINE_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
int main(int argc, char **argv) {
    char script[4096];
    snprintf(script, sizeof script, "%s.sh", argv[0]);
    char **args = calloc((size_t)argc + 2, sizeof *args);
    args[0] = "/bin/sh"; args[1] = script;
    for (int i = 1; i < argc; i++) args[i + 1] = argv[i];
    execv("/bin/sh", args);
    return 127;
}
"""


def trustc_script(commit: str, sysroot: str, trust_switch: bool = True, binary: str = "trustc") -> str:
    zhelp = "    -Z  no-trust-verify=val -- disable Trust verification" if trust_switch else "    -Z  threads=val -- nothing Trust"
    return (
        "case \"$1\" in\n"
        f"  -vV) printf 'rustc 1.99.0-dev ({commit[:9]} 2026-09-29)\\nbinary: {binary}\\ncommit-hash: {commit}\\nhost: {staircase.host_triple()}\\nrelease: 1.99.0-dev\\n' ;;\n"
        f"  -Z) printf '%s\\n' '{zhelp}' ;;\n"
        f"  --print) printf '%s\\n' '{sysroot}' ;;\n"
        "  *) exit 2 ;;\n"
        "esac\n"
    )


LEAN_PIN = "leanprover/lean4:v9.9.9"
LEAN_DIRECTORY = "leanprover--lean4---v9.9.9"
# An olean header as mint_seed_support._lean_header_identity reads one: the magic,
# format version 1, and a 40-hex world key. No proof and no Lean library is
# claimed: the bytes only make two files the same declared world.
OLEAN = b"olean" + b"\x01" + b"a" * 40 + b"\0" * 16


def clean_lean_fixture(worktree: Path, root: Path) -> Path:
    """A worktree whose Clean pin names LEAN_PIN, and an installation of that name
    under `root`. Returns the `lib/lean` `run --clean-lean-lib` is given."""
    clean = worktree / "first-party" / "clean"
    (clean / "crates" / "clean-olean").mkdir(parents=True)
    (clean / "tests").mkdir()
    (clean / "lean-toolchain").write_text(LEAN_PIN + "\n")
    (clean / "crates" / "clean-olean" / "lean_worlds.tsv").write_text(
        f"v9.9.9\toracle\t{LEAN_PIN}\ttests/oracle.olean\n")
    (clean / "tests" / "oracle.olean").write_bytes(OLEAN)
    library = root / "lean" / LEAN_DIRECTORY / "lib" / "lean"
    (library / "Init").mkdir(parents=True)
    (library / "Init" / "Prelude.olean").write_bytes(OLEAN + b"prelude")
    return library


# The environment `run` hands x.py when it is given neither --offline nor
# --clean-lean-lib, key for key, as it was before those options existed
# (SSH_AUTH_SOCK only when the caller has one).
RUN_ENVIRONMENT_KEYS = {
    "HOME", "USER", "LOGNAME", "SHELL", "TERM", "LANG", "LC_ALL", "TMPDIR", "PATH", "CARGO_HOME",
    "RUSTUP_TOOLCHAIN", "RUSTUP_AUTO_INSTALL", "TRUST_STAIRCASE_RUNG", "SOURCE_DATE_EPOCH"}
RUN_OPTION_KEYS = {"CARGO_NET_OFFLINE", "CLEAN_OLEAN_PINNED_LEAN_LIB", "CLEAN_OLEAN_REQUIRE_PINNED_LEAN"}

# A stand-in x.py for `run --fifo-jobserver` (BOOTSTRAP-JOBSERVER-PROBE-1). It holds
# MAKEFLAGS to a FIFO of this process's owner, mode 0600, that it can reach only by
# its path and that holds N-1 tokens for -jN; then it starts what a build script's
# compiler probe is under Trust std, a grandchild with only fds 0-2 and MAKEFLAGS,
# which reopens the jobserver by its path and takes a token (and returns it, unless
# told to `leak` it). Without the run holding the FIFO open, the tokens this process
# reads and puts back would be discarded when it closes its descriptor, and the
# grandchild would find none. It writes what it saw to jobserver.json; a failed
# expectation is an exit 1 with the reason.
FIFO_XPY = r'''import json, os, re, stat, subprocess, sys
flags = os.environ["MAKEFLAGS"]
match = re.fullmatch(r"-j([0-9]+) --jobserver-auth=fifo:(\S+)", flags)
assert match, flags
jobs, path = int(match.group(1)), match.group(2)
held = os.stat(path)
assert stat.S_ISFIFO(held.st_mode), "not a FIFO"
assert stat.S_IMODE(held.st_mode) == 0o600 and held.st_uid == os.getuid(), (oct(held.st_mode), held.st_uid)
inherited = []
for number in range(3, 256):
    try:
        mine = os.fstat(number)
    except OSError:
        continue
    if (mine.st_dev, mine.st_ino) == (held.st_dev, held.st_ino):
        inherited.append(number)
assert not inherited, f"x.py inherited the jobserver as descriptor(s) {inherited}"
def drain(fd):
    taken = b""
    while True:
        try:
            chunk = os.read(fd, 4096)
        except BlockingIOError:
            return taken
        if not chunk:
            return taken
        taken += chunk
fd = os.open(path, os.O_RDWR | os.O_NONBLOCK)
tokens = drain(fd)
os.write(fd, tokens)
os.close(fd)
assert len(tokens) == jobs - 1, f"the FIFO held {len(tokens)} tokens for -j{jobs}"
PROBE = """import json, os, re, sys
open_fds = []
for number in range(256):
    try:
        os.fstat(number)
    except OSError:
        continue
    open_fds.append(number)
jobs, path = re.fullmatch(r"-j([0-9]+) --jobserver-auth=fifo:(\\S+)", os.environ["MAKEFLAGS"]).groups()
fd = os.open(path, os.O_RDWR | os.O_NONBLOCK)
# -j1 holds no token: a client runs on the one it was started with.
token = os.read(fd, 1) if int(jobs) > 1 else b""
if "leak" not in sys.argv:
    os.write(fd, token)
os.close(fd)
print(json.dumps({"fds": open_fds, "token": token.decode()}))
"""
probe = subprocess.run([sys.executable, "-c", PROBE, *sys.argv[1:]], capture_output=True, text=True,
                       close_fds=True)
assert probe.returncode == 0, probe.stderr
if "extra" in sys.argv:
    fd = os.open(path, os.O_WRONLY | os.O_NONBLOCK)
    os.write(fd, b"+")
    os.close(fd)
if "replace" in sys.argv:
    os.unlink(path)
    with open(path, "w") as stand_in:
        stand_in.write("not a FIFO\n")
made = None
if "make" in sys.argv:
    # What 82bb867edd's openssl-sys build script does under Trust std, with only fds
    # 0-2: it imports the jobserver and runs `make` from PATH through jobserver_utils'
    # configure_make, which hands make the FIFO as fifo:PATH in MAKEFLAGS and MFLAGS.
    # The recipe marked + (a recursive make keeps the jobserver) says which descriptors
    # make was given and whether they are the FIFO.
    with open("jobserver.mk", "w") as out:
        out.write("all: one two three\none:\n\t+@python3 check.py $(FIFO)\ntwo three:\n\t@true\n")
    with open("check.py", "w") as out:
        out.write("""import json, os, re, sys
flags = os.environ.get("MAKEFLAGS", "")
found = re.search(r"--jobserver-(?:auth|fds)=([0-9]+),([0-9]+)", flags)
fifo = os.stat(sys.argv[1])
same = [(os.fstat(int(fd)).st_dev, os.fstat(int(fd)).st_ino) == (fifo.st_dev, fifo.st_ino)
        for fd in found.groups()] if found else []
with open("make-check.json", "w") as out:
    json.dump({"makeflags": flags, "descriptors_are_the_fifo": same}, out)
""")
    BUILD_SCRIPT = """import json, os, subprocess, sys
path = sys.argv[1]
flags = f"-j --jobserver-fds=fifo:{path} --jobserver-auth=fifo:{path}"
env = {**os.environ, "CARGO_MAKEFLAGS": flags, "MAKEFLAGS": flags, "MFLAGS": flags}
done = subprocess.run(["make", "-f", "jobserver.mk", "FIFO=" + path], env=env, capture_output=True, text=True)
print(json.dumps({"rc": done.returncode, "stderr": done.stderr}))
"""
    ran = subprocess.run([sys.executable, "-c", BUILD_SCRIPT, path], capture_output=True, text=True,
                         close_fds=True)
    assert ran.returncode == 0, ran.stderr
    made = json.loads(ran.stdout)
    assert made["rc"] == 0, made["stderr"]
    with open("make-check.json") as checked:
        made["check"] = json.load(checked)
with open("jobserver.json", "w") as out:
    json.dump({"jobs": jobs, "path": path, "tokens": len(tokens), "probe": json.loads(probe.stdout),
               "env": dict(os.environ), "make": made}, out)
'''

# A stand-in make for the adapter (seed_staircase.MAKE_ADAPTER_BODY): it prints its
# arguments, the three make variables, and the device and inode of every descriptor
# MAKEFLAGS or MFLAGS name by number (None for one that is not open).
STAND_IN_MAKE = '''import json, os, re, sys
fds = {}
for key in ("MAKEFLAGS", "MFLAGS"):
    for found in re.finditer(r"=([0-9]+),([0-9]+)", os.environ.get(key, "")):
        for fd in found.groups():
            try:
                held = os.fstat(int(fd))
                fds[fd] = [held.st_dev, held.st_ino]
            except OSError:
                fds[fd] = None
print(json.dumps({"argv": sys.argv[1:], "fds": fds,
                  **{key: os.environ.get(key) for key in ("MAKEFLAGS", "MFLAGS", "CARGO_MAKEFLAGS")}}))
'''


@unittest.skipUnless(os.name == "posix" and CC, "native fixtures need a POSIX C compiler")
class Stage0AdmissionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.tmp = Path(tempfile.mkdtemp(prefix="seed-staircase-test-"))
        source = cls.tmp / "trampoline.c"
        source.write_text(TRAMPOLINE_C)
        cls.trampoline = cls.tmp / "trampoline"
        subprocess.run([CC, "-o", str(cls.trampoline), str(source)], check=True)

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def stage0(self, name: str, commit: str = HEAD, trust_switch: bool = True, binary: str = "trustc") -> Path:
        root = Path(tempfile.mkdtemp(prefix=f"{name}-", dir=self.tmp)).resolve()
        (root / "bin").mkdir()
        for tool in ("trustc", "cargo"):
            shutil.copy2(self.trampoline, root / "bin" / tool)
        (root / "bin" / "trustc.sh").write_text(trustc_script(commit, str(root), trust_switch, binary))
        (root / "bin" / "cargo.sh").write_text("printf 'cargo 1.99.0-dev\\n'\n")
        (root / "lib").mkdir()
        (root / "lib" / "librustc_driver-fixture.dylib").write_bytes(f"driver {name}".encode())
        return root

    def admit(self, root: Path, target: str | None = HEAD, compat: list[Path] | None = None) -> dict:
        return staircase.admit(root, REPO, target, compat or [])

    def test_trust_stage0_is_admitted_with_its_identity(self) -> None:
        identity = self.admit(self.stage0("trust"))
        self.assertNotIn("refusals", identity, identity.get("refusals"))
        self.assertEqual(identity["commit"], HEAD)
        self.assertEqual(set(identity["sha256"]), {"bin/trustc", "bin/cargo", "lib/librustc_driver-fixture.dylib"})

    def test_stage0_without_exactly_one_driver_is_refused(self) -> None:
        root = self.stage0("two-drivers")
        (root / "lib" / "librustc_driver-second.dylib").write_bytes(b"another build")
        refusals = self.admit(root).get("refusals", [])
        self.assertTrue(any("exactly one lib/librustc_driver" in r for r in refusals), refusals)

    def test_genesis_shaped_script_stage0_is_refused(self) -> None:
        root = self.stage0("genesis")
        (root / "bin" / "trustc").write_text('#!/bin/sh\nexec "$HOME/.cargo/bin/rustc" "$@"\n')
        refusals = self.admit(root).get("refusals", [])
        self.assertTrue(any("`#!` script" in r for r in refusals), refusals)

    def test_renamed_stock_compiler_is_refused_by_its_commit(self) -> None:
        refusals = self.admit(self.stage0("stock", commit=STOCK_COMMIT)).get("refusals", [])
        self.assertTrue(any(STOCK_COMMIT in r and "not a commit" in r for r in refusals), refusals)

    def test_an_upstream_compiler_whose_commit_trust_merged_is_refused(self) -> None:
        # Trust merges upstream: a stock nightly's commit can be in this history.
        refusals = self.admit(self.stage0("upstream-nightly", binary="rustc")).get("refusals", [])
        self.assertTrue(any("`binary: rustc`, not trustc" in r for r in refusals), refusals)

    def test_stage0_without_the_trust_switch_is_refused(self) -> None:
        refusals = self.admit(self.stage0("noswitch", trust_switch=False)).get("refusals", [])
        self.assertTrue(any("Trust verification switch" in r for r in refusals), refusals)

    @unittest.skipUnless(platform.system() == "Linux", "native Linux host identity")
    def test_native_elf_cannot_report_another_host(self) -> None:
        root = self.stage0("foreign-host")
        script = root / "bin/trustc.sh"
        script.write_text(script.read_text().replace(staircase.host_triple(), "aarch64-apple-darwin"))
        refusals = self.admit(root).get("refusals", [])
        self.assertTrue(any("not native" in r for r in refusals), refusals)

    @unittest.skipUnless(PARENT, "needs a parent commit")
    def test_a_staircase_only_goes_forward(self) -> None:
        refusals = self.admit(self.stage0("backward"), target=PARENT).get("refusals", [])
        self.assertTrue(any("not an ancestor" in r for r in refusals), refusals)

    def test_stage0_in_a_stock_root_is_refused(self) -> None:
        root = self.tmp / "home" / ".rustup" / "toolchains" / "stable" / "x"
        shutil.copytree(self.stage0("rustup-root"), root)
        refusals = self.admit(root).get("refusals", [])
        self.assertTrue(any("stock root (/.rustup/)" in r for r in refusals), refusals)

    @unittest.skipUnless(platform.system() == "Darwin", "Mach-O load commands")
    def test_seed_shaped_foreign_dylib_needs_a_declared_compat_library(self) -> None:
        # The 2026-07-13 seed's shape: bin/cargo loads an absolute, package-manager
        # path. Admission must name it (x.py only ever showed a dyld abort), and
        # accept it only through a declared compat library.
        root = self.stage0("foreign-dylib")
        libdir = self.tmp / "compat"
        libdir.mkdir(exist_ok=True)
        (self.tmp / "foo.c").write_text("int foo(void) { return 7; }\n")
        (self.tmp / "main.c").write_text("int foo(void);\nint main(void) { return foo() == 7 ? 0 : 1; }\n")
        foreign = "/nonexistent-seed-staircase-test/opt/libfoo/lib/libfoo.1.dylib"
        subprocess.run([CC, "-dynamiclib", "-o", str(libdir / "libfoo.1.dylib"), str(self.tmp / "foo.c"),
                        "-install_name", foreign], check=True)
        subprocess.run([CC, "-o", str(root / "bin" / "linked-tool"), str(self.tmp / "main.c"),
                        str(libdir / "libfoo.1.dylib")], check=True)
        closure = staircase.dylib_closure(root, [])
        self.assertEqual([r["load"] for r in closure["unresolved"]], [foreign])
        refusals = self.admit(root).get("refusals", [])
        self.assertTrue(any(foreign in r and "compat library" in r for r in refusals), refusals)
        identity = self.admit(root, compat=[libdir])
        self.assertNotIn("refusals", identity, identity.get("refusals"))
        [row] = identity["dylib_closure"]["compat"]
        self.assertEqual(row["provider"], str(libdir / "libfoo.1.dylib"))
        self.assertEqual(len(row["provider_sha256"]), 64)


    @unittest.skipUnless(PARENT, "needs a parent commit")
    def test_the_configuration_must_hand_x_py_the_admitted_stage0(self) -> None:
        stage0 = self.stage0("cfg")
        admission = self.admit(stage0)
        self.assertNotIn("refusals", admission)
        tree = Path(tempfile.mkdtemp(prefix="tree-", dir=self.tmp)).resolve()
        base = tree / "base.toml"
        base.write_text('profile = "compiler"\n[build]\nsubmodules = false\n')

        def record(text: str, *xpy: str, seed_mode: bool = False, name: str = "rung.toml") -> dict:
            (tree / name).write_text(text)
            return staircase.config_tools_record(tree, ["--config", name, *xpy, "build"], admission, seed_mode)

        rung = (f'include = ["base.toml"]\n[build]\nrustc = "{stage0}/bin/trustc"\n'
                f'cargo = "{stage0}/bin/cargo"\n')
        good = record(rung)
        self.assertTrue(good["matches_admission"], good["problems"])
        self.assertEqual(good["tools"]["rustc"]["kind"], staircase.native_kind(self.trampoline))
        self.assertEqual(good["tools"]["cargo"]["sha256"], staircase.sha256_file(stage0 / "bin" / "cargo"))

        # The right bytes at another path, and a compiler that is not the admitted one.
        other = self.stage0("other")
        self.assertRegex(" ".join(record(rung.replace(str(stage0), str(other)))["problems"]), "outside the admitted stage0")
        with open(other / "bin" / "trustc", "ab") as handle:
            handle.write(b"\0another build")
        self.assertRegex(" ".join(record(rung.replace(str(stage0), str(other)))["problems"]), "bytes differ")

        # The genesis adapter's shape: a `#!` script named as the compiler.
        script = tree / "genesis" / "rustc"
        script.parent.mkdir()
        script.write_text("#!/bin/sh\nexec \"$HOME/.cargo/bin/rustc\" \"$@\"\n")
        problems = " ".join(record(f'[build]\nrustc = "{script}"\n')["problems"])
        self.assertIn("not a native executable (script)", problems)

        # Under a stock root, by real path.
        stock = tree / ".rustup" / "toolchains" / "stable" / "bin" / "rustc"
        stock.parent.mkdir(parents=True)
        shutil.copy2(stage0 / "bin" / "trustc", stock)
        self.assertRegex(" ".join(record(f'[build]\nrustc = "{stock}"\n')["problems"]), r"stock root \(/\.rustup/\)")

        # Seed mode: the configuration names no compiler, or the in-tree seed is not what ran.
        self.assertTrue(record('include = ["base.toml"]\n', seed_mode=True)["matches_admission"])
        named = record(rung, seed_mode=True)
        self.assertRegex(" ".join(named["problems"]), r"--seed-mode, but the configuration sets \[build\] rustc")
        # ... including through an include, and through --set.
        record(rung, name="inc.toml")
        self.assertFalse(record('include = ["inc.toml"]\n', seed_mode=True)["matches_admission"])
        self.assertFalse(record('include = ["base.toml"]\n', "--set", f"build.rustc={stage0}/bin/trustc",
                                seed_mode=True)["matches_admission"])

        # Bootstrap's merge order: the including file over its includes, --set over both.
        (tree / "a.toml").write_text('[build]\nrustc = "/a/trustc"\ncargo = "/a/cargo"\n')
        (tree / "b.toml").write_text('[build]\nrustc = "/b/trustc"\n')
        merged = staircase.config_build_tools(tree / "a.toml", [])
        self.assertEqual(merged, {"rustc": "/a/trustc", "cargo": "/a/cargo"})
        (tree / "top.toml").write_text('include = ["a.toml", "b.toml"]\n[build]\ncargo = "/top/cargo"\n')
        self.assertEqual(staircase.config_build_tools(tree / "top.toml", []),
                         {"rustc": "/b/trustc", "cargo": "/top/cargo"})
        self.assertEqual(staircase.config_build_tools(tree / "top.toml", ["--set", "build.cargo=/set/cargo"])["cargo"],
                         "/set/cargo")
        (tree / "loop.toml").write_text('include = ["loop.toml"]\n')
        with self.assertRaisesRegex(staircase.Refusal, "includes itself"):
            staircase.config_build_tools(tree / "loop.toml", [])

    @mock.patch.object(staircase, "require_pinned_root")
    def test_lineage_chains_rungs_by_commit_and_by_bytes(self, _root_gate) -> None:
        final = self.stage0("final")
        seed_bytes = {"bin/trustc": "1" * 64, "bin/cargo": "2" * 64, "lib/librustc_driver-s.dylib": "3" * 64}
        produced = staircase.sysroot_files(final)
        root = {"kind": "stage0-admission", "commit": PARENT, "sha256": seed_bytes}
        rung = {"label": "r0", "worktree": "/w", "commit": HEAD, "stage0_commit": PARENT, "rc": 0,
                "stage0_sha256": seed_bytes, "stage0_matches_admission": True, "no_stock_evidence": True,
                "build_census": {"rustc_info_files": 7}, "produced": {"sha256": produced}}
        record = staircase.build_lineage(root, [rung], final, REPO, None)
        self.assertEqual(record["final"]["commit"], HEAD)
        self.assertEqual(record["final"]["trustc_sha256"], staircase.sha256_file(final / "bin" / "trustc"))
        [only] = record["rungs"]
        self.assertEqual([i["label"] for i in only["invocations"]], ["r0"])
        self.assertIn("not recorded by invocation(s) r0", only["configuration_evidence"])
        configured = {**rung, "config_tools": {"matches_admission": True, "problems": []}}
        self.assertEqual(staircase.build_lineage(root, [configured], final, REPO, None)["rungs"][0]
                         ["configuration_evidence"], "recorded for every invocation")
        with self.assertRaisesRegex(staircase.Refusal, "does not hand x.py its admitted stage0: seed-mode"):
            staircase.build_lineage(root, [{**rung, "config_tools": {"matches_admission": False,
                                                                     "problems": ["seed-mode"]}}],
                                    final, REPO, None)

        # An interrupted invocation resumed in place is one rung; only the last must succeed.
        killed = {**rung, "label": "r0-killed", "rc": None, "produced": None}
        record = staircase.build_lineage(root, [killed, rung], final, REPO, None)
        self.assertEqual([i["label"] for i in record["rungs"][0]["invocations"]], ["r0-killed", "r0"])

        other_bytes = {**seed_bytes, "bin/trustc": "9" * 64}
        for broken, reason in (
            ({**rung, "stage0_commit": HEAD}, "not by the previous rung"),
            ({**rung, "rc": 1}, "did not succeed"),
            # the right COMMIT built by another compiler (say, a genesis-seeded seal)
            ({**rung, "stage0_sha256": other_bytes}, "not the compiler the previous rung produced"),
            ({**rung, "stage0_matches_admission": False}, "did not run its admitted stage0"),
            ({**rung, "no_stock_evidence": False}, "no clean no-stock evidence"),
            # a record from before the build census required a compiler record (R0's shape)
            ({**rung, "build_census": {"rustc_info_files": 0}}, "read no .rustc_info.json"),
            ({**rung, "build_census": None}, "read no .rustc_info.json"),
            ({**rung, "produced": {"sha256": {**produced, "bin/trustc": "0" * 64}}}, "not the stage2 the last rung produced"),
        ):
            with self.assertRaisesRegex(staircase.Refusal, reason):
                staircase.build_lineage(root, [broken], final, REPO, None)
        with self.assertRaisesRegex(staircase.Refusal, "no clean no-stock evidence"):
            staircase.build_lineage(root, [{**killed, "no_stock_evidence": False}, rung], final, REPO, None)
        with self.assertRaisesRegex(staircase.Refusal, "carries refusals"):
            staircase.build_lineage({**root, "refusals": ["x"]}, [rung], final, REPO, None)
        # The double compile is part of the record only when its staircase tree IS
        # the stage2 being sealed, and its other tree is what the independent
        # compiler built (see test_a_double_compile_is_bound_to_its_own_build).
        independent = {"bin/trustc": "4" * 64, "bin/cargo": "5" * 64, "lib/librustc_driver-i.dylib": "6" * 64}
        ddc_tree = {**produced, "bin/ay": "7" * 64}
        ddc = {"verdict": "compiler-and-std-identical", "staircase_identity": produced, "ddc_identity": ddc_tree,
               "ddc_seed": {"commit": PARENT, "sha256": independent},
               "run": {"label": "ddc", "rc": 0, "commit": HEAD, "worktree": "/w", "stage0_commit": PARENT,
                       "stage0_sha256": independent, "stage0_matches_admission": True,
                       "no_stock_evidence": True, "build_census": {"rustc_info_files": 5},
                       "produced": {"sha256": ddc_tree}}}
        self.assertEqual(staircase.build_lineage(root, [rung], final, REPO, ddc)["ddc"]["run"]["label"], "ddc")
        # A double compile of some other tree says nothing about this one.
        for identity in ({**produced, "bin/trustc": "0" * 64}, {}, None):
            with self.assertRaisesRegex(staircase.Refusal, "double compile's staircase tree is not"):
                staircase.build_lineage(root, [rung], final, REPO, {**ddc, "staircase_identity": identity})
        self.ddc_fixture = (root, rung, final, ddc)

    @mock.patch.object(staircase, "require_pinned_root")
    def test_a_pinned_root_carries_the_host_record_that_admitted_it(self, _root_gate) -> None:
        """docs/PLAN.md PKG-S6: a pinned root (root.admission.pinned_seed, set on
        Linux) is admitted by its host record in the seed ledger. The lineage reads
        that record through select_host_record and capture_host_record and says
        which kind it is and what it discloses; a root without pinned_seed (Darwin)
        gets no new key."""
        final = self.stage0("final")
        seed_bytes = {"bin/trustc": "1" * 64, "bin/cargo": "2" * 64, "lib/librustc_driver-s.dylib": "3" * 64}
        rung = {"label": "r0", "worktree": "/w", "commit": HEAD, "stage0_commit": PARENT, "rc": 0,
                "stage0_sha256": seed_bytes, "stage0_matches_admission": True, "no_stock_evidence": True,
                "build_census": {"rustc_info_files": 7}, "produced": {"sha256": staircase.sysroot_files(final)}}
        plain = {"kind": "stage0-admission", "commit": PARENT, "sha256": seed_bytes}
        pinned = {**plain, "pinned_seed": {"kind": "seed-sysroot", "compiler_commit": PARENT}}
        self.assertNotIn("pin_admission", staircase.build_lineage(plain, [rung], final, REPO, None)["root"])
        # This checkout's own ledger records the Darwin mint: admitted, kind `mint`, nothing disclosed.
        with mock.patch.object(staircase, "host_triple", return_value="aarch64-apple-darwin"):
            record = staircase.build_lineage(pinned, [rung], final, REPO, None)
        self.assertEqual(record["root"]["pin_admission"], {"kind": "mint", "root_disclosure": None})
        # A ledger with no table for the build host: refused, whatever the rungs say.
        # Read from a copy of this checkout's ledger without any Linux table, so the
        # case holds once a Linux host is recorded too (docs/PLAN.md PKG-S6).
        linux = "aarch64-unknown-linux-gnu"
        admitted = staircase.pinned_root_admission
        with tempfile.TemporaryDirectory() as directory:
            repo = self.copied_seed(Path(directory).resolve(), "aarch64-apple-darwin", without=linux)
            with mock.patch.object(staircase, "host_triple", return_value=linux), \
                    mock.patch.object(staircase, "pinned_root_admission",
                                      side_effect=lambda _repo, host: admitted(repo, host)), \
                    self.assertRaisesRegex(staircase.Refusal, f"{linux} seed host record is not "
                                           "admitted: seed admission has no exact build-host mint record"):
                staircase.build_lineage(pinned, [rung], final, REPO, None)

    @staticmethod
    def copied_seed(repo: Path, host: str, *, without: str | None = None) -> Path:
        """`repo` laid out with this checkout's src/stage0, its seed ledger (without
        `without`'s host tables) and `host`'s proofs."""
        seed = REPO / "bootstrap" / "trust-stage0"
        (repo / "src").mkdir()
        shutil.copyfile(REPO / "src" / "stage0", repo / "src" / "stage0")
        copied = repo / "bootstrap" / "trust-stage0"
        shutil.copytree(seed / "host-proofs" / host, copied / "host-proofs" / host)
        kept, skipping = [], False
        for line in (seed / "seed-ledger.toml").read_text().splitlines(keepends=True):
            if line.startswith("["):
                skipping = without is not None and line.startswith(f'[release.hosts."{without}"')
            if not skipping:
                kept.append(line)
        (copied / "seed-ledger.toml").write_text("".join(kept))
        return repo

    def test_a_pinned_roots_host_record_must_name_its_kind(self) -> None:
        # What capture_host_record returns names its kind in one word, and its
        # root_disclosure is a table; a ledger with no [release] admits nothing.
        host = "aarch64-apple-darwin"
        load = staircase.seed_host_ledger_module

        def capturing(record):
            def loaded():
                module = load()
                module.capture_host_record = lambda *_args: (record, "0" * 64)
                return module
            return loaded

        with tempfile.TemporaryDirectory() as directory:
            repo = self.copied_seed(Path(directory).resolve(), host)
            helper = load()
            for record, message in (
                ({"schema": helper.GENESIS_SCHEMA, "host": host}, "seed host record names no admission kind"),
                ({"schema": helper.GENESIS_SCHEMA, "host": host, "admission_kind": "Bad Kind"},
                 "seed host record names no admission kind"),
                ({"schema": helper.SCHEMA, "host": host, "root_disclosure": "x"},
                 "seed host record's root_disclosure is not a table"),
            ):
                with self.subTest(record=record), \
                        mock.patch.object(staircase, "seed_host_ledger_module", side_effect=capturing(record)), \
                        self.assertRaisesRegex(staircase.Refusal, f"the pinned root's {host} {message}"):
                    staircase.pinned_root_admission(repo, host)
            # Not vacuous: the same stand-in with a word and a table is admitted as it says.
            with mock.patch.object(staircase, "seed_host_ledger_module", side_effect=capturing(
                    {"schema": helper.GENESIS_SCHEMA, "admission_kind": "genesis-root", "root_disclosure": {}})):
                self.assertEqual(staircase.pinned_root_admission(repo, host),
                                 {"kind": "genesis-root", "root_disclosure": {}})
            ledger = repo / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
            for text in ('scope = "internal"\n', 'release = "x"\n'):
                with self.subTest(text=text):
                    ledger.write_text(text)
                    with self.assertRaisesRegex(staircase.Refusal, "has no \\[release\\] table"):
                        staircase.pinned_root_admission(repo, host)

    def test_a_pinned_roots_host_record_must_be_the_one_its_proofs_derive(self) -> None:
        host = "aarch64-apple-darwin"
        seed = REPO / "bootstrap" / "trust-stage0"
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory).resolve()
            (repo / "src").mkdir()
            shutil.copyfile(REPO / "src" / "stage0", repo / "src" / "stage0")
            copied = repo / "bootstrap" / "trust-stage0"
            shutil.copytree(seed / "host-proofs" / host, copied / "host-proofs" / host)
            ledger = (seed / "seed-ledger.toml").read_text()
            (copied / "seed-ledger.toml").write_text(ledger)
            self.assertEqual(staircase.pinned_root_admission(repo, host), {"kind": "mint", "root_disclosure": None})
            receipt = copied / "host-proofs" / host / "SEED-MINT"
            original = receipt.read_bytes()
            receipt.write_bytes(original + b"# one more line\n")
            with self.assertRaisesRegex(staircase.Refusal, f"the pinned root's {host} seed host record is not "
                                        "admitted: seed admission host record differs"):
                staircase.pinned_root_admission(repo, host)
            receipt.write_bytes(original)
            (copied / "seed-ledger.toml").write_text(ledger.replace("surface_sha256 = \"", "surface_sha256 = \"0", 1))
            with self.assertRaisesRegex(staircase.Refusal, "seed host record is not admitted"):
                staircase.pinned_root_admission(repo, host)
            # The single-host format names no host record: a pinned root is not admitted through it.
            legacy = ledger[:ledger.index("[release.hosts.")]
            (copied / "seed-ledger.toml").write_text(legacy)
            with self.assertRaisesRegex(staircase.Refusal, "single-host format"):
                staircase.pinned_root_admission(repo, host)
            (copied / "seed-ledger.toml").unlink()
            with self.assertRaisesRegex(staircase.Refusal, "seed ledger or src/stage0 cannot be read"):
                staircase.pinned_root_admission(repo, host)

    @mock.patch.object(staircase, "require_pinned_root")
    def test_a_double_compile_is_bound_to_its_own_build(self, _root_gate) -> None:
        """Measured hazard (2026-10-01): with only rc and commit checked, the
        independent side of a double compile could be any tree — the staircase's
        own manifest passed twice compared `identical` and was sealed as a DDC."""
        self.test_lineage_chains_rungs_by_commit_and_by_bytes()
        root, rung, final, ddc = self.ddc_fixture
        run = ddc["run"]
        final_ids = staircase.sysroot_files(final)
        for broken, reason in (
            ({**ddc, "run": None}, "needs the independent compiler's build record"),
            ({**ddc, "run": {**run, "rc": 2}}, "not a successful build"),
            ({**ddc, "run": {**run, "commit": PARENT}}, "not a successful build"),
            ({**ddc, "run": {**run, "worktree": "/elsewhere"}}, "not where the last rung built"),
            ({**ddc, "run": {**run, "stage0_sha256": rung["stage0_sha256"]}}, "did not run the admitted independent"),
            ({**ddc, "run": {**run, "stage0_commit": HEAD}}, "did not run the admitted independent"),
            ({**ddc, "run": {**run, "stage0_matches_admission": False}}, "did not run the admitted independent"),
            ({**ddc, "run": {**run, "no_stock_evidence": False}}, "DDC build ddc carries no clean no-stock"),
            ({**ddc, "run": {**run, "build_census": {"rustc_info_files": 0}}}, "DDC build ddc's build census read no"),
            # the staircase tree's manifest handed in as the independent one
            ({**ddc, "ddc_identity": ddc["staircase_identity"]}, "independent tree is not the stage2 the DDC build"),
            ({**ddc, "ddc_identity": None}, "independent tree is not the stage2 the DDC build"),
            # "independent" compilers that are the lineage's own: the root seed, the sealed compiler
            ({**ddc, "ddc_seed": {**ddc["ddc_seed"], "sha256": root["sha256"]},
              "run": {**run, "stage0_sha256": root["sha256"]}}, "not a diverse one"),
            ({**ddc, "ddc_seed": {**ddc["ddc_seed"], "sha256": final_ids},
              "run": {**run, "stage0_sha256": final_ids}}, "not a diverse one"),
        ):
            with self.subTest(reason=reason), self.assertRaisesRegex(staircase.Refusal, reason):
                staircase.build_lineage(root, [rung], final, REPO, broken)


class DiverseDoubleCompileTests(unittest.TestCase):
    """The staircase DDC reuses the pack cut's comparator and relation classifier
    (mint_seed_support.py); what it adds is the verdict over the compiler-and-std
    key set W12 names."""

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="seed-staircase-ddc-"))
        self.support = staircase.mint_support()
        for arm in ("a", "b"):
            root = self.tmp / arm / "stage2"
            (root / "bin").mkdir(parents=True)
            (root / "lib" / "rustlib" / "host" / "lib").mkdir(parents=True)
            (root / "bin" / "trustc").write_bytes(b"trustc")
            (root / "bin" / "ay").write_bytes(b"ay")
            (root / "lib" / "librustc_driver-1.dylib").write_bytes(b"driver")
            (root / "lib" / "rustlib" / "host" / "lib" / "libstd-1.rlib").write_bytes(b"std")
        self.seed = {"kind": "stage0-admission", "commit": HEAD, "sha256": {}, "stage0": str(self.tmp)}
        patcher = mock.patch.object(self.support, "ddc_seed_identity", return_value={"relation": "same-lineage"})
        patcher.start()
        self.addCleanup(patcher.stop)

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def record(self, seed: dict | None = None) -> dict:
        paths = []
        for arm in ("a", "b"):
            path = self.tmp / f"{arm}.json"
            path.write_text(json.dumps(self.support.stage2_manifest(self.tmp / arm / "stage2")))
            paths.append(path)
        return staircase.ddc_record(paths[0], paths[1], seed or self.seed, REPO)

    def test_identical_trees(self) -> None:
        record = self.record()
        self.assertEqual(record["verdict"], "identical")
        self.assertEqual(record["stage2_tree_sha256_staircase"], record["stage2_tree_sha256_ddc_seed"])
        self.assertEqual(record["relation"], "same-lineage")
        self.assertEqual(record["compiler_and_std_entries"], 3)
        # The staircase tree's identity, read from its manifest the way
        # sysroot_files reads a stage2: what binds the comparison to the seal.
        self.assertEqual(record["staircase_identity"], staircase.sysroot_files(self.tmp / "a" / "stage2"))

    def test_a_tool_outside_the_compiler_and_std_is_listed_not_hidden(self) -> None:
        (self.tmp / "b" / "stage2" / "bin" / "ay").write_bytes(b"ay built by another stage0")
        record = self.record()
        self.assertEqual(record["verdict"], "compiler-and-std-identical")
        self.assertEqual(record["differences"], ["differs: bin/ay"])

    def test_one_differing_std_byte_or_extra_library_is_different(self) -> None:
        (self.tmp / "b" / "stage2" / "lib" / "rustlib" / "host" / "lib" / "libstd-1.rlib").write_bytes(b"stD")
        record = self.record()
        self.assertEqual(record["verdict"], "different")
        self.assertIn("differs: lib/rustlib/host/lib/libstd-1.rlib", record["compiler_and_std_differences"])
        (self.tmp / "b" / "stage2" / "lib" / "rustlib" / "host" / "lib" / "libstd-1.rlib").write_bytes(b"std")
        (self.tmp / "b" / "stage2" / "lib" / "rustlib" / "host" / "lib" / "libextra-1.rlib").write_bytes(b"x")
        self.assertEqual(self.record()["verdict"], "different")

    def test_trees_without_a_compiler_or_std_are_not_evidence(self) -> None:
        for arm in ("a", "b"):
            (self.tmp / arm / "stage2" / "lib" / "rustlib" / "host" / "lib" / "libstd-1.rlib").unlink()
        self.assertEqual(self.record()["verdict"], "different")

    def test_a_refused_ddc_seed_is_not_evidence(self) -> None:
        with self.assertRaisesRegex(staircase.Refusal, "DDC seed admission carries refusals"):
            self.record({**self.seed, "refusals": ["stock"]})


STARTED = "Thu Oct  1 07:59:27 2026"


def tick_row(pid: int, ppid: int = 1, exe: str = "/bin/stand-in", started: str = STARTED) -> str:
    """One TICK_LISTING row, as `ps -o pid=,ppid=,lstart=,comm=` prints it."""
    return f"{pid:>5} {ppid:>5} {started}     {exe}\n"


class RunRungTests(unittest.TestCase):
    """`run` end to end over a stand-in x.py: the environment it gets, the trap
    shims, the record, and a stop request that still yields a record."""

    XPY = """import json, os, subprocess, sys, time
json.dump(dict(os.environ), open("env.json", "w"))
if "probe-cargo" in sys.argv:
    subprocess.run(["cargo", "--version"])
if "badenv" in sys.argv:
    # A launch environment that is not UTF-8, as `ps -E` then prints it.
    env = dict(os.environb)
    env[b"STAIRCASE_NOT_UTF8"] = b"\\xff\\xfe"
    subprocess.run([sys.executable, "-c", "import time; time.sleep(4)"], env=env)
if "scrubbed" in sys.argv:
    # A descendant started with a CLEARED environment (no rung marker), by
    # absolute path: what a build script's env_clear() + Command does.
    subprocess.run(["/usr/bin/env", "-i", sys.argv[sys.argv.index("scrubbed") + 1]])
if "sleep" in sys.argv:
    time.sleep(120)
if "ignore-term" in sys.argv:
    # A build that does not end on SIGTERM (measured 2026-10-01: x.py hung tearing
    # down its multiprocessing pool after a stop request reached its extraction).
    import signal
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    open("term-ignored", "w").close()
    time.sleep(120)
"""

    def setUp(self) -> None:
        # resolved: the tool resolves its ledger (/var is /private/var on macOS)
        self.tmp = Path(tempfile.mkdtemp(prefix="seed-staircase-run-")).resolve()
        self.tree = self.tmp / "tree"
        self.tree.mkdir()
        (self.tree / "x.py").write_text(self.XPY)
        subprocess.run(["git", "-C", str(self.tree), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(self.tree), "-c", "user.name=t", "-c", "user.email=t@t",
                        "commit", "-q", "--allow-empty", "-m", "x"], check=True)
        self.stage0 = self.tmp / "stage0"
        (self.stage0 / "bin").mkdir(parents=True)
        if platform.system() == "Linux":
            # Native OS stand-ins only for the runner/lifecycle fixture: no
            # Trust compiler, build census or qualifying proof is fabricated.
            for name in ("trustc", "cargo"):
                shutil.copy2("/bin/true", self.stage0 / "bin" / name)
        else:
            (self.stage0 / "bin" / "trustc").write_bytes(b"trustc")
        self.admission = self.tmp / "admission.json"
        admission = {
            "kind": "stage0-admission", "commit": HEAD, "stage0": str(self.stage0),
            "sha256": staircase.sysroot_files(self.stage0)}
        if platform.system() == "Linux":
            admission["dylib_closure"] = staircase.dylib_closure(self.stage0, [])
        self.admission.write_text(json.dumps(admission))
        self.ledger = self.tmp / "ledger"

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def start(self, label: str, *xpy: str, tool_args: tuple[str, ...] = ()) -> subprocess.Popen:
        return subprocess.Popen(
            [sys.executable, str(SCRIPT), "run", "--worktree", str(self.tree), "--label", label,
             "--ledger", str(self.ledger), "--stage0-admission", str(self.admission),
             "--min-available-gib", "0", *tool_args, "--", *xpy],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

    def test_the_rung_environment_and_a_trapped_stock_lookup(self) -> None:
        tool = self.start("probe", "probe-cargo")
        out, err = tool.communicate(timeout=120)
        self.assertEqual(tool.returncode, 0, err)
        record = json.loads(out)
        env = json.loads((self.tree / "env.json").read_text())
        self.assertEqual(env["TRUST_STAIRCASE_RUNG"], "probe")
        self.assertEqual(env["RUSTUP_TOOLCHAIN"], "__trust_no_rustup__")
        # Build-time stamps (ay's build.datetime_utc) follow the source commit, not
        # the wall clock, so two builds of one commit can compare byte for byte.
        commit_time = subprocess.run(["git", "-C", str(self.tree), "log", "-1", "--format=%ct"],
                                     capture_output=True, text=True, check=True).stdout.strip()
        self.assertEqual(env["SOURCE_DATE_EPOCH"], commit_time)
        # No RUSTUP_HOME: with it set beside RUSTUP_TOOLCHAIN, cargo hashes the mtime
        # of $RUSTUP_HOME/toolchains/<toolchain>/bin/rustc, fails, and writes no
        # .rustc_info.json at all (measured 2026-10-01) — which empties the build-tree
        # census of the very files that say which compiler cargo saw.
        self.assertNotIn("RUSTUP_HOME", env)
        self.assertEqual(env["RUSTUP_AUTO_INSTALL"], "0")
        self.assertFalse({"RUSTC", "CARGO", "RUSTC_WRAPPER"} & set(env), env)
        self.assertEqual(env["PATH"].split(":")[0], str(self.ledger / "trap"))
        # The stand-in looked `cargo` up on PATH: the trap refused it, and the
        # record says so rather than calling the rung clean.
        [hit] = record["trap_hits"]
        self.assertIn("cargo\t--version", hit)
        # The hit names its caller's command line, so it can be attributed after the
        # caller is gone (a build script lives for milliseconds).
        self.assertIn("x.py probe-cargo", hit.split("\t")[4])
        self.assertFalse(record["no_stock_evidence"])
        # The record names the tool that wrote it, by bytes.
        self.assertEqual(record["tool"]["sha256"], staircase.sha256_file(SCRIPT))
        self.assertEqual(json.loads((self.ledger / "rungs.jsonl").read_text().splitlines()[-1])["label"], "probe")

    def test_a_declared_tool_dir_comes_after_the_os_dirs_and_is_recorded(self) -> None:
        tools = self.tmp / "tools"
        tools.mkdir()
        shutil.copy2("/bin/true", tools / "ninja")
        tool = self.start("tools", "plain", tool_args=("--tool-dir", str(tools)))
        out, err = tool.communicate(timeout=120)
        self.assertEqual(tool.returncode, 0, err)
        record = json.loads(out)
        path = json.loads((self.tree / "env.json").read_text())["PATH"].split(":")
        self.assertEqual(path[0], str(self.ledger / "trap"))
        self.assertEqual(path[-1], str(tools))
        self.assertLess(path.index("/usr/bin"), path.index(str(tools)))
        [row] = record["tool_dirs"]
        [entry] = row["entries"]
        self.assertEqual(entry["name"], "ninja")
        self.assertEqual(entry["sha256"], staircase.sha256_file(tools / "ninja"))
        self.assertTrue(record["tool_dirs_unchanged"])

    def test_a_tool_dir_that_changes_under_the_build_voids_its_evidence(self) -> None:
        tools = self.tmp / "tools"
        tools.mkdir()
        shutil.copy2("/bin/true", tools / "ninja")
        self.tree.joinpath("x.py").write_text(self.XPY + (
            f"open({str(tools / 'ninja')!r}, 'ab').write(b'changed')\n"))
        tool = self.start("changed", "plain", tool_args=("--tool-dir", str(tools)))
        out, err = tool.communicate(timeout=120)
        record = json.loads(out)
        self.assertFalse(record["tool_dirs_unchanged"])
        self.assertFalse(record["no_stock_evidence"])

    def test_a_stop_request_reaches_the_build_and_the_record_is_still_written(self) -> None:
        tool = self.start("stopped", "sleep")
        for _ in range(600):
            if (self.tree / "env.json").exists():
                break
            time.sleep(0.1)
        else:
            self.fail("the stand-in x.py never started")
        tool.send_signal(signal.SIGTERM)
        out, err = tool.communicate(timeout=120)
        record = json.loads(out)
        self.assertEqual(record["rc"], -signal.SIGTERM, err)
        self.assertEqual(tool.returncode, 1)
        self.assertFalse(record["no_stock_evidence"] and record.get("produced"))

    def plain_and_optioned(self, *options: str) -> tuple[dict, dict, dict, dict]:
        """One run with no new option and one with `options`: (record, x.py's
        environment) of each."""
        runs = []
        for label, extra in (("plain", ()), ("optioned", options)):
            tool = self.start(label, "plain", tool_args=extra)
            out, err = tool.communicate(timeout=120)
            self.assertEqual(tool.returncode, 0, err)
            runs += [json.loads(out), json.loads((self.tree / "env.json").read_text())]
        return runs[0], runs[1], runs[2], runs[3]

    def test_offline_and_a_pinned_lean_library_add_only_their_variables_and_one_record_key(self) -> None:
        library = clean_lean_fixture(self.tree, self.tmp)
        plain, plain_env, record, env = self.plain_and_optioned("--offline", "--clean-lean-lib", str(library))
        # Without the options: today's environment, key for key, and today's record.
        self.assertEqual(set(plain_env) - {"SSH_AUTH_SOCK"}, RUN_ENVIRONMENT_KEYS)
        self.assertEqual(plain_env, plain["environment"])
        self.assertNotIn("clean_lean", plain)
        self.assertFalse(RUN_OPTION_KEYS & set(plain_env))
        # With them: the same environment plus exactly the three variables ...
        self.assertEqual(set(env) - set(plain_env), RUN_OPTION_KEYS)
        self.assertEqual({key: value for key, value in env.items() if key not in RUN_OPTION_KEYS},
                         {**plain_env, "TRUST_STAIRCASE_RUNG": "optioned"})
        self.assertEqual({key: env[key] for key in RUN_OPTION_KEYS}, {
            "CARGO_NET_OFFLINE": "true", "CLEAN_OLEAN_PINNED_LEAN_LIB": str(library),
            "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"})
        self.assertEqual(env, record["environment"])
        # ... and the same record plus exactly one key.
        self.assertEqual(set(record) - set(plain), {"clean_lean"})
        lean = record["clean_lean"]
        self.assertEqual(lean["library"], str(library))
        self.assertEqual(lean["before"], lean["after"])
        self.assertTrue(lean["unchanged"])
        self.assertEqual(set(lean["before"]), {"fingerprint", "manifest_sha256"})
        # The manifest digest is the digest of the file the mint's own command writes.
        manifest = self.tmp / "clean-lean-inputs.json"
        subprocess.run([sys.executable, "-I", "-S", "-B", str(REPO / "scripts" / "mint_seed_support.py"),
                        "clean-lean-inputs", "--root", str(self.tree), "--library", str(library),
                        "--output", str(manifest)], check=True)
        self.assertEqual(lean["before"]["manifest_sha256"], staircase.sha256_file(manifest))
        self.assertEqual(lean["before"]["fingerprint"], json.loads(manifest.read_text())["fingerprint"])
        self.assertEqual(json.loads((self.ledger / "rungs.jsonl").read_text().splitlines()[-1])["clean_lean"], lean)

    def test_each_option_alone_adds_only_its_own(self) -> None:
        library = clean_lean_fixture(self.tree, self.tmp)
        _, plain_env, record, env = self.plain_and_optioned("--offline")
        self.assertEqual(set(env) - set(plain_env), {"CARGO_NET_OFFLINE"})
        self.assertNotIn("clean_lean", record)
        _, plain_env, record, env = self.plain_and_optioned("--clean-lean-lib", str(library))
        self.assertEqual(set(env) - set(plain_env), RUN_OPTION_KEYS - {"CARGO_NET_OFFLINE"})
        self.assertTrue(record["clean_lean"]["unchanged"])

    def test_a_lean_library_that_changes_under_the_build_is_recorded_as_changed(self) -> None:
        library = clean_lean_fixture(self.tree, self.tmp)
        self.tree.joinpath("x.py").write_text(self.XPY + (
            f"open({str(library / 'Init' / 'Prelude.olean')!r}, 'ab').write(b'changed')\n"))
        tool = self.start("lean-changed", "plain", tool_args=("--clean-lean-lib", str(library)))
        out, err = tool.communicate(timeout=120)
        self.assertEqual(tool.returncode, 0, err)
        lean = json.loads(out)["clean_lean"]
        self.assertFalse(lean["unchanged"])
        self.assertNotEqual(lean["before"], lean["after"])

    def test_a_library_the_clean_pin_does_not_name_is_refused_before_the_build_starts(self) -> None:
        library = clean_lean_fixture(self.tree, self.tmp)
        other = self.tmp / "lean" / "leanprover--lean4---v0.0.0" / "lib" / "lean"
        shutil.copytree(library, other)
        for given, words in ((other, "exact pinned"), (Path("lean/lib/lean"), "absolute path")):
            with self.subTest(given=given):
                tool = self.start("wrong-lean", "plain", tool_args=("--clean-lean-lib", str(given)))
                out, err = tool.communicate(timeout=120)
                self.assertEqual(tool.returncode, 1, err)
                self.assertIn(words, json.loads(out)["refused"])
                self.assertIn("--clean-lean-lib", json.loads(out)["refused"])
                # Nothing ran and nothing was written.
                self.assertFalse((self.tree / "env.json").exists())
                self.assertFalse(self.ledger.exists())

    def fifo_run(self, label: str, *xpy: str, tool_args: tuple[str, ...] = ("--fifo-jobserver",)
                 ) -> tuple[int, dict, str]:
        """`run --fifo-jobserver` of the FIFO stand-in: (exit code, printed JSON, stderr)."""
        self.tree.joinpath("x.py").write_text(FIFO_XPY)
        self.tree.joinpath("jobserver.json").unlink(missing_ok=True)
        tool = self.start(label, *xpy, tool_args=tool_args)
        out, err = tool.communicate(timeout=120)
        return tool.returncode, json.loads(out), err

    def test_a_fifo_jobserver_is_reached_by_its_path_from_a_probe_with_only_fds_0_to_2(self) -> None:
        code, record, err = self.fifo_run("fifo", "-j", "4", "build")
        self.assertEqual(code, 0, err)
        path = self.ledger / "tmp" / "jobserver.fifo"
        seen = json.loads((self.tree / "jobserver.json").read_text())
        # x.py saw a private FIFO at the run's TMPDIR holding N-1 tokens for -jN ...
        self.assertEqual((seen["jobs"], seen["path"], seen["tokens"]), (4, str(path), 3))
        self.assertEqual(seen["env"]["MAKEFLAGS"], f"-j4 --jobserver-auth=fifo:{path}")
        self.assertEqual(seen["env"]["TMPDIR"], str(self.ledger / "tmp"))
        self.assertEqual(seen["env"], record["environment"])
        # ... and a grandchild with only fds 0-2 (a build script's probe under Trust std)
        # reopened it by its path and took a token.
        self.assertEqual(seen["probe"], {"fds": [0, 1, 2], "token": "+"})
        # Every token came back; the record says so, and the FIFO is gone. The record
        # names the make adapter first on x.py's PATH by its bytes, and the make it runs.
        make = staircase.real_make([])
        adapter = self.ledger / "pathbin" / "make"
        self.assertEqual(record["jobserver"], {
            "kind": "fifo", "path": str(path), "jobs": 4, "jobs_from": "x.py -j", "tokens": 3, "tokens_at_end": 3,
            "path_unchanged": True,
            "make_adapter": {"path": str(adapter), "sha256": staircase.sha256_file(adapter), "make": make,
                             "make_sha256": staircase.sha256_file(Path(os.path.realpath(make)))}})
        self.assertEqual(adapter.read_text(), staircase.make_adapter_text(record["python"], make))
        self.assertEqual(seen["env"]["PATH"].split(":")[1], str(adapter.parent))
        self.assertEqual(adapter.stat().st_mode & 0o777, 0o755)
        self.assertFalse(path.exists() or path.is_symlink())
        self.assertEqual(json.loads((self.ledger / "rungs.jsonl").read_text().splitlines()[-1])["jobserver"],
                         record["jobserver"])
        # One job: no token to preload, and the FIFO is still made, held and removed.
        code, record, err = self.fifo_run("one", "-j1", "build")
        self.assertEqual(code, 0, err)
        self.assertEqual((record["jobserver"]["tokens"], record["jobserver"]["tokens_at_end"]), (0, 0))

    def test_make_run_by_a_build_step_reaches_the_fifo_through_the_adapter(self) -> None:
        # This host's make (GNU make 4.3 on the GB10) stops on fifo:PATH; through the
        # adapter it is handed the FIFO as two descriptors, and the tokens are the FIFO's.
        code, record, err = self.fifo_run("make", "-j", "3", "make")
        self.assertEqual(code, 0, err)
        made = json.loads((self.tree / "jobserver.json").read_text())["make"]
        self.assertEqual(made["rc"], 0, made["stderr"])
        self.assertNotIn("jobserver unavailable", made["stderr"])
        self.assertRegex(made["check"]["makeflags"], r"--jobserver-(auth|fds)=[0-9]+,[0-9]+")
        self.assertNotIn("fifo:", made["check"]["makeflags"])
        self.assertEqual(made["check"]["descriptors_are_the_fifo"], [True, True])
        self.assertEqual((record["jobserver"]["tokens"], record["jobserver"]["tokens_at_end"]), (2, 2))
        self.assertTrue(record["jobserver"]["path_unchanged"])

    def test_a_ledger_path_with_white_space_is_refused_before_anything_is_written(self) -> None:
        self.ledger = self.tmp / "led ger"
        code, refused, err = self.fifo_run("spaced", "-j", "2", "build")
        self.assertEqual(code, 1, err)
        self.assertRegex(refused["refused"], r"holds white space, and a jobserver client reads MAKEFLAGS word by "
                                             r"word\. Nothing was started and nothing was written")
        self.assertFalse(self.ledger.exists())
        self.assertFalse((self.tree / "jobserver.json").exists())

    def test_the_fifo_is_removed_when_x_py_cannot_be_started(self) -> None:
        # The log x.py would write is a directory: opening it fails after the FIFO is made.
        (self.ledger / "logs" / "blocked.log").mkdir(parents=True)
        self.tree.joinpath("x.py").write_text(FIFO_XPY)
        tool = self.start("blocked", "-j", "2", "build", tool_args=("--fifo-jobserver",))
        out, err = tool.communicate(timeout=120)
        self.assertNotEqual(tool.returncode, 0, out)
        self.assertIn("IsADirectoryError", err)
        self.assertFalse((self.tree / "jobserver.json").exists())
        fifo = self.ledger / "tmp" / "jobserver.fifo"
        self.assertFalse(fifo.exists() or fifo.is_symlink())

    def test_a_stop_request_while_x_py_is_being_started_leaves_no_fifo_behind(self) -> None:
        # The log is a FIFO with no reader yet, so the run waits there with the
        # jobserver made and x.py not started; a SIGTERM then must not end the run on
        # the spot with the FIFO left behind.
        (self.ledger / "logs").mkdir(parents=True)
        log = self.ledger / "logs" / "early.log"
        os.mkfifo(log)
        fifo = self.ledger / "tmp" / "jobserver.fifo"
        tool = self.start("early", "-j", "2", "sleep", tool_args=("--fifo-jobserver",))
        for _ in range(600):
            if fifo.exists():
                break
            time.sleep(0.1)
        else:
            tool.kill()
            self.fail(f"the run never made its FIFO: {tool.communicate()}")
        time.sleep(0.5)
        tool.send_signal(signal.SIGTERM)
        time.sleep(0.5)
        reader = os.open(log, os.O_RDONLY | os.O_NONBLOCK)
        try:
            out, err = tool.communicate(timeout=120)
        finally:
            os.close(reader)
        self.assertEqual(tool.returncode, 1, err)
        printed = json.loads(out)
        if "refused" in printed:
            self.assertRegex(printed["refused"], r"a SIGTERM reached this run before x.py was started, so x.py was "
                                                 r"not started and no record was written")
        else:
            self.assertEqual(printed["stop"]["signal"], "SIGTERM")
            self.assertEqual(printed["rc"], -signal.SIGTERM)
            self.assertEqual(printed["jobserver"]["tokens_at_end"], 1)
        self.assertFalse(fifo.exists() or fifo.is_symlink())

    def test_a_jobserver_that_does_not_balance_is_recorded_and_not_judged_here(self) -> None:
        path = self.ledger / "tmp" / "jobserver.fifo"
        for word, at_end in (("leak", 2), ("extra", 4)):
            with self.subTest(word):
                code, record, err = self.fifo_run(word, "-j", "4", word)
                # The build's exit and the tool's are x.py's: the count is a fact for the reader.
                self.assertEqual((code, record["rc"]), (0, 0), err)
                self.assertEqual((record["jobserver"]["tokens"], record["jobserver"]["tokens_at_end"]), (3, at_end))
                self.assertTrue(record["jobserver"]["path_unchanged"])
                self.assertFalse(path.exists())

    def test_a_jobserver_path_replaced_under_the_build_is_recorded_kept_and_refused_next_time(self) -> None:
        path = self.ledger / "tmp" / "jobserver.fifo"
        code, record, err = self.fifo_run("replaced", "-j", "2", "replace")
        self.assertEqual(code, 0, err)
        self.assertEqual(record["jobserver"]["path_unchanged"], False)
        self.assertEqual(record["jobserver"]["tokens_at_end"], 1)
        # What stands at the path is not this run's FIFO, so it is not removed ...
        self.assertEqual(path.read_text(), "not a FIFO\n")
        # ... and the next run of this ledger refuses before anything starts.
        rungs = (self.ledger / "rungs.jsonl").read_text()
        code, refused, err = self.fifo_run("after", "-j", "2", "build")
        self.assertEqual(code, 1, err)
        self.assertRegex(refused["refused"], r"jobserver.fifo is already there: .*Nothing was started")
        self.assertFalse((self.tree / "jobserver.json").exists())
        self.assertEqual((self.ledger / "rungs.jsonl").read_text(), rungs)

    def test_without_a_job_count_nothing_starts_and_a_configured_one_is_read(self) -> None:
        code, refused, err = self.fifo_run("unknown", "build")
        self.assertEqual(code, 1, err)
        self.assertRegex(refused["refused"], r"--fifo-jobserver: the job count x.py runs with is named nowhere.*"
                                             r"Nothing was started and nothing was written")
        self.assertFalse((self.tree / "jobserver.json").exists())
        self.assertFalse(self.ledger.exists())
        (self.tree / "bootstrap.toml").write_text("[build]\njobs = 2\n")
        code, record, err = self.fifo_run("configured", "build")
        self.assertEqual(code, 0, err)
        self.assertEqual((record["jobserver"]["jobs"], record["jobserver"]["jobs_from"]),
                         (2, f"[build] jobs of {self.tree / 'bootstrap.toml'}"))
        self.assertEqual(json.loads((self.tree / "jobserver.json").read_text())["tokens"], 1)

    def test_without_the_fifo_jobserver_the_environment_and_record_are_what_they_were(self) -> None:
        # No -j and no configuration: a run without the option reads no job count.
        tool = self.start("plain", "plain")
        out, err = tool.communicate(timeout=120)
        self.assertEqual(tool.returncode, 0, err)
        plain, plain_env = json.loads(out), json.loads((self.tree / "env.json").read_text())
        self.assertEqual(set(plain_env) - {"SSH_AUTH_SOCK"}, RUN_ENVIRONMENT_KEYS)
        self.assertEqual(plain_env, plain["environment"])
        self.assertNotIn("jobserver", plain)
        self.assertEqual(list((self.ledger / "tmp").iterdir()), [])
        plain_pathbin = sorted(entry.name for entry in (self.ledger / "pathbin").iterdir())
        self.assertNotIn("make", plain_pathbin)
        tool = self.start("optioned", "-j", "3", "plain", tool_args=("--fifo-jobserver",))
        out, err = tool.communicate(timeout=120)
        self.assertEqual(tool.returncode, 0, err)
        record, env = json.loads(out), json.loads((self.tree / "env.json").read_text())
        # With it: exactly MAKEFLAGS more, and exactly one record key more.
        self.assertEqual(set(env) - set(plain_env), {"MAKEFLAGS"})
        self.assertEqual({key: value for key, value in env.items() if key != "MAKEFLAGS"},
                         {**plain_env, "TRUST_STAIRCASE_RUNG": "optioned"})
        self.assertEqual(set(record) - set(plain), {"jobserver"})
        self.assertEqual(set(plain) - set(record), set())
        # Its make adapter is in pathbin only for runs given the option: a later run of
        # the ledger without it reaches the make it always reached.
        adapter = self.ledger / "pathbin" / "make"
        self.assertNotEqual(sorted(plain_pathbin), sorted(entry.name for entry in adapter.parent.iterdir()))
        self.assertTrue(adapter.is_file())
        tool = self.start("again", "plain")
        out, err = tool.communicate(timeout=120)
        self.assertEqual(tool.returncode, 0, err)
        self.assertEqual(sorted(entry.name for entry in adapter.parent.iterdir()), plain_pathbin)
        self.assertEqual(json.loads((self.tree / "env.json").read_text()),
                         {**plain_env, "TRUST_STAIRCASE_RUNG": "again"})
        # A make in pathbin that is not the adapter is not removed.
        adapter.write_text("#!/bin/sh\n# not the adapter\n")
        tool = self.start("kept", "plain")
        out, err = tool.communicate(timeout=120)
        self.assertEqual(tool.returncode, 0, err)
        self.assertEqual(adapter.read_text(), "#!/bin/sh\n# not the adapter\n")

    def test_a_build_that_ignores_the_stop_request_is_killed_after_the_grace_period(self) -> None:
        tool = self.start("ignores", "ignore-term", tool_args=("--stop-grace-seconds", "2"))
        for _ in range(600):
            if (self.tree / "term-ignored").exists():
                break
            time.sleep(0.1)
        else:
            tool.kill()
            self.fail("the stand-in x.py never started")
        tool.send_signal(signal.SIGTERM)
        # The stand-in ignores SIGTERM and would sleep 120 s.
        out, err = tool.communicate(timeout=60)
        record = json.loads(out)
        self.assertEqual(record["rc"], -signal.SIGKILL, err)
        self.assertEqual(record["stop"]["signal"], "SIGTERM")
        self.assertIn("escalated_to_sigkill_at", record["stop"])
        self.assertFalse(record["no_stock_evidence"] and record.get("produced"))

    def test_a_launch_environment_that_is_not_utf8_does_not_end_the_census(self) -> None:
        # Measured 2026-09-30: `ps -E` printed a 0xff byte from a process's
        # environment, the census died on the decode five hours into rung R0, and
        # the build compiled on for six more hours with nobody watching.
        tool = self.start("badenv", "badenv")
        out, err = tool.communicate(timeout=120)
        self.assertEqual(tool.returncode, 0, err)
        census = json.loads(out)["process_census"]
        self.assertNotIn("error", census, err)
        self.assertEqual(census["ended"], "watched-exited")
        self.assertTrue(census["executables"], census)
        self.assertLessEqual(census["max_gap_s"], staircase.MAX_CENSUS_GAP_S)

    def test_a_build_the_census_stops_watching_is_stopped(self) -> None:
        tool = self.start("unwatched", "sleep")
        sampler = None
        for _ in range(600):
            listing = subprocess.run(["/bin/ps", "-axo", "pid=,command="], capture_output=True).stdout
            for line in listing.decode("utf-8", "replace").splitlines():
                if "_sample unwatched " in line and str(SCRIPT) in line:
                    sampler = int(line.split(None, 1)[0])
            if sampler and (self.tree / "env.json").exists():
                break
            time.sleep(0.1)
        else:
            tool.kill()
            self.fail("the stand-in x.py or its census never started")
        os.kill(sampler, signal.SIGKILL)
        # The stand-in would sleep 120 s: the tool must stop it long before that.
        out, err = tool.communicate(timeout=60)
        record = json.loads(out)
        self.assertIn("sampler_died", record, err)
        self.assertEqual(record["rc"], -signal.SIGTERM)
        self.assertFalse(record["no_stock_evidence"])

    def test_a_census_killed_mid_rung_keeps_its_last_checkpoint_and_is_not_complete(self) -> None:
        out = self.tmp / "census.json"
        calls = {"n": 0}

        def listing(argv: list[str]) -> str:
            if "-Eww" in argv:
                return f"{os.getpid()} /bin/stand-in TRUST_STAIRCASE_RUNG=ck\n"
            calls["n"] += 1
            if calls["n"] > 2:  # the third sample: the census is killed here
                raise KeyboardInterrupt
            return tick_row(os.getpid())

        with mock.patch.object(staircase, "ps_listing", side_effect=listing), \
                mock.patch.object(staircase.time, "sleep"):
            with self.assertRaises(KeyboardInterrupt):
                staircase.sample_processes("ck", os.getpid(), out, [], 0.0, 10**6, checkpoint_every=2)
        census = json.loads(out.read_text())
        self.assertEqual(census["ended"], "running")
        self.assertEqual(census["iterations"], 2)
        self.assertEqual(census["executables"][0]["exe"], "/bin/stand-in")
        self.assertFalse(staircase.census_is_complete(census))

    def test_a_stalled_ps_costs_one_bounded_sample_not_the_census(self) -> None:
        # Measured 2026-10-01: in a 12.5 h rung under load average 130-170, `ps`
        # stalled eight times; each stall cost the old 30 s timeout, and consecutive
        # stalls opened a 178 s blind spot, over MAX_CENSUS_GAP_S, voiding the
        # rung's evidence for a reason that had nothing to do with stock Rust.
        out = self.tmp / "census.json"
        real = staircase.ps_listing
        calls = {"n": 0}

        def listing(argv: list[str]) -> str:
            calls["n"] += 1
            if calls["n"] <= 3:  # three stalled listings in a row
                return real(["/bin/sleep", "30"])
            return f"{os.getpid()} /bin/stand-in TRUST_STAIRCASE_RUNG=st\n" if "-Eww" in argv else tick_row(os.getpid())

        started = time.monotonic()
        with mock.patch.object(staircase, "SAMPLE_TIMEOUT_S", 0.5), \
                mock.patch.object(staircase, "ps_listing", side_effect=listing):
            staircase.sample_processes("st", os.getpid(), out, [], 0.0, 8)
        census = json.loads(out.read_text())
        self.assertEqual(census["failed_samples"], 3, census["errors"])
        self.assertLess(census["max_gap_s"], 5.0)
        self.assertLess(time.monotonic() - started, 10.0)
        self.assertEqual(census["executables"][0]["exe"], "/bin/stand-in")

    def test_a_census_names_its_long_gaps(self) -> None:
        out = self.tmp / "census.json"
        clock = {"t": 0.0}
        calls = {"n": 0}

        def listing(argv: list[str]) -> str:
            if "-Eww" in argv:
                return f"{os.getpid()} /bin/stand-in TRUST_STAIRCASE_RUNG=gp\n"
            calls["n"] += 1
            if calls["n"] == 3:  # the third sample's listing: the machine stalls 45 s
                clock["t"] += 45.0
            return tick_row(os.getpid())

        with mock.patch.object(staircase, "ps_listing", side_effect=listing), \
                mock.patch.object(staircase.time, "monotonic", side_effect=lambda: clock["t"]), \
                mock.patch.object(staircase.time, "sleep", side_effect=lambda s: clock.__setitem__("t", clock["t"] + 1.0)):
            staircase.sample_processes("gp", os.getpid(), out, [], 1.0, 5)
        census = json.loads(out.read_text())
        self.assertEqual(census["max_gap_s"], 46.0)
        [gap] = census["long_gaps"]
        self.assertEqual(gap["gap_s"], 46.0)
        self.assertIn("at", gap)

    def test_a_killed_census_child_is_never_waited_for(self) -> None:
        """Measured 2026-10-01: `ps -axE`, blocked in the kernel reading another
        process's memory, outlived its SIGKILL by ~90 s; subprocess.run's timeout
        path waits for the killed child, so a "10 s" sample cost 100 s, twice in a
        row, and a five-hour rung's census had a 229.5 s blind spot. A child that
        does not die on SIGKILL is the stand-in here."""
        class Unkillable:
            def __init__(self, args, **_kwargs):
                self.args, self.returncode, self.killed = args, None, False
                self.stdout = self.stderr = self.stdin = None

            def communicate(self, input=None, timeout=None):
                time.sleep(timeout or 0)
                raise subprocess.TimeoutExpired(self.args, timeout)

            def kill(self):
                self.killed = True

            def poll(self):
                return None

            def wait(self, timeout=None):
                time.sleep(8 if timeout is None else timeout)  # still in the kernel
                return 0

            def __enter__(self):
                return self

            def __exit__(self, *exc):
                self.wait()

        started = time.monotonic()
        with mock.patch.object(staircase, "SAMPLE_TIMEOUT_S", 0.2), \
                mock.patch.object(staircase.subprocess, "Popen", Unkillable):
            with self.assertRaises(subprocess.TimeoutExpired):
                staircase.ps_listing(["/bin/ps", "-axEww", "-o", "pid=,command="])
        self.assertLess(time.monotonic() - started, 3.0)
        abandoned = staircase._ABANDONED.pop()
        self.assertTrue(abandoned.killed)

    def test_stalled_environment_reads_do_not_blind_the_census(self) -> None:
        """Environment reads are off the tick: the census keeps listing the rung
        from the process table while every `ps -E` stalls (old census: every
        sample failed, so the whole run was one blind spot)."""
        out = self.tmp / "census.json"

        def listing(argv: list[str]) -> str:
            if any("E" in arg and arg.startswith("-") for arg in argv):
                time.sleep(0.2)
                raise subprocess.TimeoutExpired(argv, 0.2)
            return tick_row(os.getpid())

        with mock.patch.object(staircase, "ps_listing", side_effect=listing):
            staircase.sample_processes("ev", os.getpid(), out, [], 0.0, 8)
        census = json.loads(out.read_text())
        self.assertEqual(census["failed_samples"], 0, census["errors"])
        self.assertLess(census["max_gap_s"], 1.0)
        self.assertGreater(census["environment_read_failures"], 0)
        self.assertEqual(census["executables"][0]["exe"], "/bin/stand-in")

    def test_orphans_are_members_only_when_they_carry_the_marker(self) -> None:
        out = self.tmp / "census.json"
        me = os.getpid()
        ticks = {"n": 0}

        def listing(argv: list[str]) -> str:
            if "-Eww" in argv:
                pids = argv[argv.index("-p") + 1].split(",")
                env = {str(me): "x.py", "70001": "cargo TRUST_STAIRCASE_RUNG=or", "70002": "cargo HOME=/x"}
                return "".join(f"{pid} {env[pid]}\n" for pid in pids if pid in env)
            ticks["n"] += 1
            rows = tick_row(me) + tick_row(4242, exe="/usr/libexec/old-daemon")  # pre-existing orphan
            if ticks["n"] >= 2:  # new orphans: one marked, one not, one gone before it is read
                rows += (tick_row(70001, exe="/opt/stock/bin/cargo") + tick_row(70002, exe="/opt/other/bin/cargo")
                         + tick_row(70003, exe="/opt/gone/bin/rustc"))
            if ticks["n"] >= 3:  # the marked orphan's child: a member by descent
                rows += tick_row(70004, ppid=70001, exe="/opt/stock/bin/rustc")
            return rows

        with mock.patch.object(staircase, "ps_listing", side_effect=listing):
            staircase.sample_processes("or", me, out, ["/allowed"], 0.0, 4)
        census = json.loads(out.read_text())
        exes = {row["exe"]: row["class"] for row in census["executables"]}
        self.assertEqual(exes["/opt/stock/bin/cargo"], "RUST-OUTSIDE-ADMITTED-ROOTS")
        self.assertEqual(exes["/opt/stock/bin/rustc"], "RUST-OUTSIDE-ADMITTED-ROOTS")
        self.assertNotIn("/opt/other/bin/cargo", exes)     # another workload's orphan
        self.assertNotIn("/usr/libexec/old-daemon", exes)  # listed before the rung began
        self.assertEqual(census["marked_orphans"], 1)
        [gone] = census["unverified_orphans"]
        self.assertEqual(gone["exe"], "/opt/gone/bin/rustc")
        self.assertEqual(census["flagged"], ["/opt/gone/bin/rustc", "/opt/stock/bin/cargo", "/opt/stock/bin/rustc"])

    @unittest.skipUnless(CC, "needs a C compiler for a native stand-in")
    def test_a_descendant_with_a_cleared_environment_is_in_the_census(self) -> None:
        """The old census found the rung only by the marker in each process's
        launch environment: a build script that clears its child's environment
        and runs a stock compiler by absolute path was invisible to it."""
        source = self.tmp / "sleeper.c"
        source.write_text("#include <unistd.h>\nint main(void) { sleep(3); return 0; }\n")
        stock = self.tmp / "elsewhere" / "bin"
        stock.mkdir(parents=True)
        subprocess.run([CC, "-o", str(stock / "cargo"), str(source)], check=True)
        tool = self.start("scrubbed", "scrubbed", str(stock / "cargo"))
        out, err = tool.communicate(timeout=120)
        census = json.loads(out)["process_census"]
        exes = {row["exe"]: row["class"] for row in census["executables"]}
        self.assertEqual(exes.get(str(stock / "cargo")), "RUST-OUTSIDE-ADMITTED-ROOTS", (census, err))
        self.assertIn(str(stock / "cargo"), census["flagged"])
        self.assertFalse(json.loads(out)["no_stock_evidence"])

    def test_census_completeness(self) -> None:
        complete = {"ended": "watched-exited", "max_gap_s": 3.0}
        self.assertTrue(staircase.census_is_complete(complete))
        self.assertFalse(staircase.census_is_complete({**complete, "ended": "cap"}))
        self.assertFalse(staircase.census_is_complete({**complete, "max_gap_s": staircase.MAX_CENSUS_GAP_S + 1}))
        self.assertFalse(staircase.census_is_complete({"error": "no census written"}))


class TrustSwitchTests(unittest.TestCase):
    def test_exact_option_names_only(self) -> None:
        self.assertTrue(staircase.advertises_trust_switch("    -Z   no-trust-verify=val -- off"))
        self.assertTrue(staircase.advertises_trust_switch("    -Z   trust-verify=val -- on/off"))
        self.assertFalse(staircase.advertises_trust_switch("    -Z   trust-verify-level=val -- x"))
        self.assertFalse(staircase.advertises_trust_switch("trust-verify=val without -Z"))


class BuildCensusTests(unittest.TestCase):
    def setUp(self) -> None:
        self.build = Path(tempfile.mkdtemp(prefix="seed-staircase-census-"))

    def tearDown(self) -> None:
        shutil.rmtree(self.build, ignore_errors=True)

    def info(self, rel: str, version: str, sysroot: str) -> None:
        path = self.build / rel / ".rustc_info.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"rustc_fingerprint": 1, "outputs": {
            "1": {"success": True, "status": "", "code": 0, "stdout": f"{version}\nbinary: rustc\n", "stderr": ""},
            "2": {"success": True, "status": "", "code": 0, "stdout": f"___\nlib___.rlib\n{sysroot}\n", "stderr": ""},
        }}))

    def test_stock_stage0_cache_is_flagged_and_trust_is_not(self) -> None:
        self.info("bootstrap", f"rustc 1.98.0 ({STOCK_COMMIT[:9]} 2026-08-18)",
                  f"{staircase.HOME}/.rustup/toolchains/stable-aarch64-apple-darwin")
        self.info("host/stage1-rustc", f"rustc 1.99.0-dev ({HEAD[:10]} 2026-09-29)", str(self.build / "host/stage0"))
        census = staircase.scan_build(self.build, REPO)
        self.assertFalse(census["clean"])
        [flagged] = census["flagged_rustc_info"]
        self.assertEqual(flagged["file"], "bootstrap/.rustc_info.json")
        self.assertEqual(len(flagged["flags"]), 2, flagged["flags"])

    def test_foreign_std_paths_in_a_driver_are_flagged(self) -> None:
        driver = self.build / "host" / "stage1" / "lib" / "librustc_driver-x.dylib"
        driver.parent.mkdir(parents=True)
        driver.write_bytes(b"\xcf\xfa\xed\xfe" + f"/rustc/{HEAD}/library/std\0/rustc/{STOCK_COMMIT}/library/core\0".encode())
        census = staircase.scan_build(self.build, REPO)
        self.assertEqual(census["foreign_rustc_paths"], [f"host/stage1/lib/librustc_driver-x.dylib: /rustc/{STOCK_COMMIT}"])
        driver.write_bytes(b"\xcf\xfa\xed\xfe" + f"/rustc/{HEAD}/library/std\0".encode())
        self.trust_info()
        self.assertTrue(staircase.scan_build(self.build, REPO)["clean"])

    @unittest.skipUnless(PARENT, "needs a parent commit")
    def test_a_rung_may_name_only_its_own_and_its_stage0_commits(self) -> None:
        # Trust merges upstream, so "in this history" admits a stock nightly's std;
        # a rung's census allows exactly the rung's source and its stage0.
        driver = self.build / "host" / "stage1" / "lib" / "librustc_driver-x.dylib"
        driver.parent.mkdir(parents=True)
        driver.write_bytes(b"\xcf\xfa\xed\xfe" + f"/rustc/{HEAD}/library/std\0/rustc/{PARENT}/library/core\0".encode())
        self.trust_info()
        self.assertTrue(staircase.scan_build(self.build, REPO)["clean"])
        census = staircase.scan_build(self.build, REPO, {HEAD})
        self.assertEqual(census["foreign_rustc_paths"], [f"host/stage1/lib/librustc_driver-x.dylib: /rustc/{PARENT}"])
        self.assertTrue(staircase.scan_build(self.build, REPO, {HEAD, PARENT})["clean"])

    def trust_info(self) -> None:
        self.info("host/stage1-rustc", f"rustc 1.99.0-dev ({HEAD[:10]} 2026-09-29)", str(self.build / "host/stage0"))

    def test_a_census_without_a_compiler_record_is_not_clean(self) -> None:
        """Measured 2026-10-01: with RUSTUP_HOME beside the rustup sentinel cargo
        wrote no .rustc_info.json in a twelve-hour rung, and the census still
        said clean on the std paths alone."""
        driver = self.build / "host" / "stage1" / "lib" / "librustc_driver-x.dylib"
        driver.parent.mkdir(parents=True)
        driver.write_bytes(b"\xcf\xfa\xed\xfe" + f"/rustc/{HEAD}/library/std\0".encode())
        census = staircase.scan_build(self.build, REPO)
        self.assertEqual(census["rustc_info_files"], 0)
        self.assertFalse(census["clean"])
        self.trust_info()
        self.assertTrue(staircase.scan_build(self.build, REPO)["clean"])

    def test_unremapped_std_roots_are_reported(self) -> None:
        tool = self.build / "host" / "stage1" / "bin" / "ay"
        tool.parent.mkdir(parents=True)
        tool.write_bytes(b"\xcf\xfa\xed\xfe\0library/std/src/panicking.rs\0")
        census = staircase.scan_build(self.build, REPO)
        self.assertEqual(census["unremapped_std_roots"], {"host/stage1/bin/ay": {"<home>/trust": 1}})


    def test_seed_and_current_tool_domains_both_remain_in_the_census(self) -> None:
        self.trust_info()
        expected = []
        for domain in ["bootstrap-tools", "bootstrap-seed-tools"]:
            rel = f"host/{domain}/aarch64-apple-darwin/release/targo"
            tool = self.build / rel
            tool.parent.mkdir(parents=True)
            tool.write_bytes(b"\xcf\xfa\xed\xfe" + f"/rustc/{STOCK_COMMIT}/library/core\0".encode())
            expected.append(f"{rel}: /rustc/{STOCK_COMMIT}")
        census = staircase.scan_build(self.build, REPO, {HEAD})
        self.assertEqual(census["foreign_rustc_paths"], sorted(expected))
        self.assertEqual(census["rustc_path_targets"], 2)
        self.assertFalse(census["clean"])


class RungConfigAndInputsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="seed-staircase-config-"))

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def sysroot(self, rel: str, tools=("trustc", "cargo", "trustdoc", "trustfmt")) -> Path:
        root = self.tmp / rel
        (root / "bin").mkdir(parents=True)
        for tool in tools:
            (root / "bin" / tool).write_text("")
        return root

    def test_rung_config_includes_the_base_and_names_every_stage0_tool(self) -> None:
        base = self.tmp / "bootstrap.toml"
        base.write_text('[build]\nsubmodules = false\n')
        stage0 = self.sysroot("rung-1/stage2")
        text = staircase.write_rung_config(base, stage0, self.tmp / "rung.toml")
        self.assertIn(f"include = [{json.dumps(str(base.resolve()))}]", text)
        for key, tool in (("rustc", "trustc"), ("cargo", "cargo"), ("rustdoc", "trustdoc"), ("rustfmt", "trustfmt")):
            self.assertIn(f"{key} = {json.dumps(str(stage0 / 'bin' / tool))}", text)
        with self.assertRaises(staircase.Refusal):
            staircase.write_rung_config(base, stage0, self.tmp / "rung.toml")  # never overwritten

    def test_rung_config_refuses_incomplete_or_genesis_stage0(self) -> None:
        base = self.tmp / "bootstrap.toml"
        base.write_text("")
        with self.assertRaisesRegex(staircase.Refusal, "no bin/cargo"):
            staircase.write_rung_config(base, self.sysroot("partial", ("trustc",)), self.tmp / "a.toml")
        with self.assertRaisesRegex(staircase.Refusal, "genesis-stage0"):
            staircase.write_rung_config(base, self.sysroot("build/host/genesis-stage0"), self.tmp / "b.toml")

    def test_rung_zero_config_is_the_recreators_seed_mode_with_no_compiler_keys(self) -> None:
        tree = self.tmp / "tree"
        (tree / "scripts").mkdir(parents=True)
        shutil.copy2(REPO / "scripts" / "recreate_bootstrap.py", tree / "scripts")
        (tree / "src/bootstrap").mkdir(parents=True)
        shutil.copy2(REPO / "src/bootstrap/stage0_identity.py", tree / "src/bootstrap")
        record = staircase.write_seed_config(tree, "/opt/llvm/bin/llvm-config")
        text = (tree / "bootstrap.toml").read_text()
        self.assertIn("(seed stage0 mode)", text)
        self.assertIn('llvm-config = "/opt/llvm/bin/llvm-config"', text)
        for key in ("rustc", "cargo", "rustdoc", "rustfmt", "cargo-clippy"):
            self.assertNotRegex(text, rf"(?m)^\s*{key}\s*=")
        self.assertEqual(record["sha256"], staircase.sha256_file(tree / "bootstrap.toml"))

    def test_libgit2_crate_must_match_the_lockfile_checksum(self) -> None:
        crate = self.tmp / "libgit2-sys-0.18.8+1.9.7.crate"
        crate.write_bytes(b"not the pinned crate")
        lock = self.tmp / "Cargo.lock"
        lock.write_text('[[package]]\nname = "libgit2-sys"\nversion = "0.18.8+1.9.7"\n'
                        'checksum = "7f7c568b25d7489bc3fb2988ed69ab111d2944d2f5fec3d5c987fe545ea97b50"\n')
        if platform.system() != "Darwin":
            self.skipTest("libgit2-compat is a macOS-only input")
        with self.assertRaisesRegex(staircase.Refusal, "!= Cargo.lock checksum"):
            staircase.libgit2_compat(crate, lock, self.tmp / "out")
        self.assertFalse((self.tmp / "out").exists())

    def test_a_tool_dir_never_carries_a_rust_tool_or_a_stock_root(self) -> None:
        tools = self.tmp / "tools"
        tools.mkdir()
        with self.assertRaisesRegex(staircase.Refusal, "declares no tool"):
            staircase.tool_dir_record([tools])
        shutil.copy2("/bin/true", tools / "ninja")
        self.assertEqual([e["name"] for e in staircase.tool_dir_record([tools])[0]["entries"]], ["ninja"])
        for name in ("cargo", "rustc", "trustc", "targo", "rustup"):
            (tools / name).symlink_to("/bin/true")
            with self.assertRaisesRegex(staircase.Refusal, "Rust tool name"):
                staircase.tool_dir_record([tools])
            (tools / name).unlink()
        # A harmless name whose target is a Rust tool is still a Rust tool.
        stock = self.tmp / "elsewhere"
        stock.mkdir()
        shutil.copy2("/bin/true", stock / "cargo")
        (tools / "helper").symlink_to(stock / "cargo")
        with self.assertRaisesRegex(staircase.Refusal, "Rust tool name"):
            staircase.tool_dir_record([tools])
        (tools / "helper").unlink()
        # Anything that resolves into rustup's or cargo's tree is refused by place.
        rustup = self.tmp / ".rustup" / "toolchains" / "x" / "bin"
        rustup.mkdir(parents=True)
        shutil.copy2("/bin/true", rustup / "ld.lld")
        (tools / "ld.lld").symlink_to(rustup / "ld.lld")
        with self.assertRaisesRegex(staircase.Refusal, "stock root"):
            staircase.tool_dir_record([tools])
        (tools / "ld.lld").unlink()
        (tools / "notes").write_text("not a program")
        with self.assertRaisesRegex(staircase.Refusal, "not an executable file"):
            staircase.tool_dir_record([tools])

    def test_scrubbed_environment_reaches_no_stock_tool(self) -> None:
        ledger = self.tmp / "ledger"
        staircase.write_traps(ledger / "trap", ledger / "trap.log")
        env = staircase.scrubbed_env(ledger, "unit", [], sys.executable)
        for forbidden in ("/.cargo/", "/.rustup/", "/opt/homebrew/", "aterm/pkg/reroute"):
            self.assertNotIn(forbidden, env["PATH"])
        self.assertEqual(env["RUSTUP_TOOLCHAIN"], "__trust_no_rustup__")
        self.assertNotIn("RUSTC", env)
        self.assertNotIn("CARGO", env)
        probe = subprocess.run(["cargo", "--version"], env=env, capture_output=True, text=True)
        self.assertEqual(probe.returncode, 127)
        self.assertIn("cargo\t--version", (ledger / "trap.log").read_text())

    def test_the_scrubbed_environment_without_the_new_options_is_the_one_it_always_was(self) -> None:
        # `run --offline` and `run --clean-lean-lib` (the first Linux seed's builds) are
        # additions: every rung run without them, and every record of one, is unchanged.
        ledger = self.tmp / "ledger"
        caller = {"HOME": "/caller-home", "USER": "caller", "LOGNAME": "caller-login", "PATH": os.environ["PATH"]}
        with mock.patch.dict(os.environ, caller, clear=True):
            env = staircase.scrubbed_env(ledger, "unit", [], "/usr/bin/python3.12", source_date_epoch="17",
                                         tool_dirs=[Path("/tools")])
            explicit = staircase.scrubbed_env(ledger, "unit", [], "/usr/bin/python3.12", source_date_epoch="17",
                                              tool_dirs=[Path("/tools")], offline=False, clean_lean=None)
            lean = {"CLEAN_OLEAN_PINNED_LEAN_LIB": "/lean/lib/lean", "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"}
            both = staircase.scrubbed_env(ledger, "unit", [], "/usr/bin/python3.12", source_date_epoch="17",
                                          tool_dirs=[Path("/tools")], offline=True, clean_lean=lean)
            unflagged = staircase.scrubbed_env(ledger, "unit", [], "/usr/bin/python3.12", source_date_epoch="17",
                                               tool_dirs=[Path("/tools")], makeflags=None)
            flags = "-j3 --jobserver-auth=fifo:/l/tmp/jobserver.fifo"
            all_three = staircase.scrubbed_env(ledger, "unit", [], "/usr/bin/python3.12", source_date_epoch="17",
                                               tool_dirs=[Path("/tools")], offline=True, clean_lean=lean,
                                               makeflags=flags)
        expected = {
            "HOME": staircase.HOME, "USER": "caller", "LOGNAME": "caller-login",
            "SHELL": "/bin/sh", "TERM": "dumb", "LANG": "en_US.UTF-8", "LC_ALL": "en_US.UTF-8",
            "TMPDIR": str(ledger / "tmp"),
            "PATH": f"{ledger / 'trap'}:{ledger / 'pathbin'}:/usr/bin:/bin:/usr/sbin:/sbin:"
                    "/Library/Developer/CommandLineTools/usr/bin:/tools",
            "CARGO_HOME": str(ledger / "cargo-home"),
            "RUSTUP_TOOLCHAIN": "__trust_no_rustup__", "RUSTUP_AUTO_INSTALL": "0",
            "TRUST_STAIRCASE_RUNG": "unit", "SOURCE_DATE_EPOCH": "17",
        }
        self.assertEqual(env, expected)
        self.assertEqual(list(env), list(expected))  # the order x.py receives them in
        self.assertEqual(explicit, env)
        # Each option adds its variables after everything else and changes no other.
        self.assertEqual(list(both), [*expected, "CARGO_NET_OFFLINE", *lean])
        self.assertEqual(both, {**expected, "CARGO_NET_OFFLINE": "true", **lean})
        # `run --fifo-jobserver`: MAKEFLAGS last, and nothing without it.
        self.assertEqual(unflagged, env)
        self.assertEqual(list(unflagged), list(expected))
        self.assertEqual(list(all_three), [*expected, "CARGO_NET_OFFLINE", *lean, "MAKEFLAGS"])
        self.assertEqual(all_three, {**both, "MAKEFLAGS": flags})

    def test_the_job_count_is_read_as_bootstrap_reads_it(self) -> None:
        # `run --fifo-jobserver` advertises -jN for the N x.py runs with: its -j over
        # --set build.jobs over [build] jobs of the configuration it reads.
        tree = (self.tmp / "jobs").resolve()
        tree.mkdir()
        (tree / "base.toml").write_text("[build]\njobs = 2\n")
        (tree / "bootstrap.toml").write_text('include = ["base.toml"]\n')
        self.assertEqual(staircase.xpy_jobs(tree, ["build"]), (2, f"[build] jobs of {tree / 'base.toml'}"))
        (tree / "bootstrap.toml").write_text('include = ["base.toml"]\n\n[build]\njobs = 5\n')
        self.assertEqual(staircase.xpy_jobs(tree, ["build"]), (5, f"[build] jobs of {tree / 'bootstrap.toml'}"))
        self.assertEqual(staircase.xpy_jobs(tree, ["build", "--set", "build.jobs=6"]), (6, "x.py --set build.jobs"))
        self.assertEqual(staircase.xpy_jobs(tree, ["--set=build.jobs=6", "build", "-j", "7"]), (7, "x.py -j"))
        for words in (["-j7", "build"], ["build", "--jobs", "7"], ["--jobs=7", "build"], ["-j=7"]):
            self.assertEqual(staircase.xpy_jobs(tree, words), (7, "x.py -j"), words)
        (tree / "other.toml").write_text("[build]\njobs = 9\n")
        self.assertEqual(staircase.xpy_jobs(tree, ["--config", "other.toml", "build"])[0], 9)
        self.assertEqual(staircase.xpy_jobs(tree, [f"--config={tree / 'other.toml'}", "build"])[0], 9)
        # What follows `--` is the test harness's, not x.py's.
        self.assertEqual(staircase.xpy_jobs(tree, ["test", "--", "-j", "3"])[0], 5)
        for words, pattern in ((["-j", "0"], r"x.py's -j is 0; Bootstrap reads a count below 1 as this host's"),
                               (["-j", "four"], r"x.py's -j is 'four', not a whole job count"),
                               (["-j", "2", "--jobs", "3"], r"name the job count 2 times"),
                               (["-vj4", "build"], r"'-vj4' may hold -j among other short flags"),
                               (["-j", "4097"], r"over the 4096 jobs"),
                               (["--set", "build.jobs=0"], r"--set build.jobs is 0")):
            with self.subTest(words), self.assertRaisesRegex(staircase.Refusal, pattern):
                staircase.xpy_jobs(tree, words)
        for value, pattern in (("true", "is True, not a whole job count"), ('"4"', "is '4', not a whole job count"),
                               ("-1", "is -1; Bootstrap reads a count below 1")):
            (tree / "bootstrap.toml").write_text(f"[build]\njobs = {value}\n")
            with self.subTest(value), self.assertRaisesRegex(staircase.Refusal, pattern):
                staircase.xpy_jobs(tree, ["build"])
        (tree / "bootstrap.toml").write_text("[build]\n")
        (tree / "base.toml").unlink()
        with self.assertRaisesRegex(staircase.Refusal, r"named nowhere: not by -j or --set build.jobs among its "
                                                       rf"arguments, and not by \[build\] jobs of {tree}/bootstrap.toml"):
            staircase.xpy_jobs(tree, ["build"])
        (tree / "bootstrap.toml").unlink()
        with self.assertRaisesRegex(staircase.Refusal, r"named nowhere: .* not by \[build\] jobs of any configuration"):
            staircase.xpy_jobs(tree, ["build"])
        # The largest count whose tokens are preloaded whole.
        self.assertEqual(staircase.xpy_jobs(tree, ["-j", "4096"]), (4096, "x.py -j"))

    def test_includes_merge_later_over_earlier_and_one_that_includes_itself_is_refused(self) -> None:
        tree = (self.tmp / "includes").resolve()
        tree.mkdir()
        (tree / "a.toml").write_text("[build]\njobs = 2\n")
        (tree / "b.toml").write_text("[build]\njobs = 3\n")
        (tree / "none.toml").write_text("[build]\n")
        # Bootstrap merges the last include first and keeps what is set: a later
        # include over an earlier one (the including file over all, tested above).
        (tree / "bootstrap.toml").write_text('include = ["a.toml", "b.toml", "none.toml"]\n')
        self.assertEqual(staircase.xpy_jobs(tree, ["build"]), (3, f"[build] jobs of {tree / 'b.toml'}"))
        (tree / "bootstrap.toml").write_text('include = ["b.toml", "a.toml"]\n')
        self.assertEqual(staircase.xpy_jobs(tree, ["build"]), (2, f"[build] jobs of {tree / 'a.toml'}"))
        # A file that includes itself, directly or through another, is refused, not followed for ever.
        for files in ({"bootstrap.toml": 'include = ["bootstrap.toml"]\n'},
                      {"bootstrap.toml": 'include = ["c.toml"]\n', "c.toml": 'include = ["a.toml", "bootstrap.toml"]\n'}):
            for name, text in files.items():
                (tree / name).write_text(text)
            with self.subTest(files), self.assertRaisesRegex(
                    staircase.Refusal, rf"cannot be read for its \[build\] jobs: {tree}/bootstrap.toml includes itself\. "
                                       "Nothing was started and nothing was written"):
                staircase.xpy_jobs(tree, ["build"])

    def test_the_fifo_jobserver_preflight_refuses_what_it_cannot_hand_over(self) -> None:
        tree = (self.tmp / "preflight").resolve()
        tree.mkdir()
        ledger = tree / "ledger"
        (ledger / "tmp").mkdir(parents=True)
        fifo = ledger / "tmp" / "jobserver.fifo"
        make = shutil.which("make", path=":".join(staircase.OS_PATH))
        self.assertEqual(staircase.fifo_jobserver_preflight(tree, ledger, ["-j", "2"], []),
                         {"jobs": 2, "source": "x.py -j", "path": fifo, "make": make})
        # Something at the FIFO's path, even a dangling link, is never removed.
        fifo.symlink_to(tree / "gone")
        with self.assertRaisesRegex(staircase.Refusal, r"jobserver.fifo is already there: .*nothing was written or "
                                                       r"removed"):
            staircase.fifo_jobserver_preflight(tree, ledger, ["-j", "2"], [])
        self.assertTrue(fifo.is_symlink())
        fifo.unlink()
        # A python whose path a #! line cannot name.
        with mock.patch.object(staircase, "python311", return_value="/opt/a python/bin/python3"), \
                self.assertRaisesRegex(staircase.Refusal, r"the python /opt/a python/bin/python3 holds white space, "
                                                          r"and the make adapter's #! line names it"):
            staircase.fifo_jobserver_preflight(tree, ledger, ["-j", "2"], [])
        # No make after pathbin: refused, unless a declared tool directory holds one.
        empty = tree / "empty"
        empty.mkdir()
        tools = tree / "tools"
        tools.mkdir()
        (tools / "make").write_text("#!/bin/sh\n")
        (tools / "make").chmod(0o755)
        with mock.patch.object(staircase, "OS_PATH", (str(empty),)):
            with self.assertRaisesRegex(staircase.Refusal, rf"there is no make on x.py's PATH after its pathbin "
                                                           rf"\({empty}\)\..*Nothing was started and nothing was "
                                                           "written. Install make"):
                staircase.fifo_jobserver_preflight(tree, ledger, ["-j", "2"], [])
            self.assertEqual(staircase.fifo_jobserver_preflight(tree, ledger, ["-j", "2"], [tools])["make"],
                             str(tools / "make"))
        self.assertEqual(list((ledger / "tmp").iterdir()), [])


class MakeAdapterTests(unittest.TestCase):
    """The make adapter `run --fifo-jobserver` puts first on x.py's PATH, run over a
    stand-in make: GNU make before 4.4 cannot read --jobserver-auth=fifo:PATH, so a
    FIFO named that way is handed over as two descriptors on it."""

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="seed-staircase-make-")).resolve()
        self.stand_in = self.tmp / "real-make"
        self.stand_in.write_text(f"#!{staircase.python311()}\n{STAND_IN_MAKE}")
        self.stand_in.chmod(0o755)
        (self.tmp / "pathbin").mkdir()
        self.record = staircase.install_make_adapter(self.tmp, staircase.python311(), str(self.stand_in))
        self.adapter = Path(self.record["path"])
        self.fifo = self.tmp / "jobserver.fifo"
        os.mkfifo(self.fifo, 0o600)
        # The run holds the FIFO open with its tokens for as long as x.py runs.
        self.held = os.open(self.fifo, os.O_RDWR | os.O_NONBLOCK)
        os.write(self.held, b"++")

    def tearDown(self) -> None:
        os.close(self.held)
        shutil.rmtree(self.tmp, ignore_errors=True)

    def make(self, *argv: str, **env: str) -> subprocess.CompletedProcess:
        # A build script's child under Trust std: only fds 0-2.
        return subprocess.run([str(self.adapter), *argv], env={"PATH": "/usr/bin:/bin", **env},
                              capture_output=True, text=True, close_fds=True)

    def test_what_is_installed_is_the_adapter_for_its_python_and_make(self) -> None:
        text = staircase.make_adapter_text(staircase.python311(), str(self.stand_in))
        self.assertEqual(self.adapter.read_text(), text)
        self.assertEqual(self.record, {"path": str(self.tmp / "pathbin" / "make"),
                                       "sha256": staircase.sha256_file(self.adapter), "make": str(self.stand_in),
                                       "make_sha256": staircase.sha256_file(self.stand_in)})
        self.assertEqual(text.splitlines()[:3], [f"#!{staircase.python311()} -I", staircase.MAKE_ADAPTER_MARK,
                                                 f"MAKE = {str(self.stand_in)!r}"])

    def test_a_fifo_is_handed_over_as_two_descriptors_on_it_and_the_rest_is_unchanged(self) -> None:
        flags = f"-j --jobserver-fds=fifo:{self.fifo} --jobserver-auth=fifo:{self.fifo}"
        done = self.make("-C", "dir", "build_libs", MAKEFLAGS=flags, MFLAGS=flags, CARGO_MAKEFLAGS=flags)
        self.assertEqual(done.returncode, 0, done.stderr)
        seen = json.loads(done.stdout)
        self.assertEqual(seen["argv"], ["-C", "dir", "build_libs"])
        match = re.fullmatch(r"-j --jobserver-fds=([0-9]+),([0-9]+) --jobserver-auth=\1,\2", seen["MAKEFLAGS"])
        self.assertIsNotNone(match, seen["MAKEFLAGS"])
        self.assertEqual(seen["MFLAGS"], seen["MAKEFLAGS"])
        self.assertNotEqual(match.group(1), match.group(2))
        fifo = os.stat(self.fifo)
        self.assertEqual(seen["fds"], {fd: [fifo.st_dev, fifo.st_ino] for fd in match.groups()})
        # Only what make reads is changed, and the tokens are where they were.
        self.assertEqual(seen["CARGO_MAKEFLAGS"], flags)
        self.assertEqual(os.read(self.held, 16), b"++")

    def test_a_make_handed_no_fifo_is_run_as_it_was_asked(self) -> None:
        for env in ({}, {"MAKEFLAGS": "-k"}, {"MAKEFLAGS": "-j --jobserver-auth=3,4", "MFLAGS": "-j"}):
            with self.subTest(env):
                done = self.make("all", **env)
                self.assertEqual(done.returncode, 0, done.stderr)
                seen = json.loads(done.stdout)
                self.assertEqual(seen["argv"], ["all"])
                self.assertEqual((seen["MAKEFLAGS"], seen["MFLAGS"]), (env.get("MAKEFLAGS"), env.get("MFLAGS")))

    def test_a_fifo_that_cannot_be_handed_over_runs_no_make(self) -> None:
        plain = self.tmp / "plain-file"
        plain.write_text("+++")
        for flags, pattern in (
                (f"-j --jobserver-auth=fifo:{self.fifo}", None),
                (f"-j --jobserver-auth=fifo:{self.tmp / 'gone'}", r"the jobserver FIFO .*/gone cannot be opened: No "
                                                                  "such file or directory"),
                (f"-j --jobserver-auth=fifo:{plain}", r"the jobserver .*/plain-file is not a FIFO")):
            with self.subTest(flags):
                if pattern is None:
                    # MAKEFLAGS and MFLAGS that name two FIFOs.
                    done = self.make(MAKEFLAGS=flags, MFLAGS=f"-j --jobserver-auth=fifo:{plain}")
                    pattern = r"MAKEFLAGS and MFLAGS name 2 FIFO jobservers \(.*/jobserver.fifo, .*/plain-file\)"
                else:
                    done = self.make(MAKEFLAGS=flags)
                self.assertEqual(done.returncode, 2)
                self.assertEqual(done.stdout, "")
                self.assertRegex(done.stderr, rf"^seed staircase make adapter: {pattern}; .*real-make was not run\n$")
        self.assertEqual(os.read(self.held, 16), b"++")

    def test_process_classes(self) -> None:
        home = staircase.HOME
        allowed = ["/w/build"]
        self.assertEqual(staircase.classify_exe(f"{home}/.rustup/toolchains/stable/bin/rustc", allowed), "STOCK-RUST")
        self.assertEqual(staircase.classify_exe("/opt/homebrew/bin/cargo", allowed), "STOCK-RUST")
        self.assertEqual(staircase.classify_exe("/opt/homebrew/Cellar/python@3.14/bin/python3", allowed), "FOREIGN-NONRUST")
        self.assertEqual(staircase.classify_exe("/w/build/host/stage0/bin/cargo", allowed), "ok")
        self.assertEqual(staircase.classify_exe("/elsewhere/bin/rustc", allowed), "RUST-OUTSIDE-ADMITTED-ROOTS")


if __name__ == "__main__":
    unittest.main()
