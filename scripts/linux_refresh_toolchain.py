#!/usr/bin/env python3
"""Bring a Linux host's Trust toolchain to a target commit: one seed-staircase rung.

`src/stage0` pins no Linux archive (docs/PLAN.md, PKG-S6), so a Linux
host cannot build main from a pinned seed, and every seed re-pin leaves its installed
toolchain further behind. What the host can do is build the target commit from the
Trust toolchain it already has, through `seed_staircase.py run` (trap shims, process
and build census), and seal the result. This is that procedure as one command: the
steps of docs/SEED_STAIRCASE.md, "Before a rung of a current commit", in order.

    plan   print every command in order and run nothing
    run    run them; a step whose output is already in the ledger is not repeated

It claims nothing the staircase does not. The root of such a chain is unpinned, so
no lineage record follows (`seed_staircase.py lineage` refuses it) and a seal made
here says `stage0_lineage=absent`. It never flips the rustup `trust` link:
`--seal` runs `promote-toolchain.sh --no-flip`, which prints the two commands.

`--seal` supplies the two things that script's gates need and a rung has neither of:
the `trust-serial-command` every gate starts the compiler through, built from the
rung's own source by the rung's own `targo` into the ledger (the clone stays clean),
and a build slot, by running the script under `scripts/build-slot`. A caller that
already names an executor in TRUST_TOOLCHAIN_SERIAL_COMMAND, or already holds a
slot, keeps its own. A rung seals with its own commit's script, so which of this a
commit needs is read from the commit before anything is built: one whose script
predates the executor (083f70d694, 2026-11-07; the pinned seed 82bb867edd does) is
sealed with the bare command, as it always was.

`--fixed-point` builds the commit a second time from the first build's own stage2,
at the same path with the same LLVM, and compares the two stage2 trees
(`mint_seed_support.py ddc-compare`). Identical trees say the result does not depend
on which compiler built the compiler. They do not make the double compile diverse:
both builds descend from the one stage0. Given with `--seal`, a comparison that
finds the two trees not identical is a refusal before the seal: neither tree is
sealed and both are kept. `run` again with `--seal` and without `--fixed-point`
then seals the second build, and no rung is built again.

What is compared is each build's own stage2: the first in the build directory moved
into the ledger (`<label>-build/<host>/stage2`), the second in the rung worktree. The
read-only copy the second build is built from (`<label>-stage2`) is not compared: a
manifest records every entry's mode, and the copy has no write bit. Until 2026-11-12
the copy was what was read, and two builds of 6762badf3c on aarch64 Linux were
reported NOT identical in 559 of 561 entries whose bytes are the same.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
STAIRCASE = HERE / "seed_staircase.py"
MINT_SUPPORT = HERE / "mint_seed_support.py"
# bootstrap_dependency_closure.py refuses a larger budget.
PREPARE_TIMEOUT_S = 900
# The build outputs a second build of one commit may reuse: neither is built by a
# Rust compiler, so keeping them isolates the bytes the compared compilers produce.
NATIVE_OUTPUTS = ("llvm", "lld")
# What x.py asks of a build-tree manager before it takes the build lock (x.py,
# `_trust_build_lock_frontend`).
MANAGER_PROBE = ("--trust-build-tree-lock", "--protocol")
MANAGER_V2 = b"trust-build-tree-manager-v2\n"
# What promote-toolchain.sh reads the serial executor's path from.
SERIAL_VARIABLE = "TRUST_TOOLCHAIN_SERIAL_COMMAND"
# What scripts/build-slot sets for the command it admits, and what the executor asks for.
SLOT_VARIABLE = "BUILD_SLOT_HELD"
# How long the seal waits for a build slot (`build-slot --wait-timeout`).
SEAL_SLOT_WAIT_S = 900
# The usage line of a scripts/build-slot older than fdb293a14d (2026-11-10), which
# refuses `--wait-timeout` on an ordinary admission.
OLD_SLOT_WAIT = "[--exclusive [--wait-timeout S]]"


class Refusal(Exception):
    """A step's precondition does not hold. Nothing was changed by raising it."""


def host_triple(system: str | None = None, machine: str | None = None) -> str:
    system = platform.system() if system is None else system
    machine = platform.machine() if machine is None else machine
    if system != "Linux":
        raise Refusal("this is the Linux procedure; a macOS host builds from the src/stage0 pin "
                      "(scripts/recreate_bootstrap.py)")
    arch = {"aarch64": "aarch64", "arm64": "aarch64", "x86_64": "x86_64"}.get(machine)
    if arch is None:
        raise Refusal(f"no Linux host triple is known for machine {machine!r}")
    return f"{arch}-unknown-linux-gnu"


def git_command(repo: Path, *args: str) -> list[str]:
    # Automatic maintenance must finish inside the command that owns this
    # checkout. Detached GC can keep writing after temporary-source cleanup.
    # Keep maintenance enabled; both current and older Git run it synchronously.
    return ["git", "-c", "maintenance.autoDetach=false", "-c", "gc.autoDetach=false",
            "-C", str(repo), *args]


def git(repo: Path, *args: str) -> str:
    done = subprocess.run(git_command(repo, *args), capture_output=True, text=True)
    if done.returncode:
        raise Refusal(f"git -C {repo} {' '.join(args)}: {done.stderr.strip() or done.returncode}")
    return done.stdout.strip()


def gitlinks(worktree: Path) -> list[tuple[str, str]]:
    """(path, pin) of every submodule HEAD's tree names."""
    links = []
    for entry in git(worktree, "ls-tree", "-r", "-z", "HEAD").split("\0"):
        if entry.startswith("160000 "):
            meta, path = entry.split("\t", 1)
            links.append((path, meta.split()[2]))
    return links


def submodule_names(worktree: Path) -> dict[str, str]:
    """path -> name, from the worktree's .gitmodules."""
    if not (worktree / ".gitmodules").is_file():
        return {}
    names = {}
    for line in git(worktree, "config", "-f", ".gitmodules", "--get-regexp",
                    r"^submodule\..*\.path$").splitlines():
        key, path = line.split(" ", 1)
        names[path] = key[len("submodule."):-len(".path")]
    return names


def materialize_submodules(worktree: Path, modules: Path, repo: Path) -> list[str]:
    """Check out every submodule of `worktree` at its pin, from `modules/<path>`.

    `modules` is another checkout's module store (`<git dir>/modules`), so nothing is
    fetched: a pin that store lacks is a refusal that names the command, not a clone
    from the network. Nested submodules come from the nested store the same way.
    """
    done = []
    names = submodule_names(worktree)
    for path, pin in gitlinks(worktree):
        store = modules / path
        if not (store / "HEAD").is_file():
            raise Refusal(f"{store} is not a module store: {repo} never initialised {path}")
        if subprocess.run(["git", "-C", str(store), "cat-file", "-e", pin + "^{commit}"],
                          capture_output=True).returncode:
            raise Refusal(f"{path} is pinned at {pin[:10]}, which {store} does not hold; in {repo} run "
                          "scripts/submodule_sync.sh --fetch --restore")
        name = names.get(path)
        if name is None:
            raise Refusal(f"{worktree}/.gitmodules names no submodule at {path}")
        git(worktree, "config", f"submodule.{name}.url", str(store))
        git(worktree, "-c", "protocol.file.allow=always", "submodule", "--quiet", "update",
            "--init", "--no-fetch", "--", path)
        done.append(path)
        done += [f"{path}/{nested}"
                 for nested in materialize_submodules(worktree / path, store / "modules", repo)]
    return done


def clone_rung(repo: Path, commit: str, worktree: Path) -> list[str]:
    """A clean local clone of `commit` with every submodule, nested ones included."""
    if worktree.exists():
        raise Refusal(f"{worktree} exists")
    git(repo, "clone", "--quiet", "--no-checkout", str(repo), str(worktree))
    git(worktree, "checkout", "--quiet", "--detach", commit)
    return materialize_submodules(worktree, Path(git(repo, "rev-parse", "--absolute-git-dir")) / "modules",
                                  repo)


def worktree_problems(worktree: Path, commit: str) -> list[str]:
    """Why an existing rung worktree is not a clean checkout of `commit` (empty: it is)."""
    problems = []
    head = git(worktree, "rev-parse", "HEAD")
    if head != commit:
        problems.append(f"HEAD is {head[:10]}, not {commit[:10]}")
    dirty = git(worktree, "status", "--porcelain", "--ignore-submodules=none")
    if dirty:
        problems.append(f"{len(dirty.splitlines())} path(s) differ from HEAD, the first: {dirty.splitlines()[0]}")
    status = subprocess.run(["git", "-C", str(worktree), "submodule", "status", "--recursive"],
                            capture_output=True, text=True).stdout
    off = [line.split()[1] for line in status.splitlines() if line[:1] in "-+U"]
    if off:
        problems.append("submodule(s) not at their pins: " + ", ".join(off))
    return problems


def rung_problems(record: dict) -> list[str]:
    """Why a `seed_staircase.py run` record is not a clean rung (empty: it is)."""
    problems = []
    if record.get("rc") != 0:
        problems.append(f"x.py exited {record.get('rc')}")
    if record.get("no_stock_evidence") is not True:
        detail = {key: record.get(key) for key in ("trap_hits", "stage0_matches_admission",
                                                   "stage0_runtime_unchanged", "tool_dirs_unchanged",
                                                   "sampler_died")}
        problems.append(f"the no-stock evidence is not clean: {json.dumps(detail, sort_keys=True)}")
    return problems


def shown(repo: Path, commit: str, path: str) -> str | None:
    """A file of `commit`, or None when the commit has nothing at that path."""
    result = subprocess.run(["git", "-C", str(repo), "show", f"{commit}:{path}"],
                            capture_output=True, text=True, errors="replace")
    return result.stdout if result.returncode == 0 else None


def seal_uses_executor(repo: Path, commit: str) -> bool:
    """Does this commit's own promote-toolchain.sh start its gates through the serial
    executor? Read from the commit, so `plan` answers before a worktree exists and
    `run` refuses before a build of hours whose seal could not be made.

    False: the script predates the executor and is run bare, as it always was.
    True: the commit also has the crate that builds the executor and a build-slot
    this script's command line suits. Anything in between is a refusal."""
    promote = shown(repo, commit, "scripts/promote-toolchain.sh")
    if promote is None:
        raise Refusal(f"{commit[:10]} has no scripts/promote-toolchain.sh, so --seal has nothing to run")
    if SERIAL_VARIABLE not in promote:
        return False
    manifest = shown(repo, commit, "crates/trust-resource-controller/Cargo.toml") or ""
    slot = shown(repo, commit, "scripts/build-slot")
    problems = []
    if 'name = "trust-serial-command"' not in manifest:
        problems.append("no trust-serial-command binary in crates/trust-resource-controller/Cargo.toml")
    if not re.search(r"(?m)^serial-command\s*=", manifest):
        problems.append("no serial-command feature in crates/trust-resource-controller/Cargo.toml")
    if slot is None:
        problems.append("no scripts/build-slot")
    elif OLD_SLOT_WAIT in slot:
        problems.append("a scripts/build-slot that bounds only an --exclusive wait (it predates fdb293a14d)")
    if problems:
        raise Refusal(f"{commit[:10]}'s promote-toolchain.sh starts its gates through {SERIAL_VARIABLE}, "
                      f"which --seal supplies by building that commit's trust-serial-command and running "
                      f"under that commit's scripts/build-slot; the commit has {'; '.join(problems)}. "
                      "Run the rung without --seal and seal it by hand (INSTALL.md, \"Register the toolchain\")")
    return True


class Plan:
    """The commands of one refresh, and the ledger files that say a step is done."""

    # Whether the commit's own promote-toolchain.sh needs the serial executor and a
    # build slot (`seal_uses_executor`, asked by `main` when `--seal` is given).
    serial = True

    def __init__(self, args: argparse.Namespace, host: str, commit: str):
        self.args, self.host, self.commit = args, host, commit
        self.ledger: Path = args.ledger
        self.repo: Path = args.repo
        self.label: str = args.label or f"r-{commit[:10]}"
        self.worktree: Path = args.worktree or self.ledger / f"w-{commit[:10]}"
        self.stage0: Path = args.stage0

    # ledger files -----------------------------------------------------------
    def file(self, label: str, suffix: str) -> Path:
        return self.ledger / f"{label}.{suffix}"

    def stage2(self) -> Path:
        return self.worktree / "build" / self.host / "stage2"

    def kept_stage2(self) -> Path:
        return self.ledger / f"{self.label}-stage2"

    def kept_build(self) -> Path:
        return self.ledger / f"{self.label}-build"

    def first_stage2(self) -> Path:
        """The first build's own stage2 once `set_aside` has moved its build tree into
        the ledger, with the modes that build gave it. `kept_stage2()` is the copy of
        it the second build is built from, every write bit removed."""
        return self.kept_build() / self.host / "stage2"

    def compared(self) -> list[tuple[str, Path, str]]:
        """What --fixed-point compares: (which build, its own stage2, its label)."""
        return [("first", self.first_stage2(), self.label), ("second", self.stage2(), self.label + "-fp")]

    def bootstrap(self) -> Path:
        """Where bootstrap.py builds this commit's Bootstrap, and where x.py looks for
        a build-tree manager."""
        return self.worktree / "build" / "bootstrap" / "debug" / "bootstrap"

    # commands ---------------------------------------------------------------
    def staircase(self, *words: str) -> list[str]:
        return [sys.executable, str(STAIRCASE), *words]

    def admit(self, stage0: Path) -> list[str]:
        return self.staircase("admit", str(stage0), "--repo", str(self.repo), "--target", self.commit)

    def seed_config(self) -> list[str]:
        return self.staircase("seed-config", "--worktree", str(self.worktree))

    def config(self, stage0: Path, label: str) -> list[str]:
        return self.staircase("config", "--base", str(self.worktree / "bootstrap.toml"),
                              "--stage0", str(stage0), "--out", str(self.file(label, "bootstrap.toml")))

    def prepare_env(self) -> dict[str, str]:
        return {"HOME": os.environ.get("HOME", ""), "USER": os.environ.get("USER", ""),
                "LANG": "C.UTF-8", "PATH": f"{self.ledger / 'trap'}:/usr/bin:/bin",
                "CARGO_HOME": str(self.ledger / "cargo-home")}

    def prepare(self, stage0: Path) -> list[str]:
        return [sys.executable, "-I", "-S", "-B",
                str(self.worktree / "scripts" / "bootstrap_dependency_closure.py"), "prepare",
                "--repo-root", str(self.worktree), "--targo", str(stage0 / "bin" / "cargo"),
                "--timeout", str(PREPARE_TIMEOUT_S)]

    def construct(self) -> list[str]:
        return [sys.executable, str(self.worktree / "x.py"), "--version"]

    def construct_env(self, label: str) -> dict[str, str]:
        return {**self.prepare_env(), "RUST_BOOTSTRAP_CONFIG": str(self.file(label, "bootstrap.toml"))}

    def construct_line(self, label: str) -> str:
        return (f"(cd {self.worktree} && env -i "
                + " ".join(f"{k}={shlex.quote(v)}" for k, v in self.construct_env(label).items())
                + f" {shlex.join(self.construct())} > {self.file(label, 'bootstrap.log')} 2>&1)"
                + "   # builds Bootstrap, the build-tree manager x.py needs; its exit status is not the verdict")

    def run(self, label: str) -> list[str]:
        tools = [word for directory in self.args.tool_dir for word in ("--tool-dir", str(directory))]
        return self.staircase("run", "--worktree", str(self.worktree), "--label", label,
                              "--ledger", str(self.ledger), *tools,
                              "--stage0-admission", str(self.file(label, "admission.json")),
                              "--", "--config", str(self.file(label, "bootstrap.toml")),
                              "build", "--stage", "2")

    def manifest(self, tree: Path, out: Path) -> list[str]:
        return [sys.executable, str(MINT_SUPPORT), "stage2-manifest", str(tree), str(out)]

    def compare(self) -> list[str]:
        return [sys.executable, str(MINT_SUPPORT), "ddc-compare",
                str(self.file(self.label, "stage2.json")), str(self.file(self.label + "-fp", "stage2.json"))]

    # the seal ---------------------------------------------------------------
    def serial_target(self) -> Path:
        """Where the seal's serial executor is built: in the ledger, so the rung
        clone stays the clean tree its build stamp names."""
        return self.ledger / f"{self.label}-serial-command"

    def serial_command(self) -> Path:
        return self.serial_target() / "release" / "trust-serial-command"

    def serial_crate(self) -> Path:
        return self.worktree / "crates" / "trust-resource-controller"

    def serial_env(self) -> dict[str, str]:
        """The rung's stage2 first on PATH and nothing of the host's Rust after it."""
        return {**self.prepare_env(),
                "PATH": f"{self.stage2() / 'bin'}:{self.ledger / 'trap'}:/usr/bin:/bin",
                "CARGO_TARGET_DIR": str(self.serial_target()),
                "RUSTUP_TOOLCHAIN": "__trust_no_rustup__", "RUSTUP_AUTO_INSTALL": "0"}

    def serial_fetch(self) -> list[str]:
        """The executor's crate is its own workspace with its own lock, which names
        registry versions Bootstrap's lock does not; the rung's closure is not
        promised to hold them. Fetching what the lock names downloads only what the
        cargo home lacks. (`fetch` is not a compilation, so it takes no lane flag.)"""
        return [str(self.stage2() / "bin" / "targo"), "fetch", "--locked"]

    def serial_build(self) -> list[str]:
        return [str(self.stage2() / "bin" / "targo"), "--unverified", "build", "--locked", "--offline",
                "--release", "--features", "serial-command", "--bin", "trust-serial-command"]

    def serial_build_line(self) -> str:
        log = self.file(self.label, "serial-command.log")
        return (f"(cd {self.serial_crate()} && env -i "
                + " ".join(f"{k}={shlex.quote(v)}" for k, v in self.serial_env().items())
                + f" sh -c {shlex.quote(shlex.join(self.serial_fetch()) + ' && ' + shlex.join(self.serial_build()))}"
                + f" > {log} 2>&1)   # not run when {SERIAL_VARIABLE} already names one")

    def seal(self, held: bool = False) -> list[str]:
        """`held`: the caller already holds a build slot, so none is asked for
        (build-slot refuses `--wait-timeout` inside a held slot)."""
        promote = ["bash", str(self.worktree / "scripts" / "promote-toolchain.sh"), "--no-flip", str(self.stage2())]
        if held or not self.serial:
            return promote
        # One CPU: the gates start one compiler at a time, and a slot asked for with
        # no budget borrows every free one for as long as the seal runs.
        return [sys.executable, str(self.worktree / "scripts" / "build-slot"), "--cpus", "1",
                "--wait-timeout", str(SEAL_SLOT_WAIT_S), "--", *promote]

    def config_note(self) -> str:
        lld = ', rust.bootstrap-override-lld = "self-contained"' if self.args.lld else ""
        return f"   # then: jobs = {self.args.jobs}{lld}"

    def lines(self) -> list[str]:
        """Every command of the refresh, in order, as a person would type it."""
        fp = self.label + "-fp"
        out = [f"# {self.label}: {self.commit[:10]} from {self.stage0} on {self.host}; ledger {self.ledger}",
               f"clone {self.repo} at {self.commit[:10]} into {self.worktree}, submodules from its module store",
               shlex.join(self.admit(self.stage0)) + f" > {self.file(self.label, 'admission.json')}",
               shlex.join(self.seed_config()),
               shlex.join(self.config(self.stage0, self.label)) + self.config_note(),
               "env -i " + " ".join(f"{k}={shlex.quote(v)}" for k, v in self.prepare_env().items()) + " "
               + shlex.join(self.prepare(self.stage0)),
               self.construct_line(self.label),
               shlex.join(self.run(self.label)) + f" > {self.file(self.label, 'run.json')}"]
        if self.args.fixed_point:
            out += [f"cp -a {self.stage2()} {self.kept_stage2()} && chmod -R a-w {self.kept_stage2()}",
                    f"mv {self.worktree / 'build'} {self.kept_build()}   # then copy back "
                    + ", ".join(NATIVE_OUTPUTS),
                    shlex.join(self.admit(self.kept_stage2())) + f" > {self.file(fp, 'admission.json')}",
                    shlex.join(self.config(self.kept_stage2(), fp)) + self.config_note(),
                    self.construct_line(fp),
                    shlex.join(self.run(fp)) + f" > {self.file(fp, 'run.json')}",
                    *(f"rm -f {self.file(label, 'stage2.json')} && "
                      + shlex.join(self.manifest(tree, self.file(label, "stage2.json")))
                      + f"   # the {which} build's own stage2" for which, tree, label in self.compared()),
                    shlex.join(self.compare()) + f" > {self.file(self.label, 'fixed-point.txt')}"]
        if self.args.seal and self.serial:
            out += [self.serial_build_line(),
                    f"(cd {self.worktree} && {SERIAL_VARIABLE}={self.serial_command()} {shlex.join(self.seal())})"
                    f"   # `run` keeps a {SERIAL_VARIABLE} the caller already names, and inside a held slot "
                    f"({SLOT_VARIABLE}=1) starts the script without build-slot"]
        elif self.args.seal:
            out.append(f"(cd {self.worktree} && {shlex.join(self.seal())})"
                       f"   # this commit's script predates {SERIAL_VARIABLE}")
        return out


def say(text: str) -> None:
    print(f"linux-refresh: {text}", flush=True)


def to_file(command: list[str], out: Path, *, env: dict[str, str] | None = None, cwd: Path | None = None,
            stderr: Path | None = None, merge: bool = False) -> int:
    """Run `command` with stdout in `out`. The file is written beside its final name
    and moved there only when the command exits 0, so a present file is a finished
    step. `stderr` names a file for the messages; `merge` puts them in `out` too."""
    partial = out.with_name(out.name + ".partial")
    with open(partial, "wb") as sink:
        if stderr is not None:
            with open(stderr, "wb") as errors:
                code = subprocess.run(command, stdout=sink, stderr=errors, env=env, cwd=cwd).returncode
        else:
            code = subprocess.run(command, stdout=sink, stderr=subprocess.STDOUT if merge else None,
                                  env=env, cwd=cwd).returncode
    if code == 0:
        partial.replace(out)
    return code


def write_traps(ledger: Path) -> None:
    """The trap shims `seed_staircase.py run` writes, written before the dependency
    fetch so that it cannot reach a stock Rust tool by name either."""
    sys.path.insert(0, str(HERE))
    try:
        import seed_staircase
    finally:
        sys.path.remove(str(HERE))
    ledger.joinpath("trap.log").touch()
    seed_staircase.write_traps(ledger / "trap", ledger / "trap.log")


def self_contained_lld(stage0: Path, host: str) -> list[Path]:
    """What `-Clink-self-contained=+linker` needs of a stage0: its rust-lld and the
    `ld.lld` wrapper the C compiler driver is pointed at."""
    tools = stage0 / "lib" / "rustlib" / host / "bin"
    return [tools / "rust-lld", tools / "gcc-ld" / "ld.lld"]


def speaks_manager_v2(binary: Path, cwd: Path) -> bool:
    """x.py's own probe of a build-tree manager, asked of `binary`."""
    try:
        probe = subprocess.run([str(binary), *MANAGER_PROBE], cwd=cwd, capture_output=True, timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        return False
    return probe.returncode == 0 and probe.stdout == MANAGER_V2


def asks_manager_v2(worktree: Path) -> bool:
    """Whether this commit's x.py takes the build lock through a protocol-v2 manager.

    It is read from the x.py being built, not from the commit's ancestry: x.py names
    the answer it requires (MANAGER_V2) in its own source since fb01581fb3."""
    script = worktree / "x.py"
    try:
        text = script.read_bytes()
    except OSError as error:
        raise Refusal(f"{script} cannot be read ({error.strerror}), so whether it needs a "
                      "build-tree manager is not known") from error
    return MANAGER_V2.strip() in text


def construct_bootstrap(plan: Plan, label: str) -> None:
    """Give a fresh rung worktree the build-tree manager x.py will ask for.

    Since fb01581fb3 (2026-11-07) x.py takes the build lock through a manager that
    answers protocol v2: the tree's own built Bootstrap, a `targo` on PATH, or
    TRUST_BUILD_TREE_MANAGER_TARGO. A fresh rung worktree has no Bootstrap, a rung's
    PATH holds no targo, `seed_staircase.py run` passes no manager, and a stage0
    older than that commit (the pinned seed 82bb867edd is) speaks v1. So the rung
    stopped in a second: "native build-tree manager v2 is unavailable".

    `x.py --version` is one of the four requests x.py lets through without the lock,
    and bootstrap.py builds Bootstrap for it from the rung config's stage0 before
    Bootstrap refuses the unknown flag. The step is therefore judged by the binary
    it leaves, not by its exit status. It runs under the rung's PATH, traps
    included, and before the recorded rung; the rung's build census then reads the
    whole build directory, this binary's compiler records among it.

    An x.py older than fb01581fb3 (82bb867edd's) takes the lock itself and asks for
    no manager, and its Bootstrap does not answer the probe, so for it this step
    does nothing. Asking anyway refused every build of that commit.
    """
    if not asks_manager_v2(plan.worktree):
        say(f"{label}: this commit's x.py takes the build lock itself; no build-tree manager to construct")
        return
    binary = plan.bootstrap()
    if speaks_manager_v2(binary, plan.worktree):
        return
    say(f"{label}: constructing this commit's Bootstrap, the build-tree manager x.py asks for")
    log = plan.file(label, "bootstrap.log")
    with open(log, "wb") as sink:
        code = subprocess.run(plan.construct(), stdout=sink, stderr=subprocess.STDOUT,
                              env=plan.construct_env(label), cwd=plan.worktree).returncode
    if not speaks_manager_v2(binary, plan.worktree):
        raise Refusal(f"{binary} is not a protocol-v2 build-tree manager after `x.py --version` (exit {code}); "
                      f"x.py would refuse the rung. Its output is {log}")


def config_tail(jobs: int, lld: bool) -> str:
    """What a rung config adds to the recreator's seed-mode config and the stage0 keys.
    It follows the [build] table `seed_staircase.py config` ends with."""
    tail = ("# linux_refresh_toolchain.py: the recreator's seed-mode config for this commit,\n"
            f"# unchanged but for the stage0 keys above and the job count.\njobs = {jobs}\n")
    if lld:
        tail += ("\n# --lld: every Rust link of the build goes through the building compiler's own\n"
                 "# rust-lld rather than the system linker (GNU ld is single-threaded).\n"
                 "[rust]\nbootstrap-override-lld = \"self-contained\"\n")
    return tail


def last_table(config: str) -> str | None:
    """The header of the last TOML table a config text opens."""
    headers = [line.strip() for line in config.splitlines() if line.startswith("[")]
    return headers[-1] if headers else None


def rung(plan: Plan, label: str, stage0: Path) -> None:
    """Admit `stage0`, write the rung config, fill the cargo home, run, and judge."""
    record_path = plan.file(label, "run.json")
    if record_path.is_file():
        problems = rung_problems(json.loads(record_path.read_text()))
        if problems:
            raise Refusal(f"{record_path} records a rung that did not finish clean ({'; '.join(problems)}); "
                          "x.py resumes under a new --label")
        say(f"{label}: already built clean ({record_path})")
        return
    admission = plan.file(label, "admission.json")
    if not admission.is_file() and to_file(plan.admit(stage0), admission):
        raise Refusal(f"seed_staircase.py admit refused {stage0}; its reasons are in {admission}.partial")
    config = plan.file(label, "bootstrap.toml")
    if not config.is_file():
        if not (plan.worktree / "bootstrap.toml").is_file():
            must(plan.seed_config(), f"{label}: the worktree's base config could not be written",
                 stdout=subprocess.DEVNULL)
        draft = config.with_name(config.name + ".partial")
        must(plan.config(stage0, label)[:-1] + [str(draft)], f"{label}: the rung config could not be written",
             stdout=subprocess.DEVNULL)
        text = draft.read_text()
        if last_table(text) != "[build]":
            raise Refusal(f"{draft} does not end in its [build] table, so a job count cannot be appended to it")
        if plan.args.lld:
            missing = [str(path) for path in self_contained_lld(stage0, plan.host) if not path.is_file()]
            if missing:
                raise Refusal(f"--lld needs the stage0's own linker, and {stage0} has no {', '.join(missing)}")
        draft.write_text(text + config_tail(plan.args.jobs, plan.args.lld))
        draft.replace(config)
    write_traps(plan.ledger)
    (plan.ledger / "cargo-home").mkdir(exist_ok=True)
    say(f"{label}: preparing the offline dependency closure")
    if to_file(plan.prepare(stage0), plan.file(label, "prepare.log"), env=plan.prepare_env(), cwd=plan.worktree,
               merge=True):
        raise Refusal(f"the dependency closure is not ready; see {plan.file(label, 'prepare.log')}.partial")
    construct_bootstrap(plan, label)
    say(f"{label}: building (x.py's output goes to {plan.ledger / 'logs' / (label + '.log')})")
    code = to_file(plan.run(label), record_path, stderr=plan.file(label, "run.stderr"))
    if code:
        raise Refusal(f"seed_staircase.py run exited {code}; its record is {record_path}.partial and its "
                      f"messages {plan.file(label, 'run.stderr')}")
    problems = rung_problems(json.loads(record_path.read_text()))
    if problems:
        raise Refusal(f"{label} is not a clean rung: {'; '.join(problems)}")
    say(f"{label}: clean rung, {json.loads(record_path.read_text()).get('elapsed_s')} s")


def ended(code: int) -> str:
    """How a command ended, in words."""
    return f"was killed by signal {-code}" if code < 0 else f"exited {code}"


def must(command: list[str], doing: str, **options) -> None:
    """Run `command`, whose own words go to the terminal; a failure is a refusal that
    says what was being done and how the command ended. Each of these was
    `check=True`: this script's traceback under the command's one line."""
    code = subprocess.run(command, **options).returncode
    if code:
        raise Refusal(f"{doing}: `{shlex.join(command)}` {ended(code)}; what it said is above")


def last_line(text: str) -> str:
    """The last line of what a command printed that is not blank."""
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    return lines[-1] if lines else "(it printed nothing on stderr)"


def comparer_starts() -> None:
    """Refuse --fixed-point now when mint_seed_support.py cannot start from here.

    The comparison is the last step, after two builds of the commit, and
    mint_seed_support.py loads src/bootstrap/stage0_identity.py from the checkout
    it is in before it reads its command line. On 2026-11-12 that file was not
    found, and a second build of 2 h 45 min ended in this script's traceback."""
    command = [sys.executable, str(MINT_SUPPORT), "--help"]
    done = subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True, errors="replace")
    if done.returncode:
        raise Refusal(f"--fixed-point compares the two builds with {MINT_SUPPORT}, and that program does not "
                      f"start from this checkout: `{shlex.join(command)}` {ended(done.returncode)}, and the last "
                      f"line it printed on stderr is: {last_line(done.stderr)}\n    This is asked before anything "
                      "is cloned or built because the comparison comes last, after two builds of the commit, "
                      "and a comparison that cannot start would leave both without a verdict. Run this script "
                      "from a complete checkout (that program loads src/bootstrap/stage0_identity.py from the "
                      "checkout it is in), or without --fixed-point")


def write_manifest(plan: Plan, which: str, tree: Path, label: str) -> None:
    """Write `<label>.stage2.json`, the manifest of `tree`.

    mint_seed_support.py creates its output and refuses a path that exists, so the
    manifest is written beside its final name and moved there only when the command
    exited 0: a file under the final name is a finished manifest of this comparison
    (`refresh` removes an earlier one). A command that fails is a refusal in words.
    It was `check=True`: a traceback, after both builds."""
    out = plan.file(label, "stage2.json")
    partial = out.with_name(out.name + ".partial")
    partial.unlink(missing_ok=True)
    command = plan.manifest(tree, partial)
    done = subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True, errors="replace")
    if done.returncode == 0 and partial.is_file():
        partial.replace(out)
        return
    partial.unlink(missing_ok=True)
    how = ended(done.returncode) + (" and wrote no manifest" if done.returncode == 0 else "")
    raise Refusal(f"--fixed-point: no manifest of the {which} build's stage2, {tree}, could be written, so the two "
                  f"builds were not compared and nothing was sealed. `{shlex.join(command)}` {how}, and the last "
                  f"line it printed on stderr is: {last_line(done.stderr)}\n    Both builds are kept (the first "
                  f"in {plan.kept_build()}, the second in {plan.worktree / 'build'}) and neither is built again: "
                  "once the cause is removed, the same command line resumes at the comparison")


def copy_tree(source: Path, target: Path) -> None:
    """`cp -a`, visible under its final name only when complete."""
    partial = target.with_name(target.name + ".partial")
    if partial.exists():
        must(["chmod", "-R", "u+w", str(partial)], f"an unfinished copy at {partial} could not be removed")
        shutil.rmtree(partial)
    must(["cp", "-a", str(source), str(partial)],
         f"{source} could not be copied to {target} (the unfinished copy is {partial}; the same command line "
         "starts the copy again)")
    partial.rename(target)


def set_aside(plan: Plan) -> None:
    """Keep the first build's stage2 (read-only) and its build tree, and leave at the
    path the first build used a build directory that holds only the native outputs.
    Every part is skipped when already done, so an interrupted call can be repeated."""
    kept, moved, build = plan.kept_stage2(), plan.kept_build(), plan.worktree / "build"
    if not kept.exists():
        copy_tree(plan.stage2(), kept)
        must(["chmod", "-R", "a-w", str(kept)], f"the kept copy {kept} could not be made read-only")
    if not moved.exists():
        build.rename(moved)
    (build / plan.host).mkdir(parents=True, exist_ok=True)
    for name in NATIVE_OUTPUTS:
        if (moved / plan.host / name).is_dir() and not (build / plan.host / name).exists():
            copy_tree(moved / plan.host / name, build / plan.host / name)


def seal(plan: Plan) -> None:
    """Seal the rung's stage2 with `promote-toolchain.sh --no-flip`.

    Since 083f70d694 (2026-11-07) every gate of that script starts the compiler and the
    shipped tools through `trust-serial-command`, named in TRUST_TOOLCHAIN_SERIAL_COMMAND,
    and that program starts nothing for a caller that holds no build slot. A rung has
    neither, and this step used to run the script bare: on 2026-11-10 it refused a
    stage2 that passes every gate, each UI row printed FAIL with no reason, and the
    refusal said to fix the compiler. The script now names the cause before any gate;
    this supplies both.

    The executor is built from the rung's own source by the rung's own targo, offline
    from the closure the rung prepared, into the ledger. It is not the independently
    packaged one the script's comment asks for: a Linux host has no package of it. A
    caller that has one names it in the variable and it is used as given.
    """
    environment = dict(os.environ)
    if not plan.serial:
        say(f"sealing {plan.stage2()} (--no-flip); this commit's script predates {SERIAL_VARIABLE}")
        if subprocess.run(plan.seal(), cwd=plan.worktree, env=environment).returncode:
            raise Refusal("promote-toolchain.sh refused the seal; its output is above")
        return
    if environment.get(SERIAL_VARIABLE):
        say(f"the seal's serial executor is the one the caller names: {environment[SERIAL_VARIABLE]}")
    else:
        executor, log = plan.serial_command(), plan.file(plan.label, "serial-command.log")
        say(f"building the seal's serial executor with the rung's own targo ({executor})")
        steps = [("build", plan.serial_build())]
        if not executor.is_file():
            # A rerun (after a refused seal, say) finds the executor in the ledger: the
            # offline build then only checks that it is current, and nothing is fetched twice.
            steps.insert(0, ("fetch its locked dependencies", plan.serial_fetch()))
        with open(log, "wb") as sink:
            for step, command in steps:
                code = subprocess.run(command, stdout=sink, stderr=subprocess.STDOUT,
                                      env=plan.serial_env(), cwd=plan.serial_crate()).returncode
                if code:
                    break
        if code or not executor.is_file():
            raise Refusal(f"trust-serial-command did not {step} (exit {code}), and no gate of "
                          f"promote-toolchain.sh can start without it; nothing was sealed. Its output is {log}")
        environment[SERIAL_VARIABLE] = str(executor)
    held = environment.get(SLOT_VARIABLE) == "1"
    if not held:
        # build-slot refuses a caller's CARGO_BUILD_JOBS larger than the `--cpus 1` it is
        # asked for, and sets it to 1 for the script either way: the caller's count was
        # for the rung, which is built by now.
        environment.pop("CARGO_BUILD_JOBS", None)
    say(f"sealing {plan.stage2()} (--no-flip), "
        + ("in the build slot this run already holds" if held else "under a build slot"))
    code = subprocess.run(plan.seal(held), cwd=plan.worktree, env=environment).returncode
    if code and held:
        raise Refusal("promote-toolchain.sh refused the seal; its output is above")
    if code:
        # Two programs can have ended this command, and only one of them is the script.
        raise Refusal(f"scripts/build-slot or promote-toolchain.sh refused the seal (exit {code}); the output is "
                      "above. A last line that begins `build-slot:` is the slot's own refusal (no slot within "
                      f"{SEAL_SLOT_WAIT_S} s, or a request it rejects): promote-toolchain.sh was not started and "
                      "no gate ran. A line that begins `promote:` is the script's")


def refresh(plan: Plan) -> int:
    plan.ledger.mkdir(parents=True, exist_ok=True)
    if plan.worktree.exists():
        problems = worktree_problems(plan.worktree, plan.commit)
        if problems:
            raise Refusal(f"{plan.worktree} is not a clean checkout of {plan.commit[:10]}: {'; '.join(problems)}")
    else:
        say(f"cloning {plan.commit[:10]} into {plan.worktree}")
        say("submodules: " + ", ".join(clone_rung(plan.repo, plan.commit, plan.worktree)))
    rung(plan, plan.label, plan.stage0)
    identical = None
    if plan.args.fixed_point:
        fp = plan.label + "-fp"
        if not plan.file(fp, "run.json").is_file():
            set_aside(plan)
        rung(plan, fp, plan.kept_stage2())
        # Each build's own tree, with the modes that build gave it. The read-only
        # copy the second build was built from differs from every build in the mode
        # of every entry that has one (Plan.first_stage2).
        report = plan.file(plan.label, "fixed-point.txt")
        # Anew on every comparison: the trees are what is compared, and what an
        # earlier comparison left (a verdict, a manifest of whatever that run read)
        # says nothing about this one.
        for earlier in (report, *(plan.file(label, "stage2.json") for _, _, label in plan.compared())):
            earlier.unlink(missing_ok=True)
        for which, tree, label in plan.compared():
            write_manifest(plan, which, tree, label)
        with open(report, "wb") as sink:
            identical = subprocess.run(plan.compare(), stdout=sink, stderr=subprocess.STDOUT).returncode == 0
        say(f"fixed point: the two stage2 trees are {'identical' if identical else 'NOT identical'} ({report})")
    if plan.args.seal:
        if identical is False:
            # Asked for both: a comparison that failed is not followed by a seal of one side.
            raise Refusal(f"not sealing {plan.stage2()}: --fixed-point found the two stage2 trees NOT identical "
                          f"({report}). Both are kept. Run again with --seal and without --fixed-point to seal "
                          "this one once the difference is understood; nothing is rebuilt")
        seal(plan)
    return 0 if identical in (None, True) else 1


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    result.add_argument("mode", choices=("plan", "run"))
    result.add_argument("--ledger", type=Path, required=True,
                        help="where the worktree, configs, records, logs and cargo home go")
    result.add_argument("--stage0", type=Path, required=True,
                        help="the Trust toolchain to build from: a sealed one (~/toolchains/trust-<rev>) "
                             "or an earlier rung's stage2; `admit` judges it")
    result.add_argument("--commit", default="HEAD", help="the commit to build (default: --repo's HEAD)")
    result.add_argument("--repo", type=Path, default=HERE.parent,
                        help="the checkout to clone from; its module store supplies the submodules")
    result.add_argument("--worktree", type=Path,
                        help="the rung worktree (default: <ledger>/w-<commit>); an existing one must be "
                             "a clean checkout of the commit")
    result.add_argument("--label", help="the rung's name in the ledger (default: r-<commit>)")
    result.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    result.add_argument("--tool-dir", type=Path, action="append", default=[],
                        help="passed to `seed_staircase.py run` (a directory holding only a user-installed "
                             "build tool, such as ninja); repeatable")
    result.add_argument("--lld", action="store_true",
                        help="link the build's Rust code with the stage0's own rust-lld "
                             "(rust.bootstrap-override-lld = \"self-contained\") instead of the system "
                             "linker; refused when the stage0 ships none")
    result.add_argument("--fixed-point", action="store_true",
                        help="build the commit again from its own stage2 and compare the two")
    result.add_argument("--seal", action="store_true",
                        help="seal the final stage2 with promote-toolchain.sh --no-flip, under a build "
                             "slot, with a trust-serial-command built by the rung's own targo "
                             f"(or the one {SERIAL_VARIABLE} names)")
    result.add_argument("--host", help=argparse.SUPPRESS)
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        host = args.host or host_triple()
        args.ledger, args.repo = args.ledger.resolve(), args.repo.resolve()
        args.stage0 = args.stage0.resolve()
        args.worktree = args.worktree.resolve() if args.worktree else None
        args.tool_dir = [directory.resolve() for directory in args.tool_dir]
        if args.jobs < 1:
            raise Refusal("--jobs must be at least 1")
        commit = git(args.repo, "rev-parse", "--verify", args.commit + "^{commit}")
        plan = Plan(args, host, commit)
        if args.fixed_point:
            comparer_starts()
        if args.seal:
            plan.serial = seal_uses_executor(args.repo, commit)
            named = os.environ.get(SERIAL_VARIABLE)
            # promote-toolchain.sh's own rule (serial_executor), asked before the build: a
            # commit older than serial_precondition turns a wrong value into FAIL rows
            # with no reason, and a newer one names it only after the rung is built.
            if plan.serial and named and not (named.startswith("/") and os.path.isfile(named)
                                              and not os.path.islink(named) and os.access(named, os.X_OK)):
                raise Refusal(f"{SERIAL_VARIABLE}={named} is not the absolute path of a regular executable file "
                              "(a relative path, a missing file, a directory, a symlink and a file that is not "
                              "executable are each refused by promote-toolchain.sh). Name the executor itself, "
                              "or unset the variable and --seal builds the rung's own")
        if args.mode == "plan":
            print("\n".join(plan.lines()))
            return 0
        return refresh(plan)
    except Refusal as refusal:
        print(f"linux-refresh: refused: {refusal}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
